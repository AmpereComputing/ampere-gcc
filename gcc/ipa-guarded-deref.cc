/* IPA pass to transform indirect calls to guarded direct calls.
   Copyright (C) 2022 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 3, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "tree.h"
#include "gimple.h"
#include "alloc-pool.h"
#include "tree-pass.h"
#include "tree-cfg.h"
#include "ssa.h"
#include "cgraph.h"
#include "gimple-pretty-print.h"
#include "gimple-iterator.h"
#include "symbol-summary.h"
#include "ipa-utils.h"

#include "attr-fnspec.h"
#include "gimple-ssa.h"
#include "data-streamer.h"
#include "lto-streamer.h"
#include "print-tree.h"
#include "calls.h"
#include "gimple-fold.h"
#include "tree-vrp.h"
#include "ipa-prop.h"
#include "ipa-fnsummary.h"
#include "demangle.h"
#include "dbgcnt.h"
#include "intl.h"
#include "stringpool.h"
#include "attribs.h"
#include "streamer-hooks.h"

#include "alloc-pool.h"
#include "tree-pass.h"
#include "gimple-iterator.h"
#include "tree-dfa.h"
#include "cgraph.h"
#include "ipa-utils.h"
#include "symbol-summary.h"
#include "gimple-pretty-print.h"
#include "gimple-walk.h"
#include "print-tree.h"
#include "tree-streamer.h"
#include "alias.h"
#include "calls.h"
#include "ipa-modref-tree.h"
#include "ipa-modref.h"
#include "value-range.h"
#include "ipa-prop.h"
#include "ipa-fnsummary.h"
#include "attr-fnspec.h"
#include "symtab-clones.h"
#include "gimple-ssa.h"
#include "tree-phinodes.h"
#include "tree-ssa-operands.h"
#include "ssa-iterators.h"
#include "stringpool.h"
#include "tree-ssanames.h"
#include "attribs.h"
#include "tree-cfg.h"
#include "tree-eh.h"
#include "hash-traits.h"

/* Struct that holds a function pointer type.
   In our context a function pointer type is a record-field pair,
   with the field being of a function pointer type.  */

struct function_pointer_type
{
  /* Record type hosting the function pointer.  */
  tree record;
  /* field_decl of the function pointer.  */
  tree field;
};

/* Add a default hash trait for the type function_pointer_type, so it can be used
   as key in hash collections (hash_map, hash_set, etc.).  */

template <>
struct default_hash_traits <function_pointer_type>
  : typed_noop_remove <function_pointer_type>
{
  GTY((skip)) typedef function_pointer_type value_type;
  GTY((skip)) typedef function_pointer_type compare_type;
  static hashval_t
  hash (function_pointer_type p)
    {
      return TYPE_UID (p.record) ^ DECL_UID (p.field);
    }
  static const bool empty_zero_p = true;
  static bool
  is_empty (function_pointer_type p)
    {
      return p.record == NULL_TREE;
    }
  static bool
  is_deleted (function_pointer_type p ATTRIBUTE_UNUSED)
    {
      return false;
    }
  static bool
  equal (const function_pointer_type &l,
	 const function_pointer_type &r)
    {
      return (l.record == r.record) && (l.field == r.field);
    }
  static void
  mark_empty (function_pointer_type &p)
    {
      p.record = NULL_TREE;
      p.field = NULL_TREE;
    }
  static void
  mark_deleted (function_pointer_type &p)
    {
      p.record = NULL_TREE;
      p.field = NULL_TREE;
    }
};

/* Store a call target to a function-pointer-type.
   With this class we can correlate a field-record-pair
   with a function pointer field with a call target.

   We maintain a 1:N mapping here, i.e. a fpt can have exactly 1 call target,
   but a call target can be referenced by multiple fpts.

   Note, that the information needs to be extracted with
   the function pointer type as key and the call target as value.
   However, on call graph modification events, we need a reverse
   lookup (currenlty we don't optimize this code path).  */

class function_pointer_type_assignments
{
private:
  /* Track function-pointer-types and their assigned call targets.  */
  hash_map <function_pointer_type, cgraph_node *> m_assignments;

public:
  function_pointer_type_assignments () {}

  /* Get the call target for a function pointer type (if any).  */
  cgraph_node *get_target (const function_pointer_type &v)
    {
      cgraph_node **pnode = m_assignments.get (v);
      return pnode ? *pnode : NULL;
    }

  /* Add a new assignment for a function pointer type.  */

  void
  add_assignment (function_pointer_type fpt, cgraph_node *target)
    {
      bool existed_p;
      cgraph_node *&node = m_assignments.get_or_insert (fpt, &existed_p);
      if (existed_p)
	  /* More, than one target -> set call target to NULL (unknown).  */
	  node = NULL;
      else
	  node = target;
    }

  /* Print all stored information.  */

  void
  print (void)
    {
      if (!dump_file)
	return;

      fprintf (dump_file,
	       "Collected the following function pointer assignments:\n");

      hash_map<function_pointer_type, cgraph_node*>::iterator iter
	       = m_assignments.begin ();
      for (; iter != m_assignments.end (); ++iter)
	{
	  function_pointer_type fpt = (*iter).first;
	  cgraph_node* callee = (*iter).second;

	  if (fpt.record == NULL_TREE
	      || fpt.field == NULL_TREE
	      || callee == NULL)
	    continue;

	  fprintf (dump_file, "  ");
	  print_generic_expr (dump_file, fpt.record, TDF_NONE);
	  fprintf (dump_file, "::");
	  print_generic_expr (dump_file, fpt.field, TDF_NONE);
	  fprintf (dump_file, " := %s\n", callee ? callee->name () : "<unknown>");
	}
    }

  /* Callback for node removal.  */

  void
  remove (cgraph_node *node)
    {
      /* We iterate over all entries, which is not optimal.
	 To improve this, we need a way for a reverse-lookup.  */
      hash_map<function_pointer_type, cgraph_node*>::iterator iter
	       = m_assignments.begin ();
      for (; iter != m_assignments.end (); ++iter)
	  /* If the cgraph node matches then mark it as removed.  */
	  if ((*iter).second == node)
	    (*iter).second = NULL;
    }

  void
  serialize (struct output_block *ob, lto_symtab_encoder_t &encoder)
    {
      unsigned HOST_WIDE_INT elements = m_assignments.elements ();

      /* Write the number of elements.  */
      streamer_write_uhwi (ob, elements);

      hash_map<function_pointer_type, cgraph_node*>::iterator iter
	       = m_assignments.begin ();
      for (; iter != m_assignments.end (); ++iter)
	{
	  /* Write the function pointer type.  */
	  function_pointer_type fpt = (*iter).first;
	  stream_write_tree_ref (ob, fpt.record);
	  stream_write_tree_ref (ob, fpt.field);

	  /* Write the callee.  */
	  unsigned HOST_WIDE_INT symid;
	  cgraph_node* callee = (*iter).second;
	  if (callee)
	    symid = lto_symtab_encoder_encode (encoder, callee);
	  else
	    symid = 0;

	  streamer_write_uhwi (ob, symid);
	}
    }

  void
  deserialize (lto_input_block &ib, class data_in *data_in,
	       lto_symtab_encoder_t &encoder)
    {
      size_t elements = streamer_read_uhwi (&ib);
      for (size_t i = 0; i < elements; i++)
	{
	  /* Read the function pointer type.  */
	  function_pointer_type fpt;
	  fpt.record = stream_read_tree_ref (&ib, data_in);
	  fpt.field = stream_read_tree_ref (&ib, data_in);

	  /* Read the callee.  */
	  cgraph_node *callee = NULL;
	  unsigned HOST_WIDE_INT symid = streamer_read_uhwi (&ib);
	  if (symid)
	    {
	      symtab_node *scallee = lto_symtab_encoder_deref (encoder, symid);
	      callee = dyn_cast <cgraph_node *> (scallee);
	    }

	  /* Add the function pointer type assignment.  */
	  add_assignment (fpt, callee);
	}
    }

  ~function_pointer_type_assignments () {}
};

/* Store a record-field-pair to a call graph edge.
   With this class we can correlate an indirect call with
   the field-record-pair of its call site.

   Note, that the information needs to be extracted with
   the edge as key and the function pointer type as value.  */

class indirect_call_summary
  :  public call_summary<function_pointer_type *>
{
public:
  indirect_call_summary (symbol_table *table)
    : call_summary <function_pointer_type *> (table)
  { }

  /* Hook that is called by summary when an edge is duplicated.  */
  virtual void duplicate (cgraph_edge *src ATTRIBUTE_UNUSED,
			  cgraph_edge *dst ATTRIBUTE_UNUSED,
			  function_pointer_type *old_fpt,
			  function_pointer_type *new_fpt)
    {
      /* We may not have record-field-pair, because not every edge
	 is an indirect call.  */
      if (!old_fpt)
	return;

      new_fpt->record = old_fpt->record;
      new_fpt->field = old_fpt->field;
    }

  /* Print all stored information.  */

  void
  print (void)
    {
      if (!dump_file)
	return;

      fprintf (dump_file,
	       "Collected the following indirect calls:\n");

      cgraph_node *caller = NULL;
      FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (caller)
	{
	  for (cgraph_edge *e = caller->indirect_calls; e; e = e->next_callee)
	    {
	      function_pointer_type *fpt = get (e);
	      if (fpt && fpt->record && fpt->field)
		{
		  fprintf (dump_file, "  ");
		  fprintf (dump_file, "%s -> ", caller->name ());
		  print_generic_expr (dump_file, fpt->record, TDF_NONE);
		  fprintf (dump_file, "::");
		  print_generic_expr (dump_file, fpt->field, TDF_NONE);
		  fprintf (dump_file, "\n");
		}
	    }
	}
     }

  void
  serialize (struct output_block *ob, lto_symtab_encoder_t encoder)
    {
      unsigned HOST_WIDE_INT elements = 0;

      /* We iterate over all (cnodes x edges) and store all that have
	 additional information stored.  */

      lto_symtab_encoder_iterator it;
      for (it = lsei_start_function_in_partition (encoder); !lsei_end_p (it);
	   lsei_next_function_in_partition (&it))
	{
	  cgraph_node *node = lsei_cgraph_node (it);
	  if (node->has_gimple_body_p ())
	    elements++;
	}

      /* Write the number of elements.  */
      streamer_write_uhwi (ob, elements);

      for (it = lsei_start_function_in_partition (encoder); !lsei_end_p (it);
	   lsei_next_function_in_partition (&it))
	{
	  cgraph_node *caller = lsei_cgraph_node (it);
	  if (!caller->has_gimple_body_p ())
	    continue;

	  /* Write caller.  */
	  unsigned HOST_WIDE_INT symid = lto_symtab_encoder_encode (encoder,
								    caller);
	  streamer_write_uhwi (ob, symid);

	  for (cgraph_edge *e = caller->indirect_calls; e; e = e->next_callee)
	    {
	      function_pointer_type *fpt = get (e);
	      if (fpt && fpt->record && fpt->field)
		{
		  /* Write the function pointer type.  */
		  stream_write_tree_ref (ob, fpt->record);
		  stream_write_tree_ref (ob, fpt->field);
		}
	      else
		{
		  stream_write_tree_ref (ob, NULL_TREE);
		  stream_write_tree_ref (ob, NULL_TREE);
		}
	    }
	}
    }

  void
  deserialize (lto_input_block &ib, class data_in *data_in,
	       lto_symtab_encoder_t &encoder)
    {
      /* Read the number of elements.  */
      size_t elements = streamer_read_uhwi (&ib);

      for (size_t i = 0; i < elements; i++)
	{
	  /* Read caller.  */
	  unsigned HOST_WIDE_INT symid = streamer_read_uhwi (&ib);
	  symtab_node *scaller = lto_symtab_encoder_deref (encoder, symid);
	  cgraph_node *caller = dyn_cast <cgraph_node *> (scaller);

	  for (cgraph_edge *e = caller->indirect_calls; e; e = e->next_callee)
	    {
	      tree record = stream_read_tree_ref (&ib, data_in);
	      tree field = stream_read_tree_ref (&ib, data_in);
	      if (record == NULL_TREE && field == NULL_TREE)
		continue;

	      function_pointer_type *fpt = get_create (e);
	      fpt->record = record;
	      fpt->field = field;
	    }
	}
    }
};

class gimple_walker
{
public:
  gimple_walker () {}

  void walk (void* data);

protected:
  /* Overload these callbacks.  */
  virtual void walk_gassign (__attribute__ ((unused)) cgraph_node*,
			     __attribute__ ((unused)) gassign*,
			     __attribute__ ((unused)) void*) {}
  virtual void walk_gcall (__attribute__ ((unused)) cgraph_node*,
			   __attribute__ ((unused)) gcall*,
			   __attribute__ ((unused)) void*) {}

private:
  /* Will walk declarations, locals, ssa names, and basic blocks.  */
  void _walk_cnode (cgraph_node *cnode, void *data);

  /* Iterate over all basic blocks in CNODE.  */
  void _walk_bb (cgraph_node *cnode, basic_block bb, void *data);

  /* Iterate over all gimple_stmt in BB.  */
  void _walk_gimple (cgraph_node *cnode, gimple *stmt, void *data);
};

void
gimple_walker::walk (void *data)
{
  hash_set<tree> fndecls2;
  cgraph_node *node = NULL;

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    {
      node->get_body ();
      tree decl = node->decl;
      gcc_assert (decl);
      const bool already_in_set = fndecls2.contains (decl);

      /* I think it is possible for different nodes to point to the same
	 declaration.  */
      if (already_in_set)
	continue;

      if (dump_file)
	dump_function_to_file (node->decl, dump_file, TDF_NONE);

      _walk_cnode (node, data);

      /* Add to set of known declarations.  */
      fndecls2.add (decl);
    }
}

/* Walk over all basic blocks in CNODE.  */

void
gimple_walker::_walk_cnode (cgraph_node *cnode, void *data)
{
  cnode->get_body ();
  tree decl = cnode->decl;
  gcc_assert (decl);

  function *func = DECL_STRUCT_FUNCTION (decl);
  gcc_assert (func);

  basic_block bb = NULL;

  push_cfun (func);
  FOR_EACH_BB_FN (bb, func)
    {
      _walk_bb (cnode, bb, data);
    }
  pop_cfun ();
}

/* Walk over each gimple statement in BB.  */

void
gimple_walker::_walk_bb (cgraph_node *cnode, basic_block bb, void *data)
{
  gimple_stmt_iterator gsi;
  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      _walk_gimple (cnode, stmt, data);
    }
}

/* Switch for different gimple instruction types.  */

void
gimple_walker::_walk_gimple (cgraph_node *cnode, gimple *stmt, void *data)
{
  const enum gimple_code code = gimple_code (stmt);
  switch (code)
    {
      case GIMPLE_ASSIGN:
	{
	  gassign *assign = dyn_cast<gassign *> (stmt);
	  walk_gassign (cnode, assign, data);
	  break;
	}
      case GIMPLE_CALL:
	{
	  gcall *call = dyn_cast<gcall *> (stmt);
	  walk_gcall (cnode, call, data);
	  break;
	}
      default:
	break;
    }
}

class gimple_assignment_collector : public gimple_walker
{
protected:
  virtual void walk_gassign (cgraph_node *cnode, gassign *stmt, void *data)
    {
      if (dump_file)
	fprintf (dump_file, "%s: Entering.\n", __func__);

      function_pointer_type_assignments *fpas
	= (function_pointer_type_assignments*) data;

      tree lhs = gimple_assign_lhs (stmt);
      gcc_assert (lhs);

      /* We only care about a rhs which is a variable or a constant.
	 Therefore, we only need to look at unary or single rhs.  */
      const enum gimple_rhs_class gclass = gimple_assign_rhs_class (stmt);
      if (gclass != GIMPLE_UNARY_RHS
	  && gclass != GIMPLE_SINGLE_RHS)
	{
	  if (dump_file)
	    fprintf (dump_file, "%s: RHS class not matching.\n", __func__);
	  return;
	}

      tree rhs = gimple_assign_rhs1 (stmt);

      if (dump_file)
	{
	  fprintf (dump_file, "%s: Analysing assignment:\n", __func__);
	  fprintf (dump_file, " Function: %s\n", cnode->name ());
	  fprintf (dump_file, " LHS: ");
	  print_generic_expr (dump_file, lhs, TDF_NONE);
	  fprintf (dump_file, "\n RHS: ");
	  print_generic_expr (dump_file, rhs, TDF_NONE);
	  fprintf (dump_file, "\n");
	}

      /* We are only interested in function pointers.  */
      tree rhs_t = TREE_TYPE (rhs);
      tree lhs_t = TREE_TYPE (lhs);
      if (TREE_CODE (rhs_t) != POINTER_TYPE
	  || TREE_CODE (lhs_t) != POINTER_TYPE)
	{
	  if (dump_file)
	    fprintf (dump_file, "%s: LHS not pointer type.\n", __func__);
	  return;
	}
      if (TREE_CODE (TREE_TYPE (rhs_t)) != FUNCTION_TYPE
	  || TREE_CODE (TREE_TYPE (lhs_t)) != FUNCTION_TYPE)
	{
	  if (dump_file)
	    fprintf (dump_file, "%s: RHS not function type.\n", __func__);
	  return;
	}

      /* We only care about function pointers assigned to fields.
	 So we look for COMPONENT_REF.  */
      const enum tree_code code = TREE_CODE (lhs);
      if (code != COMPONENT_REF)
	{
	  if (dump_file)
	    fprintf (dump_file, "%s: LHS not component ref.\n", __func__);
	  return;
	}

      tree base = TREE_OPERAND (lhs, 0);
      tree base_t = TREE_TYPE (base);

      /* We either have a record or a pointer to a record.  */
      if (TREE_CODE (base_t) == POINTER_TYPE)
	base_t = TREE_TYPE (base_t);

      if (TREE_CODE (base_t) != RECORD_TYPE)
	{
	  if (dump_file)
	    {
	      fprintf (dump_file, "%s: Base type not record type.\n", __func__);
	      fprintf (dump_file, "%s: base: ", __func__);
	      print_generic_expr (dump_file, base, TDF_DETAILS);
	      fprintf (dump_file, "%s: base_t: ", __func__);
	      print_generic_expr (dump_file, base_t, TDF_DETAILS);
	    }
	  return;
	}

      /* We only care about addr expressions.  */
      if (TREE_CODE (rhs) != ADDR_EXPR)
	{
	  if (dump_file)
	    fprintf (dump_file, "%s: RHS is not addr expr.\n", __func__);
	  return;
	}

      tree possible_decl = TREE_OPERAND (rhs, 0);
      if (TREE_CODE (possible_decl) != FUNCTION_DECL)
	{
	  if (dump_file)
	    fprintf (dump_file, "%s: RHS addr expr is not a function decl.\n",
		     __func__);
	  return;
	}

      tree field = TREE_OPERAND (lhs, 1);

      /* Add record type and field decl to global summary.  */
      function_pointer_type pair;
      pair.record = base_t;
      pair.field = field;
      cgraph_node *node = cgraph_node::get (possible_decl);

      /* This is a candidate for optimization.  */
      if (dump_file)
	{
	  cgraph_node *orig = cgraph_node::get (cfun->decl);
	  fprintf (dump_file, "Candidate found in %s:\n", orig->name ());
	  print_gimple_stmt (dump_file, stmt, dump_flags);
	}

      fpas->add_assignment (pair, node);
    }

  virtual void walk_gcall (cgraph_node *cnode, gcall *stmt, void *data)
    {
      (void)cnode;

      if (dump_file)
	fprintf (dump_file, "%s: Entering.\n", __func__);

      function_pointer_type_assignments *fpas
	= (function_pointer_type_assignments*) data;

      gcc_assert (stmt);
      tree lhs = gimple_call_lhs (stmt);
      if (!lhs)
	return;

      tree lhs_t = TREE_TYPE (lhs);
      /* We are only interested in function pointers.  */
      if (TREE_CODE (lhs_t) != POINTER_TYPE)
	return;
      if (TREE_CODE (TREE_TYPE (lhs_t)) != FUNCTION_TYPE)
	return;

      /* We only care about function pointers assigned to fields.
	 So we look for COMPONENT_REF.  */
      const enum tree_code code = TREE_CODE (lhs);
      if (code != COMPONENT_REF)
	return;

      /* We either have a record or a pointer to a record.  */
      tree base = TREE_OPERAND (lhs, 0);
      tree base_t = TREE_TYPE (base);
      if (TREE_CODE (base_t) != POINTER_TYPE)
	return;
      base_t = TREE_TYPE (base_t);
      if (TREE_CODE (base_t) != RECORD_TYPE)
	return;
      if (!TYPE_P (base_t))
	return;

      tree field = TREE_OPERAND (lhs, 1);

      /* Add record type and field decl to global summary.  */
      function_pointer_type pair;
      pair.record = base_t;
      pair.field = field;

      /* This is a reason to not optimize this pointer.  */
      if (dump_file)
	{
	  cgraph_node *orig = cgraph_node::get (cfun->decl);
	  fprintf (dump_file, "Counter-candidate found in %s:\n", orig->name ());
	  print_gimple_stmt (dump_file, stmt, dump_flags);
	}

      fpas->add_assignment (pair, NULL);
    }
};

/* Globals (prefixed by '_').  */
static function_pointer_type_assignments *_function_pointer_type_assignments;
static indirect_call_summary *_indirect_call_summaries;
static struct cgraph_node_hook_list *_cgraph_removal_hook_holder;

/* Function updates our global summary.  */

static void
remove_cgraph_callback (cgraph_node *node, void *data ATTRIBUTE_UNUSED)
{
  if (dump_file)
    fprintf (dump_file, "%s: node removal: %s\n", __func__, node->name ());
  _function_pointer_type_assignments->remove (node);
}

/* Register notification callbacks.  */

static void
guarded_deref_register_cgraph_hooks (void)
{
  _cgraph_removal_hook_holder
    = symtab->add_cgraph_removal_hook (&remove_cgraph_callback, NULL);
}

/* Unregister notification callbacks.  */

static void
guarded_deref_unregister_cgraph_hooks (void)
{
  if (_cgraph_removal_hook_holder)
    symtab->remove_cgraph_removal_hook (_cgraph_removal_hook_holder);
  _cgraph_removal_hook_holder = NULL;
}

static void
guarded_deref_find_indirect (struct cgraph_node *node,
			     indirect_call_summary *ics)
{
  if (!node || node->inlined_to || !node->has_gimple_body_p ())
    return;

  for (cgraph_edge *e = node->indirect_calls; e; e = e->next_callee)
    {
      gimple *stmt = e->call_stmt;
      if (gimple_code (stmt) != GIMPLE_CALL)
	continue;

      gcall *call_stmt = dyn_cast<gcall *> (stmt);
      tree target = gimple_call_fn (call_stmt);
      if (!target)
	continue;

      if (TREE_CODE (target) != SSA_NAME)
	continue;

      gimple *def = SSA_NAME_DEF_STMT (target);

      if (!gimple_assign_load_p (def))
	continue;

      const enum gimple_rhs_class gclass = gimple_assign_rhs_class (def);
      const bool valid = gclass == GIMPLE_UNARY_RHS || gclass == GIMPLE_SINGLE_RHS;
      if (!valid)
	continue;

      tree rhs = gimple_assign_rhs1 (def);
      const enum tree_code code = TREE_CODE (rhs);
      bool is_load = COMPONENT_REF == code;
      if (!is_load)
	continue;

      tree base = TREE_OPERAND (rhs, 0);
      tree field = TREE_OPERAND (rhs, 1);
      if (RECORD_TYPE != TREE_CODE (TREE_TYPE (base)))
	continue;

      function_pointer_type *fpt = ics->get_create (e);
      fpt->record = TREE_TYPE (base);
      fpt->field = field;
    }
}

static void
guarded_deref_generate_summary (void)
{
  if (dump_file)
    fprintf (dump_file, "%s: Entering.\n", __func__);

  /* Allocate globals.  */
  _function_pointer_type_assignments = new function_pointer_type_assignments;
  _indirect_call_summaries = new indirect_call_summary (symtab);

  /* First collect all function pointer assignments.  */
  gimple_assignment_collector collector;
  collector.walk (_function_pointer_type_assignments);

  /* Now collect all indirect calls.  */
  cgraph_node *cnode = NULL;
  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (cnode)
    {
      guarded_deref_find_indirect (cnode, _indirect_call_summaries);
    }

  /* Print collected information.  */
  _function_pointer_type_assignments->print ();
  _indirect_call_summaries-> print ();

  /* Register hooks for cgraph changes in other passes.  */
  guarded_deref_register_cgraph_hooks ();
}

static void
guarded_deref_write_summary (void)
{
  if (dump_file)
    fprintf (dump_file, "%s: Entering.\n", __func__);

  /* Only run if we are in a sane state.  */
  if (!_function_pointer_type_assignments || !_indirect_call_summaries)
    return;

  /* Print collected information.  */
  _function_pointer_type_assignments->print ();
  _indirect_call_summaries-> print ();

  /* Unregister cgraph change hooks.  */
  guarded_deref_unregister_cgraph_hooks ();

  /* Create an output block to write out information into.  */
  struct output_block *ob = create_output_block (LTO_section_ipa_guarded_deref);

  /* Get the cgraph_node encoder.  */
  lto_symtab_encoder_t encoder = ob->decl_state->symtab_node_encoder;

  /* Write collected function pointer assignments to the OB.  */
  _function_pointer_type_assignments->serialize (ob, encoder);

  /* Write edge summaries.  */
  _indirect_call_summaries->serialize (ob, encoder);

  /* Delete the information in memory.  */
  delete _function_pointer_type_assignments;
  _function_pointer_type_assignments = NULL;
  delete _indirect_call_summaries;
  _indirect_call_summaries = NULL;

  /* Write the contents of the output block into the instruction stream.  */
  produce_asm (ob, NULL);

  /* Now destroy the output block.  */
  destroy_output_block (ob);
}

static void
guarded_deref_read_summary (void)
{
  if (dump_file)
    fprintf (dump_file, "%s: Entering.\n", __func__);

  if (_indirect_call_summaries || _function_pointer_type_assignments)
    return;

  /* Allocate globals.  */
  _indirect_call_summaries = new indirect_call_summary (symtab);
  _function_pointer_type_assignments = new function_pointer_type_assignments;

  struct lto_file_decl_data **file_data_vec = lto_get_file_decl_data ();
  struct lto_file_decl_data *file_data;
  unsigned int j = 0;
  while ((file_data = file_data_vec[j++]))
    {
      size_t len;
      const char *data = lto_get_summary_section_data (file_data,
						       LTO_section_ipa_guarded_deref,
						       &len);
      if (!data)
	continue;

      const struct lto_function_header *header
	= (const struct lto_function_header*) data;

      const int cfg_offset = sizeof (*header);
      const int main_offset = cfg_offset + header->cfg_size;
      const int string_offset = main_offset + header->main_size;
      class data_in *data_in;

      lto_input_block ib ((const char *) data + main_offset,
			  header->main_size, file_data->mode_table);
      data_in = lto_data_in_create (file_data,
				    (const char *) data + string_offset,
				    header->string_size, vNULL);

      lto_symtab_encoder_t encoder = file_data->symtab_node_encoder;

      /* Read collected function pointer assignments from LTO stream.  */
      _function_pointer_type_assignments->deserialize (ib, data_in, encoder);

       /* Read collected indirect call summary from LTO stream.  */
      _indirect_call_summaries->deserialize (ib, data_in, encoder);

      lto_free_section_data (file_data, LTO_section_ipa_guarded_deref, NULL,
			     data, len);
      lto_data_in_delete (data_in);
    }

  /* Print collected information.  */
  _function_pointer_type_assignments->print ();
  _indirect_call_summaries-> print ();

  /* Register hooks for cgraph changes in other passes.  */
  guarded_deref_register_cgraph_hooks ();
}

static unsigned int
guarded_deref_execute (void)
{
  if (dump_file)
    fprintf (dump_file, "%s: Entering.\n", __func__);

  if (!_function_pointer_type_assignments
      || !_indirect_call_summaries)
    return 0;

  /* Unregister cgraph change hooks.  */
  guarded_deref_unregister_cgraph_hooks ();

  /* Print collected information.  */
  _function_pointer_type_assignments->print ();
  _indirect_call_summaries-> print ();

  if (dump_file)
    fprintf (dump_file, "%s: Starting propagation.\n", __func__);

  cgraph_node *cnode = NULL;
  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (cnode)
    {
      if (cnode->inlined_to)
	continue;

      for (cgraph_edge *e = cnode->indirect_calls; e; e = e->next_callee)
	{
	  /* Get the function pointer type for the edge (if any).  */
	  function_pointer_type *fpt = _indirect_call_summaries->get (e);
	  if (!fpt || !fpt->record || !fpt->field)
	    continue;

	  if (dump_file)
	    {
	      fprintf (dump_file, "looking for...:");
	      print_generic_expr (dump_file, fpt->record, TDF_NONE);
	      fprintf (dump_file, " ");
	      print_generic_expr (dump_file, fpt->field, TDF_NONE);
	      fprintf (dump_file, "\n");
	    }

	  /* Now get the call target (if any).  */
	  cgraph_node *target = _function_pointer_type_assignments->get_target (*fpt);
	  if (!target || !target->decl)
	    continue;

	  /* Convert the indirect call to a direct (speculative) call.  */
	  cgraph_edge *new_edge = ipa_make_edge_direct_to_target (e,
								  target->decl,
								  true);

	  if (!new_edge)
	    continue;

	  if (dump_file)
	    {
	      fprintf (dump_file,
		       "Replaced indirect call in %s by "
		       "speculative direct call to %s\n",
		       e->caller->name (), target->name ());
	    }

	  /* Update the function summaries.  */
	  ipa_update_overall_fn_summary (cnode);
	}
    }

  if (dump_file)
    fprintf (dump_file, "%s: Finished propagation.\n", __func__);

  return 0;
}

namespace {

const pass_data pass_data_ipa_guarded_deref =
{
  IPA_PASS, /* type */
  "guarded-deref", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_IPA_GUARDED_DEREF, /* tv_id */
  0, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_ipa_guarded_deref : public ipa_opt_pass_d
{
public:
  pass_ipa_guarded_deref (gcc::context *ctxt)
    : ipa_opt_pass_d (pass_data_ipa_guarded_deref, ctxt,
		      guarded_deref_generate_summary, /* generate_summary */
		      guarded_deref_write_summary, /* write_summary */
		      guarded_deref_read_summary, /* read_summary */
		      NULL, /* write_optimization_summary */
		      NULL, /* read_optimization_summary */
		      NULL, /* stmt_fixup */
		      0, /* function_transform_todo_flags_start */
		      NULL, /* function_transform */
		      NULL) /* variable_transform */
  {}

  /* opt_pass methods: */
  bool gate (function *) final override
    {
      return ((in_lto_p || flag_lto) && flag_ipa_guarded_deref);
    }

  unsigned int execute (function *) final override
    {
      return guarded_deref_execute ();
    }

}; // class pass_ipa_guarded_deref

} // anon namespace

ipa_opt_pass_d *
make_pass_ipa_guarded_deref (gcc::context *ctxt)
{
  return new pass_ipa_guarded_deref (ctxt);
}
