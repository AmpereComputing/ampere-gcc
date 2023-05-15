/* Condition Sinking Optimization
   Copyright (C) 2021-2022 Free Software Foundation, Inc.

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
#include "target.h"
#include "tree.h"
#include "gimple.h"
#include "tree-pass.h"
#include "ssa.h"
#include "gimple-pretty-print.h"
#include "fold-const.h"
#include "gimple-fold.h"
#include "gimplify.h"
#include "gimple-iterator.h"
#include "tree-cfg.h"
#include "tree-ssa.h"
#include "tree-dfa.h"
#include "cgraph.h"
#include "cfghooks.h"
#include "cfgloop.h"
#include "cfganal.h"
#include "ipa-utils.h"
#include "attribs.h"
#include "calls.h"
#include "tree-cfgcleanup.h"

#define IS_PURE_FLAG_PREFIX     "__is_pure_flag"
#define CSO_CLONED_FUNC_SUFFIX  "cso_cloned_fun"

#define FMO_INSERT_FUNC_TAG     "fmo_insert_func"
#define FMO_VEC_FLD_ELT_TAG     "vec_fld_elt_list"

/* Data structure to hold where to insert runtime check against partially pure
   virtual function call.  */

struct purify_call_info
{
  cgraph_node *node;

  cgraph_node *clone;

  /* Partially pure virtual function call.  */
  tree vcall_fn;

  auto_vec<cgraph_node *> vcall_targets;

  tree vcall_object_source;

  /* Before which statements to insert runtime check.  */
  auto_vec<gimple *> check_points;

  tree is_pure_flag;

  purify_call_info (cgraph_node *node)
    : node (node), clone (NULL), vcall_fn (NULL)
    , vcall_object_source (NULL), is_pure_flag (NULL) { }
};

static auto_vec<tree> *fmo_insert_funcs;
static auto_delete_vec<purify_call_info> *purify_calls;

/* Return true if the STMT is an expensive call stmt.  */

static bool
is_expensive_call (gimple *stmt)
{
  gcc_checking_assert (is_gimple_call (stmt));

  // TODO: Relies on devirtualization to cover all virtual function instances.
  return false;
}

/* Check if the BB meet the following conditions,
   (1) Has two outgoing edges.
   (2) The LHS is either none of SSA.
   (3) Doesn't have a function call with side effects.
   (4) The call stmt inside the block is cheap.  */

static bool
is_condition_block_on_cso_path (basic_block bb)
{
  gimple_stmt_iterator gsi;
  gimple *stmt;
  tree lhs;

  if (EDGE_COUNT (bb->succs) != 2)
    return false;

  /* Skip the last stmt. */
  gsi = gsi_last_bb (bb);
  stmt = gsi_stmt (gsi);
  if (gimple_code (stmt) != GIMPLE_COND)
    return false;
  gsi_prev (&gsi);

  /* Scan all stmts backward. */
  for (; !gsi_end_p (gsi); gsi_prev (&gsi))
    {
      stmt = gsi_stmt (gsi);
      if (is_gimple_debug (stmt))
	continue;
      else if (is_gimple_call (stmt))
	{
	  lhs = gimple_call_lhs (stmt);
	  if (gimple_has_side_effects (stmt))
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "> CSO: Found side-effect call ");
		  print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
		}
	      return false;
	    }
	  if (is_expensive_call (stmt))
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "> CSO: Found expensive call ");
		  print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
		}
	      return false;
	    }
	}
      else if (gimple_code (stmt) == GIMPLE_ASSIGN)
	lhs = gimple_assign_lhs (stmt);
      else
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "> CSO: Found other stmt ");
	      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
	    }
	  return false;
	}

      if (lhs && (TREE_CODE (lhs) != SSA_NAME))
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "> CSO: Found lhs is not a SSA name ");
	      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
	    }
	  return false;
	}
    }

  return true;
}

static bool
offset_is_multiple_of_p (tree offset, const offset_int &wi_size)
{
  if (TREE_CODE (offset) == INTEGER_CST)
    {
      offset_int wi_offset = wi::to_offset (offset);

      return wi::multiple_of_p (wi_offset, wi_size, SIGNED);
    }

  if (TREE_CODE (offset) != SSA_NAME)
    return false;

  gimple *offset_stmt = SSA_NAME_DEF_STMT (offset);

  if (gimple_code (offset_stmt) != GIMPLE_ASSIGN)
    return false;

  if (gimple_assign_rhs_code (offset_stmt) == MULT_EXPR)
    {
      tree scale = gimple_assign_rhs2 (offset_stmt);

      if (TREE_CODE (scale) == INTEGER_CST)
	{
	  offset_int wi_scale = wi::to_offset (scale);

	  if (wi::multiple_of_p (wi_scale, wi_size, SIGNED))
	    return true;
	}
    }
  else if (gimple_assign_rhs_code (offset_stmt) == LSHIFT_EXPR)
    {
      tree bits = gimple_assign_rhs2 (offset_stmt);

      if (TREE_CODE (bits) == INTEGER_CST && tree_fits_uhwi_p (bits))
	{
	  unsigned HOST_WIDE_INT hwi_bits = tree_to_uhwi (bits);
	  offset_int wi_scale = offset_int (1) << hwi_bits;

	  if (wi::multiple_of_p (wi_scale, wi_size, SIGNED))
	    return true;
	}
    }

  return false;
}

/* Return true if VALUE is loaded from a class field that is a pointer to an
   array/vector memory.  */

static bool
load_from_vector_field_p (tree value, tree &field, tree &owner_type)
{
  gimple *stmt;

  if (TREE_CODE (value) != SSA_NAME)
    return false;

  while (true)
    {
      stmt = SSA_NAME_DEF_STMT (value);

      if (gimple_code (stmt) == GIMPLE_PHI)
	{
	  tree def_ssa = NULL_TREE;

	  for (unsigned i = 0; i < gimple_phi_num_args (stmt); i++)
	    {
	      tree arg = gimple_phi_arg_def (stmt, i);

	      if (integer_zerop (arg))
		continue;

	      if (TREE_CODE (arg) != SSA_NAME)
		return false;

	      /* Allow only one non-zero definition.  */
	      if (!def_ssa)
		def_ssa = arg;
	      else if (!operand_equal_p (def_ssa, arg))
		return false;
	    }

	  if (!def_ssa)
	    return false;

	  value = def_ssa;
	}
      else if (gimple_assign_ssa_name_copy_p (stmt))
	value = gimple_assign_rhs1 (stmt);
      else
	break;
    }

  /* Check that object pointer of vcall comes from an item of aggregate-type
     element in some vector ptr field of a record type.  */
  if (!gimple_assign_load_p (stmt))
    return false;

  tree rhs = gimple_assign_rhs1 (stmt);

  if (TREE_CODE (rhs) != COMPONENT_REF)
    return false;

  if (!POINTER_TYPE_P (TREE_TYPE (TREE_OPERAND (rhs, 1))))
    return false;

  tree memref = TREE_OPERAND (rhs, 0);

  if (TREE_CODE (memref) != MEM_REF)
    return false;

  if (!integer_zerop (TREE_OPERAND (memref, 1)))
    return false;

  tree elem_addr = TREE_OPERAND (memref, 0);

  if (TREE_CODE (elem_addr) != SSA_NAME)
    return false;

  gimple *elem_addr_stmt = SSA_NAME_DEF_STMT (elem_addr);

  if (gimple_code (elem_addr_stmt) != GIMPLE_ASSIGN)
    return false;

  if (gimple_assign_rhs_code (elem_addr_stmt) == POINTER_PLUS_EXPR)
    {
      tree elem_type = DECL_CONTEXT (TREE_OPERAND (rhs, 1));
      offset_int elem_size = wi::to_offset (TYPE_SIZE_UNIT (elem_type));
      tree offset = gimple_assign_rhs2 (elem_addr_stmt);

      if (!offset_is_multiple_of_p (offset, elem_size))
	return false;

      elem_addr = gimple_assign_rhs1 (elem_addr_stmt);

      if (TREE_CODE (elem_addr) != SSA_NAME)
	return false;

      elem_addr_stmt = SSA_NAME_DEF_STMT (elem_addr);

      if (gimple_code (elem_addr_stmt) != GIMPLE_ASSIGN)
	return false;
    }

  tree elem_list = gimple_assign_rhs1 (elem_addr_stmt);

  if (TREE_CODE (elem_list) != COMPONENT_REF)
    return false;

  tree elem_list_field = TREE_OPERAND (elem_list, 1);

  if (!lookup_attribute (FMO_VEC_FLD_ELT_TAG,
			 DECL_ATTRIBUTES (elem_list_field)))
    return false;

  elem_list = TREE_OPERAND (elem_list, 0);

  if (TREE_CODE (elem_list) != MEM_REF)
    return false;

  tree orig_type = TREE_TYPE (TREE_OPERAND (elem_list, 0));

  if (!POINTER_TYPE_P (orig_type))
    return false;

  orig_type = TREE_TYPE (orig_type);
  if (!RECORD_OR_UNION_TYPE_P (orig_type))
    return false;

  field = TREE_OPERAND (rhs, 1);
  owner_type = orig_type;

  return true;
}

/* Check whether two vcalls refer to same virtual function of a class type.  */

static bool
same_virtual_method_call_p (const_tree vcall_fn_1, const_tree vcall_fn_2)
{
  if (obj_type_ref_class (vcall_fn_1) != obj_type_ref_class (vcall_fn_2))
    return false;

  if (!operand_equal_p (OBJ_TYPE_REF_TOKEN (vcall_fn_1),
			OBJ_TYPE_REF_TOKEN (vcall_fn_2)))
    return false;

  return true;
}

/* Check whether STMT is a memory load to fetch a class's vtable. */

static inline bool
load_vptr_p (gimple *stmt)
{
  if (!gimple_assign_single_p (stmt))
    return false;

  tree rhs = gimple_assign_rhs1 (stmt);

  if (TREE_CODE (rhs) == COMPONENT_REF)
    {
      tree field = TREE_OPERAND (rhs, 1);

      if (TREE_CODE (field) == FIELD_DECL && DECL_VIRTUAL_P (field))
	return true;
    }

  return false;
}

/* Mark every block that has a path to function return, or reversely reachable
   from EXIT_BLOCK.  Blocks in EH ladding pad or infinite loop would be
   excluded.  */

static void
mark_blocks_reaching_exit ()
{
  edge e;
  edge_iterator ei;
  basic_block *tos, *worklist, bb;
  bool has_noreturn_block = false;

  FOR_EACH_BB_FN (bb, cfun)
    {
      bb->flags &= ~BB_REACHABLE;

      if (!EDGE_COUNT (bb->succs))
	has_noreturn_block = true;
    }

  if (!has_noreturn_block)
    {
      FOR_EACH_EDGE (e, ei, EXIT_BLOCK_PTR_FOR_FN (cfun)->preds)
	{
	  if (e->flags & EDGE_FAKE)
	    {
	      has_noreturn_block = true;
	      break;
	    }
	}
    }

  if (!has_noreturn_block)
    {
      FOR_EACH_BB_FN (bb, cfun)
	bb->flags |= BB_REACHABLE;
      return;
    }

  /* First determine which blocks can reach exit via normal paths.  */
  tos = worklist = XNEWVEC (basic_block, n_basic_blocks_for_fn (cfun) + 1);

  /* Place the exit block on our worklist.  */
  EXIT_BLOCK_PTR_FOR_FN (cfun)->flags |= BB_REACHABLE;
  *tos++ = EXIT_BLOCK_PTR_FOR_FN (cfun);

  /* Iterate: find everything reachable from what we've already seen.  */
  while (tos != worklist)
    {
      bb = *--tos;

      FOR_EACH_EDGE (e, ei, bb->preds)
	{
	  basic_block src = e->src;

	  if (e->flags & EDGE_FAKE)
	    continue;

	  if (!(src->flags & BB_REACHABLE))
	    {
	      src->flags |= BB_REACHABLE;
	      *tos++ = src;
	    }
	}
    }

  free (worklist);
}

/* Check whether NODE is a partially pure function.  For an indirect
   call with side effects, if one of its possible targets is pure/const, it
   is partially pure.  Any function containing such kind calls is also
   partially pure, if side effects of the function are only introduced by
   these partially pure calls.  Now we only handle virtual function call,
   since its targets could be easily deduced from class inheritance graph.
   All pure/const targets of related virtual call are recorded in
   VCALL_TARGETS of PURIFY_CALL_INFO kept in NODE->aux, and where to insert
   partially pure check are placed to CHECK_POINTS field, which will be
   used by later dynamic code generation.  */

static bool
function_is_partially_pure_p (cgraph_node *node)
{
  if (node->get_availability () < AVAIL_AVAILABLE)
    return false;

  if (!node->has_gimple_body_p ())
    return false;

  /* This is not a must check, but could simplify dynamic code generation when
     alias is present.  */
  if (node->has_aliases_p ())
    return false;

  /* Skip function if it contains no indirect calls.  */
  if (!node->indirect_calls)
    return false;

  cfun_context fn_context (node);
  gimple *vcall_repr = NULL;
  tree vcall_fn = NULL_TREE;
  tree load_field = NULL_TREE;
  tree owner_type = NULL_TREE;

  gcc_checking_assert (!node->aux);

  /* Only care about calls in normal executable blocks, excluding EH landing
     pad blocks. */
  mark_blocks_reaching_exit ();

  for (cgraph_edge *cs = node->callees; cs; cs = cs->next_callee)
    {
      gimple *call_stmt = cs->call_stmt;

      if (!gimple_has_side_effects (call_stmt))
	continue;

      if (gimple_bb (call_stmt)->flags & BB_REACHABLE)
	return false;
    }

  for (cgraph_edge *cs = node->indirect_calls; cs; cs = cs->next_callee)
    {
      gimple *call_stmt = cs->call_stmt;

      if (!gimple_has_side_effects (call_stmt))
	continue;

      if (!(gimple_bb (call_stmt)->flags & BB_REACHABLE))
	continue;

      tree call_fn = gimple_call_fn (call_stmt);

      if (!virtual_method_call_p (call_fn))
	return false;

      /* Only handle identical virtual function call.  */
      if (!vcall_repr)
	{
	  vcall_repr = call_stmt;
	  vcall_fn = call_fn;
	}
      else if (!same_virtual_method_call_p (vcall_fn, call_fn))
	return false;

      tree otr_object = OBJ_TYPE_REF_OBJECT (call_fn);
      tree new_load_field;
      tree new_owner_type;

      if (!load_from_vector_field_p (otr_object, new_load_field,
				     new_owner_type))
	return false;

      if (!load_field)
	{
	  load_field = new_load_field;
	  owner_type = new_owner_type;
	}
      else if (load_field != new_load_field
	       || !types_same_for_odr (owner_type, new_owner_type))
	return false;
    }

  if (!vcall_repr)
    return false;

  bool complete;
  vec<cgraph_node *> targets
    = possible_polymorphic_call_targets (vcall_fn, vcall_repr, &complete);
  cgraph_node *target;
  auto_vec<cgraph_node *> pure_targets;
  unsigned i;

  FOR_EACH_VEC_ELT (targets, i, target)
    {
      int flags = flags_from_decl_or_type (target->decl);

      gcc_checking_assert (!target->thunk && !target->alias
			   && !target->inlined_to);

      if ((flags & (ECF_CONST | ECF_PURE))
	  && !(flags & ECF_LOOPING_CONST_OR_PURE)
	  && !pure_targets.contains (target))
	pure_targets.safe_push (target);
    }

  tree insert_decl = NULL_TREE;
  tree insert_param_ssa = NULL_TREE;

  /* NOTE: three functions are involved in dynamical pure function shaping:
     cso candidate function, virtual function call targets, and function
     to insert runtime pure check.  Class type referenced by these functions
     might be different, and is only equivalent in terms of ODR.  */

  FOR_EACH_VEC_ELT (*fmo_insert_funcs, i, insert_decl)
    {
      tree param = DECL_ARGUMENTS (insert_decl);
      tree insert_type = TREE_TYPE (param);

      gcc_checking_assert (param && POINTER_TYPE_P (insert_type));

      insert_type = TREE_TYPE (insert_type);

      gcc_checking_assert (RECORD_OR_UNION_TYPE_P  (insert_type));

      if (types_same_for_odr (owner_type, insert_type))
	{
	  tree field = TYPE_FIELDS (DECL_CONTEXT (load_field));

	  for (param = DECL_CHAIN (param); field; field = DECL_CHAIN (field))
	    {
	      if (field == load_field)
		{
		  tree param_type = TREE_TYPE (param);
		  tree field_type = TREE_TYPE (field);
		  struct function *insert_fun
			= DECL_STRUCT_FUNCTION (insert_decl);

		  gcc_checking_assert (POINTER_TYPE_P (param_type)
				       && POINTER_TYPE_P (field_type));

		  if (!types_same_for_odr (TREE_TYPE (param_type),
					   TREE_TYPE (field_type)))
		    return false;

		  insert_param_ssa = ssa_default_def (insert_fun, param);
		  break;
		}

	      gcc_checking_assert (param);
	      param = DECL_CHAIN (param);
	    }
	  break;
	}
    }

  if (!insert_param_ssa)
    return false;

  cfun_context insert_fn_context (insert_decl);
  gimple *use_stmt;
  imm_use_iterator imm_iter;
  auto_vec<gimple *> check_points;

  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, insert_param_ssa)
    {
      if (!gimple_vdef (use_stmt))
	continue;

      if (gimple_code (use_stmt) != GIMPLE_ASSIGN || !gimple_store_p (use_stmt))
	return false;

      /* We add dynamic check at where the parameter is inserted to target
	 record type.  */
      if (gimple_assign_rhs1 (use_stmt) != insert_param_ssa)
	return false;

      check_points.safe_push (use_stmt);
    }

  if (check_points.is_empty ())
    return false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      gimple *check_point;
      cgraph_node *insert_fn_node = cgraph_node::get (insert_decl);

      fprintf (dump_file, "> CSO: Found partially pure function %s/%d",
	       node->asm_name (), node->order);

      fprintf (dump_file, "\n       vcall: ");
      print_generic_expr (dump_file, vcall_fn, TDF_SLIM);

      fprintf (dump_file, "\n       vcall object source function: %s/%d",
	       insert_fn_node->asm_name (), insert_fn_node->order);

      fprintf (dump_file, "\n       check points in source function:\n");
      FOR_EACH_VEC_ELT (check_points, i, check_point)
	{
	  fprintf (dump_file, "         ");
	  print_gimple_stmt (dump_file, check_point, 0, TDF_SLIM);
	}

      fprintf (dump_file, "\n");
    }

  if (!purify_calls)
    purify_calls = new auto_delete_vec<purify_call_info> ();

  /* We only support dynamic check on one partially pure function.  */
  if (purify_calls->length () >= 1)
    return false;

  purify_call_info *info = new purify_call_info (node);

  info->vcall_fn = vcall_fn;
  info->vcall_targets.safe_splice (pure_targets);
  info->check_points.safe_splice (check_points);
  info->vcall_object_source = insert_param_ssa;

  purify_calls->safe_push (info);
  node->aux = (void *) info;

  return true;
}

/* Check whether STMT is a call to partially pure function.  */

static bool
call_is_partially_pure_p (gimple *stmt)
{
  tree fndecl = gimple_call_fndecl (stmt);

  /* Only get here in IPA stage.  */
  gcc_assert (symtab->state < EXPANSION);

  if (!fndecl)
    return false;

  cgraph_node *node = cgraph_node::get (fndecl);

  if (!node->aux && !function_is_partially_pure_p (node))
    {
      node->aux = (void *) 1;
      return false;
    }

  if (node->aux == (void *) 1)
    return false;

  return true;
}

static tree
create_static_variable (const char *name, tree type, tree init,
			bool is_volatile = false)
{
  tree var
    = build_decl (UNKNOWN_LOCATION, VAR_DECL, create_tmp_var_name (name), type);

  if (is_volatile)
    TREE_THIS_VOLATILE (var) = 1;
  TREE_READONLY (var) = 0;
  DECL_ARTIFICIAL (var) = 1;
  DECL_IGNORED_P (var) = 1;
  TREE_STATIC (var) = 1;
  TREE_USED (var) = 1;
  DECL_VISIBILITY (var) = VISIBILITY_HIDDEN;
  DECL_INITIAL (var) = init;

  varpool_node::finalize_decl (var);
  return var;
}

static tree
create_static_variable (const char *name, tree init, bool is_volatile = false)
{
  return create_static_variable (name, TREE_TYPE (init), init, is_volatile);
}

/* Build a static array to hold pure function table composed by TARGETS.  */

static tree
build_target_function_table (vec<cgraph_node *> &targets, tree entry_type)
{
  tree table_type = build_array_type_nelts (entry_type, targets.length ());
  vec<constructor_elt, va_gc> *entries;
  cgraph_node *target;
  unsigned i;

  gcc_checking_assert (POINTER_TYPE_P (entry_type));

  vec_alloc (entries, targets.length ());

  FOR_EACH_VEC_ELT (targets, i, target)
    CONSTRUCTOR_APPEND_ELT (entries, NULL_TREE,
			    build1 (ADDR_EXPR, entry_type, target->decl));

  tree table_init = build_constructor (table_type, entries);

  TREE_CONSTANT (table_init) = 1;
  TREE_READONLY (table_init) = 1;
  TREE_STATIC (table_init) = 1;

  return create_static_variable ("__pure_fn_table", table_type, table_init);
}

#if 0
static tree
build_vptr_cache_table (unsigned count)
{
  tree entry_type = build_pointer_type (void_type_node);
  tree table_type = build_array_type_nelts (entry_type, count);
  vec<constructor_elt, va_gc> *entries;

  vec_alloc (entries, count);

  for (unsigned i = 0; i < count; i++)
    CONSTRUCTOR_APPEND_ELT (entries, NULL_TREE, build_zero_cst (entry_type));

  tree table_init = build_constructor (table_type, entries);

  TREE_STATIC (table_init) = 1;

  return create_static_variable ("__vptr_cache", table_type, table_init, true);
}
#endif

static inline void
append_to_block (basic_block bb, gimple *stmt)
{
  gimple_stmt_iterator gsi = gsi_last_bb (bb);

  gcc_checking_assert (gimple_code (stmt) != GIMPLE_PHI);
  gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);
}

static inline void
set_condition_edges (edge e_true, edge e_false, profile_probability true_prob)
{
  e_true->flags &= ~EDGE_FALLTHRU;
  e_true->flags |= EDGE_TRUE_VALUE;
  e_true->probability = true_prob;

  e_false->flags &= ~EDGE_FALLTHRU;
  e_false->flags |= EDGE_FALSE_VALUE;
  e_false->probability = true_prob.invert ();
}

static inline void
set_immediate_dominator (basic_block bb, basic_block dom_bb)
{
  if (dom_info_available_p (CDI_DOMINATORS))
    set_immediate_dominator (CDI_DOMINATORS, bb, dom_bb);
}

/* Generate code to lookup VALUE in table via a loop, which will be inserted
   at edge E_INSERT.  Block containing result of lookup is recorded in
   BB_RESULT_PTR.  */

static tree
generate_table_lookup (tree value, tree table, tree vuse, edge e_insert,
		       basic_block *bb_result_ptr)
{
  basic_block bb_result = split_edge (e_insert);
  basic_block bb_latch = split_edge (e_insert);
  basic_block bb_header = split_edge (e_insert);
  basic_block bb_preheader = split_edge (e_insert);
  edge e_entry = single_succ_edge (bb_preheader);
  edge e_incre = single_succ_edge (bb_header);
  edge e_break = single_succ_edge (bb_latch);
  edge e_found = make_edge (bb_header, bb_result, 0);
  edge e_latch = make_edge (bb_latch, bb_header, 0);
  tree index_0 = make_ssa_name (sizetype);
  tree index_1 = make_ssa_name (sizetype);
  tree element = make_ssa_name (TREE_TYPE (value));
  tree result = make_ssa_name (boolean_type_node);

  set_immediate_dominator (bb_result, bb_header);

  /* Generate statements in loop header.  */

  gphi *index_phi = create_phi_node (index_0, bb_header);

  add_phi_arg (index_phi, size_int (0), e_entry, UNKNOWN_LOCATION);
  add_phi_arg (index_phi, index_1, e_latch, UNKNOWN_LOCATION);

  gcc_checking_assert (VAR_P (table));

  unsigned table_size = CONSTRUCTOR_NELTS (DECL_INITIAL (table));
  tree array_ref = build4 (ARRAY_REF, TREE_TYPE (value), table, index_0,
			   NULL_TREE, NULL_TREE);
  gimple *load = gimple_build_assign (element, array_ref);
  profile_probability found_prob
    = profile_probability::guessed_always ().apply_scale (1, table_size);

  gimple_set_vuse (load, vuse);
  append_to_block (bb_header, load);
  append_to_block (bb_header, gimple_build_cond (EQ_EXPR, value, element,
						 NULL_TREE, NULL_TREE));
  set_condition_edges (e_found, e_incre, found_prob);

  /* Generate statements to form loop latch.  */

  tree plus_one = size_binop (PLUS_EXPR, index_0, size_int (1));
  profile_probability break_prob = profile_probability::always ();

  if (table_size > 1)
    break_prob = break_prob.apply_scale (1, table_size - 1);

  append_to_block (bb_latch, gimple_build_assign (index_1, plus_one));
  append_to_block (bb_latch,
		   gimple_build_cond (EQ_EXPR, index_1, size_int (table_size),
				      NULL_TREE, NULL_TREE));
  set_condition_edges (e_break, e_latch, break_prob);

  /* Generate result statement in loop exit.  */

  gphi *result_phi = create_phi_node (result, bb_result);

  add_phi_arg (result_phi, boolean_true_node, e_found, UNKNOWN_LOCATION);
  add_phi_arg (result_phi, boolean_false_node, e_break, UNKNOWN_LOCATION);

  *bb_result_ptr = bb_result;

  /* Notify pass manager to construct loop structure.  */
  loops_state_set (LOOPS_NEED_FIXUP);

  return result;
}

/*
   Generate following sequence of code that is meant to update pure flag at
   runtime.
*/

static void
generate_dynamic_pure_flag_update (tree target_table, tree vptr_cache,
				   tree is_pure_flag,
				   tree vcall_object,
				   tree vptr_expr,
				   unsigned HOST_WIDE_INT vcall_token,
				   gimple *stmt_to_insert)
{
  /* Function to insert dynamic code on pure flag may not be the function
     to be applied CSO transformation.  Since update_ssa() could not work
     properly for more than one function bodies at same time, here we will
     manually generate all things around both normal and virtual SSA web.  */
  tree vuse = gimple_vuse (stmt_to_insert);
  basic_block bb_check = gimple_bb (stmt_to_insert);
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt_to_insert);
  edge e_insert
    = split_block (bb_check, (gsi_prev_nondebug (&gsi), gsi_stmt (gsi)));

  gcc_checking_assert (vuse && gimple_vdef (stmt_to_insert));

  /*  Generate statements in bb_check_valid_obj.  */
  basic_block bb_join = e_insert->dest;
  basic_block bb_check_valid_obj = split_edge (e_insert);
  edge e_then_check_valid_obj = single_succ_edge (bb_check_valid_obj);
  basic_block bb_check_is_pure = split_edge (e_then_check_valid_obj);
  edge e_else_check_valid_obj = make_edge (bb_check_valid_obj, bb_join, 0);
  tree null_object = build_zero_cst (TREE_TYPE (vcall_object));

  /* Adjust dominator conveniently.  */
  set_immediate_dominator (bb_join, bb_check_valid_obj);

  append_to_block (bb_check_valid_obj,
		   gimple_build_cond (NE_EXPR, vcall_object, null_object,
				      NULL_TREE, NULL_TREE));

  set_condition_edges (e_then_check_valid_obj, e_else_check_valid_obj,
		       profile_probability::likely ());

  /*  Generate statements in bb_check_is_pure.  */
  edge e_then_check_is_pure = single_succ_edge (bb_check_is_pure);
  basic_block bb_check_vptr_cache = split_edge (e_then_check_is_pure);
  edge e_else_check_is_pure = make_edge (bb_check_is_pure, bb_join, 0);
  tree is_pure_zero = build_zero_cst (TREE_TYPE (is_pure_flag));
  tree ssa_is_pure = make_ssa_name (TREE_TYPE (is_pure_flag));
  gimple *load_is_pure = gimple_build_assign (ssa_is_pure, is_pure_flag);

  gimple_set_vuse (load_is_pure, vuse);
  append_to_block (bb_check_is_pure, load_is_pure);
  append_to_block (bb_check_is_pure,
		   gimple_build_cond (NE_EXPR, ssa_is_pure, is_pure_zero,
				      NULL_TREE, NULL_TREE));
  set_condition_edges (e_then_check_is_pure, e_else_check_is_pure,
		       profile_probability::very_likely ());

  /* Generate statements in bb_check_vptr_cache.  */
  edge e_then_check_vptr_cache = single_succ_edge (bb_check_vptr_cache);
  basic_block bb_check_null_cache = split_edge (e_then_check_vptr_cache);
  edge e_else_check_vptr_cache = make_edge (bb_check_vptr_cache, bb_join, 0);
  tree vptr_type = TREE_TYPE (vptr_cache);
  tree ssa_vptr = make_ssa_name (vptr_type);
  tree ssa_vptr_cache = make_ssa_name (vptr_type);
  gimple *load_vptr = gimple_build_assign (ssa_vptr, vptr_expr);
  gimple *load_vptr_cache = gimple_build_assign (ssa_vptr_cache, vptr_cache);

  gimple_set_vuse (load_vptr, vuse);
  gimple_set_vuse (load_vptr_cache, vuse);
  append_to_block (bb_check_vptr_cache, load_vptr);
  append_to_block (bb_check_vptr_cache, load_vptr_cache);
  append_to_block (bb_check_vptr_cache,
		   gimple_build_cond (NE_EXPR, ssa_vptr, ssa_vptr_cache,
				      NULL_TREE, NULL_TREE));
  set_condition_edges (e_then_check_vptr_cache, e_else_check_vptr_cache,
		       profile_probability::very_unlikely ());

  /* Generate statements in bb_check_null_cache.  */
  edge e_then_check_null_cache = single_succ_edge (bb_check_null_cache);
  basic_block bb_lookup_vcall = split_edge (e_then_check_null_cache);
  edge e_else_check_null_cache = make_edge (bb_check_null_cache, bb_join, 0);

  append_to_block (bb_check_null_cache,
		   gimple_build_cond (EQ_EXPR, ssa_vptr_cache,
				      build_zero_cst (vptr_type), NULL_TREE,
				      NULL_TREE));
  set_condition_edges (e_then_check_null_cache, e_else_check_null_cache,
		       profile_probability::very_likely ());

  /* We could only split an edge only after its flags has been properly set. */
  basic_block bb_set_is_pure = split_edge (e_else_check_null_cache);

  /* Generate statements in bb_lookup_vcall.  */
  tree ssa_vcall = make_ssa_name (TREE_TYPE (vptr_type));
  tree offset = build_int_cst (vptr_type, vcall_token * POINTER_SIZE_UNITS);
  tree vcall_expr = build2 (MEM_REF, TREE_TYPE (vptr_type), ssa_vptr, offset);
  gimple *load_vcall = gimple_build_assign (ssa_vcall, vcall_expr);

  gimple_set_vuse (load_vcall, vuse);
  append_to_block (bb_lookup_vcall, load_vcall);

  tree ssa_found = generate_table_lookup (ssa_vcall, target_table, vuse,
					  single_succ_edge (bb_lookup_vcall),
					  &bb_lookup_vcall);
  append_to_block (bb_lookup_vcall,
		   gimple_build_cond (EQ_EXPR, ssa_found, boolean_true_node,
				      NULL_TREE, NULL_TREE));

  edge e_then_lookup_vcall = single_succ_edge (bb_lookup_vcall);
  basic_block bb_store_cache = split_edge (e_then_lookup_vcall);

  set_condition_edges (e_then_lookup_vcall,
		       make_edge (bb_lookup_vcall, bb_set_is_pure, 0),
		       profile_probability::very_likely ());

  /* Generate statements in bb_store_cache.  */
  gimple *store_cache = gimple_build_assign (vptr_cache, ssa_vptr);
  tree vdef_store_cache = copy_ssa_name (vuse, store_cache);

  gimple_set_vuse (store_cache, vuse);
  gimple_set_vdef (store_cache, vdef_store_cache);
  append_to_block (bb_store_cache, store_cache);

  /* Generate statements in bb_set_is_pure.  */
  gimple *set_is_pure = gimple_build_assign (is_pure_flag, is_pure_zero);
  tree vdef_set_is_pure = copy_ssa_name (vuse, set_is_pure);

  gimple_set_vuse (set_is_pure, vuse);
  gimple_set_vdef (set_is_pure, vdef_set_is_pure);
  append_to_block (bb_set_is_pure, set_is_pure);

  /* Generate virtual SSA merge PHI in bb_join.  */
  gphi *new_vphi = create_phi_node (SSA_NAME_VAR (vuse), bb_join);

  add_phi_arg (new_vphi, vuse, e_else_check_valid_obj, UNKNOWN_LOCATION);
  add_phi_arg (new_vphi, vuse, e_else_check_is_pure, UNKNOWN_LOCATION);
  add_phi_arg (new_vphi, vuse, e_else_check_vptr_cache, UNKNOWN_LOCATION);
  add_phi_arg (new_vphi, vdef_store_cache, single_succ_edge (bb_store_cache),
	       UNKNOWN_LOCATION);
  add_phi_arg (new_vphi, vdef_set_is_pure, single_succ_edge (bb_set_is_pure),
	       UNKNOWN_LOCATION);

  SET_USE (gimple_vuse_op (stmt_to_insert), gimple_phi_result (new_vphi));
}

/* For a class OBJECT expression that belongs to one function, and a virtual
   function VCALL_FN expression belonging to another one, build a memref
   to get vtable address from OBJECT, which follows generation of vtable
   address used by VCALL_FN as template.  */

static tree
generate_vptr_load_for_object (tree object, tree vcall_fn)
{
  tree otr_type = obj_type_ref_class (vcall_fn);
  tree field = NULL_TREE;

  for (field = TYPE_FIELDS (otr_type); field; )
    {
      tree field_type = TREE_TYPE (field);

      if (DECL_VIRTUAL_P (field))
	{
	  gcc_assert (POINTER_TYPE_P (field_type));
	  break;
	}

      gcc_assert (DECL_ARTIFICIAL (field)
		  && TREE_CODE (field_type) == RECORD_TYPE);

      field = TYPE_FIELDS (field_type);
    }

  gcc_assert (field);

  tree mref_type = build_qualified_type (DECL_CONTEXT (field),
					 TYPE_QUAL_CONST);
  tree vtbl_expr;

  if (TREE_CODE (TREE_TYPE (object)) == POINTER_TYPE)
    mref_type = build_pointer_type (mref_type);
  else
    mref_type = build_reference_type (mref_type);

  vtbl_expr = build2 (MEM_REF, TREE_TYPE (mref_type), object,
		      build_zero_cst (mref_type));
  vtbl_expr = build3 (COMPONENT_REF, TREE_TYPE (field), vtbl_expr,
		      field, NULL_TREE);
  return vtbl_expr;
}

static tree
generate_dynamic_pure_flag (purify_call_info *info)
{
  if (info->is_pure_flag)
    return info->is_pure_flag;

  tree insert_param = SSA_NAME_VAR (info->vcall_object_source);
  cfun_context fn_context (DECL_CONTEXT (insert_param));

  tree vptr_expr = generate_vptr_load_for_object (info->vcall_object_source,
						  info->vcall_fn);
  tree vptr_type = TREE_TYPE (vptr_expr);
  tree vptr_cache
    = create_static_variable ("__vptr_cache", build_zero_cst (vptr_type), true);
  tree target_table
    = build_target_function_table (info->vcall_targets, TREE_TYPE (vptr_type));

  /* Initialize "__is_pure_flag" to 1, since expansion of vector field
     starts from empty state.   */
  tree is_pure_type = integer_type_node;
  tree is_pure_flag
    = create_static_variable (IS_PURE_FLAG_PREFIX, build_one_cst (is_pure_type),
			      true);

  unsigned HOST_WIDE_INT vcall_token
		= tree_to_uhwi (OBJ_TYPE_REF_TOKEN (info->vcall_fn));
  unsigned i;
  gimple *stmt;

  FOR_EACH_VEC_ELT (info->check_points, i, stmt)
    {
      if (i)
	vptr_expr = unshare_expr (vptr_expr);

      generate_dynamic_pure_flag_update (target_table, vptr_cache,
					 is_pure_flag,
					 info->vcall_object_source,
					 vptr_expr, vcall_token, stmt);
    }

  info->is_pure_flag = is_pure_flag;
  return is_pure_flag;
}

/* For a possible partially pure GCALL_ORIGIN statement, do versioning on
   the function called as the following:
   (1) Clone all blocks in CSO_BLOCKS_QUALIFIED.
   (2) Generate a dynamic check to switch between the versions with and without
   CSO applied.

     if (__is_pure_flag == true)
       cso_region_origin, which is to call gcall_cloned.
     else
       cso_region_cloned, which is to call gcall_origin.

   The CSO transformation will be applied to cso_region_origin, and we expect
   the gcall_cloned will be optimized after CSO.  */

static bool
generate_dynamic_pure_call (gimple *gcall_origin,
			    const vec<basic_block> &cso_blocks_qualified)
{
  gimple *gcall_cloned;
  unsigned i, j;
  basic_block cb;
  basic_block cso_candidate = gimple_bb (gcall_origin);

  /* Get the block prior to CSO region. */
  edge cso_edge_origin = EDGE_PRED (cso_candidate, 0);
  edge cso_edge_cloned;
  basic_block prior_cso_bb = cso_edge_origin->src;
  cgraph_edge *cs;

  /* Step 1: Clone the function called in cso_candidate block.

     WARNING: We have to do this clone before cloning all basic blocks in cso
     region, otherwise gcc may fail in update_ssa. This is because the
     update_ssa facility can't handle two different functions simultaneously,
     i.e. the function to be cloned and the function on which we will apply CSO.
     Before doing this clone, CSO doesn't have any real SSA changes in CSO
     algorithm yet, so it won't break function clone operation below.  */

  tree fndecl_origin = gimple_call_fndecl (gcall_origin);

  gcc_checking_assert (fndecl_origin != NULL_TREE);

  cgraph_node *old_callee_node = cgraph_node::get (fndecl_origin);
  cgraph_node *new_callee_node, *caller_node;
  purify_call_info *info = (purify_call_info *) old_callee_node->aux;

  if (!info->clone)
    {
      new_callee_node = old_callee_node->create_version_clone_with_body (
	    vNULL, NULL, NULL, NULL, NULL, CSO_CLONED_FUNC_SUFFIX, NULL);
      gcc_assert (new_callee_node != NULL);
      info->clone = new_callee_node;

      /* Mark the virtual function calls in cloned callee as PURE.

	 We expect the optimization passes after IPA CSO could simplify the
	 cloned callee and eventually it can be identified as a pure function.
	 This way, the true path after the dynamic check we just inserted will
	 always be valid with CSO applied.

	 If this cloned callee can't be identified as a pure function finally,
	 we will give it up in IPA CSO FIXUP pass by changing the dynamic
	 check condition (__is_pure_flag == true) to be (false). Then, the
	 true path will be removed by DCE pass after, and CSO transformation
	 will be reverted automatically.

	 Please note that, no matter how the passes after IPA CSO will behave,
	 we always statically apply CSO transformation to the code on true
	 path.  */
      for (cs = new_callee_node->indirect_calls; cs; cs = cs->next_callee)
	{
	  gimple *call_stmt = cs->call_stmt;
	  tree call_fn = gimple_call_fn (call_stmt);

	  if (!virtual_method_call_p (call_fn))
	    continue;

	  if (!same_virtual_method_call_p (call_fn, info->vcall_fn))
	    continue;

	  /* Assume the vcall is pure.  */
	  gimple_call_set_pure (as_a<gcall *> (call_stmt), true);

	  /* Assume no exception throw for the vcall.  */
	  gimple_call_set_nothrow (as_a<gcall *> (call_stmt), true);

	  /* Clear virtual definition operand of the vcall.  */
	  update_stmt_fn (DECL_STRUCT_FUNCTION (new_callee_node->decl),
			  call_stmt);

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "> CSO: Assume pure and nothrow for ");
	      print_gimple_stmt (dump_file, call_stmt, 0, TDF_SLIM);
	    }
	}
    }
  else
    new_callee_node = info->clone;

  tree fndecl_cloned = new_callee_node->decl;

  /* Step 2: Clone all blocks in cso_blocks_qualified and cso_candidate. */

  unsigned n = cso_blocks_qualified.length () + 1;
  initialize_original_copy_tables ();

  basic_block *cso_region_origin = XNEWVEC (basic_block, n);
  basic_block *cso_region_cloned = XNEWVEC (basic_block, n);

  cso_region_origin[0] = cso_candidate;
  FOR_EACH_VEC_ELT (cso_blocks_qualified, i, cb)
    cso_region_origin[i + 1] = cb;

  gcc_checking_assert ((i + 1) == n);

  /* Clone all blocks in cso_region_origin into cso_region_cloned. Record the
     cloned CSO entry edge into cso_edge_cloned. */
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> CSO: Before cloning blocks\n");
      for (j = 0; j < n; j++)
	{
	  gimple_dump_bb (dump_file, cso_region_origin[j], 0, TDF_SLIM);
	  fprintf (dump_file, "\n");
	}
    }

  copy_bbs (cso_region_origin, n, cso_region_cloned, NULL, 0, NULL,
	    prior_cso_bb->loop_father, prior_cso_bb, true);
  add_phi_args_after_copy (cso_region_cloned, n, NULL);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> CSO: After cloning blocks\n");
      for (i = 0; i < n; i++)
	{
	  gimple_dump_bb (dump_file, cso_region_cloned[i], 0, TDF_SLIM);
	  fprintf (dump_file, "\n");
	}
    }

  /* Step 3: Adjust some function declarations and cgraph edges. */

  /* Change the declaration of the callee in original cso_candidate block to
     be the clone one. */

  gimple_call_set_fndecl (gcall_origin, fndecl_cloned);

  /* Update cgraph node edge from caller to original callee by setting callee
     stmt in the edge to be the cloned gcall stmt. */

  gcall_cloned = first_stmt (cso_region_cloned[0]);
  gcc_checking_assert (gcall_cloned && is_gimple_call (gcall_cloned));

  caller_node = cgraph_node::get (current_function_decl);
  cs = caller_node->get_edge (gcall_origin);
  cs->set_call_stmt (cs, as_a<gcall *> (gcall_cloned));

  /* Create a new cgraph node edge from caller to new callee and set the callee
     stmt to be the original gcall stmt. */
  caller_node->create_edge (new_callee_node, as_a<gcall *> (gcall_origin),
			    profile_count::zero ());

  /* Step 4: Generate an if statement for dynamic check . */

  /* The true path is for cso_edge_origin, because this way the CSO
     transformation algorithm after will always work on cso_blocks_qualified.
   */

  tree is_pure_flag = generate_dynamic_pure_flag (info);
  tree is_pure_type = TREE_TYPE (is_pure_flag);
  tree ssa_is_pure = make_ssa_name (is_pure_type);

  append_to_block (prior_cso_bb,
		   gimple_build_assign (ssa_is_pure, is_pure_flag));
  append_to_block (prior_cso_bb,
		   gimple_build_cond (NE_EXPR, ssa_is_pure,
				      build_zero_cst (is_pure_type), NULL_TREE,
				      NULL_TREE));

  cso_edge_cloned = make_edge (prior_cso_bb, cso_region_cloned[0], 0);
  set_condition_edges (cso_edge_origin, cso_edge_cloned,
		       profile_probability::guessed_always ());

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> CSO: Dynamic check is generated\n");
      gimple_dump_bb (dump_file, prior_cso_bb, 0, TDF_SLIM);
      fprintf (dump_file, "\n");
      gimple_dump_bb (dump_file, cso_edge_origin->dest, 0, TDF_SLIM);
      fprintf (dump_file, "\n");
      gimple_dump_bb (dump_file, cso_edge_cloned->dest, 0, TDF_SLIM);
    }

  free_original_copy_tables ();
  free (cso_region_origin);
  free (cso_region_cloned);

  return true;
}

static bool
check_call_in_cso_candidate (basic_block cso_candidate,
			     const vec<basic_block> &cso_blocks_qualified,
			     bool allow_dynamic_pure)
{
  gimple *stmt = first_stmt (cso_candidate);

  /* Check the CSO region should have only one predecessor and hot function
     call in cso_candidate. */
  gcc_checking_assert (single_pred_p (cso_candidate));
  gcc_checking_assert (is_gimple_call (stmt));

  if (allow_dynamic_pure)
    {
      if (!gimple_has_side_effects (stmt))
	return false;

      if (!call_is_partially_pure_p (stmt))
	return false;

      generate_dynamic_pure_call (stmt, cso_blocks_qualified);
    }
  else
    {
      if (!true /* !is_expensive_call (gcall_origin) */)
	return false;
    }

  return true;
}

/* Return true if BB is a condition block which requires,
   (1) Has two outgoing edges.
   (2) For all stmts, LHS is either none or SSA.
   (3) The call stmt inside the block is expensive.

   Set SPLIT_POS to the stmt that may either introduce side effect or PHI.  */

static bool
is_condition_block_as_cso_candidate (basic_block bb, gimple *&split_pos,
				     bool allow_dynamic_pure)
{
  gimple_stmt_iterator gsi;
  gimple *stmt;
  tree lhs;

  if (EDGE_COUNT (bb->succs) != 2)
    return false;

  /* Skip the last stmt. */
  gsi = gsi_last_bb (bb);
  stmt = gsi_stmt (gsi);
  if (gimple_code (stmt) != GIMPLE_COND)
    return false;
  gsi_prev (&gsi);

  /* Scan all stmts backward. */
  split_pos = NULL;
  for (; !gsi_end_p (gsi); gsi_prev (&gsi))
    {
      stmt = gsi_stmt (gsi);

      if (is_gimple_debug (stmt))
	continue;
      else if (is_gimple_call (stmt))
	{
	  lhs = gimple_call_lhs (stmt);

	  /* Apart from cond stmt, only SSA definition is allowed. */
	  if (lhs && TREE_CODE (lhs) != SSA_NAME)
	    return false;

	  if (!allow_dynamic_pure && gimple_has_side_effects (stmt))
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (
		    dump_file,
		    "> CSO: A side-effect call can't be in CSO candidate block ");
		  print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
		}
	      return false;
	    }

	  gimple *nop = gimple_build_nop ();
	  gsi_insert_before (&gsi, nop, GSI_SAME_STMT);
	  split_pos = nop;
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "> CSO: Found call in CSO candidate block ");
	      print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
	    }
	  return true;
	}
      else if (gimple_code (stmt) == GIMPLE_ASSIGN)
	{
	  lhs = gimple_assign_lhs (stmt);

	  /* Apart from cond stmt, only SSA definition is allowed. */
	  if (TREE_CODE (lhs) != SSA_NAME)
	    return false;
	}
      else
	return false;
    }

  return false;
}

/* Return the CSO_TARGET basic block if BB is a cso candidate.  */

static basic_block
is_cso_candidate (basic_block bb, basic_block *cso_target, gimple *split_pos)
{
  basic_block condition_bb;
  gimple_stmt_iterator gsi;
  gimple *stmt;
  tree lhs;

  /* A block with outgoing loop back edge can't be a cso candidate. */
  edge e1 = EDGE_SUCC (bb, 0);
  edge e2 = EDGE_SUCC (bb, 1);
  if (e1->flags & EDGE_DFS_BACK)
    return NULL;
  if (e2->flags & EDGE_DFS_BACK)
    return NULL;

  /* One of the two outgoing edges is a critical edge, and the other is not. */
  bool e1_is_critical = EDGE_CRITICAL_P (e1);
  bool e2_is_critical = EDGE_CRITICAL_P (e2);
  if (!(e1_is_critical ^ e2_is_critical))
    return NULL;

  /* All defs except condition stmt must be used inside the block. */
  gsi = gsi_last_bb (bb);
  gsi_prev (&gsi);
  for (; !gsi_end_p (gsi); gsi_prev (&gsi))
    {
      stmt = gsi_stmt (gsi);

      if (is_gimple_debug (stmt))
	continue;

      /* Don't check further beyond split_pos. */
      if (split_pos && split_pos == stmt)
	break;

      if (!(lhs = gimple_get_lhs (stmt)))
	continue;

      /* All SSAs defined in condition_bb are only used by condition_bb
	 itself. */
      gimple *use_stmt;
      imm_use_iterator use_iter;
      FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, lhs)
	{
	  basic_block use_bb = gimple_bb (use_stmt);
	  if (use_bb != bb)
	    return NULL;
	}
    }

  /* Warning: CSO may still fail even if we split the block. */
  if (split_pos)
    {
      /* Split block after split_pos. */
      edge e = split_block (bb, split_pos);
      condition_bb = e->dest;
      // clear_vdef_vuse (e->src);
      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "> CSO: Split block #%d to gen #%d\n", bb->index,
		 condition_bb->index);
    }
  else
    condition_bb = bb;

  *cso_target = e1_is_critical ? e1->dest : e2->dest;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> CSO: Found candidate block #%d\n",
	       condition_bb->index);
      fprintf (dump_file, "> CSO: Found target block #%d\n",
	       (*cso_target)->index);
    }

  return condition_bb;
}

/* Check whether MEMREF0 and MEMREF1 are from same struct/class object.  */

static bool
has_same_component_base_p (const tree memref0, const tree memref1)
{
  enum tree_code code0 = TREE_CODE (memref0);
  enum tree_code code1 = TREE_CODE (memref1);

  /* TODO: Two loads may root to different inner objects of same struct/class
     (e.g.  base->arr[3].f1 and base->f2).  */
  if (code0 != COMPONENT_REF && code0 != BIT_FIELD_REF && code0 != REALPART_EXPR
      && code0 != IMAGPART_EXPR)
    return false;

  if (code1 != COMPONENT_REF && code1 != BIT_FIELD_REF && code1 != REALPART_EXPR
      && code1 != IMAGPART_EXPR)
    return false;

  return operand_equal_p (TREE_OPERAND (memref0, 0), TREE_OPERAND (memref1, 0),
			  OEP_ADDRESS_OF);
}

static bool
check_mem_alias (gimple *stmt, tree mem)
{
  if (gimple_assign_load_p (stmt))
    {
      tree mem1 = gimple_assign_rhs1 (stmt);
      if (has_same_component_base_p (mem, mem1))
	return true;
    }
  else if (gimple_store_p (stmt))
    {
      tree mem1 = gimple_get_lhs (stmt);
      if (has_same_component_base_p (mem, mem1))
	return true;
    }

  return false;
}

/* Return true if we can find a dominating stmt that access the same memory as
   the one being loaded in STMT.  */

static bool
find_dominating_mem (const gimple *stmt)
{
  imm_use_iterator vuse_iter;
  tree mem, vdef, vuse;
  gimple *vdef_stmt, *vuse_stmt;

  vuse = gimple_vuse (stmt);
  mem = gimple_assign_rhs1 (stmt);
  auto_vec<tree> worklist;

  worklist.safe_push (vuse);
  auto_bitmap visited;
  do
    {
      vuse = worklist.pop ();

      if (SSA_NAME_IS_DEFAULT_DEF (vuse))
	continue;

      vdef_stmt = SSA_NAME_DEF_STMT (vuse);

      if (gimple_code (vdef_stmt) == GIMPLE_PHI)
	vdef = gimple_phi_result (vdef_stmt);
      else
	{
	  vdef = gimple_vdef (vdef_stmt);
	  gcc_checking_assert (vdef != NULL_TREE);

	  if (check_mem_alias (vdef_stmt, mem))
	    return true;
	}

      FOR_EACH_IMM_USE_STMT (vuse_stmt, vuse_iter, vdef)
	{
	  if (vuse_stmt == stmt)
	    continue;

	  /* It's impossible that this PHI dominates mem.  */
	  if (gimple_code (vuse_stmt) == GIMPLE_PHI)
	    continue;

	  if (!dom_info_available_p (CDI_DOMINATORS))
	    calculate_dominance_info (CDI_DOMINATORS);
	  if (!dominated_by_p (CDI_DOMINATORS, gimple_bb (stmt),
			       gimple_bb (vuse_stmt)))
	    continue;

	  if (check_mem_alias (vuse_stmt, mem))
	    return true;
	}

      if (gimple_code (vdef_stmt) == GIMPLE_PHI)
	{
	  for (unsigned int i = 0; i < gimple_phi_num_args (vdef_stmt); ++i)
	    if (bitmap_set_bit (visited, gimple_uid (vdef_stmt)))
	      worklist.safe_push (PHI_ARG_DEF (vdef_stmt, i));
	}
      else if (bitmap_set_bit (visited, gimple_uid (vdef_stmt)))
	worklist.safe_push (gimple_vuse (vdef_stmt));
    }
  while (!worklist.is_empty ());

  return false;
}

/* Return true if a load from a _vptr or _vtbl field. E.g.
   (1) _229 = _228->D.4992._vptr.Base
   (2) _230 = MEM[(int (*__vtbl_ptr_type) () *)_229 + 50B];  */

static bool
vptr_field_load_p (gimple *stmt)
{
  if (!gimple_assign_single_p (stmt))
    return false;

  tree rhs = gimple_assign_rhs1 (stmt);

  if (TREE_CODE (rhs) == MEM_REF)
    {
      tree base = TREE_OPERAND (rhs, 0);

      if (!FUNCTION_POINTER_TYPE_P (TREE_TYPE (rhs))
	  || TREE_CODE (base) != SSA_NAME)
	return false;

      stmt = SSA_NAME_DEF_STMT (base);
    }

  return load_vptr_p (stmt);
}

/* Return false, if there exists a memory load inside CSO_BLOCKS_QUALIFIED that
   does not have any dominating memory access outside.  */

static bool
cso_blocks_no_trap (const auto_vec<basic_block> &cso_blocks_qualified,
		    bool safe_vptr)
{
  unsigned i;
  basic_block cb;

  FOR_EACH_VEC_ELT (cso_blocks_qualified, i, cb)
    {
      gimple_stmt_iterator gsi;
      gimple *stmt;
      tree lhs;

      for (gsi = gsi_start_bb (cb); !gsi_end_p (gsi); gsi_next (&gsi))
	{
	  stmt = gsi_stmt (gsi);

	  if (is_gimple_debug (stmt))
	    continue;

	  if (!gimple_assign_load_p (stmt))
	    continue;

	  lhs = gimple_assign_lhs (stmt);
	  gcc_checking_assert (TREE_CODE (lhs) == SSA_NAME);

	  if (!find_dominating_mem (stmt))
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file,
			   "> CSO: Found memory may trap after cso! ");
		  print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
		}

	      if (safe_vptr && vptr_field_load_p (stmt))
		{
		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (
			dump_file,
			"> CSO: Assume safe to load _vptr or _vtbl field!\n");
		    }
		}
	      else
		return false;
	    }
	  else
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file,
			   "> CSO: Found dominating memory access for ");
		  print_gimple_stmt (dump_file, stmt, 0, TDF_SLIM);
		}
	    }
	}
    }
  return true;
}

/* Parse all blocks backward starting from CSO_TARGET to find all basic blocks
   that might be on cso paths.  */

static void
find_cso_blocks (basic_block cso_candidate, basic_block cso_target,
		 auto_vec<basic_block> &cso_blocks)
{
  auto_vec<basic_block> worklist;
  edge_iterator ei;
  edge pred;
  unsigned i;
  basic_block cb;
  edge e1, e2;

  e1 = find_edge (cso_candidate, cso_target);

  /* Add the cso target to cso_blocks. The cso candidate is excluded. */
  cso_blocks.safe_push (cso_target);
  worklist.safe_push (cso_target);
  do
    {
      basic_block cso_bb = worklist.pop ();

      /* Check all preds to find new cso blocks. */
      FOR_EACH_EDGE (pred, ei, cso_bb->preds)
	{
	  if (pred->flags & EDGE_DFS_BACK)
	    continue;

	  /* Skip cso blocks we have identified. */
	  basic_block pred_bb = pred->src;
	  if (pred_bb == cso_candidate)
	    continue;
	  if (cso_blocks.contains (pred_bb))
	    continue;

	  /* The cso candidate must dominate all other cso blocks. */
	  if (!dom_info_available_p (CDI_DOMINATORS))
	    calculate_dominance_info (CDI_DOMINATORS);
	  if (!dominated_by_p (CDI_DOMINATORS, pred_bb, cso_candidate))
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "> CSO: #%d is not dominated by #%d!\n",
			   pred_bb->index, cso_candidate->index);
		}
	      continue;
	    }

	  /* The condition block on cso path should not be expensive and does
	     not have side effects. */
	  if (!is_condition_block_on_cso_path (pred_bb))
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file,
			   "> CSO: #%d is not a condition block on cso path!\n",
			   pred_bb->index);
		}
	      continue;
	    }

	  /* In cso_target, all PHIs coming from pred_bb must be the same as
	     from cso_candidate. */
	  e2 = find_edge (pred_bb, cso_target);
	  if (e2 != NULL)
	    {
	      bool phi_arg_is_same = true;
	      for (gphi_iterator gpi = gsi_start_phis (cso_target);
		   !gsi_end_p (gpi); gsi_next (&gpi))
		{
		  gphi *phi = gpi.phi ();
		  tree arg1 = gimple_phi_arg (phi, e1->dest_idx)->def;
		  tree arg2 = gimple_phi_arg (phi, e2->dest_idx)->def;

		  if (!virtual_operand_p (PHI_RESULT (phi))
		      && !operand_equal_p (arg1, arg2, 0))
		    {
		      if (dump_file && (dump_flags & TDF_DETAILS))
			{
			  fprintf (dump_file,
				   "> CSO: Different PHI values detected! ");
			  print_gimple_stmt (dump_file, phi, 0, TDF_SLIM);
			}
		      phi_arg_is_same = false;
		      break;
		    }
		}
	      if (!phi_arg_is_same)
		continue;
	    }

	  cso_blocks.safe_push (pred_bb);
	  worklist.safe_push (pred_bb);
	}
    }
  while (!worklist.is_empty ());

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> CSO: Found cso blocks");
      FOR_EACH_VEC_ELT (cso_blocks, i, cb)
	fprintf (dump_file, " #%d", cb->index);
      fprintf (dump_file, "\n");
    }
}

/* Within the CFG consisting of cso blocks only, if a block can be reached by
   CSO_CANDIDATE, we add it to CSO_BLOCKS_QUALIFIED.  */

static bool
find_cso_blocks_qualified (basic_block cso_candidate, basic_block cso_target,
			   const auto_vec<basic_block> &cso_blocks,
			   auto_vec<basic_block> &cso_blocks_qualified)
{
  auto_vec<basic_block> worklist;
  edge_iterator ei;
  edge succ;
  unsigned i;
  basic_block cb;

  worklist.safe_push (cso_candidate);
  do
    {
      basic_block cso_bb = worklist.pop ();

      FOR_EACH_EDGE (succ, ei, cso_bb->succs)
	{
	  basic_block succ_bb = succ->dest;

	  /* Don't add any block that can't be reached backward. */
	  if (!cso_blocks.contains (succ_bb))
	    continue;

	  /* Don't add the block that already exists. */
	  if (cso_blocks_qualified.contains (succ_bb))
	    continue;

	  /* Don't add cso target block. */
	  if (succ_bb == cso_target)
	    continue;

	  cso_blocks_qualified.safe_push (succ_bb);
	  worklist.safe_push (succ_bb);
	}
    }
  while (!worklist.is_empty ());

  if (cso_blocks_qualified.is_empty ())
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "> CSO: Can't find a qualified CSO path!\n");

      return false;
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> CSO: Found qualified cso blocks");
      FOR_EACH_VEC_ELT (cso_blocks_qualified, i, cb)
	fprintf (dump_file, " #%d", cb->index);
      fprintf (dump_file, "\n");
    }

  return true;
}

/* Find the edges connecting cso paths in CSO_BLOCKS_QUALIFIED and other blocks
   outside, and insert a duplicated CSO_CANDIDATE on the each edge.  */

static void
cso_transform_cfg (basic_block cso_candidate, basic_block cso_target,
		   const auto_vec<basic_block> &cso_blocks_qualified)
{
  unsigned i;
  basic_block cb;
  edge_iterator ei;
  edge succ;

  initialize_original_copy_tables ();
  FOR_EACH_VEC_ELT (cso_blocks_qualified, i, cb)
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "> CSO: Handle block #%d\n", cb->index);

      cb->flags |= BB_VISITED;
      basic_block cloned_bb;
      FOR_EACH_EDGE (succ, ei, cb->succs)
	{
	  basic_block succ_bb = succ->dest;
	  if (cso_blocks_qualified.contains (succ_bb) || succ_bb == cso_target)
	    continue;

	  basic_block empty_bb = split_edge (succ);
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    fprintf (dump_file, "> CSO: Split edge #%d->#%d to gen #%d\n",
		     cb->index, succ_bb->index, empty_bb->index);

	  /* Insert cloned copy of cso candidate on this edge. */
	  cloned_bb = duplicate_block (cso_candidate, succ, cb);
	  cloned_bb->flags |= BB_DUPLICATED;

	  /* Redirect the edge that doesn't connect cso_target. */
	  edge e1 = EDGE_SUCC (cloned_bb, 0);
	  edge e2 = EDGE_SUCC (cloned_bb, 1);
	  if (e1->dest == cso_target)
	    redirect_edge_succ (e2, empty_bb);
	  else if (e2->dest == cso_target)
	    redirect_edge_succ (e1, empty_bb);
	  else
	    gcc_unreachable ();

	  /* Add phis to the succs of cloned_bb, which must have been marked
	     with flag BB_DUPLICATED at cloning bb time. */
	  add_phi_args_after_copy_bb (cloned_bb);
	  cloned_bb->flags &= ~BB_DUPLICATED;

	  /* Avoid to check the cloned_bb later again. */
	  cloned_bb->flags |= BB_VISITED;

	  /* Update domination correctly. */
	  if (dom_info_available_p (CDI_DOMINATORS))
	    {
	      set_immediate_dominator (CDI_DOMINATORS, cloned_bb, cb);
	      if (get_immediate_dominator (CDI_DOMINATORS, empty_bb) == cb)
		set_immediate_dominator (CDI_DOMINATORS, empty_bb, cloned_bb);
	    }

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "> CSO: Clone block #%d to gen #%d\n",
		       cso_candidate->index, cloned_bb->index);
	      fprintf (dump_file,
		       "> CSO: Insert block #%d between #%d and #%d\n",
		       cloned_bb->index, cb->index, empty_bb->index);
	    }
	}
    }

  cso_candidate->flags |= BB_VISITED;

  free_original_copy_tables ();
}

/* Force the gimple cond to be true if the false edge is to connect CSO_TARGET,
   and vice versa.  */

static void
cleanup_cso_candidate (basic_block cso_candidate, basic_block cso_target)
{
  gimple_stmt_iterator gsi;
  gimple *stmt;
  gcond *cond;
  edge te, fe;

  gsi = gsi_last_bb (cso_candidate);
  stmt = gsi_stmt (gsi);
  gcc_checking_assert (gimple_code (stmt) == GIMPLE_COND);
  cond = as_a<gcond *> (stmt);

  extract_true_false_edges_from_block (cso_candidate, &te, &fe);
  if (te->dest == cso_target)
    gimple_cond_make_false (cond);
  else if (fe->dest == cso_target)
    gimple_cond_make_true (cond);
  else
    gcc_unreachable ();

  /* Remove all dead gimples except condition stmt.  */
  gsi_prev (&gsi);
  for (; !gsi_end_p (gsi); gsi_prev (&gsi))
    gsi_remove (&gsi, true);

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "> CSO: Cleanup block #%d\n\n", cso_candidate->index);
}

unsigned int
do_cso (bool allow_dynamic_pure)
{
  basic_block bb, next_bb;
  int cso_is_done = 0;

  /* Clear all the visited flags.  */
  FOR_EACH_BB_FN (bb, cfun)
    bb->flags &= ~BB_VISITED;

  for (bb = cfun->cfg->x_entry_block_ptr->next_bb;
       bb != cfun->cfg->x_exit_block_ptr; bb = next_bb)
    {
      basic_block cso_target;
      auto_vec<basic_block> cso_blocks;
      auto_vec<basic_block> cso_blocks_qualified;
      gimple *split_pos;

      next_bb = bb->next_bb;

      if (bb->flags & BB_VISITED)
	continue;

      if (!is_condition_block_as_cso_candidate (bb, split_pos,
						allow_dynamic_pure))
	continue;

      /* Check if bb is a cso candidate. */
      if (!(bb = is_cso_candidate (bb, &cso_target, split_pos)))
	continue;

      /* Find blocks that might be on cso paths. */
      find_cso_blocks (bb, cso_target, cso_blocks);

      /* Find qualified cso blocks that can be reached by cso_candidate. */
      if (!find_cso_blocks_qualified (bb, cso_target, cso_blocks,
				      cso_blocks_qualified))
	continue;

      /* Skip if cso blocks may trap on invalid memory access. */
      if (!cso_blocks_no_trap (cso_blocks_qualified, allow_dynamic_pure))
	continue;

      /* Check code size of call in cso candidate block, and try to
	 generate versioning code for FMO case to make CSO safe.  */
      if (!check_call_in_cso_candidate (bb, cso_blocks_qualified,
					allow_dynamic_pure))
	continue;

      cso_is_done = 1;
      /* Duplicate cso candidate and insert it appropriately. */
      cso_transform_cfg (bb, cso_target, cso_blocks_qualified);

      /* Force cso candidate to go to cso path. */
      cleanup_cso_candidate (bb, cso_target);

      /* For the case triggered by FMO, we do CSO only once. */
      if (allow_dynamic_pure)
	break;
    }

  if (dom_info_available_p (CDI_DOMINATORS))
    free_dominance_info (CDI_DOMINATORS);

  if (cso_is_done)
    return TODO_cleanup_cfg | TODO_update_ssa;
  else
    return 0;
}

namespace {

const pass_data pass_data_cso = {
  GIMPLE_PASS,	 /* type */
  "cond-sinking", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_TREE_CSO,	 /* tv_id */
  0,		 /* properties_required */
  0,		 /* properties_provided */
  0,		 /* properties_destroyed */
  0,		 /* todo_flags_start */
  0,		 /* todo_flags_finish */
};

class pass_cso : public gimple_opt_pass
{
public:
  pass_cso (gcc::context *ctxt) : gimple_opt_pass (pass_data_cso, ctxt) {}

  virtual bool gate (function *) { return flag_tree_cond_sinking != 0; }
  virtual unsigned int execute (function *) { return do_cso (false); }

}; // class pass_cso

} // namespace

gimple_opt_pass *
make_pass_cso (gcc::context *ctxt)
{
  return new pass_cso (ctxt);
}

static unsigned int
do_ipa_cso ()
{
  cgraph_node *node;

  FOR_EACH_FUNCTION (node)
    {
      node->aux = NULL;

      if (!node->has_gimple_body_p () || node->inlined_to)
	continue;

      if (lookup_attribute (FMO_INSERT_FUNC_TAG, DECL_ATTRIBUTES (node->decl)))
	{
	  if (!fmo_insert_funcs)
	    fmo_insert_funcs = new auto_vec<tree> ();
	  fmo_insert_funcs->safe_push (node->decl);
	}
    }

  if (!fmo_insert_funcs)
    return 0;

  FOR_EACH_DEFINED_FUNCTION (node)
    {
      if (!node->has_gimple_body_p () || node->inlined_to)
	continue;

      if (lookup_attribute (FMO_INSERT_FUNC_TAG, DECL_ATTRIBUTES (node->decl)))
	continue;

      cfun_context context (node);

      if (do_cso (true))
	{
	  cleanup_tree_cfg (TODO_update_ssa);
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "> CSO: After IPA CSO\n");
	      dump_function_to_file (node->decl, dump_file,
				     TDF_SLIM | TDF_VOPS);
	    }
	}
    }

  FOR_EACH_FUNCTION (node)
    node->aux = NULL;

  delete fmo_insert_funcs;
  fmo_insert_funcs = NULL;

  delete purify_calls;
  purify_calls = NULL;

  return 0;
}

/* Check for calling non-pure cso-cloned functions in cso_region_origin.  */

static bool
region_has_non_pure_cloned_call (basic_block region_header)
{
  cgraph_edge *e;
  cgraph_node *current_node = cgraph_node::get (current_function_decl);

  /* Check callees whose name contain CSO_CLONED_FUNC_SUFFIX and have
   * side-effects.  */
  for (e = current_node->callees; e; e = e->next_callee)
    {
      const char *callee_name = e->callee->name ();
      if (callee_name && strstr (callee_name, CSO_CLONED_FUNC_SUFFIX)
	  && gimple_has_side_effects (e->call_stmt))
	{
	  /* Whether gcall is in current cso_region_origin.  */
	  if (!dom_info_available_p (CDI_DOMINATORS))
	    calculate_dominance_info (CDI_DOMINATORS);
	  if (dominated_by_p (CDI_DOMINATORS, e->call_stmt->bb, region_header))
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		fprintf (dump_file, "%s is not pure.\n", callee_name);
	      return true;
	    }
	}
    }
  return false;
}

/* Change STMT ("tmp = {v} is_pure_flag") into "tmp = 0".  */

static inline void
revert_cso_check_code (gimple *stmt)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Revert cso code in BB%d: changing\n\t",
	       stmt->bb->index);
      print_gimple_stmt (dump_file, stmt, 0);
    }

  /* Replace is_pure_flag with 0 in load stmt.  */
  gcc_assert (gimple_assign_load_p (stmt));
  gimple_assign_set_rhs1 (stmt, build_zero_cst (
				  TREE_TYPE (gimple_assign_lhs (stmt))));
  update_stmt (stmt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "into\n\t");
      print_gimple_stmt (dump_file, stmt, 0);
      fprintf (dump_file, "\n");
    }
}

/* Fetch COND_BB's "if (var) == true" destination.  */

basic_block
fetch_if_true_dest (basic_block cond_bb, tree var)
{
  gimple *last = last_stmt (cond_bb);
  gcc_assert (gimple_code (last) == GIMPLE_COND);
  tree lhs = gimple_cond_lhs (last);
  tree rhs = gimple_cond_rhs (last);
  gcc_assert ((lhs == var && zerop (rhs))
	      || (rhs == var && zerop (lhs)));
  edge true_e, false_e;
  extract_true_false_edges_from_block (cond_bb, &true_e, &false_e);
  switch (gimple_cond_code (last))
    {
    case NE_EXPR:
      return true_e->dest;
    case EQ_EXPR:
      return false_e->dest;
    default:
      gcc_unreachable ();
      return NULL;
    }
}

/* Main entry of ipa_cso_fixup. For a function that has applied CSO:
   1. Find the dynamic check stmt.
   2. Verify that the cloned function is pure now.
   3. If the verification failed, change dynamic check stmt to "if (false)".
 */

static unsigned int
do_ipa_cso_fixup ()
{
  /* Collect "__is_pure_flag" symbols. (References to them will be loaded with
   * function bodies.)  */
  auto_vec<varpool_node *> is_pure_flag_nodes;
  varpool_node *vnode;

  FOR_EACH_VARIABLE (vnode)
    {
      // Symbol's name startswith "__is_pure_flag" ?
      if (!strncmp (vnode->name (), IS_PURE_FLAG_PREFIX,
		    sizeof (IS_PURE_FLAG_PREFIX) - 1))
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    fprintf (dump_file, "Found is_pure_flag: %s\n", vnode->name ());
	  gcc_assert (vnode->decl && TREE_STATIC (vnode->decl));
	  is_pure_flag_nodes.safe_push (vnode);
	}
    }

  if (is_pure_flag_nodes.is_empty ())
    return 0;

  cgraph_node *node;
  unsigned todo = 0;

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    {
      /* Check if the function contains cso dynamic check code.  */
      bool loaded = false;
      ipa_ref *ref;
      unsigned i;
      unsigned todo_fun = 0;
      /* Iterate all is_pure_flags.  */
      FOR_EACH_VEC_ELT (is_pure_flag_nodes, i, vnode)
	{
	  if (!vnode)
	    continue;

	  /* is_pure_flag will be loaded in dynamic check code (contains cloned
	   * function call) and dynamic update code. If the cloned function is
	   * not pure, then dynamic update code should also be removed.  */
	  bool need_revert = false;
	  auto_vec<gimple *, 2> load_stmts;
	  auto_vec<gimple *, 1> store_stmts;

	  for (unsigned j = 0; vnode->iterate_referring (j, ref); j++)
	    {
	      if (ref->referring->decl != node->decl)
		continue;
	      switch (ref->use)
		{
		case IPA_REF_LOAD:
		  /* Found a read from __is_pure_flag.  */
		  if (!loaded)
		    {
		      if (dump_file && (dump_flags & TDF_DETAILS))
			{
			  fprintf (dump_file, "\nFunction ");
			  print_generic_expr (dump_file, node->decl, TDF_SLIM);
			  fprintf (dump_file, "\n\n");
			}
		      push_cfun (DECL_STRUCT_FUNCTION (node->decl));
		      loaded = true;
		    }
		  gcc_assert (gimple_assign_load_p (ref->stmt));
		  gcc_assert (strncmp (IDENTIFIER_POINTER (DECL_NAME (
					 gimple_assign_rhs1 (ref->stmt))),
				       IS_PURE_FLAG_PREFIX,
				       sizeof (IS_PURE_FLAG_PREFIX) - 1)
			      == 0);
		  /* Check whether cso_region_origin contains non-pure clone
		   * gcall.  */
		  if (region_has_non_pure_cloned_call (
			fetch_if_true_dest (ref->stmt->bb,
					    gimple_assign_lhs (ref->stmt))))
		    need_revert = true;
		  load_stmts.safe_push (ref->stmt);
		  break;
		case IPA_REF_STORE:
		  store_stmts.safe_push (ref->stmt);
		  break;
		default:
		  gcc_unreachable ();
		}
	    }
	  if (need_revert)
	    {
	      /* Revert dynamic check code.  */
	      unsigned j;
	      gimple *stmt;
	      FOR_EACH_VEC_ELT (load_stmts, j, stmt)
		revert_cso_check_code (stmt);

	      /* Remove update is_pure_flag stmts.  */
	      FOR_EACH_VEC_ELT (store_stmts, j, stmt)
		{
		  /* Unlink virtual operands.  */
		  unlink_stmt_vdef (stmt);
		  if (gimple_vdef (stmt)
		      && TREE_CODE (gimple_vdef (stmt)) == SSA_NAME)
		    release_ssa_name (gimple_vdef (stmt));
		  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
		  gsi_remove (&gsi, true);
		}
	      /* Remove is_pure_flag from symbols.  */
	      vnode->remove ();
	      is_pure_flag_nodes[i] = NULL;
	      todo_fun = TODO_cleanup_cfg | TODO_update_ssa;
	      todo |= todo_fun;
	    }
	}

      if (todo_fun && dump_file && (dump_flags & TDF_DETAILS))
	dump_function_to_file (cfun->decl, dump_file, TDF_SLIM | TDF_VOPS);
      if (loaded)
	{
	  if (dom_info_available_p (CDI_DOMINATORS))
	    free_dominance_info (CDI_DOMINATORS);
	  pop_cfun ();
	}
    }

  return todo;
}

namespace {

const pass_data pass_data_ipa_cso = {
  SIMPLE_IPA_PASS,		      /* type */
  "cond-sinking",		      /* name */
  OPTGROUP_NONE,		      /* optinfo_flags */
  TV_IPA_CSO,			      /* tv_id */
  PROP_cfg | PROP_ssa,		      /* properties_required */
  0,				      /* properties_provided */
  0,				      /* properties_destroyed */
  0,				      /* todo_flags_start */
  TODO_cleanup_cfg | TODO_update_ssa, /* todo_flags_finish */
};

class pass_ipa_cso : public simple_ipa_opt_pass
{
public:
  pass_ipa_cso (gcc::context *ctx)
    : simple_ipa_opt_pass (pass_data_ipa_cso, ctx), is_fixup (false)
  {}

  /* opt_pass methods: */
  opt_pass *clone () { return new pass_ipa_cso (m_ctxt); }

  void set_pass_param (unsigned n, bool param)
  {
    gcc_assert (n == 0);
    is_fixup = param;
  }

  virtual bool gate (function *)
  {
    return optimize >= 3 && flag_ipa_cond_sinking;
  }

  virtual unsigned execute (function *)
  {
    if (!is_fixup)
      return do_ipa_cso ();
    else
      return do_ipa_cso_fixup ();
  }

private:
  /* Whether we're in cso "fixup" process.  */
  bool is_fixup;
}; // class pass_ipa_cso

} // namespace

simple_ipa_opt_pass *
make_pass_ipa_cso (gcc::context *ctxt)
{
  return new pass_ipa_cso (ctxt);
}
