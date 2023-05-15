/* Array dead and redundant store elimination
   Copyright (C) 2021-2022 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "tree.h"
#include "gimple.h"
#include "tree-pass.h"
#include "ssa.h"
#include "fold-const.h"
#include "gimple-iterator.h"
#include "gimple-pretty-print.h"
#include "gimplify-me.h"
#include "tree-cfg.h"
#include "tree-dfa.h"
#include "tree-chrec.h"
#include "tree-inline.h"
#include "gimple-range.h"
#include "gimple-walk.h"
#include "gimplify.h"
#include "cfganal.h"
#include "cfgloop.h"
#include "cfghooks.h"
#include "tree-ssa-propagate.h"
#include "tree-ssa-loop.h"
#include "tree-ssa-loop-niter.h"
#include "tree-ssa-loop-ivopts.h"
#include "tree-ssa-dce.h"
#include "ipa-utils.h"
#include "tree-affine.h"
#include "tree-hash-traits.h"
#include "tree-into-ssa.h"
#include "tree-scalar-evolution.h"

/* This file implements array dead store elimination.  */

static bool dse_always_clone_callee = true;

static int
function_param_index (tree fndecl, tree name)
{
  tree fnargs = DECL_ARGUMENTS (fndecl);
  tree param;
  int index = 0;

  if (TREE_CODE (name) == SSA_NAME)
    {
      name = SSA_NAME_VAR (name);
      if (!name)
	return -1;
    }

  for (param = fnargs; param; param = DECL_CHAIN (param), index++)
    if (param == name)
      return index;

  return -1;
}

static unsigned
function_num_params (tree fndecl)
{
  return list_length (DECL_ARGUMENTS (fndecl));
}

static void
mark_reachable_blocks (basic_block header, bool include_header = true)
{
  edge e;
  edge_iterator ei;
  basic_block *tos, *worklist, bb;

  if (!header)
    header = ENTRY_BLOCK_PTR_FOR_FN (cfun);

  tos = worklist = XNEWVEC (basic_block, n_basic_blocks_for_fn (cfun));

  FOR_EACH_BB_FN (bb, cfun)
    bb->flags &= ~BB_REACHABLE;

  if (include_header)
    header->flags |= BB_REACHABLE;

  FOR_EACH_EDGE (e, ei, header->succs)
    {
      *tos++ = e->dest;
      e->dest->flags |= BB_REACHABLE;
    }

  while (tos != worklist)
    {
      basic_block b = *--tos;

      FOR_EACH_EDGE (e, ei, b->succs)
	{
	  basic_block dest = e->dest;

	  if (!(dest->flags & BB_REACHABLE))
	    {
	      *tos++ = dest;
	      dest->flags |= BB_REACHABLE;
	    }
	}
    }

  free (worklist);
}

static tree
gimple_call_return_arg (gimple *stmt)
{
  gcall *call = dyn_cast<gcall *> (stmt);

  if (!call)
    return NULL_TREE;

  unsigned flags = gimple_call_return_flags (call);

  if (flags & ERF_RETURNS_ARG)
    {
      unsigned arg_idx = flags & ERF_RETURN_ARG_MASK;

      if (arg_idx < gimple_call_num_args (call))
	return gimple_call_arg (call, arg_idx);
    }

  return NULL_TREE;
}

static inline bool
stmt_is_reachable_p (gimple *stmt)
{
  gcc_checking_assert (gimple_bb (stmt));
  return gimple_bb (stmt)->flags & BB_REACHABLE;
}

static inline edge
cond_other_edge (edge e)
{
  basic_block bb = e->src;

  if (EDGE_COUNT (bb->succs) != 2)
    return NULL;

  edge other_e = EDGE_SUCC (bb, 0);

  if (other_e == e)
    other_e = EDGE_SUCC (bb, 1);

  return other_e;
}

static inline bool
memref_expr_p (tree value)
{
  tree base = get_base_address (value);

  return DECL_P (base)
	 || TREE_CODE (base) == MEM_REF
	 || TREE_CODE (base) == TARGET_MEM_REF;
}

static inline bool
gimple_rvalue_p (tree value)
{
  return !DECL_P (value) && is_gimple_val (value);
}

static tree
check_ssa (tree *opnd_ptr, int *walk_subtrees ATTRIBUTE_UNUSED,
	   void *data)
{
  tree opnd = *opnd_ptr;
  tree ssa = (tree) data;

  if (opnd == ssa)
    return ssa;

  return NULL_TREE;
}

static bool
ssa_in_expr_p (tree ssa, tree expr)
{
  return walk_tree (&expr, check_ssa, ssa, NULL) != NULL_TREE;
}

enum match_kind {
  MATCH_ALWAYS  = 0,
  MATCH_TYPE    = 1,
  MATCH_SIZE    = 2,
  MATCH_PROMOTE = 3,
};

static tree
get_ssa_copy (gimple *stmt, bool keep_ssa = false, int match_kind = MATCH_TYPE)
{
  tree copy = NULL_TREE;
  tree lhs = gimple_get_lhs (stmt);

  if (is_gimple_assign (stmt))
    {
      if (gimple_vuse (stmt))
	return NULL_TREE;

      enum tree_code code = gimple_assign_rhs_code (stmt);

      copy = gimple_assign_rhs1 (stmt);
      if (code == VIEW_CONVERT_EXPR)
	{
	  copy = TREE_OPERAND (copy, 0);
	  if (handled_component_p (copy))
	    return NULL_TREE;
	}
      else if (code == SSA_NAME || CONVERT_EXPR_CODE_P (code))
	;
      else if ((TREE_CODE_CLASS (code) != tcc_constant && code != ADDR_EXPR)
	       || keep_ssa)
	return NULL_TREE;
    }
  else if (auto phi = dyn_cast<gphi *> (stmt))
    {
      copy = degenerate_phi_result (phi);
      if (!copy)
	return NULL_TREE;
    }
  else if (!(copy = gimple_call_return_arg (stmt)) || !gimple_rvalue_p (copy))
    return NULL_TREE;

  tree lhs_type = TREE_TYPE (lhs);
  tree copy_type = TREE_TYPE (copy);

  if (!POINTER_TYPE_P (copy_type) && !INTEGRAL_TYPE_P (copy_type))
    match_kind = MATCH_TYPE;
  else if (!POINTER_TYPE_P (lhs_type) && !INTEGRAL_TYPE_P (lhs_type))
    return NULL_TREE;

  switch (match_kind)
    {
    case MATCH_TYPE:
      if (!types_compatible_p (lhs_type, copy_type))
	return NULL_TREE;
      break;

    case MATCH_SIZE:
      if (TYPE_PRECISION (lhs_type) != TYPE_PRECISION (copy_type))
	return NULL_TREE;
      break;

    case MATCH_PROMOTE:
      if (TYPE_PRECISION (lhs_type) < TYPE_PRECISION (copy_type))
	return NULL_TREE;
      break;

    default:
      break;
    }

  if (keep_ssa && TREE_CODE (copy) != SSA_NAME)
    return NULL_TREE;

  return copy;
}

static tree
get_ssa_copy (tree expr, bool keep_ssa = false, int match_kind = MATCH_TYPE)
{
  if (TREE_CODE (expr) != SSA_NAME)
    return NULL_TREE;

  return get_ssa_copy (SSA_NAME_DEF_STMT (expr), keep_ssa, match_kind);
}

static tree
skip_ssa_copy (tree expr, bool keep_ssa = false, int match_kind = MATCH_TYPE)
{
  while (tree copy = get_ssa_copy (expr, keep_ssa, match_kind))
    expr = copy;

  return expr;
}

static tree
find_loop_latch_niter (class loop *loop, edge *exit)
{
  push_dump_file save (NULL, TDF_NONE);
  tree niter = chrec_dont_know;

  *exit = NULL;

  for (auto ex : get_loop_exit_edges (loop))
    {
      class tree_niter_desc niter_desc;

      /* Only care about exit that dominates latch.  */
      if (!number_of_iterations_exit_assumptions (loop, ex, &niter_desc, NULL)
	  || chrec_contains_undetermined (niter_desc.niter))
	continue;

      if (integer_zerop (niter_desc.assumptions))
	continue;

      if (integer_nonzerop (niter_desc.may_be_zero))
	{
	  niter = build_zero_cst (TREE_TYPE (niter_desc.niter));
	  *exit = ex;
	  break;
	}

      tree new_niter = niter_desc.niter;

      if (niter == chrec_dont_know)
	{
	  niter = new_niter;
	  *exit = ex;
	}
      else if (TREE_CODE (new_niter) == INTEGER_CST)
	{
	  /* Prefer constants, the lower the better.  */
	  if (TREE_CODE (niter) != INTEGER_CST
	      || tree_int_cst_lt (new_niter, niter))
	    {
	      niter = new_niter;
	      *exit = ex;
	    }
	}
      else if (TREE_CODE (niter) != INTEGER_CST)
	{
	   /* From those exit conditions, the one that is nearest to the latch
	      would give the minimum iterations in all possibility.  */
	  if (dominated_by_p (CDI_DOMINATORS, ex->src, (*exit)->src))
	    {
	      niter = new_niter;
	      *exit = ex;
	    }
	}
    }

  return niter;
}

static inline tree
copy_ssa_name_if_not (tree ssa, tree &new_ssa)
{
  if (!new_ssa)
    new_ssa = copy_ssa_name (ssa);

  return new_ssa;
}

static tree
split_ssa_at_stmt (tree ssa, gassign *stmt, bool only_needed)
{
  tree new_ssa = NULL_TREE;
  basic_block bb = gimple_bb (stmt);
  imm_use_iterator use_iter;
  gimple *use_stmt;

  if (!only_needed)
    new_ssa = copy_ssa_name (ssa);

  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, ssa)
    {
      if (use_stmt == stmt)
	continue;

      if (gphi *phi = dyn_cast <gphi *> (use_stmt))
	{
	  for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
	    {
	      tree arg = gimple_phi_arg_def (phi, i);

	      if (arg != ssa)
		continue;

	      edge e = gimple_phi_arg_edge (phi, i);

	      if (dominated_by_p (CDI_DOMINATORS, e->src, bb))
		add_phi_arg (phi, copy_ssa_name_if_not (ssa, new_ssa), e,
			     gimple_phi_arg_location (phi, i));
	    }
	}
      else if (stmt_dominates_stmt_p (stmt, use_stmt))
	{
	  use_operand_p use_p;

	  FOR_EACH_IMM_USE_ON_STMT (use_p, use_iter)
	    SET_USE (use_p, copy_ssa_name_if_not (ssa, new_ssa));

	  update_stmt (use_stmt);
	}
    }

  if (new_ssa)
    {
      if (SSA_NAME_OCCURS_IN_ABNORMAL_PHI (ssa))
	SSA_NAME_OCCURS_IN_ABNORMAL_PHI (new_ssa) = 1;
      gimple_assign_set_lhs (stmt, new_ssa);
    }
  else
    {
      gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
      gsi_remove (&gsi, true);
    }

  return new_ssa;
}

static tree
split_ssa_at_edge (tree ssa, edge e, bool only_needed = true)
{
  gassign *stmt = gimple_build_assign (NULL_TREE, ssa);

  gsi_insert_on_edge_immediate (e, stmt);

  return split_ssa_at_stmt (ssa, stmt, only_needed);
}

static tree
split_ssa_at_gsi (tree ssa, gimple_stmt_iterator *gsi,
		  bool before, bool only_needed = true)
{
  gassign *stmt = gimple_build_assign (NULL_TREE, ssa);

  if (before)
    gsi_insert_before (gsi, stmt, GSI_NEW_STMT);
  else
    gsi_insert_after (gsi, stmt, GSI_NEW_STMT);

  return split_ssa_at_stmt (ssa, stmt, only_needed);
}

enum memory_alloc_kind
{
  ALLOC_NONE,
  ALLOC_HEAP,
  ALLOC_STACK
};

static int
memory_alloc_stmt_p (gimple *stmt)
{
  if (!gimple_call_builtin_p (stmt, BUILT_IN_NORMAL))
    return ALLOC_NONE;

  tree callee = gimple_call_fndecl (stmt);

  switch (DECL_FUNCTION_CODE (callee))
    {
    case BUILT_IN_MALLOC:
    case BUILT_IN_CALLOC:
    case BUILT_IN_ALIGNED_ALLOC:
      return ALLOC_HEAP;

    CASE_BUILT_IN_ALLOCA:
      return ALLOC_STACK;

    default:
      break;
    }

  return ALLOC_NONE;
}

static inline int
memory_alloc_base_p (tree base)
{
  if (TREE_CODE (base) != SSA_NAME)
    return 0;

  return memory_alloc_stmt_p (SSA_NAME_DEF_STMT (base));
}

static bool
memory_free_stmt_p (gimple *stmt)
{
  if (!gimple_call_builtin_p (stmt, BUILT_IN_NORMAL))
    return false;

  tree callee = gimple_call_fndecl (stmt);

  if (DECL_FUNCTION_CODE (callee) == BUILT_IN_FREE)
    return true;

  return false;
}

static tree
memory_alloc_size (gimple *stmt)
{
  tree callee = gimple_call_fndecl (stmt);
  tree size = NULL_TREE;

  if (!callee)
    return NULL_TREE;

  switch (DECL_FUNCTION_CODE (callee))
    {
    case BUILT_IN_MALLOC:
    CASE_BUILT_IN_ALLOCA:
      size = gimple_call_arg (stmt, 0);
      break;

    case BUILT_IN_ALIGNED_ALLOC:
      size = gimple_call_arg (stmt, 1);
      break;

    case BUILT_IN_CALLOC:
      {
	tree arg0 = gimple_call_arg (stmt, 0);
	tree arg1 = gimple_call_arg (stmt, 1);

	if (TREE_CODE (arg0) != INTEGER_CST || TREE_CODE (arg1) != INTEGER_CST)
	  return NULL_TREE;

	return size_binop (MULT_EXPR, arg0, arg1);
      }

    default:
      return NULL_TREE;
    }

  return TREE_CODE (size) == INTEGER_CST ? size : NULL_TREE;
}

static bool
local_memory_in_function_p (tree object)
{
  if (VAR_P (object))
    {
      if (decl_function_context (object) == current_function_decl)
	return true;

      if (TREE_STATIC (object))
	{
	  varpool_node *vnode = varpool_node::get (object);

	  if (!vnode || !vnode->can_remove_if_no_refs_p ())
	    return false;

	  ipa_ref *ref = NULL;
	  cgraph_node *curr_node = cgraph_node::get (current_function_decl);

	  gcc_assert (curr_node);

	  for (unsigned i = 0; vnode->iterate_referring (i, ref); i++)
	    {
	      if (dyn_cast<cgraph_node *> (ref->referring) != curr_node)
		return false;
	    }

	  return true;
	}
    }
  else if (TREE_CODE (object) == SSA_NAME)
    {
      gimple *stmt = SSA_NAME_DEF_STMT (object);

      if (memory_alloc_stmt_p (stmt) == ALLOC_STACK)
	return true;
    }

  return false;
}

/* Return true if STMT1 dominates STMT2, and STMT2 is executed at most once
   after STMT1.  */

static bool
stmt_linear_dominates_stmt_p (gimple *stmt1, gimple *stmt2)
{
  basic_block bb1 = gimple_bb (stmt1);
  basic_block bb2 = gimple_bb (stmt2);

  if (bb1 != bb2)
    {
      if (bb1->loop_father != bb2->loop_father)
	return false;

      if (bb2->flags & BB_IRREDUCIBLE_LOOP)
	return false;
    }

  return stmt_dominates_stmt_p (stmt1, stmt2);
}

static tree
get_mem_access_base_and_offset (tree expr, HOST_WIDE_INT *offset_ptr = NULL,
				HOST_WIDE_INT *size_ptr = NULL)
{
  poly_int64 psize, poffset, pmax_size;
  HOST_WIDE_INT offset, size;
  bool reverse;
  tree base = get_ref_base_and_extent (expr, &poffset, &psize, &pmax_size,
				       &reverse);

  if (!poffset.is_constant (&offset) || !psize.is_constant (&size) || size < 0
      || !known_size_p (pmax_size) || maybe_ne (pmax_size, size))
    return error_mark_node;

  if (offset_ptr)
    *offset_ptr = offset;

  if (size_ptr)
    *size_ptr = size;

  return base;
}

/* Return base address if it is from a SSA pointer or decl variable.  */

static tree
get_mem_access_simple_base (tree expr, HOST_WIDE_INT *offset_ptr = NULL,
			    HOST_WIDE_INT *size_ptr = NULL)
{
  tree base = get_mem_access_base_and_offset (expr, offset_ptr, size_ptr);

  if (TREE_CODE (base) == MEM_REF)
    {
      tree offset = TREE_OPERAND (base, 1);

      base = TREE_OPERAND (base, 0);
      if (TREE_CODE (base) != SSA_NAME)
	return error_mark_node;

      if (!tree_fits_shwi_p (offset))
	return error_mark_node;

      if (offset_ptr)
	*offset_ptr += tree_to_shwi (offset);
    }
  else if (!DECL_P (base))
    return error_mark_node;

  return base;
}

static bool
collect_memref (gimple *, tree, tree memref, void *data)
{
  auto &vars = *(auto_vec<tree> *) data;

  vars.safe_push (memref);
  return false;
}

static tree
collect_ssa (tree *opnd_ptr, int *, void *data)
{
  auto &ssa_set = *(hash_set<tree_ssa_name_hash> *) data;
  tree opnd = *opnd_ptr;

  if (TREE_CODE (opnd) == SSA_NAME)
    ssa_set.add (opnd);

  return NULL_TREE;
}

struct memref_area
{
  HOST_WIDE_INT offset;
  HOST_WIDE_INT size;
};

class memref_areas : public auto_vec<memref_area>
{
public:
  void add (HOST_WIDE_INT offset, HOST_WIDE_INT size)
  {
    gcc_checking_assert (offset >= 0 && size > 0);
    gcc_checking_assert (offset + size > offset);

    for (auto &area : *this)
      {
	if (area.offset == offset)
	  {
	    if (area.size < size)
	      area.size = size;
	    return;
	  }
      }

    safe_push ({ offset, size });
  }

  void add (const memref_area &area)
  {
    add (area.offset, area.size);
  }

  void add (const memref_areas &areas)
  {
    for (auto &area : areas)
      add (area);
  }

  bool add (tree memref, tree base_to_check = NULL_TREE)
  {
    HOST_WIDE_INT offset, size;
    tree base = get_mem_access_simple_base (memref, &offset, &size);

    if ((base_to_check && !operand_equal_p (base, base_to_check))
	 || offset + size <= offset)
      return false;

    add (offset, size);
    return true;
  }

  HOST_WIDE_INT get_max_size () const
  {
    HOST_WIDE_INT max_size = 0;

    for (auto &area : *this)
      {
	HOST_WIDE_INT size = area.offset + area.size;

	if (max_size < size)
	  max_size = size;
      }

    return max_size;
  }

  bool include_p (HOST_WIDE_INT offset, HOST_WIDE_INT size)
  {
    for (auto &area : *this)
      {
	if (area.offset <= offset && area.size >= size)
	  return true;
      }

    return false;
  }

  bool include_p (const memref_area &area)
  {
    return include_p (area.offset, area.size);
  }

  bool include_p (const memref_areas &areas)
  {
    for (auto &area : areas)
      {
	if (!include_p (area))
	  return false;
      }

    return true;
  }
};

static bool as_pointer_type_p (tree type)
{
  if (POINTER_TYPE_P (type))
    return true;

  if (INTEGRAL_TYPE_P (type) && TYPE_PRECISION (type) == POINTER_SIZE)
    return true;

  return false;
}

class addr_base_map
{
  class addr_group
  {
  public:
    int index;
    addr_group *parent;

    vec<tree> todo_source_addrs;
    vec<int> sources;

    vec<tree> members;

    void add_address (tree addr)
    {
      gcc_checking_assert (TREE_CODE (addr) == SSA_NAME);
      members.safe_push (addr);
    }

    void clear ()
    {
      todo_source_addrs.release ();
      sources.release ();
      members.release ();
    }

    addr_group (tree addr, int index = 0)
    : index (index), parent (NULL), todo_source_addrs (vNULL)
    , sources (vNULL), members (vNULL)
    {
      add_address (addr);
    }

    ~addr_group ()
    {
      clear ();
    }

    bool is_root () const { return !parent; }

    void combine (addr_group *other)
    {
      gcc_checking_assert (is_root () && other->is_root ());

      if (todo_source_addrs.is_empty ())
	std::swap (todo_source_addrs, other->todo_source_addrs);
      else
	todo_source_addrs.safe_splice (other->todo_source_addrs);

      if (sources.is_empty ())
	std::swap (sources, other->sources);
      else
	sources.safe_splice (other->sources);

      members.safe_splice (other->members);

      other->clear ();
      other->parent = this;
    }
  };

  bool ignore_null;
  auto_delete_vec<addr_group> group_graph;
  int used_group_count;

  auto_vec<vec<tree> > base_sets;
  int used_base_count;

  hash_map<tree, int> addr_to_index;

  static bool final_base_p (tree addr)
  {
    return TREE_CODE (addr) == SSA_NAME
	   || CONSTANT_CLASS_P (addr)
	   || decl_address_invariant_p (addr);
  }

  static tree strip_base (tree addr)
  {
    if (TREE_CODE (addr) == ADDR_EXPR)
      {
	addr = get_base_address (TREE_OPERAND (addr, 0));

	if (TREE_CODE (addr) == MEM_REF
	    || TREE_CODE (addr) == TARGET_MEM_REF)
	  addr = TREE_OPERAND (addr, 0);

	gcc_assert (final_base_p (addr));
      }
    else
      {
	gcc_assert (as_pointer_type_p (TREE_TYPE (addr)));
	gcc_assert (is_gimple_mem_ref_addr (addr));
      }

    return addr;
  }

  int get_index (tree addr)
  {
    gcc_checking_assert (final_base_p (addr));

    if (int *index = addr_to_index.get (addr))
      {
	gcc_checking_assert (*index != -1);
	return *index;
      }

    return -1;
  }

  void set_index (tree addr, int index)
  {
    bool existed;
    auto &old_index = addr_to_index.get_or_insert (addr, &existed);

    gcc_checking_assert (index != -1);

    if (existed)
      {
	gcc_checking_assert (TREE_CODE (addr) == SSA_NAME);
	gcc_checking_assert (old_index < -1 || old_index == index);
      }

    old_index = index;
  }

  addr_group *get_group (int index)
  {
    gcc_checking_assert (-index - 2 < used_group_count);
    return group_graph[-index - 2];
  }

  int add_base (vec<tree> base_set)
  {
    int real_base_count = (int) base_sets.length ();

    if (used_base_count == real_base_count)
      base_sets.safe_push (base_set);
    else
      {
	base_sets[used_base_count].release ();
	base_sets[used_base_count] = base_set;
      }

    return ++used_base_count;
  }

  int add_base (tree base)
  {
    vec<tree> base_set = vNULL;

    base_set.reserve_exact (1);
    base_set.quick_push (base);

    return add_base (base_set);
  }

  vec<tree> get_base (int index)
  {
    gcc_checking_assert (index <= used_base_count);
    return base_sets[index - 1];
  }

  addr_group *create_group (tree addr)
  {
    bool existed;
    auto &index = addr_to_index.get_or_insert (addr, &existed);
    int real_group_count = (int) group_graph.length ();
    addr_group *group;

    gcc_checking_assert (!existed);

    if (used_group_count == real_group_count)
      {
	group = new addr_group (addr);

	group_graph.safe_push (group);
      }
    else
      {
	group = group_graph[used_group_count];

	gcc_checking_assert (group);
	group->parent = NULL;
	group->clear ();
	group->add_address (addr);
      }

    used_group_count++;
    index = group->index = -used_group_count - 1;

    return group;
  }

  int assign_group_index (addr_group *group, int index)
  {
    for (auto member : group->members)
      set_index (member, index);

    return group->index = index;
  }

  int compute_group_base (addr_group *group)
  {
    int base_index = -1;

    gcc_checking_assert (group->is_root ());
    gcc_checking_assert (group->todo_source_addrs.is_empty ());
    gcc_checking_assert (group->index < -1);

    if (group->sources.is_empty ())
      {
	base_index = 0;
	gcc_unreachable ();
      }
    else
      {
	vec<tree> base_set = vNULL;
	vec<int> sources = group->sources;
	int null_index = -1;

	group->sources = vNULL;

	for (unsigned i = 0; i < sources.length (); i++)
	  {
	    int index = sources[i];
	    auto base_set = get_base (index);

	    if (integer_zerop (base_set[0]))
	      {
		if (base_set.length () == 1)
		  {
		    if (null_index == -1)
		      null_index = index;

		    sources.unordered_remove (i--);
		    continue;
		  }

		gcc_checking_assert (!ignore_null);

		if (null_index != -2)
		  {
		    null_index = -2;
		    if (i)
		      std::swap (sources[0], sources[i]);
		  }
	      }

	    for (unsigned j = 0; j < i; j++)
	      {
		if (index == sources[j])
		  {
		    sources.unordered_remove (i--);
		    break;
		  }
	      }
	  }

	if (!ignore_null && null_index >= 0)
	  {
	    sources.safe_push (null_index);

	    if (sources.length () > 1)
	      std::swap (sources[0], sources.last ());
	  }

	if (sources.is_empty ())
	  base_index = null_index;
	else if (sources.length () == 1)
	  base_index = sources[0];
	else
	  {
	    base_set.safe_splice (get_base (sources[0]));

	    for (unsigned i = 1; i < sources.length (); i++)
	      {
		unsigned cmp_end = base_set.length ();

		for (auto src_base : get_base (sources[i]))
		  {
		    bool duplicated = false;

		    if (integer_zerop (src_base))
		      continue;

		    for (unsigned k = 0; k < cmp_end; k++)
		      {
			if (operand_equal_p (src_base, base_set[k]))
			  {
			    duplicated = true;
			    break;
			  }
		      }

		    if (!duplicated)
		      base_set.safe_push (src_base);
		  }
	      }

	    base_index = add_base (base_set);
	  }

	gcc_checking_assert (base_index >= 0);
	sources.release ();
      }

    assign_group_index (group, base_index);

    group->members.release ();
    return base_index;
  }

  int analyze_address (tree addr, int index = -1);
  int get_address_base_1 (tree);

public:
  addr_base_map (bool ignore_null = true)
  : ignore_null (ignore_null), used_group_count (0), used_base_count (0)
  { }

  ~addr_base_map ()
  {
    for (auto &base_set : base_sets)
      base_set.release ();
  }

  void initialize ()
  {
    used_base_count = 0;

    for (auto &base_set : base_sets)
      base_set.release ();

    addr_to_index.empty ();
  }

  bool same_base_p (tree addr1, tree addr2)
  {
    return get_address_base_1 (addr1) == get_address_base_1 (addr2);
  }

  vec<tree> get_address_base (tree mem_or_addr)
  {
    int index = get_address_base_1 (mem_or_addr);

    return get_base (index);
  }
};

int
addr_base_map::analyze_address (tree addr, int index)
{
  gimple *stmt = NULL;
  vec<tree> src_addrs = vNULL;

  if (TREE_CODE (addr) != SSA_NAME)
    {
      gcc_checking_assert (final_base_p (addr));
      goto end;
    }

  stmt = SSA_NAME_DEF_STMT (addr);

  if (tree copy = get_ssa_copy (stmt, false, MATCH_SIZE))
    src_addrs.safe_push (copy);
  else if (is_gimple_assign (stmt))
    {
      tree rhs1 = gimple_assign_rhs1 (stmt);

      switch (gimple_assign_rhs_code (stmt))
	{
	case ADDR_EXPR:
	case POINTER_PLUS_EXPR:
	  src_addrs.safe_push (rhs1);
	  break;

	case PLUS_EXPR:
	case MINUS_EXPR:
	  if (TREE_CODE (gimple_assign_rhs2 (stmt)) == INTEGER_CST)
	    src_addrs.safe_push (rhs1);
	  break;

	case MAX_EXPR:
	case MIN_EXPR:
	  src_addrs.safe_push (rhs1);
	  src_addrs.safe_push (gimple_assign_rhs2 (stmt));
	  break;

	case COND_EXPR:
	  src_addrs.safe_push (gimple_assign_rhs2 (stmt));
	  src_addrs.safe_push (gimple_assign_rhs3 (stmt));
	  break;

	default:
	  break;
	}
    }
  else if (auto phi = dyn_cast <gphi *> (stmt))
    {
      for (unsigned i = 0; i < gimple_phi_num_args (phi); ++i)
	{
	  tree arg = gimple_phi_arg_def (phi, i);

	  if (!src_addrs.contains (arg))
	    src_addrs.safe_push (arg);
	}
    }
  else if (auto arg = gimple_call_return_arg (stmt))
    {
      if (gimple_rvalue_p (arg))
	src_addrs.safe_push (arg);
    }

end:
  if (src_addrs.is_empty ())
    index = add_base (addr);
  else if (index == -1)
    {
      addr_group *group = create_group (addr);

      group->todo_source_addrs = src_addrs;

      return group->index;
    }
  else
    {
      addr_group *group = get_group (index);

      group->members.safe_push (addr);

      if (group->todo_source_addrs.is_empty ())
	group->todo_source_addrs = src_addrs;
      else
	{
	  group->todo_source_addrs.safe_splice (src_addrs);
	  src_addrs.release ();
	}
    }

  set_index (addr, index);
  return index;
}

int
addr_base_map::get_address_base_1 (tree mem_or_addr)
{
  tree base = get_base_address (mem_or_addr);

  gcc_assert (TREE_CODE (mem_or_addr) != WITH_SIZE_EXPR);

  if (TREE_CODE (base) == MEM_REF
      || TREE_CODE (base) == TARGET_MEM_REF)
    base = TREE_OPERAND (base, 0);

  tree addr = DECL_P (base) ? base : strip_base (base);
  int index = get_index (addr);

  if (index == -1)
    {
      used_group_count = 0;
      index = analyze_address (addr);
    }

  if (index >= 0)
    return index;

  auto_vec<addr_group *> stack;
  addr_group *start = get_group (index);
  addr_group *curr = start;

  stack.safe_push (start);

  while (true)
    {
      while (!curr->todo_source_addrs.is_empty ())
	{
	  tree src_addr = strip_base (curr->todo_source_addrs.pop ());
	  int src_index = get_index (src_addr);

	  if (src_index == -1)
	    {
	      if (curr->todo_source_addrs.is_empty ()
		  && curr->sources.is_empty ())
		{
		  src_index = analyze_address (src_addr, curr->index);
		}
	      else if ((src_index = analyze_address (src_addr)) < -1)
		{
		  curr = get_group (src_index);
		  stack.safe_push (curr);
		  continue;
		}
	    }

	  gcc_checking_assert (src_index);

	  if (src_index > 0)
	    {
	      curr->sources.safe_push (src_index);
	    }
	  else if (src_index != curr->index)
	    {
	      addr_group *src = get_group (src_index);

	      gcc_checking_assert (src->is_root ());

	      for (; curr != src; stack.pop (), curr = stack.last ())
		{
		  assign_group_index (curr, src_index);
		  src->combine (curr);
		}
	    }
	}

      index = compute_group_base (curr);

      if (curr == start)
	break;

      curr = (stack.pop (), stack.last ());
      curr->sources.safe_push (index);
    }

  return index;
}

static inline void
dump_address (FILE *file, tree addr)
{
  if (DECL_P (addr))
    fprintf (file, "&");
  print_generic_expr (file, addr, TDF_NONE);
  if (!DECL_P (addr) && INTEGRAL_TYPE_P (TREE_TYPE (addr)))
    fprintf (file, "<i>");
}

static void
dump_address (FILE *file, vec<tree> addr_set)
{
  for (unsigned i = 0; i < addr_set.length (); i++)
    {
      if (i)
	fprintf (file, ", ");
      dump_address (file, addr_set[i]);
    }
}

enum addr_usage
{
  AU_NONE    = 0,
  AU_COND    = 1 << 0,
  AU_COND_EX = 1 << 1,
  AU_CALL    = 1 << 2,
  AU_SAVED   = 1 << 3,
  AU_OTHER   = 1 << 4
};

class addr_analyzer : public addr_base_map
{
public:
  hash_map<tree, int> base_to_index;
  auto_vec<tree> index_to_base;
  auto_vec<vec<tree>> addr_sets;
  auto_bitmap ssa_visited;
  auto_vec<char> base_usage;

  hash_map<tree, int> var_to_index;
  auto_vec<tree> index_to_var;
  auto_vec<vec<gimple *>> var_access_sets;

  addr_analyzer (bool ignore_null = true) : addr_base_map (ignore_null)
  { }

  ~addr_analyzer ()
  {
    for (auto &addr_set : addr_sets)
      addr_set.release ();
  }

  vec<tree> get_address_set (tree base)
  {
    auto index_ptr = base_to_index.get (base);

    if (!index_ptr)
      return vNULL;

    return addr_sets[*index_ptr];
  }

  int get_base_usage (tree base)
  {
    auto index_ptr = base_to_index.get (base);

    gcc_checking_assert (index_ptr);

    return base_usage[*index_ptr];
  }

  bool exclude_base_p (tree base, int usage)
  {
    return get_base_usage (base) & (usage | AU_OTHER);
  }

  void add_var_access (tree var, gimple *stmt)
  {
    if (gimple_clobber_p (stmt))
      return;

    bool existed;
    auto &index = var_to_index.get_or_insert (var, &existed);

    if (!existed)
      {
	index = var_access_sets.length ();
	var_access_sets.safe_push (vNULL);
	index_to_var.safe_push (var);
      }

    if (!var_access_sets[index].contains (stmt))
      var_access_sets[index].safe_push (stmt);
  }

  vec<gimple *> get_var_access_set (tree var)
  {
    auto index_ptr = var_to_index.get (var);

    if (!index_ptr)
      return vNULL;

    return var_access_sets[*index_ptr];
  }

  void process_address (tree, int = 0);
  void process_comparison (tree, tree);
  void process_init_expr (tree);
  void process_memref (tree);
  void process_non_address_stmt (gimple *);
  void process_stmt (gimple *);
  void process_bb (basic_block);
  void process (bool = false);
  bool prepare ();

  void dump (FILE *);
};

void
addr_analyzer::process_address (tree addr, int usage)
{
  if (!as_pointer_type_p (TREE_TYPE (addr)) || TREE_CODE (addr) == INTEGER_CST)
    return;

  bool add_ssa = false;

  if (TREE_CODE (addr) == SSA_NAME)
    {
      add_ssa = bitmap_set_bit (ssa_visited, SSA_NAME_VERSION (addr));

      if (!add_ssa && !usage)
	return;
    }

  for (auto base : get_address_base (addr))
    {
      bool existed;
      auto &index = base_to_index.get_or_insert (base, &existed);

      if (!existed)
	{
	  index = addr_sets.length ();
	  index_to_base.safe_push (base);
	  addr_sets.safe_push (vNULL);
	  base_usage.safe_push (usage);
	}
      else
	base_usage[index] |= usage;

      if (add_ssa)
	addr_sets[index].safe_push (addr);
    }
}

void
addr_analyzer::process_comparison (tree op1, tree op2)
{
  if (!as_pointer_type_p (TREE_TYPE (op1)))
    return;

  int usage = AU_COND;

  if (!integer_zerop (op1) && !integer_zerop (op2) && !same_base_p (op1, op2))
    usage |= AU_COND_EX;

  process_address (op1, usage);
  process_address (op2, usage);
}

void
addr_analyzer::process_init_expr (tree init)
{
  if (TREE_CODE (init) == CONSTRUCTOR)
    {
      unsigned i;
      tree value;

      FOR_EACH_CONSTRUCTOR_VALUE (CONSTRUCTOR_ELTS (init), i, value)
	process_init_expr (value);
    }
  else if (gimple_rvalue_p (init))
    process_address (init, AU_SAVED);
}

void
addr_analyzer::process_non_address_stmt (gimple *stmt)
{
  auto_vec<tree> addr_exprs;
  ssa_op_iter iter;
  tree use;

  walk_stmt_load_store_addr_ops (stmt, &addr_exprs, NULL, NULL,
				 collect_memref);

  for (auto addr : addr_exprs)
    process_address (addr, AU_OTHER);

  FOR_EACH_SSA_TREE_OPERAND (use, stmt, iter, SSA_OP_USE)
    process_address (use, AU_OTHER);
}

void
addr_analyzer::process_memref (tree memref)
{
  hash_set<tree_ssa_name_hash> ssa_set;
  bool skip_pointer = false;

  walk_tree (&memref, collect_ssa, &ssa_set, NULL);

  if (TREE_CODE (memref) == WITH_SIZE_EXPR)
    memref = TREE_OPERAND (memref, 0);

  if (memref_expr_p (memref))
    skip_pointer = true;

  for (auto ssa : ssa_set)
    {
      tree type = TREE_TYPE (ssa);

      if ((INTEGRAL_TYPE_P (type) && TYPE_PRECISION (type) == POINTER_SIZE)
	  || (!skip_pointer && POINTER_TYPE_P (type)))
	process_address (ssa, AU_OTHER);
    }
}

void
addr_analyzer::process_stmt (gimple *stmt)
{
  if (is_gimple_debug (stmt))
    return;

  if (tree lhs = gimple_get_lhs (stmt))
    {
      if (TREE_CODE (lhs) == SSA_NAME)
	process_address (lhs);
      else
	process_memref (lhs);
    }

  if (is_gimple_assign (stmt))
    {
      tree rhs1 = gimple_assign_rhs1 (stmt);
      tree rhs2 = gimple_assign_rhs2 (stmt);

      if (gimple_vdef (stmt))
	process_init_expr (rhs1);

      switch (gimple_assign_rhs_code (stmt))
	{
	case MAX_EXPR:
	case MIN_EXPR:
	case OBJ_TYPE_REF:
	case ADDR_SPACE_CONVERT_EXPR:
	case CONSTRUCTOR:
	  break;

	case ADDR_EXPR:
	  process_memref (TREE_OPERAND (rhs1, 0));
	  break;

	case POINTER_PLUS_EXPR:
	  process_address (rhs2, AU_OTHER);
	  break;

	case NE_EXPR:
	case EQ_EXPR:
	case LE_EXPR:
	case LT_EXPR:
	case GE_EXPR:
	case GT_EXPR:
	case MINUS_EXPR:
	case POINTER_DIFF_EXPR:
	  process_comparison (rhs1, rhs2);
	  break;

	case COND_EXPR:
	  if (COMPARISON_CLASS_P (rhs1))
	    process_comparison (TREE_OPERAND (rhs1, 0),
				TREE_OPERAND (rhs1, 1));
	  break;

	default:
	  if (get_ssa_copy (stmt, false, MATCH_SIZE))
	    break;

	  if (gimple_assign_single_p (stmt) && !gimple_rvalue_p (rhs1))
	    process_memref (rhs1);
	  else if (!gimple_vuse (stmt))
	    process_non_address_stmt (stmt);
	}
    }
  else if (auto cond = dyn_cast <gcond *> (stmt))
    process_comparison (gimple_cond_lhs (cond), gimple_cond_rhs (cond));
  else if (auto ret = dyn_cast<greturn *> (stmt))
    {
      if (tree val = gimple_return_retval (ret))
	process_memref (val);
    }
  else if (is_gimple_call (stmt))
    {
      bool free_p = memory_free_stmt_p (stmt);

      for (unsigned i = 2; i < gimple_num_ops (stmt); i++)
	{
	  tree arg = gimple_op (stmt, i);

	  if (!arg)
	    continue;

	  if (!gimple_rvalue_p (arg))
	    process_memref (arg);
	  else if (!free_p)
	    process_address (arg, AU_CALL);
	}
    }
  else if (gimple_code (stmt) != GIMPLE_PHI)
    process_non_address_stmt (stmt);
}

static void
gimplify_addr_expr (gimple *stmt, tree *opnd_ptr)
{
  tree opnd = *opnd_ptr;

  if (!opnd || TREE_CODE (opnd) != ADDR_EXPR)
    return;

  tree base = get_base_address (TREE_OPERAND (opnd, 0));

  if (DECL_P (base) && !VAR_P (base))
    return;

  if (TREE_CODE_CLASS (TREE_CODE (base)) == tcc_constant)
    return;

  tree new_opnd = *opnd_ptr = make_ssa_name (TREE_TYPE (opnd));
  auto new_stmt = gimple_build_assign (new_opnd, opnd);
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);

  gcc_checking_assert (gimple_code (stmt) != GIMPLE_PHI);
  gsi_insert_before (&gsi, new_stmt, GSI_SAME_STMT);

  if (gimple_assign_single_p (stmt))
    gimple_assign_set_rhs_code (stmt, SSA_NAME);

  update_stmt (stmt);
}

static bool
add_var_access_fn (gimple *stmt, tree memref, tree, void *data)
{
  memref = get_base_address (memref);

  if (memref && VAR_P (memref))
    ((addr_analyzer *) data)->add_var_access (memref, stmt);

  return false;
}

bool
addr_analyzer::prepare ()
{
  basic_block bb;

  FOR_EACH_BB_FN (bb, cfun)
    {
      for (auto gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	{
	  gimple *stmt = gsi_stmt (gsi);

	  if (gimple_code (stmt) == GIMPLE_ASM)
	    return false;

	  if (gimple_assign_load_p (stmt))
	    {
	      tree lhs = gimple_assign_lhs (stmt);

	      if (is_gimple_reg_type (TREE_TYPE (lhs)))
		gcc_assert (!memref_expr_p (lhs));
	    }

	  if (gimple_assign_single_p (stmt) && gimple_vdef (stmt))
	    gimplify_addr_expr (stmt, gimple_assign_rhs1_ptr (stmt));
	  else if (is_gimple_call (stmt))
	    {
	      for (unsigned i = 2; i < gimple_num_ops (stmt); i++)
		gimplify_addr_expr (stmt, gimple_op_ptr (stmt, i));
	    }
	  else if (auto ret = dyn_cast <greturn *> (stmt))
	    gimplify_addr_expr (ret, gimple_return_retval_ptr (ret));

	  if (gimple_vuse (stmt))
	    walk_stmt_load_store_ops (stmt, this, add_var_access_fn,
				      add_var_access_fn);
	}
    }

  return true;
}

void
addr_analyzer::process_bb (basic_block bb)
{
  for (auto gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    process_stmt (gsi_stmt (gsi));

  for (auto gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    process_stmt (gsi_stmt (gsi));
}

void
addr_analyzer::process (bool only_reachable)
{
  basic_block bb;

  FOR_EACH_BB_FN (bb, cfun)
    {
      if (!only_reachable || (bb->flags & BB_REACHABLE))
	process_bb (bb);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    dump (dump_file);
}

void
addr_analyzer::dump (FILE *file)
{
  for (unsigned i = 0; i < var_access_sets.length (); i++)
    {
      tree var = index_to_var [i];

      fprintf (file, "Direct access to ");
      dump_address (file, var);

      fprintf (file, ":\n");

      for (auto stmt : var_access_sets[i])
	{
	  fprintf (file, "  ");
	  print_gimple_stmt (file, stmt, 0, TDF_NONE);
	}
    }
  fprintf (file, "\n");

  for (unsigned i = 0; i < addr_sets.length (); i++)
    {
      bool has_address = false;

      for (auto addr : addr_sets[i])
	{
	  if (POINTER_TYPE_P (TREE_TYPE (addr)))
	    {
	      has_address = true;
	      break;
	    }
	}

      if (!has_address)
	continue;

      tree base = index_to_base [i];

      fprintf (file, "Address based on ");
      dump_address (file, base);

      if (auto usage = base_usage[i])
	{
	  int n = 0;

	  fprintf (file, " (");
	  if (usage & AU_COND_EX)
	    n += fprintf (file, "cond-ex");
	  else if (usage & AU_COND)
	    n += fprintf (file, "cond");

	  if (usage & AU_CALL)
	    n += fprintf (file, "%scall", n ? ", " : "");

	  if (usage & AU_SAVED)
	    n += fprintf (file, "%ssaved", n ? ", " : "");

	  if (usage & AU_OTHER)
	    n += fprintf (file, "%sother", n ? ", " : "");
	  fprintf (file, ")");
	}

      fprintf (file, ": ");
      dump_address (file, addr_sets[i]);
      fprintf (file, "\n");

      if (TREE_CODE (base) == SSA_NAME && !SSA_NAME_IS_DEFAULT_DEF (base))
	{
	  fprintf (file, "  ");
	  print_gimple_stmt (file, SSA_NAME_DEF_STMT (base), 0, TDF_NONE);
	}
    }
  fprintf (file, "\n");
}

static bool
stmt_is_inside_loop (class loop *loop, gimple *stmt)
{
  const_basic_block bb = gimple_bb (stmt);

  if (!bb || !flow_bb_inside_loop_p (loop, bb))
    return false;

  return true;
}

static tree
get_range_type (tree type)
{
  if (!TYPE_P (type))
    type = TREE_TYPE (type);

  return POINTER_TYPE_P (type) ? ptrdiff_type_node : type;
}

class symbolic_range
{
  value_range m_value;
  tree m_symbol;
  int m_zero_bits;

public:
  static hash_map<tree, tree> *decl_symbols;

  symbolic_range () : m_symbol (NULL_TREE), m_zero_bits (0) { }

  symbolic_range (tree value_or_type)
  {
    if (TYPE_P (value_or_type))
      set_varying (value_or_type);
    else
      init (value_or_type);
  }

  symbolic_range (tree type, const wide_int &value_int)
  {
    gcc_checking_assert (INTEGRAL_TYPE_P (type));
    init (wide_int_to_tree (type, value_int));
  }

  value_range &value () { return m_value; }
  const value_range &value () const { return m_value; }
  value_range_kind kind () const { return m_value.kind (); }
  tree type () const { return m_value.type (); }
  tree min () const { return m_value.min (); }
  tree max () const { return m_value.max (); }
  tree symbol () const { return m_symbol; }
  int zero_bits () const { return m_zero_bits; }

  bool varying_p () const
  {
    if (m_value.varying_p ())
      {
	gcc_checking_assert (!m_zero_bits);
	return !symbol ();
      }
    return false;
  }

  bool undefined_p () const
  {
    if (m_value.undefined_p ())
      {
	gcc_checking_assert (!m_zero_bits);
	return true;
      }
    return false;
  }

  bool pointer_p () const
  {
    return symbol () || POINTER_TYPE_P (m_value.type ());
  }

  bool full_p () const;

  bool singleton_p (tree *value = NULL) const
  {
    return m_value.singleton_p (value);
  }

  void init (tree);  /* clear m_symbol */
  void set (tree);   /* keep m_symbol */
  void set (tree, tree, value_range_kind = VR_RANGE, int = 0);

  void set_symbol (tree symbol)
  {
    gcc_checking_assert (symbol);
    gcc_checking_assert (types_compatible_p (ptrdiff_type_node,
					     m_value.type ()));
    m_symbol = symbol;
  }

  void set_zero_bits (int zero_bits, bool sync_range = true)
  {
    if (undefined_p ())
      return;

    if (m_zero_bits < zero_bits)
      m_zero_bits = zero_bits;
    else
      m_zero_bits = MAX (zero_bits, 0);

    if (sync_range)
      sync_with_zero_bits ();
  }

  void sync_with_zero_bits ();

  void set_varying (tree type)
  {
    m_symbol = NULL_TREE;
    m_zero_bits = 0;
    m_value.set_varying (type);
  }

  void set_full ()
  {
    gcc_checking_assert (!undefined_p ());

    /* Note: Varying range with non-null symbol is not really varying_p.  */
    if (varying_p ())
      return;

    tree type = m_value.type ();

    if (m_symbol || m_zero_bits)
      set (TYPE_MIN_VALUE (type), TYPE_MAX_VALUE (type), VR_RANGE, -1);
    else
      m_value.set_varying (type);
  }

  void set_undefined ()
  {
    m_symbol = NULL_TREE;
    m_zero_bits = 0;
    m_value.set_undefined ();
  }

  void union_ (const symbolic_range &);
  void union_ (const symbolic_range *other)
  {
    union_ (*other);
  }

  void intersect (const symbolic_range &);
  void intersect (const symbolic_range *other)
  {
    intersect (*other);
  }

  bool intersect_r (const symbolic_range &other)
  {
    symbolic_range orig = *this;

    intersect (other);
    return !equal_p (orig);
  }

  bool intersect_r (const symbolic_range *other)
  {
    return intersect_r (*other);
  }

  bool have_symbol_p (const_tree symbol) const
  {
    return vrp_operand_equal_p (m_symbol, symbol);
  }

  bool same_symbol_p (const symbolic_range &other) const
  {
    return have_symbol_p (other.m_symbol);
  }

  bool equal_p (const symbolic_range &other, bool only_value = false) const
  {
    if (!m_value.equal_p (other.m_value))
      return false;

    if (!only_value)
      return same_symbol_p (other) && m_zero_bits == other.m_zero_bits;
    return true;
  }

  bool operator== (const symbolic_range &other) const
  {
    return equal_p (other);
  }

  bool operator!= (const symbolic_range &other) const
  {
    return !equal_p (other);
  }

  void dump (FILE *file) const;
  void debug () const;
};

hash_map<tree, tree> *symbolic_range::decl_symbols;

inline bool
symbolic_range::full_p () const
{
  if (m_value.varying_p ())
    return true;

  if (m_value.kind () != VR_RANGE)
    return false;

  tree type = m_value.type ();

  if (wi::to_wide (min ()) != wi::min_value (type))
    return false;

  const wide_int max_range = wi::to_wide (max ());
  const wide_int max_value = wi::max_value (type);

  if (m_zero_bits <= 0)
    return max_range == max_value;

  unsigned prec = TYPE_PRECISION (type);
  const wide_int mask = wi::mask (m_zero_bits, true, prec);

  return max_range == wi::bit_and (max_value, mask);
}

void
symbolic_range::init (tree value)
{
  tree type = TREE_TYPE (value);
  tree offset = NULL_TREE;

  m_symbol = NULL_TREE;
  m_zero_bits = 0;

  if (!POINTER_TYPE_P (type))
    {
      set (value);
      return;
    }

  if (TREE_CODE (value) == ADDR_EXPR)
    {
      poly_int64 psize, poffset, pmax_size;
      HOST_WIDE_INT offset_int;
      bool reverse;
      bool known_size = false;
      tree base = get_ref_base_and_extent (TREE_OPERAND (value, 0),
					   &poffset, &psize,
					   &pmax_size, &reverse);

      if (poffset.is_constant (&offset_int))
	{
	  HOST_WIDE_INT size;

	  gcc_assert ((offset_int % BITS_PER_UNIT) == 0);
	  offset = wide_int_to_tree (ptrdiff_type_node,
				     offset_int / BITS_PER_UNIT);

	  if (psize.is_constant (&size) && size >= 0
	      && known_size_p (pmax_size) && !maybe_ne (pmax_size, size))
	    known_size = true;
	}

      if (TREE_CODE (base) == MEM_REF || TREE_CODE (base) == TARGET_MEM_REF)
	{
	  tree op1 = TREE_OPERAND (base, 1);

	  if (offset && !integer_zerop (op1))
	    offset = int_const_binop (PLUS_EXPR, offset,
				      fold_convert (ptrdiff_type_node, op1));

	  m_symbol = TREE_OPERAND (base, 0);
	}
      else if (VAR_P (base))
	{
	  bool existed;
	  tree &base_symbol = decl_symbols->get_or_insert (base, &existed);

	  if (!existed)
	    {
	      if (offset && integer_zerop (offset)
		  && VAR_P (TREE_OPERAND (value, 0)))
		base_symbol = value;
	      else
		base_symbol = build1 (ADDR_EXPR,
				      build_pointer_type (TREE_TYPE (base)),
				      base);
	    }

	  m_symbol = base_symbol;
	}
      else
	{
	  set_varying (type);
	  return;
	}

      if (!offset)
	offset = TYPE_MIN_VALUE (ptrdiff_type_node);

      m_zero_bits = 0;
      if (!known_size)
	set (offset, TYPE_MAX_VALUE (ptrdiff_type_node));
      else
	set (offset);
    }
  else
    {
      m_symbol = value;
      set (build_zero_cst (ptrdiff_type_node));
    }

  gcc_checking_assert (TREE_CODE (m_symbol) == SSA_NAME
		       || (TREE_CODE (m_symbol) == ADDR_EXPR
			   && VAR_P (TREE_OPERAND (m_symbol, 0)))
		       || is_gimple_constant (m_symbol));
}

inline void
symbolic_range::set (tree value)
{
  tree type = TREE_TYPE (value);

  gcc_checking_assert (INTEGRAL_TYPE_P (type));

  if (TREE_CODE (value) == INTEGER_CST)
    {
      if (TREE_OVERFLOW_P (value))
	value = drop_tree_overflow (value);

      m_zero_bits = wi::ctz (wi::to_wide (value));
      m_value.set (value);
    }
  else
    {
      m_zero_bits = 0;
      m_value.set_varying (type);
    }
}

inline void
symbolic_range::set (tree min_, tree max_, value_range_kind kind_,
		     int zero_bits)
{
  tree val;

  if (TREE_OVERFLOW_P (min_))
    min_ = drop_tree_overflow (min_);

  if (TREE_OVERFLOW_P (max_))
    max_ = drop_tree_overflow (max_);

  m_value.set (min_, max_, kind_);

  if (m_value.singleton_p (&val) && TREE_CODE (val) == INTEGER_CST)
    m_zero_bits = wi::ctz (wi::to_wide (val));
  else if (zero_bits < 0)  /* Do not reset zero_bits */
    sync_with_zero_bits ();
  else
    set_zero_bits (zero_bits);
}

void
symbolic_range::sync_with_zero_bits ()
{
  if (!m_zero_bits)
    return;

  tree type = m_value.type ();
  int prec = TYPE_PRECISION (type);

  gcc_checking_assert (INTEGRAL_TYPE_P (type));

  if (prec <= m_zero_bits)
    {
      const wide_int max_int = wi::to_wide (max ());
      const wide_int min_int = wi::to_wide (min ());

      if (m_value.kind () != VR_ANTI_RANGE)
	{
	  if (max_int == 0)
	    {
	      if (min_int != 0)
		m_value.set (max ());
	    }
	  else if (min_int == 0)
	    m_value.set (min ());
	  else if (wi::ltu_p (max_int, max_int - min_int))
	    m_value.set (build_zero_cst (type));
	  else
	    set_undefined ();
	}
      else
	{
	  if (wi::gtu_p (max_int, max_int - min_int))
	    m_value.set (build_zero_cst (type));
	  else
	    set_undefined ();
	}
      return;
    }

  const wide_int mask = wi::mask (m_zero_bits, true, prec);

  if (m_value.kind () != VR_ANTI_RANGE)
    {
      /* X <= ge_int (max), X >= le_int (min) */
      const wide_int ge_int = wi::to_wide (max ());
      const wide_int le_int = wi::to_wide (min ());
      wide_int new_ge_int = wi::bit_and (ge_int, mask);
      wide_int new_le_int = wi::bit_and (le_int, mask);

      if (ge_int != new_ge_int)
	{
	  if (wi::gt_p (le_int, new_ge_int, TYPE_SIGN (type)))
	    {
	      set_undefined ();
	      return;
	    }

	  m_value.set (min (), wide_int_to_tree (type, new_ge_int));
	}

      if (le_int != new_le_int)
	{
	  new_le_int += wi::set_bit_in_zero (m_zero_bits, prec);

	  m_value.set (wide_int_to_tree (type, new_le_int), max ());
	}
    }
  else
    {
      /* X <= ge_int (min - 1), X >= le_int (max + 1) */
      const wide_int ge_int = wi::to_wide (min ()) - 1;
      const wide_int le_int = wi::to_wide (max ()) + 1;
      wide_int new_ge_int = wi::bit_and (ge_int, mask);
      wide_int new_le_int = wi::bit_and (le_int, mask);
      bool ge_is_same = true;
      bool le_is_same = true;

      if (ge_int != new_ge_int)
	{
	  if (wi::gtu_p (ge_int - new_ge_int, ge_int - le_int))
	    {
	      set_undefined ();
	      return;
	    }
	  ge_is_same = false;
	}

      if (le_int != new_le_int)
	{
	  new_le_int += wi::set_bit_in_zero (m_zero_bits, prec);
	  le_is_same = false;
	}

      if (le_is_same && ge_is_same)
	return;

      if (wi::gt_p (new_le_int, new_ge_int, TYPE_SIGN (type)))
	{
	  tree n_min = min ();
	  tree n_max = max ();

	  if (!ge_is_same)
	    n_min = wide_int_to_tree (type, new_ge_int + 1);

	  if (!le_is_same)
	    n_max = wide_int_to_tree (type, new_le_int - 1);

	  m_value.set (n_min, n_max, m_value.kind ());
	}
      else
	m_value.set (wide_int_to_tree (type, new_le_int),
		     wide_int_to_tree (type, new_ge_int));
    }
}

void
symbolic_range::union_ (const symbolic_range &other)
{
  if (varying_p () || other.undefined_p ())
    return;

  if (undefined_p () || other.varying_p ())
    {
      *this = other;
      return;
    }

  if (!same_symbol_p (other))
    {
      set_varying (TREE_TYPE (m_symbol ? m_symbol : min ()));
      return;
    }

  if (m_zero_bits > other.m_zero_bits)
    m_zero_bits = other.m_zero_bits;

  m_value.union_ (other.m_value);

  /* We may get a varying value range, and normalize its bound when there
     are zero-bits.  */
  if (m_zero_bits)
    sync_with_zero_bits ();
}

void
symbolic_range::intersect (const symbolic_range &other)
{
  if (undefined_p () || other.varying_p ())
    return;

  if (other.undefined_p ())
    {
      set_undefined ();
      return;
    }

  if (varying_p ())
    {
      *this = other;
      return;
    }

  if (!same_symbol_p (other))
    return;

  if (!other.full_p ())
    {
      if (m_zero_bits && full_p ())
	m_value.set_varying (m_value.type ());

      m_value.intersect (other.m_value);

      if (m_value.kind () == VR_UNDEFINED)
	{
	  m_symbol = NULL_TREE;
	  m_zero_bits = 0;
	  return;
	}
    }

  if (m_zero_bits < other.m_zero_bits)
    m_zero_bits = other.m_zero_bits;

  if (m_zero_bits)
    sync_with_zero_bits ();
}

void
symbolic_range::dump (FILE *file) const
{
  if (m_symbol)
    {
      print_generic_expr (file, TREE_TYPE (m_symbol));
      fprintf (file, " [");
      print_generic_expr (file, m_symbol, TDF_NONE);
      fprintf (file, "], ");
    }

  if (!undefined_p () && !varying_p ())
    {
      if (m_zero_bits < 10)
	fprintf (file, "%d, ", 1 << m_zero_bits);
      else
	fprintf (file, "2^%d, ", m_zero_bits);
    }

  m_value.dump (file);
}

void
symbolic_range::debug () const
{
  dump (stderr);
  fprintf (stderr, "\n");
}

/* A wrapper to handle symbolic value range unary computation.  */

static void
symbolic_range_fold_unary_expr (symbolic_range *vr,
				enum tree_code code, tree expr_type,
				const symbolic_range *vr0,
				tree vr0_type)
{
  if (vr0->undefined_p ())
    {
      vr->set_undefined ();
      return;
    }

  vr->set_varying (expr_type);

  if (CONVERT_EXPR_CODE_P (code))
    {
      if (POINTER_TYPE_P (expr_type))
	{
	  if (POINTER_TYPE_P (vr0_type))
	    *vr = *vr0;
	  return;
	}

      if (POINTER_TYPE_P (vr0_type) || vr0->varying_p ())
	return;
    }
  else
    {
      gcc_checking_assert (!POINTER_TYPE_P (expr_type));
      gcc_checking_assert (!vr0->pointer_p ());
    }

  range_fold_unary_expr (&vr->value (), code, expr_type, &vr0->value (),
			 vr0_type);

  switch (code)
    {
      CASE_CONVERT:
      case NEGATE_EXPR:
      case ABS_EXPR:
      case ABSU_EXPR:
	vr->set_zero_bits (vr0->zero_bits ());
	break;

      default:
	break;
    }
}

static void
symbolic_range_fold_unary_expr (enum tree_code code, tree expr_type,
				symbolic_range *vr0,
				tree vr0_type)
{
  symbolic_range tmp_vr;

  symbolic_range_fold_unary_expr (&tmp_vr, code, expr_type, vr0, vr0_type);
  *vr0 = tmp_vr;
}

/* A wrapper to handle symbolic value range binary computation.  */

static void
symbolic_range_fold_binary_expr (symbolic_range *vr,
				 enum tree_code code,
				 tree expr_type,
				 const symbolic_range *vr0,
				 const symbolic_range *vr1)
{
  if (vr0->undefined_p () || vr1->undefined_p ())
    {
      vr->set_undefined ();
      return;
    }

  vr->set_varying (expr_type);

  if (code == POINTER_PLUS_EXPR)
    {
      gcc_checking_assert (POINTER_TYPE_P (expr_type));
      code = PLUS_EXPR;
    }

  if (code == PLUS_EXPR && POINTER_TYPE_P (expr_type))
    {
      gcc_checking_assert (vr0->pointer_p () && !vr1->pointer_p ());

      if (vr0->varying_p ())
	return;

      value_range tmp_range;

      range_fold_unary_expr (&tmp_range, CONVERT_EXPR, ptrdiff_type_node,
			     &vr1->value (), vr1->type ());
      range_fold_binary_expr (&vr->value (), PLUS_EXPR, ptrdiff_type_node,
			      &vr0->value (), &tmp_range);
      vr->set_symbol (vr0->symbol ());
    }
  else if (code == POINTER_DIFF_EXPR)
    {
      gcc_checking_assert (vr0->pointer_p () && vr1->pointer_p ());

      if (vr0->varying_p () || vr1->varying_p () || !vr0->same_symbol_p (*vr1))
	return;

      code = MINUS_EXPR;
      range_fold_binary_expr (&vr->value (), code, expr_type, &vr0->value (),
			      &vr1->value ());
    }
  else if (code == MIN_EXPR || code == MAX_EXPR)
    {
      if (!vr0->same_symbol_p (*vr1) || vr0->varying_p () || vr1->varying_p ())
	return;

      range_fold_binary_expr (&vr->value (), code, get_range_type (expr_type),
			      &vr0->value (), &vr1->value ());

      if (vr0->symbol ())
	vr->set_symbol (vr0->symbol ());
    }
  else if (POINTER_TYPE_P (expr_type))
    return;
  else
    {
      gcc_checking_assert (!vr0->pointer_p () && !vr1->pointer_p ());

      range_fold_binary_expr (&vr->value (), code, expr_type, &vr0->value (),
			      &vr1->value ());
    }

  int zb0 = vr0->zero_bits ();
  int zb1 = vr1->zero_bits ();
  int zb_new = 0;

  switch (code)
    {
      case PLUS_EXPR:
      case MINUS_EXPR:
      case TRUNC_MOD_EXPR:
      case CEIL_MOD_EXPR:
      case FLOOR_MOD_EXPR:
      case ROUND_MOD_EXPR:
      case MIN_EXPR:
      case MAX_EXPR:
      case BIT_IOR_EXPR:
      case BIT_XOR_EXPR:
	zb_new = MIN (zb0, zb1);
	break;

      case BIT_AND_EXPR:
	zb_new = MAX (zb0, zb1);
	break;

      case MULT_EXPR:
	zb_new = zb0 + zb1;
	break;

      case TRUNC_DIV_EXPR:
      case CEIL_DIV_EXPR:
      case FLOOR_DIV_EXPR:
      case ROUND_DIV_EXPR:
	if (zb0 > zb1)
	  {
	    tree cst;

	    if (vr1->singleton_p (&cst)
		&& TREE_CODE (cst) == INTEGER_CST
		&& wi::popcount (wi::abs (wi::to_wide (cst))) == 1)
	    zb_new = zb0 - zb1;
	  }
	break;

      case LSHIFT_EXPR:
      case RSHIFT_EXPR:
      case RROTATE_EXPR:
	{
	  wide_int min_int = wi::to_wide (vr1->min ());
	  HOST_WIDE_INT shift;

	  if (wi::fits_shwi_p (min_int))
	    shift = min_int.to_shwi ();
	  else
	    shift = -1;

	  if (code == LSHIFT_EXPR)
	    {
	      if (shift < 0)
		zb_new = zb0;
	      else if (shift >= INT_MAX - zb0)
		zb_new = INT_MAX;
	      else
		zb_new = (int)(shift + zb0);
	    }
	  else if (shift >= 0 && shift < zb0)
	    zb_new = zb0 - shift;

	  break;
	}

      default:
	break;
    }

  vr->set_zero_bits (zb_new);
}

static void
symbolic_range_fold_binary_expr (enum tree_code code,
				 tree expr_type,
				 symbolic_range *vr0,
				 const symbolic_range *vr1)
{
  symbolic_range tmp_vr;

  symbolic_range_fold_binary_expr (&tmp_vr, code, expr_type, vr0, vr1);
  *vr0 = tmp_vr;
}

class symbolic_range_table
{
protected:
  symbolic_range *sr_values;
  hash_map <tree, tree> decl_symbols;

public:
  static unsigned ssa_name_version (const tree name)
  {
    gcc_checking_assert (name && !SSA_NAME_IS_VIRTUAL_OPERAND (name));
    gcc_checking_assert (!SSA_NAME_IN_FREE_LIST (name));
    return SSA_NAME_VERSION (name);
  }

  symbolic_range &get_range (const tree name)
  {
    return sr_values[ssa_name_version (name)];
  }

  symbolic_range get_range (const tree name, const wide_int &value_int)
  {
    const symbolic_range &range = get_range (name);

    if (range.undefined_p () || value_int == 0)
      return range;

    symbolic_range new_range;
    const symbolic_range cst_range (range.type (), value_int);

    symbolic_range_fold_binary_expr (&new_range, PLUS_EXPR, TREE_TYPE (name),
				     &range, &cst_range);
    return new_range;
  }

  symbolic_range get_range_from_tree (tree name)
  {
    if (TREE_CODE (name) == SSA_NAME)
      return get_range (name);
    return symbolic_range (name);
  }

  symbolic_range_table () : sr_values (NULL)
  {
    symbolic_range::decl_symbols = &decl_symbols;
  }

  ~symbolic_range_table ()
  {
    symbolic_range::decl_symbols = NULL;
    delete[] sr_values;
  }
};

struct ssa_predicate
{
  tree_code op;
  tree opnd;
};

/* cmp (name + value)  */
class compare_operand
{
  void init (tree name_or_type, const wide_int &wi_cst, bool overflow_)
  {
    if (TYPE_P (name_or_type))
      name = build_int_cst (name_or_type, 0);
    else
      name = name_or_type;

    value = wide_int_to_tree (get_range_type (name_or_type), wi_cst);
    overflow = wi_cst != 0 ? overflow_ : false;
  }

public:
  static symbolic_range_table *range_table;

  tree name;
  tree value;

  /* NOTE: For pointer, no-overflow also means "name + value" is
     inside data object pointed by "name".  */
  bool overflow;

  compare_operand (tree name_or_type, const wide_int &wi_cst, bool overflow_)
  {
    init (name_or_type, wi_cst, overflow_);
  }

  compare_operand (tree name_or_type, HOST_WIDE_INT cst = 0,
		   bool overflow_ = true)
  {
    tree type = get_range_type (name_or_type);

    init (name_or_type, wi::shwi (cst, TYPE_PRECISION (type)), overflow_);
  }

  tree name_type () const
  {
    return TREE_TYPE (name);
  }

  tree value_type () const
  {
    return TREE_TYPE (value);
  }

  bool name_is_ssa_p () const
  {
    return TREE_CODE (name) == SSA_NAME;
  }

  bool name_is_cvt_p () const
  {
    return TREE_CODE (name) == NOP_EXPR;
  }

  tree name_to_ssa () const
  {
    if (name_is_ssa_p ())
      return name;

    tree opnd = TREE_OPERAND (name, 0);

    gcc_checking_assert (name_is_cvt_p ());
    gcc_checking_assert (TREE_CODE (opnd) == SSA_NAME);

    return opnd;
  }

  void update_overflow (bool reset = false);

  int compare (const compare_operand *other);

  void set_name (const tree new_name)
  {
    tree new_type = TREE_TYPE (new_name);

    gcc_checking_assert (TREE_CODE (new_name) == SSA_NAME);

    if (types_compatible_p (name_type (), new_type))
      name = new_name;
    else
      {
	gcc_checking_assert (INTEGRAL_TYPE_P (name_type ()));
	gcc_checking_assert (INTEGRAL_TYPE_P (new_type));
	gcc_checking_assert (TYPE_PRECISION (name_type ())
			     == TYPE_PRECISION (new_type));

	name = fold_convert (name_type (), new_name);
      }
  }

  void set_value (const tree value_int, bool update = true)
  {
    gcc_checking_assert (types_compatible_p (value_type (),
			 TREE_TYPE (value_int)));
    value = value_int;

    if (update)
      update_overflow (true);
  }

  template <typename T>
  void set_value (const T &value_int, bool update = true)
  {
    set_value (wide_int_to_tree (value_type (), value_int), update);
  }

  symbolic_range name_range () const;

  symbolic_range range () const;

  bool can_derive_compare_p (const tree other, const wide_int &add_int,
			     bool is_le);

  bool adjust_value (const tree add_value, bool plus);

  bool combine (const tree other, const wide_int &add_int,
		bool other_overflow, bool is_le);

  bool convert (const tree type, bool is_le);
};

symbolic_range_table *compare_operand::range_table;

symbolic_range
compare_operand::name_range () const
{
  symbolic_range &range = range_table->get_range (name_to_ssa ());

  if (name_is_ssa_p () || range.undefined_p ())
    return range;

  symbolic_range cvt_range;

  symbolic_range_fold_unary_expr (&cvt_range, CONVERT_EXPR, value_type (),
				  &range, range.type ());
  return cvt_range;
}

symbolic_range
compare_operand::range () const
{
  if (integer_zerop (value))
    return name_range ();

  symbolic_range range;
  const symbolic_range tmp_range = name_range ();
  const symbolic_range cst_range (value);

  symbolic_range_fold_binary_expr (&range, PLUS_EXPR, name_type (),
				   &tmp_range, &cst_range);
  return range;
}

void
compare_operand::update_overflow (bool reset)
{
  if (reset)
    overflow = true;
  else if (!overflow)
    return;

  const wide_int value_int = wi::to_wide (value);

  if (value_int == 0)
    {
      overflow = false;
      return;
    }

  const symbolic_range range = name_range ();

  if (range.kind () != VR_RANGE)
    return;

  if (POINTER_TYPE_P (name_type ()))
    {
      if (TYPE_OVERFLOW_UNDEFINED (name_type ()))
	{
	  const wide_int &value_int = wi::to_wide (value);

	  /* Check whether a pointer with a negative offset overflows by
	     using range information against root base address.  */
	  if (wi::neg_p (value_int))
	    {
	      const wide_int &min_int = wi::to_wide (range.min ());

	      if (!wi::neg_p (min_int)
		  && !wi::neg_p (value_int + min_int))
		overflow = false;
	    }
	  else
	    {
	      const wide_int &max_int = wi::to_wide (range.max ());

	      if (wi::neg_p (max_int) && wi::les_p (max_int, -value_int))
		overflow = false;
	    }
	}
      return;
    }

  signop sign = TYPE_SIGN (value_type ());
  wi::overflow_type wi_ovf;

  wi::add (wi::to_wide (range.min ()), value_int, sign, &wi_ovf);

  if (wi_ovf != wi::OVF_NONE)
    return;

  wi::add (wi::to_wide (range.max ()), value_int, sign, &wi_ovf);

  if (wi_ovf != wi::OVF_NONE)
    return;

  overflow = false;
}

int
compare_operand::compare (const compare_operand *other)
{
  if (POINTER_TYPE_P (name_type ()))
    {
      /* Ensure range of compare_operand's "name" based on root address
	 does not wrap around.  */
      if (!TYPE_OVERFLOW_UNDEFINED (name_type ()))
	return 0;

      /* Ensure range of compare_operand's "name" + "value" does not
	 wrap around.  */
      if (overflow || other->overflow)
	return 0;
    }

  signop sign = TYPE_SIGN (value_type ());

  if (operand_equal_p (name, other->name))
    {
      const symbolic_range range = name_range ();

      if (range.kind () != VR_RANGE)
	return 0;

      wide_int value_int_0 = wi::to_wide (value);
      wide_int value_int_1 = wi::to_wide (other->value);
      wide_int min_int_0 = wi::to_wide (range.min ()) + value_int_0;
      wide_int max_int_0 = wi::to_wide (range.max ()) + value_int_0;
      wide_int min_int_1 = wi::to_wide (range.min ()) + value_int_1;
      wide_int max_int_1 = wi::to_wide (range.max ()) + value_int_1;

      if (wi::lt_p (min_int_0, max_int_0, sign)
	  && wi::lt_p (min_int_1, max_int_1, sign))
	return wi::lt_p (min_int_1, min_int_0, sign) ? 1 : -1;
    }

  const symbolic_range range_0 = range ();

  if (range_0.kind () != VR_RANGE)
    return 0;

  const symbolic_range range_1 = other->range ();

  if (range_1.kind () != VR_RANGE)
    return 0;

  if (wi::le_p (wi::to_wide (range_1.max ()),
		wi::to_wide (range_0.min ()), sign))
    return 1;

  if (wi::le_p (wi::to_wide (range_0.max ()),
		wi::to_wide (range_1.min ()), sign))
    return -1;

  return 0;
}

/* Suppose that OTHER_NAME {<= | >=} compare_operand, whether this relation
   can be maintained for OTHER_NAME + ADD_INT {<= | >=} compare_operand +
   ADD_INT according to range information.  */

bool
compare_operand::can_derive_compare_p (const tree other,
				       const wide_int &add_int,
				       bool is_le)
{
  const symbolic_range &other_range = range_table->get_range (other);

  if (other_range.kind () != VR_RANGE)
    return false;

  const symbolic_range this_range = range ();

  if (this_range.kind () != VR_RANGE)
    return false;

  signop sign = TYPE_SIGN (value_type ());
  wide_int wrap_point;

  if (wi::neg_p (add_int, sign))
    wrap_point = wi::min_value (value_type ()) - add_int - 1;
  else
    wrap_point = wi::max_value (value_type ()) - add_int;

  if (is_le)
    {
      if (wi::gt_p (wi::to_wide (other_range.min ()), wrap_point, sign))
	return true;

      if (wi::le_p (wi::to_wide (this_range.max ()), wrap_point, sign))
	return true;
    }
  else
    {
      if (wi::le_p (wi::to_wide (other_range.max ()), wrap_point, sign))
	return true;

      if (wi::gt_p (wi::to_wide (this_range.min ()), wrap_point, sign))
	return true;
    }

  return false;
}

static bool
valid_compare_value_p (const wide_int &add_int, const tree type)
{
  if (TYPE_UNSIGNED (type))
    return true;

  return add_int != wi::min_value (type) && add_int != wi::max_value (type);
}

static bool
adjust_compare_value (const tree value, const wide_int &add_int,
		      wide_int &res_int)
{
  tree type = TREE_TYPE (value);

  if (TYPE_UNSIGNED (type))
    {
      res_int = wi::to_wide (value) + add_int;
      return true;
    }
  else
    {
      wi::overflow_type overflow;

      res_int = wi::add (wi::to_wide (value), add_int, TYPE_SIGN (type),
			 &overflow);

      if (overflow != wi::OVF_NONE)
	return false;

      return valid_compare_value_p (res_int, type);
    }
}

bool
compare_operand::adjust_value (const tree add_value, bool plus)
{
  if (integer_zerop (add_value))
    return true;

  wide_int add_int = wi::to_wide (add_value);
  wide_int res_int;

  if (!plus)
    add_int = -add_int;

  if (!valid_compare_value_p (add_int, value_type ()))
    return false;

  if (!adjust_compare_value (value, add_int, res_int))
    return false;

  set_value (res_int);

  return true;
}

static bool
range_wrap_p (const symbolic_range &range, const wide_int &value)
{
  if (value == 0)
    return false;

  if (range.kind () != VR_RANGE)
    return true;

   signop sign = TYPE_SIGN (range.type ());

  if (wi::neg_p (value))
    {
      wide_int min_int = wi::to_wide (range.min ());
      wide_int min_limit = wi::min_value (range.type ());

      return wi::lt_p (min_int, min_limit - value, sign);
    }
  else
    {
      wide_int max_int = wi::to_wide (range.max ());
      wide_int max_limit = wi::max_value (range.type ());

      return wi::gt_p (max_int, max_limit - value, sign);
   }
}

/* Given OTHER and constant ADD_INT, check when
     o. X {<= | >=} OTHER + ADD_INT
     o. OTHER {<= | >=} compare_operand
   whether X {<= | >=} compare_operand + ADD_INT.  */

bool
compare_operand::combine (const tree other,
			  const wide_int &add_int,
			  bool other_overflow,
			  bool is_le)
{
  wide_int new_int;
  bool new_overflow = true;
  bool check_by_range = true;
  tree type = name_type ();

  gcc_checking_assert (types_compatible_p (TREE_TYPE (other), type));

  if (!adjust_compare_value (value, add_int, new_int))
    return false;

  if (TYPE_UNSIGNED (value_type ()))
    {
      /* For unsigned integer type, overflow means value wrap.  And we
	 only use a simple check for unsigned type here, which could
	 be extended later.  */
      if (!is_le && !other_overflow)
	{
	  new_overflow = overflow;
	  check_by_range = false;
	}
    }
  else if (!other_overflow)
    {
      if (wi::neg_p (add_int) == is_le)
	{
	  /* 1. name_a <= name_b + v1  (v1 <  0)
		name_b <= name_c + v2  (v2 >= 0)

		name_b + v1 no-overflow  ->  name_b >= min - v1
		name_c + v2 overflow     ->  name_b <  min + v2

	     2. name_a >= name_b + v1  (v1 >  0)
		name_b >= name_c + v2  (v2 <= 0)

		name_b + v1 no-overflow  ->  name_b <= max - v1
		name_c + v2 overflow     ->  name_b >  max + v2

	     If min + v2 <= min - v1 (v1 + v2 <= 0) for 1, or
		max + v2 >= max - v1 (v1 + v2 >= 0) for 2,

	     it causes an empty set for name_b, which means
	     name_c + v2 does not overflow in the situation.  */
	  if (!overflow)
	    new_overflow = false;
	  else if (new_int == 0)
	    new_overflow = false;
	  else if (wi::neg_p (new_int) == is_le)
	    {
	      if (is_le)
		new_overflow = wi::lts_p (new_int, add_int);
	      else
		new_overflow = wi::gts_p (new_int, add_int);
	    }
	  check_by_range = false;
	}
      else if (!overflow)
	{
	  if (new_int == 0 || (wi::neg_p (new_int) == is_le))
	    {
	      new_overflow = false;
	      check_by_range = false;
	    }
	  else if (POINTER_TYPE_P (type))
	    {
	      symbolic_range &range = range_table->get_range (name);

	      if (!range_wrap_p (range, new_int))
		{
		  new_overflow = false;
		  check_by_range = false;
		}
	    }
	}
    }

  if (check_by_range)
    {
      if (POINTER_TYPE_P (type))
	return false;

      if (!can_derive_compare_p (other, add_int, is_le))
	return false;
    }

  set_value (new_int, false);

  overflow = new_overflow;
  update_overflow ();

  if (overflow
      && !TYPE_OVERFLOW_UNDEFINED (type) && !TYPE_OVERFLOW_WRAPS (type))
    return false;

  return true;
}

/* Convert same-sized signed compare to unsigned, or same-sized unsigned to
   signed.  Here is an assumption that value range is [0 - signed_max].  */

bool
compare_operand::convert (const tree type, bool is_le)
{
  tree orig_type = name_type ();
  bool is_unsigned = TYPE_UNSIGNED (orig_type);

  gcc_checking_assert (INTEGRAL_TYPE_P (type));

  if (is_unsigned == is_le)
    {
      const symbolic_range this_range = range ();

      if (this_range.kind () != VR_RANGE)
	return false;

      if (wi::neg_p (wi::to_wide (is_le ? this_range.max ()
					: this_range.min ())))
	return false;
    }

  tree ssa = name_to_ssa ();

  if (types_compatible_p (TREE_TYPE (ssa), type))
    {
      name = ssa;
      value = fold_convert (TREE_TYPE (ssa), value);
    }
  else
    {
      name = fold_convert (type, ssa);
      value = fold_convert (type, value);
    }

  if (wi::neg_p (wi::to_wide (value)))
    {
      if (is_unsigned)
	update_overflow ();
      else
	overflow = true;
    }

  return true;
}

class ssa_constraint
{
public:
  vec<compare_operand> le_opnds;  /* <= operand */
  vec<compare_operand> ge_opnds;  /* >= operand */
  bool undefined;

  ssa_constraint (bool undefined)
  : le_opnds (vNULL), ge_opnds (vNULL), undefined (undefined)
  { }

  ssa_constraint (vec<compare_operand> le_opnds_ = vNULL,
		  vec<compare_operand> ge_opnds_ = vNULL)
  : le_opnds (le_opnds_)
  , ge_opnds (ge_opnds_)
  , undefined (false)
  { }

  ssa_constraint (ssa_constraint &temp, bool copy = false)
  {
    if (copy)
      {
	le_opnds = temp.le_opnds.copy ();
	ge_opnds = temp.ge_opnds.copy ();
      }
    else
      {
	le_opnds = temp.le_opnds;
	ge_opnds = temp.ge_opnds;

	temp.le_opnds = vNULL;
	temp.ge_opnds = vNULL;
      }

    undefined = temp.undefined;
  }

  ~ssa_constraint ()
  {
    le_opnds.release ();
    ge_opnds.release ();
  }

  static compare_operand *find (vec<compare_operand> &cmp_opnds,
				const tree name);

  static vec<compare_operand> derive (const tree name,
				      const tree add_value,
				      bool plus,
				      bool overflow,
				      const vec<compare_operand> &cmp_opnds,
				      bool is_le);

  static vec<compare_operand> derive (const compare_operand *base_cmp_opnd,
				      const vec<compare_operand> &cmp_opnds,
				      bool is_le);

  static bool union_ (vec<compare_operand> &cmp_opnds_0,
		      vec<compare_operand> &cmp_opnds_1,
		      bool is_le);

  static bool intersect (vec<compare_operand> &cmp_opnds_0,
			 const compare_operand *cmp_opnd_1,
			 bool is_le);

  static bool intersect (vec<compare_operand> &cmp_opnds_0,
			 const vec<compare_operand> &cmp_opnds_1,
			 bool is_le);

  static void dump (FILE *file, vec<compare_operand> &cmp_opnds);

  bool union_ (ssa_constraint &other);

  bool intersect (const ssa_constraint &other);
  bool intersect (const vec<compare_operand> &cmp_opnds, bool is_le);
  bool intersect (const compare_operand *cmp_opnd, bool is_le);
  bool intersect (tree name, bool is_le);

  void copy (const ssa_constraint &other)
  {
    le_opnds = other.le_opnds.copy ();
    ge_opnds = other.ge_opnds.copy ();
    undefined = other.undefined;
  }

  bool varying_p () const
  {
    return le_opnds.is_empty () && ge_opnds.is_empty () && !undefined;
  }

  bool undefined_p () const
  {
    return undefined;
  }

  void set_varying ()
  {
    le_opnds.release ();
    ge_opnds.release ();
    undefined = false;
  }

  void set_undefined ()
  {
    le_opnds.release ();
    ge_opnds.release ();
    undefined = true;
  }

  vec<compare_operand> &get_operands (bool is_le)
  {
    if (is_le)
      return le_opnds;
    return ge_opnds;
  }

  void dump (FILE *file);
  void debug (bool nl = true);
};

compare_operand *
ssa_constraint::find (vec<compare_operand> &cmp_opnds, const tree name)
{
  for (auto &opnd : cmp_opnds)
    {
      if (operand_equal_p (opnd.name, name))
	return &opnd;
    }

  return NULL;
}

/* For item (name [<=, >=] item) in cmp_opnds, collect those also satisfies
   that name + add_value [<=, >=] item + add_value.  */

vec<compare_operand>
ssa_constraint::derive (const tree name,
			const tree add_value,
			bool plus,
			bool overflow, /* name + add_value may overflow */
			const vec<compare_operand> &cmp_opnds,
			bool is_le)
{
  if (integer_zerop (add_value))
    return cmp_opnds.copy ();

  wide_int add_int = wi::to_wide (add_value);

  if (!plus)
    add_int = -add_int;

  if (!valid_compare_value_p (add_int, get_range_type (name)))
    return vNULL;

  vec<compare_operand> new_cmp_opnds = vNULL;

  for (auto cmp_opnd : cmp_opnds)
    {
      if (cmp_opnd.combine (name, add_int, overflow, is_le))
	new_cmp_opnds.safe_push (cmp_opnd);
    }

  return new_cmp_opnds;
}

vec<compare_operand>
ssa_constraint::derive (const compare_operand *base_opnd,
			const vec<compare_operand> &cmp_opnds,
			bool is_le)
{
  tree other_name = base_opnd->name;

  gcc_checking_assert (TREE_CODE (other_name) == SSA_NAME);

  return derive (other_name, base_opnd->value, true,
		 base_opnd->overflow, cmp_opnds, is_le);
}

bool
ssa_constraint::union_ (vec<compare_operand> &cmp_opnds_0,
			vec<compare_operand> &cmp_opnds_1,
			bool is_le)
{
  bool changed = false;

  for (unsigned i = 0; i < cmp_opnds_0.length (); i++)
    {
      auto &cmp_opnd_0 = cmp_opnds_0[i];

      if (auto opnd = find (cmp_opnds_1, cmp_opnd_0.name))
	{
	  auto &cmp_opnd_1 = *opnd;

	  if (operand_equal_p (cmp_opnd_0.value, cmp_opnd_1.value))
	    continue;

	  if (!cmp_opnd_0.overflow && !cmp_opnd_1.overflow)
	    {
	      if (tree_int_cst_lt (cmp_opnd_1.value,
				   cmp_opnd_0.value) ^ is_le)
		{
		  cmp_opnd_0.value = cmp_opnd_1.value;
		  changed = true;
		}
	      continue;
	    }

	  if (POINTER_TYPE_P (cmp_opnd_0.name_type ()))
	    {
	      /* When pointer might wrap around, it is meaningless to use
		 range information based on a symbolic address.  */
	      cmp_opnds_0.unordered_remove (i--);
	      changed = true;
	      continue;
	    }
	  else if (int cmp = cmp_opnd_0.compare (&cmp_opnd_1))
	    {
	      if ((cmp > 0) ^ is_le)
		{
		  cmp_opnd_0 = cmp_opnd_1;
		  changed = true;
		}
	      continue;
	    }
	}

      bool remove = true;

      for (const auto &cmp_opnd_1 : cmp_opnds_1)
	{
	  if (operand_equal_p (cmp_opnd_0.name, cmp_opnd_1.name))
	    continue;

	  if (int cmp = cmp_opnd_0.compare (&cmp_opnd_1))
	    {
	      if ((cmp < 0) ^ is_le)
		remove = false;
	      else if (!find (cmp_opnds_0, cmp_opnd_1.name))
		{
		  cmp_opnd_0 = cmp_opnd_1;
		  changed = true;
		  remove = false;
		}
	      break;
	    }
	}

      if (remove)
	{
	  cmp_opnds_0.unordered_remove (i--);
	  changed = true;
	}
    }

  return changed;
}

bool
ssa_constraint::intersect (vec<compare_operand> &cmp_opnds_0,
			   const compare_operand *cmp_opnd_1,
			   bool is_le)
{
  compare_operand *cmp_opnd_0 = find (cmp_opnds_0, cmp_opnd_1->name);

  if (!cmp_opnd_0)
    {
      cmp_opnds_0.safe_push (*cmp_opnd_1);
      return true;
    }

  if (operand_equal_p (cmp_opnd_0->value, cmp_opnd_1->value))
    return false;

  if (cmp_opnd_0->overflow || cmp_opnd_1->overflow)
    {
      int cmp = cmp_opnd_0->compare (cmp_opnd_1);

      if (!cmp)
	return false;

      if ((cmp < 0) ^ is_le)
	{
	  *cmp_opnd_0 = *cmp_opnd_1;
	  return true;
	}
    }
  else if (tree_int_cst_lt (cmp_opnd_0->value, cmp_opnd_1->value) ^ is_le)
    {
      cmp_opnd_0->value = cmp_opnd_1->value;
      return true;
    }

  return false;
}

bool
ssa_constraint::intersect (vec<compare_operand> &cmp_opnds_0,
			   const vec<compare_operand> &cmp_opnds_1,
			   bool is_le)
{
  bool changed = false;

  for (auto &cmp_opnd_1 : cmp_opnds_1)
    changed |= intersect (cmp_opnds_0, &cmp_opnd_1, is_le);

  return changed;
}

bool
ssa_constraint::union_ (ssa_constraint &other)
{
  bool changed = false;

  if (varying_p () || other.undefined_p ())
    return false;

  if (undefined_p ())
    {
      copy (other);
      return true;
    }

  if (other.varying_p ())
    {
      set_varying ();
      return true;
    }

  changed |= union_ (le_opnds, other.le_opnds, true);
  changed |= union_ (ge_opnds, other.ge_opnds, false);

  return changed;
}

bool
ssa_constraint::intersect (const ssa_constraint &other)
{
  bool changed = false;

  if (undefined_p ())
    return false;

  if (other.undefined_p ())
    {
      set_undefined ();
      return true;
    }

  changed |= intersect (other.le_opnds, true);
  changed |= intersect (other.ge_opnds, false);

  return changed;
}

bool
ssa_constraint::intersect (const compare_operand *cmp_opnd, bool is_le)
{
  if (undefined_p ())
    return false;

  return intersect (get_operands (is_le), cmp_opnd, is_le);
}

bool
ssa_constraint::intersect (tree name, bool is_le)
{
  compare_operand cmp_opnd (name);

  return intersect (&cmp_opnd, is_le);
}

bool
ssa_constraint::intersect (const vec<compare_operand> &cmd_opnds, bool is_le)
{
  if (undefined_p () || cmd_opnds.is_empty ())
    return false;

  return intersect (get_operands (is_le), cmd_opnds, is_le);
}

void
ssa_constraint::dump (FILE *file, vec<compare_operand> &cmp_opnds)
{
  if (cmp_opnds.is_empty ())
    {
      fprintf (file, "{ }");
      return;
    }
  fprintf (file, "{ ");
  for (unsigned i = 0; i < cmp_opnds.length (); i++)
    {
      const compare_operand &cmp_opnd = cmp_opnds[i];
      int sign = tree_int_cst_sgn (cmp_opnd.value);

      if (i)
	fprintf (file, ", ");

      print_generic_expr (file, cmp_opnd.name);

      if (sign == 1)
	fprintf (file, "+");

      if (sign)
	print_generic_expr (file, cmp_opnd.value);

      if (cmp_opnd.overflow)
	fprintf (file, " <OV>");
    }
  fprintf (file, " }");
}

void
ssa_constraint::dump (FILE *file)
{
  if (undefined_p ())
    fprintf (file, "UNDEFINED");
  else
    {
      dump (file, ge_opnds);
      fprintf (file, " - ");
      dump (file, le_opnds);
    }
}

void
ssa_constraint::debug (bool nl)
{
  dump (stderr);

  if (nl)
    fprintf (stderr, "\n");
}

static bool
ssa_strictly_dominated_by_p (tree name, gimple *stmt)
{
  gimple *def_stmt = SSA_NAME_DEF_STMT (name);

  gcc_checking_assert (gimple_bb (stmt));

  if (SSA_NAME_IS_DEFAULT_DEF (name))
    return false;

  gcc_checking_assert (def_stmt->uid && stmt->uid);

  if (def_stmt->uid <= stmt->uid)
    return false;

  return dominated_by_p (CDI_DOMINATORS, gimple_bb (def_stmt),
			 gimple_bb (stmt));
}

static bool
ssa_strictly_dominated_by_p (tree name1, tree name2)
{
  if (SSA_NAME_IS_DEFAULT_DEF (name2))
    {
      if (!SSA_NAME_IS_DEFAULT_DEF (name1))
	return true;

      return SSA_NAME_VERSION (name1) > SSA_NAME_VERSION (name2);
    }

  return ssa_strictly_dominated_by_p (name1, SSA_NAME_DEF_STMT (name2));
}

class aff_form : public aff_tree
{
public:
  bool valid;
  int additive;
  tree real_depv;

  aff_form ()
   : valid (false)
   , additive (0)
   , real_depv (NULL)
  { }

  void invalidate ();

  void aff_const (tree cst_type, const poly_widest_int &cst);
  void aff_elt (tree elt_type, tree elt);
  void aff_scale (const widest_int &scale_in);
  bool aff_add (const poly_widest_int &cst);
  bool aff_add (aff_form &other);
  void aff_division (tree name, const widest_int &denum);

  void combine_real_depv (const aff_form &other);
};

void
aff_form::invalidate (void)
{
  if (!valid)
    return;

  valid = false;
  additive = 0;

  aff_combination_const (this, this->type, 0);
}

void
aff_form::aff_const (tree cst_type, const poly_widest_int &cst)
{
  valid = true;
  additive = 1;

  aff_combination_const (this, cst_type, cst);
}

void
aff_form::aff_elt (tree elt_type, tree elt)
{
  valid = true;
  additive = 1;

  aff_combination_elt (this, elt_type, elt);
}

void
aff_form::aff_scale (const widest_int &scale_in)
{
  gcc_assert (valid);

  if (additive && n && scale_in < 0)
    additive = -additive;

  aff_combination_scale (this, scale_in);
}

bool
aff_form::aff_add (const poly_widest_int &cst)
{
  aff_tree comb_cst;

  gcc_assert (valid);

  aff_combination_const (&comb_cst, type, cst);
  aff_combination_add (this, &comb_cst);
  return true;
}

bool
aff_form::aff_add (aff_form &other)
{
  gcc_assert (valid && other.valid);

  if (additive)
    {
      if (!n || !other.additive)
	additive = other.additive;
      else if (other.n && additive != other.additive)
	additive = 0;
    }

  aff_combination_add (this, &other);

  /* Too many affine elements.  */
  if (rest)
    {
      invalidate ();
      return false;
    }

  return true;
}

void
aff_form::aff_division (tree name, const widest_int &denum)
{
  tree name_type = TREE_TYPE (name);
  signop sign = TYPE_SIGN (name_type);
  tree denum_op;
  tree div_op;
  bool neg;
  int name_additive = additive;

  gcc_assert (valid);

  for (unsigned i = 0 ; i < n; i++)
    {
      tree val = elts[i].val;

      /* TODO: handle multi-level division */
      if (TREE_CODE (val) != SSA_NAME)
	{
	  invalidate ();
	  return;
	}
    }

  gcc_assert (n <= 1);

  if (!n)
    {
      widest_int res = wi::div_trunc (offset.coeffs[0], denum, sign);

      aff_const (name_type, res);
      additive = name_additive;
      return;
    }

  if (wi::neg_p (denum, sign))
    {
      denum_op = wide_int_to_tree (name_type, wi::neg (denum));
      neg = true;
    }
  else
    {
      denum_op = wide_int_to_tree (name_type, denum);
      neg = false;
    }

  div_op = fold_build2 (TRUNC_DIV_EXPR, name_type, name, denum_op);

  aff_elt (name_type, div_op);
  additive = name_additive;

  if (neg)
    aff_scale (-1);
}

void
aff_form::combine_real_depv (const aff_form &other)
{
  if (!other.real_depv || real_depv == other.real_depv)
    return;

  if (real_depv && ssa_strictly_dominated_by_p (real_depv, other.real_depv))
    return;

  real_depv = other.real_depv;
}

struct div_expr
{
  bool is_signed;

  widest_int c0;   /*   [ (c1 * n + c0) / d ] * m   */
  widest_int c1;
  widest_int div;
  widest_int mul;
};

class approx_mathfn
{
public:
  tree name;

  /* y = c1 * n + c0 */
  widest_int c0;
  widest_int c1;

  /* integer division operations */
  auto_vec<div_expr, 8> div_ops;

  bool has_inc;
  bool has_dec;

  approx_mathfn (tree name_)
   : name (name_)
   , has_inc (false)
   , has_dec (false)
  { }
};

typedef pair_hash<tree_ssa_name_hash, tree_ssa_name_hash> ssa_pair_hash;

struct mathfn_dep
{
  tree base;
  tree depv;  /* dependent origin variable */
};

struct iv_scev_desc
{
  tree init;
  tree step;
  tree niter;
  wide_int wi_dist;
  bool new_dist_p;
  bool always_updated;
};

class symbolic_vrp_prop : public symbolic_range_table
{
  int *bb_to_cfg_order;
  int *cfg_order_to_bb;
  auto_vec<gimple *> uid_to_stmt;

  auto_vec<vec<tree> > indirect_use_sets;
  auto_vec<ssa_predicate> predicates;
  auto_delete_vec<ssa_constraint> constraints;
  auto_vec<mathfn_dep> mathfn_deps;
  auto_delete_vec<approx_mathfn> mathfns;
  auto_vec<iv_scev_desc> scev_descs;

  auto_bitmap stmts_to_check;
  hash_set<gimple *> latch_visited;

  hash_map<ssa_pair_hash, aff_form *> affine_map;
  hash_map<ssa_pair_hash, tree_pair> fold_cache[2];

  template <typename T>
  static T& get_ssa_info (auto_vec<T> &info_vec, tree name)
  {
    unsigned version = ssa_name_version (name);

    if (info_vec.length () <= version)
      info_vec.safe_grow_cleared (version + 100);

    return info_vec[version];
  }

  template <typename T>
  static T* try_to_get_ssa_info (auto_vec<T> &info_vec, tree name)
  {
    unsigned version = ssa_name_version (name);

    if (info_vec.length () <= version)
      return NULL;

    return &info_vec[version];
  }

public:
  ssa_predicate &get_predicate (tree name)
  {
    return get_ssa_info (predicates, name);
  }

  bool has_useful_predicate (tree name)
  {
    ssa_predicate *predicate = try_to_get_ssa_info (predicates, name);

    return predicate && predicate->opnd
	   && TREE_CODE_CLASS (predicate->op) == tcc_comparison;
  }

private:
  void add_predicate (tree name, enum tree_code code, tree opnd)
  {
    ssa_predicate &predicate = get_predicate (name);

    /* Range updating of comparison operand could bring new range for defined
       SSA with this comparison as predicate.  */
    predicate.op = code;
    predicate.opnd = add_indirect_use (opnd, name);
  }

  ssa_constraint *&get_constraint (tree name)
  {
    return get_ssa_info (constraints, name);
  }

  tree &get_mathfn_depv (tree name)
  {
    return get_ssa_info (mathfn_deps, name).depv;
  }

  tree &get_mathfn_base (tree name)
  {
    return get_ssa_info (mathfn_deps, name).base;
  }

  approx_mathfn *&get_mathfn (tree name)
  {
    return get_ssa_info (mathfns, name);
  }

  vec<tree> &get_indirect_uses (tree name)
  {
    return get_ssa_info (indirect_use_sets, name);
  }

  tree add_indirect_use (tree name, tree use)
  {
    if (TREE_CODE (name) == SSA_NAME)
      {
	auto &indirect_uses = get_indirect_uses (name);

	if (!indirect_uses.contains (use))
	  indirect_uses.safe_push (use);
      }

    return name;
  }

  iv_scev_desc &get_scev_desc (tree name)
  {
    return get_ssa_info (scev_descs, name);
  }

  void get_mathfn_depv_list (tree name, vec<tree> &list)
  {
    for (; name; name = get_mathfn_depv (name))
      list.safe_push (name);
  }

  void build_range_predicate_for_copy (tree, tree, enum tree_code, edge);
  void build_range_predicate_from_condition (gcond *);
  void build_range_predicate_from_switch (gswitch *);

  bool insert_exit_iv_definition (tree, tree, tree, tree, edge);
  void init_iv_scev_desc (class loop *);
  void init_ranges ();

  tree get_common_mathfn_depv (tree, tree);
  tree get_ptr_expr_mathfn_depv (tree, tree &);
  void build_linear_mathfn_dependence (gimple *);
  bool get_mathfn_affine_form (aff_form *, tree, tree);
  aff_form *build_mathfn_affine_form (tree, tree);
  void make_mathfn_approximation (tree);

  bool compute_range_by_statement (tree, symbolic_range &);
  symbolic_range compute_range_by_statement (tree);
  bool update_operand_range (tree, gimple *, symbolic_range &,
			     auto_vec<tree> &);

  bool update_range_by_predicate (tree);
  bool update_range_by_mathfn (tree);
  bool update_range_by_constraint (tree);
  bool update_range_by_statement (tree);
  bool update_range_by_scev (tree);
  bool update_range_by_semantics (tree);
  bool update_operand_range_by_result (tree, auto_vec<tree> &);

  bool derive_constraint_for_cvt (tree, const tree, ssa_constraint &);
  bool derive_constraint_for_add (const tree, const tree, bool,
				  ssa_constraint &);
  bool intersect_ssa_constraint (tree, ssa_constraint *, bool = false);
  bool copy_ssa_constraint (tree, tree);
  void get_constraint_for_union (tree, tree, ssa_constraint &);

  bool get_minus_range_from_constraint (tree, tree, symbolic_range &, bool);
  bool compute_range_for_pointer_minus (tree, tree, tree, int,
					symbolic_range &);
  bool compute_range_for_pointer_plus (tree, tree, symbolic_range &);

  bool fold_to_one (tree, const widest_int &, tree, const widest_int &,
		    aff_tree *);
  bool fold_to_one_by_dominance (tree, const widest_int &,
				 tree, const widest_int &, aff_tree *);
  const tree_pair &fold_to_one (tree, tree, bool);
  bool minus_to_compare_operand (tree, tree, compare_operand *);
  bool pointer_minus_to_constraint (const compare_operand &,
				    const compare_operand &,
				    ssa_constraint &, bool);
  bool compute_constraint_for_minus (tree, tree, ssa_constraint &);
  bool compute_constraint_for_pointer_plus (tree, tree, ssa_constraint &);

  bool update_ssa_constraint (ssa_constraint *, tree, bool, const wide_int &);
  bool update_ssa_constraint (tree, tree, bool, const wide_int &);
  bool update_ssa_constraint_by_predicate (tree, ssa_predicate &);
  bool update_ssa_constraint_by_predicate (tree);
  bool update_ssa_constraint_by_statement (tree);
  bool update_ssa_constraint_by_scev (tree);
  bool update_ssa_constraint (tree);

  void update_worklist (tree, auto_bitmap &);
  void mark_undefined_range (gimple *, auto_bitmap &);
  void mark_undefined_ranges_by_dominance (gimple *, auto_bitmap &);
  void meet_propagate_backward ();

  void mark_undefined_constraint (tree name)
  {
    ssa_constraint *&constraint = get_constraint (name);

    if (!constraint)
      constraint = new ssa_constraint (/* undefined= */  true);
    else
      constraint->set_undefined ();
  }

  void dump_stmt (FILE *file, const char *prefix, gimple *stmt,
		  bool whole = true)
  {
    tree result = gimple_get_lhs (stmt);

    gcc_checking_assert (stmt->uid && result);

    fprintf (file, "%s#%d:  ", prefix, stmt->uid);

    if (whole)
      {
	ssa_predicate &predicate = get_predicate (result);

	if (predicate.opnd)
	  {
	    fprintf (file, "[");
	    print_generic_expr (file, result, TDF_NONE);
	    fprintf (file, " %s ", op_symbol_code (predicate.op));
	    print_generic_expr (file, predicate.opnd, TDF_NONE);
	    fprintf (file, "] ");
	  }
	print_gimple_stmt (file, stmt, 0, TDF_NONE);
      }
    else
      {
	print_generic_expr (dump_file, result, TDF_NONE);
	fprintf (file, "\n");
      }
  }

  void dump_stmt (FILE *file, gimple *stmt, bool whole = true)
  {
    dump_stmt (file, "", stmt, whole);
  }

  void dump_range (FILE *file, const char *prefix, symbolic_range &range)
  {
    fprintf (file, "%sRange: ",prefix);
    range.dump (file);
    fprintf (file, "\n");
  }

  void dump_range (FILE *file, symbolic_range &range)
  {
    dump_range (file, "", range);
  }

public:
  symbolic_vrp_prop () : bb_to_cfg_order (NULL), cfg_order_to_bb (NULL) { }

  void build_range_predicates ();
  void init ();
  void fini ();

  void add_stmt (gimple *stmt)
  {
    bool changed = bitmap_set_bit (stmts_to_check, stmt->uid);
    gcc_checking_assert (stmt->uid && changed);
  }

  void clear_stmt (gimple *stmt)
  {
    bool changed = bitmap_clear_bit (stmts_to_check, stmt->uid);
    gcc_checking_assert (stmt->uid && changed);
  }

  bool include_stmt_p (gimple *stmt)
  {
    return stmt->uid && bitmap_bit_p (stmts_to_check, stmt->uid);
  }

  void join_propagate ();
  void meet_propagate ();

  virtual ~symbolic_vrp_prop ();
};

void
symbolic_vrp_prop::build_range_predicate_for_copy (tree name, tree value,
						   enum tree_code code, edge e)
{
  /* For ssa that is not referred in conditional statement, we still could
     deduce range predicate based on some kind of value equivalency with
     those operands of conditional statement.

	int x;
	long v;

	...

	v = (long)x;

	if (x == const)
	  {
	    v_t = v;   (predicate for v_t: == (long)const)
	  }
	else
	  {
	    v_f = v;   (predicate for v_f: != (long)const)
	  }

      Here we only consider incompatible ssa copy, such as integer promotion
      or same-sized but different signed-ness cast. Because it is easy to
      know predicate by transitivity for normal ssa copy with same type.  */

  tree copy = get_ssa_copy (name, true, MATCH_PROMOTE);

  if (!copy || has_single_use (copy))
    return;

  tree type = TREE_TYPE (name);
  tree copy_type = TREE_TYPE (copy);

  if (!INTEGRAL_TYPE_P (copy_type))
    return;

  if (TYPE_SIGN (type) != TYPE_SIGN (copy_type)
      && code != NE_EXPR && code != EQ_EXPR)
    return;

  if (types_compatible_p (type, copy_type))
    return;

  tree copy_value = fold_convert (copy_type, value);

  if (TYPE_PRECISION (type) != TYPE_PRECISION (copy_type)
      && !tree_int_cst_equal (value, fold_convert (type, copy_value)))
    return;

  if (TREE_OVERFLOW_P (copy_value))
    copy_value = drop_tree_overflow (copy_value);

  tree new_ssa = split_ssa_at_edge (copy, e);

  if (new_ssa)
    add_predicate (new_ssa, code, copy_value);
}

void
symbolic_vrp_prop::build_range_predicate_from_condition (gcond *cond)
{
  tree cond_lhs = gimple_cond_lhs (cond);
  tree cond_rhs = gimple_cond_rhs (cond);
  tree cond_type = TREE_TYPE (cond_lhs);

  if (POINTER_TYPE_P (cond_type))
    {
      /* We could not infer any useful range information from condition
	 like (ptr CMP const).   */
      if (is_gimple_constant (cond_lhs) || is_gimple_constant (cond_rhs))
	return;
    }
  else if (!INTEGRAL_TYPE_P (cond_type))
    return;

  enum tree_code code = gimple_cond_code (cond);
  edge_iterator ei;
  edge e;

  if (TREE_CODE (cond_lhs) != SSA_NAME && TREE_CODE (cond_rhs) == SSA_NAME)
    {
      std::swap (cond_lhs, cond_rhs);
      code = swap_tree_comparison (code);
    }

  /* For a conditional statement, try to split live range of ssa comparison
     operands as:

	if (x < y)
	  {
	    x_t = x;  (predicate for x_t: < y)
	    y_t = y;  (predicate for y_t: > x_t)
	  }
	else
	  {
	    x_f = x;  (predicate for x_f: >= y)
	    y_f = y;  (predicate for y_f: <= x_f)
	  }

     We expect that each piece of ssa value is correlated with only one range
     predicate, which comes from comparison relationship of two operands.  */

  FOR_EACH_EDGE (e, ei, gimple_bb (cond)->succs)
    {
      tree new_cond_lhs = NULL_TREE;
      tree new_cond_rhs = NULL_TREE;
      enum tree_code pred_code = code;

      if (e->flags & EDGE_FALSE_VALUE)
	pred_code = invert_tree_comparison (code, false);

      if (TREE_CODE (cond_rhs) == SSA_NAME)
	new_cond_rhs = split_ssa_at_edge (cond_rhs, e);

      if (TREE_CODE (cond_lhs) == SSA_NAME)
	{
	  new_cond_lhs = split_ssa_at_edge (cond_lhs, e);

	  if (TREE_CODE (cond_rhs) == INTEGER_CST)
	    build_range_predicate_for_copy (cond_lhs, cond_rhs, pred_code, e);
	}

      if (new_cond_lhs)
	add_predicate (new_cond_lhs, pred_code, cond_rhs);

      if (new_cond_rhs)
	add_predicate (new_cond_rhs, swap_tree_comparison (pred_code),
		       new_cond_lhs ? new_cond_lhs : cond_lhs);
    }
}

struct case_info
{
  tree min;
  tree max;
  tree new_op;
};

class case_set : public auto_vec<tree>
{
public:
  tree label;

  case_set (tree label) : label (label) { }
};

void
symbolic_vrp_prop::build_range_predicate_from_switch (gswitch *gs)
{
  unsigned n = gimple_switch_num_labels (gs);
  tree op = gimple_switch_index (gs);
  tree type = TREE_TYPE (op);

  if (TREE_CODE (op) != SSA_NAME)
    return;

  auto_delete_vec<case_set> label_cases_map;
  hash_map<tree, unsigned> label_indices;
  tree default_label = CASE_LABEL (gimple_switch_label (gs, 0));

  for (unsigned case_idx = 1; case_idx < n; ++case_idx)
    {
      tree cl = gimple_switch_label (gs, case_idx);
      tree label = CASE_LABEL (cl);

      if (label == default_label)
	continue;

      bool existed;
      auto &label_idx = label_indices.get_or_insert (label, &existed);
      case_set *label_cases;

      if (existed)
	label_cases = label_cases_map[label_idx];
      else
	{
	  label_idx = label_cases_map.length ();
	  label_cases = new case_set (label);
	  label_cases_map.safe_push (label_cases);
	}

      label_cases->safe_push (cl);
    }

  basic_block switch_bb = gimple_bb (gs);

  for (auto label_cases : label_cases_map)
    {
      auto_vec<case_info> case_info_vec;
      bool skip = false;

      for (auto &cl : *label_cases)
	{
	  tree min = CASE_LOW (cl);
	  tree max = CASE_HIGH (cl);

	  if (TREE_TYPE (min) != type)
	    min = wide_int_to_tree (type, wi::to_wide (min));

	  if (!max)
	    max = min;
	  else if (TREE_TYPE (max) != type)
	    max = wide_int_to_tree (type, wi::to_wide (max));

	  case_info_vec.safe_push ({min, max, NULL_TREE});

	  if (max != min && tree_int_cst_le (max, min))
	    {
	      skip = true;
	      break;
	    }
	}

      if (skip)
	continue;

      basic_block label_bb = label_to_block (cfun, label_cases->label);
      edge label_e = find_edge (switch_bb, label_bb);
      tree new_op = split_ssa_at_edge (op, label_e);

      if (!new_op)
	continue;

      /* TODO: Create a phi to merge values from multiple switch-cases.  */
      if (label_cases->length () > 1)
	continue;
      else
	case_info_vec[0].new_op = new_op;

      for (auto &info : case_info_vec)
	{
	  tree min_new_op = info.new_op;
	  gimple *new_stmt = SSA_NAME_DEF_STMT (min_new_op);

	  if (info.min != info.max)
	    {
	      gimple_stmt_iterator gsi = gsi_for_stmt (new_stmt);
	      tree max_new_op = split_ssa_at_gsi (min_new_op, &gsi,
						  false, false);
	      add_predicate (min_new_op, GE_EXPR, info.min);
	      add_predicate (max_new_op, LE_EXPR, info.max);
	    }
	   else
	     add_predicate (min_new_op, EQ_EXPR, info.min);
	}
    }
}

void
symbolic_vrp_prop::build_range_predicates ()
{
  basic_block bb;

  calculate_dominance_info (CDI_DOMINATORS);

  scev_initialize ();

  for (auto loop : loops_list (cfun, 0))
    init_iv_scev_desc (loop);

  scev_finalize ();

  FOR_EACH_BB_FN (bb, cfun)
    {
      gimple *stmt = last_stmt (bb);

      if (!stmt)
	continue;

      if (auto cond = dyn_cast<gcond *> (stmt))
	build_range_predicate_from_condition (cond);
      else if (auto sw = dyn_cast<gswitch *> (stmt))
	build_range_predicate_from_switch (sw);
    }
}

tree
symbolic_vrp_prop::get_common_mathfn_depv (tree name1, tree name2)
{
  if (name1 == name2)
    return name1;

  if (!get_mathfn_depv (name1) && !get_mathfn_depv (name2))
    return NULL_TREE;

  auto_vec<tree, 8> list1;
  auto_vec<tree, 8> list2;

  get_mathfn_depv_list (name1, list1);
  get_mathfn_depv_list (name2, list2);

  tree common = NULL_TREE;

  unsigned pos1 = list1.length ();
  unsigned pos2 = list2.length ();

  for (; pos1 > 0 && pos2 > 0; pos1--, pos2--)
    {
      tree last1 = list1[pos1 - 1];
      tree last2 = list2[pos2 - 1];

      if (last1 != last2)
	break;

      common = last1;
    }

  return common;
}

tree
symbolic_vrp_prop::get_ptr_expr_mathfn_depv (tree expr, tree &expr_base)
{
  tree type = TREE_TYPE (expr);
  tree base = NULL_TREE;
  tree depv = NULL_TREE;

  gcc_assert (POINTER_TYPE_P (type));

  expr_base = NULL_TREE;

  if (TREE_CODE (expr) == SSA_NAME)
    {
      if ((base = get_mathfn_base (expr)))
	depv = get_mathfn_depv (expr);
      else
	base = expr;

      expr_base = base;
      return depv;
    }

  if (TREE_CODE (expr) != ADDR_EXPR)
    return NULL_TREE;

  aff_tree comb;

  tree_to_aff_combination (expr, type, &comb);

  /* Too many affine elements.  */
  if (comb.rest)
    return NULL_TREE;

  for (unsigned i = 0; i < comb.n; i++)
    {
      tree val = comb.elts[i].val;

      if (POINTER_TYPE_P (TREE_TYPE (val)))
	{
	  if (base)
	    return NULL_TREE;

	  base = val;
	  continue;
	}

      if (TREE_CODE (val) != SSA_NAME)
	return NULL_TREE;

      if (!depv)
	depv = val;
      else if (!(depv = get_common_mathfn_depv (depv, val)))
	return NULL_TREE;
    }

  if (!base || TREE_CODE (base) == INTEGER_CST)
    return NULL_TREE;

  if (TREE_CODE (base) == SSA_NAME)
    {
      tree tmp_depv = get_mathfn_depv (base);
      tree tmp_base = get_mathfn_base (base);

      if (tmp_depv)
	{
	  if (!depv)
	    {
	      depv = tmp_depv;
	      base = tmp_base;
	    }
	  else if ((tmp_depv = get_common_mathfn_depv (tmp_depv, depv)))
	    {
	      depv = tmp_depv;
	      base = tmp_base;
	    }
	}
    }

  expr_base = base;
  return depv;
}

void
symbolic_vrp_prop::build_linear_mathfn_dependence (gimple *stmt)
{
  enum tree_code code = gimple_assign_rhs_code (stmt);
  tree result = gimple_assign_lhs (stmt);
  tree type = TREE_TYPE (result);
  tree rhs1 = gimple_assign_rhs1 (stmt);
  tree rhs2 = NULL_TREE;
  tree &depv = get_mathfn_depv (result);
  tree &base = get_mathfn_base (result);

  if (tree copy = get_ssa_copy (stmt, false, MATCH_TYPE))
    {
      if (POINTER_TYPE_P (type))
	depv = get_ptr_expr_mathfn_depv (copy, base);
      else if (TREE_CODE (copy) == SSA_NAME)
	depv = rhs1;
      goto end;
    }

  if (TREE_CODE_CLASS (code) == tcc_binary)
    rhs2 = gimple_assign_rhs2 (stmt);

  switch (code)
    {
    case PLUS_EXPR:
    case MINUS_EXPR:
      if (TREE_CODE (rhs1) == SSA_NAME)
	{
	  if (TREE_CODE (rhs2) == INTEGER_CST)
	    depv = rhs1;
	  else if (TREE_CODE (rhs2) == SSA_NAME)
	    depv = get_common_mathfn_depv (rhs1, rhs2);
	}
      else if (TREE_CODE (rhs1) == INTEGER_CST && TREE_CODE (rhs2) == SSA_NAME)
	depv = rhs2;
      break;

    case POINTER_PLUS_EXPR:
      depv = get_ptr_expr_mathfn_depv (rhs1, base);

      if (TREE_CODE (rhs2) == SSA_NAME)
	{
	  if (!base)
	    base = rhs1;

	  if (!depv)
	    depv = get_mathfn_depv (rhs2);
	  else
	    depv = get_common_mathfn_depv (depv, rhs2);

	  if (!depv)
	    {
	      base = rhs1;
	      depv = rhs2;
	    }
	}
      else if (TREE_CODE (rhs2) != INTEGER_CST)
	{
	  depv = NULL_TREE;
	  base = NULL_TREE;
	}
      break;

    case POINTER_DIFF_EXPR:
      {
	tree rhs1_depv, rhs1_base;
	tree rhs2_depv, rhs2_base;

	rhs1_depv = get_ptr_expr_mathfn_depv (rhs1, rhs1_base);
	rhs2_depv = get_ptr_expr_mathfn_depv (rhs2, rhs2_base);

	if (rhs1_base && rhs2_base && operand_equal_p (rhs1_base, rhs2_base))
	  {
	    if (!rhs1_depv)
	      depv = rhs2_depv;
	    else if (!rhs2_depv)
	      depv = rhs1_depv;
	    else
	      depv = get_common_mathfn_depv (rhs1_depv, rhs2_depv);
	  }
	break;
      }

    case MULT_EXPR:
    case TRUNC_DIV_EXPR:
      if (TREE_CODE (rhs1) == SSA_NAME && TREE_CODE (rhs2) == INTEGER_CST)
	{
	  wide_int cst_val = wi::to_wide (rhs2);
	  wide_int cst_neg = wi::neg (cst_val);

	  /* Skip zero value and signed max value.  */
	  if (cst_val != cst_neg)
	    depv = rhs1;
	}
      break;

    case LSHIFT_EXPR:
    case RSHIFT_EXPR:
      if (TREE_CODE (rhs1) == SSA_NAME && TREE_CODE (rhs2) == INTEGER_CST)
	{
	  wide_int cst_val = wi::to_wide (rhs2);

	  if (wi::ltu_p (cst_val, TYPE_PRECISION (type) - 1))
	    depv = rhs1;
	}
      break;

    case BIT_AND_EXPR:
      if (TREE_CODE (rhs1) == SSA_NAME && TREE_CODE (rhs2) == INTEGER_CST)
	{
	  wide_int cst_val = wi::to_wide (rhs2);
	  wide_int cst_neg = wi::neg (cst_val);

	  /* Skip zero value and signed max value.  */
	  if (cst_val != cst_neg && (cst_neg & (cst_neg - 1)) == 0)
	    depv = rhs1;
	}
      break;

    case NEGATE_EXPR:
    case BIT_NOT_EXPR:
      if (TREE_CODE (rhs1) == SSA_NAME)
	depv = rhs1;
      break;

    default:
      break;
  }

end:
  if (depv && dump_file && (dump_flags & TDF_DETAILS))
    {
      gimple *depv_stmt = SSA_NAME_DEF_STMT (depv);

      dump_stmt (dump_file, stmt);

      if (base)
	{
	  fprintf (dump_file, "base: ");
	  print_generic_expr (dump_file, base, TDF_NONE);
	  fprintf (dump_file, ", ");
	}

      fprintf (dump_file, "depv: ");

      if (depv_stmt->uid)
	{
	  print_generic_expr (dump_file, depv, TDF_NONE);
	  fprintf (dump_file, " (#%d)\n", depv_stmt->uid);
	}
      else
	print_gimple_stmt (dump_file, depv_stmt, 0, TDF_NONE);

      fprintf (dump_file, "\n");
    }
}

static bool copy_of_p (tree name1, tree name2)
{
  if (operand_equal_p (name1, name2))
    return true;

  if (TREE_CODE (name1) != SSA_NAME)
    return false;

  basic_block bb1 = gimple_bb (SSA_NAME_DEF_STMT (name1));

  if (!bb1)
    return false;

  if (TREE_CODE (name2) == SSA_NAME)
    {
      basic_block bb2 = gimple_bb (SSA_NAME_DEF_STMT (name2));

      if (bb2 && !dominated_by_p (CDI_DOMINATORS, bb1, bb2))
	return false;
    }

  while ((name1 = get_ssa_copy (name1)))
    {
      if (operand_equal_p (name1, name2))
	return true;
    }

  return false;
}


bool
symbolic_vrp_prop::get_mathfn_affine_form (aff_form *form, tree name,
					   tree depv)
{
  tree type = TREE_TYPE (depv);

  if (TREE_CODE (name) == ADDR_EXPR)
    {
      aff_tree comb;

      tree_to_aff_combination (name, TREE_TYPE (name), &comb);

      gcc_assert (!comb.rest);

      form->aff_const (type, comb.offset);

      for (unsigned i = 0; i < comb.n; i++)
	{
	  tree val = comb.elts[i].val;
	  tree val_type = TREE_TYPE (val);
	  const widest_int &coef = comb.elts[i].coef;
	  aff_form val_form;

	  if (POINTER_TYPE_P (val_type))
	    {
	      gcc_assert (coef == 1);

	      if (TREE_CODE (val) != SSA_NAME
		  || !get_mathfn_affine_form (&val_form, val, depv))
		val_form.aff_elt (val_type, val);
	    }
	  else if (!get_mathfn_affine_form (&val_form, val, depv))
	    {
	      form->invalidate ();
	      return false;
	    }

	  val_form.aff_scale (coef);
	  if (!form->aff_add (val_form))
	    return false;

	  form->combine_real_depv (val_form);
	}
      gcc_assert (form->n);
    }
  else if (POINTER_TYPE_P (TREE_TYPE (name)))
    {
      if (TREE_CODE (name) != SSA_NAME || !get_mathfn_depv (name))
	form->aff_elt (TREE_TYPE (name), name);
      else
	*form = *build_mathfn_affine_form (name, depv);
    }
  else if (TREE_CODE (name) == INTEGER_CST)
    form->aff_const (type, wi::to_poly_widest (name));
  else if (TREE_CODE (name) != SSA_NAME)
    return false;
  else if (copy_of_p (depv, name))
    form->aff_elt (type, depv);
  else if (!get_mathfn_depv (name))
    return false;
  else
    *form = *build_mathfn_affine_form (name, depv);

  return form->valid;
}

aff_form *
symbolic_vrp_prop::build_mathfn_affine_form (tree name, tree depv)
{
  bool existed;
  tree_pair name_key (name, depv);
  auto &cache = affine_map.get_or_insert (name_key, &existed);

  if (existed)
    return cache;

  gimple *stmt = SSA_NAME_DEF_STMT (name);
  enum tree_code code = gimple_assign_rhs_code (stmt);
  tree rhs1 = gimple_assign_rhs1 (stmt);
  tree rhs2 = gimple_assign_rhs2 (stmt);
  aff_form *form = cache = new aff_form;
  aff_form tmp_form;

  if (rhs1 == get_mathfn_base (name))
    form->aff_elt (TREE_TYPE (rhs1), rhs1);
  else if (!get_mathfn_affine_form (form, rhs1, depv))
    return form;

  switch (code)
    {
    case POINTER_PLUS_EXPR:
    case POINTER_DIFF_EXPR:
    case PLUS_EXPR:
    case MINUS_EXPR:
      if (!get_mathfn_affine_form (&tmp_form, rhs2, depv))
	{
	  form->invalidate ();
	  break;
	}

      if (code == MINUS_EXPR || code == POINTER_DIFF_EXPR)
	tmp_form.aff_scale (-1);

      form->combine_real_depv (tmp_form);
      form->aff_add (tmp_form);
      break;

    case MULT_EXPR:
      form->aff_scale (wi::to_widest (rhs2));
      break;

    case TRUNC_DIV_EXPR:
      form->aff_division (rhs1, wi::to_widest (rhs2));
      break;

    case LSHIFT_EXPR:
    case RSHIFT_EXPR:
      {
	widest_int scale = widest_int (1) << wi::to_widest (rhs2);

	if (code == LSHIFT_EXPR)
	  form->aff_scale (scale);
	else
	  form->aff_division (rhs1, scale);
	break;
      }

    case BIT_AND_EXPR:
      {
	widest_int scale
		= widest_int::from (wi::neg (wi::to_wide (rhs2)), UNSIGNED);

	form->aff_division (rhs1, scale);
	form->aff_scale (scale);
	break;
      }

    case NEGATE_EXPR:
      form->aff_scale (-1);
      break;

    case BIT_NOT_EXPR:
      /* ~x = -x - 1 */
      form->aff_scale (-1);
      form->aff_add (-1);
      break;

    default:
      /* Use the nearest SSA name with the form (+-)basic_depv + const as the
	 real depv, since it is more likely that the SSA is equipped with more
	 accurate range information.  */
      if (form->n == 1 && form->elts[0].val == depv
	  && wi::abs (form->elts[0].coef) == 1)
	form->real_depv = name;
    }

  if (form->valid)
    {
      int ptr_cnt = POINTER_TYPE_P (TREE_TYPE (name)) ? 1 : 0;
      unsigned i;

      gcc_assert (form->offset.is_constant ());

      for (i = 0; i < form->n; i++)
	{
	  tree &val = form->elts[i].val;

	  if (CONVERT_EXPR_CODE_P (TREE_CODE (val)))
	    {
	      tree opnd = TREE_OPERAND (val, 0);
	      tree type = TREE_TYPE (opnd);

	      if (TYPE_PRECISION (type) != TYPE_PRECISION (val)
		  || (!POINTER_TYPE_P (type) && !INTEGRAL_TYPE_P (type)))
		break;

	      val = opnd;
	    }

	  if (POINTER_TYPE_P (TREE_TYPE (val)))
	    {
	      if (form->elts[i].coef != 1)
		break;

	      ptr_cnt--;
	    }
	  else if (TREE_CODE (val) == TRUNC_DIV_EXPR)
	    continue;
	  else if (val != depv)
	    break;
	}

      if (ptr_cnt || i < form->n)
	form->invalidate ();
    }

  return form;
}

static void
print_widest_int (FILE *file, const widest_int &cst)
{
  if (wi::neg_p (cst))
    {
      fprintf (file, "(");
      print_dec (cst, file, SIGNED);
      fprintf (file, ")");
    }
  else
    print_dec (cst, file, SIGNED);
}

void
symbolic_vrp_prop::make_mathfn_approximation (tree name)
{
  tree depv = get_mathfn_depv (name);

  if (!depv)
    return;

  gimple *stmt = SSA_NAME_DEF_STMT (name);

  switch (gimple_assign_rhs_code (stmt))
    {
    case POINTER_PLUS_EXPR:
    case POINTER_DIFF_EXPR:
    case PLUS_EXPR:
    case MINUS_EXPR:
      {
	ssa_op_iter iter;
	tree use;
	unsigned count = 0;

	FOR_EACH_SSA_TREE_OPERAND (use, stmt, iter, SSA_OP_USE)
	  count++;

	if (count > 1)
	  break;
      }
    default:
      return;
    }

  aff_form *form = build_mathfn_affine_form (name, depv);

  if (!form->valid)
    return;

  if (POINTER_TYPE_P (TREE_TYPE (name)))
    {
      tree base = NULL_TREE;

      for (unsigned i = 0; i < form->n; i++)
	{
	  tree val = form->elts[i].val;

	  if (POINTER_TYPE_P (TREE_TYPE (val)))
	    {
	      base = val;
	      for (i++; i < form->n; i++)
		form->elts[i - 1] = form->elts[i];
	      form->n--;
	      break;
	    }
	}
      get_mathfn_base (name) = base;
    }

  if (form->additive && form->n <= 1)
    return;

  auto mathfn = new approx_mathfn (name);

  mathfn->c0 = form->offset.coeffs[0];
  mathfn->c1 = 0;

  get_mathfn (name) = mathfn;
  add_indirect_use (depv, name);

  for (unsigned i = 0; i < form->n; i++)
    {
      tree val = form->elts[i].val;
      const widest_int &coef = form->elts[i].coef;

      if (TREE_CODE (val) == SSA_NAME)
	{
	  mathfn->c1 = coef;

	  if (wi::neg_p (coef))
	    mathfn->has_dec = true;
	  else if (coef != 0)
	    mathfn->has_inc = true;
	}
      else
	{
	  tree temp = TREE_OPERAND (val, 0);
	  div_expr div_op;

	  if (temp == depv)
	    {
	      div_op.c0 = 0;
	      div_op.c1 = 1;
	    }
	  else
	    {
	      aff_form *temp_form = build_mathfn_affine_form (temp, depv);

	      gcc_assert (temp_form->valid && temp_form->n == 1);

	      div_op.c0 = temp_form->offset.coeffs[0];
	      div_op.c1 = temp_form->elts[0].coef;
	    }
	  div_op.div = wi::to_widest (TREE_OPERAND (val, 1));
	  div_op.mul = coef;
	  div_op.is_signed = (TYPE_SIGN (TREE_TYPE (temp)) == SIGNED);

	  gcc_assert (!wi::neg_p (div_op.div));

	  mathfn->div_ops.safe_push (div_op);

	  if (wi::neg_p (div_op.mul) ^ wi::neg_p (div_op.c1))
	    mathfn->has_dec = true;
	  else
	    mathfn->has_inc = true;
	}
    }

  tree real_depv = form->real_depv;

  if (real_depv)
    {
      aff_form *depv_form = build_mathfn_affine_form (real_depv, depv);
      const widest_int &depv_c0 = depv_form->offset.coeffs[0];
      const widest_int &depv_c1 = depv_form->elts[0].coef;
      bool depv_c0_is_0 = (depv_c0 == 0);
      bool depv_c1_is_1 = (depv_c1 == 1);
      unsigned prec = TYPE_PRECISION (TREE_TYPE (depv));

      gcc_assert (depv_form->valid && depv_form->n == 1);

      /* Set new real dependent variable */
      get_mathfn_depv (name) = real_depv;

      gcc_assert (depv_c1 == 1 || depv_c1 == -1);

      if (!depv_c0_is_0 || !depv_c1_is_1)
	{
	  if (!depv_c0_is_0)
	    mathfn->c0 = wi::sext (mathfn->c0 - mathfn->c1 * depv_c0, prec);

	  if (!depv_c1_is_1)
	    mathfn->c1 = wi::sext (wi::neg (mathfn->c1), prec);

	  for (auto &div_op : mathfn->div_ops)
	    {
	      if (!depv_c0_is_0)
		div_op.c0 = wi::sext (div_op.c0 - div_op.c1 * depv_c0, prec);

	      if (!depv_c1_is_1)
		div_op.c1 = wi::sext (wi::neg (div_op.c1), prec);
	    }
	}
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      bool first = true;
      tree base = get_mathfn_base (name);

      fprintf (dump_file, "quasi affine mathfn for #%d:  ", stmt->uid);
      print_gimple_stmt (dump_file, stmt, 0, TDF_NONE);

      print_generic_expr (dump_file, name, TDF_NONE);
      fprintf (dump_file, " = ");

      if (base)
	{
	  print_generic_expr (dump_file, base, TDF_NONE);
	  fprintf (dump_file, " + ");
	}

      depv = get_mathfn_depv (name);
      if (mathfn->c1 != 0)
	{
	  print_widest_int (dump_file, mathfn->c1);
	  fprintf (dump_file, " * ");
	  print_generic_expr (dump_file, depv, TDF_NONE);
	  first = false;
	}

      for (const auto &div_op : mathfn->div_ops)
	{
	  if (first)
	    first = false;
	  else
	    fprintf (dump_file, " + ");

	  print_widest_int (dump_file, div_op.mul);
	  fprintf (dump_file, " * ((");
	  print_widest_int (dump_file, div_op.c1);
	  fprintf (dump_file, " * ");
	  print_generic_expr (dump_file, depv, TDF_NONE);
	  if (div_op.c0 != 0)
	    {
	      fprintf (dump_file, " + ");
	      print_widest_int (dump_file, div_op.c0);
	    }
	  fprintf (dump_file, ") / ");
	  print_widest_int (dump_file, div_op.div);
	  fprintf (dump_file, ")");
	}

      if (mathfn->c0 != 0)
	{
	  if (!first)
	    fprintf (dump_file, " + ");
	  print_widest_int (dump_file, mathfn->c0);
	}

      fprintf (dump_file, "\n\n");
    }
}

bool
symbolic_vrp_prop::update_range_by_predicate (tree name)
{
  ssa_predicate &predicate = get_predicate (name);
  tree cmp_opnd = predicate.opnd;

  if (!cmp_opnd)
    return false;

  symbolic_range &range = get_range (name);
  symbolic_range opnd_range = get_range_from_tree (cmp_opnd);
  tree_code cmp_op = predicate.op;

  if (opnd_range.undefined_p ())
    return range.intersect_r (opnd_range);

  if (opnd_range.varying_p ())
    return false;

  tree type = opnd_range.type ();
  tree min, max;

  switch (cmp_op)
    {
    case NE_EXPR:
      if (!POINTER_TYPE_P (TREE_TYPE (name)))
	{
	  tree val;

	  if (opnd_range.singleton_p (&val)
	      && TREE_CODE (val) == INTEGER_CST)
	    {
	      opnd_range.set (val, val, VR_ANTI_RANGE);
	      break;
	    }
	}
      return false;

    case EQ_EXPR:
      break;

    case LT_EXPR:
    case LE_EXPR:
      min = TYPE_MIN_VALUE (type);
      max = opnd_range.max ();

      if (cmp_op == LE_EXPR)
	opnd_range.set (min, max);
      else if (tree_int_cst_equal (min, max))
	opnd_range.set_undefined ();
      else
	{
	  max = int_const_binop (MINUS_EXPR, max, build_one_cst (type));
	  opnd_range.set (min, max);
	}
      break;

    case GT_EXPR:
    case GE_EXPR:
      min = opnd_range.min ();
      max = TYPE_MAX_VALUE (type);

      if (cmp_op == GE_EXPR)
	opnd_range.set (min, max);
      else if (tree_int_cst_equal (min, max))
	opnd_range.set_undefined ();
      else
	{
	  min = int_const_binop (PLUS_EXPR, min, build_one_cst (type));
	  opnd_range.set (min, max);
	}
      break;

    default:
      return false;
    }

  return range.intersect_r (opnd_range);
}

static bool
compute_range_by_mathfn (approx_mathfn *mathfn, tree type,
			 symbolic_range &range,
			 const widest_int &depv_min,
			 const widest_int &depv_max)
{
  unsigned prec = TYPE_PRECISION (type);
  widest_int min = depv_min * mathfn->c1 + mathfn->c0;
  widest_int max = depv_max * mathfn->c1 + mathfn->c0;
  widest_int mask = wi::mask <widest_int> (prec, true);
  widest_int half = wi::set_bit_in_zero <widest_int> (prec - 1);
  widest_int min_1;
  widest_int max_1;
  widest_int adjust_val;
  bool adjust = true;

  if (!mathfn->has_inc || !mathfn->has_dec)
    adjust = false;
  else if (depv_min + 1 == depv_max || depv_min == depv_max)
    adjust = false;

  if (adjust)
    {
      min_1 = min + mathfn->c1;
      max_1 = max - mathfn->c1;
      adjust_val = -1;
    }

  for (auto &div_op : mathfn->div_ops)
    {
      widest_int div_min = depv_min * div_op.c1 + div_op.c0;
      widest_int div_max = depv_max * div_op.c1 + div_op.c0;

      if (div_op.is_signed)
	{
	  if (((div_min + half) & mask) != ((div_max + half) & mask))
	    return false;

	  div_min = wi::sext (div_min, prec);
	  div_max = wi::sext (div_max, prec);

	  if (adjust)
	    {
	      if (wi::neg_p (div_min) == wi::neg_p (div_max)
		  || div_min == 0 || div_max == 0)
		adjust_val += wi::abs (div_op.mul);
	      else
		adjust_val += wi::abs (div_op.mul) << 1;
	    }
	}
      else
	{
	  /* Not monotonic variation */
	  if ((div_min & mask) != (div_max & mask))
	    return false;

	  div_min = wi::zext (div_min, prec);
	  div_max = wi::zext (div_max, prec);

	  if (adjust)
	    adjust_val += wi::abs (div_op.mul);
	}

      min += (div_min / div_op.div) * div_op.mul;
      max += (div_max / div_op.div) * div_op.mul;

      if (adjust)
	{
	  min_1 += ((div_min + div_op.c1) / div_op.div) * div_op.mul;
	  max_1 += ((div_max - div_op.c1) / div_op.div) * div_op.mul;
	}
    }

  widest_int dist = max - min;

  if (wi::neg_p (dist))
    {
      std::swap (max, min);
      dist = -dist;
    }

  if (adjust)
    {
      if (wi::les_p (dist, adjust_val))
	return false;

      widest_int min_t = min_1 - adjust_val;
      widest_int max_t = max_1 + adjust_val;

      if (wi::gts_p (min, min_t))
	min = min_t;

      if (wi::lts_p (max, max_t))
	max = max_t;
    }

  if (wi::ges_p (max - min, ~mask))
    return false;

  if (TYPE_SIGN (type) == UNSIGNED)
    {
      min = wi::zext (min, prec);
      max = wi::zext (max, prec);
    }
  else
    {
      min = wi::sext (min, prec);
      max = wi::sext (max, prec);
    }

  if (wi::les_p (min, max))
    range.set (wide_int_to_tree (type, min),
	       wide_int_to_tree (type, max));
  else
    range.set (wide_int_to_tree (type, max + 1),
	       wide_int_to_tree (type, min - 1),
	       VR_ANTI_RANGE);

  return true;
}

bool
symbolic_vrp_prop::update_range_by_mathfn (tree result)
{
  approx_mathfn *mathfn = get_mathfn (result);

  if (!mathfn)
    return false;

  tree depv = get_mathfn_depv (result);
  tree base = get_mathfn_base (result);
  tree range_type = get_range_type (result);

  symbolic_range &range = get_range (result);
  symbolic_range &depv_range = get_range (depv);
  symbolic_range tmp_range;

  if (depv_range.undefined_p ())
    return range.intersect_r (depv_range);

  widest_int depv_min = wi::to_widest (depv_range.min ());
  widest_int depv_max = wi::to_widest (depv_range.max ());

  if (depv_range.kind () == VR_ANTI_RANGE)
    {
      tree depv_type = TREE_TYPE (depv);
      widest_int type_min = wi::to_widest (TYPE_MIN_VALUE (depv_type));
      widest_int type_max = wi::to_widest (TYPE_MAX_VALUE (depv_type));
      symbolic_range tmp1_range;

      if (!compute_range_by_mathfn (mathfn, range_type, tmp_range,
				    type_min, depv_min - 1))
	return false;

      if (!compute_range_by_mathfn (mathfn, range_type, tmp1_range,
				    depv_max + 1, type_max))
	return false;

      tmp_range.union_ (tmp1_range);
    }
  else if (!compute_range_by_mathfn (mathfn, range_type, tmp_range,
				     depv_min, depv_max))
    return false;

  if (base)
    {
      symbolic_range &base_range = get_range (base);
      symbolic_range new_range;

      symbolic_range_fold_binary_expr (&new_range, POINTER_PLUS_EXPR,
				       TREE_TYPE (result), &base_range,
				       &tmp_range);
      return range.intersect_r (new_range);
    }

  return range.intersect_r (tmp_range);
}

bool
symbolic_vrp_prop::get_minus_range_from_constraint (tree name1, tree name2,
						    symbolic_range &range,
						    bool overflow)
{
  bool reverse = false;
  tree type = TREE_TYPE (name1);

  if (TREE_CODE (name1) != SSA_NAME || TREE_CODE (name2) != SSA_NAME)
    return false;

  if (ssa_strictly_dominated_by_p (name2, name1))
    {
      std::swap (name1, name2);
      reverse = true;
    }
  else
    gcc_assert (ssa_strictly_dominated_by_p (name1, name2));

  ssa_constraint *constraint = get_constraint (name1);

  if (!constraint)
    return false;

  tree range_type = get_range_type (type);
  tree min = NULL_TREE;
  tree max = NULL_TREE;
  auto le_opnd = ssa_constraint::find (constraint->le_opnds, name2);
  auto ge_opnd = ssa_constraint::find (constraint->ge_opnds, name2);

  if (le_opnd)
    {
      if (reverse)
	min = int_const_binop (MINUS_EXPR, build_int_cst (range_type, 0),
			       le_opnd->value);
      else
	max = le_opnd->value;
    }

  if (ge_opnd)
    {
      if (reverse)
	max = int_const_binop (MINUS_EXPR, build_int_cst (range_type, 0),
			       ge_opnd->value);
      else
	min = ge_opnd->value;
    }

  if (min && max)
    {
      if (wi::gt_p (wi::to_wide (min), wi::to_wide (max),
	  TYPE_SIGN (range_type)))
	return false;

      range.set (min, max);
      return true;
    }

  if (overflow)
    return false;

  if (le_opnd && le_opnd->overflow)
    return false;

  if (ge_opnd && ge_opnd->overflow)
    return false;

  if (min)
    max = TYPE_MAX_VALUE (range_type);
  else if (max)
    min = TYPE_MIN_VALUE (range_type);
  else
    return false;

  range.set (min, max);
  return true;
}

bool
symbolic_vrp_prop::update_range_by_constraint (tree name)
{
  ssa_constraint *constraint = get_constraint (name);

  if (!constraint)
    return false;

  symbolic_range &range = get_range (name);

  if (range.undefined_p ())
    return false;

  tree type = TREE_TYPE (name);

  if (POINTER_TYPE_P (type) && !TYPE_OVERFLOW_UNDEFINED (type))
    return false;

  bool changed = false;

  for (const auto &cmp_opnd : constraint->le_opnds)
    {
      symbolic_range opnd_range = cmp_opnd.range ();

      if (opnd_range.undefined_p ())
	return range.intersect_r (opnd_range);

      if (opnd_range.kind () != VR_RANGE)
	continue;

      if (POINTER_TYPE_P (type) && cmp_opnd.overflow)
	continue;

      opnd_range.set (TYPE_MIN_VALUE (opnd_range.type ()), opnd_range.max ());
      changed |= range.intersect_r (opnd_range);
    }

  for (const auto &cmp_opnd : constraint->ge_opnds)
    {
      symbolic_range opnd_range = cmp_opnd.range ();

      if (opnd_range.undefined_p ())
	return range.intersect_r (opnd_range);

      if (opnd_range.kind () != VR_RANGE)
	continue;

      if (POINTER_TYPE_P (type) && cmp_opnd.overflow)
	continue;

      opnd_range.set (opnd_range.min (), TYPE_MAX_VALUE (opnd_range.type ()));
      changed |= range.intersect_r (opnd_range);
    }

  return changed;
}

bool
symbolic_vrp_prop::compute_range_for_pointer_minus (tree pointer,
						    tree offset,
						    tree minus_offset,
						    int cmp,
						    symbolic_range &range)
{
  const auto &addr_offset = fold_to_one (pointer, minus_offset, true);

  if (tree addr = addr_offset.first)
    {
      symbolic_range addr_range = get_range_from_tree (addr);

      if (!offset)
	offset = addr_offset.second;
      else
	offset = fold_binary (PLUS_EXPR, TREE_TYPE (offset), offset,
			      addr_offset.second);

      if (!integer_zerop (offset))
	{
	  symbolic_range offset_range = get_range_from_tree (offset);

	  symbolic_range_fold_binary_expr (POINTER_PLUS_EXPR, TREE_TYPE (addr),
					   &addr_range, &offset_range);
	}

      if (cmp && addr_range.kind () != VR_RANGE)
	return false;

      if (cmp > 0)
	addr_range.set (TYPE_MIN_VALUE (addr_range.type ()),
			addr_range.max ());
      else if (cmp < 0)
	addr_range.set (addr_range.min (),
			TYPE_MAX_VALUE (addr_range.type ()));

      return range.intersect_r (addr_range);
    }

  return false;
}

bool
symbolic_vrp_prop::compute_range_for_pointer_plus (tree pointer,
						   tree offset,
						   symbolic_range &range)
{
  if (TREE_CODE (pointer) != SSA_NAME || TREE_CODE (offset) != SSA_NAME)
    return false;

  gimple *stmt = SSA_NAME_DEF_STMT (offset);

  if (!is_gimple_assign (stmt) || gimple_assign_rhs_code (stmt) != NEGATE_EXPR)
    return false;

  tree minus_offset = gimple_assign_rhs1 (stmt);

  if (TREE_CODE (minus_offset) != SSA_NAME)
    return false;

  ssa_constraint *constraint = get_constraint (pointer);

  if (!constraint)
    return false;

  range.set_varying (TREE_TYPE (pointer));

  bool has_range = compute_range_for_pointer_minus (pointer, NULL_TREE,
						    minus_offset, 0, range);

  for (auto &cmp_opnd : constraint->le_opnds)
    has_range |= compute_range_for_pointer_minus (cmp_opnd.name_to_ssa (),
						  cmp_opnd.value,
						  minus_offset, 1, range);

  for (auto &cmp_opnd : constraint->ge_opnds)
    has_range |= compute_range_for_pointer_minus (cmp_opnd.name_to_ssa (),
						  cmp_opnd.value,
						  minus_offset, -1, range);

  return has_range;
}

bool
symbolic_vrp_prop::compute_range_by_statement (tree result,
					       symbolic_range &result_range)
{
  gimple *stmt = SSA_NAME_DEF_STMT (result);

  if (tree copy = get_ssa_copy (stmt, true, MATCH_TYPE))
    {
      result_range = get_range (copy);
      return true;
    }

  if (auto phi = dyn_cast<gphi *> (stmt))
    {
      for (unsigned i = 0; i < gimple_phi_num_args (phi); ++i)
	{
	  tree arg = PHI_ARG_DEF (phi, i);

	  result_range.union_ (get_range_from_tree (arg));
	}
      return true;
    }

  ssa_op_iter iter;
  tree use;

  FOR_EACH_SSA_TREE_OPERAND (use, stmt, iter, SSA_OP_USE)
    {
      symbolic_range &range = get_range (use);

      if (range.undefined_p ())
	return true;
    }

  if (gimple_vuse (stmt) || !is_gimple_assign (stmt))
    return false;

  tree type = TREE_TYPE (result);
  tree rhs1 = gimple_assign_rhs1 (stmt);
  enum tree_code code = gimple_assign_rhs_code (stmt);

  if (code == SSA_NAME || code == ADDR_EXPR
      || TREE_CODE_CLASS (code) == tcc_constant)
    result_range = get_range_from_tree (rhs1);
  else if (code == COND_EXPR)
    {
      tree rhs2 = gimple_assign_rhs2 (stmt);
      tree rhs3 = gimple_assign_rhs3 (stmt);

      result_range = get_range_from_tree (rhs2);
      result_range.union_ (get_range_from_tree (rhs3));
    }
  else if (TREE_CODE_CLASS (code) == tcc_unary)
    {
      symbolic_range rhs1_range = get_range_from_tree (rhs1);

      symbolic_range_fold_unary_expr (&result_range, code, type, &rhs1_range,
				      TREE_TYPE (rhs1));
    }
  else if (TREE_CODE_CLASS (code) == tcc_binary)
    {
      tree rhs2 = gimple_assign_rhs2 (stmt);
      symbolic_range rhs1_range = get_range_from_tree (rhs1);
      symbolic_range rhs2_range = get_range_from_tree (rhs2);

      symbolic_range_fold_binary_expr (&result_range, code, type, &rhs1_range,
				       &rhs2_range);

      if (code == MINUS_EXPR || code == POINTER_DIFF_EXPR)
	{
	  bool overflow = !TYPE_OVERFLOW_UNDEFINED (TREE_TYPE (rhs1));
	  symbolic_range more_range;

	  if (get_minus_range_from_constraint (rhs1, rhs2, more_range,
					       overflow))
	    {
	      gcc_checking_assert (!more_range.undefined_p ());
	      result_range.intersect (more_range);
	    }
	}
      else if (code == POINTER_PLUS_EXPR)
	{
	  symbolic_range more_range;

	  if (compute_range_for_pointer_plus (rhs1, rhs2, more_range))
	    {
	      gcc_checking_assert (!more_range.undefined_p ());
	      result_range.intersect (more_range);
	    }
	}
    }
  else
    return false;

  return true;
}

symbolic_range
symbolic_vrp_prop::compute_range_by_statement (tree result)
{
  tree type = TREE_TYPE (result);
  symbolic_range result_range;

  if (!compute_range_by_statement (result, result_range))
    result_range.set_varying (type);

  if (POINTER_TYPE_P (type) && result_range.varying_p ())
    result_range.init (result);

  return result_range;
}

bool
symbolic_vrp_prop::update_range_by_statement (tree result)
{
  symbolic_range &range = get_range (result);

  return range.intersect_r (compute_range_by_statement (result));
}

static bool
calculate_distance (tree step, tree niter, tree type, wide_int &wi_dist)
{
  tree range_type = get_range_type (type);

  gcc_checking_assert (TYPE_UNSIGNED (TREE_TYPE (niter)));

  if (wi::neg_p (wi::to_wide (niter)))
    return false;

  if (tree_int_cst_lt (TYPE_MAX_VALUE (range_type), niter))
    return false;

  wi::overflow_type overflow;
  unsigned prec = TYPE_PRECISION (range_type);
  wide_int wi_niter = wi::to_wide (niter, prec);
  wide_int wi_step = wi::to_wide (step, prec);

  wi_dist = wi::smul (wi_niter, wi_step, &overflow);
  if (overflow || wi_dist == wi::min_value (signed_type_for (range_type)))
    return false;

  return true;
}

bool
symbolic_vrp_prop::update_range_by_scev (tree result)
{
  auto &scev_desc = get_scev_desc (result);
  tree init = scev_desc.init;

  if (!init)
    return false;

  symbolic_range &range = get_range (result);
  symbolic_range niter_range = get_range_from_tree (scev_desc.niter);
  tree range_type = get_range_type (result);
  tree type = TREE_TYPE (result);
  wide_int wi_dist;

  scev_desc.new_dist_p = false;

  if (niter_range.undefined_p ())
    return range.intersect_r (&niter_range);

  if (niter_range.kind () != VR_RANGE
      || wi::neg_p (wi::to_wide (niter_range.min ())))
    return false;

  if (!calculate_distance (scev_desc.step, niter_range.max (), type, wi_dist))
    return false;

  symbolic_range init_range = get_range_from_tree (init);
  symbolic_range scev_range;
  symbolic_range dist_range;

  if (wi::neg_p (wi_dist) && TYPE_UNSIGNED (range_type))
    {
      dist_range.set (build_zero_cst (range_type),
		      wide_int_to_tree (range_type, -wi_dist));

      symbolic_range_fold_binary_expr (&scev_range, MINUS_EXPR, range_type,
				       &init_range, &dist_range);
    }
  else
    {
      if (wi::neg_p (wi_dist))
	dist_range.set (wide_int_to_tree (range_type, wi_dist),
			build_zero_cst (range_type));
      else
	dist_range.set (build_zero_cst (range_type),
			wide_int_to_tree (range_type, wi_dist));

      symbolic_range_fold_binary_expr (&scev_range, PLUS_EXPR, type,
				       &init_range, &dist_range);
    }

  scev_desc.wi_dist = wi_dist;
  scev_desc.new_dist_p = true;

  return range.intersect_r (&scev_range);
}

bool
symbolic_vrp_prop::update_operand_range (tree operand, gimple *stmt,
					 symbolic_range &new_range,
					 auto_vec<tree> &operands)
{
  symbolic_range opnd_range = get_range (operand);

  opnd_range.intersect (new_range);

  if (opnd_range.undefined_p ())
    return false;

  symbolic_range &range = get_range (operand);

  if (range.equal_p (opnd_range))
    return false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n");
      dump_stmt (dump_file, SSA_NAME_DEF_STMT (operand), false);
      dump_range (dump_file, range);

      dump_stmt (dump_file, "> Update by result of ", stmt);
      dump_range (dump_file, range);
    }

  range = opnd_range;
  operands.safe_push (operand);
  return true;
}

bool
symbolic_vrp_prop::update_range_by_semantics (tree result)
{
  gimple *stmt = SSA_NAME_DEF_STMT (result);
  symbolic_range &range = get_range (result);
  tree symbol = range.symbol ();
  tree size;

  if (!symbol)
    return false;

  if (TREE_CODE (symbol) == ADDR_EXPR)
    {
      tree var = TREE_OPERAND (symbol, 0);

      if (!VAR_P (var))
	return false;

      size = TYPE_SIZE_UNIT (TREE_TYPE (var));
      if (!size || TREE_CODE (size) != INTEGER_CST)
	return false;
    }
  else if (!memory_alloc_base_p (symbol))
    return false;
  else if (!(size = memory_alloc_size (SSA_NAME_DEF_STMT (symbol))))
    return false;

  basic_block bb = gimple_bb (stmt);
  widest_int wi_size = wi::to_widest (size);
  imm_use_iterator use_iter;
  gimple *use_stmt;
  bool update = false;

  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, result)
    {
      if (!gimple_vuse (use_stmt) || !is_gimple_assign (use_stmt))
	continue;

      basic_block use_bb = gimple_bb (use_stmt);

      if (use_bb != bb && !dominated_by_p (CDI_POST_DOMINATORS, bb, use_bb))
	continue;

      tree memref = NULL_TREE;
      HOST_WIDE_INT offset;

      if (gimple_vdef (use_stmt))
	memref = gimple_assign_lhs (use_stmt);
      else if (gimple_assign_load_p (use_stmt))
	memref = gimple_assign_rhs1 (use_stmt);
      else
	continue;

      if (get_mem_access_simple_base (memref, &offset) != result || offset < 0)
	continue;

      tree mem_type = TREE_TYPE (memref);
      widest_int mem_size = wi::to_widest (TYPE_SIZE_UNIT (mem_type));
      widest_int wmin = -offset;
      widest_int wmax = wi_size - mem_size - offset;

      if (wmin > wmax
	  || !wi::fits_to_tree_p (wmin, ptrdiff_type_node)
	  || !wi::fits_to_tree_p (wmax, ptrdiff_type_node))
	continue;

      /* Pointer to access variable should not exceed range of memory area
	 assigned to the variable.  */
      symbolic_range new_range = range;

      new_range.set (wide_int_to_tree (ptrdiff_type_node, wmin),
		     wide_int_to_tree (ptrdiff_type_node, wmax));

      new_range.intersect (range);

      /* User code might contain invalid memory access, just exclude it if
	 found.  */
      if (!new_range.undefined_p () && !new_range.equal_p (range))
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      if (!update)
		{
		  fprintf (dump_file, "\n");
		  dump_stmt (dump_file, stmt, false);
		  dump_range (dump_file, range);
		}

	      fprintf (dump_file, "> Update by semantics from ");
	      print_gimple_stmt (dump_file, use_stmt, 0, TDF_NONE);
	      dump_range (dump_file, new_range);
	    }
	  range = new_range;
	  update = true;
	}
    }

  return update;
}

bool
symbolic_vrp_prop::update_operand_range_by_result (tree result,
						   auto_vec<tree> &operands)
{
  gimple *stmt = SSA_NAME_DEF_STMT (result);
  symbolic_range range = get_range (result);

  if (range.full_p () || range.undefined_p ())
    return false;

  if (tree copy = get_ssa_copy (stmt, true, MATCH_TYPE))
    return update_operand_range (copy, stmt, range, operands);

  /* TODO: Now we do not back-propagate range through PHI since it needs to
     consider problem of computation convergence.  */
  if (!is_gimple_assign (stmt))
    return false;

  tree rhs1 = gimple_assign_rhs1 (stmt);
  tree type = TREE_TYPE (result);
  enum tree_code code = gimple_assign_rhs_code (stmt);

  if (TREE_CODE_CLASS (code) == tcc_unary)
    {
      tree rhs1_type = TREE_TYPE (rhs1);

      if (CONVERT_EXPR_CODE_P (code))
	{
	 if (TYPE_PRECISION (type) != TYPE_PRECISION (rhs1_type))
	   return false;
	}
      else if (code != NEGATE_EXPR && code != BIT_NOT_EXPR)
	return false;

      symbolic_range rhs1_range;

      symbolic_range_fold_unary_expr (&rhs1_range, code, rhs1_type, &range,
				      type);

      return update_operand_range (rhs1, stmt, rhs1_range, operands);
    }

  if (TREE_CODE_CLASS (code) == tcc_binary)
    {
      tree rhs2 = gimple_assign_rhs2 (stmt);
      tree ssa_opnd;
      symbolic_range cst_range;

      if (TREE_CODE (rhs1) == SSA_NAME)
	{
	  ssa_opnd = rhs1;
	  cst_range = get_range_from_tree (rhs2);
	}
      else if (TREE_CODE (rhs2) == SSA_NAME)
	{
	  ssa_opnd = rhs2;
	  cst_range = get_range_from_tree (rhs1);
	}
      else
	return false;

      if (!cst_range.singleton_p ())
	return false;

      if (code == POINTER_PLUS_EXPR)
	{
	  if (ssa_opnd == rhs1)
	    {
	      symbolic_range  tmp_range = cst_range;

	      symbolic_range_fold_unary_expr (&cst_range, NEGATE_EXPR,
					      TREE_TYPE (rhs2), &tmp_range,
					      TREE_TYPE (rhs2));
	    }
	  else
	    {
	      code = POINTER_DIFF_EXPR;
	      type = ptrdiff_type_node;
	    }
	}
      else if (code == PLUS_EXPR)
	code = MINUS_EXPR;
      else if (code == MINUS_EXPR)
	{
	  if (ssa_opnd == rhs1)
	    code = PLUS_EXPR;
	  else
	    std::swap (range, cst_range);
	}
      else if (code == BIT_XOR_EXPR)
	;
      else if (code == MULT_EXPR)
	{
	  tree scale;

	  cst_range.singleton_p (&scale);

	  if (integer_zerop (scale))
	    return false;

	  /* TODO: handle negative dividend.  */
	  if (tree_int_cst_sgn (scale) < 0)
	    return false;

	  /* For multiplication, we could not simply shrink result range by
	     scale due to possible overflow of the operation.  */
	  if (!TYPE_OVERFLOW_UNDEFINED (type) && range.kind () != VR_RANGE)
	    return false;

	  code = TRUNC_DIV_EXPR;
	}
      else if (code == EXACT_DIV_EXPR)
	code = MULT_EXPR;
      else if (code == TRUNC_DIV_EXPR)
	{
	  /* TODO: Support division.  */
	  return false;
	}
      else
	return false;

      symbolic_range ssa_range;

      symbolic_range_fold_binary_expr (&ssa_range, code, type, &range,
				       &cst_range);

      return update_operand_range (ssa_opnd, stmt, ssa_range, operands);
    }

  return false;
}

bool
symbolic_vrp_prop::update_ssa_constraint (ssa_constraint *constraint,
					  tree other, bool is_le,
					  const wide_int &value)
{
  ssa_constraint *other_constraint = get_constraint (other);
  compare_operand cmp_opnd (other, value, false);
  bool changed = constraint->intersect (&cmp_opnd, is_le);

  if (other_constraint)
    {
      auto cmp_opnds = ssa_constraint::derive (&cmp_opnd,
				other_constraint->get_operands (is_le), is_le);

      changed |= constraint->intersect (cmp_opnds, is_le);
    }

  return changed;
}

bool
symbolic_vrp_prop::update_ssa_constraint (tree name, tree other, bool is_le,
					  const wide_int &value)
{
  ssa_constraint *&constraint = get_constraint (name);

  if (!constraint)
    constraint = new ssa_constraint;

  return update_ssa_constraint (constraint, other, is_le, value);
}

bool
symbolic_vrp_prop::update_ssa_constraint_by_predicate (tree name,
						ssa_predicate &predicate)
{
  tree opnd = predicate.opnd;

  if (!opnd || TREE_CODE (opnd) != SSA_NAME)
    return false;

  tree type = TREE_TYPE (name);
  tree range_type = get_range_type (type);
  bool is_le = false;
  HOST_WIDE_INT cst = 0;

  switch (predicate.op)
    {
    case LE_EXPR:
      is_le = true;
      break;

    case LT_EXPR:
      is_le = true;
      if (!TYPE_UNSIGNED (get_range_type (type)))
	cst = -1;
      break;

    case GE_EXPR:
      break;

    case GT_EXPR:
      cst = 1;
      break;

    default:
      return false;
    }

  return update_ssa_constraint (name, opnd, is_le,
				wi::shwi (cst, TYPE_PRECISION (range_type)));
}

bool
symbolic_vrp_prop::update_ssa_constraint_by_predicate (tree name)
{
  return update_ssa_constraint_by_predicate (name, get_predicate (name));
}

bool
symbolic_vrp_prop::derive_constraint_for_cvt (tree type, const tree name,
					      ssa_constraint &constraint)
{
  ssa_constraint *name_constraint = get_constraint (name);

  if (!name_constraint)
    return false;

  const symbolic_range &name_range = get_range (name);

  if (name_range.kind () != VR_RANGE
      || wi::neg_p (wi::to_wide (name_range.min ()))
      || wi::neg_p (wi::to_wide (name_range.max ())))
    return false;

  bool changed = false;

  for (auto cmp_opnd : name_constraint->le_opnds)
    {
      if (cmp_opnd.convert (type, true))
	changed |= constraint.intersect (&cmp_opnd, true);
    }

  for (auto cmp_opnd : name_constraint->ge_opnds)
    {
      if (cmp_opnd.convert (type, false))
	changed |= constraint.intersect (&cmp_opnd, false);
    }

  return changed;
}

bool
symbolic_vrp_prop::derive_constraint_for_add (const tree name,
					      const tree add_value, bool plus,
					      ssa_constraint &constraint)
{
  ssa_constraint *name_constraint = get_constraint (name);

  if (!name_constraint)
    return false;

  bool overflow = !TYPE_OVERFLOW_UNDEFINED (TREE_TYPE (name));

  constraint.le_opnds
	= ssa_constraint::derive (name, add_value, plus, overflow,
				  name_constraint->le_opnds, true);
  constraint.ge_opnds
	= ssa_constraint::derive (name, add_value, plus, overflow,
				  name_constraint->ge_opnds, false);
  return true;
}

bool
symbolic_vrp_prop::intersect_ssa_constraint (tree result,
					     ssa_constraint *constraint,
					     bool copy)
{
  if (!constraint || constraint->varying_p ())
    return false;

  ssa_constraint *&result_constraint = get_constraint (result);

  if (!result_constraint)
    {
      result_constraint = new ssa_constraint (*constraint, copy);
      return true;
    }

  return result_constraint->intersect (*constraint);
}

bool
symbolic_vrp_prop::copy_ssa_constraint (tree result, tree source)
{
  bool changed = intersect_ssa_constraint (result, get_constraint (source),
					   true /* copy */);
  tree pred_opnd = get_predicate (result).opnd;
  gimple *use_stmt;
  imm_use_iterator use_iter;

  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, source)
    {
      if (!include_stmt_p (use_stmt)
	  || !ssa_strictly_dominated_by_p (result, use_stmt))
	continue;

      tree use = gimple_get_lhs (use_stmt);

      /* Covered by predicate, no need to repeat computation.  */
      if (use == pred_opnd)
	continue;

      ssa_predicate &use_predicate = get_predicate (use);

      if (use_predicate.opnd != source)
	continue;

      /* TODO: Some comparison relation between two variables might be missed,
	 for example ssa_3 and ssa_4 in the below case.  A complete solution
	 is to build a full comparison constraint graph.

	 ssa_1_a = ssa_1  // range predicate (ssa_1 < ssa_2)
	 ssa_2_a = ssa_2  // range predicate (ssa_2 > ssa_1_a)

	 ssa_3 = ssa_2_a
	 ssa_4 = ssa_1_a
	 */
      ssa_predicate predicate;

      predicate.op = swap_tree_comparison (use_predicate.op);
      predicate.opnd = use;

      changed |= update_ssa_constraint_by_predicate (result, predicate);
    }

  return changed;
}

void
symbolic_vrp_prop::get_constraint_for_union (tree result, tree arg,
					     ssa_constraint &constraint)
{
  if (TREE_CODE (arg) != SSA_NAME)
    return;

  if (get_range (arg).undefined_p ())
    {
      constraint.set_undefined ();
      return;
    }

  if (ssa_strictly_dominated_by_p (result, arg))
    {
      constraint.intersect (arg, true);
      constraint.intersect (arg, false);
    }

  if (auto arg_constraint = get_constraint (arg))
    {
      for (auto &cmp_opnd : arg_constraint->le_opnds)
	{
	  if (ssa_strictly_dominated_by_p (result, cmp_opnd.name_to_ssa ()))
	    constraint.intersect (&cmp_opnd, true);
	}

      for (auto &cmp_opnd : arg_constraint->ge_opnds)
	{
	  if (ssa_strictly_dominated_by_p (result, cmp_opnd.name_to_ssa ()))
	    constraint.intersect (&cmp_opnd, false);
	}
    }
}

static void
aff_combination_init (aff_tree *comb, tree name,
		      const widest_int &scale = 1,
		      bool reverse = false)
{
  tree type = TREE_TYPE (name);

  if (TREE_CODE (name) == INTEGER_CST)
    aff_combination_const (comb, type, wi::to_widest (name));
  else if (TREE_CODE (name) == SSA_NAME)
    aff_combination_elt (comb, type, name);
  else
    tree_to_aff_combination (name, type, comb);

  aff_combination_scale (comb, reverse ? -scale : scale);
}

/* A helper function for fold_to_one, NAME1 is supposed to be dominated by
   NAME2.  */

bool
symbolic_vrp_prop::fold_to_one_by_dominance (tree name1,
					     const widest_int &coef1,
					     tree name2,
					     const widest_int &coef2,
					     aff_tree *comb)
{
  if (operand_equal_p (name1, name2))
    {
      aff_combination_init (comb, name1, coef1 + coef2);
      return true;
    }

  if (TREE_CODE (name1) != SSA_NAME)
    return false;

  if (tree copy = get_ssa_copy (name1, true))
    return fold_to_one (copy, coef1, name2, coef2, comb);

  aff_tree tmp_comb;
  gimple *stmt1 = SSA_NAME_DEF_STMT (name1);
  gimple *stmt2;

  if (!is_gimple_assign (stmt1))
    return false;

  enum tree_code code = gimple_assign_rhs_code (stmt1);
  tree rhs[2] = { gimple_assign_rhs1 (stmt1), gimple_assign_rhs2 (stmt1) };
  bool sign[2];

  switch (code)
    {
    case POINTER_PLUS_EXPR:
    case POINTER_DIFF_EXPR:
    case PLUS_EXPR:
    case MINUS_EXPR:
      sign[0] = false;
      sign[1] = (code == POINTER_DIFF_EXPR || code == MINUS_EXPR);

      for (int i = 0; i < 2; i++)
	{
	  if (!fold_to_one (rhs[1 - i], sign[1 - i] ? -coef1 : coef1, name2,
			    coef2, comb))
	    continue;

	  if (TREE_CODE (rhs[i]) == INTEGER_CST || !comb->n)
	    {
	      aff_combination_init (&tmp_comb, rhs[i], coef1, sign[i]);
	      aff_combination_add (comb, &tmp_comb);
	      return true;
	    }

	  /* TODO: Handle ADDR_EXPR and other EXPRs that can be expanded to
	     affine combination of multiple SSAs.  */
	  gcc_checking_assert (comb->n == 1);

	  if (fold_to_one (rhs[i], sign[i] ? -coef1 : coef1,
			   comb->elts[0].val, comb->elts[0].coef, &tmp_comb))
	    {
	      /* Clear element in comb.  */
	      comb->n = 0;
	      aff_combination_add (comb, &tmp_comb);
	      return true;
	    }
	}
      break;

    case MULT_EXPR:
      if (TREE_CODE (rhs[1]) == INTEGER_CST)
	return fold_to_one (rhs[0], coef1 * wi::to_widest (rhs[1]), name2,
			    coef2, comb);

      if (TREE_CODE (name2) != SSA_NAME)
	return false;

      stmt2 = SSA_NAME_DEF_STMT (name2);
      if (!is_gimple_assign (stmt2))
	return false;

      if (gimple_assign_rhs_code (stmt2) == MULT_EXPR)
	{
	  tree name2_rhs[2] = { gimple_assign_rhs1 (stmt2),
				gimple_assign_rhs2 (stmt2) };

	  for (int i = 0; i < 2; i++)
	    for (int j = 0; j < 2; j++)
	      {
		if (!operand_equal_p (rhs[i], name2_rhs[j]))
		  continue;

		if (!fold_to_one (rhs[1 - i], coef1, name2_rhs[1 - j], coef2,
				  comb)
		    || comb->n)
		  return false;

		gcc_assert (comb->offset.is_constant ());

		aff_combination_init (comb, rhs[i]);
		aff_combination_scale (comb, comb->offset.coeffs[0]);

		return true;
	      }
	}
      break;

    case LSHIFT_EXPR:
      if (TREE_CODE (rhs[1]) == INTEGER_CST)
	return fold_to_one (rhs[0], coef1 << wi::to_widest (rhs[1]), name2,
			    coef2, comb);
      break;

    case RSHIFT_EXPR:
    case TRUNC_DIV_EXPR:
    case CEIL_DIV_EXPR:
    case FLOOR_DIV_EXPR:
    case ROUND_DIV_EXPR:
      if (TREE_CODE (rhs[0]) == SSA_NAME && TREE_CODE (rhs[1]) == INTEGER_CST)
	{
	  HOST_WIDE_INT bits;

	  if (code == RSHIFT_EXPR)
	    {
	      if (!tree_fits_shwi_p (rhs[1]))
		break;

	      bits = tree_to_shwi (rhs[1]);
	    }
	  else
	    {
	      widest_int cst = wi::to_widest (rhs[1]);

	      if (wi::popcount (cst) != 1)
		break;

	      bits = wi::ctz (cst);
	    }

	  if (get_range (rhs[0]).zero_bits () < bits || bits < 0)
	    break;

	  widest_int div_coef1 = coef1 >> bits;

	  if ((div_coef1 << bits) == coef1)
	    return fold_to_one (rhs[0], div_coef1, name2, coef2, comb);
	}
      break;

    case EXACT_DIV_EXPR:
      if (TREE_CODE (rhs[1]) == INTEGER_CST )
	{
	  widest_int div_coef1 = wi::to_widest (rhs[1]);
	  widest_int rem_coef1;

	  if (div_coef1 == 0 || wi::neg_p (wi::to_wide (rhs[1])))
	    break;

	  div_coef1 = wi::divmod_trunc (coef1, div_coef1, SIGNED, &rem_coef1);

	  if (rem_coef1 == 0)
	    return fold_to_one (rhs[0], div_coef1, name2, coef2, comb);
	}
      break;

    case NEGATE_EXPR:
    case BIT_NOT_EXPR:
      if (!fold_to_one (rhs[0], -coef1, name2, coef2, comb))
	return false;

      if (code == BIT_NOT_EXPR)
	{
	  aff_combination_const (&tmp_comb, TREE_TYPE (name1), -coef1);
	  aff_combination_add (comb, &tmp_comb);
	}
      return true;

    CASE_CONVERT:
      {
	tree type = TREE_TYPE (name1);
	tree rhs_type = TREE_TYPE (rhs[0]);

	if (TYPE_PRECISION (type) != TYPE_PRECISION (rhs_type))
	  return false;

	if (POINTER_TYPE_P (type) != POINTER_TYPE_P (rhs_type))
	  return false;

	if (INTEGRAL_TYPE_P (type) != INTEGRAL_TYPE_P (rhs_type))
	  return false;

	return fold_to_one (rhs[0], coef1, name2, coef2, comb);
      }

    default:
      break;
    }

  return false;
}

/* Fold a two-SSAs expression (coef1 * name1 + coef2 * name2) to one SSA
   if possible.  */

bool
symbolic_vrp_prop::fold_to_one (tree name1, const widest_int &coef1,
				tree name2, const widest_int &coef2,
				aff_tree *comb)
{
  bool swap = false;

  if (TREE_CODE (name1) != SSA_NAME)
    swap = true;
  else if (TREE_CODE (name2) == SSA_NAME)
    swap = ssa_strictly_dominated_by_p (name2, name1);

  if (swap)
    return fold_to_one_by_dominance (name2, coef2, name1, coef1, comb);
  else
    return fold_to_one_by_dominance (name1, coef1, name2, coef2, comb);
}

const tree_pair &
symbolic_vrp_prop::fold_to_one (tree name1, tree name2, bool minus)
{
  tree_pair name_key (name1, name2);
  bool existed;
  auto &cache = fold_cache[minus].get_or_insert (name_key, &existed);
  aff_tree comb;

  if (existed)
    return cache;

  /* Note: since we only use zero-bit information of range computed at the
     stage of join-propagation, we do not need to do folding iteratively
     when referenced range is renewed.  If the folding function will be
     extended in some way of using other range information, we have to
     REPEAT process of folding.  */

  cache.first = NULL_TREE;
  cache.second = NULL_TREE;

  if (!fold_to_one (name1, 1, name2, minus ? -1 : 1, &comb))
    return cache;

  widest_int value_int = comb.offset.coeffs[0];
  tree cmp_name = NULL_TREE;

  gcc_assert (comb.n <= 1 && comb.offset.is_constant ());

  if (comb.n == 1)
    {
      tree name = cmp_name = comb.elts[0].val;

      if (comb.elts[0].coef == -1)
	{
	  gimple *stmt = SSA_NAME_DEF_STMT (name);

	  if (!is_gimple_assign (stmt))
	    return cache;

	  enum tree_code code = gimple_assign_rhs_code (stmt);
	  tree rhs1, rhs2;

	  switch (code)
	    {
	    case MINUS_EXPR:
	      rhs1 = gimple_assign_rhs1 (stmt);

	      if (TREE_CODE (rhs1) != INTEGER_CST)
		return cache;

	      rhs2 = gimple_assign_rhs2 (stmt);
	      if (TREE_CODE (rhs2) != SSA_NAME)
		return cache;

	      cmp_name = rhs2;
	      value_int -= wi::to_widest (rhs1);
	      break;

	    case NEGATE_EXPR:
	    case BIT_NOT_EXPR:
	      rhs1 = gimple_assign_rhs1 (stmt);

	      if (TREE_CODE (rhs1) != SSA_NAME)
		return cache;

	      cmp_name = rhs1;

	      if (code == BIT_NOT_EXPR)
		value_int += 1;
	      break;

	    default:
	      return cache;
	    }
	}
      else if (comb.elts[0].coef != 1)
	return cache;
    }
  else
    return cache;

  if (cmp_name)
    {
      cache.first = cmp_name;
      cache.second
	= wide_int_to_tree (get_range_type (TREE_TYPE (name1)), value_int);
    }

  return cache;
}

bool
symbolic_vrp_prop::minus_to_compare_operand (tree name1, tree name2,
					     compare_operand *cmp_opnd)
{
  /* This should be handled in get_minus_range_from_constraint().  */
  if (name1 == name2)
    return false;

  const tree_pair &addr_offset = fold_to_one (name1, name2, /* minus= */ true);

  if (!addr_offset.first)
    return false;

  cmp_opnd->set_name (addr_offset.first);
  cmp_opnd->set_value (addr_offset.second);

  return true;
}

bool
symbolic_vrp_prop::pointer_minus_to_constraint (
				const compare_operand &name1_opnd,
				const compare_operand &name2_opnd,
				ssa_constraint &constraint, bool is_le)
{
  tree type = name1_opnd.name_type ();
  tree minus_type;
  tree name2_max = NULL_TREE;
  bool is_ptrdiff;

  if (name1_opnd.overflow)
    return false;

  if (POINTER_TYPE_P (name2_opnd.name_type ()))
    {
      /* For compare_operand of pointer type, if "name + value" does not
	 overflow, this implies "name + value" should be inside same object
	 pointed into by "name".

	 And if there exists comparison relation between two pointers, it
	 also means these two pointers are derived from same object.

	 An object is not allowed to be larger than half of the address
	 space, and if pointer type is assumed to never overflow
	 (!flag_wrapv_pointer), we can infer a fact that looks nature but
	 not always correct if overflow happens.

	      ptr1 - ptr2 >= 0   <==>   ptr1 >= ptr2

	 In other words, pointer_diff operation never produce overflow
	 result.  */
      if (name2_opnd.overflow)
	return false;

      /* pointer - pointer */
      is_ptrdiff = true;
      minus_type = get_range_type (type);
    }
  else
    {
      const symbolic_range range = name2_opnd.range ();

      /* There is an implicit type conversion from size_t to ssize_t for
	 pointer plus operation, so comparison relationship of offset SSA
	 remains for pointer comparison only when offset's value range is
	 in [0, signed_max] or [signed_min, 0]. But now we only consider
	 the former.  */
      if (range.kind () != VR_RANGE
	  || wi::neg_p (wi::to_wide (range.max ())))
	return false;

      /* pointer - integer */
      is_ptrdiff = false;
      minus_type = type;
      name2_max = range.max ();
    }

  compare_operand cmp_opnd (minus_type);

  if (!minus_to_compare_operand (name1_opnd.name_to_ssa (),
				 name2_opnd.name_to_ssa (), &cmp_opnd)
      || !cmp_opnd.adjust_value (name1_opnd.value, true)
      || !cmp_opnd.adjust_value (name2_opnd.value, false))
    return false;

  if (!is_ptrdiff && cmp_opnd.overflow)
    {
      const wide_int &value_int = wi::to_wide (cmp_opnd.value);

      /* Given two pointers ptr_1, ptr_2, and a positive offset, we know that
	 ptr_2 - (ptr_1 + offset) >= 0, then if we can prove that
	 ptr_2 - ptr_1 > 0, then (ptr1 + offset) must be inside object pointed
	 by ptr2 and ptr1, and they have comparision relationship as:

	      ptr_2 >= ptr_1 + offset >= ptr_1

	 Otherwise, they might be:

		.........................................
		^                               ^       ^
	   ptr1 + offset (pointer wraps)      ptr2    ptr1
	*/
      if (wi::neg_p (value_int)
	  || wi::neg_p (value_int + wi::to_wide (name2_max)))
	return false;

      cmp_opnd.overflow = false;
    }

  return constraint.intersect (&cmp_opnd, is_le);
}

bool
symbolic_vrp_prop::compute_constraint_for_minus (tree name1, tree name2,
						 ssa_constraint &constraint)
{
  tree type = TREE_TYPE (name1);

  /* TODO: support integer minus operation.  */
  if (!POINTER_TYPE_P (type) || !TYPE_OVERFLOW_UNDEFINED (type))
    return false;

  ssa_constraint *name_constraint[2] = { get_constraint (name1),
					 get_constraint (name2) };

  if (!name_constraint[0] && !name_constraint[1])
    return false;

  if (!POINTER_TYPE_P (TREE_TYPE (name2)))
    {
      /* This is pointer minus offset operation.  Although offset is size_t,
	 it is treated as ssize_t.  And here we check that the offset is in
	 the range [0, signed_max].  */
      const symbolic_range &range = get_range (name2);

      if (range.kind () != VR_RANGE
	  || wi::neg_p (wi::to_wide (range.max ())))
	return false;
    }

  vec<compare_operand> bounds[2][2];  /* [name1 / name2][le / ge] */

  for (unsigned n = 0; n < 2; n++)
    {
      if (name_constraint[n])
	{
	  bounds[n][0] = name_constraint[n]->le_opnds;
	  bounds[n][1] = name_constraint[n]->ge_opnds;
	}
      else
	{
	  bounds[n][0] = vNULL;
	  bounds[n][1] = vNULL;
	}
    }

  const compare_operand name1_opnd (name1);
  const compare_operand name2_opnd (name2);
  bool changed = false;

  for (unsigned c = 0; c < 2; c++)
    {
      /*
       *  Suppose that:
       *      ge1 <= name1 <= le1
       *      ge2 <= name2 <= le2
       */
      for (const auto &name2_bound : bounds[1][c])
	{
	  /*  name1 - le2 <= name1 - name2 <= name1 - ge2 */
	  changed |= pointer_minus_to_constraint (name1_opnd, name2_bound,
						  constraint, c);
	}

      for (const auto &name1_bound : bounds[0][c])
	{
	  /*  ge1 - name2 <= name1 - name2 <= le1 - name2 */
	  changed |= pointer_minus_to_constraint (name1_bound, name2_opnd,
						  constraint, !c);

	  /*  ge1 - le2 <= name1 - name2 <= le1 - ge2  */
	  for (const auto &name2_bound_rev : bounds[1][1 - c])
	    changed |= pointer_minus_to_constraint (name1_bound,
						    name2_bound_rev,
						    constraint, !c);
	}
    }

  return changed;
}

bool
symbolic_vrp_prop::compute_constraint_for_pointer_plus (tree pointer,
							tree offset,
						  ssa_constraint &constraint)
{
  if (TREE_CODE (pointer) != SSA_NAME)
    return false;

  bool folded = false;

  if (TREE_CODE (offset) == SSA_NAME)
    {
      auto &cache = fold_to_one (pointer, offset, /* minus= */ false);

      if (cache.first)
	{
	  pointer = cache.first;
	  offset = cache.second;
	  folded = true;
	}
    }

  symbolic_range &range = get_range (pointer);
  symbolic_range offset_range = get_range_from_tree (offset);
  bool no_wrap = false;
  bool changed = false;

  if (!folded && range.singleton_p ())
    return false;

  if (offset_range.singleton_p (&offset))
    no_wrap = true;
  else if (range.kind () == VR_RANGE)
    {
      symbolic_range_fold_unary_expr (CONVERT_EXPR, ptrdiff_type_node,
				      &offset_range, TREE_TYPE (offset));

      if (offset_range.kind () == VR_RANGE
	  && !range_wrap_p (range, wi::to_wide (offset_range.max ()))
	  && !range_wrap_p (range, wi::to_wide (offset_range.min ())))
	no_wrap = true;
    }

  if (no_wrap)
    {
      if (update_ssa_constraint (&constraint, pointer, true,
				 wi::to_wide (offset_range.max ())))
	changed = true;

      if (update_ssa_constraint (&constraint, pointer, false,
				 wi::to_wide (offset_range.min ())))
	changed = true;
    }

  if (TREE_CODE (offset) == SSA_NAME)
    {
      gimple *stmt = SSA_NAME_DEF_STMT (offset);

      if (!is_gimple_assign (stmt)
	  || gimple_assign_rhs_code (stmt) != NEGATE_EXPR)
	return changed;

      tree minus_offset = gimple_assign_rhs1 (stmt);

      if (TREE_CODE (minus_offset) != SSA_NAME)
	return changed;

      if (compute_constraint_for_minus (pointer, minus_offset, constraint))
	changed = true;
    }

  return changed;
}

bool
symbolic_vrp_prop::update_ssa_constraint_by_statement (tree result)
{
  tree type = TREE_TYPE (result);
  gimple *stmt = SSA_NAME_DEF_STMT (result);

  if (gimple_code (stmt) == GIMPLE_PHI)
    {
      ssa_constraint phi_constraint (/* undefined= */ true);

      for (unsigned i = 0; i < gimple_phi_num_args (stmt); ++i)
	{
	  tree arg = PHI_ARG_DEF (stmt, i);
	  ssa_constraint arg_constraint;

	  get_constraint_for_union (result, arg, arg_constraint);

	  if (arg_constraint.varying_p ())
	    return false;

	  phi_constraint.union_ (arg_constraint);
	}

      return intersect_ssa_constraint (result, &phi_constraint);
    }

  if (is_gimple_assign (stmt))
    {
      tree rhs1 = gimple_assign_rhs1 (stmt);
      enum tree_code code = gimple_assign_rhs_code (stmt);

      if (code == COND_EXPR)
	{
	  tree rhs2 = gimple_assign_rhs2 (stmt);
	  tree rhs3 = gimple_assign_rhs3 (stmt);

	  if (TREE_CODE (rhs2) != SSA_NAME || TREE_CODE (rhs3) != SSA_NAME)
	    return false;

	  ssa_constraint rhs2_constraint;
	  ssa_constraint rhs3_constraint;

	  get_constraint_for_union (result, rhs2, rhs2_constraint);
	  get_constraint_for_union (result, rhs3, rhs3_constraint);
	  rhs2_constraint.union_ (rhs3_constraint);

	  return intersect_ssa_constraint (result, &rhs2_constraint);
	}

      if (TREE_CODE_CLASS (code) == tcc_unary)
	{
	  tree rhs1_type = TREE_TYPE (rhs1);

	  if (CONVERT_EXPR_CODE_P (code) && TREE_CODE (rhs1) == SSA_NAME)
	    {
	      if (types_compatible_p (type, rhs1_type))
		return copy_ssa_constraint (result, rhs1);

	      if (INTEGRAL_TYPE_P (type) && INTEGRAL_TYPE_P (rhs1_type)
		  && TYPE_PRECISION (type) == TYPE_PRECISION (rhs1_type))
		{
		  ssa_constraint new_constraint;

		  derive_constraint_for_cvt (type, rhs1, new_constraint);

		  return intersect_ssa_constraint (result, &new_constraint);
		}
	    }
	}
      else if (TREE_CODE_CLASS (code) == tcc_binary)
	{
	  tree rhs2 = gimple_assign_rhs2 (stmt);
	  ssa_constraint new_constraint;

	  if (code == POINTER_PLUS_EXPR)
	    {
	      if (!compute_constraint_for_pointer_plus (rhs1, rhs2,
							new_constraint))
		return false;
	    }
	  else if (code == PLUS_EXPR)
	    {
	      if (TREE_CODE (rhs1) == SSA_NAME
		  && TREE_CODE (rhs2) == INTEGER_CST)
		derive_constraint_for_add (rhs1, rhs2, true, new_constraint);
	      else
		return false;
	    }
	  else if (code == MINUS_EXPR)
	    {
	      if (TREE_CODE (rhs1) != SSA_NAME)
		return false;

	      if (TREE_CODE (rhs2) == SSA_NAME)
		compute_constraint_for_minus (rhs1, rhs2, new_constraint);
	      else if (TREE_CODE (rhs2) == INTEGER_CST)
		derive_constraint_for_add (rhs1, rhs2, false, new_constraint);
	      else
		return false;
	    }
	  else if (code == POINTER_DIFF_EXPR)
	    {
	      if (TREE_CODE (rhs1) != SSA_NAME || TREE_CODE (rhs2) != SSA_NAME)
		return false;

	      compute_constraint_for_minus (rhs1, rhs2, new_constraint);
	    }
	  else
	    return false;

	  return intersect_ssa_constraint (result, &new_constraint);
	}
      else if (code == SSA_NAME)
	return copy_ssa_constraint (result, rhs1);
    }

  return false;
}

bool
symbolic_vrp_prop::update_ssa_constraint_by_scev (tree result)
{
  auto &scev_desc = get_scev_desc (result);
  tree init = scev_desc.init;

  if (!init || TREE_CODE (init) != SSA_NAME || !scev_desc.new_dist_p)
    return false;

  const wide_int &wi_dist = scev_desc.wi_dist;

  if ((scev_desc.always_updated
       && TREE_CODE (scev_desc.niter) == INTEGER_CST
       && TYPE_OVERFLOW_UNDEFINED (TREE_TYPE (result)))
      || !range_wrap_p (get_range (init), wi_dist))
    return update_ssa_constraint (result, init, !wi::neg_p (wi_dist), wi_dist);

  return false;
}

bool
symbolic_vrp_prop::update_ssa_constraint (tree result)
{
  bool changed = false;

  if (update_ssa_constraint_by_predicate (result))
    {
      changed = true;

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "> Update compare constraint by predicate\n");
	  fprintf (dump_file, "Compare constraint: ");
	  get_constraint (result)->dump (dump_file);
	  fprintf (dump_file, "\n");
	}
    }

  if (update_ssa_constraint_by_statement (result))
    {
      changed = true;

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "> Update compare constraint by statement\n");
	  fprintf (dump_file, "Compare constraint: ");
	  get_constraint (result)->dump (dump_file);
	  fprintf (dump_file, "\n");
	}
    }

  if (update_ssa_constraint_by_scev (result))
    {
      changed = true;

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "> Update compare constraint by scev\n");
	  fprintf (dump_file, "Compare constraint: ");
	  get_constraint (result)->dump (dump_file);
	  fprintf (dump_file, "\n");
	}
    }

  return changed;
}

static bool
get_iv_update_stmts (class loop *loop, tree iv,
		     auto_vec<gimple *> &update_stmts,
		     auto_vec<tree> &iv_set)
{
  const edge latch = loop_latch_edge (loop);
  gimple *stmt = SSA_NAME_DEF_STMT (iv);
  const tree value = PHI_ARG_DEF_FROM_EDGE (stmt, latch);
  auto_vec<tree> worklist;
  auto_bitmap visited;

  if (TREE_CODE (value) != SSA_NAME)
    return false;

  bitmap_set_bit (visited, SSA_NAME_VERSION (iv));
  bitmap_set_bit (visited, SSA_NAME_VERSION (value));

  worklist.safe_push (value);
  iv_set.safe_push (iv);

  do
    {
      tree name = worklist.pop ();
      gimple *stmt = SSA_NAME_DEF_STMT (name);

      if (!stmt_is_inside_loop (loop, stmt))
	return 0;

      iv_set.safe_push (name);

      if (auto phi = dyn_cast<gphi *> (stmt))
	{
	  for (unsigned i = 0; i < gimple_phi_num_args (phi); ++i)
	    {
	      tree arg = PHI_ARG_DEF (stmt, i);

	      if (TREE_CODE (arg) != SSA_NAME)
		return false;

	      if (bitmap_set_bit (visited, SSA_NAME_VERSION (arg)))
		worklist.safe_push (arg);
	    }
	}
      else if (is_gimple_assign (stmt))
	{
	  tree rhs1 = gimple_assign_rhs1 (stmt);
	  enum tree_code code = gimple_assign_rhs_code (stmt);

	  if (CONVERT_EXPR_CODE_P (code))
	    {
	      if (!types_compatible_p (TREE_TYPE (iv), TREE_TYPE (rhs1)))
		return false;
	    }
	  else if (code == POINTER_PLUS_EXPR || code == PLUS_EXPR
		   || code == MINUS_EXPR)
	    {
	      tree rhs2 = gimple_assign_rhs2 (stmt);

	      if (TREE_CODE (rhs2) != INTEGER_CST)
		return false;

	      update_stmts.safe_push (stmt);
	    }
	  else if (code == COND_EXPR)
	    {
	      tree rhs2 = gimple_assign_rhs2 (stmt);
	      tree rhs3 = gimple_assign_rhs3 (stmt);

	      if (TREE_CODE (rhs2) != SSA_NAME)
		return false;

	      if (bitmap_set_bit (visited, SSA_NAME_VERSION (rhs2)))
		worklist.safe_push (rhs2);

	      rhs1 = rhs3;
	    }
	  else if (code != SSA_NAME)
	    return false;

	  if (TREE_CODE (rhs1) != SSA_NAME)
	    return false;

	  if (bitmap_set_bit (visited, SSA_NAME_VERSION (rhs1)))
	    worklist.safe_push (rhs1);
	}
      else
	return false;
    } while (!worklist.is_empty ());

  return true;
}

static void
replace_ssa (tree old_ssa, tree new_val)
{
  imm_use_iterator use_iter;
  gimple *use_stmt;
  gimple *stmt = SSA_NAME_DEF_STMT (old_ssa);
  gimple_stmt_iterator si = gsi_for_stmt (stmt);
  bool ssa_val_p = TREE_CODE (new_val) == SSA_NAME;

  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, old_ssa)
    {
      use_operand_p use_p;

      FOR_EACH_IMM_USE_ON_STMT (use_p, use_iter)
	SET_USE (use_p, ssa_val_p ? new_val : unshare_expr (new_val));

      if (!ssa_val_p)
	update_stmt (use_stmt);
    }

  gsi_remove (&si, true);
  release_defs (stmt);
}

bool
symbolic_vrp_prop::insert_exit_iv_definition (tree iv, tree init, tree step,
					      tree niter, edge exit)
{
  tree type = TREE_TYPE (iv);
  wide_int wi_dist;

  if (!calculate_distance (step, niter, type, wi_dist))
    return false;

  tree exit_iv = split_ssa_at_edge (iv, exit);

  if (!exit_iv)
    return false;

  tree dist_type = type;
  enum tree_code plus_code = PLUS_EXPR;

  if (POINTER_TYPE_P (type))
    {
      dist_type = sizetype;
      plus_code = POINTER_PLUS_EXPR;
    }

  gimple_seq stmts = NULL;
  gimple *stmt = SSA_NAME_DEF_STMT (exit_iv);
  tree expr = fold_build2 (plus_code, type, init,
			   wide_int_to_tree (dist_type, wi_dist));

  expr = force_gimple_operand (expr, &stmts, true, NULL_TREE);
  gsi_insert_seq_on_edge_immediate (exit, stmts);
  gimple_assign_set_rhs1 (stmt, expr);
  update_stmt (stmt);

  return true;
}

void
symbolic_vrp_prop::init_iv_scev_desc (class loop *loop)
{
  edge exit;
  edge inside = NULL;
  edge entry = loop_preheader_edge (loop);
  tree niter = find_loop_latch_niter (loop, &exit);
  gcond *exit_cond = NULL;
  tree iv_niter_0 = NULL_TREE;
  tree iv_niter_1 = NULL_TREE;
  tree ex_niter_0 = NULL_TREE;
  tree ex_niter_1 = NULL_TREE;

  if (niter != chrec_dont_know
      && (exit_cond = safe_dyn_cast<gcond *> (last_stmt (exit->src))))
    inside = cond_other_edge (exit);

  for (auto si = gsi_start_nonvirtual_phis (loop->header); !gsi_end_p (si);
       gsi_next_nonvirtual_phi (&si))
    {
      gphi *phi = si.phi ();
      tree result = gimple_phi_result (phi);
      tree type = TREE_TYPE (result);

      if (!INTEGRAL_TYPE_P (type) && !POINTER_TYPE_P (type))
	continue;

      auto_vec<gimple *> update_stmts;
      auto_vec<tree> iv_set;

      if (!get_iv_update_stmts (loop, result, update_stmts, iv_set))
	continue;

      if (TYPE_OVERFLOW_UNDEFINED (type))
	{
	  tree init = PHI_ARG_DEF_FROM_EDGE (phi, entry);
	  unsigned update = 0;

	  for (auto stmt : update_stmts)
	    {
	      tree step = gimple_assign_rhs2 (stmt);
	      wide_int offset = wi::to_wide (step);
	      enum tree_code code = gimple_assign_rhs_code (stmt);

	      if (wi::neg_p (offset))
		update |= code == MINUS_EXPR ? 1 : 2;
	      else if (offset != 0)
		update |= code == MINUS_EXPR ? 2 : 1;
	    }

	  if (update == 1)
	    add_predicate (result, GE_EXPR, init);
	  else if (update == 2)
	    add_predicate (result, LE_EXPR, init);
	}

      if (!exit_cond || update_stmts.length () != 1)
	continue;

      gimple *update_stmt = update_stmts[0];
      basic_block update_bb = gimple_bb (update_stmt);

      if (update_bb->loop_father != loop
	  || update_bb->flags & BB_IRREDUCIBLE_LOOP)
	continue;

      tree step = gimple_assign_rhs2 (update_stmt);

      if (gimple_assign_rhs_code (update_stmt) == MINUS_EXPR)
	step = fold_unary (NEGATE_EXPR, TREE_TYPE (step), step);

      tree dom_exit_iv = NULL_TREE;

      /* For iv that is not main iv determining loop iteration, we need
	 to insert assert statement to split lifetime of the iv at the
	 point of loop exit.  */
      for (auto iv : iv_set)
	{
	  if (iv == gimple_cond_lhs (exit_cond)
	      || iv == gimple_cond_lhs (exit_cond))
	    {
	      dom_exit_iv = NULL_TREE;
	      break;
	    }

	  gimple *stmt = SSA_NAME_DEF_STMT (iv);

	  if (!stmt_dominates_stmt_p (stmt, exit_cond))
	    continue;

	  if (!dom_exit_iv
	      || stmt_dominates_stmt_p (SSA_NAME_DEF_STMT (dom_exit_iv), stmt))
	    dom_exit_iv = iv;
	}

      if (!dom_exit_iv)
	continue;

      tree iv_niter = NULL_TREE;
      tree ex_niter = NULL_TREE;

      if (stmt_dominates_stmt_p (exit_cond, update_stmt))
	{
	  if (integer_zerop (niter))
	    continue;

	  if (iv_niter_1)
	    ;
	  else if (TREE_CODE (niter) == INTEGER_CST)
	    {
	      iv_niter_1 = fold_binary (MINUS_EXPR, TREE_TYPE (niter), niter,
					build_one_cst (TREE_TYPE (niter)));
	      ex_niter_0 = niter;
	    }
	  else
	    iv_niter_1 = make_ssa_name (TREE_TYPE (niter));

	  iv_niter = iv_niter_1;
	  ex_niter = ex_niter_0;
	}
      else
	{
	  if (iv_niter_0)
	    ;
	  else if (TREE_CODE (niter) == INTEGER_CST)
	    {
	      iv_niter_0 = niter;
	      ex_niter_1 = fold_binary (PLUS_EXPR, TREE_TYPE (niter), niter,
					build_one_cst (TREE_TYPE (niter)));
	    }
	  else
	    iv_niter_0 = make_ssa_name (TREE_TYPE (niter));

	  iv_niter = iv_niter_0;
	  ex_niter = ex_niter_1;
	}

      tree copy_iv = split_ssa_at_edge (dom_exit_iv, inside, false);

      auto &scev_desc = get_scev_desc (copy_iv);
      tree init = PHI_ARG_DEF_FROM_EDGE (phi, entry);

      scev_desc.init = add_indirect_use (init, copy_iv);
      scev_desc.step = add_indirect_use (step, copy_iv);
      scev_desc.niter = add_indirect_use (iv_niter, copy_iv);
      scev_desc.always_updated = false;

      if (dominated_by_p (CDI_DOMINATORS, loop->latch, update_bb))
	{
	  scev_desc.always_updated = true;

	  if (ex_niter)
	    insert_exit_iv_definition (dom_exit_iv, init, step, ex_niter,
				       exit);
	}
    }

  if (TREE_CODE (niter) != INTEGER_CST)
    {
      gimple_seq stmts = NULL;
      gimple *stmt;

      if (iv_niter_1 && !iv_niter_0)
	iv_niter_0 = make_ssa_name (TREE_TYPE (niter));

      if (iv_niter_0)
	{
	  niter = force_gimple_operand (unshare_expr (niter), &stmts, true,
					NULL_TREE);
	  stmt = gimple_build_assign (iv_niter_0, niter);
	  gimple_seq_add_stmt_without_update (&stmts, stmt);
	}

      if (iv_niter_1)
	{
	  stmt = gimple_build_assign (iv_niter_1, MINUS_EXPR, iv_niter_0,
				      build_one_cst (TREE_TYPE (niter)));
	  gimple_seq_add_stmt_without_update (&stmts, stmt);
	}

      if (stmts)
	gsi_insert_seq_on_edge_immediate (inside, stmts);
    }
}

void
symbolic_vrp_prop::init_ranges ()
{
  unsigned i;
  tree name;

  sr_values = new symbolic_range[num_ssa_names];
  constraints.safe_grow_cleared (num_ssa_names, true);

  FOR_EACH_SSA_NAME (i, name, cfun)
    {
      if (SSA_NAME_IN_FREE_LIST (name) || SSA_NAME_IS_VIRTUAL_OPERAND (name))
	continue;

      symbolic_range &range = get_range (name);

      if (!SSA_NAME_IS_DEFAULT_DEF (name))
	{
	  gimple *stmt = SSA_NAME_DEF_STMT (name);

	  if (!gimple_bb (stmt))
	    continue;

	  if (stmt->uid && stmt_is_reachable_p (stmt))
	    {
	      add_stmt (stmt);

	      /* Do not initialize range to undefined for call and other
		 statement involving memory operation, since its defining
		 result would be of any value.  */
	      if (!gimple_vuse (stmt) && !is_gimple_call (stmt))
		{
		  range.set_undefined ();
		  continue;
	       }
	    }
	}

      if (POINTER_TYPE_P (TREE_TYPE (name)))
	range.init (name);
      else if (INTEGRAL_TYPE_P (TREE_TYPE (name)))
	get_range_query (cfun)->range_of_expr (range.value (), name);
    }
}

void
symbolic_vrp_prop::init (void)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\nFunction to propagate value ranges:\n");
      dump_function_to_file (current_function_decl, dump_file, dump_flags);
    }

  calculate_dominance_info (CDI_DOMINATORS);
  calculate_dominance_info (CDI_POST_DOMINATORS);

  bb_to_cfg_order = XNEWVEC (int, last_basic_block_for_fn (cfun) + 1);
  cfg_order_to_bb = XNEWVEC (int, n_basic_blocks_for_fn (cfun));

  int n = pre_and_rev_post_order_compute_fn (cfun, NULL,
					     cfg_order_to_bb, false);
  for (int i = 0; i < n; ++i)
    bb_to_cfg_order[cfg_order_to_bb[i]] = i;

  set_gimple_stmt_max_uid (cfun, 1);
  uid_to_stmt.safe_push (NULL);

  for (int i = 0; i < n; ++i)
    {
      basic_block bb = BASIC_BLOCK_FOR_FN (cfun, cfg_order_to_bb[i]);

      for (auto si = gsi_start_phis (bb); !gsi_end_p (si); gsi_next (&si))
	{
	  gimple *stmt = gsi_stmt (si);
	  tree result = PHI_RESULT (stmt);
	  tree type = TREE_TYPE (result);

	  gimple_set_uid (stmt, 0);

	  if (SSA_NAME_IS_VIRTUAL_OPERAND (result))
	    continue;

	  if (!INTEGRAL_TYPE_P (type) && !POINTER_TYPE_P (type))
	    continue;

	  gimple_set_uid (stmt, inc_gimple_stmt_max_uid (cfun));
	  uid_to_stmt.safe_push (stmt);
	}

      for (auto si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	{
	  gimple *stmt = gsi_stmt (si);
	  tree result = gimple_get_lhs (stmt);

	  gimple_set_uid (stmt, 0);

	  if (!result || TREE_CODE (result) != SSA_NAME)
	    continue;

	  tree type = TREE_TYPE (result);

	  if (!INTEGRAL_TYPE_P (type) && !POINTER_TYPE_P (type))
	    continue;

	  gimple_set_uid (stmt, inc_gimple_stmt_max_uid (cfun));
	  uid_to_stmt.safe_push (stmt);

	  if (!is_gimple_assign (stmt))
	    continue;

	  if (gimple_assign_rhs_code (stmt) == SSA_NAME)
	    {
	      tree orig_ssa = gimple_assign_rhs1 (stmt);
	      auto &orig_uses = get_indirect_uses (orig_ssa);

	      for (unsigned i = 0; i < orig_uses.length (); i++)
		{
		  tree use_ssa = orig_uses[i];
		  gimple *use_stmt = SSA_NAME_DEF_STMT (use_ssa);

		  if (!gimple_bb (use_stmt)
		      || !stmt_dominates_stmt_p (stmt, use_stmt))
		    continue;

		  ssa_predicate &use_predicate = get_predicate (use_ssa);

		  if (use_predicate.opnd == orig_ssa)
		    use_predicate.opnd = result;

		  add_indirect_use (result, use_ssa);
		  orig_uses.unordered_remove (i--);
		}
	    }

	  build_linear_mathfn_dependence (stmt);
	  make_mathfn_approximation (result);
	}
    }

  init_ranges ();
}

void
symbolic_vrp_prop::fini ()
{
  for (auto iter = affine_map.begin (); iter != affine_map.end (); ++iter)
    {
      delete (*iter).second;
      (*iter).second = NULL;
    }

  free_dominance_info (CDI_POST_DOMINATORS);
}

symbolic_vrp_prop::~symbolic_vrp_prop ()
{
  free (bb_to_cfg_order);
  free (cfg_order_to_bb);

  for (auto &use_set : indirect_use_sets)
    use_set.release ();
}

void
symbolic_vrp_prop::join_propagate ()
{
  unsigned max_uid = gimple_stmt_max_uid (cfun);
  auto_bitmap worklist;

  bitmap_copy (worklist, stmts_to_check);
  bitmap_set_bit (worklist, max_uid);

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "Propagate symbolic ranges in JOIN mode:\n");

  while (true)
    {
      unsigned stmt_uid = bitmap_first_set_bit (worklist);

      if (stmt_uid == max_uid)
	break;

      gimple *stmt = uid_to_stmt[stmt_uid];
      tree result = gimple_get_lhs (stmt);
      symbolic_range &range = get_range (result);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  dump_stmt (dump_file, "\n", stmt);
	  dump_range (dump_file, range);
	}

      bitmap_clear_bit (worklist, stmt_uid);

      /* This pointer acts as reference base for other pointers.  */
      if (range.symbol () == result)
	continue;

      symbolic_range new_range = compute_range_by_statement (result);

      if (new_range.undefined_p ())
	continue;

      if (!range.undefined_p () && new_range.same_symbol_p (range))
	{
	  if (!new_range.equal_p (range, true))
	    {
	      /* NOTE: zero-bits computation is not independent of range
		 information (in handling shift operations), normal dataflow
		 propagation would require lots of iterations in presence of
		 loop, which might causes very slow computation convergence.
		 So when range will be expanded, we conservatively set it to
		 be full one so as to accelerate convergence.  Another way is
		 to decouple computation of zero-bits from computation of
		 range.  */
	      new_range.set_full ();
	    }
	  else if (new_range.zero_bits () == range.zero_bits ())
	    continue;
	}

      range = new_range;

      if (dump_file && (dump_flags & TDF_DETAILS))
	dump_range (dump_file, "> Update by joining\n", range);

      gimple *use_stmt;
      imm_use_iterator use_iter;

      FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, result)
	{
	  if (!include_stmt_p (use_stmt))
	    continue;

	  bool added = bitmap_set_bit (worklist, use_stmt->uid);

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    dump_stmt (dump_file, added ? " + " : " * ", use_stmt);
	}
    }

  unsigned i;
  bitmap_iterator bi;

  EXECUTE_IF_SET_IN_BITMAP (stmts_to_check, 0, i, bi)
    {
      tree result = gimple_get_lhs (uid_to_stmt[i]);

      if (!POINTER_TYPE_P (TREE_TYPE (result)))
	{
	  symbolic_range range;

	  get_range_query (cfun)->range_of_expr (range.value (), result);
	  get_range (result).intersect (range);
	}
    }
}

void
symbolic_vrp_prop::meet_propagate_backward ()
{
  unsigned max_uid = gimple_stmt_max_uid (cfun);
  unsigned i;
  bitmap_iterator bi;
  auto_bitmap worklist;

  EXECUTE_IF_SET_IN_BITMAP (stmts_to_check, 0, i, bi)
    {
      gimple *stmt = uid_to_stmt[i];

      if (update_range_by_semantics (gimple_get_lhs (stmt)))
	{
	  gcc_checking_assert (max_uid > stmt->uid);
	  bitmap_set_bit (worklist, max_uid - stmt->uid);
	}
    }

  if (bitmap_empty_p (worklist))
    return;

  bitmap_set_bit (worklist, max_uid);

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file,
	     "\nPropagate symbolic ranges backward before MEET mode:\n");

  while (true)
    {
      unsigned stmt_uid = bitmap_first_set_bit (worklist);

      if (stmt_uid == max_uid)
	break;

      gimple *stmt = uid_to_stmt[max_uid - stmt_uid];
      auto_vec<tree> opnds;

      bitmap_clear_bit (worklist, stmt_uid);

      if (!update_operand_range_by_result (gimple_get_lhs (stmt), opnds))
	continue;

      for (auto opnd : opnds)
	{
	  gimple *opnd_stmt = SSA_NAME_DEF_STMT (opnd);

	  if (bitmap_bit_p (stmts_to_check, opnd_stmt->uid))
	    bitmap_set_bit (worklist, max_uid - opnd_stmt->uid);
	}
    }
}

void
symbolic_vrp_prop::mark_undefined_range (gimple *stmt, auto_bitmap &worklist)
{
  if (!stmt->uid)
    return;

  tree result = gimple_get_lhs (stmt);
  symbolic_range &range = get_range (result);

  if (range.undefined_p ())
    return;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      dump_stmt (dump_file, "\n", stmt);
      dump_range (dump_file, range);
    }

  range.set_undefined ();
  mark_undefined_constraint (result);

  if (dump_file && (dump_flags & TDF_DETAILS))
    dump_range (dump_file, "> Update to undefined\n", range);

  update_worklist (result, worklist);
  bitmap_clear_bit (worklist, stmt->uid);
}

void
symbolic_vrp_prop::mark_undefined_ranges_by_dominance (gimple *stmt,
						       auto_bitmap &worklist)
{
  basic_block bb = gimple_bb (stmt);
  auto bbs = get_all_dominated_blocks (CDI_POST_DOMINATORS, bb);

  bbs.safe_splice (get_all_dominated_blocks (CDI_DOMINATORS, bb));

  for (auto bb : bbs)
    {
      if (!(bb->flags & BB_REACHABLE))
	continue;

      bb->flags &= ~BB_REACHABLE;

      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "\n> Mark BB %d as unreachable\n", bb->index);

      for (auto si = gsi_start_phis (bb); !gsi_end_p (si); gsi_next (&si))
	mark_undefined_range (gsi_stmt (si), worklist);

      for (auto si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	mark_undefined_range (gsi_stmt (si), worklist);
    }
}

void
symbolic_vrp_prop::update_worklist (tree name, auto_bitmap &worklist)
{
  gimple *stmt = SSA_NAME_DEF_STMT (name);
  gimple *use_stmt;
  imm_use_iterator use_iter;

  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, name)
    {
      if (!include_stmt_p (use_stmt))
	continue;

      if (gimple_code (use_stmt) == GIMPLE_PHI)
	{
	  basic_block use_bb = gimple_bb (use_stmt);
	  class loop *use_loop = use_bb->loop_father;

	  if (use_loop->header == use_bb)
	    {
	      if (!stmt_is_inside_loop (use_loop, stmt))
		{
		  /* Once a new value range comes from loop entry, value
		     range propagation from latch is renewed.  */
		  latch_visited.remove (use_stmt);
		}
	      else if (latch_visited.add (use_stmt))
		{
		  /* Do not allow to continuously propagate value range
		     from loop latch more than once, which can avoid
		     long time range computation convergence.  */
		  if (dump_file && (dump_flags & TDF_DETAILS))
		    dump_stmt (dump_file, "Skip ", use_stmt);
		  continue;
		}
	    }
	}

      bool added = bitmap_set_bit (worklist, use_stmt->uid);

      if (dump_file && (dump_flags & TDF_DETAILS))
	dump_stmt (dump_file, added ? " + " : " * ", use_stmt);
    }

  for (auto use : get_indirect_uses (name))
    {
      gimple *use_stmt = SSA_NAME_DEF_STMT (use);
      bool added = bitmap_set_bit (worklist, use_stmt->uid);

      if (dump_file && (dump_flags & TDF_DETAILS))
	dump_stmt (dump_file, added ? " + " : " * ", use_stmt);
    }
}

void
symbolic_vrp_prop::meet_propagate ()
{
  unsigned max_uid = gimple_stmt_max_uid (cfun);
  auto_bitmap worklist;
  unsigned i;
  tree name;

  meet_propagate_backward ();

  bitmap_copy (worklist, stmts_to_check);
  bitmap_set_bit (worklist, max_uid);
  latch_visited.empty ();

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "\nPropagate symbolic ranges in MEET mode:\n");

  compare_operand::range_table = this;

  while (true)
    {
      unsigned stmt_uid = bitmap_first_set_bit (worklist);

      if (stmt_uid == max_uid)
	break;

      gimple *stmt = uid_to_stmt[stmt_uid];
      tree result = gimple_get_lhs (stmt);
      symbolic_range &range = get_range (result);
      bool update = false;

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  dump_stmt (dump_file, "\n", stmt);
	  dump_range (dump_file, range);
	}

      bitmap_clear_bit (worklist, stmt_uid);

      if (range.undefined_p ())
	continue;

      if (update_range_by_mathfn (result))
	{
	  update = true;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    dump_range (dump_file, "> Update by mathfn\n", range);
	}

      if (update_range_by_scev (result))
	{
	  update = true;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    dump_range (dump_file, "> Update by scev\n", range);
	}

      if (update_range_by_statement (result))
	{
	  update = true;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    dump_range (dump_file, "> Update by statement\n", range);
	}

      if (update_ssa_constraint (result))
	{
	  update = true;

	  if (update_range_by_constraint (result)
	      && dump_file && (dump_flags & TDF_DETAILS))
	    dump_range (dump_file, "> Update by compare constraint\n", range);
	}

      if (update_range_by_predicate (result))
	{
	  update = true;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    dump_range (dump_file, "> Update by predicate\n", range);
	}

      if (update)
	{
	  update_worklist (result, worklist);

	  if (range.undefined_p ())
	    {
	      mark_undefined_constraint (result);
	      mark_undefined_ranges_by_dominance (stmt, worklist);
	    }
	}
    }

  compare_operand::range_table = NULL;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      gimple *stmt;
      auto_bitmap name_list;
      bool dump_param = false;

      fprintf (dump_file, "\nSSA name ranges: \n");

      for (tree param = DECL_ARGUMENTS (cfun->decl); param;
	   param = DECL_CHAIN (param))
	{
	  tree type = TREE_TYPE (param);

	  if (!POINTER_TYPE_P (type) && !INTEGRAL_TYPE_P (type))
	    continue;

	  if (tree name = ssa_default_def (cfun, param))
	    {
	      symbolic_range &range = get_range (name);

	      print_generic_expr (dump_file, name, TDF_NONE);
	      fprintf (dump_file, ":  ");
	      range.dump (dump_file);
	      fprintf (dump_file, "\n");
	      dump_param = true;
	    }
	}

      FOR_EACH_VEC_ELT_FROM (uid_to_stmt, i, stmt, 1)
	bitmap_set_bit (name_list, SSA_NAME_VERSION (gimple_get_lhs (stmt)));

      if (dump_param && !bitmap_empty_p (name_list))
	fprintf (dump_file, "-\n");

      FOR_EACH_SSA_NAME (i, name, cfun)
	{
	  if (!bitmap_bit_p (name_list, SSA_NAME_VERSION (name)))
	    continue;

	  symbolic_range &range = get_range (name);

	  print_generic_expr (dump_file, name, TDF_NONE);
	  fprintf (dump_file, ":  ");

	  if (range.undefined_p ())
	    {
	      if (POINTER_TYPE_P (TREE_TYPE (name)))
		fprintf (dump_file, "*");
	    }
	  range.dump (dump_file);
	  fprintf (dump_file, "\n");
	}

      fprintf (dump_file, "\nSSA name compare constraints: \n");

      FOR_EACH_SSA_NAME (i, name, cfun)
	{
	  if (!bitmap_bit_p (name_list, SSA_NAME_VERSION (name)))
	    continue;

	  ssa_constraint *constraint = get_constraint (name);

	  if (!constraint || constraint->varying_p ())
	    continue;

	  print_generic_expr (dump_file, name, TDF_NONE);
	  fprintf (dump_file, ":  ");
	  print_generic_expr (dump_file, TREE_TYPE (name));
	  fprintf (dump_file, "  ");
	  constraint->dump (dump_file);
	  fprintf (dump_file, "\n");
	}

      fprintf (dump_file, "\n");
    }
}

static void
split_array_address (tree addr, tree &base, tree &index, tree &scale)
{
  base = addr = skip_ssa_copy (addr, true);
  index = NULL_TREE;
  scale = NULL_TREE;

  if (TREE_CODE (addr) != SSA_NAME)
    return;

  gimple *stmt = SSA_NAME_DEF_STMT (addr);

  if (!is_gimple_assign (stmt))
    return;

  enum tree_code code = gimple_assign_rhs_code (stmt);
  tree rhs1 = skip_ssa_copy (gimple_assign_rhs1 (stmt));

  if (code == POINTER_PLUS_EXPR)
    {
      tree rhs2 = skip_ssa_copy (gimple_assign_rhs2 (stmt));

      if (TREE_CODE (rhs2) != SSA_NAME)
	return;

      gimple *off_stmt = SSA_NAME_DEF_STMT (rhs2);

      if (!is_gimple_assign (off_stmt))
	return;

      if (gimple_assign_rhs_code (off_stmt) == MULT_EXPR)
	{
	  index = skip_ssa_copy (gimple_assign_rhs1 (off_stmt));
	  scale = skip_ssa_copy (gimple_assign_rhs2 (off_stmt));

	  if (TREE_CODE (index) == INTEGER_CST)
	    std::swap (index, scale);
	  else if (TREE_CODE (scale) != INTEGER_CST)
	    return;
	}
      else
	{
	  index = skip_ssa_copy (rhs2);
	  scale = build_one_cst (sizetype);
	}

      base = rhs1;

      if (TREE_CODE (index) != SSA_NAME)
	return;

      gimple *cvt_stmt = SSA_NAME_DEF_STMT (index);

      if (is_gimple_assign (cvt_stmt)
	  && CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (cvt_stmt)))
	{
	  tree real_index = gimple_assign_rhs1 (cvt_stmt);

	  if (!INTEGRAL_TYPE_P (TREE_TYPE (real_index)))
	    return;

	  if (TYPE_PRECISION (TREE_TYPE (index))
			< TYPE_PRECISION (TREE_TYPE (real_index)))
	    return;

	  index = real_index;
	}
    }
  else if (TREE_CODE (rhs1) == ADDR_EXPR)
    {
      tree memref = TREE_OPERAND (rhs1, 0);

      if (TREE_CODE (memref) != ARRAY_REF)
	return;

      tree bound = array_ref_low_bound (memref);

      if (!integer_zerop (bound))
	return;

      HOST_WIDE_INT offset;

      base = get_mem_access_simple_base (TREE_OPERAND (memref, 0), &offset);

      if (base == error_mark_node || offset)
	{
	  base = addr;
	  return;
	}

      if (DECL_P (base))
	base = build1 (ADDR_EXPR, build_pointer_type (TREE_TYPE (base)),
		       base);

      index = skip_ssa_copy (TREE_OPERAND (memref, 1));
      scale = array_ref_element_size (memref);
    }
}

class array_manip_callee_info
{
public:
  int array_param_idx;
  tree array_param;
  tree array_basis;

  int count_param_idx;
  /* If non-NULL, it indicates array manipulation does not exceed a count
     bound specified by  this field.  */
  tree count_param;
  tree count_basis;
  tree count_limit;

  tree elem_size;
  int elem_size_shift;

  addr_analyzer analyzer;
  cgraph_node *node;
  cgraph_node *dse_node;
  bool need_clone;

  class loop *main_loop;

  auto_vec<gimple *> array_loads;
  auto_vec<gimple *> array_stores;

  basic_block return_bb;
  unsigned array_basis_phi_idx;

  hash_map<tree_ssa_name_hash, std::pair<tree, HOST_WIDE_INT>> bound_addr_map;
  hash_map<gimple *, tree> other_addrs_to_bound;

  int byref_elem;
  memref_areas byref_load_areas;

  symbolic_vrp_prop vrp_prop;

  array_manip_callee_info (cgraph_node *node)
    : array_param_idx (-1), array_param (NULL_TREE), array_basis (NULL_TREE)
    , count_param_idx (-1), count_param (NULL_TREE), count_basis (NULL_TREE)
    , count_limit (NULL_TREE), elem_size (NULL_TREE), elem_size_shift (INT_MAX)
    , node (node), dse_node (NULL)
    , need_clone (dse_always_clone_callee || !node->can_change_signature)
    , main_loop (NULL), return_bb (NULL), array_basis_phi_idx (0)
    , byref_elem (-1)
  { }

  void reset_count_bound ()
  {
    if (!count_param)
      return;

    count_param_idx = -2;
    count_param = NULL_TREE;
    count_basis = NULL_TREE;

    if (dump_file && (dump_flags & TDF_DETAILS))
     fprintf (dump_file, "Reset array count\n");
  }

  bool determine_sole_array_updated ();
  bool get_possible_callers (auto_vec<cgraph_edge *> &);
  bool mark_array_access_region ();
  bool check_return_value ();
  bool check_call (gimple *);
  bool check_store_values_uniqueness ();
  bool check_store_stmts ();
  bool check_load_as_condition_seed (gimple *);
  void check_load_stmts ();
  bool find_array_and_count_basis ();
  bool address_in_bound_p (tree, HOST_WIDE_INT, HOST_WIDE_INT* = NULL);
  bool check_address_bound (tree, HOST_WIDE_INT = 0);
  void profile_address_bound (tree, auto_vec<tree_pair> &, basic_block = NULL);
  void profile_address_plus_count (tree, tree, gimple *,
				   auto_vec<tree_pair> &);
  void profile_array_access_bound ();
  bool check_array_forward_updating ();
  bool find_qualified_array (auto_vec<cgraph_edge *> &);

  void annotate_label_and_clone (class loop *&, basic_block &);
  void make_node_with_dse_check ();
  gcall *insert_bound_argument (cgraph_edge *, tree);
};

bool
array_manip_callee_info::determine_sole_array_updated ()
{
  for (auto cs = node->indirect_calls; cs; cs = cs->next_callee)
    {
      if (!(gimple_call_flags (cs->call_stmt) & (ECF_CONST | ECF_PURE)))
	return false;
    }

  for (auto cs = node->callees; cs; cs = cs->next_callee)
    {
      gimple *call_stmt = cs->call_stmt;

      if (gimple_call_flags (call_stmt) & (ECF_CONST | ECF_PURE))
	continue;

      /* Now only self-recursive call is handled.
	 TODO: support call that has similar characteristics.  */
      if (node != cs->callee)
	return false;
    }

  tree unique_base = NULL_TREE;
  basic_block bb;

  FOR_EACH_BB_FN (bb, cfun)
    {
      for (auto gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	{
	  gimple *stmt = gsi_stmt (gsi);

	  if (gimple_clobber_p (stmt))
	    continue;

	  if (gimple_has_volatile_ops (stmt))
	    return false;

	  if (!gimple_vuse (stmt))
	    continue;

	  if (gimple_code (stmt) == GIMPLE_ASM)
	    return false;

	  tree lhs = gimple_get_lhs (stmt);

	  if (!lhs || TREE_CODE (lhs) == SSA_NAME)
	    continue;

	  /* Do not handle WITH_SIZE_EXPR or other inner reference expr
	     involving no memory access.  */
	  if (!memref_expr_p (lhs))
	    return false;

	  auto base_set = analyzer.get_address_base (lhs);

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      print_gimple_stmt (dump_file, stmt, 0, dump_flags);
	      fprintf (dump_file, "  Address base: ");
	      dump_address (dump_file, base_set);
	      fprintf (dump_file, "\n");
	    }

	  if (base_set.length () > 1)
	    return false;

	  if (!unique_base)
	    unique_base = base_set[0];
	  else if (!operand_equal_p (unique_base, base_set[0]))
	    return false;
	}
    }

  if (!unique_base)
    return false;

  /* Currently, we only consider memory base that is from function
     parameter.  */
  if ((array_param_idx = function_param_index (node->decl, unique_base)) < 0)
    return false;

  array_param = unique_base;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> Found sole stored array at ");
      dump_address (dump_file, array_param);
      fprintf (dump_file, "\n");
    }

  return true;
}

static tree
extract_local_array_argument (cgraph_edge *cs, int param_idx,
			      addr_base_map &base_map, tree &size)
{
  gcall *call_stmt = cs->call_stmt;
  cgraph_node *callee = cs->callee;

  if (gimple_call_num_args (call_stmt) < function_num_params (callee->decl))
    return NULL_TREE;

  cfun_context ctx (cs->caller);
  tree array_arg = gimple_call_arg (call_stmt, param_idx);

  if (!POINTER_TYPE_P (TREE_TYPE (array_arg)) || !gimple_rvalue_p (array_arg))
    return NULL_TREE;

  auto base_set = base_map.get_address_base (array_arg);

  if (base_set.length () != 1 || !local_memory_in_function_p (base_set[0]))
    return NULL_TREE;

  tree array = base_set[0];

  if (TREE_CODE (array) == SSA_NAME)
    size = memory_alloc_size (SSA_NAME_DEF_STMT (array));
  else if (TREE_CODE (TREE_TYPE (array)) == ARRAY_TYPE)
    size = TYPE_SIZE_UNIT (TREE_TYPE (array));
  else
    return NULL_TREE;

  unsigned prec = TYPE_PRECISION (sizetype);

  /* Array size is too large to be converted to signed integer, also skipped
     if it is zero.  */
  if (!size || wi::les_p (wi::to_wide (size), wi::zero (prec)))
    return NULL_TREE;

  return array;
}

bool
array_manip_callee_info::get_possible_callers (
					auto_vec<cgraph_edge *> &manip_edges)
{
  tree elem_type = NULL_TREE;
  tree size = NULL_TREE;
  bool any_caller = false;

  for (auto cs = node->callers; cs; cs = cs->next_caller)
    {
      /* Reset aux field to indicate the edge is not considered initially.  */
      cs->aux = NULL;

      if (cs->caller == node)
	continue;

      tree new_size;
      tree array = extract_local_array_argument (cs, array_param_idx,
						 analyzer, new_size);
      if (!array)
	{
	  need_clone = true;
	  continue;
	}

      tree new_elem_type = TREE_TYPE (TREE_TYPE (array));

      if (!elem_type)
	{
	  elem_type = new_elem_type;
	  size = new_size;
	}
      else if (!types_compatible_p (elem_type, new_elem_type))
	return false;
      else if (wi::ltu_p (wi::to_wide (size), wi::to_wide (new_size)))
	size = new_size;

      manip_edges.safe_push (cs);
      any_caller = true;
    }

  if (!any_caller)
    return false;

  elem_size = TYPE_SIZE_UNIT (elem_type);

  if (!elem_size || TREE_CODE (elem_size) != INTEGER_CST)
    return false;

  /* TODO: now we only allow element size with power of 2.  */
  if (wi::popcount (wi::to_wide (elem_size)) == 1)
    elem_size_shift = wi::ctz (wi::to_wide (elem_size));

  count_limit = size_binop (CEIL_DIV_EXPR, size, elem_size);
  return true;
}

/* For value sources that determine the result of array updating, we call them
   array updating condition seeds, which might including incoming arguments of
   the function, the array content or any value derived from array content.  */

bool
array_manip_callee_info::check_load_as_condition_seed (gimple *load)
{
  auto_vec<tree> worklist;

  worklist.safe_push (gimple_assign_lhs (load));

  do
    {
      tree val = worklist.pop ();
      imm_use_iterator use_iter;
      gimple *use_stmt;

      FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, val)
	{
	  if (is_gimple_debug (use_stmt) || !stmt_is_reachable_p (use_stmt))
	    continue;

	  /* A pointer value loaded from array element might be converted to
	     a same-sized integer, which is stored to memory.  For example,

		ptr = elem[i];
		ptr_as_int = (intptr_t) ptr;
		elem[j] = ptr_as_int;

	     And this kind of use on pointer value does not means the value
	     acts as condition seed to impact array updating.  */
	  if (tree copy = get_ssa_copy (use_stmt, true, MATCH_SIZE))
	    {
	      gcc_checking_assert (copy == val);
	      worklist.safe_push (gimple_get_lhs (use_stmt));
	      continue;
	    }

	  /* Fail the check if memory access occurs on non-assignment
	     statement.  */
	  if (!is_gimple_assign (use_stmt) || !gimple_vuse (use_stmt))
	    return false;

	  if (gimple_vdef (use_stmt))
	    {
	      /* Integer ssa may occur in a memref as an array index.  */
	      if (ssa_in_expr_p (val, gimple_assign_lhs (use_stmt)))
		return false;

	      /* Value of array element is stored to other element is seen
		 as updating operation on the array, not a condition seed.  */
	      gcc_checking_assert (gimple_assign_rhs1 (use_stmt) == val);
	      continue;
	    }

	  /* The load whose address is value of array element is a condition
	     seed.  For example,

		if (op (elem[i]->val, elem[j]->val))
		  elem[k] = ...

	     In the above, array updating is determined by the "val" field of
	     object pointed by array element.  */

	  if (!byref_load_areas.add (gimple_assign_rhs1 (use_stmt), val))
	    return false;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "  Condition seed: ");
	      print_gimple_stmt (dump_file, use_stmt, 0);
	    }
	}
    } while (!worklist.is_empty ());

  return true;
}

void
array_manip_callee_info::check_load_stmts ()
{
  gimple *stmt;
  unsigned i;

  /* Check whether any load is aliased to the array being processed.  If aliased,
     it implies that value content of the array is used to decide how to modify
     the array.  Additionally, it also means that the element referenced may be
     outside of current array part.

     As to the array argument in caller side, we impose a requirement on it.
     The address of array should not escape, and never be kept into any memory.
     Then, the code below is not allowed.

	T array[size];
	  ...
	*memory = &array[offset];

     Once this is satisfied, we will known any address loaded from memory
     never point to memory region of the array, by which alias analysis could
     simplified.  */

  FOR_EACH_VEC_ELT (array_loads, i, stmt)
    {
      if (!stmt_is_reachable_p (stmt))
	{
	  array_loads.unordered_remove (i--);
	  continue;
	}

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Check array load: ");
	  print_gimple_stmt (dump_file, stmt, 0, TDF_NONE);
	}

      HOST_WIDE_INT offset, size;
      tree rhs = gimple_assign_rhs1 (stmt);
      tree base = get_mem_access_simple_base (rhs, &offset, &size);
      symbolic_range &range = vrp_prop.get_range (base);

      gcc_checking_assert (range.symbol ());

      if (range.symbol () != array_basis)
	reset_count_bound ();

      if (range.kind () != VR_RANGE || wi::neg_p (wi::to_wide (range.min ())))
	{
	  reset_count_bound ();
	  byref_elem = 0;
	  break;
	}

      if (byref_elem && !check_load_as_condition_seed (stmt))
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    fprintf (dump_file, "  Disable byref-element access for array\n");
	  byref_elem = 0;
	}

      if (count_param)
	{
	  offset += size + BITS_PER_UNIT - 1;
	  check_address_bound (base, offset / BITS_PER_UNIT);
	}
    }

  if (!byref_elem)
    byref_load_areas.release ();
  else if (!byref_load_areas.is_empty ())
    byref_elem = 1;
}

bool
array_manip_callee_info::check_call (gimple *call_stmt)
{
  tree fndecl = gimple_call_fndecl (call_stmt);

  if (fndecl && DECL_STRUCT_FUNCTION (fndecl) == cfun)
    {
      tree param = DECL_ARGUMENTS (cfun->decl);

      gcc_checking_assert (gimple_vdef (call_stmt));

      for (int i = 0; i < (int) gimple_call_num_args (call_stmt); i++,
	   param = DECL_CHAIN (param))
	{
	  if (!param)
	    return false;

	  tree arg = gimple_call_arg (call_stmt, i);

	  if (!types_compatible_p (TREE_TYPE (arg), TREE_TYPE (param)))
	    return false;

	  if (TREE_CODE (arg) != SSA_NAME)
	    {
	      if (i == array_param_idx)
		return false;

	      if (i == count_param_idx)
		{
		  reset_count_bound ();
		  continue;
		}
	    }

	  if (!as_pointer_type_p (TREE_TYPE (arg)))
	    continue;

	  auto base_set = analyzer.get_address_base (arg);

	  if (i == array_param_idx)
	    {
	      if (base_set.length () != 1 || array_param != base_set[0])
		return false;
	    }
	  else if (base_set.contains (array_param))
	    {
	      /* Check that the array parameter occurs only once in argument
		 list of recursive call.  This ensure that except known array
		 parameter, other parameter in the callee should not point to
		 the array.  */
	      reset_count_bound ();
	      byref_elem = 0;
	    }
	}

      /* TODO: function call with static chain is really seldom,  so fail the
	 check if this happens, which could simplify some check following.  */
      if (gimple_call_chain (call_stmt) || param)
	return false;
    }
  else
    {
      gcc_checking_assert (!gimple_vdef (call_stmt));

      for (unsigned i = 2; i < gimple_num_ops (call_stmt); i++)
	{
	  tree arg = gimple_op (call_stmt, i);

	  if (arg && TREE_CODE (arg) == SSA_NAME
	      && as_pointer_type_p (TREE_TYPE (arg))
	      && analyzer.get_address_base (arg).contains (array_param))
	    {
	      reset_count_bound ();
	      byref_elem = 0;
	    }
	}
    }

  auto_vec<tree> memrefs;

  /* It is possible that memory access on the address is part of function
     call either as an argument or return value.  For simplicity, we just
     fail the check since the case should be really seldom.  */
  walk_stmt_load_store_ops (call_stmt, &memrefs, collect_memref, NULL);

  for (auto memref : memrefs)
    {
      auto base_set = analyzer.get_address_base (memref);

      if (base_set.contains (array_param))
	return false;
    }

  return true;
}

bool
array_manip_callee_info::mark_array_access_region ()
{
  basic_block bb;

  if (!find_array_and_count_basis ())
    return false;

  mark_reachable_blocks (main_loop->header);

  analyzer.process (/* only_reachable= */ true);

  FOR_EACH_BB_FN (bb, cfun)
    {
      for (auto si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	{
	  gimple *stmt = gsi_stmt (si);

	  if (!gimple_vuse (stmt))
	    continue;

	  if (auto ret = dyn_cast<greturn *> (stmt))
	    {
	      tree val = gimple_return_retval (ret);

	      if (val && !gimple_rvalue_p (val))
		return false;
	    }
	  else if (bb->flags & BB_REACHABLE)
	    {
	      /* Simply skip loop that contains irreducible loop.  */
	      if (bb->flags & BB_IRREDUCIBLE_LOOP)
		return false;

	      if (is_gimple_call (stmt) && !check_call (stmt))
		return false;

	      tree memref = NULL_TREE;

	      if (gimple_vdef (stmt))
		{
		  array_stores.safe_push (stmt);

		  if (!(memref = gimple_get_lhs (stmt)))
		    continue;

		  /* TODO: support store to aggregate.  */
		  if (!is_gimple_reg_type (TREE_TYPE (memref)))
		    return false;

		  /* TODO: support assignment whose lhs and rhs are both
		     memory reference, in all probability, it is an aggregate
		     copy statement.  */
		  if (is_gimple_assign (stmt)
		      && !gimple_rvalue_p (gimple_assign_rhs1 (stmt)))
		    return false;
		}
	      else if (gimple_assign_load_p (stmt))
		{
		  auto base_set = analyzer.get_address_base (
					memref = gimple_assign_rhs1 (stmt));

		  if (!base_set.contains (array_param))
		    continue;

		  if (base_set.length () != 1)
		    reset_count_bound ();

		  array_loads.safe_push (stmt);
		}

	      if (memref)
		{
		  HOST_WIDE_INT offset, size;
		  tree base = get_mem_access_simple_base (memref, &offset,
							  &size);

		  /* For statement that has complicated memory access effects,
		     we conservatively assume it may access whole region of
		     the array.  */
		  if (base == error_mark_node || offset + size < size)
		    return false;
		}
	    }
	  else
	    {
	      /* Now we only handle the case in which all memory accesses to
		 array are completely inside one loop, with which we could
		 simplify the analysis.  As a TODO to support generic case.  */
	      return false;
	    }
	}
    }

  /* The array address should only be used in memory reference and
     recursive call.  */
  if (analyzer.exclude_base_p (array_param, AU_COND_EX | AU_SAVED))
    return false;

  return true;
}

static bool
remove_function (cgraph_node *node)
{
  if (!node->can_remove_if_no_direct_calls_and_refs_p ()
      || !node->ref_list.referring.is_empty ())
    return false;

  for (auto cs = node->callers; cs; cs = cs->next_caller)
    {
      if (cs->caller != node)
	return false;
    }

  function *fun = DECL_STRUCT_FUNCTION (node->decl);

  free_dominance_info (fun, CDI_DOMINATORS);
  free_dominance_info (fun, CDI_POST_DOMINATORS);
  node->remove ();

  return true;
}

static void
cleanup_function (cgraph_node *node, bool simple = false)
{
  cfun_context ctx (node);
  push_dump_file save (NULL, TDF_NONE);

  if (!simple)
    {
      auto_bitmap unused_names;
      unsigned i;
      tree name;
      basic_block bb;

      FOR_EACH_SSA_NAME (i, name, cfun)
	{
	  if (SSA_NAME_IN_FREE_LIST (name)
	      || SSA_NAME_IS_VIRTUAL_OPERAND (name))
	    continue;

	  gimple *stmt = SSA_NAME_DEF_STMT (name);

	  if (gimple_bb (stmt) && has_zero_uses (name))
	    bitmap_set_bit (unused_names, SSA_NAME_VERSION (name));
	}

      simple_dce_from_worklist (unused_names);

      /* Purge generated copies.  */
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (auto si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);

	      if (!gimple_assign_single_p (stmt))
		continue;

	      tree lhs = gimple_assign_lhs (stmt);
	      tree rhs = gimple_assign_rhs1 (stmt);

	      if (TREE_CODE (lhs) != SSA_NAME
		  || TREE_TYPE (lhs) != TREE_TYPE (rhs))
		continue;

	      if (TREE_CODE (rhs) == SSA_NAME && may_propagate_copy (lhs, rhs))
		replace_ssa (lhs, rhs);
	      else if (is_gimple_invariant_address (rhs)
		       && has_single_use (lhs))
		replace_ssa (lhs, rhs);
	    }
	}
    }

  free_dominance_info (CDI_DOMINATORS);
  loop_optimizer_finalize ();
}

bool
array_manip_callee_info::check_return_value ()
{
  edge_iterator ei;
  edge return_edge;
  tree return_val = NULL_TREE;

  FOR_EACH_EDGE (return_edge, ei, EXIT_BLOCK_PTR_FOR_FN (cfun)->preds)
    {
      if (!(return_edge->src->flags & BB_REACHABLE))
	continue;

      auto ret = safe_dyn_cast<greturn *> (last_stmt (return_edge->src));

      if (!ret)
	continue;

      tree val = gimple_return_retval (ret);

      if (!val)
	continue;

      if (is_gimple_ip_invariant (val))
	;
      else if (TREE_CODE (val) != SSA_NAME)
	return false;
     else if (!SSA_NAME_IS_DEFAULT_DEF (val))
	{
	  gimple *stmt = SSA_NAME_DEF_STMT (val);
	  edge entry = loop_preheader_edge (main_loop);

	  /* Return value should be determined before entering the loop.  */
	  if (!dominated_by_p (CDI_DOMINATORS, entry->src, gimple_bb (stmt)))
	    return false;
	}
      else if (function_param_index (cfun->decl, val) < 0)
	return false;

      /* Return value in function should be identical.  */
      if (return_val && !operand_equal_p (return_val, val))
	return false;

      /* If function passes some pointer outside, it may cause escape of array
	 element.  */
      if (POINTER_TYPE_P (TREE_TYPE (val)))
	byref_elem = 0;

      return_bb = return_edge->src;
    }

  return true;
}

/* For indirect ref array, whose element is data pointer, instead of data
   content, we need to ensure that any two elements never points to same data,
   if array-manip callee function would depend on previous result of itself.
   Otherwise, changing data pointed by an element also implies side effect
   of other aliased elements, we could not simply eliminate operations on any
   element.  This constraint is enforced in caller side by applying
   corresponding check.  And for callee side, we should also check that any
   updating on some element will not break the condition.  */

bool
array_manip_callee_info::check_store_values_uniqueness ()
{
  hash_set<tree_ssa_name_hash> load_values;
  hash_map<tree_ssa_name_hash, gimple *> store_map;
  auto_vec<gimple *> stores (array_stores.length ());

  for (auto stmt : array_loads)
    load_values.add (gimple_assign_lhs (stmt));

  for (auto stmt : array_stores)
    {
      if (is_gimple_call (stmt))
	continue;

      tree value = skip_ssa_copy (gimple_assign_rhs1 (stmt), true, MATCH_SIZE);

      stores.quick_push (stmt);

      if (integer_zerop (value))
	continue;

      if (TREE_CODE (value) != SSA_NAME)
	return false;

      /* If an element is updated to a newly-allocated object, this is safe.
	 Or the value to update the element comes from other element, while
	 the latter element should also be redefined with another new
	 value.  */
      if (!memory_alloc_stmt_p (SSA_NAME_DEF_STMT (value))
	  && !load_values.contains (value))
	return false;

      /* More than one elements are updated with same value, which breaks the
	 constraint.  */
      if (store_map.put (value, stmt))
	return false;

      /* A statement of updating one array element with a new value, might
	 correspond to changes on more than elements, if the statement lies in
	 a loop.

	   val = load ...

	   loop {
	     store = val
	   }

	 We must ensure that store is executed at most once after the load.  */
      if (!stmt_linear_dominates_stmt_p (SSA_NAME_DEF_STMT (value), stmt))
	return false;
    }

  for (auto iter = store_map.begin (); iter != store_map.end (); ++iter)
    {
      gimple *load = SSA_NAME_DEF_STMT ((*iter).first);

      if (is_gimple_call (load))
	continue;

      bool found = false;
      basic_block store_bb = gimple_bb ((*iter).second);
      HOST_WIDE_INT ld_offset, ld_size;
      tree ld_base = get_mem_access_simple_base (gimple_assign_rhs1 (load),
						 &ld_offset, &ld_size);

      for (auto &stmt : stores)
	{
	  HOST_WIDE_INT st_offset, st_size;
	  tree st_base = get_mem_access_simple_base (gimple_assign_lhs (stmt),
						     &st_offset, &st_size);

	  if (!copy_of_p (st_base, ld_base) || ld_offset != st_offset
	      || ld_size != st_size)
	    continue;

	  if (!stmt_linear_dominates_stmt_p (load, stmt))
	    continue;

	  basic_block bb = gimple_bb (stmt);

	  /* There must be a redefinition of the element whose original
	     value is transferred to another element.  */
	  if (store_bb == bb
	      || dominated_by_p (CDI_DOMINATORS, store_bb, bb)
	      || dominated_by_p (CDI_POST_DOMINATORS, store_bb, bb))
	    {
	      stmt = stores.last ();
	      stores.pop ();
	      found = true;
	      break;
	    }
	}

      if (!found)
	return false;
    }

  return true;
}

bool
array_manip_callee_info::check_store_stmts ()
{
  unsigned i;
  gimple *stmt;

  FOR_EACH_VEC_ELT (array_stores, i, stmt)
    {
      if (!stmt_is_reachable_p (stmt))
	{
	  array_stores.unordered_remove (i--);
	  continue;
	}

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Check array store: ");
	  print_gimple_stmt (dump_file, stmt, 0, TDF_NONE);
	}

      /* Self-recursive call */
      if (is_gimple_call (stmt))
	{
	  tree param = DECL_ARGUMENTS (cfun->decl);
	  int param_idx = 0;

	  for (; param; param = DECL_CHAIN (param), param_idx++)
	    {
	      tree arg = gimple_call_arg (stmt, param_idx);
	      tree arg_type = TREE_TYPE (param);
	      symbolic_range range;

	      if (!is_gimple_reg_type (arg_type))
		continue;

	      if (memref_expr_p (arg))
		range.set_varying (arg_type);
	      else
		range = vrp_prop.get_range_from_tree (arg);

	      if (INTEGRAL_TYPE_P (arg_type))
		{
		  tree param_ssa = ssa_default_def (cfun, param);

		  if (!param_ssa)
		    return false;

		  symbolic_range &param_range = vrp_prop.get_range (param_ssa);

		  range.union_ (param_range);

		  if (!range.equal_p (param_range))
		    return false;
		}
	      else if (param_idx == array_param_idx)
		{
		  if (range.kind () != VR_RANGE
		      || wi::neg_p (wi::to_wide (range.min ())))
		    return false;

		  gcc_checking_assert (range.symbol ());

		  if (!operand_equal_p (array_basis, range.symbol ()))
		    return false;

		  if (count_param)
		    check_address_bound (*other_addrs_to_bound.get (stmt));
		}
	    }
	}

      tree lhs = gimple_get_lhs (stmt);

      if (lhs && TREE_CODE (lhs) != SSA_NAME)
	{
	  HOST_WIDE_INT offset, size;
	  tree base = get_mem_access_simple_base (lhs, &offset, &size);
	  symbolic_range &range = vrp_prop.get_range (base);

	  if (range.kind () != VR_RANGE
	      || wi::neg_p (wi::to_wide (range.min ())))
	    return false;

	  gcc_checking_assert (range.symbol ());

	  /* All memory writes should come from same array basis address in
	     the loop.  */
	  if (!operand_equal_p (array_basis, range.symbol ()))
	    return false;

	  /* For indirect ref array, do not modify its content using return
	     value of its recursive call.  */
	  if (is_gimple_call (stmt))
	    byref_elem = 0;

	  if (count_param)
	    {
	      offset += size + BITS_PER_UNIT - 1;
	      check_address_bound (base, offset / BITS_PER_UNIT);
	    }
	}
    }

  if (byref_elem && !check_store_values_uniqueness ())
    byref_elem = 0;

  return true;
}

bool
array_manip_callee_info::address_in_bound_p (tree addr, HOST_WIDE_INT offset,
					     HOST_WIDE_INT *max_offset)
{
  auto &bound_item = bound_addr_map.get_or_insert (addr);

  gcc_checking_assert (offset >= 0);

  if (max_offset)
    *max_offset = bound_item.second;

  if (bound_item.second >= offset)
    return true;

  tree offset_expr = build_int_cst (ptrdiff_type_node, offset);
  symbolic_range offset_range = vrp_prop.get_range_from_tree (offset_expr);
  symbolic_range &bound_range = vrp_prop.get_range (bound_item.first);
  symbolic_range range;

  symbolic_range_fold_binary_expr (&range, POINTER_PLUS_EXPR, TREE_TYPE (addr),
				   &bound_range, &offset_range);

  if (range.kind () != VR_RANGE)
    return false;

  const wide_int max_int = wi::to_wide (range.max ());

  if (wi::neg_p (max_int))
    {
      gcc_assert (bound_range.kind () == VR_RANGE);

      if (!tree_fits_shwi_p (bound_range.max ())
	  || (offset = -tree_to_shwi (bound_range.max ())) < 0)
	offset = HOST_WIDE_INT_MAX;
    }
  else if (max_int != 0)
    return false;

  bound_item.second = offset;

  if (max_offset)
    *max_offset = offset;

  return true;
}

bool
array_manip_callee_info::check_address_bound (tree addr, HOST_WIDE_INT offset)
{
  if (address_in_bound_p (addr, offset))
    return true;

  auto_bitmap visited;
  auto_vec<tree> worklist;
  HOST_WIDE_INT max_offset = -1;

  bitmap_set_bit (visited, SSA_NAME_VERSION (addr));
  worklist.safe_push (addr);

  do
    {
      tree addr = worklist.pop ();
      tree copy = skip_ssa_copy (addr, true);

      if (copy != addr
	  && !bitmap_set_bit (visited, SSA_NAME_VERSION (copy)))
	continue;

      gimple *addr_stmt = SSA_NAME_DEF_STMT (copy);

      if (gimple_code (addr_stmt) != GIMPLE_PHI
	  || gimple_bb (addr_stmt) == main_loop->header)
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      tree bound_addr = bound_addr_map.get (addr)->first;

	      fprintf (dump_file, "Address ");
	      print_generic_expr (dump_file, addr, TDF_NONE);
	      fprintf (dump_file, " (");
	      print_generic_expr (dump_file, bound_addr, TDF_NONE);
	      fprintf (dump_file, ") is out of bound \n");
	    }

	  reset_count_bound ();
	  return false;
	}

      for (unsigned i = 0; i < gimple_phi_num_args (addr_stmt); i++)
	{
	  tree arg = gimple_phi_arg_def (addr_stmt, i);
	  HOST_WIDE_INT new_max_offset;

	  if (integer_zerop (arg)
	      || !bitmap_set_bit (visited, SSA_NAME_VERSION (arg)))
	    continue;

	  if (!address_in_bound_p (arg, offset, &new_max_offset))
	    worklist.safe_push (arg);
	  else if (max_offset < 0 || max_offset > new_max_offset)
	    max_offset = new_max_offset;
	}
    } while (!worklist.is_empty ());

  gcc_assert (max_offset >= 0);

  bound_addr_map.get (addr)->second = max_offset;
  return true;
}

static tree
insert_to_bb_end (tree expr, basic_block bb, const char *name = NULL)
{
  if (TREE_CODE (expr) == SSA_NAME)
    return expr;

  gimple_stmt_iterator gsi = gsi_last_bb (bb);
  gimple *last = last_stmt (bb);
  bool before = false;

  if (last && stmt_ends_bb_p (last))
    {
      gsi = gsi_for_stmt (last);
      before = true;
    }

  expr = force_gimple_operand_gsi (&gsi, expr, true, NULL, before,
				   GSI_NEW_STMT);
  if (name)
    SET_SSA_NAME_VAR_OR_IDENTIFIER (expr, get_identifier (name));

  return expr;
}

void
array_manip_callee_info::profile_address_bound (tree addr,
						auto_vec<tree_pair> &count_map,
						basic_block bb)
{
  gimple *addr_stmt = SSA_NAME_DEF_STMT (addr);
  tree minus_bound = NULL_TREE;

  if (!bb)
    bb = gimple_bb (addr_stmt);

  for (unsigned i = count_map.length (); i > 0; i--)
    {
      auto &count_item = count_map[i - 1];
      tree count = count_item.first;
      gimple *count_stmt = SSA_NAME_DEF_STMT (count);

      if (!dominated_by_p (CDI_DOMINATORS, bb, gimple_bb (count_stmt)))
	continue;

      if (!dominated_by_p (CDI_DOMINATORS, gimple_bb (addr_stmt),
			   gimple_bb (count_stmt)))
	{
	  gimple_stmt_iterator gsi = gsi_after_labels (gimple_bb (count_stmt));

	  addr = split_ssa_at_gsi (addr, &gsi, true, false);
	  addr_stmt = SSA_NAME_DEF_STMT (addr);
	}

      if (!(minus_bound = count_item.second))
	{
	  gimple_stmt_iterator gsi = gsi_for_stmt (count_stmt);
	  bool before = false;

	  if (gimple_code (count_stmt) == GIMPLE_PHI)
	    {
	      gsi = gsi_after_labels (gimple_bb (count_stmt));
	      before = true;
	    }

	  minus_bound = fold_convert (sizetype, count);
	  minus_bound = build2 (MULT_EXPR, sizetype, minus_bound, elem_size);
	  minus_bound = build1 (NEGATE_EXPR, sizetype, minus_bound);
	  minus_bound = force_gimple_operand_gsi (&gsi, minus_bound, true,
						  NULL, before, GSI_NEW_STMT);
	  count_item.second = minus_bound;
	}

      break;
    }

  bool existed;
  auto &bound_item = bound_addr_map.get_or_insert (addr, &existed);

  if (existed)
    return;

  gcc_checking_assert (minus_bound);

  tree expr = build2 (POINTER_PLUS_EXPR, ptr_type_node, addr,
		      minus_bound);

  bound_item.first = insert_to_bb_end (expr, gimple_bb (addr_stmt), "bound");
  bound_item.second = -1;

  if (tree copy = skip_ssa_copy (addr, true))
    addr_stmt = SSA_NAME_DEF_STMT (copy);

  if (auto phi = dyn_cast<gphi *> (addr_stmt))
    {
      if (gimple_bb (addr_stmt) == main_loop->header)
	return;

      for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
	{
	  tree arg = gimple_phi_arg_def (phi, i);
	  edge arg_e = gimple_phi_arg_edge (phi, i);

	  if (!integer_zerop (arg))
	    profile_address_bound (arg, count_map, arg_e->src);
	}
    }
}

void
array_manip_callee_info::profile_address_plus_count (tree addr, tree count,
						gimple *stmt,
						auto_vec<tree_pair> &count_map)
{
  basic_block bb = gimple_bb (SSA_NAME_DEF_STMT (addr));
  tree new_addr;

  if (TREE_CODE (count) == SSA_NAME)
    {
      basic_block count_bb = gimple_bb (SSA_NAME_DEF_STMT (count));

      if (!dominated_by_p (CDI_DOMINATORS, bb, count_bb))
	{
	  gcc_assert (dominated_by_p (CDI_DOMINATORS, count_bb, bb));
	  bb = count_bb;
	}
    }
  else
    gcc_assert (TREE_CODE (count) == INTEGER_CST);

  new_addr = fold_convert (sizetype, count);
  new_addr = fold_build2 (MULT_EXPR, sizetype, count, elem_size);
  new_addr = build2 (POINTER_PLUS_EXPR, TREE_TYPE (addr), addr, new_addr);
  new_addr = insert_to_bb_end (new_addr, bb);

  profile_address_bound (new_addr, count_map);
  other_addrs_to_bound.put (stmt, new_addr);
}

void
array_manip_callee_info::profile_array_access_bound ()
{
  auto_vec<tree_pair> count_map;

  count_map.safe_push ({ count_basis, NULL_TREE });

  for (unsigned i = 0; i < count_map.length (); )
    {
      tree count_var = count_map[i++].first;
      gimple *use_stmt;
      imm_use_iterator use_iter;

      FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, count_var)
	{
	  if (gimple_assign_ssa_name_copy_p (use_stmt))
	    {
	      tree copy = gimple_assign_lhs (use_stmt);

	      if (vrp_prop.has_useful_predicate (copy))
		count_map.safe_push ({ copy, NULL_TREE });
	    }
	}
    }

  for (auto stmt : array_loads)
    {
      tree rhs = gimple_assign_rhs1 (stmt);
      tree base = get_mem_access_simple_base (rhs);

      profile_address_bound (base, count_map, gimple_bb (stmt));
    }

  for (auto stmt : array_stores)
    {
      tree lhs = gimple_get_lhs (stmt);

      if (lhs)
	{
	  tree base = get_mem_access_simple_base (lhs);

	  profile_address_bound (base, count_map, gimple_bb (stmt));
	}

      if (is_gimple_call (stmt))
	profile_address_plus_count (gimple_call_arg (stmt, array_param_idx),
				    gimple_call_arg (stmt, count_param_idx),
				    stmt, count_map);
    }

  edge latch = loop_latch_edge (main_loop);
  gimple *array_stmt = SSA_NAME_DEF_STMT (array_basis);
  gimple *count_stmt = SSA_NAME_DEF_STMT (count_basis);

  profile_address_plus_count (PHI_ARG_DEF_FROM_EDGE (array_stmt, latch),
			      PHI_ARG_DEF_FROM_EDGE (count_stmt, latch),
			      array_stmt, count_map);
}

bool
array_manip_callee_info::find_array_and_count_basis ()
{
  unsigned i;
  tree name;
  hash_set<tree> maybe_count_params;

  FOR_EACH_SSA_NAME (i, name, cfun)
    {
      if (SSA_NAME_IN_FREE_LIST (name)
	  || !POINTER_TYPE_P (TREE_TYPE (name))
	  || !gimple_bb (SSA_NAME_DEF_STMT (name)))
	continue;

      tree base, index, scale;

      split_array_address (name, base, index, scale);

      if (!index || TREE_CODE (index) != SSA_NAME)
	continue;

      tree index_var = SSA_NAME_VAR (index);

      if (!index_var || TREE_CODE (index_var) != PARM_DECL)
	continue;

      auto base_set = analyzer.get_address_base (name);

      if (base_set.length () != 1
	  || !operand_equal_p (array_param, base_set[0]))
	continue;

      if (tree index_ssa = ssa_default_def (cfun, index_var))
	maybe_count_params.add (index_ssa);
    }

  edge entry = loop_preheader_edge (main_loop);
  edge latch = loop_latch_edge (main_loop);

  for (auto si = gsi_start_phis (main_loop->header); !gsi_end_p (si);
       gsi_next (&si))
    {
      gimple *stmt = gsi_stmt (si);
      tree result = gimple_phi_result (stmt);
      tree init = PHI_ARG_DEF_FROM_EDGE (stmt, entry);
      tree next = PHI_ARG_DEF_FROM_EDGE (stmt, latch);

      if (POINTER_TYPE_P (TREE_TYPE (result)))
	{
	  auto base_set = analyzer.get_address_base (result);

	  if (!base_set.contains (array_param))
	    continue;

	  if (base_set.length () != 1)
	    return false;

	  /* Found multiple array basis addresses.  */
	  if (array_basis)
	    return false;

	  /* TODO: array basis address used in loop could be array_param
	     + non-zero-cst.  */
	  if (init != array_param)
	    return false;

	  if (TREE_CODE (next) != SSA_NAME)
	    return false;

	  array_basis = result;
	}
      else if (count_param_idx >= -1 && INTEGRAL_TYPE_P (TREE_TYPE (result)))
	{
	  /* TODO: Find count parameter in a more reasonable way, and count
	     basis used in loop could be count_param + non-zero-cst.  */
	  if (TREE_CODE (init) != SSA_NAME || !SSA_NAME_IS_DEFAULT_DEF (init))
	    continue;

	  if (TREE_CODE (next) != SSA_NAME)
	    continue;

	  int param_idx = function_param_index (cfun->decl, init);

	  if (param_idx < 0)
	    continue;

	  if (count_param)
	    reset_count_bound ();
	  else if (maybe_count_params.contains (init))
	    {
	      count_param_idx = param_idx;
	      count_param = init;
	      count_basis = result;

	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "> Found array count parameter(#%d): ",
			   count_param_idx);
		  print_generic_expr (dump_file, count_param, TDF_NONE);
		  fprintf (dump_file, "\n");
		}
	    }
	}

      if (!array_basis)
	array_basis_phi_idx++;
    }

  return array_basis;
}

bool
array_manip_callee_info::check_array_forward_updating ()
{
  vrp_prop.build_range_predicates ();

  /* Remark reachability since some new blocks might be added.  */
  mark_reachable_blocks (main_loop->header);

  if (count_param)
    profile_array_access_bound ();

  vrp_prop.init ();

  if (count_param)
    {
      tree type = TREE_TYPE (count_param);
      symbolic_range &range = vrp_prop.get_range (count_param);
      widest_int wi_limit;

      wi_limit = wi::to_widest (TYPE_MAX_VALUE (sizetype));
      wi_limit = wi_limit / wi::to_widest (elem_size) + 1;

      if (count_limit && wi_limit > wi::to_widest (count_limit))
	wi_limit = wi::to_widest (count_limit);

      if (wi_limit > wi::to_widest (TYPE_MAX_VALUE (type)))
	wi_limit = wi::to_widest (TYPE_MAX_VALUE (type));

      /* A reasonable assumption that 64-bit integer count parameter is
	 in range of [0, 0xFFFFFFFF].  */
      if (TYPE_PRECISION (type) == 64 && wi_limit > 0xFFFFFFFF)
	wi_limit = 0xFFFFFFFF;

      range.set (build_zero_cst (type), wide_int_to_tree (type, wi_limit));
    }

  edge entry = loop_preheader_edge (main_loop);
  edge latch = loop_latch_edge (main_loop);
  basic_block header = main_loop->header;

  for (auto si = gsi_start_phis (header); !gsi_end_p (si); gsi_next (&si))
    {
      gimple *stmt = gsi_stmt (si);

      if (!stmt->uid)
	continue;

      tree result = gimple_phi_result (stmt);

      /* All addresses in the loop are derived from a base address at header
	 block, propagation should not cross related defining statements.  */
      if (POINTER_TYPE_P (TREE_TYPE (result)))
	{
	  vrp_prop.get_range (result).init (result);
	  vrp_prop.clear_stmt (stmt);
	}
    }

  vrp_prop.join_propagate ();

  for (auto si = gsi_start_phis (header); !gsi_end_p (si); gsi_next (&si))
    {
      gimple *stmt = gsi_stmt (si);

      if (!stmt->uid)
	continue;

      tree result = gimple_phi_result (stmt);

      if (!POINTER_TYPE_P (TREE_TYPE (result)))
	{
	  /* For non-pointer iv SSA in loop header, if its range is unavailable
	     in that its evolution is too complicated to be computed by normal
	     VRP, we use a tricky assume-and-prove means to infer, this can
	     avoid iterative computation due to loop back-edge.  We assume that
	     value range of non-pointer SSA in loop header is determined by its
	     init value, and all value range computation are done under this
	     assumption.  At last, we will check whether the value range of SSA
	     in loop header is expanded.  If so, the assumption is not true,
	     and consider the check is failed.  */
	  ssa_predicate &predicate = vrp_prop.get_predicate (result);

	  switch (predicate.op)
	    {
	      case LT_EXPR:
	      case LE_EXPR:
	      case GT_EXPR:
	      case GE_EXPR:
		/* Range will definitely be expanded from initial value, resort
		   to iterative computation with at most two times.  */
		continue;

	      default:
		break;
	    }

	  tree init = PHI_ARG_DEF_FROM_EDGE (stmt, entry);

	  /* If initial value of SSA is a constant, it range is in all
	     possibility to be expanded, also do not use assume-and-prove
	     means.  */
	  if (TREE_CODE (init) != SSA_NAME)
	    continue;

	  vrp_prop.get_range (result) = vrp_prop.get_range (init);
	  vrp_prop.clear_stmt (stmt);
	}
    }

  vrp_prop.meet_propagate ();
  vrp_prop.fini ();

  if (dump_file && (dump_flags & TDF_DETAILS) && !bound_addr_map.is_empty ())
    {
      unsigned i;
      tree name;

      fprintf (dump_file, "Bound check addresses and ranges:\n");

      FOR_EACH_SSA_NAME (i, name, cfun)
	{
	  if (SSA_NAME_IN_FREE_LIST (name)
	      || !POINTER_TYPE_P (TREE_TYPE (name)))
	   continue;

	  if (auto *bound_item = bound_addr_map.get (name))
	    {
	      tree bound_addr = bound_item->first;

	      print_gimple_stmt (dump_file, SSA_NAME_DEF_STMT (bound_addr),
				 TDF_NONE);
	      fprintf (dump_file, "  Range: ");
	      vrp_prop.get_range (bound_addr).dump (dump_file);
	      fprintf (dump_file, "\n");
	    }
	}

      fprintf (dump_file, "\n");
    }

  for (auto si = gsi_start_phis (header); !gsi_end_p (si); gsi_next (&si))
    {
      gimple *stmt = gsi_stmt (si);

      if (!stmt->uid || vrp_prop.include_stmt_p (stmt))
	continue;

      tree result = gimple_phi_result (stmt);
      tree next = PHI_ARG_DEF_FROM_EDGE (stmt, latch);

      if (result == array_basis)
	{
	  symbolic_range &next_range = vrp_prop.get_range (next);

	  /* The array basis address should advance with non-negative offset
	     in next iteration.  */
	  if (next_range.kind () != VR_RANGE
	      || wi::neg_p (wi::to_wide (next_range.min ()))
	      || !operand_equal_p (array_basis, next_range.symbol ()))
	    return false;

	  if (count_param)
	    check_address_bound (*other_addrs_to_bound.get (stmt));
	}
      else if (!POINTER_TYPE_P (TREE_TYPE (result)))
	{
	  symbolic_range &range = vrp_prop.get_range (result);
	  symbolic_range &next_range = vrp_prop.get_range (next);

	  next_range.union_ (range);

	  /* Value range of non-pointer SSA in loop header will be expanded.  */
	  if (!next_range.equal_p (range, true))
	    return false;
	}
    }

  if (!check_store_stmts ())
    return false;

  check_load_stmts ();
  return true;
}

bool
array_manip_callee_info::find_qualified_array (
				auto_vec<cgraph_edge *> &manip_edges)
{
  cfun_context ctx (node);

  if (!determine_sole_array_updated ())
    return false;

  if (!get_possible_callers (manip_edges))
    return false;

  unsigned i;
  tree name;
  basic_block dom_bb = NULL;

  loop_optimizer_init (LOOPS_NORMAL);

  FOR_EACH_SSA_NAME (i, name, cfun)
    {
      if (SSA_NAME_IN_FREE_LIST (name)
	  || !SSA_NAME_IS_VIRTUAL_OPERAND (name))
	continue;

      gimple *stmt = SSA_NAME_DEF_STMT (name);
      basic_block bb = gimple_bb (stmt);

      if (!bb || !gimple_vdef (stmt))
	continue;

      if (!dom_bb)
	dom_bb = bb;
      else
	dom_bb = nearest_common_dominator (CDI_DOMINATORS, dom_bb, bb);
    }

  class loop *loop = dom_bb->loop_father;
  bool simple_clean = true;

  if (!loop_depth (loop))
    goto end;

  while (loop_depth (loop) > 1)
    loop = loop_outer (loop);

  main_loop = loop;

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "> LOOP %d: Check memory access pattern\n",
	     main_loop->num);

  if (!check_return_value () || !mark_array_access_region ())
    goto end;

  if (check_array_forward_updating ())
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "> LOOP %d: Found forward memory access pattern\n",
		 main_loop->num);
      return true;
    }

  simple_clean = false;

end:
  cleanup_function (node, simple_clean);
  return false;
}

gcall *
array_manip_callee_info::insert_bound_argument (cgraph_edge *call_edge,
						tree bound_addr)
{
  auto_vec<tree> args;
  gcall *call_stmt = call_edge->call_stmt;
  gimple_stmt_iterator gsi = gsi_for_stmt (call_stmt);
  cgraph_node *caller = call_edge->caller;
  cfun_context ctx (caller);

  gcc_checking_assert (call_edge->callee == node && dse_node);

  for (unsigned i = 0; i < gimple_call_num_args (call_stmt); i++)
    {
      args.safe_push (gimple_call_arg (call_stmt, i));

      if (i == (unsigned) array_param_idx)
	{
	  bound_addr = force_gimple_operand_gsi (&gsi, bound_addr, true,
						 NULL_TREE, true,
						 GSI_SAME_STMT);
	  args.safe_push (bound_addr);
	}
    }

  gcall *new_call = gimple_build_call_vec (dse_node->decl, args);

  if (tree lhs = gimple_call_lhs (call_stmt))
    gimple_call_set_lhs (new_call, lhs);

  if (tree vdef = gimple_vdef (call_stmt))
    {
      gimple_set_vdef (new_call, vdef);
      SSA_NAME_DEF_STMT (vdef) = new_call;
    }

  gimple_set_vuse (new_call, gimple_vuse (call_stmt));
  gimple_call_copy_flags (new_call, call_stmt);
  gimple_call_set_chain (new_call, gimple_call_chain (call_stmt));
  gsi_replace (&gsi, new_call, false);

  cgraph_update_edges_for_call_stmt (call_stmt,
				     gimple_call_fndecl (call_stmt), new_call);

  caller->remove_stmt_references (call_stmt);
  caller->record_stmt_references (new_call);
  return new_call;
}

static tree
add_parameter_to_function (cgraph_node *node, unsigned param_idx,
			   const char *suffix)
{
  cfun_context ctx (node);
  vec<ipa_adjusted_param, va_gc> *new_params = NULL;
  auto_vec<tree> arg_decls;
  const char *name = suffix;

  push_function_arg_decls (&arg_decls, node->decl);
  gcc_checking_assert (!arg_decls.is_empty ());
  vec_safe_reserve (new_params, arg_decls.length () + 1);

  for (unsigned i = 0; i < arg_decls.length (); ++i)
    {
      ipa_adjusted_param adj;

      memset (&adj, 0, sizeof (adj));

      adj.type = TREE_TYPE (arg_decls[i]);
      adj.base_index = i;
      adj.prev_clone_index = i;
      adj.op = IPA_PARAM_OP_COPY;
      new_params->quick_push (adj);

      if (i == param_idx)
	{
	  tree arg_name = DECL_NAME (arg_decls[i]);

	  if (arg_name)
	    name = concat (IDENTIFIER_POINTER (arg_name), suffix, NULL);

	  adj.type = TREE_TYPE (arg_decls[i]);
	  adj.base_index = i;
	  adj.prev_clone_index = i;
	  adj.op = IPA_PARAM_OP_NEW;
	  new_params->quick_push (adj);
	}
    }

  auto adjustments = new ipa_param_body_adjustments (new_params, node->decl);

  adjustments->modify_formal_parameters ();

  delete adjustments;

  arg_decls.truncate (0);
  push_function_arg_decls (&arg_decls, node->decl);

  tree new_param = arg_decls[param_idx + 1];

  DECL_NAME (new_param) = get_identifier (name);

  return get_or_create_ssa_default_def (cfun, new_param);
}

void
array_manip_callee_info::annotate_label_and_clone (class loop *&dse_loop,
						   basic_block &dse_return_bb)
{
  push_dump_file save (NULL, TDF_NONE);
  edge e;
  edge_iterator ei;

  for (auto loop : loops_list (cfun, 0))
    {
      if (loop_depth (loop) != 1)
	continue;

      edge entry = loop_preheader_edge (loop);

      if (loop == main_loop)
	{
	  tree lab = create_artificial_label (UNKNOWN_LOCATION);
	  gimple_stmt_iterator gsi = gsi_start_bb (entry->src);

	  gsi_insert_before (&gsi, gimple_build_label (lab), GSI_SAME_STMT);
	}
      else
	split_edge (entry);
    }

  if (return_bb)
    {
      FOR_EACH_EDGE (e, ei, EXIT_BLOCK_PTR_FOR_FN (cfun)->preds)
	{
	  if (return_bb == e->src)
	    {
	      tree lab = create_artificial_label (UNKNOWN_LOCATION);
	      gimple_stmt_iterator gsi = gsi_start_bb (e->src);

	      gsi_insert_before (&gsi, gimple_build_label (lab),
				 GSI_SAME_STMT);
	    }
	  else
	    split_block_after_labels (e->src);
	}
    }

  dse_node = node->create_version_clone_with_body (vNULL, NULL, NULL, NULL,
						   NULL, "array_dse", NULL);
  gcc_assert (dse_node);

  cfun_context ctx (dse_node);

  dse_loop = NULL;

  for (auto loop : loops_list (cfun, 0))
    {
      if (loop_depth (loop) != 1)
	continue;

      edge entry = NULL;

      FOR_EACH_EDGE (entry, ei, loop->header->preds)
	{
	  if (entry->src != loop->latch)
	    break;
	}

      gcc_checking_assert (entry && EDGE_COUNT (loop->header->preds) == 2);

      if (safe_dyn_cast<glabel *> (first_stmt (entry->src)))
	{
	  dse_loop = loop;
	  break;
	}
    }

  if (return_bb)
    {
      FOR_EACH_EDGE (e, ei, EXIT_BLOCK_PTR_FOR_FN (cfun)->preds)
	{
	  if (safe_dyn_cast<glabel *> (first_stmt (e->src)))
	    {
	      dse_return_bb = e->src;
	      break;
	    }
	}
    }
  else
    dse_return_bb = NULL;
}

#define NODE_NOT_ARRAY_MANIP      ((void *) 1)
#define CALL_ARRAY_MANIP_IN_CHECK ((void *) 1)

void
array_manip_callee_info::make_node_with_dse_check ()
{
  if (dse_node)
    return;

  unsigned i;
  tree name;
  auto_vec<gimple *> restore_stmts;
  cfun_context ctx (node);
  gimple_stmt_iterator gsi;

  FOR_EACH_SSA_NAME (i, name, cfun)
    {
      if (SSA_NAME_IN_FREE_LIST (name) || SSA_NAME_IS_VIRTUAL_OPERAND (name))
	continue;

      symbolic_range &range = vrp_prop.get_range (name);
      tree value;

      if (range.symbol () || !range.singleton_p (&value))
	continue;

      gimple *stmt = SSA_NAME_DEF_STMT (name);

      gcc_assert (gimple_bb (stmt));

      if (!is_gimple_assign (stmt) || gimple_vuse (stmt))
	continue;

      /* We could do some constant replacements before transformation.  */
      gsi = gsi_for_stmt (stmt);
      gsi_replace (&gsi, gimple_build_assign (name, value), false);

      if (need_clone)
	restore_stmts.safe_push (stmt);
    }

  class loop *dse_loop = main_loop;
  basic_block dse_return_bb = return_bb;

  if (need_clone)
    {
      annotate_label_and_clone (dse_loop, dse_return_bb);

      /* Restore original statements.  */
      for (auto restore_stmt : restore_stmts)
	{
	  tree name = gimple_assign_lhs (restore_stmt);
	  gimple *stmt = SSA_NAME_DEF_STMT (gimple_get_lhs (restore_stmt));

	  gsi = gsi_for_stmt (stmt);
	  gimple_assign_set_lhs (restore_stmt, name);
	  gsi_replace (&gsi, restore_stmt, false);
	}
    }
  else
    dse_node = node;

  cfun_context dse_ctx (dse_node);
  gimple *addr_stmt = NULL;
  tree return_val = NULL_TREE;

  for (i = 0, gsi = gsi_start_phis (dse_loop->header); !gsi_end_p (gsi);
       gsi_next (&gsi))
    {
      if (i++ == array_basis_phi_idx)
	{
	  tree lhs = gimple_phi_result (addr_stmt = gsi_stmt (gsi));

	  gcc_checking_assert (POINTER_TYPE_P (TREE_TYPE (lhs)));
	  break;
	}
    }

  gcc_checking_assert (addr_stmt);

  tree bound_ssa = add_parameter_to_function (dse_node, array_param_idx,
					      ".bound");
  edge latch = loop_latch_edge (dse_loop);
  tree latch_value = PHI_ARG_DEF_FROM_EDGE (addr_stmt, latch);
  basic_block break_bb = split_edge (latch);
  gimple *break_cond = gimple_build_cond (GE_EXPR, latch_value, bound_ssa,
					  NULL_TREE, NULL_TREE);
  gsi = gsi_last_bb (break_bb);
  gsi_insert_after (&gsi, break_cond, GSI_NEW_STMT);

  if (dse_return_bb)
    {
      auto ret = as_a<greturn *> (last_stmt (dse_return_bb));

      return_val = gimple_return_retval (ret);
      gcc_checking_assert (return_val);
      return_val = unshare_expr (return_val);
    }

  edge to_loop = single_succ_edge (break_bb);
  edge to_stop = make_edge (break_bb, EXIT_BLOCK_PTR_FOR_FN (cfun), 0);
  basic_block new_return_bb = split_edge (to_stop);
  edge to_exit = single_succ_edge (new_return_bb);
  gimple *new_return_stmt = gimple_build_return (return_val);

  gsi = gsi_last_bb (new_return_bb);
  gsi_insert_after (&gsi, new_return_stmt, GSI_NEW_STMT);

  /* Clear flags on fake edge to exit.  */
  to_exit->flags = 0;

  to_loop->flags &= ~EDGE_FALLTHRU;
  to_loop->flags |= EDGE_FALSE_VALUE;
  to_stop->flags |= EDGE_TRUE_VALUE;

  to_loop->probability = profile_probability::very_likely ();
  to_stop->probability = profile_probability::very_unlikely ();

  auto_vec<cgraph_edge *, 2> recursive_edges;

  for (auto cs = dse_node->callees; cs; cs = cs->next_callee)
    {
      if (cs->callee == node)
	recursive_edges.safe_push (cs);
    }

  for (auto cs : recursive_edges)
    insert_bound_argument (cs, bound_ssa);

  if (need_clone)
    cleanup_function (dse_node);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n> Make array manip function for DSE:\n");
      dump_function_to_file (dse_node->decl, dump_file, TDF_NONE);
    }
}

static bool
analyze_array_manip_callee (cgraph_node *node,
			    auto_vec<cgraph_edge *> &manip_edges)
{
  if (node->aux)
    return false;

  node->aux = NODE_NOT_ARRAY_MANIP;

  if (!node->has_gimple_body_p ()
      || !tree_versionable_function_p (node->decl)
      || !opt_for_fn (node->decl, optimize)
      || node->inlined_to
      || node->comdat_local_p ()
      || node->get_availability () < AVAIL_AVAILABLE)
    return false;

  gcc_assert (!node->clone_of);

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "\n> Analyze array manip function %s: \n",
	     node->dump_asm_name ());

  auto callee_info = new array_manip_callee_info (node);
  auto_vec<cgraph_edge *> new_edges;

  if (!callee_info->find_qualified_array (new_edges))
    {
      delete callee_info;
      return false;
    }

  manip_edges.safe_splice (new_edges);
  node->aux = callee_info;
  return true;
}

static bool
decompose_array_access (gimple *stmt, tree elem_type, tree &base, tree &index,
			wide_int &index_offset, bool split_base)
{
  tree memref;

  if (gimple_vdef (stmt))
    memref = gimple_assign_lhs (stmt);
  else
    memref = gimple_assign_rhs1 (stmt);

  /* Skip memory reference containing bit-field.  */
  if (TREE_CODE (memref) == BIT_FIELD_REF)
    return false;

  tree expr = memref;

  while (handled_component_p (expr))
    {
      if (TREE_CODE (expr) == ARRAY_RANGE_REF)
	return false;

      if (TREE_CODE (expr) == ARRAY_REF)
	break;

      expr = TREE_OPERAND (expr, 0);
    }

  tree size = TYPE_SIZE_UNIT (elem_type);
  HOST_WIDE_INT offset_int;

  index_offset = wi::zero (TYPE_PRECISION (sizetype));

  /* Only allow one-dimension array access.  */
  if (TREE_CODE (expr) == ARRAY_REF)
    {
      if (!operand_equal_p (size, array_ref_element_size (expr)))
	return false;

      tree bound = array_ref_low_bound (expr);

      if (TREE_CODE (bound) != INTEGER_CST)
	return false;

      index = TREE_OPERAND (expr, 1);

      if (!integer_zerop (bound))
	{
	  if (TREE_CODE (index) == INTEGER_CST)
	    index = fold_binary (MINUS_EXPR, TREE_TYPE (index), index, bound);
	  else
	    index_offset = -wi::to_wide (bound, TYPE_PRECISION (sizetype));
	}

      expr = TREE_OPERAND (expr, 0);
      base = get_mem_access_simple_base (expr, &offset_int);
    }
  else
    {
      index = NULL_TREE;
      base = get_mem_access_simple_base (memref, &offset_int);
    }

  if (TREE_CODE (expr) != MEM_REF && !DECL_P (expr))
    return false;

  if (base == error_mark_node)
    return false;

  if (offset_int)
    {
      if (!tree_fits_shwi_p (TYPE_SIZE (elem_type)))
	return false;

      HOST_WIDE_INT bits = tree_to_shwi (TYPE_SIZE (elem_type));
      HOST_WIDE_INT rem_bits = offset_int % bits;

      index_offset += offset_int / bits;

      if (!index)
	{
	  tree mref_size = TYPE_SIZE (TREE_TYPE (memref));

	  if (!tree_fits_shwi_p (mref_size))
	    return false;

	  HOST_WIDE_INT mref_bits = tree_to_shwi (mref_size);

	  if (rem_bits < 0)
	    {
	      rem_bits += bits;
	      index_offset -= 1;
	    }

	  /* Cross element boundary.  */
	  if (mref_bits > bits - rem_bits)
	    return false;
	}
      else if (rem_bits)
	return false;
    }

  if (split_base && !index && !DECL_P (expr))
    {
      tree scale;

      split_array_address (base, base, index, scale);

      if (scale && !operand_equal_p (scale, size))
	return false;
    }

  return true;
}

class array_manip_caller_info
{
public:
  cgraph_node *node;
  addr_analyzer analyzer;
  symbolic_vrp_prop vrp_prop;

  array_manip_caller_info (cgraph_node *node) : node (node) { }
};

class array_manip_call_info
{
public:
  array_manip_callee_info &callee_info;

  gcall *call_stmt;

  tree array;
  tree array_addr;
  tree array_size;

  tree array_arg;
  tree count_arg;

  bool self_use_p;

  addr_analyzer &analyzer;
  symbolic_vrp_prop &vrp_prop;

  auto_vec<gimple *> access_set;
  hash_map<gimple *, symbolic_range *> access_range_map;

  int byref_elem;
  memref_areas byref_load_areas;
  symbolic_range load_use_range;

  array_manip_call_info (cgraph_edge *cs,
			 array_manip_callee_info &callee_info,
			 addr_analyzer &analyzer,
			 symbolic_vrp_prop &vrp_prop)
    : callee_info (callee_info), call_stmt (cs->call_stmt), array (NULL_TREE)
    , array_addr (NULL_TREE), count_arg (NULL_TREE), self_use_p (false)
    , analyzer (analyzer), vrp_prop (vrp_prop)
    , byref_elem (callee_info.byref_elem)
  {
    int array_arg_idx = callee_info.array_param_idx;
    int count_arg_idx = callee_info.count_param_idx;

    array = extract_local_array_argument (cs, array_arg_idx, analyzer,
					  array_size);

    array_size = fold_convert (ptrdiff_type_node, array_size);

    if (DECL_P (array))
      array_addr = build1 (ADDR_EXPR, build_pointer_type (TREE_TYPE (array)),
			   array);

    gcc_checking_assert (array_arg_idx >= 0);
    array_arg = gimple_call_arg (call_stmt, array_arg_idx);

    if (count_arg_idx >= 0)
      count_arg = gimple_call_arg (call_stmt, count_arg_idx);

    for (unsigned i = 0; i < gimple_call_num_args (call_stmt); i++)
      {
	if (i == (unsigned) array_arg_idx)
	  continue;

	tree arg = gimple_call_arg (call_stmt, i);

	if (!POINTER_TYPE_P (TREE_TYPE (arg)))
	  continue;

	auto base_set = analyzer.get_address_base (arg);

	/* Check that in caller side the array occurs only once in argument
	   list.  This ensure that except known array parameter, other
	   parameter in callee should not point to the array.  */
	if (base_set.contains (array))
	  byref_elem = 0;
      }

    if (byref_elem)
      byref_load_areas.safe_splice (callee_info.byref_load_areas);
  }

  ~array_manip_call_info ()
  {
    for (auto access : access_set)
      {
	if (auto range_ptr = access_range_map.get (access))
	  delete *range_ptr;
      }
  }

  void get_array_range_at_index (symbolic_range &array_range,
				 symbolic_range &index_range);

  void get_array_range_at_index (symbolic_range &array_range, tree index)
  {
    symbolic_range index_range = vrp_prop.get_range_from_tree (index);

    get_array_range_at_index (array_range, index_range);
  }

  symbolic_range get_array_range (tree base = NULL_TREE)
  {
    return vrp_prop.get_range_from_tree (base ? base : array_addr);
  }

  symbolic_range get_array_range_at_index (tree index)
  {
    symbolic_range array_range = get_array_range ();

    get_array_range_at_index (array_range, index);
    return array_range;
  }

  void expand_array_range (symbolic_range &array_range, bool to_up);

  symbolic_range expand_array_range (tree base, bool to_up)
  {
    symbolic_range array_range = get_array_range (base);

    expand_array_range (array_range, to_up);
    return array_range;
  }

  symbolic_range expand_array_range_at_index (tree index, bool to_up)
  {
    symbolic_range array_range = get_array_range_at_index (index);

    expand_array_range (array_range, to_up);
    return array_range;
  }

  bool check_array_for_dse ();
  bool malloc_linear_dominates_stmt_p (tree, gimple *);
  bool only_accessed_via_array_byref_element (tree, gimple *);
  bool check_array_byref_element ();
  symbolic_range get_self_use_range (hash_set<tree> &);
  bool compute_array_redundant_part ();
  tree create_array_redundant_bound ();
};

void
array_manip_call_info::get_array_range_at_index (symbolic_range &array_range,
						 symbolic_range &index_range)
{
  tree elem_type = TREE_TYPE (TREE_TYPE (array));
  tree elem_size = TYPE_SIZE_UNIT (elem_type);
  tree addr_type = build_pointer_type (elem_type);
  symbolic_range esize_range = vrp_prop.get_range_from_tree (elem_size);

  symbolic_range_fold_unary_expr (CONVERT_EXPR, ptrdiff_type_node,
				  &esize_range, sizetype);

  if (!index_range.undefined_p ()
      && !types_compatible_p (index_range.type (), ptrdiff_type_node))
    symbolic_range_fold_unary_expr (CONVERT_EXPR, ptrdiff_type_node,
				    &index_range, index_range.type ());

  symbolic_range_fold_binary_expr (MULT_EXPR, ptrdiff_type_node,
				   &index_range, &esize_range);
  symbolic_range_fold_binary_expr (POINTER_PLUS_EXPR, addr_type,
				   &array_range, &index_range);
}

void
array_manip_call_info::expand_array_range (symbolic_range &array_range,
					   bool to_up)
{
  if (array_range.undefined_p ())
    return;

  gcc_checking_assert (array_range.have_symbol_p (array_addr));

  if (array_range.kind () == VR_ANTI_RANGE)
    array_range.set (build_zero_cst (ptrdiff_type_node), array_size);
  else if (to_up)
    {
      if (wi::les_p (wi::to_wide (array_size),
		     wi::to_wide (array_range.min ())))
	array_range.set_undefined ();
      else if (wi::neg_p (wi::to_wide (array_range.min ())))
	array_range.set (build_zero_cst (ptrdiff_type_node), array_size);
      else
	array_range.set (array_range.min (), array_size);
    }
  else
    {
      if (wi::neg_p (wi::to_wide (array_range.max ())))
	array_range.set_undefined ();
      else if (wi::lts_p (wi::to_wide (array_size),
			  wi::to_wide (array_range.max ())))
	array_range.set (build_zero_cst (ptrdiff_type_node), array_size);
     else
	array_range.set (build_zero_cst (ptrdiff_type_node),
			 array_range.max ());
    }
}

bool
array_manip_call_info::check_array_for_dse ()
{
  if (TREE_CODE (array) == SSA_NAME)
    {
      gimple *stmt = SSA_NAME_DEF_STMT (array);

      /* Definition of array might not dominate call statement, because an
	 address whose origin includes not only the array, but also a null
	 pointer (via a PHI) is also considered as member of the array address
	 set.  When this happens, it is hard to generate cfg-correct code at
	 transformation stage to assure dominance rule on def-use chain.  */
      if (!stmt_dominates_stmt_p (stmt, call_stmt))
	return false;
    }

  if (analyzer.exclude_base_p (array, AU_COND_EX | AU_SAVED))
    return false;

  auto addr_set = analyzer.get_address_set (array);

  gcc_checking_assert (!addr_set.is_empty ());

  access_set.safe_splice (analyzer.get_var_access_set (array));

  for (auto addr : addr_set)
    {
      gimple *use_stmt;
      imm_use_iterator use_iter;

      if (analyzer.get_address_base (addr).length () > 1)
	return false;

      FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, addr)
	{
	  if (is_gimple_call (use_stmt))
	    {
	      if (gimple_call_builtin_p (use_stmt, BUILT_IN_MEMSET))
		;
	      else if (use_stmt != call_stmt)
		return false;

	      auto_vec<tree> memrefs;

	      /* It is possible that memory access on the address is part of
		 function call either as an argument or return value. For
		 simplicity, we just fail the check since the case should be
		 really seldom.  */
	      walk_stmt_load_store_ops (use_stmt, &memrefs, collect_memref,
					collect_memref);

	      for (auto memref : memrefs)
		{
		  if (analyzer.get_address_base (memref).contains (array))
		    return false;
		}
	    }
	  else if (gimple_vuse (use_stmt))
	    {
	      /* Return statement might carry a memory access as its return
		 value, just skip this rare case.  */
	      if (!is_gimple_assign (use_stmt))
		return false;

	      access_set.safe_push (use_stmt);
	    }
	}
    }

  mark_reachable_blocks (gimple_bb (call_stmt), false);

  if (!(gimple_bb (call_stmt)->flags & BB_REACHABLE))
    self_use_p = false;
  else if (!count_arg)
    return false;
  else
    self_use_p = true;

  if (count_arg)
    {
      tree count_param = callee_info.count_param;
      symbolic_range arg_range = vrp_prop.get_range_from_tree (count_arg);
      symbolic_range param_range
		   = callee_info.vrp_prop.get_range_from_tree (count_param);

      gcc_checking_assert (param_range.kind () == VR_RANGE);

      /* Range of count argument is not covered by assumed range of count
	 parameter.  */
      if (arg_range.intersect_r (param_range))
	{
	  /* TODO: if array-manip call does not depend on array result of
	     previous invocation on it, we could generate a runtime check on
	     count to ensure it satisfies range assumption on count
	     parameter.  */
	  if (self_use_p || true)
	    return false;

	  callee_info.need_clone = true;
	}
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Memory access statement on ");
      dump_address (dump_file, array);
      fprintf (dump_file, ":\n");
    }

  tree elem_type = TREE_TYPE (TREE_TYPE (array));
  tree elem_size = TYPE_SIZE_UNIT (elem_type);

  for (auto access : access_set)
    {
      tree base, index;
      wide_int index_offset;

      gcc_checking_assert (gimple_vuse (access));

      if (dump_file && (dump_flags & TDF_DETAILS))
	print_gimple_stmt (dump_file, access, 0, TDF_NONE);

      if (!(gimple_bb (access)->flags & BB_REACHABLE))
	continue;

      if (gimple_has_volatile_ops (access) && !gimple_clobber_p (access))
	return false;

      /* TODO: support assignment whose lhs and rhs are both memory reference,
	 in all probability, it is an aggregate copy statement.  */
      if (gimple_vdef (access)
	  && !gimple_rvalue_p (gimple_assign_rhs1 (access)))
	return false;

      if (!decompose_array_access (access, elem_type, base, index,
				   index_offset, false))
	return false;

      if (DECL_P (base))
	{
	  gcc_checking_assert (base == array);
	  base = array_addr;
	}

      symbolic_range range = get_array_range (base);

      if (index_offset != 0)
	{
	  tree index_cst = wide_int_to_tree (ptrdiff_type_node, index_offset);

	  get_array_range_at_index (range, index_cst);
	}

      if (index)
	get_array_range_at_index (range, index);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "  Range: ");
	  range.dump (dump_file);
	  fprintf (dump_file, "\n");
	}

      if (range.undefined_p ())
	{
	  gimple_bb (access)->flags &= ~BB_REACHABLE;
	  continue;
	}

      if (!range.have_symbol_p (array_addr) || range.zero_bits () < 0)
	return false;

      wide_int access_size
		= wi::one (TYPE_PRECISION (sizetype)) << range.zero_bits ();

      /* Check that memory access should not cross array element boundary,
	 now only power-of-2 element size is supported.  */
      if (!wi::multiple_of_p (access_size, wi::to_wide (elem_size), SIGNED))
	return false;

      access_range_map.put (access, new symbolic_range (range));
    }

  if (byref_elem)
    byref_elem = check_array_byref_element ();

  return compute_array_redundant_part ();
}

bool
array_manip_call_info::only_accessed_via_array_byref_element (tree base,
							gimple *store_stmt)
{
  if (analyzer.exclude_base_p (base, AU_COND_EX | AU_CALL))
    return false;

  for (auto access : analyzer.get_var_access_set (base))
    {
      if (access != store_stmt)
	return false;
    }

  for (auto addr : analyzer.get_address_set (base))
    {
      gimple *use_stmt;
      imm_use_iterator use_iter;

      FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, addr)
	{
	  if (gimple_vuse (use_stmt) && use_stmt != store_stmt
	      && !memory_free_stmt_p (use_stmt))
	    return false;
	}
    }

  return true;
}

bool
array_manip_call_info::malloc_linear_dominates_stmt_p (tree base, gimple *stmt)
{
  if (TREE_CODE (base) != SSA_NAME)
    return false;

  gimple *base_stmt = SSA_NAME_DEF_STMT (base);

  if (!memory_alloc_stmt_p (base_stmt))
    return false;

  if (!stmt_linear_dominates_stmt_p (base_stmt, stmt))
    return false;

  for (auto addr : analyzer.get_address_set (base))
    {
      if (gimple_code (SSA_NAME_DEF_STMT (addr)) == GIMPLE_PHI)
	return false;
    }

  return true;
}

static tree
loop_simple_iv_p (class loop * loop, tree expr)
{
  tree iv_head = NULL_TREE;
  tree iv_step = NULL_TREE;

  while (true)
    {
      expr = skip_ssa_copy (expr);

      if (TREE_CODE (expr) != SSA_NAME)
	return NULL_TREE;

      gimple *stmt = SSA_NAME_DEF_STMT (expr);

      if (gimple_code (stmt) == GIMPLE_PHI)
	{
	  if (gimple_bb (stmt) != loop->header)
	    return NULL_TREE;

	  if (iv_head == expr)
	    return iv_step;

	  if (iv_head)
	    return NULL_TREE;

	  iv_head = expr;
	  expr = PHI_ARG_DEF_FROM_EDGE (stmt, loop_latch_edge (loop));
	}
      else if (is_gimple_assign (stmt))
	{
	  enum tree_code code = gimple_assign_rhs_code (stmt);
	  tree rhs1 = gimple_assign_rhs1 (stmt);
	  tree rhs2 = gimple_assign_rhs2 (stmt);

	  switch (code)
	    {
	    case POINTER_PLUS_EXPR:
	    case PLUS_EXPR:
	    case MINUS_EXPR:
	      rhs2 = skip_ssa_copy (rhs2);
	      if (TREE_CODE (rhs2) != INTEGER_CST)
		return NULL_TREE;

	      if (!just_once_each_iteration_p (loop, gimple_bb (stmt)))
		return NULL_TREE;

	      if (iv_step)
		return NULL_TREE;

	      expr = rhs1;

	      if (code != MINUS_EXPR)
		iv_step = rhs2;
	      else
		iv_step = fold_unary (NEGATE_EXPR, TREE_TYPE (rhs2), rhs2);
	      break;

	    default:
	      return NULL_TREE;
	    }
	}
      else
	return NULL_TREE;
    }

  return NULL_TREE;
}

static bool
addr_differ_with_iteration_p (class loop *loop, tree addr, HOST_WIDE_INT dist)
{
  tree iv_step = loop_simple_iv_p (loop, addr);

  if (!iv_step)
    {
      tree base, index, scale;

      split_array_address (addr, base, index, scale);

      if (!index || !expr_invariant_in_loop_p (loop, base))
	return false;

      iv_step = loop_simple_iv_p (loop, index);

      if (!iv_step)
	return false;

      iv_step = size_binop (MULT_EXPR,
			    fold_convert (sizetype, iv_step),
			    fold_convert (sizetype, scale));
    }

  wide_int wi_step = wi::to_wide (iv_step);
  wide_int wi_dist = wi::shwi (dist, TYPE_PRECISION (sizetype));

  gcc_checking_assert (dist > 0);

  if (wi::neg_p (wi_step))
    {
      wi_step = wi::abs (wi_step);
      if (wi::neg_p (wi_step))
	return false;
    }

  /* Ensure that distance of two adjacent address is not less than the stride,
     otherwise it will cause overlap when accessing the data via indirect
     array. */
  if (wi::lts_p (wi_step, wi_dist))
    return false;

  return true;
}

bool
array_manip_call_info::check_array_byref_element ()
{
  if (!self_use_p)
    return false;

  tree retval = gimple_call_lhs (call_stmt);

  /* Do not use indirect ref array if array-manip callee function leaks any
     address outside.  */
  if (retval && POINTER_TYPE_P (TREE_TYPE (retval)))
    return false;

  tree elem_type = TREE_TYPE (TREE_TYPE (array));

  if (!POINTER_TYPE_P (elem_type))
    return false;

  bool found_init = false;
  memref_areas byref_store_areas;

  for (auto access : access_set)
    {
      if (gimple_vdef (access))
	continue;

      if (!(gimple_bb (access)->flags & BB_REACHABLE))
	continue;

      tree ref_addr = gimple_assign_lhs (access);

      if (!POINTER_TYPE_P (TREE_TYPE (ref_addr)))
	return false;

      if (analyzer.exclude_base_p (ref_addr, AU_COND_EX | AU_CALL | AU_SAVED))
	return false;

      for (auto addr : analyzer.get_address_set (ref_addr))
	{
	  gimple *addr_stmt = SSA_NAME_DEF_STMT (addr);

	  /* Do not allow address offsetting.  */
	  if (is_gimple_assign (addr_stmt))
	    {
	      enum tree_code code = gimple_assign_rhs_code (addr_stmt);
	      tree rhs1 = gimple_assign_rhs1 (addr_stmt);

	      if ((code == ADDR_EXPR && !is_gimple_invariant_address (rhs1))
		  || code == POINTER_PLUS_EXPR)
		return false;
	    }

	  imm_use_iterator use_iter;
	  gimple *use_stmt;

	  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, addr)
	    {
	      if (!gimple_vuse (use_stmt))
		continue;

	      if (!is_gimple_assign (use_stmt))
		return false;

	      tree memref = NULL_TREE;
	      memref_areas *areas;

	      if (!gimple_vdef (use_stmt))
		{
		  memref = gimple_assign_rhs1 (use_stmt);
		  areas = &byref_load_areas;
		}
	      else
		{
		  /* Already has been excluded by AU_SAVED address analyzer
		     check.  */
		  gcc_assert (gimple_assign_rhs1 (use_stmt) != addr);

		  memref = gimple_assign_lhs (use_stmt);
		  areas = &byref_store_areas;
		}

	      if (!areas->add (memref, addr))
		return false;
	    }
	}
    }

  /* Not all fields loaded acting as condition seeds are rewritten in caller,
     we have to use value of array element, instead of data object value
     pointed to by element.  */
  if (!byref_store_areas.include_p (byref_load_areas))
    return false;

  /* Deduce max access size on data object indirectly referenced by array,
     and ensure distance of two adjacent pointer elements should not be
     less than this size, otherwise it will cause memory access overlap,
     and implicitly impact array manip operations.  */
  HOST_WIDE_INT ref_size = byref_store_areas.get_max_size ();

  if (ref_size)
    ref_size = (ref_size - 1) / BITS_PER_UNIT + 1;
  else
    ref_size = 1;

  for (auto access : access_set)
    {
      if (!gimple_vdef (access))
	continue;

      tree ref_addr = gimple_assign_rhs1 (access);

      if (integer_zerop (ref_addr))
	continue;

      auto_vec<tree> base_set;

      for (auto base : analyzer.get_address_base (ref_addr))
	{
	  if (!only_accessed_via_array_byref_element (base, access))
	    return false;

	  if (malloc_linear_dominates_stmt_p (base, access))
	    continue;

	  /* We expect that only array manipulating callee function modifies
	     the array after its initialization.  */
	  if (gimple_bb (access)->flags & BB_REACHABLE)
	    return false;

	  if (!local_memory_in_function_p (base)
	      && !memory_alloc_base_p (base))
	    return false;

	  base_set.safe_push (base);
	}

      if (base_set.is_empty ())
	continue;

      /* We have a very simple assumption that initialization takes place only
	 once, and dominates following operations on the array.  The key point
	 to the check is to ensure that elements of array never point to same
	 object.  */
      if (found_init)
	return false;

      found_init = true;

      class loop *loop = gimple_bb (access)->loop_father;

      if (loop_depth (loop) != 1
	  || !dominated_by_p (CDI_DOMINATORS, gimple_bb (call_stmt),
			      loop->header))
	return false;

      if (!addr_differ_with_iteration_p (loop, ref_addr, ref_size))
	return false;
    }

  return true;
}

symbolic_range
array_manip_call_info::get_self_use_range (hash_set<tree> &overwrite_indices)
{
  basic_block call_bb = gimple_bb (call_stmt);
  auto_vec<tree> worklist;
  hash_set<tree> visited;
  auto_vec<tree> vals;
  bool has_dom = false;
  tree last_dom_val = count_arg;
  unsigned last_val_cnt = 0;
  bool fail = false;

  worklist.safe_push (count_arg);
  visited.add (count_arg);

  do
    {
      tree val = worklist.pop ();

      if (TREE_CODE (val) == INTEGER_CST || SSA_NAME_IS_DEFAULT_DEF (val))
	{
	  vals.safe_push (val);
	  continue;
	}

      gimple *stmt = SSA_NAME_DEF_STMT (val);
      basic_block bb = gimple_bb (stmt);

      if (!(bb->flags & BB_REACHABLE))
	{
	  vals.safe_push (val);
	  continue;
	}

      if (dominated_by_p (CDI_DOMINATORS, call_bb, bb))
	{
	  if (worklist.is_empty ())
	    {
	      last_dom_val = val;
	      last_val_cnt = vals.length ();
	      has_dom = false;
	    }
	  else if (has_dom)
	    {
	      /* Now only allow one dominating input.  */
	      fail = true;
	      break;
	    }
	  else
	    {
	      worklist.safe_push (val);
	      std::swap (worklist[0], worklist.last ());
	      has_dom = true;
	      continue;
	    }
	}

      if (auto phi = dyn_cast<gphi *> (stmt))
	{
	  for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
	    {
	      tree arg = gimple_phi_arg_def (phi, i);

	      if (!visited.add (arg))
		worklist.safe_push (arg);
	    }
	}
      else if (is_gimple_assign (stmt))
	{
	  enum tree_code code = gimple_assign_rhs_code (stmt);
	  tree rhs1 = gimple_assign_rhs1 (stmt);

	  fail = true;
	  switch (code)
	    {
	    case VIEW_CONVERT_EXPR:
	      rhs1 = get_base_address (rhs1);

	    /* fall-through.  */

	    case INTEGER_CST:
	    CASE_CONVERT:
	      if (!INTEGRAL_TYPE_P (TREE_TYPE (rhs1))
		  || TYPE_PRECISION (TREE_TYPE (val))
			!= TYPE_PRECISION (TREE_TYPE (rhs1)))
		goto out;
	      break;

	    case SSA_NAME:
	      break;

	    case PLUS_EXPR:
	      /* We expect new array count is advanced one-by-one.  */
	      if (!integer_onep (gimple_assign_rhs2 (stmt))
		  || !overwrite_indices.contains (val))
		goto out;
	      break;

	    default:
	      goto out;
	    }

	  if (!visited.add (rhs1))
	    worklist.safe_push (rhs1);

	  fail = false;
	}
      else
	{
	  fail = true;
	  break;
	}
    } while (!worklist.is_empty ());

out:
  if (fail)
    {
      vals.truncate (last_val_cnt);
      if (last_dom_val)
	vals.safe_push (last_dom_val);
    }

  symbolic_range range;

  gcc_checking_assert (!vals.is_empty ());

  /* Array elements starting from 0 till index represented by "val" might
     be referenced inside array-manip callee function.  We need to mark
     the range.  */
  for (auto val : vals)
    range.union_ (expand_array_range_at_index (val, /* to_up = */ false));

  return range;
}

static inline int
dominate_p (gimple *stmt1, gimple *stmt2)
{
  if (stmt_dominates_stmt_p (stmt1, stmt2))
    return 1;

  if (stmt_dominates_stmt_p (stmt2, stmt1))
    return -1;

  return 0;
}

class memref_clique
{
public:
  memref_areas areas;
  gimple *first;
  gimple *last;

  memref_clique (const memref_areas &copy_areas, gimple *first = NULL,
		 gimple *last = NULL)
  : first (first), last (last)
  {
    areas.safe_splice (copy_areas);
  }
};

bool
array_manip_call_info::compute_array_redundant_part ()
{
  tree elem_type = TREE_TYPE (TREE_TYPE (array));
  hash_set<tree> overwrite_indices;
  hash_map<tree_ssa_name_hash, vec<memref_clique *>> clique_map;

  for (auto access : access_set)
    {
      if (gimple_vdef (access))
	continue;

      if (!(gimple_bb (access)->flags & BB_REACHABLE))
	continue;

      symbolic_range **range_ptr = access_range_map.get (access);
      tree ref_addr = gimple_assign_lhs (access);

      gcc_checking_assert (range_ptr);

      if (!byref_elem || analyzer.exclude_base_p (ref_addr, AU_COND))
	{
	  load_use_range.union_ (**range_ptr);
	  continue;
	}

      bool can_ignore = true;
      memref_areas areas;
      gimple *last = access;
      bool dom_call_p = stmt_dominates_stmt_p (access, call_stmt);

      for (auto addr : analyzer.get_address_set (ref_addr))
	{
	  auto base_set = analyzer.get_address_base (addr);
	  imm_use_iterator use_iter;
	  gimple *use_stmt;

	  can_ignore = false;

	  if (base_set.length () != 1)
	    break;

	  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, addr)
	    {
	      if (is_gimple_debug (use_stmt))
		continue;

	      /* The use statement should be dominated by access, to be
		 specific, a PHI may not meet the requirement.  */
	      if (self_use_p && gimple_code (use_stmt) == GIMPLE_PHI)
		goto out;

	      if (!gimple_vuse (use_stmt))
		continue;

	      if (!is_gimple_assign (use_stmt) || !gimple_vdef (use_stmt))
		goto out;

	      if (!self_use_p)
		continue;

	      /* Ensure that all stores to byref element should be executed
		 before the array-manip call.  */
	      int dom = dominate_p (use_stmt, last);

	      if (!dom)
		goto out;
	      else if (dom > 0)
		;
	      else if (dom_call_p
		       && !stmt_dominates_stmt_p (use_stmt, call_stmt))
		goto out;
	      else
		last = use_stmt;

	      if (!areas.add (gimple_assign_lhs (use_stmt), addr))
		goto out;
	    }

	  can_ignore = true;
	}
out:
      if (!can_ignore)
	{
	  load_use_range.union_ (**range_ptr);
	  continue;
	}

      tree base, index;
      wide_int index_offset;

      if (!areas.is_empty ()
	  && decompose_array_access (access, elem_type, base, index,
				     index_offset, true)
	  && index && TREE_CODE (index) == SSA_NAME && index_offset == 0)
	{
	  bool existed;
	  bool insert = true;
	  auto &clique_set = clique_map.get_or_insert (index, &existed);

	  if (existed)
	    {
	      for (auto clique : clique_set)
		{
		  int dom_first, dom_last;

		  if (dom_call_p != stmt_dominates_stmt_p (clique->first,
							   call_stmt))
		    continue;

		  if (!(dom_first = dominate_p (access, clique->first)))
		    continue;

		  if (!(dom_last = dominate_p (last, clique->last)))
		    continue;

		  if (dom_first > 0)
		    clique->first = access;

		  if (dom_last < 0)
		    clique->last = last;

		  clique->areas.add (areas);
		  insert = false;
		  break;
		}
	    }
	  else
	    clique_set = vNULL;

	  if (insert)
	    clique_set.safe_push (new memref_clique (areas, access, last));
	}
    }

  for (auto iter = clique_map.begin (); iter != clique_map.end (); ++iter)
    {
      auto clique_set = (*iter).second;
      bool skip_check = false;

      for (auto clique : clique_set)
	{
	  if (!skip_check && clique->areas.include_p (byref_load_areas))
	    {
	      overwrite_indices.add ((*iter).first);
	      skip_check = true;
	    }
	  delete clique;
	}

      clique_set.release ();
    }

  if (self_use_p)
    load_use_range.union_ (get_self_use_range (overwrite_indices));

  symbolic_range manip_range;

  manip_range = expand_array_range (array_arg, /* to_up = */ true);

  if (count_arg)
    manip_range.intersect (expand_array_range_at_index (count_arg, false));

  load_use_range.intersect (manip_range);

  if (load_use_range.undefined_p ())
    return true;

  if (load_use_range.kind () != VR_RANGE)
    return false;

  if (param_array_dse_redundancy_percent > 0)
    {
      widest_int manip_lower = wi::to_widest (manip_range.min ());
      widest_int manip_upper = wi::to_widest (manip_range.max ());
      widest_int refer_upper = wi::to_widest (load_use_range.max ());
      widest_int manip_size = manip_upper - manip_lower;
      widest_int elem_size = wi::to_widest (TYPE_SIZE_UNIT (elem_type));
      widest_int kill_size = manip_upper - refer_upper - elem_size;

      /* Skip if redundancy percentage does not exceeds specified
	 threshold.  */
      if (kill_size * 100 < manip_size * param_array_dse_redundancy_percent)
	return false;
    }

  return true;
}

tree
array_manip_call_info::create_array_redundant_bound ()
{
  tree bound_addr = unshare_expr_without_location (array_addr);
  tree bound_size = load_use_range.max ();
  tree array_type = TREE_TYPE (array);
  tree elem_size = TYPE_SIZE_UNIT (TREE_TYPE (array_type));

  gcc_checking_assert (load_use_range.kind () == VR_RANGE);

  bound_size = fold_convert (sizetype, bound_size);
  bound_size = size_binop (PLUS_EXPR, bound_size, elem_size);

  if (DECL_P (array))
    {
      bound_addr = build2 (MEM_REF, array_type, bound_addr,
			   fold_convert (ptr_type_node, bound_size));
      bound_addr = build1 (ADDR_EXPR, build_pointer_type (array_type),
			   bound_addr);
    }
  else
    bound_addr = build2 (POINTER_PLUS_EXPR, array_type, bound_addr,
			 bound_size);

  return bound_addr;
}

static bool
analyze_array_manip_caller (cgraph_node *node)
{
  cfun_context ctx (node);
  auto caller_info = new array_manip_caller_info (node);
  auto &analyzer = caller_info->analyzer;
  auto &vrp_prop = caller_info->vrp_prop;
  auto_delete_vec<array_manip_caller_info> container (1);
  bool found = false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "\n> Analyze array manip caller function %s: \n",
	     node->dump_asm_name ());

  gcc_assert (node->aux == NODE_NOT_ARRAY_MANIP);
  node->aux = NULL;

  /* RAII container to release callee_info when it is not used.  */
  container.quick_push (caller_info);

  if (!analyzer.prepare ())
    return false;

  loop_optimizer_init (LOOPS_NORMAL);

  vrp_prop.build_range_predicates ();

  mark_reachable_blocks (NULL);

  vrp_prop.init ();
  vrp_prop.join_propagate ();
  vrp_prop.meet_propagate ();
  vrp_prop.fini ();

  analyzer.process ();

  calculate_dominance_info (CDI_DOMINATORS);

  for (auto cs = node->callees; cs; cs = cs->next_callee)
    {
      if (cs->aux != CALL_ARRAY_MANIP_IN_CHECK)
	continue;

      auto callee = cs->callee;

      gcc_checking_assert (callee->aux && callee->aux != NODE_NOT_ARRAY_MANIP);

      auto callee_info = (array_manip_callee_info *) callee->aux;
      auto call_info = new array_manip_call_info (cs, *callee_info, analyzer,
						  vrp_prop);

      if (call_info->check_array_for_dse ())
	{
	  cs->aux = (void *) call_info;
	  found = true;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "\n> Found candidate call:  ");
	      print_gimple_stmt (dump_file, cs->call_stmt, 0, TDF_NONE);
	    }
	}
      else
	{
	  callee_info->need_clone = true;
	  delete call_info;
	}
    }

  if (found)
    {
      container.pop ();
      node->aux = caller_info;
    }

  return found;
}

static bool
apply_array_dse (cgraph_edge *manip_edge)
{
  auto call_info = (array_manip_call_info *) manip_edge->aux;
  auto_delete_vec<array_manip_call_info> container (1);
  cgraph_node *caller = manip_edge->caller;

  /* RAII container to release call_info.  */
  container.quick_push (call_info);
  manip_edge->aux = NULL;

  /* Ensure that callee node will not be removed after redirecting to new
     callee node, because we need to release optimization specific information
     associated with cgraph node.   */
  gcc_assert (manip_edge->inline_failed);

  if (call_info->load_use_range.undefined_p ())
    {
      /* Caller does not reference any content of array, so the call could be
	 removed.  */
      cfun_context ctx (caller);
      gimple *call_stmt = manip_edge->call_stmt;

      /* TODO: update call lhs with right return value.  */
      if (gimple_call_lhs (call_stmt))
	return false;

      gimple_stmt_iterator gsi = gsi_for_stmt (call_stmt);
      basic_block call_bb = gimple_bb (call_stmt);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file,
		   "> Remove call in %s since array is fully redundant:\n",
		   caller->dump_asm_name ());
	  print_gimple_stmt (dump_file, call_stmt, 2, TDF_NONE);
	}

      caller->remove_stmt_references (call_stmt);

      unlink_stmt_vdef (call_stmt);
      if (gsi_remove (&gsi, true))
	gimple_purge_dead_eh_edges (call_bb);
      release_defs (call_stmt);

      cgraph_update_edges_for_call_stmt (call_stmt,
					 gimple_call_fndecl (call_stmt), NULL);
    }
  else
    {
      tree bound_addr = call_info->create_array_redundant_bound ();
      auto callee_info = (array_manip_callee_info *) manip_edge->callee->aux;
      gcall *new_call;

      callee_info->make_node_with_dse_check ();
      new_call = callee_info->insert_bound_argument (manip_edge, bound_addr);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  cfun_context ctx (caller);

	  fprintf (dump_file, "> Rewrite call in %s:\n",
		   caller->dump_asm_name ());
	  fprintf (dump_file, "> Array redundant bound >=: ");
	  print_generic_expr (dump_file, bound_addr, TDF_NONE);
	  fprintf (dump_file, "\n");
	  dump_bb (dump_file, gimple_bb (new_call), 2, TDF_NONE);
	}
    }

  return true;
}

static unsigned int
do_array_dse (void)
{
  cgraph_node **order = XNEWVEC (cgraph_node *, symtab->cgraph_count);
  int nnodes = ipa_reverse_postorder (order);
  auto_vec<cgraph_edge *> cand_edges;
  auto_vec<cgraph_node *> cand_callers;
  auto_vec<cgraph_node *> cand_callees;
  cgraph_node *node;

  gcc_assert (nnodes == symtab->cgraph_count);

  FOR_EACH_FUNCTION (node)
    node->aux = NULL;

  for (int i = nnodes - 1; i >= 0; i--)
    {
      cgraph_node *node = order[i];

      if (!node->has_gimple_body_p () || node->inlined_to)
	{
	  node->aux = NODE_NOT_ARRAY_MANIP;
	  continue;
	}

      if (analyze_array_manip_callee (node, cand_edges))
	cand_callees.safe_push (node);
    }

  for (unsigned i = 0; i < cand_edges.length (); i++)
    {
      auto cand_edge = cand_edges[i];
      auto cand_caller = cand_edge->caller;

      /* Skip function that could be both as array-manip caller and callee.  */
      if (cand_caller->aux != NODE_NOT_ARRAY_MANIP)
	cand_edges.unordered_remove (i--);

      if (cand_callers.contains (cand_caller))
	continue;

      cand_callers.safe_push (cand_caller);

      for (auto cs = cand_caller->callees; cs; cs = cs->next_callee)
	cs->aux = NULL;
    }

  for (auto cand_edge : cand_edges)
    cand_edge->aux = CALL_ARRAY_MANIP_IN_CHECK;

  for (auto cand_caller : cand_callers)
    analyze_array_manip_caller (cand_caller);

  for (auto cand_edge : cand_edges)
    {
      if (!cand_edge->aux)
	continue;

      if (cand_edge->aux != CALL_ARRAY_MANIP_IN_CHECK)
	apply_array_dse (cand_edge);
      else
	cand_edge->aux = NULL;
    }

  for (auto cand_caller : cand_callers)
    {
      delete (array_manip_caller_info *) cand_caller->aux;
      cleanup_function (cand_caller);
    }

  for (auto cand_callee : cand_callees)
    {
      delete (array_manip_callee_info *) cand_callee->aux;
      if (!remove_function (cand_callee))
	cleanup_function (cand_callee);
    }

  FOR_EACH_FUNCTION (node)
    node->aux = NULL;

  free (order);
  return 0;
}

namespace {

const pass_data pass_data_ipa_array_dse =
{
  SIMPLE_IPA_PASS, /* type */
  "array-dse", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_IPA_ARRAY_DSE, /* tv_id */
  PROP_cfg | PROP_ssa, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_ipa_array_dse : public simple_ipa_opt_pass
{
public:
  pass_ipa_array_dse (gcc::context *ctxt)
    : simple_ipa_opt_pass (pass_data_ipa_array_dse, ctxt)
  {}

  /* opt_pass methods: */
  virtual bool gate (function *)
    {
      return optimize >= 3 && flag_ipa_array_dse;
    }

  virtual unsigned int execute (function *) { return do_array_dse (); }

}; // class pass_ipa_array_dse

} // anon namespace

simple_ipa_opt_pass *
make_pass_ipa_array_dse (gcc::context *ctxt)
{
  return new pass_ipa_array_dse (ctxt);
}
