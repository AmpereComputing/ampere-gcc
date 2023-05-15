/* IPA optimization to transform global malloced or static scalar
   variable to be specific function local.
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
#include "tree.h"
#include "gimple.h"
#include "gimple-iterator.h"
#include "ssa.h"
#include "tree-pass.h"
#include "tree-cfg.h"
#include "gimplify.h"
#include "gimple-pretty-print.h"
#include "tree-into-ssa.h"
#include "ipa-utils.h"
#include "fold-const.h"
#include "tree-dfa.h"
#include "cfgloop.h"

static bool
dominated_by_p (enum cdi_direction dir, gimple *stmt0, gimple *stmt1)
{
  basic_block bb0 = gimple_bb (stmt0);
  basic_block bb1 = gimple_bb (stmt1);

  if (bb0 == bb1)
    {
      renumber_gimple_stmt_uids_in_blocks (&bb0, 1);

      if (dir == CDI_DOMINATORS)
	return stmt0->uid > stmt1->uid;
      else
	return stmt0->uid < stmt1->uid;
    }

  return dominated_by_p (dir, bb0, bb1);
}

enum {
  NF_INIT_LOOP = 1,
  NF_INIT_DOM  = 2
};

static inline bool
node_has_flag (cgraph_node *node, int flag)
{
  intptr_t aux_flags = (intptr_t) node->aux;

  return aux_flags & flag;
}

static inline bool
node_set_flag (cgraph_node *node, int flag)
{
  if (node_has_flag (node, flag))
    return false;

  intptr_t aux_flags = (intptr_t) node->aux;

  node->aux = (void *) (aux_flags | flag);
  return true;
}

static gimple *
memory_alloc_stmt (gimple *stmt)
{
  if (!gimple_call_builtin_p (stmt, BUILT_IN_NORMAL))
    {
      if (!gimple_assign_single_p (stmt))
	return NULL;

      tree rhs = gimple_assign_rhs1 (stmt);

      if (TREE_CODE (rhs) != SSA_NAME || !has_single_use (rhs))
	return NULL;

      stmt = SSA_NAME_DEF_STMT (rhs);
      if (!gimple_call_builtin_p (stmt, BUILT_IN_NORMAL))
	return NULL;
    }

  tree callee = gimple_call_fndecl (stmt);

  switch (DECL_FUNCTION_CODE (callee))
    {
    case BUILT_IN_MALLOC:
    case BUILT_IN_CALLOC:
      return stmt;

    default:
      return NULL;
    }
}

static bool
memory_free_stmt_p (gimple *stmt)
{
  tree callee = gimple_call_fndecl (stmt);

  if (DECL_FUNCTION_CODE (callee) == BUILT_IN_FREE)
    return true;

  return false;
}

static bool
is_scalar_memop_on_alloc_address (tree ref_val, gimple *use_stmt)
{
  if (gimple_has_volatile_ops (use_stmt))
    return false;

  if (!gimple_assign_load_p (use_stmt) && !gimple_store_p (use_stmt))
    return false;

  tree type = TREE_TYPE (ref_val);
  tree lhs = gimple_get_lhs (use_stmt);
  tree memref;
  HOST_WIDE_INT offset, size;
  bool reverse;

  gcc_checking_assert (POINTER_TYPE_P (type));

  if (gimple_store_p (use_stmt))
    /*  *var = ... =  */
    memref = lhs;
  else
    /*  ... = *var  */
    memref = gimple_assign_rhs1 (use_stmt);

  memref = get_ref_base_and_extent_hwi (memref, &offset, &size, &reverse);

  if (!memref || offset || TREE_CODE (memref) != MEM_REF
      || !operand_equal_p (TREE_OPERAND (memref, 0), ref_val)
      || !integer_zerop (TREE_OPERAND (memref, 1))
      || !types_compatible_p (TREE_TYPE (lhs), TREE_TYPE (type)))
    return false;

  ssa_op_iter iter;
  tree use;
  int use_count = 0;

  /* Exclude address-escape case like *var = var  */
  FOR_EACH_SSA_TREE_OPERAND (use, use_stmt, iter, SSA_OP_USE)
    if (operand_equal_p (use, ref_val))
      use_count++;

  if (use_count > 1)
    return false;

  return true;
}

static inline bool
stmt_in_loop_p (gimple *stmt)
{
  basic_block bb = gimple_bb (stmt);

  gcc_checking_assert (bb);

  if (loop_outer (bb->loop_father) || (bb->flags & BB_IRREDUCIBLE_LOOP))
    return false;

  return true;
}

static inline bool
stmts_in_same_regular_loop_p (gimple *stmt1, gimple *stmt2)
{
  basic_block bb1 = gimple_bb (stmt1);
  basic_block bb2 = gimple_bb (stmt2);

  gcc_checking_assert (bb1 && bb2);

  if (bb1->loop_father != bb2->loop_father
      || (bb1->flags & BB_IRREDUCIBLE_LOOP)
      || (bb2->flags & BB_IRREDUCIBLE_LOOP))
    return false;

  return true;
}

static bool
ipa_dominated_by_p (cgraph_node *callee_node,
		    vec<gimple *> *stmts_in_callee,
		    cgraph_node *caller_node,
		    gimple *stmt_in_caller, bool dom_p)
{
  cgraph_node *node;
  auto_vec<gimple *, 1> stmt_as_vec;
  vec<gimple *> *stmts_to_check;

  if (caller_node != callee_node)
    {
      gimple *call_stmt = NULL;

      for (node = callee_node; ; )
	{
	  if (node->used_from_other_partition || node->cannot_return_p ()
	      || node->get_availability () != AVAIL_LOCAL
	      || node->has_aliases_p ())
	    return false;

	  cgraph_edge *cs = node->callers;

	  /* Now we only allow function that is called only once by other
	     function (non-recursive call).  */
	  if (!cs || cs->next_caller || cs->caller == node)
	    return false;

	  call_stmt = cs->call_stmt;
	  node = cs->caller;

	  if (node == caller_node)
	    break;

	  struct function *node_fun = DECL_STRUCT_FUNCTION (node->decl);

	  if (!single_succ_p (ENTRY_BLOCK_PTR_FOR_FN (node_fun)))
	    return false;

	  if (node_set_flag (node, NF_INIT_LOOP))
	    {
	      cfun_context ctx (node);

	      loop_optimizer_init (AVOID_CFG_MODIFICATIONS);
	      mark_irreducible_loops ();
	    }

	  /* Once function is repeated, side effect made to allocated variable
	     will be non local.  */
	  if (stmt_in_loop_p (call_stmt))
	    return false;
	}

      gcc_checking_assert (call_stmt);

      if (!stmts_in_same_regular_loop_p (stmt_in_caller, call_stmt))
	return false;

      stmt_as_vec.quick_push (call_stmt);
      stmts_to_check = &stmt_as_vec;
    }
  else
    {
      gcc_checking_assert (stmts_in_callee);

      stmts_to_check = stmts_in_callee;
    }

  cfun_context caller_ctx (caller_node);

  if (node_set_flag (caller_node, NF_INIT_DOM))
    {
      calculate_dominance_info (CDI_DOMINATORS);
      calculate_dominance_info (CDI_POST_DOMINATORS);
    }

  auto dir = dom_p ? CDI_DOMINATORS : CDI_POST_DOMINATORS;

  for (auto stmt : *stmts_to_check)
    {
      if (!dominated_by_p (dir, stmt, stmt_in_caller))
	return false;
    }

  return true;
}

static void
remove_referring_stmt (gimple *stmt, bool check_alloc = false)
{
  gimple *alloc_stmt = stmt;
  gimple_stmt_iterator gsi;

  if (check_alloc)
    {
      alloc_stmt = memory_alloc_stmt (stmt);
      if (!alloc_stmt)
	alloc_stmt = stmt;
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "Remove statement%s:\n",
	     alloc_stmt != stmt ? "s" : "");

  if (alloc_stmt != stmt)
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	print_gimple_stmt (dump_file, alloc_stmt, 0, TDF_VOPS);

      gsi = gsi_for_stmt (alloc_stmt);
      unlink_stmt_vdef (alloc_stmt);
      gsi_remove (&gsi, true);
      release_defs (alloc_stmt);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      print_gimple_stmt (dump_file, stmt, 0, TDF_VOPS);
      fprintf (dump_file, "\n");
    }

  gsi = gsi_for_stmt (stmt);
  unlink_stmt_vdef (stmt);
  gsi_remove (&gsi, true);
  release_defs (stmt);
}

static void
replace_store_with_ssa (gimple *stmt, tree var_ssa)
{
  gcc_checking_assert (gimple_store_p (stmt));

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Update store statement:\n");
      print_gimple_stmt (dump_file, stmt, 0, TDF_VOPS);
    }

  create_new_def_for (var_ssa, stmt, NULL);
  update_stmt (stmt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "->\n");
      print_gimple_stmt (dump_file, stmt, 0, TDF_VOPS);
      fprintf (dump_file, "\n");
    }
}

static void
replace_load_with_ssa (gimple *stmt, tree var_ssa)
{
  gcc_checking_assert (gimple_assign_load_p (stmt));

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Update load statement:\n");
      print_gimple_stmt (dump_file, stmt, 0, TDF_VOPS);
    }

  gimple_assign_set_rhs1 (stmt, var_ssa);
  update_stmt (stmt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "->\n");
      print_gimple_stmt (dump_file, stmt, 0, TDF_VOPS);
      fprintf (dump_file, "\n");
    }
}

static void
rewrite_load_from_alloc_scalar (gimple *stmt, tree var_ssa)
{
  tree ref_val = gimple_assign_lhs (stmt);
  gimple *use_stmt;
  imm_use_iterator use_iter;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Rewrite reference:\n");
      print_gimple_stmt (dump_file, stmt, 0, TDF_VOPS);
      fprintf (dump_file, "\n");
    }

  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, ref_val)
    {
      if (gimple_store_p (use_stmt))
	replace_store_with_ssa (use_stmt, var_ssa);
      else if (gimple_assign_load_p (use_stmt))
	replace_load_with_ssa (use_stmt, var_ssa);
      else
	{
	  gcc_checking_assert (is_gimple_debug (use_stmt)
			       || memory_free_stmt_p (use_stmt));
	  remove_referring_stmt (use_stmt);
	}
    }
  remove_referring_stmt (stmt);
}

static void
rewrite_alloc_scalar (cgraph_node *refer_node, varpool_node *var,
		      vec<gimple *> &stmts_to_remove_ref)
{
  tree type = TREE_TYPE (TREE_TYPE (var->decl));
  const char *name = get_name (var->decl);
  tree var_ssa = make_temp_ssa_name (type, NULL, name ? name : "tmp");
  gimple *init = gimple_build_assign (var_ssa, build_zero_cst (type));
  ipa_ref *ref;
  bool has_alloc = false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Localize malloc memory access *");
      print_generic_expr (dump_file, var->decl);
      fprintf (dump_file, " in %s()\n\n", refer_node->name ());
    }

  for (unsigned i = 0; var->iterate_referring (i, ref); i++)
    {
      if (dyn_cast <cgraph_node *> (ref->referring) != refer_node)
	continue;

      if (ref->use == IPA_REF_STORE)
	{
	  gimple_stmt_iterator gsi = gsi_for_stmt (ref->stmt);

	  gcc_checking_assert (!has_alloc);
	  gcc_checking_assert (memory_alloc_stmt (ref->stmt));

	  has_alloc = true;
	  gsi_insert_after (&gsi, init, GSI_SAME_STMT);
	  remove_referring_stmt (ref->stmt, true);
	}
      else
	{
	  gcc_checking_assert (ref->use == IPA_REF_LOAD);
	  rewrite_load_from_alloc_scalar (ref->stmt, var_ssa);
	}
      stmts_to_remove_ref.safe_push (ref->stmt);
    }

  if (!has_alloc)
    {
      basic_block entry_bb = single_succ (ENTRY_BLOCK_PTR_FOR_FN (cfun));
      gimple_stmt_iterator gsi = gsi_start_nondebug_after_labels_bb (entry_bb);

      gsi_insert_before (&gsi, init, GSI_SAME_STMT);
    }
}

static void
rewrite_static_scalar (cgraph_node *refer_node, varpool_node *var,
		       gimple *init, gimple *fini, bool remove,
		       vec<gimple *> &stmts_to_remove_ref)
{
  tree type = TREE_TYPE (var->decl);
  const char *name = get_name (var->decl);
  tree var_ssa = NULL_TREE;
  ipa_ref *ref;

  if (!remove)
    var_ssa = make_temp_ssa_name (type, NULL, name ? name : "tmp");

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Localize variable access ");
      print_generic_expr (dump_file, var->decl);
      fprintf (dump_file, " in %s()\n\n", refer_node->name ());
    }

  if (init)
    {
      basic_block entry_bb = single_succ (ENTRY_BLOCK_PTR_FOR_FN (cfun));
      gimple_stmt_iterator gsi = gsi_start_nondebug_after_labels_bb (entry_bb);

      gcc_checking_assert (var_ssa);

      gimple_set_lhs (init, var_ssa);
      gsi_insert_before (&gsi, init, GSI_SAME_STMT);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Insert init statement:\n");
	  print_gimple_stmt (dump_file, init, 0, TDF_VOPS);
	  fprintf (dump_file, "\n");
	}

      if (fini)
	{
	  edge e;
	  edge_iterator ei;
	  bool fini_used = false;

	  gcc_checking_assert (memory_free_stmt_p (fini));

	  FOR_EACH_EDGE (e, ei, EXIT_BLOCK_PTR_FOR_FN (cfun)->preds)
	    {
	      greturn *ret = safe_dyn_cast<greturn *> (last_stmt (e->src));

	      if (!ret)
		continue;

	      if (fini_used)
		fini = gimple_copy (fini);
	      else
		fini_used = true;

	      gsi = gsi_for_stmt (ret);
	      gimple_call_set_arg (fini, 0, var_ssa);
	      gsi_insert_before (&gsi, fini, GSI_SAME_STMT);

	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "Insert fini statement:\n");
		  print_gimple_stmt (dump_file, fini, 0, TDF_VOPS);
		  fprintf (dump_file, "\n");
		}
	    }
	}
    }

  for (unsigned i = 0; var->iterate_referring (i, ref); i++)
    {
      if (dyn_cast <cgraph_node *> (ref->referring) != refer_node)
	continue;

      if (ref->use == IPA_REF_STORE)
	{
	  if (remove)
	    remove_referring_stmt (ref->stmt, true);
	  else
	    replace_store_with_ssa (ref->stmt, var_ssa);
	}
      else
	{
	  gcc_checking_assert (ref->use == IPA_REF_LOAD);

	  if (remove)
	    {
	      tree ref_val = gimple_assign_lhs (ref->stmt);
	      gimple *use_stmt;
	      imm_use_iterator use_iter;

	      FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, ref_val)
		{
		  gcc_checking_assert (memory_free_stmt_p (use_stmt));
		  remove_referring_stmt (use_stmt);
		}
	      remove_referring_stmt (ref->stmt);
	    }
	  else
	    replace_load_with_ssa (ref->stmt, var_ssa);
	}

      stmts_to_remove_ref.safe_push (ref->stmt);
    }
}

static bool
scalar_type_p (tree type)
{
  if (INTEGRAL_TYPE_P (type) || POINTER_TYPE_P (type)
      || SCALAR_FLOAT_TYPE_P (type))
    return true;
  return false;
}

static gimple *
copy_call_without_location (gimple *stmt)
{
  tree callee = unshare_expr_without_location (gimple_call_fndecl (stmt));
  auto_vec<tree> args;

  for (unsigned i = 0; i < gimple_call_num_args (stmt); i++)
    {
      tree arg = gimple_call_arg (stmt, i);
      args.safe_push (unshare_expr_without_location (arg));
    }

  return gimple_build_call_vec (callee, args);
}

#define HAS_ST_ANY   1
#define HAS_ST_DOM   2
#define HAS_ST_PDOM  4

static bool
localize_var (cgraph_node *refer_node, varpool_node *var)
{
  if (var->aux == (void *) -1)
    return false;

  var->aux = (void *) -1;

  if (DECL_EXTERNAL (var->decl) || var->in_other_partition
      || !var->can_remove_if_no_refs_p ())
    return false;

  tree type = TREE_TYPE (var->decl);

  /* Only care about scalar variable.  */
  if (!scalar_type_p (type))
    return false;

  ipa_ref *ref = NULL;
  ipa_ref *alloc_ref = NULL;
  ipa_ref *free_ref = NULL;
  bool is_scalar_alloc = false;
  int store_state = 0;
  tree store_value = NULL_TREE;
  gimple *alloc_stmt = NULL;
  gimple *free_stmt = NULL;
  unsigned i;

  for (i = 0; var->iterate_referring (i, ref); i++)
    {
      cgraph_node *node = dyn_cast <cgraph_node *> (ref->referring);

      if (!node)
	return false;

      gimple *ref_stmt = ref->stmt;

      if (!ref_stmt || gimple_has_volatile_ops (ref_stmt))
	return false;

      /* Identify patterns as:

	 1. scalar_type *var_ptr;  // static variable

	    ...

	    var_ptr = (scalar_type *) malloc (sizeof (scalar_type *));

	    *var_ptr = . ;

	    ...

	    . = *var_ptr;

	    free (var_ptr);

	 Except in malloc and free, the variable could only be used as address
	 to access memory, otherwise the address returned by malloc might escape
	 somewhere.  Actually, use in condition expression also does not cause
	 escape, but we do not support it now.

	2. scalar_type var;   // static variable

	   fn1 ()
	   {
	     ...
	     . = var;
	     ...
	   }

	   fn2 ()
	   {
	     ...
	     var = CST;

	     fn1 ();
	     ...
	   }

	   or

	   scalar_type var = CST;

	   fn3 ()
	   {
	     ...
	     fn1 ();

	     var = CST;
	   }

	 If we know that a static variable always keep constant when entering f2(),
	 the variable could be changed to a local variable in the function.  */
      if (ref->use == IPA_REF_STORE)
	{
	  if (alloc_ref)
	    return false;

	  if (!gimple_store_p (ref_stmt)
	      || !operand_equal_p (var->decl, gimple_get_lhs (ref_stmt)))
	    return false;

	  if ((alloc_stmt = memory_alloc_stmt (ref_stmt)))
	    {
	      if (store_state)
		return false;

	      tree callee = gimple_call_fndecl (alloc_stmt);
	      tree alloc_size = NULL_TREE;

	      switch (DECL_FUNCTION_CODE (callee))
		{
		case BUILT_IN_MALLOC:
		  alloc_size = gimple_call_arg (alloc_stmt, 0);
		  if (!is_gimple_ip_invariant (alloc_size))
		    return false;
		  break;

		case BUILT_IN_CALLOC:
		  {
		    tree arg0 = gimple_call_arg (alloc_stmt, 0);
		    tree arg1 = gimple_call_arg (alloc_stmt, 1);

		    if (TREE_CODE (arg0) == INTEGER_CST
			&& TREE_CODE (arg1) == INTEGER_CST)
		      alloc_size = size_binop (MULT_EXPR, arg0, arg1);
		    else if (!is_gimple_ip_invariant (arg0)
			     || !is_gimple_ip_invariant (arg1))
		      return false;
		    break;
		  }

		default:
		  return false;
		}

	      gcc_checking_assert (POINTER_TYPE_P (type));

	      if (scalar_type_p (TREE_TYPE (type)))
		{
		  tree elem_size = TYPE_SIZE_UNIT (TREE_TYPE (type));

		  if (alloc_size && tree_int_cst_le (elem_size, alloc_size))
		    is_scalar_alloc = true;
		}

	      alloc_ref = ref;
	    }
	  else
	    {
	      if (node != refer_node)
		{
		  if (!gimple_assign_single_p (ref_stmt))
		    return false;

		  tree rhs = gimple_assign_rhs1 (ref_stmt);

		  if (!is_gimple_ip_invariant (rhs))
		    return false;

		  if (!store_value)
		    store_value = rhs;
		  else if (!operand_equal_p (store_value, rhs))
		    return false;

		  if (store_state & HAS_ST_DOM)
		    ;
		  else if (ipa_dominated_by_p (refer_node, NULL, node,
					       ref_stmt, true))
		    store_state |= HAS_ST_DOM;
		  else if (store_state & HAS_ST_PDOM)
		    ;
		  else if (ipa_dominated_by_p (refer_node, NULL, node,
					       ref_stmt, false))
		    store_state |= HAS_ST_PDOM;
		}

	      store_state |= HAS_ST_ANY;
	    }
	}
    }

  auto_vec<gimple *, 8> stmts_to_check;
  bool has_load = false;

  for (i = 0; var->iterate_referring (i, ref); i++)
    {
      gimple *ref_stmt = ref->stmt;

      if (ref->use == IPA_REF_LOAD)
	{
	  if (!gimple_assign_load_p (ref_stmt))
	    return false;

	  if (!operand_equal_p (var->decl, gimple_assign_rhs1 (ref_stmt)))
	    return false;

	  tree ref_val = gimple_assign_lhs (ref_stmt);

	  if (TREE_CODE (ref_val) != SSA_NAME)
	    return false;

	  gimple *use_stmt;
	  imm_use_iterator use_iter;
	  bool check_load = false;

	  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, ref_val)
	    {
	      if (is_gimple_debug (use_stmt))
		continue;

	      if (gimple_call_builtin_p (use_stmt, BUILT_IN_NORMAL))
		{
		  if (free_ref)
		    return false;

		  if (alloc_ref)
		    {
		      tree callee = gimple_call_fndecl (use_stmt);

		      if (DECL_FUNCTION_CODE (callee) == BUILT_IN_FREE)
			{
			  tree arg0 = gimple_call_arg (use_stmt, 0);

			  if (!operand_equal_p (arg0, ref_val))
			    return false;

			  if (alloc_ref->referring != ref->referring)
			    return false;

			  free_ref = ref;
			  free_stmt = use_stmt;
			  continue;
			}

		      is_scalar_alloc = false;
		    }
		}
	      else if (is_scalar_alloc
		       && !is_scalar_memop_on_alloc_address (ref_val, use_stmt))
		is_scalar_alloc = false;

	      /* Found normal load reference in other function.  */
	      check_load = true;
	    }

	  if (check_load)
	    {
	      cgraph_node *node = dyn_cast <cgraph_node *> (ref->referring);

	      if (node != refer_node)
		return false;

	      has_load = true;

	      if (alloc_ref)
		stmts_to_check.safe_push (ref_stmt);
	    }
	}
      else if (ref->use != IPA_REF_STORE)
	return false;
    }

  auto_vec<gimple *, 8> stmts_to_remove_ref;

  if (alloc_ref)
    {
      if (!free_ref)
	return false;

      cgraph_node *alloc_node = as_a <cgraph_node *> (alloc_ref->referring);

      /* Ensure dominance constraint for replacement SSA to be created.  */
      if (!ipa_dominated_by_p (refer_node, &stmts_to_check, alloc_node,
			       alloc_stmt, true))
	return false;

      /* Side effect made to the allocated variable should not escape this
	 function.  And if the variable is local to the function, this check
	 could be removed.  */
      if (!ipa_dominated_by_p (refer_node, &stmts_to_check, alloc_node,
			       free_stmt, false))
	return false;

      if (alloc_node == refer_node
	  && !stmts_in_same_regular_loop_p (alloc_stmt, free_stmt))
	return false;

      {
	cfun_context alloc_ctx (alloc_node);

	if (!dominated_by_p (CDI_DOMINATORS, free_stmt, alloc_stmt)
	    || !dominated_by_p (CDI_POST_DOMINATORS, alloc_stmt, free_stmt))
	return false;
      }

      if (is_scalar_alloc)
	rewrite_alloc_scalar (refer_node, var, stmts_to_remove_ref);
      else
	{
	  gimple *init = NULL;
	  gimple *fini = NULL;

	  if (refer_node != alloc_node)
	    {
	      init = copy_call_without_location (alloc_stmt);
	      fini = copy_call_without_location (free_stmt);
	    }

	  rewrite_static_scalar (refer_node, var, init, fini, !has_load,
				 stmts_to_remove_ref);
	}
    }
  else
    {
      gimple *init = NULL;

      if (has_load)
	{
	  if (store_state & HAS_ST_DOM)
	    ;
	  else if (store_state & HAS_ST_PDOM)
	    {
	      tree decl_init = DECL_INITIAL (var->decl);

	      if (!decl_init || !operand_equal_p (store_value, decl_init))
		return false;
	    }
	  else
	    return false;

	  init = gimple_build_assign (NULL_TREE, store_value);
	}

      rewrite_static_scalar (refer_node, var, init, NULL, !has_load,
			     stmts_to_remove_ref);
    }

  for (auto stmt : stmts_to_remove_ref)
    refer_node->remove_stmt_references (stmt);

  var->aux = (void *) 1;
  return true;
}

/* Execute the driver for IPA variable localization.  */
static unsigned int
ipa_localize_var (void)
{
  cgraph_node **order = XNEWVEC (cgraph_node *, symtab->cgraph_count);
  int nnodes = ipa_reverse_postorder (order);
  cgraph_node *node;
  varpool_node *var;

  gcc_assert (nnodes == symtab->cgraph_count);

  FOR_EACH_VARIABLE (var)
    var->aux = (void *) 0;

  FOR_EACH_FUNCTION (node)
    node->aux = (void *) 0;

  for (int i = nnodes - 1; i >= 0; i--)
    {
      cgraph_node *node = order[i];

      if (!node->has_gimple_body_p () || node->inlined_to)
	{
	  gcc_checking_assert (!node->aux);
	  continue;
	}

      ipa_ref *ref = NULL;
      auto_vec<varpool_node *> ref_vars;
      bool changed = false;

      for (unsigned j = 0; node->iterate_reference (j, ref); j++)
	{
	  var = dyn_cast<varpool_node *> (ref->referred);

	  if (var && !ref_vars.contains (var))
	    ref_vars.safe_push (var);
	}

      cfun_context ctx (node);

      for (auto var : ref_vars)
	changed |= localize_var (node, var);

      if (changed)
	update_ssa (TODO_update_ssa);

      if (node_has_flag (node, NF_INIT_LOOP))
	loop_optimizer_finalize ();

      if (node_has_flag (node, NF_INIT_DOM))
	{
	  free_dominance_info (CDI_DOMINATORS);
	  free_dominance_info (CDI_POST_DOMINATORS);
	}

      node->aux = (void *) 0;
    }

  FOR_EACH_VARIABLE (var)
    var->aux = (void *) 0;

  return 0;
}

namespace {

const pass_data pass_data_ipa_localize_var =
{
  SIMPLE_IPA_PASS, /* type */
  "localize-var",  /* name */
  OPTGROUP_NONE,   /* optinfo_flags */
  TV_IPA_LOCALIZE_VAR, /* tv_id */
  0, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_ipa_localize_var : public simple_ipa_opt_pass
{
public:
  pass_ipa_localize_var (gcc::context *ctxt)
    : simple_ipa_opt_pass (pass_data_ipa_localize_var, ctxt)
  {}

  /* opt_pass methods: */
  virtual bool gate (function *)
    {
      return optimize >= 3 && flag_ipa_localize_var;
    }

  virtual unsigned int execute (function *) { return ipa_localize_var (); }

}; // class pass_ipa_localize_var

} // anon namespace

simple_ipa_opt_pass *
make_pass_ipa_localize_var (gcc::context *ctxt)
{
  return new pass_ipa_localize_var (ctxt);
}
