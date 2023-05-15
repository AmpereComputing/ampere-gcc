/* Loop depth reduction optimization for the GNU compiler.
   Copyright (C) 2022-2023 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3, or (at your option) any
later version.

GCC is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
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
#include "tree-cfgcleanup.h"
#include "gimple.h"
#include "cfghooks.h"
#include "tree-pass.h"
#include "ssa.h"
#include "gimple-pretty-print.h"
#include "fold-const.h"
#include "cfganal.h"
#include "gimplify.h"
#include "gimple-iterator.h"
#include "tree-cfg.h"
#include "tree-inline.h"
#include "cfgloop.h"
#include "tree-ssa-loop.h"
#include "tree-ssa-loop-niter.h"
#include "tree-ssa-loop-ivopts.h"
#include "tree-scalar-evolution.h"

/* The info for a loop that is to do LRO.  */

class lro_loop_info
{
public:
  /* The inner loop for checking if a value is in a set.  */
  loop_p inner_loop;

  /* The outer loop containing the inner_loop.  */
  loop_p outer_loop;

  /* Basic blocks in the inner_loop.  */
  basic_block *inner_bbs;

  /* Basic blocks in the outer_loop.  */
  basic_block *outer_bbs;

  /* All blocks in the inner_loop.  */
  basic_block bb1_in_il, bb2_in_il;
  edge entry_edge_il;

  /* The entry block of the outer_loop.  */
  basic_block ol_entry_bb, bb_before_il;
  /* Blocks in outer_loop after inner_loop.  */
  basic_block bb1_after_il, bb2_after_il, bb3_after_il;

  /* The number of iterations, entry and exit edge of outer loop.  */
  tree ol_niter;
  edge ol_entry_edge, ol_exit_edge;

  /* aset: use array as set in the inner_loop.  */
  tree aset_array, aset_size;
  /* The aset write stmt to append the unique element in the array.  */
  gimple *aset_wt_stmt;
  /* The aset checks if the lro_idx can be found like:
       lro_idx = lro_idx_memref;  // some kind of memory access
       found = aset.add(lro_idx); */
  tree lro_idx_memref;

  /* The target write statement (like lro_array[idx] = val) determined by the
     aset find result. After transformation, the idx and write val of
     lro_wt_stmt will be stored/loaded as temps.  */
  auto_vec<gimple *> lro_wt_stmts;

  /* All memory reference statements except those loads from and stores to aset
     and lro arrays.  */
  auto_vec<gimple *> other_memrefs;

  lro_loop_info ()
    : inner_loop (NULL), outer_loop (NULL), inner_bbs (NULL), outer_bbs (NULL),
      entry_edge_il (NULL), ol_entry_bb (NULL), bb_before_il (NULL),
      ol_niter (NULL_TREE), ol_entry_edge (NULL), ol_exit_edge (NULL),
      aset_array (NULL_TREE), aset_size (NULL_TREE), aset_wt_stmt (NULL)
  {}

  ~lro_loop_info ()
  {
    if (inner_bbs)
      free (inner_bbs);

    if (outer_bbs)
      free (outer_bbs);
  }

  bool check_loop_structure (loop_p);
  bool analyze_loop ();
  bool check_inner_loop ();
  bool check_bb1_in_inner_loop (tree);
  bool check_bb2_in_inner_loop (tree &);
  bool check_outer_loop ();
  bool check_blocks_before_inner_loop ();
  bool check_bb1_after_inner_loop ();
  bool check_bb2_after_inner_loop ();
  bool check_bb3_after_inner_loop ();

  void transform_loop ();
  void reduce_inner_loop ();
  void split_outer_loop ();

  bool check_non_alias ();
  bool check_profitable1 ();
  bool check_profitable2 ();
  void dump_info ();
};

static unsigned lro_name_suffix_id = 0;

#define TEST(cond) \
  if (!(cond)) \
    return false;

#define TEST_WITH_MSG(cond, message) \
  if (!(cond)) \
    { \
      if (dump_file && (dump_flags & TDF_DETAILS)) \
	fprintf (dump_file, "[FAIL] %s\n", (message)); \
      return false; \
    }

/* Return true if the rhs code of STMT is the same to CODE.  */

static bool
gimple_assign_rhs_code_p (gimple *stmt, enum tree_code code)
{
  TEST (stmt != NULL && is_gimple_assign (stmt))
  return gimple_assign_rhs_code (stmt) == code;
}

/* Return true if VAR is ssa. */

static bool
ssa_p (tree var)
{
  return TREE_CODE (var) == SSA_NAME;
}

/* Return true if VAR is ssa and it has single nondebug use. */

static bool
ssa_has_single_use_p (tree var)
{
  return TREE_CODE (var) == SSA_NAME && has_single_use (var);
}

/* Return the define stmt of VAR if it is ssa, otherwise return NULL.  */

static gimple *
get_ssa_def_stmt (tree var)
{
  gcc_checking_assert (var != NULL_TREE);
  return ssa_p (var) ? SSA_NAME_DEF_STMT (var) : NULL;
}

/* Set all stmts in BB as not visited.  */

static void
set_all_stmts_not_visited (basic_block bb)
{
  gimple_stmt_iterator si;
  for (si = gsi_start_phis (bb); !gsi_end_p (si); gsi_next (&si))
    gimple_set_visited (gsi_stmt (si), false);
  for (si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
    gimple_set_visited (gsi_stmt (si), false);
}

/* Return false if STMT is NULL or STMT is not in block BB, otherwise return
   true and set STMT as visited.  */

static bool
visit_gs (gimple *stmt, basic_block bb = NULL)
{
  if (!stmt)
    return false;
  if (bb && gimple_bb (stmt) != bb)
    return false;
  gimple_set_visited (stmt, true);
  return true;
}

/* Hepler functions to check if STMT is load/store of ARRAY_REF.  */
static bool
gimple_load_from_array_ref_p (gimple *stmt)
{
  if (!gimple_assign_rhs_code_p (stmt, ARRAY_REF))
    return false;
  return true;
}
static bool
gimple_store_to_array_ref_p (gimple *stmt)
{
  TEST (gimple_assign_single_p (stmt))
  tree lhs = gimple_assign_lhs (stmt);
  TEST (TREE_CODE (lhs) == ARRAY_REF)
  return true;
}
static bool
gimple_load_from_mem_p (gimple *stmt)
{
  TEST (stmt != NULL && is_gimple_assign (stmt))
  switch (gimple_assign_rhs_code (stmt))
    {
    case ARRAY_REF:
    case ARRAY_RANGE_REF:
    case MEM_REF:
    case COMPONENT_REF:
      return true;
    default:
      return false;
    }
}

/* Get the last none debug stmt of BB.  If COND_P is true, return the condition
   stmt or NULL if not found.  */

static gimple *
get_bb_last_stmt (basic_block bb, bool cond_p = false)
{
  gimple_stmt_iterator gsi = gsi_last_bb (bb);
  while (!gsi_end_p (gsi))
    {
      gimple *last_stmt = gsi_stmt (gsi);

      if (is_gimple_debug (last_stmt))
	gsi_prev (&gsi);
      else if (cond_p)
	return gimple_code (last_stmt) == GIMPLE_COND ? last_stmt : NULL;
      else
	return last_stmt;
    }
  return NULL;
}

/* Return the phi stmt, if the BB has only one phi stmt.  */

static gphi *
get_single_phi (basic_block bb)
{
  gphi_iterator gpi;
  gphi *phi = NULL;
  for (gpi = gsi_start_nonvirtual_phis (bb); !gsi_end_p (gpi);
       gsi_next_nonvirtual_phi (&gpi))
    {
      if (phi)
	return NULL;
      phi = gpi.phi ();
    }

  return phi;
}

/* Return true if STMT is like: lhs = rhs1 + 1.
   If VAR is not NULL, check if it is the rhs1, otherwise set it to rhs1.  */

static bool
is_accumulation_one (gimple *stmt, tree &var)
{
  TEST (gimple_assign_rhs_code_p (stmt, PLUS_EXPR));

  tree rhs1 = gimple_assign_rhs1 (stmt);
  tree rhs2 = gimple_assign_rhs2 (stmt);
  if (var != NULL_TREE)
    {
      TEST (rhs1 == var)
    }
  else
    var = rhs1;

  /* The rhs order is canonicalized (the rhs2 should be const one).  */
  if (!integer_onep (rhs2))
    return false;
  return true;
}

/* Return true if COND is a condition stmt like LHS < RHS.
   If LHS is not NULL, it is tested to be on the left side of LT_EXPR.
   If the cond code is >, LHS and RHS are inverted.  */

static bool
extract_gcond_lt_gt (gimple *gcond, tree &lhs, tree &rhs, edge &e_true,
		     edge &e_false)
{
  tree_code code = gimple_cond_code (gcond);
  TEST (code == LT_EXPR || code == GT_EXPR)

  tree tmp_lhs = gimple_cond_lhs (gcond);
  rhs = gimple_cond_rhs (gcond);
  extract_true_false_edges_from_block (gimple_bb (gcond), &e_true, &e_false);
  if (code == GT_EXPR)
    std::swap (tmp_lhs, rhs);

  if (lhs != NULL_TREE)
    {
      TEST (tmp_lhs == lhs)
    }
  else
    lhs = tmp_lhs;
  return true;
}

/* Return true if COND is a condition stmt like VAR == TARGET.
   If VAR is not NULL, it is checked to be either lhs or rhs.
   If the cond code is !=, E_TRUE and E_FALSE are inverted.  */

static bool
extract_gcond_eq_ne (gimple *gcond, tree &var, tree &target, edge &e_true,
		     edge &e_false)
{
  tree_code code = gimple_cond_code (gcond);
  TEST (code == EQ_EXPR || code == NE_EXPR)

  tree lhs = gimple_cond_lhs (gcond);
  tree rhs = gimple_cond_rhs (gcond);
  if (var != NULL_TREE)
    {
      if (lhs == var)
	target = rhs;
      else
	{
	  TEST (gimple_cond_rhs (gcond) == var)
	  target = lhs;
	}
    }
  else
    {
      var = lhs;
      target = rhs;
    }

  extract_true_false_edges_from_block (gimple_bb (gcond), &e_true, &e_false);
  if (code == NE_EXPR)
    std::swap (e_true, e_false);
  return true;
}

/* Return VAR if it is not defined by a cast.  Otherwise, return the casted
   source or return NULL if the cast has precision loss.
   If CHECK_SINGLE_USE is true, will return NULL if any of the variable is not
   ssa with single use.  */

static tree
backward_from_integer_cast (tree var, bool check_single_use = false)
{
  if (check_single_use && !ssa_has_single_use_p (var))
    return NULL;

  gimple *def_stmt = get_ssa_def_stmt (var);
  if (def_stmt == NULL || !gimple_assign_rhs_code_p (def_stmt, NOP_EXPR))
    {
      return var;
    }

  visit_gs (def_stmt);
  tree rhs = gimple_assign_rhs1 (def_stmt);
  tree lhs_type = TREE_TYPE (var);
  tree rhs_type = TREE_TYPE (rhs);
  if (lhs_type == NULL_TREE || TREE_CODE (lhs_type) != INTEGER_TYPE)
    return NULL_TREE;
  if (rhs_type == NULL_TREE || TREE_CODE (rhs_type) != INTEGER_TYPE)
    return NULL_TREE;
  if (TYPE_PRECISION (lhs_type) < TYPE_PRECISION (rhs_type))
    return NULL_TREE;

  if (check_single_use && !ssa_has_single_use_p (var))
    return NULL;
  return rhs;
}

/* Return true if all stmts have been visited except DEBUG stmt. */

static bool
visited_all_stmts_p (basic_block bb)
{
  gphi_iterator gpi;
  gimple_stmt_iterator gsi;
  for (gpi = gsi_start_nonvirtual_phis (bb); !gsi_end_p (gpi);
       gsi_next_nonvirtual_phi (&gpi))
    {
      TEST (gimple_visited_p (gsi_stmt (gpi)));
    }
  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (is_gimple_debug (stmt))
	continue;
      if (gimple_visited_p (stmt))
	continue;
      if (gimple_nop_p (stmt))
	continue;
      return false;
    }
  return true;
}

/* Return true if bb2 with exit edge is checking the upper bound of IV.  */

bool
lro_loop_info::check_bb2_in_inner_loop (tree &iv)
{
  tree last_iv = NULL_TREE, aset_sz = NULL_TREE;

  /* Find a cond: last_iv < aset_size */
  gimple *gcond;
  edge e_true, e_false;
  TEST (visit_gs (gcond = get_bb_last_stmt (bb2_in_il, /* cond_p */ true)))
  TEST (extract_gcond_lt_gt (gcond, last_iv, aset_sz, e_true, e_false))
  TEST (e_false->dest == bb1_after_il)
  aset_size = aset_sz;

  /* Find a stmt: last_iv = iv + 1; */
  gimple *def_stmt;
  TEST (visit_gs (def_stmt = get_ssa_def_stmt (last_iv), bb2_in_il))
  TEST (is_accumulation_one (def_stmt, iv));

  /* Find a phi: iv = phi(0, last_iv) */
  gphi *phi;
  TEST (visit_gs (phi = get_single_phi (bb1_in_il)))
  TEST (phi == get_ssa_def_stmt (iv))
  gcc_checking_assert (gimple_phi_num_args (phi) == 2);
  unsigned e_latch
    = gimple_phi_arg_edge (phi, 0) == loop_latch_edge (inner_loop) ? 0 : 1;
  TEST (gimple_phi_arg_def (phi, e_latch) == last_iv)
  TEST (integer_zerop (gimple_phi_arg_def (phi, 1 - e_latch)))
  entry_edge_il = gimple_phi_arg_edge (phi, 1 - e_latch);
  return true;
}

static bool
extract_load_from_array_ref (gimple *stmt, tree &array, tree &idx)
{
  TEST (gimple_load_from_array_ref_p (stmt))
  array = TREE_OPERAND (gimple_assign_rhs1 (stmt), 0);
  idx = TREE_OPERAND (gimple_assign_rhs1 (stmt), 1);
  return true;
}

/* Return true if the target BB1 in LRO_INFO is traversing an array to find an
   unique element.  */

bool
lro_loop_info::check_bb1_in_inner_loop (tree iv)
{
  /* Find the gimple cond: aset == lro_idx */
  gimple *gcond;
  tree opnd1 = NULL_TREE, opnd2 = NULL_TREE;
  edge e_true, e_false;
  TEST (visit_gs (gcond = get_bb_last_stmt (bb1_in_il, /* cond_p */ true)))
  TEST (extract_gcond_eq_ne (gcond, opnd1, opnd2, e_true, e_false))
  TEST (e_true->dest == bb1_after_il && e_false->dest == bb2_in_il)

  gimple *load_aset_stmt, *load_lro_idx_stmt;
  /* The loaded values should not be used elsewhere.  */
  TEST (opnd1 = backward_from_integer_cast (opnd1, true))
  TEST (opnd2 = backward_from_integer_cast (opnd2, true))
  TEST (visit_gs (load_aset_stmt = get_ssa_def_stmt (opnd1), bb1_in_il))
  TEST (visit_gs (load_lro_idx_stmt = get_ssa_def_stmt (opnd2), bb1_in_il))

  /* Find a load stmt: aset_elt = aset_array[iv];  */
  tree aset_arr = NULL_TREE, cur_idx = NULL_TREE;
  bool swap_p = false;
  if (extract_load_from_array_ref (load_aset_stmt, aset_arr, cur_idx))
    {
      TEST (cur_idx = backward_from_integer_cast (cur_idx))
      if (cur_idx != iv)
	swap_p = true;
    }
  if (swap_p)
    {
      std::swap (load_aset_stmt, load_lro_idx_stmt);
      TEST (extract_load_from_array_ref (load_aset_stmt, aset_arr, cur_idx))
      TEST (backward_from_integer_cast (cur_idx) == iv)
    }
  aset_array = aset_arr;

  /* Find a load stmt: lro_idx = lro_array[?] */
  TEST (gimple_load_from_mem_p (load_lro_idx_stmt))
  lro_idx_memref = gimple_assign_rhs1 (load_lro_idx_stmt);
  other_memrefs.safe_push (load_lro_idx_stmt);
  return true;
}

/* Return true, if the inner loop is qualified for LRO.  */

bool
lro_loop_info::check_inner_loop ()
{
  set_all_stmts_not_visited (bb1_in_il);
  set_all_stmts_not_visited (bb2_in_il);

  tree iv = NULL_TREE;
  TEST (check_bb2_in_inner_loop (iv))
  TEST (check_bb1_in_inner_loop (iv))

  TEST (visited_all_stmts_p (bb1_in_il));
  TEST (visited_all_stmts_p (bb2_in_il));
  return true;
}

/* Return true if the BB1 after inner loop is to check if the unique element
   is found.  */

bool
lro_loop_info::check_bb1_after_inner_loop ()
{
  gphi *phi;
  TEST (visit_gs (phi = get_single_phi (bb1_after_il)))
  TEST (gimple_phi_num_args (phi) == 3);

  /* Get aset found result.  */
  tree found_in_aset_p = gimple_phi_result (phi);
  TEST (ssa_has_single_use_p (found_in_aset_p))
  for (int i = 0; i < 3; i++)
    {
      edge e = gimple_phi_arg_edge (phi, i);
      tree arg = gimple_phi_arg_def (phi, i);
      if (e->src == bb1_in_il)
	{
	  TEST (integer_nonzerop (arg))
	}
      else
	{
	  TEST (e->src == bb2_in_il || e->src == bb_before_il)
	  TEST (integer_zerop (arg))
	}
    }

  /* Find a cond stmt: if (found_in_aset_p != 0) */
  gimple *gcond;
  tree rhs;
  edge e_true, e_false;
  TEST (visit_gs (gcond = get_bb_last_stmt (bb1_after_il, /* cond_p */ true)))
  TEST (extract_gcond_eq_ne (gcond, found_in_aset_p, rhs, e_true, e_false))
  if (integer_zerop (rhs))
    std::swap (e_true, e_false);

  TEST (e_false->dest == bb2_after_il)
  TEST (e_true->dest == bb3_after_il)
  return true;
}

/* If STMT is a simple calculation statement like: lhs = ssa OP invariant,
   return the rhs1 (i.e. the ssa), otherwise return NULL_TREE.  */

static tree
get_val_from_invar_calc (loop_p loop, gimple *stmt)
{
  if (!is_gimple_assign (stmt) || gimple_num_ops (stmt) != 3)
    return NULL_TREE;
  switch (gimple_assign_rhs_code (stmt))
    {
    case PLUS_EXPR:
    case MINUS_EXPR:
    case MULT_EXPR:
    case MIN_EXPR:
    case MAX_EXPR:
    case BIT_AND_EXPR:
    case BIT_IOR_EXPR:
    case BIT_XOR_EXPR:
    case RSHIFT_EXPR:
    case LSHIFT_EXPR:
      {
	tree rhs1 = gimple_assign_rhs1 (stmt);
	tree rhs2 = gimple_assign_rhs2 (stmt);
	if (expr_invariant_in_loop_p (loop, rhs2))
	  return rhs1;
	else if (expr_invariant_in_loop_p (loop, rhs1))
	  return rhs2;
	break;
      }

    default:
      break;
    }
  return NULL_TREE;
}

/* Return true if the BB2 after inner loop is as expected after not found the
   lro_idx.  See the LRO pattern for more details.  */

bool
lro_loop_info::check_bb2_after_inner_loop ()
{
  auto_vec<gimple *> lro_stores;

  /* Search backward from the last stmt to find all store stmts in the block. */
  gimple *def_stmt;
  TEST (visit_gs (def_stmt = get_bb_last_stmt (bb2_after_il)));
  do
    {
      TEST (gimple_store_to_array_ref_p (def_stmt))
      tree array_ref = gimple_assign_lhs (def_stmt);
      if (operand_equal_p (TREE_OPERAND (array_ref, 0), aset_array))
	{
	  /* One store is for aset, the other stores are for LRO arrays. */
	  TEST (aset_wt_stmt == NULL)
	  aset_wt_stmt = def_stmt;
	}
      else
	lro_stores.safe_push (def_stmt);

      TEST (gimple_vuse (def_stmt))
      TEST (def_stmt = get_ssa_def_stmt (gimple_vuse (def_stmt)))
      if (!gimple_bb (def_stmt) || gimple_bb (def_stmt) != bb2_after_il)
	break;
      visit_gs (def_stmt);
    }
  while (true);
  TEST (aset_wt_stmt != NULL && !lro_stores.is_empty ())

  /* 1. find the aset_array related stmts.  */

  /* The aset value should be stored into the index of current aset_size.  */
  tree aset_array_ref = gimple_assign_lhs (aset_wt_stmt);
  tree aset_idx = TREE_OPERAND (aset_array_ref, 1);
  TEST (backward_from_integer_cast (aset_idx) == aset_size);

  /* The value stored into aset should be the same as lro_idx (i.e. loaded from
     lro_idx_memref).  */
  tree lro_idx = gimple_assign_rhs1 (aset_wt_stmt);
  TEST (lro_idx = backward_from_integer_cast (lro_idx));
  TEST (visit_gs (def_stmt = get_ssa_def_stmt (lro_idx), bb2_after_il))
  TEST (gimple_load_from_mem_p (def_stmt))
  TEST (operand_equal_p (gimple_assign_rhs1 (def_stmt), lro_idx_memref))

  /* 2. find the lro_wt_stmt related stmts.  */

  for (auto wt_stmt : lro_stores)
    {
      /* The lro index should be loaded from lro_idx_memref.  */
      tree lro_array_ref = gimple_assign_lhs (wt_stmt);
      lro_idx = TREE_OPERAND (lro_array_ref, 1);
      TEST (lro_idx = backward_from_integer_cast (lro_idx));
      TEST (visit_gs (def_stmt = get_ssa_def_stmt (lro_idx), bb2_after_il))
      TEST (gimple_load_from_mem_p (def_stmt))
      TEST (operand_equal_p (gimple_assign_rhs1 (def_stmt), lro_idx_memref))

      /* Bypass the cast and calculations with const integers to find an
	 original load stmt from the same lro_array.  */
      tree lro_val = gimple_assign_rhs1 (wt_stmt);
      gimple *lro_rd_stmt = NULL;
      while (true)
	{
	  /* The loaded value and related calculation results should not be used
	     in elsewhere. */
	  TEST (lro_val = backward_from_integer_cast (lro_val, true));
	  TEST (visit_gs (def_stmt = get_ssa_def_stmt (lro_val), bb2_after_il))
	  if (gimple_load_from_array_ref_p (def_stmt))
	    {
	      TEST (lro_rd_stmt == NULL)
	      lro_rd_stmt = def_stmt;
	      /* Should load from the same element of lro_array.  */
	      TEST (operand_equal_p (lro_array_ref,
				     gimple_assign_rhs1 (lro_rd_stmt)))
	      break;
	    }
	  else
	    {
	      TEST (lro_val = get_val_from_invar_calc (outer_loop, def_stmt))
	    }
	}
      TEST (lro_rd_stmt != NULL)

      lro_wt_stmts.safe_push (wt_stmt);
    }

  return true;
}

/* Return true if the BB3 after inner loop (i.e. the latch) is as expected.  */

bool
lro_loop_info::check_bb3_after_inner_loop ()
{
  /* No need to check the gimple condition, which has already been covered by
     the SCEV while checking of number of iterations.  */

  /* Find the phi to get: last_aset_size = phi(new_aset_size, aset_size).  */

  gphi *phi;
  TEST (visit_gs (phi = get_single_phi (bb3_after_il)))
  gcc_checking_assert (gimple_phi_num_args (phi) == 2);

  unsigned idx_from_bb1
    = (bb1_after_il == gimple_phi_arg_edge (phi, 0)->src) ? 0 : 1;
  TEST (aset_size == gimple_phi_arg_def (phi, idx_from_bb1))
  tree new_aset_size = gimple_phi_arg_def (phi, 1 - idx_from_bb1);
  tree last_aset_size = PHI_RESULT (phi);

  /* Find the stmt to calculate: new_aset_size = aset_size + 1;  */
  gimple *def_stmt;
  TEST (visit_gs (def_stmt = get_ssa_def_stmt (new_aset_size), bb2_after_il));
  TEST (is_accumulation_one (def_stmt, aset_size))

  /* Find the phi to get: aset_size = phi(0, last_aset_size);  */

  TEST (visit_gs (def_stmt = get_ssa_def_stmt (aset_size), ol_entry_bb))
  TEST (gimple_code (def_stmt) == GIMPLE_PHI)

  gphi *phi2 = as_a<gphi *> (def_stmt);
  gcc_checking_assert (gimple_phi_num_args (phi2) == 2);
  unsigned e_latch
    = (gimple_phi_arg_edge (phi2, 0) == loop_latch_edge (outer_loop)) ? 0 : 1;
  TEST (aset_size == PHI_RESULT (phi2))
  TEST (last_aset_size == gimple_phi_arg_def (phi2, e_latch))
  TEST (integer_zerop (gimple_phi_arg_def (phi2, 1 - e_latch)))
  return true;
}

void
lro_loop_info::dump_info ()
{
  fprintf (dump_file, "\n> Aset info:");
  fprintf (dump_file, "\n  aset_size: ");
  print_generic_expr (dump_file, aset_size);
  fprintf (dump_file, "\n  aset_array: ");
  print_generic_expr (dump_file, aset_array);

  fprintf (dump_file, "\n> LRO write stmts:\n");
  for (auto lro_wt_stmt : lro_wt_stmts)
    {
      fprintf (dump_file, "  ");
      print_gimple_stmt (dump_file, lro_wt_stmt, 0);
    }

  fprintf (dump_file, "> Other memref stmts:\n");
  for (auto memrefs : other_memrefs)
    {
      fprintf (dump_file, "  ");
      print_gimple_stmt (dump_file, memrefs, 0);
    }
}

/* Return true if STMT belongs to LOOP.  */

static inline bool
stmt_inside_loop_p (const loop_p loop, gimple *stmt)
{
  basic_block bb = gimple_bb (stmt);
  return bb && flow_bb_inside_loop_p (loop, bb);
}

/* Return true if the outer loop entry block is as expected.  */

bool
lro_loop_info::check_blocks_before_inner_loop ()
{
  /* 1. Check condition stmt.  */
  gimple *gcond;
  TEST (visit_gs (gcond = get_bb_last_stmt (bb_before_il, /* cond_p */ true)))
  tree lower_bound = NULL_TREE, aset_sz = NULL_TREE;
  edge e_true, e_false;
  TEST (extract_gcond_lt_gt (gcond, lower_bound, aset_sz, e_true, e_false))
  TEST (integer_zerop (lower_bound) && aset_size == aset_sz)
  TEST (e_true->dest == entry_edge_il->src)
  TEST (e_false->dest == bb1_after_il)

  /* 2. Check other memory operations and collect maybe aliased arrays.  */

  gphi *vphi;
  auto_vec<tree> worklist;
  TEST (vphi = get_virtual_phi (ol_entry_bb))
  worklist.safe_push (gimple_phi_result (vphi));

  gimple *use_stmt;
  imm_use_iterator use_iter;
  do
    {
      tree vdef = worklist.pop ();

      FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, vdef)
	{
	  if (gimple_visited_p (use_stmt)
	      || !stmt_inside_loop_p (outer_loop, use_stmt))
	    continue;
	  visit_gs (use_stmt);

	  switch (gimple_code (use_stmt))
	    {
	    case GIMPLE_ASSIGN:
	      /* Currently only support array load/store.  */
	      if (tree new_vdef = gimple_vdef (use_stmt))
		{
		  worklist.safe_push (new_vdef);
		}
	      other_memrefs.safe_push (use_stmt);
	      break;

	    case GIMPLE_PHI:
	      worklist.safe_push (gimple_phi_result (use_stmt));
	      break;

	    case GIMPLE_CALL:
	      other_memrefs.safe_push (use_stmt);
	      break;

	    default:
	      return false;
	    }
	}
    }
  while (!worklist.is_empty ());
  return true;
}

/* Return true, if the outer loop is qualified for LRO.  */

bool
lro_loop_info::check_outer_loop ()
{
  basic_block *bbs = outer_bbs = get_loop_body (outer_loop);
  for (unsigned i = 0; i < outer_loop->num_nodes; i++)
    {
      if (bbs[i]->loop_father == outer_loop)
	set_all_stmts_not_visited (bbs[i]);
    }

  TEST (check_bb1_after_inner_loop ())
  TEST (check_bb2_after_inner_loop ())
  TEST (check_bb3_after_inner_loop ())
  TEST (check_blocks_before_inner_loop ())

  TEST (visited_all_stmts_p (bb1_after_il))
  TEST (visited_all_stmts_p (bb2_after_il))
  return true;
}

static inline bool
contains_p (tree expr, const poly_offset_int &size, const offset_int &offset)
{
  tree type = TREE_TYPE (expr);

  if (!COMPLETE_TYPE_P (type))
    return false;

  return known_le (size + offset, wi::to_poly_offset (TYPE_SIZE (type)));
}

static inline bool
contains_p (tree expr, tree type, const offset_int &offset = 0)
{
  if (!COMPLETE_TYPE_P (type))
    return false;

  return contains_p (expr, wi::to_poly_offset (TYPE_SIZE (type)), offset);
}

/* Given a memref expression, try to find out a base that is safe to be used
   in alias analysis. In other word, the access undergone by the memref would
   always be inside memory range of the base. This is mostly for array
   reference, because we assume that out-of-bound access to an array is an
   Undefined Behavior.  */

static tree
get_alias_safe_base (tree exp)
{
  tree safe_base = exp;

  while (handled_component_p (exp))
    {
      tree base = TREE_OPERAND (exp, 0);
      tree type = TREE_TYPE (exp);
      enum tree_code code = TREE_CODE (exp);

      if (code == ARRAY_REF || code == ARRAY_RANGE_REF)
	{
	  tree array_type = TREE_TYPE (base);

	  if (TREE_CODE (array_type) != ARRAY_TYPE
	      || !COMPLETE_TYPE_P (array_type))
	    break;

	  if (!contains_p (array_type, type))
	    break;

	  tree domain_type = TYPE_DOMAIN (array_type);

	  if (!domain_type)
	    break;

	  tree lower_bound = TYPE_MIN_VALUE (domain_type);
	  tree upper_bound = TYPE_MAX_VALUE (domain_type);

	  if (!lower_bound)
	    lower_bound = integer_zero_node;

	  /* Do not consider array with zero or unknown dimension.  */
	  if (!upper_bound || TREE_CODE (lower_bound) != INTEGER_CST
	      || TREE_CODE (upper_bound) != INTEGER_CST
	      || tree_int_cst_equal (lower_bound, upper_bound))
	    break;

	  tree index = TREE_OPERAND (exp, 1);

	  /* Find array access with variable index, we assume that the index
	     would not exceed bounds of the array, otherwise this causes
	     Undefined Behavior.  */
	  if (!poly_int_tree_p (index))
	    safe_base = base;
	  else if (TREE_CODE (index) != INTEGER_CST
		   || wi::to_offset (index) < wi::to_offset (lower_bound)
		   || wi::to_offset (index) > wi::to_offset (upper_bound))
	    break;
	}
      else if (code == COMPONENT_REF)
	{
	  if (!contains_p (TREE_OPERAND (exp, 1), type))
	    break;
	}
      else if (code == BIT_FIELD_REF)
	{
	  if (!contains_p (base, wi::to_offset (TREE_OPERAND (exp, 1)),
			   wi::to_offset (TREE_OPERAND (exp, 2))))
	    break;
	}
      else if (code == REALPART_EXPR)
	{
	  if (!contains_p (base, type))
	    break;
	}
      else if (code == IMAGPART_EXPR)
	{
	  if (!contains_p (base, type, wi::to_offset (TYPE_SIZE (type))))
	    break;
	}
      else if (code == VIEW_CONVERT_EXPR)
	{
	  if (!contains_p (base, type))
	    break;
	}
      else
	break;

      exp = base;
    }

  return safe_base;
}

static bool
may_alias_p (tree mem, tree exp)
{
  tree base = exp;

  if (handled_component_p (exp))
    base = get_base_address (exp);

  if (!DECL_P (base) && TREE_CODE (base) != MEM_REF
      && TREE_CODE (base) != TARGET_MEM_REF
      && TREE_CODE (base) != WITH_SIZE_EXPR)
    return false;

  if (!refs_may_alias_p (mem, exp))
    return false;

  if (flag_strict_aliasing)
    {
      tree mem_base = get_alias_safe_base (mem);
      tree exp_base = get_alias_safe_base (exp);

      if ((mem_base != mem || exp_base != exp)
	  && !refs_may_alias_p (mem_base, exp_base))
	return false;
    }

  return true;
}

static bool
store_may_clobber_p (gimple *store, gimple *memref)
{
  tree store_mem = gimple_assign_lhs (store);

  gcc_checking_assert (TREE_CODE (store_mem) != SSA_NAME);
  gcc_checking_assert (gimple_vuse (memref));

  if (auto assign = dyn_cast<gassign *> (memref))
    {
      tree lhs = gimple_assign_lhs (assign);

      if (TREE_CODE (lhs) != SSA_NAME && may_alias_p (store_mem, lhs))
	return true;

      tree rhs = gimple_assign_rhs1 (assign);

      if (TREE_CODE (rhs) != SSA_NAME && may_alias_p (store_mem, rhs))
	return true;

      return false;
    }

  if (auto call = dyn_cast<gcall *> (memref))
    {
      if (call_may_clobber_ref_p (call, store_mem))
	return true;

      for (unsigned i = 1; i < gimple_num_ops (call); i++)
	{
	  tree arg = gimple_op (call, i);

	  if (arg && may_alias_p (store_mem, arg))
	    return true;
	}

      return false;
    }

  return true;
}

/* Check if there is any memory alias that would impact correctness of lro
   transformation.  */

bool
lro_loop_info::check_non_alias ()
{
  gimple *store, *store1;
  unsigned i, j;

  FOR_EACH_VEC_ELT (lro_wt_stmts, i, store)
    {
      if (store_may_clobber_p (store, aset_wt_stmt))
	return false;

      FOR_EACH_VEC_ELT_FROM (lro_wt_stmts, j, store1, i + 1)
	{
	  if (store_may_clobber_p (store, store1))
	    return false;
	}

      for (auto memref : other_memrefs)
	{
	  if (store_may_clobber_p (store, memref))
	    return false;
	}
    }

  for (auto memref : other_memrefs)
    {
      if (store_may_clobber_p (aset_wt_stmt, memref))
	return false;
    }

  return true;
}

/* Return true if it is profitable to do LRO optimization.  */

bool
lro_loop_info::check_profitable1 ()
{
  TEST (tree_fits_shwi_p (ol_niter))
  HOST_WIDE_INT niter = tree_to_shwi (ol_niter) + 1;

  if (param_lro_min_niter)
    {
      TEST (niter >= param_lro_min_niter)
    }

  if (param_lro_max_niter)
    {
      TEST (niter <= param_lro_max_niter)
    }

  TEST (niter <= param_max_completely_peel_times)

  if (!param_lro_max_insns && outer_loop->unroll)
    {
      /* Skip loop that definitely could not be fully unrolled.  */
      TEST (outer_loop->unroll != 1 && outer_loop->unroll >= niter)
    }

  return true;
}

/* Return true if it is profitable to do LRO optimization.  */

bool
lro_loop_info::check_profitable2 ()
{
  int total = 0;
  eni_weights weights;

  TEST (lro_wt_stmts.length () <= (unsigned) param_lro_max_store_stmts)

  for (unsigned i = 0; i < outer_loop->num_nodes; i++)
    {
      basic_block bb = outer_bbs[i];

      if (bb->loop_father == inner_loop
	  || bb == bb1_after_il || bb == bb2_after_il)
	continue;

      for (auto gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	{
	  gimple *stmt = gsi_stmt (gsi);

	  if (bb == bb_before_il && gimple_code (stmt) == GIMPLE_COND)
	    continue;

	  total += estimate_num_insns (stmt, &weights);
	}
    }

  for (auto store : lro_wt_stmts)
    total += 2 * estimate_num_insns (store, &weights);

  if (param_lro_max_insns)
    {
      TEST (total <= param_lro_max_insns)
    }
  else
    {
      /* User wants to enable LRO on loop only if the loop could be fully
	 unrolled.  */
      total *= tree_to_shwi (ol_niter) + 1;
      TEST (total <= param_max_completely_peeled_insns)
    }

  return true;
}

/* Check loop INNER and initialize LRO with basic info (loops, blocks, edges).
   Return false if INNER doesn't satisfy LRO requirements.  */

bool
lro_loop_info::check_loop_structure (loop_p inner)
{
  /* There must be a nested loop.  */
  inner_loop = inner;
  outer_loop = loop_outer (inner);
  TEST (outer_loop && outer_loop->num && outer_loop->num_nodes > 5
	&& !optimize_loop_for_size_p (outer_loop)
	&& can_duplicate_loop_p (outer_loop)
	&& can_duplicate_loop_p (inner_loop))

  /* Initialize blocks in inner loop.  */
  basic_block *bbs = inner_bbs = get_loop_body (inner_loop);
  bb1_in_il = bbs[0];
  TEST (inner_loop->num_nodes == 3)
  TEST (empty_block_p (bbs[1]))
  bb2_in_il = bbs[2];
  TEST (EDGE_COUNT (bb1_in_il->succs) == 2 && EDGE_COUNT (bb1_in_il->preds) == 2
	&& EDGE_COUNT (bb2_in_il->succs) == 2)

  /* Initialize blocks in outer loop */

  TEST (ol_exit_edge = single_exit (outer_loop))
  if (ol_exit_edge->src != outer_loop->latch)
    {
      TEST (empty_block_p (outer_loop->latch))
    }
  bb3_after_il = ol_exit_edge->src;
  TEST (EDGE_COUNT (bb3_after_il->preds) == 2)

  tree_niter_desc niter;

  TEST (number_of_iterations_exit (outer_loop, ol_exit_edge, &niter, false))
  TEST (integer_zerop (niter.may_be_zero)
	&& TREE_CODE (niter.niter) == INTEGER_CST)

  ol_niter = niter.niter;
  TEST (check_profitable1 ())

  edge e;
  edge_iterator ei;
  FOR_EACH_EDGE (e, ei, bb3_after_il->preds)
    {
      if (EDGE_COUNT (e->src->preds) == 1)
	bb2_after_il = e->src;
      else if (EDGE_COUNT (e->src->preds) == 3)
	bb1_after_il = e->src;
      else
	return false;
    }
  TEST (bb1_after_il && bb2_after_il)

  FOR_EACH_EDGE (e, ei, bb1_in_il->preds)
    {
      if (e->src != inner_loop->latch)
	bb_before_il = e->src;
    }
  TEST (bb_before_il)
  if (empty_block_p (bb_before_il))
    {
      TEST (single_pred_p (bb_before_il))
      bb_before_il = single_pred_edge (bb_before_il)->src;
    }
  TEST (EDGE_COUNT (bb_before_il->succs) == 2)

  ol_entry_bb = outer_loop->header;
  TEST (EDGE_COUNT (ol_entry_bb->preds) == 2)
  FOR_EACH_EDGE (e, ei, ol_entry_bb->preds)
    {
      if (e->src != inner_loop->latch)
	ol_entry_edge = e;
    }
  TEST (ol_entry_edge)

  return true;
}

/* Return true if a LRO loop is found.  */

bool
lro_loop_info::analyze_loop ()
{
  TEST (check_inner_loop ())

  TEST_WITH_MSG (check_outer_loop (), "check outer loop");

  TEST_WITH_MSG (check_non_alias (), "check alias");

  TEST_WITH_MSG (check_profitable2 (), "check profitable");

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file,
	       "\n[LRO] Found a candidate in %s (inner loop %d, outer loop %d)",
	       current_function_name (), inner_loop->num, outer_loop->num);
      dump_info ();
    }

  return true;
}

void
remove_stmt (gimple *stmt)
{
  gcc_checking_assert (stmt);
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  gsi_remove (&gsi, true);
}

/* Reduce the LRO inner loop by changing the condition and removing aset write
   stmt, so the inner loop is dead and will be removed by other passes.  */

void
lro_loop_info::reduce_inner_loop ()
{
  /* Always go to the bb2.  */
  gimple *cond_stmt = get_bb_last_stmt (bb1_after_il);
  edge e_always_go = find_edge (bb1_after_il, bb2_after_il);
  gcc_checking_assert (e_always_go);

  if (e_always_go->flags |= EDGE_TRUE_VALUE)
    gimple_cond_make_true (as_a<gcond *> (cond_stmt));
  else
    gimple_cond_make_false (as_a<gcond *> (cond_stmt));

  remove_stmt (aset_wt_stmt);
}

static tree
create_temp_array (tree inner_type, poly_uint64 nelts, const char *name)
{
  tree atype = build_array_type_nelts (inner_type, nelts);

  char str[32];
  sprintf (str, "_%d", lro_name_suffix_id);
  char *tmp_name = concat (name, str, NULL);
  tree avar = create_tmp_var (atype, tmp_name);
  TREE_ADDRESSABLE (avar) = 1;
  return avar;
}

static tree
build_array_ref (tree elt_type, tree array_var, tree idx)
{
  return build4 (ARRAY_REF, elt_type, unshare_expr (array_var), idx, NULL_TREE,
		 NULL_TREE);
}

/* Split the outer loop into two loops.  The former loop scatters the indices
   and values to temps, while the latter loop gathers them from temps. */

void
lro_loop_info::split_outer_loop ()
{
  /* Prepare 1: create a following loop to write back temps to the LRO write
     stmt.  */
  tree iv = create_tmp_reg (size_type_node);
  tree iv_before, iv_after;
  tree upper_bound = build_int_cst (size_type_node, tree_to_shwi (ol_niter));
  /* Avoid modifying the PHIs of the dest block.  */
  split_edge (ol_exit_edge);
  loop_p lro_wt_loop
    = create_empty_loop_on_edge (ol_exit_edge, size_zero_node, size_one_node,
				 upper_bound, iv, &iv_before, &iv_after,
				 loop_outer (outer_loop));

  poly_uint64 nelts = tree_to_shwi (ol_niter) + 1;

  for (unsigned i = 0; i < lro_wt_stmts.length (); i++)
    {
      /* Prepare 2: create temp arrays for the LRO write stmt.  */

      gimple *lro_wt_stmt = lro_wt_stmts[i];

      tree origin_idx = aset_size;
      tree temp_idx_type, temp_idx_array, temp_val_type, temp_val_array;
      tree wt_val = gimple_assign_rhs1 (lro_wt_stmt);
      tree lro_idx = TREE_OPERAND (gimple_assign_lhs (lro_wt_stmt), 1);

      temp_idx_type = TREE_TYPE (lro_idx);
      temp_idx_array = create_temp_array (temp_idx_type, nelts, "_lro_idx");
      temp_val_type = TREE_TYPE (wt_val);
      temp_val_array = create_temp_array (temp_val_type, nelts, "_lro_val");
      lro_name_suffix_id++;

      /* 1. Store indices and values to temp arrays in the original loop.  */

      gimple_stmt_iterator gsi1 = gsi_for_stmt (lro_wt_stmt);
      tree idx_ref1
	= build_array_ref (temp_idx_type, temp_idx_array, origin_idx);
      gimple *new_store = gimple_build_assign (idx_ref1, lro_idx);
      gsi_insert_before (&gsi1, new_store, GSI_SAME_STMT);

      tree val_ref1
	= build_array_ref (temp_val_type, temp_val_array, origin_idx);
      new_store = gimple_build_assign (val_ref1, wt_val);
      gsi_insert_before (&gsi1, new_store, GSI_SAME_STMT);

      /* 2. Read indices and values from temp arrays in the following loop.  */

      gimple_stmt_iterator gsi2 = gsi_last_bb (lro_wt_loop->header);
      gsi_move_after (&gsi1, &gsi2);

      tree idx_ssa = make_ssa_name (temp_idx_type);
      tree idx_ref2
	= build_array_ref (temp_idx_type, temp_idx_array, iv_before);
      gimple *new_load = gimple_build_assign (idx_ssa, idx_ref2);
      gsi_insert_before (&gsi2, new_load, GSI_SAME_STMT);

      tree val_ssa = make_ssa_name (temp_val_type);
      tree val_ref2
	= build_array_ref (temp_val_type, temp_val_array, iv_before);
      new_load = gimple_build_assign (val_ssa, val_ref2);
      gsi_insert_before (&gsi2, new_load, GSI_SAME_STMT);

      tree arr_ref = gimple_assign_lhs (lro_wt_stmt);
      TREE_OPERAND (arr_ref, 1) = idx_ssa;
      gimple_assign_set_rhs1 (lro_wt_stmt, val_ssa);
      update_stmt (lro_wt_stmt);
    }
}

/* Apply LRO to the loops described by LRO_INFO.  */

void
lro_loop_info::transform_loop ()
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n[LRO TRANS] Step 1: reducing the inner loop %d\n",
	       inner_loop->num);
    }
  reduce_inner_loop ();

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n[LRO TRANS] Step 2: splitting the outer loop %d\n",
	       outer_loop->num);
    }
  split_outer_loop ();
}

/* Main routine to do loop reduction optimization.  */

static unsigned int
tree_ssa_lro (void)
{
  unsigned todo = 0;
  unsigned res = 0;

  loop_optimizer_init (LOOPS_NORMAL | LOOPS_HAVE_RECORDED_EXITS);
  calculate_dominance_info (CDI_DOMINATORS);
  scev_initialize ();

  for (auto loop : loops_list (cfun, LI_ONLY_INNERMOST))
    {
      lro_loop_info lro_info;
      if (!lro_info.check_loop_structure (loop))
	continue;

      if (lro_info.analyze_loop ())
	{
	  lro_info.transform_loop ();
	  res++;
	}
    }

  if (res)
    {
      todo |= TODO_update_ssa | TODO_cleanup_cfg | TODO_verify_all;
    }

  scev_finalize ();
  free_dominance_info (CDI_DOMINATORS);
  loop_optimizer_finalize ();
  return todo;
}

namespace {

const pass_data pass_data_lro = {
  GIMPLE_PASS,		 /* type */
  "lro",		 /* name */
  OPTGROUP_NONE,	 /* optinfo_flags */
  TV_TREE_LRO,		 /* tv_id */
  (PROP_cfg | PROP_ssa), /* properties_required */
  0,			 /* properties_provided */
  0,			 /* properties_destroyed */
  0,			 /* todo_flags_start */
  0,			 /* todo_flags_finish */
};

class pass_lro : public gimple_opt_pass
{
public:
  pass_lro (gcc::context *ctxt) : gimple_opt_pass (pass_data_lro, ctxt) {}

  /* opt_pass methods: */
  opt_pass *clone () final override { return new pass_lro (m_ctxt); }
  bool gate (function *) final override
  {
    return flag_tree_lro != 0 && param_lro_max_store_stmts > 0;
  }
  unsigned int execute (function *) final override { return tree_ssa_lro (); }
}; // class pass_lro

} // namespace

gimple_opt_pass *
make_pass_lro (gcc::context *ctxt)
{
  return new pass_lro (ctxt);
}
