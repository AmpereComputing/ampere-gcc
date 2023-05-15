/* Generate buildin for simple gimple patterns.
   Copyright (C) 2020-2021 Free Software Foundation, Inc.

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
#include "tree.h"
#include "gimple.h"
#include "cfghooks.h"
#include "tree-pass.h"
#include "ssa.h"
#include "gimple-pretty-print.h"
#include "fold-const.h"
#include "cfganal.h"
#include "gimple-iterator.h"
#include "tree-cfg.h"
#include "tree-ssa.h"
#include "cfgloop.h"
#include "tree-cfgcleanup.h"
#include "ipa-field-merge.h"
#include "tree-ssa-loop-mgo.h"
#include "tree-ssa-loop-ch.h"
#include "tree-ssa-loop-manip.h"

/* Append STMT to the end of block BB. */

static inline void
append_to_block (basic_block bb, gimple *stmt)
{
  gimple_stmt_iterator gsi = gsi_last_bb (bb);

  gcc_checking_assert (gimple_code (stmt) != GIMPLE_PHI);
  gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);
}

/* Duplicates basic block BB and redirects edge E to it.  Returns the
   new basic block.  The new basic block is placed after the basic block
   AFTER. Fix all phis on the edges outgoing cloned bb.  */

static basic_block
copy_bb_and_fix_phis (basic_block bb, edge e, basic_block after)
{
  basic_block new_bb = duplicate_block (bb, e, after);
  new_bb->flags |= BB_DUPLICATED;
  add_phi_args_after_copy_bb (new_bb);
  new_bb->flags &= ~BB_DUPLICATED;

  return new_bb;
}

/* The info for a loop that is to do strcmp. */

class strcmp_loop_info
{
public:
  /* The loop that is analyzed. */
  class loop *loop;

  /* The blocks in the loop.
     bb1 is for boundary check. bb2 is for char comparison. bb3 is empty. */
  basic_block bb1, bb2, bb3;

  /* The idx vars in bb1 and bb2. */
  tree idx1, idx2;

  /* The phis in bb1 and bb2. */
  gphi *bb1_phi, *bb2_phi;

  /* The loop exit blocks. bb1_exit is from bb1, while bb2_exit is from bb2. */
  edge bb1_exit, bb2_exit;

  /* The number of all uses of the phi inside the loop. The phi with only 1
     uses will be canonicalized to be 2 uses. */
  int num_of_uses;

  /* The load stmts that will be vectorized. */
  gimple *ld_stmt_l, *ld_stmt_r;

  /* The addresses for ld_stmt_l and ld_stmt_r. They are like,
     addr_l = base_l + offset
     addr_r = base_r + offset */
  tree addr_l, addr_r;

  /* The base addresses of addr_l and addr_r. */
  tree base_l, base_r;

  /* The stride for this accumulate stmt will be changed from 1 to vector
     width, i.e. 8. */
  gimple *accumulate_stmt;

  /* The condition statement to check upboundary of string index. */
  gimple *cond_stmt;

  /* The upbound of the loop. */
  tree upbound;

  strcmp_loop_info (class loop *loop = NULL) : loop (loop)
  {
    bb1 = bb2 = bb3 = NULL;
    idx1 = idx2 = NULL_TREE;
    bb1_phi = bb2_phi = NULL;
    bb1_exit = bb2_exit = NULL;
    num_of_uses = 0;
    ld_stmt_l = ld_stmt_r = NULL;
    addr_l = addr_r = NULL_TREE;
    base_l = base_r = NULL_TREE;
    accumulate_stmt = NULL;
    cond_stmt = NULL;
    upbound = NULL_TREE;
  }

  ~strcmp_loop_info () {}
};

#define TEST(cond) \
  if (!(cond)) \
    return false;

/* Return true if STMT is like i = i + 1.  */

static bool
is_accumulation (gimple *stmt, tree rhs)
{
  gcc_checking_assert (rhs != NULL_TREE);

  TEST (gimple_assign_rhs_code_p (stmt, PLUS_EXPR));
  TEST (TREE_CODE (rhs) == SSA_NAME);

  tree lhs = gimple_assign_lhs (stmt);
  tree rhs1 = gimple_assign_rhs1 (stmt);
  tree rhs2 = gimple_assign_rhs2 (stmt);
  TEST (
    (TREE_CODE (rhs1) == SSA_NAME && rhs1 == rhs && integer_onep (rhs2))
    || (TREE_CODE (rhs2) == SSA_NAME && rhs2 == rhs && integer_onep (rhs1)));

  tree lhs_id = SSA_NAME_IDENTIFIER (lhs);
  tree rhs_id = SSA_NAME_IDENTIFIER (rhs);
  TEST (lhs_id == rhs_id);

  return true;
}

/* Return true if all stmts have been visited except DEBUG stmt. */

static bool
visited_all_stmts (basic_block bb, gphi *phi, auto_bitmap &visited)
{
  /* Scan all stmts in current block. */
  gphi_iterator gpi;
  for (gpi = gsi_start_phis (bb); !gsi_end_p (gpi); gsi_next (&gpi))
    TEST (phi == gpi.phi ());

  gimple_stmt_iterator gsi;
  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (is_gimple_debug (stmt))
	continue;
      if (bitmap_bit_p (visited, gimple_uid (stmt)))
	continue;
      if (gimple_nop_p (stmt))
	continue;

      return false;
    }

  return true;
}

/* Return the upbound of the loop iteration. In the meantime, the blocks
   on true and false edges are returned as TRUE_DEST and FALSE_DEST. */

static tree
get_upbound (basic_block bb, tree idx, basic_block &true_dest,
	     basic_block &false_dest)
{
  tree lhs, rhs;
  tree lhs_ssa_name, rhs_ssa_name;
  tree limit = NULL_TREE;
  tree idx_ssa_name = SSA_NAME_IDENTIFIER (idx);

  gcc_checking_assert (idx_ssa_name != NULL_TREE);
  lhs_ssa_name = rhs_ssa_name = NULL_TREE;
  if (extract_block_cond (bb, NE_EXPR, lhs, rhs, true_dest, false_dest))
    {
      if (TREE_CODE (lhs) == SSA_NAME)
	lhs_ssa_name = SSA_NAME_IDENTIFIER (lhs);
      if (TREE_CODE (rhs) == SSA_NAME)
	rhs_ssa_name = SSA_NAME_IDENTIFIER (rhs);
      if (lhs_ssa_name == idx_ssa_name)
	limit = rhs;
      else if (rhs_ssa_name == idx_ssa_name)
	limit = lhs;
    }
  else if (extract_block_cond (bb, LT_EXPR, lhs, rhs, true_dest, false_dest))
    {
      if (TREE_CODE (lhs) == SSA_NAME)
	lhs_ssa_name = SSA_NAME_IDENTIFIER (lhs);
      if (lhs_ssa_name == idx_ssa_name)
	limit = rhs;
    }

  return limit;
}

/* Return true if the block is a pattern like below, and len_13 is idx1.

  # len_15 = PHI <len_13(7), len_8(D)(6)>
  len_13 = len_15 + 1;
  if (len_limit_9(D) != len_13)
    goto <bb 7>; [94.50%]
  else
    goto <bb 10>; [5.50%] */

static bool
bb1_is_valid (strcmp_loop_info *info, basic_block &true_dest,
	      basic_block &false_dest)
{
  auto_bitmap visited;

  TEST (TREE_CODE (info->idx1) == SSA_NAME);
  TEST (SSA_NAME_IDENTIFIER (info->idx1) != NULL_TREE);
  gimple *def = SSA_NAME_DEF_STMT (info->idx1);
  info->bb1 = gimple_bb (def);

  TEST (info->upbound
	= get_upbound (info->bb1, info->idx1, true_dest, false_dest));

  /* Mark visited stmts. */
  bitmap_set_bit (visited, gimple_uid (def));
  bitmap_set_bit (visited, gimple_uid (last_stmt (info->bb1)));

  /* Scan all stmts in current block. */
  TEST (visited_all_stmts (info->bb1, info->bb1_phi, visited));

  return true;
}

/* Return true if find an expression pattern like below,

   addr = base + idx
   t = *addr  */

static bool
find_char_ld (tree t, tree idx, tree &addr, tree &base)
{
  TEST (TREE_CODE (t) == SSA_NAME);
  gimple *g = SSA_NAME_DEF_STMT (t);

  TEST (g);
  TEST (is_gimple_assign (g));
  TEST (gimple_assign_load_p (g));

  /* (1) Check t = *addr  */
  poly_int64 ld_offset, ld_size;
  ld_offset = ld_size = -1;
  TEST (addr = load_from_memory_p (g, ld_offset, ld_size));
  TEST (TREE_CODE (addr) == SSA_NAME);
  TEST (known_eq (ld_offset, poly_int64 (0)));
  TEST (known_eq (ld_size, poly_int64 (BITS_PER_UNIT)));

  /* (2) Check addr = arr + idx  */
  gimple *stmt = SSA_NAME_DEF_STMT (addr);
  TEST (gimple_assign_rhs_code_p (stmt, POINTER_PLUS_EXPR));

  /* One of the operands should be idx. */
  tree rhs1, rhs2;
  rhs1 = gimple_assign_rhs1 (stmt);
  rhs2 = gimple_assign_rhs2 (stmt);
  TEST (TREE_CODE (rhs1) == SSA_NAME && TREE_CODE (rhs2) == SSA_NAME);
  if (rhs1 == idx)
    base = rhs2;
  else if (rhs2 == idx)
    base = rhs1;
  else
    return false;

  /* (3) These two stmts should be in the same block. */
  TEST (gimple_bb (stmt) == gimple_bb (g));

  return true;
}

/* Return true if a block has code sequence below, in which _1 is idx2.

  # len_15 = PHI <len_13(7), len_8(D)(6)>
  _1 = (sizetype) len_15;
  _2 = pb_10(D) + _1;
  _3 = *_2;
  _5 = cur_12(D) + _1;
  _6 = *_5;
  if (_3 != _6)
    goto <bb 9>; [5.50%]
  else
    goto <bb 4>; [94.50%]  */

static bool
bb2_is_valid (strcmp_loop_info *info, basic_block &true_dest,
	      basic_block &false_dest)
{
  tree lhs, rhs;
  auto_bitmap visited;

  TEST (TREE_CODE (info->idx2) == SSA_NAME);
  gimple *def = SSA_NAME_DEF_STMT (info->idx2);
  info->bb2 = gimple_bb (def);

  TEST (
    extract_block_cond (info->bb2, NE_EXPR, lhs, rhs, true_dest, false_dest));

  TEST (lhs != info->idx2);
  TEST (rhs != info->idx2);

  TEST (find_char_ld (lhs, info->idx2, info->addr_l, info->base_l));
  TEST (find_char_ld (rhs, info->idx2, info->addr_r, info->base_r));

  /* Mark visited stmts. */
  bitmap_set_bit (visited, gimple_uid (def));
  bitmap_set_bit (visited, gimple_uid (last_stmt (info->bb2)));
  bitmap_set_bit (visited, gimple_uid (SSA_NAME_DEF_STMT (lhs)));
  bitmap_set_bit (visited, gimple_uid (SSA_NAME_DEF_STMT (info->addr_l)));
  bitmap_set_bit (visited, gimple_uid (SSA_NAME_DEF_STMT (rhs)));
  bitmap_set_bit (visited, gimple_uid (SSA_NAME_DEF_STMT (info->addr_r)));

  info->ld_stmt_l = SSA_NAME_DEF_STMT (lhs);
  info->ld_stmt_r = SSA_NAME_DEF_STMT (rhs);

  /* Scan all stmts in current block. */
  TEST (visited_all_stmts (info->bb2, info->bb2_phi, visited));

  return true;
}

/* Return the phi stmt, if the BB has only one phi stmt.  */

static gphi *
get_single_phi (basic_block bb)
{
  gphi_iterator gpi;
  gphi *phi = NULL;
  for (gpi = gsi_start_phis (bb); !gsi_end_p (gpi); gsi_next (&gpi))
    {
      if (phi)
	return NULL;
      phi = gpi.phi ();
    }

  return phi;
}

/* Return true if STMT is a copy to generate sizetype like below,

   _1 = (sizetype) i_1  */

static bool
is_sizetype_copy (const gimple *stmt)
{
  if (!is_gimple_assign (stmt))
    return false;

  tree rhs = gimple_assign_rhs1 (stmt);

  if (gimple_assign_single_p (stmt))
    return TREE_CODE (rhs) == SSA_NAME;

  if (CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt)))
    {
      tree lhs = gimple_assign_lhs (stmt);

      if (TREE_CODE (rhs) == SSA_NAME && TREE_TYPE (lhs) == sizetype)
	return true;
    }

  return false;
}

static void
dump_loop (class loop *loop)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n> Analyzing loop #%d:\n", loop->num);
      basic_block *bbs = get_loop_body (loop);
      for (unsigned int i = 0; i < loop->num_nodes; i++)
	dump_bb (dump_file, bbs[i], 0, TDF_DETAILS);
      free (bbs);
    }
}

static void
dump_loop_info (strcmp_loop_info *info)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> Found a loop containing strcmp pattern:\n");
      dump_bb (dump_file, info->bb1, 0, TDF_DETAILS);
      dump_bb (dump_file, info->bb2, 0, TDF_DETAILS);
      dump_bb (dump_file, info->bb3, 0, TDF_DETAILS);

      fprintf (dump_file, "> The phi stmts:\n");
      print_gimple_stmt (dump_file, info->bb1_phi, 0, TDF_SLIM);
      print_gimple_stmt (dump_file, info->bb2_phi, 0, TDF_SLIM);

      fprintf (dump_file, "num_of_uses = %d:\n", info->num_of_uses);

      fprintf (dump_file, "\n> Two loop exit blocks:\n");
      dump_bb (dump_file, info->bb1_exit->dest, 0, TDF_DETAILS);
      dump_bb (dump_file, info->bb2_exit->dest, 0, TDF_DETAILS);

      fprintf (dump_file, "\nThe following two stmts need to be vectorized.\n");
      print_gimple_stmt (dump_file, info->ld_stmt_l, 0, TDF_SLIM);
      print_gimple_stmt (dump_file, info->ld_stmt_r, 0, TDF_SLIM);

      fprintf (dump_file,
	       "\nThe stride of the following stmt need to be changed.\n");
      print_gimple_stmt (dump_file, info->accumulate_stmt, 0, TDF_SLIM);
    }
}

/* Return true if the LOOP is a typical strcmp pattern. In the meantime, some
   loop info is recorded into INFO.

   The loop body must have 3 basic blocks. The latch block must be empty, and
   it is recorded as bb3. One of the other two blocks should be for comparing
   a single char, and the other is for checking the string length. The former
   one is recorded as bb1, and the latter one is recorded as bb2.

   The loop body could be ordered like either case 1 "bb1 bb2 bb3" or case 2
   "bb2 bb1 bb3". However, the case 2 is a canonical one, so we will always
   transform the case 1 to the case 2.

   The field num_of_uses in INFO is to record the number of uses of the phi
   defined in bb2. For case 1, num_of_uses is 1, while for case 2, num_of_uses
   is 2. We use this field to differ case 1 and case 2 in the algorithm.  */

static bool
analyze_loop (strcmp_loop_info *info)
{
  gimple *use_stmt;
  imm_use_iterator use_iter;
  gphi *phi;
  class loop *loop = info->loop;
  edge latch = loop_latch_edge (loop);

  /* Step 1: Roughly check loop shape and find phi. */

  TEST (loop->num_nodes == 3);
  TEST (phi = get_single_phi (loop->header));
  TEST (gimple_phi_num_args (phi) == 2);
  info->bb3 = latch->src;
  TEST (empty_block_p (info->bb3));

  edge loop_entry = loop_preheader_edge (loop);
  tree def = PHI_ARG_DEF_FROM_EDGE (phi, loop_entry);
  TEST (TREE_CODE (def) == SSA_NAME || TREE_CODE (def) == INTEGER_CST);

  tree first = gimple_phi_result (phi);
  tree last = PHI_ARG_DEF_FROM_EDGE (phi, latch);

  TEST (TREE_CODE (first) == SSA_NAME && TREE_CODE (last) == SSA_NAME);
  TEST (first != last);

  dump_loop (loop);

  /* Step 2: Find idx1 and idx2.  */

  info->bb1_phi = info->bb2_phi = NULL;

  /* idx1 is the def of an accumulation. e.g. the lhs of i_1 = i_2 + 1  */
  info->idx1 = NULL_TREE;
  /* idx2 is the def of a string offset. e.g the lhs of _1 = (sizetype) i_1  */
  info->idx2 = NULL_TREE;
  info->num_of_uses = 0;
  info->accumulate_stmt = NULL;
  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, first)
    {
      if (is_accumulation (use_stmt, first))
	{
	  info->idx1 = gimple_assign_lhs (use_stmt);
	  info->accumulate_stmt = use_stmt;
	  info->num_of_uses++;
	}
      else if (is_sizetype_copy (use_stmt))
	{
	  info->idx2 = gimple_assign_lhs (use_stmt);
	  info->num_of_uses++;
	}
    }

  TEST (info->idx1 == last);

  if (info->num_of_uses == 1 && info->idx1 != NULL_TREE
      && info->idx2 == NULL_TREE)
    {
      FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, info->idx1)
	{
	  if (is_sizetype_copy (use_stmt))
	    info->idx2 = gimple_assign_lhs (use_stmt);
	  if (use_stmt == phi)
	    info->bb1_phi = phi;
	}
      TEST (info->idx2 != NULL_TREE);
      TEST (info->bb1_phi);
    }
  else if (info->num_of_uses == 2 && info->idx1 != NULL_TREE
	   && info->idx2 != NULL_TREE)
    {
      info->bb2_phi = phi;
    }
  else
    return false;

  /* Step 3: Check code patterns in two basic blocks bb1 and bb2.
     idx1 is defined in bb1, idx2 is defined in bb2. */

  basic_block bb1_true, bb1_false;
  basic_block bb2_true, bb2_false;
  TEST (bb1_is_valid (info, bb1_true, bb1_false));
  info->bb1 = gimple_bb (SSA_NAME_DEF_STMT (info->idx1));
  info->cond_stmt = last_stmt (info->bb1);
  TEST (bb2_is_valid (info, bb2_true, bb2_false));
  info->bb2 = gimple_bb (SSA_NAME_DEF_STMT (info->idx2));

  /* Step 4: Check if the CFG follows either of
     (1) bb1->bb2, bb2->bb3, bb3->bb1
     (2) bb2->bb1, bb1->bb3, bb3->bb2
     bb3 is an empty block.  */

  if (info->bb1 == loop->header)
    {
      TEST (bb1_true == info->bb2)
      TEST (bb2_false == info->bb3)
    }
  else if (info->bb2 == loop->header)
    {
      TEST (bb2_false == info->bb1);
      TEST (bb1_true == info->bb3);
    }
  else
    return false;

  basic_block bb4 = bb1_false;
  basic_block bb5 = bb2_true;

  /* Collect all info into strcmp_loop_info. */

  info->bb1_exit = find_edge (info->bb1, bb4);
  info->bb2_exit = find_edge (info->bb2, bb5);

  dump_loop_info (info);

  return true;
}

/* Assume the LOOP is an canonical one, and we collect INFO to help code
   transformation. */

static void
collect_loop_info (strcmp_loop_info &info)
{
  edge e1, e2;
  gimple_stmt_iterator gsi;
  class loop *loop = info.loop;

  info.bb2 = loop->header;
  info.bb3 = loop->latch;
  info.bb1 = single_pred (loop->latch);

  info.bb1_phi = get_single_phi (info.bb1);
  gcc_checking_assert (info.bb1_phi == NULL);
  info.bb2_phi = get_single_phi (info.bb2);

  info.idx2 = gimple_phi_result (info.bb2_phi);

  e1 = EDGE_SUCC (info.bb1, 0);
  e2 = EDGE_SUCC (info.bb1, 1);
  if (e1->dest == info.bb3)
    info.bb1_exit = e2;
  else
    info.bb1_exit = e1;

  e1 = EDGE_SUCC (info.bb2, 0);
  e2 = EDGE_SUCC (info.bb2, 1);
  if (e1->dest == info.bb1)
    info.bb2_exit = e2;
  else
    info.bb2_exit = e1;

  info.num_of_uses = 2;

  for (gsi = gsi_start_bb (info.bb2); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (!info.addr_l && gimple_assign_rhs_code_p (stmt, POINTER_PLUS_EXPR))
	{
	  info.addr_l = gimple_assign_lhs (stmt);
	  continue;
	}
      if (!info.ld_stmt_l && gimple_assign_load_p (stmt))
	{
	  info.ld_stmt_l = stmt;
	  continue;
	}
      if (!info.addr_r && gimple_assign_rhs_code_p (stmt, POINTER_PLUS_EXPR))
	{
	  info.addr_r = gimple_assign_lhs (stmt);
	  continue;
	}
      if (!info.ld_stmt_r && gimple_assign_load_p (stmt))
	{
	  info.ld_stmt_r = stmt;
	  continue;
	}
    }

  for (gsi = gsi_start_bb (info.bb1); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (!info.accumulate_stmt && gimple_assign_rhs_code_p (stmt, PLUS_EXPR))
	{
	  info.accumulate_stmt = stmt;
	  continue;
	}
      if (!info.cond_stmt && gimple_code (stmt) == GIMPLE_COND)
	{
	  info.cond_stmt = stmt;
	  basic_block true_dest, false_dest;
	  info.upbound
	    = get_upbound (info.bb1, info.idx2, true_dest, false_dest);
	  continue;
	}
    }
}

/* Analyze the pred of prehead of the loop to make sure it is a proper while-do
   loop for strcmp pattern. */

static bool
analyze_loop_pred (const strcmp_loop_info info)
{
  /* loop_prehead is an empty block, and we skip it. */
  edge loop_entry = loop_preheader_edge (info.loop);
  basic_block loop_prehead = loop_entry->src;
  TEST (empty_block_p (loop_prehead));
  TEST (single_succ_p (loop_prehead) && single_pred_p (loop_prehead));
  basic_block pred = single_pred (loop_prehead);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> Analyzing loop pred #%d:\n", info.loop->num);
      dump_bb (dump_file, pred, 0, TDF_DETAILS);
    }

  /* The last stmt in pred must be a cond stmt, and one of its operands should
     be the loop incoming values of info.b2_phi. */
  tree idx = PHI_ARG_DEF_FROM_EDGE (info.bb2_phi, loop_entry);
  tree lhs, rhs;
  basic_block true_dest, false_dest;
  if (extract_block_cond (pred, NE_EXPR, lhs, rhs, true_dest, false_dest))
    {
      TEST (
	(operand_equal_p (lhs, idx) && operand_equal_p (rhs, info.upbound))
	|| (operand_equal_p (rhs, idx) && operand_equal_p (lhs, info.upbound)));
      TEST (true_dest == loop_prehead);
    }
  else if (extract_block_cond (pred, LT_EXPR, lhs, rhs, true_dest, false_dest))
    {
      TEST (operand_equal_p (lhs, idx));
      TEST (operand_equal_p (rhs, info.upbound));
      TEST (true_dest == loop_prehead);
    }
  else
    return false;

  return true;
}

/* Insert a NOP to trigger loop rotation. This is to make sure the loop head
   is always to compare char inside string. */

static void
insert_nop (const strcmp_loop_info info)
{
  gimple_stmt_iterator gsi;

  gcc_checking_assert (info.num_of_uses == 1);

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "> Insert a NOP to canonicalize loop #%d\n",
	     info.loop->num);

  gsi = gsi_last_bb (info.bb3);
  gimple *nop = gimple_build_nop ();
  gsi_insert_before (&gsi, nop, GSI_SAME_STMT);
}

/* Vectorize the loop as described by NEW_INFO. */

static void
vectorize_loop (const strcmp_loop_info new_info)
{
  gphi *phi = get_single_phi (new_info.bb2);
  tree def = gimple_phi_result (phi);
  tree type = TREE_TYPE (def);

  /* Handle cloned bb1 */

  /* Change stride from 1 to 8 */
  if (integer_onep (gimple_assign_rhs1 (new_info.accumulate_stmt)))
    gimple_assign_set_rhs1 (new_info.accumulate_stmt, build_int_cst (type, 8));
  else
    gimple_assign_set_rhs2 (new_info.accumulate_stmt, build_int_cst (type, 8));
  update_stmt (new_info.accumulate_stmt);
  tree accumulate_lhs = gimple_assign_lhs (new_info.accumulate_stmt);

  /* Change condition opcode to either LE or GE. */
  enum tree_code new_cond_code;
  tree cond_stmt_lhs = gimple_cond_lhs (new_info.cond_stmt);
  tree cond_stmt_rhs = gimple_cond_rhs (new_info.cond_stmt);
  tree cond_stmt_lhs_ssa_name = SSA_NAME_IDENTIFIER (cond_stmt_lhs);
  tree cond_stmt_rhs_ssa_name = SSA_NAME_IDENTIFIER (cond_stmt_rhs);
  tree accumulate_lhs_ssa_name = SSA_NAME_IDENTIFIER (accumulate_lhs);
  if (accumulate_lhs_ssa_name == cond_stmt_lhs_ssa_name)
    new_cond_code = LE_EXPR;
  else if (accumulate_lhs_ssa_name == cond_stmt_rhs_ssa_name)
    new_cond_code = GE_EXPR;
  else
    gcc_unreachable ();
  gcond *new_cond_stmt = dyn_cast<gcond *> (new_info.cond_stmt);
  gimple_cond_set_code (new_cond_stmt, new_cond_code);

  /* Handle cloned bb2 */

  tree lhs, rhs, opnd1, new_rhs;
  /* Change *_2 to MEM[(uint64_t *)_2] for ld_stmt_l. */
  lhs = gimple_assign_lhs (new_info.ld_stmt_l);
  rhs = gimple_assign_rhs1 (new_info.ld_stmt_l);
  /* MEM_REF's pointer type is determined by the offset. */
  opnd1 = fold_convert (build_pointer_type (uint64_type_node),
			TREE_OPERAND (rhs, 1));
  new_rhs
    = fold_build2 (MEM_REF, uint64_type_node, TREE_OPERAND (rhs, 0), opnd1);
  gimple_assign_set_rhs1 (new_info.ld_stmt_l, new_rhs);
  update_stmt (new_info.ld_stmt_l);
  TREE_TYPE (lhs) = uint64_type_node;
  SET_SSA_NAME_VAR_OR_IDENTIFIER (lhs, NULL_TREE);

  /* Change *_2 to MEM[(uint64_t *)_2] for ld_stmt_r. */
  lhs = gimple_assign_lhs (new_info.ld_stmt_r);
  rhs = gimple_assign_rhs1 (new_info.ld_stmt_r);
  opnd1 = fold_convert (build_pointer_type (uint64_type_node),
			TREE_OPERAND (rhs, 1));
  new_rhs
    = fold_build2 (MEM_REF, uint64_type_node, TREE_OPERAND (rhs, 0), opnd1);
  gimple_assign_set_rhs1 (new_info.ld_stmt_r, new_rhs);
  update_stmt (new_info.ld_stmt_r);
  TREE_TYPE (lhs) = uint64_type_node;
  SET_SSA_NAME_VAR_OR_IDENTIFIER (lhs, NULL_TREE);

  /* Remove all debug info for current bb. Otherwise, we would have to check
     all debug stmt to modify the counterpart in debug info for the tree type
     we have just changed.  */
  gimple_stmt_iterator gsi;
  for (gsi = gsi_start_bb (new_info.bb2); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (is_gimple_debug (stmt))
	gsi_remove (&gsi, true);
    }
}

/* Insert a new phi in BB for using DEF. */

static tree
insert_new_phi (basic_block bb, tree def)
{
  tree t = make_temp_ssa_name (TREE_TYPE (def), NULL, "");
  gphi *phi = create_phi_node (t, bb);
  edge e = single_pred_edge (bb);
  add_phi_arg (phi, def, e, UNKNOWN_LOCATION);

  return t;
}

/* Add the following code to the trailing block of the vectorized loop.

  <bb 4> [local count: 679839639]:
  len_phi = phi (new_phi_lhs)
  l_phi = phi (addr_l)
  r_phi = phi (addr_r)
  temp_27 = l_25 ^ r_26;
  _11 = __builtin_ctzll (temp_27);
  _12 = _11 >> 3;
  temp_len_28 = (unsigned int) _12;
  len_29 = temp_len_28 + _47;
  new_addr_l = l_phi + len_29;
  new_addr_r = r_phi + len_29;
  goto <bb 10>; [100.00%]  */

static void
add_tail_bb_stmts (basic_block tail_bb, edge old_exit_edge,
		   const strcmp_loop_info old_info,
		   const strcmp_loop_info new_info)
{
  tree new_phi_lhs = gimple_phi_result (new_info.bb2_phi);
  location_t loc = gimple_location (new_info.cond_stmt);

  tree add_lhs = copy_ssa_name (new_phi_lhs);
  tree offset = make_ssa_name (size_type_node);
  tree new_addr_l = copy_ssa_name (new_info.addr_l);
  tree new_addr_r = copy_ssa_name (new_info.addr_r);
  tree l = gimple_assign_lhs (new_info.ld_stmt_l);
  tree r = gimple_assign_lhs (new_info.ld_stmt_r);

  /* Use the original type. */
  tree origin_ld_type = TREE_TYPE (gimple_assign_lhs (old_info.ld_stmt_l));
  tree new_ld_stmt_l = make_ssa_name (origin_ld_type);
  tree new_ld_stmt_r = make_ssa_name (origin_ld_type);

  if (old_exit_edge == old_info.bb1_exit)
    {
      gimple *add_stmt = gimple_build_assign (add_lhs, new_info.upbound);
      gimple_set_location (add_stmt, loc);
      append_to_block (tail_bb, add_stmt);
    }
  else if (old_exit_edge == old_info.bb2_exit)
    {
      l = insert_new_phi (tail_bb, l);
      r = insert_new_phi (tail_bb, r);

      /* temp_27 = l_25 ^ r_26; */
      gcc_checking_assert (TREE_TYPE (l) == TREE_TYPE (r));
      tree xor_lhs = copy_ssa_name (l);
      gimple *xor_stmt = gimple_build_assign (xor_lhs, BIT_XOR_EXPR, l, r);
      gimple_set_location (xor_stmt, loc);

      /* _11 = __builtin_ctzll (temp_27); */
      tree decl = builtin_decl_implicit (BUILT_IN_CTZLL);
      gimple *ctzll_stmt
	= gimple_build_call (decl, 1, gimple_assign_lhs (xor_stmt));
      gimple_set_location (ctzll_stmt, loc);
      tree ctzll_lhs = make_ssa_name (integer_type_node);
      gimple_call_set_lhs (ctzll_stmt, ctzll_lhs);

      /* _12 = _11 >> 3; */
      tree rshift_lhs = copy_ssa_name (ctzll_lhs);
      gimple *rshift_stmt
	= gimple_build_assign (rshift_lhs, RSHIFT_EXPR, ctzll_lhs,
			       build_int_cst (unsigned_type_node, 3));
      gimple_set_location (rshift_stmt, loc);

      /* temp_len_28 = (unsigned int) _12; */
      tree typecast_lhs = make_ssa_name (TREE_TYPE (new_phi_lhs));
      gimple *typecast_stmt
	= gimple_build_assign (typecast_lhs, NOP_EXPR, rshift_lhs);
      gimple_set_location (typecast_stmt, loc);

      /* len_29 = temp_len_28 + _47; */
      tree len_t = copy_ssa_name (new_phi_lhs);
      gphi *len_phi = create_phi_node (len_t, tail_bb);
      edge tail_edge = single_pred_edge (tail_bb);
      add_phi_arg (len_phi, new_phi_lhs, tail_edge, UNKNOWN_LOCATION);
      gimple *add_stmt
	= gimple_build_assign (add_lhs, PLUS_EXPR, typecast_lhs, len_t);
      gimple_set_location (add_stmt, loc);

      /* Split the edge to bb2_exit->dest and insert some stmts in between. */
      append_to_block (tail_bb, xor_stmt);
      append_to_block (tail_bb, ctzll_stmt);
      append_to_block (tail_bb, rshift_stmt);
      append_to_block (tail_bb, typecast_stmt);
      append_to_block (tail_bb, add_stmt);
    }
  else
    gcc_unreachable ();

  /* Covert from int to size_t. */
  gimple *offset_stmt = gimple_build_assign (offset, NOP_EXPR, add_lhs);
  gimple_set_location (offset_stmt, loc);
  append_to_block (tail_bb, offset_stmt);

  /* new_addr_l = addr_l + len_29; */
  tree base_l = insert_new_phi (tail_bb, new_info.base_l);
  gimple *addr_stmt_l
    = gimple_build_assign (new_addr_l, POINTER_PLUS_EXPR, base_l, offset);
  gimple_set_location (addr_stmt_l, loc);
  append_to_block (tail_bb, addr_stmt_l);

  /* new_addr_r = addr_r + len_29; */
  tree base_r = insert_new_phi (tail_bb, new_info.base_r);
  gimple *addr_stmt_r
    = gimple_build_assign (new_addr_r, POINTER_PLUS_EXPR, base_r, offset);
  gimple_set_location (addr_stmt_r, loc);
  append_to_block (tail_bb, addr_stmt_r);

  /* Insert new load stmts from addr_stmt_l and addr_stmt_r. */
  tree new_ld_l = build_simple_mem_ref (new_addr_l);
  gimple *trailing_ld_l = gimple_build_assign (new_ld_stmt_l, new_ld_l);
  append_to_block (tail_bb, trailing_ld_l);

  tree new_ld_r = build_simple_mem_ref (new_addr_r);
  gimple *trailing_ld_r = gimple_build_assign (new_ld_stmt_r, new_ld_r);
  append_to_block (tail_bb, trailing_ld_r);

  /* If a phi in exit_bb uses the def in the loop, we need to update it.
     This solution is only valid for loop closed SSA, i.e. for a def defined
     in a loop, if it is used outside loop, there must be a phi at the loop
     exit blocks. */

  basic_block exit_bb = single_succ (tail_bb);
  edge new_exit_edge = single_succ_edge (tail_bb);
  gphi_iterator gpi;
  gphi *phi;

  /* The exit_bb has two pred edges, i.e. old_exit_edge and new_exit_edge. */
  for (gpi = gsi_start_nonvirtual_phis (exit_bb); !gsi_end_p (gpi);
       gsi_next_nonvirtual_phi (&gpi))
    {
      phi = gpi.phi ();
      tree def = PHI_ARG_DEF_FROM_EDGE (phi, old_exit_edge);
      gimple *stmt
	= (TREE_CODE (def) == SSA_NAME) ? SSA_NAME_DEF_STMT (def) : 0;

      /* For a def from an old stmts we have identified previously for this
	 optimization, we update the phi arg in exit_bb with the new def
	 counterpart.

	 For an unknown def, we simply insert a new phi using the old def in
	 tail bb, and update phi arg in exit_bb with the new phi. */

      if ((old_exit_edge == old_info.bb1_exit
	   && (operand_equal_p (def, new_info.upbound)
	       || stmt == old_info.accumulate_stmt))
	  || (old_exit_edge == old_info.bb2_exit && stmt == old_info.bb2_phi))
	{
	  add_phi_arg (phi, add_lhs, new_exit_edge, loc);
	  continue;
	}
      else if (def == old_info.addr_l)
	{
	  add_phi_arg (phi, new_addr_l, new_exit_edge, loc);
	  continue;
	}
      else if (def == old_info.addr_r)
	{
	  add_phi_arg (phi, new_addr_r, new_exit_edge, loc);
	  continue;
	}
      else if (stmt == old_info.ld_stmt_l)
	{
	  add_phi_arg (phi, new_ld_stmt_l, new_exit_edge, loc);
	  continue;
	}
      else if (stmt == old_info.ld_stmt_r)
	{
	  add_phi_arg (phi, new_ld_stmt_r, new_exit_edge, loc);
	  continue;
	}
      else
	{
	  tree new_phi = insert_new_phi (tail_bb, def);
	  add_phi_arg (phi, new_phi, new_exit_edge, loc);
	  continue;
	}
    }
}

/* We need to add some new defs in tail blocks to make sure the semantic
   keeps the same as the original loop. Please note that all of defs in
   the loop could be used outside the loop, so all new defs need to be
   fixed in tail blocks. */

static void
insert_tail_bbs (basic_block cond_bb, tree new_def,
		 const strcmp_loop_info old_info,
		 const strcmp_loop_info new_info)
{
  /* Step 1: Add tail bb from bb2. */
  location_t loc = gimple_location (new_info.bb2_phi);
  basic_block tail_bb = split_edge (new_info.bb2_exit);
  add_tail_bb_stmts (tail_bb, old_info.bb2_exit, old_info, new_info);

  /* Step2: Insert a new cond BB from bb1. */
  basic_block exit_bb
    = copy_bb_and_fix_phis (cond_bb, new_info.bb1_exit, new_info.bb1_exit->src);

  edge e_true, e_false;
  extract_true_false_edges_from_block (exit_bb, &e_true, &e_false);
  basic_block old_exit_bb = old_info.bb1_exit->dest;
  if (e_false->dest != old_exit_bb)
    e_false = redirect_edge_and_branch (e_false, old_exit_bb);

  /* Update phi arg. */
  gphi *exit_bb_phi = get_single_phi (exit_bb);
  tree vec_def = gimple_assign_lhs (new_info.accumulate_stmt);
  add_phi_arg (exit_bb_phi, vec_def, single_pred_edge (exit_bb), loc);

  /* Update condition statement. */
  gcond *cond_stmt = dyn_cast<gcond *> (last_stmt (exit_bb));
  gimple_cond_set_code (cond_stmt, NE_EXPR);
  tree lhs = gimple_cond_lhs (cond_stmt);
  tree rhs = gimple_cond_rhs (cond_stmt);
  tree phi_res = gimple_phi_result (exit_bb_phi);
  if (operand_equal_p (new_def, lhs))
    gimple_cond_set_lhs (cond_stmt, phi_res);
  else if (operand_equal_p (new_def, rhs))
    gimple_cond_set_rhs (cond_stmt, phi_res);
  else
    gcc_unreachable ();
  update_stmt (cond_stmt);

  /* Step 3: Add tail bb from bb1 going through the exit_bb. */
  basic_block tail_bb_2 = split_edge (e_false);
  add_tail_bb_stmts (tail_bb_2, old_info.bb1_exit, old_info, new_info);
}

/* Insert a new condition block before the cloned loop, and update some
   coresponding phis with the LOOP_ENTRY_DEF. */

static basic_block
insert_new_cond_bb (const strcmp_loop_info new_info, basic_block old_cond_bb,
		    edge cond_entry, tree loop_entry_def)
{
  gimple_stmt_iterator gsi;
  gphi *new_phi = get_single_phi (new_info.bb2);
  location_t phi_loc = gimple_location (new_phi);

  /* Copy the bb1 in cloned loop to generate new condition block before the
     cloned loop. This is to make sure the vectorization length is enough
     before entering the vectorized cloned loop. */
  basic_block new_cond_bb
    = copy_bb_and_fix_phis (new_info.bb1, cond_entry, cond_entry->src);

  /* Find the accumulate stmt, and update its operand with loop_entry_def. */
  gsi = gsi_start_bb (new_cond_bb);
  gimple *new_cond_bb_stmt = NULL;
  while (!gsi_end_p (gsi))
    {
      new_cond_bb_stmt = gsi_stmt (gsi);
      if (gimple_assign_rhs_code_p (new_cond_bb_stmt, PLUS_EXPR))
	break;
      gsi_next (&gsi);
      new_cond_bb_stmt = NULL;
    }
  gcc_checking_assert (new_cond_bb_stmt);
  if (integer_nonzerop (gimple_assign_rhs1 (new_cond_bb_stmt)))
    gimple_assign_set_rhs2 (new_cond_bb_stmt, loop_entry_def);
  else
    gimple_assign_set_rhs1 (new_cond_bb_stmt, loop_entry_def);
  update_stmt (new_cond_bb_stmt);

  edge e_true, e_false;
  extract_true_false_edges_from_block (new_cond_bb, &e_true, &e_false);
  redirect_edge_and_branch (e_true, new_info.bb2);
  e_false = redirect_edge_and_branch (e_false, old_cond_bb);
  /* The phi in cloned loop entry needs to be fixed. */
  add_phi_arg (new_phi, loop_entry_def, e_true, phi_loc);
  /* The phi in old_cond_bb needs to be fixed. */
  gphi *cond_bb_phi = get_single_phi (old_cond_bb);
  add_phi_arg (cond_bb_phi, loop_entry_def, e_false, phi_loc);

  /* Insert a new expr for "+ 8" before cond_stmt in cloned loop. */
  gassign *stride_stmt;
  gphi *phi = get_single_phi (new_info.bb2);
  tree new_stride_def = copy_ssa_name (gimple_phi_result (phi));
  tree accumulate_lhs = gimple_assign_lhs (new_info.accumulate_stmt);
  stride_stmt
    = gimple_build_assign (new_stride_def, PLUS_EXPR, accumulate_lhs,
			   build_int_cst (TREE_TYPE (loop_entry_def), 8));
  gsi = gsi_for_stmt (new_info.cond_stmt);
  gsi_insert_before (&gsi, stride_stmt, GSI_NEW_STMT);

  ssa_op_iter i;
  use_operand_p use_p;
  FOR_EACH_SSA_USE_OPERAND (use_p, new_info.cond_stmt, i, SSA_OP_USE)
    {
      tree use_ssa_name = SSA_NAME_VAR (USE_FROM_PTR (use_p));
      if (use_ssa_name == NULL_TREE)
	continue;
      if (operand_equal_p (use_ssa_name, SSA_NAME_VAR (accumulate_lhs)))
	SET_USE (use_p, new_stride_def);
    }
  update_stmt (new_info.cond_stmt);

  return new_cond_bb;
}

/* Transform the loop to be an optimized version by inserting a vectorized
   version before the original loop.

   Before doing code transformation, we need to guarantee the strcmp loop must
   be with case 2, i.e. "bb2 bb1 bb3". This way we can easily clone the loop
   and avoid loop rotation operation along with code transformation. */

static unsigned int
transform_loop (const strcmp_loop_info old_info)
{
  class loop *loop = old_info.loop;
  basic_block *loop_region_origin, *loop_region_cloned;

  gcc_checking_assert (loop->num_nodes == 3);

  /* Step 1: Split loop preheader by keeping the last condition comparison
     stmt only. This is to create a new entry to the peeling condition check
     basic block before the do-while loop. */

  edge loop_entry = loop_preheader_edge (loop);

  /* loop_prehead is an empty block. */
  basic_block loop_prehead = loop_entry->src;
  gcc_checking_assert (empty_block_p (loop_prehead));

  /* There must be a condition block before loop_prehead. */
  basic_block old_cond_bb = EDGE_PRED (loop_prehead, 0)->src;

  /* Isolate the condition stmt by splitting cond_block. */
  old_cond_bb = split_block_before_cond_jump (old_cond_bb);
  edge cond_entry = single_pred_edge (old_cond_bb);

  /* Create a new phi in old_cond_bb for index var, and add coresponding
     args. */
  gphi *phi = get_single_phi (old_info.bb2);
  location_t phi_loc = gimple_phi_arg_location_from_edge (phi, loop_entry);
  tree loop_entry_def = PHI_ARG_DEF_FROM_EDGE (phi, loop_entry);
  tree new_def = copy_ssa_name (gimple_phi_result (phi));
  gphi *cond_bb_phi = create_phi_node (new_def, old_cond_bb);
  SET_PHI_ARG_DEF (phi, loop_entry->dest_idx, new_def);

  /* Update new_def into cond_stmt of old_cond_bb. */
  gcond *cond_stmt = dyn_cast<gcond *> (last_stmt (old_cond_bb));
  tree lhs = gimple_cond_lhs (cond_stmt);
  tree rhs = gimple_cond_rhs (cond_stmt);
  if (operand_equal_p (old_info.upbound, lhs))
    gimple_cond_set_rhs (cond_stmt, new_def);
  else if (operand_equal_p (old_info.upbound, rhs))
    gimple_cond_set_lhs (cond_stmt, new_def);
  else
    gcc_unreachable ();
  update_stmt (cond_stmt);

  /* The new phi in old_cond_bb should use the old def. */
  add_phi_arg (cond_bb_phi, loop_entry_def, cond_entry, phi_loc);

  /* Step 2: Clone the loop and insert the cloned loop at the new entry. */

  initialize_original_copy_tables ();
  loop_region_origin = XNEWVEC (basic_block, loop->num_nodes);
  loop_region_cloned = XNEWVEC (basic_block, loop->num_nodes);
  loop_region_origin[0] = old_info.bb1;
  loop_region_origin[1] = old_info.bb2;
  loop_region_origin[2] = old_info.bb3;
  edge old_exits[2], new_exits[2];
  old_exits[0] = old_info.bb1_exit;
  old_exits[1] = old_info.bb2_exit;

  /* For old loop, bb2 is the loop head. */
  gcc_checking_assert (loop->header == old_info.bb2);

  /* Generate new loop structure.  */
  class loop *new_loop = duplicate_loop (loop, loop_outer (loop));

  copy_bbs (loop_region_origin, 3, loop_region_cloned, old_exits, 2, new_exits,
	    old_cond_bb->loop_father, cond_entry->src, true);
  redirect_edge_and_branch (cond_entry, loop_region_cloned[1]);
  add_phi_args_after_copy (loop_region_cloned, 3, NULL);

  /* Cloned bb2 phi arg for loop entry needs to be copied directly from
     original loop entry. */
  gphi *new_phi = get_single_phi (loop_region_cloned[1]);
  add_phi_arg (new_phi, loop_entry_def, cond_entry, phi_loc);

  dump_loop (new_loop);

  strcmp_loop_info new_info (new_loop);
  new_info.base_l = old_info.base_l;
  new_info.base_r = old_info.base_r;
  collect_loop_info (new_info);

  /* Step 3: Vectorize cloned loop. The stride in the cloned loop is 8. */

  vectorize_loop (new_info);

  /* Step 4: Insert a new condition block before the new loop. Since the
     condition is similar as the boundary exit of the new loop, and we also
     need a "+ 8" operation, here we simply clone the exit block from the new
     loop, and then modify corresponding def/use chains as well as phis. */

  insert_new_cond_bb (new_info, old_cond_bb, cond_entry, loop_entry_def);

  /* Step 5: Insert some statments in tail blocks from either bb1 or bb2. */

  insert_tail_bbs (old_cond_bb, new_def, old_info, new_info);

  /* Clean up everything. */
  free_original_copy_tables ();
  free (loop_region_origin);
  free (loop_region_cloned);

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "Generated builtin for strcmp in function %s!\n",
	     current_function_name ());

  return TODO_cleanup_cfg;
}

/* Analyze string comparision code sequence as below,

  while (++len != len_limit)
    {
      if (pb[len] != cur[len])
	break;
    }

  And transform it to be the code below,

  uint64_t temp;
  uint32_t temp_len;
  uint64_t l, r;
  ++len;
  while ((len + 8) < len_limit) {
    l = *(uint64_t *)(pb+len);
    r = *(uint64_t *)(cur+len);
    if (l == r) {
      len += 8;
      continue;
    } else
      goto LABEL1;
  }
  while (len != len_limit)
    {
      if (pb[len] != cur[len])
	break;
      ++len;
    }
  goto LABEL2;
LABEL1:
  temp = l ^ r; \
  temp_len = (__builtin_ctzll(temp) >> 3);  \
  len = len + temp_len;
LABEL2:

  To make code transformation consistent for different scenarios, we need
  first to canonicalize the loop to make char comparison in the loop head
  block. After canonicalization, the PHI node in the loop head will have
  two uses insize the loop.
*/

static unsigned int
gen_strcmp ()
{
  unsigned int res = 0;

  bool need_rotation = false;
  bool found_strcmp = false;
  for (auto loop : loops_list (cfun, LI_ONLY_INNERMOST))
    {
      strcmp_loop_info strcmp_info (loop);
      if (analyze_loop (&strcmp_info))
	{
	  found_strcmp = true;
	  if (strcmp_info.num_of_uses == 1)
	    {
	      insert_nop (strcmp_info);
	      need_rotation = true;
	    }
	}
    }

  if (!found_strcmp)
    return 0;

  /* Canonicalize the loop for which we just inserted a nop in bb3. This is to
     trigger a loop rotation, and transform case 1 to case 2 for the loop. */
  if (need_rotation)
    {
      res |= copy_headers_1 (cfun);
      if (res | TODO_cleanup_cfg)
	{
	  cleanup_tree_cfg ();
	  res &= ~TODO_cleanup_cfg;
	}
      gcc_checking_assert (res == 0);
    }

  int cur_num_of_loops = number_of_loops (cfun);

  /* Code transformation. */
  res = 0;
  for (auto loop : loops_list (cfun, LI_ONLY_INNERMOST))
    {
      /* Newly created loops should be excluded. */
      if (loop->num >= cur_num_of_loops)
	break;

      strcmp_loop_info strcmp_info (loop);
      if (analyze_loop (&strcmp_info))
	{
	  /* Fail fast if the loop is not canonicalized. */
	  if (strcmp_info.num_of_uses == 1)
	    continue;

	  gcc_checking_assert (strcmp_info.num_of_uses == 2);
	  if (!analyze_loop_pred (strcmp_info))
	    continue;

	  res |= transform_loop (strcmp_info);
	}
    }

  if (res)
    {
      free_dominance_info (CDI_DOMINATORS);
      rewrite_into_loop_closed_ssa (NULL, TODO_update_ssa);
    }

  return res;
}

static unsigned int
gen_builtin ()
{
  unsigned int res;

  res = gen_strcmp ();
  /* TODO: Add more peephole transformations here. */

  return res;
}

/* Distribute all loops in the current function.  */

namespace {

const pass_data pass_data_gen_builtin = {
  GIMPLE_PASS,		 /* type */
  "gen-builtin",	 /* name */
  OPTGROUP_LOOP,	 /* optinfo_flags */
  TV_TREE_GEN_BUILTIN,	 /* tv_id */
  (PROP_cfg | PROP_ssa), /* properties_required */
  0,			 /* properties_provided */
  0,			 /* properties_destroyed */
  0,			 /* todo_flags_start */
  0,			 /* todo_flags_finish */
};

class pass_gen_builtin : public gimple_opt_pass
{
public:
  pass_gen_builtin (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_gen_builtin, ctxt)
  {}

  /* opt_pass methods: */
  virtual bool gate (function *) { return flag_tree_gen_builtin; }
  virtual unsigned int execute (function *) { return gen_builtin (); }

}; // class pass_gen_builtin

} // namespace

gimple_opt_pass *
make_pass_gen_builtin (gcc::context *ctxt)
{
  return new pass_gen_builtin (ctxt);
}
