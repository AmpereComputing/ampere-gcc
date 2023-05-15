/* Loop memory gathering optimization.
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
#include "target.h"
#include "tree.h"
#include "gimple.h"
#include "tree-pass.h"
#include "ssa.h"
#include "cfghooks.h"
#include "gimple-pretty-print.h"
#include "fold-const.h"
#include "gimple-fold.h"
#include "gimplify.h"
#include "gimple-iterator.h"
#include "gimplify-me.h"
#include "tree-cfg.h"
#include "cfgloop.h"
#include "tree-scalar-evolution.h"
#include "tree-dfa.h"
#include "tree-chrec.h"
#include "tree-into-ssa.h"
#include "tree-ssa-loop-ivopts.h"
#include "tree-ssa-loop-manip.h"
#include "tree-ssa-loop-niter.h"
#include "tree-ssa-loop.h"
#include "stor-layout.h"

/* In a loop, it is optimal if only one memory stream is activated, that is,
   all memory operations sequentially access one data region.  But it is not
   always the case, such as traversing link list or manipulating discrete
   arrays.  In this scenario, the loop would contain multiple scattered memory
   accesses, which could trigger inefficient multi-way hardware prefetching,
   thus making cpu cache hit rate drop.

   For nested loops, if scattered memory accesses inside inner loop remain
   unchanged in each iteration of outer loop, we can dynamically gather result
   data into a sequential memory region when the first access in the inner
   loop takes place.  In this way the hardware prefetching can be reduced,
   and cpu cache hit rate can be improved.  The optimization is called memory
   gathering optimization (abbreviated as MGO).

   A piece of pseudo code for nested loop is given as:

   outer-loop ()
     {
       ...
       inner-loop (iter, iter_count)
	 {
	   ...
	   Type1 v1 = LOAD_FN1 (iter);
	   Type2 v2 = LOAD_FN2 (v1);
	   Type3 v3 = LOAD_FN3 (v2);
	   ...
	   iter = NEXT_FN (iter);
	 }
       ...
     }

   "LOAD_FNx()" is a conceptual function that translates its argument to a
   result, and is composed of a sequence of operations in which there is only
   one memory load.  It is capable of representing simple memory dereference
   like "iter->field", or complicated one like "array[iter * 2 + cst].field".

   "NEXT_FN()" is also a conceptual function which defines how an iterator is
   advanced.  It is able to describe simple integer iterator, list iterator,
   or even pure-function-based iterator on advanced stuff like hashset/tree.

   The baseline transformation will be:

   typedef struct cache_elem
     {
       bool   init;
       Type1  c_v1;
       Type2  c_v2;
       Type3  c_v3;
     } cache_elem;

   cache_elem *cache_arr = calloc (iter_count, sizeof (cache_elem));

   outer-loop ()
     {
       ...
       size_t cache_idx = 0;

       inner-loop (iter, iter_count)
	 {
	   ...
	   if (!cache_arr[cache_idx]->init)
	     {
	       v1 = LOAD_FN1 (iter);
	       v2 = LOAD_FN2 (v1);
	       v3 = LOAD_FN3 (v2);

	       cache_arr[cache_idx]->init = true;
	       cache_arr[cache_idx]->c_v1 = v1;
	       cache_arr[cache_idx]->c_v2 = v2;
	       cache_arr[cache_idx]->c_v3 = v3;
	     }
	   else
	     {
	       v1 = cache_arr[cache_idx]->c_v1;
	       v2 = cache_arr[cache_idx]->c_v2;
	       v3 = cache_arr[cache_idx]->c_v3;
	     }
	   ...
	   cache_idx++;
	   iter = NEXT_FN (iter);
	 }
       ...
     }

   free (cache_arr);

   "iter_count" stands for an upper bound for inner-loop iteration count,
   which must be an outer-loop invariant expression, in that it determines
   data count in cache space, and the space is allocated before outer-loop.
   And to avoid OOM at large count and negative impact for small count, two
   thresholds for maximum and minimum cache data count are added.  */


/* A unique suffix ID used in name generation, will be updated each time mgo
   is applied.  */
static unsigned mgo_name_suffix_id = 0;
static bool mgo_runtime_alias_check_on_bit_field = true;
static bool mgo_init_using_bit_field = true;

class loop_iter_info;

/* Data structure to hold temporary loop-wise information for mgo.  */
class loop_mgo_info
{
public:
  class loop *loop;

  /* Virtual PHI in loop header.  */
  gphi *root_vphi;

  /* Expression representing number of loop iterations.  */
  tree iterations;

  /* All memory store/clobber statements in a loop.  */
  auto_vec<gimple *> store_vdefs;

  /* All non-pure function call/gnu-asm statements in a loop.  */
  auto_vec<gimple *> other_vdefs;

  /* All iterators for mgo in a loop.  */
  auto_delete_vec<loop_iter_info> iters;

  loop_mgo_info (class loop *loop) : loop (loop), root_vphi (NULL),
				     iterations (NULL_TREE) {}
  ~loop_mgo_info () {}

  bool has_vdefs () const
  {
    return !store_vdefs.is_empty () || !other_vdefs.is_empty ();
  }
};

static inline loop_mgo_info *
get_mgo_info (const class loop *loop)
{
  loop_mgo_info *info = (loop_mgo_info *) loop->aux;

  gcc_checking_assert (info && info->loop == loop);

  return info;
}

/* Return true if STMT belongs to LOOP.  */

static inline bool
stmt_inside_loop_p (const class loop *loop, gimple *stmt)
{
  basic_block bb = gimple_bb (stmt);

  return bb && flow_bb_inside_loop_p (loop, bb);
}

/* A wrapper function on print_gimple_stmt(), with basic block number plus
   loop number and depth as prefix when printing STMT.  */

static void
print_gimple_stmt_with_bb (FILE *file, gimple *stmt, int spc = 0,
			   dump_flags_t flags = TDF_NONE,
			   bool with_loop = false)
{
  basic_block bb = gimple_bb (stmt);

  if (bb)
    {
      if (with_loop)
	fprintf (file, "(BB %d, LOOP %d:D%u) ", bb->index,
		 bb->loop_father->num, loop_depth (bb->loop_father));
      else
	fprintf (file, "(BB %d) ", bb->index);
    }

  print_gimple_stmt (file, stmt, spc, flags);
}

/* Create a conditional expression as COND ? VAL1 : VAL2.  */

static inline tree
build_cond_expr (tree cond, tree val1, tree val2)
{
  if (TREE_CODE (TREE_TYPE (cond)) != BOOLEAN_TYPE)
    cond = fold_build2 (NE_EXPR, boolean_type_node, cond,
			build_zero_cst (TREE_TYPE (cond)));

  return fold_build3 (COND_EXPR, TREE_TYPE (val1), cond, val1, val2);
}

/* Given a struct/class pointer ADDR, and FIELD_DECL belonging to the
   struct/class, create a field reference expression.  */

static inline tree
build_field_ref (tree addr, tree field_decl)
{
  tree addr_type = TREE_TYPE (addr);
  tree type = DECL_CONTEXT (field_decl);

  if (TREE_CODE (addr_type) == POINTER_TYPE)
    addr_type = build_pointer_type (type);
  else
    addr_type = build_reference_type (type);

  tree memref = build2 (MEM_REF, type, addr, build_zero_cst (addr_type));

  return build3 (COMPONENT_REF, TREE_TYPE (field_decl), memref, field_decl,
		 NULL_TREE);
}

/* Generate a gimple assignment as LHS = OP1 CODE OP2, or simple LHS = OP1,
   if OP2 is NULL. The statement will be inserted before GSI when BEFORE is
   true, otherwise appended after it.  */

static inline gassign *
build_assign_at_gsi (gimple_stmt_iterator *gsi, bool before, tree lhs,
		     tree op1, enum tree_code code = NOP_EXPR,
		     tree op2 = NULL_TREE)
{
  gassign *stmt;

  if (op2)
    stmt = gimple_build_assign (lhs, code, op1, op2);
  else
    stmt = gimple_build_assign (lhs, op1);

  if (before)
    gsi_insert_before (gsi, stmt, GSI_NEW_STMT);
  else
    gsi_insert_after (gsi, stmt, GSI_NEW_STMT);
  return stmt;
}

/* Generate a gimple assignment and insert it as the last stmt of BB.  */

static inline gassign *
build_assign_after_bb (basic_block bb, tree lhs, tree op1,
		       enum tree_code code = NOP_EXPR, tree op2 = NULL_TREE)
{
  gimple_stmt_iterator gsi = gsi_last_bb (bb);

  return build_assign_at_gsi (&gsi, false, lhs, op1, code, op2);
}

/* Generate a gimple conditional statement as OP1 CODE OP2, and insert it as
   the last stmt of BB.  */

static inline gcond *
build_cond_after_bb (basic_block bb, tree op1, enum tree_code code, tree op2)
{
  gimple_stmt_iterator gsi = gsi_last_bb (bb);
  gcond *cond = gimple_build_cond (code, op1, op2, NULL_TREE, NULL_TREE);

  gsi_insert_after (&gsi, cond, GSI_NEW_STMT);
  return cond;
}

/* Find all statements with memory-write effect in LOOP, including memory
   stores and non-pure function calls, and keep them in separate vectors.  */

static bool
get_vdefs_in_loop (const class loop *loop)
{
  loop_mgo_info *info = get_mgo_info (loop);
  gphi *vphi;

  if (info->root_vphi)
    return info->has_vdefs ();

  if (!(vphi = get_virtual_phi (loop->header)))
    return false;

  info->root_vphi = vphi;

  edge latch = loop_latch_edge (loop);
  tree first = gimple_phi_result (vphi);
  tree last = PHI_ARG_DEF_FROM_EDGE (vphi, latch);

  if (first == last)
    return false;

  auto_vec<tree> worklist;
  auto_bitmap visited;

  bitmap_set_bit (visited, SSA_NAME_VERSION (first));
  bitmap_set_bit (visited, SSA_NAME_VERSION (last));
  worklist.safe_push (last);

  do
    {
      tree vuse = worklist.pop ();
      gimple *stmt = SSA_NAME_DEF_STMT (vuse);
      basic_block bb = gimple_bb (stmt);

      gcc_checking_assert (stmt_inside_loop_p (loop, stmt));

      if (bb->loop_father != loop)
	{
	  class loop *subloop = bb->loop_father;

	  /* The virtual SSA name belongs to an inner loop, find out and
	     recursively process the topmost inner loop, then merge those
	     inner VDEFs into the enclosing loop.  */
	  while (loop != loop_outer (subloop))
	    subloop = loop_outer (subloop);

	  get_vdefs_in_loop (subloop);

	  loop_mgo_info *subloop_info = get_mgo_info (subloop);
	  gphi *subloop_vphi = subloop_info->root_vphi;

	  gcc_checking_assert (subloop_vphi);

	  tree result = gimple_phi_result (subloop_vphi);

	  /* Once an inner loop has been merged, its first virtual SSA name
	     is marked as visited to avoid repetition.  Here is a subtle case
	     that the virtual SSA name in processing is just the first one of
	     the inner loop.  The SSA name has tag of visited, but the inner
	     loop has not been merged.  */
	  if (vuse == result
	      || bitmap_set_bit (visited, SSA_NAME_VERSION (result)))
	    {
	      edge entry = loop_preheader_edge (subloop);
	      tree init = PHI_ARG_DEF_FROM_EDGE (subloop_vphi, entry);

	      info->store_vdefs.safe_splice (subloop_info->store_vdefs);
	      info->other_vdefs.safe_splice (subloop_info->other_vdefs);

	      if (bitmap_set_bit (visited, SSA_NAME_VERSION (init)))
		worklist.safe_push (init);
	    }
	}
      else if (gimple_code (stmt) == GIMPLE_PHI)
	{
	  for (unsigned i = 0; i < gimple_phi_num_args (stmt); ++i)
	    {
	      tree arg = gimple_phi_arg_def (stmt, i);

	      if (bitmap_set_bit (visited, SSA_NAME_VERSION (arg)))
		worklist.safe_push (arg);
	    }
	}
      else
	{
	  tree prev = gimple_vuse (stmt);

	  if (gimple_assign_single_p (stmt))
	    info->store_vdefs.safe_push (stmt);
	  else
	    info->other_vdefs.safe_push (stmt);

	  if (bitmap_set_bit (visited, SSA_NAME_VERSION (prev)))
	    worklist.safe_push (prev);
	}
    }
  while (!worklist.is_empty ());

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      unsigned i;
      gimple *stmt;

      fprintf (dump_file, "VDEFs in loop %d:\n", loop->num);

      FOR_EACH_VEC_ELT (info->store_vdefs, i, stmt)
	print_gimple_stmt_with_bb (dump_file, stmt);

      FOR_EACH_VEC_ELT (info->other_vdefs, i, stmt)
	print_gimple_stmt_with_bb (dump_file, stmt);

      fprintf (dump_file, "\n");
    }

  return info->has_vdefs ();
}

/* Try to deduce a possible minimum iteration count for LOOP, and return the
   expression if successful, otherwise return chrec_dont_know.  */

static tree
get_loop_iterations (class loop *loop)
{
  loop_mgo_info *info = get_mgo_info (loop);

  if (info->iterations)
    return info->iterations;

  auto_vec<edge> exits = get_loop_exit_edges (loop);
  unsigned i;
  edge ex;
  tree niter = chrec_dont_know;
  basic_block bb = NULL;

  FOR_EACH_VEC_ELT (exits, i, ex)
    {
      class tree_niter_desc niter_desc;

      /* Only care about exit that dominates latch.  */
      if (!number_of_iterations_exit_assumptions (loop, ex, &niter_desc, NULL)
	  || chrec_contains_undetermined (niter_desc.niter))
	continue;

      tree assumptions = niter_desc.assumptions;
      tree may_be_zero = niter_desc.may_be_zero;
      tree niter_type = TREE_TYPE (niter_desc.niter);
      tree niter_zero = build_int_cst (niter_type, 0);
      tree niter_one = build_int_cst (niter_type, 1);
      tree new_niter = size_binop (PLUS_EXPR, niter_desc.niter, niter_one);

      /* Generate expression to calculate iterations count at runtime (i.e.):

	   assumptions && !may_be_zero ? (niter + 1) : 0

	 If the count could not be normally evaluated, 0 will be given as
	 result to let dynamic check on that be possible.  */
      if (integer_nonzerop (may_be_zero))
	new_niter = niter_zero;
      else if (COMPARISON_CLASS_P (may_be_zero))
	{
	  tree not_be_zero = fold_build1 (TRUTH_NOT_EXPR, boolean_type_node,
					  may_be_zero);

	  /* Try to combine may_be_zero with assumptions, this can simplify
	     computation of niter expression.  */
	  if (!integer_nonzerop (assumptions))
	    assumptions = fold_build2 (TRUTH_AND_EXPR, boolean_type_node,
				       assumptions, not_be_zero);
	  else
	    assumptions = not_be_zero;
	}
      else if (!integer_zerop (may_be_zero))
	continue;

      if (!integer_nonzerop (assumptions))
	new_niter = build_cond_expr (assumptions, new_niter, niter_zero);

      if (niter == chrec_dont_know)
	{
	  niter = new_niter;
	  bb = ex->src;
	}
      else if (TREE_CODE (new_niter) == INTEGER_CST)
	{
	  /* Prefer constants, the lower the better.  */
	  if (TREE_CODE (niter) != INTEGER_CST
	      || tree_int_cst_lt (new_niter, niter))
	    {
	      niter = new_niter;
	      bb = ex->src;
	    }
	}
      else if (TREE_CODE (niter) != INTEGER_CST)
	{
	   /* From those exit conditions, the one that is nearest to the latch
	      would give the minimum iterations in all possibility.  */
	  if (dominated_by_p (CDI_DOMINATORS, ex->src, bb))
	    {
	      niter = new_niter;
	      bb = ex->src;
	    }
	}
    }

  info->iterations = niter;
  return niter;
}

/* Given a load, we will analyze feasibility of caching it, from mgo loop to
   all its parent loops one-by-one.  This data structure is used to hold
   per-loop analysis information for the load.  */

class dep_load_info
{
public:
  /* The load is a candidate to cache or not, if given outer loop is present.
     For example, exclude it if the loop contains an aliased store that could
     not be resolved.  */
  bool excluded;

  /* All memory store statements in given outer loop, which may clobber the
     load.  */
  auto_vec<gimple *> mod_stmts;

  dep_load_info () : excluded (false) {}
};

/* All loads that originate from a loop iterator are organized as a dependent
   load tree, whose root is the iterator.  The data structure corresponds to
   a tree node.  */

class dep_load
{
public:
  /* Outer loop invariant operands used in load address computation.  */
  auto_vec<tree> invar_opnds;

  /* Statements used to compute load address from result value of parent. */
  auto_vec<gimple *> addr_stmts;

  /* Loads that depends on current one.  */
  auto_delete_vec<dep_load> children;

  /* Need to cache the this load?  */
  bool need_caching;

  /* Level of pointer-chasing from iterator to current load.  */
  int level;

  /* Statements that define value represented by this load.  There might be
     more than one statement due to dependent loads merging.  While root node
     is somewhat different, it only contains PHI statements, and each PHI
     correlates with an iterator.  */
  auto_vec<gimple *> def_stmts;

  /* Analysis information collected for all parent loops.  */
  auto_delete_vec<dep_load_info> analysis_for_loops;

  /* The cost of current load.  The lower the better.  */
  int cost;

  /* SSA names to track the lower/upper bounds of the load address, which
     will be set at runtime by caching initialization code.  */
  tree addr_min;
  tree addr_max;

  inline bool is_root () const { return !level; }
  inline bool is_leaf () const { return children.is_empty (); }

  /* Check whether the load is excluded from caching candidates when outer
     loop denoted by LOOP_INDEX is present in loop hierarchy for mgo.  */

  bool excluded_p (unsigned loop_index) const
  {
    gcc_checking_assert (!analysis_for_loops.is_empty ());

    unsigned last_index = analysis_for_loops.length () - 1;

    if (last_index < loop_index)
      {
	gcc_checking_assert (analysis_for_loops[last_index]->excluded);
	return true;
      }

    return analysis_for_loops[loop_index]->excluded;
  }

  /* Return cost to cache the load.  The simple rules of cost:
       - The origin dependent load in level N costs N.
       - Caching a dependent load costs 2.
     It is estimated as: the cost of caching - 2 * the cost of origin load. */

  int get_caching_cost () const
  {
    static const int CACHE_COST = 2;

    return (need_caching ? CACHE_COST : 0) - 2 * level;
  }

  int get_runtime_check_cost (unsigned loop_index) const
  {
    static const int GEN_ADDR_COST = 1;
    static const int CMP_ADDR_COST = 1;

    int gen_addr_cost = 0;
    int cmp_addr_cost = 0;

    /* TODO:  More precise cost model is required, which would take execution
       profile count into consideration.  */
    for (unsigned i = 0; i <= loop_index; i++)
      {
	dep_load_info *dl_info = analysis_for_loops[i];
	unsigned j;
	gimple *store;

	gcc_checking_assert (!dl_info->excluded);

	FOR_EACH_VEC_ELT (dl_info->mod_stmts, j, store)
	  {
	    gcc_checking_assert (store);
	    cmp_addr_cost += CMP_ADDR_COST;
	  }
      }

    if (cmp_addr_cost)
      gen_addr_cost = GEN_ADDR_COST;

    return gen_addr_cost + cmp_addr_cost;
  }

  /* Estimate the cost of the data caching operation.  The model should cover
     both the data caching code and runtime alias checking code.

     For example, do not apply mgo for the below two situations:
     (1) The loop body is too small to afford inserting such a lot of data
	 caching code.
     (2) There are too many places where we need to insert dynamic checking
	 code, and it would bring too much overhead.  */

  int get_total_cost (unsigned loop_index) const
  {
    if (excluded_p (loop_index))
      return 0;

    int total = 0;
    unsigned i;
    dep_load *child;

    total += get_caching_cost ();
    total += get_runtime_check_cost (loop_index);

    FOR_EACH_VEC_ELT (children, i, child)
      total += child->get_total_cost (loop_index);

    return total;
  }

  /* Remove child from dependent load tree, whose position is specified by
     INDEX.  */

  void remove_child (unsigned index)
  {
    delete children[index];
    children.unordered_remove (index);
  }

  dep_load (gimple *def_stmt, int level = 0)
    : need_caching (level > 0), level (level), cost (0), addr_min (NULL_TREE),
      addr_max (NULL_TREE)
  {
    def_stmts.safe_push (def_stmt);
  }

  ~dep_load () {}
};

/* A utility class to traverse dependent load tree in pre-order.  */

class dep_load_walker
{
  struct dep_load_vec
  {
    dep_load **addr;
    unsigned size;
    unsigned index;

    dep_load *node () const
    {
      gcc_checking_assert (index < size);
      return addr[index];
    }
  };

  /* Root of dependent load tree.  */
  dep_load *root;

  /* Stack to hold child dependent loads in same level.  */
  auto_vec<dep_load_vec, 8> stack;

  /* Whether to traverse children tree of current load.  */
  bool walk_children_p;

public:
  dep_load_walker () : root (NULL), walk_children_p (true) {}

  void init (const dep_load *dl_root)
  {
    /* In the class, "root" is actually used as a const pointer, but we can
       not syntactically decorate it with const specifier, this is meant to
       support both usages w/o const requirement.  */
    root = const_cast<dep_load *> (dl_root);
    walk_children_p = true;

    dep_load_vec dl_vec = { &root, 1, 0 };
    stack.safe_push (dl_vec);
  }

  void skip_children () { walk_children_p = false; }

  dep_load *next ()
  {
    while (!stack.is_empty ())
      {
	dep_load_vec &dl_vec = stack.last ();

	if (walk_children_p)
	  {
	    dep_load *dl = dl_vec.node ();

	    if (!dl->is_leaf ())
	      {
		dep_load_vec new_dl_vec
		  = { dl->children.begin (), dl->children.length (), 0 };
		stack.safe_push (new_dl_vec);
		return new_dl_vec.node ();
	      }
	  }

	if (++dl_vec.index < dl_vec.size)
	  {
	    walk_children_p = true;
	    return dl_vec.node ();
	  }

	/* All children have been visited, force walker to advance to sibling
	   of the children's parent.  */
	walk_children_p = false;

	stack.pop ();
      }

    return NULL;
  }
};

#define WALK_DEP_LOAD_PRE_ORDER(WALKER, ROOT, DL) \
  for ((DL) = (ROOT), (WALKER).init (ROOT); (DL); (DL) = (WALKER).next ())

/* Dump dependent load tree with indention.  */

static void
dump_dep_load (FILE *file, const dep_load *dl_root)
{
  const dep_load *dl;
  dep_load_walker dl_walker;

  WALK_DEP_LOAD_PRE_ORDER (dl_walker, dl_root, dl)
    {
      int indent = dl->level * 2;
      unsigned i;
      gimple *stmt;
      dep_load_info *dl_info;

      fprintf (file, "%*s", indent, "");

      if (dl->is_root ())
	fprintf (file, "root:\n");
      else
	fprintf (file, "level %d%s:\n", dl->level,
		 dl->need_caching ? "" : " (not cached)");

      FOR_EACH_VEC_ELT (dl->def_stmts, i, stmt)
	{
	  fprintf (file, "%*s", indent, "");
	  print_gimple_stmt_with_bb (file, stmt);
	}

      if (!dl->invar_opnds.is_empty ())
	{
	  tree opnd;

	  fprintf (file, "%*sInvariant operands:\n", indent + 2, "");

	  FOR_EACH_VEC_ELT (dl->invar_opnds, i, opnd)
	    {
	      fprintf (file, "%*s", indent + 4, "");

	      if (SSA_NAME_IS_DEFAULT_DEF (opnd))
		{
		  print_generic_expr (file, opnd);
		  fprintf (file, "\n");
		}
	      else
		print_gimple_stmt_with_bb (file, SSA_NAME_DEF_STMT (opnd));
	    }
	}

      if (!dl->addr_stmts.is_empty ())
	{

	  fprintf (file, "%*sAddress computation stmts:\n", indent + 2, "");

	  FOR_EACH_VEC_ELT (dl->addr_stmts, i, stmt)
	    {
	      fprintf (file, "%*s", indent + 4, "");
	      print_gimple_stmt_with_bb (file, stmt);
	    }
	}

      FOR_EACH_VEC_ELT (dl->analysis_for_loops, i, dl_info)
	{
	  if (dl_info->excluded)
	    fprintf (file, "%*sExcluded in outer loop #%d\n",
		     indent + 2, "", i);

	  if (!dl_info->mod_stmts.is_empty ())
	    {
	      unsigned j;

	      fprintf (file, "%*sAliased stores in outer loop #%d:\n",
		       indent + 2, "", i);

	      FOR_EACH_VEC_ELT (dl_info->mod_stmts, j, stmt)
		{
		  fprintf (file, "%*s", indent + 4, "");
		  print_gimple_stmt_with_bb (file, stmt);
		}
	    }
	}
    }

  if (dl_root->is_root ())
    fprintf (file, "\n");
}

/* Cache element type layout related things for a dependent load tree.  */

class cache_type_info
{
public:
  /* The "init" flag field used to track if a cache element is initialized.  */
  tree init_field;

  /* Cache type fields for all "need-caching" loads in the tree, generated
     in pre-order of the tree.  */
  auto_vec<tree> fields;

  /* The structure type to hold above fields.  */
  tree struct_type;

  /* Maximum count of cache elements could be allocated.  */
  int max_count;

  cache_type_info ()
    : init_field (NULL_TREE), struct_type (NULL_TREE), max_count (0) {}
};

/* A list that is completely generated from scratch in current function, is
   called dyn-list, for example:

     foo ()
       {
	 list = NULL;
	 ...
	 elem = new list_elem;
	 init (elem);
	 elem->next = list;

	 list = elem;
	 ...
       }

   The data structure describes how this kind of list is generated.  */

struct dyn_list_desc
{
  /* Statement to initialize list head.  */
  auto_vec<gimple *> head_init_stmts;

  /* Statements to link two lists.  */
  auto_vec<gimple *> head_link_stmts;

  /* Statements to allocate a new list element.  */
  auto_vec<gimple *> elem_alloc_stmts;
};

/* Since loads are cached in term of loop iteration, we will try to construct
   a dependent tree for all loads orginated from a loop iterator, which is
   described by the data structure.  */

class loop_iter_info
{
public:
  /* The iterator's PHI statement in the loop header.  */
  gphi *iter_phi;

  /* The iterator's initialization value outside the loop.  */
  tree iter_init;

  /* All statements that compose together as an iterator advancing
     operation.  */
  auto_vec<gimple *> iter_next_stmts;

  /* Root of dependent load tree for the iterator.  */
  dep_load *dep_load_root;

  /* The loop that the iterator lies in.  */
  class loop *mgo_loop;

  /* The outer loop that mgo starts from.  At first, it will be set to a
     legal one as outer as possible, and later be adjusted to an optimal
     one in which the best dependent load candidates could be obtained.  */
  class loop *mgo_outer_loop;

  /* The mgo outer loop has been finalized, and could not be further
     adjusted.  */
  bool outer_loop_adjustable_p;

  /* Expression to calculate length of cache array.  */
  tree cache_data_count;

  /* If the iterator is for a list that is dynamically created in current
     function, this points to a descriptor on the list.  */
  dyn_list_desc *dyn_list;

  /* Cache element type layout information.  */
  cache_type_info ct_info;

  /* SSA name to represent mgo transformation status at runtime.  */
  tree trans_ok;

  loop_iter_info (gphi *phi, const auto_vec<gimple *> &next_stmts,
		  const auto_vec<tree> &invar_opnds)
    : iter_phi (phi), dep_load_root (NULL), outer_loop_adjustable_p (true),
      cache_data_count (NULL_TREE), dyn_list (NULL), trans_ok (NULL_TREE)
  {
    unsigned i;
    tree opnd;

    iter_next_stmts.safe_splice (next_stmts);

    mgo_loop = gimple_bb (phi)->loop_father;
    iter_init = PHI_ARG_DEF_FROM_EDGE (phi, loop_preheader_edge (mgo_loop));

    /* Initialize to the outermost real loop.  */
    mgo_outer_loop = superloop_at_depth (mgo_loop, 1);

    FOR_EACH_VEC_ELT (invar_opnds, i, opnd)
      adjust_outer_loop_for_expr (opnd);
  }

  ~loop_iter_info ()
  {
    if (dep_load_root)
      delete dep_load_root;

    if (dyn_list)
      delete dyn_list;
  }

  bool post_check ();
  bool clean_trivial_dep_load () const;
  bool process_dep_load ();
  bool merge (class loop_iter_info *);
  void insert_mgo_code ();

private:
  bool adjust_outer_loop (class loop *outer_loop, bool exact = false)
  {
    gcc_checking_assert (mgo_outer_loop != mgo_loop);

    if (!outer_loop_adjustable_p)
      return mgo_outer_loop == outer_loop;

    if (flow_loop_nested_p (mgo_outer_loop, outer_loop))
      {
	mgo_outer_loop = outer_loop;

	if (outer_loop == mgo_loop)
	  return false;
      }

    gcc_checking_assert (flow_loop_nested_p (outer_loop, mgo_loop));

    if (exact)
      {
	if (mgo_outer_loop != outer_loop)
	  return false;

	outer_loop_adjustable_p = false;
      }

    return true;
  }

  /* Adjust mgo_outer_loop to a loop, as outer as possible, in which EXPR
     remains invariant.  */

  bool adjust_outer_loop_for_expr (tree expr)
  {
    class loop *invar_loop
	= outermost_invariant_loop_for_expr (mgo_loop, expr);

    /* The expression should be mgo_loop invariant at least.  */
    gcc_checking_assert (invar_loop);

    return adjust_outer_loop (invar_loop);
  }

  /* Enable runtime alias check or not.  */

  bool allow_runtime_alias_check_p () const
  {
    if (param_mgo_runtime_alias_check == 1)
      return true;

    if (param_mgo_runtime_alias_check == 2)
      return dyn_list != NULL;

    return false;
  }

  bool safe_new_memory_store_p (const gimple *) const;
  bool check_normal_iterator ();
  bool analyze_dyn_list_gen ();
  bool check_dyn_list_iterator ();
  unsigned analyze_dep_load_in_loop (class loop *);
  bool prune_dep_load () const;
  bool finalize_dep_load () const;

  void gen_intersect_range_check (dep_load *, gimple *) const;
  bool gen_runtime_alias_check (dep_load *) const;
  bool gen_cache_type_info ();
  void gen_caching_code () const;
  tree gen_cache_array () const;
  void gen_extended_dyn_list () const;
  tree gen_cache_data_pointer () const;
};

/* Return true if STMT is an assignment copy from a SSA name.  */

static bool
assign_ssa_copy_p (const gimple *stmt)
{
  if (!is_gimple_assign (stmt))
    return false;

  tree rhs = gimple_assign_rhs1 (stmt);

  if (gimple_assign_single_p (stmt))
    return TREE_CODE (rhs) == SSA_NAME;

  if (CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt)))
    {
      tree lhs = gimple_assign_lhs (stmt);

      if (TREE_CODE (rhs) == SSA_NAME
	  && types_compatible_p (TREE_TYPE (lhs), TREE_TYPE (rhs)))
	return true;
    }

  return false;
}

/* Return base address of MEMREF, if the address is an SSA name and the
   MEMREF's offset is 0, otherwise return NULL_TREE.  If non-NULL, offset
   to the base, access size and max_size, will be kept to POFFSET, PSIZE
   and PMAX_SIZE respectively  */

static tree
get_ref_base_addr_ssa (tree memref, poly_int64 *poffset = NULL,
		       poly_int64 *psize = NULL, poly_int64 *pmax_size = NULL)
{
  bool reverse;

  gcc_checking_assert ((!poffset == !psize) && (!psize == !pmax_size));

  if (poffset)
    memref = get_ref_base_and_extent (memref, poffset, psize, pmax_size,
				      &reverse);
  else
    memref = get_base_address (memref);

  if (memref && TREE_CODE (memref) == MEM_REF)
    {
      tree base = TREE_OPERAND (memref, 0);

      if (TREE_CODE (base) == SSA_NAME
	  && integer_zerop (TREE_OPERAND (memref, 1)))
	return base;
    }

  return NULL_TREE;
}

/* Returns outer parent loop of LOOP, and 0-based INDEX is numbered starting
   from LOOP itself to the outermost.  */

static inline class loop *
loop_parent (class loop *loop, unsigned index)
{
  unsigned depth = loop_depth (loop);

  gcc_checking_assert (depth >= index);

  return superloop_at_depth (loop, depth - index);
}

/* Returns the relative depth of LOOP against OUTER_LOOP.  */

static inline unsigned
loop_relative_depth (const class loop *outer_loop, const class loop *loop)
{
  gcc_checking_assert (outer_loop == loop
		       || flow_loop_nested_p (outer_loop, loop));

  return loop_depth (loop) - loop_depth (outer_loop);
}

/* Returns true if STMT is a memory allocation statement.  */

static bool
memory_alloc_stmt_p (const gimple *stmt)
{
  if (!gimple_call_builtin_p (stmt, BUILT_IN_NORMAL))
    return false;

  tree callee = gimple_call_fndecl (stmt);

  switch (DECL_FUNCTION_CODE (callee))
    {
    case BUILT_IN_MALLOC:
    case BUILT_IN_ALIGNED_ALLOC:
    case BUILT_IN_CALLOC:
    CASE_BUILT_IN_ALLOCA:
    case BUILT_IN_STRDUP:
    case BUILT_IN_STRNDUP:
      break;

    case BUILT_IN_REALLOC:
      /* TODO: Although realloc () involves side effect to existing memory, it
	 might be safe to consider it as a simple malloc-like operation in
	 most situations.  But here we conservatively ignore it.  */

    case BUILT_IN_POSIX_MEMALIGN:
      /* TODO: posix_memalign () places address of allocated memory in its
	 first argument, not directly returns the address to caller, which
	 also incurs non-allocation side effect to memory.  Now we also ignore
	 it.  */

    default:
      return false;
    }

  return true;
}

/* Given STMT1 and STMT2 in same basic block, return true if STMT1 is before
   STMT2, otherwise return false.  */

static bool
stmt_is_before_in_bb_p (const gimple *stmt1, const gimple *stmt2)
{
  bool stmt1_is_phi = gimple_code (stmt1) == GIMPLE_PHI;
  basic_block bb = gimple_bb (stmt1);

  gcc_checking_assert (bb == gimple_bb (stmt2));

  if (stmt1_is_phi ^ (gimple_code (stmt2) == GIMPLE_PHI))
    return stmt1_is_phi;

  gimple_stmt_iterator gsi;

  if (stmt1_is_phi)
    gsi = gsi_start_phis (bb);
  else
    gsi = gsi_start_bb (bb);

  for (; !gsi_end_p (gsi); gsi_next (&gsi))
    {
      if (gsi_stmt (gsi) == stmt1)
	return true;

      if (gsi_stmt (gsi) == stmt2)
	return false;
    }

  gcc_unreachable ();
  return false;
}

/* Return true if STMT may be in a path from HEAD_STMT to TAIL_STMT, and
   except being as start point, HEAD_STMT occurs only once, which looks like
   the pattern that STMT kills certain effect (value) of HEAD_STMT before
   reaching TAIL_STMT.  A precondition for the function is that HEAD_STMT is
   known to dominate TAIL_STMT.  */

static bool
stmt_may_in_path_of_dom_pair_p (const gimple *head_stmt,
				const gimple *tail_stmt, const gimple *stmt)
{
  basic_block head_bb = gimple_bb (head_stmt);
  basic_block tail_bb = gimple_bb (tail_stmt);
  basic_block bb = gimple_bb (stmt);

  gcc_checking_assert (dominated_by_p (CDI_DOMINATORS, tail_bb, head_bb));

  if (head_bb == bb)
    {
      if (stmt_is_before_in_bb_p (stmt, head_stmt))
	return false;

      if (tail_bb != bb)
	return true;

      return stmt_is_before_in_bb_p (stmt, tail_stmt);
    }
  else if (head_bb == tail_bb)
    return false;
  else if (tail_bb == bb)
    {
      if (stmt_is_before_in_bb_p (stmt, tail_stmt))
	return true;
    }
  else if (!dominated_by_p (CDI_DOMINATORS, bb, head_bb))
    /* The statement STMT must be dominated by HEAD_STMT, otherwise there is
       a path from entry -> STMT -> TAIL_STMT, but without HEAD_STMT, which
       conflicts with the precondition.  */
    return false;
  else if (dominated_by_p (CDI_DOMINATORS, tail_bb, bb))
    return true;

  class loop *comm_loop = find_common_loop (head_bb->loop_father,
					    tail_bb->loop_father);

  /* There is no such path if HEAD_STMT and TAIL_STMT are inside a loop which
     does not include STMT.  */
  if (!flow_bb_inside_loop_p (comm_loop, bb))
    return false;

  /* TODO: A more formalized algorithm to detect general control flow patterns
     by using data flow analysis method.  Now a simple check is used here.  If
     from TAIL_BB to HEAD_BB, only single predecessor is found, STMT must not
     be between them for it does not dominate TAIL_BB at this point.  */
  for (; tail_bb != head_bb; tail_bb = single_pred (tail_bb))
    {
      if (!single_pred_p (tail_bb))
	return true;
    }

  return false;
}

/* If we can determine STORE does not impact any value that has been
   mgo-cached, it is deemed to be mgo-caching-safe.  Especially, a newly-
   allocated memory might be part of dynamically-generated list for mgo,
   we should ensure that STORE just provides initialization value, not
   redefinition.  */

bool
loop_iter_info::safe_new_memory_store_p (const gimple *store) const
{
  if (!gimple_assign_single_p (store))
    return false;

  tree base = get_ref_base_addr_ssa (gimple_assign_lhs (store));

  if (!base)
    return false;

  gimple *base_stmt = SSA_NAME_DEF_STMT (base);

  if (!memory_alloc_stmt_p (base_stmt))
    return false;

  /* Do not hope that memory allocation occurs in iterator loop.
     TODO: this is not a necessary check, could be removed.  */
  if (flow_bb_inside_loop_p (mgo_loop, gimple_bb (base_stmt)))
    return false;

  /* For a store to new list element, if memory allocation (marked as ALLOC)
     and the store (STORE) does not cross list iterating loop (LIST), this
     store is an initialization, otherwise it is a redefinition.

       ALLOC;                                 ALLOC;

       STORE; [ initialization ]              loop {
						 LIST;
       loop {                                 }
	  LIST;
       }                                      STORE;   [ Redefinition ]

     The former is safe for mgo-caching, while the latter is not.  */
  if (stmt_may_in_path_of_dom_pair_p (base_stmt, store, iter_phi))
    return false;

  return true;
}

/* Try to deduce a representable cache data count expression for mgo on the
   iterator, which should be not less than iteration count.  And check whether
   there exists an outer loop in which initial value of the iterator and the
   cache data count expression must be invariant.  Return false if some
   condition could not be satisfied.  */

bool
loop_iter_info::check_normal_iterator ()
{
  if (!adjust_outer_loop_for_expr (iter_init))
    return false;

  tree niter = get_loop_iterations (mgo_loop);

  if (niter == chrec_dont_know)
    return false;

  if (!adjust_outer_loop_for_expr (niter))
    return false;

  /* Here cache data count is assumed to be signed integer, which might be
     too stricter for unsigned integer loop index, but should be enough in
     real application.  So maximum count does not exceed upper bound of
     signed integer type.  */
  tree niter_type = TREE_TYPE (niter);
  int prec = MIN (TYPE_PRECISION (niter_type), TYPE_PRECISION (sizetype));
  wide_int max_value = wi::max_value (prec, SIGNED);
  unsigned HOST_WIDE_INT max_count = param_mgo_max_cache_array_length;

  if (wi::fits_uhwi_p (max_value))
    max_count = MIN (max_count, max_value.to_uhwi ());

  /* Skip mgo if cache data count thresholds are unreasonable.  */
  if (max_count < (unsigned HOST_WIDE_INT) param_mgo_min_cache_array_length)
    return false;

  ct_info.max_count = max_count;
  cache_data_count = niter;

  return true;
}

/* Return true if ALLOC_STMT would allocate a memory space whose totally size
   equals ELEM_SIZE.  */

static bool
alloc_only_one_elem_p (gimple *alloc_stmt, tree elem_size)
{
  tree callee = gimple_call_fndecl (alloc_stmt);

  switch (DECL_FUNCTION_CODE (callee))
    {
    case BUILT_IN_MALLOC:
    CASE_BUILT_IN_ALLOCA:
      return tree_int_cst_equal (elem_size, gimple_call_arg (alloc_stmt, 0));

    case BUILT_IN_ALIGNED_ALLOC:
      return tree_int_cst_equal (elem_size, gimple_call_arg (alloc_stmt, 1));

    case BUILT_IN_CALLOC:
      {
	tree arg0 = gimple_call_arg (alloc_stmt, 0);
	tree arg1 = gimple_call_arg (alloc_stmt, 1);

	if (TREE_CODE (arg0) != INTEGER_CST || TREE_CODE (arg1) != INTEGER_CST)
	  return false;

	return tree_int_cst_equal (elem_size,
				   size_binop (MULT_EXPR, arg0, arg1));
      }

    default:
      return false;
    }
}

/* Return true if STMT may modify memory specified by BASE + OFFSET.  If side
   effect by STMT could not be determined, or affected size is not equal to
   SIZE, it means a clobber operation, and *CLOBBER will be set to true.  */

static bool
store_to_memory_p (gimple *stmt, tree base, poly_int64 &offset,
		   poly_int64 &size, bool *clobber)
{
  if (!gimple_store_p (stmt))
    return false;

  poly_int64 st_offset, st_size, st_max_size;
  tree st_base = get_ref_base_addr_ssa (gimple_assign_lhs (stmt), &st_offset,
					&st_size, &st_max_size);

  if (!st_base || !operand_equal_p (st_base, base))
    return false;

  if (known_eq (offset, st_offset) && known_eq (size, st_size))
    *clobber = maybe_ne (size, st_max_size) || gimple_has_volatile_ops (stmt);
  else if (known_le (offset + size, st_offset))
    return false;
  else if (!known_size_p (st_max_size))
    *clobber = true;
  else if (known_ge (offset, st_offset + st_max_size))
    return false;
  else
    *clobber = true;

  return true;
}

/* Return base address if STMT is a non-volatile memory load with same OFFSET
   and SIZE.  And if OFFSET and SIZE do not contain valid incoming values,
   they are used to receive resulting offset and size.  */

extern tree
load_from_memory_p (gimple *stmt, poly_int64 &offset, poly_int64 &size)
{
  if (!gimple_assign_load_p (stmt) || gimple_has_volatile_ops (stmt))
    return NULL_TREE;

  poly_int64 ld_offset, ld_size, ld_max_size;
  tree base = get_ref_base_addr_ssa (gimple_assign_rhs1 (stmt), &ld_offset,
				     &ld_size, &ld_max_size);

  if (!base || !known_size_p (ld_max_size) || !known_eq (ld_size, ld_max_size))
    return NULL_TREE;

  if (!known_size_p (size))
    {
      offset = ld_offset;
      size = ld_size;
    }
  else if (!known_eq (offset, ld_offset) || !known_eq (size, ld_size))
    return NULL_TREE;

  return base;
}

/* Scan all iterator def stmts and store stmts to list->next outside the loop.
   Check whether iterated data corresponds to the same data set, which implies
   we are capable of tracking down the memory access via iterator to make sure
   iterated data could be cached.  For example, the code below is not trackable
   because parameter p may point to different list.

   f (class data *p)
   {
     iter = p;
     while (iter)
     {
       ... = *iter;
       iter = iter->next;
     }
   }

   TODO: Support adding new elements to the list tail or any other element.  */

bool
loop_iter_info::analyze_dyn_list_gen ()
{
  poly_int64 offset = -1;
  poly_int64 size = -1;

  /* Extract offset and size of memory access to list->next field.  */
  if (!load_from_memory_p (iter_next_stmts[0], offset, size))
    return false;

  /* List contains elements generated outside current function, so skip it. */
  if (TREE_CODE (iter_init) != SSA_NAME || SSA_NAME_IS_DEFAULT_DEF (iter_init)
      || !POINTER_TYPE_P (TREE_TYPE (iter_init)))
    return false;

  tree list_type = TREE_TYPE (TREE_TYPE (iter_init));
  tree elem_size = TYPE_SIZE_UNIT (list_type);

  /* List element type should be a struct/union.  */
  if (!AGGREGATE_TYPE_P (list_type))
    return false;

  class loop *list_init_loop = mgo_loop;
  auto_vec<tree> worklist;
  auto_bitmap visited;

  dyn_list = new dyn_list_desc ();

  /* Traverse all define statements starting from iter_init.  Mark it as
     visited to avoid additional check in the loop below.  */
  bitmap_set_bit (visited, SSA_NAME_VERSION (iter_init));
  worklist.safe_push (iter_init);

  /* Search all define statements backwards to find all iterators.  */
  do
    {
      tree name = worklist.pop ();
      gimple *stmt = SSA_NAME_DEF_STMT (name);
      basic_block bb = gimple_bb (stmt);

      /* If def stmt is from the target loop, it implies that the link list
	 may be changed in target loop.  */
      if (flow_bb_inside_loop_p (mgo_loop, bb))
	return false;

      list_init_loop = find_common_loop (list_init_loop, bb->loop_father);

      /* TODO: init loop could be the outer most loop.  */
      if (!loop_outer (list_init_loop))
	return false;

      /* Push all def stmts of iters in rhs into worklist.  */
      auto_vec<tree, 6> next_defs;
      unsigned i;

      if (memory_alloc_stmt_p (stmt))
	{
	  gimple *use_stmt;
	  imm_use_iterator use_iter;

	  /* Check all uses of def_stmt to find list->next = head.  */
	  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, name)
	    {
	      bool clobber;

	      /* Exclude store to fields other than new_elem->next. Here we
		 only check whether list->next may be clobbered by other stores
		 to the same list element.  And check on other unrelated stores
		 will be implicitly covered by similar check on list->next
		 inside mgo loop later, since alias analysis is control flow
		 insensitive, same field memory access will have same alias
		 analysis result, regardless of its position.  */
	      if (!store_to_memory_p (use_stmt, name, offset, size, &clobber))
		continue;

	      if (clobber || !gimple_assign_single_p (use_stmt))
		return false;

	      /* Allow assigning to new_elem->next a SSA name, which is the
		 head of link list the code is generating.  */
	      tree rhs = gimple_assign_rhs1 (use_stmt);

	      /* Even list->next would be initialized somewhere, it does not
		 mean linkage of the list has been properly setup when a loop
		 attempts to traverse the list. A buggy example:

		   list = alloc();

		   loop (list)
		     {
		       ....
		     }

		   list->next = ...

		This would incur undefined behavior, and mgo will allow it by
		assuming list->next is zero-cleared.  */
	      if (TREE_CODE (rhs) == SSA_NAME)
		{
		  dyn_list->head_link_stmts.safe_push (use_stmt);
		  next_defs.safe_push (rhs);
		}
	      else if (!integer_zerop (rhs))
		{
		  /* Only allow a special case: new_elem->next = NULL.  */
		  return false;
		}
	    }

	  /* Each allocated element should be of the same size of list struct
	     type.  */
	  if (!alloc_only_one_elem_p (stmt, elem_size))
	    return false;

	  dyn_list->elem_alloc_stmts.safe_push (stmt);
	}
      else if (gimple_code (stmt) == GIMPLE_PHI)
	{
	  bool head_init_p = false;

	  for (i = 0; i < gimple_phi_num_args (stmt); ++i)
	    {
	      tree arg = gimple_phi_arg_def (stmt, i);

	      if (integer_zerop (arg))
		head_init_p = true;
	      else
		next_defs.safe_push (arg);
	    }

	  if (head_init_p)
	    dyn_list->head_init_stmts.safe_push (stmt);
	}
      else if (tree base = load_from_memory_p (stmt, offset, size))
	{
	  /* Found list = base->next.  Continue to trace the base.  */
	  next_defs.safe_push (base);
	}
      else if (assign_ssa_copy_p (stmt))
	next_defs.safe_push (gimple_assign_rhs1 (stmt));
      else
	return false;

      FOR_EACH_VEC_ELT (next_defs, i, name)
	{
	  /* If def stmt is for argument, we will not be able to know how link
	     list is generated.  */
	  if (TREE_CODE (name) != SSA_NAME || SSA_NAME_IS_DEFAULT_DEF (name))
	    return false;

	  if (bitmap_set_bit (visited, SSA_NAME_VERSION (name)))
	    worklist.safe_push (name);
	}
    } while (!worklist.is_empty ());

  /* Check if the original list struct can be extended for cache data.
     head_init_stmts is not necessary as there may be implicit initializations
     such as calloc a new element as head.  */
  if (dyn_list->elem_alloc_stmts.is_empty ()
      || dyn_list->head_link_stmts.is_empty ())
    return false;

  return adjust_outer_loop (list_init_loop, true);
}

/* Check if iterator is over a list that is dynamically created in current
   function.  */

bool
loop_iter_info::check_dyn_list_iterator ()
{
  /* Now only support iterator advancing as list = list->next.  */
  if (iter_next_stmts.length () != 1)
    return false;

  if (!analyze_dyn_list_gen ())
    return false;

  /* The more loops between the list init point and list traversing point
     (i.e. the target loop), the more benefits we can get from data caching,
     as target loop will access same list element more than once.  */
  unsigned dist_depth = loop_relative_depth (mgo_outer_loop, mgo_loop);
  unsigned i;
  gimple *stmt;

  gcc_checking_assert (dist_depth);

  /* If NULL is entry-init arg of PHI in the init loop header, its origin is
     actually from outside.  Then the distance depth is increased by 1.  E.g.

       head = NULL             // head is from outside of init loop
       mgo outer loop () {
	   ...                 // add new elements to head
	   target loop () {
	      ...
	   }
       }
  */
  FOR_EACH_VEC_ELT (dyn_list->head_init_stmts, i, stmt)
    if (gimple_bb (stmt) == mgo_outer_loop->header)
      {
	dist_depth++;
	break;
      }

  /* Skip list if its lifetime is started in the immediate outer loop of the
     target loop, as each list element is accessed at most once.  */
  if (dist_depth == 1)
    return false;

  return true;
}

/* Check if iterator is qualified for mgo transformation.  */

bool
loop_iter_info::post_check ()
{
  class loop *mgo_init_outer_loop = mgo_outer_loop;

  if (!check_normal_iterator ())
    {
      /* Restore mgo_outer_loop to initial outer loop and try to identify
	 whether it is an iterator over dynamically-created list.  */
      mgo_outer_loop = mgo_init_outer_loop;

      if (!check_dyn_list_iterator ())
	return false;
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      unsigned i;
      gimple *stmt;

      fprintf (dump_file, "> iterator found in loop %d (depth %u):\n",
	       mgo_loop->num, loop_depth (mgo_loop));
      print_gimple_stmt_with_bb (dump_file, iter_phi);

      fprintf (dump_file, "> iterator advancing stmts:\n");
      FOR_EACH_VEC_ELT (iter_next_stmts, i, stmt)
	print_gimple_stmt_with_bb (dump_file, stmt);

      if (cache_data_count)
	{
	  fprintf (dump_file, "> iterator cache data count:\n");
	  print_generic_expr (dump_file, cache_data_count, TDF_NONE);
	  fprintf (dump_file, "\n");
	}

      fprintf (dump_file, "> iterator mgo outer loop %d (depth %u)\n",
	       mgo_outer_loop->num, loop_depth (mgo_outer_loop));

      if (dyn_list)
	{
	  fprintf (dump_file, "> dyn-list head_link_stmts:\n");
	  FOR_EACH_VEC_ELT (dyn_list->head_link_stmts, i, stmt)
	    print_gimple_stmt_with_bb (dump_file, stmt, 0, TDF_NONE, true);

	  fprintf (dump_file, "> dyn-list head_init_stmts:\n");
	  FOR_EACH_VEC_ELT (dyn_list->head_init_stmts, i, stmt)
	    print_gimple_stmt_with_bb (dump_file, stmt, 0, TDF_NONE, true);

	  fprintf (dump_file, "> dyn-list elem_alloc_stmts:\n");
	  FOR_EACH_VEC_ELT (dyn_list->elem_alloc_stmts, i, stmt)
	    print_gimple_stmt_with_bb (dump_file, stmt, 0, TDF_NONE, true);
	}

      fprintf (dump_file, "\n");
    }

  return true;
}

/* Some library memory allocation statement may modify 'errno' variable if
   allocation fails, which impacts alias analysis for memory access.  Return
   true if memory allocation STMT would change 'errno'.  */

static bool
noalias_memory_alloc_stmt_p (gimple *stmt)
{
  if (!memory_alloc_stmt_p (stmt))
    return false;

  tree lhs = gimple_call_lhs (stmt);

  if (!lhs || TREE_CODE (lhs) != SSA_NAME)
    return false;

  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);

  for (gsi_next (&gsi); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *next_stmt = gsi_stmt (gsi);

      if (gimple_vuse (next_stmt))
	{
	  tree memref;

	  if (!gimple_assign_single_p (next_stmt))
	    break;

	  if (gimple_vdef (next_stmt))
	    memref = get_base_address (gimple_assign_lhs (next_stmt));
	  else
	    memref = get_base_address (gimple_assign_rhs1 (next_stmt));

	  if (TREE_CODE (memref) != MEM_REF || TREE_OPERAND (memref, 0) != lhs)
	    break;

	  /* The allocated memory is accessed just after allocation, which
	     means it is not null, and will not touch the global libc
	     errno variable.  */
	  return true;
	}
    }

  return false;
}

/* Return true if we can extract address of MEMREF.   */

static inline bool
can_take_address_of (tree memref)
{
  if (mgo_runtime_alias_check_on_bit_field)
    {
      /* Allow taking address of even bit field.  */
      if (TREE_CODE (memref) == COMPONENT_REF)
	memref = TREE_OPERAND (memref, 0);
    }
  else if (TREE_CODE (memref) == BIT_FIELD_REF
	   || contains_bitfld_component_ref_p (memref))
    return false;

  return !may_be_nonaddressable_p (memref);
}

/* Analyze each load in dependeng load tree to check whether it could keep
   invariant when OUTER_LOOP is included in loop hierarchy for mgo. Collect
   all stores in OUTER_LOOP, which may clobber loads in dependent load tree
   and could be resolved by adding runtime alias check.  If some unresolvable
   store is found, such as call statement, impacted tree of child dependent
   load will be excluded from candidates for caching.  Return true if there
   is any caching candidate in dependent load tree when OUTER_LOOP is
   present.  */

unsigned
loop_iter_info::analyze_dep_load_in_loop (class loop *outer_loop)
{
  class loop *skip_loop = NULL;
  unsigned index = loop_relative_depth (outer_loop, mgo_loop);
  loop_mgo_info *outer_mgo_info = get_mgo_info (outer_loop);
  dep_load_walker dl_walker;
  dep_load *dl;
  unsigned n_loads = 0;
  gimple *stmt;
  gimple *store;
  ao_ref ref;
  unsigned i;

  if (index)
    skip_loop = loop_parent (mgo_loop, index - 1);

  get_vdefs_in_loop (outer_loop);

  /* We should ensure that iterator advances with constant state transition.
     To be specific, this means that index iterator has constant stride, and
     list iterator has constant linkage.  So, all memory operands used in
     iterator advancing operation is required to be invariant in
     OUTER_LOOP.  */
  FOR_EACH_VEC_ELT (iter_next_stmts, i, stmt)
    {
      unsigned j;

      if (!gimple_vuse (stmt))
	continue;
      else if (gimple_assign_load_p (stmt))
	ao_ref_init (&ref, gimple_assign_rhs1 (stmt));
      else if (outer_mgo_info->has_vdefs ())
	return 0;

      /* Non-pure call and gnu-asm statements are always conservatively
	 assumed to impact all memory locations.  So check alias with these
	 statements before normal stores with the hope of using them as
	 shortcut terminators to memory alias analysis.  */
      FOR_EACH_VEC_ELT (outer_mgo_info->other_vdefs, j, store)
	{
	  if (skip_loop
	      && flow_bb_inside_loop_p (skip_loop, gimple_bb (store)))
	    continue;

	  if (noalias_memory_alloc_stmt_p (store))
	    continue;

	  if (stmt_may_clobber_ref_p_1 (store, &ref))
	    return 0;
	}

      FOR_EACH_VEC_ELT (outer_mgo_info->store_vdefs, j, store)
	{
	  if (skip_loop
	      && flow_bb_inside_loop_p (skip_loop, gimple_bb (store)))
	    continue;

	  if (stmt_may_clobber_ref_p_1 (store, &ref)
	      && !safe_new_memory_store_p (store))
	    return 0;
	}
    }

  WALK_DEP_LOAD_PRE_ORDER (dl_walker, dep_load_root, dl)
    {
      if (index)
	{
	  dep_load_info *last_dl_info = dl->analysis_for_loops.last ();

	  /* Here is an implicit constraint on invocation of this function.
	     We assume that the function should be called from LOOP to its
	     outer parents one-by-one.  Here add assertion to detect violation
	     of this assumption.  */
	  if (last_dl_info->excluded)
	    {
	      /* If the load is unable to resolve alias in certain inner
		 parent loop, it is also not in outer parent loop.  */
	      gcc_checking_assert (!dl->is_root ());

	      dl_walker.skip_children ();
	      continue;
	    }

	  gcc_checking_assert (dl->analysis_for_loops.length () == index);
	}

      dep_load_info *dl_info = new dep_load_info ();

      dl->analysis_for_loops.safe_push (dl_info);

      if (dl->is_root ())
	continue;

      dl_info->excluded = true;

      tree ld_memref = gimple_assign_rhs1 (dl->def_stmts[0]);
      tree opnd;

      FOR_EACH_VEC_ELT (dl->invar_opnds, i, opnd)
	{
	  /* If an operand for load address computation becomes variant in
	     OUTER_LOOP, the load has to be excluded.  */
	  if (!expr_invariant_in_loop_p (outer_loop, opnd))
	    goto walk_next;
	}

      ao_ref_init (&ref, ld_memref);

      FOR_EACH_VEC_ELT (outer_mgo_info->other_vdefs, i, store)
	{
	  if (skip_loop
	      && flow_bb_inside_loop_p (skip_loop, gimple_bb (store)))
	    continue;

	  if (noalias_memory_alloc_stmt_p (store))
	    continue;

	  if (stmt_may_clobber_ref_p_1 (store, &ref))
	    {
	      dl_info->mod_stmts.safe_push (store);
	      goto walk_next;
	    }
	}

      FOR_EACH_VEC_ELT (outer_mgo_info->store_vdefs, i, store)
	{
	  if (skip_loop
	      && flow_bb_inside_loop_p (skip_loop, gimple_bb (store)))
	    continue;

	  if (!stmt_may_clobber_ref_p_1 (store, &ref)
	      || safe_new_memory_store_p (store))
	    continue;

	  /* Do not cache a load that will be killed, or runtime alias check
	     is disabled.  */
	  if (!allow_runtime_alias_check_p ()
	      || stmt_kills_ref_p (store, &ref))
	    {
	      dl_info->mod_stmts.safe_push (store);
	      goto walk_next;
	    }

	  tree st_memref = gimple_assign_lhs (store);

	  /* To add runtime alias check, we need to fetch and compare
	     address of store and load.  So if objects being involved are
	     nonaddressable, exclude the load for no way to do that.  */
	  if (!can_take_address_of (st_memref)
	      || !can_take_address_of (ld_memref))
	    {
	      dl_info->mod_stmts.safe_push (store);
	      goto walk_next;
	    }

	  dl_info->mod_stmts.safe_push (store);
	}

      dl_info->excluded = false;
      n_loads++;

    walk_next:
      /* If a load is excluded, no need to process its children dependent
	 load tree.  */
      if (dl_info->excluded)
	dl_walker.skip_children ();
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> Analyzing dependent load in loop %d "
	       "(depth %u):\n", outer_loop->num, loop_depth (outer_loop));
      dump_dep_load (dump_file, dep_load_root);
    }

  return n_loads;
}

/* In most situations, there is no benefit to cache level 1 load, so remove
   the load if it has no children.  Return true if the root contains nothing.
   TODO: mgo could also be applied to the case where there are more than one
   level 1 loads, and all of them are from different memory regions.
   For example:

     loop (i)                  loop (i)
       {                         {
	 ... = A[i];               ... = cache_arr[i].A;
	 ... = B[i];      =>       ... = cache_arr[i].B;
	 ... = C[i];               ... = cache_arr[i].C;
       }                         }

   This can improve cache efficiency by reducing hardware memory access
   streams.  */

bool
loop_iter_info::clean_trivial_dep_load () const
{
  dep_load *dl;
  unsigned i;

  FOR_EACH_VEC_ELT (dep_load_root->children, i, dl)
    {
      if (dl->is_leaf ())
	dep_load_root->remove_child (i--);
      else
	dl->need_caching = false;
    }

  return dep_load_root->is_leaf ();
}

/* Check if there exists aliased store in some path from the START_STMT
   to the loads represented by DL.  */

static bool
keep_unchanged_from_stmt (const gimple *start_stmt, const dep_load *dl)
{
  dep_load_info *dl_info = dl->analysis_for_loops[0];
  gimple *def_stmt = dl->def_stmts[0];
  gimple *mod_stmt;
  unsigned i;

  FOR_EACH_VEC_ELT (dl_info->mod_stmts, i, mod_stmt)
    if (stmt_may_in_path_of_dom_pair_p (start_stmt, def_stmt, mod_stmt))
      return false;

  return true;
}

/* Check whether DL0 and DL1 are from same struct/class object.  */

static bool
has_same_component_base_p (const dep_load *dl0, const dep_load *dl1)
{
  tree memref0 = gimple_assign_rhs1 (dl0->def_stmts[0]);
  tree memref1 = gimple_assign_rhs1 (dl1->def_stmts[0]);
  enum tree_code code0 = TREE_CODE (memref0);
  enum tree_code code1 = TREE_CODE (memref1);

  /* TODO: Two loads may root to different inner objects of same struct/class
     (e.g.  base->arr[3].f1 and base->f2).  */
  if (code0 != COMPONENT_REF && code0 != BIT_FIELD_REF &&
      code0 != REALPART_EXPR && code0 != IMAGPART_EXPR)
    return false;

  if (code1 != COMPONENT_REF && code1 != BIT_FIELD_REF &&
      code1 != REALPART_EXPR && code1 != IMAGPART_EXPR)
    return false;

  return operand_equal_p (TREE_OPERAND (memref0, 0), TREE_OPERAND (memref1, 0),
			  OEP_ADDRESS_OF);
}

/* Prune dependent load tree to exclude some loads to avoid runtime trap and
   ease runtime alias check.  Return true if dependent load tree is not
   empty.  */

bool
loop_iter_info::prune_dep_load () const
{
  basic_block last_always_executed = mgo_loop->latch;
  auto_vec<edge> exits = get_loop_exit_edges (mgo_loop);
  unsigned i;
  edge ex;
  dep_load_walker dl_walker;
  dep_load *dl;

  /* Get the last always executed basic block in loop.  */
  FOR_EACH_VEC_ELT (exits, i, ex)
    last_always_executed = nearest_common_dominator (
			CDI_DOMINATORS, last_always_executed, ex->src);

  WALK_DEP_LOAD_PRE_ORDER (dl_walker, dep_load_root, dl)
    {
      dep_load *child;

      if (dl->is_leaf ())
	continue;

      /* If a child is always executed, it is non-trapping.  As other
	 children are loaded from the same base (of structure type),
	 they are also non-trapping.  */
      auto_delete_vec<dep_load> may_trap_children;

      /* Move the child that doesn't always execute in the loop to
	 'may_trap_children'.  */
      FOR_EACH_VEC_ELT (dl->children, i, child)
	{
	  if (!dominated_by_p (CDI_DOMINATORS, last_always_executed,
			       gimple_bb (child->def_stmts[0])))
	    {
	      dl->children.unordered_remove (i--);
	      may_trap_children.safe_push (child);
	    }
	}

      unsigned non_trap_count = dl->children.length ();

      /* If a child in 'may_trap_children' has the same base as the ones that
	 always execute in the loop, move it back.  */
      FOR_EACH_VEC_ELT (may_trap_children, i, child)
	{
	  for (unsigned j = 0; j < non_trap_count; j++)
	    {
	      if (has_same_component_base_p (child, dl->children[j]))
		{
		  dl->children.safe_push (child);
		  may_trap_children.unordered_remove (i--);
		  break;
		}
	    }
	}

      if (dump_file && (dump_flags & TDF_DETAILS)
	  && !may_trap_children.is_empty ())
	{
	  fprintf (dump_file, "> Pruning may-trap dependent loads:\n");

	  FOR_EACH_VEC_ELT (may_trap_children, i, child)
	    dump_dep_load (dump_file, child);
	}

      FOR_EACH_VEC_ELT (dl->children, i, child)
	{
	  if (child->excluded_p (0))
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "> Pruning dependent load against "
				      "mgo:\n");

		  dump_dep_load (dump_file, child);
		}

	      dl->remove_child (i--);
	    }
	  else if (!keep_unchanged_from_stmt (iter_phi, child))
	    {
	      /* A load is "pre-clobbered", if there exists aliased store in
		 some path from iterator definition point to the load.  Since
		 we will pre-cache value of the load at loop header, these
		 stores may pre-clobber the value and we have to reload it
		 after true alias is detected, which would complicate
		 generation of runtime alias checking code.  Now we simply
		 prune it, and as a TODO to support that.  */
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "> Pruning pre-clobbered dependent "
				      "load:\n");

		  dump_dep_load (dump_file, child);
		}

	      dl->remove_child (i--);
	    }
	}
    }

  return !dep_load_root->is_leaf ();
}

/* Flag on statement to indicate it is a node in dependent load tree.  */
#define GF_DEP_LOAD    GF_PLF_1

/* Flag on statement to indicate it is included in dependent load tree. */
#define GF_INCLUDED    GF_PLF_2

/* Finalize dependent load tree by removing those loads with unresolvable
   store alias.  Return true if final dependent load tree is not empty.  */

bool
loop_iter_info::finalize_dep_load () const
{
  dep_load_walker dl_walker;
  dep_load *dl;
  dep_load *child;
  unsigned outer_loop_index = loop_relative_depth (mgo_outer_loop, mgo_loop);
  unsigned i;

  WALK_DEP_LOAD_PRE_ORDER (dl_walker, dep_load_root, dl)
    {
      FOR_EACH_VEC_ELT (dl->children, i, child)
	{
	  if (!child->excluded_p (outer_loop_index))
	    continue;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "> Pruning dependent load against mgo:\n");
	      dump_dep_load (dump_file, child);
	    }

	  dl->remove_child (i--);
	}
    }

  if (clean_trivial_dep_load ())
    return false;

  auto_vec<gimple *> worklist;
  auto_bitmap visited;

  WALK_DEP_LOAD_PRE_ORDER (dl_walker, dep_load_root, dl)
    {
      gimple *stmt;
      unsigned j;

      /* Merge obviously identical dependent loads to save caching cost and
	 and data size.  */
      FOR_EACH_VEC_ELT (dl->children, i, child)
	{
	  tree memref = gimple_assign_rhs1 (child->def_stmts[0]);
	  tree type = TREE_TYPE (memref);
	  dep_load *other;

	  FOR_EACH_VEC_ELT_FROM (dl->children, j, other, i + 1)
	    {
	      tree other_memref = gimple_assign_rhs1 (other->def_stmts[0]);
	      tree other_type = TREE_TYPE (other_memref);

	      if (operand_equal_p (memref, other_memref, OEP_ADDRESS_OF)
		  && types_compatible_p (type, other_type))
		{
		  child->def_stmts.safe_splice (other->def_stmts);
		  child->children.safe_splice (other->children);
		  other->children.release ();
		  dl->remove_child (j--);
		}
	    }
	}

      FOR_EACH_VEC_ELT (dl->children, i, child)
	{
	  FOR_EACH_VEC_ELT (child->def_stmts, j, stmt)
	    {
	      gcc_checking_assert (gimple_plf (stmt, GF_DEP_LOAD));
	      gimple_set_plf (stmt, GF_INCLUDED, true);
	    }

	  FOR_EACH_VEC_ELT (child->addr_stmts, j, stmt)
	    {
	      gcc_checking_assert (!gimple_plf (stmt, GF_DEP_LOAD));
	      gimple_set_plf (stmt, GF_INCLUDED, true);
	    }
	}

      /* In dependent load tree, the root node does not need to be cached,
	 while the leaf node should always be.  */
      if (!dl->need_caching || dl->is_leaf ())
	continue;

      dl->need_caching = false;
      worklist.safe_splice (dl->def_stmts);

      /* If a node in dependent load tree is only used by its children nodes,
	 it acts as a temporary to generate other nodes, so does not need to
	 allocate a slot in cache data space.  */
      do
	{
	  tree value = gimple_get_lhs (worklist.pop ());
	  gimple *use_stmt;
	  imm_use_iterator use_iter;

	  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, value)
	    {
	      if (is_gimple_debug (use_stmt))
		continue;

	      if (!stmt_inside_loop_p (mgo_loop, use_stmt)
		  || !gimple_plf (use_stmt, GF_INCLUDED))
		{
		  /* Find some external use of load value, have to
		     cache it.  */
		  dl->need_caching = true;

		  /* Clear worklist for following reuse.  */
		  worklist.truncate (0);
		  break;
		}

	      gcc_checking_assert (gimple_uid (use_stmt));

	      if (!gimple_plf (use_stmt, GF_DEP_LOAD)
		  && bitmap_set_bit (visited, gimple_uid (use_stmt)))
		worklist.safe_push (use_stmt);
	    }
	} while (!worklist.is_empty ());
    }

  return true;
}

/* Checks whether LOOP has any abnormal/eh exit where we could not insert
   statement.  */

static inline bool
has_abnormal_or_eh_exit_p (class loop *loop)
{
  auto_vec<edge> exits = get_loop_exit_edges (loop);
  unsigned i;
  edge ex;

  FOR_EACH_VEC_ELT (exits, i, ex)
    if (ex->flags & (EDGE_ABNORMAL | EDGE_EH))
      return true;

  return false;
}

/* Main entry to perform analysis and preparation on dependent load tree for
   mgo transformation.  */

bool
loop_iter_info::process_dep_load ()
{
  if (dep_load_root->is_leaf ())
    return false;

  if (!analyze_dep_load_in_loop (mgo_loop))
    return false;

  if (!prune_dep_load ())
    return false;

  gcc_checking_assert (flow_loop_nested_p (mgo_outer_loop, mgo_loop));

  class loop *outer_loop = mgo_loop;
  unsigned n_loads = 1;

  /* Analyze dependent load tree in all parent loops one by one, and try to
     identify the outermost loop that is qualified for mgo.  */
  do
    {
      class loop *next_outer_loop = loop_outer (outer_loop);
      unsigned next_n_loads;

      if (has_abnormal_or_eh_exit_p (next_outer_loop))
	break;

      next_n_loads = analyze_dep_load_in_loop (next_outer_loop);

      if (next_n_loads < n_loads)
	break;

      n_loads = next_n_loads;
      outer_loop = next_outer_loop;
    } while (outer_loop != mgo_outer_loop);

  /* For outer loop, the closer to mgo loop, the more dependent load
     candidates, but the higher mgo-caching initialization cost.  Now we
     simplely choose the outermost loop that contains maximum dependent
     loads.  */
  if (!adjust_outer_loop (outer_loop))
    return false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "> Final mgo outer loop %d (depth %u)\n\n",
	     mgo_outer_loop->num, loop_depth (mgo_outer_loop));

  return finalize_dep_load ();
}

/* Try to merge with dependent load tree of OTHER iterator if two iterators
   would advance at the same pace.  */

bool
loop_iter_info::merge (loop_iter_info *other)
{
  if (dyn_list || other->dyn_list)
    return false;

  dep_load *dl_root = dep_load_root;
  dep_load *dl_root_other = other->dep_load_root;

  gcc_checking_assert (cache_data_count == other->cache_data_count);

  dl_root->def_stmts.safe_splice (dl_root_other->def_stmts);
  dl_root->children.safe_splice (dl_root_other->children);
  dl_root_other->children.release ();

  adjust_outer_loop (other->mgo_outer_loop);
  return true;
}

static inline char *
append_mgo_suffix (const char *name)
{
  char suffix[32];

  sprintf (suffix, "_%u", mgo_name_suffix_id);
  return concat (name, suffix, NULL);
}

/* Create a SSA name definition statement at preheader of LOOP, whose
   initialization arg is INIT. STR_NAME, if non-NULL, will be concatenated
   to be name prefix of the SSA name.  */

static tree
make_ssa_name_before_loop (const class loop *loop, tree init,
			   const char *str_name = NULL)
{
  basic_block preheader = loop_preheader_edge (loop)->src;
  gimple_stmt_iterator gsi = gsi_last_bb (preheader);
  tree name = NULL_TREE;
  if (str_name != NULL)
    {
      char *tmp_name = append_mgo_suffix (str_name);
      name = make_temp_ssa_name (TREE_TYPE (init), NULL, tmp_name);
      free (tmp_name);
    }
  else
    name = make_ssa_name (TREE_TYPE (init));

  init = force_gimple_operand_gsi (&gsi, init, false,
				   NULL_TREE, false, GSI_NEW_STMT);

  build_assign_after_bb (preheader, name, init);
  return name;
}

/* ----------------------------------------------------------------------- *
 *                         GENERATE ALIAS CHECK CODE                       *
 * ----------------------------------------------------------------------- */

/* Extract address lower/upper inclusive bound of MEMREF into ADDR_MIN and
   ADDR_MAX.  If extra statements are generated, they will be placed before
   position denoted by GSI.  */

static void
gen_memref_address_range (tree memref, tree &addr_min, tree &addr_max,
			  gimple_stmt_iterator *gsi)
{
  poly_int64 bitsize, bitpos;
  tree offset;
  machine_mode mode;
  int unsignedp, reversep, volatilep = 0;
  tree base = get_inner_reference (memref, &bitsize, &bitpos, &offset, &mode,
				   &unsignedp, &reversep, &volatilep);
  tree minpos = NULL_TREE, maxpos = NULL_TREE;

  gcc_checking_assert (base);

  base = build_fold_addr_expr (unshare_expr (base));

  if (maybe_ne (bitpos, 0))
    minpos = size_int (bits_to_bytes_round_down (bitpos));

  if (offset)
    {
      if (minpos)
	{
	  offset = size_binop (PLUS_EXPR, offset, minpos);
	  minpos = NULL_TREE;
	}

      base = fold_build_pointer_plus (base, offset);
    }
  else
    bitsize += bitpos;

  if (maybe_ne (bitsize, BITS_PER_UNIT))
    maxpos = size_int (bits_to_bytes_round_up (bitsize) - 1);

  base = force_gimple_operand_gsi (gsi, base, true, NULL, true,
				   GSI_SAME_STMT);

  addr_min = minpos ? fold_build_pointer_plus (base, minpos) : base;
  addr_max = maxpos ? fold_build_pointer_plus (base, maxpos) : base;
}

/* Generate runtime alias check on address range overlapping for the load
   DL and its aliased STORE statement.  If true alias is detected, mgo
   transformation status flag will be set to false to switch the following
   execution to non-optimized code.  */

void
loop_iter_info::gen_intersect_range_check (dep_load *dl, gimple *store) const
{
  tree st_memref = gimple_assign_lhs (store);
  tree st_addr_min, st_addr_max;
  gimple_stmt_iterator gsi = gsi_for_stmt (store);

  gen_memref_address_range (st_memref, st_addr_min, st_addr_max, &gsi);

  /* load_addr_min > store_addr_max.  */
  tree cond_min = fold_build2 (GT_EXPR, boolean_type_node,
			       fold_convert (ptr_type_node, dl->addr_min),
			       fold_convert (ptr_type_node, st_addr_max));

  /* load_addr_max < store_addr_min.  */
  tree cond_max = fold_build2 (LT_EXPR, boolean_type_node,
			       fold_convert (ptr_type_node, dl->addr_max),
			       fold_convert (ptr_type_node, st_addr_min));

  tree cond
    = fold_build2 (TRUTH_OR_EXPR, boolean_type_node, cond_min, cond_max);

  /* new_trans_ok = (cond_min || cond_max) ? trans_ok : false.  */
  tree new_trans_ok = build_cond_expr (cond, trans_ok, boolean_false_node);
  new_trans_ok = force_gimple_operand_gsi (&gsi, new_trans_ok, true, NULL,
					   false, GSI_CONTINUE_LINKING);

  /* Let update_ssa () to construct phi web for mgo transformation status.  */
  create_new_def_for (trans_ok, SSA_NAME_DEF_STMT (new_trans_ok), NULL);
}

/* Generate runtime alias checking code for the load DL.  The code will
   include address range computation for DL, and address overlapping check
   with all its aliased stores.  */

bool
loop_iter_info::gen_runtime_alias_check (dep_load *dl) const
{
  unsigned outer_loop_index = loop_relative_depth (mgo_outer_loop, mgo_loop);
  bool has_alias = false;

  for (unsigned i = 0; i <= outer_loop_index; i++)
    {
      dep_load_info *dl_info = dl->analysis_for_loops[i];

      gcc_checking_assert (!dl_info->excluded);

      if (!dl_info->mod_stmts.is_empty ())
	{
	  has_alias = true;
	  break;
	}
    }

  if (!has_alias)
    return true;

  /* Create SSA names to record address lower/upper bounds for DL.

     TODO: Address range of DL could be associated with some existing SSA
     names, for example DL always happens in a continuous memory region.  In
     this situation, we could bypass the address range computation.  */
  dl->addr_min
    = make_ssa_name_before_loop (mgo_outer_loop, vrp_val_max (ptr_type_node),
				 "_addr_min");
  dl->addr_max
    = make_ssa_name_before_loop (mgo_outer_loop, vrp_val_min (ptr_type_node),
				 "_addr_max");

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> Create address bounds:  ");
      print_generic_expr (dump_file, dl->addr_min, TDF_SLIM);
      fprintf (dump_file, " and ");
      print_generic_expr (dump_file, dl->addr_max, TDF_SLIM);
      fprintf (dump_file, " for ");
      print_gimple_expr (dump_file, dl->def_stmts[0], 0, TDF_SLIM);
      fprintf (dump_file, "\n");
    }

  for (unsigned i = 0; i <= outer_loop_index; i++)
    {
      dep_load_info *dl_info = dl->analysis_for_loops[i];
      unsigned j;
      gimple *store;

      /* TODO:
	o.  Combine and merge some range checks.
	o.  Hoist range checks outside of loop if both load and store's
	    address ranges can be identified as loop invariant SSA names.  */
      FOR_EACH_VEC_ELT (dl_info->mod_stmts, j, store)
	gen_intersect_range_check (dl, store);
    }

  return true;
}

/* Generate address range incremental computation code for load represented
   by DL.  MEMREF means the load expression.  */

static void
gen_address_range_updating (dep_load *dl, tree memref,
			    gimple_stmt_iterator *gsi)
{
  tree addr_min;
  tree addr_max;

  gen_memref_address_range (memref, addr_min, addr_max, gsi);

  /* load_addr_min = MIN (addr_min, load_addr_min)  */
  addr_min = fold_convert (ptr_type_node, addr_min);
  addr_min = size_binop (MIN_EXPR, addr_min, dl->addr_min);
  addr_min = force_gimple_operand_gsi (gsi, addr_min, true, NULL, false,
				       GSI_CONTINUE_LINKING);

  /* load_addr_max = MAX (addr_max, load_addr_max)  */
  addr_max = fold_convert (ptr_type_node, addr_max);
  addr_max = size_binop (MAX_EXPR, addr_max, dl->addr_max);
  addr_max = force_gimple_operand_gsi (gsi, addr_max, true, NULL, false,
				       GSI_CONTINUE_LINKING);

  create_new_def_for (dl->addr_min, SSA_NAME_DEF_STMT (addr_min), NULL);
  create_new_def_for (dl->addr_max, SSA_NAME_DEF_STMT (addr_max), NULL);
}

/* ----------------------------------------------------------------------- *
 *                           GENERATE CACHE TYPE                           *
 * ----------------------------------------------------------------------- */

/* Generate field decl in cache element type for each load in dependent load
   tree DL_ROOT, which needs to be cached, and records these new fields into
   FIELDS.  */

static void
gen_cache_field_decl (dep_load *dl_root, auto_vec<tree> &fields)
{
  unsigned unique_id = 0;
  dep_load_walker dl_walker;
  dep_load *dl;

  WALK_DEP_LOAD_PRE_ORDER (dl_walker, dl_root, dl)
    {
      if (!dl->need_caching)
	continue;

      tree cache_expr = gimple_assign_rhs1 (dl->def_stmts[0]);
      tree cache_type = TREE_TYPE (cache_expr);
      const char *name = "";

      /* For field reference, add its name into new cache field.  */
      if (TREE_CODE (cache_expr) == COMPONENT_REF)
	{
	  tree field = TREE_OPERAND (cache_expr, 1);
	  name = IDENTIFIER_POINTER (DECL_NAME (field));
	}

      char *buf = XALLOCAVEC (char, strlen (name) + 36);

      if (*name)
	sprintf (buf, "_L%d_%s_cf_%u", dl->level, name, unique_id++);
      else
	sprintf (buf, "_L%d_cf_%u", dl->level, unique_id++);

      tree new_field = build_decl (UNKNOWN_LOCATION, FIELD_DECL,
				   get_identifier (buf), cache_type);

      if (tree_to_uhwi (TYPE_SIZE (cache_type)) > TYPE_PRECISION (cache_type)
	  && INTEGRAL_TYPE_P (cache_type))
	{
	  DECL_SIZE (new_field) = bitsize_int (TYPE_PRECISION (cache_type));
	  DECL_BIT_FIELD (new_field) = 1;
	  DECL_NONADDRESSABLE_P (new_field) = 1;
	}
      else
	SET_DECL_ALIGN (new_field, TYPE_ALIGN (cache_type));

      fields.safe_push (new_field);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "> Create field:  ");
	  print_generic_expr (dump_file, new_field, TDF_SLIM);
	  fprintf (dump_file, " for ");
	  print_gimple_expr (dump_file, dl->def_stmts[0], 0, TDF_SLIM);
	  fprintf (dump_file, "\n");
	}
    }
}

static inline int
decl_align_cmp (const void *p, const void *q)
{
  tree a = *(const tree *) p;
  tree b = *(const tree *) q;

  /* Group bit-fields at first.  */
  if (DECL_BIT_FIELD (a) ^ DECL_BIT_FIELD (b))
    return DECL_BIT_FIELD (a) ? -1 : 1;

  return DECL_ALIGN (a) - DECL_ALIGN (b);
}

/* Insert FIELDS into STRUCT_TYPE after INIT_FIELD, sorted by alignment
   requirements to save memory space required by final cache data.  */

static void
insert_fields_into_struct (tree struct_type, const auto_vec<tree> &fields,
			   tree init_field)
{
  vec<tree> sorted_fields = fields.copy ();
  sorted_fields.qsort (decl_align_cmp);

  tree last_f = init_field;
  unsigned i;
  tree field;

  FOR_EACH_VEC_ELT (sorted_fields, i, field)
    {
      DECL_CONTEXT (field) = struct_type;
      DECL_CHAIN (last_f) = field;
      last_f = field;
    }

  sorted_fields.release ();
}

/* Build a flat struct for dependent loads that need to be cached.  Return
   true if cache element size does not exceed a threshold. */

bool
loop_iter_info::gen_cache_type_info ()
{
  tree cache_struct = ct_info.struct_type = make_node (RECORD_TYPE);
  tree dyn_list_struct = NULL_TREE;

  /* Generate a flag to record whether current element is initialized.  */
  tree init_field = build_decl (UNKNOWN_LOCATION, FIELD_DECL,
				get_identifier ("_init"), boolean_type_node);
  DECL_CONTEXT (init_field) = cache_struct;

  if (mgo_init_using_bit_field)
    {
      DECL_SIZE (init_field) = bitsize_one_node;
      DECL_BIT_FIELD (init_field) = 1;
      DECL_NONADDRESSABLE_P (init_field) = 1;
    }

  ct_info.init_field = init_field;

  if (dyn_list)
    {
      dyn_list_struct = TREE_TYPE (TREE_TYPE (iter_init));

      /* Make the origin struct/class type as the 1st field, after which cache
	 fields will be appended so that cache memory space is not overlapped
	 with origin memory space.  Origin/cache fields will be accessed via
	 pointers of the origin/extended struct type respectively.  */
      tree field_orig = build_decl (UNKNOWN_LOCATION, FIELD_DECL,
				    get_identifier ("_origin"),
				    dyn_list_struct);
      TYPE_FIELDS (cache_struct) = field_orig;
      DECL_CHAIN (field_orig) = init_field;
    }
  else
    TYPE_FIELDS (cache_struct) = init_field;

  /* Generate and add all cache field decls.  */
  gen_cache_field_decl (dep_load_root, ct_info.fields);
  if (ct_info.fields.is_empty ())
    return false;

  insert_fields_into_struct (cache_struct, ct_info.fields, init_field);

  location_t loc = DECL_SOURCE_LOCATION (current_function_decl);
  char *tmp_name = append_mgo_suffix ("_cache_st");
  tree name = get_identifier (tmp_name);
  free (tmp_name);
  tree decl = build_decl (loc, TYPE_DECL, name, cache_struct);

  DECL_IGNORED_P (decl) = 1;
  DECL_ARTIFICIAL (decl) = 1;
  TYPE_NAME (cache_struct) = decl;
  TYPE_STUB_DECL (cache_struct) = decl;
  TYPE_ARTIFICIAL (cache_struct) = 1;
  layout_type (cache_struct);

  /* Calculate the cache element size.  */
  tree cache_size = TYPE_SIZE_UNIT (cache_struct);

  if (dyn_list)
    cache_size = size_binop (MINUS_EXPR, cache_size,
			     TYPE_SIZE_UNIT (dyn_list_struct));

  gcc_checking_assert (TREE_CODE (cache_size) == INTEGER_CST);
  if (wi::gtu_p (wi::to_wide (cache_size), param_mgo_max_cache_elem_size))
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "> Over-large cache element size: ");
	  print_generic_expr (dump_file, cache_size, TDF_SLIM);
	  fprintf (dump_file, "\n");
	}
      return false;
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> Cache element size is ");
      print_generic_expr (dump_file, cache_size, TDF_SLIM);
      fprintf (dump_file, " bytes\n\n");
    }

  if (!dyn_list)
    {
      wide_int max_value = wi::to_wide (TYPE_MAX_VALUE (sizetype));

      max_value = wi::udiv_trunc (max_value, wi::to_wide (cache_size));

      if (wi::fits_uhwi_p (max_value))
	{
	  unsigned HOST_WIDE_INT min_count = param_mgo_min_cache_array_length;
	  unsigned HOST_WIDE_INT max_count = max_value.to_uhwi ();

	  if (max_count < min_count)
	    return false;

	  if (max_count < (unsigned HOST_WIDE_INT) ct_info.max_count)
	    ct_info.max_count = max_count;
	}
    }

  return true;
}

/* ----------------------------------------------------------------------- *
 *                         GENERATE CACHING CODE                           *
 * ----------------------------------------------------------------------- */

/* Insert calloc to create a new cache array at preheader of mgo outer loop, and
   free it at the loop exits. */

tree
loop_iter_info::gen_cache_array () const
{
  gcc_checking_assert (cache_data_count);

  /* Calculate cache-array length from data count at runtime.  If result is
     outside of lower/upper bounds, it will be set to 0.  */
  tree min_count = size_int (param_mgo_min_cache_array_length);
  tree max_count = size_int (ct_info.max_count);
  tree count = fold_convert (sizetype, cache_data_count);
  tree length = make_ssa_name_before_loop (mgo_outer_loop, count);

  /* length = count >= min_count && count <= max_count ? count : 0  */
  tree range_check = build_range_check (UNKNOWN_LOCATION, sizetype, length, 1,
					min_count, max_count);
  length = build_cond_expr (range_check, length, size_zero_node);
  length = make_ssa_name_before_loop (mgo_outer_loop, length, "_cache_len");

  /* cache_array = calloc (length, size)  */
  tree cache_struct = ct_info.struct_type;
  tree call_expr = build_call_expr (builtin_decl_explicit (BUILT_IN_CALLOC), 2,
				    length, TYPE_SIZE_UNIT (cache_struct));
  call_expr = fold_convert (build_pointer_type (cache_struct), call_expr);
  tree cache_array
    = make_ssa_name_before_loop (mgo_outer_loop, call_expr, "_cache_array");

  /* If fail to create the cache array, transform ok flag is set to false.
     Also check if length is zero as calloc(0, n) is not guranteed to return
     NULL.
	trans_ok = (length && cache_array) ? trans_ok : false  */
  tree cmp_len = fold_build2 (NE_EXPR, boolean_type_node, length,
			      size_zero_node);
  tree cmp_arr = fold_build2 (NE_EXPR, boolean_type_node, cache_array,
			      null_pointer_node);
  tree cond = fold_build2 (TRUTH_AND_EXPR, boolean_type_node, cmp_len,
			   cmp_arr);
  tree cond_expr = build_cond_expr (cond, trans_ok, boolean_false_node);
  tree new_trans_ok
    = make_ssa_name_before_loop (mgo_outer_loop, cond_expr, "_transform_ok");

  create_new_def_for (trans_ok, SSA_NAME_DEF_STMT (new_trans_ok), NULL);

  auto_vec<edge> exits = get_loop_exit_edges (mgo_outer_loop);
  unsigned i;
  edge ex;

  FOR_EACH_VEC_ELT (exits, i, ex)
    {
      /* Make sure the cache array variable can always reach its free
	 statement.  If the exit dest has multiple predecessors, it might be
	 reached by other exits.  To avoid erroneous double-free, we insert a
	 new block at the exit edge.  */
      basic_block dest_bb = ex->dest;
      if (!single_pred_p (dest_bb))
	dest_bb = split_edge (ex);

      gimple_stmt_iterator gsi = gsi_after_labels (dest_bb);
      gimple *free_stmt
	= gimple_build_call (builtin_decl_explicit (BUILT_IN_FREE), 1,
			     cache_array);
      gsi_insert_before (&gsi, free_stmt, GSI_NEW_STMT);
    }

  return cache_array;
}

/* Enlarge size of all list element allocation statements to get extra space
   to accommodate data for caching.  */

void
loop_iter_info::gen_extended_dyn_list () const
{
  tree ct_size = TYPE_SIZE_UNIT (ct_info.struct_type);
  unsigned i;
  gimple *orig_call;

  FOR_EACH_VEC_ELT (dyn_list->elem_alloc_stmts, i, orig_call)
    {
      gimple_stmt_iterator gsi = gsi_for_stmt (orig_call);

      gcall *call = gimple_build_call (builtin_decl_explicit (BUILT_IN_CALLOC),
				       2, size_one_node, ct_size);
      gimple_call_set_lhs (call, gimple_get_lhs (orig_call));
      gsi_insert_after (&gsi, call, GSI_SAME_STMT);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "> Replaced original list element def:\n");
	  print_gimple_stmt_with_bb (dump_file, orig_call, 0, TDF_DETAILS);
	  fprintf (dump_file, "> with extended element def:\n");
	  print_gimple_stmt_with_bb (dump_file, call, 0, TDF_DETAILS);
	  fprintf (dump_file, "\n");
	}

      gsi_remove (&gsi, true);
    }
}

/* Generate base address to access caching data which should keep pace with
   iterator.  */

tree
loop_iter_info::gen_cache_data_pointer () const
{
  tree cache_struct = ct_info.struct_type;
  tree cache_ptr_type = build_pointer_type (cache_struct);
  tree cache_ptr_rhs;

  if (dyn_list)
    {
      tree iter_value = gimple_phi_result (iter_phi);

      gen_extended_dyn_list ();

      /* Convert iterator to pointer of extended list element type.  */
      cache_ptr_rhs = fold_convert (cache_ptr_type, iter_value);
    }
  else
    {
      tree cache_array = gen_cache_array ();

      cache_ptr_rhs = make_ssa_name_before_loop (mgo_loop, cache_array);

      /* Create cache array pointer updating statement in loop latch block.  */
      gimple *stmt = build_assign_after_bb (mgo_loop->latch, NULL_TREE,
					    cache_ptr_rhs, POINTER_PLUS_EXPR,
					    TYPE_SIZE_UNIT (cache_struct));
      create_new_def_for (cache_ptr_rhs, stmt, NULL);
    }

  gimple_stmt_iterator gsi = gsi_after_labels (mgo_loop->header);
  tree cache_ptr = make_temp_ssa_name (cache_ptr_type, NULL, "_cache_ptr");

  build_assign_at_gsi (&gsi, true, cache_ptr, cache_ptr_rhs);
  return cache_ptr;
}

/* Callback of walk_tree() to replace ssa operand (pointed by OPND_PTR) with
   new ssa, the pair relation is denoted by DATA.  */

static tree
replace_ssa_operands (tree *opnd_ptr, int *walk_subtrees, void *data)
{
  tree opnd = *opnd_ptr;
  hash_map<tree, tree> &ssa_reps = *(hash_map<tree, tree> *) data;

  if (TREE_CODE (opnd) == SSA_NAME)
    {
      tree *new_opnd_ptr = ssa_reps.get (opnd);

      if (new_opnd_ptr)
	{
	  /* Refer to a loop variant SSA that must be defined by a previous
	     address computation statement.  */
	  gcc_checking_assert (*new_opnd_ptr);
	  *opnd_ptr = *new_opnd_ptr;
	}
      *walk_subtrees = 0;
    }

  return NULL_TREE;
}

/* Duplicate STMT which is included in a dependent load tree, either as a
   node, or used to compute address for a node.  The new statement will be
   inserted after GSI,  and original and new result SSAs are paired into
   SSA_REPS, so that operands of following duplicated statements would
   refer to those new SSAs.  */

static gimple *
copy_dep_stmt (gimple *stmt, gimple_stmt_iterator *gsi,
	       hash_map<tree, tree> &ssa_reps)
{
  tree value = gimple_get_lhs (stmt);
  bool existed;
  tree &new_val = ssa_reps.get_or_insert (value, &existed);

  if (existed)
    return SSA_NAME_DEF_STMT (new_val);

  gimple *new_stmt = gimple_copy (stmt);
  tree *opnd_ptr = gimple_op_ptr (new_stmt, 0);
  tree value_var = SSA_NAME_VAR (value);

  if (!value_var)
    value_var = TREE_TYPE (value);

  /* Since def-use chain is not ready for new statement, we have to set SSA
     operands using walk_tree.  At first, replace result SSA of new stmt.  */
  *opnd_ptr = new_val = make_ssa_name (value_var, new_stmt);

  for (unsigned i = 1; i < gimple_num_ops (new_stmt); ++i)
    walk_tree (gimple_op_ptr (new_stmt, i), replace_ssa_operands,
	       &ssa_reps, NULL);

  gsi_insert_after (gsi, new_stmt, GSI_NEW_STMT);
  return new_stmt;
}

/* Generate memory loads as original sequence for dependent load tree DL_ROOT.
   When GEN_ADDR_RANGE is true, address updating code is also added for load
   that has store alias.  Those new loads will be inserted at end of BB, and
   result values are recorded into LOAD_VALS.  */

static void
gen_orig_load_sequence (basic_block bb, dep_load *dl_root,
			auto_vec<tree> &load_vals, bool gen_addr_range)
{
  gimple_stmt_iterator gsi = gsi_last_bb (bb);
  hash_map<tree, tree> ssa_reps;
  dep_load_walker dl_walker;
  dep_load *dl;

  WALK_DEP_LOAD_PRE_ORDER (dl_walker, dl_root, dl)
    {
      unsigned i;
      gimple *stmt;

      if (dl->is_root ())
	{
	  /* We do not regenerate root node, so result values of statements in
	     the node are the original, and will not be redefined.  */
	  FOR_EACH_VEC_ELT (dl->def_stmts, i, stmt)
	    {
	      tree root_val = gimple_get_lhs (stmt);

	      ssa_reps.put (root_val, root_val);
	    }
	  continue;
	}

      /* Address computation statements have been sorted in original order.  */
      FOR_EACH_VEC_ELT (dl->addr_stmts, i, stmt)
	copy_dep_stmt (stmt, &gsi, ssa_reps);

      gimple *new_stmt = copy_dep_stmt (dl->def_stmts[0], &gsi, ssa_reps);
      tree new_lhs = gimple_assign_lhs (new_stmt);
      tree new_rhs = gimple_assign_rhs1 (new_stmt);

      FOR_EACH_VEC_ELT_FROM (dl->def_stmts, i, stmt, 1)
	{
	  tree old_lhs = gimple_assign_lhs (stmt);

	  /* All loads in same node would define same new result.  */
	  ssa_reps.put (old_lhs, new_lhs);
	}

      if (gen_addr_range && dl->addr_min)
	gen_address_range_updating (dl, new_rhs, &gsi);

      if (dl->need_caching)
	load_vals.safe_push (new_lhs);
    }
}

/* Use values in LOAD_VALS to initialize corresponding fields in a cache
   element pointer CACHE_PTR whose type is described by CT_INFO.  Generated
   statements will be inserted at end of BB. */

static void
gen_cache_init (basic_block bb, const cache_type_info &ct_info, tree cache_ptr,
		auto_vec<tree> &load_vals)
{
  /* Set the init flag to be true.  */
  tree init_ref = build_field_ref (cache_ptr, ct_info.init_field);
  build_assign_after_bb (bb, init_ref, boolean_true_node);

  unsigned i;
  tree field_decl;

  /* Store field values to the current cache element.  As both fields and
     loaded values are added in pre-order of dependent load tree, value and
     field are matched one-by-one.  */
  FOR_EACH_VEC_ELT (ct_info.fields, i, field_decl)
    {
      tree ref = build_field_ref (cache_ptr, field_decl);
      build_assign_after_bb (bb, ref, load_vals[i]);
    }
}

/* Generate load fields from the current cache element pointer CACHE_PTR,
   whose type is described by CT_INFO.  These new load statements will be
   inserted at end of BB, and result values are recorded into LOAD_VALS.  */

static void
gen_load_from_cache (basic_block bb, const cache_type_info &ct_info,
		     tree cache_ptr, auto_vec<tree> &load_vals)
{
  unsigned i;
  tree field_decl;

  FOR_EACH_VEC_ELT (ct_info.fields, i, field_decl)
    {
      tree lhs = make_ssa_name (TREE_TYPE (field_decl));
      build_assign_after_bb (bb, lhs, build_field_ref (cache_ptr, field_decl));
      load_vals.safe_push (lhs);
    }
}

/* Create edges to link basic blocks created for mgo, and properly setup block
   relationship, including loop parent and dominate information.  */

static void
connect_mgo_bbs (basic_block bb_header, basic_block bb_merge,
		 basic_block bb_trans_no, basic_block bb_check_init,
		 basic_block bb_init_no, basic_block bb_init_yes)
{
  /* Link basic blocks that make up of condition to check whether transform
     is ok.  */
  edge trans_false_e = EDGE_PRED (bb_trans_no, 0);
  trans_false_e->flags
    = ((trans_false_e->flags & ~EDGE_FALLTHRU) | EDGE_FALSE_VALUE);
  trans_false_e->probability = profile_probability::unlikely ();

  edge trans_true_e = make_edge (bb_header, bb_check_init, EDGE_TRUE_VALUE);
  trans_true_e->probability = trans_false_e->probability.invert ();

  /* Link basic blocks that make up of condition to check that cache element
     is initialized.  */
  edge cache_false_e = make_edge (bb_check_init, bb_init_no, EDGE_FALSE_VALUE);
  cache_false_e->probability = profile_probability::unlikely ();
  make_single_succ_edge (bb_init_no, bb_merge, EDGE_FALLTHRU);

  edge cache_true_e = make_edge (bb_check_init, bb_init_yes, EDGE_TRUE_VALUE);
  cache_true_e->probability = cache_false_e->probability.invert ();
  make_single_succ_edge (bb_init_yes, bb_merge, EDGE_FALLTHRU);

  class loop *loop = bb_header->loop_father;
  add_bb_to_loop (bb_check_init, loop);
  add_bb_to_loop (bb_init_no, loop);
  add_bb_to_loop (bb_init_yes, loop);

  set_immediate_dominator (CDI_DOMINATORS, bb_trans_no, bb_header);
  set_immediate_dominator (CDI_DOMINATORS, bb_check_init, bb_header);
  set_immediate_dominator (CDI_DOMINATORS, bb_init_no, bb_check_init);
  set_immediate_dominator (CDI_DOMINATORS, bb_init_yes, bb_check_init);
  set_immediate_dominator (CDI_DOMINATORS, bb_merge, bb_header);
}

/* Generate PHIs in BB_MERGE to merge values LOAD_VALS from 3 predecessors in
   MERGE_E.  Results of generated PHIs are added into NEW_VALS.  */

static void
gen_phis_for_load_value (basic_block bb_merge, edge merge_e[3],
			 const cache_type_info &ct_info,
			 auto_vec<tree> load_vals[3],
			 auto_vec<tree> &new_vals)
{
  unsigned i;
  tree field_decl;

  FOR_EACH_VEC_ELT (ct_info.fields, i, field_decl)
    {
      tree lhs
	= make_temp_ssa_name (TREE_TYPE (field_decl), NULL,
			      IDENTIFIER_POINTER (DECL_NAME (field_decl)));
      gphi *phi = create_phi_node (lhs, bb_merge);
      add_phi_arg (phi, load_vals[0][i], merge_e[0], UNKNOWN_LOCATION);
      add_phi_arg (phi, load_vals[1][i], merge_e[1], UNKNOWN_LOCATION);
      add_phi_arg (phi, load_vals[2][i], merge_e[2], UNKNOWN_LOCATION);

      new_vals.safe_push (lhs);
    }
}

/* Replace old uses for loads in dependent load tree DL_ROOT with values in
   NEW_VALS.  */

static void
update_dep_loads (dep_load *dl_root, auto_vec<tree> &new_vals)
{
  unsigned order = 0;
  dep_load_walker dl_walker;
  dep_load *dl;

  WALK_DEP_LOAD_PRE_ORDER (dl_walker, dl_root, dl)
    {
      if (!dl->need_caching)
	continue;

      tree new_val = new_vals[order++];

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, ">> Use new value: ");
	  print_generic_expr (dump_file, new_val, TDF_SLIM);
	  fprintf (dump_file, " to replace origin dep load:\n");
	}

      unsigned i;
      gimple *old_stmt;
      gimple *use_stmt;
      imm_use_iterator iterator;
      use_operand_p imm_use_p;

      FOR_EACH_VEC_ELT (dl->def_stmts, i, old_stmt)
	{
	  tree lhs = gimple_assign_lhs (old_stmt);

	  /* Old load statements are not needed anymore.  To be simple, just
	     let following dce pass to remove them and related unused address
	     computation statements.  */
	  FOR_EACH_IMM_USE_STMT (use_stmt, iterator, lhs)
	    FOR_EACH_IMM_USE_ON_STMT (imm_use_p, iterator)
	      SET_USE (imm_use_p, new_val);

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    print_gimple_stmt_with_bb (dump_file, old_stmt);
	}
    }
}

/* Given a loop iterator for mgo, generate code to cache data illustrated as
   the following graph.

		    loop header
			 |
	    cache_ptr = cache_data_pointer
			 |
		  if (transform)
			 |
	     trans_no   / \    trans_yes
	  .------------*   *-----------------.
	  |	                             |
	  |		 	   if (cache_ptr->init)
	  |                                  |
	  |		 	   init_no  / \  init_yes
	  |                    .-----------*   *-----------.
	  |		       |	                   |
    v0 = *orig_data     v1 = *orig_data           v2 = cache_ptr->data
	  |                    |                           |
	  |             cache_ptr->data = v1               |
	  |             cache_ptr->init = true             |
	  |                    |                           |
	  '------------------->|<--------------------------'
			       |
			       V
		     v3 = PHI (v0, v1, v2)
*/

void
loop_iter_info::gen_caching_code () const
{
  tree cache_ptr = gen_cache_data_pointer ();
  gimple *def_stmt = SSA_NAME_DEF_STMT (cache_ptr);
  gcc_checking_assert (gimple_bb (def_stmt) == mgo_loop->header);

  edge fallthru = split_block (gimple_bb (def_stmt), def_stmt);
  basic_block bb_header = fallthru->src;
  basic_block bb_merge = fallthru->dest;
  basic_block bb_trans_no = split_edge (fallthru);

  basic_block bb_check_init = create_empty_bb (bb_header);
  basic_block bb_init_no = create_empty_bb (bb_check_init);
  basic_block bb_init_yes = create_empty_bb (bb_check_init);

  /* Values loaded either from cache or original list.  */
  auto_vec<tree> load_vals[3];

  /* (1) Build basic blocks.  */

  /* Check if transform is ok in header.  */
  build_cond_after_bb (bb_header, trans_ok, EQ_EXPR, boolean_true_node);

  /* Check if element is already in cache.  */
  tree init = make_ssa_name (TREE_TYPE (ct_info.init_field));
  tree init_ref = build_field_ref (cache_ptr, ct_info.init_field);
  build_assign_after_bb (bb_check_init, init, init_ref);
  build_cond_after_bb (bb_check_init, init, EQ_EXPR, boolean_true_node);

  /* Load values from the current cache pointer.  */
  gen_load_from_cache (bb_init_yes, ct_info, cache_ptr, load_vals[0]);

  /* Load values as original sequence and init the current cache element.  */
  gen_orig_load_sequence (bb_init_no, dep_load_root, load_vals[1], true);
  gen_cache_init (bb_init_no, ct_info, cache_ptr, load_vals[1]);

  /* Just load values as original load sequence.  */
  gen_orig_load_sequence (bb_trans_no, dep_load_root, load_vals[2], false);

  /* (2) Build edges and PHIs.  */

  /* Connect basic blocks with edges.  */
  connect_mgo_bbs (bb_header, bb_merge, bb_trans_no, bb_check_init, bb_init_no,
		   bb_init_yes);

  /* Generate PHIs to merge load values in bb_merge.  */
  edge merge_e[] = { EDGE_SUCC (bb_init_yes, 0), EDGE_SUCC (bb_init_no, 0),
		     EDGE_SUCC (bb_trans_no, 0) };
  auto_vec<tree> new_vals;
  gen_phis_for_load_value (bb_merge, merge_e, ct_info, load_vals, new_vals);

  /* (3) Update old dependent loads with new values.  */

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "> Updating old dependent loads with new values:\n");

  update_dep_loads (dep_load_root, new_vals);
}

/* Main entry to generate data caching code.  */

void
loop_iter_info::insert_mgo_code ()
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> Apply mgo to dependent load in loop %d "
	       "(outer %d)\n", mgo_loop->num, mgo_outer_loop->num);
      dump_dep_load (dump_file, dep_load_root);
    }

  /* TODO: Cache struct size is a factor of cost model. If it exceeds
     specified threshold, the iterator should be bypassed in advance,
     instead of doing this check here.  */
  if (!gen_cache_type_info ())
    return;

  /* Generate _transform_ok, which is initialized to true.  */
  trans_ok = make_ssa_name_before_loop (mgo_outer_loop, boolean_true_node,
					"_transform_ok");

  if (allow_runtime_alias_check_p ())
    {
      dep_load_walker dl_walker;
      dep_load *dl;

      WALK_DEP_LOAD_PRE_ORDER (dl_walker, dep_load_root, dl)
	gen_runtime_alias_check (dl);
    }

  gen_caching_code ();
}

/* ----------------------------------------------------------------------- *
 *                          END OF GENERATING CODE                         *
 * ----------------------------------------------------------------------- */

/* Given PHI at header of LOOP, scan the def/use chain in LOOP backwards to
   see whether it could be a mgo iterator,  and if identified, a
   LOOP_ITER_INFO struct describing the iterator would be returned.  */

static loop_iter_info *
identify_iterator (const class loop *loop, gphi *phi)
{
  edge latch = loop_latch_edge (loop);
  tree latch_val = PHI_ARG_DEF_FROM_EDGE (phi, latch);

  /* Value space of boolean type contains only two values, too small to get
     benefit from mgo.  */
  if (TREE_CODE (latch_val) != SSA_NAME
      || TREE_CODE (TREE_TYPE (latch_val)) == BOOLEAN_TYPE)
    return NULL;

  class loop *outer_loop = loop_outer (loop);
  auto_vec<tree> worklist;
  auto_vec<tree> invar_opnds;
  auto_vec<gimple *> iter_next_stmts;
  auto_bitmap visited;

  /* Add value from latch edge to worklist.  */
  bitmap_set_bit (visited, SSA_NAME_VERSION (latch_val));
  worklist.safe_push (latch_val);

  /* Search all def stmts backwards to check if it is an iterator.  */
  do
    {
      tree name = worklist.pop ();

      if (expr_invariant_in_loop_p (outer_loop, name))
	{
	  invar_opnds.safe_push (name);
	  continue;
	}

      gimple *stmt = SSA_NAME_DEF_STMT (name);

      if (!stmt_inside_loop_p (loop, stmt) || gimple_has_side_effects (stmt))
	return NULL;

      /* Now we require that the iterator is advanced once in each iteration
	 of the loop, so do not allow PHI statement.  TODO: Support irregular
	 loop form which contains multiple iterator advancing statements.  */
      if (gimple_code (stmt) != GIMPLE_PHI)
	{
	  tree opnd;
	  ssa_op_iter iter;

	  FOR_EACH_SSA_TREE_OPERAND (opnd, stmt, iter, SSA_OP_USE)
	    if (bitmap_set_bit (visited, SSA_NAME_VERSION (opnd)))
	      worklist.safe_push (opnd);

	  /* Record non-copy statements, as a whole, which would compose
	     iterator advancing operation.  */
	  if (!assign_ssa_copy_p (stmt))
	    iter_next_stmts.safe_push (stmt);
	}
      else if (stmt != phi)
	return NULL;

    } while (!worklist.is_empty ());

  /* Not a real iterator, since its next state is not derived from current
     state, or its state is never changed.  */
  if (!bitmap_bit_p (visited, SSA_NAME_VERSION (gimple_phi_result (phi)))
      || iter_next_stmts.is_empty ())
    return NULL;

  loop_iter_info *iter_info = new loop_iter_info (phi, iter_next_stmts,
						  invar_opnds);

  if (!iter_info->post_check ())
    {
      delete iter_info;
      return NULL;
    }

  return iter_info;
}

/* Identify all iterators qualified for mgo in LOOP, return true if something
   was found.  */

static bool
find_iterators (const class loop *loop)
{
  loop_mgo_info *mgo_info = get_mgo_info (loop);

  /* Scan all phis in loop header as there might be multiple iterators in
     a single loop.  */
  for (gphi_iterator gsi = gsi_start_nonvirtual_phis (loop->header);
       !gsi_end_p (gsi); gsi_next_nonvirtual_phi (&gsi))
    {
      loop_iter_info *iter_info = identify_iterator (loop, gsi.phi ());

      if (!iter_info)
	continue;

      mgo_info->iters.safe_push (iter_info);
    }

  return !mgo_info->iters.is_empty ();
}

static inline int
stmt_uid_cmp (const void *p0, const void *p1)
{
  unsigned uid0 = gimple_uid (*(const gimple *const *) p0);
  unsigned uid1 = gimple_uid (*(const gimple *const *) p1);

  gcc_checking_assert (uid0 && uid1);

  return (int) (uid0 - uid1);
}

/* Build value dependency for STMT in LOOP, and try to add it to a dependent
   load tree.  If operands of STMT are derived from result of certain
   dependent load, or from values that are invariant in immediate outer loop,
   it will be assigned a uid number, and its corresponding entry in DEP_ARRAY
   will be set to that dependent load, or empty if merely outer loop
   invariant.  */

static void
add_to_dep_load_tree (const class loop *loop, gimple *stmt,
		      auto_vec<dep_load *> &dep_array)
{
  tree lhs = gimple_get_lhs (stmt);
  bool is_load = false;

  /* Two kinds of statements are included in dependent load tree, one is load
     statement we are interested in, which acts as tree node, the other occurs
     in child load's address compution from result of parent load, which acts
     as a bridge between them, and will be collected into "addr_stmts" of the
     belonging child node.

		v1 = load[.]      <---  parent load

		v2 = v1 op const  <--.
				     |  child load's address computation
		v3 = base op v2   <--'

		v4 = load[v3]     <---  child load

     Currently, only statement that depends on sole one tree node is handled,
     although multiple parents are possible, which is a TODO.  And these
     statements will be assigned a non-zero uid.  For a load, it will also be
     marked as GF_DEP_LOAD, since it is definitely a tree node.  While for
     other statement, it will not be part of dependent load tree if its result
     is not used by any load.  So in order to fast check whether a statement
     with non-zero uid is really covered by a dependent load tree, GF_INCLUDED
     flag is used.

     Since these uid/flags will be cleared when analyzing other loop, we
     SHOULD NOT rely on them to do something in transformation phase.  */

  gimple_set_uid (stmt, 0);
  gimple_set_plf (stmt, GF_DEP_LOAD, false);
  gimple_set_plf (stmt, GF_INCLUDED, false);

  gcc_checking_assert (gimple_code (stmt) != GIMPLE_PHI);

  if (!lhs || TREE_CODE (lhs) != SSA_NAME || gimple_has_side_effects (stmt))
    return;

  tree type = TREE_TYPE (lhs);

  gcc_checking_assert (COMPLETE_TYPE_P (type));

  /* Now we only care about non-aggregate type with fixed size.  */
  if (TREE_CODE (TYPE_SIZE (type)) != INTEGER_CST || AGGREGATE_TYPE_P (type))
    return;

  if (gimple_assign_load_p (stmt))
    is_load = true;
  else if (gimple_vuse (stmt))
    return;

  class loop *outer_loop = loop_outer (loop);
  tree opnd;
  ssa_op_iter iter;
  dep_load *parent = NULL;

  FOR_EACH_SSA_TREE_OPERAND (opnd, stmt, iter, SSA_OP_USE)
    {
      gimple *opnd_stmt = SSA_NAME_DEF_STMT (opnd);

      if (!stmt_inside_loop_p (loop, opnd_stmt))
	{
	  if (!expr_invariant_in_loop_p (outer_loop, opnd))
	    return;

	  /* Clear uid of outer loop invariant statement to let us quickly
	     distinguish it from in-loop operands in processing below.  */
	  gimple_set_uid (opnd_stmt, 0);
	  continue;
	}

      if (!gimple_uid (opnd_stmt))
	return;

      dep_load *new_parent = dep_array[gimple_uid (opnd_stmt) - 1];

      if (!parent)
	parent = new_parent;
      else if (parent != new_parent && new_parent)
	/* TODO: A statement may depend on multiple parent nodes.  */
	return;
    }

  if (!is_load)
    {
      /* When statement defines an outer loop invariant value, its depends
	 on nothing (e.g. parent is empty), otherwise set parent found.  */
      dep_array.safe_push (parent);
      gimple_set_uid (stmt, dep_array.length ());
      return;
    }

  if (!parent)
    {
      /* The value is from a memory load whose address is outer loop
	 invariant, and could also contribute to address computation for
	 dependent load, but its value may be variant, so is ignored now.
	 TODO: resort to static alias analysis or dynamic check to ensure its
	 invariantness so as to use it as address computation statement for
	 dependent load.  */
      return;
    }

  int level = parent->level + 1;

  if (level > param_mgo_dep_load_level)
    return;

  dep_load *dl = new dep_load (stmt, level);
  auto_vec<gimple *> worklist;
  auto_bitmap visited;

  worklist.safe_push (stmt);

  /* Load address may not directly use value of prior load, it could be
     a result of a series of operations on the value, which is common in
     address computation for array access (e.g. array[(*mem + 8) % 25]).

     Here traverse backwards from the load until reaching its dependent
     parent, collect all statements that contribute to the load address
     computation.  */
  do
    {
      gimple *dep_stmt = worklist.pop ();

      FOR_EACH_SSA_TREE_OPERAND (opnd, dep_stmt, iter, SSA_OP_USE)
	{
	  gimple *opnd_stmt = SSA_NAME_DEF_STMT (opnd);

	  /* Operand is outer loop invariant.  */
	  if (!gimple_uid (opnd_stmt))
	    {
	      if (!dl->invar_opnds.contains (opnd))
		dl->invar_opnds.safe_push (opnd);
	      continue;
	    }

	  /* Reach dependent parent, stop walking.  */
	  if (gimple_plf (opnd_stmt, GF_DEP_LOAD))
	    continue;

	  if (bitmap_set_bit (visited, gimple_uid (opnd_stmt)))
	    {
	      dl->addr_stmts.safe_push (opnd_stmt);
	      worklist.safe_push (opnd_stmt);
	    }
	}
    } while (!worklist.is_empty ());

  /* Keep those address computation statements as original order.  */
  dl->addr_stmts.qsort (stmt_uid_cmp);

  dep_array.safe_push (dl);
  gimple_set_uid (stmt, dep_array.length ());
  gimple_set_plf (stmt, GF_DEP_LOAD, true);

  parent->children.safe_push (dl);
}

/* Build dependent load tree for all iterators found in LOOP.  As an example,
   there is a sequence of loads derived from an iterator, and suppose 'array'
   is a memory base address invariant in LOOP.

      ptr_a = iterator->a;
      idx_b = ptr_a->b;
      val_c = ptr_a->object.c;
      val_d = array[idx_b * 2 + 1].d;

   These loads will be identified as nodes in following dependent load tree:

      root (iterator)
	|
	'--> ptr_a = iterator->a
	       |
	       |--> idx_b = ptr_a->b
	       |      |
	       |      '--> val_d = array[idx_b * 2 + 1].d
	       |
	       '--> val_c = ptr_a->object.c

   We walk all basic blocks of LOOP in dominance order to incrementally record
   dependency relation for all loads into a linear vector, and at same time
   add each candidate load to corresponding tree by using information in the
   vector.  */

static void
find_dep_loads (const class loop *loop)
{
  basic_block *body = get_loop_body_in_dom_order (loop);
  loop_mgo_info *mgo_info = get_mgo_info (loop);
  loop_iter_info *iter_info;
  auto_vec<dep_load *> dep_array;

  for (unsigned i = 0; i < loop->num_nodes; i++)
    {
      basic_block bb = body[i];
      gimple_stmt_iterator gsi;

      for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	{
	  gimple_set_uid (gsi_stmt (gsi),  0);
	  gimple_set_plf (gsi_stmt (gsi), GF_DEP_LOAD, false);
	  gimple_set_plf (gsi_stmt (gsi), GF_INCLUDED, false);
	}

      if (!i)
	{
	  unsigned j;

	  /* Iterators should locate at loop header.  */
	  gcc_checking_assert (bb == loop->header);

	  /* Create root of dependent load tree for iterators, assign uid and
	     set flags for definition statements.  */
	  FOR_EACH_VEC_ELT (mgo_info->iters, j, iter_info)
	    {
	      gphi *iter_phi = iter_info->iter_phi;

	      iter_info->dep_load_root = new dep_load (iter_phi);
	      dep_array.safe_push (iter_info->dep_load_root);

	      gimple_set_uid (iter_phi, dep_array.length ());
	      gimple_set_plf (iter_phi, GF_DEP_LOAD, true);
	      gimple_set_plf (iter_phi, GF_INCLUDED, true);
	    }
	}

      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	add_to_dep_load_tree (loop, gsi_stmt (gsi), dep_array);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      unsigned i;

      FOR_EACH_VEC_ELT (mgo_info->iters, i, iter_info)
	{
	  if (iter_info->clean_trivial_dep_load ())
	    continue;

	  fprintf (dump_file, "> Found dependent loads in loop %d:\n",
		   loop->num);
	  dump_dep_load (dump_file, iter_info->dep_load_root);
	}
    }

  free (body);
}

static void
analyze_mgo_in_loop (class loop *loop)
{
  /* Find all the iterators that may be used in the loop.  */
  if (!find_iterators (loop))
    return;

  /* Build dependent load tree for iterators.  */
  find_dep_loads (loop);

  loop_mgo_info *mgo_info = get_mgo_info (loop);
  loop_iter_info *iter_info;
  unsigned i;

  FOR_EACH_VEC_ELT (mgo_info->iters, i, iter_info)
    if (!iter_info->process_dep_load ())
      {
	delete iter_info;
	mgo_info->iters.unordered_remove (i--);
      }

  if (mgo_info->iters.length () < 2)
    return;

  /* If two iterators advance at the same pace, their dependent load trees
     could be combined together. For example,

	for (list = list_head, i = 0; i < n; i++)
	  {
	    ... = array[i]->a;
	    ... = list->ptr->b;

	    list = list->next;
	  }

     Suppose "list_head" and "array" are invariant memory address in
     certain outer loop, then both two dependent loads "array[i]->a" and
     "list->ptr->b" could be cached by mgo, though they are derived from
     different iterators.  */
  FOR_EACH_VEC_ELT (mgo_info->iters, i, iter_info)
    {
      unsigned j;
      loop_iter_info *other_iter_info;

      FOR_EACH_VEC_ELT_FROM (mgo_info->iters, j, other_iter_info, i + 1)
	{
	  if (iter_info->merge (other_iter_info))
	    {
	      delete other_iter_info;
	      mgo_info->iters.unordered_remove (j--);
	    }
	}
    }
}

/* Find the most beneficial iterator candidate from MGO_INFO, otherwise
   return NULL.  */

static loop_iter_info *
find_best_iter_cand (const loop_mgo_info *mgo_info)
{
  int min_cost = INT_MAX;
  loop_iter_info *res = NULL;
  loop_iter_info *iter_info;
  unsigned i;

  /* Find the iterator with minimum dependent load cost.  */
  FOR_EACH_VEC_ELT (mgo_info->iters, i, iter_info)
    {
      dep_load *dl_root = iter_info->dep_load_root;
      unsigned outer_loop_index = loop_relative_depth (iter_info->mgo_outer_loop,
						       iter_info->mgo_loop);
      int cost = dl_root->get_total_cost (outer_loop_index);

      if (cost < min_cost)
	{
	  res = iter_info;
	  min_cost = cost;
	}
    }

  return res;
}

static bool
apply_mgo_in_loop (loop_mgo_info *mgo_info)
{
  loop_iter_info *iter_info = find_best_iter_cand (mgo_info);

  if (!iter_info)
    return false;

  iter_info->insert_mgo_code ();
  mgo_name_suffix_id++;

  return true;
}

static unsigned int
do_mgo (void)
{
  bool changed = false;

  gcc_assert (scev_initialized_p ());

  for (auto loop : loops_list (cfun, 0))
    loop->aux = new loop_mgo_info (loop);

  for (auto loop : loops_list (cfun, LI_FROM_INNERMOST))
    {
      /* If current loop is not an inner loop, the cached data will not
	 have a chance to be reloaded to bring benefit through L1 cache
	 line hardware prefetch.  */
      if (loop_depth (loop) < 2)
	continue;

      if (optimize_loop_for_size_p (loop))
	continue;

      analyze_mgo_in_loop (loop);
    }

  for (auto loop : loops_list (cfun, LI_FROM_INNERMOST))
    {
      loop_mgo_info *mgo_info = get_mgo_info (loop);
      changed |= apply_mgo_in_loop (mgo_info);
      delete mgo_info;
      loop->aux = NULL;
    }

  if (changed)
    {
      rewrite_into_loop_closed_ssa (NULL, TODO_update_ssa);
      return TODO_cleanup_cfg;
    }
  return 0;
}

namespace {

const pass_data pass_data_loop_mgo = {
  GIMPLE_PASS,	    /* type */
  "mgo",	    /* name */
  OPTGROUP_NONE,    /* optinfo_flags */
  TV_LOOP_MGO,	    /* tv_id */
  0,		    /* properties_required */
  0,		    /* properties_provided */
  0,		    /* properties_destroyed */
  0,		    /* todo_flags_start */
  TODO_cleanup_cfg, /* todo_flags_finish */
};

class pass_loop_mgo : public gimple_opt_pass
{
public:
  pass_loop_mgo (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_loop_mgo, ctxt)
  {}

  virtual bool gate (function *) { return flag_tree_mem_gathering; }
  virtual unsigned int execute (function *);

}; // class pass_loop_mgo

unsigned int
pass_loop_mgo::execute (function *fun)
{
  if (number_of_loops (fun) <= 2)
    return 0;

  return do_mgo ();
}

} // namespace

gimple_opt_pass *
make_pass_loop_mgo (gcc::context *ctxt)
{
  return new pass_loop_mgo (ctxt);
}
