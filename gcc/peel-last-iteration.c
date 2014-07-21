#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "hash-set.h"
#include "machmode.h"
#include "vec.h"
#include "double-int.h"
#include "input.h"
#include "alias.h"
#include "symtab.h"
#include "options.h"
#include "wide-int.h"
#include "inchash.h"
#include "tree.h"
#include "fold-const.h"
#include "hashtab.h"
#include "tm.h"
#include "hard-reg-set.h"
#include "function.h"
#include "rtl.h"
#include "flags.h"
#include "statistics.h"
#include "real.h"
#include "fixed-value.h"
#include "insn-config.h"
#include "expmed.h"
#include "dojump.h"
#include "explow.h"
#include "calls.h"
#include "varasm.h"
#include "stmt.h"
#include "expr.h"
#include "gimple-pretty-print.h"
#include "predict.h"
#include "dominance.h"
#include "cfg.h"
#include "cfgloop.h"
#include "cfghooks.h"
#include "basic-block.h"
#include "tree-ssa-alias.h"
#include "internal-fn.h"
#include "gimple-expr.h"
#include "is-a.h"
#include "gimple.h"
#include "gimplify.h"
#include "gimple-iterator.h"
#include "tree-cfg.h"
#include "gimplify-me.h"
#include "gimple-ssa.h"
#include "tree-ssa-operands.h"
#include "tree-phinodes.h"
#include "ssa-iterators.h"
#include "dumpfile.h"
#include "tree-pass.h"

gcond *
get_loop_exit_condition (const struct loop *loop);

extern const char * uninlined_function_postfix;

void initialize_original_copy_tables (void);

/* FIXME Refactor to separate functions. */
static unsigned int
peel_in_fn (void)
{
  struct loop *loop;
  basic_block *bbs, *copied_bbs;
  basic_block bb, copied_bb;

  edge exit_edge, copied_exit_edge;
  edge e, copied_e;
  edge_iterator ei, copied_ei;
  edge entry_edge;
  basic_block exit_block;
  basic_block copied_header;

  edge true_edge;
  edge false_edge;

  gimple_stmt_iterator phis;
  gimple_stmt_iterator copied_phis;

  gimple_stmt_iterator def_iterator;
  gimple_stmt_iterator copied_def_iterator;

  gimple_stmt_iterator cond_iterator;
  gimple *last_stmt;

  gimple *phi, *copied_phi;
  gimple *use_stmt;

  tree phi_op;
  tree copied_phi_op;
  tree phi_result, copied_phi_result;

  imm_use_iterator iter;
  use_operand_p use_p;
  basic_block use_bb;
  basic_block copied_def_bb;
  gimple *def_stmt;
  gimple *copied_def_stmt;

  basic_block removed_edge_dest;
  basic_block dom_bb;

  enum tree_code old_cond_code;
  enum tree_code new_cond_code;
  gimple *exit_cond;

  unsigned i;
  unsigned j;
  unsigned num_nodes;

  const char * fun_to_uninline;
  int fun_to_uninline_len;

  int uninlined_function_postfix_len;

  gimple *return_stmt;

  char fun_to_peel[256];

  int k;

  entry_edge = NULL;
  copied_def_stmt = NULL;

  fun_to_uninline = noalias;
  fun_to_uninline_len = strlen (fun_to_uninline);
  uninlined_function_postfix_len = strlen (uninlined_function_postfix);

  /* FIXME Make this more safe. */
  snprintf(fun_to_peel, sizeof fun_to_peel, "%s.%s", fun_to_uninline,
           uninlined_function_postfix);

  loop_optimizer_init (LOOPS_HAVE_SIMPLE_LATCHES | LOOPS_HAVE_PREHEADERS);

  record_loop_exits ();
  initialize_original_copy_tables ();
  k = -1;
  FOR_EACH_LOOP (loop, LI_ONLY_INNERMOST)
    {
      k++;
      if (strncmp (function_name (cfun), fun_to_peel, fun_to_uninline_len + 1 + uninlined_function_postfix_len) != 0)
        {
          if (dump_file)
            fprintf (dump_file, "%s:%d (%s): wrong function %s\n",
                     __FILE__, __LINE__, __func__,
                     function_name (cfun));
          continue;
        }
      if (k != 0)
        {
          if (dump_file)
            fprintf (dump_file, "%s:%d (%s): wrong loop\n",
                     __FILE__, __LINE__, __func__
                     );
          continue;
        }

      if (dump_file)
          fprintf (dump_file, "%s:%d (%s): found our loop\n",
                   __FILE__, __LINE__, __func__
                   );

      if (loop->header->preds->length () != 2)
        {
          if (dump_file)
            fprintf (dump_file, "%s:%d (%s): wrong preds length\n",
                     __FILE__, __LINE__, __func__
                     );
          continue;
        }

      exit_edge = single_exit (loop);
      if (!exit_edge)
        {
          if (dump_file)
            fprintf (dump_file, "%s:%d (%s): not single exit edge\n",
                     __FILE__, __LINE__, __func__
                     );
          continue;
        }
      if (exit_edge->src != loop->header)
        {
          if (dump_file)
            fprintf (dump_file, "%s:%d (%s): exit edge not from header\n",
                     __FILE__, __LINE__, __func__
                     );
          continue;
        }

      exit_cond = get_loop_exit_condition (loop);
      if (!exit_cond)
        {
          if (dump_file)
            fprintf (dump_file, "%s:%d (%s): exit condition not found\n",
                     __FILE__, __LINE__, __func__
                     );
          continue;
        }

      old_cond_code = gimple_cond_code (exit_cond);
      if (old_cond_code != LE_EXPR && old_cond_code != GE_EXPR)
        {
          if (dump_file)
            fprintf (dump_file, "%s:%d (%s): cond code is wrong\n",
                     __FILE__, __LINE__, __func__
                     );
          continue;
        }

      if (dump_file)
          fprintf (dump_file, "%s:%d (%s): about to copy loop\n",
                   __FILE__, __LINE__, __func__
                   );

      FOR_EACH_EDGE (e, ei, EXIT_BLOCK_PTR_FOR_FN (cfun)->preds)
        {
          return_stmt  = gimple_build_return (NULL_TREE);
          gsi_insert_on_edge (e, return_stmt);
        }
      gsi_commit_edge_inserts ();

      if (old_cond_code == LE_EXPR)
        new_cond_code = LT_EXPR;
      else
        new_cond_code = GT_EXPR;

      num_nodes = loop->num_nodes;

      create_preheader (loop, 0);
      copied_bbs = XNEWVEC (basic_block, num_nodes);
      bbs = get_loop_body (loop);

      FOR_EACH_EDGE (e, ei, loop->header->preds)
        {
          if (e->src != loop->latch)
            entry_edge = e;
        }

      /* Do the copying. */
      copy_bbs (bbs, num_nodes, copied_bbs, &exit_edge, 1,
                &copied_exit_edge, loop_outer (loop), exit_edge->dest, true);

      /* Fix the condition in the original. */
      gimple_cond_set_condition (as_a <gcond *> (exit_cond), new_cond_code,
                                 gimple_cond_lhs (exit_cond), gimple_cond_rhs (exit_cond));

      /* Redirect edges. */
      exit_block = exit_edge->dest;

      copied_header = copied_bbs[0];
      redirect_edge_and_branch (exit_edge, copied_header);

      set_immediate_dominator (CDI_DOMINATORS, exit_block, copied_exit_edge->src);
      set_immediate_dominator (CDI_DOMINATORS, copied_header, exit_edge->src);

      for (i = 0; i < num_nodes; ++i)
        {
          bb = bbs[i];
          copied_bb = copied_bbs[i];

          /* Fix phi node. */
          for (phis = gsi_start_phis (bb),
               copied_phis = gsi_start_phis (copied_bb);
               !gsi_end_p (phis);
               gsi_next (&phis), gsi_next (&copied_phis))
            {
              phi = gsi_stmt (phis);
              copied_phi = gsi_stmt (copied_phis);

              phi_result = gimple_phi_result (phi);

              copied_phi_result = gimple_phi_result (copied_phi);
              /* Fix uses. */
              FOR_EACH_IMM_USE_STMT (use_stmt, iter, phi_result)
                {
                  use_bb = gimple_bb (use_stmt);

                  if (dominated_by_p (CDI_DOMINATORS, use_bb, copied_bbs[0]))
                    {
                      FOR_EACH_IMM_USE_ON_STMT (use_p, iter)
                        SET_USE (use_p, copied_phi_result);
                    }
                }

              /* Only for the header. */
              if (i == 0)
                {
                 /* FIXME This is not a generic solution, but in this case it is
                  *       sufficient. */
                  add_phi_arg (as_a <gphi*> (copied_phi), phi_result,
                               exit_edge, UNKNOWN_LOCATION);
                }

              FOR_EACH_EDGE (e, ei, bb->preds)
                {
                  if (e == entry_edge)
                    continue;

                  phi_op = PHI_ARG_DEF_FROM_EDGE (phi, e);

                  if (TREE_CODE (phi_op) == SSA_NAME)
                    {
                      def_stmt = SSA_NAME_DEF_STMT (phi_op);
                      copied_def_bb = get_bb_copy (gimple_bb (def_stmt));

                      copied_def_stmt = NULL;
                      if (gimple_code (def_stmt) == GIMPLE_PHI)
                        {
                          def_iterator = gsi_start_phis (gimple_bb (def_stmt)),
                          copied_def_iterator = gsi_start_phis (copied_def_bb);
                        }
                      else
                        {
                          def_iterator = gsi_start_bb (gimple_bb (def_stmt)),
                          copied_def_iterator = gsi_start_bb (copied_def_bb);
                        }

                      /* Find the statement that defines the value for the back edge. */
                      for (;
                           !gsi_end_p (def_iterator);
                           gsi_next (&def_iterator), gsi_next (&copied_def_iterator))
                        {
                          if (gsi_stmt (def_iterator) == def_stmt)
                              {
                                copied_def_stmt = gsi_stmt (copied_def_iterator);
                                break;
                              }
                        }

                      if (gimple_code (copied_def_stmt) == GIMPLE_PHI)
                        {
                          copied_phi_op = gimple_phi_result (copied_def_stmt);
                        }
                      else if (virtual_operand_p (gimple_phi_result (phi)))
                        {
                          copied_phi_op = gimple_vdef (copied_def_stmt);
                        }
                      else
                        {
                          copied_phi_op = gimple_assign_lhs (copied_def_stmt);
                        }

                      /* Lookup the corresponding copied edge. */
                      /* FIXME This is ugly. */
                      for (j = 0; j < num_nodes; ++j)
                        {
                          if (bbs[j] == e->src)
                            break;
                        }
                      FOR_EACH_EDGE (copied_e, copied_ei, copied_bb->preds)
                        {
                          if (copied_e->src == copied_bbs[j])
                            break;
                        }

                      /* Fix phi args */
                      add_phi_arg (as_a<gphi*> (copied_phi), copied_phi_op,
                                   copied_e, UNKNOWN_LOCATION);
                    }
                }
            }
        }

      for (i = 1; i < num_nodes; ++i)
        {
          bb = bbs[i];

          cond_iterator = gsi_last_bb (bb);
          last_stmt = gsi_stmt (cond_iterator);
          if (gimple_code (last_stmt) == GIMPLE_COND
              && gimple_cond_lhs (exit_cond) == gimple_cond_lhs (last_stmt)
              && gimple_cond_rhs (exit_cond) == gimple_cond_rhs (last_stmt)
              && gimple_cond_code (exit_cond) == gimple_cond_code (last_stmt))
            {
              extract_true_false_edges_from_block (bb,
                                                   &true_edge,
                                                   &false_edge);
              removed_edge_dest = false_edge->dest;

              remove_edge (false_edge);
              gsi_remove (&cond_iterator, true);

              true_edge->flags &= ~EDGE_FALSE_VALUE;
              true_edge->flags |= EDGE_FALLTHRU;

              dom_bb = recompute_dominator (CDI_DOMINATORS, removed_edge_dest);
              set_immediate_dominator (CDI_DOMINATORS, removed_edge_dest, dom_bb);
            }
        }
    }
  free_original_copy_tables ();
  release_recorded_exits (cfun);

  return 0;
}

static bool
gate_peel_last_iteration (void)
{
  /* Run this only as a post processing step for the uninlining pass. */
  return noalias != 0;
}

namespace {

const pass_data pass_data_peel_last_iteration =
{
  GIMPLE_PASS, /* type */
  "peel-last-iteration", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_PEEL_LAST_ITERATION, /* tv_id */
  PROP_gimple_any, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  (TODO_update_ssa | TODO_cleanup_cfg), /* todo_flags_finish */
};

class pass_peel_last_iteration: public gimple_opt_pass
{
public:
  pass_peel_last_iteration(gcc::context *ctxt)
    : gimple_opt_pass (pass_data_peel_last_iteration, ctxt)
  {}

  /* opt_pass methods: */
  virtual bool gate (function *) { return gate_peel_last_iteration (); }
  virtual unsigned int execute (function *) { return peel_in_fn (); }

};

} // anon namespace

gimple_opt_pass *
make_pass_peel_last_iteration (gcc::context *ctxt)
{
  return new pass_peel_last_iteration (ctxt);
}
