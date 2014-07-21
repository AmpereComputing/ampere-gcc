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
#include "ipa-ref.h"
#include "plugin-api.h"
#include "cgraph.h"
#include "function.h"
#include "tree-ssa.h"

void
print_generic_expr (FILE *file, tree t, int flags);

typedef vec <tree> expr_vec;

extern const char * uninlined_function_postfix;
const char * uninlined_function_postfix = "innermost_loop";

static bool
is_defined_in_stmt (gimple *stmt, tree var)
{
  tree lhs;
  if (gimple_code (stmt) == GIMPLE_ASSIGN)
    {
      lhs = gimple_assign_lhs (stmt);
      if (lhs == var)
        return true;
    }
  return false;
}

static bool
is_defined_in_bb (gimple_stmt_iterator gsi, tree var)
{
  for (; !gsi_end_p (gsi); gsi_prev (&gsi))
    {
      if (is_defined_in_stmt (gsi_stmt (gsi), var))
        return true;
    }
  return false;
}

static bool
is_defined_outside (gimple *use, tree var)
{
  gimple_stmt_iterator gsi;
  gsi = gsi_for_stmt (use);
  gsi_prev (&gsi);
  /* FIXME Recursively search other also predecessor bbs. */
  return !is_defined_in_bb (gsi, var);
}

/* FIXME Is there a standard function to do this? */
static bool
contained (expr_vec v, tree var)
{
  int i = 0;
  tree u;

  FOR_EACH_VEC_ELT (v, i, u)
    {
      if (u == var)
        return true;
    }
  return false;
}

typedef void (*op_callback) (void * g, tree op, gimple *stmt, unsigned index);

static void
for_each_operand_in_loop (struct loop * loop, op_callback cb, void * g)
{
  basic_block * bbs;
  basic_block bb;
  unsigned num_nodes;
  unsigned i;
  unsigned j;
  gimple *stmt;
  tree op;

  bbs = get_loop_body (loop);
  num_nodes = loop->num_nodes;
  for (i = 0; i < num_nodes; i++)
    {
      bb = bbs[i];
      gimple_stmt_iterator iter = gsi_start_bb (bb);
      while (!gsi_end_p (iter))
        {
          stmt = gsi_stmt (iter);
          for (j = 0; j < gimple_num_ops (stmt); j++)
            {
              op = gimple_op (stmt, j);
              if (op)
                {
                  /* Here is the callback. */
                  cb (g, op, stmt, j);
                }
            }
          gsi_next (&iter);
        }
     }
  free (bbs);
}

static void
collect_cb (void * g, tree op, gimple *stmt, unsigned index)
{
  expr_vec * v = (expr_vec *) g;
  enum tree_code code;

  if (gimple_code (stmt) == GIMPLE_ASSIGN && index == 0)
    {
      /* I assume operand 0 of an assignment is the lhs. */
      return;
    }

  code = TREE_CODE (op);
  if ((code == VAR_DECL || code == PARM_DECL) &&
      ! contained (*v, op)  &&
      is_defined_outside (stmt, op))
    {
      v->safe_push (op);
    }
}

static expr_vec
collect_def_outside (struct loop * loop)
{
  expr_vec v = vNULL;
  for_each_operand_in_loop (loop, collect_cb, (void *) & v);
  return v;
}

static void
contains_call_cb (void * r, tree, gimple *stmt, unsigned)
{
  bool * ret = (bool *) r;
  if (gimple_code (stmt) == GIMPLE_CALL)
    *ret |= true;
  else
    *ret |= false;
}

static bool
contains_call (struct loop * loop)
{
  bool ret;
  ret = false;
  for_each_operand_in_loop (loop, contains_call_cb, &ret);
  return ret;
}

struct var_to_parm_cb_p
{
  tree d;
  tree d_parm;
};

static void
var_to_parm_cb (void * g, tree op, gimple *stmt, unsigned index)
{
  struct var_to_parm_cb_p * p = (struct var_to_parm_cb_p *) g;

  if (p->d == op)
    {
      gimple_set_op (stmt, index, p->d_parm);
    }
}

static void
convert_var_to_parm_uses (struct loop * loop, tree d, tree d_parm)
{
  struct var_to_parm_cb_p c;
  c.d = d;
  c.d_parm = d_parm;
  for_each_operand_in_loop (loop, var_to_parm_cb, (void *) & c);
}

static void
body_to_fun (struct loop * loop, expr_vec uv)
{
  tree name, decl, type, t, block;
  gimple_seq body = NULL;
  gimple *bind;
  int i;
  vec<tree> args;
  struct function *fun;
  basic_block new_bb, preheader;
  edge out;
  basic_block in_bb, out_bb;

  /* Make the new function similar to create_omp_child_function. */
  name = clone_function_name (cfun->decl, uninlined_function_postfix);
  decl = build_decl (input_location, FUNCTION_DECL, name, NULL_TREE);

  TREE_STATIC (decl) = 1;
  TREE_USED (decl) = 1;
  DECL_ARTIFICIAL (decl) = 1;
  DECL_NAMELESS (decl) = 0;
  DECL_IGNORED_P (decl) = 0;
  TREE_PUBLIC (decl) = 0;
  DECL_UNINLINABLE (decl) = 1;
  DECL_EXTERNAL (decl) = 0;
  DECL_CONTEXT (decl) = NULL_TREE;

  block = make_node (BLOCK);
  DECL_INITIAL (decl) = block;

  t = build_decl (DECL_SOURCE_LOCATION (decl),
                  RESULT_DECL, NULL_TREE, void_type_node);

  DECL_ARTIFICIAL (t) = 1;
  DECL_IGNORED_P (t) = 1;
  DECL_CONTEXT (t) = decl;
  DECL_RESULT (decl) = t;

  tree d_parm = NULL;
  tree d = NULL;
  tree t_first = NULL;
  t = NULL;

  tree type_new = NULL;

  tree types = NULL_TREE;
  tree *pp = &types;

  args = vNULL;

  /* Prepare the arguments collected earlier on. */
  i = 0;
  FOR_EACH_VEC_ELT (uv, i, d)
    {
      args.safe_push (d);

      type_new = copy_node (TREE_TYPE (d));

      *pp = build_tree_list (NULL, type_new);
      pp = &TREE_CHAIN (*pp);

      d_parm = build_decl (DECL_SOURCE_LOCATION (decl), PARM_DECL,
                           DECL_NAME (d), type_new);
      DECL_ARG_TYPE (d_parm) = TREE_TYPE (d);
      DECL_ARTIFICIAL (d_parm) = 1;
      DECL_CONTEXT (d_parm) = decl;
      TYPE_RESTRICT (TREE_TYPE (d_parm)) = 1;
      convert_var_to_parm_uses (loop, d, d_parm);

      if (!t_first)
        {
          t = d_parm;
          t_first = d_parm;
        }
      else
        {
          DECL_CHAIN (t) = d_parm;
          t = d_parm;
        }
    }

  type = build_function_type (void_type_node, types);

  DECL_ARGUMENTS (decl) = t_first;
  TREE_TYPE (decl) = type;

  push_struct_function (decl);
  cfun->function_end_locus = DECL_SOURCE_LOCATION (decl);
  pop_cfun ();

  /* Fill the function body. */
  bind = gimple_build_bind (NULL, body, block);
  gimple_seq_add_stmt (&body, bind);

  gimple_set_body (decl, body);

  fun = DECL_STRUCT_FUNCTION (decl);

  init_tree_ssa (fun);

  out = single_exit (loop);

  out_bb = split_edge (out);

  /* FIXME I patched this function such that
           it always creates the
           preheader.
  */
  preheader = create_preheader (loop, 128);
  in_bb = preheader;

  new_bb = move_sese_region_to_fn (fun, in_bb,
                                   out_bb, NULL_TREE);

  DECL_STRUCT_FUNCTION (decl)->curr_properties = cfun->curr_properties;

  /* Make the new function known. */
  cgraph_node::add_new_function (decl, true);

  gimple_stmt_iterator call_iter = gsi_start_bb (new_bb);
  gimple *call_stmt;
  call_stmt = gimple_build_call_vec (decl, args);
  gsi_insert_after (&call_iter, call_stmt,
                    GSI_NEW_STMT);

  cgraph_edge::rebuild_edges ();

  push_cfun (fun);
  cgraph_edge::rebuild_edges ();
  pop_cfun ();
}

static unsigned int
extract_loop_to_function (void)
{
  struct loop *loop;
  struct loop *lu;
  expr_vec v = vNULL;
  bool cc;

  const char * fun_to_uninline;
  unsigned n;

  lu = NULL;

  record_loop_exits ();

  fun_to_uninline = noalias;

  n = 0;
  FOR_EACH_LOOP (loop, LI_ONLY_INNERMOST)
    {
      /* FIXME Try to generalize this. */
      /* We assume that we outline at most one
         innermost loop.
         We choose the biggest loop, assuming
         it will bring the most benefit.
         FIXME Make sure there flows no data out of
         the loop.
      */
      if (single_exit (loop) &&
          strcmp (function_name (cfun), fun_to_uninline) == 0)
        {
          cc = contains_call (loop);
          if (!cc && n < loop->num_nodes)
            {
              n = loop->num_nodes;
              lu = loop;
            }
        }
    }

  if (lu)
    {
      if (dump_file)
        fprintf (dump_file,
                 "%s:%d (%s): uninlining in %s\n",
                 __FILE__, __LINE__, __func__, fun_to_uninline);
      v = collect_def_outside (lu);
      body_to_fun (lu, v);
    }

  release_recorded_exits (cfun);

  return 0;
}

static bool
gate_uninline_innermost_loops (void)
{
  return noalias != 0;
}

namespace {

const pass_data pass_data_uninline_innermost_loops =
{
  GIMPLE_PASS, /* type */
  "uninline-innermost-loops", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_UNINLINE_INNERMOST_LOOPS, /* tv_id */
  PROP_gimple_any, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_uninline_innermost_loops: public gimple_opt_pass
{
public:
  pass_uninline_innermost_loops (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_uninline_innermost_loops, ctxt)
  {}

  /* opt_pass methods: */
  bool gate (function *) { return gate_uninline_innermost_loops (); }
  unsigned int execute (function *) { return extract_loop_to_function (); }

};

} // anon namespace

gimple_opt_pass *
make_pass_uninline_innermost_loops (gcc::context *ctxt)
{
  return new pass_uninline_innermost_loops (ctxt);
}
