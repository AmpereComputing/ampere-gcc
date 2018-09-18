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
#include "predict.h"
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
#include "tree-into-ssa.h"

typedef vec<tree> expr_vec;

const char *uninlined_function_postfix = "innermost_loop";

/* Given stmt is an assign statement and given op is its LHS.  */

static bool
is_defined_in_stmt (const gimple *stmt, const tree op)
{
  tree lhs;
  if (gimple_code (stmt) == GIMPLE_ASSIGN)
    {
      lhs = gimple_assign_lhs (stmt);
      if (lhs == op)
        return true;
    }
  return false;
}

/* Check if op is LHS of assignment within current bb.  */

static bool
is_defined_inside (gimple *stmt, const tree op)
{
  gimple_stmt_iterator gsi;

  /* Get a gsi for the bb stmt belongs to (pointing to stmt).  */
  gsi = gsi_for_stmt (stmt);

  /* Start search in previous stmt.  */
  gsi_prev (&gsi);

  /* Iterate over all previous stmts in bb.  */
  for (; !gsi_end_p (gsi); gsi_prev (&gsi))
    {
      if (is_defined_in_stmt (gsi_stmt (gsi), op))
        return true;
    }
  return false;
}

typedef void (*op_callback) (void *g, tree op, gimple *stmt, unsigned index);

/* Call cb with arg g for each operand of each statement of each bb of the loop.  */

static void
for_each_operand_in_loop (const struct loop *loop, op_callback cb, void *g)
{
  basic_block *bbs;
  unsigned num_nodes;
  unsigned i;

  /* Get the basic blocks.  */
  bbs = get_loop_body (loop);
  num_nodes = loop->num_nodes;

  /* Iterate over basic blocks. */
  for (i = 0; i < num_nodes; i++)
    {
      basic_block bb;
      bb = bbs[i];

      /* Iterate over statements in bb.  */
      gimple_stmt_iterator iter = gsi_start_bb (bb);
      for ( ; !gsi_end_p (iter); gsi_next (&iter))
	{
	  gimple *stmt;
	  unsigned j;
	  stmt = gsi_stmt (iter);

	  /* Iterate over operands in bb.  */
	  for (j = 0; j < gimple_num_ops (stmt); j++)
	    {
	      tree op;
	      op = gimple_op (stmt, j);
	      if (op)
		{
		  /* Here is the callback. */
		  cb (g, op, stmt, j);
		}
	    }
	}
    }

  /* Free the bb list.  */
  free (bbs);
}

/* Add operand to vector if:
    - it is not LHS of assignment, and
    - op is VAR_DECL or PARM_DECL, and
    - op is not yet in v, and
    - op is not defined inside of stmt's bb.  */

static void
collect_cb (void *g, tree op, gimple *stmt, unsigned index)
{
  expr_vec *v = (expr_vec *) g;
  enum tree_code code;

  if (dump_file)
    fprintf (dump_file, "%s: Entering.\n", __func__);

  /* Filter out LHS of assignments.  */
  if (gimple_code (stmt) == GIMPLE_ASSIGN && index == 0)
    {
      if (dump_file)
        fprintf (dump_file, "Filtering out LHS of assignment.\n");
      return;
    }

  code = TREE_CODE (op);

  /* Filter out op, which are not VAR_DECL or PARM_DECL.  */
  if (code != VAR_DECL && code != PARM_DECL)
    {
      if (dump_file)
        fprintf (dump_file, "Filtering out op, which is not (VAR_DECL or PARM_DECL).\n");
       return;
    }

  /* Filter out if op already included.  */
  if (v->contains (op))
    {
      if (dump_file)
        fprintf (dump_file, "Filtering out op, which is arleady included.\n");
       return;
    }

  /* Filter out ops, which are defined inside bb. */
  if (is_defined_inside (stmt, op))
    {
      if (dump_file)
        fprintf (dump_file, "Filtering out op, which is defined inside bb.\n");
       return;
    }

  if (dump_file)
    {
    fprintf (dump_file, "Calling safe_push() for op ");
      const char *name = "<unknown name>";
      if (DECL_NAME(op) && IDENTIFIER_POINTER (DECL_NAME (op)))
	name = identifier_to_locale (IDENTIFIER_POINTER (DECL_NAME (op)));
      fprintf (dump_file, "'%s'\n", name);
    }

  v->safe_push(op);
}

/* Return unique list of operands in the given loop,
   which are defined outside of the loop.  */

static expr_vec
collect_def_outside (struct loop *loop)
{
  expr_vec v = vNULL;

  if (dump_file)
    fprintf (dump_file, "%s: Entering.\n", __func__);

  for_each_operand_in_loop (loop, collect_cb, (void *) &v);
  return v;
}

/* Set boolean to true if:
    - stmt is GIMPLE_CALL.  */

static void
contains_call_cb (void *r, tree, gimple *stmt, unsigned)
{
  bool *ret = (bool *) r;
  if (gimple_code (stmt) == GIMPLE_CALL)
    *ret = true;
}

/* Return true if loop contains a call statement with operands.  */

static bool
contains_call (struct loop *loop)
{
  bool ret = false;
  for_each_operand_in_loop (loop, contains_call_cb, (void *) &ret);
  return ret;
}

struct var_to_parm_cb_p
{
  tree d;
  tree d_parm;
};

/* Replace op in stmt by p->d_parm if op == p->d.  */

static void
var_to_parm_cb (void *g, tree op, gimple *stmt, unsigned index)
{
  struct var_to_parm_cb_p *p = (struct var_to_parm_cb_p *) g;

  if (p->d == op)
    {
      gimple_set_op (stmt, index, p->d_parm);
    }
}

/* Replace ops in all stmts of loop by p->d_parm if op == p->d.  */

static void
convert_var_to_parm_uses (struct loop *loop, tree d, tree d_parm)
{
  struct var_to_parm_cb_p c;
  c.d = d;
  c.d_parm = d_parm;
  for_each_operand_in_loop (loop, var_to_parm_cb, (void *) &c);
}

/* Create a function declaration with void return type.  */

static tree
build_void_function_declaration (struct loop *loop, tree name, expr_vec parameter_vector, vec<tree> *args)
{
  /* We use NULL_TREE as placeholder here.
     This will be fixed later on.  */
  tree type = NULL_TREE;

  /* Create the function declaration.  */
  tree decl = build_decl (input_location, FUNCTION_DECL, name, type);

  TREE_STATIC (decl) = 1;
  TREE_USED (decl) = 1;
  DECL_ARTIFICIAL (decl) = 1;
  DECL_NAMELESS (decl) = 0;
  DECL_IGNORED_P (decl) = 0;
  TREE_PUBLIC (decl) = 0;
  DECL_UNINLINABLE (decl) = 1;
  DECL_EXTERNAL (decl) = 0;
  DECL_CONTEXT (decl) = NULL_TREE;
  DECL_INITIAL (decl) = make_node (BLOCK);
  BLOCK_SUPERCONTEXT (DECL_INITIAL (decl)) = decl;
  DECL_ATTRIBUTES (decl) = DECL_ATTRIBUTES (cfun->decl);

  /* Create result declaration.  */
  tree t = build_decl (DECL_SOURCE_LOCATION (decl),
		  RESULT_DECL, NULL_TREE, void_type_node);

  DECL_ARTIFICIAL (t) = 1;
  DECL_IGNORED_P (t) = 1;
  DECL_CONTEXT (t) = decl;
  DECL_RESULT (decl) = t;

  /* Now we prepare several collections from the parameter vector.  */

  tree t_first = NULL; /* First element of decl chain.  */
  tree t_last = NULL; /* Last element of decl chain.  */
  tree types = NULL_TREE; /* TREE_LIST of types.  */
  tree *pp = &types; /* Helper to create the TREE_LIST. */

  /* Prepare the arguments collected earlier on.  */
  int i = -1;
  tree d = NULL;
  FOR_EACH_VEC_ELT (parameter_vector, i, d)
    {
      /* Append parameter to args vector.  */
      args->safe_push (d);

      /* Get parameter type.  */
      tree type_new = copy_node (TREE_TYPE (d));

      /* Append type to tree list.  */
      *pp = build_tree_list (NULL, type_new);
      pp = &TREE_CHAIN (*pp);

      /* Allocate and initialize parameter declaration.  */
      tree d_parm = build_decl (DECL_SOURCE_LOCATION (decl), PARM_DECL,
                           DECL_NAME (d), type_new);
      DECL_ARG_TYPE (d_parm) = TREE_TYPE (d);
      DECL_ARTIFICIAL (d_parm) = 1;
      DECL_CONTEXT (d_parm) = decl;
      if (POINTER_TYPE_P (TREE_TYPE (d)))
	TYPE_RESTRICT (TREE_TYPE (d_parm)) = 1;

      if (dump_file)
	{
	  const char *name = "<unknown name>";
	  tree t TREE_TYPE (d);
	  int isptr = 0;
	  if (DECL_NAME(d) && IDENTIFIER_POINTER (DECL_NAME (d)))
	    {
	      name = identifier_to_locale (IDENTIFIER_POINTER (DECL_NAME (d)));
	      isptr = POINTER_TYPE_P (t);
	    }
	  fprintf (dump_file, "Parameter %s isptr=%i\n", name, isptr);
	}

      /* Convert the loop to use the parameters.  */
      convert_var_to_parm_uses (loop, d, d_parm);

      if (!t_first)
        {
          t_first = d_parm;
          t_last = d_parm;
        }
      else
        {
          DECL_CHAIN (t_last) = d_parm;
          t_last = d_parm;
        }
    }

  /* Replace the placeholder type by the actual type (void f(args...)).  */
  type = build_function_type (void_type_node, types);
  TREE_TYPE (decl) = type;
  DECL_ARGUMENTS (decl) = t_first;

  /* Allocate memory for the function structure.  The call to
     allocate_struct_function clobbers CFUN, so we need to restore
     it afterward.  */
  push_struct_function (decl);
  cfun->function_end_locus = DECL_SOURCE_LOCATION (decl);
  init_tree_ssa (cfun);
  pop_cfun ();

  return decl;
}

/* Converts the loop body into its own function
 * with the given arguments.
 *
 * This is inspired by create_omp_child_function and create_loop_fn.  */

static void
body_to_fun (struct loop *loop, expr_vec parameter_vector)
{
  /* Build function declaration.  */
  tree name = clone_function_name (cfun->decl, uninlined_function_postfix);
  vec<tree> args = vNULL; /* Vector of parameters. */
  tree decl = build_void_function_declaration (loop, name, parameter_vector, &args);

  /* Fill the function body.  */
  gimple_seq body = NULL;
  gimple *bind = gimple_build_bind (NULL, body, DECL_INITIAL (decl));
  gimple_seq_add_stmt (&body, bind);

  /* We'll create a CFG for child_fn, so no gimple body is needed.  */
  gimple_set_body (decl, body);

  struct function *child_cfun = DECL_STRUCT_FUNCTION (decl);

  /* We need a SESE (single entry - single exit) region to ease the outlining.  */

  basic_block in_bb = create_preheader (loop, CP_FORCE_PREHEADERS);

  if (dump_file)
    {
      fprintf (dump_file, "%s: in_bb: %i\n", __func__, in_bb->index);
      fprintf (dump_file, "%s: loop->header: %i\n", __func__, loop->header->index);
      fprintf (dump_file, "%s: loop->latch: %i\n", __func__, loop->latch->index);
    }

  edge out = single_exit (loop);
  if (!out)
    {
      if (dump_file)
        fprintf (dump_file, "Loop does not have a single exit!\n");
    }

  gcc_assert (out != NULL);

  if (dump_file)
    {
      fprintf (dump_file, "%s: Exit edge src: %i.\n", __func__, out->src->index);
      fprintf (dump_file, "%s: Exit edge dest: %i.\n", __func__, out->dest->index);
    }

  basic_block out_bb = split_edge (out);

  if (dump_file)
    {
      fprintf (dump_file, "%s: out_bb: %i\n", __func__, out_bb->index);
    }

  /* Move the single-entry-single-exit region into its own function.
     We get the new BB in the original function (which returns
     the "factored-out" region.  */
  basic_block new_bb = move_sese_region_to_fn (child_cfun, in_bb,
                                   out_bb, NULL_TREE);

  if (dump_file)
    {
      fprintf (dump_file, "%s: new_bb: %i\n", __func__, new_bb->index);
      fprintf (dump_file, "new_bb has %u edges: ", EDGE_COUNT(new_bb->preds));
      edge p;
      edge_iterator ei;
      FOR_EACH_EDGE (p, ei, new_bb->preds)
        {
	  basic_block runner = p->src;
	  fprintf (dump_file, "bb%i, ", runner->index);
	}
      fprintf(dump_file, "-\n");
    }

  /* Add call statement into new bb */
  gimple *call_stmt = gimple_build_call_vec (decl, args);
  gimple_stmt_iterator call_iter = gsi_start_bb (new_bb);
  gsi_insert_after (&call_iter, call_stmt, GSI_NEW_STMT);

  /* Add return statement into new exit bb.  */
  gimple *stmt = gimple_build_return (NULL);
  gimple_stmt_iterator gsi = gsi_last_bb(out_bb);
  gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);

  /* Copy function properties */
  child_cfun->curr_properties = cfun->curr_properties;

  /* Create the new function call graph node */
  cgraph_node::get_create (decl);
  /* Make the new function known. */
  cgraph_node::add_new_function (decl, true);

  /* Edge fixup */
  update_max_bb_count ();
  cgraph_edge::rebuild_edges ();

  if (gimple_in_ssa_p (cfun))
    {
      if (dump_file)
	fprintf (dump_file, "gimple_in_ssa_p(cfun) is true\n");
      update_ssa (TODO_update_ssa);
    }
  else
    {
      if (dump_file)
	fprintf (dump_file, "gimple_in_ssa_p(cfun) is false\n");
    }


  push_cfun (child_cfun);
  update_max_bb_count ();
  cgraph_edge::rebuild_edges ();

  if (gimple_in_ssa_p (cfun))
    {
      if (dump_file)
	fprintf (dump_file, "gimple_in_ssa_p(child) is true\n");
      update_ssa (TODO_update_ssa);
    }
  else
    {
      if (dump_file)
	fprintf (dump_file, "gimple_in_ssa_p(child) is false\n");
    }

  pop_cfun ();
}

static unsigned int
extract_loop_to_function ()
{
  struct loop *loop;
  struct loop *lu;
  expr_vec v = vNULL;
  unsigned n;

  lu = NULL;

  /* First create the list of loop exits of cfun
     (searches all edges of all bb in cfun).  */
  record_loop_exits ();

  n = 0;
  FOR_EACH_LOOP_FN (cfun, loop, LI_ONLY_INNERMOST)
    {
      /* We need single-entry single-exit loops.  */
      if (!single_exit (loop))
	continue;
      if (EDGE_COUNT(loop->header->preds) > 2)
	continue;

      /* We can't deal with calls inside of loops.  */
      if (contains_call (loop))
	continue;

      if (n < loop->num_nodes)
	{
	  n = loop->num_nodes;
	  lu = loop;
	}
    }

  if (lu)
    {
      const char *fun_to_uninline = noloopalias;
      if (dump_file)
        fprintf (dump_file,
                 "%s:%d (%s): uninlining in %s\n",
                 __FILE__, __LINE__, __func__, fun_to_uninline);

      /* First we get a unique list of operands in the loop,
         which are defined outside of the loop.  */
      v = collect_def_outside (lu);

      /* Now we create a new function with the given list of arguments.  */
      body_to_fun (lu, v);
    }

  /* Free the list of loop exits of cfun. */
  release_recorded_exits (cfun);

  return 0;
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
  virtual bool gate (function *fun)
    {
      const char *fun_to_uninline = noloopalias;

      if (fun_to_uninline == NULL)
	return false;

      if (strcmp(fun_to_uninline, "*") == 0)
	return true;

      if (fun == NULL)
	return false;

      return (strcmp (function_name (fun), fun_to_uninline) == 0);
    }

  virtual unsigned int execute (function *)
    {
      return extract_loop_to_function ();
    }
};

} // anon namespace

gimple_opt_pass *
make_pass_uninline_innermost_loops (gcc::context *ctxt)
{
  return new pass_uninline_innermost_loops (ctxt);
}
