/* Copyright (C) 2019-2022 Free Software Foundation, Inc.

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
#include "tree-pass.h"
#include "cgraph.h"
#include "gimple.h"
#include "gimple-iterator.h"
#include "gimple-pretty-print.h"
#include "ssa.h"
#include "tree-cfg.h"
#include "stor-layout.h"
#include "ipa-lto-utils.h"
#include "ipa-utils.h"

unsigned
ipa_void_ptr_param_specialization (void)
{
  cgraph_node *cnode = NULL;

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (cnode)
    {
      cfun_context ctx (cnode);
      basic_block bb = NULL;

      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gimple_stmt_iterator gsi = gsi_start_bb (bb); !gsi_end_p (gsi);
	       gsi_next (&gsi))
	    {
	      gimple *stmt = gsi_stmt (gsi);
	      gcall *call = dyn_cast<gcall *> (stmt);
	      if (NULL == call)
		continue;

	      tree fndecl = gimple_call_fndecl (call);
	      if (!fndecl)
		continue;

	      cgraph_node *callee = cgraph_node::get (fndecl);
	      if (!callee)
		continue;

	      unsigned non_recursive_callers = 0;
	      for (cgraph_edge *caller_edge = callee->callers; caller_edge;
		   caller_edge = caller_edge->next_caller)
		{
		  if (caller_edge->caller == cnode)
		    continue;
		  non_recursive_callers++;
		}

	      if (1 != non_recursive_callers)
		continue;

	      // Let's find out whether there is a void* parameter
	      // That is not in the last position...
	      unsigned n = gimple_call_num_args (call);
	      unsigned i = 0;
	      bool has_void_ptr_parameter_non_void_ptr_arg = false;
	      for (tree param = DECL_ARGUMENTS (fndecl); NULL_TREE != param;
		   param = DECL_CHAIN (param))
		{
		  tree param_type = TREE_TYPE (param);
		  if (i >= n)
		    {
		      i++;
		      break;
		    }
		  if (param_type != ptr_type_node)
		    {
		      i++;
		      continue;
		    }

		  tree arg_i = gimple_call_arg (call, i);
		  tree arg_i_type = TREE_TYPE (arg_i);

		  if (arg_i_type == ptr_type_node)
		    {
		      i++;
		      continue;
		    }

		  has_void_ptr_parameter_non_void_ptr_arg = true;
		  break;
		}

	      if (!has_void_ptr_parameter_non_void_ptr_arg)
		continue;

	      if (dump_file)
		{
		  fprintf (dump_file,
			   "We have an interesting arg/param - pair\n");
		  print_gimple_stmt (dump_file, call, TDF_NONE);
		  fprintf (dump_file, "\n");
		}

	      unsigned j = 0;
	      tree param = NULL_TREE;
	      for (param = DECL_ARGUMENTS (fndecl); NULL_TREE != param;
		   param = DECL_CHAIN (param))
		{
		  if (j == i)
		    break;
		  j++;
		}

	      tree arg_i = gimple_call_arg (call, i);
	      TREE_TYPE (param) = TREE_TYPE (arg_i);
	      relayout_decl (param);

	      unsigned k = 0;
	      tree var = NULL_TREE;
	      cfun_context ctx2 (fndecl);
	      hash_set<gimple *> stmts2;

	      FOR_EACH_SSA_NAME (k, var, cfun)
		{
		  // if (!SSA_NAME_IS_DEFAULT_DEF (var)) continue;
		  //  We have the default definition of a parameter
		  tree ssa_name = SSA_NAME_VAR (var);
		  if (ssa_name != param)
		    continue;

		  if (dump_file)
		    {
		      fprintf (dump_file,
			       "We must change the following variable...");
		      print_generic_expr (dump_file, var, TDF_NONE);
		      fprintf (dump_file, "\n");
		      print_generic_expr (dump_file, ssa_name, TDF_NONE);
		      fprintf (dump_file, "\n");
		      print_generic_expr (dump_file, param, TDF_NONE);
		      fprintf (dump_file, "\n");
		    }

		  TREE_TYPE (var) = TREE_TYPE (arg_i);
		}
	    }
	}
    }

  return 0;
}

namespace {
const pass_data pass_data_ipa_void_ptr_param_specialization = {
  SIMPLE_IPA_PASS,
  "void-ptr-param-specialization",
  OPTGROUP_NONE,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0,
  0,
  0,
  (TODO_update_ssa),
};

class pass_ipa_void_ptr_param_specialization : public simple_ipa_opt_pass
{
public:
  pass_ipa_void_ptr_param_specialization (gcc::context *ctx)
    : simple_ipa_opt_pass (pass_data_ipa_void_ptr_param_specialization, ctx)
  {}

  virtual bool gate (function *)
  {
    return flag_ipa_void_ptr_param_specialization && lang_c_p ();
  }

  virtual unsigned execute (function *)
  {
    return ipa_void_ptr_param_specialization ();
  }
};
} /* namespace.  */

simple_ipa_opt_pass *
make_pass_ipa_void_ptr_param_specialization (gcc::context *ctx)
{
  return new pass_ipa_void_ptr_param_specialization (ctx);
}
