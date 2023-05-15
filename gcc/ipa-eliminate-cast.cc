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
#include "tree-pretty-print.h"
#include "gimple.h"
#include "ssa.h"
#include "ipa-utils.h"

static unsigned
ipa_eliminate_cast (void)
{
  cgraph_node *cnode = NULL;

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (cnode)
    {
      cfun_context ctx (cnode);
      tree local = NULL;
      unsigned i = 0;

      FOR_EACH_LOCAL_DECL (cfun, i, local)
	{
	  if (TREE_TYPE (local) != ptr_type_node)
	    continue;

	  tree ssa = NULL;
	  unsigned j = 0;
	  auto_vec<tree> ssas;
	  FOR_EACH_SSA_NAME (j, ssa, cfun)
	    {
	      tree ssa_name = SSA_NAME_VAR (ssa);
	      if (ssa_name != local)
		continue;
	      ssas.safe_push (ssa);
	    }

	  if (ssas.length () != 1)
	    continue;

	  tree inspecting = ssas.pop ();

	  gimple *s = SSA_NAME_DEF_STMT (inspecting);

	  gassign *_gassign = dyn_cast<gassign *> (s);
	  if (!_gassign)
	    continue;

	  const enum gimple_rhs_class rhs_class
	    = gimple_assign_rhs_class (_gassign);
	  if (GIMPLE_SINGLE_RHS != rhs_class)
	    continue;

	  tree rhs = gimple_assign_rhs1 (_gassign);
	  tree rhs_t = TREE_TYPE (rhs);
	  if (POINTER_TYPE != TREE_CODE (rhs_t))
	    continue;

	  gimple *stmt;
	  imm_use_iterator iterator;
	  bool can_transform = true;
	  FOR_EACH_IMM_USE_STMT (stmt, iterator, inspecting)
	    {
	      bool is_cond = dyn_cast<gcond *> (stmt);
	      bool is_gdebug = dyn_cast<gdebug *> (stmt);
	      can_transform &= is_cond || is_gdebug;
	    }

	  if (!can_transform)
	    continue;

	  if (dump_file)
	    {
	      fprintf (dump_file, "Changing type of local '");
	      print_generic_expr (dump_file, local, TDF_NONE);
	      fprintf (dump_file, "' from ");
	      print_generic_expr (dump_file, TREE_TYPE (local), TDF_NONE);
	      fprintf (dump_file, " to ");
	      print_generic_expr (dump_file, rhs_t, TDF_NONE);
	      fprintf (dump_file, "\n");
	    }
	  TREE_TYPE (local) = rhs_t;

	  ssas.safe_push (inspecting);
	  for (auto ssa: ssas)
	    {
	      if (dump_file)
		{
		  fprintf (dump_file, "Changing type of ssa '");
		  print_generic_expr (dump_file, ssa, TDF_NONE);
		  fprintf (dump_file, "' from ");
		  print_generic_expr (dump_file, TREE_TYPE (ssa), TDF_NONE);
		  fprintf (dump_file, " to ");
		  print_generic_expr (dump_file, rhs_t, TDF_NONE);
		  fprintf (dump_file, "\n");
		}
	      TREE_TYPE (ssa) = rhs_t;
	    }
	}
    }

  return 0;
}

namespace {
const pass_data pass_data_ipa_eliminate_cast = {
  SIMPLE_IPA_PASS,
  "eliminate-cast",
  OPTGROUP_NONE,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0,
  0,
  0,
  0,
};

class pass_ipa_eliminate_cast : public simple_ipa_opt_pass
{
public:
  pass_ipa_eliminate_cast (gcc::context *ctx)
    : simple_ipa_opt_pass (pass_data_ipa_eliminate_cast, ctx)
  {}

  virtual bool gate (function *)
  {
    return flag_ipa_eliminate_cast;
  }

  virtual unsigned execute (function *) { return ipa_eliminate_cast (); }
};
} /* namespace.  */

simple_ipa_opt_pass *
make_pass_ipa_eliminate_cast (gcc::context *ctx)
{
  return new pass_ipa_eliminate_cast (ctx);
}
