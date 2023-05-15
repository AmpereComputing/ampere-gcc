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
#include "tree-cfg.h"
#include "gimple.h"
#include "ssa.h"
#include "gimple-ssa.h"
#include "tree-into-ssa.h"
#include "cgraph.h"
#include "gimple-pretty-print.h"
#include "ipa-lto-utils.h"
#include "ipa-utils.h"

static bool bail_out = false;
extern bool
has_incoming_alignment_data (cgraph_node *);

static hash_map<tree, tree> backup_vars;
static hash_map<tree, tree> backup_memref;

static void
retype (vec<tree> &vars, tree var, tree type);

static void
analyze_assign_nop_expr (vec<tree> &vars, tree, tree, gassign *stmt)
{
  const enum tree_code t_code = gimple_assign_rhs_code (stmt);
  gcc_assert (NOP_EXPR == t_code);

  if (dump_file)
    {
      fprintf (dump_file, "Changed from ....");
      print_gimple_stmt (dump_file, stmt, TDF_NONE);
    }

  tree lhs = gimple_assign_lhs (stmt);
  tree rhs = gimple_assign_rhs1 (stmt);
  retype (vars, lhs, TREE_TYPE (rhs));

  if (dump_file)
    {
      fprintf (dump_file, "Changed to....");
      print_gimple_stmt (dump_file, stmt, TDF_NONE);
    }
}

static bool
is_interesting_type_align (tree test, tree input)
{
  if (test == input)
    return true;
  if (TYPE_MAIN_VARIANT (test) == TYPE_MAIN_VARIANT (input))
    return true;

  if (TYPE_POINTER_TO (input) == test)
    return true;
  if (TREE_TYPE (test) && TREE_TYPE (input)
      && TREE_TYPE (test) == TREE_TYPE (input))
    return true;

  return false;
}

static void
retype (tree var, tree new_t)
{
  tree old_t = TREE_TYPE (var);

  TREE_TYPE (var) = new_t;

  // Clear SSA name information if changed to incompatible type.
  if (TREE_CODE (var) == SSA_NAME && !types_compatible_p (old_t, new_t))
    SSA_NAME_PTR_INFO (var) = NULL;
}

static void
retype (vec<tree> &vars, tree var, tree type)
{
  if (TREE_TYPE (var) == type)
    return;

  if (!backup_vars.get (var))
    backup_vars.put (var, TREE_TYPE (var));

  if (dump_file)
    {
      fprintf (dump_file, "Changed...");
      print_generic_expr (dump_file, var, TDF_NONE);
      fprintf (dump_file, "...from...");
      print_generic_expr (dump_file, TREE_TYPE (var), TDF_NONE);
      fprintf (dump_file, "...to...");
      print_generic_expr (dump_file, type, TDF_NONE);
      fprintf (dump_file, "\n");
    }

  retype (var, type);

  // Add to the list of changed variables
  if (vars.contains (var))
    return;

  // Changed variables can only be SSA...
  if (TREE_CODE (var) != SSA_NAME)
    return;

  vars.safe_push (var);
}

static void
retype_ssa_for_ssa_name_to_type (vec<tree> &vars, tree ssa_name,
				 tree type)
{
  unsigned i = 0;
  tree var = NULL_TREE;

  FOR_EACH_SSA_NAME (i, var, cfun)
    {
      tree ssa_name_var = SSA_NAME_VAR (var);
      if (ssa_name_var != ssa_name)
	continue;

      retype (vars, var, type);
    }
}

static void
retype_related (vec<tree> &vars, tree var, tree type)
{
  retype (vars, var, type);
  if (!SSA_NAME_VAR (var))
    return;
  retype (vars, SSA_NAME_VAR (var), type);
  retype_ssa_for_ssa_name_to_type (vars, SSA_NAME_VAR (var), type);
}

static void
analyze_assign_pointer_plus_expr (vec<tree> &vars, tree type, tree,
				  gassign *stmt)
{
  const enum tree_code t_code = gimple_assign_rhs_code (stmt);
  gcc_assert (POINTER_PLUS_EXPR == t_code || POINTER_DIFF_EXPR == t_code);

  tree lhs = gimple_assign_lhs (stmt);
  tree rhs1 = gimple_assign_rhs1 (stmt);

  tree rhs2 = gimple_assign_rhs2 (stmt);
  gcc_assert (lhs && rhs1 && rhs2);

  tree rhs1_type = TREE_TYPE (rhs1);
  gcc_assert (rhs1_type);

  if (!is_interesting_type_align (rhs1_type, type))
    return;

  retype_related (vars, lhs, rhs1_type);
}

static void
analyze_assign_binary (vec<tree> &vars, tree type, tree var, gassign *stmt)
{
  if (bail_out)
    return;

  const enum gimple_rhs_class code = gimple_assign_rhs_class (stmt);
  gcc_assert (GIMPLE_BINARY_RHS == code);

  const enum tree_code t_code = gimple_assign_rhs_code (stmt);
  switch (t_code)
    {
    case POINTER_PLUS_EXPR:
      analyze_assign_pointer_plus_expr (vars, type, var, stmt);
      break;
    case POINTER_DIFF_EXPR:
      break;
    default:
      bail_out = true;
      if (dump_file)
	{
	  fprintf (dump_file, "Not implementing analysis for complex gimple "
			      "assignments at the moment....");
	  print_gimple_stmt (dump_file, stmt, TDF_NONE);
	}
      break;
    }
}

static void
analyze_assign_ssa_name (vec<tree> &vars, tree type, tree var, gassign *stmt)
{
  const enum tree_code t_code = gimple_assign_rhs_code (stmt);
  gcc_assert (SSA_NAME == t_code);

  tree lhs = gimple_assign_lhs (stmt);
  tree rhs1 = gimple_assign_rhs1 (stmt);

  if (TREE_CODE (lhs) == MEM_REF)
    {
      tree lhs_op_0 = TREE_OPERAND (lhs, 0);
      tree lhs_op_0_type = TREE_TYPE (lhs_op_0);
      gcc_assert (lhs_op_0 == var || rhs1 == var);

      // So here, we need to determine whether var is used in the lhs or rhs.
      if (lhs_op_0 == var && is_interesting_type_align (lhs_op_0_type, type))
	{
	  tree deref = TREE_TYPE (lhs_op_0_type);

	  if (!backup_memref.get (lhs))
	    backup_memref.put (lhs, TREE_OPERAND (lhs, 1));

	  TREE_OPERAND (lhs, 1)
	      = build_int_cst (lhs_op_0_type,
			       tree_to_uhwi (TREE_OPERAND (lhs, 1)));

	  if (!backup_vars.get (lhs))
	    backup_vars.put (lhs, TREE_TYPE (lhs));

	  retype (lhs, deref);
	  retype_related (vars, rhs1, deref);
	}

      if (rhs1 == var && is_interesting_type_align (TREE_TYPE (rhs1), type))
	{
	  if (!backup_vars.get (lhs))
	    backup_vars.put (lhs, TREE_TYPE (lhs));

	  retype (lhs, TREE_TYPE (rhs1));
	  if (!backup_memref.get (lhs))
	    backup_memref.put (lhs, TREE_OPERAND (lhs, 1));

	  TREE_OPERAND (lhs, 1)
	      = build_int_cst (TYPE_POINTER_TO (TREE_TYPE (rhs1)),
			       tree_to_uhwi (TREE_OPERAND (lhs, 1)));
	  retype_related (vars, lhs_op_0, TYPE_POINTER_TO (TREE_TYPE (rhs1)));
	}

      if (dump_file)
	{
	  print_gimple_stmt (dump_file, stmt, TDF_NONE);
	  fprintf (dump_file, "Let's double check: lhs = ");
	  print_generic_expr (dump_file, TREE_TYPE (lhs), TDF_NONE);
	  fprintf (dump_file, "\nLet's double check: op0 = ");
	  print_generic_expr (dump_file, TREE_TYPE (TREE_OPERAND (lhs, 0)),
			      TDF_NONE);
	  fprintf (dump_file, "\nLet's double check: op1 = ");
	  print_generic_expr (dump_file, TREE_TYPE (TREE_OPERAND (lhs, 1)),
			      TDF_NONE);
	  fprintf (dump_file, "\nLet's double check: rhs = ");
	  print_generic_expr (dump_file, TREE_TYPE (rhs1), TDF_NONE);
	  fprintf (dump_file, "\n");
	}
    }
  else if (TREE_CODE (lhs) == SSA_NAME)
    {
      if (is_interesting_type_align (TREE_TYPE (rhs1), type))
	{
	  if (!backup_vars.get (lhs))
	    backup_vars.put (lhs, TREE_TYPE (lhs));

	  retype (lhs, TREE_TYPE (rhs1));
	  retype_related (vars, lhs, TREE_TYPE (rhs1));
	}
    }
  else
    bail_out = true;
}

static void
analyze_assign_mem_ref_rhs (vec<tree> &vars, tree type, tree var, gassign *stmt)
{
  const enum tree_code t_code = gimple_assign_rhs_code (stmt);
  gcc_assert (MEM_REF == t_code);

  tree lhs = gimple_assign_lhs (stmt);
  tree rhs1 = gimple_assign_rhs1 (stmt);

  tree op_0 = TREE_OPERAND (rhs1, 0);
  tree op_0_type = TREE_TYPE (op_0);
  if (op_0 == var && is_interesting_type_align (op_0_type, type))
    {
      tree op_1 = TREE_OPERAND (rhs1, 1);

      tree good_type = TREE_TYPE (op_0);
      if (!backup_memref.get (rhs1))
	backup_memref.put (rhs1, TREE_OPERAND (rhs1, 1));

      TREE_OPERAND (rhs1, 1) = build_int_cst (good_type, tree_to_uhwi (op_1));

      tree deref_type = TREE_TYPE (good_type);
      if (!backup_vars.get (rhs1))
	backup_vars.put (rhs1, TREE_TYPE (rhs1));

      retype (rhs1, deref_type);

      retype_related (vars, lhs, deref_type);
    }

  if (dump_file)
    {
      print_gimple_stmt (dump_file, stmt, TDF_NONE);
      fprintf (dump_file, "Let's double check: lhs = ");
      print_generic_expr (dump_file, TREE_TYPE (lhs), TDF_NONE);
      fprintf (dump_file, "\nLet's double check: rhs = ");
      print_generic_expr (dump_file, TREE_TYPE (rhs1), TDF_NONE);
      fprintf (dump_file, "\nLet's double check: op1 = ");
      print_generic_expr (dump_file, TREE_TYPE (TREE_OPERAND (rhs1, 1)),
			  TDF_NONE);
      fprintf (dump_file, "\n");
    }
}

static void
analyze_assign_single (vec<tree> &vars, tree type, tree var, gassign *stmt)
{
  if (bail_out)
    return;

  const enum gimple_rhs_class code = gimple_assign_rhs_class (stmt);
  gcc_assert (GIMPLE_SINGLE_RHS == code);

  const enum tree_code t_code = gimple_assign_rhs_code (stmt);
  switch (t_code)
    {
    case MEM_REF:
      analyze_assign_mem_ref_rhs (vars, type, var, stmt);
      break;
    case SSA_NAME:
      analyze_assign_ssa_name (vars, type, var, stmt);
      break;
    default:
      {
	bail_out = true;
	if (dump_file)
	  {
	    fprintf (dump_file, "Not implementing analysis for complex gimple "
				"assignments at the moment....");
	    print_gimple_stmt (dump_file, stmt, TDF_NONE);
	  }
      }
    }
}

static void
analyze_assign_unary (vec<tree> &vars, tree type, tree var, gassign *stmt)
{
  if (bail_out)
    return;

  const enum gimple_rhs_class code = gimple_assign_rhs_class (stmt);
  gcc_assert (GIMPLE_UNARY_RHS == code);

  const enum tree_code t_code = gimple_assign_rhs_code (stmt);
  switch (t_code)
    {
    case NOP_EXPR:
      analyze_assign_nop_expr (vars, type, var, stmt);
      break;
    default:
      {
	bail_out = true;
	if (dump_file)
	  {
	    fprintf (dump_file, "Not implementing analysis for complex gimple "
				"assignments at the moment....");
	    print_gimple_stmt (dump_file, stmt, TDF_NONE);
	  }
      }
    }
}

static void
analyze_assign (vec<tree> &vars, tree type,
		tree var, gassign *stmt)
{
  if (bail_out)
    return;

  const enum gimple_rhs_class code = gimple_assign_rhs_class (stmt);
  switch (code)
    {
    case GIMPLE_UNARY_RHS:
      analyze_assign_unary (vars, type, var, stmt);
      break;
    case GIMPLE_SINGLE_RHS:
      analyze_assign_single (vars, type, var, stmt);
      break;
    case GIMPLE_BINARY_RHS:
      analyze_assign_binary (vars, type, var, stmt);
      break;
    default:
      {
	if (dump_file)
	  {
	    fprintf (dump_file, "Not implementing analysis for complex gimple "
				"assignments at the moment....");
	    print_gimple_stmt (dump_file, stmt, TDF_NONE);
	  }
	bail_out = true;
      }
    }
}

static void
analyze_phi (vec<tree> &vars, tree type, tree, gphi *stmt)
{
  // If one of the operands is of an interesting type, then the left hand side
  // can be of the interesting type. Not so sure yet about the rest of the phi
  // operands...
  tree lhs = gimple_phi_result (stmt);
  unsigned n = gimple_phi_num_args (stmt);
  bool interesting = false;
  tree interesting_type = NULL;
  for (unsigned i = 0; i < n; i++)
    {
      tree rhs_i = gimple_phi_arg_def (stmt, i);
      tree rhs_ti = TREE_TYPE (rhs_i);
      interesting = is_interesting_type_align (rhs_ti, type);
      interesting_type = interesting ? rhs_ti : interesting_type;
    }

  if (dump_file)
    fprintf (dump_file, "Retyping due to phi rule\n");
  retype_related (vars, lhs, interesting_type);
}

static void
analyze (vec<tree> &vars, tree type, tree var, gimple *stmt)
{
  if (bail_out)
    return;

  if (auto assign = dyn_cast<gassign *> (stmt))
    analyze_assign (vars, type, var, assign);
  else if (auto phi = dyn_cast<gphi *> (stmt))
    analyze_phi (vars, type, var, phi);
  else if (dump_file)
    {
      fprintf (dump_file, "Chose not to analyze...");
      print_gimple_stmt (dump_file, stmt, TDF_NONE);
    }
}

static void
analyze (vec<tree> &vars, tree type, tree var)
{
  if (bail_out)
    return;

  gimple *use_stmt = NULL;
  imm_use_iterator iterator;

  if (dump_file)
    {
      fprintf (dump_file, "Exploring the uses of...");
      print_generic_expr (dump_file, var, TDF_NONE);
      fprintf (dump_file, "\n");
    }

  FOR_EACH_IMM_USE_STMT (use_stmt, iterator, var)
    {
      if (dump_file)
	print_gimple_stmt (dump_file, use_stmt, TDF_NONE);

      analyze (vars, type, var, use_stmt);
      if (bail_out)
	return;
    }
}

static void
revert_type_changes (void);

static void
analyze (auto_vec<tree> &vars, tree type)
{
  bool fixed_point = true;

  do
    {
      auto_vec<tree> vars_copy;

      vars_copy.safe_splice (vars);

      for (auto var : vars)
	analyze (vars_copy, type, var);

      fixed_point = true;
      for (auto var : vars_copy)
	{
	  if (vars.contains (var))
	    continue;

	  vars.safe_push (var);
	  fixed_point = false;
	}
    } while (!fixed_point && !bail_out);

  if (bail_out)
    {
      if (dump_file)
	fprintf (dump_file, "BAIL OUT\n");
      revert_type_changes ();
    }

  backup_vars.empty ();
  backup_memref.empty ();
  bail_out = false;
}

// Revert types
static void
revert_type_changes (void)
{
  for (auto i = backup_vars.begin (), e = backup_vars.end (); i != e; ++i)
    {
      tree var = (*i).first;
      tree old_type = (*i).second;
      TREE_TYPE (var) = old_type;
    }

  for (auto i = backup_memref.begin (), e = backup_memref.end (); i != e; ++i)
    {
      tree root = (*i).first;
      tree old_op1 = (*i).second;
      TREE_OPERAND (root, 1) = old_op1;
    }
}

// We need to determine the variables that
// receive the first parameters (in other words, we are retyping the first
// parameter... and its forward slice Of course, it is very likely that the
// forward slice will be almost everything in the function because a function
// that does not depend on the incoming pointer is really rare...
static void
analyze (cgraph_node *c)
{
  cfun_context ctx (c);
  auto_vec<tree> param_to_look_for;
  tree parm_0 = DECL_ARGUMENTS (c->decl);
  gcc_assert (parm_0);

  tree parm_0_type = TREE_TYPE (parm_0);

  if (dump_file)
    dump_function_to_file (c->decl, dump_file, TDF_VOPS);

  unsigned i = 0;
  tree var = NULL_TREE;
  FOR_EACH_SSA_NAME (i, var, cfun)
    {
      backup_vars.put (var, TREE_TYPE (var));

      tree ssa_name = SSA_NAME_VAR (var);
      if (ssa_name != parm_0)
	continue;

      param_to_look_for.safe_push (var);
    }

  // We have not specialized this type, so there's no point
  if (parm_0_type == ptr_type_node)
    return;
  if (parm_0_type == long_integer_type_node)
    return;
  if (parm_0_type == char_type_node)
    return;

  analyze (param_to_look_for, parm_0_type);

  update_ssa (TODO_update_ssa);
}

static unsigned
ipa_retyper_auto (void)
{
  cgraph_node *cnode = NULL;
  auto_vec<cgraph_node *> candidates;
  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (cnode)
    {
      if (!has_incoming_alignment_data (cnode))
	continue;

      candidates.safe_push (cnode);
    }

  for (auto cnode : candidates)
    analyze (cnode);

  return 0;
}

static unsigned
ipa_retyper (void)
{
  return ipa_retyper_auto ();
}

namespace {
const pass_data pass_data_ipa_retyper = {
  SIMPLE_IPA_PASS,
  "retyper",
  OPTGROUP_NONE,
  TV_NONE,
  0,
  0,
  0,
  0,
  (TODO_verify_all),
};

class pass_ipa_retyper : public simple_ipa_opt_pass
{
public:
  pass_ipa_retyper (gcc::context *ctx)
    : simple_ipa_opt_pass (pass_data_ipa_retyper, ctx)
  {}

  virtual bool gate (function *)
  {
    return flag_ipa_retyper && lang_c_p ();
  }

  virtual unsigned execute (function *) { return ipa_retyper (); }
};
} /* namespace.  */

simple_ipa_opt_pass *
make_pass_ipa_retyper (gcc::context *ctx)
{
  return new pass_ipa_retyper (ctx);
}
