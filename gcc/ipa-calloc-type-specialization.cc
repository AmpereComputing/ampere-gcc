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
#include "stor-layout.h"
#include "gimple-iterator.h"
#include "ssa.h"
#include "gimple-pretty-print.h"
#include "ipa-type-escape-analysis.h"
#include "ipa-utils.h"

class gimple_caster_statement : public gimple_caster
{
public:
  gimple_caster_statement (tpartitions2_t &types,
			   hash_map<tree, bool> *whitelisted2)
    : gimple_caster (types, whitelisted2)
  {}

  /* If assignment is casted, mark them as escaping.
   * Assignments from calloc and other known functions
   * are allowed.
   */
  tree walk_statement (tree var, gassign *s);

  /* If it is a simple assignment of the type
   * VAR = VAR or SSA_NAME = SSA_NAME
   * or something similar, then this is a simple case
   */
  bool is_decl_decl (gassign *s);

  /* If it is a simple assignment of the type
   * VAR_DECL || SSA_NAME = MEM_REF
   */
  bool is_mem_ref_right (gassign *s);
  bool is_mem_ref_left (gassign *s);

  /* Make sure that var is the operand 0 of rhs MEM_REF in s */
  bool is_var_op0_memref (gassign *s, tree var);

  bool memref_op1_lhs_match (gassign *s);
};

bool
gimple_caster_statement::is_decl_decl (gassign *s)
{
  tree lhs = gimple_assign_lhs (s);
  tree rhs = gimple_assign_rhs1 (s);
  const bool is_lhs_var_decl = VAR_DECL == TREE_CODE (lhs);
  const bool is_lhs_ssa_name = SSA_NAME == TREE_CODE (lhs);
  const bool is_lhs_simple = is_lhs_var_decl || is_lhs_ssa_name;
  const bool is_rhs_var_decl = VAR_DECL == TREE_CODE (rhs);
  const bool is_rhs_ssa_name = SSA_NAME == TREE_CODE (rhs);
  const bool is_rhs_simple = is_rhs_var_decl || is_rhs_ssa_name;
  const bool is_simple = is_lhs_simple && is_rhs_simple;
  return is_simple;
}

bool
gimple_caster_statement::is_mem_ref_right (gassign *s)
{
  tree lhs = gimple_assign_lhs (s);
  tree rhs = gimple_assign_rhs1 (s);
  const bool is_lhs_var_decl = VAR_DECL == TREE_CODE (lhs);
  const bool is_lhs_ssa_name = SSA_NAME == TREE_CODE (lhs);
  const bool is_lhs_simple = is_lhs_var_decl || is_lhs_ssa_name;
  const bool is_rhs_mem_ref = MEM_REF == TREE_CODE (rhs);
  const bool is_simple = is_lhs_simple && is_rhs_mem_ref;
  return is_simple;
}

bool
gimple_caster_statement::is_var_op0_memref (gassign *s, tree var)
{
  tree rhs = gimple_assign_rhs1 (s);
  const bool is_rhs_mem_ref = MEM_REF == TREE_CODE (rhs);
  if (!is_rhs_mem_ref)
    return false;

  tree op_0 = TREE_OPERAND (rhs, 0);
  const bool are_equal = var == op_0;
  return are_equal;
}

bool
gimple_caster_statement::memref_op1_lhs_match (gassign *s)
{
  tree lhs = gimple_assign_lhs (s);
  tree rhs = gimple_assign_rhs1 (s);
  return TREE_TYPE (lhs) == TREE_TYPE (rhs);
}

bool
gimple_caster_statement::is_mem_ref_left (gassign *s)
{
  tree lhs = gimple_assign_lhs (s);
  tree rhs = gimple_assign_rhs1 (s);
  const bool is_lhs_mem_ref = MEM_REF == TREE_CODE (lhs);
  const bool is_rhs_var_decl = VAR_DECL == TREE_CODE (rhs);
  const bool is_rhs_ssa_name = SSA_NAME == TREE_CODE (rhs);
  const bool is_rhs_simple = is_rhs_var_decl || is_rhs_ssa_name;
  const bool is_simple = is_lhs_mem_ref && is_rhs_simple;
  return is_simple;
}

tree
gimple_caster_statement::walk_statement (tree var, gassign *s)
{
  const enum gimple_rhs_class code = gimple_assign_rhs_class (s);
  const bool is_single = GIMPLE_SINGLE_RHS == code || GIMPLE_UNARY_RHS == code;
  if (is_single)
    {
      tree lhs = gimple_assign_lhs (s);

      if (is_decl_decl (s))
	return TREE_TYPE (lhs);

      if (is_mem_ref_right (s))
	{
	  if (is_var_op0_memref (s, var) && memref_op1_lhs_match (s))
	    {
	      tree rhs = gimple_assign_rhs1 (s);
	      tree op1 = TREE_OPERAND (rhs, 1);
	      return TREE_TYPE (op1);
	    }
	}

      if (is_mem_ref_left (s))
	return TREE_TYPE (lhs);
    }

  const bool is_pointer_plus = POINTER_PLUS_EXPR == gimple_expr_code (s);
  if (is_pointer_plus)
    {
      tree rhs1 = gimple_assign_rhs1 (s);
      if (rhs1 == var)
	{
	  tree rhs2 = gimple_assign_rhs2 (s);
	  return TREE_TYPE (rhs2);
	}
    }

  return NULL;
}

static tree
find_out_how_variable_is_casted_in_statement (tree var, gimple *s)
{
  if (dump_file)
    {
      fprintf (dump_file, "Looking into variable...");
      print_generic_expr (dump_file, var, TDF_NONE);
      fprintf (dump_file, "\nLooking into statement...");
      print_gimple_stmt (dump_file, s, TDF_NONE);
      fprintf (dump_file, "\n");
    }

  // White list nothing...
  hash_map<tree, bool> *whitelisted = new hash_map<tree, bool>;
  tpartitions2_t types;
  gimple_caster_statement caster (types, whitelisted);
  gassign *_g = dyn_cast<gassign *> (s);
  gcc_assert (_g);

  tree casted_into = caster.walk_statement (var, _g);
  if (casted_into && dump_file)
    {
      fprintf (dump_file, "Casted into...");
      print_generic_expr (dump_file, TYPE_MAIN_VARIANT (casted_into), TDF_NONE);
      fprintf (dump_file, "\n");
    }

  return casted_into;
}

static unsigned
ipa_calloc_type_specialization (void)
{
  cgraph_node *cnode = NULL;

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (cnode)
    {
      cfun_context ctx (cnode);
      basic_block bb = NULL;

      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (auto gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	    {
	      gimple *stmt = gsi_stmt (gsi);
	      gcall *call = dyn_cast<gcall *> (stmt);
	      if (!call)
		continue;

	      tree callee_fndecl = gimple_call_fndecl (call);
	      if (!callee_fndecl)
		continue;
	      if (!fndecl_built_in_p (callee_fndecl, BUILT_IN_NORMAL))
		continue;
	      if (BUILT_IN_CALLOC != DECL_FUNCTION_CODE (callee_fndecl))
		continue;

	      tree lhs = gimple_call_lhs (call);
	      tree lhs_type = TREE_TYPE (lhs);
	      gimple *use_stmt;
	      imm_use_iterator iterator;
	      tree type = NULL;
	      bool useful = true;

	      if (dump_file)
		{
		  print_generic_expr (dump_file, TYPE_MAIN_VARIANT (lhs_type),
				      TDF_NONE);
		  fprintf (dump_file, "\n");
		}

	      FOR_EACH_IMM_USE_STMT (use_stmt, iterator, lhs)
		{
		  // Assign is where cast happens.
		  gassign *assign = dyn_cast<gassign *> (use_stmt);
		  if (!assign)
		    continue;

		  const enum gimple_rhs_class code
		    = gimple_assign_rhs_class (assign);
		  useful
		    &= GIMPLE_SINGLE_RHS != code || GIMPLE_BINARY_RHS != code;
		  if (!useful)
		    continue;

		  // We only care about void*
		  if (ptr_type_node != TREE_TYPE (lhs))
		    continue;

		  tree casted_into
		    = find_out_how_variable_is_casted_in_statement (lhs,
								    use_stmt);
		  if (casted_into && INTEGER_TYPE == TREE_CODE (casted_into))
		    continue;

		  if (!type)
		    {
		      type = casted_into;
		      continue;
		    }

		  useful &= (bool) casted_into;
		  if (!useful)
		    continue;

		  type_incomplete_equality equality;
		  useful &= equality.equal (casted_into, type);
		  if (dump_file)
		    fprintf (dump_file, "Still equal = %s\n",
			     useful ? "T" : "F");
		}

	      if (useful && type)
		{
		  if (dump_file)
		    fprintf (dump_file, "Substituting... ");
		  if (dump_file)
		    print_generic_expr (dump_file, TREE_TYPE (lhs), TDF_NONE);
		  if (dump_file)
		    fprintf (dump_file, " for ");
		  if (dump_file)
		    print_generic_expr (dump_file, type, TDF_NONE);
		  if (dump_file)
		    fprintf (dump_file, "\n");
		  TREE_TYPE (lhs) = type;
		  if (DECL_P (lhs))
		    relayout_decl (lhs);
		}
	    }
	}
    }

  return 0;
}

namespace {
const pass_data pass_data_ipa_calloc_type_specialization = {
  SIMPLE_IPA_PASS,
  "calloc-type-specialization",
  OPTGROUP_NONE,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0,
  0,
  0,
  0,
};

class pass_ipa_calloc_type_specialization : public simple_ipa_opt_pass
{
public:
  pass_ipa_calloc_type_specialization (gcc::context *ctx)
    : simple_ipa_opt_pass (pass_data_ipa_calloc_type_specialization, ctx)
  {}

  virtual bool gate (function *)
  {
    return flag_ipa_calloc_type_specialization;
  }

  virtual unsigned execute (function *)
  {
    return ipa_calloc_type_specialization ();
  }
};
} /* namespace.  */

simple_ipa_opt_pass *
make_pass_ipa_calloc_type_specialization (gcc::context *ctx)
{
  return new pass_ipa_calloc_type_specialization (ctx);
}
