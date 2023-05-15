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
#include "gimple-iterator.h"
#include "value-range.h"
#include "ssa.h"
#include "tree-into-ssa.h"
#include "tree-cfg.h"
#include "ipa-lto-utils.h"
#include "ipa-utils.h"

static void
transform (hash_set<tree> &vars, int alignment)
{
  hash_map<gimple *, gimple *> to_replace;
  for (auto i = vars.begin (), e = vars.end (); i != e; ++i)
    {
      tree var_with_known_alignment = (*i);
      // If we find any uses of var in bit_and_expr 1, 2, 3 we know it is zero
      gimple *use_stmt;
      imm_use_iterator iterator;
      FOR_EACH_IMM_USE_STMT (use_stmt, iterator, var_with_known_alignment)
	{
	  gassign *assign = dyn_cast<gassign *> (use_stmt);
	  if (!assign)
	    continue;

	  const enum gimple_rhs_class code = gimple_assign_rhs_class (assign);
	  bool useful = GIMPLE_BINARY_RHS == code;
	  if (!useful)
	    continue;

	  enum tree_code expr_code = gimple_assign_rhs_code (assign);
	  useful = BIT_AND_EXPR == expr_code;
	  if (!useful)
	    continue;

	  tree rhs2 = gimple_assign_rhs2 (assign);
	  expr_code = TREE_CODE (rhs2);
	  useful = INTEGER_CST == expr_code;
	  if (!useful)
	    continue;

	  int mask = tree_to_uhwi (rhs2);
	  if (mask >= alignment)
	    continue;

	  // Here we know we can change the RHS to be a simple 0.
	  tree lhs = gimple_assign_lhs (assign);
	  gimple *new_assign
	    = gimple_build_assign (lhs, build_zero_cst (TREE_TYPE (lhs)));
	  to_replace.put (assign, new_assign);
	}
    }

  basic_block bb = NULL;
  FOR_EACH_BB_FN (bb, cfun)
    {
      // We know we are replacing real statements, not phis
      for (gimple_stmt_iterator gsi = gsi_start_bb (bb); !gsi_end_p (gsi);
	   gsi_next (&gsi))
	{
	  gimple *stmt = gsi_stmt (gsi);
	  if (!to_replace.get (stmt))
	    continue;

	  gimple *new_stmt = *to_replace.get (stmt);

	  gsi_replace (&gsi, new_stmt, true);
	}
    }
}

static void
transform (cgraph_node *c, int alignment)
{
  cfun_context ctx (c);
  tree parm = DECL_ARGUMENTS (c->decl);
  unsigned i = 0;
  tree var = NULL_TREE;
  hash_set<tree> vars;
  hash_map<gimple *, tree> defs;

  FOR_EACH_SSA_NAME (i, var, cfun)
    {
      tree ssa_name = SSA_NAME_VAR (var);
      if (ssa_name != parm)
	continue;

      if (SSA_NAME_IS_DEFAULT_DEF (var))
	continue;
      gimple *stmt = SSA_NAME_DEF_STMT (var);
      defs.put (stmt, var);
      vars.add (var);
    }

  FOR_EACH_SSA_NAME (i, var, cfun)
    {
      if (SSA_NAME_IS_DEFAULT_DEF (var))
	continue;
      gimple *stmt = SSA_NAME_DEF_STMT (var);
      gassign *_gassign = dyn_cast<gassign *> (stmt);
      if (!_gassign)
	continue;
      const enum gimple_rhs_class code = gimple_assign_rhs_class (_gassign);
      const bool valid_input = GIMPLE_UNARY_RHS == code;
      if (!valid_input)
	continue;

      tree rhs = gimple_assign_rhs1 (_gassign);
      if (!vars.contains (rhs))
	continue;

      defs.put (stmt, var);
      vars.add (var);
    }

  transform (vars, alignment);
  update_ssa (TODO_update_ssa);
}

static bool
is_leaf_recursive_function (cgraph_node *c)
{
  if (c->inlined_to)
    return false;
  if (!c->has_gimple_body_p ())
    return false;

  bool recursive_call2 = false;
  int non_recursive_callee = 0;
  for (cgraph_edge *e = c->callees; e; e = e->next_callee)
    {
      cgraph_node *callee = e->callee;
      recursive_call2 |= callee == c;
      if (callee == c)
	continue;

      non_recursive_callee++;
    }

  if (non_recursive_callee > 0)
    return false;

  bool recursive_call = false;
  int non_recursive_call_count = 0;
  for (cgraph_edge *e = c->callers; e; e = e->next_caller)
    {
      cgraph_node *caller = e->caller;
      recursive_call |= caller == c;
      if (caller == c)
	continue;

      non_recursive_call_count++;
    }

  return recursive_call && non_recursive_call_count == 1;
}

bool
has_incoming_alignment_data (cgraph_node *cnode)
{
  if (!is_leaf_recursive_function (cnode))
    return false;

  cgraph_node *non_recursive_caller = NULL;
  for (cgraph_edge *e = cnode->callers; e; e = e->next_caller)
    {
      non_recursive_caller
	= e->caller == cnode ? non_recursive_caller : e->caller;
    }

  return non_recursive_caller->alignment_data
	 && non_recursive_caller->alignment_data->get (cnode)
	 && *(non_recursive_caller->alignment_data->get (cnode)) > 1;
}

static int
get_incoming_alignment_data (cgraph_node *cnode)
{
  if (!has_incoming_alignment_data (cnode))
    return -1;

  if (!is_leaf_recursive_function (cnode))
    return -1;

  cgraph_node *non_recursive_caller = NULL;
  for (cgraph_edge *e = cnode->callers; e; e = e->next_caller)
    {
      non_recursive_caller
	= e->caller == cnode ? non_recursive_caller : e->caller;
    }

  if (!non_recursive_caller->alignment_data)
    return -1;

  if (!non_recursive_caller->alignment_data->get (cnode))
    return -1;

  int retval = *(non_recursive_caller->alignment_data->get (cnode));

  if (dump_file)
    fprintf (dump_file, "%s -> %s = %d\n", non_recursive_caller->name (),
	     cnode->name (), retval);

  return retval;
}

// The abstract value corresponds to the current multiple of the value
class abs_value_t
{
private:
  bool _top;
  long _data;
  bool _bottom;

public:
  static abs_value_t plus (abs_value_t left, abs_value_t right);
  static abs_value_t meet (abs_value_t left, abs_value_t right);
  static abs_value_t mult (abs_value_t left, abs_value_t right);
  static abs_value_t sub (abs_value_t left, abs_value_t right);
  static abs_value_t lshr (abs_value_t left, abs_value_t right);
  static abs_value_t unknown (abs_value_t left, abs_value_t right);
  void print (void);
  bool bottom (void);
  bool top (void);
  long get_value (void);
  void set_top (void);
  void set_bottom (void);
  void set_value (long);
  bool equal (const abs_value_t &other);
  abs_value_t () { set_bottom (); };
};

bool
abs_value_t::equal (const abs_value_t &other)
{
  return _top == other._top && _data == other._data
	 && _bottom == other._bottom;
}

void
abs_value_t::print (void)
{
  if (!dump_file)
    return;

  if (_top)
    fprintf (dump_file, "top");
  else if (_bottom)
    fprintf (dump_file, "bottom");
  else if (_data)
    fprintf (dump_file, "value = %ld", get_value ());
}

bool
abs_value_t::bottom (void)
{
  return _bottom;
}

bool
abs_value_t::top (void)
{
  return _top;
}

long
abs_value_t::get_value (void)
{
  return _data;
}

void
abs_value_t::set_top (void)
{
  _top = true;
  _data = -1;
  _bottom = false;
}

void
abs_value_t::set_bottom (void)
{
  _top = false;
  _data = -1;
  _bottom = true;
}

void
abs_value_t::set_value (long val)
{
  _top = false;
  _data = val > 0 ? val : -val;
  _bottom = false;
}

abs_value_t
abs_value_t::plus (abs_value_t left, abs_value_t right)
{
  if (left.bottom () || right.bottom ())
    return abs_value_t ();
  if (left.top () || right.top ())
    {
      abs_value_t res;
      res.set_top ();
      return res;
    }
  abs_value_t res;
  long val = MIN (left.get_value (), right.get_value ());
  res.set_value (val);
  return res;
}

abs_value_t
abs_value_t::sub (abs_value_t left, abs_value_t right)
{
  return abs_value_t::plus (left, right);
}

abs_value_t
abs_value_t::meet (abs_value_t left, abs_value_t right)
{
  if (left.bottom () && right.bottom ())
    return abs_value_t ();
  if (left.top () || right.top ())
    {
      abs_value_t res;
      res.set_top ();
      return res;
    }
  if (left.get_value () == right.get_value () || left.bottom ()
      || right.bottom ())
    {
      abs_value_t res = left.bottom () ? right : left;
      return res;
    }

  abs_value_t res;
  res.set_top ();
  return res;
}

abs_value_t
abs_value_t::mult (abs_value_t left, abs_value_t right)
{
  if (left.bottom () && right.bottom ())
    return abs_value_t ();
  if (left.top () && right.top ())
    {
      abs_value_t res;
      res.set_top ();
      return res;
    }
  abs_value_t res;
  res.set_value (left.get_value () * right.get_value ());
  return res;
}

abs_value_t
abs_value_t::lshr (abs_value_t left, abs_value_t right)
{
  if (left.bottom () || right.bottom ())
    return abs_value_t ();
  if (left.top () || right.top ())
    {
      abs_value_t res;
      res.set_top ();
      return res;
    }
  abs_value_t res;
  res.set_value (left.get_value () >> right.get_value ());
  return res;
}

static void
print_state (hash_map<tree, abs_value_t> &state)
{
  if (!dump_file)
    return;

  for (auto i = state.begin (), e = state.end (); i != e; ++i)
    {
      tree var = (*i).first;
      abs_value_t val = (*i).second;
      if (!dump_file)
	break;

      print_generic_expr (dump_file, var, TDF_NONE);
      fprintf (dump_file, "  ->  ");
      val.print ();
      fprintf (dump_file, "\n");
    }

  fprintf (dump_file, "\n");
}

static void
interpret_nop_expr (hash_map<tree, abs_value_t> &state, gassign *assign)
{
  // The semantics of this is just assign what is on rhs1 to lhs
  tree lhs_tree = gimple_assign_lhs (assign);
  tree rhs_tree = gimple_assign_rhs1 (assign);
  abs_value_t *abs_value_left = state.get (lhs_tree);
  abs_value_t *abs_value_right = state.get (rhs_tree);
  abs_value_t new_abs_value_left
    = abs_value_t::meet (*abs_value_left, *abs_value_right);
  state.put (lhs_tree, new_abs_value_left);
  abs_value_left = state.get (lhs_tree);
}

static void
interpret_mult_expr (hash_map<tree, abs_value_t> &state, gassign *assign)
{
  // The semantics of this is just assign what is on rhs1 to lhs
  tree lhs_tree = gimple_assign_lhs (assign);
  tree rhs1_tree = gimple_assign_rhs1 (assign);
  tree rhs2_tree = gimple_assign_rhs2 (assign);
  abs_value_t *abs_value_left = state.get (lhs_tree);
  abs_value_t *abs_value_rhs1 = state.get (rhs1_tree);
  abs_value_t *abs_value_rhs2 = state.get (rhs2_tree);
  abs_value_t new_abs_value_right
    = abs_value_t::mult (*abs_value_rhs1, *abs_value_rhs2);
  abs_value_t new_abs_value_left
    = abs_value_t::meet (*abs_value_left, new_abs_value_right);
  state.put (lhs_tree, new_abs_value_left);
  abs_value_left = state.get (lhs_tree);
}

static void
interpret_truncate_div_expr (hash_map<tree, abs_value_t> &state,
			     gassign *assign)
{
  // We don't really need to model these semantics.
  tree lhs_tree = gimple_assign_lhs (assign);
  state.get (lhs_tree)->set_top ();
}

static void
interpret_unknown_expr (hash_map<tree, abs_value_t> &state)
{
  for (auto i = state.begin (), e = state.end (); i != e; ++i)
    state.get ((*i).first)->set_top ();
}

static void
interpret_plus_expr (hash_map<tree, abs_value_t> &state, gassign *assign)
{
  // The semantics of this is just assign what is on rhs1 to lhs
  tree lhs_tree = gimple_assign_lhs (assign);
  tree rhs1_tree = gimple_assign_rhs1 (assign);
  tree rhs2_tree = gimple_assign_rhs2 (assign);
  abs_value_t *abs_value_left = state.get (lhs_tree);
  abs_value_t *abs_value_rhs1 = state.get (rhs1_tree);
  abs_value_t *abs_value_rhs2 = state.get (rhs2_tree);
  abs_value_t new_abs_value_right
    = abs_value_t::plus (*abs_value_rhs1, *abs_value_rhs2);
  abs_value_t new_abs_value_left
    = abs_value_t::meet (*abs_value_left, new_abs_value_right);
  state.put (lhs_tree, new_abs_value_left);
  abs_value_left = state.get (lhs_tree);
}

static void
interpret_gphi (hash_map<tree, abs_value_t> &state, gphi *phi)
{
  tree lhs = gimple_phi_result (phi);
  abs_value_t *lhs_val = state.get (lhs);

  for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
    {
      tree rhs_i = gimple_phi_arg_def (phi, i);
      lhs_val = state.get (lhs);
      abs_value_t *rhs_val = state.get (rhs_i);
      abs_value_t new_lhs = abs_value_t::meet (*lhs_val, *rhs_val);
      state.put (lhs, new_lhs);
    }
}

static void
interpret_gassign (hash_map<tree, abs_value_t> &state, gassign *assign)
{
  enum tree_code code = gimple_assign_rhs_code (assign);

  switch (code)
    {
    case NOP_EXPR:
    case INTEGER_CST:
    case NEGATE_EXPR:
      interpret_nop_expr (state, assign);
      break;
    case PLUS_EXPR:
    case POINTER_PLUS_EXPR:
    case POINTER_DIFF_EXPR:
      interpret_plus_expr (state, assign);
      break;
    case MULT_EXPR:
      interpret_mult_expr (state, assign);
      break;
    case TRUNC_DIV_EXPR:
      interpret_truncate_div_expr (state, assign);
      break;
    case SSA_NAME:
      {
	tree lhs = gimple_assign_lhs (assign);
	if (SSA_NAME == TREE_CODE (lhs))
	  interpret_nop_expr (state, assign);
	else
	  interpret_unknown_expr (state);
      }
      break;
    default:
      interpret_unknown_expr (state);
      break;
    }
}

static void
interpret_op (gimple *stmt, hash_map<tree, abs_value_t> &state)
{
  if (auto phi = dyn_cast<gphi *> (stmt))
    interpret_gphi (state, phi);
  else if (auto assign = dyn_cast<gassign *> (stmt))
    interpret_gassign (state, assign);
  else
    gcc_unreachable ();
}

static void
copy_state (hash_map<tree, abs_value_t> &src, hash_map<tree, abs_value_t> &dest)
{
  dest.empty ();
  for (auto i = src.begin (), e = src.end (); i != e; ++i)
    {
      tree key = (*i).first;
      abs_value_t val = (*i).second;
      dest.put (key, val);
    }
}

static bool
compare_state (hash_map<tree, abs_value_t> &src,
	       hash_map<tree, abs_value_t> &dest)
{
  if (dest.elements () != src.elements ())
    return false;
  for (auto i = src.begin (), e = src.end (); i != e; ++i)
    {
      tree key = (*i).first;
      abs_value_t val_exp = (*i).second;
      abs_value_t *val_obs = dest.get (key);
      if (!val_obs)
	return false;
      if (!val_obs->equal (val_exp))
	return false;
    }
  return true;
}

static int
analyze (cgraph_node *c, tree parm_0, tree incoming_arg,
	 hash_map<gimple *, tree> &defs)
{
  // map from variable -> static approximation
  hash_map<tree, abs_value_t> state;
  abs_value_t val;
  val.set_value (get_incoming_alignment_data (c));
  state.put (incoming_arg, val);

  unsigned i = 0;
  tree var = NULL;
  FOR_EACH_SSA_NAME (i, var, cfun)
    {
      tree ssa_name = SSA_NAME_VAR (var);
      if (ssa_name == parm_0)
	continue;

      if (!SSA_NAME_IS_DEFAULT_DEF (var))
	continue;
      if (var == incoming_arg)
	continue;

      tree another_argument = var;
      abs_value_t top;
      top.set_top ();
      state.put (another_argument, top);
    }

  for (auto i = defs.begin (), e = defs.end (); i != e; ++i)
    {
      gimple *stmt = (*i).first;
      tree var = (*i).second;
      abs_value_t bottom;
      state.put (var, bottom);
      // TODO: Also add the INTEGER_CSTs here so that
      // we don't need special handling...
      gassign *assign = dyn_cast<gassign *> (stmt);
      if (!assign)
	continue;

      enum tree_code code = gimple_assign_rhs_code (assign);
      bool is_plus_expr = PLUS_EXPR == code;
      bool is_mult_expr = MULT_EXPR == code;
      bool is_div_expr = TRUNC_DIV_EXPR == code;
      bool is_pplus_expr = POINTER_PLUS_EXPR == code;
      bool is_pdiff_expr = POINTER_DIFF_EXPR == code;
      bool is_integer_cst = INTEGER_CST == code;
      bool may_have_integer_cst = is_plus_expr || is_integer_cst
				  || is_pplus_expr || is_pdiff_expr
				  || is_mult_expr || is_div_expr;
      if (!may_have_integer_cst)
	continue;

      if (is_integer_cst)
	{
	  tree rhs1 = gimple_assign_rhs1 (assign);
	  int rhs1_int_cst = tree_to_uhwi (rhs1);
	  bottom.set_value (rhs1_int_cst);
	  state.put (rhs1, bottom);
	  continue;
	}

      tree rhs1 = gimple_assign_rhs1 (assign);
      tree rhs2 = gimple_assign_rhs2 (assign);

      if (TREE_CODE (rhs1) == INTEGER_CST)
	{
	  long int int_cst_1 = tree_to_uhwi (rhs1);
	  state.put (rhs1, bottom);
	  state.get (rhs1)->set_value (int_cst_1);
	}

      if (TREE_CODE (rhs2) == INTEGER_CST)
	{
	  long int int_cst_2 = tree_to_uhwi (rhs2);
	  state.put (rhs2, bottom);
	  state.get (rhs2)->set_value (int_cst_2);
	}
    }

  print_state (state);
  hash_map<tree, abs_value_t> prev_state;
  do
    {
      copy_state (state, prev_state);

      for (auto i = defs.begin (), e = defs.end (); i != e; ++i)
	{
	  gimple *stmt = (*i).first;
	  interpret_op (stmt, state);
	}
      print_state (state);
    }
  while (!compare_state (state, prev_state));

  // So,, we have reached fixed point
  // Now we need to look at what the argument to the callsite is
  basic_block bb = NULL;
  abs_value_t *static_approx = NULL;
  FOR_EACH_BB_FN (bb, cfun)
    {
      // We know we are replacing real statements, not phis
      for (gimple_stmt_iterator gsi = gsi_start_bb (bb); !gsi_end_p (gsi);
	   gsi_next (&gsi))
	{
	  gimple *stmt = gsi_stmt (gsi);
	  gcall *call = dyn_cast<gcall *> (stmt);
	  if (!call)
	    continue;

	  tree arg_0 = gimple_call_arg (call, 0);
	  static_approx = state.get (arg_0);
	}
    }

  if (!static_approx)
    return 0;
  if (static_approx->top ())
    return 0;
  if (static_approx->bottom ())
    return 0;

  long int value = static_approx->get_value ();
  if (value != get_incoming_alignment_data (c))
    return 0;

  return value;
}

static int
analyze (cgraph_node *c)
{
  cfun_context ctx (c);
  tree var = NULL_TREE;
  hash_set<tree> vars;
  hash_map<gimple *, tree> defs;
  tree incoming_arg = NULL;
  tree parm_0 = DECL_ARGUMENTS (c->decl);
  unsigned i = 0;

  // TODO: We need the definitions of the parm_0 and
  // the definitions of the operands that define parm_0
  // recursively...
  gcc_assert (parm_0);

  FOR_EACH_SSA_NAME (i, var, cfun)
    {
      tree ssa_name = SSA_NAME_VAR (var);
      if (ssa_name != parm_0)
	continue;

      if (SSA_NAME_IS_DEFAULT_DEF (var))
	{
	  incoming_arg = var;
	  continue;
	}
      gimple *stmt = SSA_NAME_DEF_STMT (var);
      defs.put (stmt, var);
      vars.add (var);
    }

  auto_vec<tree> variables;

  for (auto i = vars.begin (), e = vars.end (); i != e; ++i)
    variables.safe_push (*i);

  while (!variables.is_empty ())
    {
      tree a_var = variables.pop ();

      if (SSA_NAME != TREE_CODE (a_var))
	continue;
      if (SSA_NAME_IS_DEFAULT_DEF (a_var))
	continue;

      gimple *stmt = SSA_NAME_DEF_STMT (a_var);
      defs.put (stmt, a_var);

      if (auto assign = dyn_cast<gassign *> (stmt))
	{
	  const enum gimple_rhs_class rhs_class
	    = gimple_assign_rhs_class (assign);
	  tree rhs1 = GIMPLE_TERNARY_RHS == rhs_class
			? NULL
			: gimple_assign_rhs1 (assign);
	  tree rhs2 = GIMPLE_BINARY_RHS == rhs_class
			? gimple_assign_rhs2 (assign)
			: NULL;
	  tree rhs3 = GIMPLE_TERNARY_RHS == rhs_class
			? gimple_assign_rhs3 (assign)
			: NULL;

	  if (rhs1 && !vars.contains (rhs1))
	    {
	      vars.add (rhs1);
	      variables.safe_push (rhs1);
	    }

	  if (rhs2 && !vars.contains (rhs2))
	    {
	      vars.add (rhs2);
	      variables.safe_push (rhs2);
	    }

	  if (rhs3 && !vars.contains (rhs3))
	    {
	      vars.add (rhs3);
	      variables.safe_push (rhs3);
	    }
	}
      else if (auto phi = dyn_cast<gphi *> (stmt))
	{
	  for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
	    {
	      tree arg_i = gimple_phi_arg_def (phi, i);
	      if (vars.contains (arg_i))
		continue;

	      vars.add (arg_i);
	      variables.safe_push (arg_i);
	    }
	}
    }

  return analyze (c, parm_0, incoming_arg, defs);
}

static unsigned
ipa_alignment_analysis_and_transformation (void)
{
  cgraph_node *cnode = NULL;
  auto_vec<cgraph_node *> to_analyze;

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (cnode)
    {
      if (is_leaf_recursive_function (cnode)
	  && has_incoming_alignment_data (cnode))
	to_analyze.safe_push (cnode);
    }

  // TODO: Assume that the analysis results that every function in functions
  // is actually always aligned to 8 bytes
  for (auto cnode : to_analyze)
    {
      int alignment = analyze (cnode);

      if (alignment <= 0)
	continue;

      if (dump_file)
	dump_function_to_file (cnode->decl, dump_file, TDF_NONE);

      transform (cnode, alignment);

      if (dump_file)
	dump_function_to_file (cnode->decl, dump_file, TDF_NONE);
    }

  return 0;
}

namespace {
const pass_data pass_data_ipa_alignment_analysis_and_transformation = {
  SIMPLE_IPA_PASS,
  "alignment-analysis-and-transformation",
  OPTGROUP_NONE,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0,
  0,
  (TODO_update_ssa),
  (TODO_verify_all),
};

class pass_ipa_alignment_analysis_and_transformation
  : public simple_ipa_opt_pass
{
public:
  pass_ipa_alignment_analysis_and_transformation (gcc::context *ctx)
    : simple_ipa_opt_pass (pass_data_ipa_alignment_analysis_and_transformation,
			   ctx)
  {}

  virtual bool gate (function *)
  {
    return flag_ipa_alignment_analysis_and_transformation && lang_c_p ();
  }

  virtual unsigned execute (function *)
  {
    return ipa_alignment_analysis_and_transformation ();
  }
};
} /* namespace.  */

simple_ipa_opt_pass *
make_pass_ipa_alignment_analysis_and_transformation (gcc::context *ctx)
{
  return new pass_ipa_alignment_analysis_and_transformation (ctx);
}
