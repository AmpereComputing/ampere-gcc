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
#include "gimple-expr.h"
#include "predict.h"
#include "alloc-pool.h"
#include "tree-pass.h"
#include "cgraph.h"
#include "diagnostic.h"
#include "fold-const.h"
#include "gimple-fold.h"
#include "symbol-summary.h"
#include "tree-vrp.h"
#include "ipa-prop.h"
#include "tree-pretty-print.h"
#include "tree-inline.h"
#include "ipa-fnsummary.h"
#include "ipa-utils.h"
#include "tree-ssa-ccp.h"
#include "stringpool.h"
#include "attribs.h"
#include "basic-block.h"
#include "function.h"
#include "gimple.h"
#include "stor-layout.h"
#include "cfg.h"
#include "gimple-iterator.h"
#include "gimplify.h"
#include "value-range.h"
#include "tree-ssanames.h"
#include "ssa.h"
#include "tree-into-ssa.h"
#include "gimple-ssa.h"
#include "tree.h"
#include "gimple-expr.h"
#include "predict.h"
#include "alloc-pool.h"
#include "tree-pass.h"
#include "cgraph.h"
#include "diagnostic.h"
#include "fold-const.h"
#include "gimple-fold.h"
#include "symbol-summary.h"
#include "tree-vrp.h"
#include "ipa-prop.h"
#include "tree-pretty-print.h"
#include "tree-inline.h"
#include "ipa-fnsummary.h"
#include "ipa-utils.h"
#include "tree-ssa-ccp.h"
#include "stringpool.h"
#include "attribs.h"
#include "tree-ssa-alias.h"
#include "tree-ssanames.h"
#include "gimple.h"
#include "cfg.h"
#include "gimple-iterator.h"
#include "gimple-ssa.h"
#include "gimple-pretty-print.h"
#include "tree-cfg.h"

static tree
get_replacement_int_cst_sizeof (tree t, tree old_type,
				hash_map<tree, tree> &type_map)
{
  const enum tree_code code = TREE_CODE (t);
  gcc_assert (INTEGER_CST == code);

  tree *new_type_ptr = type_map.get (old_type);
  if (!new_type_ptr)
    return NULL_TREE;

  tree new_type = *new_type_ptr;
  tree new_size_unit = TYPE_SIZE_UNIT (new_type);
  tree old_size_unit = TYPE_SIZE_UNIT (old_type);
  int new_size_int = tree_to_shwi (new_size_unit);
  int old_size_int = tree_to_shwi (old_size_unit);
  int old_int_cst = tree_to_shwi (t);
  gcc_assert ((old_int_cst % old_size_int) == 0);

  int new_constant = (old_int_cst / old_size_int) * new_size_int;
  tree new_int_cst_tree = build_int_cst (TREE_TYPE (t), new_constant);
  if (dump_file)
    fprintf (dump_file, "change sizeof constant from %d to %d\n", old_int_cst,
	     new_constant);
  return new_int_cst_tree;
}

static void
replace_sizeof_cst_assign (gcall *call, gassign *stmt,
			   hash_map<tree, tree> &type_map);

static void
replace_arg_definitions (gcall *call, tree e, hash_map<tree, tree> &type_map)
{
  const enum tree_code code = TREE_CODE (e);
  if (SSA_NAME != code)
    return;

  gimple *def = SSA_NAME_DEF_STMT (e);
  gassign *assign = dyn_cast<gassign *> (def);
  if (!assign)
    return;

  replace_sizeof_cst_assign (call, assign, type_map);
}

static bool
is_alloc_fn (tree fndecl)
{
  if (!fndecl)
    return false;
  if (!fndecl_built_in_p (fndecl))
    return false;
  switch (DECL_FUNCTION_CODE (fndecl))
    {
    // TODO: Are there others?
    case BUILT_IN_CALLOC:
    case BUILT_IN_MALLOC:
    case BUILT_IN_REALLOC:
    case BUILT_IN_MEMSET:
      break;
    default:
      return false;
      break;
    }
  return true;
}

int
which_argument_to_look_at (tree fndecl)
{
  if (!fndecl)
    return -1;
  if (!fndecl_built_in_p (fndecl))
    return -1;
  switch (DECL_FUNCTION_CODE (fndecl))
    {
    // TODO: Are there others?
    case BUILT_IN_MEMSET:
      return 2;
      break;
    case BUILT_IN_CALLOC:
    case BUILT_IN_REALLOC:
      return 1;
      break;
    case BUILT_IN_MALLOC:
      return 0;
      break;
    default:
      return -1;
      break;
    }
  return -1;
}

static void
replace_sizeof_cst_call (gcall *call, hash_map<tree, tree> &type_map)
{
  // TODO: I can possibly make this function assert in certain conditions.
  // Like, there won't be a TYPE_SIZEOF_TYPE field for functions other than
  // the memory management functions. Also, we should match old type to new
  // type.
  gcc_assert (call);
  tree fndecl = gimple_call_fndecl (call);
  if (!fndecl)
    return;
  if (!is_alloc_fn (fndecl))
    return;

  int arg_to_look_at = which_argument_to_look_at (fndecl);
  if (arg_to_look_at == -1)
    return;

  // We need to know which call we are dealing with...

  tree arg_i = gimple_call_arg (call, arg_to_look_at);
  gcc_assert (arg_i);
  if (SSA_NAME == TREE_CODE (arg_i))
    {
      replace_arg_definitions (call, arg_i, type_map);
    }
  else if (INTEGER_CST == TREE_CODE (arg_i))
    {
      tree type_sizeof_type = gimple_call_get_type_sizeof_type (call);
      tree new_tree
	= get_replacement_int_cst_sizeof (arg_i, type_sizeof_type, type_map);
      if (new_tree)
	{
	  gimple_call_set_arg (call, arg_to_look_at, new_tree);
	  tree new_type = *type_map.get (type_sizeof_type);
	  gimple_call_set_type_sizeof_type (call, new_type);
	}
    }
}

static void
replace_sizeof_cst_assign (gcall *call, gassign *stmt,
			   hash_map<tree, tree> &type_map)
{
  gcc_assert (stmt);
  const enum gimple_rhs_class rhs_class = gimple_assign_rhs_class (stmt);
  tree type_sizeof_type = gimple_call_get_type_sizeof_type (call);
  switch (rhs_class)
    {
    case GIMPLE_TERNARY_RHS:
      break;
    /* fall-through */
    case GIMPLE_BINARY_RHS:
      {
	tree rhs2 = gimple_assign_rhs2 (stmt);
	gcc_assert (rhs2);
	tree new_tree
	  = get_replacement_int_cst_sizeof (rhs2, type_sizeof_type, type_map);
	if (new_tree)
	  {
	    gimple_assign_set_rhs2 (stmt, new_tree);
	    tree new_type = *type_map.get (type_sizeof_type);
	    gimple_call_set_type_sizeof_type (call, new_type);
	  }
      }
    /* fall-through */
    case GIMPLE_UNARY_RHS:
    case GIMPLE_SINGLE_RHS:
      break;
    default:
      gcc_unreachable ();
      break;
    }
}

/*
static void
replace_sizeof_cst_call_definitions (gcall *call, hash_map <tree, tree>
&type_map)
{
  gcc_assert (call);

  unsigned n = gimple_call_num_args (call);
  for (unsigned i = 0; i < n; i++)
  {
    tree arg_i = gimple_call_arg (call, i);
    gcc_assert (arg_i);

  }
}
*/

void
replace_sizeof_cst (gimple *stmt, hash_map<tree, tree> &type_map)
{
  gcc_assert (stmt);
  gcall *call = dyn_cast<gcall *> (stmt);

  // At the moment, if there is any INTEGER_CST in STMT
  // it is guaranteed to be either a gcall* or a gassign*
  // So, let's return early if that's not the case.

  bool possible_sizeof = call;
  if (!possible_sizeof)
    return;

  tree t = gimple_call_get_type_sizeof_type (call);
  if (!t)
    return;

  if (!type_map.get (t))
    return;

  replace_sizeof_cst_call (call, type_map);
}
