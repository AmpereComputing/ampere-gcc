/* Struct Dynamic Caching Optimization.
   Copyright (C) 2020-2021 Free Software Foundation, Inc.

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
#include "tree.h"
#include "tree-pass.h"
#include "cgraph.h"
#include "diagnostic-core.h"
#include "function.h"
#include "basic-block.h"
#include "gimple.h"
#include "gimplify.h"
#include "gimple-pretty-print.h"
#include "gimple-iterator.h"
#include "cfg.h"
#include "ssa.h"
#include "tree-dfa.h"
#include "fold-const.h"
#include "tree-inline.h"
#include "stor-layout.h"
#include "tree-into-ssa.h"
#include "tree-cfg.h"
#include "ipa-utils.h"
#include "tree-eh.h"
#include "bitmap.h"
#include "cfgloop.h"
#include "langhooks.h"
#include "gimple-range.h"
#include "gimplify-me.h"
#include "cfghooks.h"
#include "attribs.h"
#include "tree-ssa-loop-niter.h"
#include "cfgexpand.h"
#include "tree-ssa-live.h" /* For remove_unused_locals.  */
#include "ipa-type-escape-analysis.h"

namespace {

#define VOID_POINTER_P(type) \
  (POINTER_TYPE_P (type) && VOID_TYPE_P (TREE_TYPE (type)))

#define TEST(cond) \
  if (!(cond)) \
    return false;

#define TEST_RET_VOID(cond) \
  if (!(cond)) \
    return;

#define TEST_WITH_MSG(cond, message) \
  if (!(cond)) \
    { \
      if (dump_file && (dump_flags & TDF_DETAILS)) \
	fprintf (dump_file, "[FAIL] %s\n", (message)); \
      return false; \
    }

#define SET_ERR_RETURN_NULL(err) \
  { \
    if (err) \
      *err = true; \
    return NULL_TREE; \
  }

#define STRING_STARTS_WITH(s, suffix) \
  (strncmp (s, suffix, sizeof (suffix) - 1) == 0)

/* Flags for operand_equal_p to treat decls with the same name equal.  */

#define COMPARE_DECL_FLAGS (OEP_DECL_NAME | OEP_LEXICOGRAPHIC)

#define APPEND_GASSIGN_1(gsi, lhs, op, rhs) \
  gsi_insert_after (&gsi, gimple_build_assign (lhs, op, rhs), \
		    GSI_CONTINUE_LINKING)

#define APPEND_GASSIGN_2(gsi, lhs, op, rhs1, rhs2) \
  gsi_insert_after (&gsi, gimple_build_assign (lhs, op, rhs1, rhs2), \
		    GSI_CONTINUE_LINKING)

/* Return true iff TYPE is stdarg va_list type.  */

static inline bool
is_va_list_type (tree type)
{
  return TYPE_MAIN_VARIANT (type) == TYPE_MAIN_VARIANT (va_list_type_node);
}

/* Called by walk_tree to check if ssa_name DATA exists in an expression.  */

static tree
check_for_ssa (tree *opnd_ptr, int *walk_subtrees ATTRIBUTE_UNUSED, void *data)
{
  tree ssa = (tree) data;
  if (*opnd_ptr == ssa)
    return ssa;

  return NULL_TREE;
}

/* Return the bit width of the FIELD. */

static HOST_WIDE_INT
get_bitsize (tree field)
{
  HOST_WIDE_INT bitsize = tree_to_uhwi (TYPE_SIZE (TREE_TYPE (field)));
  if (DECL_BIT_FIELD (field))
    bitsize = tree_to_uhwi (DECL_SIZE (field));

  return bitsize;
}

/* Return RHS if STMT is a copy stmt, and RHS is a SSA_NAME. */

static tree
get_ssa_copy (const gimple *stmt)
{
  if (!is_gimple_assign (stmt))
    return NULL_TREE;

  tree rhs = gimple_assign_rhs1 (stmt);

  if (gimple_assign_single_p (stmt)
      || CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt)))
    {
      if (TREE_CODE (rhs) == SSA_NAME)
	return rhs;
    }

  return NULL_TREE;
}

static const char *
get_type_name (tree type)
{
  const char *tname = NULL;

  if (type == NULL)
    {
      return NULL;
    }

  if (TYPE_NAME (type) != NULL)
    {
      if (TREE_CODE (TYPE_NAME (type)) == IDENTIFIER_NODE)
	{
	  tname = IDENTIFIER_POINTER (TYPE_NAME (type));
	}
      else if (DECL_NAME (TYPE_NAME (type)) != NULL)
	{
	  tname = IDENTIFIER_POINTER (DECL_NAME (TYPE_NAME (type)));
	}
    }
  return tname;
}

/* Search DEF in OLD_DEFS, and the counterpart in NEW_DEFS. */

static tree
tree_map_get (auto_vec<tree> &old_defs, auto_vec<tree> &new_defs, tree def)
{
  unsigned i;
  tree old_def;

  gcc_checking_assert (old_defs.length () == new_defs.length ());
  FOR_EACH_VEC_ELT (old_defs, i, old_def)
    {
      if (operand_equal_p (def, old_def))
	return new_defs[i];
    }
  return NULL_TREE;
}

/* Build a binary operation and gimplify it.  Emit code before GSI.
   Return the gimple_val holding the result.  */

tree
gimplify_build2 (gimple_stmt_iterator *gsi, enum tree_code code, tree type,
		 tree a, tree b)
{
  tree ret;

  ret = fold_build2_loc (gimple_location (gsi_stmt (*gsi)), code, type, a, b);
  return force_gimple_operand_gsi (gsi, ret, true, NULL, true, GSI_SAME_STMT);
}

/* Build a unary operation and gimplify it.  Emit code before GSI.
   Return the gimple_val holding the result.  */

tree
gimplify_build1 (gimple_stmt_iterator *gsi, enum tree_code code, tree type,
		 tree a)
{
  tree ret;
  gimple *g = gsi_stmt (*gsi);
  location_t loc = gimple_location (g);

  ret = fold_build1_loc (loc, code, type, a);
  return force_gimple_operand_gsi (gsi, ret, true, NULL, true, GSI_SAME_STMT);
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
  enum tree_code code;

  if (DECL_BIT_FIELD (field_decl))
    code = BIT_FIELD_REF;
  else
    code = COMPONENT_REF;

  return build3 (code, TREE_TYPE (field_decl), build_simple_mem_ref (addr),
		 field_decl, NULL_TREE);
}

/* STMT1 is before STMT2. Create new vdef if necessary. */

static void
update_stmt_vdef (gimple *stmt1, gimple *stmt2)
{
  if (gimple_vdef (stmt2) == NULL_TREE)
    return;

  tree vuse = gimple_vuse (stmt2);
  tree new_vdef = copy_ssa_name (vuse, stmt1);
  gimple_set_vuse (stmt1, vuse);
  gimple_set_vdef (stmt1, new_vdef);
  gimple_set_vuse (stmt2, new_vdef);
  update_stmt (stmt1);
  update_stmt (stmt2);
}

/* This is the counterpart of update_stmt for PHI. */

static gphi *
update_phi (gphi *phi)
{
  gphi *newphi = create_phi_node (gimple_phi_result (phi), gimple_bb (phi));

  for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
    {
      phi_arg_d rhs = *gimple_phi_arg (phi, i);
      tree arg = gimple_phi_arg_def (phi, i);
      SET_PHI_ARG_DEF (newphi, i, arg);
      gimple_phi_arg_set_location (newphi, i, rhs.locus);
    }
  gphi_iterator gpi = gsi_for_phi (phi);
  remove_phi_node (&gpi, false);
  return newphi;
}

/* Return the inner most type for arrays and pointers of TYPE.  */

static tree
inner_type (tree type)
{
  while (POINTER_TYPE_P (type) || TREE_CODE (type) == ARRAY_TYPE)
    type = TREE_TYPE (type);
  return type;
}

/* Returns iterator at the end of the list of phi nodes of BB.  */

static gphi_iterator
gsi_end_phis (basic_block bb)
{
  gimple_seq *pseq = phi_nodes_ptr (bb);

  /* Adapted from gsi_start_1. */
  gphi_iterator i;

  i.ptr = gimple_seq_last (*pseq);
  i.seq = pseq;
  i.bb = i.ptr ? gimple_bb (i.ptr) : NULL;

  return i;
}

/*  Return true if TYPE is a type which struct dco should handled.  */

static bool
handled_type (tree type)
{
  type = inner_type (type);
  if (TREE_CODE (type) == RECORD_TYPE)
    return !is_va_list_type (type);
  return false;
}

/* Check whether in C language or LTO with only C language.  */
static bool
lang_c_p (void)
{
  const char *language_string = lang_hooks.name;

  if (!language_string)
    {
      return false;
    }

  if (lang_GNU_C ())
    {
      return true;
    }
  else if (strcmp (language_string, "GNU GIMPLE") == 0) // for LTO check
    {
      unsigned i = 0;
      tree t = NULL_TREE;

      FOR_EACH_VEC_SAFE_ELT (all_translation_units, i, t)
	{
	  language_string = TRANSLATION_UNIT_LANGUAGE (t);
	  if (language_string == NULL || strncmp (language_string, "GNU C", 5)
	      || (language_string[5] != '\0'
		  && !(ISDIGIT (language_string[5]))))
	    {
	      return false;
	    }
	}
      return true;
    }
  return false;
}

/* Get the number of pointer layers.  */

static int
get_ptr_layers (tree expr)
{
  int layers = 0;
  while (POINTER_TYPE_P (expr) || TREE_CODE (expr) == ARRAY_TYPE)
    {
      layers++;
      expr = TREE_TYPE (expr);
    }
  return layers;
}

/*  Return true if the ssa_name comes from the void* parameter.  */

static bool
is_from_void_ptr_parm (tree ssa_name)
{
  gcc_assert (TREE_CODE (ssa_name) == SSA_NAME);
  tree var = SSA_NAME_VAR (ssa_name);
  return (var && TREE_CODE (var) == PARM_DECL
	  && VOID_POINTER_P (TREE_TYPE (ssa_name)));
}

/* Return true if STMT is a copy to convert to type like below,
   _1 = (type) _2  */

static bool
is_copy (const gimple *stmt, tree type)
{
  if (!is_gimple_assign (stmt))
    return NULL_TREE;

  tree rhs = gimple_assign_rhs1 (stmt);

  if (gimple_assign_single_p (stmt))
    if (TREE_CODE (rhs) == SSA_NAME)
      return true;

  if (CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt)))
    {
      tree lhs = gimple_assign_lhs (stmt);

      if (TREE_CODE (rhs) == SSA_NAME
	  && types_compatible_p (TREE_TYPE (lhs), type))
	return true;
    }

  return false;
}

/* Return true if STMT is a copy to convert to integer. */

static bool
is_copy_int (const gimple *stmt)
{
  if (!is_gimple_assign (stmt))
    return NULL_TREE;

  tree rhs = gimple_assign_rhs1 (stmt);

  if (gimple_assign_single_p (stmt))
    if (TREE_CODE (rhs) == SSA_NAME)
      return true;

  if (CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt)))
    {
      tree lhs = gimple_assign_lhs (stmt);

      if (TREE_CODE (rhs) == SSA_NAME
	  && TREE_CODE (TREE_TYPE (lhs)) == INTEGER_TYPE)
	return true;
    }

  return false;
}

/* Check if STMT is a gimple assign whose rhs code is CODE.  */

static bool
gimple_assign_rhs_code_p (gimple *stmt, enum tree_code code)
{
  TEST (stmt != NULL && is_gimple_assign (stmt))
  return gimple_assign_rhs_code (stmt) == code;
}

/* Helper function to copy some attributes from ORIG_DECL to the NEW_DECL. */

static inline void
copy_var_attributes (tree new_decl, tree orig_decl)
{
  DECL_ARTIFICIAL (new_decl) = 1;
  DECL_EXTERNAL (new_decl) = DECL_EXTERNAL (orig_decl);
  TREE_STATIC (new_decl) = TREE_STATIC (orig_decl);
  TREE_PUBLIC (new_decl) = TREE_PUBLIC (orig_decl);
  TREE_USED (new_decl) = TREE_USED (orig_decl);
  DECL_CONTEXT (new_decl) = DECL_CONTEXT (orig_decl);
  TREE_THIS_VOLATILE (new_decl) = TREE_THIS_VOLATILE (orig_decl);
  TREE_ADDRESSABLE (new_decl) = TREE_ADDRESSABLE (orig_decl);
  TREE_READONLY (new_decl) = TREE_READONLY (orig_decl);
  DECL_SEEN_IN_BIND_EXPR_P (new_decl) = DECL_SEEN_IN_BIND_EXPR_P (orig_decl);
  if (is_global_var (orig_decl))
    set_decl_tls_model (new_decl, DECL_TLS_MODEL (orig_decl));
}

/*  Is TYPE a pointer to another pointer. */

static bool
isptrptr (tree type)
{
  if (type == NULL)
    {
      return false;
    }
  bool firstptr = false;
  while (POINTER_TYPE_P (type) || TREE_CODE (type) == ARRAY_TYPE)
    {
      if (POINTER_TYPE_P (type))
	{
	  if (firstptr)
	    return true;
	  firstptr = true;
	}
      type = TREE_TYPE (type);
    }
  return false;
}

/* Adding node to map and stack.  */

static bool
add_node (tree node, int layers, hash_map<tree, int> &map,
	  auto_vec<tree> &stack)
{
  if (TREE_CODE (node) != SSA_NAME)
    {
      return false;
    }
  if (map.get (node) == NULL)
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "	");
	  fprintf (dump_file, "add node: \t\t");
	  print_generic_expr (dump_file, node);
	  fprintf (dump_file, ",\t\tptr layers: %d: \n", layers);
	}
      map.put (node, layers);
      stack.safe_push (node);
    }
  else if (*map.get (node) != layers)
    {
      return false;
    }
  return true;
}

/* Check the number of pointer layers of the gimple phi in definition.  */

static bool
check_def_phi (tree def_node, hash_map<tree, int> &ptr_layers)
{
  bool res = true;
  gimple *def_stmt = SSA_NAME_DEF_STMT (def_node);
  for (unsigned j = 0; j < gimple_phi_num_args (def_stmt); j++)
    {
      tree phi_node = gimple_phi_arg_def (def_stmt, j);
      if (integer_zerop (phi_node))
	{
	  continue;
	}
      if (ptr_layers.get (phi_node) == NULL)
	{
	  return false;
	}
      res &= *ptr_layers.get (def_node) == *ptr_layers.get (phi_node);
    }
  return res;
}

/* Check the number of pointer layers of the gimple assign in definition.  */

static bool
check_def_assign (tree def_node, hash_map<tree, int> &ptr_layers)
{
  bool res = true;
  gimple *def_stmt = SSA_NAME_DEF_STMT (def_node);
  gimple_rhs_class rhs_class = gimple_assign_rhs_class (def_stmt);
  tree_code rhs_code = gimple_assign_rhs_code (def_stmt);
  tree rhs1 = gimple_assign_rhs1 (def_stmt);
  tree rhs1_base = TREE_CODE (rhs1) == MEM_REF ? TREE_OPERAND (rhs1, 0) : rhs1;
  if (ptr_layers.get (rhs1_base) == NULL)
    {
      return false;
    }
  if (rhs_class == GIMPLE_SINGLE_RHS || rhs_class == GIMPLE_UNARY_RHS)
    {
      if (TREE_CODE (rhs1) == SSA_NAME)
	{
	  res = *ptr_layers.get (def_node) == *ptr_layers.get (rhs1);
	}
      else if (TREE_CODE (rhs1) == MEM_REF)
	{
	  res = *ptr_layers.get (def_node)
		== *ptr_layers.get (TREE_OPERAND (rhs1, 0));
	}
      else
	{
	  return false;
	}
    }
  else if (rhs_class == GIMPLE_BINARY_RHS)
    {
      if (rhs_code == POINTER_PLUS_EXPR)
	{
	  res = *ptr_layers.get (def_node) == *ptr_layers.get (rhs1);
	}
      else if (rhs_code == BIT_AND_EXPR)
	{
	  res = *ptr_layers.get (def_node) == *ptr_layers.get (rhs1);
	}
      else
	{
	  return false;
	}
    }
  else
    {
      return false;
    }
  return res;
}

/* Check node definition.  */

static bool
check_node_def (hash_map<tree, int> &ptr_layers)
{
  bool res = true;
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n======== check node definition ========\n");
    }
  for (unsigned i = 1; i < num_ssa_names; ++i)
    {
      tree name = ssa_name (i);
      if (name && ptr_layers.get (name) != NULL)
	{
	  gimple *def_stmt = SSA_NAME_DEF_STMT (name);
	  if (dump_file && (dump_flags & TDF_DETAILS)
	      && gimple_code (def_stmt) != GIMPLE_DEBUG)
	    {
	      print_gimple_stmt (dump_file, def_stmt, 0);
	    }

	  if (gimple_code (def_stmt) == GIMPLE_PHI)
	    {
	      res = check_def_phi (name, ptr_layers);
	    }
	  else if (gimple_code (def_stmt) == GIMPLE_ASSIGN)
	    {
	      res = check_def_assign (name, ptr_layers);
	    }
	  else if (gimple_code (def_stmt) == GIMPLE_NOP)
	    {
	      continue;
	    }
	  else
	    {
	      return false;
	    }
	}
    }
  return res;
}

/* Check pointer usage.  */

static bool
check_record_ptr_usage (gimple *use_stmt, tree &current_node,
			hash_map<tree, int> &ptr_layers,
			auto_vec<tree> &ssa_name_stack)
{
  gimple_rhs_class rhs_class = gimple_assign_rhs_class (use_stmt);
  tree rhs1 = gimple_assign_rhs1 (use_stmt);
  tree lhs = gimple_assign_lhs (use_stmt);
  if (rhs_class != GIMPLE_SINGLE_RHS
      || (TREE_CODE (rhs1) != COMPONENT_REF && TREE_CODE (rhs1) != SSA_NAME)
      || (TREE_CODE (lhs) != MEM_REF && TREE_CODE (lhs) != SSA_NAME))
    {
      return false;
    }

  bool res = true;
  /* MEM[(long int *)a_1] = _1; (record).
     If lhs is ssa_name, lhs cannot be the current node.
     _2 = _1->field; (No record).  */
  if (TREE_CODE (rhs1) == SSA_NAME)
    {
      tree tmp = (rhs1 != current_node) ? rhs1 : lhs;
      if (TREE_CODE (tmp) == MEM_REF)
	{
	  res = add_node (TREE_OPERAND (tmp, 0),
			  *ptr_layers.get (current_node) + 1, ptr_layers,
			  ssa_name_stack);
	}
      else
	{
	  res = add_node (tmp, *ptr_layers.get (current_node), ptr_layers,
			  ssa_name_stack);
	}
    }
  else if (TREE_CODE (lhs) == SSA_NAME && TREE_CODE (rhs1) == COMPONENT_REF)
    {
      res = !(POINTER_TYPE_P (TREE_TYPE (rhs1)));
    }
  else
    {
      res = false;
    }
  return res;
}

/* Check and record a single node.  */

static bool
check_record_single_node (gimple *use_stmt, tree &current_node,
			  hash_map<tree, int> &ptr_layers,
			  auto_vec<tree> &ssa_name_stack)
{
  gimple_rhs_class rhs_class = gimple_assign_rhs_class (use_stmt);
  tree rhs1 = gimple_assign_rhs1 (use_stmt);
  tree lhs = gimple_assign_lhs (use_stmt);
  gcc_assert (rhs_class == GIMPLE_SINGLE_RHS || rhs_class == GIMPLE_UNARY_RHS);

  if ((TREE_CODE (rhs1) != SSA_NAME && TREE_CODE (rhs1) != MEM_REF)
      || (TREE_CODE (lhs) != SSA_NAME && TREE_CODE (lhs) != MEM_REF))
    {
      return false;
    }

  bool res = true;
  if (TREE_CODE (lhs) == SSA_NAME && TREE_CODE (rhs1) == MEM_REF)
    {
      /* add such as: _2 = MEM[(struct s * *)_1].  */
      res = add_node (lhs, *ptr_layers.get (current_node) - 1, ptr_layers,
		      ssa_name_stack);
    }
  else if (TREE_CODE (lhs) == MEM_REF && TREE_CODE (rhs1) == SSA_NAME)
    {
      /* add such as: MEM[(long int *)a_1] = _1.  */
      if (rhs1 == current_node)
	{
	  res = add_node (TREE_OPERAND (lhs, 0),
			  *ptr_layers.get (current_node) + 1, ptr_layers,
			  ssa_name_stack);
	}
      else
	{
	  res = add_node (rhs1, *ptr_layers.get (current_node) - 1, ptr_layers,
			  ssa_name_stack);
	}
    }
  else if (TREE_CODE (lhs) == SSA_NAME && TREE_CODE (rhs1) == SSA_NAME)
    {
      res = add_node (lhs, *ptr_layers.get (current_node), ptr_layers,
		      ssa_name_stack);
    }
  else
    {
      res = false;
    }

  return res;
}

/* Check and record multiple nodes.  */

static bool
check_record_mult_node (gimple *use_stmt, tree &current_node,
			hash_map<tree, int> &ptr_layers,
			auto_vec<tree> &ssa_name_stack)
{
  gimple_rhs_class rhs_class = gimple_assign_rhs_class (use_stmt);
  tree_code rhs_code = gimple_assign_rhs_code (use_stmt);
  tree rhs1 = gimple_assign_rhs1 (use_stmt);
  tree lhs = gimple_assign_lhs (use_stmt);
  tree rhs2 = gimple_assign_rhs2 (use_stmt);
  gcc_assert (rhs_class == GIMPLE_BINARY_RHS);

  if ((rhs_code != POINTER_PLUS_EXPR && rhs_code != POINTER_DIFF_EXPR
       && rhs_code != BIT_AND_EXPR)
      || (TREE_CODE (lhs) != SSA_NAME && TREE_CODE (rhs1) != SSA_NAME))
    {
      return false;
    }

  bool res = true;
  if (rhs_code == POINTER_PLUS_EXPR)
    {
      res
	= add_node (lhs == current_node ? rhs1 : lhs,
		    *ptr_layers.get (current_node), ptr_layers, ssa_name_stack);
    }
  else if (rhs_code == POINTER_DIFF_EXPR)
    {
      res
	= add_node (rhs1 != current_node ? rhs1 : rhs2,
		    *ptr_layers.get (current_node), ptr_layers, ssa_name_stack);
    }
  else if (rhs_code == BIT_AND_EXPR)
    {
      if (TREE_CODE (rhs2) != INTEGER_CST)
	{
	  return false;
	}
      res
	= add_node (lhs == current_node ? rhs1 : lhs,
		    *ptr_layers.get (current_node), ptr_layers, ssa_name_stack);
    }
  return res;
}

/* Check whether gimple assign is correctly used and record node.  */

static bool
check_record_assign (tree &current_node, gimple *use_stmt,
		     hash_map<tree, int> &ptr_layers,
		     auto_vec<tree> &ssa_name_stack)
{
  gimple_rhs_class rhs_class = gimple_assign_rhs_class (use_stmt);
  if (*ptr_layers.get (current_node) == 1)
    {
      return check_record_ptr_usage (use_stmt, current_node, ptr_layers,
				     ssa_name_stack);
    }
  else if (*ptr_layers.get (current_node) > 1)
    {
      if (rhs_class != GIMPLE_BINARY_RHS && rhs_class != GIMPLE_UNARY_RHS
	  && rhs_class != GIMPLE_SINGLE_RHS)
	{
	  return false;
	}

      if (rhs_class == GIMPLE_SINGLE_RHS || rhs_class == GIMPLE_UNARY_RHS)
	{
	  return check_record_single_node (use_stmt, current_node, ptr_layers,
					   ssa_name_stack);
	}
      else if (rhs_class == GIMPLE_BINARY_RHS)
	{
	  return check_record_mult_node (use_stmt, current_node, ptr_layers,
					 ssa_name_stack);
	}
    }
  else
    return false;

  return true;
}

/* Check whether gimple phi is correctly used and record node.  */

static bool
check_record_phi (tree &current_node, gimple *use_stmt,
		  hash_map<tree, int> &ptr_layers,
		  auto_vec<tree> &ssa_name_stack)
{
  bool res = true;
  res &= add_node (gimple_phi_result (use_stmt), *ptr_layers.get (current_node),
		   ptr_layers, ssa_name_stack);

  for (unsigned i = 0; i < gimple_phi_num_args (use_stmt); i++)
    {
      if (integer_zerop (gimple_phi_arg_def (use_stmt, i)))
	{
	  continue;
	}
      res &= add_node (gimple_phi_arg_def (use_stmt, i),
		       *ptr_layers.get (current_node), ptr_layers,
		       ssa_name_stack);
    }
  return res;
}

/* Check the use of callee.  */

static bool
check_callee (cgraph_node *node, gimple *stmt, hash_map<tree, int> &ptr_layers,
	      int input_layers)
{
  /* caller main ()
	    { foo (_1, _2); }
     def    foo (void * a, size_t n)
	    { foo (_3, _4); }  */
  /* In safe functions, only call itself is allowed.  */
  if (node->get_edge (stmt)->callee != node)
    {
      return false;
    }
  tree input_node = gimple_call_arg (stmt, 0);
  if (ptr_layers.get (input_node) == NULL
      || *ptr_layers.get (input_node) != input_layers)
    {
      return false;
    }
  if (SSA_NAME_VAR (input_node) != DECL_ARGUMENTS (node->decl))
    {
      return false;
    }

  for (unsigned i = 1; i < gimple_call_num_args (stmt); i++)
    {
      if (ptr_layers.get (gimple_call_arg (stmt, i)) != NULL)
	{
	  return false;
	}
    }
  return true;
}

/* Check the usage of input nodes and related nodes.  */

static bool
check_node_use (cgraph_node *node, tree current_node,
		hash_map<tree, int> &ptr_layers, auto_vec<tree> &ssa_name_stack,
		int input_layers)
{
  imm_use_iterator imm_iter;
  gimple *use_stmt = NULL;
  bool res = true;
  /* Use FOR_EACH_IMM_USE_STMT as an indirect edge
     to search for possible related nodes and push to stack.  */
  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, current_node)
    {
      if (dump_file && (dump_flags & TDF_DETAILS)
	  && gimple_code (use_stmt) != GIMPLE_DEBUG)
	{
	  fprintf (dump_file, "%*s", 4, "");
	  print_gimple_stmt (dump_file, use_stmt, 0);
	}
      /* For other types of gimple, do not record the node.  */
      if (res)
	{
	  if (gimple_code (use_stmt) == GIMPLE_PHI)
	    {
	      res = check_record_phi (current_node, use_stmt, ptr_layers,
				      ssa_name_stack);
	    }
	  else if (gimple_code (use_stmt) == GIMPLE_ASSIGN)
	    {
	      res = check_record_assign (current_node, use_stmt, ptr_layers,
					 ssa_name_stack);
	    }
	  else if (gimple_code (use_stmt) == GIMPLE_CALL)
	    {
	      res = check_callee (node, use_stmt, ptr_layers, input_layers);
	    }
	  else if (gimple_code (use_stmt) == GIMPLE_RETURN)
	    {
	      res = false;
	    }
	}
    }
  return res;
}

/* Preparing the First Node for DFS.  */

static bool
set_init_node (cgraph_node *node, cgraph_edge *caller,
	       hash_map<tree, int> &ptr_layers, auto_vec<tree> &ssa_name_stack,
	       int &input_layers)
{
  /* set input_layer
     caller bar (_3, _4)
		  |-- Obtains the actual ptr layer
		      from the input node.  */
  if (caller->call_stmt == NULL
      || gimple_call_num_args (caller->call_stmt) == 0)
    {
      return false;
    }
  tree input = gimple_call_arg (caller->call_stmt, 0);
  if (!(POINTER_TYPE_P (TREE_TYPE (input))
	|| TREE_CODE (TREE_TYPE (input)) == ARRAY_TYPE)
      || !handled_type (TREE_TYPE (input)))
    {
      return false;
    }
  input_layers = get_ptr_layers (TREE_TYPE (input));

  /* set initial node
     def foo (void * a, size_t n)
		     |-- Find the initial ssa_name
			 from the parameter node.  */
  tree parm = DECL_ARGUMENTS (node->decl);
  for (unsigned j = 1; j < num_ssa_names; ++j)
    {
      tree name = ssa_name (j);
      if (!name || has_zero_uses (name) || virtual_operand_p (name))
	{
	  continue;
	}
      if (SSA_NAME_VAR (name) == parm
	  && gimple_code (SSA_NAME_DEF_STMT (name)) == GIMPLE_NOP)
	{
	  if (!add_node (name, input_layers, ptr_layers, ssa_name_stack))
	    {
	      return false;
	    }
	}
    }
  return !ssa_name_stack.is_empty ();
}

/* Check the usage of each call.  */

static bool
check_each_call (cgraph_node *node, cgraph_edge *caller)
{
  hash_map<tree, int> ptr_layers;
  auto_vec<tree> ssa_name_stack;
  int input_layers = 0;
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "======== check each call : %s/%u ========\n",
	       node->name (), node->order);
    }
  if (!set_init_node (node, caller, ptr_layers, ssa_name_stack, input_layers))
    {
      return false;
    }
  int i = 0;
  while (!ssa_name_stack.is_empty ())
    {
      tree current_node = ssa_name_stack.pop ();
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\ncur node %d: \t", i++);
	  print_generic_expr (dump_file, current_node);
	  fprintf (dump_file, ",\t\tptr layers: %d: \n",
		   *ptr_layers.get (current_node));
	}
      if (get_ptr_layers (TREE_TYPE (current_node))
	  > *ptr_layers.get (current_node))
	{
	  return false;
	}
      if (!check_node_use (node, current_node, ptr_layers, ssa_name_stack,
			   input_layers))
	{
	  return false;
	}
    }

  if (!check_node_def (ptr_layers))
    {
      return false;
    }
  return true;
}

/* Filter out function: void func (void*, int n),
   and the function has no static variable, no structure-related variable,
   and no global variable is used.  */

static bool
filter_func (cgraph_node *node)
{
  tree parm = DECL_ARGUMENTS (node->decl);
  if (!(parm && VOID_POINTER_P (TREE_TYPE (parm))
	&& VOID_TYPE_P (TREE_TYPE (TREE_TYPE (node->decl)))))
    {
      return false;
    }

  for (parm = DECL_CHAIN (parm); parm; parm = DECL_CHAIN (parm))
    {
      if (TREE_CODE (TREE_TYPE (parm)) != INTEGER_TYPE)
	{
	  return false;
	}
    }

  if (DECL_STRUCT_FUNCTION (node->decl)->static_chain_decl)
    {
      return false;
    }

  tree var = NULL_TREE;
  unsigned int i = 0;
  bool res = true;
  FOR_EACH_LOCAL_DECL (cfun, i, var)
    {
      if (TREE_CODE (var) == VAR_DECL && handled_type (TREE_TYPE (var)))
	{
	  res = false;
	}
    }
  if (!res)
    {
      return false;
    }

  for (unsigned j = 1; j < num_ssa_names; ++j)
    {
      tree name = ssa_name (j);
      if (!name || has_zero_uses (name) || virtual_operand_p (name))
	{
	  continue;
	}
      tree var = SSA_NAME_VAR (name);
      if (var && TREE_CODE (var) == VAR_DECL && is_global_var (var))
	{
	  return false;
	}
    }
  return true;
}

/* Check whether the function with the void* parameter and uses the input node
   safely.
   In these functions only component_ref can be used to dereference the last
   layer of the input structure pointer.  The hack operation pointer offset
   after type cast cannot be used.
*/

static bool
is_safe_func_with_void_ptr_parm (cgraph_node *node)
{
  if (!filter_func (node))
    {
      return false;
    }

  /* Distinguish Recursive Callers
     normal_callers:    main ()
			{ foo (_649, _651); }
     definition:	foo (void * a, size_t n)
     recursive_callers: { foo (a_1, _139); }  */
  auto_vec<cgraph_edge *> callers = node->collect_callers ();
  auto_vec<cgraph_edge *> normal_callers;
  for (unsigned i = 0; i < callers.length (); i++)
    {
      if (callers[i]->caller != node)
	{
	  normal_callers.safe_push (callers[i]);
	}
    }
  if (normal_callers.length () == 0)
    {
      return false;
    }

  for (unsigned i = 0; i < normal_callers.length (); i++)
    {
      if (!check_each_call (node, normal_callers[i]))
	{
	  return false;
	}
    }
  return true;
}

#define IS_STRUCT_RELAYOUT_NAME(tname) \
  strstr ((tname), ".reorder") || strstr ((tname), ".dfe") \
    || strstr ((tname), ".reorg") || strstr ((tname), ".sdco")

/* Calculate the multiplier.  */

static bool
calculate_mult_num (tree arg, tree *num, tree struct_type)
{
  gcc_assert (TREE_CODE (arg) == INTEGER_CST);
  bool sign = false;
  HOST_WIDE_INT size = TREE_INT_CST_LOW (arg);
  if (size < 0)
    {
      size = -size;
      sign = true;
    }
  tree struct_size = TYPE_SIZE_UNIT (struct_type);

  tree arg2 = build_int_cst (TREE_TYPE (arg), size);
  if (integer_zerop (size_binop (FLOOR_MOD_EXPR, arg2, struct_size)))
    {
      tree number = size_binop (FLOOR_DIV_EXPR, arg2, struct_size);
      if (sign)
	{
	  number = build_int_cst (TREE_TYPE (number), -tree_to_shwi (number));
	}
      *num = number;
      return true;
    }

  return false;
}

/* For recursive definition. */
static bool
is_result_of_mult (tree arg, tree *num, tree struct_type);

/* Trace and calculate the multiplier of PLUS_EXPR.  */

static bool
trace_calculate_plus (gimple *size_def_stmt, tree *num, tree struct_type)
{
  gcc_assert (gimple_assign_rhs_code (size_def_stmt) == PLUS_EXPR);

  tree num1 = NULL_TREE;
  tree num2 = NULL_TREE;
  tree arg0 = gimple_assign_rhs1 (size_def_stmt);
  tree arg1 = gimple_assign_rhs2 (size_def_stmt);
  if (!is_result_of_mult (arg0, &num1, struct_type) || num1 == NULL_TREE)
    {
      return false;
    }
  if (!is_result_of_mult (arg1, &num2, struct_type) || num2 == NULL_TREE)
    {
      return false;
    }
  *num = size_binop (PLUS_EXPR, num1, num2);
  return true;
}

/* Trace and calculate the multiplier of MULT_EXPR.  */

static bool
trace_calculate_mult (gimple *size_def_stmt, tree *num, tree struct_type)
{
  gcc_assert (gimple_assign_rhs_code (size_def_stmt) == MULT_EXPR);

  tree arg0 = gimple_assign_rhs1 (size_def_stmt);
  tree arg1 = gimple_assign_rhs2 (size_def_stmt);
  tree num1 = NULL_TREE;

  if (is_result_of_mult (arg0, &num1, struct_type) && num1 != NULL_TREE)
    {
      *num = size_binop (MULT_EXPR, arg1, num1);
      return true;
    }
  if (is_result_of_mult (arg1, &num1, struct_type) && num1 != NULL_TREE)
    {
      *num = size_binop (MULT_EXPR, arg0, num1);
      return true;
    }
  *num = NULL_TREE;
  return false;
}

/* Trace and calculate the multiplier of NEGATE_EXPR.  */

static bool
trace_calculate_negate (gimple *size_def_stmt, tree *num, tree struct_type)
{
  gcc_assert (gimple_assign_rhs_code (size_def_stmt) == NEGATE_EXPR);

  /* support NEGATE_EXPR trace: _3 = -_2; _2 = _1 * 72.  */
  tree num1 = NULL_TREE;
  tree arg0 = gimple_assign_rhs1 (size_def_stmt);
  if (!is_result_of_mult (arg0, &num1, struct_type) || num1 == NULL_TREE)
    {
      return false;
    }
  tree num0 = build_int_cst (TREE_TYPE (num1), -1);
  *num = size_binop (MULT_EXPR, num0, num1);
  return true;
}

/* Trace and calculate the multiplier of POINTER_DIFF_EXPR.  */

static bool
trace_calculate_diff (gimple *size_def_stmt, tree *num)
{
  gcc_assert (gimple_assign_rhs_code (size_def_stmt) == NOP_EXPR);

  /* support POINTER_DIFF_EXPR trace:
  _3 = (long unsigned int) _2; _2 = _1 - old_vars.  */
  tree arg = gimple_assign_rhs1 (size_def_stmt);
  size_def_stmt = SSA_NAME_DEF_STMT (arg);
  if (size_def_stmt && is_gimple_assign (size_def_stmt)
      && gimple_assign_rhs_code (size_def_stmt) == POINTER_DIFF_EXPR)
    {
      *num = NULL_TREE;
      return true;
    }
  *num = NULL_TREE;
  return false;
}

/* This function checks whether ARG is a result of multiplication
   of some number by STRUCT_SIZE.  If yes, the function returns true
   and this number is filled into NUM.

   - When USE_OLD_SIZE is true, the original size of a optimized structure
     will be used. This is for situation when the 'sizeof' result is not
     replaced (e.g. arguments of calloc/malloc).
   - When USE_OLD_SIZE is false, the new size of a optimized structure will
     be used. This is for situation when the 'sizeof' result is already
     modified (e.g. pointer plus).  */

static bool
is_result_of_mult (tree arg, tree *num, tree struct_type)
{
  tree struct_size = TYPE_SIZE_UNIT (struct_type);
  if (!struct_size || TREE_CODE (struct_size) != INTEGER_CST
      || integer_zerop (struct_size))
    return false;

  /* If we have a integer, just check if it is a multiply of STRUCT_SIZE.  */
  if (TREE_CODE (arg) == INTEGER_CST)
    {
      return calculate_mult_num (arg, num, struct_type);
    }

  gimple *size_def_stmt = SSA_NAME_DEF_STMT (arg);

  /* If the allocation statement was of the form
     D.2229_10 = <alloc_func> (D.2228_9);
     then size_def_stmt can be D.2228_9 = num.3_8 * 8;  */

  while (size_def_stmt && is_gimple_assign (size_def_stmt))
    {
      tree lhs = gimple_assign_lhs (size_def_stmt);

      /* We expect temporary here.  */
      if (!is_gimple_reg (lhs))
	return false;

      // FIXME: this should handle SHIFT also.
      tree_code rhs_code = gimple_assign_rhs_code (size_def_stmt);
      if (rhs_code == PLUS_EXPR)
	{
	  return trace_calculate_plus (size_def_stmt, num, struct_type);
	}
      else if (rhs_code == MULT_EXPR)
	{
	  return trace_calculate_mult (size_def_stmt, num, struct_type);
	}
      else if (rhs_code == SSA_NAME)
	{
	  arg = gimple_assign_rhs1 (size_def_stmt);
	  size_def_stmt = SSA_NAME_DEF_STMT (arg);
	}
      else if (rhs_code == NEGATE_EXPR)
	{
	  return trace_calculate_negate (size_def_stmt, num, struct_type);
	}
      else if (rhs_code == NOP_EXPR)
	{
	  return trace_calculate_diff (size_def_stmt, num);
	}
      else
	{
	  *num = NULL_TREE;
	  return false;
	}
    }

  *num = NULL_TREE;
  return false;
}

/*************************************************************/
/* The definitions above are utilities not specific for DCO. */
/*************************************************************/

#define COMPRESSED_SINGLE_PREFIX "_compress_var_"
#define DYN_PATH "_dyn_path_"
#define COMPRESSED_INDEX "_compressed_idx_"
#define ENCODE_FN_PREFIX "_encode_"
#define DECODE_FN_PREFIX "_decode_"

/* The maximum number of new DCO types. For code size reason, we support at
   most 3 dynamic conditions checking. */
const int MAX_NUM_NEW_TYPES = 8;

/* The number of new dynamic-DCO paths.  */
unsigned num_new_paths;
/* The current new type index (from 0 to srtype::num_of_new_types - 1).  */
unsigned new_type_idx;
/* The index of new static-DCO type in new type array (see srtype::newtype).  */
unsigned sdco_type_idx = (unsigned) -1;

inline bool
static_dco_trans_p ()
{
  return new_type_idx == sdco_type_idx;
}

struct srfield;
struct srtype;
struct srdecl;
struct srfunction;
class dco_info;
class dco_field;
class dco_variant;
class dco_field_class;
class dco_cond;
class dco_closure;
class csrfun_context;

srfunction *cur_srfun;
static vec<srfunction *> csrfun_stack;

#define SET_CFUN(srfn) csrfun_context dco_ctx (srfn);

#define SET_CFUN_WITH_LOOP_OPT(srfn, loop_opt_p) \
  csrfun_context dco_ctx (srfn, loop_opt_p);

class dco_path_info
{
public:
  /* The start stmt to clone blocks.  If it is NULL, the whole function is
     cloned (i.e. versioning).  */
  gimple *start_stmt;

  /* Blocks reachable from the start_stmt.  */
  auto_vec<basic_block> reach_bbs;
  /* Cloned basic blocks of reach_bbs.  */
  auto_vec<basic_block *> cloned_reach_bbs;

  /* Blocks that can reach the start_stmt.  */
  auto_vec<basic_block> pre_bbs;

  /* Cloned whole function versions.  */
  auto_delete_vec<srfunction> cloned_funcs;

  dco_path_info () : start_stmt (NULL) {}
  ~dco_path_info ()
  {
    unsigned i;
    basic_block *cloned_bbs;

    FOR_EACH_VEC_ELT (cloned_reach_bbs, i, cloned_bbs)
      free (cloned_bbs);
  }

  bool collect_reachable_bbs (gimple *, int);
};

struct srfunction
{
  cgraph_node *node;
  auto_vec<srdecl *> args;
  auto_vec<srdecl *> globals;
  auto_delete_vec<srdecl> decls;
  srdecl *record_decl (srtype *, tree, int arg, tree orig_type = NULL);

  srfunction *old;
  cgraph_node *newnode;
  srfunction *newf;

  bool is_safe_func;

  /* A function is either partially cloned or fully cloned (versioning). */
  dco_path_info dco_path;

  // Constructors
  srfunction (cgraph_node *n);

  // Methods
  void add_arg (srdecl *arg);
  void dump (FILE *file);
  void simple_dump (FILE *file);

  /* A function is either partially cloned or fully cloned (versioning). */
  bool partial_clone_p () { return dco_path.start_stmt != NULL; }

  struct function *get_sturct_func (void)
  {
    return DECL_STRUCT_FUNCTION (node->decl);
  }

  bool check_args (void);
  void create_new_decls (void);
  srdecl *find_decl (tree);
};

class csrfun_context
{
public:
  csrfun_context (srfunction *srfun, bool loop_opt_p = false)
    : loop_opt_p (loop_opt_p)
  {
    csrfun_stack.safe_push (cur_srfun);
    cur_srfun = srfun;

    push_cfun (DECL_STRUCT_FUNCTION (srfun->node->decl));

    if (loop_opt_p)
      loop_optimizer_init (LOOPS_HAVE_PREHEADERS | LOOPS_HAVE_SIMPLE_LATCHES
			   | LOOPS_HAVE_RECORDED_EXITS);
  }

  ~csrfun_context ()
  {
    if (loop_opt_p)
      loop_optimizer_finalize ();
    pop_cfun ();
    cur_srfun = csrfun_stack.pop ();
  }

private:
  bool loop_opt_p;
};

struct srglobal : private srfunction
{
  srglobal () : srfunction (NULL) {}

  using srfunction::create_new_decls;
  using srfunction::decls;
  using srfunction::dump;
  using srfunction::find_decl;
  using srfunction::record_decl;
};

struct srtype
{
  tree type;
  auto_delete_vec<srfield> fields;

  // array of fields that use this type.
  auto_vec<srfield *> field_sites;

  // array of functions which use directly the type
  auto_vec<srfunction *> functions;

  bool chain_type;

  // Whether rewriting is supported for this type.
  bool supported;

public:
  unsigned num_of_new_types;
  tree newtype[MAX_NUM_NEW_TYPES];
  bool visited;

  /* The DCO info linked to this type. */
  dco_info *dinfo;

  // Constructors
  srtype (tree type);

  // Methods
  void dump (FILE *file);
  void simple_dump (FILE *file);
  void add_function (srfunction *);
  void add_field_site (srfield *);

  /* Return true if it is a DCO candidate type.  */
  bool dco_candidate_p ();

  srfield *find_field (unsigned HOST_WIDE_INT offset);
  srfield *find_field_by_decl (tree fielddecl);

  unsigned create_new_dco_types (void);
  bool has_escaped (void)
  {
    if (TYPE_NON_ESCAPING_P (type))
      return false;
    const char *tname = get_type_name (type);
    if (!tname)
      return true;
    return !(IS_STRUCT_RELAYOUT_NAME (tname));
  }

  void mark_unsupported (gimple *stmt)
  {
    if (supported && dump_file && (dump_flags & TDF_DETAILS))
      {
	fprintf (dump_file, "Type ");
	print_generic_expr (dump_file, type);
	fprintf (dump_file, " is marked unsupported from: ");
	print_gimple_stmt (dump_file, stmt, 0);
      }
    supported = false;
  }
  bool has_new_type (void) { return newtype[new_type_idx] != NULL_TREE; }
};

struct srfield
{
  unsigned HOST_WIDE_INT offset;
  tree fieldtype;
  tree fielddecl;
  srtype *base;
  srtype *type;

  tree newfield[MAX_NUM_NEW_TYPES];

  /* The dco info linked to this field. */
  dco_field *dynamic_df;
  dco_field *static_df;
  /* A dead field will be removed during static DCO transformation. */
  bool dead_field_p;

  dco_field_class *dfc;

  // Constructors
  srfield (tree field, srtype *base);

  // Methods
  void dump (FILE *file);
  void simple_dump (FILE *file);

  void compress_fields (tree newfields[MAX_NUM_NEW_TYPES],
			tree newlast[MAX_NUM_NEW_TYPES], tree &field,
			unsigned cur_idx);
  void create_new_dco_fields (tree newtype[MAX_NUM_NEW_TYPES],
			      tree newfields[MAX_NUM_NEW_TYPES],
			      tree newlast[MAX_NUM_NEW_TYPES],
			      dco_variant *variant, unsigned cur_idx);
  dco_closure *get_closure ();
  bool ddco_type_change_p ();
};

struct srdecl
{
  srtype *type;
  tree decl;
  tree func;
  /* -1 : not an argument
     -2 : static chain */
  int argumentnum;

  bool visited;

  tree newdecl[MAX_NUM_NEW_TYPES];

  /* Auxiliary record complete original type information of the void* type.  */
  tree orig_type;

  // Constructors
  srdecl (srtype *type, tree decl, int argumentnum = -1, tree orgtype = NULL);

  // Methods
  void dump (FILE *file);
  bool has_new_decl (void)
  {
    return newdecl[new_type_idx] && newdecl[new_type_idx] != decl;
  }
};

typedef enum
{
  CLOSURE_INT,
  ARRAY_POINTER,
  ARRAY_INDEX,
  UNKNOWN_KIND
} DCO_KIND;

class dco_field;

/* Describe stmt closure to help rewrite. The closure could be either array
   pointers for the same memory space, or normal data without calculation. */
class dco_closure
{
public:
  /* The memory base ssa for the pointer DCO field candidate. */
  tree mem_base_ssa;

  /* The memory base global var for the pointer DCO field candidate. */
  tree mem_base_var;

  /* The size of struct for array pointer used in generating encode/decode.  */
  tree struct_size;

  /* The stmts for read/write of the DCO field. For rd/wt_change, we will
     need to add _decode and _encode for read and write respectively. */
  auto_vec<gimple *> rd_unchange;
  auto_vec<gimple *> rd_change;
  auto_vec<gimple *> wt_unchange;
  auto_vec<gimple *> wt_change;
  hash_set<gimple *> rd_unchange_set;
  hash_set<gimple *> rd_change_set;
  hash_set<gimple *> wt_unchange_set;
  hash_set<gimple *> wt_change_set;

  void add_rd_change (gimple *stmt)
  {
    if (rd_change.contains (stmt))
      return;
    rd_change.safe_push (stmt);
    rd_change_set.add (stmt);
  }
  bool rd_change_p (gimple *stmt) { return rd_change_set.contains (stmt); }

  void add_rd_unchange (gimple *stmt)
  {
    if (rd_unchange.contains (stmt))
      return;
    rd_unchange.safe_push (stmt);
    rd_unchange_set.add (stmt);
  }
  bool rd_unchange_p (gimple *stmt) { return rd_unchange_set.contains (stmt); }

  void add_wt_change (gimple *stmt, tree index = NULL_TREE)
  {
    if (wt_change.contains (stmt))
      return;
    wt_change.safe_push (stmt);
    wt_change_set.add (stmt);

    wt_array_index.safe_push (index);
  }
  bool wt_change_p (gimple *stmt) { return wt_change_set.contains (stmt); }

  void add_wt_unchange (gimple *stmt)
  {
    if (wt_unchange.contains (stmt))
      return;
    wt_unchange.safe_push (stmt);
    wt_unchange_set.add (stmt);
  }
  bool wt_unchange_p (gimple *stmt) { return wt_unchange_set.contains (stmt); }

  /* Keep the array index of for an array pointer write. It is a 1:1 map with
     wt_change. */
  auto_vec<tree> wt_array_index;

  /* Record the known special value assigned to this dco field. */
  hash_set<tree> wt_special_val;

  /* Call encode/decode function FN for RHS.  */
  tree encode_decode_rhs (tree rhs, tree fn);

  /* Encode/Decode array pointer for write/read stmt.  */
  void encode_array_pointer (gimple *wt_stmt, tree &newlhs, tree &newrhs);
  void decode_array_pointer (gimple *rd_stmt, tree &newlhs, tree &newrhs);

  bool change_p (gimple *stmt)
  {
    return wt_change_p (stmt) || rd_change_p (stmt);
  }
  bool unchange_p (gimple *stmt)
  {
    return wt_unchange_p (stmt) || rd_unchange_p (stmt);
  }

  void dump ();
  dco_closure () : mem_base_ssa (NULL_TREE), mem_base_var (NULL_TREE) {}
  ~dco_closure () {}
};

/* Record the boundary informations for the RHS of USE_STMT.  */

class dco_bound_info
{
public:
  gimple *use_stmt;
  srfunction *srfn;

  /* The bound is the sum of const exprs.  */
  auto_vec<tree> const_exprs;
  auto_vec<gimple *> const_stmts;

  dco_bound_info (gimple *use_stmt) : use_stmt (use_stmt), srfn (cur_srfun) {}

  bool get_upper_bound ();

  void dump (FILE *file)
  {
    unsigned i;
    tree expr;

    fprintf (file, "[UPPER BOUND] Bound of ");
    print_generic_expr (file, gimple_assign_rhs1 (use_stmt));

    fprintf (file, " : ");

    FOR_EACH_VEC_ELT (const_exprs, i, expr)
      {
	if (i)
	  fprintf (file, " + ");
	print_generic_expr (file, expr);
      }
    fprintf (file, "\n");

    for (auto stmt : const_stmts)
      {
	fprintf (file, "Bound def: ");
	print_gimple_stmt (file, stmt, 0);
      }
  }
};

static bool
extract_greater_than_exit_condition (edge ex, enum tree_code &code,
				     tree &cond_lhs, tree &cond_rhs)
{
  gcond *cond = safe_dyn_cast<gcond *> (last_stmt (ex->src));

  if (!cond)
    return false;

  code = gimple_cond_code (cond);

  if (ex->flags & EDGE_FALSE_VALUE)
    code = invert_tree_comparison (code, false);

  cond_lhs = gimple_cond_lhs (cond);
  cond_rhs = gimple_cond_rhs (cond);

  if (code == LT_EXPR || code == LE_EXPR)
    {
      code = swap_tree_comparison (code);
      std::swap (cond_lhs, cond_rhs);
    }
  else if (code != GE_EXPR && code != GT_EXPR)
    return false;

  return true;
}

/* Return the inner variable decl or const integer if exists, otherwise return
   NULL_TREE.  */

static tree
maybe_const_expr (tree expr)
{
  if (TREE_CODE (expr) == INTEGER_CST)
    return expr;

  while (TREE_CODE (expr) == COMPONENT_REF)
    expr = TREE_OPERAND (expr, 0);

  if (TREE_CODE (expr) == MEM_REF)
    {
      tree addr = TREE_OPERAND (expr, 0);

      if (TREE_CODE (addr) != ADDR_EXPR)
	return NULL_TREE;

      expr = TREE_OPERAND (addr, 0);
    }

  if (TREE_CODE (expr) == VAR_DECL && !auto_var_p (expr))
    return expr;

  return NULL_TREE;
}

static tree
get_real_expr (tree expr, bool allow_cvt = true, gimple **ref_stmt_ptr = NULL)
{
  gimple *ref_stmt = NULL;

  while (TREE_CODE (expr) == SSA_NAME)
    {
      gimple *stmt = SSA_NAME_DEF_STMT (expr);

      if (!is_gimple_assign (stmt))
	break;

      tree rhs1 = gimple_assign_rhs1 (stmt);

      if (gimple_assign_rhs_class (stmt) == GIMPLE_SINGLE_RHS)
	expr = rhs1;
      else if (allow_cvt && CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt))
	       && tree_nop_conversion_p (TREE_TYPE (rhs1), TREE_TYPE (expr)))
	expr = rhs1;
      else
	break;

      ref_stmt = stmt;
    }

  if (ref_stmt_ptr)
    *ref_stmt_ptr = ref_stmt;

  return expr;
}

static bool
get_iv_bound (gphi *phi, basic_block use_bb, auto_vec<tree> &bound,
	      auto_vec<gimple *> &bound_stmts)
{
  class loop *loop = gimple_bb (phi)->loop_father;
  edge entry = loop_preheader_edge (loop);
  edge latch = loop_latch_edge (loop);
  tree entry_value = PHI_ARG_DEF_FROM_EDGE (phi, entry);
  tree latch_value = PHI_ARG_DEF_FROM_EDGE (phi, latch);
  tree value = gimple_phi_result (phi);

  entry_value = get_real_expr (entry_value);

  if (TREE_CODE (entry_value) != INTEGER_CST
      || tree_int_cst_lt (vrp_val_max (signed_char_type_node), entry_value)
      || tree_int_cst_sign_bit (entry_value))
    return false;

  if (TREE_CODE (latch_value) != SSA_NAME)
    return false;

  gimple *stmt = SSA_NAME_DEF_STMT (latch_value);

  if (!is_gimple_assign (stmt))
    return false;

  if (gimple_assign_rhs_code (stmt) != PLUS_EXPR
      || gimple_assign_rhs1 (stmt) != value)
    return false;

  tree step = gimple_assign_rhs2 (stmt);

  if (TREE_CODE (step) != INTEGER_CST || tree_int_cst_sign_bit (step))
    return false;

  if (!TYPE_OVERFLOW_UNDEFINED (TREE_TYPE (value)))
    {
      if (!integer_onep (step) || !finite_loop_p (loop))
	return false;
    }

  auto_vec<edge> exits = get_loop_exit_edges (loop);
  unsigned i;
  edge ex;

  FOR_EACH_VEC_ELT (exits, i, ex)
    {
      enum tree_code code;
      tree cond_lhs;
      tree cond_rhs;

      if (!extract_greater_than_exit_condition (ex, code, cond_lhs, cond_rhs))
	continue;

      cond_lhs = get_real_expr (cond_lhs, false);
      if (TREE_CODE (cond_lhs) != SSA_NAME
	  || !INTEGRAL_TYPE_P (TREE_TYPE (cond_lhs)))
	continue;

      if (cond_lhs != value && cond_lhs != latch_value)
	{
	  gimple *cond_lhs_stmt = SSA_NAME_DEF_STMT (cond_lhs);

	  if (!is_gimple_assign (cond_lhs_stmt)
	      || !CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (cond_lhs_stmt)))
	    continue;

	  if (gimple_assign_rhs1 (cond_lhs_stmt) != value
	      && gimple_assign_rhs1 (cond_lhs_stmt) != latch_value)
	    continue;

	  if (TYPE_PRECISION (TREE_TYPE (cond_lhs))
	      < TYPE_PRECISION (TREE_TYPE (value)))
	    continue;
	}

      gimple *cond_rhs_stmt = NULL;

      cond_rhs = get_real_expr (cond_rhs, true, &cond_rhs_stmt);
      if (!maybe_const_expr (cond_rhs))
	continue;

      bool add_one = true;

      if (dominated_by_p (CDI_DOMINATORS, use_bb, ex->src))
	add_one = use_bb == ex->src;
      else if (just_once_each_iteration_p (loop, ex->src))
	continue;

      bound.safe_push (cond_rhs);

      if (TREE_CODE (cond_rhs) != INTEGER_CST)
	{
	  gcc_checking_assert (cond_rhs_stmt);
	  bound_stmts.safe_push (cond_rhs_stmt);
	}

      if (add_one)
	bound.safe_push (build_one_cst (TREE_TYPE (value)));

      return true;
    }

  return false;
}

/* Return the potential upper_bound of RHS of the STMT. Return false, if we
   cannot figure out anything at all. */

bool
dco_bound_info::get_upper_bound ()
{
  tree rhs = gimple_assign_rhs1 (use_stmt);
  auto_vec<tree> worklist;

  gcc_checking_assert (INTEGRAL_TYPE_P (TREE_TYPE (rhs)));
  worklist.safe_push (rhs);

  do
    {
      tree expr = worklist.pop ();

      if (TREE_CODE (expr) == INTEGER_CST)
	{
	  const_exprs.safe_push (expr);
	  continue;
	}

      if (TREE_CODE (expr) != SSA_NAME)
	return false;

      gimple *def_stmt = SSA_NAME_DEF_STMT (expr);

      if (gphi *phi = dyn_cast<gphi *> (def_stmt))
	{
	  basic_block bb = gimple_bb (phi);
	  class loop *loop = bb->loop_father;

	  if (loop->header != bb)
	    return false;

	  if (!get_iv_bound (phi, gimple_bb (use_stmt), const_exprs,
			     const_stmts))
	    return false;

	  continue;
	}

      if (!is_gimple_assign (def_stmt))
	return false;

      enum tree_code code = gimple_assign_rhs_code (def_stmt);
      tree rhs1 = gimple_assign_rhs1 (def_stmt);
      tree rhs2 = gimple_assign_rhs2 (def_stmt);

      switch (code)
	{
	CASE_CONVERT:
	  rhs1 = gimple_assign_rhs1 (def_stmt);
	  if (!INTEGRAL_TYPE_P (TREE_TYPE (rhs1)))
	    return false;

	  /* fall-through.  */

	case SSA_NAME:
	case INTEGER_CST:
	  worklist.safe_push (rhs1);
	  break;

	case PLUS_EXPR:
	  worklist.safe_push (rhs1);
	  worklist.safe_push (rhs2);
	  break;

	default:
	  if (!gimple_assign_single_p (def_stmt))
	    return false;

	  if (!maybe_const_expr (rhs1))
	    return false;

	  const_exprs.safe_push (rhs1);
	  const_stmts.safe_push (def_stmt);
	}
    }
  while (!worklist.is_empty ());

  return !const_exprs.is_empty ();
}

/* All fields belong to this class should have the same type. */

class dco_field_class
{
public:
  /* The same type for all of the fields in the class. */
  tree fieldtype;

  /* The fields with the same type are in the same element of this vector. */
  auto_vec<srfield *> srfields;

  /* The upper bounds to be checked dynamicly and corresponding use stmts.  */
  auto_delete_vec<dco_bound_info> bound_infos;

  /* Record all info related if the current class is an identified closure. */
  dco_closure closure_info;

  /* Back reference to corresponding dco_cond. */
  dco_cond *dc;

  srfield *get_srfield_from_decl (tree fielddecl)
  {
    for (auto srf : srfields)
      if (srf->fielddecl == fielddecl)
	return srf;
    return NULL;
  }

  dco_field_class (srfield *srf) : dc (NULL)
  {
    srfields.safe_push (srf);
    fieldtype = srf->fieldtype;
  }
  ~dco_field_class () {}
};

/* The DCO condition for a specified data type. Multiple vars with the same
   data type can map to the same dco_cond object. */

class dco_cond
{
public:
  /* The old field data type for this condition. */
  tree old_type;

  /* The new field data type for this condition. */
  tree new_type;

  /* The bit width of the new_type if it is a bit field. */
  unsigned bits;

  /* May have multiple fields mapping to this condition, as they have the
     same data type. */
  auto_vec<dco_field *> dco_fields;

  /* Bit mask position for this condition. */
  int bitmask;

  /* The condition variable we want to check. */
  tree cond_var;

  /* The vars to hold the min and max input. */
  tree min_val, max_val;

  /* The constant value we need to check at run-time. */
  tree low_bound, high_bound;

  /* True if we need the boundary check. */
  bool low_bound_check, high_bound_check;

  /* Hold all special constant values for this condition type. */
  auto_vec<HOST_WIDE_INT> special_values;

  /* The type class to which all of dco_fields in this condition belongs. */
  dco_field_class *dfc;

  /* Encode and decode function decls, if there're special values.  */
  tree encode_fn, decode_fn;

  dco_cond (tree old_type)
    : old_type (old_type), new_type (NULL_TREE), bits (0), bitmask (0),
      cond_var (NULL_TREE), min_val (NULL_TREE), max_val (NULL_TREE),
      low_bound (NULL_TREE), high_bound (NULL_TREE), low_bound_check (true),
      high_bound_check (true), dfc (NULL), encode_fn (NULL_TREE),
      decode_fn (NULL_TREE)
  {}
  dco_cond () { dco_cond (NULL_TREE); }
  ~dco_cond () {}
};

/* The field for which we will do DCO optimization. */

class dco_field
{
public:
  /* The old fields to be handled for DCO. */
  tree field;

  /* The new type for caching the field. */
  tree new_type;

  /* The new fielddecl with the new type. */
  tree new_field;

  /* The input var that is read from a file, and assigned to the dco_field. */
  tree input_var;

  /* The ssa for the input_var. */
  tree input_ssa;

  /* The memory base SSA for the pointer DCO field candidate. */
  tree mem_base_ssa;

  /* The condition var descriptor for this field. */
  dco_cond *cond;

  /* This field's max value we can know at compile time. If it is 0, it means
     the max value cannot be determined at compile time.*/
  HOST_WIDE_INT max_value;

  /* The bit width of the field if it is not zero. */
  unsigned bits;

  /* The total number of static reference count. The bigger, the smaller data
     caching sizes for IPA_DCO_DYNAMIC_AGGRESSIVE. */
  unsigned ref_cnt;

  /* The original data field of a shadow field if it is not NULL. */
  srfield *original;

  /* A shadow dco field must have a sscanf dco field counter part. */
  dco_field *sscanf_df;

  /* All init constants of the original srfield. */
  auto_vec<tree> init_consts;

  /* All assignment stmts that need to be optimized as shadow. */
  auto_vec<gimple *> shadow_stmts;

  /* The 1:1 map of shadow_stmts to indicate the current function of a shadow
     stmt belongs to. */
  auto_vec<srfunction *> shadow_stmts_func;

  /* True if current field is for dynamic DCO. */
  bool dynamic;

  /* All analysis result for a pointer dco field. */
  dco_closure *arr_ptr;

  /* To identify different kind of dco fields. */
  DCO_KIND dco_kind;

  /* For dynamic DCO only. */
  dco_field (tree field = NULL_TREE, tree input_var = NULL_TREE,
	     tree input_ssa = NULL_TREE, tree mem_base_ssa = NULL_TREE,
	     DCO_KIND dco_kind = CLOSURE_INT)
    : field (field), new_type (NULL_TREE), new_field (NULL_TREE),
      input_var (input_var), input_ssa (input_ssa), mem_base_ssa (mem_base_ssa),
      cond (0), max_value (0), bits (0), ref_cnt (0), original (0),
      sscanf_df (0), dynamic (true), arr_ptr (NULL), dco_kind (dco_kind)
  {}
  /* For both dynamic and static DCO. */
  dco_field (tree field, HOST_WIDE_INT max_value, srfield *original,
	     bool dynamic, DCO_KIND dco_kind = CLOSURE_INT)
    : field (field), new_type (NULL_TREE), new_field (NULL_TREE),
      mem_base_ssa (NULL_TREE), cond (0), max_value (max_value), bits (0),
      ref_cnt (0), original (original), sscanf_df (0), dynamic (dynamic),
      arr_ptr (NULL), dco_kind (dco_kind)
  {}
  ~dco_field () {}

  unsigned get_bits (void) { return cond ? cond->bits : bits; }
};

/* A hot variable that needs to be cached. */

class dco_data
{
public:
  /* The variable declaration that will be initialzed for data to be cached. */
  tree var;

  /* The upper_bound expr to help data initialization. */
  tree upper_bound;

  /* If dco_data is allocated in start-function, record the ssa_name of
     allocated ptr, we may need this to create dco_refs.  */
  tree ssa_def;

  /* varpool_node for a global dco_data variable. We may need this to search for
     dco_refs.  */
  varpool_node *vnode;

  /* It is to clone the stmt initializing data. */
  gimple *cloned_stmt;

  dco_data (tree var, tree upper_bound, tree ssa_def, varpool_node *vnode)
    : var (var), upper_bound (upper_bound), ssa_def (ssa_def), vnode (vnode)
  {}
  ~dco_data () {}
};

/* A variable that needs to be modified according to the caching data. */

class dco_ref
{
public:
  /* The variable's declaration.  */
  tree var;

  /* "real" type, for void*.  */
  tree orig_type;

  /* dco_data referred by this variable.  */
  dco_data *source;

  /* Number of elements, if this variable is an array.  */
  tree upper_bound;

  /* For array of records, this is the field to be modified.  */
  tree field;

  /* It is to clone the var. */
  tree cloned_var;

  /* It is to clone the stmt initializing data. */
  gimple *cloned_stmt;

  dco_ref (tree var, tree orig_type, dco_data *source, tree upper_bound,
	   tree field)
    : var (var), orig_type (orig_type), source (source),
      upper_bound (upper_bound), field (field)
  {}
  ~dco_ref () {}
};

/* All variants for different dynamic checking condition combinations.  */
class dco_variant
{
public:
  /* The bitmask for dco_conds. Each bit maps to the pos of dco_cond. */
  int bitmask;

  /* New atructure type for caching data. */
  tree new_type;

  /* Condition index var for switch-case */
  tree cond;

  dco_variant () : bitmask (0), new_type (NULL_TREE), cond (NULL_TREE) {}
  dco_variant (tree cond, tree new_type) : new_type (new_type), cond (cond) {}
  dco_variant (tree cond, int bitmask) : bitmask (bitmask), cond (cond) {}
  ~dco_variant () {}
};

typedef enum
{
  /* Dynamic */
  IPA_DCO_DYNAMIC_POS = 0,

  IPA_DCO_DYNAMIC = 1 << IPA_DCO_DYNAMIC_POS,
  IPA_DCO_DYNAMIC_MULT = 1 << (IPA_DCO_DYNAMIC_POS + 1),
  IPA_DCO_DYNAMIC_AGGRESSIVE = 1 << (IPA_DCO_DYNAMIC_POS + 2),
  IPA_DCO_DYNAMIC_SHADOW = 1 << (IPA_DCO_DYNAMIC_POS + 3),
  IPA_DCO_DYNAMIC_BITFIELD = 1 << (IPA_DCO_DYNAMIC_POS + 4),

  /* Static */
  IPA_DCO_STATIC_POS = 8,

  IPA_DCO_STATIC = 1 << IPA_DCO_STATIC_POS,
  IPA_DCO_STATIC_SHADOW = 1 << (IPA_DCO_STATIC_POS + 1),
  IPA_DCO_STATIC_POINTER = 1 << (IPA_DCO_STATIC_POS + 2),
  IPA_DCO_STATIC_BITFIELD = 1 << (IPA_DCO_STATIC_POS + 3),
  IPA_DCO_STATIC_DEAD_FIELD = 1 << (IPA_DCO_STATIC_POS + 4),
} IPA_DCO_TYPE;

/* Do Dynamic-DCO if any of the DYNAMIC flag is set.  */
unsigned IPA_DCO_DYNAMIC_FLAGS = IPA_DCO_DYNAMIC | IPA_DCO_DYNAMIC_MULT
				 | IPA_DCO_DYNAMIC_AGGRESSIVE
				 | IPA_DCO_DYNAMIC_BITFIELD;
/* Do Static-DCO if any of the STATIC flag is set.  */
unsigned IPA_DCO_STATIC_FLAGS
  = IPA_DCO_STATIC | IPA_DCO_STATIC_SHADOW | IPA_DCO_STATIC_BITFIELD;

/* Use to represent current DCO flags, as flag_ipa_dco_aggressive will be reset
   after setting cfun.  */
unsigned flag_cur_dco_aggressive;

#define UNSET_FLAG(flag, bits) flag &= ~(bits);
#define CHECK_FLAG(flag, bits) (flag & (bits))

/* An array index field, and the array is for memory at mem_base_ssa. */

class dco_array_index
{
public:
  tree field;
  tree mem_base_ssa;

  dco_array_index (tree field, tree mem_base_ssa)
    : field (field), mem_base_ssa (mem_base_ssa)
  {}
  ~dco_array_index () {}
};

/* The class to hold dco information. A single info object is only for one
   hot data structure to be cached. */
class dco_info
{
public:
  /* The data type adapt to DCO. */
  srtype *dco_type;

  /* The function with start point.  */
  srfunction *start_srfn;

  /* all dco fields covering both dynamic and static. */
  auto_vec<dco_field *> dco_fields;

  /* The flags to control whether to do dynamic/static DCO.  */
  bool static_dco_p = false;
  bool dynamic_dco_p = false;

  /* Note that dynamic_xxx_dco_fields and static_dco_fields may have overhap.
     Here the dynamic and static means the run-time path differences for DCO.
     A field can be optimized at compile time statically for all cases,
     and it can also be further aggressively optimized at run-time for
     special scenarios with run-time checking enabled. For example, for
     a hot array pointer, we can statically hold it with a 32-bit integer,
     and we can also aggressively use 16-bit integer if only we have run-time
     conditional check. */

  /* Multiple fields of the data struct for different dynamic checking
     conditions. */
  auto_delete_vec<dco_field> dynamic_sscanf_dco_fields;

  /* The fields for dynmaic_shadow, whose original must be in
     dynamic_sscanf_dco_fields. */
  auto_delete_vec<dco_field> dynamic_shadow_dco_fields;

  /* Multiple fields of the data struct for static compression. */
  auto_delete_vec<dco_field> static_dco_fields;

  /* Variants of data type after DCO. The number of dco variants of the
     dco_type should be 2^(len(dco_conds))-1.  */
  auto_delete_vec<dco_variant> dco_variants;

  /* All dco_data vars need to be compressed, which is to help the compression
     code generation. */
  auto_delete_vec<dco_data> dco_data_vec;

  /* All variables to be modified according to compressed data.  */
  auto_delete_vec<dco_ref> dco_refs;

  /* All indivisual dco conditions. */
  auto_delete_vec<dco_cond> dco_conds;

  /* The fields with the same type are in the same element of this vector. */
  auto_delete_vec<dco_field_class> df_class;

  /* The flag to indicate what kind of DCO to do. bit-N is for conds[N]. */
  tree dyn_path;

  /* The fclose statement to help dyn_path generation. */
  gimple *fclose_stmt;

  /* Insert code to calculate min and max after data input. */
  gimple *sscanf_stmt;

  /* The initial variable into which the data read from sscanf is assigned. */
  tree init_var;

  /* The file handler for fopen and fclose. */
  tree fh;

  /* Insert switch (__dyn_path__) stmts after multiple fork points
     in different functions. */
  auto_vec<gimple *> fork_points;

  /* Pass this info from SDCO to DDCO */
  auto_vec<dco_array_index *> *dcoai;

  dco_info (srtype *dco_type)
    : dco_type (dco_type), start_srfn (NULL), dyn_path (NULL_TREE),
      fclose_stmt (NULL), sscanf_stmt (NULL), init_var (NULL_TREE),
      fh (NULL_TREE)
  {}
  dco_info ()
    : dco_type (NULL), start_srfn (NULL), dyn_path (NULL_TREE),
      fclose_stmt (NULL), sscanf_stmt (NULL), init_var (NULL_TREE),
      fh (NULL_TREE)
  {}
  ~dco_info () {}
};

/* Constructor of srfunction. */

srfunction::srfunction (cgraph_node *n)
  : node (n), old (NULL), newnode (NULL), newf (NULL), is_safe_func (false)
{}

/* Add an ARG to the list of arguments for the function. */

void
srfunction::add_arg (srdecl *arg)
{
  args.safe_push (arg);
}

/* Dump the SRFUNCTION to the file FILE.  */

void
srfunction::dump (FILE *file)
{
  if (node)
    {
      fprintf (file, "function : ");
      print_generic_expr (file, node->decl);
      fprintf (file, " with arguments: ");
      for (unsigned i = 0; i < args.length (); i++)
	{
	  if (i == 0)
	    fprintf (file, "\n  ");
	  else
	    fprintf (file, "\n,  ");
	  args[i]->dump (file);
	}

      fprintf (file, "\nuses globals: ");
      for (unsigned i = 0; i < globals.length (); i++)
	{
	  fprintf (file, "\n  ");
	  globals[i]->dump (file);
	}

      fprintf (file, "\ndecls: ");
    }
  else
    fprintf (file, "globals : ");

  for (unsigned i = 0; i < decls.length (); i++)
    {
      fprintf (file, "\n  ");
      decls[i]->dump (file);
    }
}

/* Simple dump the SRFUNCTION to the file FILE; used so it is not recusive.  */

void
srfunction::simple_dump (FILE *file)
{
  print_generic_expr (file, node->decl);
}

/* Constructor of FIELD. */

srfield::srfield (tree field, srtype *base)
  : offset (int_byte_position (field)), fieldtype (TREE_TYPE (field)),
    fielddecl (field), base (base), type (NULL), dynamic_df (0), static_df (0),
    dead_field_p (false)
{
  for (int i = 0; i < MAX_NUM_NEW_TYPES; i++)
    newfield[i] = NULL_TREE;
}

/* Constructor of TYPE. */

srtype::srtype (tree type)
  : type (type), chain_type (false), supported (true), num_of_new_types (0),
    visited (false), dinfo (0)
{
  for (int i = 0; i < MAX_NUM_NEW_TYPES; i++)
    newtype[i] = NULL_TREE;

  for (tree field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
    {
      if (TREE_CODE (field) == FIELD_DECL)
	{
	  srfield *t = new srfield (field, this);
	  fields.safe_push (t);
	}
    }
}

/* Return true if it is a DCO candidate type.  */

bool
srtype::dco_candidate_p ()
{
  TEST (!has_escaped () && supported && fields.length () > 2)
  return true;
}

/* Add FIELD to the list of fields that use this type.  */

void
srtype::add_field_site (srfield *field)
{
  field_sites.safe_push (field);
}

/* Constructor of DECL. */

srdecl::srdecl (srtype *tp, tree decl, int argnum, tree orig_type)
  : type (tp), decl (decl), func (NULL_TREE), argumentnum (argnum),
    visited (false), orig_type (orig_type)
{
  if (TREE_CODE (decl) == SSA_NAME)
    func = current_function_decl;
  else if (!is_global_var (decl))
    func = DECL_CONTEXT (decl);
  for (int i = 0; i < MAX_NUM_NEW_TYPES; i++)
    newdecl[i] = NULL_TREE;
}

/* Find DECL in the function. */

srdecl *
srfunction::find_decl (tree decl)
{
  for (unsigned i = 0; i < decls.length (); i++)
    if (decls[i]->decl == decl)
      return decls[i];
  return NULL;
}

/* Record DECL of the TYPE with argument num ARG. */

srdecl *
srfunction::record_decl (srtype *type, tree decl, int arg, tree orig_type)
{
  /* Search for the decl to see if it is already there.  */
  srdecl *decl1 = find_decl (decl);

  if (decl1)
    {
      /* Added the orig_type information.  */
      if (!decl1->orig_type && orig_type)
	{
	  decl1->orig_type = orig_type;
	}
      return decl1;
    }

  gcc_assert (type);

  orig_type = isptrptr (TREE_TYPE (decl)) ? TREE_TYPE (decl) : orig_type;
  decl1 = new srdecl (type, decl, arg, orig_type);
  decls.safe_push (decl1);
  return decl1;
}

/* Find the field at OFF offset.  */

srfield *
srtype::find_field (unsigned HOST_WIDE_INT off)
{
  unsigned int i;
  srfield *field;

  /* FIXME: handle array/struct field inside the current struct. */
  /* NOTE This does not need to be fixed to handle libquatumn */
  FOR_EACH_VEC_ELT (fields, i, field)
    {
      if (off == field->offset)
	return field;
    }
  return NULL;
}

/* Find the field according to field decl.  */

srfield *
srtype::find_field_by_decl (tree fielddecl)
{
  unsigned int i;
  srfield *field;

  FOR_EACH_VEC_ELT (fields, i, field)
    {
      if (operand_equal_p (fielddecl, field->fielddecl, COMPARE_DECL_FLAGS))
	return field;
    }
  return NULL;
}

/* Add the function FN to the list of functions if it
   is there not already. */

void
srtype::add_function (srfunction *fn)
{
  unsigned decluid;
  unsigned i;
  decluid = DECL_UID (fn->node->decl);

  srfunction *fn1;
  // Search for the decl to see if it is already there.
  FOR_EACH_VEC_ELT (functions, i, fn1)
    {
      if (DECL_UID (fn1->node->decl) == decluid)
	return;
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "Recording new function: %u.\n", decluid);

  functions.safe_push (fn);
}

/* Dump out the type structure to FILE. */

void
srtype::dump (FILE *f)
{
  unsigned int i;
  srfield *field;
  srfunction *fn;

  if (chain_type)
    fprintf (f, "chain decl ");

  fprintf (f, "type : ");
  print_generic_expr (f, type);
  fprintf (f, "(%d) { ", TYPE_UID (type));
  fprintf (f, "\nfields = {\n");
  FOR_EACH_VEC_ELT (fields, i, field)
    {
      field->dump (f);
    }
  fprintf (f, "}\n ");

  fprintf (f, "\nfunctions = {\n");
  FOR_EACH_VEC_ELT (functions, i, fn)
    {
      fn->simple_dump (f);
      fprintf (f, " ");
    }
  fprintf (f, "}\n");
  fprintf (f, "}\n");
}

/* A simplified dump out the type structure to FILE. */

void
srtype::simple_dump (FILE *f)
{
  print_generic_expr (f, type);
  fprintf (f, "(%d)", TYPE_UID (type));
}

/* Reorder fields in descending.

   NEWFIELDS: the first member of the chain with the largest size.
   FIELD: the node to be inserted. */

void
srfield::compress_fields (tree newfields[MAX_NUM_NEW_TYPES],
			  tree newlast[MAX_NUM_NEW_TYPES], tree &field,
			  unsigned cur_idx)
{
  if (newfields[cur_idx] == NULL)
    {
      newfields[cur_idx] = field;
      newlast[cur_idx] = field;
    }
  else
    {
      tree tmp = newfields[cur_idx];
      HOST_WIDE_INT field_bitsize = get_bitsize (field);
      HOST_WIDE_INT tmp_bitsize = get_bitsize (tmp);
      if (field_bitsize > tmp_bitsize)
	{
	  DECL_CHAIN (field) = tmp;
	  newfields[cur_idx] = field;
	}
      else
	{
	  while (DECL_CHAIN (tmp)
		 && (field_bitsize <= get_bitsize (DECL_CHAIN (tmp))))
	    {
	      tmp = DECL_CHAIN (tmp);
	    }

	  /* now tmp size > field size
	     insert field: tmp -> xx ==> tmp -> field -> xx.  */
	  DECL_CHAIN (field) = DECL_CHAIN (tmp); // field -> xx
	  DECL_CHAIN (tmp) = field;		 // tmp -> field
	}
    }
}

/* Create the new dco fields for this field.
   newtype[MAX_NUM_NEW_TYPES]: srtype's member variable,
   newfields[MAX_NUM_NEW_TYPES]: created by create_new_dco_types func,
   newlast[MAX_NUM_NEW_TYPES]: created by create_new_dco_types func.  */

void
srfield::create_new_dco_fields (tree newtype[MAX_NUM_NEW_TYPES],
				tree newfields[MAX_NUM_NEW_TYPES],
				tree newlast[MAX_NUM_NEW_TYPES],
				dco_variant *variant, unsigned cur_idx)
{
  /* newtype, corresponding to newtype[MAX_NUM_NEW_TYPES] in srtype.  */
  tree nt = fieldtype;

  /* For dynamic path, i.e. variant != 0
     (1) dynamic_df will be determined by either variant->bitmask or original
     (2) static_df will always be used
     dynamic_df has high priority over static_df.

     For static path, i.e. variant == 0
     (1) static_df will always be used
     (2) dynamic_df will always not be used.  */

  dco_field *df = 0;
  const char *suffix;
  if (dynamic_df || static_df)
    {
      if (static_df)
	{
	  df = static_df;
	  suffix = ".sdco";
	  if (df->dco_kind == ARRAY_INDEX)
	    suffix = ".sdcoai";
	  if (df->dco_kind == ARRAY_POINTER)
	    suffix = ".sdcoap";
	}

      /* dynamic path */
      if (dynamic_df && variant)
	{
	  /* For dynamic sscanf */
	  if (dynamic_df->cond)
	    {
	      gcc_checking_assert (variant->bitmask != 0);
	      if (dynamic_df->cond->bitmask & variant->bitmask)
		{
		  suffix = ".ddco";
		  df = dynamic_df;
		}
	    }
	  /* For dynamic shadow */
	  else if (dynamic_df->original)
	    {
	      newfield[cur_idx] = NULL_TREE;
	      return;
	    }
	  else
	    gcc_unreachable ();
	}
    }

  tree field = make_node (FIELD_DECL);
  DECL_NAME (field) = DECL_NAME (fielddecl);

  if (df)
    {
      const char *name = IDENTIFIER_POINTER (DECL_NAME (field));
      char *new_name = concat (name, suffix, NULL);
      DECL_NAME (field) = get_identifier (new_name);
      free (new_name);
      df->new_field = field;

      gcc_checking_assert (df->new_type);
      nt = df->new_type;
    }

  /* Common members do not need to reconstruct.
     Otherwise, int* -> int** or void* -> void**.  */
  TREE_TYPE (field) = nt;

  DECL_SOURCE_LOCATION (field) = DECL_SOURCE_LOCATION (fielddecl);
  SET_DECL_ALIGN (field, DECL_ALIGN (fielddecl));
  DECL_USER_ALIGN (field) = DECL_USER_ALIGN (fielddecl);
  TREE_ADDRESSABLE (field) = TREE_ADDRESSABLE (fielddecl);
  DECL_NONADDRESSABLE_P (field) = DECL_NONADDRESSABLE_P (fielddecl);
  TREE_THIS_VOLATILE (field) = TREE_THIS_VOLATILE (fielddecl);
  DECL_CONTEXT (field) = newtype[cur_idx];
  DECL_PACKED (field) = 1;
  DECL_BIT_FIELD (field) = DECL_BIT_FIELD (fielddecl);
  if (DECL_BIT_FIELD (field))
    DECL_SIZE (field) = bitsize_int (TYPE_PRECISION (nt));
  else
    DECL_SIZE (field) = TYPE_SIZE (nt);

  /* Always not align compressed fields. */
  if (df)
    SET_DECL_ALIGN (field, 0);

  /* Set bit field properties. We only generate bitfield when a field
     (1) df->new_type is true, which measn this field has new DCO type
	 candidate.
     (2) df->bits is not 0, which means, this field is slected as a bitfield
	 candidate within a dco_cond, because it is hotter than others. */
  if (df && df->bits)
    {
      unsigned bits = df->get_bits ();
      DECL_BIT_FIELD (field) = 1;
      DECL_SIZE (field) = bitsize_int (bits);
      DECL_NONADDRESSABLE_P (field) = 1;
      /* Build unsigned bitfield integer type.  */
      nt = build_nonstandard_integer_type (bits, 1);
      TREE_TYPE (field) = nt;
      df->new_type = nt;
    }

  compress_fields (newfields, newlast, field, cur_idx);

  /* srfield member variable, which stores the new field decl.  */
  newfield[cur_idx] = field;
}

dco_closure *
srfield::get_closure ()
{
  return &(dfc->closure_info);
}

bool
srfield::ddco_type_change_p ()
{
  dco_cond *cond = dynamic_df->cond;
  tree new_field = newfield[new_type_idx];
  return cond->old_type != TREE_TYPE (new_field);
}

/* Create the new TYPE corresponding to THIS type. */

unsigned
srtype::create_new_dco_types (void)
{
  /* Record the first member of the field chain.  */
  tree newfields[MAX_NUM_NEW_TYPES];
  tree newlast[MAX_NUM_NEW_TYPES];
  num_of_new_types = 0;
  sdco_type_idx = (unsigned) -1;

  if (dinfo->dynamic_dco_p)
    num_of_new_types = dinfo->dco_variants.length ();
  /* Append the static dco type to the new type array.  */
  if (dinfo->static_dco_p)
    sdco_type_idx = num_of_new_types++;

  const char *tname = get_type_name (type);

  for (unsigned i = 0; i < num_of_new_types; i++)
    {
      newfields[i] = NULL_TREE;
      newlast[i] = NULL_TREE;
      newtype[i] = make_node (RECORD_TYPE);

      if (tname)
	{
	  char *name = NULL;
	  if (i == sdco_type_idx)
	    name = concat (tname, ".sdco", NULL);
	  else
	    {
	      char id[10];
	      sprintf (id, "%d", i);
	      name = concat (tname, ".ddco.", id, NULL);
	    }
	  tree name_id = get_identifier (name);
	  tree decl
	    = build_decl (UNKNOWN_LOCATION, TYPE_DECL, name_id, newtype[i]);
	  TYPE_STUB_DECL (newtype[i]) = decl;
	  TYPE_NAME (newtype[i]) = name_id;
	  free (name);
	}
    }

  for (unsigned i = 0; i < num_of_new_types; i++)
    {
      unsigned j;
      srfield *f;
      FOR_EACH_VEC_ELT (fields, j, f)
	{
	  if (f->dead_field_p)
	    continue;
	  dco_variant *dv = i == sdco_type_idx ? NULL : dinfo->dco_variants[i];
	  f->create_new_dco_fields (newtype, newfields, newlast, dv, i);
	}
    }

  /* No reason to warn about these structs since the warning would
     have happened already.  */
  int save_warn_padded = warn_padded;
  warn_padded = 0;

  for (unsigned i = 0; i < num_of_new_types; i++)
    {
      TYPE_FIELDS (newtype[i]) = newfields[i];
      TYPE_NON_ESCAPING_P (newtype[i]) = true;
      layout_type (newtype[i]);
      if (i != sdco_type_idx)
	dinfo->dco_variants[i]->new_type = newtype[i];
    }

  warn_padded = save_warn_padded;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Created %d types:\n", num_of_new_types);
      for (unsigned i = 0; i < num_of_new_types; i++)
	{
	  print_generic_expr (dump_file, newtype[i]);
	  fprintf (dump_file, "(%d)", TYPE_UID (newtype[i]));
	  fprintf (dump_file, "\n");
	}
    }

  return num_of_new_types;
}

/* Create all of the new decls (SSA_NAMES included) for THIS function. */

void
srfunction::create_new_decls (void)
{
  /* If this function has been cloned, we don't need to
     create the new decls. */
  if (newnode)
    return;

  for (unsigned i = 0; i < decls.length (); i++)
    {
      srdecl *decl = decls[i];
      srtype *type = decl->type;
      /* If the type of the decl does not change,
	 then don't create a new decl. */
      if (!type->has_new_type ())
	{
	  decl->newdecl[new_type_idx] = decl->decl;
	  continue;
	}

      /* Handle SSA_NAMEs. */
      if (TREE_CODE (decl->decl) == SSA_NAME)
	{
	  tree newtype1;
	  tree inner = SSA_NAME_VAR (decl->decl);
	  tree newinner = NULL_TREE;

	  newtype1 = reconstruct_complex_type (isptrptr (decls[i]->orig_type)
						 ? decls[i]->orig_type
						 : TREE_TYPE (decls[i]->decl),
					       type->newtype[new_type_idx]);
	  if (inner)
	    {
	      srdecl *in = find_decl (inner);
	      gcc_assert (in);
	      newinner = in->newdecl[new_type_idx];
	    }
	  tree od = decls[i]->decl;
	  /* Create the new ssa names and copy some attributes from the old one.
	   */

	  tree nd = make_ssa_name (newinner ? newinner : newtype1);
	  decl->newdecl[new_type_idx] = nd;
	  /* If the old decl was a default defition, handle it specially. */
	  if (SSA_NAME_IS_DEFAULT_DEF (od))
	    {
	      SSA_NAME_IS_DEFAULT_DEF (nd) = true;
	      SSA_NAME_DEF_STMT (nd) = gimple_build_nop ();

	      /* Set the default definition for the ssaname if needed. */
	      if (inner)
		{
		  gcc_assert (newinner);
		  set_ssa_default_def (cfun, newinner, nd);
		}
	    }
	  SSA_NAME_OCCURS_IN_ABNORMAL_PHI (nd)
	    = SSA_NAME_OCCURS_IN_ABNORMAL_PHI (od);
	  statistics_counter_event (cfun, "Create new ssa_name", 1);
	}
      else if (TREE_CODE (decls[i]->decl) == VAR_DECL)
	{
	  tree orig_var = decl->decl;
	  const char *tname = NULL;
	  if (DECL_NAME (orig_var))
	    tname = IDENTIFIER_POINTER (DECL_NAME (orig_var));
	  tree new_name = NULL;
	  char *name = NULL;
	  char id[10];
	  sprintf (id, "%d", new_type_idx);
	  if (tname)
	    {
	      name = concat (tname, ".dco.", id, NULL);
	      new_name = get_identifier (name);
	      free (name);
	    }
	  tree newtype1
	    = reconstruct_complex_type (TREE_TYPE (orig_var),
					type->newtype[new_type_idx]);
	  decl->newdecl[new_type_idx]
	    = build_decl (DECL_SOURCE_LOCATION (orig_var), VAR_DECL, new_name,
			  newtype1);
	  copy_var_attributes (decl->newdecl[new_type_idx], orig_var);
	  if (!is_global_var (orig_var))
	    add_local_decl (cfun, decl->newdecl[new_type_idx]);
	  else
	    varpool_node::add (decl->newdecl[new_type_idx]);
	  statistics_counter_event (cfun, "Create new var decl", 1);
	}
      /* Paramater decls are already handled in rewrite_dco_paths. */
      else if (TREE_CODE (decls[i]->decl) == PARM_DECL)
	;
      else
	internal_error ("Unhandled declaration type stored");

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Created New decls for ");
	  decls[i]->dump (dump_file);
	  fprintf (dump_file, "\n");
	  print_generic_expr (dump_file, decls[i]->newdecl[new_type_idx]);
	  fprintf (dump_file, "\n");
	  fprintf (dump_file, "\n");
	}
    }
}

/* Dump out the field structure to FILE. */

void
srfield::dump (FILE *f)
{
  fprintf (f, "field (%d) { ", DECL_UID (fielddecl));
  fprintf (f, "base = ");
  base->simple_dump (f);
  fprintf (f, ", offset = " HOST_WIDE_INT_PRINT_DEC, offset);
  fprintf (f, ", type = ");
  print_generic_expr (f, fieldtype);
  fprintf (f, "}\n");
}

/* Dump out the decl structure to FILE. */

void
srdecl::dump (FILE *file)
{
  if (!func)
    fprintf (file, "global ");
  if (argumentnum != -1)
    fprintf (file, "argument(%d) ", argumentnum);
  fprintf (file, "decl: ");
  print_generic_expr (file, decl);
  fprintf (file, " type: ");
  type->simple_dump (file);
}

/* Structure definition for ipa_struct_dco.  */

struct ipa_struct_dco
{
private:
  /* The current srfield set in rewrite_expr.  */
  srfield *cur_srfd;

  struct const_map
  {
    tree var;
    HOST_WIDE_INT hwi;

    const_map (tree var, HOST_WIDE_INT hwi) : var (var), hwi (hwi) {}
    ~const_map () {}
  };
  auto_delete_vec<const_map> global_consts;

public:
  // Constructors
  ipa_struct_dco (void) : done_recording (false) {}

  unsigned execute (auto_vec<dco_array_index *> &dcoai);

  // fields
  auto_delete_vec<srtype> types;
  auto_delete_vec<srfunction> functions;
  srglobal globals;
  hash_set<cgraph_node *> safe_functions;

  bool done_recording;

  void dump_types (FILE *f);
  void dump_newtypes (FILE *f);
  void dump_types_escaped (FILE *f);
  void dump_functions (FILE *f);
  bool record_accesses (void);
  void prune_function (srfunction *);
  void prune_globals (void);
  void prune_escaped_types (void);
  bool create_new_types (dco_info &info);
  srdecl *find_decl (tree);
  void create_new_args (cgraph_node *new_node);

  srdecl *record_var (tree decl, int arg = -1);
  void record_safe_func_with_void_ptr_parm (void);
  srfunction *record_function (cgraph_node *node, srfunction *sfn = NULL);
  srfunction *find_function (cgraph_node *node);
  void record_field_type (tree field, srtype *base_srtype);
  void record_struct_field_types (tree base_type, srtype *base_srtype);
  srtype *record_type (tree type);
  srtype *find_type (tree type);
  void maybe_record_stmt (gimple *);
  void maybe_record_assign (gassign *);
  void maybe_record_allocation_site (cgraph_node *, gimple *);
  bool allocation_stmt_p (gimple *stmt);
  bool types_dco_equal_p (tree type1, tree type2);
  bool types_dco_compatible_p (tree type1, tree type2);
  tree get_allocate_size (tree type, tree decl, tree orig_type, gimple *stmt,
			  bool *error);
  tree get_allocate_size_iterate (tree type, gimple *stmt, tree *ssa_def,
				  bool *error);

  bool rewrite_stmt (gimple *, gimple_stmt_iterator *);
  bool rewrite_assign (gassign *, gimple_stmt_iterator *);
  bool rewrite_allocation_stmt (gcall *stmt, tree decl, tree new_decl,
				tree type, tree orig_type, tree new_type,
				gimple_stmt_iterator *gsi);
  bool rewrite_call (gcall *, gimple_stmt_iterator *);
  bool rewrite_cond (gcond *, gimple_stmt_iterator *ARG_UNUSED);
  bool rewrite_phi (gphi *);
  bool rewrite_expr (tree expr, tree &newexpr,
		     bool ignore_missing_decl = false);
  bool rewrite_lhs_rhs (tree lhs, tree rhs, tree &newlhs, tree &newrhs);
  bool get_type_field (tree expr, tree &base, bool &indirect, srtype *&type,
		       srfield *&field, bool &realpart, bool &imagpart,
		       bool &address, bool should_create = false);
  bool wholeaccess (tree expr, tree base, tree accesstype, srtype *t);

  void check_definition_assign (srdecl *decl, vec<srdecl *> &worklist);
  void check_definition_call (srdecl *decl, vec<srdecl *> &worklist);
  void check_definition (srdecl *decl, vec<srdecl *> &);
  void check_uses (srdecl *decl, vec<srdecl *> &);
  void check_use (srdecl *decl, gimple *stmt, vec<srdecl *> &);
  void check_type_and_push (tree newdecl, srdecl *decl,
			    vec<srdecl *> &worklist);
  void check_other_side (srdecl *decl, tree other, vec<srdecl *> &worklist);

  void find_vars (gimple *stmt);
  void mark_type_unsupported (tree type, gimple *stmt);
  void maybe_record_other_side (tree side, tree other);

  /* All DCO related functions are defined as below. */

  /* Rewrite references of all shadow data. */
  void cleanup_shadow_write (dco_info &info, bool dynamic);
  void insert_shadow_stmt (gimple *stmt, unsigned idx, dco_field *df, tree base,
			   bool dynamic);
  void rewrite_shadow_read (dco_info &info, bool dynamic);

  /* Clone and rewrite functions for static-DCO. */
  void create_new_static_dco_functions (void);
  bool has_rewritten_type (srfunction *f);
  void rewrite_static_dco_funcs (dco_info &info);

  /* Rewrite functions for static-DCO.  */
  unsigned static_dco_transform (dco_info &info);
  /* Clone and rewrite cloned paths for dynamic-DCO. */
  unsigned dynamic_dco_transform (dco_info &info);
  tree create_compress_field_fn (dco_cond *dc, int idx, int decomp);
  tree create_compress_single_fn (dco_info &info, unsigned dco_path_idx,
				  dco_variant *dv);
  bool find_dco_paths (dco_info &);
  void clone_part_func (dco_info &, srfunction *);
  void clone_whole_func (srfunction *);
  void clone_dco_paths (dco_info &);
  void rewrite_dco_paths (dco_info &);
  void rewrite_part_func (srfunction *);
  void rewrite_whole_func (srfunction *);
  void rewrite_block (basic_block);
  void clean_func_after_rewrite (srfunction *);

  /* Dynamic checking code generation. */
  bool create_dco_variants (dco_info &info);
  bool finalize_bitfields (dco_info &info);
  bool finalize_data_caching (dco_info &info);
  bool finalize_static_data_caching (dco_info &info);
  bool finalize_dynamic_data_caching (dco_info &info);
  bool dco_field_p (tree var, const dco_cond *dc);
  bool dco_input_ssa_p (tree var, const dco_cond *dc);
  bool dco_field_load_p (tree var, const dco_cond *dc);
  bool dco_peephole_const_p (tree var, HOST_WIDE_INT &hwi);
  bool dco_global_const_p (tree var, HOST_WIDE_INT &hwi);
  bool dco_operand_equal_p (tree var1, tree var2);
  void check_high_bound (dco_cond *dc, HOST_WIDE_INT hwi);
  bool finalize_boundary (dco_info &info);
  void create_dyn_path (dco_info &info);
  bool gimple_use_dco_type (dco_info &info, gimple *stmt,
			    auto_vec<tree *> &refs);
  void insert_code_calc_dyn_path (dco_info &info);
  void insert_code_compress_data (dco_info &info, edge e);
  void insert_code_switch_data (dco_info &info, edge e);
  bool dco_type_pointer_p (dco_info &info, tree def, int *level);
  tree get_dco_type_pointer_ref (dco_info &info, tree t);
  bool hot_data_continuous_p (dco_info &info);
  void normalize_dco_type_uses (dco_info &info);
  void insert_code_clone_hot_data (dco_info &info);
  bool dco_type_pointer_escape (dco_info &info, gimple *stmt);
  void insert_code_clone_hot_data_pass1_phi (
    dco_info &info, basic_block bb, auto_vec<gimple *> &old_stmts,
    hash_map<gimple *, gimple *> &stmt_map, auto_vec<tree> &old_defs,
    auto_vec<tree> &new_defs);
  gimple *create_new_dco_type_pointer_def (dco_info &info, gimple *stmt,
					   auto_vec<tree> &old_defs,
					   auto_vec<tree> &new_defs,
					   gimple_stmt_iterator &gsi);
  void insert_code_clone_hot_data_pass1 (dco_info &info,
					 auto_vec<gimple *> &old_stmts,
					 hash_map<gimple *, gimple *> &stmt_map,
					 auto_vec<tree> &old_defs,
					 auto_vec<tree> &new_defs);
  void insert_code_clone_hot_data_pass2 (dco_info &info,
					 auto_vec<gimple *> &old_stmts,
					 hash_map<gimple *, gimple *> &stmt_map,
					 auto_vec<tree> &old_defs,
					 auto_vec<tree> &new_defs);
  bool dco_ref_arrary_p (dco_info &info, tree var);
  bool insert_encode_decode_for_clone (gimple *old_stmt, gimple *new_stmt);
  edge insert_code_modify_single_ref (edge e, tree ref, dco_data *data,
				      tree orig_size, tree new_size);
  void add_dynamic_checking (dco_info &info);

  /* DCO analysis utilities. */
  static int input_order_cmp (const void *p, const void *q);
  bool get_base_type (tree var, tree &base, srtype *&t, srfield *&f);
  dco_field *dco_fields_contains (auto_vec<dco_field *> &dfs, tree field);
  bool find_sscanf_dco_fields (dco_info &info);
  bool find_dynamic_dco_fields (dco_info &info);
  bool find_static_dco_fields (dco_info &info);
  bool static_compress_p (dco_info &info, tree field);
  bool find_array_index (dco_info &info);
  void accumulate_dco_field (dco_info &info, tree var);
  void cal_dco_ref_cnt (dco_info &info);
  bool find_sscanf (gimple *stmt, gimple *&sscanf_stmt, gimple *&input,
		    tree &mem_base, DCO_KIND &dco_kind);
  tree find_fh (gimple *sscanf_stmt);
  bool find_dco_cand (dco_info &info);
  bool find_dyn_dco_cand (dco_info &info);
  bool find_mem_base_ssa_array_pointer (dco_info &info, dco_field_class *dfc);
  bool find_mem_base_ssa_array_index (dco_field_class *dfc);
  bool wt_dco_field_only_p (dco_info &info, dco_field_class *dfc, tree ssa_def);
  bool check_closure_int (dco_info &info, dco_field_class *dfc, DCO_KIND kind);
  bool check_closure_array_pointer (dco_info &info, dco_field_class *dfc);
  void collect_closure_rd_change (dco_info &info, dco_field_class *dfc);
  bool check_upper_bounds (dco_info &info);
  void collect_closure_info_static (dco_info &info);
  void collect_closure_info_dynamic (dco_info &info);
  void record_dco_path_info (dco_info &info);
  bool array_pointer_p (gimple *stmt, tree mem_base_ssa, tree &index);
  bool check_var_init (tree var, tree init);
  bool find_hot_access (dco_info &info, auto_vec<dco_field *> &dco_fields);
  bool is_stmt_before_fclose (dco_info &info, gimple *stmt, symtab_node *node);
  bool find_dco_data_single (dco_info &info, tree node, varpool_node *vnode);
  bool find_dco_data (dco_info &info);
  tree get_ptr_decl (tree var);
  bool add_dco_ref (dco_info &info, dco_data *data, tree ref, tree field);
  bool find_dco_refs_iterate (dco_info &info, dco_data *data, tree var,
			      bool loop_back);
  bool find_dco_refs (dco_info &info);
  bool find_fopen_fclose (dco_info &info);
  void classify_dynamic_dco_fields (dco_info &info);
  void find_dead_fields (dco_info &info);
  bool find_data_shadow (dco_info &info, bool dynamic);
  void classify_dco_fields (dco_info &info);
  bool check_unpair_copy (const auto_vec<gimple *> &unpair_stmts,
			  const auto_vec<srfunction *> &unpair_stmts_func,
			  srfield *&srf, auto_vec<tree> &init_consts);
  bool check_init_zero (tree base);
  void record_dcoai (dco_info &info, auto_vec<dco_array_index *> &dcoai);

  /* Leagality check. */
  bool check_dco_data_uses (dco_info &info);
  bool check_dco_data_init (dco_info &info);
};

/* Methods for ipa_struct_dco.  */

/* Dump all of the recorded types to file F. */

void
ipa_struct_dco::dump_types (FILE *f)
{
  unsigned i;
  srtype *type;
  FOR_EACH_VEC_ELT (types, i, type)
    {
      fprintf (f, "======= the %dth type: ======\n", i);
      type->dump (f);
      fprintf (f, "\n");
    }
}

/* Dump all of the created newtypes to file F.  */

void
ipa_struct_dco::dump_newtypes (FILE *f)
{
  unsigned i = 0;
  srtype *type = NULL;
  FOR_EACH_VEC_ELT (types, i, type)
    {
      if (!type->has_new_type ())
	{
	  continue;
	}
      for (unsigned j = 0; j < type->num_of_new_types; j++)
	{
	  fprintf (f, "======= the %dth newtype, ", i);
	  if (j != sdco_type_idx)
	    fprintf (f, "dynamic variant %d: ======\n", j);
	  else
	    fprintf (f, "static: ======\n");

	  fprintf (f, "type : ");
	  print_generic_expr (f, type->newtype[j]);
	  fprintf (f, "(%d) ", TYPE_UID (type->newtype[j]));
	  fprintf (f, "{ ");
	  fprintf (f, "\nfields = {\n");

	  for (tree field = TYPE_FIELDS (TYPE_MAIN_VARIANT (type->newtype[j]));
	       field; field = DECL_CHAIN (field))
	    {
	      fprintf (f, "field (%d) ", DECL_UID (field));
	      print_generic_expr (f, field);
	      fprintf (f, " {");
	      fprintf (f, "type = ");
	      print_generic_expr (f, TREE_TYPE (field));
	      if (DECL_BIT_FIELD (field))
		{
		  fprintf (f, ", bits = %ld", tree_to_uhwi (DECL_SIZE (field)));
		}
	      fprintf (f, "}\n");
	    }
	  fprintf (f, "}\n");
	  fprintf (f, "size : ");
	  print_generic_expr (f, TYPE_SIZE_UNIT (type->newtype[j]));
	  fprintf (f, "\n\n");
	}
    }
}

/* Dump all of the recorded types to file F. */

void
ipa_struct_dco::dump_types_escaped (FILE *f)
{
  unsigned i;
  srtype *type;
  FOR_EACH_VEC_ELT (types, i, type)
    {
      if (type->has_escaped ())
	{
	  type->simple_dump (f);
	  fprintf (f, " has escaped.\n");
	}
    }
  fprintf (f, "\n");
}

/* Dump all of the record functions to file F. */

void
ipa_struct_dco::dump_functions (FILE *f)
{
  unsigned i;
  srfunction *fn;

  globals.dump (f);
  fprintf (f, "\n\n");
  FOR_EACH_VEC_ELT (functions, i, fn)
    {
      fn->dump (f);
      fprintf (f, "\n");
    }
  fprintf (f, "\n\n");
}

/* Find the recorded srtype corresponding to TYPE.  */

srtype *
ipa_struct_dco::find_type (tree type)
{
  unsigned i;
  /* Get the main variant as we are going
     to find that type only. */
  type = TYPE_MAIN_VARIANT (type);

  srtype *type1;
  // Search for the type to see if it is already there.
  FOR_EACH_VEC_ELT (types, i, type1)
    {
      if (types_dco_compatible_p (type1->type, type))
	return type1;
    }
  return NULL;
}
/* Record field type.  */

void
ipa_struct_dco::record_field_type (tree field, srtype *base_srtype)
{
  tree field_type = TREE_TYPE (field);
  /* The uid of the type in the structure is different
     from that outside the structure.  */
  srtype *field_srtype = record_type (inner_type (field_type));
  srfield *field_srfield = base_srtype->find_field (int_byte_position (field));
  /* We might have an variable sized type which we don't set the handle.  */
  if (field_srfield)
    {
      field_srfield->type = field_srtype;
      field_srtype->add_field_site (field_srfield);
    }
}

/* Record structure all field types.  */

void
ipa_struct_dco::record_struct_field_types (tree base_type, srtype *base_srtype)
{
  for (tree field = TYPE_FIELDS (base_type); field; field = DECL_CHAIN (field))
    {
      if (TREE_CODE (field) == FIELD_DECL)
	{
	  tree field_type = TREE_TYPE (field);
	  if (handled_type (field_type))
	    {
	      record_field_type (field, base_srtype);
	    }
	}
    }
}

/* Record TYPE if not already recorded.  */

srtype *
ipa_struct_dco::record_type (tree type)
{
  unsigned typeuid;

  /* Get the main variant as we are going
     to record that type only.  */
  type = TYPE_MAIN_VARIANT (type);
  typeuid = TYPE_UID (type);

  srtype *type1;

  type1 = find_type (type);
  if (type1)
    return type1;

  /* If already done recording just return NULL.  */
  if (done_recording)
    return NULL;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Recording new type: %u.\n", typeuid);
      fprintf (dump_file, "type (%p): ", type);
      print_generic_expr (dump_file, type);
      fprintf (dump_file, ", size: ");
      print_generic_expr (dump_file, TYPE_SIZE_UNIT (type));
      fprintf (dump_file, "\n");
    }

  type1 = new srtype (type);
  types.safe_push (type1);

  record_struct_field_types (type, type1);

  return type1;
}

/* Record var DECL; optionally specify argument number in a function. */

srdecl *
ipa_struct_dco::record_var (tree decl, int arg)
{
  srtype *type;
  srdecl *sd = NULL;

  /* Only the structure type RECORD_TYPE is recorded.
     Therefore, the void* type is filtered out.  */
  if (handled_type (TREE_TYPE (decl)))
    {
      type = record_type (inner_type (TREE_TYPE (decl)));

      if (done_recording && !type)
	return NULL;

      gcc_assert (type);
      if (TREE_CODE (decl) == VAR_DECL && is_global_var (decl))
	sd = globals.record_decl (type, decl, arg);
      else
	{
	  gcc_assert (cur_srfun);
	  sd = cur_srfun->record_decl (type, decl, arg);
	}
    }

  return sd;
}

/* Mark the inner type of TYPE as unsupported. */

void
ipa_struct_dco::mark_type_unsupported (tree type, gimple *stmt)
{
  if (!handled_type (type))
    return;
  srtype *stype = record_type (inner_type (type));
  if (!stype)
    return;

  stype->mark_unsupported (stmt);
}

void
ipa_struct_dco::find_vars (gimple *stmt)
{
  switch (gimple_code (stmt))
    {
    case GIMPLE_ASSIGN:
      if (gimple_assign_rhs_class (stmt) == GIMPLE_SINGLE_RHS
	  || gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR
	  || gimple_assign_rhs_code (stmt) == NOP_EXPR)
	{
	  tree lhs = gimple_assign_lhs (stmt);
	  tree rhs = gimple_assign_rhs1 (stmt);

	  /* Add a safe func mechanism.  */
	  bool l_find = true;
	  bool r_find = true;

	  l_find = !(cur_srfun->is_safe_func && TREE_CODE (lhs) == SSA_NAME
		     && is_from_void_ptr_parm (lhs));
	  r_find = !(cur_srfun->is_safe_func && TREE_CODE (rhs) == SSA_NAME
		     && is_from_void_ptr_parm (rhs));

	  if ((TREE_CODE (lhs) == SSA_NAME) && VOID_POINTER_P (TREE_TYPE (lhs))
	      && handled_type (TREE_TYPE (rhs)) && l_find)
	    {
	      srtype *t = find_type (inner_type (TREE_TYPE (rhs)));
	      srdecl *d = find_decl (lhs);
	      if (!d && t)
		{
		  cur_srfun->record_decl (t, lhs, -1,
					  isptrptr (TREE_TYPE (rhs))
					    ? TREE_TYPE (rhs)
					    : NULL);
		  tree var = SSA_NAME_VAR (lhs);
		  if (var && VOID_POINTER_P (TREE_TYPE (var)))
		    cur_srfun->record_decl (t, var, -1,
					    isptrptr (TREE_TYPE (rhs))
					      ? TREE_TYPE (rhs)
					      : NULL);
		}
	    }
	  /* find void ssa_name such as:
	     void * _1; struct s * _2;
	     _2 = _1 + _3; _1 = calloc (size, num).  */
	  if (TREE_CODE (rhs) == SSA_NAME && VOID_POINTER_P (TREE_TYPE (rhs))
	      && handled_type (TREE_TYPE (lhs)) && r_find)
	    {
	      srtype *t = find_type (inner_type (TREE_TYPE (lhs)));
	      srdecl *d = find_decl (rhs);
	      if (!d && t)
		{
		  tree orig_type = TREE_TYPE (lhs);
		  cur_srfun->record_decl (t, rhs, -1, orig_type);
		  tree var = SSA_NAME_VAR (rhs);
		  if (var && VOID_POINTER_P (TREE_TYPE (var)))
		    cur_srfun->record_decl (t, var, -1, orig_type);
		}
	    }
	}
      else if (gimple_assign_rhs_code (stmt) == LE_EXPR
	       || gimple_assign_rhs_code (stmt) == LT_EXPR
	       || gimple_assign_rhs_code (stmt) == GE_EXPR
	       || gimple_assign_rhs_code (stmt) == GT_EXPR
	       || (gimple_assign_rhs_code (stmt) == POINTER_DIFF_EXPR
		   && types_dco_compatible_p (TYPE_MAIN_VARIANT (TREE_TYPE (
						gimple_assign_rhs1 (stmt))),
					      TYPE_MAIN_VARIANT (TREE_TYPE (
						gimple_assign_rhs2 (stmt))))))
	{
	  break;
	}
      else
	{
	  /* We won't handle these stmts in rewrite phase, mark on the types. */
	  mark_type_unsupported (TREE_TYPE (gimple_assign_lhs (stmt)), stmt);
	  for (unsigned j = 1; j < gimple_num_ops (stmt); ++j)
	    mark_type_unsupported (TREE_TYPE (gimple_op (stmt, j)), stmt);
	}
      break;

    case GIMPLE_RETURN:
    case GIMPLE_CALL:
    case GIMPLE_ASM:
    default:
      break;
    }
}

/* Maybe record access of statement for further analaysis. */

void
ipa_struct_dco::maybe_record_stmt (gimple *stmt)
{
  switch (gimple_code (stmt))
    {
    case GIMPLE_ASSIGN:
      maybe_record_assign (as_a<gassign *> (stmt));
      break;
    case GIMPLE_CALL:
    case GIMPLE_DEBUG:
    case GIMPLE_GOTO:
    case GIMPLE_SWITCH:
      break;
    default:
      break;
    }
}

/* Return TRUE if STMT is an allocation statement that is handled. */

bool
ipa_struct_dco::allocation_stmt_p (gimple *stmt)
{
  return gimple_call_builtin_p (stmt, BUILT_IN_REALLOC)
	 || gimple_call_builtin_p (stmt, BUILT_IN_MALLOC)
	 || gimple_call_builtin_p (stmt, BUILT_IN_CALLOC);
}

/* Returns the allocated size / T size for STMT.  That is the number of
   elements in the array allocated.   */

tree
ipa_struct_dco::get_allocate_size (tree type, tree decl, tree orig_type,
				   gimple *stmt, bool *error)
{
  if (error)
    *error = false;
  if (!allocation_stmt_p (stmt))
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\nNot an allocate statement:\n");
	  print_gimple_stmt (dump_file, stmt, 0);
	  fprintf (dump_file, "\n");
	}
      return NULL;
    }

  tree use_type = type;
  /* Specify the correct size to relax multi-layer pointer.  */
  if (TREE_CODE (decl) == SSA_NAME && orig_type && isptrptr (orig_type))
    use_type = orig_type;

  tree struct_size = TYPE_SIZE_UNIT (use_type);
  tree size = gimple_call_arg (stmt, 0);

  if (gimple_call_builtin_p (stmt, BUILT_IN_REALLOC)
      || gimple_call_builtin_p (stmt, BUILT_IN_ALIGNED_ALLOC))
    size = gimple_call_arg (stmt, 1);
  else if (gimple_call_builtin_p (stmt, BUILT_IN_CALLOC))
    {
      tree arg1;
      arg1 = gimple_call_arg (stmt, 1);
      /* Check that second argument is a constant equal to the size of
	 structure.  */
      if (operand_equal_p (arg1, struct_size, 0))
	return size;
      /* ??? Check that first argument is a constant equal to the size of
	 structure.  */
      /* If the allocated number is equal to the value of struct_size,
	 the value of arg1 is changed to the allocated number.  */
      if (operand_equal_p (size, struct_size, 0))
	return arg1;
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "calloc with unexpected size (should be ");
	  print_generic_expr (dump_file, struct_size);
	  fprintf (dump_file, "): ");
	  print_gimple_stmt (dump_file, stmt, 0);
	}
      SET_ERR_RETURN_NULL (error);
    }

  tree num;
  if (!is_result_of_mult (size, &num, use_type))
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file,
		   "Get number of elements failed (not multiplied by ");
	  print_generic_expr (dump_file, struct_size);
	  fprintf (dump_file, "): ");
	  print_gimple_stmt (dump_file, stmt, 0);
	}
      SET_ERR_RETURN_NULL (error);
    }

  return num;
}

void
ipa_struct_dco::maybe_record_other_side (tree side, tree other)
{
  gcc_assert (TREE_CODE (side) == SSA_NAME || TREE_CODE (side) == ADDR_EXPR);
  srtype *type = NULL;
  if (handled_type (TREE_TYPE (other)))
    type = record_type (inner_type (TREE_TYPE (other)));
  if (!type)
    return;

  if (TREE_CODE (side) == ADDR_EXPR)
    side = TREE_OPERAND (side, 0);
  srdecl *d = find_decl (side);
  if (d)
    return;

  /* MEM[(struct s *)_1].f1 = _2; _2 = calloc (size, num).  */
  if (VOID_POINTER_P (TREE_TYPE (side)) && TREE_CODE (side) == SSA_NAME)
    {
      /* The type is other, the declaration is side.  */
      cur_srfun->record_decl (type, side, -1,
			      isptrptr (TREE_TYPE (other)) ? TREE_TYPE (other)
							   : NULL);
    }
}

/* Record accesses in an assignment statement STMT.  */

void
ipa_struct_dco::maybe_record_assign (gassign *stmt)
{
  if (gimple_clobber_p (stmt)
      || gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR)
    {
      return;
    }
  /* Copies, References, Taking addresses. */
  if (gimple_assign_rhs_class (stmt) == GIMPLE_SINGLE_RHS)
    {
      tree lhs = gimple_assign_lhs (stmt);
      tree rhs = gimple_assign_rhs1 (stmt);
      /* If we have a = &b.c then we need to mark the type of b
	 as escaping as tracking a will be hard.  */
      if (TREE_CODE (rhs) == ADDR_EXPR)
	{
	  tree r = TREE_OPERAND (rhs, 0);
	  if (handled_component_p (r))
	    {
	      return;
	    }
	}
      if ((TREE_CODE (rhs) == SSA_NAME || TREE_CODE (rhs) == ADDR_EXPR))
	maybe_record_other_side (rhs, lhs);
      if (TREE_CODE (lhs) == SSA_NAME)
	maybe_record_other_side (lhs, rhs);
    }
}

bool
check_mem_ref_offset (tree expr, tree *num)
{
  bool ret = false;

  if (TREE_CODE (expr) != MEM_REF)
    {
      return false;
    }

  /* Try to find the structure size.  */
  tree field_off = TREE_OPERAND (expr, 1);
  tree tmp = TREE_OPERAND (expr, 0);
  if (TREE_CODE (tmp) == ADDR_EXPR)
    {
      tmp = TREE_OPERAND (tmp, 0);
    }
  /* Specify the correct size for the multi-layer pointer.  */
  tree struct_type = isptrptr (TREE_TYPE (tmp)) ? TREE_TYPE (tmp)
						: inner_type (TREE_TYPE (tmp));
  ret = is_result_of_mult (field_off, num, struct_type);
  return ret;
}

tree
get_ref_base_and_offset (tree &e, HOST_WIDE_INT &offset, bool &realpart,
			 bool &imagpart, tree &accesstype, tree *num)
{
  offset = 0;
  realpart = false;
  imagpart = false;
  accesstype = NULL_TREE;
  if (TREE_CODE (e) == REALPART_EXPR)
    {
      e = TREE_OPERAND (e, 0);
      realpart = true;
    }
  if (TREE_CODE (e) == IMAGPART_EXPR)
    {
      e = TREE_OPERAND (e, 0);
      imagpart = true;
    }
  tree expr = e;
  while (true)
    {
      switch (TREE_CODE (expr))
	{
	case COMPONENT_REF:
	  {
	    /* x.a = _1; If expr is the lvalue of stmt,
	       then field type is FIELD_DECL - POINTER_TYPE - RECORD_TYPE.  */
	    tree field = TREE_OPERAND (expr, 1);
	    tree field_off = byte_position (field);
	    if (TREE_CODE (field_off) != INTEGER_CST)
	      return NULL;
	    offset += tree_to_shwi (field_off);
	    /* x.a = _1; If expr is the lvalue of stmt,
	       then expr type is VAR_DECL - RECORD_TYPE (fetch x) */
	    expr = TREE_OPERAND (expr, 0);
	    accesstype = NULL;
	    break;
	  }
	case MEM_REF:
	  {
	    /* _2 = MEM[(struct s * *)_1];
	       If expr is the right value of stmt，then field_off type is
	       INTEGER_CST - POINTER_TYPE - POINTER_TYPE - RECORD_TYPE.  */
	    tree field_off = TREE_OPERAND (expr, 1);
	    gcc_assert (TREE_CODE (field_off) == INTEGER_CST);
	    /* So we can mark the types as escaping if different. */
	    accesstype = TREE_TYPE (field_off);
	    if (!check_mem_ref_offset (expr, num))
	      {
		offset += tree_to_uhwi (field_off);
	      }
	    return TREE_OPERAND (expr, 0);
	  }
	default:
	  return expr;
	}
    }
}

/* Helper to create a function declaration together with arguments and result
   declarations.  */

tree
create_new_fn_decl (char *fn_name, int n_args, tree *arg_types,
		    tree return_type)
{
  tree fn_type = build_function_type_array (return_type, n_args, arg_types);
  tree fndecl = build_fn_decl (fn_name, fn_type);
  tree id = get_identifier (fn_name);
  SET_DECL_ASSEMBLER_NAME (fndecl, id);
  DECL_NAME (fndecl) = id;
  DECL_ARTIFICIAL (fndecl) = 1;
  DECL_EXTERNAL (fndecl) = 0;
  DECL_CONTEXT (fndecl) = NULL_TREE;
  DECL_INITIAL (fndecl) = make_node (BLOCK);
  DECL_STATIC_CONSTRUCTOR (fndecl) = 0;

  /* Function result declairation.  */
  tree resdecl
    = build_decl (UNKNOWN_LOCATION, RESULT_DECL, NULL_TREE, return_type);
  DECL_RESULT (fndecl) = resdecl;

  /* Function arguments.  */
  tree prev_arg = NULL_TREE;
  for (int i = 0; i < n_args; i++)
    {
      tree arg_decl
	= build_decl (UNKNOWN_LOCATION, PARM_DECL, NULL, arg_types[i]);
      DECL_ARTIFICIAL (arg_decl) = 1;
      DECL_IGNORED_P (arg_decl) = 1;
      TREE_USED (arg_decl) = 1;
      DECL_CONTEXT (arg_decl) = fndecl;
      DECL_ARG_TYPE (arg_decl) = arg_types[i];
      TREE_READONLY (arg_decl) = 1;
      if (prev_arg)
	TREE_CHAIN (prev_arg) = arg_decl;
      else
	DECL_ARGUMENTS (fndecl) = arg_decl;
      prev_arg = arg_decl;
    }

  return fndecl;
}

/* Return true if EXPR was accessing the whole type T.  */

bool
ipa_struct_dco::wholeaccess (tree expr, tree base, tree accesstype, srtype *t)
{
  if (expr == base)
    return true;

  if (TREE_CODE (expr) == ADDR_EXPR && TREE_OPERAND (expr, 0) == base)
    return true;

  if (!accesstype)
    return false;

  if (!types_dco_compatible_p (TREE_TYPE (expr), TREE_TYPE (accesstype)))
    return false;

  if (!handled_type (TREE_TYPE (expr)))
    return false;

  srtype *other_type = find_type (inner_type (TREE_TYPE (expr)));

  if (t == other_type)
    return true;

  return false;
}

bool
ipa_struct_dco::get_type_field (tree expr, tree &base, bool &indirect,
				srtype *&type, srfield *&field, bool &realpart,
				bool &imagpart, bool &address,
				bool should_create)
{
  tree num = NULL_TREE;
  HOST_WIDE_INT offset;
  tree accesstype;
  address = false;
  bool mark_as_bit_field = false;

  if (TREE_CODE (expr) == BIT_FIELD_REF)
    {
      expr = TREE_OPERAND (expr, 0);
      mark_as_bit_field = true;
    }

  /* ref is classified into two types: COMPONENT_REF or MER_REF.  */
  base = get_ref_base_and_offset (expr, offset, realpart, imagpart, accesstype,
				  &num);

  /* Variable access, unkown type. */
  if (base == NULL)
    return false;

  if (TREE_CODE (base) == ADDR_EXPR)
    {
      address = true;
      base = TREE_OPERAND (base, 0);
    }

  srdecl *d = find_decl (base);
  srtype *t;

  if (integer_zerop (base))
    {
      gcc_assert (!d);
      if (!accesstype)
	return false;
      t = find_type (inner_type (inner_type (accesstype)));
      if (!t && should_create && handled_type (accesstype))
	t = record_type (inner_type (accesstype));
      if (!t)
	return false;
    }
  /* If no such decl is found or orig_type is not added to this decl, then add
     it.  */
  else if (!d && accesstype)
    {
      if (!should_create)
	return false;
      if (!handled_type (accesstype))
	return false;
      t = find_type (inner_type (inner_type (accesstype)));
      if (!t)
	t = record_type (inner_type (accesstype));
      if (!t || t->has_escaped ())
	return false;
      /* _1 = MEM[(struct s * *)a_1].
	 then base a_1: ssa_name  - pointer_type - integer_type.  */

      bool is_int_ptr
	= POINTER_TYPE_P (TREE_TYPE (base))
	  && (TREE_CODE (inner_type (TREE_TYPE (base))) == INTEGER_TYPE);
      if (!(VOID_POINTER_P (TREE_TYPE (base))
	    || (cur_srfun->is_safe_func && is_int_ptr)))
	{
	  return false;
	}
      if (TREE_CODE (base) == SSA_NAME
	  && !(cur_srfun->is_safe_func && is_int_ptr))
	{
	  /* Add a safe func mechanism.  */
	  if (!(cur_srfun->is_safe_func && is_from_void_ptr_parm (base)))
	    {
	      /* Add auxiliary information of the multi-layer pointer
		 type.  */
	      cur_srfun->record_decl (t, base, -1,
				      isptrptr (accesstype) ? accesstype
							    : NULL);
	    }
	}
    }
  else if (!d)
    return false;
  else
    t = d->type;

  if (t->has_escaped () || mark_as_bit_field)
    return false;

  /* Escape the operation of fetching field with pointer offset such as:
   *(&(t->right)) = malloc (0); -> MEM[(struct S * *)_1 + 8B] = malloc (0);
   */
  if ((TREE_CODE (expr) == MEM_REF) && (offset != 0))
    {
      return false;
    }

  if (wholeaccess (expr, base, accesstype, t))
    {
      field = NULL;
      type = t;
      indirect = accesstype != NULL;
      return true;
    }

  srfield *f;
  if ((TREE_CODE (expr) == COMPONENT_REF)
      && DECL_BIT_FIELD (TREE_OPERAND (expr, 1)))
    /* For bitfield, byte_position is not reliable.  */
    f = t->find_field_by_decl (TREE_OPERAND (expr, 1));
  else
    f = t->find_field (offset);
  if (!f)
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\nunkown field\n");
	  print_generic_expr (dump_file, expr);
	  fprintf (dump_file, "\n");
	  print_generic_expr (dump_file, base);
	}
      return false;
    }
  if (!types_dco_compatible_p (f->fieldtype, TREE_TYPE (expr)))
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\nfieldtype = ");
	  print_generic_expr (dump_file, f->fieldtype);
	  fprintf (dump_file, "\naccess type = ");
	  print_generic_expr (dump_file, TREE_TYPE (expr));
	  fprintf (dump_file, "\noriginal expr = ");
	  print_generic_expr (dump_file, expr);
	}
      return false;
    }
  field = f;
  type = t;
  indirect = accesstype != NULL;
  return true;
}

/* Find function corresponding to NODE.  */

srfunction *
ipa_struct_dco::find_function (cgraph_node *node)
{
  for (unsigned i = 0; i < functions.length (); i++)
    if (functions[i]->node == node)
      return functions[i];
  return NULL;
}

void
ipa_struct_dco::check_type_and_push (tree newdecl, srdecl *decl,
				     vec<srdecl *> &worklist)
{
  srtype *type = decl->type;
  if (integer_zerop (newdecl) || TREE_CODE (newdecl) == ADDR_EXPR)
    return;

  srdecl *d = find_decl (newdecl);
  if (!d)
    {
      if (TREE_CODE (newdecl) == INTEGER_CST)
	{
	  return;
	}
      /* If we have a non void* or a decl (which is hard to track),
	 then mark the type as escaping.  */
      if (!VOID_POINTER_P (TREE_TYPE (newdecl)) || DECL_P (newdecl))
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "\nunkown decl: ");
	      print_generic_expr (dump_file, newdecl);
	      fprintf (dump_file, " in type:\n");
	      print_generic_expr (dump_file, TREE_TYPE (newdecl));
	      fprintf (dump_file, "\n");
	    }
	  return;
	}
      /* At this point there should only be unkown void* ssa names. */
      gcc_assert (TREE_CODE (newdecl) == SSA_NAME);
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\nrecording unkown decl: ");
	  print_generic_expr (dump_file, newdecl);
	  fprintf (dump_file, " as type:\n");
	  type->simple_dump (dump_file);
	  fprintf (dump_file, "\n");
	}
      d = cur_srfun->record_decl (type, newdecl, -1);
      worklist.safe_push (d);
      return;
    }

  /* Only add to the worklist if the decl is a SSA_NAME.  */
  if (TREE_CODE (newdecl) == SSA_NAME)
    worklist.safe_push (d);
}

/* Check the definition of gimple assign.  */

void
ipa_struct_dco::check_definition_assign (srdecl *decl, vec<srdecl *> &worklist)
{
  tree ssa_name = decl->decl;
  gimple *stmt = SSA_NAME_DEF_STMT (ssa_name);
  gcc_assert (gimple_code (stmt) == GIMPLE_ASSIGN);
  /* a) if the SSA_NAME is sourced from a pointer plus, record the pointer and
	check to make sure the addition was a multiple of the size.
	check the pointer type too.  */
  tree rhs = gimple_assign_rhs1 (stmt);
  if (gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR)
    {
      if (TREE_CODE (rhs) == SSA_NAME)
	{
	  check_type_and_push (rhs, decl, worklist);
	}
      return;
    }

  if (gimple_assign_rhs_code (stmt) == MAX_EXPR
      || gimple_assign_rhs_code (stmt) == MIN_EXPR
      || gimple_assign_rhs_code (stmt) == BIT_IOR_EXPR
      || gimple_assign_rhs_code (stmt) == BIT_XOR_EXPR
      || gimple_assign_rhs_code (stmt) == BIT_AND_EXPR)
    {
      tree rhs2 = gimple_assign_rhs2 (stmt);
      if (TREE_CODE (rhs) == SSA_NAME)
	{
	  check_type_and_push (rhs, decl, worklist);
	}
      if (TREE_CODE (rhs2) == SSA_NAME)
	{
	  check_type_and_push (rhs2, decl, worklist);
	}
      return;
    }

  /* Casts between pointers and integer are escaping.  */
  if (gimple_assign_cast_p (stmt))
    {
      return;
    }

  /* d) if the name is from a cast/assignment, make sure it is used as
	that type or void*
	i) If void* then push the ssa_name into worklist.  */
  gcc_assert (gimple_assign_single_p (stmt));
  check_other_side (decl, rhs, worklist);
}

/* Check the definition of gimple call.  */

void
ipa_struct_dco::check_definition_call (srdecl *decl, vec<srdecl *> &worklist)
{
  tree ssa_name = decl->decl;
  gimple *stmt = SSA_NAME_DEF_STMT (ssa_name);
  gcc_assert (gimple_code (stmt) == GIMPLE_CALL);

  /* For realloc, check the type of the argument.  */
  if (gimple_call_builtin_p (stmt, BUILT_IN_REALLOC))
    {
      check_type_and_push (gimple_call_arg (stmt, 0), decl, worklist);
    }

  return;
}

/*
  2) Check SSA_NAMEs for non type usages (source or use) (worlist of srdecl)
     a) if the SSA_NAME is sourced from a pointer plus, record the pointer and
	check to make sure the addition was a multiple of the size.
	check the pointer type too.
     b) If the name is sourced from an allocation check the allocation
	i) Add SSA_NAME (void*) to the worklist if allocated from realloc
     c) if the name is from a param, make sure the param type was of the
	original type
     d) if the name is from a cast/assignment, make sure it is used as that
	type or void* i) If void* then push the ssa_name into worklist
*/
void
ipa_struct_dco::check_definition (srdecl *decl, vec<srdecl *> &worklist)
{
  tree ssa_name = decl->decl;

  /* c) if the name is from a param, make sure the param type was
     of the original type */
  if (SSA_NAME_IS_DEFAULT_DEF (ssa_name))
    {
      return;
    }
  gimple *stmt = SSA_NAME_DEF_STMT (ssa_name);

  /*
     b) If the name is sourced from an allocation check the allocation
	i) Add SSA_NAME (void*) to the worklist if allocated from realloc
  */
  if (gimple_code (stmt) == GIMPLE_CALL)
    {
      check_definition_call (decl, worklist);
    }
  /* If the SSA_NAME is sourced from an inline-asm, the type escapes.  */
  if (gimple_code (stmt) == GIMPLE_ASM)
    {
      return;
    }

  /* If the SSA_NAME is sourced from a PHI check add each name to the worklist
     and check to make sure they are used correctly.  */
  if (gimple_code (stmt) == GIMPLE_PHI)
    {
      for (unsigned i = 0; i < gimple_phi_num_args (stmt); i++)
	{
	  check_type_and_push (gimple_phi_arg_def (stmt, i), decl, worklist);
	}
      return;
    }
  if (gimple_code (stmt) == GIMPLE_ASSIGN)
    {
      check_definition_assign (decl, worklist);
    }
}

void
ipa_struct_dco::check_other_side (srdecl *decl, tree other,
				  vec<srdecl *> &worklist)
{
  if (TREE_CODE (other) == SSA_NAME || DECL_P (other)
      || TREE_CODE (other) == INTEGER_CST)
    {
      check_type_and_push (other, decl, worklist);
    }
}

/* VAR is an ssa_name defined by some array + offset.
   1) For global variables, returns declaration of the array.
   2) For arrays locally allocated with recogized functions, returns the
      ssa_name it is assigned with.
   3) Return NULL_TREE if cannot decide.  */

tree
ipa_struct_dco::get_ptr_decl (tree var)
{
  if (TREE_CODE (var) != SSA_NAME)
    return NULL_TREE;
  tree lhs, rhs, base;
  gimple *stmt = SSA_NAME_DEF_STMT (var);
  tree var_type = TREE_TYPE (var);

  if (gimple_code (stmt) == GIMPLE_ASSIGN)
    {
      gassign *assign = as_a<gassign *> (stmt);
      switch (gimple_assign_rhs_class (assign))
	{
	case GIMPLE_TERNARY_RHS:
	  return NULL_TREE;

	case GIMPLE_BINARY_RHS:
	  if (gimple_assign_rhs_code (assign) != POINTER_PLUS_EXPR)
	    return NULL_TREE;
	  lhs = gimple_assign_rhs1 (assign);
	  rhs = gimple_assign_rhs2 (assign);
	  if (types_dco_compatible_p (TREE_TYPE (lhs), var_type)
	      || VOID_POINTER_P (TREE_TYPE (lhs)))
	    return get_ptr_decl (lhs);
	  return NULL_TREE;

	case GIMPLE_UNARY_RHS:
	case GIMPLE_SINGLE_RHS:
	  {
	    rhs = gimple_assign_rhs1 (stmt);
	    if (TREE_CODE (rhs) == SSA_NAME)
	      {
		if (types_dco_compatible_p (TREE_TYPE (rhs), var_type)
		    || VOID_POINTER_P (TREE_TYPE (rhs)))
		  return get_ptr_decl (rhs);
		return NULL_TREE;
	      }
	    else if (TREE_CODE (rhs) == VAR_DECL)
	      return rhs;
	    else if (TREE_CODE (rhs) == COMPONENT_REF)
	      {
		base = TREE_OPERAND (rhs, 0);
		if (DECL_P (base))
		  return rhs;
		return NULL_TREE;
	      }
	    else
	      return NULL_TREE;
	  }
	default:
	  return NULL_TREE;
	}
    }
  else if (gimple_code (stmt) == GIMPLE_CALL)
    {
      if (!allocation_stmt_p (stmt))
	return NULL_TREE;
      return gimple_get_lhs (stmt);
    }
  else if (gimple_code (stmt) == GIMPLE_PHI)
    /* Can be supported (not affecting correctness). */
    return NULL_TREE;
  else
    return NULL_TREE;
}

/* Check if the uses of pointer diff result are supported.  */

void
check_ptr_diff_uses (srdecl *decl, gimple *diff)
{
  tree lhs = gimple_get_lhs (diff);
  srtype *type = decl->type;
  tree otype_size = TYPE_SIZE_UNIT (decl->type->type);

  gimple *use_stmt;
  imm_use_iterator imm_iter;
  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, lhs)
    {
      if (is_gimple_debug (use_stmt))
	continue;
      if (is_gimple_assign (use_stmt)
	  && gimple_assign_rhs_code (use_stmt) == EXACT_DIV_EXPR)
	{
	  if (gimple_assign_rhs1 (use_stmt) != lhs
	      || !tree_int_cst_equal (gimple_assign_rhs2 (use_stmt),
				      otype_size))
	    goto fail_check;
	}
      else if (is_gimple_assign (use_stmt)
	       && gimple_assign_rhs_code (use_stmt) == NOP_EXPR)
	{
	  tree lhs1 = gimple_assign_lhs (use_stmt);
	  gimple *use_stmt1;
	  imm_use_iterator imm_iter1;

	  FOR_EACH_IMM_USE_STMT (use_stmt1, imm_iter1, lhs1)
	    {
	      if (is_gimple_assign (use_stmt1)
		  && gimple_assign_rhs_code (use_stmt1) == POINTER_PLUS_EXPR)
		{
		  tree rhs1 = gimple_assign_rhs1 (use_stmt1);
		  tree type1 = TREE_TYPE (TREE_TYPE (rhs1));
		  if (types_compatible_p (type1, type->type))
		    continue;
		}
	      goto fail_check;
	    }
	}
      else
	goto fail_check;
    }
  return;

fail_check:
  type->mark_unsupported (use_stmt);
}

void
ipa_struct_dco::check_use (srdecl *decl, gimple *stmt, vec<srdecl *> &worklist)
{
  if (gimple_code (stmt) == GIMPLE_RETURN || gimple_code (stmt) == GIMPLE_ASM)
    {
      return;
    }
  /* If the SSA_NAME PHI check and add the src to the worklist and
     check to make sure they are used correctly.  */
  if (gimple_code (stmt) == GIMPLE_PHI)
    {
      check_type_and_push (gimple_phi_result (stmt), decl, worklist);
      return;
    }

  if (gimple_code (stmt) == GIMPLE_COND)
    {
      tree rhs1 = gimple_cond_lhs (stmt);
      tree rhs2 = gimple_cond_rhs (stmt);
      tree orhs = rhs1;
      if (rhs1 == decl->decl)
	orhs = rhs2;
      if (integer_zerop (orhs))
	return;
      check_type_and_push (orhs, decl, worklist);
      return;
    }

  /* Casts between pointers and integer are escaping.  */
  if (gimple_assign_cast_p (stmt))
    {
      return;
    }

  /* We might have a_1 = ptr_2 == ptr_3; */
  if (is_gimple_assign (stmt)
      && TREE_CODE_CLASS (gimple_assign_rhs_code (stmt)) == tcc_comparison)
    {
      tree rhs1 = gimple_assign_rhs1 (stmt);
      tree rhs2 = gimple_assign_rhs2 (stmt);
      tree orhs = rhs1;
      if (rhs1 == decl->decl)
	orhs = rhs2;
      if (integer_zerop (orhs))
	return;
      check_type_and_push (orhs, decl, worklist);
      return;
    }

  if (gimple_assign_single_p (stmt))
    {
      tree lhs = gimple_assign_lhs (stmt);
      tree rhs = gimple_assign_rhs1 (stmt);
      /* Check if we have a_1 = b_2; that a_1 is in the correct type. */
      if (decl->decl == rhs)
	{
	  check_other_side (decl, lhs, worklist);
	  return;
	}
    }

  if (is_gimple_assign (stmt)
      && gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR)
    {
      tree lhs = gimple_assign_lhs (stmt);
      check_other_side (decl, lhs, worklist);
    }

  if (is_gimple_assign (stmt)
      && gimple_assign_rhs_code (stmt) == POINTER_DIFF_EXPR)
    {
      tree rhs1 = gimple_assign_rhs1 (stmt);
      tree rhs2 = gimple_assign_rhs2 (stmt);
      tree other = rhs1 == decl->decl ? rhs2 : rhs1;
      check_other_side (decl, other, worklist);

      /* Check the pointer diff for pointer to type only once.  */
      if (other == rhs2 && !POINTER_TYPE_P (TREE_TYPE (TREE_TYPE (rhs2))))
	check_ptr_diff_uses (decl, stmt);
      return;
    }
}

/*
   2) Check SSA_NAMEs for non type usages (source or use) (worlist of srdecl)
	d) if the name is used in a cast/assignment, make sure it is used as
	   that type or void*
	   i) If void* then push the ssa_name into worklist
	e) if used in conditional check the other side
	   i) If the conditional is non NE/EQ then mark the type as non
	      rejecting
	f) Check if the use in a Pointer PLUS EXPR Is used by mulitplication
	   of its size
  */
void
ipa_struct_dco::check_uses (srdecl *decl, vec<srdecl *> &worklist)
{
  tree ssa_name = decl->decl;
  imm_use_iterator imm_iter;
  use_operand_p use_p;

  FOR_EACH_IMM_USE_FAST (use_p, imm_iter, ssa_name)
    {
      gimple *stmt = USE_STMT (use_p);

      if (is_gimple_debug (stmt))
	continue;

      check_use (decl, stmt, worklist);
    }
}

/* Record function corresponding to NODE. */

srfunction *
ipa_struct_dco::record_function (cgraph_node *node, srfunction *sfn)
{
  function *fn;
  tree parm, var;
  unsigned int i;
  if (!sfn)
    {
      sfn = new srfunction (node);
      functions.safe_push (sfn);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "\nRecording accesses and types from function: %s/%u\n",
	     node->name (), node->order);

  /* Nodes without a body are not interesting.  Especially do not
     visit clones at this point for now - we get duplicate decls
     there for inline clones at least.  */
  if (!node->has_gimple_body_p () || node->inlined_to)
    return sfn;

  fn = DECL_STRUCT_FUNCTION (node->decl);

  if (!fn)
    return sfn;

  cur_srfun = sfn;
  basic_block bb;
  gimple_stmt_iterator si;

  cur_srfun->is_safe_func = safe_functions.contains (node);
  if (dump_file)
    {
      fprintf (dump_file, "\nfunction %s/%u: is_safe_func = %d\n",
	       node->name (), node->order, cur_srfun->is_safe_func);
    }

  /* Record the static chain decl.  */
  if (fn->static_chain_decl)
    {
      srdecl *sd = record_var (fn->static_chain_decl, -2);
      if (sd)
	{
	  /* Specify that this type is used by the static
	     chain so it cannot be split. */
	  sd->type->chain_type = true;
	  sfn->add_arg (sd);
	  sd->type->add_function (sfn);
	}
    }

  /* Record the arguments. */
  for (parm = DECL_ARGUMENTS (node->decl), i = 0; parm;
       parm = DECL_CHAIN (parm), i++)
    {
      srdecl *sd = record_var (parm, i);
      if (sd)
	{
	  sfn->add_arg (sd);
	  sd->type->add_function (sfn);
	}
    }

  /* If the cfg does not exist for the function, don't process the function.  */
  if (!fn->cfg)
    return sfn;

  /* The following order is done for recording stage:
     0) Record all variables/SSA_NAMES that are of struct type
     1) Record MEM_REF/COMPONENT_REFs
	a) Record SSA_NAMEs (void*) and record that as the accessed type.
  */

  SET_CFUN (sfn);

  FOR_EACH_LOCAL_DECL (cfun, i, var)
    {
      if (TREE_CODE (var) != VAR_DECL)
	continue;

      record_var (var);
    }

  for (i = 1; i < num_ssa_names; ++i)
    {
      tree name = ssa_name (i);
      if (!name || has_zero_uses (name) || virtual_operand_p (name))
	continue;

      record_var (name);
    }

  /* Find the variables which are used via MEM_REF and are void* types. */
  FOR_EACH_BB_FN (bb, cfun)
    {
      for (si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	{
	  gimple *stmt = gsi_stmt (si);
	  find_vars (stmt);
	}
    }

  auto_vec<srdecl *> worklist;
  for (unsigned i = 0; i < cur_srfun->decls.length (); i++)
    {
      srdecl *decl = cur_srfun->decls[i];
      if (TREE_CODE (decl->decl) == SSA_NAME)
	{
	  decl->visited = false;
	  worklist.safe_push (decl);
	}
    }

  /*
     2) Check SSA_NAMEs for non type usages (source or use) (worklist of srdecl)
	a) if the SSA_NAME is sourced from a pointer plus, record the pointer
	   and check to make sure the addition was a multiple of the size.
	   check the pointer type too.
	b) If the name is sourced from an allocation check the allocation
	   i) Add SSA_NAME (void*) to the worklist if allocated from realloc
	c) if the name is from a param, make sure the param type was of the
	   original type
	d) if the name is used in a cast/assignment, make sure it is used as
	   that type or void*
	   i) If void* then push the ssa_name into worklist
	e) if used in conditional check the other side
	   i) If the conditional is non NE/EQ then mark the type as non
	      rejecting
	f) Check if the use in a Pointer PLUS EXPR Is used by multiplication of
	   its size
  */

  while (!worklist.is_empty ())
    {
      srdecl *decl = worklist.pop ();
      if (decl->visited)
	continue;
      decl->visited = true;
      check_definition (decl, worklist);
      check_uses (decl, worklist);
    }

  FOR_EACH_BB_FN (bb, cfun)
    {
      for (si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	{
	  gimple *stmt = gsi_stmt (si);
	  maybe_record_stmt (stmt);
	}
    }

  return sfn;
}

const char *
get_func_name (tree decl)
{
  if (!decl || TREE_CODE (decl) != FUNCTION_DECL || !DECL_NAME (decl))
    return NULL;

  tree decl_name = DECL_NAME (decl);
  if (TREE_CODE (decl_name) != IDENTIFIER_NODE)
    return NULL;

  return IDENTIFIER_POINTER (decl_name);
}

/* For a function that contains the void* parameter and passes the structure
   pointer, check whether the function uses the input node safely.
   For these functions, the void* parameter and related ssa_name are not
   recorded in record_function (), and the input structure type is not escaped.
*/

void
ipa_struct_dco::record_safe_func_with_void_ptr_parm ()
{
  cgraph_node *node = NULL;

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    {
      cfun_context ctx (node);

      if (is_safe_func_with_void_ptr_parm (node))
	{
	  safe_functions.add (node);
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    fprintf (dump_file, "\nfunction %s/%u is safe function.\n",
		     node->name (), node->order);
	}
    }
}

/* Record all accesses for all types including global variables. */

bool
ipa_struct_dco::record_accesses (void)
{
  varpool_node *var;
  cgraph_node *cnode;

  /* Record global (non-auto) variables first. */
  FOR_EACH_VARIABLE (var)
    {
      if (!var->real_symbol_p ())
	continue;

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Recording global variable: ");
	  print_generic_expr (dump_file, var->decl);
	  fprintf (dump_file, "\n");
	}
      record_var (var->decl);
    }

  /* Add a safe func mechanism.  */
  record_safe_func_with_void_ptr_parm ();

  cgraph_node **order = XCNEWVEC (cgraph_node *, symtab->cgraph_count);
  int order_pos = ipa_reverse_postorder (order);

  /* Traverse by reverse post order.  The 1st node is main.  */
  for (int i = 0; i < order_pos; i++)
    {
      cnode = order[i];
      if (!cnode->real_symbol_p ())
	continue;

      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "About to inspect %s\n", cnode->name ());

      /* Record accesses inside a function. */
      if (cnode->definition)
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    fprintf (dump_file, "Record function %s\n", cnode->name ());

	  /* TODO: Support an alias node.  */
	  TEST_WITH_MSG (!cnode->alias, "Unhandled CGraph Alias Node");
	  record_function (cnode);
	}
      else
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    fprintf (dump_file, "Record return type from %s\n", cnode->name ());
	}
      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "Finished inspecting %s\n", cnode->name ());
    }
  free (order);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n");
      fprintf (dump_file, "==============================================\n\n");
      fprintf (dump_file, "======== all types (before pruning): ========\n\n");
      dump_types (dump_file);
      fprintf (dump_file, "======= all functions (before pruning): =======\n");
      dump_functions (dump_file);
    }
  /* If record_var () is called later, new types will not be recorded.  */
  done_recording = true;
  return true;
}

/* Prune the decls in function SRFN.  */

void
ipa_struct_dco::prune_function (srfunction *srfn)
{
  /* Prune function arguments of types that escape. */
  for (unsigned i = 0; i < srfn->args.length ();)
    {
      if (srfn->args[i]->type->has_escaped ())
	srfn->args.ordered_remove (i);
      else
	i++;
    }

  /* Prune global variables that the function uses of types that escape. */
  for (unsigned i = 0; i < srfn->globals.length ();)
    {
      if (srfn->globals[i]->type->has_escaped ())
	srfn->globals.ordered_remove (i);
      else
	i++;
    }

  /* Prune variables that the function uses of types that escape. */
  for (unsigned i = 0; i < srfn->decls.length ();)
    {
      srdecl *decl = srfn->decls[i];
      if (decl->type->has_escaped ())
	{
	  srfn->decls.ordered_remove (i);
	  delete decl;
	}
      else
	i++;
    }
}

/* Prune global variables.  */

void
ipa_struct_dco::prune_globals (void)
{
  for (unsigned i = 0; i < globals.decls.length ();)
    {
      srdecl *decl = globals.decls[i];
      if (decl->type->has_escaped ())
	{
	  globals.decls.ordered_remove (i);
	  delete decl;
	}
      else
	i++;
    }
}

/* Prune the escaped types and their decls from what was recorded.  */

void
ipa_struct_dco::prune_escaped_types (void)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "==============================================\n\n");
      fprintf (dump_file, "all types (after prop but before pruning): \n\n");
      dump_types (dump_file);
      fprintf (dump_file, "all functions (after prop but before pruning): \n");
      dump_functions (dump_file);
    }

  if (dump_file)
    dump_types_escaped (dump_file);

  /* Prune the function arguments which escape
     and functions which have no types as arguments. */
  for (unsigned i = 0; i < functions.length (); i++)
    prune_function (functions[i]);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "==============================================\n\n");
      fprintf (dump_file, "========= all types (after pruning): =========\n\n");
      dump_types (dump_file);
      fprintf (dump_file, "======== all functions (after pruning): ========\n");
      dump_functions (dump_file);
    }
}

/* Create a global variable to identify the current dynamic caching type and
   path.  */

void
ipa_struct_dco::create_dyn_path (dco_info &info)
{
  tree name = get_identifier (DYN_PATH);
  tree var = build_decl (BUILTINS_LOCATION, VAR_DECL, name, integer_type_node);

  TREE_PUBLIC (var) = 1;
  TREE_STATIC (var) = 1;
  DECL_IGNORED_P (var) = 1;
  DECL_ARTIFICIAL (var) = 1;
  DECL_INITIAL (var) = integer_zero_node;
  SET_DECL_ASSEMBLER_NAME (var, name);

  varpool_node::finalize_decl (var);
  info.dyn_path = var;
}

char *
append_suffix (const char *s1, unsigned suffix)
{
  char s2[32];
  sprintf (s2, "%u", suffix);
  return concat (s1, s2, NULL);
}

/* dyn_path = (upper_bound <= high_bound) ? dyn_path : 0 */

void
gimplify_upper_bound_check (gimple_stmt_iterator *gsi, tree upper_bound,
			    tree high_bound, tree &dyn_path)
{
  tree dcoai_cond
    = fold_build2 (LE_EXPR, boolean_type_node, upper_bound, high_bound);
  dcoai_cond = build_cond_expr (dcoai_cond, dyn_path, integer_zero_node);
  dyn_path = force_gimple_operand_gsi (gsi, dcoai_cond, true, NULL, false,
				       GSI_CONTINUE_LINKING);
}

static bool
contains_expr_p (auto_vec<tree> &exprs, tree in)
{
  for (auto expr : exprs)
    if (operand_equal_p (in, expr))
      return true;
  return false;
}

/* dyn_path = (expr >= 0 && expr <= high_bound) ? dyn_path : 0 */

void
gimplify_bound_expr_check (gimple_stmt_iterator *gsi, tree expr,
			   tree high_bound, tree &dyn_path)
{
  tree etype = TREE_TYPE (expr);
  tree lo_cond
    = fold_build2 (GE_EXPR, boolean_type_node, expr, integer_zero_node);
  tree up_cond = fold_build2 (LE_EXPR, boolean_type_node, expr,
			      fold_convert (etype, high_bound));
  tree cond_expr
    = fold_build2 (TRUTH_AND_EXPR, boolean_type_node, lo_cond, up_cond);
  tree rhs = build_cond_expr (cond_expr, dyn_path, integer_zero_node);
  dyn_path = force_gimple_operand_gsi (gsi, rhs, true, NULL, false,
				       GSI_CONTINUE_LINKING);
}

/* Insert dynamic checking code to calculate info.dyn_path. */

void
ipa_struct_dco::insert_code_calc_dyn_path (dco_info &info)
{
  unsigned i, j;
  dco_cond *dc;
  dco_field *df;
  tree cmp;
  tree bitmask;
  class loop *loop;
  basic_block bb;
  edge latch_edge, entry_edge;
  gimple *stmt;
  edge_iterator ei;

  bb = gimple_bb (info.sscanf_stmt);
  loop = bb->loop_father;
  latch_edge = loop_latch_edge (loop);
  gcc_checking_assert (loop->num != 0);
  gcc_checking_assert (!info.dco_conds.is_empty ());

  /* Insert code to calculate min and max after input_ssa inside the loop. */
  FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
    {
      /* Use the old type for min and max value, as they will be used to
	 compare with the input ssa, which is with old type. */
      tree ssa_type = TREE_TYPE (dc->dco_fields[0]->input_ssa);
      char *tmp_names[2] = { append_suffix ("_dco_min_cond", i),
			     append_suffix ("_dco_max_cond", i) };
      dc->min_val = make_temp_ssa_name (ssa_type, NULL, tmp_names[0]);
      dc->max_val = make_temp_ssa_name (ssa_type, NULL, tmp_names[1]);

      /* Insert phi for min and max in loop header. */
      gphi *min_phi = create_phi_node (dc->min_val, loop->header);
      gphi *max_phi = create_phi_node (dc->max_val, loop->header);

      /* For the input_ssa of each dco fields, we calculate min and max.
	 Assume all of the dco_fields have been sorted in terms of the
	 position of input_ssa. We should always access an input_ssa in
	 forward direction. This way, all fields' input will be used to
	 update min_val and max_val in order. */
      tree min_val = dc->min_val;
      tree max_val = dc->max_val;
      auto_vec<tree> input_ssa;
      FOR_EACH_VEC_ELT (dc->dco_fields, j, df)
	{
	  /* We handle the same input_ssa only once. */
	  if (input_ssa.contains (df->input_ssa))
	    continue;
	  else
	    input_ssa.safe_push (df->input_ssa);

	  gcc_checking_assert (TREE_TYPE (df->input_ssa) == ssa_type);

	  /* Insert new stmt immediately after input_ssa. */
	  gimple_stmt_iterator input_gsi
	    = gsi_for_stmt (SSA_NAME_DEF_STMT (df->input_ssa));
	  bb = gimple_bb (SSA_NAME_DEF_STMT (df->input_ssa));

	  /* min = (input < min) ? input : min_phi */
	  cmp
	    = fold_build2 (LT_EXPR, boolean_type_node, df->input_ssa, min_val);
	  tree input_min_rhs = build_cond_expr (cmp, df->input_ssa, min_val);
	  min_val = make_temp_ssa_name (ssa_type, NULL, tmp_names[0]);
	  stmt = gimple_build_assign (min_val, input_min_rhs);
	  gsi_insert_after (&input_gsi, stmt, GSI_SAME_STMT);

	  /* max = (input < max) ? input : max_phi */
	  cmp
	    = fold_build2 (GT_EXPR, boolean_type_node, df->input_ssa, max_val);
	  tree input_max_rhs = build_cond_expr (cmp, df->input_ssa, max_val);
	  max_val = make_temp_ssa_name (ssa_type, NULL, tmp_names[1]);
	  stmt = gimple_build_assign (max_val, input_max_rhs);
	  gsi_insert_after (&input_gsi, stmt, GSI_SAME_STMT);
	}
      free (tmp_names[0]);
      free (tmp_names[1]);

      /* Add input_min_rhs and input_max_rhs phis. */
      add_phi_arg (min_phi, min_val, latch_edge, UNKNOWN_LOCATION);
      add_phi_arg (max_phi, max_val, latch_edge, UNKNOWN_LOCATION);
      FOR_EACH_EDGE (entry_edge, ei, loop->header->preds)
	{
	  if (entry_edge == latch_edge)
	    continue;
	  add_phi_arg (min_phi, build_zero_cst (ssa_type), entry_edge,
		       UNKNOWN_LOCATION);
	  add_phi_arg (max_phi, build_zero_cst (ssa_type), entry_edge,
		       UNKNOWN_LOCATION);
	}
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n[DCO] Insert min/max calculation\n");
      dump_bb (dump_file, loop->header, 0, TDF_DETAILS);
      dump_bb (dump_file, bb, 0, TDF_DETAILS);
    }

  gimple_stmt_iterator fclose_gsi = gsi_for_stmt (info.fclose_stmt);

  /* Insert code to calculate dco_cond after fclose. */
  FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
    {
      tree cmp_min = NULL_TREE;
      tree cmp_max = NULL_TREE;
      tree cmp_tmp = NULL_TREE;

      /* min >= low_bound */
      if (dc->low_bound_check)
	cmp_min = fold_build2 (GE_EXPR, boolean_type_node, dc->min_val,
			       dc->low_bound);
      /* max <= high_bound */
      if (dc->high_bound_check)
	cmp_max = fold_build2 (LE_EXPR, boolean_type_node, dc->max_val,
			       dc->high_bound);

      /* ((min >= low_bound) && (max <= high_bound)) */
      if (dc->low_bound_check && dc->high_bound_check)
	cmp_tmp
	  = fold_build2 (TRUTH_AND_EXPR, boolean_type_node, cmp_min, cmp_max);
      else if (dc->low_bound_check)
	cmp_tmp = cmp_min;
      else if (dc->high_bound_check)
	cmp_tmp = cmp_max;
      else
	gcc_unreachable ();

      bitmask = build_int_cst (integer_type_node, dc->bitmask);
      /* cond = ((min >= low_bound) && (max <= high_bound)) ? bitmask : 0 */
      tree cond_rhs = build_cond_expr (cmp_tmp, bitmask, integer_zero_node);
      dc->cond_var
	= force_gimple_operand_gsi (&fclose_gsi, cond_rhs, true, NULL, false,
				    GSI_CONTINUE_LINKING);
    }

  /* dyn_path = conds[0] | conds[1] | ... | conds[N] */
  tree dyn_path = make_temp_ssa_name (integer_type_node, NULL, "");
  gimple *cond_stmt
    = gimple_build_assign (dyn_path, info.dco_conds[0]->cond_var);
  gsi_insert_after (&fclose_gsi, cond_stmt, GSI_SAME_STMT);
  gimple_stmt_iterator cond_gsi = gsi_for_stmt (cond_stmt);
  for (unsigned k = 1; k < info.dco_conds.length (); k++)
    {
      tree temp_ssa = fold_build2 (BIT_IOR_EXPR, integer_type_node, dyn_path,
				   info.dco_conds[k]->cond_var);
      dyn_path = make_temp_ssa_name (integer_type_node, NULL, "");
      cond_stmt = gimple_build_assign (dyn_path, temp_ssa);
      gsi_insert_after (&cond_gsi, cond_stmt, GSI_SAME_STMT);
      cond_gsi = gsi_for_stmt (cond_stmt);
    }

  /* Insert code to check init_const for dynamic_shadow fields */
  auto_vec<tree> shadow_conds;
  FOR_EACH_VEC_ELT (info.dynamic_shadow_dco_fields, i, df)
    {
      gcc_checking_assert (df->sscanf_df);
      gcc_checking_assert (df->sscanf_df->cond);

      if (df->init_consts.is_empty ())
	continue;

      /* Insert new stmt immediately after input_ssa. */
      gimple_stmt_iterator input_gsi
	= gsi_for_stmt (SSA_NAME_DEF_STMT (df->input_ssa));

      /* Insert code to update shadow_valid for each init_const */
      tree shadow_valid = NULL_TREE;
      gphi *shadow_valid_phi = 0;
      tree init_const;
      FOR_EACH_VEC_ELT (df->init_consts, j, init_const)
	{
	  /* Skip a init_const that is in special_values, because the boundary
	     check for dco_cond should have cover that. */
	  if (df->sscanf_df->cond->special_values.contains (
		tree_to_uhwi (init_const)))
	    continue;

	  /* input == init_const */
	  cmp = fold_build2 (EQ_EXPR, boolean_type_node, df->input_ssa,
			     init_const);

	  if (shadow_valid == NULL_TREE)
	    {
	      shadow_valid
		= make_temp_ssa_name (boolean_type_node, NULL, "shadow_valid");
	      shadow_conds.safe_push (shadow_valid);
	      shadow_valid_phi = create_phi_node (shadow_valid, loop->header);
	    }

	  /* shadow_valid = (input == init_const) ? false : shadow_valid */
	  tree cond = build_cond_expr (cmp, boolean_false_node, shadow_valid);
	  shadow_valid
	    = make_temp_ssa_name (boolean_type_node, NULL, "shadow_valid");
	  stmt = gimple_build_assign (shadow_valid, cond);
	  gsi_insert_after (&input_gsi, stmt, GSI_SAME_STMT);
	}

      if (shadow_valid_phi)
	{
	  /* Insert phi for shadow_valid in loop header. */
	  add_phi_arg (shadow_valid_phi, shadow_valid, latch_edge,
		       UNKNOWN_LOCATION);
	  FOR_EACH_EDGE (entry_edge, ei, loop->header->preds)
	    {
	      if (entry_edge == latch_edge)
		continue;
	      add_phi_arg (shadow_valid_phi, boolean_true_node, entry_edge,
			   UNKNOWN_LOCATION);
	    }
	}
    }

  if (!shadow_conds.is_empty ())
    {
      /* shadow_cond = shadow_conds[0] && shadow_conds[1] ... */
      tree shadow_cond
	= make_temp_ssa_name (boolean_type_node, NULL, "shadow_cond");
      cond_stmt = gimple_build_assign (shadow_cond, shadow_conds[0]);
      gsi_insert_after (&cond_gsi, cond_stmt, GSI_SAME_STMT);
      cond_gsi = gsi_for_stmt (cond_stmt);
      for (unsigned k = 1; k < shadow_conds.length (); k++)
	{
	  tree temp_ssa = fold_build2 (TRUTH_AND_EXPR, boolean_type_node,
				       shadow_cond, shadow_conds[k]);
	  shadow_cond
	    = make_temp_ssa_name (integer_type_node, NULL, "shadow_cond");
	  cond_stmt = gimple_build_assign (shadow_cond, temp_ssa);
	  gsi_insert_after (&cond_gsi, cond_stmt, GSI_SAME_STMT);
	  cond_gsi = gsi_for_stmt (cond_stmt);
	}

      /* dyn_path = shadow_cond ? dyn_path : 0 */
      shadow_cond = build_cond_expr (shadow_cond, dyn_path, integer_zero_node);
      dyn_path = force_gimple_operand_gsi (&cond_gsi, shadow_cond, true, NULL,
					   false, GSI_CONTINUE_LINKING);
    }

  /* Check the array upper bound if a dco_cond is for array index. */
  FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
    {
      if (dc->dco_fields[0]->dco_kind == CLOSURE_INT)
	continue;

      dco_array_index *dcoai;
      bool found_dcoai = false;
      unsigned i;
      FOR_EACH_VEC_ELT (*info.dcoai, i, dcoai)
	{
	  if (dc->dco_fields[0]->field == dcoai->field)
	    {
	      found_dcoai = true;
	      break;
	    }
	}
      gcc_checking_assert (found_dcoai);

      /* Get the array size */
      gimple *stmt = SSA_NAME_DEF_STMT (dcoai->mem_base_ssa);
      gcc_checking_assert (gimple_call_builtin_p (stmt, BUILT_IN_CALLOC));
      tree array_size = gimple_call_arg (stmt, 0);

      tree btype = TREE_TYPE (dc->high_bound);
      array_size = unshare_expr_without_location (array_size);
      array_size = gimplify_build1 (&cond_gsi, NOP_EXPR, btype, array_size);
      gimplify_upper_bound_check (&cond_gsi, array_size, dc->high_bound,
				  dyn_path);

      auto_vec<tree> bound_expr_checked;

      /* We check that 1) all upper bounds are less than the high bound and
	 2) upper bound-exprs are all positive and less than the high bound to
	 avoid overlap.  */
      for (auto binfo : dc->dfc->bound_infos)
	{
	  tree upper_bound = NULL_TREE;
	  for (auto expr : binfo->const_exprs)
	    {
	      if (TREE_CODE (expr) != INTEGER_CST)
		expr = unshare_expr_without_location (expr);

	      if (!contains_expr_p (bound_expr_checked, expr))
		{
		  gimplify_bound_expr_check (&cond_gsi, expr, dc->high_bound,
					     dyn_path);
		  bound_expr_checked.safe_push (expr);
		}

	      if (upper_bound == NULL_TREE)
		upper_bound
		  = gimplify_build1 (&cond_gsi, NOP_EXPR, btype, expr);
	      else
		upper_bound
		  = gimplify_build2 (&cond_gsi, PLUS_EXPR, btype, upper_bound,
				     fold_convert (btype, expr));
	    }
	  gimplify_upper_bound_check (&cond_gsi, upper_bound, dc->high_bound,
				      dyn_path);
	}
    }

  /* Store dyn_path to global var. */
  gimple *dyn_path_stmt = gimple_build_assign (info.dyn_path, dyn_path);
  gsi_insert_after (&cond_gsi, dyn_path_stmt, GSI_SAME_STMT);

  bb = gimple_bb (info.fclose_stmt);
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n[DCO] Insert _dyn_path calculation\n");
      dump_bb (dump_file, bb, 0, TDF_DETAILS);
    }
}

/* Search and store basic_blocks that:
   1) can reach STMT (when DIRECTION = 0);
   2) can be reached from STMT (when DIRECTION != 0).
   Return false if DCO cannot be performed.  */

bool
dco_path_info::collect_reachable_bbs (gimple *stmt, int direction)
{
  basic_block start_bb = gimple_bb (stmt);
  if (!start_bb)
    return false;

  /* The start block should not be in a loop.  */
  if (start_bb->loop_father != NULL
      && loop_outer (start_bb->loop_father) != NULL)
    return false;

  edge e;
  basic_block bb;
  edge_iterator ei;
  auto_bitmap visited;
  basic_block stop_bb;
  auto_vec<basic_block> *store_list;

  auto_vec<basic_block> worklist;
  worklist.safe_push (start_bb);
  bool exit_p = false;

  if (direction)
    {
      stop_bb = EXIT_BLOCK_PTR_FOR_FN (cfun);
      store_list = &reach_bbs;
    }
  else
    {
      stop_bb = ENTRY_BLOCK_PTR_FOR_FN (cfun);
      store_list = &pre_bbs;
    }

  do
    {
      bb = worklist.pop ();
      if (!bitmap_set_bit (visited, bb->index))
	continue;

      if (bb != stop_bb)
	store_list->safe_push (bb);
      else
	exit_p = true;

      if (direction)
	FOR_EACH_EDGE (e, ei, bb->succs)
	  worklist.safe_push (e->dest);
      else
	FOR_EACH_EDGE (e, ei, bb->preds)
	  worklist.safe_push (e->src);
    }
  while (!worklist.is_empty ());

  if (!exit_p)
    return false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Found %d blocks in func ", store_list->length ());
      print_generic_expr (dump_file, cfun->decl);
      fprintf (dump_file, " %s:\n",
	       direction ? "to be cloned" : "before start-point");

      for (unsigned i = 0; store_list->iterate (i, &bb); ++i)
	fprintf (dump_file, "%d ", bb->index);

      fprintf (dump_file, "\n\n");
    }

  start_stmt = stmt;
  return true;
}

bool
ipa_struct_dco::find_dco_paths (dco_info &info)
{
  /* Start point function */
  srfunction *srfn = info.start_srfn;
  gimple *start_stmt = info.fclose_stmt;

  do
    {
      /* Already seen.  */
      if (srfn->dco_path.start_stmt)
	return false;

      SET_CFUN (srfn);

      TEST (srfn->dco_path.collect_reachable_bbs (start_stmt, 1));
      TEST (srfn->dco_path.collect_reachable_bbs (start_stmt, 0));

      /* Start at the entry function.  */
      if (srfn == functions[0])
	return true;

      /* The current function should only be called once.  */
      struct cgraph_edge *cs = srfn->node->callers;
      TEST (cs && cs->next_caller == NULL && cs->call_stmt != NULL)

      srfn = find_function (cs->caller);
      start_stmt = cs->call_stmt;
    }
  while (srfn);

  for (auto srfn : functions)
    {
      if (!srfn->partial_clone_p ())
	{
	  cgraph_node *node = srfn->node;
	  TEST_WITH_MSG (node->can_change_signature
			   && tree_versionable_function_p (node->decl)
			   && opt_for_fn (node->decl, optimize)
			   && !node->comdat_local_p ()
			   && node->get_availability () >= AVAIL_AVAILABLE,
			 "find DCO paths")
	}
    }

  return false;
}

/* Generate a gimple conditional statement as OP1 CODE OP2, and insert it as
   the last stmt of BB.  */

inline gcond *
build_cond_after_bb (basic_block bb, tree op1, enum tree_code code, tree op2)
{
  gimple_stmt_iterator gsi = gsi_last_bb (bb);
  gcond *cond = gimple_build_cond (code, op1, op2, NULL_TREE, NULL_TREE);

  gsi_insert_after (&gsi, cond, GSI_NEW_STMT);
  return cond;
}

inline void
append_to_block (basic_block bb, gimple *stmt)
{
  gimple_stmt_iterator gsi = gsi_last_bb (bb);

  gcc_checking_assert (gimple_code (stmt) != GIMPLE_PHI);
  gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);
}

/* start_bb:        switch(dyn_path)
		  /        |        \
	     default;    case 1;   case 2;  ... case max;
		/          |          \
	    origin-bbs   clone-bbs1  clone-bbs2  ...
 */
void
ipa_struct_dco::clone_part_func (dco_info &info, srfunction *srfn)
{
  calculate_dominance_info (CDI_DOMINATORS);

  dco_path_info &path = srfn->dco_path;
  auto_vec<basic_block> &reach_bbs = path.reach_bbs;
  gimple *start_stmt = path.start_stmt;
  basic_block prior_bb = reach_bbs[0];

  gcc_checking_assert (prior_bb == gimple_bb (start_stmt));
  edge next_e = split_block (prior_bb, start_stmt);
  reach_bbs[0] = next_e->dest;

  unsigned n = reach_bbs.length ();
  basic_block *origin_bbs = XNEWVEC (basic_block, n);
  unsigned i;
  basic_block bb;

  FOR_EACH_VEC_ELT (reach_bbs, i, bb)
    origin_bbs[i] = bb;

  auto_vec<basic_block *> &clone_list = path.cloned_reach_bbs;

  /* 1. Clone blocks reachable from start point.  */
  for (unsigned i = 0; i < num_new_paths; i++)
    {
      initialize_original_copy_tables ();
      basic_block *cloned_bbs = XNEWVEC (basic_block, n);

      copy_bbs (origin_bbs, n, cloned_bbs, NULL, 0, NULL, prior_bb->loop_father,
		prior_bb, true);

      /* Add phis for edges from copied bbs.  */
      add_phi_args_after_copy (cloned_bbs, n, NULL);
      free_original_copy_tables ();

      clone_list.safe_push (cloned_bbs);
    }

  /* 2. Add if-else on _dyn_path.  */
  for (unsigned i = 0; i < num_new_paths; i++)
    {
      basic_block prior_bb = split_edge (next_e);
      tree opt_var = make_ssa_name (integer_type_node);
      append_to_block (prior_bb, gimple_build_assign (opt_var, info.dyn_path));

      tree cond_var
	= build_int_cst (integer_type_node, info.dco_variants[i]->bitmask);
      append_to_block (prior_bb, gimple_build_cond (EQ_EXPR, opt_var, cond_var,
						    NULL_TREE, NULL_TREE));

      next_e = single_succ_edge (prior_bb);
      next_e->flags = (next_e->flags & ~EDGE_FALLTHRU) | EDGE_FALSE_VALUE;

      make_edge (prior_bb, clone_list[i][0], EDGE_TRUE_VALUE);
    }

  /* Necessary for visiting call stmts.  */
  cgraph_edge::rebuild_edges ();

  free (origin_bbs);
  free_dominance_info (CDI_DOMINATORS);

  if (loops_state_satisfies_p (LOOPS_NEED_FIXUP))
    {
      calculate_dominance_info (CDI_DOMINATORS);
      fix_loop_structure (NULL);
    }

  update_ssa (TODO_update_ssa);
}

void
ipa_struct_dco::clone_whole_func (srfunction *srfn)
{
  cgraph_node *new_node;
  cgraph_node *node = srfn->node;
  auto_delete_vec<srfunction> &cloned_funcs = srfn->dco_path.cloned_funcs;

  for (unsigned i = 0; i < num_new_paths; i++)
    {
      statistics_counter_event (NULL, "Create new function", 1);
      new_node = node->create_version_clone_with_body (vNULL, NULL, NULL, NULL,
						       NULL, "dco");
      new_node->can_change_signature = node->can_change_signature;
      new_node->make_local ();

      srfunction *srfn1 = new srfunction (new_node);
      if (srfn->is_safe_func)
	{
	  safe_functions.add (srfn1->node);
	  srfn1->is_safe_func = true;
	}
      cloned_funcs.safe_push (srfn1);
    }
}

void
ipa_struct_dco::clone_dco_paths (dco_info &info)
{
  push_dump_file save (NULL, TDF_NONE);
  unsigned i;
  srfunction *srfn;

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      if (srfn->partial_clone_p ())
	clone_part_func (info, srfn);
      else
	clone_whole_func (srfn);
    }
}

class closure_helper
{
private:
  /* The unique id for assign stmts used in collecting closure info.  */
  int uid;
  dco_closure *cinfo;

  auto_bitmap bm_rd_ch;
  auto_bitmap bm_wt_ch;
  auto_bitmap bm_rd_unch;
  auto_bitmap bm_wt_unch;

public:
  closure_helper (dco_closure *cinfo) : uid (0), cinfo (cinfo) {}

  void record_orig_rd_wt (basic_block bb)
  {
    for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
	 gsi_next (&si))
      {
	gimple *stmt = gsi_stmt (si);
	if (!is_gimple_assign (stmt))
	  continue;

	uid++;

	if (cinfo->rd_change_p (stmt))
	  bitmap_set_bit (bm_rd_ch, uid);
	else if (cinfo->wt_change_p (stmt))
	  bitmap_set_bit (bm_wt_ch, uid);
	else if (cinfo->rd_unchange_p (stmt))
	  bitmap_set_bit (bm_rd_unch, uid);
	else if (cinfo->wt_unchange_p (stmt))
	  bitmap_set_bit (bm_wt_unch, uid);
      }
  }

  void add_cloned_rd_wt (basic_block bb)
  {
    for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
	 gsi_next (&si))
      {
	gimple *stmt = gsi_stmt (si);
	if (!is_gimple_assign (stmt))
	  continue;

	uid++;

	if (bitmap_bit_p (bm_rd_ch, uid))
	  cinfo->add_rd_change (stmt);
	else if (bitmap_bit_p (bm_wt_ch, uid))
	  cinfo->add_wt_change (stmt);
	else if (bitmap_bit_p (bm_rd_unch, uid))
	  cinfo->add_rd_unchange (stmt);
	else if (bitmap_bit_p (bm_wt_unch, uid))
	  cinfo->add_wt_unchange (stmt);
      }
  }

  void reset_uid () { uid = 0; }
};

/* Collect closure info for partially cloned function SRFN in DDCO.  */

void
collect_closure_info_partial (srfunction *srfn, dco_closure *cinfo)
{
  unsigned i;
  basic_block bb;
  closure_helper helper (cinfo);

  FOR_EACH_VEC_ELT (srfn->dco_path.reach_bbs, i, bb)
    helper.record_orig_rd_wt (bb);

  for (unsigned i = 0; i < num_new_paths; i++)
    {
      helper.reset_uid ();
      unsigned len = srfn->dco_path.reach_bbs.length ();
      basic_block *cloned_bbs = srfn->dco_path.cloned_reach_bbs[i];

      for (unsigned j = 0; j < len; j++)
	helper.add_cloned_rd_wt (cloned_bbs[j]);
    }
}

/* Collect closure info for wholely cloned function SRFN in DDCO.  */

void
collect_closure_info_whole (srfunction *srfn, dco_closure *cinfo)
{
  unsigned i;
  basic_block bb;
  srfunction *cloned_srfn;
  closure_helper helper (cinfo);

  FOR_EACH_BB_FN (bb, srfn->get_sturct_func ())
    helper.record_orig_rd_wt (bb);

  FOR_EACH_VEC_ELT (srfn->dco_path.cloned_funcs, i, cloned_srfn)
    {
      helper.reset_uid ();
      FOR_EACH_BB_FN (bb, cloned_srfn->get_sturct_func ())
	helper.add_cloned_rd_wt (bb);
    }
}

/* Collect the closure info for all dynamic-DCO cloned paths.  */

void
ipa_struct_dco::collect_closure_info_dynamic (dco_info &info)
{
  unsigned i, j;
  srfunction *srfn;
  dco_cond *dc;

  FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
    {
      dco_field_class *dfc = dc->dfc;
      dco_closure *closure_info = &(dfc->closure_info);
      if (dc->dco_fields[0]->dco_kind == CLOSURE_INT)
	{
	  FOR_EACH_VEC_ELT (functions, j, srfn)
	    {
	      if (srfn->partial_clone_p ())
		collect_closure_info_partial (srfn, closure_info);
	      else
		collect_closure_info_whole (srfn, closure_info);
	    }

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    closure_info->dump ();
	}
    }
}

/* Collect the closure info for all static-DCO cloned functions.  */

void
ipa_struct_dco::collect_closure_info_static (dco_info &info)
{
  unsigned i, j;
  srfunction *srfn;
  dco_field_class *dfc;

  FOR_EACH_VEC_ELT (info.df_class, i, dfc)
    {
      srfield *srfd = dfc->srfields[0];
      if (srfd->static_df && srfd->static_df->arr_ptr)
	{
	  dco_closure *closure_info = srfd->static_df->arr_ptr;
	  FOR_EACH_VEC_ELT (functions, j, srfn)
	    {
	      if (!srfn->newf)
		continue;

	      closure_helper helper (closure_info);
	      basic_block bb;
	      FOR_EACH_BB_FN (bb, srfn->get_sturct_func ())
		helper.record_orig_rd_wt (bb);

	      helper.reset_uid ();
	      FOR_EACH_BB_FN (bb, srfn->newf->get_sturct_func ())
		helper.add_cloned_rd_wt (bb);
	    }

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    closure_info->dump ();
	}
    }
}

void
ipa_struct_dco::record_dco_path_info (dco_info &info)
{
  unsigned i;
  srfunction *srfn;

  /* 1. record accesse info for cloned stmts.  */

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      push_dump_file save (NULL, TDF_NONE);

      if (srfn->partial_clone_p ())
	record_function (srfn->node, srfn);
      else
	{
	  for (new_type_idx = 0; new_type_idx < num_new_paths; new_type_idx++)
	    {
	      srfunction *cloned_srfn
		= srfn->dco_path.cloned_funcs[new_type_idx];
	      record_function (cloned_srfn->node, cloned_srfn);
	      prune_function (cloned_srfn);
	    }
	}
    }

  prune_globals ();
  gcc_checking_assert (!info.dco_type->has_escaped ());

  /* 2. collect closure info for cloned paths.  */
  collect_closure_info_dynamic (info);
}

static void
release_srdecl_ssa_name (srdecl *srd)
{
  if (!srd->has_new_decl ())
    return;

  tree ssa_name = NULL_TREE;
  if (srd->argumentnum >= 0)
    ssa_name = ssa_default_def (cfun, srd->decl);
  else if (TREE_CODE (srd->decl) == SSA_NAME)
    ssa_name = srd->decl;

  if (ssa_name && num_imm_uses (ssa_name) == 0)
    release_ssa_name (ssa_name);
}

void
ipa_struct_dco::clean_func_after_rewrite (srfunction *srfn)
{
  unsigned i;
  tree ssa_name;
  srdecl *srd;

  if (static_dco_trans_p () || !srfn->partial_clone_p ())
    {
      FOR_EACH_VEC_ELT (srfn->args, i, srd)
	release_srdecl_ssa_name (srd);
      FOR_EACH_VEC_ELT (srfn->decls, i, srd)
	release_srdecl_ssa_name (srd);
    }
  else if (srfn->partial_clone_p ())
    {
      new_type_idx = 0;
      FOR_EACH_VEC_ELT (srfn->decls, i, srd)
	release_srdecl_ssa_name (srd);
    }

  {
    push_dump_file save (NULL, TDF_NONE);

    update_ssa (TODO_update_ssa_only_virtuals);

    FOR_EACH_SSA_NAME (i, ssa_name, cfun)
      {
	if (SSA_NAME_IN_FREE_LIST (ssa_name))
	  continue;

	gimple *stmt = SSA_NAME_DEF_STMT (ssa_name);

	if (!stmt || (!SSA_NAME_IS_DEFAULT_DEF (ssa_name) && !gimple_bb (stmt)))
	  release_ssa_name (ssa_name);
      }

    if (flag_tree_pta)
      compute_may_aliases ();

    remove_unused_locals ();
    cgraph_edge::rebuild_edges ();
    free_dominance_info (CDI_DOMINATORS);
  }

  if (dump_file)
    {
      fprintf (dump_file, "\n[DCO TRANS] ");
      fprintf (dump_file, "After rewrite: %s\n", srfn->node->name ());
      dump_function_to_file (current_function_decl, dump_file,
			     dump_flags | TDF_VOPS);
      fprintf (dump_file, "\n\n");
    }
}

void
ipa_struct_dco::rewrite_block (basic_block bb)
{
  for (gphi_iterator si = gsi_start_phis (bb); !gsi_end_p (si);)
    {
      if (rewrite_phi (si.phi ()))
	si = gsi_start_phis (bb);
      else
	gsi_next (&si);
    }

  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);)
    {
      gimple *stmt = gsi_stmt (si);
      if (rewrite_stmt (stmt, &si))
	gsi_remove (&si, true);
      else
	gsi_next (&si);
    }

  /* Debug statements need to happen after all other statements
     have changed. */
  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);)
    {
      gimple *stmt = gsi_stmt (si);
      if (gimple_code (stmt) == GIMPLE_DEBUG)
	gsi_remove (&si, true);
      else
	gsi_next (&si);
    }
}

void
ipa_struct_dco::rewrite_part_func (srfunction *srfn)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n[DCO TRANS] Before rewrite: %s (%dth PATH)\n",
	       srfn->node->name (), new_type_idx);
      dump_function_to_file (current_function_decl, dump_file,
			     dump_flags | TDF_VOPS);
      fprintf (dump_file, "\n\n[DCO TRANS] Start to rewrite: %s (%dth PATH)\n",
	       srfn->node->name (), new_type_idx);
      fprintf (dump_file, "\n\n");
    }

  srfn->create_new_decls ();

  dco_path_info &dco_path = srfn->dco_path;
  unsigned len = dco_path.reach_bbs.length ();

  /* Rewrite each related stmts in the current path.  */
  basic_block *cloned_bbs = dco_path.cloned_reach_bbs[new_type_idx];
  for (unsigned i = 0; i < len; i++)
    rewrite_block (cloned_bbs[i]);
}

void
ipa_struct_dco::rewrite_whole_func (srfunction *srfn)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n[DCO TRANS] Before rewrite: %s\n\n",
	       srfn->node->name ());
      dump_function_to_file (current_function_decl, dump_file,
			     dump_flags | TDF_VOPS);
      fprintf (dump_file, "\n[DCO TRANS] Start to rewrite: %s\n\n",
	       srfn->node->name ());
    }

  create_new_args (srfn->node);

  srfn->create_new_decls ();

  basic_block bb;
  FOR_EACH_BB_FN (bb, cfun)
    rewrite_block (bb);
}

/* Create new function clones for the cases where the arguments
   need to be changed.  */

void
ipa_struct_dco::create_new_static_dco_functions (void)
{
  for (unsigned i = 0; i < functions.length (); i++)
    {
      srfunction *f = functions[i];
      bool anyargchanges = false;
      cgraph_node *new_node;
      cgraph_node *node = f->node;
      int newargs = 0;
      if (f->old)
	continue;

      if (f->args.length () == 0)
	continue;

      for (unsigned j = 0; j < f->args.length (); j++)
	{
	  srdecl *d = f->args[j];
	  srtype *t = d->type;
	  if (t->has_new_type ())
	    {
	      newargs += t->newtype[1] != NULL;
	      anyargchanges = true;
	    }
	}
      if (!anyargchanges)
	continue;

      if (dump_file)
	{
	  fprintf (dump_file, "Creating a clone of function: ");
	  f->simple_dump (dump_file);
	  fprintf (dump_file, "\n");
	}
      statistics_counter_event (NULL, "Create new function", 1);
      new_node = node->create_version_clone_with_body (vNULL, NULL, NULL, NULL,
						       NULL, "sdco");
      new_node->can_change_signature = node->can_change_signature;
      new_node->make_local ();
      f->newnode = new_node;
      srfunction *n = record_function (new_node);
      SET_CFUN (cur_srfun);
      n->old = f;
      f->newf = n;
      /* Create New arguments. */
      create_new_args (new_node);
    }
}

/* Does the function F uses any decl which has changed. */

bool
ipa_struct_dco::has_rewritten_type (srfunction *f)
{
  for (unsigned i = 0; i < f->decls.length (); i++)
    {
      srdecl *d = f->decls[i];
      if (d->newdecl[0] != d->decl)
	return true;
    }

  for (unsigned i = 0; i < f->globals.length (); i++)
    {
      srdecl *d = f->globals[i];
      if (d->newdecl[0] != d->decl)
	return true;
    }
  return false;
}

void
ipa_struct_dco::rewrite_static_dco_funcs (dco_info &info ATTRIBUTE_UNUSED)
{
  new_type_idx = sdco_type_idx;
  create_new_static_dco_functions ();
  prune_escaped_types ();
  collect_closure_info_static (info);

  globals.create_new_decls ();

  unsigned i;
  srfunction *srfn;
  basic_block bb;

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      if (srfn->newnode)
	continue;

      /* Function uses no rewriten types so don't cause a rewrite. */
      if (!has_rewritten_type (srfn))
	continue;

      SET_CFUN (srfn);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\n[DCO TRANS] Before rewrite: %dth_%s\n", i,
		   srfn->node->name ());
	  dump_function_to_file (current_function_decl, dump_file,
				 dump_flags | TDF_VOPS);
	  fprintf (dump_file, "\n[DCO TRANS] Start to rewrite: %dth_%s\n", i,
		   srfn->node->name ());
	}

      functions[i]->create_new_decls ();

      FOR_EACH_BB_FN (bb, cfun)
	rewrite_block (bb);

      clean_func_after_rewrite (srfn);
    }
}

/* Rewrite functions either partially or wholely.  */

void
ipa_struct_dco::rewrite_dco_paths (dco_info &info)
{
  record_dco_path_info (info);

  unsigned i;
  srfunction *srfn;

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      if (srfn->partial_clone_p ())
	{
	  SET_CFUN (srfn);

	  /* 2.1 rewrite the original function for each path.  */
	  for (new_type_idx = 0; new_type_idx < num_new_paths; new_type_idx++)
	    rewrite_part_func (srfn);

	  new_type_idx = 0;
	  clean_func_after_rewrite (srfn);
	}
      else
	{
	  /* 2.2 rewrite the cloned function for each path.  */
	  FOR_EACH_VEC_ELT (srfn->dco_path.cloned_funcs, new_type_idx,
			    cur_srfun)
	    {
	      SET_CFUN (cur_srfun);

	      rewrite_whole_func (cur_srfun);
	      clean_func_after_rewrite (cur_srfun);
	    }
	}
    }
}

/* Create all new types we want to create for the specific DCO INFO. */

bool
ipa_struct_dco::create_new_types (dco_info &info)
{
  unsigned newtypes = 0;
  srfield *srf;
  unsigned i;

  /* Scan all all srfields in dco_type to mark dco_field. */
  FOR_EACH_VEC_ELT (info.dco_type->fields, i, srf)
    {
      dco_field *df;
      unsigned j;
      FOR_EACH_VEC_ELT (info.dco_fields, j, df)
	if (srf->fielddecl == df->field)
	  {
	    if (df->dynamic)
	      srf->dynamic_df = df;
	    else
	      srf->static_df = df;
	    break;
	  }
    }

  TEST (newtypes = info.dco_type->create_new_dco_types ())
  TEST (newtypes <= MAX_NUM_NEW_TYPES)

  for (unsigned i = 0; i < newtypes; i++)
    layout_type (info.dco_type->newtype[i]);

  if (dump_file)
    {
      fprintf (dump_file, "=========== all created newtypes: ===========\n\n");
      dump_newtypes (dump_file);
    }

  return true;
}

/* Create the new arguments for the function corresponding to NODE. */

void
ipa_struct_dco::create_new_args (cgraph_node *new_node)
{
  tree decl = new_node->decl;
  auto_vec<tree> params;
  push_function_arg_decls (&params, decl);
  vec<ipa_adjusted_param, va_gc> *adjs = NULL;
  vec_safe_reserve (adjs, params.length ());
  for (unsigned i = 0; i < params.length (); i++)
    {
      struct ipa_adjusted_param adj;
      tree parm = params[i];
      memset (&adj, 0, sizeof (adj));
      adj.base_index = i;
      adj.prev_clone_index = i;
      srtype *t = find_type (inner_type (TREE_TYPE (parm)));
      if (!t || t->has_escaped () || !t->has_new_type ())
	{
	  adj.op = IPA_PARAM_OP_COPY;
	  vec_safe_push (adjs, adj);
	  continue;
	}
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Creating a new argument for: ");
	  print_generic_expr (dump_file, params[i]);
	  fprintf (dump_file, " in function: ");
	  print_generic_expr (dump_file, decl);
	  fprintf (dump_file, "\n");
	}
      adj.op = IPA_PARAM_OP_NEW;
      adj.param_prefix_index = IPA_PARAM_PREFIX_DCO;
      adj.type
	= reconstruct_complex_type (TREE_TYPE (parm), t->newtype[new_type_idx]);
      vec_safe_push (adjs, adj);
    }
  ipa_param_body_adjustments *adjustments
    = new ipa_param_body_adjustments (adjs, decl);
  adjustments->modify_formal_parameters ();
  auto_vec<tree> new_params;
  push_function_arg_decls (&new_params, decl);
  unsigned veclen = vec_safe_length (adjs);
  for (unsigned i = 0; i < veclen; i++)
    {
      if ((*adjs)[i].op != IPA_PARAM_OP_NEW)
	continue;
      tree decl = params[(*adjs)[i].base_index];
      srdecl *d = find_decl (decl);
      if (!d)
	continue;
      d->newdecl[new_type_idx] = new_params[i];
    }

  function *fn = DECL_STRUCT_FUNCTION (decl);

  if (!fn->static_chain_decl)
    return;
  srdecl *chain = find_decl (fn->static_chain_decl);
  if (!chain)
    return;

  srtype *type = chain->type;
  tree orig_var = chain->decl;
  const char *tname = NULL;
  if (DECL_NAME (orig_var))
    tname = IDENTIFIER_POINTER (DECL_NAME (orig_var));
  tree new_name = NULL;
  char *name = NULL;
  if (tname)
    {
      name = concat (tname, ".dco.0", NULL);
      new_name = get_identifier (name);
      free (name);
    }
  tree newtype1 = reconstruct_complex_type (TREE_TYPE (orig_var),
					    type->newtype[new_type_idx]);
  chain->newdecl[new_type_idx] = build_decl (DECL_SOURCE_LOCATION (orig_var),
					     PARM_DECL, new_name, newtype1);
  copy_var_attributes (chain->newdecl[new_type_idx], orig_var);
  fn->static_chain_decl = chain->newdecl[new_type_idx];
}

/* Find the refered DECL in the current function or globals.
   If this is a global decl, record that as being used
   in the current function.  */

srdecl *
ipa_struct_dco::find_decl (tree decl)
{
  srdecl *d;
  d = globals.find_decl (decl);
  if (d)
    {
      /* Record the global usage in the current function.  */
      if (!done_recording && cur_srfun)
	{
	  bool add = true;
	  /* No reason to add it to the current function if it is
	     already recorded as such. */
	  for (unsigned i = 0; i < cur_srfun->globals.length (); i++)
	    {
	      if (cur_srfun->globals[i] == d)
		{
		  add = false;
		  break;
		}
	    }
	  if (add)
	    cur_srfun->globals.safe_push (d);
	}
      return d;
    }
  if (cur_srfun)
    return cur_srfun->find_decl (decl);
  return NULL;
}

bool
ipa_struct_dco::rewrite_lhs_rhs (tree lhs, tree rhs, tree &newlhs, tree &newrhs)
{
  bool l = rewrite_expr (lhs, newlhs);
  bool r = rewrite_expr (rhs, newrhs);

  /* Handle NULL pointer specially. */
  if (l && !r && integer_zerop (rhs))
    {
      r = true;
      newrhs = fold_convert (TREE_TYPE (newlhs), rhs);
    }

  return l || r;
}

/* Rewrite the EXPR to NEWEXPR.  Return true if successful.
   NOTE: if a srfield is found in EXPR, ipa_struct_dco::cur_srfd is set.  */

bool
ipa_struct_dco::rewrite_expr (tree expr, tree &newexpr,
			      bool ignore_missing_decl)
{
  tree base;
  bool indirect;
  srtype *t;
  srfield *f;
  bool realpart, imagpart;
  bool address;

  tree newbase = NULL_TREE;

  if (TREE_CODE (expr) == CONSTRUCTOR)
    {
      srtype *t = find_type (TREE_TYPE (expr));
      if (!t)
	return false;
      gcc_assert (CONSTRUCTOR_NELTS (expr) == 0);
      if (!t->has_new_type ())
	return false;
      newexpr = build_constructor (t->newtype[new_type_idx], NULL);
      return true;
    }

  if (!get_type_field (expr, base, indirect, t, f, realpart, imagpart, address))
    return false;

  /* If the type is not changed, then just return false. */
  if (!t->has_new_type ())
    return false;
  if (f && f->dead_field_p)
    {
      cur_srfd = f;
      return true;
    }

  /*  NULL pointer handling is "special".  */
  if (integer_zerop (base))
    {
      gcc_assert (indirect && !address);
      tree newtype1
	= reconstruct_complex_type (TREE_TYPE (base), t->newtype[new_type_idx]);
      newbase = fold_convert (newtype1, base);
    }
  else
    {
      srdecl *d = find_decl (base);

      if (!d && dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Can't find decl:\n");
	  print_generic_expr (dump_file, base);
	  fprintf (dump_file, "\ntype:\n");
	  t->dump (dump_file);
	}
      if (!d && ignore_missing_decl)
	return true;
      gcc_assert (d);
      newbase = d->newdecl[new_type_idx];
    }

  if (f == NULL)
    {
      newexpr = newbase;
      if (address)
	newexpr = build_fold_addr_expr (newexpr);
      if (indirect)
	newexpr = build_simple_mem_ref (newexpr);
      if (imagpart)
	newexpr
	  = build1 (IMAGPART_EXPR, TREE_TYPE (TREE_TYPE (newexpr)), newexpr);
      if (realpart)
	newexpr
	  = build1 (REALPART_EXPR, TREE_TYPE (TREE_TYPE (newexpr)), newexpr);
      return true;
    }
  cur_srfd = f;

  tree newbase1 = newbase;
  if (address)
    newbase1 = build_fold_addr_expr (newbase1);
  if (indirect)
    {
      /* Supports the MEM_REF offset.
	 _1 = MEM[(struct DCO_TYPE *)a + old_size].f;
	 Old rewrite: _1 = a->f;
	 New rewrite: _1
	  = MEM[(struct DCO_TYPE *)a + new_size].f;
      */
      HOST_WIDE_INT offset_tmp = 0;
      HOST_WIDE_INT mem_offset = 0;
      bool realpart_tmp = false;
      bool imagpart_tmp = false;
      tree accesstype_tmp = NULL_TREE;
      tree num = NULL_TREE;
      get_ref_base_and_offset (expr, offset_tmp, realpart_tmp, imagpart_tmp,
			       accesstype_tmp, &num);

      tree ptype = TREE_TYPE (newbase1);
      /* Specify the correct size for the multi-layer pointer.  */
      tree size = isptrptr (ptype) ? TYPE_SIZE_UNIT (ptype)
				   : TYPE_SIZE_UNIT (inner_type (ptype));
      mem_offset
	= (num != NULL) ? TREE_INT_CST_LOW (num) * tree_to_shwi (size) : 0;
      newbase1 = build2 (MEM_REF, TREE_TYPE (ptype), newbase1,
			 build_int_cst (ptype, mem_offset));
    }

  tree new_field = f->newfield[new_type_idx];
  if (new_field != NULL_TREE)
    {
      newexpr = build3 (COMPONENT_REF, TREE_TYPE (new_field), newbase1,
			new_field, NULL_TREE);
    }
  if (imagpart)
    newexpr = build1 (IMAGPART_EXPR, TREE_TYPE (TREE_TYPE (newexpr)), newexpr);
  if (realpart)
    newexpr = build1 (REALPART_EXPR, TREE_TYPE (TREE_TYPE (newexpr)), newexpr);
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "newbase: %d. decl = ", (int) new_type_idx);
      print_generic_expr (dump_file, newbase1);
      fprintf (dump_file, "\nnewexpr = ");
      print_generic_expr (dump_file, newexpr);
      fprintf (dump_file, "\n");
    }

  return true;
}

/* Build a convert gimple to cast RHS to LHS.  */

tree
build_convert_gimple (tree lhs, tree rhs, gimple_stmt_iterator *gsi)
{
  tree ltype = TREE_TYPE (lhs);
  tree rtype = TREE_TYPE (rhs);
  if (types_compatible_p (ltype, rtype))
    return NULL_TREE;

  rhs = fold_build1 (CONVERT_EXPR, ltype, rhs);
  rhs = force_gimple_operand_gsi (gsi, rhs, true, NULL, true, GSI_SAME_STMT);
  return rhs;
}

static int
find_elt_index (auto_vec<gimple *> &stmts, gimple *stmt)
{
  int i;
  gimple *gs;

  FOR_EACH_VEC_ELT (stmts, i, gs)
    if (gs == stmt)
      return i;
  return -1;
}

/* Call encode/decode function FN for RHS.  */

tree
dco_closure::encode_decode_rhs (tree rhs, tree fn)
{
  tree newrhs = build_call_expr (fn, 1, rhs);
  cgraph_node *callee = cgraph_node::get (fn);
  cgraph_node *node = cgraph_node::get (current_function_decl);
  node->create_edge (callee, NULL, profile_count::zero ());
  return newrhs;
}

/* Decode array pointer for read stmt RD_STMT.  */

void
dco_closure::decode_array_pointer (gimple *rd_stmt, tree &newlhs, tree &newrhs)
{
  tree lhs = gimple_assign_lhs (rd_stmt);
  gimple_stmt_iterator gsi = gsi_for_stmt (rd_stmt);

  /* For read stmt lhs = _0->fld, should only rewrite rhs.  */
  tree ptr_type = TREE_TYPE (lhs);
  tree int_type = TREE_TYPE (newrhs);
  gcc_checking_assert (newlhs == NULL_TREE && POINTER_TYPE_P (ptr_type)
		       && INTEGRAL_TYPE_P (int_type));

  tree idx_ssa
    = gimplify_build1 (&gsi, NOP_EXPR, pointer_sized_int_node, newrhs);

  tree base_ptr = mem_base_var;
  if (!VAR_P (base_ptr))
    base_ptr = unshare_expr_without_location (base_ptr);
  tree gptr0_ssa = fold_convert (ptr_type, base_ptr);

  /* Emit gimple _X1 = _Idx * sizeof (struct).  */
  tree step1 = gimplify_build2 (&gsi, MULT_EXPR, pointer_sized_int_node,
				idx_ssa, struct_size);

  /* Emit gimple _X2 = gptr0 + _X1;  */
  tree addr_ptr = gimplify_build2 (&gsi, POINTER_PLUS_EXPR, ptr_type, gptr0_ssa,
				   fold_convert (size_type_node, step1));
  newrhs = gimplify_build1 (&gsi, NOP_EXPR, ptr_type, addr_ptr);
}

/* Encode array pointer for write stmt WT_STMT.  */

void
dco_closure::encode_array_pointer (gimple *wt_stmt, tree &newlhs, tree &newrhs)
{
  tree rhs = gimple_assign_rhs1 (wt_stmt);
  gimple_stmt_iterator gsi = gsi_for_stmt (wt_stmt);

  /* For write stmt _0->fld = rhs, should only rewrite lhs.  */
  tree int_type = TREE_TYPE (newlhs);
  tree ptr_type = TREE_TYPE (rhs);
  gcc_checking_assert (newrhs == NULL_TREE && INTEGRAL_TYPE_P (int_type)
		       && POINTER_TYPE_P (ptr_type));

  int idx = find_elt_index (wt_change, wt_stmt);
  gcc_checking_assert (idx != -1);

  tree wt_idx = wt_array_index[idx];
  if (wt_idx != NULL_TREE)
    {
      newrhs = gimplify_build1 (&gsi, NOP_EXPR, int_type, wt_array_index[idx]);
      return;
    }

  tree pointer_ssa = fold_convert (pointer_sized_int_node, rhs);

  tree base_ptr = mem_base_var;
  if (!VAR_P (base_ptr))
    base_ptr = unshare_expr_without_location (base_ptr);
  tree gptr0_ssa = fold_convert (pointer_sized_int_node, base_ptr);

  /* Emit gimple _X1 = ptr - gptr0.  */
  tree step1 = gimplify_build2 (&gsi, MINUS_EXPR, pointer_sized_int_node,
				pointer_ssa, gptr0_ssa);

  /* Emit gimple _X2 = _X1 / sizeof (struct).  */
  tree step2 = gimplify_build2 (&gsi, TRUNC_DIV_EXPR, pointer_sized_int_node,
				step1, struct_size);

  newrhs = gimplify_build1 (&gsi, NOP_EXPR, int_type, step2);
}

bool
ipa_struct_dco::rewrite_assign (gassign *stmt, gimple_stmt_iterator *gsi)
{
  tree lhs = gimple_assign_lhs (stmt);
  tree rhs1 = gimple_assign_rhs1 (stmt), rhs2;
  tree newlhs = NULL_TREE, newrhs = NULL_TREE;
  tree newrhs1 = NULL_TREE, newrhs2 = NULL_TREE;
  tree struct_type, num = NULL_TREE;
  gimple *new_stmt;
  bool r1, r2;
  dco_closure *closure_info;
  tree encode_fn, decode_fn, real_lhs, real_rhs, conv_rhs;

  if (gimple_clobber_p (stmt))
    {
      if (!rewrite_expr (lhs, newlhs))
	return false;

      tree clobber = build_constructor (TREE_TYPE (newlhs), NULL);
      TREE_THIS_VOLATILE (clobber) = true;
      new_stmt = gimple_build_assign (newlhs, clobber);
      gsi_insert_before (gsi, new_stmt, GSI_SAME_STMT);
      return true;
    }

  if (TREE_CODE_CLASS (gimple_assign_rhs_code (stmt)) == tcc_comparison)
    {
      rhs2 = gimple_assign_rhs2 (stmt);
      tree_code rhs_code = gimple_assign_rhs_code (stmt);

      if (!rewrite_lhs_rhs (rhs1, rhs2, newrhs1, newrhs2))
	return false;
      tree newexpr
	= gimplify_build2 (gsi, rhs_code, boolean_type_node, newrhs1, newrhs2);
      if (newexpr)
	{
	  newexpr
	    = fold_convert (TREE_TYPE (gimple_assign_lhs (stmt)), newexpr);
	  gimple_assign_set_rhs_from_tree (gsi, newexpr);
	  update_stmt (stmt);
	}
      return false;
    }

  if (gimple_assign_rhs_class (stmt) == GIMPLE_SINGLE_RHS)
    {
      cur_srfd = NULL;
      if (!rewrite_lhs_rhs (lhs, rhs1, newlhs, newrhs))
	return false;

      if (cur_srfd && cur_srfd->dead_field_p)
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "Removing a write to a dead field:\n");
	      print_gimple_stmt (dump_file, stmt, 0);
	      fprintf (dump_file, "\n");
	    }
	  return true;
	}

      if (cur_srfd && cur_srfd->dynamic_df
	  && cur_srfd->dynamic_df->dco_kind == CLOSURE_INT
	  && cur_srfd->ddco_type_change_p ())
	{
	  closure_info = cur_srfd->get_closure ();
	  if (closure_info->wt_change_p (stmt))
	    {
	      /* For a write stmt _0->fld = rhs, should only rewrite lhs.  */
	      gcc_checking_assert (newrhs == NULL_TREE);
	      encode_fn = cur_srfd->dynamic_df->cond->encode_fn;
	      newrhs = closure_info->encode_decode_rhs (rhs1, encode_fn);
	    }
	  else if (closure_info->rd_change_p (stmt))
	    {
	      /* For a read stmt lhs = _0->fld, should only rewrite rhs.  */
	      gcc_checking_assert (newlhs == NULL_TREE);
	      decode_fn = cur_srfd->dynamic_df->cond->decode_fn;
	      newrhs = closure_info->encode_decode_rhs (newrhs, decode_fn);
	    }
	  else if (!closure_info->unchange_p (stmt))
	    gcc_unreachable ();
	}

      if (cur_srfd && cur_srfd->static_df && cur_srfd->static_df->arr_ptr)
	{
	  closure_info = cur_srfd->get_closure ();
	  if (closure_info->wt_change_p (stmt))
	    {
	      closure_info->encode_array_pointer (stmt, newlhs, newrhs);
	    }
	  else if (closure_info->rd_change_p (stmt))
	    {
	      closure_info->decode_array_pointer (stmt, newlhs, newrhs);
	    }
	  else if (!closure_info->unchange_p (stmt))
	    gcc_unreachable ();
	}

      /* Need to convert the cached fields.  */
      real_lhs = newlhs ? newlhs : lhs;
      real_rhs = newrhs ? newrhs : rhs1;
      if ((conv_rhs = build_convert_gimple (real_lhs, real_rhs, gsi)))
	newrhs = conv_rhs;
      if (newrhs
	  && get_gimple_rhs_class (TREE_CODE (newrhs)) == GIMPLE_INVALID_RHS)
	newrhs = gimplify_build1 (gsi, NOP_EXPR, TREE_TYPE (newrhs), newrhs);
      new_stmt
	= gimple_build_assign (newlhs ? newlhs : lhs, newrhs ? newrhs : rhs1);
      goto insert_and_dump;
    }

  switch (gimple_assign_rhs_code (stmt))
    {
    case POINTER_PLUS_EXPR:
      rhs2 = gimple_assign_rhs2 (stmt);
      if (!rewrite_lhs_rhs (lhs, rhs1, newlhs, newrhs))
	return false;
      struct_type = TREE_TYPE (TREE_TYPE (lhs));
      /* Check if rhs2 is a multiplication of the size of the type. */
      if (!POINTER_TYPE_P (struct_type)
	  && !is_result_of_mult (rhs2, &num, struct_type))
	internal_error (
	  "the rhs of pointer was not a multiplicate and it slipped through");

      /* Add the judgment of num, support for POINTER_DIFF_EXPR.
	 _6 = _4 + _5;
	 _5 = (long unsigned int) _3;
	 _3 = _1 - old_2.  */
      if (num != NULL)
	num = gimplify_build1 (gsi, NOP_EXPR, sizetype, num);
      if (num != NULL)
	{
	  tree newsize = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (newlhs)));
	  newsize = gimplify_build2 (gsi, MULT_EXPR, sizetype, num, newsize);
	  new_stmt
	    = gimple_build_assign (newlhs, POINTER_PLUS_EXPR, newrhs, newsize);
	}
      else
	new_stmt
	  = gimple_build_assign (newlhs, POINTER_PLUS_EXPR, newrhs, rhs2);
      goto insert_and_dump;

    /* Support POINTER_DIFF_EXPR rewriting.  */
    case POINTER_DIFF_EXPR:
      rhs2 = gimple_assign_rhs2 (stmt);
      r1 = rewrite_expr (rhs1, newrhs1);
      r2 = rewrite_expr (rhs2, newrhs2);
      if (r1 != r2)
	{
	  /* Handle NULL pointer specially.  */
	  if (r1 && !r2 && integer_zerop (rhs2))
	    {
	      r2 = true;
	      newrhs2 = fold_convert (TREE_TYPE (newrhs1), rhs2);
	    }
	  else if (r2 && !r1 && integer_zerop (rhs1))
	    {
	      r1 = true;
	      newrhs1 = fold_convert (TREE_TYPE (newrhs2), rhs1);
	    }
	  else
	    return false;
	}
      else if (!r1 && !r2)
	return false;

      /* The two operands always have pointer/reference type.  */
      gimple_assign_set_rhs1 (stmt, newrhs1);
      gimple_assign_set_rhs2 (stmt, newrhs2);
      update_stmt (stmt);

      if (!POINTER_TYPE_P (TREE_TYPE (TREE_TYPE (rhs1))))
	{
	  gimple *use_stmt;
	  imm_use_iterator imm_iter;
	  tree lhs = gimple_assign_lhs (stmt);

	  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, lhs)
	    {
	      if (is_gimple_assign (use_stmt)
		  && gimple_assign_rhs_code (use_stmt) == EXACT_DIV_EXPR)
		{
		  tree otype_size
		    = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (rhs1)));
		  tree ntype_size
		    = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (newrhs1)));

		  gcc_checking_assert (gimple_assign_rhs1 (use_stmt) == lhs);
		  gcc_checking_assert (
		    tree_int_cst_equal (gimple_assign_rhs2 (use_stmt),
					otype_size));

		  gimple_assign_set_rhs2 (use_stmt, ntype_size);
		  update_stmt (use_stmt);
		}
	    }
	}
      return false;

    /* Cast.  */
    CASE_CONVERT:
    case VIEW_CONVERT_EXPR:
    case FIX_TRUNC_EXPR:
      rewrite_expr (rhs1, newrhs);
      if (rewrite_expr (lhs, newlhs))
	/* Only redundant cast is allowed. */
	gcc_assert (types_dco_compatible_p (TREE_TYPE (lhs), TREE_TYPE (rhs1)));
      if (!newrhs && !newlhs)
	return false;

      rhs1 = newrhs ? newrhs : rhs1;
      lhs = newlhs ? newlhs : lhs;
      conv_rhs = fold_convert (TREE_TYPE (lhs), rhs1);
      new_stmt = gimple_build_assign (lhs, conv_rhs);
      goto insert_and_dump;

    default:
      return false;
    }

insert_and_dump:
  gsi_insert_before (gsi, new_stmt, GSI_SAME_STMT);
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      print_gimple_stmt (dump_file, stmt, 0);
      fprintf (dump_file, "=>\n");
      print_gimple_stmt (dump_file, new_stmt, 0);
      fprintf (dump_file, "\n");
    }
  return true;
}

/* Rewrite allocation call statement STMT.  Return TRUE if the statement
   is to be removed. */

bool
ipa_struct_dco::rewrite_allocation_stmt (gcall *stmt, tree decl, tree new_decl,
					 tree type, tree orig_type,
					 tree new_type,
					 gimple_stmt_iterator *gsi)
{
  tree num = NULL_TREE;
  gimple *g;
  tree newrhs1 = NULL_TREE;

  num = get_allocate_size (type, decl, orig_type, stmt, NULL);
  if (!num)
    {
      if (gimple_call_builtin_p (stmt, BUILT_IN_MALLOC)
	  || gimple_call_builtin_p (stmt, BUILT_IN_ALLOCA))
	{
	  /* For alloca/malloc, if we can't get number of elements, just use
	     old allocation size, as new_struct_size <= old_struct_size.  */
	  g = gimple_build_call (gimple_call_fndecl (stmt), 1,
				 gimple_call_arg (stmt, 0));
	  gimple_call_set_lhs (g, new_decl);
	  gsi_insert_before (gsi, g, GSI_SAME_STMT);
	  return true;
	}
      internal_error ("rewrite failed for allocation");
    }

  /* The realloc call needs to have its first argument rewritten. */
  if (gimple_call_builtin_p (stmt, BUILT_IN_REALLOC))
    {
      tree rhs1 = gimple_call_arg (stmt, 0);
      if (integer_zerop (rhs1))
	newrhs1 = rhs1;
      else if (!rewrite_expr (rhs1, newrhs1))
	internal_error ("rewrite failed for realloc");
    }

  /* Go through each new lhs.  */
  /* Specify the correct size for the multi-layer pointer.  */
  tree newsize = isptrptr (orig_type) ? TYPE_SIZE_UNIT (orig_type)
				      : TYPE_SIZE_UNIT (new_type);
  /* Every allocation except for calloc needs the size multiplied out.  */
  if (!gimple_call_builtin_p (stmt, BUILT_IN_CALLOC))
    newsize = gimplify_build2 (gsi, MULT_EXPR, sizetype, num, newsize);

  if (gimple_call_builtin_p (stmt, BUILT_IN_MALLOC)
      || gimple_call_builtin_p (stmt, BUILT_IN_ALLOCA))
    g = gimple_build_call (gimple_call_fndecl (stmt), 1, newsize);
  else if (gimple_call_builtin_p (stmt, BUILT_IN_CALLOC))
    g = gimple_build_call (gimple_call_fndecl (stmt), 2, num, newsize);
  else if (gimple_call_builtin_p (stmt, BUILT_IN_REALLOC))
    g = gimple_build_call (gimple_call_fndecl (stmt), 2, newrhs1, newsize);
  else
    gcc_assert (false);
  gimple_call_set_lhs (g, new_decl);
  gsi_insert_before (gsi, g, GSI_SAME_STMT);
  return true;
}

/* Rewrite function call statement STMT.  Return TRUE if the statement
   is to be removed. */

bool
ipa_struct_dco::rewrite_call (gcall *stmt, gimple_stmt_iterator *gsi)
{
  /* Handled allocation calls are handled seperately from normal
     function calls. */
  if (allocation_stmt_p (stmt))
    {
      tree lhs = gimple_call_lhs (stmt);
      srdecl *decl = find_decl (lhs);
      if (!decl || !decl->type || !decl->type->has_new_type ())
	return false;
      srtype *type = decl->type;
      if (type->has_escaped ())
	return false;

      tree new_type = type->newtype[new_type_idx];
      tree new_decl = decl->newdecl[new_type_idx];
      return rewrite_allocation_stmt (stmt, decl->decl, new_decl, type->type,
				      decl->orig_type, new_type, gsi);
    }

  /* The function call free needs to be handled special. */
  if (gimple_call_builtin_p (stmt, BUILT_IN_FREE))
    {
      tree expr = gimple_call_arg (stmt, 0);
      tree newexpr = NULL_TREE;
      if (!rewrite_expr (expr, newexpr))
	return false;

      gimple_call_set_arg (stmt, 0, newexpr);
      update_stmt (stmt);
      return false;
    }

  /* Otherwise, look up the function to see if we have cloned it
     and rewrite the arguments. */
  tree fndecl = gimple_call_fndecl (stmt);

  /* Indirect calls are already marked as escaping so ignore.  */
  if (!fndecl)
    return false;

  cgraph_node *node = cgraph_node::get (fndecl);
  gcc_assert (node);

  srfunction *f = find_function (node);
  TEST (f != NULL)
  /* Get the new srfunction to rewrite the call:
     1) For static-DCO, only rewrite if there is a new function
     2) For dynamic-DCO, only rewrite if it is not partially cloned.  */
  if (static_dco_trans_p ())
    {
      if (!f->is_safe_func)
	{
	  TEST (f->newf != NULL)
	  f = f->newf;
	}
    }
  else
    {
      TEST (!f->partial_clone_p ())
      f = f->dco_path.cloned_funcs[new_type_idx];
    }

  gcc_checking_assert (f);
  if (f->is_safe_func)
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  print_gimple_stmt (dump_file, stmt, 0);
	  fprintf (dump_file, "=>\n");
	}

      /* Add a safe func mechanism.  */
      tree expr = gimple_call_arg (stmt, 0);
      tree newexpr = NULL_TREE;
      if (rewrite_expr (expr, newexpr))
	gimple_call_set_arg (stmt, 0, newexpr);

      gimple_call_set_fndecl (stmt, f->node->decl);

      if (dump_file && (dump_flags & TDF_DETAILS))
	print_gimple_stmt (dump_file, stmt, 0);

      update_stmt (stmt);
      return false;
    }

  tree chain = gimple_call_chain (stmt);
  unsigned nargs = gimple_call_num_args (stmt);
  auto_vec<tree> vargs (nargs);

  if (chain)
    {
      tree newchain = NULL_TREE;
      if (rewrite_expr (chain, newchain))
	chain = newchain;
    }

  for (unsigned i = 0; i < nargs; i++)
    vargs.quick_push (gimple_call_arg (stmt, i));

  int extraargs = 0;

  for (unsigned i = 0; i < f->args.length (); i++)
    {
      srdecl *d = f->args[i];
      if (d->argumentnum == -2)
	continue;
      gcc_assert (d->argumentnum != -1);
      tree arg = vargs[d->argumentnum + extraargs];
      tree newarg = NULL_TREE;
      if (!rewrite_expr (arg, newarg))
	continue;

      /* If this ARG has a replacement handle the replacement.  */
      vargs[d->argumentnum + extraargs] = newarg;
    }

  gcall *new_stmt;

  new_stmt = gimple_build_call_vec (f->node->decl, vargs);

  if (gimple_call_lhs (stmt))
    gimple_call_set_lhs (new_stmt, gimple_call_lhs (stmt));

  gimple_set_vuse (new_stmt, gimple_vuse (stmt));
  gimple_set_vdef (new_stmt, gimple_vdef (stmt));

  if (gimple_has_location (stmt))
    gimple_set_location (new_stmt, gimple_location (stmt));
  gimple_call_copy_flags (new_stmt, stmt);
  gimple_call_set_chain (new_stmt, chain);

  gimple_set_modified (new_stmt, true);

  if (gimple_vdef (new_stmt) && TREE_CODE (gimple_vdef (new_stmt)) == SSA_NAME)
    SSA_NAME_DEF_STMT (gimple_vdef (new_stmt)) = new_stmt;

  gsi_insert_before (gsi, new_stmt, GSI_SAME_STMT);

  /* We need to defer cleaning EH info on the new statement to
     fixup-cfg.  We may not have dominator information at this point
     and thus would end up with unreachable blocks and have no way
     to communicate that we need to run CFG cleanup then.  */
  int lp_nr = lookup_stmt_eh_lp (stmt);
  if (lp_nr != 0)
    {
      remove_stmt_from_eh_lp (stmt);
      add_stmt_to_eh_lp (new_stmt, lp_nr);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      print_gimple_stmt (dump_file, stmt, 0);
      fprintf (dump_file, "=>\n");
      print_gimple_stmt (dump_file, new_stmt, 0);
      fprintf (dump_file, "\n");
    }
  return true;
}

/* Rewrite the conditional statement STMT.  Return TRUE if the
   old statement is to be removed. */

bool
ipa_struct_dco::rewrite_cond (gcond *stmt,
			      gimple_stmt_iterator *ARG_UNUSED (gsi))
{
  tree_code rhs_code = gimple_cond_code (stmt);

  /* Handle only equals or not equals conditionals. */
  if (TREE_CODE_CLASS (rhs_code) != tcc_comparison)
    return false;
  tree lhs = gimple_cond_lhs (stmt);
  tree rhs = gimple_cond_rhs (stmt);

  tree newlhs = NULL_TREE;
  tree newrhs = NULL_TREE;
  if (!rewrite_lhs_rhs (lhs, rhs, newlhs, newrhs))
    return false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      print_gimple_stmt (dump_file, stmt, 0);
      fprintf (dump_file, "=>\n");
    }

  /*  Old rewrite: if (x_1 != 0B)
		-> _1 = x.dco.0_1 != 0B; if (_1 != 1)
		   The logic is incorrect.
      New rewrite: if (x_1 != 0B)
		-> if (x.dco.0_1 != 0B)；*/
  if (newlhs)
    {
      gimple_cond_set_lhs (stmt, newlhs);
    }
  if (newrhs)
    {
      gimple_cond_set_rhs (stmt, newrhs);
    }
  update_stmt (stmt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      print_gimple_stmt (dump_file, stmt, 0);
      fprintf (dump_file, "\n\n");
    }
  return false;
}

/* Rewrite PHI nodes, return true if the PHI was replaced. */

bool
ipa_struct_dco::rewrite_phi (gphi *phi)
{
  tree newlhs = NULL_TREE;
  gphi *newphi = NULL;
  tree result = gimple_phi_result (phi);
  gphi_iterator gpi;

  if (!rewrite_expr (result, newlhs))
    return false;

  if (newlhs == NULL_TREE)
    return false;

  newphi = create_phi_node (newlhs, gimple_bb (phi));

  for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
    {
      tree newrhs;
      phi_arg_d rhs = *gimple_phi_arg (phi, i);
      edge e = gimple_phi_arg_edge (phi, i);

      /* Handling the NULL phi Node.  */
      bool r = rewrite_expr (rhs.def, newrhs);
      if (!r && integer_zerop (rhs.def))
	newrhs = fold_convert (TREE_TYPE (newlhs), rhs.def);

      add_phi_arg (newphi, newrhs, e, rhs.locus);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      print_gimple_stmt (dump_file, phi, 0);
      fprintf (dump_file, "=>\n");
      print_gimple_stmt (dump_file, newphi, 0);
      fprintf (dump_file, "\n\n");
    }

  gpi = gsi_for_phi (phi);
  remove_phi_node (&gpi, false);

  return true;
}

/* Rewrite gimple statement STMT, return true if the statement is to be
   removed.  */

bool
ipa_struct_dco::rewrite_stmt (gimple *stmt, gimple_stmt_iterator *gsi)
{
  switch (gimple_code (stmt))
    {
    case GIMPLE_ASSIGN:
      return rewrite_assign (as_a<gassign *> (stmt), gsi);
    case GIMPLE_CALL:
      return rewrite_call (as_a<gcall *> (stmt), gsi);
    case GIMPLE_COND:
      return rewrite_cond (as_a<gcond *> (stmt), gsi);
      break;
    case GIMPLE_GOTO:
    case GIMPLE_SWITCH:
      break;
    case GIMPLE_DEBUG:
    case GIMPLE_ASM:
      break;
    default:
      break;
    }
  return false;
}

/* Create function to further compress fields with special_values.
   - DECOMP == 0: create function to compress the field.
   - DECOMP != 0: create function to decompress the field.
   IDX is an unique number for function name.
   Return declaration of created function.  */

tree
ipa_struct_dco::create_compress_field_fn (dco_cond *dc, int idx, int decomp)
{
  char fn_name[64];
  tree fn_decl, arg_decl;
  basic_block bb, return_bb;
  tree cond, val, result;
  edge true_e, false_e, exit_edge;
  HOST_WIDE_INT hwi_val, special_int;
  gimple_stmt_iterator gsi;
  gimple *stmt;
  unsigned i;
  /* Note: when adding predecessors, PHI can be replaced to expand args.  */
  gphi *phi;

  if (dc->special_values.is_empty ())
    return NULL_TREE;

  tree arg_type = decomp ? dc->new_type : dc->old_type;
  tree return_type = decomp ? dc->old_type : dc->new_type;

  /* Init declarations.  */
  sprintf (fn_name, "%s%d", decomp ? DECODE_FN_PREFIX : ENCODE_FN_PREFIX, idx);
  fn_decl = create_new_fn_decl (fn_name, 1, &arg_type, return_type);

  /* Push NULL cfun.  */
  cfun_context ctx;
  bb = init_lowered_empty_function (fn_decl, true,
				    profile_count::uninitialized ());
  calculate_dominance_info (CDI_DOMINATORS);

  split_edge (single_pred_edge (bb));
  result = make_ssa_name (return_type);
  create_phi_node (result, bb);
  return_bb = bb;
  bb = single_pred (bb);

  /* Insert:
	  if (arg <= high_bound && arg >= low_bound)
	    return arg;
     */
  arg_decl = DECL_ARGUMENTS (fn_decl);
  cond = build2 (LE_EXPR, boolean_type_node,
		 fold_convert (TREE_TYPE (dc->high_bound), arg_decl),
		 dc->high_bound);
  exit_edge = create_empty_if_region_on_edge (single_succ_edge (bb), cond);
  extract_true_false_edges_from_block (single_succ (bb), &true_e, &false_e);
  bb = true_e->dest;
  cond = build2 (GE_EXPR, boolean_type_node,
		 fold_convert (TREE_TYPE (dc->low_bound), arg_decl),
		 dc->low_bound);
  create_empty_if_region_on_edge (single_succ_edge (bb), cond);
  extract_true_false_edges_from_block (single_succ (bb), &true_e, &false_e);
  /* Return old value on true_e.  */
  bb = true_e->dest;
  gsi = gsi_last_bb (bb);
  val = make_ssa_name (return_type);
  APPEND_GASSIGN_1 (gsi, val, NOP_EXPR, arg_decl);
  redirect_edge_succ (single_succ_edge (bb), return_bb);
  phi = gsi_start_phis (return_bb).phi ();
  add_phi_arg (phi, val, single_succ_edge (bb), UNKNOWN_LOCATION);

  /* Insert conversion code on exit_e.  */
  hwi_val = tree_to_uhwi (dc->high_bound) + 1;
  FOR_EACH_VEC_ELT (dc->special_values, i, special_int)
    {
      bb = exit_edge->src;
      tree special_val
	= build_int_cst (signed_type_for (dc->old_type), special_int);
      tree compressed_val = build_int_cst (dc->new_type, hwi_val);

      if (i == dc->special_values.length () - 1)
	{
	  /* Omit condition check for the last special value.  */
	  redirect_edge_and_branch (single_succ_edge (bb), return_bb);
	  phi = gsi_start_phis (return_bb).phi ();
	  add_phi_arg (phi, decomp ? special_val : compressed_val,
		       single_succ_edge (bb), UNKNOWN_LOCATION);
	}
      else
	{
	  cond = build2 (EQ_EXPR, boolean_type_node, arg_decl,
			 decomp ? compressed_val : special_val);
	  exit_edge = create_empty_if_region_on_edge (exit_edge, cond);
	  extract_true_false_edges_from_block (single_succ (bb), &true_e,
					       &false_e);
	  redirect_edge_and_branch (single_succ_edge (true_e->dest), return_bb);
	  phi = gsi_start_phis (return_bb).phi ();
	  add_phi_arg (phi, decomp ? special_val : compressed_val,
		       single_succ_edge (true_e->dest), UNKNOWN_LOCATION);
	  hwi_val++;
	}
    }

  /* Return stmt.  */
  update_stmt (phi);
  stmt = gimple_build_return (result);
  gsi = gsi_last_bb (return_bb);
  gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);

  free_dominance_info (CDI_DOMINATORS);
  update_ssa (TODO_update_ssa);

  cgraph_node::create (fn_decl);
  cgraph_node::add_new_function (fn_decl, true);
  cgraph_edge::rebuild_edges ();

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n[DCO %s FIELD FUNC]\n",
	       decomp ? "DECOMPRESS" : "COMPRESS");
      dump_function_to_file (cfun->decl, dump_file, dump_flags);
    }
  return fn_decl;
}

static dco_cond *
get_dco_cond_by_field_variant (dco_info &info, srfield *srf, dco_variant *dv)
{
  dco_cond *dc;
  unsigned i;
  FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
    if ((dc->bitmask & dv->bitmask)
	&& dc->dco_fields.contains (srf->dynamic_df))
      return dc;
  return NULL;
}

/* Create function to compress a single object. Return function decl.  */

tree
ipa_struct_dco::create_compress_single_fn (dco_info &info,
					   unsigned dco_path_idx,
					   dco_variant *dv)
{
  /* Function declairation.  */
  tree new_type = dv->new_type;
  tree orig_struct_type = info.dco_type->type;
  tree orig_struct_size = TYPE_SIZE_UNIT (orig_struct_type);
  tree size_type = TREE_TYPE (orig_struct_size);
  tree arg_types[2];
  tree orig_ptr_type = build_pointer_type (orig_struct_type);
  arg_types[0] = orig_ptr_type;
  arg_types[1] = size_type;
  char fn_name[32];
  sprintf (fn_name, "%s%d", COMPRESSED_SINGLE_PREFIX, dco_path_idx);
  tree fndecl = create_new_fn_decl (fn_name, 2, arg_types, void_type_node);

  /* Function arguments.  */
  tree struct_array = DECL_ARGUMENTS (fndecl);
  tree idx = TREE_CHAIN (struct_array);

  /* Push NULL cfun.  */
  cfun_context ctx;
  basic_block bb
    = init_lowered_empty_function (fndecl, true,
				   profile_count::uninitialized ());

  /* Function body.  */
  gimple_stmt_iterator gsi;
  gimple *stmt;
  /* Use a temporary struct to avoid overlapping.  */
  tree tmp_obj = create_tmp_var (orig_struct_type, "tmp");
  /* tmp = start[i];
     =>
     idx_1 = (long unsigned int) idx;
     _2 = idx_1 * sizeof (orig_struct);
     _3 = start + _2;
     tmp = *_3;
    */
  gsi = gsi_last_bb (bb);
  tree var_mul = make_ssa_name (long_unsigned_type_node);
  APPEND_GASSIGN_2 (gsi, var_mul, MULT_EXPR, idx, orig_struct_size);
  tree var_plus = make_ssa_name (orig_ptr_type);
  APPEND_GASSIGN_2 (gsi, var_plus, POINTER_PLUS_EXPR, struct_array, var_mul);
  tree rhs = build2 (MEM_REF, orig_struct_type, var_plus,
		     build_int_cst (orig_ptr_type, 0));
  APPEND_GASSIGN_1 (gsi, tmp_obj, MEM_REF, rhs);

  /* Init: new_struct* ptr = start + idx_1 * sizeof (new_struct) */
  tree ptr_var = create_tmp_var (build_pointer_type (new_type), "ptr");
  var_mul = make_ssa_name (long_unsigned_type_node);
  APPEND_GASSIGN_2 (gsi, var_mul, MULT_EXPR, idx, TYPE_SIZE_UNIT (new_type));
  APPEND_GASSIGN_2 (gsi, ptr_var, POINTER_PLUS_EXPR, struct_array, var_mul);

  /* Assign the fields.  */
  srfield *field;
  unsigned int i;
  FOR_EACH_VEC_ELT (info.dco_type->fields, i, field)
    {
      tree old_type = field->fieldtype;
      tree old_field = field->fielddecl;
      tree new_field = field->newfield[dco_path_idx];
      new_field = new_field ? new_field : old_field;
      tree new_type = TREE_TYPE (new_field);

      tree var = make_ssa_name (old_type);
      tree rhs
	= build3 (COMPONENT_REF, old_type, tmp_obj, old_field, NULL_TREE);
      APPEND_GASSIGN_1 (gsi, var, COMPONENT_REF, rhs);
      if (new_type != old_type)
	{
	  dco_cond *dc = get_dco_cond_by_field_variant (info, field, dv);
	  if (dc && dc->encode_fn)
	    {
	      /* Need encoding.  */
	      /* As we may have bitfield, so dc->new_type and
		 new_type can be different.  */
	      tree var1 = make_ssa_name (dc->new_type);
	      gcall *call_stmt = gimple_build_call (dc->encode_fn, 1, var);
	      gimple_call_set_lhs (call_stmt, var1);
	      gsi_insert_after (&gsi, call_stmt, GSI_CONTINUE_LINKING);
	      var = var1;
	    }
	  tree var1 = make_ssa_name (new_type);
	  APPEND_GASSIGN_1 (gsi, var1, NOP_EXPR, var);
	  var = var1;
	}
      tree ref = build2 (MEM_REF, new_type, ptr_var,
			 build_int_cst (TREE_TYPE (ptr_var), 0));
      tree lhs = build3 (COMPONENT_REF, new_type, ref, new_field, NULL_TREE);
      APPEND_GASSIGN_1 (gsi, lhs, MEM_REF, var);
    }

  /* Clobber and return.  */
  tree clobber = build_clobber (orig_struct_type);
  stmt = gimple_build_assign (tmp_obj, clobber);
  gsi_insert_after (&gsi, stmt, GSI_CONTINUE_LINKING);
  stmt = gimple_build_return (NULL);
  gsi_insert_after (&gsi, stmt, GSI_CONTINUE_LINKING);

  update_ssa (TODO_update_ssa);

  cgraph_node::create (fndecl);
  cgraph_node::add_new_function (fndecl, true);
  cgraph_edge::rebuild_edges ();

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n[DCO COMPRESS OBJECT FUNC]\n");
      dump_function_to_file (cfun->decl, dump_file, dump_flags);
    }
  return fndecl;
}

/* Split edge E and insert codes to modify a single dco_ref expression.
   Return the exit edge of created codes.  */

edge
ipa_struct_dco::insert_code_modify_single_ref (edge e, tree ref, dco_data *data,
					       tree orig_size, tree new_size)
{
  basic_block bb = split_edge (e);
  gimple_stmt_iterator gsi = gsi_last_bb (bb);
  gimple *stmt;

  /* For each dco_ref, create code like:
     if (REF)
	REF = (long) DATA + ((long) REF - (long) DATA)
			/ sizeof(old_type) * sizeof(new_type);
   */
  /* 1) Create ssa_name for dco_ref.  */
  tree ref_ssa_name = create_tmp_reg (TREE_TYPE (ref));
  stmt = gimple_build_assign (ref_ssa_name, unshare_expr (ref));
  gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);
  /* 2) Create the if-else structure.  */
  tree condition
    = build2 (EQ_EXPR, boolean_type_node, ref_ssa_name, null_pointer_node);
  edge exit_e
    = create_empty_if_region_on_edge (single_succ_edge (bb), condition);
  edge true_e, false_e;
  extract_true_false_edges_from_block (single_succ (bb), &true_e, &false_e);
  gsi = gsi_last_bb (false_e->dest);

  /* 3) Create conversion codes.  */
  tree data_ssa_def = data->ssa_def;
  if (!data_ssa_def)
    {
      data_ssa_def = make_ssa_name (TREE_TYPE (data->var));
      APPEND_GASSIGN_1 (gsi, data_ssa_def, NOP_EXPR, unshare_expr (data->var));
    }
  tree var_sub = make_ssa_name (ptrdiff_type_node);
  APPEND_GASSIGN_2 (gsi, var_sub, POINTER_DIFF_EXPR, ref_ssa_name,
		    data_ssa_def);
  tree var_div = make_ssa_name (ptrdiff_type_node);
  APPEND_GASSIGN_2 (gsi, var_div, TRUNC_DIV_EXPR, var_sub,
		    fold_convert (ptrdiff_type_node, orig_size));
  tree var_mul = make_ssa_name (ptrdiff_type_node);
  APPEND_GASSIGN_2 (gsi, var_mul, MULT_EXPR, var_div,
		    fold_convert (ptrdiff_type_node, new_size));
  tree var_mul2 = make_ssa_name (size_type_node);
  APPEND_GASSIGN_1 (gsi, var_mul2, NOP_EXPR, var_mul);
  tree var_add = make_ssa_name (TREE_TYPE (data_ssa_def));
  APPEND_GASSIGN_2 (gsi, var_add, POINTER_PLUS_EXPR, data_ssa_def, var_mul2);
  /* 4) Store.  */
  gsi_insert_after (&gsi, gimple_build_assign (unshare_expr (ref), var_add),
		    GSI_CONTINUE_LINKING);
  return exit_e;
}

/* Split edge E and insert code to compress data.  */

void
ipa_struct_dco::insert_code_compress_data (dco_info &info, edge e)
{
  gimple_stmt_iterator gsi;
  gimple *stmt;
  unsigned i, j;
  cgraph_node *node;
  dco_data *dd;
  dco_variant *dv;
  auto_vec<tree> dco_data_names;
  auto_vec<tree> dco_data_size_names;
  basic_block bb = e->src;
  class loop *outer_loop = bb->loop_father;

  if (!dom_info_available_p (CDI_DOMINATORS))
    calculate_dominance_info (CDI_DOMINATORS);
  if (!loops_state_satisfies_p (LOOPS_HAVE_PREHEADERS))
    loop_optimizer_init (LOOPS_HAVE_PREHEADERS);
  record_loop_exits ();
  node = cgraph_node::get (current_function_decl);

  /* Generate SSA_NAMEs for dco_data, if they are global addresses.  */
  gsi = gsi_last_bb (bb);
  FOR_EACH_VEC_ELT (info.dco_data_vec, j, dd)
    {
      if (TREE_CODE (dd->var) == SSA_NAME)
	dco_data_names.safe_push (dd->var);
      else
	{
	  tree var = make_ssa_name (TREE_TYPE (dd->var));
	  stmt = gimple_build_assign (var, dd->var);
	  gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);
	  dco_data_names.safe_push (var);
	}
      if (TREE_CODE (dd->upper_bound) == SSA_NAME)
	dco_data_size_names.safe_push (dd->upper_bound);
      else
	{
	  tree var = make_ssa_name (TREE_TYPE (dd->upper_bound));
	  stmt = gimple_build_assign (var, dd->upper_bound);
	  gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);
	  dco_data_size_names.safe_push (var);
	}
    }

  /* Insert code to compress hot data in terms of dyn_path. */
  edge entry_e = single_succ_edge (bb);
  FOR_EACH_VEC_ELT (info.dco_variants, i, dv)
    {
      edge true_e, false_e;
      tree condition
	= build2 (EQ_EXPR, boolean_type_node, info.dyn_path, dv->cond);
      create_empty_if_region_on_edge (entry_e, condition);
      extract_true_false_edges_from_block (entry_e->dest, &true_e, &false_e);

      /* Create function decl and node for compressed single object.  */
      tree compress_single_fn = create_compress_single_fn (info, i, dv);
      cgraph_node *new_node = cgraph_node::get_create (compress_single_fn);
      cgraph_node::add_new_function (compress_single_fn, true);

      /* For each variable(pool) to compress, insert loop like:
	<bb START> :
	_1 = POOL;
	_2 = POOL_SIZE;
	goto <bb COND>;

	<bb COND> :
	# i_1 = PHI <0, i_2(THEN)>
	if (i_1 < _2)
	goto <bb THEN>;
	else
	goto <bb ELSE>;

	<bb THEN> :
	_compress_var_x (_1, i_1);
	i_2 = i_1 + 1;

	<bb ELSE> :
	*/
      edge current_e = true_e;
      for (size_t j = 0; j < info.dco_data_vec.length (); ++j)
	{
	  tree iv_before, iv_after;
	  tree size_type = TREE_TYPE (dco_data_size_names[j]);
	  tree iv = create_tmp_reg (size_type, COMPRESSED_INDEX);
	  loop_p loop
	    = create_empty_loop_on_edge (current_e, build_zero_cst (size_type),
					 build_int_cst (size_type, 1),
					 dco_data_size_names[j], iv, &iv_before,
					 &iv_after, outer_loop);

	  /* Build call statement to compress a single object.  */
	  basic_block latch_bb = loop->latch;
	  gsi = gsi_last_bb (latch_bb);
	  gcall *call = gimple_build_call (compress_single_fn, 2,
					   dco_data_names[j], iv_before);
	  gsi_insert_after (&gsi, call, GSI_CONTINUE_LINKING);
	  node->create_edge (new_node, call, latch_bb->count);

	  current_e = single_exit (loop);
	}

      /* Following current_e, create code to modify dco_refs.  */
      dco_ref *dr;
      FOR_EACH_VEC_ELT (info.dco_refs, j, dr)
	{
	  if (dr->upper_bound)
	    {
	      /* 1) dco_ref is an array, create a loop.  */
	      tree iv_before, iv_after;
	      tree ptr_type
		= dr->orig_type ? dr->orig_type : TREE_TYPE (dr->var);
	      tree size_type = TREE_TYPE (dr->upper_bound);
	      loop_p loop
		= create_empty_loop_on_edge (current_e,
					     build_zero_cst (size_type),
					     build_int_cst (size_type, 1),
					     dr->upper_bound,
					     create_tmp_reg (size_type, NULL),
					     &iv_before, &iv_after, outer_loop);
	      /* Fetch array element.  */
	      gsi = gsi_last_bb (loop->latch);
	      tree var1 = make_ssa_name (ptr_type);
	      gsi_insert_after (&gsi, gimple_build_assign (var1, dr->var),
				GSI_NEW_STMT);
	      tree var_mul = make_ssa_name (long_unsigned_type_node);
	      APPEND_GASSIGN_2 (gsi, var_mul, MULT_EXPR, iv_before,
				TYPE_SIZE_UNIT (TREE_TYPE (ptr_type)));
	      tree var_plus = make_ssa_name (ptr_type);
	      APPEND_GASSIGN_2 (gsi, var_plus, POINTER_PLUS_EXPR, var1,
				var_mul);
	      tree ref_expr = build2 (MEM_REF, TREE_TYPE (ptr_type), var_plus,
				      build_int_cst (ptr_type, 0));
	      if (dr->field)
		ref_expr = build3 (COMPONENT_REF, TREE_TYPE (dr->field),
				   ref_expr, dr->field, NULL_TREE);
	      /* Modify the ref's value.  */
	      insert_code_modify_single_ref (single_succ_edge (loop->latch),
					     ref_expr, dr->source,
					     TYPE_SIZE_UNIT (
					       info.dco_type->type),
					     TYPE_SIZE_UNIT (dv->new_type));
	      current_e = single_exit (loop);
	    }
	  else
	    /* 2) dco_ref is a single ptr.  */
	    current_e
	      = insert_code_modify_single_ref (current_e, dr->var, dr->source,
					       TYPE_SIZE_UNIT (
						 info.dco_type->type),
					       TYPE_SIZE_UNIT (dv->new_type));
	}

      entry_e = false_e;
    }

  return;
}

/* Check STMT to collect all references with the pointer of TYPE into REFS.
   Return true if REFS is not empty. Note that the pointer could be either
   pointer's pointer. */

bool
ipa_struct_dco::gimple_use_dco_type (dco_info &info, gimple *stmt,
				     auto_vec<tree *> &refs)
{
  unsigned i;

  auto_vec<tree *> opnds;
  tree *opnd;

  tree old_lhs = gimple_get_lhs (stmt);
  if (!old_lhs || !get_dco_type_pointer_ref (info, old_lhs))
    /* Used not as DCO_TYPE, so no need to copy it.  */
    return false;

  if (gimple_code (stmt) == GIMPLE_PHI)
    {
      gphi *phi = dyn_cast<gphi *> (stmt);
      opnds.safe_push (gimple_phi_result_ptr (phi));
      for (i = 0; i < gimple_phi_num_args (phi); i++)
	{
	  opnd = gimple_phi_arg_def_ptr (phi, i);
	  opnds.safe_push (opnd);
	}
    }
  else if (is_gimple_assign (stmt))
    {
      for (i = 0; i < gimple_num_ops (stmt); ++i)
	{
	  opnd = gimple_op_ptr (stmt, i);
	  opnds.safe_push (opnd);
	}
    }
  else if (is_gimple_call (stmt))
    {
      if (gimple_call_lhs (stmt) != NULL_TREE)
	opnds.safe_push (gimple_call_lhs_ptr (stmt));
      for (i = 0; i < gimple_call_num_args (stmt); i++)
	{
	  opnd = gimple_call_arg_ptr (stmt, i);
	  opnds.safe_push (opnd);
	}
    }
  else
    gcc_unreachable ();

  FOR_EACH_VEC_ELT (opnds, i, opnd)
    {
      if (get_dco_type_pointer_ref (info, *opnd) != NULL_TREE)
	refs.safe_push (opnd);
    }

  return !refs.is_empty ();
}

/* Return true if def is a pointer, or pointer's pointer, of dco_type. */

bool
ipa_struct_dco::dco_type_pointer_p (dco_info &info, tree def, int *level = 0)
{
  tree type = TREE_TYPE (def);

  TEST (POINTER_TYPE_P (type));

  /* Get the innermost non pointer type */
  while (POINTER_TYPE_P (type))
    {
      type = TREE_TYPE (type);
      if (level)
	(*level)++;
    }

  TEST (types_dco_compatible_p (type, info.dco_type->type));

  return true;
}

/* Return the top level dco_type pointer tree node. */

tree
ipa_struct_dco::get_dco_type_pointer_ref (dco_info &info, tree t)
{
  tree type = TREE_TYPE (t);

  if (TREE_CODE (t) == MEM_REF)
    {
      t = TREE_OPERAND (t, 0);
      while (type != NULL_TREE)
	{
	  if (types_dco_compatible_p (info.dco_type->type, type))
	    return t;
	  type = TREE_TYPE (type);
	}

      return NULL_TREE;
    }

  while (type != NULL_TREE)
    {
      if (types_dco_compatible_p (info.dco_type->type, type))
	return t;
      type = TREE_TYPE (type);
    }

  if (TREE_CODE (t) == COMPONENT_REF)
    {
      t = TREE_OPERAND (t, 0);
      type = TREE_TYPE (t);

      if (types_dco_compatible_p (info.dco_type->type, type))
	{
	  t = TREE_OPERAND (t, 0);
	  return t;
	}
    }

  return NULL_TREE;
}

/* Create it if the PHI is a dco_type pointer. */

void
ipa_struct_dco::insert_code_clone_hot_data_pass1_phi (
  dco_info &info, basic_block bb, auto_vec<gimple *> &old_stmts,
  hash_map<gimple *, gimple *> &stmt_map, auto_vec<tree> &old_defs,
  auto_vec<tree> &new_defs)
{
  /* Copy the PHI nodes and define new SSA_NAME  */
  gphi_iterator end_gpi = gsi_end_phis (bb);
  for (gphi_iterator gpi = gsi_start_phis (bb); !gsi_end_p (gpi);
       gsi_next (&gpi))
    {
      gphi *phi = gpi.phi ();
      tree old_name = gimple_phi_result (phi);

      if (dco_type_pointer_p (info, old_name))
	{
	  /* Clone and set new result. */
	  gphi *copy = create_phi_node (NULL_TREE, bb);
	  for (unsigned j = 0; j < gimple_phi_num_args (phi); ++j)
	    add_phi_arg (copy, gimple_phi_arg_def (phi, j),
			 gimple_phi_arg_edge (phi, j), UNKNOWN_LOCATION);
	  tree new_type = build_pointer_type (info.dco_type->newtype[0]);
	  tree new_name = make_temp_ssa_name (new_type, copy, "");
	  tree *def = gimple_phi_result_ptr (copy);
	  SET_DEF (def, new_name);
	  gimple_set_uid (copy, gimple_uid (phi));

	  old_stmts.safe_push (phi);
	  stmt_map.put (phi, copy);
	  old_defs.safe_push (old_name);
	  new_defs.safe_push (new_name);

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "[CLONE PASS 1] ");
	      print_gimple_stmt (dump_file, phi, 0);
	      fprintf (dump_file, "-> ");
	      print_gimple_stmt (dump_file, copy, 0);
	    }
	}

      if (gpi.phi () == end_gpi.phi ())
	break;
    }
}

/* Return true, if
   (1) the RHS of STMT is pointer's pointer of dco_type
   (2) and, the LHS is not.  */

bool
ipa_struct_dco::dco_type_pointer_escape (dco_info &info, gimple *stmt)
{
  TEST (gimple_assign_single_p (stmt));

  tree lhs = gimple_assign_lhs (stmt);
  tree rhs = gimple_assign_rhs1 (stmt);

  int level = 0;
  TEST (dco_type_pointer_p (info, rhs, &level));
  TEST (level == 2);

  return !dco_type_pointer_p (info, lhs);
}

/* Clone the STMT and define new_lhs if the old_lhs is a dco_pointer. */

gimple *
ipa_struct_dco::create_new_dco_type_pointer_def (dco_info &info, gimple *stmt,
						 auto_vec<tree> &old_defs,
						 auto_vec<tree> &new_defs,
						 gimple_stmt_iterator &gsi)
{
  tree old_lhs = gimple_get_lhs (stmt);
  gimple *copy = gimple_copy (stmt);
  tree new_lhs = gimple_get_lhs (copy);
  static unsigned id = 0;

  /* Build appropriate pointer type. */
  int level = 0;
  tree new_type = info.dco_type->newtype[0];
  if (!dco_type_pointer_p (info, old_lhs, &level))
    return copy;

  while (level)
    {
      new_type = build_pointer_type (new_type);
      level--;
    }

  if (TREE_CODE (old_lhs) == SSA_NAME)
    {
      new_lhs = make_temp_ssa_name (new_type, copy, "");
      gimple_set_lhs (copy, new_lhs);
      update_stmt (copy);

      old_defs.safe_push (old_lhs);
      new_defs.safe_push (new_lhs);
    }
  else if (VAR_P (old_lhs) || TREE_CODE (old_lhs) == COMPONENT_REF)
    {
      gcc_checking_assert (is_gimple_assign (stmt));

      /* Create a new var */
      char *tmp_name = append_suffix ("_hot_dco_var_", id++);
      tree name = get_identifier (tmp_name);
      free (tmp_name);
      new_lhs = build_decl (BUILTINS_LOCATION, VAR_DECL, name, new_type);
      TREE_PUBLIC (new_lhs) = 1;
      TREE_STATIC (new_lhs) = 1;
      DECL_IGNORED_P (new_lhs) = 1;
      DECL_ARTIFICIAL (new_lhs) = 1;
      SET_DECL_ASSEMBLER_NAME (new_lhs, name);
      varpool_node::finalize_decl (new_lhs);

      gimple_set_lhs (copy, new_lhs);
      update_stmt (copy);

      old_defs.safe_push (old_lhs);
      new_defs.safe_push (new_lhs);

      /* Find DCO_DATA or DCO_REF */
      dco_data *dd;
      unsigned j;
      FOR_EACH_VEC_ELT (info.dco_data_vec, j, dd)
	{
	  if (!operand_equal_p (dd->var, old_lhs))
	    continue;

	  dd->cloned_stmt = copy;
	  break;
	}

      dco_ref *df;
      FOR_EACH_VEC_ELT (info.dco_refs, j, df)
	{
	  if (!operand_equal_p (df->var, old_lhs))
	    continue;

	  df->cloned_stmt = copy;

	  if (df->upper_bound == NULL_TREE)
	    break;

	  /* For pointer array, we always use alloca and memset. */
	  new_type = build_pointer_type (new_type);

	  /*alloca_res = alloca (size * upper_bound) */
	  tree num
	    = gimplify_build2 (&gsi, MULT_EXPR, size_type_node, df->upper_bound,
			       TYPE_SIZE_UNIT (new_type));
	  tree alloca_decl = builtin_decl_explicit (BUILT_IN_ALLOCA);
	  gimple *alloca_stmt = gimple_build_call (alloca_decl, 1, num);
	  tree alloca_res = make_temp_ssa_name (new_type, alloca_stmt, "");
	  gimple_call_set_lhs (alloca_stmt, alloca_res);
	  update_stmt (alloca_stmt);

	  /* alloca_res = memset (alloca_res, 0, upper_bound) */
	  tree memset_decl = builtin_decl_implicit (BUILT_IN_MEMSET);
	  gimple *memset_stmt
	    = gimple_build_call (memset_decl, 3, alloca_res, integer_zero_node,
				 df->upper_bound);
	  tree memset_res = make_temp_ssa_name (new_type, memset_stmt, "");
	  gimple_call_set_lhs (memset_stmt, memset_res);
	  update_stmt (memset_stmt);

	  /* new_lhs = alloca_res */
	  gcc_checking_assert (is_gimple_assign (stmt));
	  gimple_assign_set_rhs1 (copy, memset_res);
	  update_stmt (copy);

	  gsi_insert_before (&gsi, alloca_stmt, GSI_SAME_STMT);
	  update_stmt_vdef (alloca_stmt, stmt);
	  gsi_insert_before (&gsi, memset_stmt, GSI_SAME_STMT);
	  update_stmt_vdef (memset_stmt, stmt);

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "-> ");
	      print_gimple_stmt (dump_file, alloca_stmt, 0);
	      fprintf (dump_file, "-> ");
	      print_gimple_stmt (dump_file, memset_stmt, 0);
	    }
	}
    }

  return copy;
}

/* Normalize dco data of void * type, so that following passes can find and
   clone related stmts.  */

void
ipa_struct_dco::normalize_dco_type_uses (dco_info &info)
{
  dco_data *dd;
  unsigned i;

  FOR_EACH_VEC_ELT (info.dco_data_vec, i, dd)
    {
      if (!dd->ssa_def || !VOID_POINTER_P (TREE_TYPE (dd->ssa_def)))
	continue;

      srdecl *decl = find_decl (dd->ssa_def);
      if (!decl || decl->type != info.dco_type)
	continue;

      TREE_TYPE (dd->ssa_def) = build_pointer_type (info.dco_type->type);
    }
}

/* Clone identified stmt using dco_type pointer, and create new defs with
   smaller size. */

void
ipa_struct_dco::insert_code_clone_hot_data_pass1 (
  dco_info &info, auto_vec<gimple *> &old_stmts,
  hash_map<gimple *, gimple *> &stmt_map, auto_vec<tree> &old_defs,
  auto_vec<tree> &new_defs)
{
  gimple *stmt, *copy;
  unsigned i;

  srfunction *srfn = info.start_srfn;

  gcc_checking_assert (!srfn->dco_path.pre_bbs.is_empty ());
  gcc_checking_assert (info.dco_variants.length () == 1);
  gcc_checking_assert (info.dco_type->num_of_new_types == 1);

  /* Clone all stmts using info.dco_type, and create new defs. */
  basic_block bb;
  FOR_EACH_VEC_ELT_REVERSE (srfn->dco_path.pre_bbs, i, bb)
    {
      insert_code_clone_hot_data_pass1_phi (info, bb, old_stmts, stmt_map,
					    old_defs, new_defs);

      /* Copy others and define new SSA_NAME. */
      for (gimple_stmt_iterator gsi = gsi_start_bb (bb); !gsi_end_p (gsi);
	   gsi_next (&gsi))
	{
	  stmt = gsi_stmt (gsi);
	  if (!is_gimple_assign (stmt) && !is_gimple_call (stmt))
	    continue;

	  auto_vec<tree *> refs;
	  if (!gimple_use_dco_type (info, stmt, refs))
	    continue;

	  /* Skip escaping from pointer's pointer, which implies another
	     memory space and has nothing to do with doc_type's pointer. */
	  if (dco_type_pointer_escape (info, stmt))
	    continue;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "[CLONE PASS 1] ");
	      print_gimple_stmt (dump_file, stmt, 0);
	    }

	  /* Create new defs, which could be either SSA_NAME or VAR, if only
	     the LHS type is a DCO type pointer. */
	  copy = create_new_dco_type_pointer_def (info, stmt, old_defs,
						  new_defs, gsi);
	  old_stmts.safe_push (stmt);
	  stmt_map.put (stmt, copy);

	  /* Insert newly created stmt. */
	  gsi_insert_before (&gsi, copy, GSI_SAME_STMT);
	  update_stmt_vdef (copy, stmt);

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "-> ");
	      print_gimple_stmt (dump_file, copy, 0);
	    }
	}
    }
}

/* Return true, if VAR is a dco ref, and it's an array. */

bool
ipa_struct_dco::dco_ref_arrary_p (dco_info &info, tree var)
{
  dco_ref *df;
  unsigned i;
  FOR_EACH_VEC_ELT (info.dco_refs, i, df)
    {
      if (!operand_equal_p (df->var, var))
	continue;

      return (df->upper_bound != NULL_TREE);
    }

  return false;
}

/* Update NEW_STMTS with the NEW_DEFS we have created in pass 1. */

void
ipa_struct_dco::insert_code_clone_hot_data_pass2 (
  dco_info &info, auto_vec<gimple *> &old_stmts,
  hash_map<gimple *, gimple *> &stmt_map, auto_vec<tree> &old_defs,
  auto_vec<tree> &new_defs)
{
  unsigned i;

  /* Scan all stmt copies, and replace all references with new defs. */
  gimple *old_stmt, *new_stmt, **new_stmt_ptr;
  FOR_EACH_VEC_ELT (old_stmts, i, old_stmt)
    {
      auto_vec<tree *> old_refs, new_refs;
      new_stmt_ptr = stmt_map.get (old_stmt);
      gcc_checking_assert (new_stmt_ptr);
      new_stmt = *new_stmt_ptr;

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "[CLONE PASS 2] ");
	  print_gimple_stmt (dump_file, old_stmt, 0);
	  fprintf (dump_file, "-> ");
	  print_gimple_stmt (dump_file, new_stmt, 0);
	}

      if (allocation_stmt_p (new_stmt))
	{
	  tree old_decl = gimple_get_lhs (old_stmt);
	  tree new_decl = gimple_get_lhs (new_stmt);
	  tree type = TREE_TYPE (TREE_TYPE (old_decl));
	  tree old_type = type;
	  tree new_type = TREE_TYPE (TREE_TYPE (new_decl));
	  /* Precondition: void* are replaced already.  */
	  gcc_checking_assert (!(VOID_POINTER_P (TREE_TYPE (old_decl))
				 || VOID_POINTER_P (TREE_TYPE (new_decl))));
	  gimple_stmt_iterator gsi = gsi_for_stmt (new_stmt);
	  if (rewrite_allocation_stmt (as_a<gcall *> (new_stmt), old_decl,
				       new_decl, type, old_type, new_type,
				       &gsi))
	    {
	      gsi_remove (&gsi, true);
	      gsi_prev (&gsi);
	      new_stmt = gsi_stmt (gsi);
	    }
	}
      else
	{
	  /* Collect all dco_type pointer references. */
	  gimple_use_dco_type (info, old_stmt, old_refs);
	  gimple_use_dco_type (info, new_stmt, new_refs);

	  /* Get LHS */
	  tree *old_ref, *new_ref;
	  tree old_lhs = gimple_get_lhs (old_stmt);

	  /* Skip dco_type pointer array intialization, because we have handled
	     it in pass 1. */
	  if (dco_ref_arrary_p (info, old_lhs))
	    continue;

	  /* Scan all operands referring dco_type pointer. */
	  unsigned j;
	  FOR_EACH_VEC_ELT (old_refs, j, old_ref)
	    {
	      new_ref = new_refs[j];

	      /* Skip LHS, because the new def has been created previously. */
	      if (*old_ref == old_lhs)
		{
		  tree ref = get_dco_type_pointer_ref (info, *old_ref);
		  if (ref == *old_ref)
		    continue;
		}

	      /* Update to new def for all other operands. */
	      if (TREE_CODE (*old_ref) == SSA_NAME)
		{
		  gimple *old_def_stmt = SSA_NAME_DEF_STMT (*old_ref);
		  if (gimple_code (old_def_stmt) == GIMPLE_NOP)
		    {
		      /* default_def (i.e. an uninitialized local var)  */
		      tree new_var
			= tree_map_get (old_defs, new_defs, *old_ref);
		      if (!new_var)
			{
			  /* No decl avaliable, create one.  */
			  tree new_type
			    = build_pointer_type (info.dco_type->newtype[0]);
			  tree tmp_var = create_tmp_reg (new_type);
			  new_var = make_ssa_name (new_type);
			  SET_SSA_NAME_VAR_OR_IDENTIFIER (new_var, tmp_var);
			  SSA_NAME_DEF_STMT (new_var) = gimple_build_nop ();
			  set_ssa_default_def (cfun, tmp_var, new_var);
			  old_defs.safe_push (*old_ref);
			  new_defs.safe_push (new_var);
			}
		      *new_ref = new_var;
		    }
		  else
		    {
		      gimple **def_stmt = stmt_map.get (old_def_stmt);
		      gcc_checking_assert (def_stmt);
		      *new_ref = gimple_get_lhs (*def_stmt);
		    }
		}
	      else if (VAR_P (*old_ref))
		{
		  tree new_var = tree_map_get (old_defs, new_defs, *old_ref);
		  gcc_checking_assert (new_var);
		  *new_ref = new_var;
		}
	      else if (TREE_CODE (*old_ref) == COMPONENT_REF
		       || TREE_CODE (*old_ref) == MEM_REF)
		{
		  tree ref = get_dco_type_pointer_ref (info, *old_ref);
		  gcc_checking_assert (ref != NULL_TREE);
		  tree new_var = tree_map_get (old_defs, new_defs, ref);
		  gcc_checking_assert (new_var);

		  /* Change to use new dco_type base. */
		  tree mem_ref = (TREE_CODE (*old_ref) == COMPONENT_REF)
				   ? TREE_OPERAND (*new_ref, 0)
				   : *new_ref;
		  if (*old_ref != ref)
		    {
		      TREE_OPERAND (mem_ref, 0) = new_var;
		      TREE_OPERAND (mem_ref, 1)
			= copy_node (TREE_OPERAND (mem_ref, 1));
		      TREE_TYPE (mem_ref) = TREE_TYPE (TREE_TYPE (new_var));
		      TREE_TYPE (TREE_OPERAND (mem_ref, 1))
			= TREE_TYPE (new_var);

		      /* Change to use new field defined in new dco type. */
		      tree base;
		      srtype *t;
		      srfield *f;
		      if (get_base_type (*old_ref, base, t, f))
			{
			  TREE_OPERAND (*new_ref, 1) = f->newfield[0];
			  TREE_TYPE (*new_ref) = TREE_TYPE (f->newfield[0]);

			  if (!insert_encode_decode_for_clone (old_stmt,
							       new_stmt))
			    {
			      tree rhs = gimple_assign_rhs1 (new_stmt);
			      gimple_stmt_iterator gsi
				= gsi_for_stmt (new_stmt);
			      tree new_rhs
				= build_convert_gimple (f->newfield[0], rhs,
							&gsi);
			      if (new_rhs)
				gimple_assign_set_rhs1 (new_stmt, new_rhs);
			    }
			}
		    }
		  else
		    *new_ref = new_var;
		}
	      else
		gcc_unreachable ();
	    }

	  /* Change offset for pointer_plus.  */
	  if (gimple_code (new_stmt) == GIMPLE_ASSIGN
	      && gimple_assign_rhs_code (new_stmt) == POINTER_PLUS_EXPR
	      && types_dco_compatible_p (info.dco_type->type,
					 TREE_TYPE (TREE_TYPE (old_lhs))))
	    {
	      /* Change:
		    new_lhs = new_rhs1 + old_offset;
		 into:
		    new_offset = num * new_struct_size;
		    new_lhs = new_rhs1 + new_offset;
	       */
	      tree rhs2 = gimple_assign_rhs2 (new_stmt);
	      tree newlhs = gimple_assign_lhs (new_stmt);
	      tree num;
	      if (!is_result_of_mult (rhs2, &num, info.dco_type->type) || !num)
		internal_error ("the rhs of pointer was not a multiplicate");

	      gimple_stmt_iterator gsi = gsi_for_stmt (new_stmt);
	      tree newsize = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (newlhs)));
	      tree new_offset
		= gimplify_build2 (&gsi, MULT_EXPR, sizetype, num, newsize);
	      gimple_assign_set_rhs2 (new_stmt, new_offset);
	    }
	}

      if (gimple_code (new_stmt) == GIMPLE_PHI)
	new_stmt = update_phi (dyn_cast<gphi *> (new_stmt));
      else
	update_stmt (new_stmt);
      update_stmt (old_stmt);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "=> ");
	  print_gimple_stmt (dump_file, new_stmt, 0);
	}
    }
  update_ssa (TODO_update_ssa);
}

/* If an old_stmt reqire encode/decode, we will do it for the new_stmt.
   This is because all old_stmts are before fclose, and they originally
   don't need encode/decode, but for new_stmts we created for hot data,
   we have to apply encode and decode.  Return true if successful.  */

bool
ipa_struct_dco::insert_encode_decode_for_clone (gimple *old_stmt,
						gimple *new_stmt)
{
  TEST (gimple_assign_single_p (old_stmt));

  tree lhs = gimple_assign_lhs (old_stmt);
  tree rhs = gimple_assign_rhs1 (old_stmt);
  bool read_p = (TREE_CODE (rhs) == COMPONENT_REF);

  tree base;
  srtype *t;
  srfield *f;
  TEST (get_base_type (read_p ? rhs : lhs, base, t, f) && f->dynamic_df);

  tree fn
    = read_p ? f->dynamic_df->cond->decode_fn : f->dynamic_df->cond->encode_fn;
  TEST (fn != NULL_TREE);

  gimple_stmt_iterator gsi = gsi_for_stmt (new_stmt);
  tree newrhs = gimple_assign_rhs1 (new_stmt);
  tree newlhs = gimple_assign_lhs (new_stmt);

  dco_closure *closure_info = f->get_closure ();
  gcc_checking_assert (closure_info->change_p (old_stmt));

  tree res = closure_info->encode_decode_rhs (newrhs, fn);
  res = gimplify_build1 (&gsi, NOP_EXPR, TREE_TYPE (newlhs), res);
  gimple_assign_set_rhs1 (new_stmt, res);
  return true;
}

/* Return true if each hot data is in continuous memory space. We must guarantee
   this, if we use cloning data solution.  */

bool
ipa_struct_dco::hot_data_continuous_p (dco_info &info)
{
  srfunction *srfn = info.start_srfn;

  gcc_checking_assert (!srfn->dco_path.pre_bbs.is_empty ());

  basic_block bb;
  unsigned i;
  FOR_EACH_VEC_ELT_REVERSE (srfn->dco_path.pre_bbs, i, bb)
    {
      /* Copy others and define new SSA_NAME. */
      for (gimple_stmt_iterator gsi = gsi_start_bb (bb); !gsi_end_p (gsi);
	   gsi_next (&gsi))
	{
	  gimple *stmt = gsi_stmt (gsi);

	  if (!is_gimple_assign (stmt))
	    continue;

	  tree old_lhs = gimple_get_lhs (stmt);
	  if (!dco_type_pointer_p (info, old_lhs, 0))
	    continue;

	  if (TREE_CODE (old_lhs) == COMPONENT_REF)
	    {
	      tree base = TREE_OPERAND (old_lhs, 0);
	      if (!VAR_P (base))
		{
		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file,
			       "hot data is not in continuous memory space!\n");
		      print_gimple_stmt (dump_file, stmt, 0);
		    }
		  return false;
		}
	    }
	}
    }

  return true;
}

/* In terms of DCO_DATA and DCO_REF we have identified previously, we insert
   code to clone all of hot data and related pointers with smaller memory. */

void
ipa_struct_dco::insert_code_clone_hot_data (dco_info &info)
{
  auto_vec<gimple *> old_stmts;
  hash_map<gimple *, gimple *> stmt_map;
  auto_vec<tree> old_defs;
  auto_vec<tree> new_defs;

  /* Normalize dco data of void * type.  */
  normalize_dco_type_uses (info);

  /* Define new LHS for the stmt copy. */
  insert_code_clone_hot_data_pass1 (info, old_stmts, stmt_map, old_defs,
				    new_defs);

  /* Update all refs using the old LHS with the newly defined LHS above. */
  insert_code_clone_hot_data_pass2 (info, old_stmts, stmt_map, old_defs,
				    new_defs);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n[AFTER HOT DATA CLONE]\n");
      basic_block bb;
      unsigned i;
      FOR_EACH_VEC_ELT_REVERSE (info.start_srfn->dco_path.pre_bbs, i, bb)
	{
	  gimple_dump_bb (dump_file, bb, 0, TDF_SLIM | TDF_VOPS);
	  fprintf (dump_file, "\n");
	}
    }
}

/* Insert a call to builtin free to free the memory of VAR.  */

static void
insert_code_free_data (tree var, gimple_stmt_iterator *gsi)
{
  if (!VAR_P (var))
    var = unshare_expr (var);
  if (TREE_CODE (var) != SSA_NAME)
    var = gimplify_build1 (gsi, NOP_EXPR, TREE_TYPE (var), var);

  gimple *free_stmt
    = gimple_build_call (builtin_decl_explicit (BUILT_IN_FREE), 1, var);
  gsi_insert_before (gsi, free_stmt, GSI_SAME_STMT);
}

/* At run-time, we need to switch to all DCO_DATA and DCO_REF for dyn_path,
   i.e. copy cloned_var back to var. If upper_bound in DCO_REF is not NULL,
   cloned_var will be the base of memory on stack. */

void
ipa_struct_dco::insert_code_switch_data (dco_info &info, edge e)
{
  srfunction *srfn = info.start_srfn;

  /* Path must have been cloned. */
  gcc_checking_assert (!srfn->dco_path.reach_bbs.is_empty ());
  gcc_checking_assert (e);

  if (!dom_info_available_p (CDI_DOMINATORS))
    calculate_dominance_info (CDI_DOMINATORS);

  /* Insert if-else structure on dyn_path check.  */
  edge true_e, false_e;
  tree hot_path_val = build_int_cst (TREE_TYPE (info.dyn_path),
				     (1 << info.dco_conds.length ()) - 1);
  tree condition
    = build2 (EQ_EXPR, boolean_type_node, info.dyn_path, hot_path_val);
  create_empty_if_region_on_edge (e, condition);
  extract_true_false_edges_from_block (e->dest, &true_e, &false_e);

  /* Insert code switch DCO_DATA.  */
  unsigned i;
  dco_data *dd;
  basic_block bb = true_e->dest;
  gimple_stmt_iterator gsi = gsi_last_bb (bb);
  FOR_EACH_VEC_ELT (info.dco_data_vec, i, dd)
    {
      gcc_checking_assert (dd->cloned_stmt);
      tree rhs = gimple_assign_rhs1 (dd->cloned_stmt);
      if (tree new_rhs = build_convert_gimple (dd->var, rhs, &gsi))
	rhs = new_rhs;
      gimple *stmt = gimple_build_assign (unshare_expr (dd->var), rhs);
      gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);
    }

  /* To free original/cloned vars on the true/false edge respectively.  */
  gimple_stmt_iterator gsi1 = gsi_start_bb (true_e->dest);
  gimple_stmt_iterator gsi2 = gsi_start_bb (false_e->dest);
  FOR_EACH_VEC_ELT (info.dco_data_vec, i, dd)
    {
      insert_code_free_data (dd->var, &gsi1);
      tree cloned_var = gimple_assign_rhs1 (dd->cloned_stmt);
      insert_code_free_data (cloned_var, &gsi2);
    }

  /* Insert code switch DCO_REF.  */
  dco_ref *dr;
  FOR_EACH_VEC_ELT (info.dco_refs, i, dr)
    {
      gcc_checking_assert (dr->cloned_stmt);
      tree cloned_var = gimple_assign_rhs1 (dr->cloned_stmt);
      if (TREE_CODE (cloned_var) != SSA_NAME)
	cloned_var = gimplify_build1 (&gsi, NOP_EXPR, TREE_TYPE (cloned_var),
				      cloned_var);
      if (dr->upper_bound)
	{
	  /* Insert code as:
	       memcpy (REF, REF_cloned, upper_bound * sizeof(element_type));  */
	  tree ptr_type = dr->orig_type ? dr->orig_type : TREE_TYPE (dr->var);
	  tree num
	    = gimplify_build2 (&gsi, MULT_EXPR, size_type_node, dr->upper_bound,
			       TYPE_SIZE_UNIT (ptr_type));
	  tree dest
	    = gimplify_build1 (&gsi, NOP_EXPR, TREE_TYPE (dr->var), dr->var);
	  gimple *stmt
	    = gimple_build_call (builtin_decl_explicit (BUILT_IN_MEMCPY), 3,
				 dest, cloned_var, num);
	  gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);
	}
      else
	{
	  if (tree new_rhs = build_convert_gimple (dr->var, cloned_var, &gsi))
	    cloned_var = new_rhs;
	  gimple *stmt
	    = gimple_build_assign (unshare_expr (dr->var), cloned_var);
	  gsi_insert_after (&gsi, stmt, GSI_NEW_STMT);
	}
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\n[INSERT CODE SWITCH DATA] after insertion:\n");
      dump_bb (dump_file, bb, 2, TDF_DETAILS);
    }
}

/* Add some code for DCO dynamic checking and data compressing. */

void
ipa_struct_dco::add_dynamic_checking (dco_info &info)
{
  gimple_stmt_iterator gsi = gsi_for_stmt (info.fclose_stmt);
  basic_block bb = gsi_bb (gsi);
  gcc_assert (single_succ_p (bb));

  SET_CFUN (info.start_srfn);

  insert_code_calc_dyn_path (info);
  if (flag_ipa_dco_clone_data)
    {
      insert_code_clone_hot_data (info);
      insert_code_switch_data (info, single_succ_edge (bb));
    }
  else
    {
      insert_code_compress_data (info, single_succ_edge (bb));
    }

  cgraph_edge::rebuild_edges ();
  update_ssa (TODO_update_ssa_only_virtuals);
}

/* Clean up all of write stmts to shadow field by changing the RHS to be true,
   which means it is a shadow. */

void
ipa_struct_dco::cleanup_shadow_write (dco_info &info, bool dynamic = false)
{
  unsigned i, j;
  dco_field *df;
  gimple *stmt;

  FOR_EACH_VEC_ELT (info.dco_fields, i, df)
    {
      if (!df->original)
	continue;

      FOR_EACH_VEC_ELT (df->shadow_stmts, j, stmt)
	{
	  SET_CFUN (df->shadow_stmts_func[j]);

	  gcc_checking_assert (gimple_assign_single_p (stmt));
	  if (dynamic)
	    {
	      gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
	      gsi_remove (&gsi, true);
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "[DCO REMOVE STMT] ");
		  print_gimple_stmt (dump_file, stmt, 0);
		}
	    }
	  else
	    {
	      gimple_assign_set_rhs1 (stmt,
				      build_int_cst (TREE_TYPE (df->field), 1));
	      update_stmt (stmt);
	    }
	}
    }
}

/* Insert the followings for shadow data read before STMT. The IDX operand is
   the shadow data.

   * For static: (shadow_field == true) ? original_field : 0
   * For dynamic: (original_field != init_const) ? original_field : 0 */

void
ipa_struct_dco::insert_shadow_stmt (gimple *stmt, unsigned idx, dco_field *df,
				    tree base, bool dynamic = false)
{
  tree shadow = gimple_op (stmt, idx);
  tree original = build_field_ref (base, df->original->fielddecl);

  /* Insert new stmt immediately before stmt. */
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);

  /* original_ssa = original */
  tree original_ssa = make_temp_ssa_name (TREE_TYPE (original), NULL, "");
  gimple *original_stmt = gimple_build_assign (original_ssa, original);
  gsi_insert_before (&gsi, original_stmt, GSI_SAME_STMT);

  tree cmp;
  if (dynamic)
    {
      gcc_checking_assert (df->init_consts.length () == 1);
      tree init_const = df->init_consts[0];

      /* new_shadow_ssa = ( original_ssa != init_const ? original_ssa : 0 ) */
      cmp = fold_build2 (NE_EXPR, boolean_type_node, original_ssa, init_const);
    }
  else
    {
      /* shadow_ssa = shadow */
      tree shadow_ssa = make_temp_ssa_name (TREE_TYPE (shadow), NULL, "");
      gimple *shadow_stmt = gimple_build_assign (shadow_ssa, shadow);
      gsi_insert_before (&gsi, shadow_stmt, GSI_SAME_STMT);
      update_stmt (shadow_stmt);

      /* new_shadow_ssa = ( shadow_ssa == true ? original_ssa : 0 ) */
      cmp = fold_build2 (EQ_EXPR, boolean_type_node, shadow_ssa,
			 build_int_cst (TREE_TYPE (shadow), 1));
    }

  tree new_shadow = build_cond_expr (cmp, original_ssa,
				     build_int_cst (TREE_TYPE (shadow), 0));
  new_shadow = force_gimple_operand_gsi (&gsi, new_shadow, true, NULL, true,
					 GSI_SAME_STMT);
  tree new_shadow_ssa = make_temp_ssa_name (TREE_TYPE (shadow), NULL, "");
  gimple *new_shadow_stmt = gimple_build_assign (new_shadow_ssa, new_shadow);
  gsi_insert_before (&gsi, new_shadow_stmt, GSI_SAME_STMT);

  gimple_set_op (stmt, idx, new_shadow_ssa);
  update_stmt (original_stmt);
  /* Add a new rd_change stmt.  */
  df->original->get_closure ()->add_rd_change (original_stmt);
  update_stmt (new_shadow_stmt);
  update_stmt (stmt);
}

/* Rewrite all of read of shadow field by using question expression. */

void
ipa_struct_dco::rewrite_shadow_read (dco_info &info, bool dynamic = false)
{
  unsigned i;
  srfunction *srfn;

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      basic_block bb = NULL;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
	       gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (!is_gimple_assign (stmt))
		continue;

	      for (unsigned j = 1; j < gimple_num_ops (stmt); ++j)
		{
		  srtype *t;
		  srfield *f;
		  tree base;
		  tree opnd = gimple_op (stmt, j);
		  if (!get_base_type (opnd, base, t, f))
		    continue;
		  if (t != info.dco_type)
		    continue;

		  unsigned k;
		  dco_field *df;
		  FOR_EACH_VEC_ELT (info.dco_fields, k, df)
		    {
		      if (!df->original)
			continue;
		      if (df->field != f->fielddecl)
			continue;

		      insert_shadow_stmt (stmt, j, df, base, dynamic);
		      break;
		    }
		}
	    }
	}
    }
}

/* Do Static-DCO transformation, return the TODOs requested.  */

unsigned
ipa_struct_dco::static_dco_transform (dco_info &info)
{
  /* Do Static-DCO transformation.  */
  if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_STATIC_SHADOW))
    {
      cleanup_shadow_write (info);
      rewrite_shadow_read (info);
    }

  bool status = create_new_types (info);
  gcc_checking_assert (status && info.dco_type->num_of_new_types == 1
		       && sdco_type_idx == 0);

  rewrite_static_dco_funcs (info);
  return TODO_remove_functions | TODO_verify_all;
}

/* Do Dynamic-DCO transformation, return the TODOs requested.  */

unsigned
ipa_struct_dco::dynamic_dco_transform (dco_info &info)
{
  /* Do Static-DCO transformation.  */
  if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_DYNAMIC_SHADOW))
    {
      cleanup_shadow_write (info, true);
      rewrite_shadow_read (info, true);
    }

  /* Create all dco variants in terms of classified dco conditions. */
  if (!create_dco_variants (info))
    return 0;

  num_new_paths = info.dco_variants.length ();
  if (num_new_paths > MAX_NUM_NEW_TYPES)
    return 0;

  /* Create new dynamic and static DCO types. */
  bool status = create_new_types (info);
  gcc_checking_assert (status
		       && info.dco_type->num_of_new_types == num_new_paths);

  /* Insert encode/decode functions.  */
  unsigned i;
  dco_cond *dc;
  FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
    {
      dc->encode_fn = create_compress_field_fn (dc, i, 0);
      dc->decode_fn = create_compress_field_fn (dc, i, 1);
    }

  clone_dco_paths (info);
  rewrite_dco_paths (info);
  add_dynamic_checking (info);

  /* Remove functions that may not be called.  */
  return TODO_verify_all;
}

/* Strip the copy with typecasting of int or unsigned int.  */

gimple *
strip_copy_stmts (gimple *stmt)
{
  while (is_copy_int (stmt))
    {
      tree rhs = gimple_assign_rhs1 (stmt);
      stmt = SSA_NAME_DEF_STMT (rhs);
    }
  return stmt;
}

static bool
calloc_mem_base_ssa_p (tree var)
{
  if (TREE_CODE (var) == SSA_NAME)
    {
      gimple *def_stmt = SSA_NAME_DEF_STMT (var);
      return def_stmt && gimple_call_builtin_p (def_stmt, BUILT_IN_CALLOC);
    }
  return false;
}

/* The the plus with the 1st array index (i.e. const 1) generated by
   struct-reorg.  */

gimple *
strip_plus_1st_array_index (gimple *stmt)
{
  if (!gimple_assign_rhs_code_p (stmt, PLUS_EXPR))
    return stmt;

  tree rhs1 = gimple_assign_rhs1 (stmt);
  tree rhs2 = gimple_assign_rhs2 (stmt);
  if (TREE_CODE (rhs2) != SSA_NAME)
    return stmt;

  gimple *rhs2_stmt = SSA_NAME_DEF_STMT (rhs2);
  if (!rhs2_stmt)
    return stmt;

  /* 1 + rhs2? */
  if (integer_onep (rhs1))
    return rhs2_stmt;

  if (TREE_CODE (rhs1) != SSA_NAME)
    return stmt;

  /* rhs1 = 1;
     rhs1 + rhs2; */
  gimple *rhs1_stmt = SSA_NAME_DEF_STMT (rhs1);
  if (!rhs1_stmt || !gimple_assign_single_p (rhs1_stmt)
      || !integer_onep (gimple_assign_rhs1 (rhs1_stmt)))
    return stmt;

  return rhs2_stmt;
}

static void
set_if_unknown (DCO_KIND &dco_kind, DCO_KIND val)
{
  if (dco_kind == UNKNOWN_KIND)
    dco_kind = val;
}

/* Return true if the rhs of STMT is defined by a sscanf call stmt. The INPUT
   will be the gimple who define the SSA for the input variable. */

bool
ipa_struct_dco::find_sscanf (gimple *stmt, gimple *&sscanf_stmt, gimple *&input,
			     tree &mem_base, DCO_KIND &dco_kind)
{
  tree rhs;
  gimple *stmt1, *stmt2;
  tree vuse;
  tree callee;
  const char *fn_name;
  tree rhs1, rhs2;
  gimple *rhs1_stmt, *rhs2_stmt;
  bool found_var;
  tree arg, arg_v;
  tree var;
  enum tree_code rhs_code;
  auto_vec<gimple *> var_stmts;

  /* Check pattern dco_type->field = _ssa_name */
  TEST (gimple_assign_single_p (stmt));
  rhs = gimple_assign_rhs1 (stmt);
  TEST (TREE_CODE (rhs) == SSA_NAME);
  stmt1 = SSA_NAME_DEF_STMT (rhs);
  stmt1 = strip_copy_stmts (stmt1);

  if (dco_kind == ARRAY_INDEX)
    {
      stmt1 = strip_plus_1st_array_index (stmt1);
      stmt1 = strip_copy_stmts (stmt1);
    }

  /* Search backward to find a VAR following def/use chain. */
  if (gimple_assign_rhs_code_p (stmt1, POINTER_PLUS_EXPR))
    {
      rhs1 = gimple_assign_rhs1 (stmt1);
      rhs2 = gimple_assign_rhs2 (stmt1);
      TEST (TREE_CODE (rhs1) == SSA_NAME && TREE_CODE (rhs2) == SSA_NAME);
      if (mem_base != NULL)
	{
	  TEST (mem_base == rhs1);
	}
      else
	{
	  TEST (
	    gimple_call_builtin_p (SSA_NAME_DEF_STMT (rhs1), BUILT_IN_CALLOC));
	  mem_base = rhs1;
	}

      /* Check a multiplication */
      stmt1 = SSA_NAME_DEF_STMT (rhs2);
      rhs_code = gimple_assign_rhs_code (stmt1);
      TEST (rhs_code == MULT_EXPR);
      rhs1 = gimple_assign_rhs1 (stmt1);
      rhs2 = gimple_assign_rhs1 (stmt1);
      TEST (TREE_CODE (rhs1) == SSA_NAME);
      TEST (TREE_CODE (TREE_TYPE (rhs2)) == INTEGER_TYPE);

      /* Skip a copy */
      stmt1 = SSA_NAME_DEF_STMT (rhs1);
      TEST (is_copy_int (stmt1));
      rhs = gimple_assign_rhs1 (stmt1);
      TEST (TREE_CODE (rhs) == SSA_NAME);

      /* Check an addition */
      stmt1 = SSA_NAME_DEF_STMT (rhs);
      if (gimple_assign_rhs_code_p (stmt1, PLUS_EXPR))
	{
	  rhs = gimple_assign_rhs2 (stmt1);
	  TEST (TREE_CODE (rhs) == SSA_NAME);
	  stmt1 = SSA_NAME_DEF_STMT (rhs);
	}

      /* Must be a copy from a var. */
      TEST (gimple_assign_single_p (stmt1));
      TEST (VAR_P (gimple_assign_rhs1 (stmt1)))
      var_stmts.safe_push (stmt1);

      set_if_unknown (dco_kind, ARRAY_POINTER);
    }
  else if (gimple_assign_rhs_code_p (stmt1, PLUS_EXPR))
    {
      rhs1 = gimple_assign_rhs1 (stmt1);
      rhs2 = gimple_assign_rhs2 (stmt1);
      TEST (TREE_CODE (rhs1) == SSA_NAME && TREE_CODE (rhs2) == SSA_NAME);

      rhs1_stmt = SSA_NAME_DEF_STMT (rhs1);
      rhs2_stmt = SSA_NAME_DEF_STMT (rhs2);

      if (is_copy (rhs1_stmt, unsigned_type_node)
	  && is_copy (rhs2_stmt, unsigned_type_node))
	{
	  rhs = gimple_assign_rhs1 (rhs1_stmt);
	  TEST (TREE_CODE (rhs) == SSA_NAME);
	  stmt1 = SSA_NAME_DEF_STMT (rhs);

	  rhs = gimple_assign_rhs1 (rhs2_stmt);
	  TEST (TREE_CODE (rhs) == SSA_NAME);
	  stmt2 = SSA_NAME_DEF_STMT (rhs);

	  TEST (gimple_assign_single_p (stmt1)
		&& gimple_assign_single_p (stmt2));

	  /* One of the operends of the addition must be a copy from a var. */
	  if (!VAR_P (gimple_assign_rhs1 (stmt1)))
	    {
	      TEST (VAR_P (gimple_assign_rhs1 (stmt2)))
	      stmt1 = stmt2;
	    }
	  var_stmts.safe_push (stmt1);

	  set_if_unknown (dco_kind, ARRAY_INDEX);
	}
      else if (gimple_assign_single_p (rhs1_stmt)
	       && gimple_assign_single_p (rhs2_stmt))
	{
	  if (VAR_P (gimple_assign_rhs1 (rhs1_stmt)))
	    var_stmts.safe_push (rhs1_stmt);
	  if (VAR_P (gimple_assign_rhs1 (rhs2_stmt)))
	    var_stmts.safe_push (rhs2_stmt);

	  set_if_unknown (dco_kind, CLOSURE_INT);
	}
      else
	{
	  /* Check a peephole pattern like below in reversed order,
	     _196 = hD.7580;
	     _197 = (long unsigned intD.4695) _196;
	     _198 = _197 * 96;
	     PPI_rhs2_cast_1908 = (_reorg_SP_ptr_type.dfe.reorder) _198;
	     PtrPlusInt_Adj_1907 = PPI_rhs2_cast_1908 / 96;
	     PtrPlusInt_1906 = PPI_rhs1_cast_1909 + PtrPlusInt_Adj_1907;  */

	  /* For addition. */
	  if (is_copy_int (rhs1_stmt) && !is_copy_int (rhs2_stmt))
	    stmt1 = rhs2_stmt;
	  else if (!is_copy_int (rhs1_stmt) && is_copy_int (rhs2_stmt))
	    stmt1 = rhs1_stmt;
	  else
	    return false;

	  /* Expect a DIV here. */
	  TEST (is_gimple_assign (stmt1));
	  rhs_code = gimple_assign_rhs_code (stmt1);
	  TEST (rhs_code == EXACT_DIV_EXPR || rhs_code == TRUNC_DIV_EXPR);
	  rhs = gimple_assign_rhs1 (stmt1);
	  TEST (TREE_CODE (rhs) == SSA_NAME);

	  /* Skip a copy */
	  stmt1 = SSA_NAME_DEF_STMT (rhs);
	  TEST (is_copy_int (stmt1));
	  rhs = gimple_assign_rhs1 (stmt1);
	  TEST (TREE_CODE (rhs) == SSA_NAME);

	  /* Check a multiplication */
	  stmt1 = SSA_NAME_DEF_STMT (rhs);
	  rhs_code = gimple_assign_rhs_code (stmt1);
	  TEST (rhs_code == MULT_EXPR);
	  rhs = gimple_assign_rhs1 (stmt1);
	  TEST (TREE_CODE (rhs) == SSA_NAME);

	  /* Skip an int copy */
	  stmt1 = SSA_NAME_DEF_STMT (rhs);
	  TEST (is_copy_int (stmt1));
	  rhs = gimple_assign_rhs1 (stmt1);
	  TEST (TREE_CODE (rhs) == SSA_NAME);

	  /* Check an addition */
	  stmt1 = SSA_NAME_DEF_STMT (rhs);
	  if (gimple_assign_rhs_code_p (stmt1, PLUS_EXPR))
	    {
	      rhs = gimple_assign_rhs2 (stmt1);
	      TEST (TREE_CODE (rhs) == SSA_NAME);
	      stmt1 = SSA_NAME_DEF_STMT (rhs);
	    }

	  /* Find a var. */
	  TEST (gimple_assign_single_p (stmt1));
	  rhs = gimple_assign_rhs1 (stmt1);
	  TEST (VAR_P (rhs));
	  var_stmts.safe_push (stmt1);

	  set_if_unknown (dco_kind, ARRAY_POINTER);
	}
    }
  else
    {
      /* Check pattern _ssa_name = var */
      TEST (gimple_assign_single_p (stmt1));
      TEST (VAR_P (gimple_assign_rhs1 (stmt1)));
      var_stmts.safe_push (stmt1);

      set_if_unknown (dco_kind, CLOSURE_INT);
    }

  unsigned i;
  FOR_EACH_VEC_ELT (var_stmts, i, stmt1)
    {
      input = stmt1;

      /* This var will be read from a sscanf. */
      var = gimple_assign_rhs1 (stmt1);

      /* Search backward to find sscanf following vdef/vuse chain until finding
	 a NOP stmt that doesn't belong to any block. */
      while (gimple_bb (stmt1))
	{
	  vuse = gimple_vuse (stmt1);
	  if (!vuse)
	    break;
	  stmt1 = SSA_NAME_DEF_STMT (vuse);
	  if (gimple_code (stmt1) == GIMPLE_CALL)
	    {
	      callee = gimple_call_fn (stmt1);
	      if (callee != NULL_TREE && TREE_CODE (callee) == OBJ_TYPE_REF)
		continue;

	      callee = gimple_call_fndecl (stmt1);
	      fn_name = get_func_name (callee);
	      if (!fn_name || strcmp (fn_name, "sscanf") != 0)
		continue;

	      /* The sscanf stmt must use the var we have detected. */
	      found_var = false;
	      for (unsigned i = 2; i < gimple_call_num_args (stmt1); ++i)
		{
		  arg = gimple_call_arg (stmt1, i);
		  if (TREE_CODE (arg) != ADDR_EXPR)
		    continue;
		  arg_v = TREE_OPERAND (arg, 0);
		  if (arg_v != var)
		    continue;
		  found_var = true;
		  break;
		}
	      TEST (found_var);

	      sscanf_stmt = stmt1;

	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "[DCO FOUND SSCANF] ");
		  print_gimple_stmt (dump_file, stmt1, 0);
		}

	      return true;
	    }
	}
    }

  return false;
}

/* Return the file handler, which is used by a fget and read out a string for
   the given SSCANF. */

tree
ipa_struct_dco::find_fh (gimple *sscanf_stmt)
{
  tree sscanf_arg0;
  tree fget_arg0;
  tree vuse;
  gimple *stmt;
  tree callee;
  const char *fn_name;

  vuse = gimple_vuse (sscanf_stmt);
  stmt = SSA_NAME_DEF_STMT (vuse);
  if (gimple_code (stmt) != GIMPLE_CALL)
    return NULL_TREE;

  callee = gimple_call_fn (stmt);
  if (callee != NULL_TREE && TREE_CODE (callee) == OBJ_TYPE_REF)
    return NULL_TREE;

  callee = gimple_call_fndecl (stmt);
  fn_name = get_func_name (callee);
  if (!fn_name || strcmp (fn_name, "fgets") != 0)
    return NULL_TREE;

  /* Check fget is using the string for sscanf. */
  fget_arg0 = gimple_call_arg (stmt, 0);
  sscanf_arg0 = gimple_call_arg (sscanf_stmt, 0);
  if (TREE_OPERAND (fget_arg0, 0) != TREE_OPERAND (sscanf_arg0, 0))
    return NULL_TREE;

  return gimple_call_arg (stmt, 2);
}

bool
ipa_struct_dco::is_stmt_before_fclose (dco_info &info, gimple *stmt,
				       symtab_node *node)
{
  gcc_checking_assert (info.fclose_stmt);
  srfunction *f = find_function (dyn_cast<cgraph_node *> (node));
  gcc_checking_assert (f);

  /* If array allocations are outside start-point's function, we may need to
     create global vars to record the sizes.  */
  return f->dco_path.pre_bbs.contains (gimple_bb (stmt));
}

/*  If TYPE1 and TYPE2 should be considered compatible by DCO.  */

bool
ipa_struct_dco::types_dco_compatible_p (tree type1, tree type2)
{
  return types_compatible_p (type1, type2) || types_dco_equal_p (type1, type2);
}

/*  If TYPE1 and TYPE2 should be considered equal by DCO.  */

bool
ipa_struct_dco::types_dco_equal_p (tree type1, tree type2)
{
  if (type1 == type2)
    return true;
  TEST (TREE_CODE (type1) == TREE_CODE (type2));

  const char *tname1;
  const char *tname2;
  size_t len1;
  size_t len2;
  const char *p;

  switch (TREE_CODE (type1))
    {
    case POINTER_TYPE:
      return types_dco_equal_p (inner_type (type1), inner_type (type2));

    case RECORD_TYPE:
      /* Handle types generated by structure field reorganize optimizations. */
      tname1 = get_type_name (type1);
      tname2 = get_type_name (type2);
      TEST (tname1 && tname2);
      len1 = strlen (tname1);
      len2 = strlen (tname2);
      if (len1 > len2)
	{
	  std::swap (len1, len2);
	  std::swap (tname1, tname2);
	}
      p = strstr (tname2, tname1);
      TEST (p);
      p += len1;
      /* As suffixes with '.' are generated by compiler, should be safe to skip
	 the rest of p.  */
      return (
	STRING_STARTS_WITH (p, ".reorder") || STRING_STARTS_WITH (p, ".dfe")
	|| STRING_STARTS_WITH (p, ".reorg") || STRING_STARTS_WITH (p, ".sdco")
	|| STRING_STARTS_WITH (p, ".ddco"));

    default:
      return false;
    }
}

/* Return number of objects of TYPE following define chain from STMT.
   If the number is not certain, set ERROR so we can abort DCO.
   If SSA_DEF is not NULL, the ssa_name of allocated ptr will be assigned to it.
 */

tree
ipa_struct_dco::get_allocate_size_iterate (tree type, gimple *stmt,
					   tree *ssa_def, bool *error)
{
  tree lhs, rhs, size;
  const char *decl_name;
  tree prev_type, mul_by;
  gassign *assign, *plus_stmt, *mul_stmt;
  if (error)
    *error = false;

  switch (gimple_code (stmt))
    {
    case GIMPLE_ASSIGN:
      assign = as_a<gassign *> (stmt);
      rhs = gimple_assign_rhs1 (assign);
      if ((gimple_assign_single_p (assign) || gimple_assign_cast_p (assign))
	  && TREE_CODE (rhs) == SSA_NAME)
	{
	  lhs = gimple_assign_lhs (assign);
	  size = get_allocate_size_iterate (type, SSA_NAME_DEF_STMT (rhs),
					    ssa_def, error);
	  /* Handle the global arrays split by struct_reorg:
	     1) The new array ptrs are marked with suffix ".gptr".
	     2) The array ptr are calculated with form:
		.gptr0 = calloc(NUM, size_all);
		.gptr1 = .gptr0 + NUM * sizeof (TREE_TYPE(.gptr0));
		.gptr2 = .gptr1 + NUM * sizeof (TREE_TYPE(.gptr1));
		...
	   */
	  if (!size && !(error && *error) && TREE_CODE (lhs) == VAR_DECL
	      && (decl_name = IDENTIFIER_POINTER (DECL_NAME (lhs)))
	      && strstr (decl_name, ".reorg_gptr"))
	    {
	      /* Check the POINTER_PLUS_EXPR */
	      plus_stmt = dyn_cast<gassign *> (SSA_NAME_DEF_STMT (rhs));
	      if (!plus_stmt
		  || gimple_assign_rhs_code (plus_stmt) != POINTER_PLUS_EXPR)
		SET_ERR_RETURN_NULL (error)
	      lhs = gimple_assign_rhs1 (plus_stmt);
	      rhs = gimple_assign_rhs2 (plus_stmt);
	      prev_type = TREE_TYPE (lhs);
	      /* Check the MULT_EXPR */
	      mul_stmt = dyn_cast<gassign *> (SSA_NAME_DEF_STMT (rhs));
	      if (!mul_stmt || gimple_assign_rhs_code (mul_stmt) != MULT_EXPR)
		SET_ERR_RETURN_NULL (error)
	      lhs = gimple_assign_rhs1 (mul_stmt);
	      rhs = gimple_assign_rhs2 (mul_stmt);
	      if (TREE_CODE (lhs) == SSA_NAME)
		{
		  size = lhs;
		  mul_by = rhs;
		}
	      else
		{
		  if (TREE_CODE (rhs) != SSA_NAME)
		    SET_ERR_RETURN_NULL (error)
		  size = rhs;
		  mul_by = lhs;
		}
	      if (TREE_CODE (mul_by) != INTEGER_CST
		  || !operand_equal_p (mul_by, TYPE_SIZE_UNIT (prev_type)))
		SET_ERR_RETURN_NULL (error)
	      /* We can trace to original calloc/malloc to make this safer.  */
	    }
	  return size;
	}
      return NULL_TREE;
    case GIMPLE_CALL:
      lhs = gimple_get_lhs (stmt);
      gcc_checking_assert (TREE_CODE (lhs) == SSA_NAME);
      if (ssa_def)
	*ssa_def = lhs;
      return get_allocate_size (type, lhs, NULL_TREE, stmt, error);
    default:
      return NULL_TREE;
    }
}

/* Check if NODE is a variable to be cached, if so, record it. VNODE
   contains referrring to NODE.  */

bool
ipa_struct_dco::find_dco_data_single (dco_info &info, tree node,
				      varpool_node *vnode)
{
  struct ipa_ref *ref;
  bool error = false;
  tree size_expr = NULL_TREE, new_size_expr;
  tree ssa_def = NULL_TREE;

  for (unsigned i = 0; vnode->iterate_referring (i, ref); i++)
    {
      /* Filter for writes to NODE.  */
      if (ref->use != IPA_REF_STORE)
	continue;
      tree lhs = gimple_get_lhs (ref->stmt);
      if (!operand_equal_p (lhs, node, COMPARE_DECL_FLAGS))
	continue;
      /* Ignore assignments after start-point.  */
      if (!is_stmt_before_fclose (info, ref->stmt, ref->referring))
	continue;
      if ((new_size_expr
	   = get_allocate_size_iterate (info.dco_type->type, ref->stmt,
					&ssa_def, &error)))
	{
	  TEST_WITH_MSG (!size_expr,
			 "dco_data allocated twice before start-point");
	  size_expr = new_size_expr;

	  if (ref->referring != info.start_srfn->node)
	    /* Igore references to dco_data before start-point.  */
	    ssa_def = NULL_TREE;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "[DCO FIND_DATA] Add array: ");
	      print_generic_expr (dump_file, node);
	      fprintf (dump_file, ", size: ");
	      print_generic_expr (dump_file, size_expr);
	      fprintf (dump_file, ", ssa_def: ");
	      print_generic_expr (dump_file, ssa_def);
	      fprintf (dump_file, "\n");
	    }
	}
      TEST_WITH_MSG (!error, "get_allocate_size_iterate");
    }

  if (size_expr)
    info.dco_data_vec.safe_push (
      new dco_data (node, size_expr, ssa_def, vnode));
  return true;
}

/* Find all variables to be cached (dco_data):
   - Define source is malloc/calloc (before start-point).
   - Will be used after fclose (e.g. global variables).
   - [TODO] If a dco_data is wrapped deeper in a compound type, it might be
   missed, because we're not walking down the tree_nodes fully (it's hard to
   find dco_data this way). Better search them from calling calloc()?  */

bool
ipa_struct_dco::find_dco_data (dco_info &info)
{
  varpool_node *vnode;
  tree new_type = info.dco_type->type;

  /* 1) Process all global vars, search for arrays of cached objects.  */
  FOR_EACH_VARIABLE (vnode)
    {
      tree node = vnode->decl;
      tree node_type = TREE_TYPE (node);
      /* Global object should also be cached if we support this.  */
      TEST_WITH_MSG (!types_dco_compatible_p (node_type, new_type),
		     "Global object of cached type")
      switch (TREE_CODE (node_type))
	{
	case POINTER_TYPE:
	  if (types_dco_compatible_p (TREE_TYPE (node_type), new_type))
	    TEST (find_dco_data_single (info, node, vnode));
	  break;
	case RECORD_TYPE:
	  for (tree t = TYPE_FIELDS (node_type); t; t = DECL_CHAIN (t))
	    {
	      if (TREE_CODE (t) != FIELD_DECL)
		continue;
	      tree field_type = TREE_TYPE (t);
	      if (POINTER_TYPE_P (field_type)
		  && types_dco_compatible_p (TREE_TYPE (field_type), new_type))
		{
		  tree field_node
		    = build3 (COMPONENT_REF, field_type, node, t, NULL_TREE);
		  TEST (find_dco_data_single (info, field_node, vnode));
		}
	      TEST_WITH_MSG (TREE_CODE (field_type) != RECORD_TYPE,
			     "RECORD->RECORD->...->dco_data not supported")
	      /* More safe: trace-back following VDEF/VUSE.  */
	    }
	  break;
	case ARRAY_TYPE:
	case UNION_TYPE:
	case QUAL_UNION_TYPE:
	  if (dump_file)
	    {
	      fprintf (dump_file, "[DCO FIND_DATA] node_type not handled: ");
	      print_generic_expr (dump_file, node_type);
	      fprintf (dump_file, "\n");
	    }
	  return false;
	default:
	  break;
	}
    }

  /* TODO: Check local objects of cached type.  */
  TEST_WITH_MSG (!info.dco_data_vec.is_empty (), "No dco_data found");
  return true;
}

/* Add REF as a dco_ref entry into INFO.
   When REF is array of records, FIELD is field decl we're interested in.
   e.g. given definition "struct {new_type *p;} SS;" :
   - With "SS ss_array[10]", FIELD is "p", REF is "ss_array".
   - With "SS ss", FIELD is NULL_TREE and REF is "ss->p".
 */

bool
ipa_struct_dco::add_dco_ref (dco_info &info, dco_data *data, tree ref,
			     tree field)
{
  unsigned i;
  dco_data *dd;
  dco_ref *dr;
  tree size_expr = NULL_TREE;
  bool error = false;
  gimple *def_stmt = NULL;
  tree type = TREE_TYPE (ref);

  /* The way we're searching for dco_refs, dco_data vars will also meet the
     requirements. Rule out them.  */
  FOR_EACH_VEC_ELT (info.dco_data_vec, i, dd)
    if (operand_equal_p (ref, dd->var, COMPARE_DECL_FLAGS))
      return true;

  /* Rule out duplicants.  */
  FOR_EACH_VEC_ELT (info.dco_refs, i, dr)
    if (operand_equal_p (ref, dr->var, COMPARE_DECL_FLAGS))
      {
	if (dr->field)
	  {
	    gcc_checking_assert (field);
	    if (!operand_equal_p (field, dr->field, COMPARE_DECL_FLAGS))
	      {
		/* Different fields in an array of structures.  */
		type = dr->orig_type ? dr->orig_type : type;
		size_expr = dr->upper_bound;
		continue;
	      }
	  }
	if (dr->source != data)
	  {
	    if (dump_file)
	      {
		fprintf (dump_file, "[DCO FIND_REF] variable ");
		print_generic_expr (dump_file, ref);
		fprintf (dump_file,
			 " referring to multiple dco_data variables: ");
		print_generic_expr (dump_file, dr->source->var);
		fprintf (dump_file, " and ");
		print_generic_expr (dump_file, data->var);
		fprintf (dump_file, "\n");
	      }
	    return false;
	  }
	return true;
      }

  /* Use the "real" type for void*.  */
  if (VOID_POINTER_P (type))
    {
      srdecl *decl = find_decl (ref);
      if (decl && decl->orig_type && POINTER_TYPE_P (decl->orig_type))
	type = decl->orig_type;
      else
	{
	  if (dump_file)
	    {
	      fprintf (dump_file, "[DCO FIND_REF] orig_type not found for ");
	      print_generic_expr (dump_file, ref);
	      fprintf (dump_file, "\n");
	    }
	  return false;
	}
    }

  /* If REF is an array, get the size it is allocated with.  */
  if ((!size_expr) && POINTER_TYPE_P (type)
      && !types_dco_compatible_p (TREE_TYPE (type), info.dco_type->type))
    {
      if (TREE_CODE (ref) == SSA_NAME)
	def_stmt = SSA_NAME_DEF_STMT (ref);
      else
	{
	  tree base = ref;
	  if (TREE_CODE (ref) == COMPONENT_REF)
	    base = TREE_OPERAND (base, 0);
	  gcc_checking_assert (TREE_CODE (base) == VAR_DECL);
	  varpool_node *vnode = varpool_node::get (base);
	  struct ipa_ref *iref;
	  /* Local array is not handled yet.  */
	  TEST_WITH_MSG (vnode, "[DCO FIND_REF] not a global array.");
	  for (unsigned i = 0; vnode->iterate_referring (i, iref); i++)
	    {
	      /* Filter for writes to NODE.  */
	      if (iref->use != IPA_REF_STORE)
		continue;
	      tree lhs = gimple_get_lhs (iref->stmt);
	      if (!operand_equal_p (lhs, ref, COMPARE_DECL_FLAGS))
		continue;
	      /* Ignore assignments after start-point.  */
	      if (!is_stmt_before_fclose (info, iref->stmt, iref->referring))
		continue;
	      /* skip "DEC_REF = 0B".  */
	      if (gimple_assign_single_p (iref->stmt)
		  && integer_zerop (gimple_assign_rhs1 (iref->stmt)))
		continue;
	      TEST_WITH_MSG (
		!def_stmt,
		"[DCO FIND_REF] Multiple allocations before start-point?");
	      def_stmt = iref->stmt;
	    }
	  TEST_WITH_MSG (def_stmt, "[DCO FIND_REF] no def_stmt found");
	}

      size_expr
	= get_allocate_size_iterate (TREE_TYPE (type), def_stmt, NULL, &error);
      TEST_WITH_MSG (!error, "get_allocate_size_iterate");
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "[DCO FIND_REF] Add dco_ref: ");
      print_generic_expr (dump_file, ref);
      fprintf (dump_file, ", type: ");
      print_generic_expr (dump_file, type);
      fprintf (dump_file, ", data: ");
      print_generic_expr (dump_file, data->var);
      if (size_expr)
	{
	  fprintf (dump_file, ", size_expr: ");
	  print_generic_expr (dump_file, size_expr);
	}
      if (field)
	{
	  fprintf (dump_file, ", field: ");
	  print_generic_expr (dump_file, field);
	}
      fprintf (dump_file, "\n");
    }
  info.dco_refs.safe_push (new dco_ref (ref, type, data, size_expr, field));
  return true;
}

/* Given a dco_data variable DATA and a variable VAR referring to DATA,
   find dco_refs iteratively follow the use chain of VAR.  */

bool
ipa_struct_dco::find_dco_refs_iterate (dco_info &info, dco_data *data, tree var,
				       bool loop_back)
{
  use_operand_p use_p;
  imm_use_iterator iter;
  gimple *stmt;
  gphi *phi;
  edge e;
  bool loop_var;
  tree base, field, ref, lhs, var_type;
  tree new_type = info.dco_type->type;
  auto_vec<basic_block> &reach_bbs = info.start_srfn->dco_path.reach_bbs;

  switch (TREE_CODE (var))
    {
    /* 1) For SSA_NAME, iterate through use chain.  */
    case SSA_NAME:
      FOR_EACH_IMM_USE_FAST (use_p, iter, var)
	{
	  stmt = USE_STMT (use_p);
	  /* If a local ptr of compressed type is defined before start-point and
	     used after start-point, quit DCO. (Otherwise we need to clone and
	     version the ptr's define statement.)  */
	  if (reach_bbs.contains (gimple_bb (stmt))
	      && !(reach_bbs.contains (gimple_bb (SSA_NAME_DEF_STMT (var)))))
	    {
	      if (dump_file)
		{
		  fprintf (dump_file,
			   "[DCO FIND_REF] Local usage not handled: ");
		  print_gimple_stmt (dump_file, stmt, 0);
		  fprintf (dump_file, "  Defined at: ");
		  print_gimple_stmt (dump_file, SSA_NAME_DEF_STMT (var), 0);
		}
	      return false;
	    }

	  switch (gimple_code (stmt))
	    {
	    case GIMPLE_ASSIGN:
	      /* Rule out: expr(var) = X.  */
	      lhs = gimple_get_lhs (stmt);
	      if (!walk_tree (&lhs, check_for_ssa, var, NULL)
		  && get_dco_type_pointer_ref (info, lhs))
		TEST (find_dco_refs_iterate (info, data, lhs, loop_back))
	      break;
	    case GIMPLE_PHI:
	      /* Check if VAR is from back_edge.  */
	      loop_var = false;
	      phi = dyn_cast<gphi *> (stmt);
	      for (unsigned i = 0; i < gimple_phi_num_args (phi); ++i)
		if (gimple_phi_arg_def (phi, i) == var)
		  {
		    e = gimple_phi_arg_edge (phi, i);
		    if (e->flags & EDGE_DFS_BACK)
		      {
			loop_var = true;
			break;
		      }
		  }
	      if (!loop_var)
		{
		  TEST (find_dco_refs_iterate (info, data,
					       gimple_get_lhs (stmt),
					       loop_back))
		}
	      else if (loop_back)
		{
		  TEST (find_dco_refs_iterate (info, data,
					       gimple_get_lhs (stmt), false))
		}
	      break;
	    case GIMPLE_DEBUG:
	    case GIMPLE_COND:
	    case GIMPLE_SWITCH:
	    case GIMPLE_NOP:
	      break;
	    default:
	      /* Cannot be sure how dco_data is used, like GIMPLE_CALL?  */
	      if (dump_file)
		{
		  fprintf (dump_file,
			   "[DCO FIND_REF] dco_data usage not handled: ");
		  print_gimple_stmt (dump_file, stmt, 0);
		}
	      return false;
	    }
	}
      return true;

    /* 2) For VAR_DECL, submit a dco_ref.  */
    case VAR_DECL:
      return add_dco_ref (info, data, var, NULL_TREE);

    /* 3) For MEM_REF, find dco_ref following base's def chain.  */
    case MEM_REF:
      if (!integer_zerop (TREE_OPERAND (var, 1)))
	{
	  if (dump_file)
	    {
	      fprintf (dump_file,
		       "[DCO FIND_REF] MEM_REF offset not handled: ");
	      print_generic_expr (dump_file, var);
	      fprintf (dump_file, "\n");
	    }
	  return false;
	}
      var_type = TREE_TYPE (var);
      if (!POINTER_TYPE_P (var_type)
	  || !types_dco_compatible_p (TREE_TYPE (var_type), new_type))
	{
	  if (dump_file)
	    {
	      fprintf (dump_file, "[DCO FIND_REF] Type not compatible: ");
	      print_generic_expr (dump_file, var_type);
	      fprintf (dump_file, "\n");
	    }
	  return false;
	}
      base = TREE_OPERAND (var, 0);
      if ((ref = get_ptr_decl (base)))
	return add_dco_ref (info, data, ref, NULL_TREE);
      if (dump_file)
	{
	  fprintf (dump_file, "[DCO FIND_REF] Failed to get array decl from: ");
	  print_generic_expr (dump_file, base);
	  fprintf (dump_file, "\n");
	}
      return false;

    case COMPONENT_REF:
      base = TREE_OPERAND (var, 0);
      if (TREE_CODE (base) == VAR_DECL)
	return add_dco_ref (info, data, var, NULL_TREE);
      else if (TREE_CODE (base) == MEM_REF)
	base = TREE_OPERAND (base, 0);
      field = TREE_OPERAND (var, 1);
      if ((ref = get_ptr_decl (base)))
	return add_dco_ref (info, data, ref, field);
      if (dump_file)
	{
	  fprintf (dump_file, "[DCO FIND_REF] Failed to get array decl from: ");
	  print_generic_expr (dump_file, base);
	  fprintf (dump_file, "\n");
	}
      return false;

    default:
      if (dump_file)
	{
	  fprintf (dump_file,
		   "[DCO FIND_REF] Unknown use kind, code: %s, var: ",
		   get_tree_code_name (TREE_CODE (var)));
	  print_generic_expr (dump_file, var);
	  fprintf (dump_file, "\n");
	}
      return false;
    }
}

/* Find all dco_refs (variables/arrays to be modified according to some
   dco_data):
   - Will be used after fclose (e.g. global variables).
   - Before fclose, value or array content is assigned with references to some
     recognized dco_data. (If there are multiple dco_data variables referenced
     by one dco_ref, quit DCO. Because we don't know how to modify it then.)
 */

bool
ipa_struct_dco::find_dco_refs (dco_info &info)
{
  unsigned i, j;
  dco_data *dd;
  struct ipa_ref *ref;

  /* For each dco_data variable, follow the use chains and search for dco_refs.
   */
  FOR_EACH_VEC_ELT (info.dco_data_vec, i, dd)
    {
      if (dd->ssa_def)
	{
	  /* We have an ssa_name in start function.  */
	  SET_CFUN (info.start_srfn);
	  TEST (find_dco_refs_iterate (info, dd, dd->ssa_def, true))
	}

      for (j = 0; dd->vnode->iterate_referring (j, ref); j++)
	{
	  /* Filter for memory loads.  */
	  if (ref->use != IPA_REF_LOAD)
	    continue;
	  /* Ignore assignments after start-point.  */
	  if (!is_stmt_before_fclose (info, ref->stmt, ref->referring))
	    continue;
	  TEST (gimple_assign_single_p (ref->stmt));
	  tree rhs = gimple_assign_rhs1 (ref->stmt);
	  tree lhs = gimple_assign_lhs (ref->stmt);
	  if (!operand_equal_p (rhs, dd->var, COMPARE_DECL_FLAGS))
	    continue;

	  SET_CFUN (find_function (dyn_cast<cgraph_node *> (ref->referring)));
	  TEST (find_dco_refs_iterate (info, dd, lhs, true));
	}
    }

  return true;
}

/* Compare the gimple order of input_ssa for dco fields. */

int
ipa_struct_dco::input_order_cmp (const void *p, const void *q)
{
  const dco_field *a = *(const dco_field *const *) p;
  const dco_field *b = *(const dco_field *const *) q;

  gimple *ga = SSA_NAME_DEF_STMT (a->input_ssa);
  gimple *gb = SSA_NAME_DEF_STMT (b->input_ssa);

  if (gimple_uid (ga) < gimple_uid (gb))
    return -1;
  else if (gimple_uid (ga) > gimple_uid (gb))
    return 1;
  else
    return 0;
}

/* Get the BASE and field of the VAR. */

bool
ipa_struct_dco::get_base_type (tree var, tree &base, srtype *&t, srfield *&f)
{
  TEST (TREE_CODE (var) == COMPONENT_REF);

  /* Ignore data access that is canonical. */
  bool realpart, imagpart;
  bool address;
  bool indirect;
  TEST (
    get_type_field (var, base, indirect, t, f, realpart, imagpart, address));

  return true;
}

/* Return true if var is initialized as either init or zero. */

bool
ipa_struct_dco::check_var_init (tree var, tree init)
{
  unsigned i;
  srfunction *srfn;

  TEST (TREE_CODE (var) != SSA_NAME);

  bool found_init = false;
  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      basic_block bb = NULL;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
	       gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (!gimple_assign_single_p (stmt))
		continue;

	      tree lhs = gimple_assign_lhs (stmt);
	      if (!operand_equal_p (lhs, var))
		continue;

	      tree rhs = gimple_assign_rhs1 (stmt);
	      if (integer_zerop (rhs) || rhs == init)
		{
		  found_init = true;
		  continue;
		}

	      return false;
	    }
	}
    }

  return found_init;
}

/* Scan STMT operands backward following def/use chain to make sure the
   expression is for calculating &arr[index], and return the INDEX. The
   offset should be multiple number of sizeof the array element.

   The INDEX might be an expression rather than SSA_NAME.  */

bool
ipa_struct_dco::array_pointer_p (gimple *stmt, tree mem_base, tree &index)
{
  TEST (is_gimple_assign (stmt));
  gcc_checking_assert (mem_base);

  /* Skip copy */
  while (gimple_assign_single_p (stmt))
    {
      tree rhs = gimple_assign_rhs1 (stmt);
      if (TREE_CODE (rhs) != SSA_NAME)
	break;
      stmt = SSA_NAME_DEF_STMT (rhs);
    }

  if (is_gimple_assign (stmt))
    {
      tree lhs = gimple_assign_lhs (stmt);
      tree rhs1 = gimple_assign_rhs1 (stmt);
      tree_code rhs_code = gimple_assign_rhs_code (stmt);

      if (rhs_code == POINTER_PLUS_EXPR)
	{
	  tree struct_type = TREE_TYPE (TREE_TYPE (lhs));
	  tree rhs2 = gimple_assign_rhs2 (stmt);
	  gcc_checking_assert (
	    VOID_POINTER_P (TREE_TYPE (mem_base))
	    || types_dco_compatible_p (struct_type,
				       TREE_TYPE (TREE_TYPE (mem_base))));
	  /* Calculate index from ptr and offset respectfully.  */
	  tree index1, index2;
	  if (rhs1 == mem_base)
	    index1 = integer_zero_node;
	  else
	    TEST (array_pointer_p (SSA_NAME_DEF_STMT (rhs1), mem_base, index1));
	  if (!is_result_of_mult (rhs2, &index2, struct_type))
	    {
	      if (dump_file)
		{
		  fprintf (dump_file,
			   "[DCO WARN] offset is not a multiplicate");
		  fprintf (dump_file, " of struct_size=");
		  print_generic_expr (dump_file, TYPE_SIZE_UNIT (struct_type));
		  fprintf (dump_file, "\n");
		}
	    }
	  index = fold_build2 (PLUS_EXPR, size_type_node, index1, index2);
	  return true;
	}
      else if (gimple_assign_single_p (stmt))
	{
	  if (operand_equal_p (rhs1, mem_base, COMPARE_DECL_FLAGS))
	    {
	      index = integer_zero_node;
	      return true;
	    }
	  if (TREE_CODE (rhs1) == SSA_NAME)
	    return array_pointer_p (SSA_NAME_DEF_STMT (rhs1), mem_base, index);
	}
    }
  else if (allocation_stmt_p (stmt))
    {
      index = integer_zero_node;
      return true;
    }

  return false;
}

/* Find mem_base_ssa. Any base SSA we can find following POINTER_PLUS_EXPR
   chain, in which the pointer field is used, will be the candidate. In the
   mean time, the SSA_NAME_DEF_STMT must be BUILT_IN_CALLOC. */

bool
ipa_struct_dco::find_mem_base_ssa_array_pointer (dco_info &info,
						 dco_field_class *dfc)
{
  unsigned i, j;
  srfield *srf;
  srfunction *srfn;
  dco_closure *closure_info = &(dfc->closure_info);

  FOR_EACH_VEC_ELT (dfc->srfields, i, srf)
    {
      FOR_EACH_VEC_ELT (functions, j, srfn)
	{
	  SET_CFUN (srfn);

	  basic_block bb = NULL;
	  FOR_EACH_BB_FN (bb, cfun)
	    {
	      for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
		   gsi_next (&si))
		{
		  gimple *stmt = gsi_stmt (si);
		  if (!is_gimple_assign (stmt))
		    continue;

		  /* A DCO candidate must be a struct field. */
		  tree lhs = gimple_assign_lhs (stmt);
		  srtype *t = 0;
		  srfield *f = 0;
		  tree base = NULL_TREE;
		  if (!get_base_type (lhs, base, t, f))
		    continue;

		  /* Only care the fields of a dco_type. */
		  if (t != info.dco_type)
		    continue;
		  if (f != srf)
		    continue;

		  TEST (gimple_assign_single_p (stmt));
		  tree rhs1 = gimple_assign_rhs1 (stmt);
		  TEST (TREE_CODE (rhs1) == SSA_NAME);
		  gimple *stmt1 = SSA_NAME_DEF_STMT (rhs1);

		  /* Skip pattern pointer + offset */
		  while (gimple_assign_rhs_code_p (stmt1, POINTER_PLUS_EXPR))
		    {
		      rhs1 = gimple_assign_rhs1 (stmt1);
		      if (TREE_CODE (rhs1) != SSA_NAME)
			break;
		      stmt1 = SSA_NAME_DEF_STMT (rhs1);
		    }

		  if (calloc_mem_base_ssa_p (rhs1))
		    {
		      closure_info->mem_base_ssa = rhs1;
		      return true;
		    }
		}
	    }
	}
    }

  return false;
}

bool
ipa_struct_dco::find_mem_base_ssa_array_index (dco_field_class *dfc)
{
  unsigned i;
  srfield *srf;
  srfunction *srfn;
  dco_closure *closure_info = &(dfc->closure_info);
  tree gptr = NULL_TREE;

  FOR_EACH_VEC_ELT (dfc->srfields, i, srf)
    {
      tree field_decl = srf->fielddecl;
      tree attrib
	= lookup_attribute ("addr_to_index", DECL_ATTRIBUTES (field_decl));
      TEST (attrib != NULL_TREE && TREE_VALUE (attrib) != NULL_TREE);

      if (gptr != NULL_TREE)
	{
	  TEST (TREE_VALUE (attrib) == gptr)
	}
      else
	gptr = TREE_VALUE (attrib);
    }

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      basic_block bb = NULL;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
	       gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (!is_gimple_assign (stmt))
		continue;

	      /* A DCO candidate must be a struct field. */
	      if (gptr != gimple_assign_lhs (stmt))
		continue;

	      tree ssa = gimple_assign_rhs1 (stmt);
	      TEST (calloc_mem_base_ssa_p (ssa))

	      closure_info->mem_base_ssa = ssa;
	      return true;
	    }
	}
    }
  return false;
}

static void
dump_vec_gimples (auto_vec<gimple *> &stmts, const char *name)
{
  fprintf (dump_file, "Gimples in %s:\n", name);
  unsigned i;
  gimple *stmt;

  FOR_EACH_VEC_ELT (stmts, i, stmt)
    print_gimple_stmt (dump_file, stmt, 0);

  fprintf (dump_file, "\n");
}

static void
dump_vec_trees (auto_vec<tree> &exprs, const char *name)
{
  fprintf (dump_file, "Trees in %s:\n", name);
  unsigned i;
  tree exp;

  FOR_EACH_VEC_ELT (exprs, i, exp)
    {
      print_generic_expr (dump_file, exp);
      fprintf (dump_file, "\n");
    }
  fprintf (dump_file, "\n");
}

void
dco_closure::dump ()
{
  fprintf (dump_file, "\n[CLOSURE]\n");
  fprintf (dump_file, "mem_base_ssa: ");
  print_generic_expr (dump_file, mem_base_ssa);
  fprintf (dump_file, "\nmem_base_var: ");
  print_generic_expr (dump_file, mem_base_var);
  fprintf (dump_file, "\n");
  dump_vec_gimples (rd_change, "rd_change");
  dump_vec_gimples (rd_unchange, "rd_unchange");
  dump_vec_gimples (wt_change, "wt_change");
  dump_vec_gimples (wt_unchange, "wt_unchange");
  if (mem_base_ssa != NULL_TREE)
    dump_vec_trees (wt_array_index, "wt_array_index");
}

/* Return true if all stmts using ssa_def are to write a DCO field. */

bool
ipa_struct_dco::wt_dco_field_only_p (dco_info &info, dco_field_class *dfc,
				     tree ssa_def)
{
  imm_use_iterator imm_iter;
  gimple *stmt;
  FOR_EACH_IMM_USE_STMT (stmt, imm_iter, ssa_def)
    {
      if (gimple_code (stmt) == GIMPLE_DEBUG)
	continue;

      /* We don't know if it is PHI. */
      if (!is_gimple_assign (stmt))
	return false;

      tree lhs = gimple_assign_lhs (stmt);
      srtype *t = 0;
      srfield *f = 0;
      tree base = NULL_TREE;
      if (!get_base_type (lhs, base, t, f))
	return false;

      if (t != info.dco_type || !dfc->srfields.contains (f))
	return false;
    }

  return true;
}

/* Return true, if no calculation with unknown boundary introduced. */

bool
ipa_struct_dco::check_closure_int (dco_info &info, dco_field_class *dfc,
				   DCO_KIND kind)
{
  unsigned i, j;
  srfield *srf;
  srfunction *srfn;
  dco_cond *dc = dfc->dc;
  dco_closure *closure_info = &(dfc->closure_info);
  gcc_checking_assert (kind != ARRAY_POINTER);

  FOR_EACH_VEC_ELT (dfc->srfields, i, srf)
    {
      FOR_EACH_VEC_ELT (functions, j, srfn)
	{
	  SET_CFUN_WITH_LOOP_OPT (srfn, kind == ARRAY_INDEX);

	  basic_block bb = NULL;
	  FOR_EACH_BB_FN (bb, cfun)
	    {
	      for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
		   gsi_next (&si))
		{
		  gimple *stmt = gsi_stmt (si);
		  if (!is_gimple_assign (stmt))
		    continue;

		  /* A DCO candidate must be a struct field. */
		  tree lhs = gimple_assign_lhs (stmt);
		  srtype *t = 0;
		  srfield *f = 0;
		  tree base = NULL_TREE;
		  if (!get_base_type (lhs, base, t, f))
		    continue;

		  /* Only care the fields of a dco_type. */
		  if (t != info.dco_type)
		    continue;
		  if (f != srf)
		    continue;
		  if (dc && !dco_field_p (lhs, dc))
		    continue;

		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "[CHECK CLOSURE] ");
		      print_gimple_stmt (dump_file, stmt, 0);
		    }

		  /* Skip if we have already analyzed this stmt. */
		  if (closure_info->wt_unchange_p (stmt)
		      || closure_info->wt_change_p (stmt))
		    continue;

		  /* All write stmts could be
		     (1) unchange, i.e. optimize away encode/decode
		     (2) change with optimized value, i.e. optimized away encode
		     (3) change, i.e. use unoptimized encode

		     For case (3), we may have the scenario like below,

			B = A->field;
			... = B;
			C->field = B;

		     We still can prove C->field is from A->field, so they are
		     in a closure, but we must decode A->field and encode
		     C->field, because B may be used outside the clsoure, for
		     which we don't care about.

		     Besides, case (2) is only for array pointer. */

		  tree rhs1 = gimple_assign_rhs1 (stmt);
		  if (closure_info->wt_special_val.contains (rhs1))
		    {
		      /* Case (3) */
		      closure_info->add_wt_change (stmt);

		      if (dump_file && (dump_flags & TDF_DETAILS))
			{
			  fprintf (dump_file, "Case (3.1): need to change. \n");
			}
		      continue;
		    }

		  TEST (gimple_assign_single_p (stmt));
		  TEST (TREE_CODE (rhs1) == SSA_NAME);
		  gimple *stmt1 = SSA_NAME_DEF_STMT (rhs1);

		  if (gimple_assign_single_p (stmt1))
		    {
		      rhs1 = gimple_assign_rhs1 (stmt1);

		      /* Check if RHS is from the the same DCO class. */
		      srtype *t = 0;
		      srfield *f = 0;
		      tree base = NULL_TREE;
		      if (get_base_type (rhs1, base, t, f)
			  && dfc->srfields.contains (f))
			{
			  /* ssa_def must be rhs of the write stmts. */
			  tree ssa_def = gimple_assign_lhs (stmt1);
			  if (ssa_def == gimple_assign_rhs1 (stmt))
			    {
			      if (wt_dco_field_only_p (info, dfc, ssa_def))
				{
				  /* Case (1) */
				  closure_info->add_wt_unchange (stmt);
				  closure_info->add_rd_unchange (stmt1);

				  if (dump_file && (dump_flags & TDF_DETAILS))
				    {
				      fprintf (dump_file,
					       "Case (1): No need to change: ");
				      print_gimple_stmt (dump_file, stmt1, 0);
				    }
				}
			      else
				{
				  /* Case (3) */
				  closure_info->add_wt_change (stmt);

				  if (dump_file && (dump_flags & TDF_DETAILS))
				    {
				      fprintf (
					dump_file,
					"Case (3.2): need to change. \n");
				    }
				}

			      continue;
			    }
			}
		    }

		  if (kind == ARRAY_INDEX)
		    {
		      dco_bound_info *binfo = new dco_bound_info (stmt);
		      if (binfo->get_upper_bound ())
			{
			  dfc->bound_infos.safe_push (binfo);

			  if (dump_file && (dump_flags & TDF_DETAILS))
			    binfo->dump (dump_file);
			  continue;
			}
		      delete binfo;
		    }

		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "[DCO CLOSURE FAIL] ");
		      print_gimple_stmt (dump_file, stmt, 0);
		    }

		  return false;
		}
	    }
	}
    }

  /* Collect rd_change */
  if (kind == CLOSURE_INT)
    collect_closure_rd_change (info, dfc);

  if (dump_file && (dump_flags & TDF_DETAILS))
    closure_info->dump ();

  return true;
}

/* Return true if STMT is a copy to convert from/to integer/pointer. */

static bool
is_copy_int_or_ptr (const gimple *stmt)
{
  if (!is_gimple_assign (stmt))
    return NULL_TREE;

  tree rhs = gimple_assign_rhs1 (stmt);

  if (gimple_assign_single_p (stmt))
    if (TREE_CODE (rhs) == SSA_NAME)
      return true;

  if (CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (stmt)))
    {
      tree lhs = gimple_assign_lhs (stmt);

      if (TREE_CODE (rhs) == SSA_NAME
	  && (TREE_CODE (TREE_TYPE (lhs)) == INTEGER_TYPE
	      || POINTER_TYPE_P (TREE_TYPE (lhs))))
	return true;
    }

  return false;
}

/* Strip the copy with typecasting of int or unsigned int.  */

gimple *
strip_copy_ptr_stmts (gimple *stmt)
{
  while (is_copy_int_or_ptr (stmt))
    {
      tree rhs = gimple_assign_rhs1 (stmt);
      stmt = SSA_NAME_DEF_STMT (rhs);
    }
  return stmt;
}

/* The array pointer to index gimples are generated by struct-reorg:
     ptr = ...;
     _X1 = ptr - gptr0;
     index = _X1 / sizeof (struct);  */

bool
strip_array_pointer_to_index (gimple *index_stmt, gimple *&ptr_stmt)
{
  TEST (gimple_assign_rhs_code_p (index_stmt, TRUNC_DIV_EXPR))

  tree x1 = gimple_assign_rhs1 (index_stmt);
  tree size = gimple_assign_rhs2 (index_stmt);
  TEST (TREE_CODE (x1) == SSA_NAME && TREE_CODE (size) == INTEGER_CST)

  gimple *minus_stmt = SSA_NAME_DEF_STMT (x1);
  TEST (gimple_assign_rhs_code_p (minus_stmt, MINUS_EXPR))

  tree gptr0 = gimple_assign_rhs2 (minus_stmt);
  gimple *gptr0_stmt = SSA_NAME_DEF_STMT (gptr0);

  TEST (gptr0_stmt != NULL)
  gptr0_stmt = strip_copy_stmts (gptr0_stmt);
  TEST (gimple_assign_single_p (gptr0_stmt));
  gptr0 = gimple_assign_rhs1 (gptr0_stmt);
  TEST (VAR_P (gptr0)
	&& strstr (IDENTIFIER_POINTER (DECL_NAME (gptr0)), "reorg_gptr0"))

  tree struct_type = TREE_TYPE (TREE_TYPE (gptr0));
  TEST (tree_int_cst_equal (size, TYPE_SIZE_UNIT (struct_type)))

  tree ptr = gimple_assign_rhs1 (minus_stmt);
  TEST (TREE_CODE (ptr) == SSA_NAME)
  ptr_stmt = SSA_NAME_DEF_STMT (ptr);
  TEST (ptr_stmt != NULL)
  ptr_stmt = strip_copy_stmts (ptr_stmt);
  return ptr_stmt;
}

/* The array pointer to index gimples are generated by struct-reorg:
     index = ...;
     _X1 = index * sizeof (struct);
     ptr = gptr0 + _X1;  */

bool
strip_array_index_to_pointer (gimple *ptr_stmt, gimple *&index_stmt)
{
  TEST (gimple_assign_rhs_code_p (ptr_stmt, POINTER_PLUS_EXPR))

  tree gptr0 = gimple_assign_rhs1 (ptr_stmt);
  tree x1 = gimple_assign_rhs2 (ptr_stmt);
  TEST (TREE_CODE (gptr0) == SSA_NAME && TREE_CODE (x1) == SSA_NAME)

  gimple *gptr0_stmt = SSA_NAME_DEF_STMT (gptr0);
  TEST (gptr0_stmt != NULL && gimple_assign_single_p (gptr0_stmt))
  gptr0 = gimple_assign_rhs1 (gptr0_stmt);
  TEST (VAR_P (gptr0)
	&& strstr (IDENTIFIER_POINTER (DECL_NAME (gptr0)), "reorg_gptr0"))

  gimple *mult_stmt = SSA_NAME_DEF_STMT (x1);
  TEST (gimple_assign_rhs_code_p (mult_stmt, MULT_EXPR))
  tree index = gimple_assign_rhs1 (mult_stmt);
  tree size = gimple_assign_rhs2 (mult_stmt);
  TEST (TREE_CODE (index) == SSA_NAME || TREE_CODE (size) == INTEGER_CST)

  tree struct_type = TREE_TYPE (TREE_TYPE (gptr0));
  TEST (tree_int_cst_equal (size, TYPE_SIZE_UNIT (struct_type)))

  index_stmt = SSA_NAME_DEF_STMT (index);
  TEST (index_stmt != NULL)
  return true;
}

/* Strip the struct-reorg generated array-pointer to array-index and
   array-index to array-pointer gimples, and find the source gimple.
   Otherwise, return the input STMT.  */

gimple *
strip_array_pointer_index_pair (gimple *stmt)
{
  gimple *stmt1, *result;
  if (!strip_array_pointer_to_index (stmt, stmt1))
    return stmt;
  if (!strip_array_index_to_pointer (stmt1, result))
    return stmt;
  return result;
}

/* Return true, if
     (1) all pointers in DFC point to the same memory space.
     (2) and, all pointers in DFC are for arrary.
     (3) and, no calculation with unknown boundary for dynamic-DCO.  */

bool
ipa_struct_dco::check_closure_array_pointer (dco_info &info,
					     dco_field_class *dfc)
{
  unsigned i, j;
  srfield *srf;
  srfunction *srfn;
  dco_cond *dc = dfc->dc;
  dco_closure *closure_info = &(dfc->closure_info);
  bool dynamic_dco_p = CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_DYNAMIC);

  FOR_EACH_VEC_ELT (dfc->srfields, i, srf)
    {
      FOR_EACH_VEC_ELT (functions, j, srfn)
	{
	  SET_CFUN_WITH_LOOP_OPT (srfn, dynamic_dco_p);

	  basic_block bb = NULL;
	  FOR_EACH_BB_FN (bb, cfun)
	    {
	      for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
		   gsi_next (&si))
		{
		  gimple *stmt = gsi_stmt (si);
		  if (!is_gimple_assign (stmt))
		    continue;

		  /* A DCO candidate must be a struct field. */
		  tree lhs = gimple_assign_lhs (stmt);
		  srtype *t = 0;
		  srfield *f = 0;
		  tree base = NULL_TREE;
		  if (!get_base_type (lhs, base, t, f))
		    continue;

		  /* Only care the fields of a dco_type. */
		  if (t != info.dco_type)
		    continue;
		  if (f != srf)
		    continue;
		  if (dc && !dco_field_p (lhs, dc))
		    continue;

		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "[CHECK CLOSURE] ");
		      print_gimple_stmt (dump_file, stmt, 0);
		    }

		  /* Skip if we have already analyzed this stmt. */
		  if (closure_info->wt_unchange_p (stmt)
		      || closure_info->wt_change_p (stmt))
		    continue;

		  /* All write stmts could be
		     (1) unchange, i.e. optimize away encode/decode
		     (2) change with optimized value, i.e. optimized away encode
		     (3) change, i.e. use unoptimized encode

		     For case (3), we may have the scenario like below,

			B = A->field;
			... = B;
			C->field = B;

		     We still can prove C->field is from A->field, so they are
		     in a closure, but we must decode A->field and encode
		     C->field, because B may be used outside the clsoure, for
		     which we don't care about.

		     Besides, case (2) is only for array pointer. */

		  tree rhs1 = gimple_assign_rhs1 (stmt);
		  if (closure_info->wt_special_val.contains (rhs1))
		    {
		      /* Case (3) */
		      closure_info->add_wt_change (stmt);

		      if (dump_file && (dump_flags & TDF_DETAILS))
			{
			  fprintf (dump_file, "Case (3.1): need to change. \n");
			}
		      continue;
		    }

		  TEST (gimple_assign_single_p (stmt));
		  TEST (TREE_CODE (rhs1) == SSA_NAME);
		  gimple *stmt1 = SSA_NAME_DEF_STMT (rhs1);
		  if (dynamic_dco_p)
		    {
		      stmt1 = strip_copy_ptr_stmts (stmt1);
		      stmt1 = strip_array_pointer_index_pair (stmt1);

		      if (gimple_assign_single_p (stmt1))
			{
			  rhs1 = gimple_assign_rhs1 (stmt1);

			  /* Check if RHS is from the the same DCO class. */
			  srtype *t = 0;
			  srfield *f = 0;
			  tree base = NULL_TREE;
			  if (get_base_type (rhs1, base, t, f)
			      && dfc->srfields.contains (f))
			    {
			      /* Case (3) the write rhs is sourced from a read.
			       */
			      closure_info->add_wt_change (stmt);

			      if (dump_file && (dump_flags & TDF_DETAILS))
				{
				  fprintf (dump_file,
					   "Case (3.2): need to change. \n");
				}
			      continue;
			    }
			}

		      dco_bound_info *binfo = new dco_bound_info (stmt);
		      if (binfo->get_upper_bound ())
			{
			  dfc->bound_infos.safe_push (binfo);

			  if (dump_file && (dump_flags & TDF_DETAILS))
			    binfo->dump (dump_file);
			  continue;
			}
		      delete binfo;
		    }
		  else
		    {
		      /* Skip pattern pointer + offset */
		      while (
			gimple_assign_rhs_code_p (stmt1, POINTER_PLUS_EXPR))
			{
			  rhs1 = gimple_assign_rhs1 (stmt1);
			  if (TREE_CODE (rhs1) != SSA_NAME)
			    goto fail_closure;
			  stmt1 = SSA_NAME_DEF_STMT (rhs1);
			}

		      if (closure_info->mem_base_ssa != NULL_TREE
			  && SSA_NAME_DEF_STMT (closure_info->mem_base_ssa)
			       == stmt1)
			{
			  tree index = NULL_TREE;
			  if (array_pointer_p (stmt, closure_info->mem_base_ssa,
					       index))
			    {
			      /* Case (2) */
			      closure_info->add_wt_change (stmt, index);

			      if (dump_file && (dump_flags & TDF_DETAILS))
				{
				  fprintf (dump_file,
					   "Case (2.1): Got index of array ");
				  print_generic_expr (
				    dump_file, closure_info->mem_base_ssa);
				  fprintf (dump_file, " -> ");
				  print_generic_expr (dump_file, index);
				  fprintf (dump_file, "\n");
				}
			      continue;
			    }
			}
		      else if (gimple_assign_single_p (stmt1))
			{
			  rhs1 = gimple_assign_rhs1 (stmt1);
			  /* Check if RHS is from the the same DCO class. */
			  srtype *t = 0;
			  srfield *f = 0;
			  tree base = NULL_TREE;
			  if (get_base_type (rhs1, base, t, f)
			      && dfc->srfields.contains (f))
			    {
			      /* ssa_def must be rhs of the write stmts. */
			      tree ssa_def = gimple_assign_lhs (stmt1);
			      if (ssa_def == gimple_assign_rhs1 (stmt))
				{
				  if (wt_dco_field_only_p (info, dfc, ssa_def))
				    {
				      /* Case (1) */
				      closure_info->add_wt_unchange (stmt);
				      closure_info->add_rd_unchange (stmt1);

				      if (dump_file
					  && (dump_flags & TDF_DETAILS))
					{
					  fprintf (
					    dump_file,
					    "Case (1): No need to change: ");
					  print_gimple_stmt (dump_file, stmt1,
							     0);
					}
				    }
				  else
				    {
				      /* Case (3) */
				      closure_info->add_wt_change (stmt);

				      if (dump_file
					  && (dump_flags & TDF_DETAILS))
					{
					  fprintf (
					    dump_file,
					    "Case (3.2): need to change. \n");
					}
				    }

				  continue;
				}
			    }

			  /* Check if RHS is just a mem_base */
			  if (!check_var_init (rhs1,
					       closure_info->mem_base_ssa))
			    goto fail_closure;

			  closure_info->mem_base_var = rhs1;
			  /* Figure out the array index */
			  tree index = NULL_TREE;
			  if (array_pointer_p (stmt, closure_info->mem_base_var,
					       index))
			    {
			      /* Case (2) */
			      closure_info->add_wt_change (stmt, index);

			      if (dump_file && (dump_flags & TDF_DETAILS))
				{
				  fprintf (dump_file,
					   "Case (2.2): Got index of array ");
				  print_generic_expr (
				    dump_file, closure_info->mem_base_var);
				  fprintf (dump_file, "-> ");
				  print_generic_expr (dump_file, index);
				  fprintf (dump_file, "\n");
				}
			      continue;
			    }
			}
		    }

		fail_closure:
		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "[DCO CLOSURE FAIL] ");
		      print_gimple_stmt (dump_file, stmt, 0);
		    }

		  return false;
		}
	    }
	}
    }

  if (!dynamic_dco_p)
    collect_closure_rd_change (info, dfc);

  if (!dynamic_dco_p)
    {
      tree struct_type = TREE_TYPE (TREE_TYPE (closure_info->mem_base_var));
      gcc_checking_assert (TREE_CODE (struct_type) == RECORD_TYPE);
      closure_info->struct_size = TYPE_SIZE_UNIT (struct_type);

      /* Heuristically we want to find the mem_base_var that is defined by
	 struct reorg optimization. This way, we could hoist less invariants
	 and reduce register pressure eventually. */
      imm_use_iterator imm_iter;
      gimple *use_stmt = NULL;
      FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, closure_info->mem_base_ssa)
	{
	  if (!gimple_assign_single_p (use_stmt))
	    continue;

	  tree lhs = gimple_assign_lhs (use_stmt);
	  if (VAR_P (lhs)
	      && strstr (IDENTIFIER_POINTER (DECL_NAME (lhs)), "reorg_gptr0"))
	    {
	      closure_info->mem_base_var = lhs;
	      break;
	    }
	}
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    closure_info->dump ();

  return true;
}

void
ipa_struct_dco::collect_closure_rd_change (dco_info &info, dco_field_class *dfc)
{
  unsigned i;
  srfunction *srfn;
  dco_closure *closure_info = &(dfc->closure_info);

  /* Collect rd_change */
  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      basic_block bb = NULL;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
	       gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (closure_info->rd_unchange_p (stmt))
		continue;
	      if (!is_gimple_assign (stmt))
		continue;

	      for (unsigned j = 1; j < gimple_num_ops (stmt); ++j)
		{
		  srtype *t;
		  srfield *f;
		  tree base;
		  tree opnd = gimple_op (stmt, j);
		  if (!get_base_type (opnd, base, t, f))
		    continue;
		  if (t != info.dco_type)
		    continue;
		  if (!dfc->srfields.contains (f))
		    continue;

		  closure_info->add_rd_change (stmt);
		  break;
		}
	    }
	}
    }
}

/* The uses/defs for a specific bound expression.  */

class bound_expr_info
{
public:
  tree expr;
  auto_vec<gimple *> uses;
  auto_vec<gimple *> defs;

  bound_expr_info (tree expr) : expr (expr) {}
};

/* Class to store the uses and defs of each bound expr, which is classified by
   the variable decl.
   E.g. For an expr "var.field", "var" is the variable decl. */

class bound_var_info
{
public:
  tree var;

  /* Some definitions like memset/memcpy may define the whole variable.  */
  auto_vec<gimple *> var_defs;

  /* All unique const exprs in bounds related to VAR.  */
  auto_delete_vec<bound_expr_info> exprs;

  bound_var_info (tree var) : var (var) {}

  bound_expr_info *get_expr_info (tree expr)
  {
    for (auto expr_info : exprs)
      if (operand_equal_p (expr, expr_info->expr))
	return expr_info;
    return NULL;
  }

  bound_expr_info *get_or_create_expr_info (tree expr)
  {
    bound_expr_info *expr_info = get_expr_info (expr);
    if (expr_info)
      return expr_info;

    expr_info = new bound_expr_info (expr);
    exprs.safe_push (expr_info);
    return expr_info;
  }

  bool add_expr_store_def (gimple *store_stmt)
  {
    tree lhs = gimple_assign_lhs (store_stmt);
    bound_expr_info *expr_info = get_expr_info (lhs);
    if (!expr_info)
      return false;
    expr_info->defs.safe_push (store_stmt);
    return true;
  }

  bool add_builtin_call_def (gimple *, cgraph_node *, bool &supported);
  bool check_all_def_uses (gimple *start_stmt);
};

/* A known function call may define the variable or an expression.  Return true
   if found such definition.  SUPPORTED is set to false if the function is not
   unknown or not supported currently.  */

bool
bound_var_info::add_builtin_call_def (gimple *call_stmt, cgraph_node *cnode,
				      bool &supported)
{
  supported = false;
  tree decl = gimple_call_fndecl (call_stmt);
  TEST (decl)

  if (!gimple_call_builtin_p (call_stmt, BUILT_IN_NORMAL))
    {
      const char *cname = get_func_name (decl);
      /* Known read-only functions.  */
      if (strcmp (cname, "fopen") || strcmp (cname, "fclose")
	  || strcmp (cname, "fprintf"))
	{
	  supported = true;
	  return false;
	}
      return false;
    }

  switch (DECL_FUNCTION_CODE (decl))
    {
    case BUILT_IN_MEMSET:
    case BUILT_IN_MEMCPY:
    case BUILT_IN_STRCPY:
      {
	supported = true;
	if (cnode != cur_srfun->node)
	  return false;

	tree expr = gimple_call_arg (call_stmt, 0);
	if (TREE_CODE (expr) == ADDR_EXPR)
	  expr = TREE_OPERAND (expr, 0);

	if (VAR_P (expr) && expr == var)
	  {
	    var_defs.safe_push (call_stmt);
	    return true;
	  }
	if (bound_expr_info *expr_info = get_expr_info (expr))
	  {
	    expr_info->defs.safe_push (call_stmt);
	    return true;
	  }
	return false;
      }
    case BUILT_IN_PRINTF:
      /* read only calls are not definitions.  */
      supported = true;
      return false;
    default:
      return false;
    }
}

/* Check that each definition dominates the start-point and use stmts.  */

bool
bound_var_info::check_all_def_uses (gimple *start_stmt)
{
  for (auto var_def : var_defs)
    {
      TEST (stmt_dominates_stmt_p (var_def, start_stmt));
    }

  for (auto expr_info : exprs)
    {
      for (auto expr_def : expr_info->defs)
	{
	  TEST (stmt_dominates_stmt_p (expr_def, start_stmt));
	  for (auto use_stmt : expr_info->uses)
	    {
	      TEST (stmt_dominates_stmt_p (expr_def, use_stmt));
	      for (auto var_def : var_defs)
		{
		  TEST (stmt_dominates_stmt_p (var_def, use_stmt));
		}
	    }
	}
    }
  return true;
}

void
add_bound_var_info (auto_delete_vec<bound_var_info> &var_infos, tree expr,
		    gimple *use_stmt)
{
  tree var = maybe_const_expr (expr);
  gcc_checking_assert (var != NULL_TREE);
  bound_var_info *var_info = NULL;
  for (auto vi : var_infos)
    if (vi->var == var)
      {
	var_info = vi;
	break;
      }

  if (!var_info)
    {
      var_info = new bound_var_info (var);
      var_infos.safe_push (var_info);
    }

  bound_expr_info *expr_info = var_info->get_or_create_expr_info (expr);
  if (!expr_info->uses.contains (use_stmt))
    expr_info->uses.safe_push (use_stmt);
}

/* Check if each bound expr has a dominated definition, which makes our dynamic
   check on the upper bound valid.  Say if an expr may has two values, then we
   don't know if the dynamicly checked expr is the value used.  */

bool
ipa_struct_dco::check_upper_bounds (dco_info &info)
{
  auto_delete_vec<bound_var_info> var_infos;

  /* 1. Extract vars and exprs in bound informations.  */
  for (auto dfc : info.df_class)
    {
      for (auto binfo : dfc->bound_infos)
	{
	  /* TODO: support up bounds in other functions.  */
	  TEST (binfo->srfn == info.start_srfn)

	  unsigned i = 0;

	  for (auto expr : binfo->const_exprs)
	    {
	      if (TREE_CODE (expr) == INTEGER_CST)
		continue;

	      add_bound_var_info (var_infos, expr, binfo->const_stmts[i++]);
	    }
	}
    }

  SET_CFUN (info.start_srfn);
  calculate_dominance_info (CDI_DOMINATORS);

  /* 2. Collect definitions for such vars and exprs.  */
  for (auto var_info : var_infos)
    {
      varpool_node *vnode;
      struct ipa_ref *ref;

      FOR_EACH_VARIABLE (vnode)
	if (vnode->decl == var_info->var)
	  break;
      TEST (vnode != NULL)

      for (unsigned i = 0; vnode->iterate_referring (i, ref); i++)
	{
	  switch (ref->use)
	    {
	    case IPA_REF_ADDR:
	      {
		struct cgraph_node *cnode
		  = dyn_cast<cgraph_node *> (ref->referring);
		/* Other address taken is not supported currently.  */
		TEST (gimple_code (ref->stmt) == GIMPLE_CALL)

		bool supported = false;
		if (var_info->add_builtin_call_def (ref->stmt, cnode,
						    supported))
		  {
		    if (dump_file && (dump_flags & TDF_DETAILS))
		      {
			fprintf (dump_file,
				 "[UPPER BOUND] Found a definition: ");
			print_gimple_stmt (dump_file, ref->stmt, 0);
		      }
		  }
		TEST (supported)
		break;
	      }
	    case IPA_REF_STORE:
	      {
		struct cgraph_node *cnode
		  = dyn_cast<cgraph_node *> (ref->referring);
		if (cnode != cur_srfun->node)
		  break;

		if (var_info->add_expr_store_def (ref->stmt))
		  {
		    if (dump_file && (dump_flags & TDF_DETAILS))
		      {
			fprintf (dump_file,
				 "[UPPER BOUND] Found a definition: ");
			print_gimple_stmt (dump_file, ref->stmt, 0);
		      }
		  }
		break;
	      }
	    case IPA_REF_ALIAS:
	      return false;
	    default:
	      break;
	    }
	}
    }

  /* 3. Check each expr has and only has one definition which dominates the
     start-point (i.e. the place to insert dynamic checking code) and use
     stmts. */
  for (auto var_info : var_infos)
    {
      TEST (var_info->check_all_def_uses (info.fclose_stmt));
    }

  free_dominance_info (CDI_DOMINATORS);
  return true;
}

DCO_KIND
find_dco_kind_from_decl (tree decl)
{
  tree dname = DECL_NAME (decl);
  if (dname == NULL_TREE)
    return UNKNOWN_KIND;

  if (strstr (IDENTIFIER_POINTER (dname), ".sdcoap"))
    return ARRAY_POINTER;
  if (strstr (IDENTIFIER_POINTER (dname), ".sdcoai"))
    return ARRAY_INDEX;
  return UNKNOWN_KIND;
}

/* Find the sscanf that read data from a file and the data is assigned them to
   the fields of the type DECL. All fields that can be affected by input data
   will be treated as the DCO candidate fields. All DCO candidate fields will
   be classified in terms of the data type. We use an indenpendent dco_cond
   flag for each data type. */

bool
ipa_struct_dco::find_sscanf_dco_fields (dco_info &info)
{
  unsigned i, j;
  srfunction *srfn;
  dco_field *df;
  basic_block input_bb = 0;

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      basic_block bb = NULL;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
	       gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (!is_gimple_assign (stmt))
		continue;

	      /* A DCO candidate must be a struct field. */
	      tree lhs = gimple_assign_lhs (stmt);
	      srtype *t = 0;
	      srfield *f = 0;
	      tree base = NULL_TREE;
	      if (!get_base_type (lhs, base, t, f))
		continue;

	      /* Only care the fields of a dco_type. */
	      if (t != info.dco_type)
		continue;

	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "[DCO CHECK] ");
		  print_gimple_stmt (dump_file, stmt, 0);
		}

	      /* Guarantee this struct field is from a file. */
	      gimple *sscanf_stmt = 0;
	      gimple *input = 0;
	      tree mem_base_ssa = NULL_TREE;
	      DCO_KIND dco_kind = find_dco_kind_from_decl (f->fielddecl);
	      if (!find_sscanf (stmt, sscanf_stmt, input, mem_base_ssa,
				dco_kind))
		continue;

	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "[USE DCO TYPE] ");
		  print_gimple_stmt (dump_file, stmt, 0);
		}

	      /* sscanf must be in a loop */
	      if (gimple_bb (sscanf_stmt)->loop_father->num == 0)
		continue;

	      tree var = gimple_assign_rhs1 (input);

	      if (!info.sscanf_stmt)
		{
		  info.sscanf_stmt = sscanf_stmt;
		  info.init_var = base;
		  info.fh = find_fh (sscanf_stmt);
		  TEST (info.fh != NULL_TREE);
		}

	      /* Only one sscanf stmt is allowed, but we can enhance it to
		 allow multiple sscanf stmts. */
	      TEST (info.sscanf_stmt == sscanf_stmt);
	      TEST (info.init_var == base);

	      /* We will only analyze the function containing sscanf. */
	      info.start_srfn = srfn;

	      /* Check all dynamic sscanf DCO fields. */
	      tree field = TREE_OPERAND (lhs, 1);
	      FOR_EACH_VEC_ELT (info.dynamic_sscanf_dco_fields, j, df)
		{
		  /* All dco fields should define their ssas in the same BB. */
		  input_bb = gimple_bb (SSA_NAME_DEF_STMT (df->input_ssa));
		  TEST (gimple_bb (input) == input_bb);
		}

	      /* Skip all dynamic dco_fields we have found. */
	      if (dco_fields_contains (info.dynamic_sscanf_dco_fields, field)
		  || dco_fields_contains (info.dynamic_shadow_dco_fields,
					  field))
		continue;

	      /* Record a DCO field candidate. */
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "[DCO FIELD] ");
		  print_generic_expr (dump_file, field);
		  fprintf (dump_file, "\n");
		  fprintf (dump_file, "[DCO FIELD TYPE] ");
		  print_generic_expr (dump_file, TREE_TYPE (field));
		  fprintf (dump_file, "\n");
		  fprintf (dump_file, "[DCO FIELD KIND] ");
		  fprintf (dump_file, "%d\n", dco_kind);
		  fprintf (dump_file, "[DCO INPUT VAR] ");
		  print_generic_expr (dump_file, var);
		  fprintf (dump_file, "\n");
		}

	      if (POINTER_TYPE_P (f->fieldtype))
		{
		  if (!CHECK_FLAG (flag_cur_dco_aggressive,
				   IPA_DCO_STATIC_POINTER))
		    {
		      if (dump_file && (dump_flags & TDF_DETAILS))
			{
			  fprintf (dump_file,
				   "[DCO POINTER FAIL] A pointer type is "
				   "not supported yet!\n");
			}
		      continue;
		    }
		}

	      tree in_ssa = gimple_assign_rhs1 (stmt);
	      gcc_checking_assert (TREE_CODE (in_ssa) == SSA_NAME);
	      df = new dco_field (field, var, in_ssa, mem_base_ssa, dco_kind);
	      info.dynamic_sscanf_dco_fields.safe_push (df);
	      info.dco_fields.safe_push (df);
	      input_bb = gimple_bb (SSA_NAME_DEF_STMT (df->input_ssa));
	    }
	}
    }

  TEST (!info.dynamic_sscanf_dco_fields.is_empty ());
  TEST (info.start_srfn);

  /* Sort all dco_fields in the order of input ssa position. This is required
     to simplify the min_val and max_val calculation. */
  SET_CFUN (info.start_srfn);
  renumber_gimple_stmt_uids_in_blocks (&input_bb, 1);
  info.dynamic_sscanf_dco_fields.qsort (input_order_cmp);

  return true;
}

/* Find all fields that can dynamically cached. */

bool
ipa_struct_dco::find_dynamic_dco_fields (dco_info &info)
{
  /* We need to do shadow_dco detection first. This way the sscanf-dco could
     skip the shadow_dco field. */
  if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_DYNAMIC_SHADOW))
    {
      /* Check if the DCO candidates have cloned data. */
      find_data_shadow (info, true);
    }

  /* Dynamic path will only be determined by sscanf dco fields. The dynamic
     sscanf dco_fields don't include any dynamic shadow dco_fields. */
  TEST_WITH_MSG (find_sscanf_dco_fields (info), "find_sscanf_dco_fields");

  gcc_checking_assert (!info.dynamic_sscanf_dco_fields.is_empty ());

  /* Find fopen and fclose stmts that use the file handler accessed by the
     sscanf we have found. */
  TEST_WITH_MSG (find_fopen_fclose (info), "find_fopen_fclose");

  /* Find a hot block containing hot dco_fields accesses. */
  TEST_WITH_MSG (find_hot_access (info, info.dynamic_sscanf_dco_fields),
		 "find_hot_access for dynamic");

  if (!info.dynamic_shadow_dco_fields.is_empty ())
    {
      /* The original of a dynamic_shadow field must be one of dynamic_sscanf
	 fields. */
      dco_field *df;
      unsigned i;
      FOR_EACH_VEC_ELT (info.dynamic_shadow_dco_fields, i, df)
	{
	  gcc_checking_assert (df->original);

	  TEST (df->sscanf_df
		= dco_fields_contains (info.dynamic_sscanf_dco_fields,
				       df->original->fielddecl));

	  /* Record input_ssa to help init_const checking. */
	  df->input_ssa = df->sscanf_df->input_ssa;
	}
    }

  return true;
}

/* Search info.init_var backward using def/use chain until finding
   the ssa_def of one of dco_data. The ssa_def should be a calloc
   statment we have captured previously inf find_dco_data. */

bool
ipa_struct_dco::check_dco_data_init (dco_info &info)
{
  auto_vec<tree> worklist;
  auto_bitmap visited;

  bitmap_set_bit (visited, SSA_NAME_VERSION (info.init_var));
  worklist.safe_push (info.init_var);

  do
    {
      tree t = worklist.pop ();

      unsigned i;
      dco_data *dd;
      bool found_ssa_def = false;

      FOR_EACH_VEC_ELT (info.dco_data_vec, i, dd)
	{
	  if (dd->ssa_def == t)
	    {
	      found_ssa_def = true;
	      break;
	    }
	}
      if (found_ssa_def)
	return true;

      gimple *stmt = SSA_NAME_DEF_STMT (t);
      if (gimple_code (stmt) == GIMPLE_PHI)
	{
	  for (unsigned i = 0; i < gimple_phi_num_args (stmt); ++i)
	    {
	      tree arg = gimple_phi_arg_def (stmt, i);

	      if (bitmap_set_bit (visited, SSA_NAME_VERSION (arg)))
		worklist.safe_push (arg);
	    }
	}
      else if (gimple_assign_single_p (stmt)
	       || gimple_assign_rhs_code_p (stmt, POINTER_PLUS_EXPR))
	{
	  tree rhs = gimple_assign_rhs1 (stmt);
	  if (TREE_CODE (rhs) == SSA_NAME)
	    {
	      if (bitmap_set_bit (visited, SSA_NAME_VERSION (rhs)))
		worklist.safe_push (rhs);
	    }
	}
    }
  while (!worklist.is_empty ());

  return false;
}

/* Finalize what field will be coverted to bitfield, for which bits will
   be the width. Heuristically, the bitfield candidates are,
   (1) for dynamic, the original type is long int (64-bit).
   (2) for static, the max_value is not 0. */

bool
ipa_struct_dco::finalize_bitfields (dco_info &info)
{
  unsigned i, j;
  dco_cond *dc;
  dco_field *static_df;
  srfield *srf;
  unsigned total_static_bits = 0;

  /* Collect existing bitfields. */
  FOR_EACH_VEC_ELT (info.dco_type->fields, i, srf)
    {
      tree field = srf->fielddecl;

      if (!DECL_BIT_FIELD (field))
	continue;

      /* All recoganized dco_fields must not be bit field. */
      gcc_checking_assert (
	!dco_fields_contains (info.static_dco_fields, field));
      gcc_checking_assert (
	!dco_fields_contains (info.dynamic_sscanf_dco_fields, field));
      gcc_checking_assert (
	!dco_fields_contains (info.dynamic_shadow_dco_fields, field));

      total_static_bits += tree_to_uhwi (DECL_SIZE (field));
    }

  /* For static compression. Calculate bitsize for static field. */
  if (info.static_dco_p
      && CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_STATIC_BITFIELD))
    {
      FOR_EACH_VEC_ELT (info.static_dco_fields, i, static_df)
	{
	  if (POINTER_TYPE_P (TREE_TYPE (static_df->field))
	      || static_df->max_value == 0)
	    continue;

	  gcc_checking_assert (static_df->max_value > 0
			       && static_df->max_value <= 0xffffffff);

	  unsigned order = 0;
	  for (j = 0; j < 32; j++)
	    {
	      if ((static_df->max_value >> j) & 1)
		order = j;
	    }
	  static_df->bits = (order + 1);
	  total_static_bits += static_df->bits;
	}
    }

  /* For dynamic caching. */
  if (info.dynamic_dco_p
      && CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_DYNAMIC_BITFIELD))
    {
      FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
	{
	  /* Heuristically, only try bit field for big data size. */
	  if (TYPE_MAIN_VARIANT (dc->old_type) != long_integer_type_node)
	    continue;

	  /* Find the hottest field. */
	  unsigned max_ref_cnt = 0;
	  dco_field *max_df = 0;
	  dco_field *df;
	  FOR_EACH_VEC_ELT (dc->dco_fields, j, df)
	    {
	      if (df->ref_cnt > max_ref_cnt)
		{
		  max_df = df;
		  max_ref_cnt = df->ref_cnt;
		}
	    }

	  /* Choose the hottest candidate to try bitfield. */
	  max_df->bits = TYPE_PRECISION (dc->new_type) - total_static_bits;
	  TEST (max_df->bits > 0);

	  /* The DCO condition covering this field is marked as bitfield,
	     although not all of the fields for this condition are marked as
	     bitfield. */
	  dc->bits = max_df->bits;

	  /* All bit fields should have the same data type to make reorder easy.
	   */
	  FOR_EACH_VEC_ELT (info.static_dco_fields, j, static_df)
	    {
	      static_df->new_type = max_df->new_type;
	    }

	  break;
	}
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      dco_field *df;
      FOR_EACH_VEC_ELT (info.dco_fields, i, df)
	{
	  if (!df->bits)
	    continue;

	  fprintf (dump_file, "[DCO BITFIELD]: ");
	  print_generic_expr (dump_file, df->field);
	  fprintf (dump_file, ":%d", df->bits);
	  fprintf (dump_file, "\n");
	}
    }

  return true;
}

/* Check the uses of all dco_fields to make sure the DCO is valid. */

bool
ipa_struct_dco::check_dco_data_uses (dco_info &info)
{
  TEST (check_dco_data_init (info));

  if (flag_ipa_dco_clone_data)
    {
      TEST (hot_data_continuous_p (info));
    }

  return true;
}

bool
ipa_struct_dco::find_fopen_fclose (dco_info &info)
{
  unsigned i;
  srfunction *srfn;
  basic_block bb;
  gimple_stmt_iterator si;
  tree fh;

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      const char *fn_name = get_func_name (srfn->node->decl);

      SET_CFUN (srfn);

      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (is_gimple_call (stmt))
		{
		  tree decl = gimple_call_fndecl (stmt);
		  const char *callee = get_func_name (decl);
		  if (!callee || strcmp (callee, "fclose") != 0)
		    continue;

		  /* The fclose must use the same file handler as the fget,
		     which reads data for sscanf. */
		  fh = gimple_call_arg (stmt, 0);
		  if (fh != info.fh)
		    continue;

		  info.fclose_stmt = stmt;

		  /* fclose and sscanf should be invoked in the same func. */
		  TEST (info.start_srfn == srfn);

		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "\nFound fclose in function %s:\n",
			       fn_name);
		      print_gimple_stmt (dump_file, stmt, 0);
		    }

		  return true;
		}
	    }
	}
    }

  return false;
}

/* Reduce the high_bound of DC by 1, if HWI is larger than the high_bound. */

void
ipa_struct_dco::check_high_bound (dco_cond *dc, HOST_WIDE_INT hwi)
{
  HOST_WIDE_INT hwi_high_bound = tree_to_uhwi (dc->high_bound);
  if (hwi >= 0 && hwi <= hwi_high_bound)
    return;

  if (dc->special_values.contains (hwi))
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file,
		   "[DCO ASSIGN] Found special value %ld, and it is already "
		   "registerd.\n",
		   hwi);
	}

      return;
    }

  hwi_high_bound--;
  dc->high_bound = build_int_cst (TREE_TYPE (dc->high_bound), hwi_high_bound);
  dc->special_values.safe_push (hwi);
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file,
	       "[DCO ASSIGN] Found special value %ld, and reduce "
	       "high_bound to %lx\n",
	       hwi, hwi_high_bound);
    }
}

/* Return true if the VAR is a mem reference of DCO field. */

bool
ipa_struct_dco::dco_field_p (tree var, const dco_cond *dc)
{
  TEST (TREE_CODE (var) == COMPONENT_REF);

  /* Find the stmt assigning to the DCO field. */
  tree field = TREE_OPERAND (var, 1);
  dco_field *df;
  unsigned k;
  FOR_EACH_VEC_ELT (dc->dco_fields, k, df)
    {
      if (df->field == field)
	return true;
    }

  return false;
}

/* Return true if var is one of DC's input_ssa. */

bool
ipa_struct_dco::dco_input_ssa_p (tree var, const dco_cond *dc)
{
  TEST (TREE_CODE (var) == SSA_NAME);

  dco_field *df;
  unsigned k;
  FOR_EACH_VEC_ELT (dc->dco_fields, k, df)
    {
      if (df->input_ssa == var)
	return true;
    }

  return false;
}

/* Return true the VAR is loaded from another DCO field. */

bool
ipa_struct_dco::dco_field_load_p (tree var, const dco_cond *dc)
{
  TEST (TREE_CODE (var) == SSA_NAME);
  gimple *stmt = SSA_NAME_DEF_STMT (var);
  TEST (gimple_assign_load_p (stmt));
  tree rhs = gimple_assign_rhs1 (stmt);
  TEST (dco_field_p (rhs, dc));

  return true;
}

/* Return true if VAR is a global variable, and it is assigned to be a constant
   and it is never changed globally. The assumption is this VAR doesn't have
   address taken, and it the type containing it doesn't escape. */

bool
ipa_struct_dco::dco_global_const_p (tree var, HOST_WIDE_INT &hwi)
{
  srtype *t;
  srfield *f;
  tree base;
  TEST (get_base_type (var, base, t, f));
  TEST (!t->has_escaped ());
  TEST (true /* !address_taken */);

  unsigned i, j;
  const_map *cm;
  FOR_EACH_VEC_ELT (global_consts, i, cm)
    {
      if (operand_equal_p (cm->var, var))
	{
	  hwi = cm->hwi;
	  return true;
	}
    }

  bool is_const = false;
  srfunction *srfn;
  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      basic_block bb;
      gimple_stmt_iterator si;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (!gimple_assign_single_p (stmt))
		continue;

	      tree lhs = gimple_assign_lhs (stmt);
	      tree rhs = gimple_assign_rhs1 (stmt);
	      if (operand_equal_p (var, lhs))
		{
		  if (!dco_peephole_const_p (rhs, hwi))
		    return false;

		  is_const = true;
		  bool found = false;
		  FOR_EACH_VEC_ELT (global_consts, j, cm)
		    {
		      if (operand_equal_p (cm->var, var))
			{
			  if (cm->hwi != hwi)
			    {
			      if (dump_file && (dump_flags & TDF_DETAILS))
				{
				  fprintf (dump_file, "[DCO ASSIGN] ");
				  print_gimple_stmt (dump_file, stmt, 0);
				  fprintf (
				    dump_file,
				    "[DCO ASSIGN] Fail to find a constant!\n");
				}
			      return false;
			    }
			  found = true;
			}
		    }

		  if (found)
		    continue;

		  /* Record a global constant here. */
		  global_consts.safe_push (new const_map (var, hwi));

		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "[DCO ASSIGN] ");
		      print_gimple_stmt (dump_file, stmt, 0);
		      fprintf (dump_file,
			       "[DCO ASSIGN] Register a global constant!\n");
		    }
		}
	    }
	}
    }

  return is_const;
}

/* Return true if VAR is a simple constant that can be identified by peephole.
   and the HWI will be updated accordingly. Otherwise, the HWI will not be
   changed. */

bool
ipa_struct_dco::dco_peephole_const_p (tree var, HOST_WIDE_INT &hwi)
{
  if (TREE_CODE (var) == INTEGER_CST)
    {
      hwi = tree_to_shwi (var);
      return true;
    }

  TEST (TREE_CODE (var) == SSA_NAME);
  gimple *stmt = SSA_NAME_DEF_STMT (var);

  /* var might be an argument. */
  TEST (!gimple_nop_p (stmt));

  TEST (is_gimple_assign (stmt));

  if (gimple_assign_load_p (stmt))
    {
      tree rhs = gimple_assign_rhs1 (stmt);
      TEST (dco_global_const_p (rhs, hwi));
      return true;
    }

  enum tree_code rhs_code = gimple_assign_rhs_code (stmt);
  bool is_const = true;
  HOST_WIDE_INT hwi1, hwi2;
  tree rhs1, rhs2;
  switch (rhs_code)
    {
    case PLUS_EXPR:
    case MULT_EXPR:
    case MAX_EXPR:
    case MIN_EXPR:
      rhs1 = gimple_assign_rhs1 (stmt);
      rhs2 = gimple_assign_rhs2 (stmt);
      is_const &= dco_peephole_const_p (rhs1, hwi1);
      is_const &= dco_peephole_const_p (rhs2, hwi2);
      break;
    default:
      is_const = false;
      break;
    }

  if (!is_const)
    return false;

  switch (rhs_code)
    {
    case PLUS_EXPR:
      hwi = hwi1 + hwi2;
      break;
    case MULT_EXPR:
      hwi = hwi1 * hwi2;
      break;
    case MAX_EXPR:
      hwi = (hwi1 > hwi2) ? hwi1 : hwi2;
      break;
    case MIN_EXPR:
      hwi = (hwi1 < hwi2) ? hwi1 : hwi2;
      break;
    default:
      return false;
    }

  return true;
}

/* Return TRUE if VAR1 and VAR2 are equal, given some analysis results
   of DCO.  */

bool
ipa_struct_dco::dco_operand_equal_p (tree var1, tree var2)
{
  if (operand_equal_p (var1, var2))
    return true;

  /* Match code and operands.  */
  tree_code code = TREE_CODE (var1);
  TEST (code == TREE_CODE (var2));

  if (code == SSA_NAME)
    {
      gimple *stmt1 = SSA_NAME_DEF_STMT (var1);
      gimple *stmt2 = SSA_NAME_DEF_STMT (var2);
      TEST (!gimple_nop_p (stmt1) && !gimple_nop_p (stmt2));
      TEST (is_gimple_assign (stmt1) && is_gimple_assign (stmt2));
      return dco_operand_equal_p (gimple_assign_rhs_to_tree (stmt1),
				  gimple_assign_rhs_to_tree (stmt2));
    }

  /* Only part of the cases are covered now.  */
  HOST_WIDE_INT hwi;
  switch (get_gimple_rhs_class (code))
    {
    case GIMPLE_UNARY_RHS:
      if (TREE_CODE (var1) == COMPONENT_REF || TREE_CODE (var1) == MEM_REF)
	{
	  if (dco_global_const_p (var1, hwi)
	      && operand_equal_p (var1, var2, COMPARE_DECL_FLAGS))
	    return true;
	}
      return false;
    case GIMPLE_BINARY_RHS:
      return dco_operand_equal_p (TREE_OPERAND (var1, 0),
				  TREE_OPERAND (var2, 0))
	     && dco_operand_equal_p (TREE_OPERAND (var1, 1),
				     TREE_OPERAND (var2, 1));
    default:
      return false;
    }
}

/* Tune the upper boundary for dynamic caching fields. The data field
   may be assigned a constant that is larger than the maximum value. For this
   case, we can reserve a special value for it, and the data caching
   can encode/decode it by creating a map between this reserved value
   and the real big value. In the meantime, we will have to reduce the
   upper boundary for this specific field. */

bool
ipa_struct_dco::finalize_boundary (dco_info &info)
{
  unsigned i, j;
  dco_cond *dc;
  srfunction *srfn;

  /* Initialize the low_bound and high_bound. */
  FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
    {
      tree ssa_type = TREE_TYPE (dc->dco_fields[0]->input_ssa);

      /* The low bound is always zero. */
      dc->low_bound = fold_convert (ssa_type, integer_zero_node);

      /* The high bound is the max value of the type. */
      unsigned bits = dc->bits ? dc->bits : TYPE_PRECISION (dc->new_type);
      unsigned max_val_cst = wi::max_value (bits, UNSIGNED).to_uhwi ();
      dc->high_bound = build_int_cst (ssa_type, max_val_cst);
    }

  FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
    {
      FOR_EACH_VEC_ELT (functions, j, srfn)
	{
	  SET_CFUN (srfn);

	  basic_block bb;
	  gimple_stmt_iterator si;
	  FOR_EACH_BB_FN (bb, cfun)
	    {
	      for (si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
		{
		  gimple *stmt = gsi_stmt (si);
		  if (!gimple_assign_single_p (stmt))
		    continue;

		  /* Skip if it is not an assignment to DCO field. */
		  tree lhs = gimple_assign_lhs (stmt);
		  if (!dco_field_p (lhs, dc))
		    continue;

		  /* Skip if it is loaded from a DCO field. */
		  tree rhs = gimple_assign_rhs1 (stmt);
		  if (dco_field_load_p (rhs, dc))
		    continue;

		  /* Skip if it is from input_ssa. */
		  if (dco_input_ssa_p (rhs, dc))
		    {
		      dc->dfc->closure_info.wt_special_val.add (rhs);
		      continue;
		    }

		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "[DCO ASSIGN] ");
		      print_gimple_stmt (dump_file, stmt, 0);
		    }

		  /* Make sure the assignment is a constant. If possible, we
		     try to find all possible costants by peephole. */
		  HOST_WIDE_INT hwi;
		  if (dco_peephole_const_p (rhs, hwi))
		    {
		      check_high_bound (dc, hwi);
		      dc->dfc->closure_info.wt_special_val.add (rhs);
		      continue;
		    }
		}
	    }
	}
    }

  return true;
}

/* Finalize the new type for the dynamic data to be cached.  */

bool
ipa_struct_dco::finalize_dynamic_data_caching (dco_info &info)
{
  unsigned i;
  tree old_type, new_type;
  bool is_unsigned;
  dco_field *df;

  /* For dynamic fields, we heuristically change data type. */
  FOR_EACH_VEC_ELT (info.dynamic_sscanf_dco_fields, i, df)
    {
      old_type = TREE_TYPE (df->field);
      /* We have proven that all pointers must be for arrary. */
      if (POINTER_TYPE_P (old_type))
	old_type = pointer_sized_int_node;
      new_type = NULL_TREE;
      is_unsigned = TYPE_UNSIGNED (old_type);
      switch (TYPE_PRECISION (old_type))
	{
	case 64:
	  TEST (types_compatible_p (old_type, long_long_integer_type_node)
		|| types_compatible_p (old_type, pointer_sized_int_node));
	  new_type = is_unsigned ? short_unsigned_type_node : integer_type_node;
	  if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_DYNAMIC_AGGRESSIVE))
	    new_type = is_unsigned ? short_unsigned_type_node
				   : short_integer_type_node;
	  break;
	case 32:
	  TEST (types_compatible_p (old_type, integer_type_node));
	  new_type
	    = is_unsigned ? short_unsigned_type_node : short_integer_type_node;
	  break;
	case 16:
	  TEST (types_compatible_p (old_type, short_integer_type_node));
	  new_type
	    = is_unsigned ? unsigned_char_type_node : signed_char_type_node;
	  break;
	default:
	  gcc_unreachable ();
	  break;
	}

      if (new_type == NULL_TREE)
	continue;

      df->new_type = new_type;
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "[DCO DYNAMIC] change the type of ");
	  print_generic_expr (dump_file, df->field);
	  fprintf (dump_file, " from (prec=%d) to ", TYPE_PRECISION (old_type));
	  print_generic_expr (dump_file, new_type);
	  fprintf (dump_file, "(prec=%d)\n", TYPE_PRECISION (new_type));
	}
    }

  /* All dco fields will be classified in terms of the same type.
     For each type, we create a dco_cond. */
  classify_dynamic_dco_fields (info);

  /* Update the new type for DCO conditions. */
  dco_cond *dc;
  FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
    dc->new_type = dc->dco_fields[0]->new_type;

  return true;
}

/* Finalize the new type for the static data to be cached.  */

bool
ipa_struct_dco::finalize_static_data_caching (dco_info &info)
{
  unsigned i;
  tree old_type, new_type;
  dco_field *df;

  /* For static compression fields, compress them according to max_value. */
  FOR_EACH_VEC_ELT (info.static_dco_fields, i, df)
    {
      old_type = TREE_TYPE (df->field);

      if (!CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_STATIC_POINTER))
	gcc_checking_assert (df->max_value != 0);

      if (df->max_value == 0)
	{
	  if (df->dco_kind == ARRAY_INDEX)
	    new_type = old_type;
	  else
	    {
	      gcc_checking_assert (POINTER_TYPE_P (old_type));
	      new_type = pointer_sized_int_node;
	    }
	}
      else
	{
	  /* Conservatively we only do static compression for unsigned type. */
	  if (df->max_value <= 0xff)
	    new_type = unsigned_char_type_node;
	  else if (df->max_value <= 0xffff)
	    new_type = short_unsigned_type_node;
	  else if (df->max_value <= 0xffffffff)
	    new_type = unsigned_type_node;
	  else
	    gcc_unreachable ();
	}

      df->new_type = new_type;
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "[DCO STATIC] change the type of ");
	  print_generic_expr (dump_file, df->field);
	  fprintf (dump_file, " from (prec=%d) to ", TYPE_PRECISION (old_type));
	  print_generic_expr (dump_file, new_type);
	  fprintf (dump_file, "(prec=%d)\n", TYPE_PRECISION (new_type));
	}
    }
  return true;
}

/* Finalize the new type for the data to be cached.

   In the meantime, the bitfield and field boundary need to be determined by
   checking all of possible values. */

bool
ipa_struct_dco::finalize_data_caching (dco_info &info)
{
  cal_dco_ref_cnt (info);

  if (info.static_dco_p && !finalize_static_data_caching (info))
    info.static_dco_p = false;
  if (info.dynamic_dco_p && !finalize_dynamic_data_caching (info))
    info.dynamic_dco_p = false;

  TEST (info.dynamic_dco_p || info.static_dco_p);
  finalize_bitfields (info);

  if (info.dynamic_dco_p && !finalize_boundary (info))
    info.dynamic_dco_p = false;

  /* Check all data in dco_cond refer to a closure. */
  dco_cond *dc;
  unsigned i;
  FOR_EACH_VEC_ELT (info.dco_conds, i, dc)
    {
      DCO_KIND kind = dc->dco_fields[0]->dco_kind;
      gcc_checking_assert (kind != UNKNOWN_KIND);
      if (kind == ARRAY_POINTER)
	{
	  TEST_WITH_MSG (check_closure_array_pointer (info, dc->dfc),
			 "check closure for array pointer")
	}
      else
	{
	  TEST_WITH_MSG (check_closure_int (info, dc->dfc, kind),
			 "check closure")
	}
    }

  if (info.dynamic_dco_p && !check_upper_bounds (info))
    info.dynamic_dco_p = false;

  return info.dynamic_dco_p || info.static_dco_p;
}

/* Create all dco variants for the given dco_type in terms of dco_conds.
   The number of dco variants should be 2^(len(dco_conds))-1. */

bool
ipa_struct_dco::create_dco_variants (dco_info &info)
{
  unsigned i;
  tree cond_idx;
  unsigned num_of_variants = (1 << info.dco_conds.length ());

  create_dyn_path (info);

  if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_DYNAMIC_MULT))
    {
      /* Create all dco variants for the dco_type. */
      for (i = 1; i < num_of_variants; i++)
	{
	  /* Create a case constant for this variant. */
	  cond_idx = build_int_cst (TREE_TYPE (info.dyn_path), i);

	  /* Initialize a new dco_variant. */
	  info.dco_variants.safe_push (new dco_variant (cond_idx, i));
	}
    }
  else
    {
      i = num_of_variants - 1;
      cond_idx = build_int_cst (TREE_TYPE (info.dyn_path), i);
      info.dco_variants.safe_push (new dco_variant (cond_idx, i));
    }

  return true;
}

/* Classify all fields for the given dco_type. */

void
ipa_struct_dco::classify_dynamic_dco_fields (dco_info &info)
{
  unsigned i, j;
  dco_field *df;
  dco_cond *dc, *new_dc;
  bool found_cond;

  /* Figure out all of dco conditions. A single dco condition maps to multiple
     fields with the same data type. */
  FOR_EACH_VEC_ELT (info.dynamic_sscanf_dco_fields, i, df)
    {
      found_cond = false;
      FOR_EACH_VEC_ELT (info.dco_conds, j, dc)
	{
	  if (TREE_TYPE (df->field) == dc->old_type)
	    {
	      /* Map from dco_field to uniq dco_cond */
	      df->cond = dc;
	      /* Map from dco_cond to multiple dco_fields */
	      dc->dco_fields.safe_push (df);

	      found_cond = true;
	      break;
	    }
	}

      if (!found_cond)
	{
	  new_dc = new dco_cond (TREE_TYPE (df->field));
	  /* Map from dco_field to uniq dco_cond */
	  df->cond = new_dc;
	  /* Map from dco_cond to multiple dco_fields */
	  new_dc->dco_fields.safe_push (df);

	  gcc_checking_assert (!info.df_class.is_empty ());

	  /* Find the corresponding field type class. */
	  unsigned m, n;
	  dco_field_class *dfc;
	  srfield *srf;
	  FOR_EACH_VEC_ELT (info.df_class, m, dfc)
	    {
	      FOR_EACH_VEC_ELT (dfc->srfields, n, srf)
		if (srf->fielddecl == df->field)
		  {
		    new_dc->dfc = dfc;
		    dfc->dc = new_dc;
		    break;
		  }
	    }
	  gcc_checking_assert (new_dc->dfc);

	  info.dco_conds.safe_push (new_dc);
	  new_dc->bitmask = info.dco_conds.length ();
	  /* Copy mem_base_ssa from dco_field to dco_cond. */
	  new_dc->dfc->closure_info.mem_base_ssa = df->mem_base_ssa;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "[DCO COND] ");
	      print_generic_expr (dump_file, new_dc->old_type);
	      fprintf (dump_file, "\n");
	      fprintf (dump_file, "[DCO COND POS ] ");
	      fprintf (dump_file, "%d\n", new_dc->bitmask);
	    }
	}
    }
}

/* Scan field's assignments globally to determin whether it can be statically
   compressed or not. */

bool
ipa_struct_dco::static_compress_p (dco_info &info, tree field)
{
  unsigned i;
  srfunction *srfn;
  auto_vec<tree> worklist;
  auto_bitmap visited;
  HOST_WIDE_INT max_value = 0;
  tree lhs, rhs;

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      basic_block bb;
      gimple_stmt_iterator si;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (!gimple_assign_single_p (stmt))
		continue;

	      /* A DCO candidate must be a struct field. */
	      lhs = gimple_assign_lhs (stmt);
	      srtype *t = 0;
	      srfield *f = 0;
	      tree base = NULL_TREE;
	      if (!get_base_type (lhs, base, t, f))
		continue;

	      if (f->fielddecl != field)
		continue;

	      rhs = gimple_assign_rhs1 (stmt);
	      worklist.safe_push (rhs);
	      do
		{
		  tree t = worklist.pop ();

		  if (TREE_CODE (t) == INTEGER_CST)
		    {
		      HOST_WIDE_INT value = TREE_INT_CST_LOW (t);
		      /* Don't compress negative value conservatively. */
		      if (value < 0)
			{
			  max_value = 0;
			  goto found_max_value;
			}
		      if (value > max_value)
			max_value = value;
		      continue;
		    }
		  else if (TREE_CODE (t) == SSA_NAME)
		    {
		      /* Skip if already visited. */
		      if (!bitmap_set_bit (visited, SSA_NAME_VERSION (t)))
			continue;
		    }
		  else
		    {
		      max_value = 0;
		      goto found_max_value;
		    }

		  gimple *stmt = SSA_NAME_DEF_STMT (t);
		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "[DCO STATIC] check field ");
		      print_generic_expr (dump_file, field);
		      fprintf (dump_file, ", ");
		      print_gimple_stmt (dump_file, stmt, 0);
		    }
		  if (gimple_code (stmt) == GIMPLE_PHI)
		    {
		      for (unsigned i = 0; i < gimple_phi_num_args (stmt); ++i)
			{
			  tree arg = gimple_phi_arg_def (stmt, i);
			  worklist.safe_push (arg);
			}
		    }
		  else if ((rhs = get_ssa_copy (stmt)) != NULL_TREE)
		    {
		      worklist.safe_push (rhs);
		    }
		  else
		    {
		      max_value = 0;
		      goto found_max_value;
		    }
		}
	      while (!worklist.is_empty ());
	    }
	}
    }

found_max_value:

  /* We cannot know the max value at compile time, if it is 0. */
  TEST (max_value);

  dco_field *df = new dco_field (field, max_value, 0, false);

  info.static_dco_fields.safe_push (df);
  info.dco_fields.safe_push (df);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "[DCO STATIC] Found a static compression type : ");
      print_generic_expr (dump_file, field);
      fprintf (dump_file, ", max_value = %ld\n", max_value);
    }

  return true;
}

/* Accumulate reference count if var is a DCO field access. */

void
ipa_struct_dco::accumulate_dco_field (dco_info &info, tree var)
{
  srtype *t;
  srfield *f;
  tree base;
  TEST_RET_VOID (get_base_type (var, base, t, f));
  TEST_RET_VOID (t == info.dco_type);

  unsigned i;
  dco_field *df;
  FOR_EACH_VEC_ELT (info.dco_fields, i, df)
    {
      if (df->field == f->fielddecl)
	df->ref_cnt++;
    }
}

/* Calculate the reference count of all DCO fields. */

void
ipa_struct_dco::cal_dco_ref_cnt (dco_info &info)
{
  unsigned i;
  srfunction *srfn;

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      basic_block bb = NULL;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
	       gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (!is_gimple_assign (stmt))
		continue;

	      accumulate_dco_field (info, gimple_assign_lhs (stmt));
	      for (unsigned j = 1; j < gimple_num_ops (stmt); ++j)
		accumulate_dco_field (info, gimple_op (stmt, j));
	    }
	}
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      dco_field *df;
      fprintf (dump_file, "[DCO] Reference count\n");
      FOR_EACH_VEC_ELT (info.dco_fields, i, df)
	{
	  print_generic_expr (dump_file, df->field);
	  fprintf (dump_file, " : %d\n", df->ref_cnt);
	}
    }
}

dco_field *
ipa_struct_dco::dco_fields_contains (auto_vec<dco_field *> &dfs, tree field)
{
  dco_field *df;
  unsigned j;
  FOR_EACH_VEC_ELT (dfs, j, df)
    {
      if (df->field == field)
	return df;
    }
  return 0;
}

/* Return true if find array pointer that can be statically lowered or array
   index that can be dynamically lowered. */

bool
ipa_struct_dco::find_array_index (dco_info &info)
{
  bool found_array_idx = false;

  dco_field_class *dfc;
  unsigned i;
  FOR_EACH_VEC_ELT (info.df_class, i, dfc)
    {
      bool array_ptr_p = false;
      if (POINTER_TYPE_P (dfc->fieldtype))
	{
	  if (!find_mem_base_ssa_array_pointer (info, dfc))
	    continue;
	  array_ptr_p = true;
	}
      else if (TREE_CODE (dfc->fieldtype) == INTEGER_TYPE)
	{
	  if (!find_mem_base_ssa_array_index (dfc))
	    continue;
	}
      else
	continue;

      /* Check all pointers pointing to a memory space closure. */
      if (array_ptr_p && !check_closure_array_pointer (info, dfc))
	continue;

      srfield *srf;
      unsigned j;
      FOR_EACH_VEC_ELT (dfc->srfields, j, srf)
	{
	  /* Skip the field that is already identified by other static DCO. */
	  dco_field *df
	    = dco_fields_contains (info.static_dco_fields, srf->fielddecl);
	  if (df)
	    continue;

	  /* Record a new static dco field, and mark it as an ARRAY_INDEX. */
	  df = new dco_field (srf->fielddecl, HOST_WIDE_INT (0), 0, false,
			      array_ptr_p ? ARRAY_POINTER : ARRAY_INDEX);

	  info.static_dco_fields.safe_push (df);
	  info.dco_fields.safe_push (df);
	  df->mem_base_ssa = dfc->closure_info.mem_base_ssa;
	  if (array_ptr_p)
	    df->arr_ptr = &(dfc->closure_info);

	  found_array_idx = true;

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "Found array %s field ",
		       array_ptr_p ? "pointer" : "index");
	      print_generic_expr (dump_file, df->field);
	      fprintf (dump_file, "\n");
	    }
	}
    }

  return found_array_idx;
}

/* Scan all of fields in dco_type to check whether each can be statically
   compressed or not. This can help further data caching. */

bool
ipa_struct_dco::find_static_dco_fields (dco_info &info)
{
  bool found_static_compress = false;
  unsigned i;
  srfield *srf;

  /* It is high priority to find shadow data. */
  if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_STATIC_SHADOW))
    {
      /* Check if the DCO candidates have cloned data. */
      found_static_compress |= find_data_shadow (info, false);
    }

  FOR_EACH_VEC_ELT (info.dco_type->fields, i, srf)
    {
      if (dco_fields_contains (info.static_dco_fields, srf->fielddecl))
	continue;

      found_static_compress |= static_compress_p (info, srf->fielddecl);
    }

  if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_STATIC_POINTER))
    found_static_compress |= find_array_index (info);

  if (found_static_compress)
    gcc_checking_assert (!info.static_dco_fields.is_empty ());

  /* Find a hot block containing hot dco_fields accesses. */
  TEST_WITH_MSG (find_hot_access (info, info.static_dco_fields),
		 "find_hot_access for static");

  TEST_WITH_MSG (found_static_compress, "find_static_dco_fields");
  return true;
}

/* Classify all fields in dco_type in terms of data type. */

void
ipa_struct_dco::classify_dco_fields (dco_info &info)
{
  srfield *srf;
  dco_field_class *dfc;
  unsigned i, j;

  FOR_EACH_VEC_ELT (info.dco_type->fields, i, srf)
    {
      bool found = false;
      FOR_EACH_VEC_ELT (info.df_class, j, dfc)
	{
	  if (dfc->fieldtype == srf->fieldtype)
	    {
	      dfc->srfields.safe_push (srf);
	      srf->dfc = dfc;
	      found = true;
	      break;
	    }
	}
      if (!found)
	{
	  dfc = new dco_field_class (srf);
	  srf->dfc = dfc;
	  info.df_class.safe_push (dfc);
	}
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      FOR_EACH_VEC_ELT (info.df_class, i, dfc)
	{
	  fprintf (dump_file, "[DCO FIELD TYPE] %d\n", i);
	  FOR_EACH_VEC_ELT (dfc->srfields, j, srf)
	    {
	      print_generic_expr (dump_file, srf->fieldtype);
	      fprintf (dump_file, " : ");
	      print_generic_expr (dump_file, srf->fielddecl);
	      fprintf (dump_file, "\n");
	    }
	}
    }
}

/* Return true if the memory at BASE pointer is initialized as zero. */

bool
ipa_struct_dco::check_init_zero (tree base)
{
  tree rhs1 = NULL_TREE;
  tree mem_base = NULL_TREE;
  TEST (TREE_CODE (base) == SSA_NAME);

  /* Search backward following def/use chain until finding a memory pointer. */
  gimple *stmt = SSA_NAME_DEF_STMT (base);
  while (gimple_bb (stmt))
    {
      if (gimple_assign_rhs_code_p (stmt, POINTER_PLUS_EXPR))
	{
	  rhs1 = gimple_assign_rhs1 (stmt);
	  TEST (TREE_CODE (rhs1) == SSA_NAME);
	  stmt = SSA_NAME_DEF_STMT (rhs1);
	}
      else if (gimple_assign_single_p (stmt))
	{
	  rhs1 = gimple_assign_rhs1 (stmt);
	  TEST (TREE_CODE (rhs1) == COMPONENT_REF);
	  break;
	}
      else
	return false;
    }

  mem_base = rhs1;
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Found memory base ");
      print_generic_expr (dump_file, mem_base);
      fprintf (dump_file, "\n");
    }

  /* Scan all references of the memory base, i.e. rhs1, to make sure this
     piece of memory is initialized to be zero. */
  srfunction *srfn;
  unsigned i;
  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      basic_block bb = NULL;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
	       gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (!is_gimple_assign (stmt))
		continue;

	      tree lhs = gimple_assign_lhs (stmt);
	      if (operand_equal_p (mem_base, lhs))
		{
		  TEST (gimple_assign_single_p (stmt));
		  rhs1 = gimple_assign_rhs1 (stmt);
		  TEST (TREE_CODE (rhs1) == SSA_NAME);
		  TEST (gimple_call_builtin_p (SSA_NAME_DEF_STMT (rhs1),
					       BUILT_IN_CALLOC));

		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "Found zero initialization stmt ");
		      print_gimple_stmt (dump_file, stmt, 0);
		    }

		  return true;
		}
	    }
	}
    }

  return false;
}

/* The unpair data copy statements need to meet some requirements,
   (1) All accesses the same field
   (2) Initialize to be zero
   (3) The unpaired value is a constant
   Return SRF as the field that will be treated as a shadow. */

bool
ipa_struct_dco::check_unpair_copy (
  const auto_vec<gimple *> &unpair_stmts,
  const auto_vec<srfunction *> &unpair_stmts_func, srfield *&srf,
  auto_vec<tree> &init_consts)
{
  unsigned i;
  gimple *stmt;
  srtype *t = 0;
  srfield *f = 0;
  tree base = NULL_TREE;
  tree struct_base = NULL_TREE;
  srf = 0;

  FOR_EACH_VEC_ELT (unpair_stmts, i, stmt)
    {
      SET_CFUN (unpair_stmts_func[i]);

      /* Condition (3) */
      TEST (gimple_assign_single_p (stmt));
      tree rhs = gimple_assign_rhs1 (stmt);
      TEST (TREE_CODE (rhs) == INTEGER_CST);
      init_consts.safe_push (rhs);

      tree lhs = gimple_assign_lhs (stmt);
      TEST (get_base_type (lhs, base, t, f));
      if (!srf)
	{
	  srf = f;
	  struct_base = base;
	  continue;
	}
      /* Condition (1) */
      TEST (srf == f);
      TEST (struct_base == base);
    }

  /* Condition (2) */
  TEST (check_init_zero (struct_base));

  /* Support only 1 init_const */
  TEST (init_consts.length () == 1);

  return true;
}

/* Find if there is any field that is not accessed and can be removed.  */

void
ipa_struct_dco::find_dead_fields (dco_info &info)
{
  tree type = info.dco_type->type;

  /* 1. find fields unaccessed.  If a field only has write, it is also marked as
     unaccessed and can be removed.  */

  record_field_map4_t record_field_map;
  gimple_accessor accesser (record_field_map);
  accesser.walk ();
  if (detected_incompatible_syntax)
    return;

  record_field_offset_map4_t dead_field_map;
  /* A type may be treated as escaping by TEA after struct reorg (before that,
     it is non-escaping).  This is a fixup.  */
  (const_cast<tpartitions2_t &> (tea_types)).non_escaping.add (type);
  obtain_nonescaping_unaccessed_fields (tea_types, record_field_map, OPT_Wdfa,
					dead_field_map);
  field_offsets2_t **dead_field_offsets = dead_field_map.get (type);
  if (detected_incompatible_syntax || !dead_field_offsets
      || (*dead_field_offsets)->is_empty ())
    return;

  /* 2. mark the corresponding srfield as dead field. */
  for (tree field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
    {
      if (!(*dead_field_offsets)->contains (bitpos_of_field (field)))
	continue;
      for (auto dfc : info.df_class)
	{
	  if (dfc->dc)
	    continue;
	  if (srfield *srf = dfc->get_srfield_from_decl (field))
	    {
	      if (srf->static_df)
		continue;
	      srf->dead_field_p = true;
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "[DCO] Found a dead field: ");
		  print_generic_expr (dump_file, field);
		  fprintf (dump_file, "\n");
		}
	    }
	}
    }
}

/* Check if the DCO candidates have data shadow. If yes, we may further
   handle the cloned copy,

   * For static DCO, we use a boolean value to describe the shadow.
   * For dynamic DCO, we remove the shadow by checking exceptional cases
   dynamically.  */

bool
ipa_struct_dco::find_data_shadow (dco_info &info, bool dynamic)
{
  unsigned i, j;
  dco_field_class *dfc;
  srfunction *srfn;
  gimple *stmt1, *stmt2;
  bool found_shadow = false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "[DCO] Check data copy ...\n");

  FOR_EACH_VEC_ELT (info.df_class, i, dfc)
    {
      /* Only handle the case that two fields have the same type. */
      if (dfc->srfields.length () != 2)
	continue;

      auto_delete_vec<auto_vec<gimple *> > pair_stmts;
      auto_vec<gimple *> *pair_stmt;
      auto_vec<gimple *> unpair_stmts;
      auto_vec<srfunction *> unpair_stmts_func;
      auto_vec<srfunction *> pair_stmts_func;
      int pair_id = 0;
      srfield *srf = 0;
      srfield *shadow_srf;
      srfield *original_srf;
      int shadow_index;
      dco_field *df;
      gimple *stmt;
      auto_vec<tree> init_consts;

      /* Scan all references of the dco fields with the same type to detect
	 whether they are copies or not. */
      FOR_EACH_VEC_ELT (functions, j, srfn)
	{
	  SET_CFUN (srfn);

	  basic_block bb = NULL;
	  FOR_EACH_BB_FN (bb, cfun)
	    {
	      stmt1 = stmt2 = 0;
	      for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
		   gsi_next (&si))
		{
		  gimple *stmt = gsi_stmt (si);
		  if (!is_gimple_assign (stmt))
		    continue;

		  srtype *t = 0;
		  srfield *f = 0;
		  tree base = NULL_TREE;
		  tree lhs = gimple_assign_lhs (stmt);
		  if (!get_base_type (lhs, base, t, f))
		    continue;
		  if (t != info.dco_type)
		    continue;
		  if (f->fielddecl != (dfc->srfields)[0]->fielddecl
		      && f->fielddecl != (dfc->srfields)[1]->fielddecl)
		    continue;

		  if (!gimple_assign_single_p (stmt))
		    goto fail_check;

		  /* Make sure only two stmts to assign each of DCO fields. */
		  if (!stmt1)
		    {
		      pair_id = (f->fielddecl != (dfc->srfields)[0]->fielddecl);
		      stmt1 = stmt;
		    }
		  else if (!stmt2)
		    {
		      stmt2 = stmt;
		      tree rhs1 = gimple_assign_rhs1 (stmt1);
		      tree rhs2 = gimple_assign_rhs1 (stmt2);
		      if (!dco_operand_equal_p (rhs1, rhs2))
			goto fail_check;

		      /* Record pair stmts and make sure the elements in
			 pair_stmt and dfc->srfields are 1:1 map. */
		      auto_vec<gimple *> *pair_stmt = new auto_vec<gimple *> ();
		      if (pair_id == 0)
			{
			  pair_stmt->safe_push (stmt1);
			  pair_stmt->safe_push (stmt2);
			}
		      else
			{
			  pair_stmt->safe_push (stmt2);
			  pair_stmt->safe_push (stmt1);
			}
		      pair_stmts.safe_push (pair_stmt);
		      pair_stmts_func.safe_push (srfn);
		      stmt1 = stmt2 = 0;
		    }
		  else
		    gcc_unreachable ();

		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "[BB #%d] ", bb->index);
		      print_gimple_stmt (dump_file, stmt, 0);
		    }
		}

	      /* We will need to handle unpair assignments. */
	      if (stmt1 && !stmt2)
		{
		  unpair_stmts.safe_push (stmt1);
		  unpair_stmts_func.safe_push (srfn);
		}
	    }
	}

      if (!unpair_stmts.is_empty ())
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "Unpair assignments ...\n");
	      gimple *stmt;
	      FOR_EACH_VEC_ELT (unpair_stmts, j, stmt)
		{
		  fprintf (dump_file, "[BB #%d] ", gimple_bb (stmt)->index);
		  print_gimple_stmt (dump_file, stmt, 0);
		}
	    }

	  if (!check_unpair_copy (unpair_stmts, unpair_stmts_func, srf,
				  init_consts))
	    goto fail_check;

	  /* Mark the other one in the pair as a shadow. */
	  gcc_checking_assert (dfc->srfields.length () == 2);
	  gcc_checking_assert (srf);
	  if ((dfc->srfields)[0] == srf)
	    shadow_index = 1;
	  else if ((dfc->srfields)[1] == srf)
	    shadow_index = 0;
	  else
	    gcc_unreachable ();
	}
      else
	shadow_index = 0;

      found_shadow = true;
      original_srf = (dfc->srfields)[1 - shadow_index];
      shadow_srf = (dfc->srfields)[shadow_index];

      /* Add a new static dco_field. */
      df = dco_fields_contains (info.dynamic_shadow_dco_fields,
				shadow_srf->fielddecl);
      if (df)
	{
	  df->original = original_srf;
	  df->max_value = 1;
	}
      else
	{
	  df = new dco_field (shadow_srf->fielddecl, 1, original_srf, dynamic);
	  if (dynamic)
	    info.dynamic_shadow_dco_fields.safe_push (df);
	  else
	    info.static_dco_fields.safe_push (df);
	  info.dco_fields.safe_push (df);
	}

      /* Record init constatns. */
      df->init_consts = init_consts.copy ();

      /* Record all shadow stmts. */
      FOR_EACH_VEC_ELT (pair_stmts, j, pair_stmt)
	{
	  stmt = (*pair_stmt)[shadow_index];
	  df->shadow_stmts.safe_push (stmt);
	  df->shadow_stmts_func.safe_push (pair_stmts_func[j]);
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    print_gimple_stmt (dump_file, stmt, 0);
	}

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Found shadow field ");
	  print_generic_expr (dump_file,
			      (dfc->srfields)[shadow_index]->fielddecl);
	  fprintf (dump_file, "\n");
	}
      continue;

    fail_check:
      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "[FAIL CHECK COPY]\n");
    }

  return found_shadow;
}

/* Return truen if we can find a hot loop, in which
   (1) there is a struct copy for the dco_type
   (2) or, all dco_fields have reads and writes. */

bool
ipa_struct_dco::find_hot_access (dco_info &info,
				 auto_vec<dco_field *> &dco_fields)
{
  unsigned i, j;
  srfunction *srfn;
  dco_field *df;

  FOR_EACH_VEC_ELT (functions, i, srfn)
    {
      SET_CFUN (srfn);

      basic_block bb = NULL;
      FOR_EACH_BB_FN (bb, cfun)
	{
	  /* Skip blocks not in a loop. */
	  if (!bb->loop_father->num)
	    continue;

	  /* Skip input loop containing sscanf stmt. */
	  if (info.sscanf_stmt
	      && (bb->loop_father == gimple_bb (info.sscanf_stmt)->loop_father))
	    continue;

	  hash_set<tree> fields;
	  /* Scan the block to find read and writes for all dco_fields. */
	  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
	       gsi_next (&si))
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (!is_gimple_assign (stmt))
		continue;

	      tree lhs = gimple_assign_lhs (stmt);

	      /* Check if it is a struct copy. */
	      if (info.dco_type->type == TREE_TYPE (lhs))
		{
		  if (gimple_assign_single_p (stmt))
		    {
		      tree rhs = gimple_assign_rhs1 (stmt);
		      if (types_dco_compatible_p (info.dco_type->type,
						  TREE_TYPE (rhs)))
			{
			  if (dump_file && (dump_flags & TDF_DETAILS))
			    {
			      fprintf (
				dump_file,
				"[DCO] Found copying struct in hot block : \n");
			      gimple_dump_bb (dump_file, bb, 0, TDF_SLIM);
			      fprintf (dump_file, "\n");
			    }

			  return true;
			}
		    }

		  continue;
		}

	      srtype *t = 0;
	      srfield *f = 0;
	      tree base = NULL_TREE;
	      if (!get_base_type (lhs, base, t, f))
		continue;

	      /* Only care the fields of a dco_type. */
	      if (t != info.dco_type)
		continue;

	      fields.add (f->fielddecl);
	    }

	  /* Scan all dco_fields to check if all writes exist. */
	  bool write_all = true;
	  FOR_EACH_VEC_ELT (dco_fields, j, df)
	    {
	      if (!fields.contains (df->field))
		{
		  write_all = false;
		  break;
		}
	    }

	  /* Early exit when finding hot write. */
	  if (write_all)
	    {
	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (
		    dump_file,
		    "[DCO] Found writes to all dco fields a hot block : \n");
		  gimple_dump_bb (dump_file, bb, 0, TDF_SLIM);
		  fprintf (dump_file, "\n");
		}

	      return true;
	    }
	}
    }

  return false;
}

/* Find a dynamic-DCO candidate. */

bool
ipa_struct_dco::find_dyn_dco_cand (dco_info &info)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    fprintf (dump_file, "[DCO] Looking for dynamic dco fields ...\n");

  /* Find sscanf and record the DCO candidate fields. In the meantime, the
     start function is determined. */
  TEST_WITH_MSG (find_dynamic_dco_fields (info), "find_dynamic_dco_fields");

  /* Find all basic blocks need to be cloned in DCO.  */
  TEST_WITH_MSG (find_dco_paths (info), "find_dco_paths");

  /* Find variables/arrays to be cached.  */
  TEST_WITH_MSG (find_dco_data (info), "find_dco_data");

  /* Find variables/arrays to be modified according to dco_data.  */
  TEST_WITH_MSG (find_dco_refs (info), "find_dco_refs");

  /* Check all other assign stmts to record the boundary for all the DCO
     candidate fields. */
  TEST_WITH_MSG (check_dco_data_uses (info), "check_dco_data_uses");

  return true;
}

/* Check that each field of TYPE should not have a recursive srtype.  */

static bool
no_recursive_field_type_p (srtype *type)
{
  /* A dead field is ignored as it will be removed in transformation.  */
  for (auto srf : type->fields)
    if (!srf->dead_field_p && srf->type == type)
      return false;
  return true;
}

/* Find a DCO candidate. */

bool
ipa_struct_dco::find_dco_cand (dco_info &info)
{
  classify_dco_fields (info);

  /* Static compression analysis goes first. */
  if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_STATIC))
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "[DCO] Looking for static dco fields ...\n");

      /* Some fields can be compressed without dynmaic checking. */
      info.static_dco_p = find_static_dco_fields (info);

      /* Some fields can be removed. */
      if (info.static_dco_p
	  && CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_STATIC_DEAD_FIELD))
	find_dead_fields (info);
    }

  /* Avoid the complex type we are not supporting now.  */
  TEST_WITH_MSG (no_recursive_field_type_p (info.dco_type),
		 "no recursive field type");

  /* Dynamic caching analysis excludes static compression results. */
  if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_DYNAMIC))
    {
      info.dynamic_dco_p = find_dyn_dco_cand (info);
    }

  TEST_WITH_MSG (info.static_dco_p || info.dynamic_dco_p, "find DCO candidate");

  /* Finalize the new types for the data to be cached. */
  TEST_WITH_MSG (finalize_data_caching (info), "finalize_data_caching");

  return true;
}

/* Record new field and it's related mem_base_ssa. The DCOAI would be only
   meaningful for array index dco field. */

void
ipa_struct_dco::record_dcoai (dco_info &info,
			      auto_vec<dco_array_index *> &dcoai)
{
  unsigned i;
  dco_field *df;

  FOR_EACH_VEC_ELT (info.dco_fields, i, df)
    {
      if (df->dco_kind != ARRAY_INDEX && df->dco_kind != ARRAY_POINTER)
	continue;

      dcoai.safe_push (new dco_array_index (df->new_field, df->mem_base_ssa));
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "[DCOAI] ");
	  print_generic_expr (dump_file, df->new_field);
	  if (df->mem_base_ssa)
	    {
	      fprintf (dump_file, " -> ");
	      print_gimple_stmt (dump_file,
				 SSA_NAME_DEF_STMT (df->mem_base_ssa), 0);
	    }
	}
    }
}

unsigned int
ipa_struct_dco::execute (auto_vec<dco_array_index *> &dcoai)
{
  unsigned i;
  unsigned retval = 0;
  srtype *type;

  {
    push_dump_file save (NULL, TDF_NONE);
    ipa_type_escape_analysis_init ();
  }

  if (!record_accesses ())
    return 0;

  prune_escaped_types ();

  /* Handle all DCO types. */
  FOR_EACH_VEC_ELT (types, i, type)
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "[DCO] Analyzing type : ");
	  print_generic_expr (dump_file, type->type);
	  fprintf (dump_file, "\n");
	}

      /* Check if the type is escaped or not. */
      if (!type->dco_candidate_p ())
	continue;

      dco_info info (type);

      /* Analyze the 1st DCO candidate only. */
      if (!find_dco_cand (info))
	continue;

      gcc_checking_assert (info.static_dco_p ^ info.dynamic_dco_p);
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "[DCO] Found a valid DCO candidate : ");
	  print_generic_expr (dump_file, type->type);
	  fprintf (dump_file, "\n");
	}

      type->dinfo = &info;
      if (info.static_dco_p)
	{
	  retval |= static_dco_transform (info);

	  /* Record array pointer lowering info, pass it to dynamic DCO. */
	  record_dcoai (info, dcoai);
	}
      if (info.dynamic_dco_p)
	{
	  /* The dynamic condition checking code generation will use dcoai. */
	  info.dcoai = &dcoai;

	  retval |= dynamic_dco_transform (info);
	}

      /* Support only 1 DCO type for now. */
      break;
    }

  {
    push_dump_file save (NULL, TDF_NONE);
    ipa_type_escape_analysis_exit ();
  }

  return retval;
}

const pass_data pass_data_ipa_struct_dco = {
  SIMPLE_IPA_PASS,   /* type */
  "struct-dco",	     /* name */
  OPTGROUP_NONE,     /* optinfo_flags */
  TV_IPA_STRUCT_DCO, /* tv_id */
  0,		     /* properties_required */
  0,		     /* properties_provided */
  0,		     /* properties_destroyed */
  0,		     /* todo_flags_start */
  0,		     /* todo_flags_finish */
};

class pass_ipa_struct_dco : public simple_ipa_opt_pass
{
public:
  pass_ipa_struct_dco (gcc::context *ctxt)
    : simple_ipa_opt_pass (pass_data_ipa_struct_dco, ctxt)
  {}

  /* opt_pass methods: */
  virtual bool gate (function *);
  virtual unsigned int execute (function *)
  {
    /* If there is a top-level inline-asm, the pass immediately returns.  */
    if (symtab->first_asm_symbol ())
      return 0;

    unsigned retval = 0;
    flag_cur_dco_aggressive
      = (flag_ipa_dco_aggressive_static << IPA_DCO_STATIC_POS);

    /* We only pass DCOAI info from SDCO to DDCO. */
    auto_delete_vec<dco_array_index> dcoai;

    /* Static-DCO */
    if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_STATIC_FLAGS))
      {
	retval |= ipa_struct_dco ().execute (dcoai);

	if (retval &= TODO_remove_functions)
	  symtab->remove_unreachable_nodes (dump_file);
      }

    /* Force to use single dynamic path if we use clone_data method. */
    if (flag_ipa_dco_clone_data)
      flag_ipa_dco_aggressive_dynamic &= ~IPA_DCO_DYNAMIC_MULT;

    flag_cur_dco_aggressive
      = (flag_ipa_dco_aggressive_dynamic << IPA_DCO_DYNAMIC_POS);

    /* Dynamic-DCO */
    if (CHECK_FLAG (flag_cur_dco_aggressive, IPA_DCO_DYNAMIC_FLAGS))
      retval |= ipa_struct_dco ().execute (dcoai);

    return retval;
  }

}; // class pass_ipa_struct_dco

bool
pass_ipa_struct_dco::gate (function *)
{
  return optimize >= 3 && flag_ipa_struct_dco
	 /* Only enable struct optimizations in C since other
	    languages' grammar forbid.  */
	 && lang_c_p ();
}

} // anon namespace

simple_ipa_opt_pass *
make_pass_ipa_struct_dco (gcc::context *ctxt)
{
  return new pass_ipa_struct_dco (ctxt);
}
