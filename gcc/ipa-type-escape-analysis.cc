/* IPA Type Escape Analysis and Dead Field Elimination
   Copyright (C) 2019-2022 Free Software Foundation, Inc.

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
#include "diagnostic.h"
#include "gimple.h"
#include "stor-layout.h"
#include "gimple-iterator.h"
#include "tree-vrp.h"
#include "stringpool.h"
#include "tree-ssanames.h"
#include "gimple-ssa.h"
#include "gimple-pretty-print.h"
#include "gimple-walk.h"
#include "tree-cfg.h"
#include "ipa-type-escape-analysis.h"
#include "ipa-utils.h"

#define ABORT_IF_NOT_C true

extern bool sizeof_analysis_succeeds;
bool detected_incompatible_syntax = false;
bool
_filter_known_function (tree fndecl);
static bool
_follow_def_to_find_if_really_cast (tree rhs);

tpartitions2_t in_types;
const tpartitions2_t &tea_types = in_types;

/* Determine if type A is complete.  */
inline bool
is_complete (tree a)
{
  gcc_assert (a);
  tree type_size = TYPE_SIZE (a);
  const bool _is_complete = NULL_TREE != type_size;
  return _is_complete;
}

/* Asserts type A is complete.  */
inline void
assert_is_complete (tree a)
{
  const bool _is_complete = is_complete (a);
  gcc_assert (_is_complete);
}

/* Determine if type A is incomplete.  */
bool
is_incomplete (tree a)
{
  return !is_complete (a);
}

/* Assert type A has is EXPECTED_CODE.  */
void
assert_is_type (tree a, const enum tree_code expected_code)
{
  gcc_assert (a);
  const enum tree_code observed_code = TREE_CODE (a);
  const bool eq_codes = observed_code == expected_code;
  gcc_assert (eq_codes);
}

/* There are some cases where I need to change a tree to a tree.
 * Some of these are part of the way the API is written.  To avoid
 * warnings, always use this function for casting away const-ness.
 */
tree
tree_to_tree (tree t)
{
  return (tree) t;
}

/* Partition types into reaching record or non reaching record sets.  */
static void
partition_types_into_record_reaching_or_non_record_reaching (tpartitions2_t &p);

/* Fixed point calculating to determine escaping types.  */
static void
fix_escaping_types_in_set (tpartitions2_t &types);

/* Partition types into escaping or non escaping sets.  */
static void
partition_types_into_escaping_nonescaping (tpartitions2_t &p,
					   hash_map<tree, bool> *);

/* TODO:
   This was copy pasted from tree-ssa-structalias.c
   Maybe delete this and make the function visible?  */
HOST_WIDE_INT
bitpos_of_field (const tree fdecl)
{
  if (!tree_fits_shwi_p (DECL_FIELD_OFFSET (fdecl))
      || !tree_fits_shwi_p (DECL_FIELD_BIT_OFFSET (fdecl)))
    return -1;

  return (tree_to_shwi (DECL_FIELD_OFFSET (fdecl)) * BITS_PER_UNIT
	  + tree_to_shwi (DECL_FIELD_BIT_OFFSET (fdecl)));
}

void
compute_postorder (cgraph_node *r, vec<cgraph_node *> &stack,
		   hash_set<cgraph_node *> &visited,
		   hash_set<cgraph_node *> &has_body)
{
  if (!has_body.contains (r))
    return;

  if (visited.contains (r))
    {
      return;
    }
  else
    {
      visited.add (r);
    }

  for (cgraph_edge *e = r->callees; e; e = e->next_callee)
    {
      compute_postorder (e->callee, stack, visited, has_body);
    }
  stack.safe_push (r);
}

/* Iterate all gimple bodies and collect trees
 * which are themselves RECORD_TYPE or which
 * somehow reach a RECORD_TYPE tree (e.g., via a
 * pointer, array, reference, union, field, etc...).
 * Let's call these trees record_reaching_trees.
 */
void
partition_types_into_record_reaching_or_non_record_reaching (
  tpartitions2_t &partitions)
{
  gimple_type_collector collector (partitions, false);
  collector.walk ();
}

/* Iterate over all gimple bodies and find out
 * which types are escaping AND are being casted.
 */
static void
partition_types_into_escaping_nonescaping (tpartitions2_t &partitions,
					   hash_map<tree, bool> *whitelisted2)
{
  partition_types_into_record_reaching_or_non_record_reaching (partitions);
  if (detected_incompatible_syntax)
    return;
  gimple_caster caster (partitions, whitelisted2);
  caster.walk ();

  caster.fix_sets ();
  /* Unify results from different trees representing the same type
     until a fixed point is reached.  */
  fix_escaping_types_in_set (partitions);
  caster.print_reasons ();
}

/* Find equivalent RECORD_TYPE trees to tree r_i.
 * This equivalence will be used for merging the results of field accesses
 * across all equivalent RECORD_TYPE trees.

 * r_i should exists in the points_to_record set
 * and it is a tree for which this method is going to find the rest of
 * equivalent trees found in record_field_map.
 */
static vec<tree> *
find_equivalent_trees (tree r_i, record_field_map4_t &record_field_map,
		       tpartitions2_t casting)
{
  type_incomplete_equality equality;
  vec<tree> *equivalence = new vec<tree> ();
  bool is_rin_record = casting.in_points_to_record (r_i);
  if (!is_rin_record)
    return equivalence;

  for (auto j = record_field_map.begin (), f = record_field_map.end (); j != f;
       ++j)
    {
      tree r_j = (*j).first;
      const bool pointer_equal = r_i == r_j;
      if (pointer_equal)
	continue;

      bool is_p_record = casting.in_points_to_record (r_i)
			 && casting.in_points_to_record (r_j);
      if (!is_p_record)
	continue;

      const bool are_equal = equality.equal (r_i, r_j);
      if (!are_equal)
	continue;

      equivalence->safe_push (r_j);
    }
  return equivalence;
}

/*
 * FIELD is a FIELD_DECL tree, ACCESSED is a a bitflag that marks whether the
 * field is read, written or neither.  FIELD_OFFSET will hold the following map:
 * tree (RECORD_TYPE) -> unsigned (bitpos_of_field for read fields).
 */
static void
add_offset_only_if_read (tree field, unsigned access,
			 field_offsets2_t &field_offset2)
{
  gcc_assert (field);
  assert_is_type (field, FIELD_DECL);
  const bool is_read = access & Read;
  if (!is_read)
    return;

  tree _field = tree_to_tree (field);
  unsigned f_offset = bitpos_of_field (_field);
  field_offset2.add (f_offset);
}

/*
 * FIELD_MAP holds the following map:
 * tree (FIELD_DECL) -> access type
 * FIELD_OFFSET is being built here. It should hold
 * tree (RECORD_TYPE) -> bitpos_of_field for read fields).
 */
static void
keep_only_read_fields_from_field_map (field_access_map2_t &field_map,
				      field_offsets2_t &field_offset2)
{
  for (auto j = field_map.begin (), f = field_map.end (); j != f; ++j)
    {
      add_offset_only_if_read ((*j).first, (*j).second, field_offset2);
    }
}

/*
 * EQUIVALENT holds equivalent trees of RECORD_TYPE
 * Update FIELD_OFFSET as the union of all READ FIELDS for the equivalent trees.
 */
static void
keep_only_read_fields_from_equivalent_field_maps (
  vec<tree> *equivalent, record_field_map4_t &record_field_map,
  field_offsets2_t &field_offset2)
{
  for (auto j = equivalent->begin (), f = equivalent->end (); j != f; j++)
    {
      tree r_j = *j;
      field_access_map2_t *equivalent_field_map = *record_field_map.get (r_j);
      keep_only_read_fields_from_field_map (*equivalent_field_map,
					    field_offset2);
    }
}

/*
 * Whether RECORDS are escaping or can't be modified,
 * delete them from the set of candidate RECORDS to be modified.
 */
static void
erase_if_no_fields_can_be_deleted (
  record_field_offset_map4_t &record_field_offset_map, hash_set<tree> &to_keep,
  hash_set<tree> &to_erase)
{
  for (hash_map<tree, field_offsets2_t *>::iterator i
       = record_field_offset_map.begin (),
       e = record_field_offset_map.end ();
       i != e; ++i)
    {
      tree record = (*i).first;
      const bool keep = to_keep.contains (record);
      if (keep)
	continue;

      to_erase.add (record);
    }

  for (auto i = to_erase.begin (), e = to_erase.end (); i != e; ++i)
    {
      tree record = *i;
      record_field_offset_map.remove (record);
    }
}

/*
 * Mark escaping RECORD_TYPEs as ready to be deleted from the
 * set of candidates to be modified.
 */
static void
mark_escaping_types_to_be_deleted (
  record_field_offset_map4_t &record_field_offset_map, hash_set<tree> &to_erase,
  tpartitions2_t casting)
{
  tset2_t &non_escaping = casting.non_escaping;
  for (hash_map<tree, field_offsets2_t *>::iterator i
       = record_field_offset_map.begin (),
       e = record_field_offset_map.end ();
       i != e; ++i)
    {
      tree record = (*i).first;
      const bool in_set = non_escaping.contains (record);
      if (in_set)
	continue;

      to_erase.add (record);
    }
}

/* Obtain nonescaping unaccessed fields.  */
void
obtain_nonescaping_unaccessed_fields (
  tpartitions2_t casting, record_field_map4_t &record_field_map, int _warning,
  record_field_offset_map4_t &record_field_offset_map)
{
  bool has_fields_that_can_be_deleted = false;
  for (hash_map<tree, field_access_map2_t *>::iterator i
       = record_field_map.begin (),
       e = record_field_map.end ();
       i != e; ++i)
    {
      tree r_i = (*i).first;
      vec<tree> *equivalence
	= find_equivalent_trees (r_i, record_field_map, casting);
      field_offsets2_t *field_offset = new field_offsets2_t;
      field_access_map2_t *original_field_map = (*i).second;
      gcc_assert (original_field_map);
      keep_only_read_fields_from_field_map (*original_field_map, *field_offset);
      keep_only_read_fields_from_equivalent_field_maps (equivalence,
							record_field_map,
							*field_offset);
      /* These map holds the following:
	 RECORD_TYPE -> unsigned (bit_pos_offset which has been read).  */
      record_field_offset_map.put (r_i, field_offset);
      delete equivalence;
    }

  /* So now that we only have the FIELDS which are read,
     we need to compute the complement...  */

  /* Improve: This is tightly coupled, I need to decouple it...  */
  hash_set<tree> to_erase;
  hash_set<tree> to_keep;
  mark_escaping_types_to_be_deleted (record_field_offset_map, to_erase,
				     casting);
  for (auto i = record_field_offset_map.begin (),
	    e = record_field_offset_map.end ();
       i != e; ++i)
    {
      tree record = (*i).first;
      const bool will_be_erased = to_erase.contains (record);
      /* No need to compute which fields can be deleted if type is escaping.  */
      if (will_be_erased)
	continue;

      field_offsets2_t *field_offset = (*i).second;
      for (tree field = TYPE_FIELDS (record); field; field = DECL_CHAIN (field))
	{
	  unsigned f_offset = bitpos_of_field (field);
	  bool in_set2 = field_offset->contains (f_offset);
	  if (in_set2)
	    {
	      field_offset->remove (f_offset);
	      continue;
	    }
	  to_keep.add (record);
	  field_offset->add (f_offset);
	  has_fields_that_can_be_deleted = true;

	  if (_warning == 0)
	    continue;

	  /* Anonymous fields? (Which the record can be!).  */

	  warning_at (DECL_SOURCE_LOCATION (field),  _warning,
		"RECORD TYPE %qE has dead field %qE in LTO",
		TYPE_MAIN_VARIANT (record), field);
	}
    }

  if (!has_fields_that_can_be_deleted)
    {
      record_field_offset_map.empty ();
      return;
    }

  erase_if_no_fields_can_be_deleted (record_field_offset_map, to_keep,
				     to_erase);
}

/* Main interface to TypeWalker. Start recursive walk.  */
void
type_walker::walk (tree t)
{
  gcc_assert (t);
  this->tset2.empty ();
  this->_walk (t);
}

void
type_walker::_walk (tree type)
{
  /* Improve, verify that having a type is an invariant. I think there was a
   * specific example which didn't allow for it.  */
  if (detected_incompatible_syntax)
    return;
  if (!type)
    return;

  gcc_assert (type);

  /* This is an optimization.  */
  const bool _is_memoized = is_memoized (type);
  if (_is_memoized)
    return;

  /* This is for correctness. Some types are represented as a graph
     of trees and therefore we need a way to avoid loops in this graph.  */
  const bool is_recursing = tset2.contains (type);
  if (is_recursing)
    return;

  tset2.add (type);
  const enum tree_code code = TREE_CODE (type);
  switch (code)
    {
    case VOID_TYPE:
      this->walk_VOID_TYPE (type);
      break;
    case INTEGER_TYPE:
      this->walk_INTEGER_TYPE (type);
      break;
    case REAL_TYPE:
      this->walk_REAL_TYPE (type);
      break;
    case FIXED_POINT_TYPE:
      this->walk_FIXED_POINT_TYPE (type);
      break;
    case COMPLEX_TYPE:
      this->walk_COMPLEX_TYPE (type);
      break;
    case ENUMERAL_TYPE:
      this->walk_ENUMERAL_TYPE (type);
      break;
    case BOOLEAN_TYPE:
      this->walk_BOOLEAN_TYPE (type);
      break;
    case OFFSET_TYPE:
      this->walk_OFFSET_TYPE (type);
      break;
    case RECORD_TYPE:
      this->walk_RECORD_TYPE (type);
      break;
    case POINTER_TYPE:
      this->walk_POINTER_TYPE (type);
      break;
    case ARRAY_TYPE:
      this->walk_ARRAY_TYPE (type);
      break;
    case FUNCTION_TYPE:
      this->walk_FUNCTION_TYPE (type);
      break;
    /* Since we are dealing only with C at the moment, we don't care about
     * QUAL_UNION_TYPE nor LANG_TYPEs. So fail early.  */
    case UNION_TYPE:
    case REFERENCE_TYPE:
    case METHOD_TYPE:
    case QUAL_UNION_TYPE:
    case LANG_TYPE:
    default:
      {
	log ("missing %s\n", get_tree_code_name (code));
#ifdef ABORT_IF_NOT_C
	detected_incompatible_syntax = true;
#else
	gcc_unreachable ();
#endif
      }
      break;
    }

    if (POINTER_TYPE_P (type) && TYPE_REF_CAN_ALIAS_ALL (type))
    {
	log ("TYPE_REF_CAN_ALIAS_ALL %s\n", get_tree_code_name (code));
#ifdef ABORT_IF_NOT_C
	detected_incompatible_syntax = true;
#else
	gcc_unreachable ();
#endif
    }

  tset2.remove (type);
}

/* This is used to walk over subtrees. But before walking subtrees, we need to
   call the pre-order callback and after we need to call the post-order
   callback.  */
#define TypeWalkerFuncDef(code) \
  void type_walker::walk_##code (tree t) \
  { \
    assert_is_type (t, code); \
    _walk_##code##_pre (t); \
    _walk_##code (t); \
    _walk_##code##_post (t); \
  }

#define TypeWalkerFuncDefInternal(code) \
  void type_walker::_walk_##code (__attribute__ ((unused)) tree t) {}

TypeWalkerFuncDef (VOID_TYPE) TypeWalkerFuncDefInternal (VOID_TYPE)
TypeWalkerFuncDef (INTEGER_TYPE) TypeWalkerFuncDefInternal (INTEGER_TYPE)
TypeWalkerFuncDef (REAL_TYPE) TypeWalkerFuncDefInternal (REAL_TYPE)
TypeWalkerFuncDef (BOOLEAN_TYPE) TypeWalkerFuncDefInternal (BOOLEAN_TYPE)
TypeWalkerFuncDef (OFFSET_TYPE) TypeWalkerFuncDefInternal (OFFSET_TYPE)
TypeWalkerFuncDef (FIXED_POINT_TYPE)
TypeWalkerFuncDefInternal (FIXED_POINT_TYPE)
TypeWalkerFuncDef (COMPLEX_TYPE)
TypeWalkerFuncDefInternal (COMPLEX_TYPE)
TypeWalkerFuncDef (ENUMERAL_TYPE)
TypeWalkerFuncDefInternal (ENUMERAL_TYPE)

/* walk wrapper is used for unwrapping REFERENCE_TYPE, POINTER_TYPE, ARRAY_TYPE.
 */
void
type_walker::_walk_wrapper (tree t)
{
  tree inner_type = TREE_TYPE (t);
  /* I think I encountered this code:  */
  if (!inner_type)
    return;

  gcc_assert (inner_type);
  _walk (inner_type);
}

#define TypeWalkerFuncDefWrapper(code) \
  void type_walker::_walk_##code (tree t) { _walk_wrapper (t); }

TypeWalkerFuncDef (POINTER_TYPE) TypeWalkerFuncDefWrapper (POINTER_TYPE)
TypeWalkerFuncDefWrapper (REFERENCE_TYPE) TypeWalkerFuncDef (REFERENCE_TYPE)
TypeWalkerFuncDef (ARRAY_TYPE) TypeWalkerFuncDefWrapper (ARRAY_TYPE)
TypeWalkerFuncDef (RECORD_TYPE)

void
type_walker::_walk_RECORD_TYPE (tree t)
{
  _walk_record_or_union (t);
}

TypeWalkerFuncDef (UNION_TYPE)

void
type_walker::_walk_UNION_TYPE (tree t)
{
  _walk_record_or_union (t);
}

void
type_walker::_walk_record_or_union (tree t)
{
  for (tree field = TYPE_FIELDS (t); field; field = DECL_CHAIN (field))
    {
      gcc_assert (field);
      walk_field (field);
    }
}

void
type_walker::walk_field (tree t)
{
  _walk_field_pre (t);
  _walk_field (t);
  _walk_field_post (t);
}

void
type_walker::_walk_field (tree t)
{
  tree inner_type = TREE_TYPE (t);
  gcc_assert (inner_type);
  _walk (inner_type);
}

TypeWalkerFuncDef (FUNCTION_TYPE)

  void type_walker::_walk_FUNCTION_TYPE (tree t)
{
  _walk_function_or_method (t);
}

TypeWalkerFuncDef (METHOD_TYPE)

  void type_walker::_walk_METHOD_TYPE (tree t)
{
  _walk_function_or_method (t);
}

void
type_walker::_walk_function_or_method (tree t)
{
  tree ret_type = TREE_TYPE (t);
  walk_return (ret_type);
  walk_args (t);
}

void
type_walker::walk_return (tree t)
{
  _walk_return_pre (t);
  _walk_return (t);
  _walk_return_post (t);
}

void
type_walker::_walk_return (tree t)
{
  _walk (t);
}

void
type_walker::walk_args (tree t)
{
  _walk_args_pre (t);
  _walk_args (t);
  _walk_args_post (t);
}

void
type_walker::_walk_args (tree t)
{
  for (tree arg_node = TYPE_ARG_TYPES (t); NULL_TREE != arg_node;
       arg_node = TREE_CHAIN (arg_node))
    {
      tree arg_node_type = TREE_VALUE (arg_node);
      gcc_assert (arg_node_type);
      walk_arg (arg_node_type);
    }
}

void
type_walker::walk_arg (tree t)
{
  _walk_arg_pre (t);
  _walk_arg (t);
  _walk_arg_post (t);
}

void
type_walker::_walk_arg (tree t)
{
  _walk (t);
}

/* Main interface for the ExprWalker... */
void
expr_walker::walk (tree e)
{
  if (detected_incompatible_syntax)
    return;
  _walk_pre (e);
  _walk (e);
  _walk_post (e);
}

void
expr_walker::_walk (tree e)
{
  gcc_assert (e);
  const enum tree_code code = TREE_CODE (e);
  switch (code)
    {
    case INTEGER_CST:
      walk_INTEGER_CST (e);
      break;
    case REAL_CST:
      walk_REAL_CST (e);
      break;
    case STRING_CST:
      walk_STRING_CST (e);
      break;
    case BIT_FIELD_REF:
      walk_BIT_FIELD_REF (e);
      break;
    case ARRAY_REF:
      walk_ARRAY_REF (e);
      break;
    case MEM_REF:
      walk_MEM_REF (e);
      break;
    case COMPONENT_REF:
      walk_COMPONENT_REF (e);
      break;
    case SSA_NAME:
      walk_SSA_NAME (e);
      break;
    case ADDR_EXPR:
      walk_ADDR_EXPR (e);
      break;
    case VIEW_CONVERT_EXPR:
      walk_VIEW_CONVERT_EXPR (e);
      break;
    case IMAGPART_EXPR:
      walk_IMAGPART_EXPR (e);
      break;
    case VAR_DECL:
      walk_VAR_DECL (e);
      break;
    case FIELD_DECL:
      walk_FIELD_DECL (e);
      break;
    case RESULT_DECL:
      walk_RESULT_DECL (e);
      break;
    case PARM_DECL:
      walk_PARM_DECL (e);
      break;
    case FUNCTION_DECL:
      walk_FUNCTION_DECL (e);
      break;
    case CONSTRUCTOR:
      walk_CONSTRUCTOR (e);
      break;
    case LE_EXPR:
      walk_LE_EXPR (e);
      break;
    case LT_EXPR:
      walk_LT_EXPR (e);
      break;
    case EQ_EXPR:
      walk_EQ_EXPR (e);
      break;
    case GT_EXPR:
      walk_GT_EXPR (e);
      break;
    case GE_EXPR:
      walk_GE_EXPR (e);
      break;
    case NE_EXPR:
      walk_NE_EXPR (e);
      break;
    default:
      {
	log ("missing %s\n", get_tree_code_name (code));
#ifdef ABORT_IF_NOT_C
	detected_incompatible_syntax = true;
#else
	gcc_unreachable ();
#endif
      }
      break;
    }
}

/* call pre-order callback for everything
 * call pre-order callback for specific code
 * walk subtrees
 * call post-order callback for specific code
 * call post-order callback for everything.
 */
#define ExprWalkerFuncDef(code) \
  void expr_walker::walk_##code (tree e) \
  { \
    assert_is_type (e, code); \
    _walk_pre (e); \
    _walk_##code##_pre (e); \
    _walk_##code (e); \
    _walk_##code##_post (e); \
    _walk_post (e); \
  }

ExprWalkerFuncDef (CONSTRUCTOR) ExprWalkerFuncDef (INTEGER_CST)
ExprWalkerFuncDef (REAL_CST) ExprWalkerFuncDef (STRING_CST)
ExprWalkerFuncDef (BIT_FIELD_REF) ExprWalkerFuncDef (ARRAY_REF)
ExprWalkerFuncDef (MEM_REF) ExprWalkerFuncDef (COMPONENT_REF)
ExprWalkerFuncDef (SSA_NAME) ExprWalkerFuncDef (ADDR_EXPR)
ExprWalkerFuncDef (VIEW_CONVERT_EXPR)
ExprWalkerFuncDef (IMAGPART_EXPR) ExprWalkerFuncDef (FIELD_DECL)
ExprWalkerFuncDef (VAR_DECL) ExprWalkerFuncDef (RESULT_DECL)
ExprWalkerFuncDef (PARM_DECL) ExprWalkerFuncDef (FUNCTION_DECL)
ExprWalkerFuncDef (LE_EXPR) ExprWalkerFuncDef (LT_EXPR)
ExprWalkerFuncDef (EQ_EXPR) ExprWalkerFuncDef (GT_EXPR)
ExprWalkerFuncDef (GE_EXPR) ExprWalkerFuncDef (NE_EXPR)

void
expr_walker::_walk_leaf (tree e, const enum tree_code c)
{
  assert_is_type (e, c);
}

void
expr_walker::_walk_op_n (tree e, unsigned n)
{
  gcc_assert (e);
  tree op_n = TREE_OPERAND (e, n);
  gcc_assert (op_n);
  walk (op_n);
}

void
expr_walker::_walk_op_0 (tree e, const enum tree_code c)
{
  assert_is_type (e, c);
  _walk_op_n (e, 0);
}

void
expr_walker::_walk_op_1 (tree e, const enum tree_code c)
{
  assert_is_type (e, c);
  _walk_op_n (e, 0);
  _walk_op_n (e, 1);
}

void
expr_walker::_walk_CONSTRUCTOR (__attribute__ ((unused)) tree e)
{
  /* Future-work: If we want to support rewriting CONSTRUCTORs
     we will have to walk them.  */
}

void
expr_walker::_walk_LE_EXPR (tree e)
{
  _walk_op_1 (e, LE_EXPR);
}

void
expr_walker::_walk_LT_EXPR (tree e)
{
  _walk_op_1 (e, LT_EXPR);
}

void
expr_walker::_walk_EQ_EXPR (tree e)
{
  _walk_op_1 (e, EQ_EXPR);
}

void
expr_walker::_walk_GT_EXPR (tree e)
{
  _walk_op_1 (e, GT_EXPR);
}

void
expr_walker::_walk_GE_EXPR (tree e)
{
  _walk_op_1 (e, GE_EXPR);
}

void
expr_walker::_walk_NE_EXPR (tree e)
{
  _walk_op_1 (e, NE_EXPR);
}

void
expr_walker::_walk_INTEGER_CST (tree e)
{
  _walk_leaf (e, INTEGER_CST);
}

void
expr_walker::_walk_REAL_CST (tree e)
{
  _walk_leaf (e, REAL_CST);
}

void
expr_walker::_walk_STRING_CST (tree e)
{
  _walk_leaf (e, STRING_CST);
}

void
expr_walker::_walk_BIT_FIELD_REF (__attribute__ ((unused)) tree e)
{
  /* TODO:
     We currently don't support bit_field_ref.  */
}

void
expr_walker::_walk_ARRAY_REF (tree e)
{
  _walk_op_1 (e, ARRAY_REF);
}

void
expr_walker::_walk_MEM_REF (tree e)
{
  _walk_op_1 (e, MEM_REF);
}

void
expr_walker::_walk_COMPONENT_REF (tree e)
{
  _walk_op_1 (e, COMPONENT_REF);
}

void
expr_walker::_walk_SSA_NAME (tree e)
{
  _walk_leaf (e, SSA_NAME);
}

void
expr_walker::_walk_ADDR_EXPR (tree e)
{
  _walk_op_0 (e, ADDR_EXPR);
}

void
expr_walker::_walk_VIEW_CONVERT_EXPR (__attribute__ ((unused)) tree e)
{
  /* TODO: I don't think we need to do anything here.  */
}

void
expr_walker::_walk_IMAGPART_EXPR (__attribute__ ((unused)) tree e)
{
  /* TODO: I don't think we need to do anything here.  */
}

void
expr_walker::_walk_FIELD_DECL (tree e)
{
  _walk_leaf (e, FIELD_DECL);
}

void
expr_walker::_walk_VAR_DECL (tree e)
{
  _walk_leaf (e, VAR_DECL);
}

void
expr_walker::_walk_RESULT_DECL (tree e)
{
  _walk_leaf (e, RESULT_DECL);
}

void
expr_walker::_walk_PARM_DECL (tree e)
{
  _walk_leaf (e, PARM_DECL);
}

void
expr_walker::_walk_FUNCTION_DECL (tree e)
{
  _walk_leaf (e, FUNCTION_DECL);
  for (tree parm = DECL_ARGUMENTS (e); parm; parm = DECL_CHAIN (parm))
    {
      walk (parm);
    }
}

/* Main interface for GimpleWalker:
   iterate over global variables and then for all functions with gimple body. */
void
gimple_walker::walk ()
{
  _walk_globals ();
  hash_set<tree> fndecls2;
  cgraph_node *node = NULL;
  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    {
      if (detected_incompatible_syntax)
	return;
      tree decl = node->decl;
      const bool already_in_set = fndecls2.contains (decl);
      /* I think it is possible for different nodes to point to the same
	 declaration.  */
      if (already_in_set)
	continue;

      if (dump_file)
	dump_function_to_file (node->decl, dump_file, TDF_NONE);

      _walk_cnode (node);
      fndecls2.add (decl);
    }
}

/* For each global variable.  */
void
gimple_walker::_walk_globals ()
{
  varpool_node *vnode = NULL;
  FOR_EACH_VARIABLE (vnode)
    _walk_global (vnode);
}

/* Walk over global variable VNODE.  */
void
gimple_walker::_walk_global (varpool_node *vnode)
{
  struct ipa_ref *ref = NULL;
  for (unsigned i = 0; vnode->iterate_referring (i, ref); i++)
    {
      tree var_decl = vnode->decl;
      walk_tree2 (var_decl);
      tree initial = DECL_INITIAL (var_decl);
      const bool constructor
	= initial ? TREE_CODE (initial) == CONSTRUCTOR : false;
      const bool error_mark
	= initial ? TREE_CODE (initial) == ERROR_MARK : false;
      if (!initial || constructor || error_mark)
	{
	  continue;
	}
      walk_tree2 (initial);
    }
}

/* Walk over SSA_NAMEs in CNODE.  */
void
gimple_walker::_walk_ssa_names (cgraph_node *cnode)
{
  cfun_context ctx (cnode);
  size_t i = 0;
  tree ssa_name = NULL;
  FOR_EACH_SSA_NAME (i, ssa_name, cfun)
    {
      gcc_assert (ssa_name);
      walk_tree2 (ssa_name);
      tree ssa_name_var = SSA_NAME_VAR (ssa_name);
      if (!ssa_name_var)
	continue;
      walk_tree2 (ssa_name_var);
    }
}

/* Walk over declaration, locals, ssa_names, and basic blocks in CNODE.  */
void
gimple_walker::_walk_cnode (cgraph_node *cnode)
{
  currently_walking = cnode;
  _walk_decl (cnode);
  _walk_locals (cnode);
  _walk_ssa_names (cnode);
  _walk_bb (cnode);
}

/* Walk over each local declaration in CNODE.  */
void
gimple_walker::_walk_locals (cgraph_node *cnode)
{
  cfun_context ctx (cnode);
  int i = 0;
  tree var_decl = NULL;
  FOR_EACH_LOCAL_DECL (cfun, i, var_decl)
    walk_tree2 (var_decl);
}

/* Walk over all basic blocks in CNODE.  */
void
gimple_walker::_walk_bb (cgraph_node *cnode)
{
  cfun_context ctx (cnode);
  basic_block bb = NULL;
  _rebuild = false;
  FOR_EACH_BB_FN (bb, cfun)
    _walk (bb);
  if (_rebuild)
    cgraph_edge::rebuild_edges ();
}

/* Walk over CNODE->decl.  */
void
gimple_walker::_walk_decl (cgraph_node *cnode)
{
  tree decl = cnode->decl;
  gcc_assert (decl);
  walk_tree2 (decl);
}

/* Walk over each gimple statement in BB.  */
void
gimple_walker::_walk (basic_block bb)
{
  gimple_stmt_iterator gsi = gsi_start_bb (bb);
  while (!gsi_end_p (gsi))
    {
      this->_deleted = false;
      gimple *stmt = gsi_stmt (gsi);
      walk_gimple (stmt);
      /* If it is not deleted just continue.  */
      if (!this->_deleted)
	{
	  gsi_next (&gsi);
	  continue;
	}

      /* Otherwise remove statement.  */
      unlink_stmt_vdef (stmt);
      gsi_remove (&gsi, true);
      this->_rebuild = true;
    }

  for (gimple_stmt_iterator gsi = gsi_start_phis (bb); !gsi_end_p (gsi);
       gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      walk_gimple (stmt);
    }
}

/* call preorder callback
   walk subtrees
   call postorder callback.  */
void
gimple_walker::walk_gimple (gimple *stmt)
{
  _walk_pre_gimple (stmt);
  _walk_gimple (stmt);
  _walk_post_gimple (stmt);
}

/* Switch for different gimple instruction types.  */
void
gimple_walker::_walk_gimple (gimple *stmt)
{
  /* Do not use _walk_pre (s)
     Subtle but important distinction,
     we want to differentiate calling here stamtent from s.  */
  if (gassign *_gassign = dyn_cast<gassign *> (stmt))
    {
      _walk_pre_gimple (stmt);
      walk_gassign (_gassign);
      _walk_post_gimple (stmt);
      return;
    }

  if (greturn *_greturn = dyn_cast<greturn *> (stmt))
    {
      _walk_pre_gimple (stmt);
      walk_greturn (_greturn);
      _walk_post_gimple (stmt);
      return;
    }

  if (gcond *_gcond = dyn_cast<gcond *> (stmt))
    {
      _walk_pre_gimple (stmt);
      walk_gcond (_gcond);
      _walk_post_gimple (stmt);
      return;
    }

  if (gcall *_gcall = dyn_cast<gcall *> (stmt))
    {
      _walk_pre_gimple (stmt);
      walk_gcall (_gcall);
      _walk_post_gimple (stmt);
      return;
    }

  if (glabel *_glabel = dyn_cast<glabel *> (stmt))
    {
      _walk_pre_gimple (stmt);
      walk_glabel (_glabel);
      _walk_post_gimple (stmt);
      return;
    }

  if (gswitch *_gswitch = dyn_cast<gswitch *> (stmt))
    {
      _walk_pre_gimple (stmt);
      walk_gswitch (_gswitch);
      _walk_post_gimple (stmt);
      return;
    }

  if (gphi *_gphi = dyn_cast<gphi *> (stmt))
    {
      _walk_pre_gimple (stmt);
      walk_gphi (_gphi);
      _walk_post_gimple (stmt);
      return;
    }

  const enum gimple_code code = gimple_code (stmt);
  switch (code)
    {
    case GIMPLE_DEBUG:
    case GIMPLE_PREDICT:
    case GIMPLE_NOP:
      /* I think it is safe to skip these
	 but it would also be nice to walk their sub-trees.  */
      return;
      break;
    default:
      break;
    }

  /* Break if something is unexpected.  */
  const char *name = gimple_code_name[code];
  log ("gimple code name %s\n", name);
#ifdef ABORT_IF_NOT_C
  detected_incompatible_syntax = true;
#else
  gcc_unreachable ();
#endif
}

void
gimple_walker::walk_tree2 (tree t)
{
  _walk_pre_tree (t);
  _walk_tree (t);
  _walk_post_tree (t);
}

void
gimple_walker::_walk_tree (__attribute__ ((unused)) tree t)
{}

void
gimple_walker::walk_gassign (gassign *g)
{
  _walk_pre_gassign (g);
  _walk_gassign (g);
  _walk_post_gassign (g);
}

void
gimple_walker::_walk_gassign (__attribute__ ((unused)) gassign *g)
{}

void
gimple_walker::walk_greturn (greturn *g)
{
  _walk_pre_greturn (g);
  _walk_greturn (g);
  _walk_post_greturn (g);
}

void
gimple_walker::_walk_greturn (__attribute__ ((unused)) greturn *g)
{}

void
gimple_walker::walk_gcond (gcond *g)
{
  _walk_pre_gcond (g);
  _walk_gcond (g);
  _walk_post_gcond (g);
}

void
gimple_walker::_walk_gcond (__attribute__ ((unused)) gcond *g)
{}

void
gimple_walker::walk_gcall (gcall *g)
{
  _walk_pre_gcall (g);
  _walk_gcall (g);
  _walk_post_gcall (g);
}

void
gimple_walker::_walk_gcall (__attribute__ ((unused)) gcall *g)
{}

void
gimple_walker::walk_glabel (glabel *g)
{
  _walk_pre_glabel (g);
  _walk_glabel (g);
  _walk_post_glabel (g);
}

void
gimple_walker::_walk_glabel (__attribute__ ((unused)) glabel *g)
{}

void
gimple_walker::walk_gswitch (gswitch *g)
{
  _walk_pre_gswitch (g);
  _walk_gswitch (g);
  _walk_post_gswitch (g);
}

void
gimple_walker::_walk_gswitch (__attribute__ ((unused)) gswitch *g)
{}

void
gimple_walker::walk_gphi (gphi *g)
{
  _walk_pre_gphi (g);
  _walk_gphi (g);
  _walk_post_gphi (g);
}

void
gimple_walker::_walk_gphi (__attribute__ ((unused)) gphi *g)
{}

void
type_collector::collect (tree t)
{
  const bool in_set = ptrset2.in_universe (t);
  /* Early memoization...  */

  if (in_set)
    return;

  /* TODO: Can we move this to the beginning
     of the function.  */
  gcc_assert (t);

  /* This is the map that holds the types we will encounter in this walk.
     It should be empty at the beginning. It maps from tree -> bool.
     The boolean will be updated to show whether a record is reachable from
     the type.  */
  gcc_assert (ptr2.is_empty ());
  walk (t);
}

/* Make sure partitions are mutually exclusive.  */
void
type_collector::_sanity_check ()
{
  for (auto i = ptrset2.points_to_record.begin (),
	    e = ptrset2.points_to_record.end ();
       i != e; ++i)
    {
      for (auto j = ptrset2.complement.begin (), f = ptrset2.complement.end ();
	   j != f; ++j)
	{
	  tree type_ptr = *i;
	  gcc_assert (type_ptr);
	  tree type_com = *j;
	  gcc_assert (type_com);
	  const bool valid_sets = type_ptr != type_com;
	  if (valid_sets)
	    continue;

	  /* Normally, we want a stronger type comparison
	     that is not just the pointer address
	     but this is the first sanity check and then we will need to
	     determine the stronger type comparison.  But first we will need to
	     fix the types...  */
	  gcc_unreachable ();
	}
    }
}

/* Determine if T is already memoized in the TypeCollector.  */
bool
type_collector::is_memoized (tree t)
{
  /* If we haven't seen it then no.  */
  const bool in_set = ptrset2.in_universe (t);
  if (!in_set)
    return false;

  /* If the memoized type points to a record
     we must update all types that can refer
     to memoized type.  */
  const bool points_to_record = ptrset2.in_points_to_record (t);
  for (auto i = ptr2.begin (), e = ptr2.end (); i != e; ++i)
    {
      (*i).second |= points_to_record;
    }
  return true;
}

void
type_collector::_walk_VOID_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_VOID_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_INTEGER_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_INTEGER_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_REAL_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_REAL_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_FIXED_POINT_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_FIXED_POINT_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_COMPLEX_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_COMPLEX_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_ENUMERAL_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_ENUMERAL_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_BOOLEAN_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_BOOLEAN_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_collect_simple (tree t)
{
  /* Insert into persistent set.  */
  ptrset2.insert (t, *ptr2.get (t));
  /* Erase from current working set.  */
  ptr2.remove (t);
}

void
type_collector::_walk_ARRAY_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_ARRAY_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_POINTER_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_POINTER_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_REFERENCE_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_REFERENCE_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_RECORD_TYPE_post (tree t)
{
  /* All in ptr point to record.  */
  for (auto i = ptr2.begin (), e = ptr2.end (); i != e; ++i)
    {
      (*i).second = true;
    }
  _collect_simple (t);
}

void
type_collector::_walk_RECORD_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_UNION_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_UNION_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_FUNCTION_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_FUNCTION_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

void
type_collector::_walk_METHOD_TYPE_post (tree t)
{
  _collect_simple (t);
}

void
type_collector::_walk_METHOD_TYPE_pre (tree t)
{
  ptr2.put (t, false);
}

inline void
expr_collector::_walk_pre (tree e)
{
  if (!e)
    return;
  tree t = TREE_TYPE (e);
  gcc_assert (t);
  _type_collector.collect (t);

  if (RECORD_TYPE != TREE_CODE (t))
    return;

  if (!_white_listing)
    return;

  if (ptrset3->is_empty ())
    {
      gcc_assert (TYPE_P (t));
      gcc_assert (TYPE_P (TYPE_MAIN_VARIANT (t)));
      ptrset3->add (TYPE_MAIN_VARIANT (t));
      return;
    }

  bool same = true;
  for (hash_set<tree>::iterator i = ptrset3->begin (), e = ptrset3->end ();
       i != e; ++i)
    {
      tree r = *i;
      type_incomplete_equality structuralEquality;
      gcc_assert (TYPE_P (r));
      gcc_assert (TYPE_MAIN_VARIANT (r));
      same &= structuralEquality.equal (TYPE_MAIN_VARIANT (r),
					TYPE_MAIN_VARIANT (t));
      if (!same)
	break;
    }

  if (!same)
    {
      ptrset3->add (TYPE_MAIN_VARIANT (t));
    }
}

/* For global variables T, this method will collect and partition trees
   corresponding to types into std::sets.  Concretely speaking, this class
   partitions trees into two sets:
   (1) reach a RECORD_TYPE
   (2) does not reach a RECORD_TYPE. */
void
gimple_type_collector::_walk_pre_tree (tree t)
{
  if (!t)
    return;
  _expr_collector.walk (t);
}

/* For assignment statements S, this method will collect and partition trees
   corresponding to types into std::sets.  Concretely speaking, this class
   partitions trees into two sets:
   (1) reach a RECORD_TYPE
   (2) does not reach a RECORD_TYPE
   The types reachable from the lhs and rhs are placed in these sets. */
void
gimple_type_collector::_walk_pre_gassign (gassign *s)
{
  tree lhs = gimple_assign_lhs (s);
  _expr_collector.walk (lhs);

  const enum gimple_rhs_class gclass = gimple_assign_rhs_class (s);
  switch (gclass)
    {
    case GIMPLE_TERNARY_RHS:
      {
	tree rhs = gimple_assign_rhs3 (s);
	_expr_collector.walk (rhs);
      }
    /* fall-through.  */
    case GIMPLE_BINARY_RHS:
      {
	tree rhs = gimple_assign_rhs2 (s);
	_expr_collector.walk (rhs);
      }
    /* fall-through.  */
    case GIMPLE_UNARY_RHS:
    case GIMPLE_SINGLE_RHS:
      {
	tree rhs = gimple_assign_rhs1 (s);
	_expr_collector.walk (rhs);
      }
      break;
    default:
      gcc_unreachable ();
      break;
    }
}

void
gimple_type_collector::_walk_pre_greturn (greturn *s)
{
  tree retval = gimple_return_retval (s);
  if (!retval)
    return;

  _expr_collector.walk (retval);
}

void
gimple_type_collector::_walk_pre_gcall (gcall *s)
{
  /* Walk over the arguments.  */
  unsigned n = gimple_call_num_args (s);
  for (unsigned i = 0; i < n; i++)
    {
      tree a = gimple_call_arg (s, i);
      _expr_collector.walk (a);
    }

  /* Walk over the return type if it exists.  */
  tree lhs = gimple_call_lhs (s);
  if (!lhs)
    return;

  _expr_collector.walk (lhs);
}

void
gimple_type_collector::_walk_pre_gdebug (gdebug *s)
{
  if (!gimple_debug_bind_p (s))
    return;
  tree var = gimple_debug_bind_get_var (s);
  if (var)
    {
      gcc_assert (TREE_TYPE (var));
      _expr_collector.walk (var);
    }
}

/* Print working set.  */
void
gimple_type_collector::print_collected ()
{
  tpartitions2_t sets = get_record_reaching_trees ();
  /* TODO: I think previously we were printing info here for tests.  */
}

/* Walk over LHS and RHS of conditions.  */
void
gimple_type_collector::_walk_pre_gcond (gcond *s)
{
  tree lhs = gimple_cond_lhs (s);
  _expr_collector.walk (lhs);
  tree rhs = gimple_cond_rhs (s);
  _expr_collector.walk (rhs);
}

bool
type_escaper::is_memoized (tree t)
{
  /* Can only memoize here when we don't handle unions.
     Because information is propagated up and down
     the type when there are unions.  */
  if (calc2.get (t) && calc2.get (t)->is_escaping ())
    return true;
  if (calc2.get (t) && !calc2.get (t)->is_escaping ()
      && !_reason.is_escaping ())
    return true;

  return false;
}

void
type_escaper::fix_sets ()
{
  place_escaping_types_in_set ();
}

/* From a map of TREE -> BOOL, the key represents a tree type
 * and the value represents whether the tree escapes.
 * Partition this map into sets.
 */
void
type_escaper::place_escaping_types_in_set ()
{
  for (auto i = calc2.begin (), e = calc2.end (); i != e; ++i)
    {
      tree type = (*i).first;

      /* We should only track interesting types
	 Types which are not in points_to_record are the ones
	 that are pointed to by records.
	 I think it is possible to prune them ahead of time...  */
      if (!_ptrset2.in_points_to_record (type))
	continue;

      const Reason reason = (*i).second;
      reason.is_escaping () ? _ptrset2.escaping.add (type)
			    : _ptrset2.non_escaping.add (type);
    }
}

void
type_escaper::update (tree t, Reason r)
{
  gcc_assert (t);
  _reason = r;
  walk (t);
}

void
type_escaper::_update_single (tree t, Reason r)
{
  gcc_assert (t);
  _reason = r;
  _update (t);
}

void
type_escaper::_update (tree t)
{
  gcc_assert (t);
  const bool already_in_typemap = calc2.get (t);
  const bool is_volatile = TYPE_VOLATILE (t);
  Reason _is_volatile;
  _is_volatile.type_is_volatile = is_volatile;
  Reason _inner = _reason | _is_volatile;
  /* Always OR.  */
  Reason temp;
  temp = already_in_typemap ? *calc2.get (t) | _inner : _inner;
  calc2.put (t, temp);
}

void
type_escaper::_walk_ARRAY_TYPE_pre (tree t)
{
  _update (t);
}

void
type_escaper::_walk_ARRAY_TYPE_post (tree t)
{
  _update (t);
}

void
type_escaper::_walk_POINTER_TYPE_pre (tree t)
{
  _update (t);
}

void
type_escaper::_walk_POINTER_TYPE_post (tree t)
{
  _update (t);
}

void
type_escaper::_walk_REFERENCE_TYPE_pre (tree t)
{
  _update (t);
}

void
type_escaper::_walk_RECORD_TYPE_pre (tree t)
{
  /* We are entering a record.  */
  _inside_record++;
  _update (t);
}

void
type_escaper::_walk_RECORD_TYPE_post (tree t)
{
  _update (t); /* This is in case there was a union.  */

  _inside_record--; /* We are exiting a record.  */
}

/* Mark as escaping because of union
 * and propagate up and down.
 */
void
type_escaper::_walk_UNION_TYPE_pre (tree t)
{
  _inside_union++;
  bool is_escaping = _inside_union > 0;
  _reason.type_is_in_union |= is_escaping;
  _update (t);
}

/* Mark bit fields as escaping and propagate up
 * and down.
 */
void
type_escaper::_walk_field_pre (tree t)
{
  _reason.type_is_in_union |= DECL_BIT_FIELD (t);
}

void
type_escaper::_walk_UNION_TYPE_post (tree t)
{
  _inside_union--;
  _update (t);
}

/* Mark as escaping because RECORD has a function pointer
 * propagate up and down.
 */
void
type_escaper::_walk_FUNCTION_TYPE_pre (__attribute__ ((unused)) tree t)
{
  _reason.type_is_in_union |= _inside_record > 0;
}

/* Mark as escaping because RECORD has a function pointer
 * propagate up and down.
 */
void
type_escaper::_walk_METHOD_TYPE_pre (__attribute__ ((unused)) tree t)
{
  _reason.type_is_in_union |= _inside_record > 0;
}

/* Print escaping reasons.  */
void
type_escaper::print_reasons ()
{
  for (auto i = calc2.begin (), e = calc2.end (); i != e; ++i)
    {
      tree t = (*i).first;
      type_stringifier stringifier;
      std::string name = stringifier.stringify (t);
      Reason r = (*i).second;
      log ("%s reason: ", name.c_str ());
      r.print ();
    }
}

void
expr_escaper::fix_sets ()
{
  _type_escaper.fix_sets ();
}

void
expr_escaper::print_reasons ()
{
  _type_escaper.print_reasons ();
}

/* Propagate reason to subexpressions.  */
void
expr_escaper::update (tree t, Reason r)
{
  gcc_assert (t);
  _r = r;
  walk (t);
}

/* Propagate reason to type of subexpressions.  */
void
expr_escaper::_walk_pre (tree e)
{
  _stack2.safe_push (e);
  tree t = TREE_TYPE (e);

  gcc_assert (t);
  _type_escaper.update (t, _r);
}

void
expr_escaper::_walk_post (__attribute__ ((unused)) tree e)
{
  _stack2.pop ();
}

/* Capture casting on LHS.  */
void
expr_escaper::_walk_SSA_NAME_pre (tree e)
{
  tree ssa_type = TREE_TYPE (e);

  if (_stack2.length () < 4)
    return;

  tree this_expr = _stack2.last ();
  _stack2.pop ();
  tree twice = _stack2.last ();
  _stack2.pop ();
  tree prev_expr = _stack2.last ();
  _stack2.safe_push (twice);
  _stack2.safe_push (this_expr);
  if (TREE_CODE (prev_expr) != MEM_REF)
    return;

  tree op1 = TREE_OPERAND (prev_expr, 1);
  gcc_assert (TREE_CODE (op1) == INTEGER_CST);
  tree mref_type = TREE_TYPE (op1);

  Reason old_reason = _r;
  type_incomplete_equality structuralEquality;
  if (TREE_CODE (TREE_TYPE (mref_type)) == INTEGER_TYPE)
    return;

  bool in_map = curr_node && !_whitelisted2->is_empty ()
		&& _whitelisted2->get (curr_node->decl);
  bool whitelisted = in_map && *_whitelisted2->get (curr_node->decl);
  if (whitelisted)
    return;

  bool is_casted = !structuralEquality.equal (mref_type, ssa_type);
  is_casted = is_casted ? _follow_def_to_find_if_really_cast (e) : is_casted;
  _r.type_is_casted = is_casted;
  _type_escaper.update (mref_type, _r);
  _type_escaper.update (ssa_type, _r);
  _r = old_reason;
}

/* Mark constructors as escaping.  */
void
expr_escaper::_walk_CONSTRUCTOR_pre (tree e)
{
  if (TREE_CLOBBER_P (e))
    return;

  /* TODO: Instead of overloading global_is_visible field
     with has a constructor, make a field that denotes that
     a this has a constructor.
     Or better yet... modify the constructors!  */
  _r.global_is_visible = true;
  tree t = TREE_TYPE (e);
  _type_escaper.update (t, _r);
}

void
gimple_escaper::fix_sets ()
{
  _expr_escaper.curr_node = NULL;
  return _expr_escaper.fix_sets ();
}

void
gimple_escaper::print_reasons ()
{
  _expr_escaper.curr_node = NULL;
  _expr_escaper.print_reasons ();
}

/* Initialize undefined set of functions.  */
void
gimple_escaper::_init ()
{
  cgraph_node *cnode = NULL;
  FOR_EACH_FUNCTION (cnode)
    {
      if (!gimple_escaper::filter_known_function (cnode))
        undefined2.add (cnode->decl);
    }

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (cnode)
    undefined2.remove (cnode->decl);
}

/* Mark cnode graphs escaping if they are externally visible.  */
bool
gimple_escaper::is_function_escaping (cgraph_node *cnode)
{
  const bool filter = gimple_escaper::filter_known_function (cnode);
  if (filter)
    return false;

  return cnode->externally_visible;
}

/* Mark fndecl as escaping is they are externally visible or
 * there is no fndecl.  */
bool
gimple_escaper::is_function_escaping (tree fndecl)
{
  if (!fndecl)
    return true;

  if (!TREE_PUBLIC (fndecl) && !DECL_EXTERNAL (fndecl))
    return false;

  return true;
}

/* Mark variable as escaping if it is externally visible.  */
bool
gimple_escaper::is_variable_escaping (varpool_node *vnode)
{
  gcc_assert (vnode);
  const bool retval = vnode->externally_visible;
  return retval;
}

/* Walk global variable VNODE.  */
void
gimple_escaper::_walk_global (varpool_node *vnode)
{
  gcc_assert (vnode);
  tree var_decl = vnode->decl;
  Reason reason;
  const bool is_escaping = is_variable_escaping (vnode);
  reason.global_is_visible = is_escaping;

  /* TODO: Instead of overloading the semantic meaning of global is visible
     make different fields for CONSTRUCTOR and for CONSTRUCTOR is not in linking
     unit
     TODO: Once we are able to rewrite the CONSTRUCTOR we can get rid of marking
     types with bracket constructors as illegal.  */
  tree initial = DECL_INITIAL (var_decl);
  const bool constructor = initial ? TREE_CODE (initial) == CONSTRUCTOR : false;
  const bool error_mark = initial ? TREE_CODE (initial) == ERROR_MARK : false;
  reason.global_is_visible
    |= constructor || error_mark; /* static initialization...  */

  _expr_escaper.curr_node = currently_walking;
  _expr_escaper.update (var_decl, reason);
  gimple_walker::_walk_global (vnode);
}

bool
_filter_known_function (tree fndecl)
{
  assert_is_type (fndecl, FUNCTION_DECL);
  if (fndecl_built_in_p (fndecl, BUILT_IN_NORMAL))
    {
      switch (DECL_FUNCTION_CODE (fndecl))
	{
	case BUILT_IN_FREE:
	case BUILT_IN_MALLOC:
	case BUILT_IN_REALLOC:
	case BUILT_IN_CALLOC:
	case BUILT_IN_MEMSET:
	  return true;
	  break;
	default:
	  break;
	}
    }

  return false;
}

/* Return true if FNDECL is a known function.  */
bool
gimple_escaper::filter_known_function (tree fndecl)
{
  return _filter_known_function (fndecl);
}

/* Return True if NODE points to a known FUNCTION_DECL.  */
bool
gimple_escaper::filter_known_function (cgraph_node *node)
{
  if (!node)
    return false;
  return filter_known_function (node->decl);
}

/* Mark Variable declaration of unknown location as escaping.  */
void
gimple_escaper::_walk_pre_tree (tree t)
{
  /* Finding escaping global variables.  */
  Reason reason;
  if (TREE_CODE (t) == VAR_DECL)
    {
      if (DECL_SOURCE_LOCATION (t) == UNKNOWN_LOCATION)
	/* Detecting some builtin types
	   I think fprofile-generate inserts some builtin types which
	   cannot be detected in any other way...
	   TODO: Maybe add a new reason instead of overloading is_indirect.  */
	reason.is_indirect = true;
    }
  _expr_escaper.curr_node = currently_walking;
  _expr_escaper.update (t, reason);
}

void
gimple_escaper::_walk_pre_gassign (gassign *s)
{
  Reason reason;
  _expr_escaper.curr_node = currently_walking;
  const enum gimple_rhs_class code = gimple_assign_rhs_class (s);
  switch (code)
    {
    case GIMPLE_TERNARY_RHS:
      {
	tree rhs3 = gimple_assign_rhs3 (s);
	_expr_escaper.update (rhs3, reason);
      }
    /* fall-through.  */
    case GIMPLE_BINARY_RHS:
      {
	tree rhs2 = gimple_assign_rhs2 (s);
	_expr_escaper.update (rhs2, reason);
      }
    /* fall-through.  */
    case GIMPLE_UNARY_RHS:
    case GIMPLE_SINGLE_RHS:
      {
	tree rhs1 = gimple_assign_rhs1 (s);
	_expr_escaper.update (rhs1, reason);
	tree lhs = gimple_assign_lhs (s);
	if (!lhs)
	  break;
	_expr_escaper.update (lhs, reason);
      }
      break;
    default:
      gcc_unreachable ();
      break;
    }
}

void
gimple_escaper::_walk_pre_greturn (greturn *s)
{
  Reason reason;
  _expr_escaper.curr_node = currently_walking;
  tree val = gimple_return_retval (s);
  if (!val)
    return;
  _expr_escaper.update (val, reason);
}

void
gimple_escaper::_walk_pre_gcond (gcond *s)
{
  Reason reason;
  tree lhs = gimple_cond_lhs (s);
  tree rhs = gimple_cond_rhs (s);
  gcc_assert (lhs && rhs);
  _expr_escaper.curr_node = currently_walking;
  _expr_escaper.update (lhs, reason);
  _expr_escaper.update (rhs, reason);
}

void
gimple_escaper::_walk_pre_gcall (gcall *s)
{
  tree fn = gimple_call_fndecl (s);
  _expr_escaper.curr_node = currently_walking;
  /* gcc_assert (fn);
     The above assertion will not always be true
     It will be false when we have an indirect function.  */
  cgraph_node *node = fn ? cgraph_node::get (fn) : NULL;
  const bool _is_function_escaping
    = node ? is_function_escaping (node) : is_function_escaping (fn);
  const bool is_undefined = undefined2.contains (fn);
  const bool _is_escaping = is_undefined || _is_function_escaping;

  Reason arg_reason;
  arg_reason.parameter_is_visible = _is_escaping;
  arg_reason.is_indirect = !fn;
  unsigned n = gimple_call_num_args (s);
  for (unsigned i = 0; i < n; i++)
    {
      tree a = gimple_call_arg (s, i);
      gcc_assert (a);
      _expr_escaper._type_escaper.update (TREE_TYPE (a), arg_reason);
    }

  tree lhs = gimple_call_lhs (s);
  if (!lhs)
    return;
  Reason return_reason;
  return_reason.return_is_visible = _is_escaping;
  return_reason.is_indirect = !fn;
  _expr_escaper.update (lhs, return_reason);
}

static bool
_follow_def_to_find_if_really_cast (tree rhs)
{
  gimple *def_for_rhs = SSA_NAME_DEF_STMT (rhs);
  gcall *is_call = dyn_cast<gcall *> (def_for_rhs);
  if (!is_call)
    return true;

  tree fn = gimple_call_fndecl (is_call);
  if (!fn)
    return true;

  bool known_function = _filter_known_function (fn);
  return !known_function;
}

/* Determine if cast comes from a known function.
 * Do this by following the use-def chain.  */
bool
gimple_caster::follow_def_to_find_if_really_cast (tree rhs)
{
  return _follow_def_to_find_if_really_cast (rhs);
}

static inline offset_int
signed_offset (tree offset)
{
 tree type = TREE_TYPE (offset);
 return wi::sext (wi::to_offset (offset), TYPE_PRECISION (type));
}

static inline tree
get_array_etype (tree type)
{
  while (TREE_CODE (type) == ARRAY_TYPE)
    type = TREE_TYPE (type);

  return type;
}

static bool
contain_field_of_type (tree ctype, tree type, offset_int offset,
		       type_structural_equality *equality)
{
  for (tree field = TYPE_FIELDS (ctype); field; field = DECL_CHAIN (field))
    {
      offset_int field_offset = wi::to_offset (DECL_FIELD_OFFSET (field));

      field_offset += wi::to_offset (DECL_FIELD_BIT_OFFSET (field))
				     >> LOG2_BITS_PER_UNIT;

      if (offset < field_offset)
	return false;

      tree field_type = TREE_TYPE (field);
      offset_int field_size = wi::to_offset (TYPE_SIZE_UNIT (field_type));

      if (offset >= field_offset + field_size)
	continue;

      offset -= field_offset;

      if (TREE_CODE (field_type) == ARRAY_TYPE)
	{
	  if (!COMPLETE_TYPE_P (type))
	    return false;

	  offset_int type_size = wi::to_offset (TYPE_SIZE_UNIT (type));

	  while (field_size > type_size)
	    {
	      tree domain = TYPE_DOMAIN (field_type);

	      field_type = TREE_TYPE (field_type);
	      field_size = wi::to_offset (TYPE_SIZE_UNIT (field_type));

	      offset_int start = wi::to_offset (TYPE_MIN_VALUE (domain));
	      offset_int index = start + wi::divmod_trunc (offset, field_size,
							   UNSIGNED, &offset);

	      if (index > wi::to_offset (TYPE_MAX_VALUE (domain)))
		return false;

	      if (TREE_CODE (field_type) != ARRAY_TYPE)
		break;
	    }
	}

      if (offset == 0 && equality->equal (field_type, type))
	return true;

      if (!RECORD_OR_UNION_TYPE_P (field_type)
	  || !COMPLETE_TYPE_P (field_type))
	return false;

      return contain_field_of_type (field_type, type, offset, equality);
    }

  return false;
}

static int
can_cast_type_p (tree src_type, tree dst_type, offset_int offset,
		 type_structural_equality *equality)
{
  if (offset != 0)
    {
      tree size_unit = TYPE_SIZE_UNIT (src_type);

      if (!size_unit || TREE_CODE (size_unit) != INTEGER_CST)
	return 0;

      offset_int size = wi::to_offset (size_unit);

      if (offset >= size || offset < 0)
	{
	  wi::overflow_type overflow;

	  offset = wi::mod_floor (offset, size, SIGNED, &overflow);
	}
    }

  if (offset == 0 && equality->equal (src_type, dst_type))
    return 1;

  if (!COMPLETE_TYPE_P (src_type) || !RECORD_OR_UNION_TYPE_P  (src_type))
    return 0;

  if (contain_field_of_type (src_type, dst_type, offset, equality))
    return -1;

  return 0;
}

void
gimple_caster::mark_type (tree type)
{
  Reason reason;

  reason.type_is_casted = true;
  _expr_escaper.curr_node = currently_walking;
  _expr_escaper._type_escaper.update (type, reason);
}

void
gimple_caster::_walk_memref (tree memref, type_structural_equality *equality)
{
  tree base = memref;

  while (handled_component_p (base))
    base = TREE_OPERAND (base, 0);

  if (TREE_CODE (base) == MEM_REF)
    {
      tree addr = TREE_OPERAND (base, 0);
      tree addr_type = get_array_etype (TREE_TYPE (TREE_TYPE (addr)));
      tree data_type = TREE_TYPE (base);
      tree offset = TREE_OPERAND (base, 1);
      int matched = can_cast_type_p (addr_type, data_type,
				     signed_offset (offset), equality);

      if (!matched)
	{
	  mark_type (addr_type);
	  mark_type (data_type);
	}
    }
  else
    gcc_assert (TREE_CODE (base) != TARGET_MEM_REF);
}

int
gimple_caster::_walk_address (tree addr, type_structural_equality *equality,
			      tree type, tree offset)
{
  if (!POINTER_TYPE_P (type))
    return 0;

  tree addr_type = get_array_etype (TREE_TYPE (TREE_TYPE (addr)));
  tree data_type = get_array_etype (TREE_TYPE (type));

  int matched = can_cast_type_p (addr_type, data_type,
				 offset ? signed_offset (offset) : 0,
				 equality);

  if (matched > 0 && TREE_CODE (addr) == ADDR_EXPR)
    matched = -1;

  return matched;
}

static bool
add_memref (gimple *, tree, tree memref, void *data)
{
  auto &vars = *(auto_vec<tree> *) data;

  vars.safe_push (memref);
  return false;
}

void
gimple_caster::_walk_memref (gimple *stmt)
{
  if (gimple_clobber_p (stmt))
    return;

  auto_vec<tree> memrefs;

  walk_stmt_load_store_addr_ops (stmt, &memrefs, add_memref, add_memref,
				 add_memref);

  if (memrefs.is_empty ())
    return;

  type_incomplete_equality equality;

  for (auto memref : memrefs)
    _walk_memref (memref, &equality);
}

void
gimple_caster::mark_type_in_address (tree addr)
{
  mark_type (TREE_TYPE (addr));

  if (TREE_CODE (addr) == ADDR_EXPR)
    {
      tree base = get_base_address (TREE_OPERAND (addr, 0));

      if (TREE_CODE (base) == MEM_REF)
	mark_type_in_address (TREE_OPERAND (base, 0));
      else
	mark_type (TREE_TYPE (base));
    }
}

void
gimple_caster::_walk_pre_gassign (gassign *s)
{
  enum tree_code code = gimple_assign_rhs_code (s);
  tree lhs = gimple_assign_lhs (s);
  tree rhs1 = gimple_assign_rhs1 (s);
  tree rhs2 = gimple_assign_rhs2 (s);
  tree t_lhs = TREE_TYPE (lhs);
  tree t_rhs1 = TREE_TYPE (rhs1);
  int matched = -1;

  /* I originally was using gimple_assign_cast_p
     but that proved to be insufficient...
     So we have to use our equality comparison...  */
  type_incomplete_equality equality;

  _walk_memref (s);

  switch (code)
    {
    case VIEW_CONVERT_EXPR:
      rhs1 = TREE_OPERAND (rhs1, 0);
      t_rhs1 = TREE_TYPE (rhs1);

    /* fall-through. */

    case SSA_NAME:
    case ADDR_EXPR:
    CASE_CONVERT:
      if (!POINTER_TYPE_P (t_lhs) && !POINTER_TYPE_P ((t_rhs1)))
	break;

      if (POINTER_TYPE_P (t_lhs) && POINTER_TYPE_P (t_rhs1))
	{
	  matched = _walk_address (rhs1, &equality, t_lhs);

	  if (!matched)
	    {
	      /* If it is cast, we might need to look at the definition of rhs
		 If the definition comes from a known function... then we are
		 good...  */
	      if (TREE_CODE (rhs1) == SSA_NAME
		  && !follow_def_to_find_if_really_cast (rhs1))
		matched = 1;
	    }
	}
      else
	matched = 0;

      if (!matched)
	{
	  bool *whitelisted = _whitelisted2->get (currently_walking->decl);

	  if (whitelisted && *whitelisted)
	    {
	      gimple_escaper::_walk_pre_gassign (s);
	      return;
	    }

	  mark_type_in_address (lhs);
	  mark_type_in_address (rhs1);
	}

      gimple_escaper::_walk_pre_gassign (s);
      break;

    case MULT_EXPR:
    case MULT_HIGHPART_EXPR:
    case TRUNC_DIV_EXPR:
    case CEIL_DIV_EXPR:
    case FLOOR_DIV_EXPR:
    case ROUND_DIV_EXPR:
    case TRUNC_MOD_EXPR:
    case CEIL_MOD_EXPR:
    case FLOOR_MOD_EXPR:
    case ROUND_MOD_EXPR:
    case RDIV_EXPR:
    case EXACT_DIV_EXPR:
    case BIT_IOR_EXPR:
    case BIT_XOR_EXPR:
    case BIT_AND_EXPR:
      if (POINTER_TYPE_P (t_lhs))
	{
	  mark_type_in_address (lhs);
	  mark_type_in_address (rhs1);
	  mark_type_in_address (rhs2);
	}
      break;

    case MAX_EXPR:
    case MIN_EXPR:
    case COND_EXPR:
      if (POINTER_TYPE_P (t_lhs))
	{
	  for (unsigned i = 1; i < 3; i++)
	    {
	      tree opnd = gimple_op (s, gimple_num_ops (s) - i);

	      matched = _walk_address (opnd, &equality, t_lhs);
	      if (!matched)
		mark_type_in_address (opnd);
	    }
	}
      break;

    default:
      ;
    }
}

/* Check to see if arguments are casted.  */
void
gimple_caster::_walk_pre_gcall (gcall *s)
{
  gimple_escaper::_walk_pre_gcall (s);

  tree fn = gimple_call_fndecl (s);
  /* If there's no function declaration, how do we
     know the argument types.  */
  if (!fn)
    return;

  _walk_memref (s);

  cgraph_node *node = cgraph_node::get (fn);
  const bool known_function = gimple_escaper::filter_known_function (node)
			      || gimple_escaper::filter_known_function (fn);
  if (known_function)
    return;

  tree f_t = TREE_TYPE (fn);
  if (!_whitelisted2->is_empty () && _whitelisted2->get (fn)
      && *_whitelisted2->get (fn))
    return;
  bool in_map = !_whitelisted2->is_empty ()
		&& _whitelisted2->get (currently_walking->decl);
  bool whitelisted = in_map && *_whitelisted2->get (currently_walking->decl);
  if (whitelisted)
    return;

  if (!node && currently_walking->callers && currently_walking->inlined_to)
    return;

  type_incomplete_equality equality;

  unsigned i = 0;
  _expr_escaper.curr_node = currently_walking;
  for (tree a = TYPE_ARG_TYPES (f_t); NULL_TREE != a; a = TREE_CHAIN (a))
    {
      tree formal_t = TREE_VALUE (a);
      const enum tree_code code = TREE_CODE (formal_t);
      const bool is_void = VOID_TYPE == code;
      if (is_void)
	continue;

      tree real = gimple_call_arg (s, i);
      tree real_t = TREE_TYPE (real);
      bool is_casted = !equality.equal (formal_t, real_t);
      is_casted = is_casted && (formal_t != ptr_type_node);
      Reason arg_reason;
      arg_reason.type_is_casted = is_casted;
      _expr_escaper._type_escaper.update (TREE_TYPE (real), arg_reason);
      i++;
    }

  tree lhs = gimple_call_lhs (s);
  if (!lhs)
    return;

  tree r_t = TREE_TYPE (f_t);
  tree l_t TREE_TYPE (lhs);
  const bool is_casted = !equality.equal (r_t, l_t);
  Reason ret_reason;
  ret_reason.type_is_casted = is_casted;
  _expr_escaper.update (lhs, ret_reason);
}

void
gimple_caster::_walk_pre_greturn (greturn *s)
{
  tree retval = gimple_return_retval (s);
  tree type = TREE_TYPE (TREE_TYPE (cfun->decl));

  _walk_memref (s);

  gcc_assert (TREE_CODE (type) != ARRAY_TYPE);

  if (!retval)
    {
      if (!VOID_TYPE_P (type))
	mark_type (type);
      return;
    }

  tree decl = retval;

  if (TREE_CODE (retval) == SSA_NAME && SSA_NAME_VAR (retval))
    decl = SSA_NAME_VAR (retval);

  if (TREE_CODE (decl) == RESULT_DECL && DECL_BY_REFERENCE (decl))
    {
      if (TREE_CODE (TREE_TYPE (retval)) == REFERENCE_TYPE)
	type = build_reference_type (type);
      else if (TREE_CODE (TREE_TYPE (retval)) == POINTER_TYPE)
	type = build_pointer_type (type);
      else
	gcc_unreachable ();
    }

  if (POINTER_TYPE_P (type))
    {
      type_incomplete_equality equality;

      if (!_walk_address (retval, &equality, type))
	mark_type_in_address (retval);
    }
}

void
gimple_caster::_walk_pre_gphi (gphi *s)
{
  tree result = gimple_phi_result (s);
  tree type = TREE_TYPE (result);

  if (!POINTER_TYPE_P (type))
    return;

  type_incomplete_equality equality;
  bool has_cast = false;

  _walk_memref (s);

  for (unsigned i = 0; i < gimple_phi_num_args (s); i++)
    {
      tree arg = gimple_phi_arg_def (s, i);

      if (integer_zerop (arg))
	continue;

      if (!_walk_address (arg, &equality, type))
	{
	  if (TREE_CODE (arg) == SSA_NAME
	      && !follow_def_to_find_if_really_cast (arg))
	    continue;

	  mark_type_in_address (arg);
	  has_cast = true;
	}
    }

  if (has_cast)
    mark_type (type);
}

bool
type_accessor::is_in_record_field_map (tree t)
{
  return _map4.get (t);
}

field_access_map2_t *
type_accessor::get_from_record_field_map (tree t)
{
  gcc_assert (_map4.get (t));
  field_access_map2_t *value = *_map4.get (t);
  return value;
}

void
type_accessor::put_in_record_field_map (tree t, field_access_map2_t *f)
{
  if (_map4.get (t) && (*_map4.get (t) != f))
    {
      delete *(_map4.get (t));
    }
  _map4.put (t, f);
}

bool
type_accessor::is_memoized (tree t)
{
  return memoized_map2.contains (t);
}

/* Add all fields in struct to memoized map.  */
void
type_accessor::_walk_RECORD_TYPE_pre (tree t)
{
  add_all_fields_in_struct (t);
  memoized_map2.add (t);
}

/* Initialize all fields as neither read nor written.  */
void
type_accessor::add_all_fields_in_struct (tree t)
{
  const enum tree_code c = TREE_CODE (t);
  const bool is_record = RECORD_TYPE == c;
  if (!is_record)
    return;

  const bool record_already_in_map = is_in_record_field_map (t);
  field_access_map2_t *field_map;
  field_map = record_already_in_map ? get_from_record_field_map (t)
				    : new field_access_map2_t;

  /* Let's add all fields to the field map as empty.  */
  for (tree field = TYPE_FIELDS (t); field; field = DECL_CHAIN (field))
    {
      const bool field_already_in_map_2 = field_map->get (field);
      if (field_already_in_map_2)
	continue;
      field_map->put (field, Empty);
    }

  put_in_record_field_map (t, field_map);
}

void
expr_accessor::add_all_fields_in_struct (tree t)
{
  _type_accessor.walk (t);
}

void
expr_accessor::_walk_pre (tree e)
{
  _stack2.safe_push (e);
  tree t = TREE_TYPE (e);
  add_all_fields_in_struct (t);
}

void
expr_accessor::_walk_post (__attribute__ ((unused)) tree e)
{
  _stack2.pop ();
}

void
expr_accessor::update (tree e, unsigned access)
{
  _access = access;
  walk (e);
}

/* Check if we are accessing a field through pointer arithmetic.  If this is
   happening it is likely the result of an optimization. Since we are not
   modifying these types of expressions yet, we must mark all fields leading to
   the accessed fields as possibly READ.

   TODO: If we modify this expression later on, we could make our transformation
   more powerful and precise by not marking all fields leading up to this one as
   possibly read. */
void
expr_accessor::_walk_ADDR_EXPR_pre (__attribute__ ((unused)) tree e)
{
  if (_stack2.length () < 4)
    return;

  /* TODO: Fix error with double pushing.  */
  tree addr_expr = _stack2.last ();
  _stack2.pop ();
  tree twice = _stack2.last ();
  _stack2.pop ();
  tree prev_expr = _stack2.last ();
  _stack2.safe_push (addr_expr);
  _stack2.safe_push (twice);
  if (TREE_CODE (prev_expr) != MEM_REF)
    return;

  tree op_0 = TREE_OPERAND (addr_expr, 0);
  tree addr_expr_t = TREE_TYPE (op_0);

  if (TREE_CODE (addr_expr_t) != RECORD_TYPE)
    return;

  /* We are accessing a field of a record through pointer arithmetic...
     So what field offset are we computing...  */
  tree mref_expr = prev_expr;
  tree offset = TREE_OPERAND (mref_expr, 1);
  gcc_assert (TREE_CODE (offset) == INTEGER_CST);
  tree type_size_tree = TYPE_SIZE_UNIT (addr_expr_t);
  int type_size_int = tree_to_shwi (type_size_tree);
  /* TODO: Very recently inserted this assertion so we need to test this.  */
  gcc_assert (type_size_int > 0);
  unsigned offset_int = tree_to_uhwi (offset) % type_size_int;
  /* We need to get the field that corresponds to the offset_int.  */
  const bool record_already_in_map
    = _type_accessor.is_in_record_field_map (addr_expr_t);
  field_access_map2_t *field_map;
  field_map = record_already_in_map
		? _type_accessor.get_from_record_field_map (addr_expr_t)
		: new field_access_map2_t;

  /* UNSAFE! But it is necessary for testing...
     Unless there is someone who is smarter that finds another way to test this.
   */
  if (flag_ipa_dlo_tests)
    return;

  tree field = NULL;
  for (field = TYPE_FIELDS (addr_expr_t); field; field = DECL_CHAIN (field))
    {
      unsigned f_byte_offset = tree_to_uhwi (DECL_FIELD_OFFSET (field));
      unsigned f_bit_offset = tree_to_uhwi (DECL_FIELD_BIT_OFFSET (field)) / 8;
      unsigned f_offset = f_byte_offset + f_bit_offset;

      /* NOTE: ALL FIELDS BEFORE THIS ONE NEED TO EXIST
	 Otherwise, this pointer arithmetic is invalid...
	 After the transformation.  */
      const bool field_already_in_map = field_map->get (field);
      unsigned prev_access
	= field_already_in_map ? *field_map->get (field) : Empty;

      prev_access |= Read;
      field_map->put (field, prev_access);
      add_all_fields_in_struct (addr_expr_t);
      _type_accessor.put_in_record_field_map (addr_expr_t, field_map);

      if (f_offset == offset_int)
	break;
    }
}

/* Find out if we are taking the address of a FIELD_DECL.
 * If this is the case, it means that all FIELDS in this
 * RECORD_TYPE should be marked as READ for safety.
 */
void
expr_accessor::_walk_COMPONENT_REF_pre (tree e)
{
  assert_is_type (e, COMPONENT_REF);
  tree op0 = TREE_OPERAND (e, 0);
  gcc_assert (op0);
  tree op0_t = TREE_TYPE (op0);
  gcc_assert (op0_t);
  /* op0_t can either be a RECORD_TYPE or a UNION_TYPE.  */
  const enum tree_code code = TREE_CODE (op0_t);
  const bool is_record = RECORD_TYPE == code;
  const bool is_union = UNION_TYPE == code;
  const bool valid = is_record != is_union;
  gcc_assert (valid);

  tree op1 = TREE_OPERAND (e, 1);
  assert_is_type (op1, FIELD_DECL);
  const bool record_already_in_map
    = _type_accessor.is_in_record_field_map (op0_t);
  field_access_map2_t *field_map;
  field_map = record_already_in_map
		? _type_accessor.get_from_record_field_map (op0_t)
		: new field_access_map2_t;
  const bool field_already_in_map = field_map->get (op1);
  unsigned prev_access = field_already_in_map ? *field_map->get (op1) : Empty;

  prev_access |= _access;
  field_map->put (op1, prev_access);
  add_all_fields_in_struct (op0_t);
  _type_accessor.put_in_record_field_map (op0_t, field_map);

  if (_stack2.length () < 4)
    return;

  tree this_expr = _stack2.last ();
  _stack2.pop ();
  tree twice = _stack2.last ();
  _stack2.pop ();
  tree prev_expr = _stack2.last ();
  _stack2.safe_push (twice);
  _stack2.safe_push (this_expr);
  if (TREE_CODE (prev_expr) != ADDR_EXPR)
    return;

  tree t = op0_t;
  if (TREE_CODE (t) != RECORD_TYPE)
    return;

  /* If we are taking the address of a component, we need to mark the whole
   * RECORD_TYPE as escaping due to pointer arithmetic.
   * TODO: Maybe add a flag to enable and disable this for debugging and
   * testing.
   */

  /* UNSAFE! But it is necessary for testing...
     Unless there is someone who is smarter that
     finds another way to test this.
   */
  if (flag_ipa_dlo_tests)
    return;

  for (tree field = TYPE_FIELDS (t); field; field = DECL_CHAIN (field))
    {
      const bool field_already_in_map = field_map->get (field);
      unsigned prev_access
	= field_already_in_map ? *field_map->get (field) : Empty;

      prev_access |= Read;
      field_map->put (field, prev_access);
      add_all_fields_in_struct (t);
      _type_accessor.put_in_record_field_map (t, field_map);
    }
}

/* Print results.  */
void
expr_accessor::print_accesses ()
{
  /* TODO: After the migration, we changed interfaces.
     Add this debugging mechanism again at a later date.  */
}

void
gimple_accessor::print_accesses ()
{
  _expr_accessor.print_accesses ();
}

/* Mark RHS as Read and LHS as Write.  */
void
gimple_accessor::_walk_pre_gassign (gassign *s)
{
  /* There seems to be quite a bit of code duplication here...  */
  const enum gimple_rhs_class code = gimple_assign_rhs_class (s);
  switch (code)
    {
    case GIMPLE_TERNARY_RHS:
      {
	tree rhs3 = gimple_assign_rhs3 (s);
	gcc_assert (rhs3);
	_expr_accessor.update (rhs3, Read);
      }
    /* fall-through.  */
    case GIMPLE_BINARY_RHS:
      {
	tree rhs2 = gimple_assign_rhs2 (s);
	gcc_assert (rhs2);
	_expr_accessor.update (rhs2, Read);
      }
    /* fall-through.  */
    case GIMPLE_UNARY_RHS:
    case GIMPLE_SINGLE_RHS:
      {
	tree rhs1 = gimple_assign_rhs1 (s);
	_expr_accessor.update (rhs1, Read);
	tree lhs = gimple_assign_lhs (s);
	if (!lhs)
	  break;
	_expr_accessor.update (lhs, Write);
	break;
      }
    default:
      gcc_unreachable ();
      break;
    }
}

/* Mark RHS as Read and LHS as Written.  */
void
gimple_accessor::_walk_pre_gcall (gcall *s)
{
  unsigned n = gimple_call_num_args (s);
  for (unsigned i = 0; i < n; i++)
    {
      tree a = gimple_call_arg (s, i);
      gcc_assert (a);
      _expr_accessor.update (a, Read);
    }

  tree lhs = gimple_call_lhs (s);
  if (!lhs)
    return;
  _expr_accessor.update (lhs, Write);
}

/* Mark as Read.  */
void
gimple_accessor::_walk_pre_greturn (greturn *s)
{
  tree val = gimple_return_retval (s);
  if (!val)
    return;
  _expr_accessor.update (val, Read);
}

/* Mark as Read.  */
void
gimple_accessor::_walk_pre_gcond (gcond *s)
{
  tree lhs = gimple_cond_lhs (s);
  tree rhs = gimple_cond_rhs (s);
  gcc_assert (lhs && rhs);
  _expr_accessor.update (lhs, Read);
  _expr_accessor.update (rhs, Read);
}

/* Print Reasons why a type might be escaping.  */
void
Reason::print () const
{
  log ("e=%d g=%d p=%d r=%d c=%d v=%d u=%d i=%d\n", this->is_escaping (),
       this->global_is_visible, this->parameter_is_visible,
       this->return_is_visible, this->type_is_casted, this->type_is_volatile,
       this->type_is_in_union, this->is_indirect);
}

/* Or an escaping Reason.  */
Reason
Reason::operator| (const Reason &other)
{
  Reason retval;
  retval.global_is_visible = this->global_is_visible | other.global_is_visible;
  retval.parameter_is_visible
    = this->parameter_is_visible | other.parameter_is_visible;
  retval.return_is_visible = this->return_is_visible | other.return_is_visible;
  retval.type_is_casted = this->type_is_casted | other.type_is_casted;
  retval.type_is_volatile = this->type_is_volatile | other.type_is_volatile;
  retval.type_is_in_union = this->type_is_in_union | other.type_is_in_union;
  retval.is_indirect = this->is_indirect | other.is_indirect;
  return retval;
}

/* Or an escaping Reason.  */
Reason &
Reason::operator|= (const Reason &other)
{
  this->global_is_visible |= other.global_is_visible;
  this->parameter_is_visible |= other.parameter_is_visible;
  this->return_is_visible |= other.return_is_visible;
  this->type_is_casted |= other.type_is_casted;
  this->type_is_volatile |= other.type_is_volatile;
  this->type_is_in_union |= other.type_is_in_union;
  this->is_indirect |= other.is_indirect;
  return *this;
}

/* Insert TYPE into a partition depending on IN_POINTS_TO_RECORD.  */
void
type_partitions2_s::insert (tree type, bool in_points_to_record)
{
  gcc_assert (type);
  this->universe.add (type);
  in_points_to_record ? this->points_to_record.add (type)
		      : this->complement.add (type);
  const bool in_points_to_set = this->in_points_to_record (type);
  const bool in_complement = this->in_complement (type);
  const bool _xor = in_points_to_set != in_complement;
  gcc_assert (_xor);
}

/* Find out whether TYPE is already in universe.  */
bool
type_partitions2_s::in_universe (tree type)
{
  gcc_assert (type);
  const bool seen_before = this->universe.contains (type);
  return seen_before;
}

/* Find out whether TYPE is in points_to_record partition.  */
bool
type_partitions2_s::in_points_to_record (tree type)
{
  gcc_assert (type);
  const bool seen_before = this->points_to_record.contains (type);
  return seen_before;
}

/* Find out whether TYPE is not in points to record partition.  */
bool
type_partitions2_s::in_complement (tree type)
{
  gcc_assert (type);
  const bool seen_before = this->complement.contains (type);
  return seen_before;
}

bool
type_stringifier::is_memoized (tree t)
{
  return _memoized_set.contains (t);
}

/* Stringify a type.  */
std::string
type_stringifier::stringify (tree t)
{
  if (!dump_file || !t)
    return std::string ("");
  _stringification.clear ();
  gcc_assert (t);
  if (detected_incompatible_syntax)
    return std::string ("");
  walk (t);
  return _stringification;
}

void
type_stringifier::_walk_VOID_TYPE_pre (tree t)
{
  _stringify_simple (t);
}

void
type_stringifier::_walk_INTEGER_TYPE_pre (tree t)
{
  _stringify_simple (t);
}

void
type_stringifier::_walk_REAL_TYPE_pre (tree t)
{
  _stringify_simple (t);
}

void
type_stringifier::_walk_FIXED_POINT_TYPE_pre (tree t)
{
  _stringify_simple (t);
}

void
type_stringifier::_walk_COMPLEX_TYPE_pre (tree t)
{
  _stringify_simple (t);
}

void
type_stringifier::_walk_OFFSET_TYPE_pre (tree t)
{
  _stringify_simple (t);
}

void
type_stringifier::_walk_BOOLEAN_TYPE_pre (tree t)
{
  _stringify_simple (t);
}

void
type_stringifier::_stringify_simple (tree t)
{
  gcc_assert (t);
  const enum tree_code code = TREE_CODE (t);
  this->_stringification += std::string (get_tree_code_name (code));
}

void
type_stringifier::_walk_POINTER_TYPE_pre (tree t)
{
  _memoized_set.add (t);
}

void
type_stringifier::_walk_POINTER_TYPE_post (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string ("*");
}

void
type_stringifier::_walk_ARRAY_TYPE_post (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string ("[]");
}

void
type_stringifier::_walk_ARRAY_TYPE_pre (tree t)
{
  _memoized_set.add (t);
}

void
type_stringifier::_walk_REFERENCE_TYPE_post (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string ("&");
}

void
type_stringifier::_walk_UNION_TYPE_pre (tree t)
{
  this->_stringification += std::string (" union ");
  _stringify_aggregate_pre (t);
  _memoized_set.add (t);
}

void
type_stringifier::_walk_UNION_TYPE_post (tree t)
{
  _stringify_aggregate_post (t);
}

void
type_stringifier::_walk_RECORD_TYPE_pre (tree t)
{
  this->_stringification += std::string (" record ");
  _stringify_aggregate_pre (t);
  _memoized_set.add (t);
}

void
type_stringifier::_walk_RECORD_TYPE_post (tree t)
{
  _stringify_aggregate_post (t);
}

void
type_stringifier::_stringify_aggregate_pre (tree t)
{
  this->_stringification
    += type_stringifier::get_type_identifier (t) + std::string (" {");
}

void
type_stringifier::_stringify_aggregate_post (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string ("}");
}

void
type_stringifier::_walk_field_post (tree t)
{
  this->_stringification += std::string (" ")
			    + type_stringifier::get_field_identifier (t)
			    + std::string (";");
}

void
type_stringifier::_walk_METHOD_TYPE_pre (tree t)
{
  _stringify_fm_pre (t);
}

void
type_stringifier::_walk_METHOD_TYPE_post (tree t)
{
  _stringify_fm_post (t);
}

void
type_stringifier::_walk_FUNCTION_TYPE_pre (tree t)
{
  _stringify_fm_pre (t);
}

void
type_stringifier::_walk_FUNCTION_TYPE_post (tree t)
{
  _stringify_fm_post (t);
}

void
type_stringifier::_stringify_fm_pre (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string ("function { ");
}

void
type_stringifier::_stringify_fm_post (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string ("}");
}

void
type_stringifier::_walk_return_pre (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string ("(");
}

void
type_stringifier::_walk_return_post (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string (")");
}

void
type_stringifier::_walk_args_pre (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string ("(");
}

void
type_stringifier::_walk_args_post (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string (")");
}

void
type_stringifier::_walk_arg_post (__attribute__ ((unused)) tree t)
{
  this->_stringification += std::string (", ");
}

std::string
type_stringifier::get_type_identifier (tree t)
{
  if (detected_incompatible_syntax)
    return std::string ("incompatible syntax");
  tree name = TYPE_NAME (t);
  bool no_name = NULL_TREE == name;
  if (no_name)
    return std::string ("NULL_TREE == name");

  const enum tree_code name_code = TREE_CODE (name);
  const bool is_name_type_decl = TYPE_DECL == name_code;
  name = is_name_type_decl ? DECL_NAME (name) : name;
  no_name = NULL_TREE == name;
  if (no_name)
    return std::string ("NULL_TREE == name");
  const char *identifier_ptr = IDENTIFIER_POINTER (name);
  gcc_assert (identifier_ptr);
  return std::string (identifier_ptr);
}

std::string
type_stringifier::get_field_identifier (tree t)
{
  assert_is_type (t, FIELD_DECL);
  tree decl_name = DECL_NAME (t);
  if (!decl_name)
    return std::string ("");

  const char *identifier = IDENTIFIER_POINTER (decl_name);
  return std::string (identifier);
}

/* Return true if L and R have equal structural equalities.  */
bool
type_structural_equality::equal (tree l, tree r)
{
  return _equal (l, r);
}

bool
type_structural_equality::_equal (tree l, tree r)
{
  bool valid_inputs = l && r;
  if (!valid_inputs)
    return l == r;

  if (!_equal_code (l, r))
    return false;

  l = TYPE_MAIN_VARIANT (l);
  r = TYPE_MAIN_VARIANT (r);

  if (l == r)
    return true;

  if (!TYPE_STRUCTURAL_EQUALITY_P (l) && !TYPE_STRUCTURAL_EQUALITY_P (r))
    return TYPE_CANONICAL (l) == TYPE_CANONICAL (r);

  const enum tree_code code = TREE_CODE (l);

  switch (code)
    {
      case VOID_TYPE:
      case OFFSET_TYPE:
	return true;

      case INTEGER_TYPE:
      case BOOLEAN_TYPE:
      case ENUMERAL_TYPE:
      case REAL_TYPE:
      case FIXED_POINT_TYPE:
      case COMPLEX_TYPE:
      case VECTOR_TYPE:
	return useless_type_conversion_p (l, r);

      default:
	break;
    }

  bool recurse2_l = set2_l.contains (l);
  bool recurse2_r = set2_r.contains (r);
  bool recurse = recurse2_l || recurse2_r;
  if (recurse)
    return recurse;

  set2_l.add (l);
  set2_r.add (r);
  bool equal_children = false;
  switch (code)
    {
#define TSE_CASE(code) \
  case code: \
    equal_children = _walk_##code (l, r); \
    break

      TSE_CASE (RECORD_TYPE);
      TSE_CASE (POINTER_TYPE);
      TSE_CASE (REFERENCE_TYPE);
      TSE_CASE (ARRAY_TYPE);
      TSE_CASE (UNION_TYPE);
      TSE_CASE (FUNCTION_TYPE);
      TSE_CASE (METHOD_TYPE);
    default:
#ifdef ABORT_IF_NOT_C
      detected_incompatible_syntax = true;
      return false;
#else
      gcc_unreachable ();
#endif
      break;
    }

  set2_l.remove (l);
  set2_r.remove (r);
  return equal_children;
}

bool
type_structural_equality::_equal_code (tree l, tree r)
{
  const enum tree_code code_l = TREE_CODE (l);
  const enum tree_code code_r = TREE_CODE (r);
  const bool equal = code_l == code_r;
  bool array_or_ptr_l
    = TREE_CODE (l) == ARRAY_TYPE || TREE_CODE (l) == POINTER_TYPE;
  bool array_or_ptr_r
    = TREE_CODE (r) == ARRAY_TYPE || TREE_CODE (r) == POINTER_TYPE;
  bool array_or_ptr = array_or_ptr_l && array_or_ptr_r;
  return equal || array_or_ptr;
}

#define TSE_FUNC_DEF_SIMPLE(code) \
  bool type_structural_equality::_walk_##code (tree l, tree r) \
  { \
    return _equal_code (l, r); \
  }

TSE_FUNC_DEF_SIMPLE (VOID_TYPE)
TSE_FUNC_DEF_SIMPLE (INTEGER_TYPE)
TSE_FUNC_DEF_SIMPLE (REAL_TYPE)
TSE_FUNC_DEF_SIMPLE (FIXED_POINT_TYPE)
TSE_FUNC_DEF_SIMPLE (ENUMERAL_TYPE)
TSE_FUNC_DEF_SIMPLE (BOOLEAN_TYPE)
TSE_FUNC_DEF_SIMPLE (OFFSET_TYPE)
TSE_FUNC_DEF_SIMPLE (COMPLEX_TYPE)

bool
type_structural_equality::_equal_wrapper (tree l, tree r)
{
  tree inner_l = TREE_TYPE (l);
  if (TREE_CODE (inner_l) == ARRAY_TYPE
      && TREE_CODE (TREE_TYPE (inner_l)) == POINTER_TYPE)
    {
      inner_l = TREE_TYPE (inner_l);
    }
  tree inner_r = TREE_TYPE (r);
  if (TREE_CODE (inner_r) == ARRAY_TYPE
      && TREE_CODE (TREE_TYPE (inner_r)) == POINTER_TYPE)
    {
      inner_r = TREE_TYPE (inner_r);
    }
  return _equal (inner_l, inner_r);
}

#define TSE_FUNC_DEF_WRAPPER(code) \
  bool type_structural_equality::_walk_##code (tree l, tree r) \
  { \
    return _equal_wrapper (l, r); \
  }

TSE_FUNC_DEF_WRAPPER (REFERENCE_TYPE)
TSE_FUNC_DEF_WRAPPER (ARRAY_TYPE)
TSE_FUNC_DEF_WRAPPER (POINTER_TYPE)

#define TSE_FUNC_DEF_CONTAINER(code) \
  bool type_structural_equality::_walk_##code (tree l, tree r) \
  { \
    tree field_l = TYPE_FIELDS (l); \
    tree field_r = TYPE_FIELDS (r); \
    bool efield_l = field_l; \
    bool efield_r = field_r; \
    bool still_equal = efield_l == efield_r; \
    if (!still_equal) \
      return still_equal; \
\
    while (field_l && field_r && still_equal) \
      { \
	tree tfield_l = TREE_TYPE (field_l); \
	tree tfield_r = TREE_TYPE (field_r); \
	still_equal &= _equal (tfield_l, tfield_r); \
	field_l = DECL_CHAIN (field_l); \
	field_r = DECL_CHAIN (field_r); \
	efield_l = field_l; \
	efield_r = field_r; \
	still_equal &= efield_l == efield_r; \
      } \
    return still_equal; \
  }

TSE_FUNC_DEF_CONTAINER (RECORD_TYPE)
TSE_FUNC_DEF_CONTAINER (UNION_TYPE)

#define TSE_FUNC_DEF_FUNC(code) \
  bool type_structural_equality::_walk_##code (tree l, tree r) \
  { \
    tree tret_l = TREE_TYPE (l); \
    tree tret_r = TREE_TYPE (r); \
    bool still_equal = _equal (tret_l, tret_r); \
    if (!still_equal) \
      return still_equal; \
\
    tree arg_l = TYPE_ARG_TYPES (l); \
    tree arg_r = TYPE_ARG_TYPES (r); \
    bool earg_l = arg_l; \
    bool earg_r = arg_r; \
    still_equal &= earg_l == earg_r; \
    while (arg_l && arg_r && still_equal) \
      { \
	tree targ_l = TREE_VALUE (arg_l); \
	tree targ_r = TREE_VALUE (arg_r); \
	still_equal &= _equal (targ_l, targ_r); \
	arg_l = TREE_CHAIN (arg_l); \
	arg_r = TREE_CHAIN (arg_r); \
	earg_l = arg_l; \
	earg_r = arg_r; \
	still_equal &= earg_l == earg_r; \
      } \
    return still_equal; \
  }

TSE_FUNC_DEF_FUNC (FUNCTION_TYPE)
TSE_FUNC_DEF_FUNC (METHOD_TYPE)

/* Used for comparing incomplete types.  */
bool
type_incomplete_equality::_equal (tree l, tree r)
{
  bool valid_inputs = l && r;
  if (!valid_inputs)
    return l == r;

  /* Before comparing with identifiers
     make last attempt to compare using main variants.  */
  tree m_l = TYPE_MAIN_VARIANT (l);
  tree m_r = TYPE_MAIN_VARIANT (r);
  gcc_assert (m_l && m_r);
  bool can_compare_structurally = m_l == m_r;
  if (can_compare_structurally)
    return m_l == m_r;

  /* If any of these are incomplete, then we can only compare using
     identifiers...  */
  const bool complete_l = is_complete (l);
  const bool complete_r = is_complete (r);
  can_compare_structurally = complete_l && complete_r;
  if (can_compare_structurally)
    return type_structural_equality::_equal (l, r);

  const std::string n_l = type_stringifier::get_type_identifier (m_l);
  const std::string n_r = type_stringifier::get_type_identifier (m_r);
  // Get the name up to the dot...
  const size_t dot_pos_l = n_l.find (".");
  const size_t dot_pos_r = n_r.find (".");
  const std::string sub_n_l = n_l.substr (0, std::min (dot_pos_l, n_l.size ()));
  const std::string sub_n_r = n_r.substr (0, std::min (dot_pos_r, n_r.size ()));
  return sub_n_l.compare (sub_n_r) == 0;
}

/* Remove non-escaping types and place in escaping types if
 * there is a tree in escaping partition which is equivalent to
 * another tree in non-escaping partition.
 * Perform this until a fixed point is reached.
 */
static void
fix_escaping_types_in_set (tpartitions2_t &types)
{
  bool fixed_point_reached = false;
  type_incomplete_equality structuralEquality;
  do
    {
      auto_vec<tree> fixes2;
      fixed_point_reached = true;
      for (auto i = types.escaping.begin (), e = types.escaping.end (); i != e;
	   ++i)
	{
	  for (auto j = types.non_escaping.begin (),
		    f = types.non_escaping.end ();
	       j != f; ++j)
	    {
	      tree type_esc = *i;
	      gcc_assert (type_esc);
	      tree type_non = *j;
	      gcc_assert (type_non);
	      /* There can be cases where incomplete types are marked as
		 non-escaping and complete types counter parts are marked as
		 escaping.  */
	      const bool equal = structuralEquality.equal (type_esc, type_non);
	      if (!equal)
		continue;

	      fixed_point_reached = false;
	      /* Add incomplete to escaping
		 delete incomplete from non_escaping
		 We shouldn't do that inside our iteration loop.  */
	      fixes2.safe_push (type_non);
	    }
	}

      for (auto escaping_type : fixes2)
	{
	  types.escaping.add (escaping_type);
	  types.non_escaping.remove (escaping_type);
	}
    }
  while (!fixed_point_reached);
}

/* Place variants of old types in map2
 * Map them to the new types.
 * old variant RECORD_TYPE -> new TYPE
 */
void
put_variants_in_map (reorg_record_map2_t &map2)
{
  for (auto i = map2.begin (), e = map2.end (); i != e; ++i)
    {
      tree old_type = (*i).first;
      tree new_type = (*i).second;
      for (tree variant = old_type; variant;
	   variant = TYPE_NEXT_VARIANT (variant))
	map2.put (variant, new_type);
    }
}

/* Put pointers inside map. But do not replace field types. */
void
place_pointers_inside_structs (reorg_record_map2_t &map2)
{
  for (auto i = map2.begin (), e = map2.end (); i != e; ++i)
    {
      tree old_type = (*i).first;
      if (RECORD_TYPE != TREE_CODE (old_type))
	continue;
      for (tree field = TYPE_FIELDS (old_type); field;
	   field = DECL_CHAIN (field))
	{
	  tree old_field_type = TREE_TYPE (field);
	  if (POINTER_TYPE != TREE_CODE (old_field_type))
	    continue;

	  tree old_field_inner_type = TREE_TYPE (old_field_type);
	  tree *new_field_inner_type_p = map2.get (old_field_inner_type);
	  if (!new_field_inner_type_p)
	    continue;

	  tree new_field_inner_type = *new_field_inner_type_p;
	  tree new_ptr = build_pointer_type (new_field_inner_type);
	  map2.put (old_field_type, new_ptr);
	}
    }
}

/* At this stage, the fields in new RECORDs are still pointers
   to old RECRODS. So we need to change that. */
void
replace_pointers_inside_structs (reorg_record_map2_t &map2)
{
  for (auto i = map2.begin (), e = map2.end (); i != e; ++i)
    {
      tree old_type = (*i).first;
      tree new_type = (*i).second;
      if (TREE_CODE (old_type) != RECORD_TYPE)
	continue;

      for (tree field = TYPE_FIELDS (new_type); field;
	   field = DECL_CHAIN (field))
	{
	  tree field_type_old = TREE_TYPE (field);
	  tree *field_type_new_ptr = map2.get (field_type_old);
	  if (!field_type_new_ptr)
	    continue;

	  tree field_type_new = *field_type_new_ptr;
	  TREE_TYPE (field) = field_type_new;
	  relayout_decl (field);
	}
      TYPE_SIZE (new_type) = NULL;
      layout_type (new_type);
    }
}

/* Iterate over TYPE_POINTER_TO (old RECORD) and build a pointer type for new
 * RECORD. Create the following map
 *
 * old RECORD_TYPE * -> new RECORD_TYPE *
 */
void
place_pointers (reorg_record_map2_t &map2)
{
  for (auto i = map2.begin (), e = map2.end (); i != e; ++i)
    {
      tree old_type = (*i).first;
      tree new_type = (*i).second;
      if (RECORD_TYPE != TREE_CODE (old_type))
	continue;
      for (tree variant = old_type; variant;
	   variant = TYPE_NEXT_VARIANT (variant))
	{
	  for (tree t = TYPE_POINTER_TO (variant); t; t = TYPE_NEXT_PTR_TO (t))
	    {
	      tree new_ptr = build_pointer_type (new_type);
	      map2.put (t, new_ptr);
	    }
	}
    }
}

/* Modify the pointer fields in other types */
void
modify_pointers_in_other_types (hash_set<tree> &to_modify,
				reorg_record_map2_t &map2)
{
  for (auto i = to_modify.begin (), e = to_modify.end (); i != e; ++i)
    {
      tree old_type = (*i);
      if (map2.get (old_type))
	continue;
      if (TREE_CODE (old_type) != RECORD_TYPE)
	continue;

      for (tree field = TYPE_FIELDS (old_type); field;
	   field = DECL_CHAIN (field))
	{
	  tree field_type_old = TREE_TYPE (field);
	  tree *field_type_new_ptr = map2.get (field_type_old);
	  if (!field_type_new_ptr)
	    continue;

	  tree field_type_new = *field_type_new_ptr;
	  TREE_TYPE (field) = field_type_new;
	  relayout_decl (field);
	}
    }
}

void
modify_pointer_to_pointer (hash_set<tree> &to_modify, reorg_record_map2_t &map2)
{
  for (auto i = to_modify.begin (), e = to_modify.end (); i != e; ++i)
    {
      tree old_type = (*i);
      if (POINTER_TYPE != TREE_CODE (old_type))
	continue;
      if (POINTER_TYPE != TREE_CODE (TREE_TYPE ((old_type))))
	continue;
      if (RECORD_TYPE != TREE_CODE (TREE_TYPE (TREE_TYPE ((old_type)))))
	continue;

      tree old_inner_type = (TREE_TYPE (TREE_TYPE ((old_type))));
      tree *new_type_ptr = map2.get (old_inner_type);
      if (!new_type_ptr)
	continue;

      for (tree variant = old_type; variant;
	   variant = TYPE_NEXT_VARIANT (variant))
	{
	  TREE_TYPE (old_type) = TYPE_POINTER_TO (*new_type_ptr);
	}
    }
}

void
remove_typed_cache_value_p (reorg_record_map2_t &map2)
{
  for (hash_map<tree, tree>::iterator i = map2.begin (), e = map2.end ();
       i != e; ++i)
    {
      tree o_record = (*i).first;
      tree r_record = (*i).second;
      TYPE_CACHED_VALUES_P (o_record) = false;
      TYPE_CACHED_VALUES_P (r_record) = false;
    }
}

unsigned
ipa_type_escape_analysis_init ()
{
  static bool flag_checked = false;

  if (!flag_ipa_type_escape_analysis)
    return 0;

  in_types.universe.empty ();
  in_types.points_to_record.empty ();
  in_types.complement.empty ();
  in_types.escaping.empty ();
  in_types.non_escaping.empty ();
  if (!flag_ipa_sizeof)
    return 0;
  if (!sizeof_analysis_succeeds)
    return 0;
  cgraph_node *cnode = NULL;
  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (cnode)
    {
      if (!flag_checked
	  && !opt_for_fn (cnode->decl, flag_ipa_type_escape_analysis))
	{
	  flag_ipa_type_escape_analysis = false;
	  return 0;
	}
    }
  flag_checked = true;
  detected_incompatible_syntax = false;
  hash_map<tree, bool> empty;
  partition_types_into_escaping_nonescaping (in_types, &empty);

  auto_vec<tree> types_used_with_sizeof;
  for (auto i = in_types.non_escaping.begin (),
	    e = in_types.non_escaping.end ();
       i != e; ++i)
    {
      tree type = (*i);

      tree mtype = TYPE_MAIN_VARIANT (type);
      for (tree variant = mtype; variant; variant = TYPE_NEXT_VARIANT (variant))
	{
	  if (RECORD_OR_UNION_TYPE_P (variant)
	      && (TYPE_SIZEOF_P (variant) || TYPE_OFFSETOF_P (variant)))
	    types_used_with_sizeof.safe_push (variant);
	}
    }

  for (auto mtype : types_used_with_sizeof)
    {
      for (tree variant = TYPE_MAIN_VARIANT (mtype); variant;
	   variant = TYPE_NEXT_VARIANT (variant))
	{
	  log ("Marking %p  ", variant);
	  if (dump_file)
	    print_generic_expr (dump_file, variant, TDF_NONE);
	  log (" as escaping because used in sizeof\n");
	  in_types.non_escaping.remove (variant);
	  in_types.escaping.add (variant);
	}
    }

  for (auto i = in_types.non_escaping.begin (),
	    e = in_types.non_escaping.end ();
       i != e; ++i)
    {
      tree type = (*i);

      tree mtype = TYPE_MAIN_VARIANT (type);
      for (tree variant = mtype; variant; variant = TYPE_NEXT_VARIANT (variant))
	{
	  if (RECORD_OR_UNION_TYPE_P (variant) && !TYPE_SIZEOF_P (variant)
	      && !TYPE_OFFSETOF_P (variant))
	    {
	      TYPE_NON_ESCAPING_P (variant) = 1;
	      log ("Marking %p  ", variant);
	      if (dump_file)
		print_generic_expr (dump_file, variant, TDF_NONE);
	      log (" as non-escaping\n");
	    }
	}
    }
  return 0;
}

unsigned
ipa_type_escape_analysis_exit (bool keep_flag)
{
  if (!flag_ipa_type_escape_analysis)
    return 0;
  if (!flag_ipa_sizeof)
    return 0;
  if (!sizeof_analysis_succeeds)
    return 0;

  if (!keep_flag)
    {
      for (auto i = in_types.non_escaping.begin (),
		e = in_types.non_escaping.end ();
	   i != e; ++i)
	{
	  tree type = (*i);
	  if (!type)
	    continue;
	  if (RECORD_OR_UNION_TYPE_P (type))
	    {
	      tree mtype = TYPE_MAIN_VARIANT (type);
	      for (tree variant = mtype; variant;
		   variant = TYPE_NEXT_VARIANT (variant))
		{
		  TYPE_NON_ESCAPING_P (variant) = 0;
		  log ("Exitting...");
		  if (dump_file)
		    print_generic_expr (dump_file, type, TDF_NONE);
		  log (" \n");
		}
	    }
	}
    }

  in_types.universe.empty ();
  in_types.points_to_record.empty ();
  in_types.complement.empty ();
  in_types.escaping.empty ();
  in_types.non_escaping.empty ();
  return 0;
}

namespace {
const pass_data pass_data_ipa_type_escape_analysis = {
  SIMPLE_IPA_PASS,
  "type-escape-analysis",
  OPTGROUP_NONE,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0,
  0,
  0,
  0,
};

class pass_ipa_type_escape_analysis : public simple_ipa_opt_pass
{
public:
  pass_ipa_type_escape_analysis (gcc::context *ctx)
    : simple_ipa_opt_pass (pass_data_ipa_type_escape_analysis, ctx)
  {}

  opt_pass *clone () { return new pass_ipa_type_escape_analysis (m_ctxt); }

  virtual unsigned execute (function *)
  {
    ipa_type_escape_analysis_init ();
    return ipa_type_escape_analysis_exit (true);
  }
};
} // anon namespace

simple_ipa_opt_pass *
make_pass_ipa_type_escape_analysis (gcc::context *ctx)
{
  return new pass_ipa_type_escape_analysis (ctx);
}
