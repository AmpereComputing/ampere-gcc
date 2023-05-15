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
#include "gimple.h"
#include "stor-layout.h"
#include "gimple-iterator.h"
#include "ssa.h"
#include "ipa-type-escape-analysis.h"
#include "ipa-dfe.h"
#include "ipa-lto-utils.h"
#include <algorithm>

/* Basically we are creating a specialized GimpleAccesser for FieldReordering.
 * Here instead of marking fields as "READ" or "WRITE", we are marking them as
 * "READ" via pointer arithmetic.  Other "READS" and "WRITES" are ignored since
 * it would be possible to reorder the fields.
 */
class GimpleAccesserFieldReordering : public gimple_accessor
{
public:
  GimpleAccesserFieldReordering (record_field_map4_t &map)
    : gimple_accessor (map) {};

private:
  /* Mark all RHS expressions reachable from S as Read.
     all all LHS expressions reachable from S as Written.  */
  virtual void _walk_pre_gcall (gcall *s);

  /* Mark all RHS expressions reachable from S as Read.
     Mark all LHS expressions reachable from S as Written.  */
  virtual void _walk_pre_gassign (gassign *s);

  /* Mark all all expressions reachable from S as read.  */
  virtual void _walk_pre_greturn (greturn *s);

  /* Mark all expressions reachable from S as read.  */
  virtual void _walk_pre_gcond (gcond *s);

  /* Do we need a glabel? I don't think so...
     But we might need a gswitch.  */
};

/* Compare FIELD_DECL tree based on TYPE_SIZE unit.  */
static bool
compare_FIELD_DECLs_TYPE_SIZE (tree _l, tree _r)
{
  gcc_assert (_l && _r);

  tree l = tree_to_tree (_l);
  tree r = tree_to_tree (_r);

  const enum tree_code code_l = TREE_CODE (l);
  const enum tree_code code_r = TREE_CODE (r);
  const bool is_left_field_decl = code_l == FIELD_DECL;
  const bool is_right_field_decl = code_r == FIELD_DECL;
  bool is_valid = is_left_field_decl && is_right_field_decl;
  gcc_assert (is_valid);

  tree type_l = TREE_TYPE (l);
  tree type_r = TREE_TYPE (r);
  const bool is_type_l = TYPE_P (type_l);
  const bool is_type_r = TYPE_P (type_r);
  is_valid = is_type_l && is_type_r;
  gcc_assert (is_valid);

  tree size_l = TYPE_SIZE_UNIT (type_l);
  tree size_r = TYPE_SIZE_UNIT (type_r);
  is_valid = size_l && size_r;
  gcc_assert (is_valid);

  int int_l = tree_to_shwi (size_l);
  int int_r = tree_to_shwi (size_r);
  const bool is_gte_l = int_l >= 0;
  const bool is_gte_r = int_r >= 0;
  is_valid = is_gte_l && is_gte_r;
  gcc_assert (is_valid);

  return int_l > int_r;
}

/* Mark all as empty (a.k.a. we can sort) */
void
GimpleAccesserFieldReordering::_walk_pre_gassign (gassign *s)
{
  /* There seems to be quite a bit of code duplication here...  */
  const enum gimple_rhs_class code = gimple_assign_rhs_class (s);
  switch (code)
    {
    case GIMPLE_TERNARY_RHS:
      {
	tree rhs3 = gimple_assign_rhs3 (s);
	gcc_assert (rhs3);
	_expr_accessor.update (rhs3, Empty);
      }
    /* fall-through.  */
    case GIMPLE_BINARY_RHS:
      {
	tree rhs2 = gimple_assign_rhs2 (s);
	gcc_assert (rhs2);
	_expr_accessor.update (rhs2, Empty);
      }
    /* fall-through.  */
    case GIMPLE_UNARY_RHS:
    case GIMPLE_SINGLE_RHS:
      {
	tree rhs1 = gimple_assign_rhs1 (s);
	_expr_accessor.update (rhs1, Empty);
	tree lhs = gimple_assign_lhs (s);
	if (!lhs)
	  break;
	_expr_accessor.update (lhs, Empty);
	break;
      }
    default:
      gcc_unreachable ();
      break;
    }
}

/* Mark all as empty (a.k.a. we can sort) */
void
GimpleAccesserFieldReordering::_walk_pre_gcall (gcall *s)
{
  unsigned n = gimple_call_num_args (s);
  for (unsigned i = 0; i < n; i++)
    {
      tree a = gimple_call_arg (s, i);
      gcc_assert (a);
      _expr_accessor.update (a, Empty);
    }

  tree lhs = gimple_call_lhs (s);
  if (!lhs)
    return;
  _expr_accessor.update (lhs, Empty);
}

/* Mark all as empty (a.k.a. we can sort) */
void
GimpleAccesserFieldReordering::_walk_pre_greturn (greturn *s)
{
  tree val = gimple_return_retval (s);
  if (!val)
    return;
  _expr_accessor.update (val, Empty);
}

/* Mark all as empty (a.k.a. we can sort) */
void
GimpleAccesserFieldReordering::_walk_pre_gcond (gcond *s)
{
  tree lhs = gimple_cond_lhs (s);
  tree rhs = gimple_cond_rhs (s);
  gcc_assert (lhs && rhs);
  _expr_accessor.update (lhs, Empty);
  _expr_accessor.update (rhs, Empty);
}

/* Top level function.  */
static unsigned int
lto_fr_execute ();

static void
find_fields_accessed (record_field_map4_t &f);

namespace {
const pass_data pass_data_ipa_field_reorder = {
  SIMPLE_IPA_PASS,
  "field-reorder",
  OPTGROUP_NONE,
  TV_NONE,
  (PROP_cfg | PROP_ssa),
  0,
  0,
  0,
  0,
};

class pass_ipa_field_reorder : public simple_ipa_opt_pass
{
public:
  pass_ipa_field_reorder (gcc::context *ctx)
    : simple_ipa_opt_pass (pass_data_ipa_field_reorder, ctx)
  {}

  virtual bool gate (function *)
  {
    return flag_ipa_field_reorder && lang_c_p ();
  }

  virtual unsigned execute (function *) { return lto_fr_execute (); }
};
} /* Namespace.  */

static void
find_fields_accessed (record_field_map4_t &r)
{
  GimpleAccesserFieldReordering accesser (r);
  accesser.walk ();
}

const char *
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

/* Changes the records in record_field_offset_map2.
 * Input: record_field_offset_map2
 * which is a (RECORD_TYPE -> { unsigned integers {)
 * The RECORD_TYPE is the record that can change.
 * The { unsigned integers } are offsets to fields
 * which can be reordered.
 * Output:
 * map2
 * old RECORD_TYPE -> new RECORD_TYPE
 * field_map2
 * old FIELD_DECL -> new FIELD_DECL
 */
static void
change_record_types (record_field_offset_map4_t &record_field_offset_map2,
		     reorg_record_map2_t &map2, reorg_field_map2_t &field_map2)
{
  hash_set<tree> disallow;
  for (auto i = record_field_offset_map2.begin (),
	    e = record_field_offset_map2.end ();
       i != e; ++i)
    {
      tree record = (*i).first;
      if (TYPE_MAIN_VARIANT (record) != record)
	continue;

      field_offsets2_t *set = (*i).second;
      bool is_disallowed = false;
      for (tree field = TYPE_FIELDS (record); field; field = DECL_CHAIN (field))
	{
	  unsigned f_byte_offset = tree_to_uhwi (DECL_FIELD_OFFSET (field));
	  unsigned f_bit_offset = tree_to_uhwi (DECL_FIELD_BIT_OFFSET (field));
	  unsigned f_offset = 8 * f_byte_offset + f_bit_offset;
	  is_disallowed |= !set->contains (f_offset);
	}
      if (is_disallowed)
	disallow.add (record);
    }

  for (auto i = record_field_offset_map2.begin (),
	    e = record_field_offset_map2.end ();
       i != e; ++i)
    {
      tree record = (*i).first;
      if (TYPE_MAIN_VARIANT (record) != record)
	continue;
      if (disallow.contains (record))
	continue;

      auto_vec<tree> offsets_unsorted;
      auto_vec<tree> offsets_sorted;
      for (tree field = TYPE_FIELDS (record); field; field = DECL_CHAIN (field))
	{
	  offsets_unsorted.safe_push (field);
	  offsets_sorted.safe_push (field);
	}

      std::sort (offsets_sorted.begin (), offsets_sorted.end (),
		 compare_FIELD_DECLs_TYPE_SIZE);

      auto j = offsets_unsorted.begin ();
      bool different = false;
      for (auto i = offsets_sorted.begin (), e = offsets_sorted.end (); i != e;
	   ++i)
	{
	  different |= (*i) != (*j);
	  ++j;
	}

      if (!different)
	{
	  disallow.add (record);
	}
    }

  for (auto i = record_field_offset_map2.begin (),
	    e = record_field_offset_map2.end ();
       i != e; ++i)
    {
      tree record = (*i).first;
      if (TYPE_MAIN_VARIANT (record) != record)
	continue;
      if (disallow.contains (record))
	continue;

      tree new_record = build_distinct_type_copy (record);
      tree old_fields = TYPE_FIELDS (record);
      tree new_fields = copy_list (old_fields);

      TYPE_FIELDS (new_record) = new_fields;

      for (tree variant = record; variant;
	   variant = TYPE_NEXT_VARIANT (variant))
	{
	  tree new_field = TYPE_FIELDS (new_record);
	  for (tree field = TYPE_FIELDS (variant); field;
	       field = DECL_CHAIN (field))
	    {
	      field_map2.put (field, std::make_pair (new_field, false));
	      new_field = DECL_CHAIN (new_field);
	    }
	}

      auto_vec<tree> field_list;
      for (tree field = TYPE_FIELDS (new_record); field;
	   field = DECL_CHAIN (field))
	field_list.safe_push (field);

      std::sort (field_list.begin (), field_list.end (),
		 compare_FIELD_DECLs_TYPE_SIZE);

      // Now that they are in the field_list order, we want to order the
      // the fields...
      tree prev_field = NULL;
      for (auto field : field_list)
	{
	  if (!prev_field)
	    TYPE_FIELDS (new_record) = field;
	  else
	    DECL_CHAIN (prev_field) = field;
	  prev_field = field;
	}

      DECL_CHAIN (prev_field) = NULL;

      for (tree field = TYPE_FIELDS (new_record); field;
	   field = DECL_CHAIN (field))
	{
	  relayout_decl (field);
	  DECL_CONTEXT (field) = new_record;
	}

      TYPE_SIZE (new_record) = NULL;
      TYPE_ALIAS_SET (new_record) = -1;
      const char *tname = get_type_name (new_record);
      TYPE_NAME (new_record)
	= get_identifier (concat (tname, ".reorder", NULL));
      layout_type (new_record);
      TYPE_ORIGINAL (new_record) = record;
      map2.put (record, new_record);
    }
}

/* record_field_offset_map holds information on which FIELD_DECLs might be
 * resorted from RECORD_TYPEs.  to_modify holds trees which point to a
 * RECORD_TYPE which might be resorted.  From these two inputs, we need to
 * compute two maps:
 * * a map of RECORD_TYPE (old) -> RECORD_TYPE (new)
 * * a map of FIELD_DECL (old) -> FIELD_DECL (new)

 * The first maps trees in to_modify (which point to RECORD_TYPEs (old)) to
 * trees which have been modified to point to the new definition of
 * RECORD_TYPEs.

 * The second maps old FIELD_DECLs trees to the new FIELD_DECLs.
 */
static reorg_maps_t
get_reordered_field_maps (record_field_offset_map4_t &record_field_offset_map2,
			  hash_set<tree> &to_modify, reorg_record_map2_t &map2,
			  reorg_field_map2_t &field_map2)
{
  change_record_types (record_field_offset_map2, map2, field_map2);
  put_variants_in_map (map2);
  place_pointers_inside_structs (map2);
  place_pointers (map2);
  replace_pointers_inside_structs (map2);
  modify_pointers_in_other_types (to_modify, map2);
  modify_pointer_to_pointer (to_modify, map2);
  remove_typed_cache_value_p (map2);

  /* TODO: change this to return the GCC types...  */
  return std::make_pair (&map2, &field_map2);
}

/* Top level function.  */
static unsigned int
lto_fr_execute ()
{
  ipa_type_escape_analysis_init ();
  if (detected_incompatible_syntax)
    {
      ipa_type_escape_analysis_exit ();
      return 0;
    }

  record_field_map4_t record_field_map;
  find_fields_accessed (record_field_map);
  record_field_offset_map4_t record_field_offset_map;
  obtain_nonescaping_unaccessed_fields (tea_types, record_field_map, 0,
					record_field_offset_map);

  if (detected_incompatible_syntax || record_field_offset_map.is_empty ())
    {
      ipa_type_escape_analysis_exit ();
      return 0;
    }

  /* Prepare for transformation.  */
  hash_set<tree> to_modify;

  get_all_types_pointing_to (record_field_offset_map, tea_types, to_modify);

  reorg_record_map2_t a;
  reorg_field_map2_t b;
  reorg_maps_t replacements
    = get_reordered_field_maps (record_field_offset_map, to_modify, a, b);
  reorg_record_map2_t *map = replacements.first;
  reorg_field_map2_t *field_map = replacements.second;
  gcc_assert (map && field_map);
  substitute_types_in_program (*map, *field_map, false);

  ipa_type_escape_analysis_exit ();
  return 0;
}

simple_ipa_opt_pass *
make_pass_ipa_field_reorder (gcc::context *ctx)
{
  return new pass_ipa_field_reorder (ctx);
}
