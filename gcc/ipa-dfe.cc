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

/* Collect all types which point to a specific type set.  */
class specific_type_collector : public type_walker
{
public:
  /* C is the set of types that are to be looked for.  */
  specific_type_collector (hash_set<tree> *c2) : _collect_these_types2 (c2)
    {};

  /* Get final result of all types which point to types in C.  */
  hash_set<tree> get_set2 ();

private:
  hash_set<tree> *_collect_these_types2;

  /* Working set that holds final result.  */
  hash_set<tree> to_return2;

  /* Sets which reach current subtype.  */
  hash_set<tree> path2;

  /* Push or pop from path.  */
  virtual void _walk_ARRAY_TYPE_pre (tree t);
  virtual void _walk_ARRAY_TYPE_post (tree t);
  virtual void _walk_UNION_TYPE_pre (tree t);
  virtual void _walk_UNION_TYPE_post (tree t);
  virtual void _walk_POINTER_TYPE_pre (tree t);
  virtual void _walk_POINTER_TYPE_post (tree t);

  /* If in input, place all parent types in to_return.  */
  virtual void _walk_RECORD_TYPE_pre (tree t);
  virtual void _walk_RECORD_TYPE_post (tree t);
};

/* Modify expressions to match the new types.
 * Substitute old types with new types.
 * Handle pointer arithmetic.
 * Delete statements if needed.
 */
class expr_type_rewriter : public expr_walker
{
public:
  expr_type_rewriter (reorg_record_map2_t &map, reorg_field_map2_t &map2,
		      bool can_delete)
    : _delete (false), _can_delete (can_delete), _map2 (map), _fields2 (map2)
  {
    /* Create an inverse map new RECORD_TYPE -> old RECORD_TYPE.  */
    for (auto i = map.begin (), e = map.end (); i != e; ++i)
      {
	tree original = (*i).first;
	tree modified = (*i).second;
	_imap2.put (modified, original);
      }
  };

  ~expr_type_rewriter ()
  {};

  /* Handle pointer arithmetic with constants.  */
  void handle_pointer_arithmetic_constants (gimple *s, tree p, tree i);

  /* Handle pointer POINTER_DIFF_EXPR.  */
  void handle_pointer_arithmetic_diff (gimple *s, tree p);

  /* Handle POINTER_PLUS_EXPR.  */
  void handle_pointer_arithmetic_nonconstant (gimple *s, tree p, tree i, bool);

  /* Find out if this type will be modified.  */
  bool is_interesting_type (tree);

  /* Delete statement.  */
  bool delete_statement ();
  bool _delete;
  bool _can_delete;

private:
  /* Old RECORD_TYPE -> new RECORD_TYPE.  */
  reorg_record_map2_t &_map2;

  /* Old FIELD_DECL -> new FIELD_DECL.  */
  reorg_field_map2_t &_fields2;

  /* New RECORD_TYPE -> old RECORD_TYPE.  */
  hash_map<tree, tree> _imap2;

  void _walk_post (tree e);

  /* Substitute types and create new offset.  */
  void _walk_MEM_REF_post (tree e);

  /* Substitute fields referred.  */
  void _walk_COMPONENT_REF_post (tree e);

  /* Relayout parameters which are rewritten.  */
  void _walk_PARM_DECL_post (tree e);

  /* Substitute return type.  */
  void _walk_FUNCTION_DECL_post (tree e);
};

/* Walk all gimple and substitute types.  */
class gimple_type_rewriter : public gimple_walker
{
public:
  gimple_type_rewriter (reorg_record_map2_t &map, reorg_field_map2_t &map2,
			bool can_delete)
    : exprTypeRewriter (map, map2, can_delete)
    , _map (map)
  {};

  void _rewrite_function_decl ();

private:
  /* Substitute types in expressions.  */
  expr_type_rewriter exprTypeRewriter;
  reorg_record_map2_t &_map;

  /* Handle pointer arithmetic.  */
  void handle_pointer_arithmetic (gimple *s);

  /* Rewrite types in these statements.  */
  virtual void _walk_pre_gphi (gphi *);
  virtual void _walk_pre_tree (tree);
  virtual void _walk_pre_greturn (greturn *s);
  virtual void _walk_pre_gassign (gassign *s);
  virtual void _walk_pre_gcall (gcall *s);
};

/* Compute the replacement types.  */
static reorg_maps_t
get_types_replacement (record_field_offset_map4_t &record_field_offset_map,
		       hash_set<tree> &to_modify, reorg_record_map2_t &,
		       reorg_field_map2_t &);

static void
lto_dead_field_elimination ();
static unsigned int
lto_dfe_execute ();

/* Find which fields are accessed.  */
static void
find_fields_accessed (record_field_map4_t &f);

/* Iterate over all gimple bodies and find out
 * which fields are accessed for all RECORD_TYPE
 * types.
 */
static void
find_fields_accessed (record_field_map4_t &record_field_map)
{
  gimple_accessor accesser (record_field_map);
  accesser.walk ();
}

/* Find all non_escaping types which point to RECORD_TYPEs in
 * record_field_offset_map.
 */
void
get_all_types_pointing_to (record_field_offset_map4_t &record_field_offset_map2,
			   tpartitions2_t casting, hash_set<tree> &to_modify2)
{
  tset2_t &non_escaping = casting.non_escaping;

  hash_set<tree> specific_types2;

  /* Here we are just placing the types of interest in a set.  */
  for (hash_map<tree, field_offsets2_t *>::iterator i
       = record_field_offset_map2.begin (),
       e = record_field_offset_map2.end ();
       i != e; ++i)
    {
      tree record = (*i).first;
      specific_types2.add (record);
    }

  specific_type_collector specifier (&specific_types2);

  /* SpecificTypeCollector will collect all types which point to the types in
     the set.  */
  for (auto i = non_escaping.begin (), e = non_escaping.end (); i != e; ++i)
    {
      tree type = *i;
      if (is_incomplete ((type)))
	continue;
      specifier.walk (type);
    }

  /* These are all the types which need modifications.  */
  hash_set<tree> to_modify = specifier.get_set2 ();
  for (hash_set<tree>::iterator i = to_modify.begin (), e = to_modify.end ();
       i != e; ++i)
    {
      to_modify2.add (*i);
    }
}

/* Changes the records in record_field_offset_map2.
 * Input: record_field_offset_map2
 * which is a (RECORD_TYPE -> { unsigned integers {)
 * The RECORD_TYPE is the record that can change.
 * The { unsigned integers } are offsets to fields
 * which can be deleted.
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
  for (auto i = record_field_offset_map2.begin (),
	    e = record_field_offset_map2.end ();
       i != e; ++i)
    {
      tree record = (*i).first;
      if (TYPE_MAIN_VARIANT (record) != record)
	continue;

      field_offsets2_t *field_offsets = (*i).second;
      tree new_record = build_distinct_type_copy (record);
      tree prev_field = NULL_TREE;

      TYPE_FIELDS (new_record) = copy_list (TYPE_FIELDS (record));
      for (tree variant = record; variant;
	   variant = TYPE_NEXT_VARIANT (variant))
	{
	  tree new_field = TYPE_FIELDS (new_record);
	  for (tree field = TYPE_FIELDS (variant); field;
	       field = DECL_CHAIN (field))
	    {
	      unsigned f_byte_offset = tree_to_uhwi (DECL_FIELD_OFFSET (field));
	      unsigned f_bit_offset
		= tree_to_uhwi (DECL_FIELD_BIT_OFFSET (field));
	      unsigned f_offset = 8 * f_byte_offset + f_bit_offset;
	      bool to_be_deleted = false;
	      for (auto j = field_offsets->begin (), f = field_offsets->end ();
		   j != f; ++j)
		{
		  to_be_deleted |= f_offset == (unsigned) *j;
		}
	      field_map2.put (field, std::make_pair (new_field, to_be_deleted));
	      new_field = DECL_CHAIN (new_field);
	    }
	}

      for (tree field = TYPE_FIELDS (new_record); field;
	   field = DECL_CHAIN (field))
	{
	  unsigned f_byte_offset = tree_to_uhwi (DECL_FIELD_OFFSET (field));
	  unsigned f_bit_offset = tree_to_uhwi (DECL_FIELD_BIT_OFFSET (field));
	  unsigned f_offset = 8 * f_byte_offset + f_bit_offset;
	  bool to_be_deleted = false;

	  for (auto j = field_offsets->begin (), f = field_offsets->end ();
	       j != f; ++j)
	    {
	      to_be_deleted |= f_offset == (unsigned) *j;
	    }

	  if (to_be_deleted)
	    {
	      if (!prev_field)
		{
		  TYPE_FIELDS (new_record) = DECL_CHAIN (field);
		  continue;
		}
	      else if (!DECL_CHAIN (field) && prev_field)
		{
		  DECL_CHAIN (prev_field) = NULL_TREE;
		  continue;
		}
	      else if (DECL_CHAIN (field) && prev_field)
		{
		  DECL_CHAIN (prev_field) = DECL_CHAIN (field);
		  continue;
		}
	      gcc_unreachable ();
	    }
	  prev_field = field;
	}

      for (tree field = TYPE_FIELDS (new_record); field;
	   field = DECL_CHAIN (field))
	{
	  relayout_decl (field);
	  DECL_CONTEXT (field) = new_record;
	}

      TYPE_SIZE (new_record) = NULL;
      TYPE_ALIAS_SET (new_record) = -1;
      const char *tname = get_type_name (new_record);
      TYPE_NAME (new_record) = get_identifier (concat (tname, ".dfe", NULL));
      layout_type (new_record);
      TYPE_ORIGINAL (new_record) = record;
      map2.put (record, new_record);
    }
}

/* record_field_offset_map holds information on which FIELD_DECLs might be
 * deleted from RECORD_TYPEs.  to_modify holds trees which point to a
 * RECORD_TYPE which might be deleted.  From these two inputs, we need to
 * compute two maps:
 * * a map of RECORD_TYPE (old) -> RECORD_TYPE (new)
 * * a map of FIELD_DECL (old) -> FIELD_DECL (new)

 * The first maps trees in to_modify (which point to RECORD_TYPEs (old)) to
 * trees which have been modified to point to the new definition of
 * RECORD_TYPEs.

 * The second maps old FIELD_DECLs trees to the new FIELD_DECLs.
 */
static reorg_maps_t
get_types_replacement (record_field_offset_map4_t &record_field_offset_map2,
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

  /* TODO: Ok, we will need to change this some time...  */
  return std::make_pair (&map2, &field_map2);
}

/* Walk the gimple program and substitute
 * * the trees in map with map's values.
 * * the trees in field_map with field_map's values.
 */
void
substitute_types_in_program (reorg_record_map2_t &map,
			     reorg_field_map2_t &field_map, bool _delete)
{
  gimple_type_rewriter rewriter (map, field_map, _delete);
  rewriter.walk ();
  rewriter._rewrite_function_decl ();
}

/* Return a set of trees which point to the set of trees
 * that can be modified.
 */
hash_set<tree>
specific_type_collector::get_set2 ()
{
  return to_return2;
}

void
specific_type_collector::_walk_POINTER_TYPE_pre (tree t)
{
  path2.add (t);
}

void
specific_type_collector::_walk_POINTER_TYPE_post (tree t)
{
  path2.remove (t);
}

void
specific_type_collector::_walk_ARRAY_TYPE_pre (tree t)
{
  path2.add (t);
}

void
specific_type_collector::_walk_ARRAY_TYPE_post (tree t)
{
  path2.remove (t);
}

void
specific_type_collector::_walk_UNION_TYPE_pre (tree t)
{
  path2.add (t);
}

void
specific_type_collector::_walk_UNION_TYPE_post (tree t)
{
  path2.remove (t);
}

/* If we find a RECORD_TYPE which is of interest, place
 * all types which we are currently keeping track of in TO_RETURN.
 */
void
specific_type_collector::_walk_RECORD_TYPE_pre (tree t)
{
  const bool in_set = _collect_these_types2->contains (t);
  const bool must_collect = in_set;
  path2.add (t);
  if (!must_collect)
    return;

  for (hash_set<tree>::iterator i = path2.begin (), e = path2.end (); i != e;
       ++i)
    {
      tree type = *i;
      to_return2.add (type);
    }
}

void
specific_type_collector::_walk_RECORD_TYPE_post (tree t)
{
  path2.remove (t);
}

/* Relayout parameters.  */
void
expr_type_rewriter::_walk_PARM_DECL_post (tree t)
{
  tree temp = tree_to_tree (t);
  tree ttemp = TREE_TYPE (temp);
  const bool is_interesting = is_interesting_type (ttemp);

  if (!is_interesting)
    return;
  relayout_decl (temp);
}

/* Update return types.  */
void
expr_type_rewriter::_walk_FUNCTION_DECL_post (tree t)
{
  tree fn_type = TREE_TYPE (t);
  /* This is saying that we cannot have indirect functions
     such as the ones found in structs.  */
  gcc_assert (fn_type);
  tree ret_type = TREE_TYPE (fn_type);
  if (!ret_type)
    return;

  /* WARNING: You cannot use is interesting here because you haven't
     changed the return type
     This is because the return type is not an expression.
     Therefore it is awkward to do this in the expr-walker...
     const bool is_interesting = is_interesting_type (ret_type);
     Instead use the following map.  */
  const bool is_interesting = _map2.get (ret_type);
  if (!is_interesting)
    return;

  tree r_t = *_map2.get (ret_type);
  TREE_TYPE (fn_type) = r_t;
}

/* Rewrite MEM_REF operand 1.  */
void
expr_type_rewriter::_walk_MEM_REF_post (tree e)
{
  tree op0 = TREE_OPERAND (e, 0);
  tree t2 = TREE_TYPE (op0);
  const bool in_map2 = _map2.get (t2);

  if (in_map2)
    {
      tree r_t = *_map2.get (t2);
      tree _e = tree_to_tree (op0);
      TREE_TYPE (_e) = r_t;
    }

  /* The second operand is a pointer constant.
     Its type specifying the type used for type based alias analysis.  */
  tree op1 = TREE_OPERAND (e, 1);
  gcc_assert (TREE_CODE (op1) == INTEGER_CST);

  tree t = TREE_TYPE (op1);
  const bool already_rewritten = is_interesting_type (t);

  /* This is where we do the transformation.  */
  if (!already_rewritten)
    return;

  tree old_type = *_imap2.get (t);
  assert_is_type (old_type, POINTER_TYPE);
  tree old_base_type = TREE_TYPE (old_type);
  tree old_type_size_tree = TYPE_SIZE_UNIT (old_base_type);
  int old_type_size_int = tree_to_shwi (old_type_size_tree);

  tree reorg_type = t;
  assert_is_type (reorg_type, POINTER_TYPE);
  tree reorg_base_type = TREE_TYPE (reorg_type);
  tree reorg_type_size_tree = TYPE_SIZE_UNIT (reorg_base_type);
  int reorg_type_size_int = tree_to_shwi (reorg_type_size_tree);

  /* Let's find out what is the previous offset.  */
  int old_offset = tree_to_uhwi (op1);
  int remainder = old_offset % old_type_size_int;

  int new_offset
    = old_offset / old_type_size_int * reorg_type_size_int + remainder;

  tree new_offset_tree = build_int_cst (TREE_TYPE (op1), new_offset);
  tree _e = tree_to_tree (e);
  TREE_OPERAND (_e, 1) = new_offset_tree;
}

/* TODO:
   Change name of this method...  */
bool
expr_type_rewriter::is_interesting_type (tree t)
{
  const bool in_imap2 = _imap2.get (t);
  bool interesting = in_imap2;
  if (!interesting)
    return false;

  tree const_possibly_copy = *_imap2.get (t);
  tree possibly_copy = tree_to_tree (const_possibly_copy);
  const bool is_copy = possibly_copy == t;
  interesting = !is_copy;
  if (!interesting)
    return false;

  /* Let's just do a quick sanity check.  */
  /*
  tree interesting_type = t;
  bool has_valid_suffix
    = strstr (type_stringifier::get_type_identifier (interesting_type).c_str (),
	      ".reorg");
  has_valid_suffix |= (bool)
    strstr (type_stringifier::get_type_identifier (interesting_type).c_str (),
	    ".reorder");
  gcc_assert (has_valid_suffix);
  */
  return true;
}

/* Rewrite POINTER_DIFF expr.  */
void
expr_type_rewriter::handle_pointer_arithmetic_diff (gimple *s, tree op_0)
{
  /* lhs = op0 - op1 // <-- we are here
     <SNIP>
     var = lhs / [ex] old_struct_size // <-- we want to be here

     Therefore:
     Let's explore the uses of lhs.  */
  tree lhs = gimple_assign_lhs (s);

  tree reorg_type = TREE_TYPE (op_0);
  const enum tree_code code = TREE_CODE (reorg_type);
  const bool is_pointer = POINTER_TYPE == code;
  const bool is_array = ARRAY_TYPE == code;
  const bool is_valid_input = is_pointer != is_array;
  gcc_assert (is_valid_input);

  tree inner_reorg_type = TREE_TYPE (reorg_type);
  gcc_assert (inner_reorg_type);
  tree reorg_type_size_tree = TYPE_SIZE_UNIT (inner_reorg_type);
  int reorg_type_size_int = tree_to_shwi (reorg_type_size_tree);

  tree const_old_type = *_imap2.get (reorg_type);
  tree old_type = tree_to_tree (const_old_type);
  tree inner_old_type = TREE_TYPE (old_type);
  gcc_assert (old_type);
  tree old_type_size_tree = TYPE_SIZE_UNIT (inner_old_type);
  int old_type_size_int = tree_to_shwi (old_type_size_tree);

  gimple *stmt;
  imm_use_iterator iterator;
  FOR_EACH_IMM_USE_STMT (stmt, iterator, lhs)
    {
      /* stmt is a use of lhs
	gimple_expr_code is only valid for non-debug statements.  */
      bool is_debug = is_gimple_debug (stmt);
      if (is_debug)
	continue;

      enum tree_code code = gimple_expr_code (stmt);
      bool is_exact_div = code == EXACT_DIV_EXPR;
      if (!is_exact_div)
	continue;

      tree divisor = gimple_op (stmt, 2);
      enum tree_code divisor_code = TREE_CODE (divisor);
      bool is_constant = divisor_code == INTEGER_CST;
      if (!is_constant)
	continue;

      int divisor_int = tree_to_shwi (divisor);
      bool is_same_size = divisor_int == old_type_size_int;
      if (!is_same_size)
	continue;

      tree new_integer_cst_tree
	= build_int_cst (TREE_TYPE (divisor), reorg_type_size_int);
      gimple_set_op (stmt, 2, new_integer_cst_tree);
    }
}

/* Rewrite pointer arithmetic for non constant cases.  */
void
expr_type_rewriter::handle_pointer_arithmetic_nonconstant (gimple *s, tree op_0,
							   tree op_1,
							   bool is_pointer_plus)
{
  if (!is_pointer_plus)
    {
      handle_pointer_arithmetic_diff (s, op_0);
      return;
    }
  /*   _1 = _0 * 72
   *   <SNIP>
   *   _2 = _1 + CONSTANT;
   *   <SNIP>
   *   _3 = &array + _2;  < -- this is where we are
   */
  tree new_type = TREE_TYPE (gimple_assign_lhs (s));

  gimple *def_for_variable = SSA_NAME_DEF_STMT (op_1);
  /* It is possible that we are in a negation statement...
     Example:
	_2 = _1 * 72;
       <SNIP>
	_3 = -_2;  < -- def_for_variable **might** be this stmt.
       <SNIP>
       _4 = &array + _3;

     Let's find out how many operands we have.  */
  unsigned num_operands = gimple_num_ops (def_for_variable);
  /* Here operands is kind of a minomer.
     operand 0 is the lhs
     operand 1 is the rhs
     I.e. lhs = (unary_operator) rhs; */
  bool get_another_definition = num_operands == 2;
  tree possibly_not_needed
    = get_another_definition ? gimple_op (def_for_variable, 1) : NULL;
  def_for_variable = get_another_definition
		       ? SSA_NAME_DEF_STMT (possibly_not_needed)
		       : def_for_variable;

  /* Example:
       _2 = _1 * 72; <-- Now we are here...
       <SNIP>
       _3 = -_2;
       <SNIP>
       _4 = &array + _3; */

  enum gimple_code gcode = gimple_code (def_for_variable);
  switch (gcode)
    {
      /* TODO: FIXME:
	 This is unsafe, waiting for the sizeof solution.  */
    case GIMPLE_COND:
    case GIMPLE_CALL:
    case GIMPLE_ASSIGN:
      break;
    default:
      /* TODO: FIXME:
	 Can other cases land here? If so,
	 maybe use an assertion.  */
      return;
      break;
    }
  enum tree_code code = gimple_expr_code (def_for_variable);
  const bool is_plus_expr = PLUS_EXPR == code;

  /* op_0 is the variable
     That means that the reorg_type is
     But the truth is that op_0 might not have the correct type.
     So the correct type is the one used for the LHS.
     Which was obtained above.  */
  tree reorg_type_tree = new_type;
  tree reorg_inner_type = TREE_TYPE (reorg_type_tree);
  tree reorg_type_size_tree = TYPE_SIZE_UNIT (reorg_inner_type);
  int reorg_type_size_int = tree_to_shwi (reorg_type_size_tree);
  /* That means that the old type is.  */
  tree const_old_type_tree = *_imap2.get (reorg_type_tree);

  tree old_type_tree = tree_to_tree (const_old_type_tree);
  tree old_inner_type = TREE_TYPE (old_type_tree);
  tree old_type_size_tree = TYPE_SIZE_UNIT (old_inner_type);
  int old_type_size_int = tree_to_shwi (old_type_size_tree);
  log ("imap says...old_size = %d -> new_size = %d\n", old_type_size_int,
       reorg_type_size_int);

  if (is_plus_expr)
    {
      /* If we are here it is because we are adding an offset.
	 It is usually whenever we do somehting like
	   _2 = _1 + CONSTANT; <-- to change
	   _3 = &array + _2; */
      tree constant_plus = gimple_op (def_for_variable, 2);
      assert_is_type (constant_plus, INTEGER_CST);

      int old_integer_cst_int = tree_to_uhwi (constant_plus);
      int modulo = old_integer_cst_int % old_type_size_int;
      int new_integer_cst_int
	= old_integer_cst_int / old_type_size_int * reorg_type_size_int
	  + modulo;

      tree new_integer_cst_tree
	= build_int_cst (TREE_TYPE (constant_plus), new_integer_cst_int);
      gimple_set_op (def_for_variable, 2, new_integer_cst_tree);

      tree variable = gimple_op (def_for_variable, 1);
      def_for_variable = SSA_NAME_DEF_STMT (variable);
      num_operands = gimple_num_ops (def_for_variable);
      get_another_definition = num_operands == 2;
      def_for_variable = get_another_definition
			   ? SSA_NAME_DEF_STMT (gimple_op (def_for_variable, 1))
			   : def_for_variable;
      code = gimple_expr_code (def_for_variable);
    }

  if (code == MULT_EXPR)
    {
      tree op_1_earlier = gimple_assign_rhs2 (def_for_variable);

      /* We should be able to just call the constant implementation
	 handle_pointer_arithmetic_constants (def_for_variable, op_0, op_1);
	 However...
	 these variables no longer hold the type needed for them to change
	 correctly so, let's do it from here...  */

      assert_is_type (op_1_earlier, INTEGER_CST);

      tree old_integer_cst_tree = op_1_earlier;
      int old_integer_cst_int = tree_to_uhwi (old_integer_cst_tree);

      int offset = old_integer_cst_int % old_type_size_int;
      int new_integer_cst_int
	= old_integer_cst_int / old_type_size_int * reorg_type_size_int
	  + offset;

      tree new_integer_cst_tree
	= build_int_cst (TREE_TYPE (old_integer_cst_tree), new_integer_cst_int);
      gimple_set_op (def_for_variable, 2, new_integer_cst_tree);
    }
}

void
expr_type_rewriter::handle_pointer_arithmetic_constants (gimple *s, tree p,
							 tree i)
{
  /* So, because we have already changed the type
     tree p will either be the original type
     if we do not need to modify this expression
     We know if we have an original type
     when we don't have a type in our map.  */
  tree possibly_reorged_type = TREE_TYPE (p);
  bool is_interesting_case = is_interesting_type (possibly_reorged_type);
  if (!is_interesting_case)
    return;

  /* This is the type of the variable.  */
  tree reorg_type = possibly_reorged_type;
  tree original_type = *_imap2.get (reorg_type);
  /* If we are here, that means that our type has the ".reorg" suffix.
     Let's add a sanity check.  */
  /*
  bool has_suffix
    = strstr (type_stringifier::get_type_identifier (reorg_type).c_str (),
	      ".reorg");
  has_suffix |= (bool) strstr (
    type_stringifier::get_type_identifier (reorg_type).c_str (), ".reorder");
  bool is_valid_input = has_suffix;
  gcc_assert (is_valid_input);
  */

  /* We need to know what size is the previous original type.  */
  tree inner_reorg_type = TREE_TYPE (reorg_type);
  tree inner_orig_type = TREE_TYPE (original_type);
  tree old_size_tree = TYPE_SIZE_UNIT (inner_orig_type);
  int old_size_int = tree_to_shwi (old_size_tree);
  tree new_size_tree = TYPE_SIZE_UNIT (inner_reorg_type);
  int new_size_int = tree_to_shwi (new_size_tree);
  tree old_integer_cst_tree = i;
  int old_integer_cst_int = tree_to_uhwi (old_integer_cst_tree);

  int offset = old_integer_cst_int % old_size_int;
  const bool is_modulo = offset == 0;
  bool is_valid_input = is_modulo;
  if (!is_valid_input)
    return;

  int new_integer_cst_int
    = old_integer_cst_int / old_size_int * new_size_int + offset;

  tree new_integer_cst_tree
    = build_int_cst (TREE_TYPE (old_integer_cst_tree), new_integer_cst_int);
  gimple_set_op (s, 2, new_integer_cst_tree);

  if (!is_valid_input)
    {
      log ("\n%d  = %d / %d * %d\n", new_integer_cst_int, old_integer_cst_int,
	   old_size_int, new_size_int);
    }
  gcc_assert (is_valid_input);
}

/* substitute types in post-order visit.  */
void
expr_type_rewriter::_walk_post (tree e)
{
  gcc_assert (e);
  tree t = TREE_TYPE (e);
  const bool in_map = _map2.get (t);

  if (!in_map)
    return;

  tree r_t = *_map2.get (t);
  tree _e = tree_to_tree (e);
  TREE_TYPE (_e) = r_t;

  if (TREE_CODE (e) == ARRAY_REF)
    {
      tree op_0 = TREE_OPERAND (_e, 0);
      if (op_0)
	{
	  TREE_TYPE (TREE_TYPE (op_0)) = r_t;
	}
    }
}

/* Rewrite Field.  */
void
expr_type_rewriter::_walk_COMPONENT_REF_post (tree e)
{
  gcc_assert (e);

  tree f = TREE_OPERAND (e, 1);
  tree r = TREE_OPERAND (e, 0);
  /* So, what we need is a map between this field and the new field.  */
  const bool in_map = _fields2.get (f);
  tree *reorg = _imap2.get (TREE_TYPE (r));
  bool field_name_equal = false;
  tree new_field = NULL_TREE;
  for (tree field = TYPE_FIELDS (TREE_TYPE (r)); field;
       field = DECL_CHAIN (field))
    {
      if (strcmp (type_stringifier::get_field_identifier (field).c_str (),
		  type_stringifier::get_field_identifier (f).c_str ())
	  != 0)
	continue;
      field_name_equal |= true;
      new_field = field;
      break;
    }

  if (field_name_equal && reorg)
    {
      TREE_OPERAND (e, 1) = new_field;
    }

  if (!in_map)
    return;

  std::pair<tree, bool> p = *_fields2.get (f);
  tree n_f = p.first;
  bool is_deleted = p.second;
  tree _e = tree_to_tree (e);
  TREE_OPERAND (_e, 1) = n_f;

  if (!is_deleted)
    return;

  _delete = _can_delete && true;
}

void
gimple_type_rewriter::_walk_pre_gcall (gcall *stmt)
{
  replace_sizeof_cst (stmt, _map);
}

void
gimple_type_rewriter::_walk_pre_tree (tree e)
{
  /* This is for local variables
     and other declarations.  */
  exprTypeRewriter.walk (e);
  bool _delete = exprTypeRewriter._delete;
  exprTypeRewriter._delete = false;
  /* I don't think it is possible here (local variable delcarations and such).
   */
  gcc_assert (!_delete);
  const bool is_interesting
    = exprTypeRewriter.is_interesting_type (TREE_TYPE (e));

  const bool is_var_decl = TREE_CODE (e) == VAR_DECL;
  const bool is_valid = is_interesting && is_var_decl;
  if (!is_valid)
    return;
  tree _e = tree_to_tree (e);
  relayout_decl (_e);
}

void
gimple_type_rewriter::_walk_pre_greturn (greturn *s)
{
  tree val = gimple_return_retval (s);
  if (!val)
    return;
  exprTypeRewriter.walk (val);
  bool _delete = exprTypeRewriter._delete;
  exprTypeRewriter._delete = false;
  /* We can't probably have a write in a return statement.  */
  gcc_assert (!_delete);
}

/* Prepare operands for fixing pointer arithmetic.  */
void
gimple_type_rewriter::handle_pointer_arithmetic (gimple *s)
{
  const enum tree_code p = POINTER_PLUS_EXPR;
  const enum tree_code d = POINTER_DIFF_EXPR;
  const enum tree_code e = gimple_expr_code (s);
  const bool is_pointer_plus = p == e;
  const bool is_pointer_diff = d == e;
  bool is_valid_input = is_pointer_plus != is_pointer_diff;
  gcc_assert (is_valid_input);

  const enum gimple_rhs_class rhs_class = gimple_assign_rhs_class (s);
  is_valid_input = GIMPLE_BINARY_RHS == rhs_class;
  gcc_assert (is_valid_input);

  tree op_0 = gimple_assign_rhs1 (s);
  tree op_1 = gimple_assign_rhs2 (s);
  tree lhs = gimple_assign_lhs (s);
  tree op_0_t = TREE_TYPE (op_0);
  tree op_1_t = TREE_TYPE (op_1);
  tree lhs_t = TREE_TYPE (lhs);
  const bool is_op_0_t_interesting
    = exprTypeRewriter.is_interesting_type (op_0_t);
  const bool is_op_1_t_interesting
    = exprTypeRewriter.is_interesting_type (op_1_t);
  const bool is_lhs_t_interesting
    = exprTypeRewriter.is_interesting_type (lhs_t);
  bool is_interesting_case
    = is_op_0_t_interesting || is_op_1_t_interesting || is_lhs_t_interesting;
  if (!is_interesting_case)
    return;

  const enum tree_code op_1_code = TREE_CODE (op_1);
  const enum tree_code op_0_code = TREE_CODE (op_0);
  const bool is_op_0_icst = INTEGER_CST == op_0_code;
  const bool is_op_1_icst = INTEGER_CST == op_1_code;
  const bool is_constant_case = is_op_0_icst != is_op_1_icst;
  if (!is_constant_case)
    {
      exprTypeRewriter.handle_pointer_arithmetic_nonconstant (s, op_0, op_1,
							      is_pointer_plus);
      bool _delete = exprTypeRewriter._delete;
      exprTypeRewriter._delete = false;
      /* Probably no deletion in pointer arithmetic...  */
      gcc_assert (!_delete);
      return;
    }

  tree integer_constant = is_op_0_icst ? op_0 : op_1;
  tree maybe_pointer = is_op_0_icst ? op_1 : op_0;
  tree maybe_pointer_t = TREE_TYPE (maybe_pointer);
  assert_is_type (maybe_pointer_t, POINTER_TYPE);
  tree pointer_variable = maybe_pointer;

  exprTypeRewriter.handle_pointer_arithmetic_constants (s, pointer_variable,
							integer_constant);
  bool _delete = exprTypeRewriter._delete;
  exprTypeRewriter._delete = false;
  /* Probably no deletion in pointer arithmetic.  */
  gcc_assert (!_delete);
}

void
gimple_type_rewriter::_walk_pre_gassign (gassign *s)
{
  const enum gimple_rhs_class code = gimple_assign_rhs_class (s);

  switch (code)
    {
    case GIMPLE_TERNARY_RHS:
      {
	tree rhs3 = gimple_assign_rhs3 (s);
	exprTypeRewriter.walk (rhs3);
      }
    /* fall-through.  */
    case GIMPLE_BINARY_RHS:
      {
	tree rhs2 = gimple_assign_rhs2 (s);
	exprTypeRewriter.walk (rhs2);
      }
    /* fall-through.  */
    case GIMPLE_UNARY_RHS:
    case GIMPLE_SINGLE_RHS:
      {
	tree rhs1 = gimple_assign_rhs1 (s);
	exprTypeRewriter.walk (rhs1);
	tree lhs = gimple_assign_lhs (s);
	if (!lhs)
	  break;
	/* Here is the only place where we likely can delete a statement.  */
	exprTypeRewriter.walk (lhs);
	bool _delete = exprTypeRewriter._delete;
	exprTypeRewriter._delete = false;
	if (_delete)
	  {
	    _deleted = true;
	  }
      }
      break;
    default:
      gcc_unreachable ();
      break;
    }

  const enum tree_code e_code = gimple_expr_code (s);
  switch (e_code)
    {
    case POINTER_PLUS_EXPR:
    case POINTER_DIFF_EXPR:
      handle_pointer_arithmetic (s);
      break;
    default:
      break;
    }
}

void
gimple_type_rewriter::_rewrite_function_decl ()
{
  /* NOTE: It seems we only need to rewrite the return type
     for now...  */
  cgraph_node *node = NULL;
  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    {
      tree fndecl = node->decl;

      exprTypeRewriter.walk (fndecl);
      tree decl = DECL_RESULT (fndecl);
      if (!decl)
	continue;

      exprTypeRewriter.walk (decl);
    }
}

void
gimple_type_rewriter::_walk_pre_gphi (gphi *s)
{
  unsigned n = gimple_phi_num_args (s);
  for (unsigned i = 0; i < n; i++)
    {
      tree a = gimple_phi_arg_def (s, i);
      exprTypeRewriter.walk (a);
    }
}

namespace {
const pass_data pass_data_ipa_dead_field_elimination = {
  SIMPLE_IPA_PASS,
  "dead-field-elimination",
  OPTGROUP_NONE,
  TV_NONE,
  0,
  0,
  0,
  0,
  0,
};

class pass_ipa_dead_field_elimination : public simple_ipa_opt_pass
{
public:
  pass_ipa_dead_field_elimination (gcc::context *ctx)
    : simple_ipa_opt_pass (pass_data_ipa_dead_field_elimination, ctx)
  {}

  virtual bool gate (function *)
  {
    return flag_ipa_dead_field_elimination && lang_c_p ();
  }

  virtual unsigned execute (function *) { return lto_dfe_execute (); }
};
} /* namespace.  */

simple_ipa_opt_pass *
make_pass_ipa_dead_field_elimination (gcc::context *ctx)
{
  return new pass_ipa_dead_field_elimination (ctx);
}

/* Top level function.  */
static unsigned int
lto_dfe_execute ()
{
  lto_dead_field_elimination ();
  log ("finished!\n");
  return 0;
}

/*
 * Perform dead field elimination at link-time.
 * This transformation is composed of two main stages:
 *   * Finding out which fields are non escaping and unaccessed.
 *   * Creating new types and substituting their mention throughout the
 *   program.
 */
static void
lto_dead_field_elimination ()
{
  /* Analysis.  */
  ipa_type_escape_analysis_init ();
  if (detected_incompatible_syntax)
    {
      ipa_type_escape_analysis_exit ();
      return;
    }
  record_field_map4_t record_field_map;
  find_fields_accessed (record_field_map);
  if (detected_incompatible_syntax)
    {
      ipa_type_escape_analysis_exit ();
      return;
    }
  record_field_offset_map4_t record_field_offset_map;
  obtain_nonescaping_unaccessed_fields (tea_types, record_field_map, OPT_Wdfa,
					record_field_offset_map);
  if (detected_incompatible_syntax || record_field_offset_map.is_empty ())
    {
      ipa_type_escape_analysis_exit ();
      return;
    }

  /* Prepare for transformation.  */
  hash_set<tree> to_modify2;
  get_all_types_pointing_to (record_field_offset_map, tea_types, to_modify2);
  reorg_record_map2_t a;
  reorg_field_map2_t b;
  reorg_maps_t replacements
    = get_types_replacement (record_field_offset_map, to_modify2, a, b);
  reorg_record_map2_t *map = replacements.first;
  reorg_field_map2_t *field_map = replacements.second;
  gcc_assert (map && field_map);
  /* Transformation.  */
  substitute_types_in_program (*map, *field_map, true);
  ipa_type_escape_analysis_exit ();
}
