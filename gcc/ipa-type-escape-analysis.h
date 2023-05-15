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

#ifndef GCC_IPA_TYPE_ESCAPE_ANALYSIS_H
#define GCC_IPA_TYPE_ESCAPE_ANALYSIS_H

#include <string>

/* Logging function, useful for debugging.  */
void
log (const char *const fmt, ...) __attribute__ ((format (printf, 1, 0)));

inline void
log (const char *const fmt, ...)
{
  if (!dump_file)
    return;

  va_list args;
  va_start (args, fmt);
  vfprintf (dump_file, fmt, args);
  fflush (dump_file);
  va_end (args);
}

/* Determine if type A is incomplete.  */
bool is_incomplete (tree a);

/* Assert type A has is EXPECTED_CODE.  */
void assert_is_type (tree a, const enum tree_code expected_code);

/* There are some cases where I need to change a tree to a tree.
 * Some of these are part of the way the API is written.  To avoid
 * warnings, always use this function for casting away const-ness.
 */
tree tree_to_tree (tree t);

/* TODO: Rename?
   TSET_T stands for type set.  */
typedef hash_set<tree> tset2_t;

/* Base class used for visiting tree nodes starting with root T.
 * It can handle recursive cases in the tree graph by holding
 * a set of previously seen nodes and checking before walking
 * a node.

 * Unlike walk_tree, TypeWalker allows users to create post-order
 * callbacks for each type of tree.
 */
class type_walker
{
public:
  type_walker () {};

  /* Main interface to type walker.
   * Walk type T.
   */
  void walk (tree t);

protected:
  /* Typeset holds previously visited nodes.  */
  tset2_t tset2;

  /* Inner walking method, used to recurse.  */
  void _walk (tree t);

  /* Common walking method for REFERENCE_TYPE, ARRAY_TYPE, and POINTER_TYPE.  */
  void _walk_wrapper (tree t);

  /* Common walking method for RECORD_TYPE and UNION_TYPE.  */
  void _walk_record_or_union (tree t);

  /* Common walking method for FUNCTION_TYPE and METHOD_TYPE.  */
  virtual void _walk_function_or_method (tree t);

  /* If the type is memoized and we don't need to walk further down.  */
  virtual bool is_memoized (__attribute__ ((unused)) tree t) { return false; }

  /* Function definitions for different TYPEs callbacks.
     _pre is the pre-order callback.
     _post is the post-order callback.
     If you want to find a specific type in a specific order,
     (e.g., RECORD_TYPE and preorder)
     you can create a derived class and implement the function
     void _walk_RECORD_TYPE_pre (tree).

     walk_##code is the function that calls
     the preorder callback
     walking subtrees
     and the postorder callback.
     This is for each specific tree code.

     _walk_##code is the function that walks subtrees for that
     specific tree code.
   */
#define TypeWalkerFuncDecl(code) \
  virtual void _walk_##code##_pre (__attribute__ ((unused)) tree t) {}; \
  virtual void _walk_##code (tree t); \
  virtual void _walk_##code##_post (__attribute__ ((unused)) tree t) {}; \
  virtual void walk_##code (tree t)

  /* NOTE the lack of semicolon here.
     This is so that when using the macro we can use a semi-colon
     and formatting doesn't break.  */

  /* These are the types for which we can define a pre-order
   * and post-order functions.  */
  TypeWalkerFuncDecl (VOID_TYPE);
  TypeWalkerFuncDecl (INTEGER_TYPE);
  TypeWalkerFuncDecl (REAL_TYPE);
  TypeWalkerFuncDecl (FIXED_POINT_TYPE);
  TypeWalkerFuncDecl (COMPLEX_TYPE);
  TypeWalkerFuncDecl (ENUMERAL_TYPE);
  TypeWalkerFuncDecl (BOOLEAN_TYPE);
  TypeWalkerFuncDecl (OFFSET_TYPE);
  TypeWalkerFuncDecl (RECORD_TYPE);
  TypeWalkerFuncDecl (POINTER_TYPE);
  TypeWalkerFuncDecl (REFERENCE_TYPE);
  TypeWalkerFuncDecl (ARRAY_TYPE);
  TypeWalkerFuncDecl (UNION_TYPE);
  TypeWalkerFuncDecl (FUNCTION_TYPE);
  TypeWalkerFuncDecl (METHOD_TYPE);

  /* These are not types, but are still trees that
   * can be reached from a tree type.  Therefore, these
   * trees also need to be walked.
   */
  TypeWalkerFuncDecl (field);
  TypeWalkerFuncDecl (return );
  TypeWalkerFuncDecl (args);
  TypeWalkerFuncDecl (arg);
};

/* Base class for the implementation of the visitor pattern for
 * trees which are "expressions".  This might be a misnomer.
 * What it means is that it walks whatever can be the result of
 * the trees returned by gimple_assign_rhs{1,2,3}, gimple_return,
 * gimple_call...
 * TODO: The expressions visited here might not be the whole set
 * but it is what was found while experimentally running some C
 * programs.
 */
class expr_walker
{
public:
  expr_walker () {};

  /* Walk tree E.  */
  void walk (tree e);

private:
  /* Virtual function to be implemented.  Callback for all E in preorder.  */
  virtual void _walk_pre (__attribute__ ((unused)) tree e) {};

  /* Inner method that will recurse for walking subtrees in E.  */
  void _walk (tree e);

  /* Virtual function to be implemented.  Callback for all E in postorder.  */
  virtual void _walk_post (__attribute__ ((unused)) tree e) {};

  /* Walking subtrees generically.  Either it is a leaf node,
     (i.e., it does not have subtrees), or it has some operands.
     TODO: This can probably be changed to be more general
     by finding out how many operands an expression has.

     tree_code C is used to assert that we are visiting an operand
     of a specific tree code.
   */
  inline void _walk_leaf (tree e, const enum tree_code c);
  inline void _walk_op_n (tree e, unsigned n);
  inline void _walk_op_0 (tree e, const enum tree_code c);
  inline void _walk_op_1 (tree e, const enum tree_code c);

  /* Virtual function declarations for the pre-order and post-order callbacks.
   * _walk_##code##_pre is the preorder callback
   * walk_##code will call the preorder, subtree walker, and postorder
   * _walk_##code is the subtree walker
   * _walk_##code##_post is the post-order callback.
   */
#define ExprWalkerFuncDecl(code) \
  virtual void _walk_##code##_pre (__attribute__ ((unused)) tree e) {}; \
  void walk_##code (tree e); \
  void _walk_##code (tree e); \
  virtual void _walk_##code##_post (__attribute__ ((unused)) tree e) {}

  /* Some of these are not "EXPR" codes, but they are reachable
     from gimple_assign_rhs{1,2,3} and others.  */
  ExprWalkerFuncDecl (CONSTRUCTOR);
  ExprWalkerFuncDecl (INTEGER_CST);
  ExprWalkerFuncDecl (REAL_CST);
  ExprWalkerFuncDecl (STRING_CST);
  ExprWalkerFuncDecl (BIT_FIELD_REF);
  ExprWalkerFuncDecl (ARRAY_REF);
  ExprWalkerFuncDecl (MEM_REF);
  ExprWalkerFuncDecl (COMPONENT_REF);
  ExprWalkerFuncDecl (SSA_NAME);
  ExprWalkerFuncDecl (ADDR_EXPR);
  ExprWalkerFuncDecl (VIEW_CONVERT_EXPR);
  ExprWalkerFuncDecl (IMAGPART_EXPR);
  ExprWalkerFuncDecl (FIELD_DECL);
  ExprWalkerFuncDecl (VAR_DECL);
  ExprWalkerFuncDecl (RESULT_DECL);
  ExprWalkerFuncDecl (PARM_DECL);
  ExprWalkerFuncDecl (FUNCTION_DECL);
  ExprWalkerFuncDecl (LE_EXPR);
  ExprWalkerFuncDecl (LT_EXPR);
  ExprWalkerFuncDecl (EQ_EXPR);
  ExprWalkerFuncDecl (GT_EXPR);
  ExprWalkerFuncDecl (GE_EXPR);
  ExprWalkerFuncDecl (NE_EXPR);
};

/* Base class for applying the visitor pattern to gimple_stmts.
 * This class visits everything it cans during LTO.
 * That includes global variables, and all function declarations that
 * are in the current partition.
 */
class gimple_walker
{
public:
  gimple_walker () : _deleted (false), _rebuild (false) {};

  /* Walk the entire code, therefore no input is needed.  */
  void walk ();

protected:
  /* _DELETED is set by overwritten functions that
   * delete a specific gimple stmt.  This tells the
   * gimple walker to remove the gimple stmt.
   */
  bool _deleted;
  bool _rebuild;

  cgraph_node *currently_walking;

  /* Walk global variables.  */
  void _walk_globals ();

  /* Walk individual global variable V.  */
  virtual void _walk_global (varpool_node *v);

  /* Will walk declarations, locals, ssa names, and basic blocks.  */
  virtual void _walk_cnode (cgraph_node *cnode);

  /* This will walk the CNODE->decl.  */
  void _walk_decl (cgraph_node *cnode);

  /* Walk ssa_names in CNODE.  */
  void _walk_ssa_names (cgraph_node *cnode);

  /* Walk local variables in CNODE.  */
  void _walk_locals (cgraph_node *cnode);

  /* Iterate over all basic blocks in CNODE.  */
  void _walk_bb (cgraph_node *cnode);

  /* Iterate over all gimple_stmt in BB.  */
  void _walk (basic_block bb);

  /* Function declarations for virtual functions.
   * These include the pre-order callbacks, walk subtrees,
   * and post-order callbacks.
   */
  virtual void _walk_pre_tree (__attribute__ ((unused)) tree t) {};
  void walk_tree2 (tree t);
  void _walk_tree (tree t);
  virtual void _walk_post_tree (__attribute__ ((unused)) tree t) {};

  virtual void _walk_pre_gimple (__attribute__ ((unused)) gimple *g) {};
  void walk_gimple (gimple *g);
  void _walk_gimple (gimple *g);
  virtual void _walk_post_gimple (__attribute__ ((unused)) gimple *g) {};

  virtual void _walk_pre_gassign (__attribute__ ((unused)) gassign *g) {};
  void walk_gassign (gassign *g);
  void _walk_gassign (gassign *g);
  virtual void _walk_post_gassign (__attribute__ ((unused)) gassign *g) {};

  virtual void _walk_pre_greturn (__attribute__ ((unused)) greturn *g) {};
  void walk_greturn (greturn *g);
  void _walk_greturn (greturn *g);
  virtual void _walk_post_greturn (__attribute__ ((unused)) greturn *g) {};

  virtual void _walk_pre_gcond (__attribute__ ((unused)) gcond *g) {};
  void walk_gcond (gcond *g);
  void _walk_gcond (gcond *g);
  virtual void _walk_post_gcond (__attribute__ ((unused)) gcond *g) {};

  virtual void _walk_pre_glabel (__attribute__ ((unused)) glabel *g) {};
  void walk_glabel (glabel *g);
  void _walk_glabel (glabel *g);
  virtual void _walk_post_glabel (__attribute__ ((unused)) glabel *g) {};

  virtual void _walk_pre_gcall (__attribute__ ((unused)) gcall *g) {};
  void walk_gcall (gcall *g);
  void _walk_gcall (gcall *g);
  virtual void _walk_post_gcall (__attribute__ ((unused)) gcall *g) {};

  virtual void _walk_pre_gswitch (__attribute__ ((unused)) gswitch *g) {};
  void walk_gswitch (gswitch *g);
  void _walk_gswitch (gswitch *g);
  virtual void _walk_post_gswitch (__attribute__ ((unused)) gswitch *g) {};

  virtual void _walk_pre_gphi (__attribute__ ((unused)) gphi *g) {};
  void walk_gphi (gphi *g);
  void _walk_gphi (gphi *g);
  virtual void _walk_post_gphi (__attribute__ ((unused)) gphi *g) {};
};

/* TYPE_PARTITIONS_S is a structure that is shared
 * across most of the type escape analysis.  It holds
 * 4 different partitions.

 * 1. points to record
 * 2. complement of points to record
 * 3. escaping trees
 * 4. non escaping trees

 * It also has a set of all types seen so far called universe.

 * Ideally 1 union 2 should be universe and 3 union 4 should be universe.
 */
struct type_partitions2_s
{
  /* The set of all types which have been seen.  */
  tset2_t universe;

  /* The set of all types which somehow refer to a RECORD_TYPE.  */
  tset2_t points_to_record;

  /* The complement of points_to_record.  */
  tset2_t complement;

  /* The set of all escaping types.  */
  tset2_t escaping;

  /* The set of all non escaping types.  */
  tset2_t non_escaping;

  /* Determine if we have seen this type before.  */
  bool in_universe (tree);

  /* Determine if tree points to a record.  */
  bool in_points_to_record (tree);

  /* Determine if tree does not point to a record.  */
  bool in_complement (tree);

  /* Insert either in points to record or complement.  */
  void insert (tree, bool);
};

typedef struct type_partitions2_s tpartitions2_t;

/* TypeCollector is a derived class from TypeWalker
 * that collects all types reachable from T into the partitions
 * points_to_record or not points to record.
 */
class type_collector : public type_walker
{
public:
  type_collector (tpartitions2_t &ptrset) : ptrset2 (ptrset) {};
  ~type_collector () {};

  /* Main interface.  */
  void collect (tree t);

  /* Collect the result after walking all trees.  */
  tpartitions2_t &get_record_reaching_trees () { return ptrset2; }

private:
  /* PTR stands for points to record.  Before walking into a RECORD_TYPE
   * tree, the value is always false.  Once a RECORD_TYPE is visited,
   * update all values on map to be true.  At post-order keys
   * will be erased.
   * Invariants:
   * before pre-order of root T map is empty
   * after post-order of root T map is empty

   * In other words, the contents are reset after every
   * call to collect.
   */
  hash_map<tree, bool> ptr2;

  /* The type partition set that will hold partitions for
   * points to record or does not point to record.
   * Will be updated during post-order with the keys and values
   * from PTR.
   * This datastructure persists across calls to collect.
   */
public:
  tpartitions2_t &ptrset2;

private:
  /* Sanity check determines that the partitions are mutually
   * exclusive.
   */
  void _sanity_check ();

  /* Store T into partition depending on PTR.  */
  void _collect_simple (tree t);

  /* If the value is in PTRSET, no need to visit the lower nodes.  */
  virtual bool is_memoized (tree t);

  /* These functions insert and erase elements in PTR.

   * We probably don't need to create a _pre and _post
   * function for all of them.  We could probably substitute
   * one for a general *_pre and *_post method that triggers
   * for all different type T.  However, we want to avoid
   * collecting FIELD_DECL, ARGS, and some other none-types.
   */
  virtual void _walk_VOID_TYPE_pre (tree t);
  virtual void _walk_VOID_TYPE_post (tree t);
  virtual void _walk_INTEGER_TYPE_pre (tree t);
  virtual void _walk_INTEGER_TYPE_post (tree t);
  virtual void _walk_REAL_TYPE_pre (tree t);
  virtual void _walk_REAL_TYPE_post (tree t);
  virtual void _walk_FIXED_POINT_TYPE_pre (tree t);
  virtual void _walk_FIXED_POINT_TYPE_post (tree t);
  virtual void _walk_COMPLEX_TYPE_pre (tree t);
  virtual void _walk_COMPLEX_TYPE_post (tree t);
  virtual void _walk_ENUMERAL_TYPE_pre (tree t);
  virtual void _walk_ENUMERAL_TYPE_post (tree t);
  virtual void _walk_BOOLEAN_TYPE_pre (tree t);
  virtual void _walk_BOOLEAN_TYPE_post (tree t);
  virtual void _walk_ARRAY_TYPE_pre (tree t);
  virtual void _walk_ARRAY_TYPE_post (tree t);
  virtual void _walk_POINTER_TYPE_pre (tree t);
  virtual void _walk_POINTER_TYPE_post (tree t);
  virtual void _walk_REFERENCE_TYPE_pre (tree t);
  virtual void _walk_REFERENCE_TYPE_post (tree t);
  virtual void _walk_UNION_TYPE_pre (tree t);
  virtual void _walk_UNION_TYPE_post (tree t);
  virtual void _walk_FUNCTION_TYPE_pre (tree t);
  virtual void _walk_FUNCTION_TYPE_post (tree t);
  virtual void _walk_METHOD_TYPE_pre (tree t);
  virtual void _walk_METHOD_TYPE_post (tree t);

  /* When a RECORD_TYPE is found, update all values in PTR to true.  */
  virtual void _walk_RECORD_TYPE_pre (tree t);
  virtual void _walk_RECORD_TYPE_post (tree t);
};

/* Derived class from TypeWalker.  This class
 * will recursively print all type trees unlike just printing
 * the identifier.
 */
class type_stringifier : public type_walker
{
public:
  type_stringifier () {};

  /* Main method, returns a stringified version of T.  */
  std::string stringify (tree t);

  /* Only get type identifier.  */
  static std::string get_type_identifier (tree t);

  /* If field is not anonymous, return field identifier.  */
  static std::string get_field_identifier (tree t);

private:
  hash_set<tree> _memoized_set;

  /* Return true if this type has alrady been visited */
  bool is_memoized (tree);

  /* Working string... will hold result for stringify.  */
  std::string _stringification;

  /* Append get_tree_code_name.  */
  void _stringify_simple (tree t);

  /* Append identifier and "{".  */
  void _stringify_aggregate_pre (tree t);

  /* Append "}".  */
  void _stringify_aggregate_post (tree t);

  /* Append "function {".  */
  /* TODO: For C++ we will need to change this for methods.  */
  void _stringify_fm_pre (tree t);
  virtual void _walk_METHOD_TYPE_pre (tree t);
  virtual void _walk_METHOD_TYPE_post (tree t);
  virtual void _walk_FUNCTION_TYPE_pre (tree t);
  virtual void _walk_FUNCTION_TYPE_post (tree t);

  /* Append "}".  */
  void _stringify_fm_post (tree t);

  /* Most of the pre-order walk can probably be replaced by
   * a catch all pre-order call back.
   * TODO: implement that...
   */
  virtual void _walk_VOID_TYPE_pre (tree t);
  virtual void _walk_INTEGER_TYPE_pre (tree t);
  virtual void _walk_REAL_TYPE_pre (tree t);
  virtual void _walk_FIXED_POINT_TYPE_pre (tree t);
  virtual void _walk_COMPLEX_TYPE_pre (tree t);
  virtual void _walk_BOOLEAN_TYPE_pre (tree t);
  virtual void _walk_OFFSET_TYPE_pre (tree t);
  virtual void _walk_return_pre (tree t);
  virtual void _walk_args_pre (tree t);

  /* Append "*".  */
  virtual void _walk_POINTER_TYPE_pre (tree t);
  virtual void _walk_POINTER_TYPE_post (tree t);

  /* Append "&".  */
  virtual void _walk_REFERENCE_TYPE_post (tree t);

  /* Append "[]".  */
  virtual void _walk_ARRAY_TYPE_pre (tree t);
  virtual void _walk_ARRAY_TYPE_post (tree t);

  /* Append "record" */
  virtual void _walk_RECORD_TYPE_pre (tree t);
  virtual void _walk_RECORD_TYPE_post (tree t);

  /* Append "union" */
  virtual void _walk_UNION_TYPE_pre (tree t);
  virtual void _walk_UNION_TYPE_post (tree t);

  /* Append "," */
  virtual void _walk_field_post (tree t);
  virtual void _walk_return_post (tree t);

  /* Append "," */
  virtual void _walk_args_post (tree t);
  virtual void _walk_arg_post (tree t);
};

/* ExprCollector is an implementation of ExprWalker.  It walks
 * all trees in an expression and calls type collector on
 * the types for all types of nested expressions.
 */
class expr_collector : public expr_walker
{
public:
  type_collector _type_collector;
  hash_set<tree> *ptrset3;
  bool _white_listing;

  expr_collector (tpartitions2_t &p, bool white_listing)
    : _type_collector (p), ptrset3 (NULL), _white_listing (white_listing)
  {
    if (_white_listing)
      ptrset3 = new hash_set<tree> ();
  };
  ~expr_collector ()
  {
    if (_white_listing)
      delete ptrset3;
  };

  /* Holds the result after collecting from all trees.  */
  tpartitions2_t get_record_reaching_trees ()
  {
    return _type_collector.get_record_reaching_trees ();
  }

private:
  /* Catch all callback for all nested expressions E.  */
  virtual void _walk_pre (tree e);
};

/* Derived from GimpleWalker.  Its purpose is to walk all gimple
 * possible and call expression collector to collect types
 * on global variables, assign statement, return statement,
 * condition statement, and call statements.
 */
class gimple_type_collector : public gimple_walker
{
public:
  gimple_type_collector (tpartitions2_t &p, bool white_listing)
    : _expr_collector (p, white_listing) {};

  /* This holds the result after walking the whole program.  */
  tpartitions2_t get_record_reaching_trees ()
  {
    return _expr_collector.get_record_reaching_trees ();
  }

  /* Print final results.
     TODO: I believe this could be made const.  */
  void print_collected ();

  expr_collector _expr_collector;

private:
  /* Call back for global variables.  */
  virtual void _walk_pre_tree (tree);

  /* Call back for gassign.  */
  virtual void _walk_pre_gassign (gassign *s);

  /* Call back for greturn.  */
  virtual void _walk_pre_greturn (greturn *s);

  /* Call back for gcond.  */
  virtual void _walk_pre_gcond (gcond *s);

  /* Call back for gcall.  */
  virtual void _walk_pre_gcall (gcall *s);

  /* Call back for gdebug.  */
  virtual void _walk_pre_gdebug (gdebug *s);
};

/* Reason for why a type is escaping
   Used in a map with corresponding trees as keys.
   TODO: Add bit_field
   TODO: Add has function pointer
   TODO: Add has constructor.  */
struct Reason
{
  /* Determines whether a type is escaping.  */
  inline bool is_escaping () const
  {
    return this->global_is_visible || this->parameter_is_visible
	   || this->return_is_visible || this->type_is_casted
	   || this->type_is_volatile || this->type_is_in_union
	   || this->is_indirect;
  }

  /* Escapes because a global variable is visible.  */
  bool global_is_visible;

  /* Escapes because a parameter is used in an
     externally visible function.  */
  bool parameter_is_visible;

  /* Escapes because return value is from
     an externally visible function.  */
  bool return_is_visible;

  /* Escapes because of casting.  */
  bool type_is_casted;

  /* Escapes because it is volatile.  */
  bool type_is_volatile;

  /* Escapes because it is in union.  */
  bool type_is_in_union;

  /* Escapes because is in indirect function call.  */
  bool is_indirect;

  /* Merge two reason.  */
  Reason operator| (const Reason &);
  Reason &operator|= (const Reason &);

  /* Print reasons a type is escaping.  */
  void print () const;

  /* Initialize as non-escaping by default.  */
  Reason ()
    : global_is_visible (false), parameter_is_visible (false),
      return_is_visible (false), type_is_casted (false),
      type_is_volatile (false), type_is_in_union (false),
      is_indirect (false) {};
};

typedef hash_map<tree, Reason> typemap2;

/* Type Escaper propagates information on whether a type escapes
 * to all types reachable by a root type.  It also propagates
 * information up if a union is found.  At the moment
 * we don't transform types which point to unions.
 * We also don't transform RECORD_TYPEs which have function pointers.
 * This can possible be removed.  But it is future work.
 * Do not also modify types with bit fields.
 */
class type_escaper : public type_walker
{
public:
  /* Hold the partitions for escaping non escaping.  */
  tpartitions2_t &_ptrset2;

  type_escaper (tpartitions2_t &p)
    : _ptrset2 (p), _inside_union (0), _inside_record (0) {};

  /* Have information that matches a tree type with
     why a type is escaping.  */
  typemap2 calc2;

  /* Get partitions after calculating escaping types.  */
  void fix_sets ();

  /* Print reasons why a type is escaping.  */
  void print_reasons ();

  /* Update type T with escaping reason R.  */
  void update (tree t, Reason r);

  /* Update type T with escaping reason R.  */
  void _update_single (tree t, Reason r);

private:
  /* TODO: we can probably reduce the amount of functions
     by adding a catch all pre-order callback...  */
  virtual void _walk_POINTER_TYPE_pre (tree t);
  virtual void _walk_POINTER_TYPE_post (tree t);
  virtual void _walk_REFERENCE_TYPE_pre (tree t);
  virtual void _walk_ARRAY_TYPE_pre (tree t);
  virtual void _walk_ARRAY_TYPE_post (tree t);
  virtual void _walk_RECORD_TYPE_pre (tree t);
  virtual void _walk_RECORD_TYPE_post (tree t);
  virtual void _walk_field_pre (tree t);
  virtual bool is_memoized (tree t);

  /* Mark escaping reason as having a function pointer in a structure,
   * propagate up and down.  */
  virtual void _walk_METHOD_TYPE_pre (tree t);
  virtual void _walk_FUNCTION_TYPE_pre (tree t);

  /* Mark escaping reason as having a union and propagate up and down.  */
  virtual void _walk_UNION_TYPE_pre (tree t);
  virtual void _walk_UNION_TYPE_post (tree t);

  /* Record how many nested unions the current context is in.  */
  unsigned _inside_union;

  /* Record how many nested records the current context is in.  */
  unsigned _inside_record;

  /* Recursive inner function.  */
  void _update (tree t);

  /* Reason to be propagated to all trees reachable by root T
     Can be updated during the walk.  */
  Reason _reason;

  /* Final method that places types from calc to partitions.  */
  void place_escaping_types_in_set ();
};

/* Visit all expressions and update reasons why they might be deleted.  */
class expr_escaper : public expr_walker
{
public:
  expr_escaper (tpartitions2_t &types, hash_map<tree, bool> *whitelisted2)
    : _type_escaper (types), _whitelisted2 (whitelisted2) {};

  /* Main interface: T escapes because R.  */
  void update (tree t, Reason r);

  /* Will be used to propagate escaping reasons to Types.  */
  type_escaper _type_escaper;

  hash_map<tree, bool> *_whitelisted2;

  /* Holds the end result.  */
  void fix_sets ();

  /* Print end result.  */
  void print_reasons ();

  cgraph_node *curr_node;

private:
  /* Keep track of the current expressions.  The top of the stack
     is the subexpression being examined.
     The bottom of the stack is the expression called on the update
     function.  */
  auto_vec<tree> _stack2;

  /* Reason to propagate across all subexpressions.  */
  Reason _r;

  /* Push to stack.  */
  virtual void _walk_pre (tree e);

  /* Pop from stack.  */
  virtual void _walk_post (tree e);

  /* Check if there is a cast between the
     expression (MEM_REF (SSA_NAME))
     SSA_NAME is the subexpression of MEM_REF.  */
  virtual void _walk_SSA_NAME_pre (tree e);

  /* If the expression E is a constructor then we need
     to mark these types as escaping because we cannot
     deal with constructors at the moment.  */
  virtual void _walk_CONSTRUCTOR_pre (tree e);
};

/* Do a type structural equality for two types.  */
class type_structural_equality
{
public:
  type_structural_equality () {};

  /* Return TRUE if A and B have equal structures.  */
  bool equal (tree a, tree b);

protected:
  /* Recursive _equal.  */
  virtual bool _equal (tree a, tree b);

private:
  /* Use to limit recursion if we are revisiting a node.  */
  typedef hash_set<tree> tset2_t;

  /* Limit recursion for LHS.  */
  tset2_t set2_l;

  /* Limit recursion for RHS.  */
  tset2_t set2_r;

  /* Determine if the code is equal.  */
  bool _equal_code (tree a, tree b);

  /* Wrapper around POINTER_TYPE, ARRAY_TYPE and REFERENCE_TYPE.  */
  bool _equal_wrapper (tree a, tree b);

  /* Different types we are comparing.  */
#define TSE_FUNC_DECL(code) virtual bool _walk_##code (tree l, tree r)

  /* Current types that can be compared.  */
  TSE_FUNC_DECL (VOID_TYPE);
  TSE_FUNC_DECL (COMPLEX_TYPE);
  TSE_FUNC_DECL (INTEGER_TYPE);
  TSE_FUNC_DECL (REAL_TYPE);
  TSE_FUNC_DECL (FIXED_POINT_TYPE);
  TSE_FUNC_DECL (POINTER_TYPE);
  TSE_FUNC_DECL (ENUMERAL_TYPE);
  TSE_FUNC_DECL (BOOLEAN_TYPE);
  TSE_FUNC_DECL (OFFSET_TYPE);
  TSE_FUNC_DECL (RECORD_TYPE);
  TSE_FUNC_DECL (REFERENCE_TYPE);
  TSE_FUNC_DECL (ARRAY_TYPE);
  TSE_FUNC_DECL (UNION_TYPE);
  TSE_FUNC_DECL (FUNCTION_TYPE);
  TSE_FUNC_DECL (METHOD_TYPE);
};

/* Check for equality even when a type is incomplete.
   When one type is incomplete and MAIN_VARIANTS are different
   compare only with identifiers.
   Unsound but it is as sound as it can be.  */
class type_incomplete_equality : public type_structural_equality
{
public:
  type_incomplete_equality () {};

protected:
  virtual bool _equal (tree l, tree r);
};

/* Inspect gimple code and find reasons why types might escape given a gimple
 * stmt.  */
class gimple_escaper : public gimple_walker
{
public:
  gimple_escaper (tpartitions2_t &types, hash_map<tree, bool> *whitelisted2)
    : _expr_escaper (types, whitelisted2)
  {
    _init ();
  };

  /* Propagate escaping reason to subexpressions.  */
  expr_escaper _expr_escaper;

  /* Obtain final result.  */
  void fix_sets ();

  /* Print final result.  */
  void print_reasons ();

protected:
  /* Set of undefined functions, this set is filled with
   * functions obtained via FOR_EACH_FUNCTION_WITH_GIMPLE_BODY.  */
  typedef hash_set<tree> undefset2;
  undefset2 undefined2;

  /* Initializes undefined.  */
  void _init ();

  /* Return true if it is a known builtin function.  */
  static bool filter_known_function (cgraph_node *);
  static bool filter_known_function (tree);

  /* Return true if function is externally visible.  */
  static bool is_function_escaping (cgraph_node *);
  static bool is_function_escaping (tree);

  /* Return true if variable is externally visible.  */
  static bool is_variable_escaping (varpool_node *);

  /* Marks global variables with CONSTRUCTORS and ERROR_MARKs as escaping.  */
  virtual void _walk_global (varpool_node *);

  /* Do not escape on assignments.  */
  virtual void _walk_pre_gassign (gassign *s);

  /* Do not escape return values.  */
  virtual void _walk_pre_greturn (greturn *s);

  /* Do not escape gcond.  */
  virtual void _walk_pre_gcond (gcond *s);

  /* Mark arguments and return type as escaping
   * if callsite is undefined, indirect or externally visible.  */
  virtual void _walk_pre_gcall (gcall *s);

  /* Mark T as escaping if is in UNKNOWN_LOCATION.
   * This is a way of finding
   * types introduced by profiling and mark them as escaping.
   * TODO: Improve this.
   */
  virtual void _walk_pre_tree (tree t);
};

/*
 * GimpleCaster is intended to walk gimple
 * and update a map that will hold information
 * on whether a type was casted or not.
 */
class gimple_caster : public gimple_escaper
{
public:
  gimple_caster (tpartitions2_t &types, hash_map<tree, bool> *whitelisted2)
    : gimple_escaper (types, whitelisted2), _whitelisted2 (whitelisted2) {};

private:
  hash_map<tree, bool> *_whitelisted2;

  /* Determine if cast comes from a known function.  */
  static bool follow_def_to_find_if_really_cast (tree);

  /* If arguments are casted, mark them as escaping.
   * Assignments from malloc and other known functions
   * are allowed.
   * */
  virtual void _walk_pre_gcall (gcall *s);

  /* If assignment is casted, mark them as escaping.
   * Assignments from malloc and other known functions
   * are allowed.
   */
  virtual void _walk_pre_gassign (gassign *s);

  /* If return value is casted, mark it as escaping.
   * Assignments from malloc and other known functions
   * are allowed.
   */
  virtual void _walk_pre_greturn (greturn *s);

  /* If source values of phi are casted, mark them as escaping.
   * Assignments from malloc and other known functions
   * are allowed.
   */
  virtual void _walk_pre_gphi (gphi *s);

  void mark_type (tree type);
  void mark_type_in_address (tree addr);

  void _walk_memref (tree memref, type_structural_equality *equality);
  void _walk_memref (gimple *stmt);
  int _walk_address (tree addr, type_structural_equality *equality, tree type,
		     tree offset = NULL_TREE);
};

/* Bitflags used for determining if a field is
   never accessed, read or written.
   TODO: Place on their own namespace?  */
const unsigned Empty = 0x0u;
const unsigned Read = 0x01u;
const unsigned Write = 0x02u;

/* Maps FIELD_DECL -> bitflag.  */
typedef hash_map<tree, unsigned> field_access_map2_t;

/* Maps RECORD_TYPE -> (FIELD_DECL -> bitflag).  */
typedef hash_map<tree, field_access_map2_t *> record_field_map4_t;

/* Class used to determine if a FIELD is read, written or never accessed.  */
class type_accessor : public type_walker
{
public:
  type_accessor (record_field_map4_t &map) : _map4 (map) {};

  ~type_accessor () {};

  bool is_in_record_field_map (tree t);
  field_access_map2_t *get_from_record_field_map (tree t);
  void put_in_record_field_map (tree t, field_access_map2_t *);

private:
  /* Maps RECORD -> (FIELD_DECL -> bitflag).  */
  record_field_map4_t &_map4;

  /* Set of trees which are memoized and we don't need to look into them.  */
  hash_set<tree> memoized_map2;

  /* If a RECORD_TYPE is walked into, add all fields in struct to
     record_field_map.  */
  virtual void _walk_RECORD_TYPE_pre (tree t);
  void add_all_fields_in_struct (tree t);

  bool is_memoized (tree t);
};

/* Determine if a FIELD is read, written or never accessed from
   an expression.  */
class expr_accessor : public expr_walker
{
public:
  expr_accessor (record_field_map4_t &map)
    : _type_accessor (map) {};

  /* Expr E is accessed in A manner.  */
  void update (tree e, unsigned a);

  /* Print results.  */
  void print_accesses ();

  /* Add all fields to map.  Initialize with empty.  */
  void add_all_fields_in_struct (tree t);

  /* Aids expr-accessor in updating types.  */
  type_accessor _type_accessor;

private:
  /* Access {"Read", "Write", "Neither"} to propagate to all subexpressions.  */
  unsigned _access;

  /* Stack to keep track of how current subexpression was reached.  */
  auto_vec<tree> _stack2;

  /* Mark FIELD_DECL as read.
     If ADDR_EXPR is parent expression that means
     The address of a field is taken.  Mark
     all fields as possibly read.  */
  virtual void _walk_COMPONENT_REF_pre (tree e);

  /* Check if parent expression is MEM_REF.
     This means that an optimization was made
     and a FIELD_DECL is accessed via pointer
     arithmetic.  Mark all fields from start to the one
     accessed as read.
     TODO: We don't necessarily need to mark them as
     possibly read if we update these expressions to
     point to the correct address in the future.  */
  virtual void _walk_ADDR_EXPR_pre (tree e);

  /* Push to stack.  */
  virtual void _walk_pre (tree t);

  /* Pop from stack.  */
  virtual void _walk_post (tree t);
};

/* Walk all gimple and determine if fields were accessed.  */
class gimple_accessor : public gimple_walker
{
public:
  gimple_accessor (record_field_map4_t &map) : _expr_accessor (map) {};

  /* Print final results.  */
  void print_accesses ();

protected:
  /* Navigate expressions in gimple statements.  */
  expr_accessor _expr_accessor;

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

typedef hash_set<int_hash<int, -1, -2> > field_offsets2_t;
typedef hash_map<tree, field_offsets2_t *> record_field_offset_map4_t;


/* Compute set of not escaping unaccessed fields.  */
void
obtain_nonescaping_unaccessed_fields (tpartitions2_t casting,
				      record_field_map4_t &record_field_map,
				      int warning,
				      record_field_offset_map4_t &a);

extern bool detected_incompatible_syntax;

/* Map old RECORD_TYPE -> new RECORD_TYPE.  */
typedef hash_map<tree, tree> reorg_record_map2_t;

void
put_variants_in_map (reorg_record_map2_t &map);
void
place_pointers_inside_structs (reorg_record_map2_t &map);
void
place_pointers (reorg_record_map2_t &map);
void
replace_pointers_inside_structs (reorg_record_map2_t &map);
void
modify_pointers_in_other_types (hash_set<tree> &to_modify,
				reorg_record_map2_t &map2);
void
modify_pointer_to_pointer (hash_set<tree> &to_modify,
			   reorg_record_map2_t &map2);
void
remove_typed_cache_value_p (reorg_record_map2_t &map2);

extern const tpartitions2_t &tea_types;
unsigned
ipa_type_escape_analysis_init (void);
unsigned
ipa_type_escape_analysis_exit (bool keep_flag = false);
HOST_WIDE_INT bitpos_of_field (const tree);

#endif /* GCC_IPA_TYPE_ESCAPE_ANALYSIS_H.  */
