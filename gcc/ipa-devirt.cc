/* Basic IPA utilities for type inheritance graph construction and
   devirtualization.
   Copyright (C) 2013-2022 Free Software Foundation, Inc.
   Contributed by Jan Hubicka

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

/* Brief vocabulary:
     ODR = One Definition Rule
        In short, the ODR states that:
	1 In any translation unit, a template, type, function, or object can
	  have no more than one definition. Some of these can have any number
	  of declarations. A definition provides an instance.
        2 In the entire program, an object or non-inline function cannot have
	  more than one definition; if an object or function is used, it must
	  have exactly one definition. You can declare an object or function
	  that is never used, in which case you don't have to provide
	  a definition. In no event can there be more than one definition.
        3 Some things, like types, templates, and extern inline functions, can
	  be defined in more than one translation unit. For a given entity,
	  each definition must be the same. Non-extern objects and functions
	  in different translation units are different entities, even if their
	  names and types are the same.

     OTR = OBJ_TYPE_REF
       This is the Gimple representation of type information of a polymorphic call.
       It contains two parameters:
	 otr_type is a type of class whose method is called.
	 otr_token is the index into virtual table where address is taken.

     BINFO
       This is the type inheritance information attached to each tree
       RECORD_TYPE by the C++ frontend.  It provides information about base
       types and virtual tables.

       BINFO is linked to the RECORD_TYPE by TYPE_BINFO.
       BINFO also links to its type by BINFO_TYPE and to the virtual table by
       BINFO_VTABLE.

       Base types of a given type are enumerated by BINFO_BASE_BINFO
       vector.  Members of this vectors are not BINFOs associated
       with a base type.  Rather they are new copies of BINFOs
       (base BINFOs). Their virtual tables may differ from
       virtual table of the base type.  Also BINFO_OFFSET specifies
       offset of the base within the type.

       In the case of single inheritance, the virtual table is shared
       and BINFO_VTABLE of base BINFO is NULL.  In the case of multiple
       inheritance the individual virtual tables are pointer to by
       BINFO_VTABLE of base binfos (that differs of BINFO_VTABLE of
       binfo associated to the base type).

       BINFO lookup for a given base type and offset can be done by
       get_binfo_at_offset.  It returns proper BINFO whose virtual table
       can be used for lookup of virtual methods associated with the
       base type.

     token
       This is an index of virtual method in virtual table associated
       to the type defining it. Token can be looked up from OBJ_TYPE_REF
       or from DECL_VINDEX of a given virtual table.

     polymorphic (indirect) call
       This is callgraph representation of virtual method call.  Every
       polymorphic call contains otr_type and otr_token taken from
       original OBJ_TYPE_REF at callgraph construction time.

   What we do here:

   build_type_inheritance_graph triggers a construction of the type inheritance
   graph.

     We reconstruct it based on types of methods we see in the unit.
     This means that the graph is not complete. Types with no methods are not
     inserted into the graph.  Also types without virtual methods are not
     represented at all, though it may be easy to add this.

     The inheritance graph is represented as follows:

       Vertices are structures odr_type.  Every odr_type may correspond
       to one or more tree type nodes that are equivalent by ODR rule.
       (the multiple type nodes appear only with linktime optimization)

       Edges are represented by odr_type->base and odr_type->derived_types.
       At the moment we do not track offsets of types for multiple inheritance.
       Adding this is easy.

  possible_polymorphic_call_targets returns, given an parameters found in
  indirect polymorphic edge all possible polymorphic call targets of the call.

  pass_ipa_devirt performs simple speculative devirtualization.
*/

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "rtl.h"
#include "tree.h"
#include "gimple.h"
#include "gimple-iterator.h"
#include "gimplify.h"
#include "gimplify-me.h"
#include "cfghooks.h"
#include "cfganal.h"
#include "ssa.h"
#include "alloc-pool.h"
#include "tree-pass.h"
#include "tree-cfg.h"
#include "tree-dfa.h"
#include "tree-eh.h"
#include "tree-into-ssa.h"
#include "tree-cfgcleanup.h"
#include "cgraph.h"
#include "lto-streamer.h"
#include "fold-const.h"
#include "print-tree.h"
#include "calls.h"
#include "ipa-utils.h"
#include "gimple-fold.h"
#include "symbol-summary.h"
#include "tree-vrp.h"
#include "ipa-prop.h"
#include "ipa-fnsummary.h"
#include "demangle.h"
#include "dbgcnt.h"
#include "gimple-pretty-print.h"
#include "intl.h"
#include "stringpool.h"
#include "attribs.h"
#include "data-streamer.h"
#include "lto-streamer.h"
#include "streamer-hooks.h"

/* Hash based set of pairs of types.  */
struct type_pair
{
  tree first;
  tree second;
};

template <>
struct default_hash_traits <type_pair>
  : typed_noop_remove <type_pair>
{
  GTY((skip)) typedef type_pair value_type;
  GTY((skip)) typedef type_pair compare_type;
  static hashval_t
  hash (type_pair p)
  {
    return TYPE_UID (p.first) ^ TYPE_UID (p.second);
  }
  static const bool empty_zero_p = true;
  static bool
  is_empty (type_pair p)
  {
    return p.first == NULL;
  }
  static bool
  is_deleted (type_pair p ATTRIBUTE_UNUSED)
    {
      return false;
    }
  static bool
  equal (const type_pair &a, const type_pair &b)
    {
      return a.first==b.first && a.second == b.second;
    }
  static void
  mark_empty (type_pair &e)
    {
      e.first = NULL;
    }
};

/* HACK alert: this is used to communicate with ipa-inline-transform that
   thunk is being expanded and there is no need to clear the polymorphic
   call target cache.  */
bool thunk_expansion;

static bool odr_types_equivalent_p (tree, tree, bool, bool *,
				    hash_set<type_pair> *,
				    location_t, location_t);
static void warn_odr (tree t1, tree t2, tree st1, tree st2,
		      bool warn, bool *warned, const char *reason);

static bool odr_violation_reported = false;

static bool vcall_fixup_done = false;

/* Pointer set of all call targets appearing in the cache.  */
static hash_set<cgraph_node *> *cached_polymorphic_call_targets;

/* The node of type inheritance graph.  For each type unique in
   One Definition Rule (ODR) sense, we produce one node linking all
   main variants of types equivalent to it, bases and derived types.  */

struct GTY(()) odr_type_d
{
  /* leader type.  */
  tree type;
  /* All bases; built only for main variants of types.  */
  vec<odr_type> GTY((skip)) bases;
  /* All derived types with virtual methods seen in unit;
     built only for main variants of types.  */
  vec<odr_type> GTY((skip)) derived_types;

  /* All equivalent types, if more than one.  */
  vec<tree, va_gc> *types;
  /* Set of all equivalent types, if NON-NULL.  */
  hash_set<tree> * GTY((skip)) types_set;

  /* Unique ID indexing the type in odr_types array.  */
  int id;
  /* Is it in anonymous namespace? */
  bool anonymous_namespace;
  /* Did we report ODR violation here?  */
  bool odr_violated;
  /* Set when virtual table without RTTI prevailed table with.  */
  bool rtti_broken;
  /* Set when the canonical type is determined using the type name.  */
  bool tbaa_enabled;
  /* Set when type contains virtual base.  */
  bool has_virtual_base;

  bool whole_program_local_p ();

  /* Do we know about all derivations of given type?  */
  bool all_derivations_known_p ()
  {
    if (!RECORD_OR_UNION_TYPE_P (type))
      return true;

    if (TYPE_FINAL_P (type))
      return true;

    return whole_program_local_p ();
  }

  bool possibly_instantiated_p ();

  void set_has_virtual_base ()
  {
    if (!has_virtual_base)
      {
	unsigned i;
	odr_type derived;

	has_virtual_base = true;

	FOR_EACH_VEC_ELT (derived_types, i, derived)
	  derived->set_has_virtual_base ();
      }
  }
};

/* Given TYPE, return its primary vtable if it is a polymorphic class,
   otherwise return NULL.  */

tree
get_type_vtable (tree type)
{
  tree binfo = TYPE_BINFO (type);

  if (!binfo)
    return NULL;

  tree vtable = BINFO_VTABLE (binfo);
  unsigned HOST_WIDE_INT offset;

  if (!vtable || !vtable_pointer_value_to_vtable (vtable, &vtable, &offset))
    return NULL;

  return vtable;
}

/* Return TRUE if the ODR type is local in whole-program scope.

   This is typically true for final anonymous namespace types and types
   defined within functions (that may be COMDAT and thus shared across units,
   but with the same set of derived types).

   A FINAL type could not imply it is whole-program local, since it might
   be used in external library.  */

bool
odr_type_d::whole_program_local_p ()
{
  if (in_lto_p)
    return TYPE_CXX_LOCAL (type);

  /* Although a local class is always considered as whole program local in
     LGEN stage, but may not in LTO stage if multiple duplicated primary
     vtables are attached to the class due to C++ privatizing via -fno-weak.
     Thus, we can not set TYPE_CXX_LOCAL flag for local class at LGEN stage
     when building ODR type.  */
  return anonymous_namespace || decl_function_context (TYPE_NAME (type));
}

/* Return TRUE if ODR type may have any instance.  */

bool
odr_type_d::possibly_instantiated_p ()
{
  gcc_assert (symtab->state >= CONSTRUCTION);

  if (!RECORD_OR_UNION_TYPE_P (type) || !whole_program_local_p ())
    return true;

  tree vtable = get_type_vtable (type);

  if (!vtable)
    return true;

  varpool_node *vtable_node = varpool_node::get (vtable);

  /* FINAL class or class w/o virtual base has only one vtable, so just to
     check availability of primary vtable is enough.

     TODO: handle possible construction vtables when virtual inheritance
     exists.  */
  if (!has_virtual_base || derived_types.is_empty ())
    return vtable_node && vtable_node->definition;

  return true;
}

/* Return TRUE if T is local in whole-program scope.  */

static inline bool
type_whole_program_local_p (tree t)
{
  odr_type type = get_odr_type (t);

  return type && type->whole_program_local_p ();
}

/* Return true if T or type derived from T may have instance.  */

static bool
type_or_derived_type_possibly_instantiated_p (odr_type t)
{
  if (t->possibly_instantiated_p ())
    return true;
  for (auto derived : t->derived_types)
    if (type_or_derived_type_possibly_instantiated_p (derived))
      return true;
  return false;
}

/* Hash used to unify ODR types based on their mangled name and for anonymous
   namespace types.  */

struct odr_name_hasher : pointer_hash <odr_type_d>
{
  typedef union tree_node *compare_type;
  static inline hashval_t hash (const odr_type_d *);
  static inline bool equal (const odr_type_d *, const tree_node *);
  static inline void remove (odr_type_d *);
};

static bool
can_be_name_hashed_p (tree t)
{
  return (!in_lto_p || odr_type_p (t));
}

/* Hash type by its ODR name.  */

static hashval_t
hash_odr_name (const_tree t)
{
  gcc_checking_assert (TYPE_MAIN_VARIANT (t) == t);

  /* If not in LTO, all main variants are unique, so we can do
     pointer hash.  */
  if (!in_lto_p)
    return htab_hash_pointer (t);

  /* Anonymous types are unique.  */
  if (type_with_linkage_p (t) && type_in_anonymous_namespace_p (t))
    return htab_hash_pointer (t);

  gcc_checking_assert (TYPE_NAME (t)
		       && DECL_ASSEMBLER_NAME_SET_P (TYPE_NAME (t)));
  return IDENTIFIER_HASH_VALUE (DECL_ASSEMBLER_NAME (TYPE_NAME (t)));
}

/* Return the computed hashcode for ODR_TYPE.  */

inline hashval_t
odr_name_hasher::hash (const odr_type_d *odr_type)
{
  return hash_odr_name (odr_type->type);
}

/* For languages with One Definition Rule, work out if
   types are the same based on their name.

   This is non-trivial for LTO where minor differences in
   the type representation may have prevented type merging
   to merge two copies of otherwise equivalent type.

   Until we start streaming mangled type names, this function works
   only for polymorphic types.
*/

bool
types_same_for_odr (const_tree type1, const_tree type2)
{
  gcc_checking_assert (TYPE_P (type1) && TYPE_P (type2));

  type1 = TYPE_MAIN_VARIANT (type1);
  type2 = TYPE_MAIN_VARIANT (type2);

  if (type1 == type2)
    return true;

  if (!in_lto_p)
    return false;

  /* Anonymous namespace types are never duplicated.  */
  if ((type_with_linkage_p (type1) && type_in_anonymous_namespace_p (type1))
      || (type_with_linkage_p (type2) && type_in_anonymous_namespace_p (type2)))
    return false;

  /* If both type has mangled defined check if they are same.
     Watch for anonymous types which are all mangled as "<anon">.  */
  if (!type_with_linkage_p (type1) || !type_with_linkage_p (type2))
    return false;
  if (type_in_anonymous_namespace_p (type1)
      || type_in_anonymous_namespace_p (type2))
    return false;
  return (DECL_ASSEMBLER_NAME (TYPE_NAME (type1))
	  == DECL_ASSEMBLER_NAME (TYPE_NAME (type2)));
}

/* Return true if we can decide on ODR equivalency.

   In non-LTO it is always decide, in LTO however it depends in the type has
   ODR info attached. */

bool
types_odr_comparable (tree t1, tree t2)
{
  return (!in_lto_p
	  || TYPE_MAIN_VARIANT (t1) == TYPE_MAIN_VARIANT (t2)
	  || (odr_type_p (TYPE_MAIN_VARIANT (t1))
	      && odr_type_p (TYPE_MAIN_VARIANT (t2))));
}

/* Return true if T1 and T2 are ODR equivalent.  If ODR equivalency is not
   known, be conservative and return false.  */

bool
types_must_be_same_for_odr (tree t1, tree t2)
{
  if (types_odr_comparable (t1, t2))
    return types_same_for_odr (t1, t2);
  else
    return TYPE_MAIN_VARIANT (t1) == TYPE_MAIN_VARIANT (t2);
}

/* If T is compound type, return type it is based on.  */

static tree
compound_type_base (const_tree t)
{
  if (TREE_CODE (t) == ARRAY_TYPE
      || POINTER_TYPE_P (t)
      || TREE_CODE (t) == COMPLEX_TYPE
      || VECTOR_TYPE_P (t))
    return TREE_TYPE (t);
  if (TREE_CODE (t) == METHOD_TYPE)
    return TYPE_METHOD_BASETYPE (t);
  if (TREE_CODE (t) == OFFSET_TYPE)
    return TYPE_OFFSET_BASETYPE (t);
  return NULL_TREE;
}

/* Return true if T is either ODR type or compound type based from it.
   If the function return true, we know that T is a type originating from C++
   source even at link-time.  */

bool
odr_or_derived_type_p (const_tree t)
{
  do
    {
      if (odr_type_p (TYPE_MAIN_VARIANT (t)))
	return true;
      /* Function type is a tricky one. Basically we can consider it
	 ODR derived if return type or any of the parameters is.
	 We need to check all parameters because LTO streaming merges
	 common types (such as void) and they are not considered ODR then.  */
      if (TREE_CODE (t) == FUNCTION_TYPE)
	{
	  if (TYPE_METHOD_BASETYPE (t))
	    t = TYPE_METHOD_BASETYPE (t);
	  else
	   {
	     if (TREE_TYPE (t) && odr_or_derived_type_p (TREE_TYPE (t)))
	       return true;
	     for (t = TYPE_ARG_TYPES (t); t; t = TREE_CHAIN (t))
	       if (odr_or_derived_type_p (TYPE_MAIN_VARIANT (TREE_VALUE (t))))
		 return true;
	     return false;
	   }
	}
      else
	t = compound_type_base (t);
    }
  while (t);
  return t;
}

/* Compare types T1 and T2 and return true if they are
   equivalent.  */

inline bool
odr_name_hasher::equal (const odr_type_d *o1, const tree_node *t2)
{
  tree t1 = o1->type;

  gcc_checking_assert (TYPE_MAIN_VARIANT (t2) == t2);
  gcc_checking_assert (TYPE_MAIN_VARIANT (t1) == t1);
  if (t1 == t2)
    return true;
  if (!in_lto_p)
    return false;
  /* Check for anonymous namespaces.  */
  if ((type_with_linkage_p (t1) && type_in_anonymous_namespace_p (t1))
      || (type_with_linkage_p (t2) && type_in_anonymous_namespace_p (t2)))
    return false;
  gcc_checking_assert (DECL_ASSEMBLER_NAME (TYPE_NAME (t1)));
  gcc_checking_assert (DECL_ASSEMBLER_NAME (TYPE_NAME (t2)));
  return (DECL_ASSEMBLER_NAME (TYPE_NAME (t1))
	  == DECL_ASSEMBLER_NAME (TYPE_NAME (t2)));
}

/* Free ODR type V.  */

inline void
odr_name_hasher::remove (odr_type_d *v)
{
  v->bases.release ();
  v->derived_types.release ();
  if (v->types_set)
    delete v->types_set;
  ggc_free (v);
}

/* ODR type hash used to look up ODR type based on tree type node.  */

typedef hash_table<odr_name_hasher> odr_hash_type;
static odr_hash_type *odr_hash;

/* ODR types are also stored into ODR_TYPE vector to allow consistent
   walking.  Bases appear before derived types.  Vector is garbage collected
   so we won't end up visiting empty types.  */

static GTY(()) vec <odr_type, va_gc> *odr_types_ptr;
#define odr_types (*odr_types_ptr)

/* All enums defined and accessible for the unit.  */
static GTY(()) vec <tree, va_gc> *odr_enums;

/* Information we hold about value defined by an enum type.  */
struct odr_enum_val
{
  const char *name;
  wide_int val;
  location_t locus;
};

/* Information about enum values.  */
struct odr_enum
{
  location_t locus;
  auto_vec<odr_enum_val, 0> vals;
  bool warned;
};

/* A table of all ODR enum definitions.  */
static hash_map <nofree_string_hash, odr_enum> *odr_enum_map = NULL;
static struct obstack odr_enum_obstack;

/* Set TYPE_BINFO of TYPE and its variants to BINFO.  */
void
set_type_binfo (tree type, tree binfo)
{
  for (; type; type = TYPE_NEXT_VARIANT (type))
    if (COMPLETE_TYPE_P (type))
      TYPE_BINFO (type) = binfo;
    else
      gcc_assert (!TYPE_BINFO (type));
}

/* Return true if type variants match.
   This assumes that we already verified that T1 and T2 are variants of the
   same type.  */

static bool
type_variants_equivalent_p (tree t1, tree t2)
{
  if (TYPE_QUALS (t1) != TYPE_QUALS (t2))
    return false;

  if (comp_type_attributes (t1, t2) != 1)
    return false;

  if (COMPLETE_TYPE_P (t1) && COMPLETE_TYPE_P (t2)
      && TYPE_ALIGN (t1) != TYPE_ALIGN (t2))
    return false;

  return true;
}

/* Compare T1 and T2 based on name or structure.  */

static bool
odr_subtypes_equivalent_p (tree t1, tree t2,
			   hash_set<type_pair> *visited,
			   location_t loc1, location_t loc2)
{

  /* This can happen in incomplete types that should be handled earlier.  */
  gcc_assert (t1 && t2);

  if (t1 == t2)
    return true;

  /* Anonymous namespace types must match exactly.  */
  if ((type_with_linkage_p (TYPE_MAIN_VARIANT (t1))
       && type_in_anonymous_namespace_p (TYPE_MAIN_VARIANT (t1)))
      || (type_with_linkage_p (TYPE_MAIN_VARIANT (t2))
	  && type_in_anonymous_namespace_p (TYPE_MAIN_VARIANT (t2))))
    return false;

  /* For ODR types be sure to compare their names.
     To support -Wno-odr-type-merging we allow one type to be non-ODR
     and other ODR even though it is a violation.  */
  if (types_odr_comparable (t1, t2))
    {
      if (t1 != t2
	  && odr_type_p (TYPE_MAIN_VARIANT (t1))
	  && get_odr_type (TYPE_MAIN_VARIANT (t1), true)->odr_violated)
	return false;
      if (!types_same_for_odr (t1, t2))
        return false;
      if (!type_variants_equivalent_p (t1, t2))
	return false;
      /* Limit recursion: If subtypes are ODR types and we know
	 that they are same, be happy.  */
      if (odr_type_p (TYPE_MAIN_VARIANT (t1)))
        return true;
    }

  /* Component types, builtins and possibly violating ODR types
     have to be compared structurally.  */
  if (TREE_CODE (t1) != TREE_CODE (t2))
    return false;
  if (AGGREGATE_TYPE_P (t1)
      && (TYPE_NAME (t1) == NULL_TREE) != (TYPE_NAME (t2) == NULL_TREE))
    return false;

  type_pair pair={TYPE_MAIN_VARIANT (t1), TYPE_MAIN_VARIANT (t2)};
  if (TYPE_UID (TYPE_MAIN_VARIANT (t1)) > TYPE_UID (TYPE_MAIN_VARIANT (t2)))
    {
      pair.first = TYPE_MAIN_VARIANT (t2);
      pair.second = TYPE_MAIN_VARIANT (t1);
    }
  if (visited->add (pair))
    return true;
  if (!odr_types_equivalent_p (TYPE_MAIN_VARIANT (t1), TYPE_MAIN_VARIANT (t2),
			      false, NULL, visited, loc1, loc2))
    return false;
  if (!type_variants_equivalent_p (t1, t2))
    return false;
  return true;
}

/* Return true if DECL1 and DECL2 are identical methods.  Consider
   name equivalent to name.localalias.xyz.  */

static bool
methods_equal_p (tree decl1, tree decl2)
{
  if (DECL_ASSEMBLER_NAME (decl1) == DECL_ASSEMBLER_NAME (decl2))
    return true;
  const char sep = symbol_table::symbol_suffix_separator ();

  const char *name1 = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl1));
  const char *ptr1 = strchr (name1, sep);
  int len1 = ptr1 ? ptr1 - name1 : strlen (name1);

  const char *name2 = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl2));
  const char *ptr2 = strchr (name2, sep);
  int len2 = ptr2 ? ptr2 - name2 : strlen (name2);

  if (len1 != len2)
    return false;
  return !strncmp (name1, name2, len1);
}

/* Compare two virtual tables, PREVAILING and VTABLE and output ODR
   violation warnings.  */

void
compare_virtual_tables (varpool_node *prevailing, varpool_node *vtable)
{
  int n1, n2;

  if (DECL_VIRTUAL_P (prevailing->decl) != DECL_VIRTUAL_P (vtable->decl))
    {
      odr_violation_reported = true;
      if (DECL_VIRTUAL_P (prevailing->decl))
	{
	  varpool_node *tmp = prevailing;
	  prevailing = vtable;
	  vtable = tmp;
	}
      auto_diagnostic_group d;
      if (warning_at (DECL_SOURCE_LOCATION
			(TYPE_NAME (DECL_CONTEXT (vtable->decl))),
		      OPT_Wodr,
		      "virtual table of type %qD violates one definition rule",
		      DECL_CONTEXT (vtable->decl)))
	inform (DECL_SOURCE_LOCATION (prevailing->decl),
		"variable of same assembler name as the virtual table is "
		"defined in another translation unit");
      return;
    }
  if (!prevailing->definition || !vtable->definition)
    return;

  /* If we do not stream ODR type info, do not bother to do useful compare.  */
  if (!TYPE_BINFO (DECL_CONTEXT (vtable->decl))
      || !polymorphic_type_binfo_p (TYPE_BINFO (DECL_CONTEXT (vtable->decl))))
    return;

  odr_type class_type = get_odr_type (DECL_CONTEXT (vtable->decl), true);

  if (class_type->odr_violated)
    return;

  for (n1 = 0, n2 = 0; true; n1++, n2++)
    {
      struct ipa_ref *ref1, *ref2;
      bool end1, end2;

      end1 = !prevailing->iterate_reference (n1, ref1);
      end2 = !vtable->iterate_reference (n2, ref2);

      /* !DECL_VIRTUAL_P means RTTI entry;
	 We warn when RTTI is lost because non-RTTI prevails; we silently
	 accept the other case.  */
      while (!end2
	     && (end1
	         || (methods_equal_p (ref1->referred->decl,
				      ref2->referred->decl)
	             && TREE_CODE (ref1->referred->decl) == FUNCTION_DECL))
	     && TREE_CODE (ref2->referred->decl) != FUNCTION_DECL)
	{
	  if (!class_type->rtti_broken)
	    {
	      auto_diagnostic_group d;
	      if (warning_at (DECL_SOURCE_LOCATION
				  (TYPE_NAME (DECL_CONTEXT (vtable->decl))),
				OPT_Wodr,
				"virtual table of type %qD contains RTTI "
				"information",
				DECL_CONTEXT (vtable->decl)))
		{
		  inform (DECL_SOURCE_LOCATION
			      (TYPE_NAME (DECL_CONTEXT (prevailing->decl))),
			    "but is prevailed by one without from other"
			    " translation unit");
		  inform (DECL_SOURCE_LOCATION
			      (TYPE_NAME (DECL_CONTEXT (prevailing->decl))),
			    "RTTI will not work on this type");
		  class_type->rtti_broken = true;
		}
	    }
	  n2++;
          end2 = !vtable->iterate_reference (n2, ref2);
	}
      while (!end1
	     && (end2
	         || (methods_equal_p (ref2->referred->decl, ref1->referred->decl)
	             && TREE_CODE (ref2->referred->decl) == FUNCTION_DECL))
	     && TREE_CODE (ref1->referred->decl) != FUNCTION_DECL)
	{
	  n1++;
          end1 = !prevailing->iterate_reference (n1, ref1);
	}

      /* Finished?  */
      if (end1 && end2)
	{
	  /* Extra paranoia; compare the sizes.  We do not have information
	     about virtual inheritance offsets, so just be sure that these
	     match. 
	     Do this as very last check so the not very informative error
	     is not output too often.  */
	  if (DECL_SIZE (prevailing->decl) != DECL_SIZE (vtable->decl))
	    {
	      class_type->odr_violated = true;
	      auto_diagnostic_group d;
	      tree ctx = TYPE_NAME (DECL_CONTEXT (vtable->decl));
	      if (warning_at (DECL_SOURCE_LOCATION (ctx), OPT_Wodr,
			      "virtual table of type %qD violates "
			      "one definition rule",
			      DECL_CONTEXT (vtable->decl)))
		{
		  ctx = TYPE_NAME (DECL_CONTEXT (prevailing->decl));
		  inform (DECL_SOURCE_LOCATION (ctx),
			  "the conflicting type defined in another translation"
			  " unit has virtual table of different size");
		}
	    }
	  return;
	}

      if (!end1 && !end2)
	{
	  if (methods_equal_p (ref1->referred->decl, ref2->referred->decl))
	    continue;

	  class_type->odr_violated = true;

	  /* If the loops above stopped on non-virtual pointer, we have
	     mismatch in RTTI information mangling.  */
	  if (TREE_CODE (ref1->referred->decl) != FUNCTION_DECL
	      && TREE_CODE (ref2->referred->decl) != FUNCTION_DECL)
	    {
	      auto_diagnostic_group d;
	      if (warning_at (DECL_SOURCE_LOCATION
				(TYPE_NAME (DECL_CONTEXT (vtable->decl))),
			      OPT_Wodr,
			      "virtual table of type %qD violates "
			      "one definition rule",
			      DECL_CONTEXT (vtable->decl)))
		{
		  inform (DECL_SOURCE_LOCATION
			    (TYPE_NAME (DECL_CONTEXT (prevailing->decl))),
			  "the conflicting type defined in another translation "
			  "unit with different RTTI information");
		}
	      return;
	    }
	  /* At this point both REF1 and REF2 points either to virtual table
	     or virtual method.  If one points to virtual table and other to
	     method we can complain the same way as if one table was shorter
	     than other pointing out the extra method.  */
	  if (TREE_CODE (ref1->referred->decl)
	      != TREE_CODE (ref2->referred->decl))
	    {
	      if (VAR_P (ref1->referred->decl))
		end1 = true;
	      else if (VAR_P (ref2->referred->decl))
		end2 = true;
	    }
	}

      class_type->odr_violated = true;

      /* Complain about size mismatch.  Either we have too many virtual
 	 functions or too many virtual table pointers.  */
      if (end1 || end2)
	{
	  if (end1)
	    {
	      varpool_node *tmp = prevailing;
	      prevailing = vtable;
	      vtable = tmp;
	      ref1 = ref2;
	    }
	  auto_diagnostic_group d;
	  if (warning_at (DECL_SOURCE_LOCATION
			    (TYPE_NAME (DECL_CONTEXT (vtable->decl))),
			  OPT_Wodr,
			  "virtual table of type %qD violates "
			  "one definition rule",
			  DECL_CONTEXT (vtable->decl)))
	    {
	      if (TREE_CODE (ref1->referring->decl) == FUNCTION_DECL)
		{
		  inform (DECL_SOURCE_LOCATION
			   (TYPE_NAME (DECL_CONTEXT (prevailing->decl))),
			  "the conflicting type defined in another translation "
			  "unit");
		  inform (DECL_SOURCE_LOCATION
			    (TYPE_NAME (DECL_CONTEXT (ref1->referring->decl))),
			  "contains additional virtual method %qD",
			  ref1->referred->decl);
		}
	      else
		{
		  inform (DECL_SOURCE_LOCATION
			   (TYPE_NAME (DECL_CONTEXT (prevailing->decl))),
			  "the conflicting type defined in another translation "
			  "unit has virtual table with more entries");
		}
	    }
	  return;
	}

      /* And in the last case we have either mismatch in between two virtual
	 methods or two virtual table pointers.  */
      auto_diagnostic_group d;
      if (warning_at (DECL_SOURCE_LOCATION
			(TYPE_NAME (DECL_CONTEXT (vtable->decl))), OPT_Wodr,
		      "virtual table of type %qD violates "
		      "one definition rule",
		      DECL_CONTEXT (vtable->decl)))
	{
	  if (TREE_CODE (ref1->referred->decl) == FUNCTION_DECL)
	    {
	      inform (DECL_SOURCE_LOCATION
			(TYPE_NAME (DECL_CONTEXT (prevailing->decl))),
		      "the conflicting type defined in another translation "
		      "unit");
	      gcc_assert (TREE_CODE (ref2->referred->decl)
			  == FUNCTION_DECL);
	      inform (DECL_SOURCE_LOCATION
			 (ref1->referred->ultimate_alias_target ()->decl),
		      "virtual method %qD",
		      ref1->referred->ultimate_alias_target ()->decl);
	      inform (DECL_SOURCE_LOCATION
			 (ref2->referred->ultimate_alias_target ()->decl),
		      "ought to match virtual method %qD but does not",
		      ref2->referred->ultimate_alias_target ()->decl);
	    }
	  else
	    inform (DECL_SOURCE_LOCATION
		      (TYPE_NAME (DECL_CONTEXT (prevailing->decl))),
		    "the conflicting type defined in another translation "
		    "unit has virtual table with different contents");
	  return;
	}
    }
}

/* Output ODR violation warning about T1 and T2 with REASON.
   Display location of ST1 and ST2 if REASON speaks about field or
   method of the type.
   If WARN is false, do nothing. Set WARNED if warning was indeed
   output.  */

static void
warn_odr (tree t1, tree t2, tree st1, tree st2,
	  bool warn, bool *warned, const char *reason)
{
  tree decl2 = TYPE_NAME (TYPE_MAIN_VARIANT (t2));
  if (warned)
    *warned = false;

  if (!warn || !TYPE_NAME(TYPE_MAIN_VARIANT (t1)))
    return;

  /* ODR warnings are output during LTO streaming; we must apply location
     cache for potential warnings to be output correctly.  */
  if (lto_location_cache::current_cache)
    lto_location_cache::current_cache->apply_location_cache ();

  auto_diagnostic_group d;
  if (t1 != TYPE_MAIN_VARIANT (t1)
      && TYPE_NAME (t1) != TYPE_NAME (TYPE_MAIN_VARIANT (t1)))
    {
      if (!warning_at (DECL_SOURCE_LOCATION (TYPE_NAME (TYPE_MAIN_VARIANT (t1))),
		       OPT_Wodr, "type %qT (typedef of %qT) violates the "
		       "C++ One Definition Rule",
		       t1, TYPE_MAIN_VARIANT (t1)))
	return;
    }
  else
    {
      if (!warning_at (DECL_SOURCE_LOCATION (TYPE_NAME (TYPE_MAIN_VARIANT (t1))),
		       OPT_Wodr, "type %qT violates the C++ One Definition Rule",
		       t1))
	return;
    }
  if (!st1 && !st2)
    ;
  /* For FIELD_DECL support also case where one of fields is
     NULL - this is used when the structures have mismatching number of
     elements.  */
  else if (!st1 || TREE_CODE (st1) == FIELD_DECL)
    {
      inform (DECL_SOURCE_LOCATION (decl2),
	      "a different type is defined in another translation unit");
      if (!st1)
	{
	  st1 = st2;
	  st2 = NULL;
	}
      inform (DECL_SOURCE_LOCATION (st1),
	      "the first difference of corresponding definitions is field %qD",
	      st1);
      if (st2)
        decl2 = st2;
    }
  else if (TREE_CODE (st1) == FUNCTION_DECL)
    {
      inform (DECL_SOURCE_LOCATION (decl2),
	      "a different type is defined in another translation unit");
      inform (DECL_SOURCE_LOCATION (st1),
	      "the first difference of corresponding definitions is method %qD",
	      st1);
      decl2 = st2;
    }
  else
    return;
  inform (DECL_SOURCE_LOCATION (decl2), reason);

  if (warned)
    *warned = true;
}

/* Return true if T1 and T2 are incompatible and we want to recursively
   dive into them from warn_type_mismatch to give sensible answer.  */

static bool
type_mismatch_p (tree t1, tree t2)
{
  if (odr_or_derived_type_p (t1) && odr_or_derived_type_p (t2)
      && !odr_types_equivalent_p (t1, t2))
    return true;
  return !types_compatible_p (t1, t2);
}


/* Types T1 and T2 was found to be incompatible in a context they can't
   (either used to declare a symbol of same assembler name or unified by
   ODR rule).  We already output warning about this, but if possible, output
   extra information on how the types mismatch.

   This is hard to do in general.  We basically handle the common cases.

   If LOC1 and LOC2 are meaningful locations, use it in the case the types
   themselves do not have one.  */

void
warn_types_mismatch (tree t1, tree t2, location_t loc1, location_t loc2)
{
  /* Location of type is known only if it has TYPE_NAME and the name is
     TYPE_DECL.  */
  location_t loc_t1 = TYPE_NAME (t1) && TREE_CODE (TYPE_NAME (t1)) == TYPE_DECL
		      ? DECL_SOURCE_LOCATION (TYPE_NAME (t1))
		      : UNKNOWN_LOCATION;
  location_t loc_t2 = TYPE_NAME (t2) && TREE_CODE (TYPE_NAME (t2)) == TYPE_DECL
		      ? DECL_SOURCE_LOCATION (TYPE_NAME (t2))
		      : UNKNOWN_LOCATION;
  bool loc_t2_useful = false;

  /* With LTO it is a common case that the location of both types match.
     See if T2 has a location that is different from T1. If so, we will
     inform user about the location.
     Do not consider the location passed to us in LOC1/LOC2 as those are
     already output.  */
  if (loc_t2 > BUILTINS_LOCATION && loc_t2 != loc_t1)
    {
      if (loc_t1 <= BUILTINS_LOCATION)
	loc_t2_useful = true;
      else
	{
	  expanded_location xloc1 = expand_location (loc_t1);
	  expanded_location xloc2 = expand_location (loc_t2);

	  if (strcmp (xloc1.file, xloc2.file)
	      || xloc1.line != xloc2.line
	      || xloc1.column != xloc2.column)
	    loc_t2_useful = true;
	}
    }

  if (loc_t1 <= BUILTINS_LOCATION)
    loc_t1 = loc1;
  if (loc_t2 <= BUILTINS_LOCATION)
    loc_t2 = loc2;

  location_t loc = loc_t1 <= BUILTINS_LOCATION ? loc_t2 : loc_t1;

  /* It is a quite common bug to reference anonymous namespace type in
     non-anonymous namespace class.  */
  tree mt1 = TYPE_MAIN_VARIANT (t1);
  tree mt2 = TYPE_MAIN_VARIANT (t2);
  if ((type_with_linkage_p (mt1)
       && type_in_anonymous_namespace_p (mt1))
      || (type_with_linkage_p (mt2)
	  && type_in_anonymous_namespace_p (mt2)))
    {
      if (!type_with_linkage_p (mt1)
	  || !type_in_anonymous_namespace_p (mt1))
	{
	  std::swap (t1, t2);
	  std::swap (mt1, mt2);
	  std::swap (loc_t1, loc_t2);
	}
      gcc_assert (TYPE_NAME (mt1)
		  && TREE_CODE (TYPE_NAME (mt1)) == TYPE_DECL);
      tree n1 = TYPE_NAME (mt1);
      tree n2 = TYPE_NAME (mt2) ? TYPE_NAME (mt2) : NULL;

      if (TREE_CODE (n1) == TYPE_DECL)
	n1 = DECL_NAME (n1);
      if (n2 && TREE_CODE (n2) == TYPE_DECL)
	n2 = DECL_NAME (n2);
      /* Most of the time, the type names will match, do not be unnecessarily
         verbose.  */
      if (n1 != n2)
        inform (loc_t1,
	        "type %qT defined in anonymous namespace cannot match "
	        "type %qT across the translation unit boundary",
	        t1, t2);
      else
        inform (loc_t1,
	        "type %qT defined in anonymous namespace cannot match "
	        "across the translation unit boundary",
	        t1);
      if (loc_t2_useful)
        inform (loc_t2,
	        "the incompatible type defined in another translation unit");
      return;
    }
  /* If types have mangled ODR names and they are different, it is most
     informative to output those.
     This also covers types defined in different namespaces.  */
  const char *odr1 = get_odr_name_for_type (mt1);
  const char *odr2 = get_odr_name_for_type (mt2);
  if (odr1 != NULL && odr2 != NULL && odr1 != odr2)
    {
      const int opts = DMGL_PARAMS | DMGL_ANSI | DMGL_TYPES;
      char *name1 = xstrdup (cplus_demangle (odr1, opts));
      char *name2 = cplus_demangle (odr2, opts);
      if (name1 && name2 && strcmp (name1, name2))
	{
	  inform (loc_t1,
		  "type name %qs should match type name %qs",
		  name1, name2);
	  if (loc_t2_useful)
	    inform (loc_t2,
		    "the incompatible type is defined here");
	  free (name1);
	  return;
	}
      free (name1);
    }
  /* A tricky case are compound types.  Often they appear the same in source
     code and the mismatch is dragged in by type they are build from.
     Look for those differences in subtypes and try to be informative.  In other
     cases just output nothing because the source code is probably different
     and in this case we already output a all necessary info.  */
  if (!TYPE_NAME (t1) || !TYPE_NAME (t2))
    {
      if (TREE_CODE (t1) == TREE_CODE (t2))
	{
	  if (TREE_CODE (t1) == ARRAY_TYPE
	      && COMPLETE_TYPE_P (t1) && COMPLETE_TYPE_P (t2))
	    {
	      tree i1 = TYPE_DOMAIN (t1);
	      tree i2 = TYPE_DOMAIN (t2);
	
	      if (i1 && i2
		  && TYPE_MAX_VALUE (i1)
		  && TYPE_MAX_VALUE (i2)
		  && !operand_equal_p (TYPE_MAX_VALUE (i1),
				       TYPE_MAX_VALUE (i2), 0))
		{
		  inform (loc,
			  "array types have different bounds");
		  return;
		}
	    }
	  if ((POINTER_TYPE_P (t1) || TREE_CODE (t1) == ARRAY_TYPE)
	      && type_mismatch_p (TREE_TYPE (t1), TREE_TYPE (t2)))
	    warn_types_mismatch (TREE_TYPE (t1), TREE_TYPE (t2), loc_t1, loc_t2);
	  else if (TREE_CODE (t1) == METHOD_TYPE
		   || TREE_CODE (t1) == FUNCTION_TYPE)
	    {
	      tree parms1 = NULL, parms2 = NULL;
	      int count = 1;

	      if (type_mismatch_p (TREE_TYPE (t1), TREE_TYPE (t2)))
		{
		  inform (loc, "return value type mismatch");
		  warn_types_mismatch (TREE_TYPE (t1), TREE_TYPE (t2), loc_t1,
				       loc_t2);
		  return;
		}
	      if (prototype_p (t1) && prototype_p (t2))
		for (parms1 = TYPE_ARG_TYPES (t1), parms2 = TYPE_ARG_TYPES (t2);
		     parms1 && parms2;
		     parms1 = TREE_CHAIN (parms1), parms2 = TREE_CHAIN (parms2),
		     count++)
		  {
		    if (type_mismatch_p (TREE_VALUE (parms1), TREE_VALUE (parms2)))
		      {
			if (count == 1 && TREE_CODE (t1) == METHOD_TYPE)
			  inform (loc,
				  "implicit this pointer type mismatch");
			else
			  inform (loc,
				  "type mismatch in parameter %i",
				  count - (TREE_CODE (t1) == METHOD_TYPE));
			warn_types_mismatch (TREE_VALUE (parms1),
					     TREE_VALUE (parms2),
					     loc_t1, loc_t2);
			return;
		      }
		  }
	      if (parms1 || parms2)
		{
		  inform (loc,
			  "types have different parameter counts");
		  return;
		}
	    }
	}
      return;
    }

  if (types_odr_comparable (t1, t2)
      /* We make assign integers mangled names to be able to handle
	 signed/unsigned chars.  Accepting them here would however lead to
	 confusing message like
	 "type ‘const int’ itself violates the C++ One Definition Rule"  */
      && TREE_CODE (t1) != INTEGER_TYPE
      && types_same_for_odr (t1, t2))
    inform (loc_t1,
	    "type %qT itself violates the C++ One Definition Rule", t1);
  /* Prevent pointless warnings like "struct aa" should match "struct aa".  */
  else if (TYPE_NAME (t1) == TYPE_NAME (t2)
	   && TREE_CODE (t1) == TREE_CODE (t2) && !loc_t2_useful)
    return;
  else
    inform (loc_t1, "type %qT should match type %qT",
	    t1, t2);
  if (loc_t2_useful)
    inform (loc_t2, "the incompatible type is defined here");
}

/* Return true if T should be ignored in TYPE_FIELDS for ODR comparison.  */

static bool
skip_in_fields_list_p (tree t)
{
  if (TREE_CODE (t) != FIELD_DECL)
    return true;
  /* C++ FE introduces zero sized fields depending on -std setting, see
     PR89358.  */
  if (DECL_SIZE (t)
      && integer_zerop (DECL_SIZE (t))
      && DECL_ARTIFICIAL (t)
      && DECL_IGNORED_P (t)
      && !DECL_NAME (t))
    return true;
  return false;
}

/* Compare T1 and T2, report ODR violations if WARN is true and set
   WARNED to true if anything is reported.  Return true if types match.
   If true is returned, the types are also compatible in the sense of
   gimple_canonical_types_compatible_p.
   If LOC1 and LOC2 is not UNKNOWN_LOCATION it may be used to output a warning
   about the type if the type itself do not have location.  */

static bool
odr_types_equivalent_p (tree t1, tree t2, bool warn, bool *warned,
			hash_set<type_pair> *visited,
			location_t loc1, location_t loc2)
{
  /* Check first for the obvious case of pointer identity.  */
  if (t1 == t2)
    return true;

  /* Can't be the same type if the types don't have the same code.  */
  if (TREE_CODE (t1) != TREE_CODE (t2))
    {
      warn_odr (t1, t2, NULL, NULL, warn, warned,
	        G_("a different type is defined in another translation unit"));
      return false;
    }

  if ((type_with_linkage_p (TYPE_MAIN_VARIANT (t1))
       && type_in_anonymous_namespace_p (TYPE_MAIN_VARIANT (t1)))
      || (type_with_linkage_p (TYPE_MAIN_VARIANT (t2))
	  && type_in_anonymous_namespace_p (TYPE_MAIN_VARIANT (t2))))
    {
      /* We cannot trip this when comparing ODR types, only when trying to
	 match different ODR derivations from different declarations.
	 So WARN should be always false.  */
      gcc_assert (!warn);
      return false;
    }

  /* Non-aggregate types can be handled cheaply.  */
  if (INTEGRAL_TYPE_P (t1)
      || SCALAR_FLOAT_TYPE_P (t1)
      || FIXED_POINT_TYPE_P (t1)
      || TREE_CODE (t1) == VECTOR_TYPE
      || TREE_CODE (t1) == COMPLEX_TYPE
      || TREE_CODE (t1) == OFFSET_TYPE
      || POINTER_TYPE_P (t1))
    {
      if (TYPE_PRECISION (t1) != TYPE_PRECISION (t2))
	{
	  warn_odr (t1, t2, NULL, NULL, warn, warned,
		    G_("a type with different precision is defined "
		       "in another translation unit"));
	  return false;
	}
      if (TYPE_UNSIGNED (t1) != TYPE_UNSIGNED (t2))
	{
	  warn_odr (t1, t2, NULL, NULL, warn, warned,
		    G_("a type with different signedness is defined "
		       "in another translation unit"));
	  return false;
	}

      if (TREE_CODE (t1) == INTEGER_TYPE
	  && TYPE_STRING_FLAG (t1) != TYPE_STRING_FLAG (t2))
	{
	  /* char WRT uint_8?  */
	  warn_odr (t1, t2, NULL, NULL, warn, warned,
		    G_("a different type is defined in another "
		       "translation unit"));
	  return false;
	}

      /* For canonical type comparisons we do not want to build SCCs
	 so we cannot compare pointed-to types.  But we can, for now,
	 require the same pointed-to type kind and match what
	 useless_type_conversion_p would do.  */
      if (POINTER_TYPE_P (t1))
	{
	  if (TYPE_ADDR_SPACE (TREE_TYPE (t1))
	      != TYPE_ADDR_SPACE (TREE_TYPE (t2)))
	    {
	      warn_odr (t1, t2, NULL, NULL, warn, warned,
			G_("it is defined as a pointer in different address "
			   "space in another translation unit"));
	      return false;
	    }

	  if (!odr_subtypes_equivalent_p (TREE_TYPE (t1), TREE_TYPE (t2),
					  visited, loc1, loc2))
	    {
	      warn_odr (t1, t2, NULL, NULL, warn, warned,
			G_("it is defined as a pointer to different type "
			   "in another translation unit"));
	      if (warn && warned)
	        warn_types_mismatch (TREE_TYPE (t1), TREE_TYPE (t2),
				     loc1, loc2);
	      return false;
	    }
	}

      if ((TREE_CODE (t1) == VECTOR_TYPE || TREE_CODE (t1) == COMPLEX_TYPE)
	  && !odr_subtypes_equivalent_p (TREE_TYPE (t1), TREE_TYPE (t2),
					 visited, loc1, loc2))
	{
	  /* Probably specific enough.  */
	  warn_odr (t1, t2, NULL, NULL, warn, warned,
		    G_("a different type is defined "
		       "in another translation unit"));
	  if (warn && warned)
	    warn_types_mismatch (TREE_TYPE (t1), TREE_TYPE (t2), loc1, loc2);
	  return false;
	}
    }
  /* Do type-specific comparisons.  */
  else switch (TREE_CODE (t1))
    {
    case ARRAY_TYPE:
      {
	/* Array types are the same if the element types are the same and
	   the number of elements are the same.  */
	if (!odr_subtypes_equivalent_p (TREE_TYPE (t1), TREE_TYPE (t2),
					visited, loc1, loc2))
	  {
	    warn_odr (t1, t2, NULL, NULL, warn, warned,
		      G_("a different type is defined in another "
			 "translation unit"));
	    if (warn && warned)
	      warn_types_mismatch (TREE_TYPE (t1), TREE_TYPE (t2), loc1, loc2);
	  }
	gcc_assert (TYPE_STRING_FLAG (t1) == TYPE_STRING_FLAG (t2));
	gcc_assert (TYPE_NONALIASED_COMPONENT (t1)
		    == TYPE_NONALIASED_COMPONENT (t2));

	tree i1 = TYPE_DOMAIN (t1);
	tree i2 = TYPE_DOMAIN (t2);

	/* For an incomplete external array, the type domain can be
	   NULL_TREE.  Check this condition also.  */
	if (i1 == NULL_TREE || i2 == NULL_TREE)
          return type_variants_equivalent_p (t1, t2);

	tree min1 = TYPE_MIN_VALUE (i1);
	tree min2 = TYPE_MIN_VALUE (i2);
	tree max1 = TYPE_MAX_VALUE (i1);
	tree max2 = TYPE_MAX_VALUE (i2);

	/* In C++, minimums should be always 0.  */
	gcc_assert (min1 == min2);
	if (!operand_equal_p (max1, max2, 0))
	  {
	    warn_odr (t1, t2, NULL, NULL, warn, warned,
		      G_("an array of different size is defined "
			 "in another translation unit"));
	    return false;
	  }
      }
    break;

    case METHOD_TYPE:
    case FUNCTION_TYPE:
      /* Function types are the same if the return type and arguments types
	 are the same.  */
      if (!odr_subtypes_equivalent_p (TREE_TYPE (t1), TREE_TYPE (t2),
				      visited, loc1, loc2))
	{
	  warn_odr (t1, t2, NULL, NULL, warn, warned,
		    G_("has different return value "
		       "in another translation unit"));
	  if (warn && warned)
	    warn_types_mismatch (TREE_TYPE (t1), TREE_TYPE (t2), loc1, loc2);
	  return false;
	}

      if (TYPE_ARG_TYPES (t1) == TYPE_ARG_TYPES (t2)
	  || !prototype_p (t1) || !prototype_p (t2))
        return type_variants_equivalent_p (t1, t2);
      else
	{
	  tree parms1, parms2;

	  for (parms1 = TYPE_ARG_TYPES (t1), parms2 = TYPE_ARG_TYPES (t2);
	       parms1 && parms2;
	       parms1 = TREE_CHAIN (parms1), parms2 = TREE_CHAIN (parms2))
	    {
	      if (!odr_subtypes_equivalent_p
		     (TREE_VALUE (parms1), TREE_VALUE (parms2),
		      visited, loc1, loc2))
		{
		  warn_odr (t1, t2, NULL, NULL, warn, warned,
			    G_("has different parameters in another "
			       "translation unit"));
		  if (warn && warned)
		    warn_types_mismatch (TREE_VALUE (parms1),
					 TREE_VALUE (parms2), loc1, loc2);
		  return false;
		}
	    }

	  if (parms1 || parms2)
	    {
	      warn_odr (t1, t2, NULL, NULL, warn, warned,
			G_("has different parameters "
			   "in another translation unit"));
	      return false;
	    }

          return type_variants_equivalent_p (t1, t2);
	}

    case RECORD_TYPE:
    case UNION_TYPE:
    case QUAL_UNION_TYPE:
      {
	tree f1, f2;

	/* For aggregate types, all the fields must be the same.  */
	if (COMPLETE_TYPE_P (t1) && COMPLETE_TYPE_P (t2))
	  {
	    if (TYPE_BINFO (t1) && TYPE_BINFO (t2)
	        && polymorphic_type_binfo_p (TYPE_BINFO (t1))
		   != polymorphic_type_binfo_p (TYPE_BINFO (t2)))
	      {
		if (polymorphic_type_binfo_p (TYPE_BINFO (t1)))
		  warn_odr (t1, t2, NULL, NULL, warn, warned,
			    G_("a type defined in another translation unit "
			       "is not polymorphic"));
		else
		  warn_odr (t1, t2, NULL, NULL, warn, warned,
			    G_("a type defined in another translation unit "
			       "is polymorphic"));
		return false;
	      }
	    for (f1 = TYPE_FIELDS (t1), f2 = TYPE_FIELDS (t2);
		 f1 || f2;
		 f1 = TREE_CHAIN (f1), f2 = TREE_CHAIN (f2))
	      {
		/* Skip non-fields.  */
		while (f1 && skip_in_fields_list_p (f1))
		  f1 = TREE_CHAIN (f1);
		while (f2 && skip_in_fields_list_p (f2))
		  f2 = TREE_CHAIN (f2);
		if (!f1 || !f2)
		  break;
		if (DECL_VIRTUAL_P (f1) != DECL_VIRTUAL_P (f2))
		  {
		    warn_odr (t1, t2, NULL, NULL, warn, warned,
			      G_("a type with different virtual table pointers"
			         " is defined in another translation unit"));
		    return false;
		  }
		if (DECL_ARTIFICIAL (f1) != DECL_ARTIFICIAL (f2))
		  {
		    warn_odr (t1, t2, NULL, NULL, warn, warned,
			      G_("a type with different bases is defined "
				 "in another translation unit"));
		    return false;
		  }
		if (DECL_NAME (f1) != DECL_NAME (f2)
		    && !DECL_ARTIFICIAL (f1))
		  {
		    warn_odr (t1, t2, f1, f2, warn, warned,
			      G_("a field with different name is defined "
				 "in another translation unit"));
		    return false;
		  }
		if (!odr_subtypes_equivalent_p (TREE_TYPE (f1),
						TREE_TYPE (f2),
						visited, loc1, loc2))
		  {
		    /* Do not warn about artificial fields and just go into
 		       generic field mismatch warning.  */
		    if (DECL_ARTIFICIAL (f1))
		      break;

		    warn_odr (t1, t2, f1, f2, warn, warned,
			      G_("a field of same name but different type "
				 "is defined in another translation unit"));
		    if (warn && warned)
		      warn_types_mismatch (TREE_TYPE (f1), TREE_TYPE (f2), loc1, loc2);
		    return false;
		  }
		if (!gimple_compare_field_offset (f1, f2))
		  {
		    /* Do not warn about artificial fields and just go into
		       generic field mismatch warning.  */
		    if (DECL_ARTIFICIAL (f1))
		      break;
		    warn_odr (t1, t2, f1, f2, warn, warned,
			      G_("fields have different layout "
				 "in another translation unit"));
		    return false;
		  }
		if (DECL_BIT_FIELD (f1) != DECL_BIT_FIELD (f2))
		  {
		    warn_odr (t1, t2, f1, f2, warn, warned,
			      G_("one field is a bitfield while the other "
				 "is not"));
		    return false;
		  }
		else
		  gcc_assert (DECL_NONADDRESSABLE_P (f1)
			      == DECL_NONADDRESSABLE_P (f2));
	      }

	    /* If one aggregate has more fields than the other, they
	       are not the same.  */
	    if (f1 || f2)
	      {
		if ((f1 && DECL_VIRTUAL_P (f1)) || (f2 && DECL_VIRTUAL_P (f2)))
		  warn_odr (t1, t2, NULL, NULL, warn, warned,
			    G_("a type with different virtual table pointers"
			       " is defined in another translation unit"));
		else if ((f1 && DECL_ARTIFICIAL (f1))
		         || (f2 && DECL_ARTIFICIAL (f2)))
		  warn_odr (t1, t2, NULL, NULL, warn, warned,
			    G_("a type with different bases is defined "
			       "in another translation unit"));
		else
		  warn_odr (t1, t2, f1, f2, warn, warned,
			    G_("a type with different number of fields "
			       "is defined in another translation unit"));
		
		return false;
	      }
	  }
	break;
      }
    case VOID_TYPE:
    case OPAQUE_TYPE:
    case NULLPTR_TYPE:
      break;

    default:
      debug_tree (t1);
      gcc_unreachable ();
    }

  /* Those are better to come last as they are utterly uninformative.  */
  if (TYPE_SIZE (t1) && TYPE_SIZE (t2)
      && !operand_equal_p (TYPE_SIZE (t1), TYPE_SIZE (t2), 0))
    {
      warn_odr (t1, t2, NULL, NULL, warn, warned,
		G_("a type with different size "
		   "is defined in another translation unit"));
      return false;
    }

  if (TREE_ADDRESSABLE (t1) != TREE_ADDRESSABLE (t2)
      && COMPLETE_TYPE_P (t1) && COMPLETE_TYPE_P (t2))
    {
      warn_odr (t1, t2, NULL, NULL, warn, warned,
		G_("one type needs to be constructed while the other does not"));
      gcc_checking_assert (RECORD_OR_UNION_TYPE_P (t1));
      return false;
    }
  /* There is no really good user facing warning for this.
     Either the original reason for modes being different is lost during
     streaming or we should catch earlier warnings.  We however must detect
     the mismatch to avoid type verifier from cmplaining on mismatched
     types between type and canonical type. See PR91576.  */
  if (TYPE_MODE (t1) != TYPE_MODE (t2)
      && COMPLETE_TYPE_P (t1) && COMPLETE_TYPE_P (t2))
    {
      warn_odr (t1, t2, NULL, NULL, warn, warned,
		G_("memory layout mismatch"));
      return false;
    }

  gcc_assert (!TYPE_SIZE_UNIT (t1) || !TYPE_SIZE_UNIT (t2)
	      || operand_equal_p (TYPE_SIZE_UNIT (t1),
				  TYPE_SIZE_UNIT (t2), 0));
  return type_variants_equivalent_p (t1, t2);
}

/* Return true if TYPE1 and TYPE2 are equivalent for One Definition Rule.  */

bool
odr_types_equivalent_p (tree type1, tree type2)
{
  gcc_checking_assert (odr_or_derived_type_p (type1)
		       && odr_or_derived_type_p (type2));

  hash_set<type_pair> visited;
  return odr_types_equivalent_p (type1, type2, false, NULL,
			         &visited, UNKNOWN_LOCATION, UNKNOWN_LOCATION);
}

/* TYPE is equivalent to VAL by ODR, but its tree representation differs
   from VAL->type.  This may happen in LTO where tree merging did not merge
   all variants of the same type or due to ODR violation.

   Analyze and report ODR violations and add type to duplicate list.
   If TYPE is more specified than VAL->type, prevail VAL->type.  Also if
   this is first time we see definition of a class return true so the
   base types are analyzed.  */

static bool
add_type_duplicate (odr_type val, tree type)
{
  bool build_bases = false;
  bool prevail = false;
  bool odr_must_violate = false;

  if (!val->types_set)
    val->types_set = new hash_set<tree>;

  /* Chose polymorphic type as leader (this happens only in case of ODR
     violations.  */
  if ((TREE_CODE (type) == RECORD_TYPE && TYPE_BINFO (type)
       && polymorphic_type_binfo_p (TYPE_BINFO (type)))
      && (TREE_CODE (val->type) != RECORD_TYPE || !TYPE_BINFO (val->type)
          || !polymorphic_type_binfo_p (TYPE_BINFO (val->type))))
    {
      prevail = true;
      build_bases = true;
    }
  /* Always prefer complete type to be the leader.  */
  else if (!COMPLETE_TYPE_P (val->type) && COMPLETE_TYPE_P (type))
    {
      prevail = true;
      if (TREE_CODE (type) == RECORD_TYPE)
        build_bases = TYPE_BINFO (type);
    }
  else if (COMPLETE_TYPE_P (val->type) && !COMPLETE_TYPE_P (type))
    ;
  else if (TREE_CODE (val->type) == RECORD_TYPE
	   && TREE_CODE (type) == RECORD_TYPE
	   && TYPE_BINFO (type) && !TYPE_BINFO (val->type))
    {
      gcc_assert (!val->bases.length ());
      build_bases = true;
      prevail = true;
    }

  if (prevail)
    std::swap (val->type, type);

  val->types_set->add (type);

  if (!odr_hash)
    return false;

  gcc_checking_assert (can_be_name_hashed_p (type)
		       && can_be_name_hashed_p (val->type));

  bool merge = true;
  bool base_mismatch = false;
  unsigned int i;
  bool warned = false;
  hash_set<type_pair> visited;

  gcc_assert (in_lto_p);
  vec_safe_push (val->types, type);

  /* If both are class types, compare the bases.  */
  if (COMPLETE_TYPE_P (type) && COMPLETE_TYPE_P (val->type)
      && TREE_CODE (val->type) == RECORD_TYPE
      && TREE_CODE (type) == RECORD_TYPE
      && TYPE_BINFO (val->type) && TYPE_BINFO (type))
    {
      if (BINFO_N_BASE_BINFOS (TYPE_BINFO (type))
	  != BINFO_N_BASE_BINFOS (TYPE_BINFO (val->type)))
	{
	  if (!flag_ltrans && !warned && !val->odr_violated)
	    {
	      tree extra_base;
	      warn_odr (type, val->type, NULL, NULL, !warned, &warned,
			"a type with the same name but different "
			"number of polymorphic bases is "
			"defined in another translation unit");
	      if (warned)
		{
		  if (BINFO_N_BASE_BINFOS (TYPE_BINFO (type))
		      > BINFO_N_BASE_BINFOS (TYPE_BINFO (val->type)))
		    extra_base = BINFO_BASE_BINFO
				 (TYPE_BINFO (type),
				  BINFO_N_BASE_BINFOS (TYPE_BINFO (val->type)));
		  else
		    extra_base = BINFO_BASE_BINFO
				 (TYPE_BINFO (val->type),
				  BINFO_N_BASE_BINFOS (TYPE_BINFO (type)));
		  tree extra_base_type = BINFO_TYPE (extra_base);
		  inform (DECL_SOURCE_LOCATION (TYPE_NAME (extra_base_type)),
			  "the extra base is defined here");
		}
	    }
	  base_mismatch = true;
	}
      else
	for (i = 0; i < BINFO_N_BASE_BINFOS (TYPE_BINFO (type)); i++)
	  {
	    tree base1 = BINFO_BASE_BINFO (TYPE_BINFO (type), i);
	    tree base2 = BINFO_BASE_BINFO (TYPE_BINFO (val->type), i);
	    tree type1 = BINFO_TYPE (base1);
	    tree type2 = BINFO_TYPE (base2);

	    if (types_odr_comparable (type1, type2))
	      {
		if (!types_same_for_odr (type1, type2))
		  base_mismatch = true;
	      }
	    else
	      if (!odr_types_equivalent_p (type1, type2))
		base_mismatch = true;
	    if (base_mismatch)
	      {
		if (!warned && !val->odr_violated)
		  {
		    warn_odr (type, val->type, NULL, NULL,
			      !warned, &warned,
			      "a type with the same name but different base "
			      "type is defined in another translation unit");
		    if (warned)
		      warn_types_mismatch (type1, type2,
					    UNKNOWN_LOCATION, UNKNOWN_LOCATION);
		  }
		break;
	      }
	    if (BINFO_OFFSET (base1) != BINFO_OFFSET (base2))
	      {
		base_mismatch = true;
		if (!warned && !val->odr_violated)
		  warn_odr (type, val->type, NULL, NULL,
			    !warned, &warned,
			    "a type with the same name but different base "
			    "layout is defined in another translation unit");
		break;
	      }
	    /* One of bases is not of complete type.  */
	    if (!TYPE_BINFO (type1) != !TYPE_BINFO (type2))
	      {
		/* If we have a polymorphic type info specified for TYPE1
		   but not for TYPE2 we possibly missed a base when recording
		   VAL->type earlier.
		   Be sure this does not happen.  */
		if (TYPE_BINFO (type1)
		    && polymorphic_type_binfo_p (TYPE_BINFO (type1))
		    && !build_bases)
		  odr_must_violate = true;
	        break;
	      }
	    /* One base is polymorphic and the other not.
	       This ought to be diagnosed earlier, but do not ICE in the
	       checking bellow.  */
	    else if (TYPE_BINFO (type1)
		     && polymorphic_type_binfo_p (TYPE_BINFO (type1))
		        != polymorphic_type_binfo_p (TYPE_BINFO (type2)))
	      {
		if (!warned && !val->odr_violated)
		  warn_odr (type, val->type, NULL, NULL,
			    !warned, &warned,
			    "a base of the type is polymorphic only in one "
			    "translation unit");
		base_mismatch = true;
		break;
	      }
	  }
      if (base_mismatch)
	{
	  merge = false;
	  odr_violation_reported = true;
	  val->odr_violated = true;

	  if (symtab->dump_file)
	    {
	      fprintf (symtab->dump_file, "ODR base violation\n");
	    
	      print_node (symtab->dump_file, "", val->type, 0);
	      putc ('\n',symtab->dump_file);
	      print_node (symtab->dump_file, "", type, 0);
	      putc ('\n',symtab->dump_file);
	    }
	}
    }

  /* Next compare memory layout.
     The DECL_SOURCE_LOCATIONs in this invocation came from LTO streaming.
     We must apply the location cache to ensure that they are valid
     before we can pass them to odr_types_equivalent_p (PR lto/83121).  */
  if (lto_location_cache::current_cache)
    lto_location_cache::current_cache->apply_location_cache ();
  /* As a special case we stream mangles names of integer types so we can see
     if they are believed to be same even though they have different
     representation.  Avoid bogus warning on mismatches in these.  */
  if (TREE_CODE (type) != INTEGER_TYPE
      && TREE_CODE (val->type) != INTEGER_TYPE
      && !odr_types_equivalent_p (val->type, type,
			       !flag_ltrans && !val->odr_violated && !warned,
			       &warned, &visited,
			       DECL_SOURCE_LOCATION (TYPE_NAME (val->type)),
			       DECL_SOURCE_LOCATION (TYPE_NAME (type))))
    {
      merge = false;
      odr_violation_reported = true;
      val->odr_violated = true;
    }
  gcc_assert (val->odr_violated || !odr_must_violate);
  /* Sanity check that all bases will be build same way again.  */
  if (flag_checking
      && COMPLETE_TYPE_P (type) && COMPLETE_TYPE_P (val->type)
      && TREE_CODE (val->type) == RECORD_TYPE
      && TREE_CODE (type) == RECORD_TYPE
      && TYPE_BINFO (val->type) && TYPE_BINFO (type)
      && !val->odr_violated
      && !base_mismatch && val->bases.length ())
    {
      unsigned int num_poly_bases = 0;
      unsigned int j;

      for (i = 0; i < BINFO_N_BASE_BINFOS (TYPE_BINFO (type)); i++)
	if (polymorphic_type_binfo_p (BINFO_BASE_BINFO
					 (TYPE_BINFO (type), i)))
	  num_poly_bases++;
      gcc_assert (num_poly_bases == val->bases.length ());
      for (j = 0, i = 0; i < BINFO_N_BASE_BINFOS (TYPE_BINFO (type));
	   i++)
	if (polymorphic_type_binfo_p (BINFO_BASE_BINFO
				       (TYPE_BINFO (type), i)))
	  {
	    odr_type base = get_odr_type
			       (BINFO_TYPE
				  (BINFO_BASE_BINFO (TYPE_BINFO (type),
						     i)),
				true);
	    gcc_assert (val->bases[j] == base);
	    j++;
	  }
    }


  /* Regularize things a little.  During LTO same types may come with
     different BINFOs.  Either because their virtual table was
     not merged by tree merging and only later at decl merging or
     because one type comes with external vtable, while other
     with internal.  We want to merge equivalent binfos to conserve
     memory and streaming overhead.

     The external vtables are more harmful: they contain references
     to external declarations of methods that may be defined in the
     merged LTO unit.  For this reason we absolutely need to remove
     them and replace by internal variants. Not doing so will lead
     to incomplete answers from possible_polymorphic_call_targets.

     FIXME: disable for now; because ODR types are now build during
     streaming in, the variants do not need to be linked to the type,
     yet.  We need to do the merging in cleanup pass to be implemented
     soon.  */
  if (!flag_ltrans && merge
      && 0
      && TREE_CODE (val->type) == RECORD_TYPE
      && TREE_CODE (type) == RECORD_TYPE
      && TYPE_BINFO (val->type) && TYPE_BINFO (type)
      && TYPE_MAIN_VARIANT (type) == type
      && TYPE_MAIN_VARIANT (val->type) == val->type
      && BINFO_VTABLE (TYPE_BINFO (val->type))
      && BINFO_VTABLE (TYPE_BINFO (type)))
    {
      tree master_binfo = TYPE_BINFO (val->type);
      tree v1 = BINFO_VTABLE (master_binfo);
      tree v2 = BINFO_VTABLE (TYPE_BINFO (type));

      if (TREE_CODE (v1) == POINTER_PLUS_EXPR)
	{
	  gcc_assert (TREE_CODE (v2) == POINTER_PLUS_EXPR
		      && operand_equal_p (TREE_OPERAND (v1, 1),
					  TREE_OPERAND (v2, 1), 0));
	  v1 = TREE_OPERAND (TREE_OPERAND (v1, 0), 0);
	  v2 = TREE_OPERAND (TREE_OPERAND (v2, 0), 0);
	}
      gcc_assert (DECL_ASSEMBLER_NAME (v1)
		  == DECL_ASSEMBLER_NAME (v2));

      if (DECL_EXTERNAL (v1) && !DECL_EXTERNAL (v2))
	{
	  unsigned int i;

	  set_type_binfo (val->type, TYPE_BINFO (type));
	  for (i = 0; i < val->types->length (); i++)
	    {
	      if (TYPE_BINFO ((*val->types)[i])
		  == master_binfo)
		set_type_binfo ((*val->types)[i], TYPE_BINFO (type));
	    }
	  BINFO_TYPE (TYPE_BINFO (type)) = val->type;
	}
      else
	set_type_binfo (type, master_binfo);
    }
  return build_bases;
}

/* REF is OBJ_TYPE_REF, return the class the ref corresponds to.
   FOR_DUMP_P is true when being called from the dump routines.  */

tree
obj_type_ref_class (const_tree ref, bool for_dump_p)
{
  gcc_checking_assert (TREE_CODE (ref) == OBJ_TYPE_REF);
  ref = TREE_TYPE (ref);
  gcc_checking_assert (TREE_CODE (ref) == POINTER_TYPE);
  ref = TREE_TYPE (ref);
  /* We look for type THIS points to.  ObjC also builds
     OBJ_TYPE_REF with non-method calls, Their first parameter
     ID however also corresponds to class type. */
  gcc_checking_assert (TREE_CODE (ref) == METHOD_TYPE
		       || TREE_CODE (ref) == FUNCTION_TYPE);
  ref = TREE_VALUE (TYPE_ARG_TYPES (ref));
  gcc_checking_assert (TREE_CODE (ref) == POINTER_TYPE);
  tree ret = TREE_TYPE (ref);
  if (!in_lto_p && !TYPE_STRUCTURAL_EQUALITY_P (ret))
    ret = TYPE_CANONICAL (ret);
  else if (odr_type ot = get_odr_type (ret, !for_dump_p))
    ret = ot->type;
  else
    gcc_assert (for_dump_p);
  return ret;
}

/* Return true if TYPE contains any virtual base.  */

static bool
type_has_virtual_base_p (tree type)
{
  tree binfo = TYPE_BINFO (type);

  if (!binfo)
    return false;

  if (auto ot = get_odr_type (type))
    return ot->has_virtual_base;

  for (auto base_binfo : *BINFO_BASE_BINFOS (binfo))
    {
      if (BINFO_VIRTUAL_P (base_binfo)
	  || type_has_virtual_base_p (BINFO_TYPE (base_binfo)))
	return true;
    }

  return false;
}

/* Get ODR type hash entry for TYPE.  If INSERT is true, create
   possibly new entry.  */

odr_type
get_odr_type (tree type, bool insert)
{
  odr_type_d **slot = NULL;
  odr_type val = NULL;
  hashval_t hash;
  bool build_bases = false;
  bool insert_to_odr_array = false;
  int base_id = -1;

  type = TYPE_MAIN_VARIANT (type);
  if (!in_lto_p && !TYPE_STRUCTURAL_EQUALITY_P (type))
    type = TYPE_CANONICAL (type);

  gcc_checking_assert (can_be_name_hashed_p (type));

  hash = hash_odr_name (type);
  slot = odr_hash->find_slot_with_hash (type, hash,
					insert ? INSERT : NO_INSERT);

  if (!slot)
    return NULL;

  /* See if we already have entry for type.  */
  if (*slot)
    {
      val = *slot;

      if (val->type != type && insert
	  && (!val->types_set || !val->types_set->add (type)))
	build_bases = add_type_duplicate (val, type);
    }
  else
    {
      val = ggc_cleared_alloc<odr_type_d> ();
      val->type = type;
      val->bases = vNULL;
      val->derived_types = vNULL;
      if (type_with_linkage_p (type))
	val->anonymous_namespace = type_in_anonymous_namespace_p (type);
      else
	val->anonymous_namespace = 0;

      build_bases = COMPLETE_TYPE_P (val->type);
      insert_to_odr_array = true;
      *slot = val;
    }

  if (build_bases && TREE_CODE (type) == RECORD_TYPE && TYPE_BINFO (type)
      && type_with_linkage_p (type)
      && type == TYPE_MAIN_VARIANT (type))
    {
      tree binfo = TYPE_BINFO (type);
      unsigned int i;

      gcc_assert (BINFO_TYPE (TYPE_BINFO (val->type)) == type);

      for (i = 0; i < BINFO_N_BASE_BINFOS (binfo); i++)
	/* For now record only polymorphic types. other are
	   pointless for devirtualization and we cannot precisely
	   determine ODR equivalency of these during LTO.  */
	if (polymorphic_type_binfo_p (BINFO_BASE_BINFO (binfo, i)))
	  {
	    tree base_type = BINFO_TYPE (BINFO_BASE_BINFO (binfo, i));
	    odr_type base = get_odr_type (base_type, true);
	    gcc_assert (TYPE_MAIN_VARIANT (base_type) == base_type);

	    /* Propagate has_virtual_base flag to all derived classes.  */
	    if (base->has_virtual_base
		|| BINFO_VIRTUAL_P (BINFO_BASE_BINFO (binfo, i)))
	      val->set_has_virtual_base ();

	    base->derived_types.safe_push (val);
	    val->bases.safe_push (base);
	    if (base->id > base_id)
	      base_id = base->id;
	  }
	else
	  {
	    tree base_type = BINFO_TYPE (BINFO_BASE_BINFO (binfo, i));

	    /* Propagate has_virtual_base flag to all derived classes.  */
	    if (BINFO_VIRTUAL_P (BINFO_BASE_BINFO (binfo, i))
		|| type_has_virtual_base_p (base_type))
	      val->set_has_virtual_base ();
	  }
      }
  /* Ensure that type always appears after bases.  */
  if (insert_to_odr_array)
    {
      if (odr_types_ptr)
        val->id = odr_types.length ();
      vec_safe_push (odr_types_ptr, val);
    }
  else if (base_id > val->id)
    {
      odr_types[val->id] = 0;
      /* Be sure we did not recorded any derived types; these may need
	 renumbering too.  */
      gcc_assert (val->derived_types.length() == 0);
      val->id = odr_types.length ();
      vec_safe_push (odr_types_ptr, val);
    }
  return val;
}

/* Return type that in ODR type hash prevailed TYPE.  Be careful and punt
   on ODR violations.  */

tree
prevailing_odr_type (tree type)
{
  odr_type t = get_odr_type (type, false);
  if (!t || t->odr_violated)
    return type;
  return t->type;
}

/* Set tbaa_enabled flag for TYPE.  */

void
enable_odr_based_tbaa (tree type)
{
  odr_type t = get_odr_type (type, true);
  t->tbaa_enabled = true;
}

/* True if canonical type of TYPE is determined using ODR name.  */

bool
odr_based_tbaa_p (const_tree type)
{
  if (!RECORD_OR_UNION_TYPE_P (type))
    return false;
  if (!odr_hash)
    return false;
  odr_type t = get_odr_type (const_cast <tree> (type), false);
  if (!t || !t->tbaa_enabled)
    return false;
  return true;
}

/* Set TYPE_CANONICAL of type and all its variants and duplicates
   to CANONICAL.  */

void
set_type_canonical_for_odr_type (tree type, tree canonical)
{
  odr_type t = get_odr_type (type, false);
  unsigned int i;
  tree tt;

  for (tree t2 = t->type; t2; t2 = TYPE_NEXT_VARIANT (t2))
    TYPE_CANONICAL (t2) = canonical;
  if (t->types)
    FOR_EACH_VEC_ELT (*t->types, i, tt)
      for (tree t2 = tt; t2; t2 = TYPE_NEXT_VARIANT (t2))
        TYPE_CANONICAL (t2) = canonical;
}

/* Return true if we reported some ODR violation on TYPE.  */

bool
odr_type_violation_reported_p (tree type)
{
  return get_odr_type (type, false)->odr_violated;
}

/* Add TYPE of ODR type hash.  */

void
register_odr_type (tree type)
{
  if (!odr_hash)
    odr_hash = new odr_hash_type (23);
  if (type == TYPE_MAIN_VARIANT (type))
    {
      /* To get ODR warnings right, first register all sub-types.  */
      if (RECORD_OR_UNION_TYPE_P (type)
	  && COMPLETE_TYPE_P (type))
	{
	  /* Limit recursion on types which are already registered.  */
	  odr_type ot = get_odr_type (type, false);
	  if (ot
	      && (ot->type == type
		  || (ot->types_set
		      && ot->types_set->contains (type))))
	    return;
	  for (tree f = TYPE_FIELDS (type); f; f = TREE_CHAIN (f))
	    if (TREE_CODE (f) == FIELD_DECL)
	      {
		tree subtype = TREE_TYPE (f);

		while (TREE_CODE (subtype) == ARRAY_TYPE)
		  subtype = TREE_TYPE (subtype);
		if (type_with_linkage_p (TYPE_MAIN_VARIANT (subtype)))
		  register_odr_type (TYPE_MAIN_VARIANT (subtype));
	      }
	   if (TYPE_BINFO (type))
	     for (unsigned int i = 0;
	          i < BINFO_N_BASE_BINFOS (TYPE_BINFO (type)); i++)
	       register_odr_type (BINFO_TYPE (BINFO_BASE_BINFO
						 (TYPE_BINFO (type), i)));
	}
      get_odr_type (type, true);
    }
}

/* Return TRUE if all derived types of T are known and thus
   we may consider the walk of derived type complete.  */

bool
type_all_derivations_known_p (tree t)
{
  /* Non-C++ types may have IDENTIFIER_NODE here, do not crash.  */
  if (!TYPE_NAME (t) || TREE_CODE (TYPE_NAME (t)) != TYPE_DECL)
    return true;

  if (!odr_hash || !can_be_name_hashed_p (t))
    return false;

  odr_type type = get_odr_type (t, true);

  return type->all_derivations_known_p ();
}

/* Return true if type is known to have no derivations.  */

bool
type_known_to_have_no_derivations_p (tree t)
{
  if (!odr_hash || !can_be_name_hashed_p (t))
    return false;

  odr_type type = get_odr_type (t, true);

  return type->all_derivations_known_p () && !type->derived_types.length();
}

/* Dump ODR type T and all its derived types.  INDENT specifies indentation for
   recursive printing.  */

static void
dump_odr_type (FILE *f, odr_type t, int indent=0)
{
  unsigned int i;
  fprintf (f, "%*s type %i: ", indent * 2, "", t->id);
  print_generic_expr (f, t->type, TDF_SLIM);
  if (t->anonymous_namespace)
    fprintf (f, " (anonymous namespace)");
  if (t->has_virtual_base)
    fprintf (f, " (virtual base)");
  if (t->whole_program_local_p ())
    fprintf (f, " (whole program local)");
  else if (t->all_derivations_known_p ())
    fprintf (f, " (derivations known)");
  fprintf (f, "\n");
  if (TYPE_NAME (t->type))
    {
      if (DECL_ASSEMBLER_NAME_SET_P (TYPE_NAME (t->type)))
        fprintf (f, "%*s mangled name: %s\n", indent * 2, "",
		 IDENTIFIER_POINTER
		   (DECL_ASSEMBLER_NAME (TYPE_NAME (t->type))));
    }
  if (t->bases.length ())
    {
      fprintf (f, "%*s base odr type ids: ", indent * 2, "");
      for (i = 0; i < t->bases.length (); i++)
	fprintf (f, " %i", t->bases[i]->id);
      fprintf (f, "\n");
    }
  if (t->derived_types.length ())
    {
      fprintf (f, "%*s derived types:\n", indent * 2, "");
      for (i = 0; i < t->derived_types.length (); i++)
        dump_odr_type (f, t->derived_types[i], indent + 1);
    }
  fprintf (f, "\n");
}

/* Dump the type inheritance graph.  */

static void
dump_type_inheritance_graph (FILE *f)
{
  unsigned int i;
  unsigned int num_all_types = 0, num_types = 0, num_duplicates = 0;
  if (!odr_types_ptr)
    return;
  fprintf (f, "\n\nType inheritance graph:\n");
  for (i = 0; i < odr_types.length (); i++)
    {
      if (odr_types[i] && odr_types[i]->bases.length () == 0)
	dump_odr_type (f, odr_types[i]);
    }
  for (i = 0; i < odr_types.length (); i++)
    {
      if (!odr_types[i])
	continue;

      num_all_types++;
      if (!odr_types[i]->types || !odr_types[i]->types->length ())
	continue;

      /* To aid ODR warnings we also mangle integer constants but do
	 not consider duplicates there.  */
      if (TREE_CODE (odr_types[i]->type) == INTEGER_TYPE)
	continue;

      /* It is normal to have one duplicate and one normal variant.  */
      if (odr_types[i]->types->length () == 1
	  && COMPLETE_TYPE_P (odr_types[i]->type)
	  && !COMPLETE_TYPE_P ((*odr_types[i]->types)[0]))
	continue;

      num_types ++;

      unsigned int j;
      fprintf (f, "Duplicate tree types for odr type %i\n", i);
      print_node (f, "", odr_types[i]->type, 0);
      print_node (f, "", TYPE_NAME (odr_types[i]->type), 0);
      putc ('\n',f);
      for (j = 0; j < odr_types[i]->types->length (); j++)
	{
	  tree t;
	  num_duplicates ++;
	  fprintf (f, "duplicate #%i\n", j);
	  print_node (f, "", (*odr_types[i]->types)[j], 0);
	  t = (*odr_types[i]->types)[j];
	  while (TYPE_P (t) && TYPE_CONTEXT (t))
	    {
	      t = TYPE_CONTEXT (t);
	      print_node (f, "", t, 0);
	    }
	  print_node (f, "", TYPE_NAME ((*odr_types[i]->types)[j]), 0);
	  putc ('\n',f);
	}
    }
  fprintf (f, "Out of %i types there are %i types with duplicates; "
	   "%i duplicates overall\n", num_all_types, num_types, num_duplicates);
}

/* Save some WPA->ltrans streaming by freeing stuff needed only for good
   ODR warnings.
   We make TYPE_DECLs to not point back
   to the type (which is needed to keep them in the same SCC and preserve
   location information to output warnings) and subsequently we make all
   TYPE_DECLS of same assembler name equivalent.  */

static void
free_odr_warning_data ()
{
  static bool odr_data_freed = false;

  if (odr_data_freed || !flag_wpa || !odr_types_ptr)
    return;

  odr_data_freed = true;

  for (unsigned int i = 0; i < odr_types.length (); i++)
    if (odr_types[i])
      {
	tree t = odr_types[i]->type;

	TREE_TYPE (TYPE_NAME (t)) = void_type_node;

	if (odr_types[i]->types)
          for (unsigned int j = 0; j < odr_types[i]->types->length (); j++)
	    {
	      tree td = (*odr_types[i]->types)[j];

	      TYPE_NAME (td) = TYPE_NAME (t);
	    }
      }
  odr_data_freed = true;
}

/* Initialize IPA devirt and build inheritance tree graph.  */

void
build_type_inheritance_graph (void)
{
  struct symtab_node *n;
  FILE *inheritance_dump_file;
  dump_flags_t flags;

  if (odr_hash)
    {
      free_odr_warning_data ();
      return;
    }
  timevar_push (TV_IPA_INHERITANCE);
  inheritance_dump_file = dump_begin (TDI_inheritance, &flags);
  odr_hash = new odr_hash_type (23);

  /* We reconstruct the graph starting of types of all methods seen in the
     unit.  */
  FOR_EACH_SYMBOL (n)
    if (is_a <cgraph_node *> (n)
	&& DECL_VIRTUAL_P (n->decl)
	&& n->real_symbol_p ())
      get_odr_type (TYPE_METHOD_BASETYPE (TREE_TYPE (n->decl)), true);

    /* Look also for virtual tables of types that do not define any methods.

       We need it in a case where class B has virtual base of class A
       re-defining its virtual method and there is class C with no virtual
       methods with B as virtual base.

       Here we output B's virtual method in two variant - for non-virtual
       and virtual inheritance.  B's virtual table has non-virtual version,
       while C's has virtual.

       For this reason we need to know about C in order to include both
       variants of B.  More correctly, record_target_from_binfo should
       add both variants of the method when walking B, but we have no
       link in between them.

       We rely on fact that either the method is exported and thus we
       assume it is called externally or C is in anonymous namespace and
       thus we will see the vtable.  */

    else if (is_a <varpool_node *> (n)
	     && DECL_VIRTUAL_P (n->decl)
	     && TREE_CODE (DECL_CONTEXT (n->decl)) == RECORD_TYPE
	     && TYPE_BINFO (DECL_CONTEXT (n->decl))
	     && polymorphic_type_binfo_p (TYPE_BINFO (DECL_CONTEXT (n->decl))))
      get_odr_type (TYPE_MAIN_VARIANT (DECL_CONTEXT (n->decl)), true);
  if (inheritance_dump_file)
    {
      dump_type_inheritance_graph (inheritance_dump_file);
      dump_end (TDI_inheritance, inheritance_dump_file);
    }
  free_odr_warning_data ();
  timevar_pop (TV_IPA_INHERITANCE);
}

/* Return typeinfo referenced by VTABLE.  If REMOVE is TRUE, replace all
   typeinfo addresses in VTABLE with zero values.  */

static tree
extract_typeinfo_in_vtable (tree vtable, bool remove = false)
{
  tree init = ctor_for_folding (vtable);
  tree typeinfo = NULL;

  if (init == error_mark_node)
    return NULL;

  for (unsigned i = 0; i < CONSTRUCTOR_NELTS (init); i++)
    {
      constructor_elt *elt = CONSTRUCTOR_ELT (init, i);
      tree value = elt->value;

      STRIP_NOPS (value);

      if (TREE_CODE (value) != ADDR_EXPR)
	continue;

      value = TREE_OPERAND (value, 0);
      if (TREE_CODE (value) == FUNCTION_DECL)
	continue;

      gcc_assert (VAR_P (value) && !DECL_VIRTUAL_P (value));

      if (!remove)
	return value;

      if (typeinfo)
	gcc_assert (typeinfo == value);
      else
	typeinfo = value;

      elt->value = build_zero_cst (TREE_TYPE (elt->value));
    }

  return typeinfo;
}

/* Return typeinfo referenced by vtable represented by VNODE.  If REMOVE
   is TRUE, replace all typeinfo addresses in vtable with zero values.  */

static symtab_node *
extract_typeinfo_in_vtable_node (varpool_node *vnode, bool remove)
{
  symtab_node *typeinfo = NULL;
  ipa_ref *ref;

  for (unsigned i = 0; vnode->iterate_reference (i, ref); i++)
    {
      symtab_node *referred = ref->referred;

      if (ref->use == IPA_REF_ADDR && is_a <varpool_node *> (referred))
	{
	  /* This is a VTT (vtable table), not vtable.  */
	  if (DECL_VIRTUAL_P (referred->decl))
	    {
	      gcc_assert (!typeinfo);
	      return NULL;
	    }

	  if (!remove)
	    return referred;

	  if (typeinfo)
	    gcc_assert (typeinfo == referred);
	  else
	    typeinfo = referred;

	  ref->remove_reference ();
	  i--;
	}
    }

  tree decl = extract_typeinfo_in_vtable (vnode->decl, remove);

  if (typeinfo)
    gcc_assert (typeinfo->decl == decl);
  else if (decl)
    typeinfo = varpool_node::get (decl);

  return typeinfo;
}

/* Find out C++ polymorphic classes that are used locally in terms of lto
   whole program scope.  If full devirtualization is off, we only consider
   local class in function or anonymous namespace.  Otherwise, we will resort
   to lto-linker-plugin symbol resolution to check whether vtable and typeinfo
   symbols of a given class are referenced by any external regular object or
   library.  At same time, since typeinfo is used to carry symbol resolution
   information, it is always generated even user specifies -fno-rtti at LGEN
   compilation, and removal of typeinfo is postponed to this procedure.  */

void
identify_whole_program_local_types (void)
{
  hash_set<lto_file_decl_data *> *no_rtti_files = NULL;
  varpool_node *vnode;

  gcc_assert (in_lto_p && !flag_ltrans);

  if (!odr_hash)
    return;

  if (flag_devirtualize_fully)
    {
      lto_file_decl_data *prev_file_data = NULL;
      cgraph_node *cnode;

      /* Effect of -fno-rtti is file-wide, collect those files that -fno-rtti
	 has been specified for.  */
      FOR_EACH_FUNCTION (cnode)
	{
	  lto_file_decl_data *file_data = cnode->lto_file_data;

	  if (DECL_FUNCTION_SPECIFIC_OPTIMIZATION (cnode->decl)
	      && !opt_for_fn (cnode->decl, flag_rtti)
	      && prev_file_data != file_data && file_data)
	    {
	      if (!no_rtti_files)
		no_rtti_files = new hash_set<lto_file_decl_data *> ();
	      no_rtti_files->add (file_data);

	      /* Symbols coming from same lto file are likely to be grouped
		 together. Based on this fact, here is a minor optimization
		 that we do not add lto file if it is the one just added.  */
	      prev_file_data = file_data;
	    }
	}
    }

  FOR_EACH_DEFINED_VARIABLE (vnode)
    {
      tree decl = vnode->decl;
      symtab_node *typeinfo = NULL;

      if (!DECL_VIRTUAL_P (decl) || DECL_EXTERNAL (decl))
	continue;

      if (flag_devirtualize_fully)
	{
	  bool remove_rtti = no_rtti_files
			     && no_rtti_files->contains (vnode->lto_file_data);

	  /* Remove typeinfo if its referring vtable is originated from a file
	     that is impacted by -fno-rtti.  */
	  typeinfo = extract_typeinfo_in_vtable_node (vnode, remove_rtti);
	}

      tree class_type = DECL_CONTEXT (decl);
      odr_type type = get_odr_type (class_type);

      if (!type->anonymous_namespace
	  && !decl_function_context (TYPE_NAME (class_type)))
	{
	  /* This is a VTT (vtable table), or user specified -fno-rtti, but
	     forgot -fdevirtualize-fully at LGEN compilation.  */
	  if (!typeinfo)
	    continue;

	  /* If vtable of public class has no linkage (occurs with -fno-weak),
	     lto-linker-plugin could not enforce symbol resolution and tell us
	     nothing, just conservatively skip the class.  */
	  if (!TREE_PUBLIC (decl))
	    continue;

	  /* Symbol with resolution as LDPR_PREVAILING_DEF_IRONLY_EXP allows
	     external reference from dynamic library, which can not be known
	     at link time.  */
	  if (vnode->resolution != LDPR_PREVAILING_DEF_IRONLY
	      || typeinfo->resolution != LDPR_PREVAILING_DEF_IRONLY)
	    continue;
	}

      /* Skip class type that violates odr constraint, since types in conflict
	 may have incompatible vtable definition.  */
      if (type->odr_violated)
	{
	  gcc_assert (!type->anonymous_namespace);
	  continue;
	}

      tree vtable = get_type_vtable (class_type);

      gcc_assert (vtable);

      if (vtable != vnode->decl)
	{
	  /* This is not primary vtable of a class type, just a construction
	     vtable for one of its virtual base.  */
	  gcc_assert (type->has_virtual_base);
	  continue;
	}

      bool is_final = type->derived_types.is_empty ();

      if (type->types)
	{
	  tree equiv_type;
	  bool multi_vtable_p = false;
	  unsigned i;

	  /* Some kind of class type (public class w/o key member function,
	     and local class in a public inline function) requires COMDAT-like
	     vtable so as to be shared among units.  But C++ privatizing via
	     -fno-weak would introduce multiple static vtable copies for one
	     class in merged lto symbol table.  This breaks one-to-one
	     correspondence between class and vtable, and makes class liveness
	     check become not that easy.  To be simple, we exclude such class
	     type from our choice list.

	     TODO: lto_symtab_merge_symbols() currently only merges public and
	     external symbols, it could be extended to combine identical
	     static symbols similar to COMDAT.  */
	  if (class_type != type->type
	      && (vtable != get_type_vtable (type->type)))
	    continue;

	  FOR_EACH_VEC_ELT (*(type->types), i, equiv_type)
	    {
	      if (COMPLETE_TYPE_P (equiv_type)
		  && (vtable != get_type_vtable (equiv_type)))
		{
		  multi_vtable_p = true;
		  break;
		}
	    }

	  if (multi_vtable_p)
	    continue;

	  /* Mark all equivalent types in the ODR type as whole program local,
	     because representative type of the ODR type at LTRANS might not
	     be the one at WPA.  */
	  FOR_EACH_VEC_ELT (*(type->types), i, equiv_type)
	    {
	      TYPE_CXX_LOCAL (equiv_type) = 1;

	      /* If no derivation, whole program local type is marked as
		 FINAL, which could help devirtualization at LTRANS even
		 there will be more than one partitions.  */
	      if (is_final)
		TYPE_FINAL_P (equiv_type) = 1;
	    }
	}

      TYPE_CXX_LOCAL (type->type) = 1;
      if (is_final)
	TYPE_FINAL_P (type->type) = 1;
    }

  delete no_rtti_files;
}

/* Return true if N has reference from live virtual table
   (and thus can be a destination of polymorphic call). 
   Be conservatively correct when callgraph is not built or
   if the method may be referred externally.  */

static bool
referenced_from_vtable_p (struct cgraph_node *node)
{
  int i;
  struct ipa_ref *ref;
  bool found = false;

  if (node->externally_visible
      || DECL_EXTERNAL (node->decl)
      || node->used_from_other_partition)
    return true;

  /* Keep this test constant time.
     It is unlikely this can happen except for the case where speculative
     devirtualization introduced many speculative edges to this node. 
     In this case the target is very likely alive anyway.  */
  if (node->ref_list.referring.length () > 100)
    return true;

  /* We need references built.  */
  if (symtab->state <= CONSTRUCTION)
    return true;

  for (i = 0; node->iterate_referring (i, ref); i++)
    if ((ref->use == IPA_REF_ALIAS
	 && referenced_from_vtable_p (dyn_cast<cgraph_node *> (ref->referring)))
	|| (ref->use == IPA_REF_ADDR
	    && VAR_P (ref->referring->decl)
	    && DECL_VIRTUAL_P (ref->referring->decl)))
      {
	found = true;
	break;
      }
  return found;
}

/* Return if TARGET is cxa_pure_virtual.  */

static bool
is_cxa_pure_virtual_p (tree target)
{
  return target && TREE_CODE (TREE_TYPE (target)) != METHOD_TYPE
	 && DECL_NAME (target)
	 && id_equal (DECL_NAME (target),
		     "__cxa_pure_virtual");
}

/* If TARGET has associated node, record it in the NODES array.
   CAN_REFER specify if program can refer to the target directly.
   if TARGET is unknown (NULL) or it cannot be inserted (for example because
   its body was already removed and there is no way to refer to it), clear
   COMPLETEP.  */

static void
maybe_record_node (vec <cgraph_node *> &nodes,
		   tree target, hash_set<tree> *inserted,
		   bool can_refer,
		   bool *completep)
{
  struct cgraph_node *target_node, *alias_target;
  enum availability avail;
  bool pure_virtual = is_cxa_pure_virtual_p (target);

  /* __builtin_unreachable do not need to be added into
     list of targets; the runtime effect of calling them is undefined.
     Only "real" virtual methods should be accounted.  */
  if (target && TREE_CODE (TREE_TYPE (target)) != METHOD_TYPE && !pure_virtual)
    return;

  if (!can_refer)
    {
      /* The only case when method of whole-program local class type becomes
	 unreferable is when we completely optimized it out.  */
      if (!target || !type_whole_program_local_p (DECL_CONTEXT (target)))
	*completep = false;
      return;
    }

  if (!target)
    return;

  target_node = cgraph_node::get (target);

  /* Prefer alias target over aliases, so we do not get confused by
     fake duplicates.  */
  if (target_node)
    {
      alias_target = target_node->ultimate_alias_target (&avail);
      if (target_node != alias_target
	  && avail >= AVAIL_AVAILABLE
	  && target_node->get_availability ())
	target_node = alias_target;
    }

  /* Method can only be called by polymorphic call if any
     of vtables referring to it are alive. 

     While this holds for non-anonymous functions, too, there are
     cases where we want to keep them in the list; for example
     inline functions with -fno-weak are static, but we still
     may devirtualize them when instance comes from other unit.
     The same holds for LTO.

     Currently we ignore these functions in speculative devirtualization.
     ??? Maybe it would make sense to be more aggressive for LTO even
     elsewhere.  */
  if ((!flag_ltrans || flag_devirtualize_fully)
      && !pure_virtual
      && type_in_anonymous_namespace_p (DECL_CONTEXT (target))
      && (!target_node
          || !referenced_from_vtable_p (target_node)))
    ;
  /* See if TARGET is useful function we can deal with.  */
  else if (target_node != NULL
	   && (TREE_PUBLIC (target)
	       || DECL_EXTERNAL (target)
	       || target_node->definition)
	   && target_node->real_symbol_p ())
    {
      gcc_assert (!target_node->inlined_to);
      gcc_assert (target_node->real_symbol_p ());
      /* When sanitizing, do not assume that __cxa_pure_virtual is not called
	 by valid program.  */
      if (flag_sanitize & SANITIZE_UNREACHABLE)
	;
      /* Only add pure virtual if it is the only possible target.  This way
	 we will preserve the diagnostics about pure virtual called in many
	 cases without disabling optimization in other.  */
      else if (pure_virtual)
	{
	  if (nodes.length ())
	    return;
	}
      /* If we found a real target, take away cxa_pure_virtual.  */
      else if (!pure_virtual && nodes.length () == 1
	       && is_cxa_pure_virtual_p (nodes[0]->decl))
	nodes.pop ();
      if (pure_virtual && nodes.length ())
	return;
      if (!inserted->add (target))
	{
	  cached_polymorphic_call_targets->add (target_node);
	  nodes.safe_push (target_node);
	}
    }
  else if (!completep)
    ;
  /* We have definition of __cxa_pure_virtual that is not accessible (it is
     optimized out or partitioned to other unit) so we cannot add it.  When
     not sanitizing, there is nothing to do.
     Otherwise declare the list incomplete.  */
  else if (pure_virtual)
    {
      if (flag_sanitize & SANITIZE_UNREACHABLE)
	*completep = false;
    }
  else if (!type_whole_program_local_p (DECL_CONTEXT (target))
	   || DECL_EXTERNAL (target))
    *completep = false;
}

/* See if BINFO's type matches OUTER_TYPE.  If so, look up 
   BINFO of subtype of OTR_TYPE at OFFSET and in that BINFO find
   method in vtable and insert method to NODES array
   or BASES_TO_CONSIDER if this array is non-NULL.
   Otherwise recurse to base BINFOs.
   This matches what get_binfo_at_offset does, but with offset
   being unknown.

   TYPE_BINFOS is a stack of BINFOS of types with defined
   virtual table seen on way from class type to BINFO.

   MATCHED_VTABLES tracks virtual tables we already did lookup
   for virtual function in. INSERTED tracks nodes we already
   inserted.

   POSSIBLY_INSTANTIATED is true if there might exist instance
   of type.

   Clear COMPLETEP when we hit unreferable target.
  */

static void
record_target_from_binfo (vec <cgraph_node *> &nodes,
			  vec <tree> *bases_to_consider,
			  tree binfo,
			  tree otr_type,
			  vec <tree> &type_binfos,
			  HOST_WIDE_INT otr_token,
			  tree outer_type,
			  HOST_WIDE_INT offset,
			  hash_set<tree> *inserted,
			  hash_set<tree> *matched_vtables,
			  bool possibly_instantiated,
			  bool *completep)
{
  tree type = BINFO_TYPE (binfo);
  int i;
  tree base_binfo;


  if (BINFO_VTABLE (binfo))
    type_binfos.safe_push (binfo);
  if (types_same_for_odr (type, outer_type))
    {
      int i;
      tree type_binfo = NULL;

      /* Look up BINFO with virtual table.  For normal types it is always last
	 binfo on stack.  */
      for (i = type_binfos.length () - 1; i >= 0; i--)
	if (BINFO_OFFSET (type_binfos[i]) == BINFO_OFFSET (binfo))
	  {
	    type_binfo = type_binfos[i];
	    break;
	  }
      if (BINFO_VTABLE (binfo))
	type_binfos.pop ();
      /* If this is duplicated BINFO for base shared by virtual inheritance,
	 we may not have its associated vtable.  This is not a problem, since
	 we will walk it on the other path.  */
      if (!type_binfo)
	return;
      tree inner_binfo = get_binfo_at_offset (type_binfo,
					      offset, otr_type);
      if (!inner_binfo)
	{
	  gcc_assert (odr_violation_reported);
	  return;
	}
      /* For whole-program local types first check if the respective vtable is
	 alive. If not, we know the type can't be called.  */
      if (!possibly_instantiated)
	return;

      gcc_assert (inner_binfo);
      if (bases_to_consider
	  ? !matched_vtables->contains (BINFO_VTABLE (inner_binfo))
	  : !matched_vtables->add (BINFO_VTABLE (inner_binfo)))
	{
	  bool can_refer;
	  tree target = gimple_get_virt_method_for_binfo (otr_token,
							  inner_binfo,
							  &can_refer);
	  if (!bases_to_consider)
	    maybe_record_node (nodes, target, inserted, can_refer, completep);
	  /* Destructors are never called via construction vtables.  */
	  else if (!target || !DECL_CXX_DESTRUCTOR_P (target))
	    bases_to_consider->safe_push (target);
	}
      return;
    }

  /* Walk bases.  */
  for (i = 0; BINFO_BASE_ITERATE (binfo, i, base_binfo); i++)
    /* Walking bases that have no virtual method is pointless exercise.  */
    if (polymorphic_type_binfo_p (base_binfo))
      record_target_from_binfo (nodes, bases_to_consider, base_binfo, otr_type,
				type_binfos, 
				otr_token, outer_type, offset, inserted,
				matched_vtables, possibly_instantiated,
				completep);
  if (BINFO_VTABLE (binfo))
    type_binfos.pop ();
}
     
/* Look up virtual methods matching OTR_TYPE (with OFFSET and OTR_TOKEN)
   of TYPE, insert them to NODES, recurse into derived nodes. 
   INSERTED is used to avoid duplicate insertions of methods into NODES.
   MATCHED_VTABLES are used to avoid duplicate walking vtables.
   Clear COMPLETEP if unreferable target is found.

   If CONSIDER_CONSTRUCTION is true, record to BASES_TO_CONSIDER
   all cases where BASE_SKIPPED is true (because the base is abstract
   class).  */

static void
possible_polymorphic_call_targets_1 (vec <cgraph_node *> &nodes,
				     hash_set<tree> *inserted,
				     hash_set<tree> *matched_vtables,
				     tree otr_type,
				     odr_type type,
				     HOST_WIDE_INT otr_token,
				     tree outer_type,
				     HOST_WIDE_INT offset,
				     bool *completep,
				     vec <tree> &bases_to_consider,
				     bool consider_construction)
{
  tree binfo = TYPE_BINFO (type->type);
  unsigned int i;
  auto_vec <tree, 8> type_binfos;
  bool possibly_instantiated = type->possibly_instantiated_p ();

  /* We may need to consider types w/o instances because of possible derived
     types using their methods either directly or via construction vtables.
     We are safe to skip them when all derivations are known, since we will
     handle them later.
     This is done by recording them to BASES_TO_CONSIDER array.  */
  if (possibly_instantiated || consider_construction)
    {
      record_target_from_binfo (nodes,
				(!possibly_instantiated
				 && type->all_derivations_known_p ())
				? &bases_to_consider : NULL,
				binfo, otr_type, type_binfos, otr_token,
				outer_type, offset,
				inserted, matched_vtables,
				possibly_instantiated, completep);
    }
  for (i = 0; i < type->derived_types.length (); i++)
    possible_polymorphic_call_targets_1 (nodes, inserted, 
					 matched_vtables,
					 otr_type,
					 type->derived_types[i],
					 otr_token, outer_type, offset, completep,
					 bases_to_consider, consider_construction);
}

/* Cache of queries for polymorphic call targets.

   Enumerating all call targets may get expensive when there are many
   polymorphic calls in the program, so we memoize all the previous
   queries and avoid duplicated work.  */

class polymorphic_call_target_d
{
public:
  HOST_WIDE_INT otr_token;
  ipa_polymorphic_call_context context;
  odr_type type;
  vec <cgraph_node *> targets;
  tree decl_warning;
  int type_warning;
  unsigned int n_odr_types;
  bool complete;
  bool speculative;
};

/* Polymorphic call target cache helpers.  */

struct polymorphic_call_target_hasher
  : pointer_hash <polymorphic_call_target_d>
{
  static inline hashval_t hash (const polymorphic_call_target_d *);
  static inline bool equal (const polymorphic_call_target_d *,
			    const polymorphic_call_target_d *);
  static inline void remove (polymorphic_call_target_d *);
};

/* Return the computed hashcode for ODR_QUERY.  */

inline hashval_t
polymorphic_call_target_hasher::hash (const polymorphic_call_target_d *odr_query)
{
  inchash::hash hstate (odr_query->otr_token);

  hstate.add_hwi (odr_query->type->id);
  hstate.merge_hash (TYPE_UID (odr_query->context.outer_type));
  hstate.add_hwi (odr_query->context.offset);
  hstate.add_hwi (odr_query->n_odr_types);

  if (odr_query->context.speculative_outer_type)
    {
      hstate.merge_hash (TYPE_UID (odr_query->context.speculative_outer_type));
      hstate.add_hwi (odr_query->context.speculative_offset);
    }
  hstate.add_flag (odr_query->speculative);
  hstate.add_flag (odr_query->context.maybe_in_construction);
  hstate.add_flag (odr_query->context.maybe_derived_type);
  hstate.add_flag (odr_query->context.speculative_maybe_derived_type);
  hstate.commit_flag ();
  return hstate.end ();
}

/* Compare cache entries T1 and T2.  */

inline bool
polymorphic_call_target_hasher::equal (const polymorphic_call_target_d *t1,
				       const polymorphic_call_target_d *t2)
{
  return (t1->type == t2->type && t1->otr_token == t2->otr_token
	  && t1->speculative == t2->speculative
	  && t1->context.offset == t2->context.offset
	  && t1->context.speculative_offset == t2->context.speculative_offset
	  && t1->context.outer_type == t2->context.outer_type
	  && t1->context.speculative_outer_type == t2->context.speculative_outer_type
	  && t1->context.maybe_in_construction
	      == t2->context.maybe_in_construction
	  && t1->context.maybe_derived_type == t2->context.maybe_derived_type
	  && (t1->context.speculative_maybe_derived_type
	      == t2->context.speculative_maybe_derived_type)
	  /* Adding new type may affect outcome of target search.  */
	  && t1->n_odr_types == t2->n_odr_types);
}

/* Remove entry in polymorphic call target cache hash.  */

inline void
polymorphic_call_target_hasher::remove (polymorphic_call_target_d *v)
{
  v->targets.release ();
  free (v);
}

/* Polymorphic call target query cache.  */

typedef hash_table<polymorphic_call_target_hasher>
   polymorphic_call_target_hash_type;
static polymorphic_call_target_hash_type *polymorphic_call_target_hash;

/* Destroy polymorphic call target query cache.  */

static void
free_polymorphic_call_targets_hash ()
{
  if (cached_polymorphic_call_targets)
    {
      delete polymorphic_call_target_hash;
      polymorphic_call_target_hash = NULL;
      delete cached_polymorphic_call_targets;
      cached_polymorphic_call_targets = NULL;
    }
}

/* Force rebuilding type inheritance graph from scratch.
   This is use to make sure that we do not keep references to types
   which was not visible to free_lang_data.  */

void
rebuild_type_inheritance_graph ()
{
  if (!odr_hash)
    return;
  delete odr_hash;
  odr_hash = NULL;
  odr_types_ptr = NULL;
  free_polymorphic_call_targets_hash ();
}

/* When virtual function is removed, we may need to flush the cache.  */

static void
devirt_node_removal_hook (struct cgraph_node *n, void *d ATTRIBUTE_UNUSED)
{
  if (cached_polymorphic_call_targets
      && !thunk_expansion
      && cached_polymorphic_call_targets->contains (n))
    free_polymorphic_call_targets_hash ();
}

/* Look up base of BINFO that has virtual table VTABLE with OFFSET.  */

tree
subbinfo_with_vtable_at_offset (tree binfo, unsigned HOST_WIDE_INT offset,
				tree vtable)
{
  tree v = BINFO_VTABLE (binfo);
  int i;
  tree base_binfo;
  unsigned HOST_WIDE_INT this_offset;

  if (v)
    {
      if (!vtable_pointer_value_to_vtable (v, &v, &this_offset))
	gcc_unreachable ();

      if (offset == this_offset
	  && DECL_ASSEMBLER_NAME (v) == DECL_ASSEMBLER_NAME (vtable))
	return binfo;
    }

  for (i = 0; BINFO_BASE_ITERATE (binfo, i, base_binfo); i++)
    if (polymorphic_type_binfo_p (base_binfo))
      {
	base_binfo = subbinfo_with_vtable_at_offset (base_binfo, offset, vtable);
	if (base_binfo)
	  return base_binfo;
      }
  return NULL;
}

/* T is known constant value of virtual table pointer.
   Store virtual table to V and its offset to OFFSET. 
   Return false if T does not look like virtual table reference.  */

bool
vtable_pointer_value_to_vtable (const_tree t, tree *v,
				unsigned HOST_WIDE_INT *offset)
{
  /* We expect &MEM[(void *)&virtual_table + 16B].
     We obtain object's BINFO from the context of the virtual table. 
     This one contains pointer to virtual table represented via
     POINTER_PLUS_EXPR.  Verify that this pointer matches what
     we propagated through.

     In the case of virtual inheritance, the virtual tables may
     be nested, i.e. the offset may be different from 16 and we may
     need to dive into the type representation.  */
  if (TREE_CODE (t) == ADDR_EXPR
      && TREE_CODE (TREE_OPERAND (t, 0)) == MEM_REF
      && TREE_CODE (TREE_OPERAND (TREE_OPERAND (t, 0), 0)) == ADDR_EXPR
      && TREE_CODE (TREE_OPERAND (TREE_OPERAND (t, 0), 1)) == INTEGER_CST
      && (TREE_CODE (TREE_OPERAND (TREE_OPERAND (TREE_OPERAND (t, 0), 0), 0))
	  == VAR_DECL)
      && DECL_VIRTUAL_P (TREE_OPERAND (TREE_OPERAND
					 (TREE_OPERAND (t, 0), 0), 0)))
    {
      *v = TREE_OPERAND (TREE_OPERAND (TREE_OPERAND (t, 0), 0), 0);
      *offset = tree_to_uhwi (TREE_OPERAND (TREE_OPERAND (t, 0), 1));
      return true;
    }

  /* Alternative representation, used by C++ frontend is POINTER_PLUS_EXPR.
     We need to handle it when T comes from static variable initializer or
     BINFO. */
  if (TREE_CODE (t) == POINTER_PLUS_EXPR)
    {
      *offset = tree_to_uhwi (TREE_OPERAND (t, 1));
      t = TREE_OPERAND (t, 0);
    }
  else
    *offset = 0;

  if (TREE_CODE (t) != ADDR_EXPR)
    return false;
  *v = TREE_OPERAND (t, 0);
  return true;
}

/* T is known constant value of virtual table pointer.  Return BINFO of the
   instance type.  */

tree
vtable_pointer_value_to_binfo (const_tree t)
{
  tree vtable;
  unsigned HOST_WIDE_INT offset;

  if (!vtable_pointer_value_to_vtable (t, &vtable, &offset))
    return NULL_TREE;

  /* FIXME: for stores of construction vtables we return NULL,
     because we do not have BINFO for those. Eventually we should fix
     our representation to allow this case to be handled, too.
     In the case we see store of BINFO we however may assume
     that standard folding will be able to cope with it.  */
  return subbinfo_with_vtable_at_offset (TYPE_BINFO (DECL_CONTEXT (vtable)),
					 offset, vtable);
}

/* Walk bases of OUTER_TYPE that contain OTR_TYPE at OFFSET.
   Look up their respective virtual methods for OTR_TOKEN and OTR_TYPE
   and insert them in NODES.

   MATCHED_VTABLES and INSERTED is used to avoid duplicated work.  */

static void
record_targets_from_bases (tree otr_type,
			   HOST_WIDE_INT otr_token,
			   tree outer_type,
			   HOST_WIDE_INT offset,
			   vec <cgraph_node *> &nodes,
			   hash_set<tree> *inserted,
			   hash_set<tree> *matched_vtables,
			   bool *completep)
{
  while (true)
    {
      HOST_WIDE_INT pos, size;
      tree base_binfo;
      tree fld;

      if (types_same_for_odr (outer_type, otr_type))
	return;

      for (fld = TYPE_FIELDS (outer_type); fld; fld = DECL_CHAIN (fld))
	{
	  if (TREE_CODE (fld) != FIELD_DECL)
	    continue;

	  pos = int_bit_position (fld);
	  size = tree_to_shwi (DECL_SIZE (fld));
	  if (pos <= offset && (pos + size) > offset
	      /* Do not get confused by zero sized bases.  */
	      && polymorphic_type_binfo_p (TYPE_BINFO (TREE_TYPE (fld))))
	    break;
	}
      /* Within a class type we should always find corresponding fields.  */
      gcc_assert (fld && TREE_CODE (TREE_TYPE (fld)) == RECORD_TYPE);

      /* Nonbase types should have been stripped by outer_class_type.  */
      gcc_assert (DECL_ARTIFICIAL (fld));

      outer_type = TREE_TYPE (fld);
      offset -= pos;

      base_binfo = get_binfo_at_offset (TYPE_BINFO (outer_type),
					offset, otr_type);
      if (!base_binfo)
	{
	  gcc_assert (odr_violation_reported);
	  return;
	}
      gcc_assert (base_binfo);
      if (!matched_vtables->add (BINFO_VTABLE (base_binfo)))
	{
	  bool can_refer;
	  tree target = gimple_get_virt_method_for_binfo (otr_token,
							  base_binfo,
							  &can_refer);
	  if (!target || ! DECL_CXX_DESTRUCTOR_P (target))
	    maybe_record_node (nodes, target, inserted, can_refer, completep);
	  matched_vtables->add (BINFO_VTABLE (base_binfo));
	}
    }
}

/* When virtual table is removed, we may need to flush the cache.  */

static void
devirt_variable_node_removal_hook (varpool_node *n,
				   void *d ATTRIBUTE_UNUSED)
{
  if (cached_polymorphic_call_targets
      && DECL_VIRTUAL_P (n->decl)
      && type_whole_program_local_p (DECL_CONTEXT (n->decl)))
    free_polymorphic_call_targets_hash ();
}

/* Record about how many calls would benefit from given type to be final.  */

struct odr_type_warn_count
{
  tree type;
  int count;
  profile_count dyn_count;
};

/* Record about how many calls would benefit from given method to be final.  */

struct decl_warn_count
{
  tree decl;
  int count;
  profile_count dyn_count;
};

/* Information about type and decl warnings.  */

class final_warning_record
{
public:
  /* If needed grow type_warnings vector and initialize new decl_warn_count
     to have dyn_count set to profile_count::zero ().  */
  void grow_type_warnings (unsigned newlen);

  profile_count dyn_count;
  auto_vec<odr_type_warn_count> type_warnings;
  hash_map<tree, decl_warn_count> decl_warnings;
};

void
final_warning_record::grow_type_warnings (unsigned newlen)
{
  unsigned len = type_warnings.length ();
  if (newlen > len)
    {
      type_warnings.safe_grow_cleared (newlen, true);
      for (unsigned i = len; i < newlen; i++)
	type_warnings[i].dyn_count = profile_count::zero ();
    }
}

class final_warning_record *final_warning_records;

/* Return vector containing possible targets of polymorphic call of type
   OTR_TYPE calling method OTR_TOKEN within type of OTR_OUTER_TYPE and OFFSET.
   If INCLUDE_BASES is true, walk also base types of OUTER_TYPES containing
   OTR_TYPE and include their virtual method.  This is useful for types
   possibly in construction or destruction where the virtual table may
   temporarily change to one of base types.  INCLUDE_DERIVED_TYPES make
   us to walk the inheritance graph for all derivations.

   If COMPLETEP is non-NULL, store true if the list is complete. 
   CACHE_TOKEN (if non-NULL) will get stored to an unique ID of entry
   in the target cache.  If user needs to visit every target list
   just once, it can memoize them.

   If SPECULATIVE is set, the list will not contain targets that
   are not speculatively taken.

   Returned vector is placed into cache.  It is NOT caller's responsibility
   to free it.  The vector can be freed on cgraph_remove_node call if
   the particular node is a virtual function present in the cache.  */

vec <cgraph_node *>
possible_polymorphic_call_targets (tree otr_type,
			           HOST_WIDE_INT otr_token,
				   ipa_polymorphic_call_context context,
			           bool *completep,
			           void **cache_token,
				   bool speculative)
{
  static struct cgraph_node_hook_list *node_removal_hook_holder;
  vec <cgraph_node *> nodes = vNULL;
  auto_vec <tree, 8> bases_to_consider;
  odr_type type, outer_type;
  polymorphic_call_target_d key;
  polymorphic_call_target_d **slot;
  unsigned int i;
  tree binfo, target;
  bool complete;
  bool can_refer = false;
  bool skipped = false;

  otr_type = TYPE_MAIN_VARIANT (otr_type);

  /* If ODR is not initialized or the context is invalid, return empty
     incomplete list.  */
  if (!odr_hash || context.invalid || !TYPE_BINFO (otr_type))
    {
      if (completep)
	*completep = context.invalid;
      if (cache_token)
	*cache_token = NULL;
      return nodes;
    }

  /* Do not bother to compute speculative info when user do not asks for it.  */
  if (!speculative || !context.speculative_outer_type)
    context.clear_speculation ();

  type = get_odr_type (otr_type, true);

  /* Recording type variants would waste results cache.  */
  gcc_assert (!context.outer_type
	      || TYPE_MAIN_VARIANT (context.outer_type) == context.outer_type);

  /* Look up the outer class type we want to walk.
     If we fail to do so, the context is invalid.  */
  if ((context.outer_type || context.speculative_outer_type)
      && !context.restrict_to_inner_class (otr_type))
    {
      if (completep)
	*completep = true;
      if (cache_token)
	*cache_token = NULL;
      return nodes;
    }
  gcc_assert (!context.invalid);

  /* Check that restrict_to_inner_class kept the main variant.  */
  gcc_assert (!context.outer_type
	      || TYPE_MAIN_VARIANT (context.outer_type) == context.outer_type);

  /* We canonicalize our query, so we do not need extra hashtable entries.  */

  /* Without outer type, we have no use for offset.  Just do the
     basic search from inner type.  */
  if (!context.outer_type)
    context.clear_outer_type (otr_type);
  /* We need to update our hierarchy if the type does not exist.  */
  outer_type = get_odr_type (context.outer_type, true);
  /* If the type is complete, there are no derivations.  */
  if (TYPE_FINAL_P (outer_type->type))
    context.maybe_derived_type = false;

  /* Initialize query cache.  */
  if (!cached_polymorphic_call_targets)
    {
      cached_polymorphic_call_targets = new hash_set<cgraph_node *>;
      polymorphic_call_target_hash
       	= new polymorphic_call_target_hash_type (23);
      if (!node_removal_hook_holder)
	{
	  node_removal_hook_holder =
	    symtab->add_cgraph_removal_hook (&devirt_node_removal_hook, NULL);
	  symtab->add_varpool_removal_hook (&devirt_variable_node_removal_hook,
					 NULL);
	}
    }

  if (in_lto_p)
    {
      if (context.outer_type != otr_type)
        context.outer_type
	  = get_odr_type (context.outer_type, true)->type;
      if (context.speculative_outer_type)
        context.speculative_outer_type
	  = get_odr_type (context.speculative_outer_type, true)->type;
    }

  /* Look up cached answer.  */
  key.type = type;
  key.otr_token = otr_token;
  key.speculative = speculative;
  key.context = context;
  key.n_odr_types = odr_types.length ();
  slot = polymorphic_call_target_hash->find_slot (&key, INSERT);
  if (cache_token)
   *cache_token = (void *)*slot;
  if (*slot)
    {
      if (completep)
	*completep = (*slot)->complete;
      if ((*slot)->type_warning && final_warning_records)
	{
	  final_warning_records->type_warnings[(*slot)->type_warning - 1].count++;
	  if (!final_warning_records->type_warnings
		[(*slot)->type_warning - 1].dyn_count.initialized_p ())
	    final_warning_records->type_warnings
		[(*slot)->type_warning - 1].dyn_count = profile_count::zero ();
	  if (final_warning_records->dyn_count > 0)
	    final_warning_records->type_warnings[(*slot)->type_warning - 1].dyn_count
	      = final_warning_records->type_warnings[(*slot)->type_warning - 1].dyn_count
	        + final_warning_records->dyn_count;
	}
      if (!speculative && (*slot)->decl_warning && final_warning_records)
	{
	  struct decl_warn_count *c =
	     final_warning_records->decl_warnings.get ((*slot)->decl_warning);
	  c->count++;
	  if (final_warning_records->dyn_count > 0)
	    c->dyn_count += final_warning_records->dyn_count;
	}
      return (*slot)->targets;
    }

  if (!flag_safe_vcall && !in_lto_p && !vcall_fixup_done)
    complete = false;
  else
    complete = true;

  /* Do actual search.  */
  timevar_push (TV_IPA_VIRTUAL_CALL);
  *slot = XCNEW (polymorphic_call_target_d);
  if (cache_token)
    *cache_token = (void *)*slot;
  (*slot)->type = type;
  (*slot)->otr_token = otr_token;
  (*slot)->context = context;
  (*slot)->speculative = speculative;

  hash_set<tree> inserted;
  hash_set<tree> matched_vtables;

  /* First insert targets we speculatively identified as likely.  */
  if (context.speculative_outer_type)
    {
      odr_type speculative_outer_type;
      bool speculation_complete = true;
      bool check_derived_types = false;

      /* First insert target from type itself and check if it may have
	 derived types.  */
      speculative_outer_type = get_odr_type (context.speculative_outer_type, true);
      if (TYPE_FINAL_P (speculative_outer_type->type))
	context.speculative_maybe_derived_type = false;
      binfo = get_binfo_at_offset (TYPE_BINFO (speculative_outer_type->type),
				   context.speculative_offset, otr_type);
      if (binfo)
	target = gimple_get_virt_method_for_binfo (otr_token, binfo,
						   &can_refer);
      else
	target = NULL;

      /* In the case we get complete method, we don't need 
	 to walk derivations.  */
      if (target && DECL_FINAL_P (target))
	context.speculative_maybe_derived_type = false;

      if (check_derived_types
	  ? type_or_derived_type_possibly_instantiated_p
		 (speculative_outer_type)
	  : speculative_outer_type->possibly_instantiated_p ())
	maybe_record_node (nodes, target, &inserted, can_refer,
			   &speculation_complete);
      if (binfo)
	matched_vtables.add (BINFO_VTABLE (binfo));


      /* Next walk recursively all derived types.  */
      if (context.speculative_maybe_derived_type)
	for (i = 0; i < speculative_outer_type->derived_types.length(); i++)
	  possible_polymorphic_call_targets_1 (nodes, &inserted,
					       &matched_vtables,
					       otr_type,
					       speculative_outer_type->derived_types[i],
					       otr_token, speculative_outer_type->type,
					       context.speculative_offset,
					       &speculation_complete,
					       bases_to_consider,
					       false);
    }

  if (!speculative || !nodes.length ())
    {
      bool check_derived_types = false;
      /* First see virtual method of type itself.  */
      binfo = get_binfo_at_offset (TYPE_BINFO (outer_type->type),
				   context.offset, otr_type);
      if (binfo)
	target = gimple_get_virt_method_for_binfo (otr_token, binfo,
						   &can_refer);
      else
	{
	  gcc_assert (odr_violation_reported);
	  target = NULL;
	}

      /* Destructors are never called through construction virtual tables,
	 because the type is always known.  */
      if (target && DECL_CXX_DESTRUCTOR_P (target))
	context.maybe_in_construction = false;

      /* In the case we get complete method, we don't need 
	 to walk derivations.  */
      if (target && DECL_FINAL_P (target))
	{
	  check_derived_types = true;
	  context.maybe_derived_type = false;
	}

      /* If OUTER_TYPE is abstract, we know we are not seeing its instance.  */
      if (check_derived_types
	  ? type_or_derived_type_possibly_instantiated_p (outer_type)
	  : outer_type->possibly_instantiated_p ())
	maybe_record_node (nodes, target, &inserted, can_refer, &complete);
      else
	skipped = true;

      if (binfo)
	matched_vtables.add (BINFO_VTABLE (binfo));

      /* Next walk recursively all derived types.  */
      if (context.maybe_derived_type)
	{
	  for (i = 0; i < outer_type->derived_types.length(); i++)
	    possible_polymorphic_call_targets_1 (nodes, &inserted,
						 &matched_vtables,
						 otr_type,
						 outer_type->derived_types[i],
						 otr_token, outer_type->type,
						 context.offset, &complete,
						 bases_to_consider,
						 context.maybe_in_construction);

	  if (!outer_type->all_derivations_known_p ())
	    {
	      if (!speculative && final_warning_records
		  && nodes.length () == 1
		  && TREE_CODE (TREE_TYPE (nodes[0]->decl)) == METHOD_TYPE)
		{
		  if (complete
		      && warn_suggest_final_types
		      && !outer_type->derived_types.length ())
		    {
		      final_warning_records->grow_type_warnings
			(outer_type->id);
		      final_warning_records->type_warnings[outer_type->id].count++;
		      if (!final_warning_records->type_warnings
				[outer_type->id].dyn_count.initialized_p ())
			final_warning_records->type_warnings
			   [outer_type->id].dyn_count = profile_count::zero ();
		      final_warning_records->type_warnings[outer_type->id].dyn_count
			+= final_warning_records->dyn_count;
		      final_warning_records->type_warnings[outer_type->id].type
			= outer_type->type;
		      (*slot)->type_warning = outer_type->id + 1;
		    }
		  if (complete
		      && warn_suggest_final_methods
		      && types_same_for_odr (DECL_CONTEXT (nodes[0]->decl),
					     outer_type->type))
		    {
		      bool existed;
		      struct decl_warn_count &c =
			 final_warning_records->decl_warnings.get_or_insert
			    (nodes[0]->decl, &existed);

		      if (existed)
			{
			  c.count++;
			  c.dyn_count += final_warning_records->dyn_count;
			}
		      else
			{
			  c.count = 1;
			  c.dyn_count = final_warning_records->dyn_count;
			  c.decl = nodes[0]->decl;
			}
		      (*slot)->decl_warning = nodes[0]->decl;
		    }
		}
	      complete = false;
	    }
	}

      if (!speculative)
	{
	  /* Destructors are never called through construction virtual tables,
	     because the type is always known.  One of entries may be
	     cxa_pure_virtual so look to at least two of them.  */
	  if (context.maybe_in_construction)
	    for (i =0 ; i < MIN (nodes.length (), 2); i++)
	      if (DECL_CXX_DESTRUCTOR_P (nodes[i]->decl))
		context.maybe_in_construction = false;
	  if (context.maybe_in_construction)
	    {
	      if (type != outer_type
		  && (!skipped
		      || (context.maybe_derived_type
			  && !outer_type->all_derivations_known_p ())))
		record_targets_from_bases (otr_type, otr_token, outer_type->type,
					   context.offset, nodes, &inserted,
					   &matched_vtables, &complete);
	      if (skipped)
		maybe_record_node (nodes, target, &inserted, can_refer, &complete);
	      for (i = 0; i < bases_to_consider.length(); i++)
		maybe_record_node (nodes, bases_to_consider[i], &inserted, can_refer, &complete);
	    }
	}
    }

  (*slot)->targets = nodes;
  (*slot)->complete = complete;
  (*slot)->n_odr_types = odr_types.length ();
  if (completep)
    *completep = complete;

  timevar_pop (TV_IPA_VIRTUAL_CALL);
  return nodes;
}

bool
add_decl_warning (const tree &key ATTRIBUTE_UNUSED, const decl_warn_count &value,
		  vec<const decl_warn_count*> *vec)
{
  vec->safe_push (&value);
  return true;
}

/* Dump target list TARGETS into FILE.  */

static void
dump_targets (FILE *f, vec <cgraph_node *> targets, bool verbose)
{
  unsigned int i;

  for (i = 0; i < targets.length (); i++)
    {
      char *name = NULL;
      if (in_lto_p)
	name = cplus_demangle_v3 (targets[i]->asm_name (), 0);
      fprintf (f, " %s", name ? name : targets[i]->dump_name ());
      if (in_lto_p)
	free (name);
      if (!targets[i]->definition)
	fprintf (f, " (no definition%s)",
		 DECL_DECLARED_INLINE_P (targets[i]->decl)
		 ? " inline" : "");
      /* With many targets for every call polymorphic dumps are going to
	 be quadratic in size.  */
      if (i > 10 && !verbose)
	{
	  fprintf (f, " ... and %i more targets\n", targets.length () - i);
	  return;
	}
    }
  fprintf (f, "\n");
}

/* Dump all possible targets of a polymorphic call.  */

void
dump_possible_polymorphic_call_targets (FILE *f,
					tree otr_type,
					HOST_WIDE_INT otr_token,
					const ipa_polymorphic_call_context &ctx,
					bool verbose)
{
  vec <cgraph_node *> targets;
  bool final;
  odr_type type = get_odr_type (TYPE_MAIN_VARIANT (otr_type), false);
  unsigned int len;

  if (!type)
    return;
  targets = possible_polymorphic_call_targets (otr_type, otr_token,
					       ctx,
					       &final, NULL, false);
  fprintf (f, "  Targets of polymorphic call of type %i:", type->id);
  print_generic_expr (f, type->type, TDF_SLIM);
  fprintf (f, " token %i\n", (int)otr_token);

  ctx.dump (f);

  fprintf (f, "    %s%s%s%s\n      ",
	   final ? "This is a complete list." :
	   "This is partial list; extra targets may be defined in other units.",
	   ctx.maybe_in_construction ? " (base types included)" : "",
	   ctx.maybe_derived_type ? " (derived types included)" : "",
	   ctx.speculative_maybe_derived_type ? " (speculative derived types included)" : "");
  len = targets.length ();
  dump_targets (f, targets, verbose);

  targets = possible_polymorphic_call_targets (otr_type, otr_token,
					       ctx,
					       &final, NULL, true);
  if (targets.length () != len)
    {
      fprintf (f, "  Speculative targets:");
      dump_targets (f, targets, verbose);
    }
  /* Ugly: during callgraph construction the target cache may get populated
     before all targets are found.  While this is harmless (because all local
     types are discovered and only in those case we devirtualize fully and we
     don't do speculative devirtualization before IPA stage) it triggers
     assert here when dumping at that stage also populates the case with
     speculative targets.  Quietly ignore this.  */
  gcc_assert (symtab->state < IPA_SSA || targets.length () <= len);
  fprintf (f, "\n");
}


/* Return true if N can be possibly target of a polymorphic call of
   OTR_TYPE/OTR_TOKEN.  */

bool
possible_polymorphic_call_target_p (tree otr_type,
				    HOST_WIDE_INT otr_token,
				    const ipa_polymorphic_call_context &ctx,
				    struct cgraph_node *n)
{
  vec <cgraph_node *> targets;
  unsigned int i;
  bool final;

  if (fndecl_built_in_p (n->decl, BUILT_IN_UNREACHABLE)
      || fndecl_built_in_p (n->decl, BUILT_IN_TRAP))
    return true;

  if (is_cxa_pure_virtual_p (n->decl))
    return true;

  if (!odr_hash)
    return true;
  targets = possible_polymorphic_call_targets (otr_type, otr_token, ctx, &final);
  for (i = 0; i < targets.length (); i++)
    if (n->semantically_equivalent_p (targets[i]))
      return true;

  /* At a moment we allow middle end to dig out new external declarations
     as a targets of polymorphic calls.  */
  if (!final && !n->definition)
    return true;
  return false;
}


/* Return true if N can be possibly target of a polymorphic call of
   OBJ_TYPE_REF expression REF in STMT.  */

bool
possible_polymorphic_call_target_p (tree ref,
				    gimple *stmt,
				    struct cgraph_node *n)
{
  ipa_polymorphic_call_context context (current_function_decl, ref, stmt);
  tree call_fn = gimple_call_fn (stmt);

  return possible_polymorphic_call_target_p (obj_type_ref_class (call_fn),
					     tree_to_uhwi
					       (OBJ_TYPE_REF_TOKEN (call_fn)),
					     context,
					     n);
}


/* After callgraph construction new external nodes may appear.
   Add them into the graph.  */

void
update_type_inheritance_graph (void)
{
  struct cgraph_node *n;

  if (!odr_hash)
    return;
  free_polymorphic_call_targets_hash ();
  timevar_push (TV_IPA_INHERITANCE);
  /* We reconstruct the graph starting from types of all methods seen in the
     unit.  */
  FOR_EACH_FUNCTION (n)
    if (DECL_VIRTUAL_P (n->decl)
	&& !n->definition
	&& n->real_symbol_p ())
      get_odr_type (TYPE_METHOD_BASETYPE (TREE_TYPE (n->decl)), true);
  timevar_pop (TV_IPA_INHERITANCE);
}


/* Return true if N looks like likely target of a polymorphic call.
   Rule out cxa_pure_virtual, noreturns, function declared cold and
   other obvious cases.  */

bool
likely_target_p (struct cgraph_node *n)
{
  int flags;
  /* cxa_pure_virtual and similar things are not likely.  */
  if (TREE_CODE (TREE_TYPE (n->decl)) != METHOD_TYPE)
    return false;
  flags = flags_from_decl_or_type (n->decl);
  if (flags & ECF_NORETURN)
    return false;
  if (lookup_attribute ("cold",
			DECL_ATTRIBUTES (n->decl)))
    return false;
  if (n->frequency < NODE_FREQUENCY_NORMAL)
    return false;
  /* If there are no live virtual tables referring the target,
     the only way the target can be called is an instance coming from other
     compilation unit; speculative devirtualization is built around an
     assumption that won't happen.  */
  if (!referenced_from_vtable_p (n))
    return false;
  return true;
}

/* Compare type warning records P1 and P2 and choose one with larger count;
   helper for qsort.  */

static int
type_warning_cmp (const void *p1, const void *p2)
{
  const odr_type_warn_count *t1 = (const odr_type_warn_count *)p1;
  const odr_type_warn_count *t2 = (const odr_type_warn_count *)p2;

  if (t1->dyn_count < t2->dyn_count)
   return 1;
  if (t1->dyn_count > t2->dyn_count)
   return -1;
  return t2->count - t1->count;
}

/* Compare decl warning records P1 and P2 and choose one with larger count;
   helper for qsort.  */

static int
decl_warning_cmp (const void *p1, const void *p2)
{
  const decl_warn_count *t1 = *(const decl_warn_count * const *)p1;
  const decl_warn_count *t2 = *(const decl_warn_count * const *)p2;

  if (t1->dyn_count < t2->dyn_count)
   return 1;
  if (t1->dyn_count > t2->dyn_count)
   return -1;
  return t2->count - t1->count;
}


/* Try to speculatively devirtualize call to OTR_TYPE with OTR_TOKEN with
   context CTX.  */

struct cgraph_node *
try_speculative_devirtualization (tree otr_type, HOST_WIDE_INT otr_token,
				  ipa_polymorphic_call_context ctx)
{
  vec <cgraph_node *>targets
     = possible_polymorphic_call_targets
	  (otr_type, otr_token, ctx, NULL, NULL, true);
  unsigned int i;
  struct cgraph_node *likely_target = NULL;

  for (i = 0; i < targets.length (); i++)
    if (likely_target_p (targets[i]))
      {
	if (likely_target)
	  return NULL;
	likely_target = targets[i];
      }
  if (!likely_target
      ||!likely_target->definition
      || DECL_EXTERNAL (likely_target->decl))
    return NULL;

  /* Don't use an implicitly-declared destructor (c++/58678).  */
  struct cgraph_node *non_thunk_target
    = likely_target->function_symbol ();
  if (DECL_ARTIFICIAL (non_thunk_target->decl))
    return NULL;
  if (likely_target->get_availability () <= AVAIL_INTERPOSABLE
      && likely_target->can_be_discarded_p ())
    return NULL;
  return likely_target;
}

/* The ipa-devirt pass.
   When polymorphic call has only one likely target in the unit,
   turn it into a speculative call.  */

static unsigned int
ipa_devirt (void)
{
  struct cgraph_node *n;
  hash_set<void *> bad_call_targets;
  struct cgraph_edge *e;

  int npolymorphic = 0, nspeculated = 0, nconverted = 0, ncold = 0;
  int nmultiple = 0, noverwritable = 0, ndevirtualized = 0, nnotdefined = 0;
  int nwrong = 0, nok = 0, nexternal = 0, nartificial = 0;
  int ndropped = 0;

  if (!odr_types_ptr)
    return 0;

  if (dump_file)
    dump_type_inheritance_graph (dump_file);

  /* We can output -Wsuggest-final-methods and -Wsuggest-final-types warnings.
     This is implemented by setting up final_warning_records that are updated
     by get_polymorphic_call_targets.
     We need to clear cache in this case to trigger recomputation of all
     entries.  */
  if (warn_suggest_final_methods || warn_suggest_final_types)
    {
      final_warning_records = new (final_warning_record);
      final_warning_records->dyn_count = profile_count::zero ();
      final_warning_records->grow_type_warnings (odr_types.length ());
      free_polymorphic_call_targets_hash ();
    }

  FOR_EACH_DEFINED_FUNCTION (n)
    {	
      bool update = false;
      if (!opt_for_fn (n->decl, flag_devirtualize))
	continue;
      if (dump_file && n->indirect_calls)
	fprintf (dump_file, "\n\nProcesing function %s\n",
		 n->dump_name ());
      for (e = n->indirect_calls; e; e = e->next_callee)
	if (e->indirect_info->polymorphic)
	  {
	    struct cgraph_node *likely_target = NULL;
	    void *cache_token;
	    bool final;

	    if (final_warning_records)
	      final_warning_records->dyn_count = e->count.ipa ();

	    vec <cgraph_node *>targets
	       = possible_polymorphic_call_targets
		    (e, &final, &cache_token, true);
	    unsigned int i;

	    /* Trigger warnings by calculating non-speculative targets.  */
	    if (warn_suggest_final_methods || warn_suggest_final_types)
	      possible_polymorphic_call_targets (e);

	    if (dump_file)
	      dump_possible_polymorphic_call_targets 
		(dump_file, e, (dump_flags & TDF_DETAILS));

	    npolymorphic++;

	    /* See if the call can be devirtualized by means of ipa-prop's
	       polymorphic call context propagation.  If not, we can just
	       forget about this call being polymorphic and avoid some heavy
	       lifting in remove_unreachable_nodes that will otherwise try to
	       keep all possible targets alive until inlining and in the inliner
	       itself.

	       This may need to be revisited once we add further ways to use
	       the may edges, but it is a reasonable thing to do right now.  */

	    if ((e->indirect_info->param_index == -1
		|| (!opt_for_fn (n->decl, flag_devirtualize_speculatively)
		    && e->indirect_info->vptr_changed))
		&& !flag_ltrans_devirtualize)
	      {
		e->indirect_info->polymorphic = false;
		ndropped++;
	        if (dump_file)
		  fprintf (dump_file, "Dropping polymorphic call info;"
			   " it cannot be used by ipa-prop\n");
	      }

	    if (!opt_for_fn (n->decl, flag_devirtualize_speculatively))
	      continue;

	    if (!e->maybe_hot_p ())
	      {
		if (dump_file)
		  fprintf (dump_file, "Call is cold\n\n");
		ncold++;
		continue;
	      }
	    if (e->speculative)
	      {
		if (dump_file)
		  fprintf (dump_file, "Call is already speculated\n\n");
		nspeculated++;

		/* When dumping see if we agree with speculation.  */
		if (!dump_file)
		  continue;
	      }
	    if (bad_call_targets.contains (cache_token))
	      {
		if (dump_file)
		  fprintf (dump_file, "Target list is known to be useless\n\n");
		nmultiple++;
		continue;
	      }
	    for (i = 0; i < targets.length (); i++)
	      if (likely_target_p (targets[i]))
		{
		  if (likely_target)
		    {
		      likely_target = NULL;
		      if (dump_file)
			fprintf (dump_file, "More than one likely target\n\n");
		      nmultiple++;
		      break;
		    }
		  likely_target = targets[i];
		}
	    if (!likely_target)
	      {
		bad_call_targets.add (cache_token);
	        continue;
	      }
	    /* This is reached only when dumping; check if we agree or disagree
 	       with the speculation.  */
	    if (e->speculative)
	      {
		bool found = e->speculative_call_for_target (likely_target);
		if (found)
		  {
		    fprintf (dump_file, "We agree with speculation\n\n");
		    nok++;
		  }
		else
		  {
		    fprintf (dump_file, "We disagree with speculation\n\n");
		    nwrong++;
		  }
		continue;
	      }
	    if (!likely_target->definition)
	      {
		if (dump_file)
		  fprintf (dump_file, "Target is not a definition\n\n");
		nnotdefined++;
		continue;
	      }
	    /* Do not introduce new references to external symbols.  While we
	       can handle these just well, it is common for programs to
	       incorrectly with headers defining methods they are linked
	       with.  */
	    if (DECL_EXTERNAL (likely_target->decl))
	      {
		if (dump_file)
		  fprintf (dump_file, "Target is external\n\n");
		nexternal++;
		continue;
	      }
	    /* Don't use an implicitly-declared destructor (c++/58678).  */
	    struct cgraph_node *non_thunk_target
	      = likely_target->function_symbol ();
	    if (DECL_ARTIFICIAL (non_thunk_target->decl))
	      {
		if (dump_file)
		  fprintf (dump_file, "Target is artificial\n\n");
		nartificial++;
		continue;
	      }
	    if (likely_target->get_availability () <= AVAIL_INTERPOSABLE
		&& likely_target->can_be_discarded_p ())
	      {
		if (dump_file)
		  fprintf (dump_file, "Target is overwritable\n\n");
		noverwritable++;
		continue;
	      }
	    else if (dbg_cnt (devirt))
	      {
		if (dump_enabled_p ())
                  {
                    dump_printf_loc (MSG_OPTIMIZED_LOCATIONS, e->call_stmt,
				     "speculatively devirtualizing call "
				     "in %s to %s\n",
				     n->dump_name (),
				     likely_target->dump_name ());
                  }
		if (!likely_target->can_be_discarded_p ())
		  {
		    cgraph_node *alias;
		    alias = dyn_cast<cgraph_node *> (likely_target->noninterposable_alias ());
		    if (alias)
		      likely_target = alias;
		  }
		nconverted++;
		update = true;
		e->make_speculative
		  (likely_target, e->count.apply_scale (8, 10));
	      }
	  }
      if (update)
	ipa_update_overall_fn_summary (n);
    }
  if (warn_suggest_final_methods || warn_suggest_final_types)
    {
      if (warn_suggest_final_types)
	{
	  final_warning_records->type_warnings.qsort (type_warning_cmp);
	  for (unsigned int i = 0;
	       i < final_warning_records->type_warnings.length (); i++)
	    if (final_warning_records->type_warnings[i].count)
	      {
	        tree type = final_warning_records->type_warnings[i].type;
	        int count = final_warning_records->type_warnings[i].count;
	        profile_count dyn_count
		  = final_warning_records->type_warnings[i].dyn_count;

		if (!(dyn_count > 0))
		  warning_n (DECL_SOURCE_LOCATION (TYPE_NAME (type)),
			     OPT_Wsuggest_final_types, count,
			     "Declaring type %qD final "
			     "would enable devirtualization of %i call",
			     "Declaring type %qD final "
			     "would enable devirtualization of %i calls",
			     type,
			     count);
		else
		  warning_n (DECL_SOURCE_LOCATION (TYPE_NAME (type)),
			     OPT_Wsuggest_final_types, count,
			     "Declaring type %qD final "
			     "would enable devirtualization of %i call "
			     "executed %lli times",
			     "Declaring type %qD final "
			     "would enable devirtualization of %i calls "
			     "executed %lli times",
			     type,
			     count,
			     (long long) dyn_count.to_gcov_type ());
	      }
	}

      if (warn_suggest_final_methods)
	{
	  auto_vec<const decl_warn_count*> decl_warnings_vec;

	  final_warning_records->decl_warnings.traverse
	    <vec<const decl_warn_count *> *, add_decl_warning> (&decl_warnings_vec);
	  decl_warnings_vec.qsort (decl_warning_cmp);
	  for (unsigned int i = 0; i < decl_warnings_vec.length (); i++)
	    {
	      tree decl = decl_warnings_vec[i]->decl;
	      int count = decl_warnings_vec[i]->count;
	      profile_count dyn_count
		  = decl_warnings_vec[i]->dyn_count;

	      if (!(dyn_count > 0))
		if (DECL_CXX_DESTRUCTOR_P (decl))
		  warning_n (DECL_SOURCE_LOCATION (decl),
			      OPT_Wsuggest_final_methods, count,
			      "Declaring virtual destructor of %qD final "
			      "would enable devirtualization of %i call",
			      "Declaring virtual destructor of %qD final "
			      "would enable devirtualization of %i calls",
			      DECL_CONTEXT (decl), count);
		else
		  warning_n (DECL_SOURCE_LOCATION (decl),
			      OPT_Wsuggest_final_methods, count,
			      "Declaring method %qD final "
			      "would enable devirtualization of %i call",
			      "Declaring method %qD final "
			      "would enable devirtualization of %i calls",
			      decl, count);
	       else if (DECL_CXX_DESTRUCTOR_P (decl))
		  warning_n (DECL_SOURCE_LOCATION (decl),
			      OPT_Wsuggest_final_methods, count,
			      "Declaring virtual destructor of %qD final "
			      "would enable devirtualization of %i call "
			      "executed %lli times",
			      "Declaring virtual destructor of %qD final "
			      "would enable devirtualization of %i calls "
			      "executed %lli times",
			      DECL_CONTEXT (decl), count,
			      (long long)dyn_count.to_gcov_type ());
		else
		  warning_n (DECL_SOURCE_LOCATION (decl),
			      OPT_Wsuggest_final_methods, count,
			      "Declaring method %qD final "
			      "would enable devirtualization of %i call "
			      "executed %lli times",
			      "Declaring method %qD final "
			      "would enable devirtualization of %i calls "
			      "executed %lli times",
			      decl, count,
			      (long long)dyn_count.to_gcov_type ());
	    }
	}

      delete (final_warning_records);
      final_warning_records = 0;
    }

  if (dump_file)
    fprintf (dump_file,
	     "%i polymorphic calls, %i devirtualized,"
	     " %i speculatively devirtualized, %i cold\n"
	     "%i have multiple targets, %i overwritable,"
	     " %i already speculated (%i agree, %i disagree),"
	     " %i external, %i not defined, %i artificial, %i infos dropped\n",
	     npolymorphic, ndevirtualized, nconverted, ncold,
	     nmultiple, noverwritable, nspeculated, nok, nwrong,
	     nexternal, nnotdefined, nartificial, ndropped);
  return ndevirtualized || ndropped ? TODO_remove_functions : 0;
}

static tree
get_field_type (tree type, HOST_WIDE_INT offset)
{
  if (offset < 0)
    return NULL_TREE;

  while (TREE_CODE (type) == ARRAY_TYPE)
    type = TREE_TYPE (type);

  if (TREE_CODE (type) != RECORD_TYPE)
    return NULL_TREE;

  tree size = TYPE_SIZE_UNIT (type);

  if (!size || TREE_CODE (size) != INTEGER_CST || !tree_fits_shwi_p (size))
    return NULL_TREE;

  if (tree_to_shwi (size) <= offset)
    return NULL_TREE;

  for (tree field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
    {
      if (skip_in_fields_list_p (field))
	continue;

      offset_int field_offset = wi::to_offset (DECL_FIELD_OFFSET (field));

      field_offset += wi::to_offset (DECL_FIELD_BIT_OFFSET (field))
				     >> LOG2_BITS_PER_UNIT;

      if (field_offset == offset)
	return TREE_TYPE (field);

      if (field_offset > offset)
	break;
    }

  return NULL_TREE;
}

static void
fixup_vcall (cgraph_edge *edge)
{
  tree call_fn = gimple_call_fn (edge->call_stmt);

  if (!virtual_method_call_p (call_fn))
    return;

  tree otr_type = obj_type_ref_class (call_fn);
  tree real_otr_type = otr_type;
  unsigned token = tree_to_uhwi (OBJ_TYPE_REF_TOKEN (call_fn));
  auto_vec<tree> worklist;
  hash_set<tree> visited;

  worklist.safe_push (OBJ_TYPE_REF_OBJECT (call_fn));

  do
    {
      tree value = worklist.pop ();
      tree type = NULL_TREE;

      visited.add (value);

      if (TREE_CODE (value) == ADDR_EXPR)
	{
	  HOST_WIDE_INT offset, size;
	  bool reverse;
	  tree base = get_ref_base_and_extent_hwi (TREE_OPERAND (value, 0),
						   &offset, &size, &reverse);
	  if (!base || (offset % BITS_PER_UNIT))
	    continue;

	  offset /= BITS_PER_UNIT;

	  if (TREE_CODE (base) == MEM_REF
	      && !integer_zerop (TREE_OPERAND (base, 1)))
	    {
	      if (!tree_fits_shwi_p (TREE_OPERAND (base, 1)))
		continue;

	      offset += tree_to_shwi (TREE_OPERAND (base, 1));
	    }

	  if (offset)
	    type = get_field_type (TREE_TYPE (base), offset);
	  else if (TREE_CODE (base) == MEM_REF)
	    {
	      value = TREE_OPERAND (base, 0);
	      if (!visited.add (value))
		worklist.safe_push (value);
	    }
	  else if (VAR_P (base))
	    type = TREE_TYPE (base);
	}
      else if (TREE_CODE (value) == SSA_NAME)
	{
	  gimple *stmt = SSA_NAME_DEF_STMT (value);

	  if (is_gimple_assign (stmt))
	    {
	      enum tree_code code = gimple_assign_rhs_code (stmt);
	      tree rhs1 = gimple_assign_rhs1 (stmt);

	      if (code == POINTER_PLUS_EXPR)
		{
		  tree rhs2 = gimple_assign_rhs2 (stmt);

		  if (!tree_fits_shwi_p (rhs2))
		    continue;

		  HOST_WIDE_INT offset = tree_to_shwi (rhs2);

		  if (offset)
		    type = get_field_type (TREE_TYPE (TREE_TYPE (rhs1)), offset);
		  else if (!visited.add (rhs1))
		    worklist.safe_push (rhs1);
		}
	      else if (code == COND_EXPR || code == MAX_EXPR || code == MIN_EXPR)
		{
		  for (unsigned i = 1; i < 3; i++)
		    {
		      tree opnd = gimple_op (stmt, gimple_num_ops (stmt) - i);

		      if (!visited.add (opnd))
			worklist.safe_push (opnd);
		    }
		}
	      else
		{
		  if (code == VIEW_CONVERT_EXPR)
		    rhs1 = TREE_OPERAND (rhs1, 0);
		  else if (gimple_assign_rhs_class (stmt) != GIMPLE_SINGLE_RHS
			   && !CONVERT_EXPR_CODE_P (code))
		    continue;

		  if (POINTER_TYPE_P (TREE_TYPE (rhs1)) && !visited.add (rhs1))
		    worklist.safe_push (rhs1);
		}
	    }
	  else if (auto phi = dyn_cast<gphi *> (stmt))
	    {
	      for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
		{
		  tree arg = gimple_phi_arg_def (phi, i);

		  if (!visited.add (arg))
		    worklist.safe_push (arg);
		}
	    }
	  else if (is_gimple_call (stmt))
	    {
	      tree fntype = gimple_call_fntype (stmt);

	      if (!fntype)
		continue;

	      type = TREE_TYPE (fntype);

	      if (!type || !POINTER_TYPE_P (type))
		continue;

	      type = TREE_TYPE (type);
	    }

	  if (!type)
	    continue;

	  while (TREE_CODE (type) == ARRAY_TYPE)
	    type = TREE_TYPE (type);

	  type = TYPE_MAIN_VARIANT (type);
	  if (TYPE_CANONICAL (type))
	    type = TYPE_CANONICAL (type);

	  if (!RECORD_OR_UNION_TYPE_P (type) || !TYPE_BINFO (type)
	      || !polymorphic_type_binfo_p (TYPE_BINFO (type)))
	    continue;

	  if (types_same_for_odr (real_otr_type, type))
	    continue;

	  for (tree inner_type = real_otr_type; ;)
	    {
	      tree field = TYPE_FIELDS (inner_type);

	      if (!field || !DECL_ARTIFICIAL (field))
		break;

	      inner_type = TREE_TYPE (field);

	      if (!RECORD_OR_UNION_TYPE_P (inner_type)
		  || !TYPE_BINFO (inner_type)
		  || !polymorphic_type_binfo_p (TYPE_BINFO (inner_type)))
		break;

	      if (types_same_for_odr (inner_type, type))
		{
		  if (gimple_get_virt_method_for_binfo (token,
							TYPE_BINFO (type)))
		    real_otr_type = type;
		  break;
		}
	    }
	}
    } while (!worklist.is_empty ());

  if (otr_type != real_otr_type)
    {
      tree fntype = TREE_TYPE (TREE_TYPE (call_fn));
      unsigned quals = TYPE_QUALS (TYPE_METHOD_BASETYPE (fntype));
      tree basetype = build_qualified_type (real_otr_type, quals);
      tree rettype = TREE_TYPE (fntype);
      tree argtypes = TREE_CHAIN (TYPE_ARG_TYPES (fntype));
      tree new_fntype = build_method_type_directly (basetype, rettype,
						    argtypes);

      TREE_TYPE (call_fn) = build_pointer_type (new_fntype);
      gimple_call_set_fntype (edge->call_stmt, new_fntype);

      ipa_polymorphic_call_context context (edge->caller->decl, call_fn,
					    edge->call_stmt);

      edge->indirect_info->otr_type = real_otr_type;
      edge->indirect_info->context = context;
    }
}

static void
ipa_devirt_fixup_vcall (void)
{
  cgraph_node *node;

  if (flag_safe_vcall || !flag_generate_lto)
    return;

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    {
      for (auto edge = node->indirect_calls; edge; edge = edge->next_callee)
	fixup_vcall (edge);
    }

  vcall_fixup_done = true;
  free_polymorphic_call_targets_hash ();
}

namespace {

const pass_data pass_data_ipa_devirt =
{
  IPA_PASS, /* type */
  "devirt", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_IPA_DEVIRT, /* tv_id */
  0, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  ( TODO_dump_symtab ), /* todo_flags_finish */
};

class pass_ipa_devirt : public ipa_opt_pass_d
{
public:
  pass_ipa_devirt (gcc::context *ctxt)
    : ipa_opt_pass_d (pass_data_ipa_devirt, ctxt,
		      ipa_devirt_fixup_vcall, /* generate_summary */
		      NULL, /* write_summary */
		      NULL, /* read_summary */
		      NULL, /* write_optimization_summary */
		      NULL, /* read_optimization_summary */
		      NULL, /* stmt_fixup */
		      0, /* function_transform_todo_flags_start */
		      NULL, /* function_transform */
		      NULL) /* variable_transform */
  {}

  /* opt_pass methods: */
  virtual bool gate (function *)
    {
      /* In LTO, always run the IPA passes and decide on function basis if the
	 pass is enabled.  */
      if (in_lto_p)
	return true;
      return (flag_devirtualize
	      && (flag_devirtualize_speculatively
		  || (warn_suggest_final_methods
		      || warn_suggest_final_types))
	      && optimize);
    }

  virtual unsigned int execute (function *) { return ipa_devirt (); }

}; // class pass_ipa_devirt

} // anon namespace

ipa_opt_pass_d *
make_pass_ipa_devirt (gcc::context *ctxt)
{
  return new pass_ipa_devirt (ctxt);
}

#define WRAP_NEW_OP     ((void *) 1)
#define WRAP_DELETE_OP  ((void *) 2)
#define WRAP_THROW_OP   ((void *) 3)

static inline bool
node_is_wrapper_p (cgraph_node *node)
{
  if (node->aux == WRAP_NEW_OP
      || node->aux == WRAP_DELETE_OP
      || node->aux == WRAP_THROW_OP)
    return true;

  return false;
}

static inline bool
call_has_name_p (gimple *stmt, const char *name)
{
  tree decl = gimple_call_fndecl (stmt);

  return decl && id_equal (DECL_NAME (decl), name);
}

static bool
decl_is_operator_new_p (tree decl)
{
  if (DECL_IS_OPERATOR_NEW_P (decl))
    return true;

  cgraph_node *node = cgraph_node::get (decl);

  if (!node || !node->former_clone_of)
    return false;

 return DECL_IS_OPERATOR_NEW_P (node->former_clone_of);
}

static bool
decl_is_operator_delete_p (tree decl)
{
  if (DECL_IS_OPERATOR_DELETE_P (decl))
    return true;

  cgraph_node *node = cgraph_node::get (decl);

  if (!node || !node->former_clone_of)
    return false;

  return DECL_IS_OPERATOR_DELETE_P (node->former_clone_of);
}

/* Return the first call statement after function entry. If STRICT_P is NULL,
   the call should be the first executable statement at function entry.
   Otherwise, whether requirement was met is kept in *STRICT_P.  */

static gimple *
get_first_entry_call (bool *strict_p = NULL)
{
  tree default_vop = ssa_default_def (cfun, gimple_vop (cfun));
  imm_use_iterator use_iter;
  gimple *stmt;
  gimple *call_stmt = NULL;

  if (!default_vop)
    return NULL;

  if (strict_p)
    *strict_p = true;

  FOR_EACH_IMM_USE_STMT (stmt, use_iter, default_vop)
    {
      if (is_gimple_call (stmt))
	{
	  basic_block bb = gimple_bb (stmt);

	  if (call_stmt)
	    return NULL;

	  call_stmt = stmt;

	  if (single_pred_p (bb)
	      && single_pred (bb) == ENTRY_BLOCK_PTR_FOR_FN (cfun))
	    continue;
	}
      else if (is_gimple_debug (stmt))
	continue;

      if (!strict_p)
	return NULL;

      *strict_p = false;
    }

  return call_stmt;
}

/* Return true if STMT is a __cxa_allocate_exception, and a paired __cxa_throw
   should exist in same basic block. Between these two calls there are
   statements to construct an exception object.

       exception_object = __cxa_allocate_exception (size);
       ...
       exception_object->ctor();
       ...
       __cxa_throw (exception_object, &exception::rtti, &exception::dtor);

   As a whole, all these statements are mapped to one throw operation at the
   source level.  */

static bool
stmt_starts_throw_operation_p (gimple *stmt, gimple **throw_stmt_ptr = NULL)
{
  if (gimple_call_num_args (stmt) != 1)
    return false;

  basic_block bb = gimple_bb (stmt);
  gimple *throw_stmt = last_stmt (bb);

  if (!is_gimple_call (throw_stmt)
      || !(gimple_call_flags (throw_stmt) & ECF_NORETURN)
      || !call_has_name_p (throw_stmt, "__cxa_throw")
      || !call_has_name_p (stmt, "__cxa_allocate_exception"))
    return false;

  tree alloc_obj = gimple_call_lhs (stmt);
  tree alloc_size = gimple_call_arg (stmt, 0);

  if (!alloc_obj || TREE_CODE (alloc_obj) != SSA_NAME
      || TREE_CODE (alloc_size) != INTEGER_CST)
    return false;

  if (gimple_call_num_args (throw_stmt) != 3)
    return false;

  if (alloc_obj != gimple_call_arg (throw_stmt, 0))
    return false;

  tree throw_rtti = gimple_call_arg (throw_stmt, 1);
  tree throw_dtor = gimple_call_arg (throw_stmt, 2);

  if (TREE_CODE (throw_rtti) != ADDR_EXPR
      || TREE_CODE (throw_dtor) != ADDR_EXPR)
    return false;

  throw_rtti = TREE_OPERAND (throw_rtti, 0);
  throw_dtor = TREE_OPERAND (throw_dtor, 0);

  if (!VAR_P (throw_rtti) || TREE_CODE (throw_dtor) != FUNCTION_DECL)
    return false;

  if (!TREE_STATIC (throw_rtti) && !DECL_EXTERNAL (throw_rtti))
    return false;

  if (TREE_CODE (TREE_TYPE (throw_dtor)) != METHOD_TYPE)
    return false;

  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);


  /* Check statements of constructing object to be thrown, and we only allow
     memory stores to the object with constant value, which means object to
     be thrown are invariant each time.  */
  for (gsi_next (&gsi); ; gsi_next (&gsi))
    {
      gimple *ctor_stmt = gsi_stmt (gsi);

      if (ctor_stmt == throw_stmt)
	break;

      if (!gimple_vdef (ctor_stmt))
	continue;

      if (!gimple_assign_single_p (ctor_stmt))
	return false;

      tree lhs = gimple_assign_lhs (ctor_stmt);
      tree rhs = gimple_assign_rhs1 (ctor_stmt);

      if (!TREE_CLOBBER_P (rhs))
	{
	  if (!is_gimple_ip_invariant (rhs))
	    return false;

	  if (gimple_has_volatile_ops (ctor_stmt))
	    return false;
	}

      poly_int64 bitpos, bitsize, bitmaxsize;
      bool reverse;
      tree memref = get_ref_base_and_extent (lhs, &bitpos, &bitsize,
					     &bitmaxsize, &reverse);

      if (!memref || TREE_CODE (memref) != MEM_REF
	  || TREE_OPERAND (memref, 0) != alloc_obj)
	return false;

      if (!known_size_p (bitmaxsize) || !known_eq (bitsize, bitmaxsize))
	return false;

      poly_offset_int offset
	= wi::to_poly_offset (TREE_OPERAND (memref, 1)) << LOG2_BITS_PER_UNIT;
      poly_int64 alloc_bits
	= tree_to_poly_int64 (alloc_size) << LOG2_BITS_PER_UNIT;

      /* Ensure memory store is inside the object to be thrown.  */
      if (!known_subrange_p (offset + bitpos, bitsize, 0, alloc_bits))
	return false;
    }

  if (throw_stmt_ptr)
    *throw_stmt_ptr = throw_stmt;

  return true;
}

/* Return true if current function is a wrapper over 'new' operator.  */

static bool
function_wraps_new_operator ()
{
  gimple *stmt = get_first_entry_call ();

  if (!stmt)
    return false;

  tree fndecl = gimple_call_fndecl (stmt);

  /* The first statement should be a call to 'new' operator.  */
  if (!fndecl || !decl_is_operator_new_p (fndecl))
    return false;

  tree param = DECL_ARGUMENTS (cfun->decl);

  if (!param || !DECL_CHAIN (param))
    return false;

  /* The first parameter is this pointer, and the second is size to
     be allocated.  */
  param = DECL_CHAIN (param);

  if (!INTEGRAL_TYPE_P (TREE_TYPE (param)))
    return false;

  if (gimple_call_num_args (stmt) != 1
      || gimple_call_arg (stmt, 0) != ssa_default_def (cfun, param))
    return false;

  tree alloc_addr = gimple_call_lhs (stmt);

  if (TREE_CODE (alloc_addr) != SSA_NAME)
    return false;

  use_operand_p use;
  gimple *use_stmt;

  if (!single_imm_use (alloc_addr, &use, &use_stmt))
    return false;

  greturn *ret = dyn_cast <greturn *> (use_stmt);

  if (!ret || gimple_return_retval (ret) != alloc_addr)
    return false;

  if (gimple_vuse (ret) != gimple_vdef (stmt))
    return false;

  basic_block bb = gimple_bb (stmt);
  basic_block ret_bb = gimple_bb (ret);

  /* If return and 'new' statements are in same basic block, there is no
     exception handling code.  */
  if (bb == ret_bb)
    return true;

  if (single_succ_p (bb))
    return single_succ (bb) == ret_bb;

  if (EDGE_COUNT (bb->succs) != 2)
    return false;

  /* There are two successor blocks, one is normal return, and the other
     directs to exception handling code.  */
  basic_block eh_bb = EDGE_SUCC (bb, 0)->dest;

  if (eh_bb == ret_bb)
    eh_bb = EDGE_SUCC (bb, 1)->dest;

  imm_use_iterator use_iter;
  gimple *catch_stmt = NULL;
  gimple *catch_end_stmt;
  gimple *throw_stmt;

  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, gimple_vdef (stmt))
    {
      if (!is_gimple_call (use_stmt))
	continue;

      if (call_has_name_p (use_stmt, "__cxa_begin_catch"))
	{
	  catch_stmt = use_stmt;
	  break;
	}
    }

  if (!catch_stmt || gimple_call_num_args (catch_stmt) != 1)
    return false;

  tree eh_pointer = gimple_call_arg (catch_stmt, 0);

  if (TREE_CODE (eh_pointer) != SSA_NAME)
    return false;

  gimple *eh_pointer_stmt = SSA_NAME_DEF_STMT (eh_pointer);

  if (!gimple_call_builtin_p (eh_pointer_stmt, BUILT_IN_EH_POINTER))
    return false;

  basic_block catch_bb = gimple_bb (catch_stmt);

  for (basic_block temp_bb = eh_bb; temp_bb != catch_bb; )
    {
      if (!single_succ_p (temp_bb))
	return false;

      temp_bb = single_succ (temp_bb);

      if (!single_pred_p (temp_bb))
	return false;
    }

  if (!single_imm_use (gimple_vdef (catch_stmt), &use, &throw_stmt)
     || !is_gimple_call (throw_stmt))
    return false;

  /* Unconditionally rethrow an exception or throw a new exception.  */
  if (call_has_name_p (throw_stmt, "__cxa_rethrow"))
    {
      if (!(gimple_call_flags (throw_stmt) & ECF_NORETURN)
	  || gimple_call_num_args (throw_stmt))
	return false;
    }
  else if (!stmt_starts_throw_operation_p (throw_stmt, &throw_stmt))
    return false;

  if (!single_imm_use (gimple_vdef (throw_stmt), &use, &catch_end_stmt)
      || !is_gimple_call (catch_end_stmt))
    return false;

  if (!call_has_name_p (catch_end_stmt, "__cxa_end_catch"))
    return false;

  basic_block catch_end_bb = gimple_bb (catch_end_stmt);

  if (!single_pred_p (catch_end_bb)
      || single_pred (catch_end_bb) != catch_bb)
    return false;

  return true;
}

/* Return true if current function is a wrapper over 'delete' operator, without
   or with a NULL pointer check as:

  ;;   basic block 1
    if (p_1(D) != 0B)
      goto <bb 2>;
    else
      goto <bb 3>;

  ;;   basic block 2
    # .MEM_3 = VDEF <.MEM_2(D)>
    operator delete [] (p_1(D));

  ;;   basic block 3
    # .MEM_4 = PHI <.MEM_2(D)(1), .MEM_3(2)>
    # VUSE <.MEM_4>
    return;
*/

static bool
function_wraps_delete_operator ()
{
  bool simple;
  gimple *del_stmt = get_first_entry_call (&simple);

  if (!del_stmt)
    return false;

  tree fndecl = gimple_call_fndecl (del_stmt);

  /* There is only one call to 'delete' operator.  */
  if (!fndecl || !decl_is_operator_delete_p (fndecl))
    return false;

  tree param = DECL_ARGUMENTS (cfun->decl);

  if (!param || !DECL_CHAIN (param))
    return false;

  /* The first parameter is this pointer, and the second is memory pointer to
     be deleted.  */
  param = ssa_default_def (cfun, DECL_CHAIN (param));
  if (!param || !POINTER_TYPE_P (TREE_TYPE (param)))
    return false;

  /* Now only non-sized 'delete' operator is handled, which has one pointer
     parameter.

     TODO: support other variants, such as delete (void *ptr, size_t size).  */
  if (gimple_call_num_args (del_stmt) != 1
      || gimple_call_arg (del_stmt, 0) != param)
    return false;

  use_operand_p use;
  gimple *use_stmt;
  greturn *ret;
  tree ret_vuse = gimple_vdef (del_stmt);

  if (!simple)
    {
      basic_block del_bb = gimple_bb (del_stmt);

      if (!single_pred_p (del_bb) || !single_succ_p (del_bb))
	return false;

      edge cmp_e = single_pred_edge (del_bb);
      basic_block cmp_bb = cmp_e->src;

      if (!single_pred_p (cmp_bb)
	  || single_pred (cmp_bb) != ENTRY_BLOCK_PTR_FOR_FN (cfun))
	return false;

      gimple *cmp_stmt = last_stmt (cmp_bb);

      if (!cmp_stmt || gimple_code (cmp_stmt) != GIMPLE_COND)
	return false;

      tree cmp_val = NULL_TREE;

      if (gimple_cond_lhs (cmp_stmt) == param)
	cmp_val = gimple_cond_rhs (cmp_stmt);
      else if (gimple_cond_rhs (cmp_stmt) == param)
	cmp_val = gimple_cond_lhs (cmp_stmt);

      if (!cmp_val || !integer_zerop (cmp_val))
	return false;

      if (gimple_cond_code (cmp_stmt) == NE_EXPR)
	{
	  if (cmp_e->flags & EDGE_FALSE_VALUE)
	    return false;
	}
      else if (gimple_cond_code (cmp_stmt) == EQ_EXPR)
	{
	  if (cmp_e->flags & EDGE_TRUE_VALUE)
	    return false;
	}
      else
	return false;

      basic_block skip_bb;

      if (EDGE_SUCC (cmp_bb, 0) == cmp_e)
	skip_bb = EDGE_SUCC (cmp_bb, 1)->dest;
      else
	skip_bb = EDGE_SUCC (cmp_bb, 0)->dest;

      if (skip_bb == single_succ (del_bb))
	{
	  if (!single_imm_use (gimple_vdef (del_stmt), &use, &use_stmt)
	      || gimple_code (use_stmt) != GIMPLE_PHI)
	    return false;

	  ret_vuse = gimple_phi_result (use_stmt);
	}
      else if ((ret = safe_dyn_cast <greturn *> (last_stmt (skip_bb))))
	{
	  tree retval = gimple_return_retval (ret);

	  /* Only void function or function with constant return value is
	     allowed.  */
	  if (retval && !is_gimple_ip_invariant (retval))
	    return false;

	  if (gimple_vuse (ret) != gimple_vuse (del_stmt))
	    return false;
	}
      else
	return false;
    }

  if (!single_imm_use (ret_vuse, &use, &use_stmt)
      || gimple_bb (use_stmt) != gimple_bb (SSA_NAME_DEF_STMT (ret_vuse)))
    return false;

  if (!(ret = dyn_cast <greturn *> (use_stmt)))
    return false;

  tree retval = gimple_return_retval (ret);

  /* Only void function or function with constant return value is allowed.  */
  if (retval && !is_gimple_ip_invariant (retval))
    return false;

  return true;
}

/* Return true if current function always throw an invariant exception.  */

static bool
function_only_throws_exception ()
{
  gimple *stmt = get_first_entry_call ();

  if (!stmt || !stmt_starts_throw_operation_p (stmt))
    return false;

  return true;
}

/* Function type map for 'new'/'delete' vcall.  */
static hash_map<tree, tree> *fntype_map[2];

static bool
annotate_vcall_wrapper (gimple *call_stmt, auto_vec<cgraph_node *> &targets)
{
  bool is_new = false;
  bool is_delete = false;
  cgraph_node *target;
  unsigned i;

  FOR_EACH_VEC_ELT (targets, i, target)
    {
      if (!target->aux)
	return false;

      if (target->aux == WRAP_NEW_OP)
	is_new = true;
      else if (target->aux == WRAP_DELETE_OP)
	is_delete = true;
      else if (target->aux != WRAP_THROW_OP)
	return false;
    }

  if (is_new == is_delete)
   return false;

  if (!fntype_map[is_new])
    fntype_map[is_new] = new hash_map <tree, tree> ();

  bool existed_p;
  tree orig_fntype = gimple_call_fntype (call_stmt);
  tree &fntype = fntype_map[is_new]->get_or_insert (orig_fntype, &existed_p);
  const char *fntype_attr = is_new ? "cxx_new" : "cxx_delete";
  if (!existed_p)
    {
      fntype = build_distinct_type_copy (orig_fntype);
      TYPE_ATTRIBUTES (fntype) = tree_cons (get_identifier (fntype_attr),
					    NULL_TREE,
					    TYPE_ATTRIBUTES (fntype));
    }

  gimple_call_set_fntype (as_a<gcall *> (call_stmt), fntype);

  if (dump_file)
    {
      fprintf (dump_file, "\n  Mark the call as %s: ", fntype_attr);
      print_gimple_stmt (dump_file, call_stmt, 0);
    }

  return true;
}

static inline bool
contains_value_p (vec<tree> &values, tree value)
{
  unsigned i;
  tree value_in;

  FOR_EACH_VEC_ELT (values, i, value_in)
    if (operand_equal_p (value, value_in))
      return true;

  return false;
}

static auto_vec<tree> *
get_return_constant_values ()
{
  tree ret_type = TREE_TYPE (TREE_TYPE (cfun->decl));

  /* It is meaningless to optimize vcall with bool return type, which only has
     two values.  */
  if (TREE_CODE (ret_type) == BOOLEAN_TYPE)
    return NULL;

  if (!INTEGRAL_TYPE_P (ret_type) && !POINTER_TYPE_P (ret_type))
    return NULL;

  edge e;
  edge_iterator ei;
  auto_vec<tree> values;

  FOR_EACH_EDGE (e, ei, EXIT_BLOCK_PTR_FOR_FN (cfun)->preds)
    {
      greturn *ret = safe_dyn_cast<greturn *> (last_stmt (e->src));

      if (!ret)
	return NULL;

      tree retval = gimple_return_retval (ret);

      if (!retval || !is_gimple_ip_invariant (retval))
	return NULL;

      if (!contains_value_p (values, retval))
	values.safe_push (retval);
    }

  if (values.is_empty ())
    return NULL;

  auto_vec<tree> *values_ptr = new auto_vec<tree> ();

  values_ptr->safe_splice (values);
  return values_ptr;
}

static cgraph_node *
match_node_by_retval (auto_vec<cgraph_node *> &targets, tree value)
{
  unsigned i;
  cgraph_node *target;
  cgraph_node *node = NULL;

  FOR_EACH_VEC_ELT (targets, i, target)
    {
      cgraph_node *alias_target = target->ultimate_alias_target ();
      vec<tree> &values = *(auto_vec<tree> *) alias_target->aux;

      if (contains_value_p (values, value))
	{
	  if (node || values.length () > 1)
	    return NULL;

	  node = target;
	}
    }

  return node;
}

static tree
build_vtable_addr_expr (tree vtable, unsigned HOST_WIDE_INT offset)
{
  tree type = TREE_TYPE (vtable);

  gcc_checking_assert (TREE_CODE (type) == ARRAY_TYPE);
  gcc_checking_assert (DECL_VIRTUAL_P (vtable) && VAR_P (vtable));

  vtable = build1 (ADDR_EXPR, build_pointer_type (type), vtable);
  vtable = build2 (MEM_REF, type, vtable,
		   build_int_cst (ptr_type_node, offset));

  return build1 (ADDR_EXPR, build_pointer_type (type), vtable);
}

static tree
get_single_vtable (cgraph_node *node, tree otr_expr)
{
  tree vtable = NULL_TREE;
  unsigned HOST_WIDE_INT offset = 0;
  unsigned HOST_WIDE_INT token = tree_to_uhwi (OBJ_TYPE_REF_TOKEN (otr_expr));
  ipa_ref *ref;

  gcc_checking_assert (DECL_VIRTUAL_P (node->decl));

  for (unsigned i = 0; node->iterate_referring (i, ref); i++)
    {
      symtab_node *referring = ref->referring;

      /* Alias function may belong to a sole class that has no
	 inheritance relation with the class to checked, but we
	 also ignore that.  */
      if (ref->use == IPA_REF_ALIAS)
	return NULL_TREE;

      if (ref->use == IPA_REF_ADDR && VAR_P (referring->decl)
	  && DECL_VIRTUAL_P (referring->decl))
	{
	  if (vtable)
	    return NULL_TREE;

	  tree init = ctor_for_folding (referring->decl);
	  tree val;
	  unsigned j;

	  if (!init || init == error_mark_node)
	    return NULL_TREE;

	  FOR_EACH_CONSTRUCTOR_VALUE (CONSTRUCTOR_ELTS (init), j, val)
	    {
	      if (TREE_CODE (val) == ADDR_EXPR
		  && TREE_OPERAND (val, 0) == node->decl)
		break;
	    }

	  /* In theory, we should always find a slot in vtable for the
	     function.  But probably user can construct an ill-form
	     program to violate this?  */
	  if (j >= CONSTRUCTOR_NELTS (init) || j < token)
	    return NULL_TREE;

	  vtable = referring->decl;
	  offset = (j - token) * POINTER_SIZE_UNITS;
	}
    }

  gcc_assert (vtable);

  return build_vtable_addr_expr (vtable, offset);
}

static tree
get_vtable_from_otr_expr (tree otr_expr)
{
  tree fn_ptr = OBJ_TYPE_REF_EXPR (otr_expr);
  tree fn_token = OBJ_TYPE_REF_TOKEN (otr_expr);
  gimple *fn_stmt = SSA_NAME_DEF_STMT (fn_ptr);

  if (!gimple_assign_load_p (fn_stmt))
    return NULL_TREE;

  tree memref = gimple_assign_rhs1 (fn_stmt);

  if (TREE_CODE (memref) != MEM_REF)
    return NULL_TREE;

  tree offset = TREE_OPERAND (memref, 1);

  if (!tree_fits_uhwi_p (offset))
    return NULL_TREE;

  if (tree_to_uhwi (offset) != (tree_to_uhwi (fn_token) * POINTER_SIZE_UNITS))
    return NULL_TREE;

  return TREE_OPERAND (memref, 0);
}

static void
copy_arg_for_phi_nodes (edge_def *old_e, edge_def *new_e)
{
  for (gphi_iterator gsi = gsi_start_phis (old_e->dest); !gsi_end_p (gsi);
       gsi_next (&gsi))
   {
      gphi *phi = gsi.phi ();
      tree def = PHI_ARG_DEF_FROM_EDGE (phi, old_e);

      add_phi_arg (phi, unshare_expr (def), new_e,
		   gimple_phi_arg_location_from_edge (phi, old_e));
   }
}

static bool
devirtualize_call_for_condition (gimple *call_stmt,
				 auto_vec<cgraph_node *> &targets,
				 bool cmp_vtable)
{
  tree call_lhs = gimple_call_lhs (call_stmt);

  /* A const/pure virtual call without lhs has no side effect, could be
     removed. */
  if (!call_lhs)
    {
      if (dump_file)
	{
	  fprintf (dump_file, "\n  Remove dead call:\n  * ");
	  print_gimple_stmt (dump_file, call_stmt, 0);
	}
      return true;
    }

  if (TREE_CODE (call_lhs) != SSA_NAME)
    return false;

  unsigned i;
  gimple *use_stmt;
  imm_use_iterator use_iter;
  cgraph_node *target;
  auto_vec<cgraph_node *> final_targets;

  FOR_EACH_VEC_ELT (targets, i, target)
    {
      if (!target->aux || node_is_wrapper_p (target))
	return false;
    }

  /* TODO: return value of call might be converted to other type, for example,
     char type index of switch statement will be promoted to int type.  */
  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, call_lhs)
    {
      if (gimple_code (use_stmt) == GIMPLE_COND)
	{
	  enum tree_code cmp_code = gimple_cond_code (use_stmt);

	  if (cmp_code != NE_EXPR && cmp_code != EQ_EXPR)
	    return false;

	  tree cmp_expr = gimple_cond_rhs (use_stmt);

	  if (gimple_cond_lhs (use_stmt) == call_lhs)
	    cmp_expr = gimple_cond_rhs (use_stmt);
	  else if (gimple_cond_rhs (use_stmt) == call_lhs)
	    cmp_expr = gimple_cond_lhs (use_stmt);
	  else
	    return false;

	  if (!is_gimple_ip_invariant (cmp_expr))
	    return false;

	  cgraph_node *call_node = match_node_by_retval (targets, cmp_expr);

	  if (!call_node)
	    return false;

	  final_targets.safe_push (call_node);
	}
      else if (gimple_code (use_stmt) == GIMPLE_SWITCH)
	{
	  gswitch *switch_stmt = as_a <gswitch *> (use_stmt);

	  if (gimple_switch_index (switch_stmt) != call_lhs)
	    return false;

	  /* TODO: devirtualization will expand switch to if-statements,
	     which might break some optimizations for certian switch patterns,
	     such as jump table generation.  */
	  for (i = 1; i < gimple_switch_num_labels (switch_stmt); ++i)
	    {
	      tree cl = gimple_switch_label (switch_stmt, i);
	      tree min = CASE_LOW (cl);
	      tree max = CASE_HIGH (cl);

	      /* TODO: same target with multiple continuous cases.  */
	      if (max)
		return false;

	      if (TREE_TYPE (min) != TREE_TYPE (call_lhs))
		min = wide_int_to_tree (TREE_TYPE (call_lhs),
					wi::to_wide (min));

	      cgraph_node *call_node = match_node_by_retval (targets, min);

	      if (!call_node)
		return false;

	      final_targets.safe_push (call_node);
	    }
	}
      else if (!is_gimple_debug (use_stmt))
	return false;
    }

  auto_vec<tree> addr_consts;
  tree call_fn = gimple_call_fn (call_stmt);
  tree addr_expr;
  unsigned target_pos = 0;

  if (cmp_vtable)
    {
      FOR_EACH_VEC_ELT (final_targets, i, target)
	{
	  tree vtable = get_single_vtable (target, call_fn);

	  if (!vtable)
	    {
	      cmp_vtable = false;
	      addr_consts.truncate (0);
	      break;
	    }

	  addr_consts.safe_push (vtable);
	}

      if (cmp_vtable
	  && !(addr_expr = get_vtable_from_otr_expr (call_fn)))
	{
	  cmp_vtable = false;
	  addr_consts.truncate (0);
	}
    }

  if (!cmp_vtable)
    {
      FOR_EACH_VEC_ELT (final_targets, i, target)
	{
	  tree target_addr
		= build1 (ADDR_EXPR,
			  build_pointer_type (TREE_TYPE (target->decl)),
			  target->decl);

	  addr_consts.safe_push (target_addr);
	}

      addr_expr = make_temp_ssa_name (TREE_TYPE (call_fn), NULL, "vcall_addr");
      gimple *load_stmt = gimple_build_assign (addr_expr,
					       unshare_expr (call_fn));

      gimple_stmt_iterator gsi = gsi_for_stmt (call_stmt);
      gsi_insert_before (&gsi, load_stmt, GSI_SAME_STMT);
    }

  if (dump_file)
    {
      tree fn_ptr = OBJ_TYPE_REF_EXPR (call_fn);
      gimple *fn_stmt = SSA_NAME_DEF_STMT (fn_ptr);

      fprintf (dump_file, "\n  Rewrite used-by-condition call:\n  * ");
      print_gimple_stmt (dump_file, fn_stmt, 0);
      fprintf (dump_file, "  * ");
      print_gimple_stmt (dump_file, call_stmt, 0);
    }

  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, call_lhs)
    {
      if (gimple_code (use_stmt) == GIMPLE_COND)
	{
	  gcond *cond_stmt = as_a <gcond *> (use_stmt);

	  if (dump_file)
	    {
	      fprintf (dump_file, "  condition ");
	      print_gimple_expr (dump_file, cond_stmt, 0);
	    }

	  gimple_cond_set_lhs (cond_stmt, addr_expr);
	  gimple_cond_set_rhs (cond_stmt, addr_consts [target_pos++]);
	  update_stmt (use_stmt);

	  if (dump_file)
	    {
	      cgraph_node *target = final_targets[target_pos - 1];

	      fprintf (dump_file, "  ->  ");
	      print_gimple_expr (dump_file, cond_stmt, 0);
	      if (cmp_vtable)
		fprintf (dump_file, " (vtable of ");
	      else
		fprintf (dump_file, "/%d (", target->order);
	      print_generic_expr (dump_file, DECL_CONTEXT (target->decl));
	      fprintf (dump_file, ")\n");
	    }
	}
      else if (gimple_code (use_stmt) == GIMPLE_SWITCH)
	{
	  gimple_stmt_iterator gsi = gsi_for_stmt (use_stmt);
	  edge_def *link_e = split_block (gimple_bb (use_stmt),
				(gsi_prev_nondebug (&gsi), gsi_stmt (gsi)));
	  profile_probability total_prob = profile_probability::always ();
	  gswitch *switch_stmt = as_a <gswitch *> (use_stmt);

	  for (i = 1; i < gimple_switch_num_labels (switch_stmt); ++i)
	    {
	      gcond *cmp_stmt = gimple_build_cond (EQ_EXPR, addr_expr,
						   addr_consts[target_pos++],
						   NULL_TREE, NULL_TREE);
	      basic_block cmp_bb = split_edge (link_e);

	      link_e = single_succ_edge (cmp_bb);
	      gsi = gsi_start_bb (cmp_bb);
	      gsi_insert_after (&gsi, cmp_stmt, GSI_NEW_STMT);

	      edge_def *case_e = gimple_switch_edge (cfun, switch_stmt, i);
	      edge_def *true_e = make_edge (cmp_bb, case_e->dest,
					    EDGE_TRUE_VALUE);

	      copy_arg_for_phi_nodes (case_e, true_e);
	      true_e->probability = case_e->probability / total_prob;
	      link_e->flags &= ~EDGE_FALLTHRU;
	      link_e->flags |= EDGE_FALSE_VALUE;
	      link_e->probability = true_e->probability.invert ();
	      total_prob -= case_e->probability;

	      if (dump_file)
		{
		  tree cl = gimple_switch_label (switch_stmt, i);
		  cgraph_node *target = final_targets[target_pos - 1];

		  fprintf (dump_file, "  switch(");
		  print_generic_expr (dump_file, call_lhs);
		  fprintf (dump_file, ") case ");
		  print_generic_expr (dump_file, CASE_LOW (cl));
		  fprintf (dump_file, ":  ->  ");
		  print_gimple_expr (dump_file, cmp_stmt, 0);
		  if (cmp_vtable)
		    fprintf (dump_file, " (vtable of ");
		  else
		    fprintf (dump_file, "/%d (", target->order);
		  print_generic_expr (dump_file, DECL_CONTEXT (target->decl));
		  fprintf (dump_file, ")\n");
		}
	    }

	  edge_def *default_e = gimple_switch_default_edge (cfun, switch_stmt);

	  redirect_edge_succ (link_e, default_e->dest);
	  copy_arg_for_phi_nodes (default_e, link_e);
	  delete_basic_block (gimple_bb (use_stmt));
	}
      else
	{
	  gimple_stmt_iterator gsi = gsi_for_stmt (use_stmt);

	  gcc_checking_assert (is_gimple_debug (use_stmt));
	  gsi_remove (&gsi, true);
	}
    }

  return true;
}

static bool
post_devirtualize_vcall (cgraph_edge *edge)
{
  unsigned i;
  void *cache_token;
  bool complete;
  int call_flags = -1;
  gcall *call_stmt = edge->call_stmt;
  cgraph_node *target;
  auto_vec<cgraph_node *> targets;
  vec<cgraph_node *> cache_targets
	= possible_polymorphic_call_targets (edge, &complete, &cache_token);

  if (!complete || cache_targets.is_empty ())
    return false;

  FOR_EACH_VEC_ELT (cache_targets, i, target)
    {
      if (is_cxa_pure_virtual_p (target->decl))
	return false;

      if (target->get_availability () <= AVAIL_INTERPOSABLE)
	return false;

      target = target->ultimate_alias_target ();

      if (!targets.contains (target))
	{
	  int decl_flags = flags_from_decl_or_type (target->decl);

	  /* We enforce a stricker check on const/pure indirect function
	     since there is no more bits in gcall to represent
	     LOOPING_CONST_OR_PURE.  */
	  if (decl_flags & ECF_LOOPING_CONST_OR_PURE)
	    decl_flags &= ~(ECF_CONST | ECF_PURE);

	  call_flags &= decl_flags;
	  targets.safe_push (target);
	}
    }

  if (call_flags & (ECF_PURE | ECF_CONST))
    {
      bool cmp_vtable = targets.length () == cache_targets.length ();

      if (devirtualize_call_for_condition (call_stmt, targets, cmp_vtable))
	{
	  gimple_stmt_iterator gsi = gsi_for_stmt (call_stmt);
	  basic_block call_bb = gimple_bb (call_stmt);

	  unlink_stmt_vdef (call_stmt);
	  /* Record basic block before gsi_remove, since it will be cleared.  */
	  if (gsi_remove (&gsi, true))
	    gimple_purge_dead_eh_edges (call_bb);
	  release_defs (call_stmt);
	  cgraph_edge::remove (edge);
	  return true;
	}
    }
  else
    annotate_vcall_wrapper (call_stmt, targets);

  bool changed = false;

  if (call_flags & ECF_NOTHROW)
    {
      gimple_call_set_nothrow (call_stmt, true);

      if (maybe_clean_eh_stmt (call_stmt))
	changed = gimple_purge_dead_eh_edges (gimple_bb (call_stmt));
    }

  /* An indirect function is const when its function address is not changed,
     it behavior is just like a pure function.  */
  if (call_flags & ECF_CONST)
    gimple_call_set_const (call_stmt, true);
  else if (call_flags & ECF_PURE)
    gimple_call_set_pure (call_stmt, true);

  if (call_flags & (ECF_CONST | ECF_PURE))
    update_stmt (call_stmt);

  return changed;
}

static void
analyze_virtual_function (cgraph_node *node)
{
  cfun_context context (node);

  if (function_wraps_new_operator ())
    node->aux = WRAP_NEW_OP;
  else if (function_wraps_delete_operator ())
    node->aux = WRAP_DELETE_OP;
  else if (function_only_throws_exception ())
    node->aux = WRAP_THROW_OP;
  else if (flags_from_decl_or_type (node->decl) & (ECF_PURE | ECF_CONST))
    node->aux = get_return_constant_values ();
}

static hash_map<tree, odr_type> *typeinfo_map;

static void
init_typeinfo_map ()
{
  typeinfo_map = new hash_map<tree, odr_type> ();

  gcc_assert (odr_types_ptr);

  for (unsigned i = 0; i < odr_types.length (); i++)
    {
      odr_type type = odr_types[i];

      if (!type || !RECORD_OR_UNION_TYPE_P (type->type))
	continue;

      tree vtbl = get_type_vtable (type->type);

      if (!vtbl)
	continue;

      if (tree typeinfo = extract_typeinfo_in_vtable (vtbl))
	typeinfo_map->put (typeinfo, type);
    }
}

static odr_type
class_for_typeinfo (tree typeinfo)
{
  if (!typeinfo_map)
    init_typeinfo_map ();

  odr_type *type = typeinfo_map->get (typeinfo);

  if (!type)
    return NULL;
  return *type;
}

/* Rewrite an invalid dynamic_cast to a NULL pointer assignment.  */

static void
nullify_dynamic_cast (cgraph_edge *edge)
{
  gimple *call_stmt = edge->call_stmt;
  gimple_stmt_iterator gsi = gsi_for_stmt (call_stmt);
  tree dst_ptr = gimple_call_lhs (call_stmt);
  gimple *new_stmt
	= gimple_build_assign (dst_ptr, build_zero_cst (TREE_TYPE (dst_ptr)));

  gsi_insert_before (&gsi, new_stmt, GSI_SAME_STMT);
  unlink_stmt_vdef (call_stmt);
  gsi_remove (&gsi, true);
  cgraph_edge::remove (edge);
}

static bool
compare_null_stmt_p (gcond *stmt, tree name, edge &e_good, edge &e_null)
{
  if (gimple_code (stmt) != GIMPLE_COND)
    return false;

  tree opnd0 = gimple_cond_lhs (stmt);
  tree opnd1 = gimple_cond_rhs (stmt);

  if ((opnd0 != name || !integer_zerop (opnd1))
      && (opnd1 != name || !integer_zerop (opnd0)))
    return false;

  enum tree_code code = gimple_cond_code (stmt);

  if (code != EQ_EXPR && code != NE_EXPR)
    return false;

  basic_block bb = gimple_bb (stmt);

  e_good = EDGE_SUCC (bb, 0);
  e_null = EDGE_SUCC (bb, 1);

  if ((code == EQ_EXPR) ^ !(e_good->flags & EDGE_TRUE_VALUE))
    std::swap (e_good, e_null);

  return true;
}

static bool
optimize_dynamic_cast (cgraph_edge *edge)
{
  gcall *call_stmt = edge->call_stmt;

  if (gimple_call_num_args (call_stmt) != 4)
    return false;

  tree dst_ti = gimple_call_arg (call_stmt, 2);

  if (TREE_CODE (dst_ti) != ADDR_EXPR)
    return false;

  dst_ti = TREE_OPERAND (dst_ti, 0);

  if (!VAR_P (dst_ti))
    return false;

  tree src_ptr = gimple_call_arg (call_stmt, 0);
  tree dst_ptr = gimple_call_lhs (call_stmt);
  tree hint = gimple_call_arg (call_stmt, 3);

  if (!dst_ptr)
    return false;

  basic_block call_bb = gimple_bb (call_stmt);

  if (last_stmt (call_bb) == call_stmt && !single_succ_p (call_bb))
    return false;

  /* TODO: Result may be saved to a variable.  */
  if (TREE_CODE (dst_ptr) != SSA_NAME)
    return false;

  if (TREE_CODE (hint) != INTEGER_CST || int_cst_value (hint))
    return false;

  tree res_type = TREE_TYPE (dst_ptr);

  if (!POINTER_TYPE_P (res_type))
    return false;

  odr_type dst_type = class_for_typeinfo (dst_ti);

  if (!dst_type || !TYPE_CXX_LOCAL (dst_type->type))
    return false;

  odr_type type_to_compare = NULL;

  if (!TYPE_FINAL_P (dst_type->type))
    {
      auto_vec<odr_type> worklist;

      worklist.safe_push (dst_type);
      do
	{
	  odr_type type = worklist.pop ();
	  odr_type derived;
	  unsigned i;

	  /* Skip class type that is never instantiated.  */
	  if (varpool_node::get (get_type_vtable (type->type)))
	    {
	      if (type_to_compare)
		return false;

	      /* Ensure dst_type is the first ancestor base of this type so
		 that cast offset is zero.  */
	      for (odr_type base = type; base != dst_type; )
		{
		  if (base->bases.is_empty () || base->has_virtual_base
		      || !TYPE_CXX_LOCAL (base->type))
		    return false;

		  base = base->bases[0];
		}
	      type_to_compare = type;
	    }

	  FOR_EACH_VEC_ELT (type->derived_types, i, derived)
	    worklist.safe_push (derived);
	} while (!worklist.is_empty ());
    }
  else if (varpool_node::get (get_type_vtable (dst_type->type)))
    type_to_compare = dst_type;

  if (!type_to_compare)
    {
      nullify_dynamic_cast (edge);
      return true;
    }

  gimple_stmt_iterator gsi = gsi_for_stmt (call_stmt);
  tree src_ptr_type = TREE_TYPE (src_ptr);
  tree src_type = TREE_TYPE (src_ptr_type);
  tree src_vtbl = NULL_TREE;
  tree dst_vtbl;
  unsigned HOST_WIDE_INT offset;

  calculate_dominance_info (CDI_DOMINATORS);

  if (TREE_CODE (src_type) == RECORD_TYPE)
    {
      if (!COMPLETE_TYPE_P (src_type) && odr_type_p (src_type))
	src_type = prevailing_odr_type (src_type);

      for (tree field = TYPE_FIELDS (src_type); field; )
	{
	  tree field_type = TREE_TYPE (field);

	  /* Try to compose load vptr based on class type of source object
	     if type information is available.  */
	  if (DECL_VIRTUAL_P (field))
	    {
	      tree mref_type = build_qualified_type (DECL_CONTEXT (field),
						     TYPE_QUAL_CONST);
	      gcc_assert (POINTER_TYPE_P (field_type));

	      if (TREE_CODE (src_ptr_type) == POINTER_TYPE)
		mref_type = build_pointer_type (mref_type);
	      else
		mref_type = build_reference_type (mref_type);

	      src_vtbl = build2 (MEM_REF, TREE_TYPE (mref_type), src_ptr,
				 build_zero_cst (mref_type));
	      src_vtbl = build3 (COMPONENT_REF, TREE_TYPE (field), src_vtbl,
				 field, NULL_TREE);
	      break;
	    }

	  if (!DECL_ARTIFICIAL (field) || TREE_CODE (field_type) != RECORD_TYPE)
	    break;

	  field = TYPE_FIELDS (field_type);
	}
    }

  if (!src_vtbl)
    src_vtbl = build2 (MEM_REF, ptr_type_node, src_ptr,
		       build_zero_cst (build_pointer_type (ptr_type_node)));

  src_vtbl = force_gimple_operand_gsi (&gsi, src_vtbl, true, NULL, true,
				       GSI_SAME_STMT);

  dst_vtbl = BINFO_VTABLE (TYPE_BINFO (type_to_compare->type));

  if (vtable_pointer_value_to_vtable (dst_vtbl, &dst_vtbl, &offset))
    dst_vtbl = build_vtable_addr_expr (dst_vtbl, offset);
  else
    {
      dst_vtbl = unshare_expr_without_location (dst_vtbl);
      dst_vtbl = force_gimple_operand_gsi (&gsi, dst_vtbl, true, NULL, true,
					   GSI_SAME_STMT);
    }

  gcond *cond_stmt = dyn_cast <gcond *> (last_stmt (call_bb));
  edge_def *e_cast;
  edge_def *e_fail;

  if (!param_dyncast_non_null_prob && cond_stmt
      && compare_null_stmt_p (cond_stmt, dst_ptr, e_cast, e_fail))
    {
      gimple *use_stmt;
      imm_use_iterator imm_iter;
      basic_block cast_bb = e_cast->dest;

      if (phi_nodes (cast_bb) || !single_pred_p (cast_bb))
	cast_bb = split_edge (e_cast);

      FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, dst_ptr)
	{
	  if (use_stmt == cond_stmt || is_gimple_debug (use_stmt))
	    continue;

	  if (dominated_by_p (CDI_DOMINATORS, gimple_bb (use_stmt), cast_bb))
	    continue;

	  if (gphi *phi = dyn_cast <gphi *> (use_stmt))
	    {
	      for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
		{
		  if (dst_ptr != gimple_phi_arg_def (phi, i))
		    continue;

		  edge_def *e_arg = gimple_phi_arg_edge (phi, i);

		  if (!dominated_by_p (CDI_DOMINATORS, e_arg->src, cast_bb))
		    goto not_dom;
		}
	      continue;
	    }

	not_dom:
	  cond_stmt = NULL;
	  break;
	}
    }
  else
    cond_stmt = NULL;

  if (cond_stmt)
    {
      enum tree_code code = gimple_cond_code (cond_stmt);

      gimple_cond_set_lhs (cond_stmt, src_vtbl);
      gimple_cond_set_rhs (cond_stmt, dst_vtbl);
      gimple_cond_set_code (cond_stmt, invert_tree_comparison (code, false));
      update_stmt (cond_stmt);

      gsi = gsi_after_labels (e_cast->dest);
    }
  else if (param_dyncast_non_null_prob)
    {
      gimple *cmp_vtbl = gimple_build_cond (EQ_EXPR, src_vtbl, dst_vtbl,
					    NULL_TREE, NULL_TREE);

      gsi_insert_before (&gsi, cmp_vtbl, GSI_SAME_STMT);

      e_cast = split_block (call_bb, cmp_vtbl);

      /* Call statement is placed to a new block after block split.  */
      call_bb = gimple_bb (call_stmt);

      e_fail = unchecked_make_edge (gimple_bb (cmp_vtbl), call_bb, 0);

      /* Create a new block to insert static type cast.  */
      split_edge (e_cast);

      e_cast->flags &= ~EDGE_FALLTHRU;
      e_cast->flags |= EDGE_TRUE_VALUE;
      e_fail->flags |= EDGE_FALSE_VALUE;
      e_cast->probability = profile_probability::guessed_always().apply_scale
					 (param_dyncast_non_null_prob, 100);
      e_fail->probability = e_cast->probability.invert ();

      tree src_cvt = make_ssa_name (src_ptr_type);
      gphi *src_phi = create_phi_node (src_cvt, call_bb);

      add_phi_arg (src_phi, src_ptr, single_succ_edge (e_cast->dest),
		   UNKNOWN_LOCATION);
      add_phi_arg (src_phi, build_zero_cst (src_ptr_type), e_fail,
		   UNKNOWN_LOCATION);

      src_ptr = src_cvt;
      gsi = gsi_for_stmt (call_stmt);
    }
  else
    {
      tree cmp_expr;

      cmp_expr = build2 (EQ_EXPR, boolean_type_node, src_vtbl, dst_vtbl);
      cmp_expr = fold_build3 (COND_EXPR, src_ptr_type, cmp_expr, src_ptr,
			      build_zero_cst (src_ptr_type));
      cmp_expr = force_gimple_operand_gsi (&gsi, cmp_expr, true, NULL, true,
					   GSI_SAME_STMT);
      src_ptr = cmp_expr;
    }

  src_ptr = fold_convert (res_type, src_ptr);
  gsi_insert_before (&gsi, gimple_build_assign (dst_ptr, src_ptr),
		     GSI_SAME_STMT);

  gsi = gsi_for_stmt (call_stmt);
  unlink_stmt_vdef (call_stmt);
  gsi_remove (&gsi, true);
  cgraph_edge::remove (edge);
  return true;
}

/* The ipa-post-devirt pass. */

static unsigned int
ipa_post_devirt (void)
{
  cgraph_node *node;

  if (!odr_types_ptr)
    return 0;

  if (dump_file && (dump_flags & TDF_DETAILS))
    dump_type_inheritance_graph (dump_file);

  FOR_EACH_FUNCTION (node)
    {
      node->aux = NULL;

      if (node->has_gimple_body_p ())
	analyze_virtual_function (node);
    }

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    {
      cfun_context context (node);
      bool changed = false;
      bool first = true;

      for (cgraph_edge *edge = node->indirect_calls; edge; )
	{
	  cgraph_edge *next_edge = edge->next_callee;

	  /* The vcall might be removed due to EH dead edge purge.  */
	  if (edge->indirect_info->polymorphic && gimple_bb (edge->call_stmt))
	    {
	      if (dump_file && first)
		{
		  fprintf (dump_file, "\nPost-devirtualize calls in %s\n",
			   node->dump_name ());
		  first = false;
		}

	      changed |= post_devirtualize_vcall (edge);
	    }

	  edge = next_edge;
	}

      if (changed)
	{
	  cleanup_tree_cfg ();
	  update_ssa (TODO_update_ssa);
	  cgraph_edge::rebuild_edges ();
	  changed = false;
	}

      for (cgraph_edge *edge = node->callees; edge; )
	{
	  cgraph_edge *next_edge = edge->next_callee;

	  if (call_has_name_p (edge->call_stmt, "__dynamic_cast")
	      && gimple_bb (edge->call_stmt))
	    changed |= optimize_dynamic_cast (edge);

	  edge = next_edge;
	}

      if (changed)
	{
	  cleanup_tree_cfg ();
	  update_ssa (TODO_update_ssa);
	  cgraph_edge::rebuild_edges ();
	}
    }

  FOR_EACH_FUNCTION (node)
    if (node->aux)
      {
	if (!node_is_wrapper_p (node))
	  delete (auto_vec<tree> *) node->aux;

	node->aux = NULL;
      }

  for (unsigned i = 0; i < 2; i++)
    {
      delete fntype_map[i];
      fntype_map[i] = NULL;
    }

  delete typeinfo_map;
  typeinfo_map = NULL;

  return 0;
}

namespace {

const pass_data pass_data_ipa_post_devirt =
{
  SIMPLE_IPA_PASS, /* type */
  "post-devirt", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_IPA_DEVIRT, /* tv_id */
  (PROP_cfg | PROP_ssa), /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  ( TODO_dump_symtab ), /* todo_flags_finish */
};

class pass_ipa_post_devirt : public simple_ipa_opt_pass
{
public:
  pass_ipa_post_devirt (gcc::context *ctxt)
    : simple_ipa_opt_pass (pass_data_ipa_post_devirt, ctxt)
  {}

  /* opt_pass methods: */
  virtual bool gate (function *)
    {
      return flag_devirtualize_fully && optimize;
    }

  virtual unsigned int execute (function *) { return ipa_post_devirt (); }

}; // class pass_ipa_post_devirt

} // anon namespace

simple_ipa_opt_pass *
make_pass_ipa_post_devirt (gcc::context *ctxt)
{
  return new pass_ipa_post_devirt (ctxt);
}

/* Print ODR name of a TYPE if available.
   Use demangler when option DEMANGLE is used.  */

DEBUG_FUNCTION void
debug_tree_odr_name (tree type, bool demangle)
{
  const char *odr = get_odr_name_for_type (type);
  if (demangle)
    {
      const int opts = DMGL_PARAMS | DMGL_ANSI | DMGL_TYPES;
      odr = cplus_demangle (odr, opts);
    }

  fprintf (stderr, "%s\n", odr);
}

/* Register ODR enum so we later stream record about its values.  */

void
register_odr_enum (tree t)
{
  if (flag_lto)
    vec_safe_push (odr_enums, t);
}

/* Write ODR enums to LTO stream file.  */

static void
ipa_odr_summary_write (void)
{
  if (!odr_enums && !odr_enum_map)
    return;
  struct output_block *ob = create_output_block (LTO_section_odr_types);
  unsigned int i;
  tree t;

  if (odr_enums)
    {
      streamer_write_uhwi (ob, odr_enums->length ());

      /* For every ODR enum stream out
	   - its ODR name
	   - number of values,
	   - value names and constant their represent
	   - bitpack of locations so we can do good diagnostics.  */
      FOR_EACH_VEC_ELT (*odr_enums, i, t)
	{
	  streamer_write_string (ob, ob->main_stream,
				 IDENTIFIER_POINTER
				     (DECL_ASSEMBLER_NAME (TYPE_NAME (t))),
				 true);

	  int n = 0;
	  for (tree e = TYPE_VALUES (t); e; e = TREE_CHAIN (e))
	    n++;
	  streamer_write_uhwi (ob, n);
	  for (tree e = TYPE_VALUES (t); e; e = TREE_CHAIN (e))
	    {
	      streamer_write_string (ob, ob->main_stream,
				     IDENTIFIER_POINTER (TREE_PURPOSE (e)),
				     true);
	      streamer_write_wide_int (ob,
				       wi::to_wide (DECL_INITIAL
						      (TREE_VALUE (e))));
	    }

	  bitpack_d bp = bitpack_create (ob->main_stream);
	  lto_output_location (ob, &bp, DECL_SOURCE_LOCATION (TYPE_NAME (t)));
	  for (tree e = TYPE_VALUES (t); e; e = TREE_CHAIN (e))
	    lto_output_location (ob, &bp,
				 DECL_SOURCE_LOCATION (TREE_VALUE (e)));
	  streamer_write_bitpack (&bp);
	}
      vec_free (odr_enums);
      odr_enums = NULL;
    }
  /* During LTO incremental linking we already have streamed in types.  */
  else if (odr_enum_map)
    {
      gcc_checking_assert (!odr_enums);
      streamer_write_uhwi (ob, odr_enum_map->elements ());

      hash_map<nofree_string_hash, odr_enum>::iterator iter
		= odr_enum_map->begin ();
      for (; iter != odr_enum_map->end (); ++iter)
	{
	  odr_enum &this_enum = (*iter).second;
	  streamer_write_string (ob, ob->main_stream, (*iter).first, true);

	  streamer_write_uhwi (ob, this_enum.vals.length ());
	  for (unsigned j = 0; j < this_enum.vals.length (); j++)
	    {
	      streamer_write_string (ob, ob->main_stream,
				     this_enum.vals[j].name, true);
	      streamer_write_wide_int (ob, this_enum.vals[j].val);
	    }

	  bitpack_d bp = bitpack_create (ob->main_stream);
	  lto_output_location (ob, &bp, this_enum.locus);
	  for (unsigned j = 0; j < this_enum.vals.length (); j++)
	    lto_output_location (ob, &bp, this_enum.vals[j].locus);
	  streamer_write_bitpack (&bp);
	}

      delete odr_enum_map;
      obstack_free (&odr_enum_obstack, NULL);
      odr_enum_map = NULL;
    }

  produce_asm (ob, NULL);
  destroy_output_block (ob);
}

/* Write ODR enums from LTO stream file and warn on mismatches.  */

static void
ipa_odr_read_section (struct lto_file_decl_data *file_data, const char *data,
		      size_t len)
{
  const struct lto_function_header *header
    = (const struct lto_function_header *) data;
  const int cfg_offset = sizeof (struct lto_function_header);
  const int main_offset = cfg_offset + header->cfg_size;
  const int string_offset = main_offset + header->main_size;
  class data_in *data_in;

  lto_input_block ib ((const char *) data + main_offset, header->main_size,
		      file_data->mode_table);

  data_in
    = lto_data_in_create (file_data, (const char *) data + string_offset,
			  header->string_size, vNULL);
  unsigned int n = streamer_read_uhwi (&ib);

  if (!odr_enum_map)
    {
      gcc_obstack_init (&odr_enum_obstack);
      odr_enum_map = new (hash_map <nofree_string_hash, odr_enum>);
    }

  for (unsigned i = 0; i < n; i++)
    {
      const char *rname = streamer_read_string (data_in, &ib);
      unsigned int nvals = streamer_read_uhwi (&ib);
      char *name;
  
      obstack_grow (&odr_enum_obstack, rname, strlen (rname) + 1);
      name = XOBFINISH (&odr_enum_obstack, char *);

      bool existed_p;
      class odr_enum &this_enum
		 = odr_enum_map->get_or_insert (xstrdup (name), &existed_p);

      /* If this is first time we see the enum, remember its definition.  */
      if (!existed_p)
	{
	  this_enum.vals.safe_grow_cleared (nvals, true);
	  this_enum.warned = false;
	  if (dump_file)
	    fprintf (dump_file, "enum %s\n{\n", name);
	  for (unsigned j = 0; j < nvals; j++)
	    {
	      const char *val_name = streamer_read_string (data_in, &ib);
	      obstack_grow (&odr_enum_obstack, val_name, strlen (val_name) + 1);
	      this_enum.vals[j].name = XOBFINISH (&odr_enum_obstack, char *);
	      this_enum.vals[j].val = streamer_read_wide_int (&ib);
	      if (dump_file)
		fprintf (dump_file, "  %s = " HOST_WIDE_INT_PRINT_DEC ",\n",
			 val_name, wi::fits_shwi_p (this_enum.vals[j].val)
			 ? this_enum.vals[j].val.to_shwi () : -1);
	    }
	  bitpack_d bp = streamer_read_bitpack (&ib);
	  stream_input_location (&this_enum.locus, &bp, data_in);
	  for (unsigned j = 0; j < nvals; j++)
	    stream_input_location (&this_enum.vals[j].locus, &bp, data_in);
	  data_in->location_cache.apply_location_cache ();
	  if (dump_file)
	    fprintf (dump_file, "}\n");
	}
      /* If we already have definition, compare it with new one and output
	 warnings if they differs.  */
      else
	{
	  int do_warning = -1;
	  char *warn_name = NULL;
	  wide_int warn_value = wi::zero (1);

	  if (dump_file)
	    fprintf (dump_file, "Comparing enum %s\n", name);

	  /* Look for differences which we will warn about later once locations
	     are streamed.  */
	  for (unsigned j = 0; j < nvals; j++)
	    {
	      const char *id = streamer_read_string (data_in, &ib);
	      wide_int val = streamer_read_wide_int (&ib);

	      if (do_warning != -1 || j >= this_enum.vals.length ())
		continue;
	      if (strcmp (id, this_enum.vals[j].name)
		  || (val.get_precision() !=
		      this_enum.vals[j].val.get_precision())
		  || val != this_enum.vals[j].val)
		{
		  warn_name = xstrdup (id);
		  warn_value = val;
		  do_warning = j;
		  if (dump_file)
		    fprintf (dump_file, "  Different on entry %i\n", j);
		}
	    }

	  /* Stream in locations, but do not apply them unless we are going
	     to warn.  */
	  bitpack_d bp = streamer_read_bitpack (&ib);
	  location_t locus;

	  stream_input_location (&locus, &bp, data_in);

	  /* Did we find a difference?  */
	  if (do_warning != -1 || nvals != this_enum.vals.length ())
	    {
	      data_in->location_cache.apply_location_cache ();

	      const int opts = DMGL_PARAMS | DMGL_ANSI | DMGL_TYPES;
	      char *dmgname = cplus_demangle (name, opts);
	      if (this_enum.warned
		  || !warning_at (this_enum.locus,
				  OPT_Wodr, "type %qs violates the "
				  "C++ One Definition Rule",
				  dmgname))
		do_warning = -1;
	      else
	       {
		 this_enum.warned = true;
		 if (do_warning == -1)
		   inform (locus,
			   "an enum with different number of values is defined"
			   " in another translation unit");
		 else if (warn_name)
		   inform (locus,
			   "an enum with different value name"
			   " is defined in another translation unit");
		 else
		   inform (locus,
			   "an enum with different values"
			   " is defined in another translation unit");
	       }
	    }
	  else
	    data_in->location_cache.revert_location_cache ();

	  /* Finally look up for location of the actual value that diverged.  */
	  for (unsigned j = 0; j < nvals; j++)
	    {
	      location_t id_locus;

	      data_in->location_cache.revert_location_cache ();
	      stream_input_location (&id_locus, &bp, data_in);

	      if ((int) j == do_warning)
		{
		  data_in->location_cache.apply_location_cache ();

		  if (strcmp (warn_name, this_enum.vals[j].name))
		    inform (this_enum.vals[j].locus,
			    "name %qs differs from name %qs defined"
			    " in another translation unit",
			    this_enum.vals[j].name, warn_name);
		  else if (this_enum.vals[j].val.get_precision() !=
			   warn_value.get_precision())
		    inform (this_enum.vals[j].locus,
			    "name %qs is defined as %u-bit while another "
			    "translation unit defines it as %u-bit",
			    warn_name, this_enum.vals[j].val.get_precision(),
			    warn_value.get_precision());
		  /* FIXME: In case there is easy way to print wide_ints,
		     perhaps we could do it here instead of overflow check.  */
		  else if (wi::fits_shwi_p (this_enum.vals[j].val)
			   && wi::fits_shwi_p (warn_value))
		    inform (this_enum.vals[j].locus,
			    "name %qs is defined to %wd while another "
			    "translation unit defines it as %wd",
			    warn_name, this_enum.vals[j].val.to_shwi (),
			    warn_value.to_shwi ());
		  else
		    inform (this_enum.vals[j].locus,
			    "name %qs is defined to different value "
			    "in another translation unit",
			    warn_name);

		  inform (id_locus,
			  "mismatching definition");
		}
	      else
	        data_in->location_cache.revert_location_cache ();
	    }
	  if (warn_name)
	    free (warn_name);
	  obstack_free (&odr_enum_obstack, name);
	}
    }
  lto_free_section_data (file_data, LTO_section_ipa_fn_summary, NULL, data,
			 len);
  lto_data_in_delete (data_in);
}

/* Read all ODR type sections.  */

static void
ipa_odr_summary_read (void)
{
  struct lto_file_decl_data **file_data_vec = lto_get_file_decl_data ();
  struct lto_file_decl_data *file_data;
  unsigned int j = 0;

  while ((file_data = file_data_vec[j++]))
    {
      size_t len;
      const char *data
	= lto_get_summary_section_data (file_data, LTO_section_odr_types,
					&len);
      if (data)
	ipa_odr_read_section (file_data, data, len);
    }
  /* Enum info is used only to produce warnings.  Only case we will need it
     again is streaming for incremental LTO.  */
  if (flag_incremental_link != INCREMENTAL_LINK_LTO)
    {
      delete odr_enum_map;
      obstack_free (&odr_enum_obstack, NULL);
      odr_enum_map = NULL;
    }
}

namespace {

const pass_data pass_data_ipa_odr =
{
  IPA_PASS, /* type */
  "odr", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_IPA_ODR, /* tv_id */
  0, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_ipa_odr : public ipa_opt_pass_d
{
public:
  pass_ipa_odr (gcc::context *ctxt)
    : ipa_opt_pass_d (pass_data_ipa_odr, ctxt,
		      NULL, /* generate_summary */
		      ipa_odr_summary_write, /* write_summary */
		      ipa_odr_summary_read, /* read_summary */
		      NULL, /* write_optimization_summary */
		      NULL, /* read_optimization_summary */
		      NULL, /* stmt_fixup */
		      0, /* function_transform_todo_flags_start */
		      NULL, /* function_transform */
		      NULL) /* variable_transform */
  {}

  /* opt_pass methods: */
  virtual bool gate (function *)
    {
      return (in_lto_p || flag_lto);
    }

  virtual unsigned int execute (function *)
    {
      return 0;
    }

}; // class pass_ipa_odr

} // anon namespace

ipa_opt_pass_d *
make_pass_ipa_odr (gcc::context *ctxt)
{
  return new pass_ipa_odr (ctxt);
}


#include "gt-ipa-devirt.h"
