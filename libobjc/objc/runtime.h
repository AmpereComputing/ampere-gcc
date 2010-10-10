/* GNU Objective-C Runtime API.
   Copyright (C) 2010 Free Software Foundation, Inc.
   Contributed by Nicola Pero <nicola.pero@meta-innovation.com>

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3, or (at your option) any
later version.

GCC is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
License for more details.

Under Section 7 of GPL version 3, you are granted additional
permissions described in the GCC Runtime Library Exception, version
3.1, as published by the Free Software Foundation.

You should have received a copy of the GNU General Public License and
a copy of the GCC Runtime Library Exception along with this program;
see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
<http://www.gnu.org/licenses/>.  */

#ifndef __objc_runtime_INCLUDE_GNU
#define __objc_runtime_INCLUDE_GNU

/*
  This file declares the "modern" GNU Objective-C Runtime API.
  Include this file to use it.

  This API is replacing the "traditional" GNU Objective-C Runtime API
  (declared in objc/objc-api.h) which is the one supported by older
  versions of the GNU Objective-C Runtime.  The "modern" API is very
  similar to the API used by the modern Apple/NeXT runtime.

  Because the two APIs have some conflicting definitions (in
  particular, Method and Category are defined differently) you should
  include either objc/objc-api.h (to use the traditional GNU
  Objective-C Runtime API) or objc/runtime.h (to use the modern GNU
  Objective-C Runtime API), but not both.
*/
#ifdef __objc_api_INCLUDE_GNU
# error You can not include both objc/objc-api.h and objc/runtime.h.  Include objc/objc-api.h for the traditional GNU Objective-C Runtime API and objc/runtime.h for the modern one.
#endif

/* TODO: This file is incomplete.  */

#include "objc.h"

/* An 'Ivar' represents an instance variable.  It holds information
   about the name, type and offset of the instance variable.  */
typedef struct objc_ivar *Ivar;

/* A 'Property' represents a property.  It holds information about the
   name of the property, and its attributes.

   Compatibility Note: the Apple/NeXT runtime defines this as
   objc_property_t, so we define it that way as well, but obviously
   Property is the right name.  */
typedef struct objc_property *Property;
typedef struct objc_property *objc_property_t;

/* A 'Method' represents a method.  It holds information about the
   name, types and the IMP of the method.  */
typedef struct objc_method *Method;

/* A 'Category' represents a category.  It holds information about the
   name of the category, the class it belongs to, and the methods,
   protocols and such like provided by the category.  */
typedef struct objc_category *Category;

/* 'Protocol' is defined in objc/objc.h (which is included by this
   file).  */

/* Method descriptor returned by introspective Object methods.  At the
   moment, this is really just the first part of the more complete
   objc_method structure used internally by the runtime.  (PS: In the
   GNU Objective-C Runtime, selectors already include a type, so an
   objc_method_description does not add much to a SEL.  But in other
   runtimes, that is not the case, which is why
   objc_method_description exists).  */
struct objc_method_description
{
  SEL name;      /* Selector (name and signature) */
  char *types;   /* Type encoding */
};

/* The following are used in encode strings to describe the type of
   Ivars and Methods.  */
#define _C_ID       '@'
#define _C_CLASS    '#'
#define _C_SEL      ':'
#define _C_CHR      'c'
#define _C_UCHR     'C'
#define _C_SHT      's'
#define _C_USHT     'S'
#define _C_INT      'i'
#define _C_UINT     'I'
#define _C_LNG      'l'
#define _C_ULNG     'L'
#define _C_LNG_LNG  'q'
#define _C_ULNG_LNG 'Q'
#define _C_FLT      'f'
#define _C_DBL      'd'
#define _C_LNG_DBL  'D'
#define _C_BFLD     'b'
#define _C_BOOL     'B'
#define _C_VOID     'v'
#define _C_UNDEF    '?'
#define _C_PTR      '^'
#define _C_CHARPTR  '*'
#define _C_ARY_B    '['
#define _C_ARY_E    ']'
#define _C_UNION_B  '('
#define _C_UNION_E  ')'
#define _C_STRUCT_B '{'
#define _C_STRUCT_E '}'
#define _C_VECTOR   '!'
#define _C_COMPLEX  'j'

/* _C_ATOM is never generated by the compiler.  You can treat it as
   equivalent to "*".  */
#define _C_ATOM     '%'

/* The following are used in encode strings to describe some
   qualifiers of method and ivar types.  */
#define _C_CONST	'r'
#define _C_IN		'n'
#define _C_INOUT	'N'
#define _C_OUT      	'o'
#define _C_BYCOPY	'O'
#define _C_BYREF	'R'
#define _C_ONEWAY	'V'
#define _C_GCINVISIBLE	'|'

/* The same when used as flags.  */
#define _F_CONST	0x01
#define _F_IN		0x01
#define _F_OUT		0x02
#define _F_INOUT	0x03
#define _F_BYCOPY	0x04
#define _F_BYREF	0x08
#define _F_ONEWAY	0x10
#define _F_GCINVISIBLE	0x20


/** Internals: the following functions are in selector.c.  */

/* Return the name of a given selector.  */
objc_EXPORT const char *sel_getName (SEL selector);

/* Return the type of a given selector.

   Compatibility Note: the Apple/NeXT runtime has untyped selectors,
   so it does not have this function, which is specific to the GNU
   Runtime.  */
objc_EXPORT const char *sel_getType (SEL selector);

/* This is the same as sel_registerName ().  Please use
   sel_registerName () instead.  */
objc_EXPORT SEL sel_getUid (const char *name);

/* Register a selector with a given name (but unspecified types).  If
   you know the types, it is better to call sel_registerTypedName().
   If a selector with this name already exists, it is returned.  */
objc_EXPORT SEL sel_registerName (const char *name);

/* Register a selector with a given name and types.  If a selector
   with this name and types already exists, it is returned.

   Compatibility Note: the Apple/NeXT runtime has untyped selectors,
   so it does not have this function, which is specific to the GNU
   Runtime.  */
objc_EXPORT SEL set_registerTypedName (const char *name, const char *type);

/* Return YES if first_selector is the same as second_selector, and NO
   if not.  */
objc_EXPORT BOOL sel_isEqual (SEL first_selector, SEL second_selector);


/** Internals: the following functions are in objects.c.  */

/* Create an instance of class 'class', adding extraBytes to the size
   of the returned object.  This method allocates the appropriate
   amount of memory for the instance, initializes it to zero, then
   calls all the C++ constructors on appropriate C++ instance
   variables of the instance (if any) (TODO: This is not implemented
   yet).  */
objc_EXPORT id class_createInstance (Class class, size_t extraBytes);

/* Copy an object and return the copy.  extraBytes should be identical
   to the extraBytes parameter that was passed when creating the
   original object.  */
objc_EXPORT id object_copy (id object, size_t extraBytes);

/* Dispose of an object.  This method calls the appropriate C++
   destructors on appropriate C++ instance variables of the instance
   (if any) (TODO: This is not implemented yet), then frees the memory
   for the instance.  */
objc_EXPORT id object_dispose (id object);


/* TODO: Add all the other functions in the API.  */


/** Internals: the following functions are in objc-foreach.c.  */

/* 'objc_enumerationMutation()' is called when a collection is
   mutated while being "fast enumerated".  That is a hard error, and
   objc_enumerationMutation is called to deal with it.  'collection'
   is the collection object that was mutated during an enumeration.

   objc_enumerationMutation() will invoke the mutation handler if any
   is set.  Then, it will abort the program.

   Compatibility note: the Apple runtime will not abort the program
   after calling the mutation handler.
 */
objc_EXPORT void objc_enumerationMutation (id collection);

/* 'objc_set_enumeration_mutation_handler' can be used to set a
   function that will be called (instead of aborting) when a fast
   enumeration is mutated during enumeration.  The handler will be
   called with the 'collection' being mutated as the only argument and
   it should not return; it should either exit the program, or could
   throw an exception.  The recommended implementation is to throw an
   exception - the user can then use exception handlers to deal with
   it.

   This function is not thread safe (other threads may be trying to
   invoke the enumeration mutation handler while you are changing it!)
   and should be called during during the program initialization
   before threads are started.  It is mostly reserved for "Foundation"
   libraries; in the case of GNUstep, GNUstep Base may be using this
   function to improve the standard enumeration mutation handling.
   You probably shouldn't use this function unless you are writing
   your own Foundation library.
*/
objc_EXPORT void objc_setEnumerationMutationHandler (void (*handler)(id));

/* This structure (used during fast enumeration) is automatically
   defined by the compiler (it is as if this definition was always
   included in all Objective-C files).  Note that it is usually
   defined again with the name of NSFastEnumeration by "Foundation"
   libraries such as GNUstep Base.  And if NSFastEnumeration is
   defined, the compiler will use it instead of
   __objcFastEnumerationState when doing fast enumeration.
*/
/*
struct __objcFastEnumerationState
{
  unsigned long state;
  id            *itemsPtr;
  unsigned long *mutationsPtr;
  unsigned long extra[5];
};
*/


/** Internals: the following functions are implemented in encoding.c.  */

/* Traditional GNU Objective-C Runtime functions that are currently
   used to implement method forwarding.
*/

/* Return the size of a variable which has the specified 'type'
   encoding.  */
int objc_sizeof_type (const char *type);

/* Return the align of a variable which has the specified 'type'
   encoding.  */
int objc_alignof_type (const char *type);

/* Return the aligned size of a variable which has the specified
   'type' encoding.  The aligned size is the size rounded up to the
   nearest alignment.  */
int objc_aligned_size (const char *type);

/* Return the promoted size of a variable which has the specified
   'type' encoding.  This is the size rounded up to the nearest
   integral of the wordsize, taken to be the size of a void *.  */
int objc_promoted_size (const char *type);


/* The following functions are used when parsing the type encoding of
   methods, to skip over parts that are ignored.  They take as
   argument a pointer to a location inside the type encoding of a
   method (which is a string) and return a new pointer, pointing to a
   new location inside the string after having skipped the unwanted
   information.  */

/* Skip some type qualifiers (_C_CONST, _C_IN, etc).  These may
  eventually precede typespecs occurring in method prototype
  encodings.  */
const char *objc_skip_type_qualifiers (const char *type);

/* Skip one typespec element (_C_CLASS, _C_SEL, etc).  If the typespec
  is prepended by type qualifiers, these are skipped as well.  */
const char *objc_skip_typespec (const char *type);

/* Skip an offset.  */
const char *objc_skip_offset (const char *type);

/* Skip an argument specification (ie, skipping a typespec, which may
   include qualifiers, and an offset too).  */
const char *objc_skip_argspec (const char *type);

/* Read type qualifiers (_C_CONST, _C_IN, etc) from string 'type'
   (stopping at the first non-type qualifier found) and return an
   unsigned int which is the logical OR of all the corresponding flags
   (_F_CONST, _F_IN etc).  */
unsigned objc_get_type_qualifiers (const char *type);


/* Note that the following functions work for very simple structures,
   but get easily confused by more complicated ones (for example,
   containing vectors).  A better solution is required.
*/

/* The following three functions can be used to determine how a
   structure is laid out by the compiler. For example:

  struct objc_struct_layout layout;
  int i;

  objc_layout_structure (type, &layout);
  while (objc_layout_structure_next_member (&layout))
    {
      int position, align;
      const char *type;

      objc_layout_structure_get_info (&layout, &position, &align, &type);
      printf ("element %d has offset %d, alignment %d\n",
              i++, position, align);
    }

  These functions are used by objc_sizeof_type and objc_alignof_type
  functions to compute the size and alignment of structures. The
  previous method of computing the size and alignment of a structure
  was not working on some architectures, particulary on AIX, and in
  the presence of bitfields inside the structure.  */
struct objc_struct_layout
{
  const char *original_type;
  const char *type;
  const char *prev_type;
  unsigned int record_size;
  unsigned int record_align;
};

void objc_layout_structure (const char *type,
                            struct objc_struct_layout *layout);
BOOL  objc_layout_structure_next_member (struct objc_struct_layout *layout);
void objc_layout_finish_structure (struct objc_struct_layout *layout,
                                   unsigned int *size,
                                   unsigned int *align);
void objc_layout_structure_get_info (struct objc_struct_layout *layout,
                                     unsigned int *offset,
                                     unsigned int *align,
                                     const char **type);

#endif
