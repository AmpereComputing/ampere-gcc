/* Struct-reorg optimizations.
   Copyright (C) 2016-2017 Free Software Foundation, Inc.

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
#include "gimple-pretty-print.h"
#include "gimple-iterator.h"
#include "cfg.h"
#include "ssa.h"
#include "tree-dfa.h"
#include "fold-const.h"
#include "stor-layout.h"
#include "tree-into-ssa.h"
#include "tree-cfg.h"
#include "ipa-utils.h"
#include "ipa-struct-reorg.h"
#include "tree-eh.h"
#include "bitmap.h"
#include "cfgloop.h"
#include "langhooks.h"
#include "gimple-range.h"
#include "gimplify-me.h"
#include "varasm.h"
#include "tree-ssa-live.h"  /* For remove_unused_locals.  */
#include "ipa-type-escape-analysis.h"

#define VOID_POINTER_P(type) (POINTER_TYPE_P (type) && VOID_TYPE_P (TREE_TYPE (type)))

namespace {

using namespace struct_reorg;
using namespace struct_relayout;

/* Return true iff TYPE is stdarg va_list type.  */

static inline bool
is_va_list_type (tree type)
{
  return TYPE_MAIN_VARIANT (type) == TYPE_MAIN_VARIANT (va_list_type_node);
}

/* Return the inner most type for arrays and pointers of TYPE.  */

tree
inner_type (tree type)
{
  while (POINTER_TYPE_P (type)
	 || TREE_CODE (type) == ARRAY_TYPE)
    type = TREE_TYPE (type);
  return type;
}

/*  Return true if TYPE is a type which struct reorg should handled.  */

bool
handled_type (tree type)
{
  type = inner_type (type);
  if (TREE_CODE (type) == RECORD_TYPE)
    return !is_va_list_type (type);
  return false;
}

/* Check whether in C language or LTO with only C language.  */
bool
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
	  if (language_string == NULL
	      || strncmp (language_string, "GNU C", 5)
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

enum srmode
{
  NORMAL = 0,
  COMPLETE_STRUCT_RELAYOUT
};

static bool is_result_of_mult (tree arg, tree *num, tree struct_size);
bool isptrptr (tree type);

srmode current_mode;

} // anon namespace

namespace struct_reorg {

hash_map <tree, auto_vec <tree> > fields_to_finish;

/* Constructor of srfunction. */

srfunction::srfunction (cgraph_node *n)
  : node (n),
    old (NULL),
    newnode (NULL),
    newf (NULL)
{
}

/* Add an ARG to the list of arguments for the function. */

void
srfunction::add_arg(srdecl *arg)
{
  args.safe_push(arg);
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
      for(unsigned i = 0; i < globals.length (); i++)
	{
	  fprintf (file, "\n  ");
          globals[i]->dump (file);
        }

      fprintf (file, "\ndecls: ");
    }
  else
    fprintf (file, "globals : ");

  for(unsigned i = 0; i < decls.length (); i++)
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
  : offset(int_byte_position (field)),
    fieldtype (TREE_TYPE (field)),
    fielddecl (field),
    base(base),
    type(NULL),
    clusternum(0)
{
  for(int i = 0;i < max_split; i++)
    newfield[i] = NULL_TREE;
}

/* Constructor of TYPE. */

srtype::srtype (tree type)
  : type (type),
    chain_type (false),
    supported (true),
    visited (false),
    has_alloc_array (0)
{
  for (int i = 0; i < max_split; i++)
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

/* Add FIELD to the list of fields that use this type.  */

void
srtype::add_field_site (srfield *field)
{
  field_sites.safe_push(field);
}


/* Constructor of DECL. */

srdecl::srdecl (srtype *tp, tree decl, int argnum, tree orig_type)
  : type (tp),
    decl (decl),
    func (NULL_TREE),
    argumentnum (argnum),
    visited (false),
    orig_type (orig_type)
{
  if (TREE_CODE (decl) == SSA_NAME)
    func = current_function_decl;
  else if (!is_global_var (decl))
    func = DECL_CONTEXT (decl);
  for(int i = 0;i < max_split; i++)
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
      if (!decl1->orig_type && orig_type && isptrptr (orig_type))
	{
	  decl1->orig_type = orig_type;
	}
      return decl1;
    }

  gcc_assert (type);

  orig_type = isptrptr (TREE_TYPE (decl)) ? TREE_TYPE (decl) : orig_type;
  decl1 = new srdecl (type, decl, arg, isptrptr (orig_type)? orig_type : NULL);
  decls.safe_push(decl1);
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

  functions.safe_push(fn);
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
}

/* Analyze the type and decide what to be done with it. */

void
srtype::analyze (void)
{
  /* Chain decl types can't be split
     so don't try. */
  if (chain_type)
    return;

  /* If there is only one field then there is nothing
     to be done. */
  if (fields.length () == 1)
    return;

  /*  For now we unconditionally split only structures with 2 fields
      into 2 different structures.  In future we intend to add profile
      info and/or static heuristics to differentiate splitting process.  */
  if (fields.length () == 2)
    fields[1]->clusternum = 1;

  /* Otherwise we do nothing.  */
  if (fields.length () >= 3)
    {
      return;
    }
}

/* Create the new fields for this field. */

void
srfield::create_new_fields (tree newtype[max_split],
			    tree newfields[max_split],
			    tree newlast[max_split])
{
  tree nt[max_split];

  for (unsigned i = 0; i < max_split; i++)
    nt[i] = NULL;

  if (type == NULL)
    nt[0] = fieldtype;
  else
    memcpy (nt, type->newtype, sizeof(type->newtype));

  for (unsigned i = 0; i < max_split && nt[i] != NULL; i++)
    {
      tree field = make_node (FIELD_DECL);
      if (nt[1] != NULL && DECL_NAME (fielddecl))
	{
	  const char *tname = IDENTIFIER_POINTER (DECL_NAME (fielddecl));
	  char id[10];
	  char *name;

	  sprintf(id, "%d", i);
	  name = concat (tname, ".reorg.", id, NULL);
	  DECL_NAME (field) = get_identifier (name);
	  free (name);
	}
      else
	DECL_NAME (field) = DECL_NAME (fielddecl);

      TREE_TYPE (field) = reconstruct_complex_type (TREE_TYPE (fielddecl), nt[i]);
      DECL_SOURCE_LOCATION (field) = DECL_SOURCE_LOCATION (fielddecl);
      SET_DECL_ALIGN (field, DECL_ALIGN (fielddecl));
      DECL_USER_ALIGN (field) = DECL_USER_ALIGN (fielddecl);
      TREE_ADDRESSABLE (field) = TREE_ADDRESSABLE (fielddecl);
      DECL_NONADDRESSABLE_P (field) = !TREE_ADDRESSABLE (fielddecl);
      TREE_THIS_VOLATILE (field) = TREE_THIS_VOLATILE (fielddecl);
      DECL_CONTEXT (field) = newtype[clusternum];

      if (newfields[clusternum] == NULL)
	newfields[clusternum] = newlast[clusternum] = field;
      else
	{
	  DECL_CHAIN (newlast[clusternum]) = field;
	  newlast[clusternum] = field;
        }
      newfield[i] = field;
    }

}

/* Create the new TYPE corresponding to THIS type. */

bool
srtype::create_new_type (void)
{
  /* If the type has been visited,
     then return if a new type was
     created or not. */
  if (visited)
    return has_new_type ();

  visited = true;

  if (has_escaped ())
    {
      newtype[0] = type;
      return false;
    }

  bool createnewtype = false;
  unsigned maxclusters = 0;

  /* Create a new type for each field. */
  for (unsigned i = 0; i < fields.length (); i++)
    {
      srfield *field = fields[i];
      if (field->type)
	createnewtype |= field->type->create_new_type ();
      if (field->clusternum > maxclusters)
	maxclusters = field->clusternum;
    }

  /* If the fields' types did have a change or
     we are not splitting the struct into two clusters,
     then just return false and don't change the type. */
  if (!createnewtype && maxclusters == 0)
    {
      newtype[0] = type;
      return false;
    }

  /* Should have at most max_split clusters.  */
  gcc_assert (maxclusters < max_split);

  /* Record the first member of the field chain.  */
  tree newfields[max_split];
  tree newlast[max_split];

  maxclusters++;

  const char *tname = get_type_name (type);

  for (unsigned i = 0; i < maxclusters; i++)
    {
      newfields[i] = NULL_TREE;
      newlast[i] = NULL_TREE;
      newtype[i] = make_node (RECORD_TYPE);

      char *name = NULL;
      char id[10];
      sprintf(id, "%d", i);
      if (tname) 
	{
	  name = concat (".reorg.", id, NULL);
	  TYPE_NAME (newtype[i]) = build_decl (UNKNOWN_LOCATION, TYPE_DECL,
				   get_identifier (name), newtype[i]);
          free (name);
        }
    }

  for (unsigned i = 0; i < fields.length (); i++)
    {
      srfield *f = fields[i];
      f->create_new_fields (newtype, newfields, newlast);
    }


  /* No reason to warn about these structs since the warning would
     have happened already.  */
  int save_warn_padded = warn_padded;
  warn_padded = 0;

  for (unsigned i = 0; i < maxclusters; i++)
    {
      TYPE_FIELDS (newtype[i]) = newfields[i];
      layout_type (newtype[i]);
      if (TYPE_NAME (newtype[i]) != NULL)
	{
	  layout_decl (TYPE_NAME (newtype[i]), 0);
	}
    }

  warn_padded = save_warn_padded;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Created %d types:\n", maxclusters);
      for (unsigned i = 0; i < maxclusters; i++)
	{
	  print_generic_expr (dump_file, newtype[i]);
	  fprintf (dump_file, "(%d)", TYPE_UID (newtype[i]));
	  fprintf (dump_file, "\n");
	}
    }

  return true;
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
  if (is_global_var (orig_decl))
    set_decl_tls_model (new_decl, DECL_TLS_MODEL (orig_decl));
}

/* Create all of the new decls (SSA_NAMES included) for THIS function. */

void
srfunction::create_new_decls (void)
{
  /* If this function has been cloned, we don't need to
     create the new decls. */
  if (newnode)
    return;

  if (node)
    set_cfun (DECL_STRUCT_FUNCTION (node->decl));

  for (unsigned i = 0; i < decls.length (); i++)
    {
      srdecl *decl = decls[i];
      srtype *type = decl->type;
      /* If the type of the decl does not change,
	 then don't create a new decl. */
      if (!type->has_new_type ())
	{
	  decl->newdecl[0] = decl->decl;
	  continue;
	}

      /* Handle SSA_NAMEs. */
      if (TREE_CODE (decl->decl) == SSA_NAME)
	{
	  tree newtype1[max_split];
	  tree inner = SSA_NAME_VAR (decl->decl);
	  tree newinner[max_split];
	  memset (newinner, 0, sizeof(newinner));
	  for (unsigned j = 0; j < max_split && type->newtype[j]; j++)
	    {
	      newtype1[j] = reconstruct_complex_type (
		      isptrptr (decls[i]->orig_type) ? decls[i]->orig_type
		      : TREE_TYPE (decls[i]->decl),
		      type->newtype[j]);
	    }
	  if (inner)
	    {
	      srdecl *in = find_decl (inner);
	      gcc_assert (in);
	      memcpy (newinner, in->newdecl, sizeof(newinner));
	    }
	  tree od = decls[i]->decl;
	  /* Create the new ssa names and copy some attributes from the old one.  */
	  for (unsigned j = 0; j < max_split && type->newtype[j]; j++)
	    {
	      tree nd = make_ssa_name (newinner[j] ? newinner[j] : newtype1[j]);
	      decl->newdecl[j] = nd;
	      /* If the old decl was a default defintion, handle it specially. */
	      if (SSA_NAME_IS_DEFAULT_DEF (od))
		{
	          SSA_NAME_IS_DEFAULT_DEF (nd) = true;
		  SSA_NAME_DEF_STMT (nd) = gimple_build_nop ();

		  /* Set the default definition for the ssaname if needed. */
		  if (inner)
		    {
		      gcc_assert (newinner[j]);
		      set_ssa_default_def (cfun, newinner[j], nd);
		    }
		}
	      SSA_NAME_OCCURS_IN_ABNORMAL_PHI (nd)
		= SSA_NAME_OCCURS_IN_ABNORMAL_PHI (od);
	      statistics_counter_event (cfun, "Create new ssa_name", 1);
	    }
	}
      else if (TREE_CODE (decls[i]->decl) == VAR_DECL)
	{
	 tree orig_var = decl->decl;
	 const char *tname = NULL;
	 if (DECL_NAME (orig_var))
	   tname = IDENTIFIER_POINTER (DECL_NAME (orig_var));
	 for (unsigned j = 0; j < max_split && type->newtype[j]; j++)
	   {
	      tree new_name = NULL;
	      char *name = NULL;
	      char id[10];
	      sprintf(id, "%d", j);
	      if (tname)
	        {
		  name = concat (tname, ".reorg.", id, NULL);
		  new_name = get_identifier (name);
		  free (name);
		}
	      tree newtype1 = reconstruct_complex_type (TREE_TYPE (orig_var), type->newtype[j]);
	      decl->newdecl[j] = build_decl (DECL_SOURCE_LOCATION (orig_var),
					     VAR_DECL, new_name, newtype1);
	      copy_var_attributes (decl->newdecl[j], orig_var);
	      if (!is_global_var (orig_var))
		add_local_decl (cfun, decl->newdecl[j]);
	      else
		varpool_node::add (decl->newdecl[j]);
	      statistics_counter_event (cfun, "Create new var decl", 1);
	    }
        }
      /* Paramater decls are already handled in create_new_functions. */
      else if (TREE_CODE (decls[i]->decl) == PARM_DECL)
	;
      else
	internal_error ("Unhandled declaration type stored");

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Created New decls for decl:\n");
	  decls[i]->dump (dump_file);
	  fprintf (dump_file, "\n");
	  for (unsigned j = 0; j < max_split && decls[i]->newdecl[j]; j++)
	    {
	      print_generic_expr (dump_file, decls[i]->newdecl[j]);
	      fprintf (dump_file, "\n");
	    }
	  fprintf (dump_file, "\n");
	}
    }

  set_cfun (NULL);

}

/* Dump out the field structure to FILE. */

void
srfield::dump (FILE *f)
{
  fprintf (f, "field (%d) { ", DECL_UID (fielddecl));
  print_generic_expr (f, fielddecl);
  fprintf (f, ", base = ");
  base->simple_dump (f);
  fprintf (f, ", offset = " HOST_WIDE_INT_PRINT_DEC, offset);
  fprintf (f, ", type = ");
  print_generic_expr (f, fieldtype);
  fprintf (f, "}\n");
}


/* A simplified dump out the field structure to FILE. */

void
srfield::simple_dump (FILE *f)
{
  if (fielddecl)
    {
      fprintf (f, "field (%d)", DECL_UID (fielddecl));
    }
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

} // namespace struct_reorg

namespace struct_relayout {

/* Complete Structure Relayout Optimization.
   It reorganizes all structure members, and puts same member together.
   struct s {
     long a;
     int b;
     struct s* c;
   };
   Array looks like
     abcabcabcabc...
   will be transformed to
     aaaa...bbbb...cccc...
*/

#define GPTR_SIZE(i) \
  TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (gptr[i])))

unsigned transformed = 0;

unsigned
csrtype::calculate_field_num (tree field_offset)
{
  if (field_offset == NULL)
    {
      return 0;
    }

  HOST_WIDE_INT off = int_byte_position (field_offset);
  unsigned i = 1;
  for (tree field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
    {
      if (off == int_byte_position (field))
	{
	  return i;
	}
      i++;
    }
  return 0;
}

bool
csrtype::init_type_info (void)
{
  if (!type)
    return false;

  unsigned HOST_WIDE_INT cache_size = param_l1_cache_line_size;

  /* We don't split the struct if it's too small.  */
  if (tree_to_uhwi (TYPE_SIZE_UNIT (type)) < cache_size)
    return false;

  for (tree field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
    if (TREE_CODE (field) == FIELD_DECL)
      field_count++;

  /* We don't split the struct if it has few number of fields.  */
  if (field_count < min_relayout_split || field_count > max_relayout_split)
    return false;

  struct_size = TYPE_SIZE_UNIT (type);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Type: ");
      print_generic_expr (dump_file, type);
      fprintf (dump_file, " has %d members.\n", field_count);
    }
  return true;
}

} // namespace struct_relayout

namespace {

/* Structure definition for ipa_struct_reorg and ipa_struct_relayout.  */

struct ipa_struct_reorg
{
public:
  // Constructors
  ipa_struct_reorg(void)
    : current_function (NULL),
      done_recording (false)
  {
  }

  unsigned execute (enum srmode mode);

  // fields
  auto_vec_del<srtype> types;
  auto_vec_del<srfunction> functions;
  auto_vec<tree> all_types;
  srglobal globals;
  srfunction *current_function;

  bool done_recording;

  void dump_types (FILE *f);
  void dump_newtypes (FILE *f);
  void dump_types_escaped (FILE *f);
  void dump_functions (FILE *f);
  void record_accesses (void);
  void prune_escaped_types (bool = false);
  void analyze_types (void);
  void clear_visited (void);
  bool create_new_types (void);
  void create_new_decls (void);
  srdecl *find_decl (tree);
  void create_new_functions (void);
  void create_new_args (cgraph_node *new_node);
  unsigned rewrite_functions (void);
  srdecl *record_var (tree decl, int arg = -1);
  srfunction *record_function (cgraph_node *node);
  srfunction *find_function (cgraph_node *node);
  void record_field_type (tree field, srtype *base_srtype);
  void record_struct_field_types (tree base_type, srtype *base_srtype);
  srtype *record_type (tree type);
  srtype *find_type (tree type);
  void maybe_record_stmt (gimple *);
  void maybe_record_assign (gassign *);
  void maybe_record_allocation_site (cgraph_node *, gimple *);
  bool handled_allocation_stmt (gimple *stmt);
  tree allocate_size (srtype *t, srdecl *decl, gimple *stmt);

  bool rewrite_stmt (gimple*, gimple_stmt_iterator *);
  bool rewrite_assign (gassign *, gimple_stmt_iterator *);
  bool rewrite_call (gcall *, gimple_stmt_iterator *);
  bool rewrite_cond (gcond *);
  bool rewrite_debug (gimple *, gimple_stmt_iterator *);
  bool rewrite_phi (gphi *);
  bool rewrite_expr (tree expr, tree newexpr[max_split], bool ignore_missing_decl = false);
  bool rewrite_lhs_rhs (tree lhs, tree rhs, tree newlhs[max_split], tree newrhs[max_split]);
  bool get_type_field (tree expr, tree &base, bool &indirect, srtype *&type,
		       srfield *&field, bool &realpart, bool &imagpart,
		       bool &address, bool should_create = false);
  bool wholeaccess (tree expr, tree base, tree accesstype, srtype *t);

  void check_alloc_num (gimple *stmt, srtype *type);
  void check_definition_assign (srdecl *decl, vec<srdecl*> &worklist);
  void check_definition_call (srdecl *decl, vec<srdecl*> &worklist);
  void check_definition (srdecl *decl, vec<srdecl*>&);
  void check_uses (srdecl *decl, vec<srdecl*>&);
  void check_use (srdecl *decl, gimple *stmt, vec<srdecl*>&);
  void check_type_and_push (tree newdecl, srdecl *decl,
			    vec<srdecl *> &worklist);
  void check_other_side (srdecl *decl, tree other, vec<srdecl *> &worklist);

  void find_vars (gimple *stmt);
  void find_var (tree expr);
  void mark_type_unsupported (tree type, gimple *stmt);

  bool has_rewritten_type (srfunction*);
  void maybe_record_other_side (tree side, tree other);
  unsigned execute_struct_relayout (void);
};

struct ipa_struct_relayout
{
public:
  // fields
  tree gptr[max_relayout_split + 1];
  csrtype ctype;
  ipa_struct_reorg *sr;
  cgraph_node *current_node;
  int addr_to_index;
  tree index_type;
  auto_vec<tree> ctype_fields;

  enum addr_to_index_mode
  {
    ATOI_NONE,
    ATOI_NORMAL,
    ATOI_EXTRA_ALLOCATION,
    ATOI_OFFSET_GPTR
  };

  enum ctype_kind
  {
    /* Do not refer to ctype (candidate type).  */
    CTYPE_NONE,
    /* This is just ctype pointer.  */
    CTYPE_PTR,
    /* Refer to ctype pointer indirectly.  */
    CTYPE_PTR_IND,
    /* Refer to ctype, but not its pointer.  */
    CTYPE_OTHER
  };

  // Constructors
  ipa_struct_relayout (tree type, ipa_struct_reorg *sr_)
  {
    ctype.type = type;
    sr = sr_;
    current_node = NULL;

    if (flag_ipa_reorg_addr_to_index)
      addr_to_index = ATOI_EXTRA_ALLOCATION;
    else
      addr_to_index = ATOI_NONE;

    index_type = pointer_sized_int_node;

    for (int i = 0; i < max_relayout_split + 1; i++)
      {
	gptr[i] = NULL;
      }
  }

  // Methods
  int classify_type_1 (tree type);
  int classify_type (tree expr)
  {
    return classify_type_1 (TYPE_P (expr) ? expr : TREE_TYPE (expr));
  }

  bool is_ctype_p (tree type) const
  {
    return types_compatible_p (type, ctype.type);
  }

  bool refer_ctype_p (tree expr);
  bool refer_ctype_p (gimple *stmt);
  tree rewrite_type (tree type);
  bool analyze_expr (tree expr, bool only_ssa = false);
  bool analyze_expr_pair (tree lhs_expr, tree rhs_expr, bool has_ssa = true);
  bool analyze_ssa (tree ssa)
  {
    return analyze_expr (ssa, true);
  }
  void rewrite_expr (tree &expr);
  bool analyze_init (tree type, tree init);
  void rewrite_init (tree type, tree &init);
  bool analyze_decl (tree decl, int *kind_ptr = NULL);
  void rewrite_decl (tree decl);
  tree create_new_vars (tree type, const char *name);
  void create_global_ptrs (void);
  bool analyze (void);
  unsigned int rewrite (void);
  bool analyze_stmt_in_function (void);
  void rewrite_stmt_in_function (void);
  bool analyze_stmt (gimple *stmt);
  bool rewrite_stmt (gimple *stmt);
  bool analyze_phi (gphi *stmt);
  bool rewrite_phi (gphi *stmt);
  bool analyze_cond (gcond *stmt);
  bool rewrite_cond (gcond *stmt);
  bool rewrite_debug (gimple *stmt);
  bool handled_allocation_stmt (gcall *stmt);
  void init_global_ptrs (gcall *stmt, gimple_stmt_iterator *gsi);
  bool check_call_uses (gcall *stmt);
  bool analyze_call (gcall *stmt);
  bool rewrite_call (gcall *stmt);
  bool is_candidate (tree xhs);
  bool analyze_memref (tree memref);
  tree rewrite_address (tree xhs, gimple_stmt_iterator *gsi);
  void rewrite_memref (tree &memref, gimple *stmt);
  bool analyze_assign (gassign *stmt);
  bool rewrite_pointer_diff (gassign *stmt);
  bool rewrite_assign (gassign *stmt);
  bool find_hot_access (void);
  unsigned int execute (void);
};

} // anon namespace

namespace {

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

  ret = fold_build1_loc (gimple_location (gsi_stmt (*gsi)), code, type, a);
  return force_gimple_operand_gsi (gsi, ret, true, NULL, true, GSI_SAME_STMT);
}

/* Methods for ipa_struct_relayout.  */

static void
set_var_attributes (tree var)
{
  if (!var)
    {
      return;
    }
  gcc_assert (TREE_CODE (var) == VAR_DECL);

  DECL_ARTIFICIAL (var) = 1;
  DECL_EXTERNAL (var) = 0;
  TREE_STATIC (var) = 1;
  TREE_PUBLIC (var) = 0;
  TREE_USED (var) = 1;
  DECL_CONTEXT (var) = NULL;
  TREE_THIS_VOLATILE (var) = 0;
  TREE_ADDRESSABLE (var) = 0;
  TREE_READONLY (var) = 0;
  if (is_global_var (var))
    {
      set_decl_tls_model (var, TLS_MODEL_NONE);
    }
}

static tree
create_ssa (tree node, gimple_stmt_iterator *gsi)
{
  gcc_assert (TREE_CODE (node) == VAR_DECL);
  tree node_ssa = make_ssa_name (TREE_TYPE (node));
  gassign *stmt = gimple_build_assign (node_ssa, node);
  gsi_insert_before (gsi, stmt, GSI_SAME_STMT);
  return node_ssa;
}

int
ipa_struct_relayout::classify_type_1 (tree type)
{
  if (RECORD_OR_UNION_TYPE_P (type))
    return is_ctype_p (type) ? CTYPE_OTHER : CTYPE_NONE;

  if (FUNC_OR_METHOD_TYPE_P (type))
    {
      int kind = classify_type_1 (TREE_TYPE (type));

      if (kind == CTYPE_OTHER)
	return kind;

      if (kind)
	kind = CTYPE_PTR_IND;

      for (tree parm = TYPE_ARG_TYPES (type); parm; parm = TREE_CHAIN (parm))
	{
	  int parm_kind = classify_type_1 (TREE_VALUE (parm));

	  if (parm_kind == CTYPE_OTHER)
	    return parm_kind;

	  if (parm_kind)
	    kind = CTYPE_PTR_IND;
	}

      return kind;
    }

  if (POINTER_TYPE_P (type))
    {
      if (RECORD_OR_UNION_TYPE_P (TREE_TYPE (type)))
	return is_ctype_p (TREE_TYPE (type)) ? CTYPE_PTR : CTYPE_NONE;
    }
  else if (TREE_CODE (type) != ARRAY_TYPE)
    return CTYPE_NONE;

  int kind = classify_type_1 (TREE_TYPE (type));

  return kind == CTYPE_PTR ? CTYPE_PTR_IND : kind;
}

static tree
refer_type_p_fn (tree *opnd_ptr, int *walk_subtrees ATTRIBUTE_UNUSED,
		 void *data)
{
  tree opnd = *opnd_ptr;

  if (CODE_CONTAINS_STRUCT (TREE_CODE (opnd), TS_TYPED))
    {
      auto relayout = (ipa_struct_relayout *) data;

      if (relayout->classify_type (TREE_TYPE (opnd)))
	return opnd;
    }

  return NULL_TREE;
}

bool
ipa_struct_relayout::refer_ctype_p (tree expr)
{
  gcc_checking_assert (!TYPE_P (expr));
  return walk_tree (&expr, refer_type_p_fn, this, NULL);
}

bool
ipa_struct_relayout::refer_ctype_p (gimple *stmt)
{
  if (gphi *phi = dyn_cast <gphi *> (stmt))
    {
      if (refer_ctype_p (gimple_phi_result (phi)))
	return true;

      for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
	{
	  if (refer_ctype_p (gimple_phi_arg_def (phi, i)))
	    return true;
	}
    }
  else
    {
      for (unsigned i = 0; i < gimple_num_ops (stmt); i++)
	{
	  if (tree op = gimple_op (stmt, i))
	    {
	      if (refer_ctype_p (op))
		return true;
	    }
	}
    }

  return false;
}

tree
ipa_struct_relayout::rewrite_type (tree type)
{
  tree new_type;

  if (POINTER_TYPE_P (type))
    {
      tree data_type = TREE_TYPE (type);

      if (RECORD_OR_UNION_TYPE_P (data_type))
	{
	  if (!is_ctype_p (data_type))
	    return type;

	  new_type = index_type;
	}
      else
	{
	  new_type = rewrite_type (data_type);

	  if (new_type == data_type)
	    return type;

	  bool alias_all = TYPE_REF_CAN_ALIAS_ALL (type);

	  if (TREE_CODE (type) == POINTER_TYPE)
	    new_type = build_pointer_type_for_mode (new_type, ptr_mode,
						    alias_all);
	  else
	    new_type = build_reference_type_for_mode (new_type, ptr_mode,
						      alias_all);
	}
    }
  else if (TREE_CODE (type) == ARRAY_TYPE)
    {
      tree elem_type = TREE_TYPE (type);

      new_type = rewrite_type (elem_type);

      if (new_type == elem_type)
	return type;

      bool reverse = TYPE_REVERSE_STORAGE_ORDER (new_type);

      new_type = build_array_type_1 (new_type, TYPE_DOMAIN (type),
				     TYPE_TYPELESS_STORAGE (type),
				     !reverse, false);

      if (reverse)
	TYPE_REVERSE_STORAGE_ORDER (new_type) = true;
    }
  else if (FUNC_OR_METHOD_TYPE_P (type))
    {
      if (!classify_type (type))
	return type;

      tree ret_type = rewrite_type (TREE_TYPE (type));
      tree arg_types = NULL_TREE;

      for (tree parm = TYPE_ARG_TYPES (type); parm; parm = TREE_CHAIN (parm))
	{
	  tree parm_type = rewrite_type (TREE_VALUE (parm));

	  arg_types = tree_cons (NULL_TREE, parm_type, arg_types);
	}

      arg_types = nreverse (arg_types);

      if (TREE_CODE (type) == FUNCTION_TYPE)
	new_type = build_function_type (ret_type, arg_types);
      else
	{
	  tree base_type = TYPE_METHOD_BASETYPE (type);

	  gcc_assert (!is_ctype_p (base_type));

	  new_type = build_method_type_directly (base_type, ret_type,
						 arg_types);
	}
    }
  else
    {
      gcc_assert (!is_ctype_p (type));
      return type;
    }

  if (int quals = TYPE_QUALS (type))
    new_type = build_qualified_type (new_type, quals);

  return new_type;
}

bool
ipa_struct_relayout::analyze_expr (tree expr, bool only_ssa)
{
  /* TODO: Support expression whose type is not ctype pointer, but
     consists of it.  */
  if (classify_type (expr) != CTYPE_PTR)
    return false;

  if (TREE_CODE (expr) != SSA_NAME
      && (only_ssa || !integer_zerop (expr)))
    return false;

  return true;
}

bool
ipa_struct_relayout::analyze_expr_pair (tree lhs_expr, tree rhs_expr,
					bool has_ssa)
{
  if (!analyze_expr (lhs_expr) || !analyze_expr (rhs_expr))
    return false;

  if (has_ssa && TREE_CODE (lhs_expr) != SSA_NAME
      && TREE_CODE (rhs_expr) != SSA_NAME)
    return false;

  return true;
}

void
ipa_struct_relayout::rewrite_expr (tree &expr)
{
  tree old_type = TREE_TYPE (expr);
  tree new_type = rewrite_type (old_type);

  gcc_checking_assert (old_type != new_type);

  if (integer_zerop (expr))
    expr = build_zero_cst (new_type);
  else if (TREE_CODE (expr) == COMPONENT_REF
	   || TREE_CLOBBER_P (expr))
    TREE_TYPE (expr) = new_type;
  else
    gcc_checking_assert (TREE_CODE (expr) == SSA_NAME);
}

bool
ipa_struct_relayout::analyze_init (tree type, tree init)
{
  unsigned i;
  tree index, value;

  if (TREE_CODE (init) == STRING_CST)
    {
      gcc_assert (!RECORD_OR_UNION_TYPE_P (inner_type (type)));
      return true;
    }

  if (TREE_CODE (init) != CONSTRUCTOR)
    {
      gcc_assert (!AGGREGATE_TYPE_P (type));
      gcc_assert (!AGGREGATE_TYPE_P (TREE_TYPE (init)));

      int kind = classify_type (type);

      /* TODO: Support initialization value whose type is not ctype pointer,
	 but refers to the ctype pointer indirectly.  */
      if (kind > CTYPE_PTR)
	return false;

      if (kind != classify_type (init))
	return false;

      return integer_zerop (init);
    }

  FOR_EACH_CONSTRUCTOR_ELT (CONSTRUCTOR_ELTS (init), i, index, value)
    {
      if (RECORD_OR_UNION_TYPE_P (type))
	{
	  gcc_assert (index && TREE_CODE (index) == FIELD_DECL);

	  if (!analyze_init (TREE_TYPE (index), value))
	    return false;
	}
      else
	{
	  gcc_assert (TREE_CODE (type) == ARRAY_TYPE);

	  if (!analyze_init (TREE_TYPE (type), value))
	    return false;
	}
    }

  return true;
}

void
ipa_struct_relayout::rewrite_init (tree type, tree &init)
{
  if (TREE_CODE (init) != CONSTRUCTOR)
    {
      if (classify_type (type))
	rewrite_expr (init);
    }
  else if (TREE_CODE (type) == ARRAY_TYPE)
    {
      for (unsigned i = 0; i < CONSTRUCTOR_NELTS (init); ++i)
	{
	  tree &value = CONSTRUCTOR_ELT (init, i)->value;

	  rewrite_init (TREE_TYPE (type), value);
	}

      TREE_TYPE (init) = rewrite_type (TREE_TYPE (init));
    }
  else
    {
      for (tree field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
	{
	  for (unsigned i = 0; i < CONSTRUCTOR_NELTS (init); ++i)
	    {
	      tree index = CONSTRUCTOR_ELT (init, i)->index;

	      if (index == field)
		{
		  tree &value = CONSTRUCTOR_ELT (init, i)->index;

		  rewrite_init (TREE_TYPE (index), value);
		  break;
		}
	    }
	}
    }
}

bool
ipa_struct_relayout::analyze_decl (tree decl, int *kind_ptr)
{
  int kind = classify_type (decl);

  if (kind_ptr)
    *kind_ptr = kind;

  /* TODO: Support decl whose type is not ctype pointer but refers to
     ctype pointer indirectly, for example, array of ctype pointer.  */
  if (kind > CTYPE_PTR)
    return false;

  if (VAR_P (decl))
    {
      tree init = DECL_INITIAL (decl);

      if (init && init != error_mark_node
	  && !analyze_init (TREE_TYPE (decl), init))
	return false;
    }

  return true;
}

void
ipa_struct_relayout::rewrite_decl (tree decl)
{
  if (VAR_P (decl))
    {
      tree &init = DECL_INITIAL (decl);

      if (init && init != error_mark_node)
	{
	  bool has_ctype = false;

	  if (dump_file && (dump_flags & TDF_DETAILS) && refer_ctype_p (init))
	    {
	      fprintf (dump_file, "Rewrite init for variable ");
	      print_generic_expr (dump_file, decl);
	      fprintf (dump_file, ":\n");
	      print_generic_expr (dump_file, init);
	      fprintf (dump_file, "\nto\n");
	      has_ctype = true;
	    }

	  rewrite_init (TREE_TYPE (decl), init);

	  if (dump_file && (dump_flags & TDF_DETAILS) && has_ctype)
	    {
	      print_generic_expr (dump_file, init);
	      fprintf (dump_file, "\n\n");
	    }
	}
    }

  if (classify_type (decl))
    {
      tree old_type = TREE_TYPE (decl);
      tree new_type = rewrite_type (old_type);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Rewrite");

	  if (TREE_CODE (decl) == SSA_NAME)
	    fprintf (dump_file, " ssa ");
	  else if (TREE_CODE (decl) == FIELD_DECL)
	    fprintf (dump_file, " field ");
	  else if (SSA_VAR_P (decl))
	    fprintf (dump_file, " variable ");

	  print_generic_expr (dump_file, decl);

	  if (DECL_P (decl) && SSA_VAR_P (decl))
	    fprintf (dump_file, "(%u)", DECL_UID (decl));

	  if (TREE_CODE (decl) == FIELD_DECL)
	    {
	      fprintf (dump_file, " in ");
	      print_generic_expr (dump_file, DECL_CONTEXT (decl));
	    }

	  fprintf (dump_file, ":\n");
	  print_generic_expr (dump_file, old_type);
	  fprintf (dump_file, "\nto\n");
	  print_generic_expr (dump_file, new_type);
	  fprintf (dump_file, "\n\n");
	}

      if (TREE_CODE (decl) == FIELD_DECL
	  && classify_type (old_type) == CTYPE_PTR)
	{
	  tree gptr_var = gptr[0] ? gptr[0] : gptr[1];

	  DECL_ATTRIBUTES (decl) = tree_cons (
					get_identifier ("addr_to_index"),
					gptr_var,
					DECL_ATTRIBUTES (decl));
	}

      TREE_TYPE (decl) = new_type;

      if (TREE_CODE (decl) == SSA_NAME
	  && POINTER_TYPE_P (old_type) && !POINTER_TYPE_P (new_type))
	SSA_NAME_PTR_INFO (decl) = NULL;
      else if (DECL_P (decl))
	{
	  SET_DECL_MODE (decl, TYPE_MODE (new_type));

	  if (DECL_RTL_SET_P (decl))
	    make_decl_rtl (decl);
	}
    }
}

tree
ipa_struct_relayout::create_new_vars (tree type, const char *name)
{
  gcc_assert (type);
  tree new_type = build_pointer_type (type);

  tree new_name = NULL;
  if (name)
    {
      new_name = get_identifier (name);
    }

  tree new_var = build_decl (UNKNOWN_LOCATION, VAR_DECL, new_name, new_type);

  /* set new_var's attributes.  */
  set_var_attributes (new_var);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Created new var: ");
      print_generic_expr (dump_file, new_var);
      fprintf (dump_file, "\n");
    }
  return new_var;
}

void
ipa_struct_relayout::create_global_ptrs (void)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Create global gptrs: {\n");
    }

  const char *type_name = get_type_name (ctype.type);

  if (!addr_to_index || addr_to_index == ATOI_OFFSET_GPTR)
    {
      char *gptr0_name = NULL;

      if (type_name)
	gptr0_name = concat (type_name, ".reorg_gptr0", NULL);

      tree var_gptr0_type = addr_to_index ? void_type_node : ctype.type;
      tree var_gptr0 = create_new_vars (var_gptr0_type, gptr0_name);
      gptr[0] = var_gptr0;
      DECL_NONALIASED (var_gptr0) = 1;
      varpool_node::add (var_gptr0);
    }

  unsigned i = 1;
  for (tree field = TYPE_FIELDS (ctype.type); field;
	    field = DECL_CHAIN (field))
    {
      if (TREE_CODE (field) == FIELD_DECL)
	{
	  tree type = TREE_TYPE (field);

	  char *name = NULL;
	  char id[10] = {0};
	  sprintf (id, "%d", i);
	  const char *decl_name = IDENTIFIER_POINTER (DECL_NAME (field));

	  if (type_name && decl_name)
	    {
	      name = concat (type_name, "_", decl_name, ".reorg_gptr", id, NULL);
	    }

	  if (addr_to_index && classify_type (type))
	    type = rewrite_type (type);

	  tree var = create_new_vars (type, name);

	  gptr[i] = var;
	  DECL_NONALIASED (var) = 1;
	  varpool_node::add (var);
	  i++;
	}
    }
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\nTotally create %d gptrs. }\n\n", i);
    }
  gcc_assert (ctype.field_count == i - 1);
}

bool
ipa_struct_relayout::analyze_stmt_in_function (void)
{
  unsigned i;
  tree var;

  if (cfun->static_chain_decl && classify_type (cfun->static_chain_decl))
    return false;

  FOR_EACH_LOCAL_DECL (cfun, i, var)
    {
      if (!analyze_decl (var))
	return false;
    }

  for (cgraph_edge *edge = current_node->callees; edge;
       edge = edge->next_callee)
    {
      gcall *stmt = edge->call_stmt;

      if (handled_allocation_stmt (stmt) && check_call_uses (stmt))
	{
	  tree lhs = gimple_call_lhs (stmt);

	  if (!lhs || TREE_CODE (lhs) != SSA_NAME)
	    return false;

	  if (classify_type (lhs) != CTYPE_PTR)
	    {
	      /* Fixup allocation address type.  */
	      TREE_TYPE (lhs) = build_pointer_type (ctype.type);

	      if (tree var = SSA_NAME_VAR (lhs))
		SET_SSA_NAME_VAR_OR_IDENTIFIER (lhs, DECL_NAME (var));
	    }
	}
    }

  basic_block bb = NULL;
  gimple_stmt_iterator si;

  FOR_EACH_BB_FN (bb, cfun)
    {
      for (si = gsi_start_nonvirtual_phis (bb); !gsi_end_p (si);
	   gsi_next (&si))
	{
	  if (!analyze_stmt (gsi_stmt (si)))
	    return false;
	}

      for (si = gsi_start_bb (bb); !gsi_end_p (si); gsi_next (&si))
	{
	  if (!analyze_stmt (gsi_stmt (si)))
	    return false;
	}
    }

  return true;
}

void
ipa_struct_relayout::rewrite_stmt_in_function (void)
{
  basic_block bb = NULL;
  gimple_stmt_iterator si;

  FOR_EACH_BB_FN (bb, cfun)
    {
      if (addr_to_index)
	{
	  for (si = gsi_start_nonvirtual_phis (bb); !gsi_end_p (si); )
	    {
	      gimple *stmt = gsi_stmt (si);

	      gsi_next (&si);
	      rewrite_stmt (stmt);
	    }
	}

      for (si = gsi_start_bb (bb); !gsi_end_p (si);)
	{
	  gimple *stmt = gsi_stmt (si);

	  gsi_next (&si);
	  rewrite_stmt (stmt);
	}
    }

  /* Debug statements need to happen after all other statements
     have changed.  */
  FOR_EACH_BB_FN (bb, cfun)
    {
      for (si = gsi_start_bb (bb); !gsi_end_p (si);)
	{
	  gimple *stmt = gsi_stmt (si);

	  if (gimple_code (stmt) == GIMPLE_DEBUG
	      && rewrite_debug (stmt))
	    {
	      gsi_remove (&si, true);
	    }
	  else
	    {
	      gsi_next (&si);
	    }
	}
    }

  if (addr_to_index)
    {
      unsigned i;
      tree decl;

      FOR_EACH_LOCAL_DECL (cfun, i, decl)
	rewrite_decl (decl);

      FOR_EACH_SSA_NAME (i, decl, cfun)
	{
	  if (!SSA_NAME_IN_FREE_LIST (decl)
	      && !SSA_NAME_IS_VIRTUAL_OPERAND (decl))
	    rewrite_decl (decl);
	}
    }
}

bool
ipa_struct_relayout::analyze (void)
{
  cgraph_node *cnode = NULL;
  varpool_node *vnode = NULL;
  tree type;
  unsigned i;

  ctype_fields.release ();

  FOR_EACH_VEC_ELT (sr->all_types, i, type)
    {
      for (tree field = TYPE_FIELDS (type); field;
	   field = DECL_CHAIN (field))
	{
	  int kind;

	  if (!analyze_decl (field, &kind))
	    return false;

	  if (kind)
	    ctype_fields.safe_push (field);
	}
    }

  FOR_EACH_VARIABLE (vnode)
    {
      if (!analyze_decl (vnode->decl))
	return false;
    }

  FOR_EACH_FUNCTION (cnode)
    {
      /* TODO: Support functions whose return type or parameter types refer
	 to ctype.  */
      if (classify_type (cnode->decl))
	return false;

      if (!cnode->has_gimple_body_p ())
	continue;

      cfun_context ctx (cnode);

      current_node = cnode;

      if (!analyze_stmt_in_function ())
	return false;

      current_node = NULL;
    }

  return true;
}

unsigned int
ipa_struct_relayout::rewrite (void)
{
  cgraph_node *cnode = NULL;
  unsigned i = 0;

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (cnode)
    {
      cfun_context ctx (cnode);

      current_node = cnode;

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\nBefore rewrite: %dth_%s\n", i,
		   cnode->name ());
	  dump_function_to_file (cfun->decl, dump_file, dump_flags | TDF_VOPS);
	  fprintf (dump_file,
		   "\n======== Start to rewrite: %dth_%s ========\n", i,
		   cnode->name ());
	}

      rewrite_stmt_in_function ();
      update_ssa (TODO_update_ssa_only_virtuals);

      if (dump_file)
	{
	  fprintf (dump_file, "\nAfter rewrite: %dth_%s\n", i,
		   cnode->name ());
	  dump_function_to_file (cfun->decl, dump_file, dump_flags | TDF_VOPS);
	}
      i++;

      if (flag_tree_pta)
	compute_may_aliases ();

      remove_unused_locals ();
      cgraph_edge::rebuild_edges ();
      free_dominance_info (CDI_DOMINATORS);

      current_node = NULL;
    }

  if (addr_to_index)
    {
      varpool_node *vnode;
      tree field;
      unsigned i;

      FOR_EACH_VARIABLE (vnode)
	rewrite_decl (vnode->decl);

      FOR_EACH_VEC_ELT (ctype_fields, i, field)
	rewrite_decl (field);
    }

  return TODO_verify_all;
}

bool
ipa_struct_relayout::analyze_stmt (gimple *stmt)
{
  if (!refer_ctype_p (stmt))
    {
      gimple_set_visited (stmt, false);
      return true;
    }

  gimple_set_visited (stmt, true);

  switch (gimple_code (stmt))
    {
    case GIMPLE_ASSIGN:
      return analyze_assign (as_a <gassign *> (stmt));

    case GIMPLE_PHI:
      return analyze_phi (as_a <gphi *> (stmt));

    case GIMPLE_COND:
      return analyze_cond (as_a <gcond *> (stmt));

    case GIMPLE_CALL:
      return analyze_call (as_a <gcall *> (stmt));

    case GIMPLE_DEBUG:
      break;

    default:
      return false;
    }

  return true;
}

/* Return TRUE if the old stmt is to be removed.  */

bool
ipa_struct_relayout::rewrite_stmt (gimple *stmt)
{
  if (!gimple_visited_p (stmt))
    return false;

  switch (gimple_code (stmt))
    {
    case GIMPLE_ASSIGN:
      return rewrite_assign (as_a <gassign *> (stmt));

    case GIMPLE_PHI:
      return rewrite_phi (as_a <gphi *> (stmt));

    case GIMPLE_COND:
      return rewrite_cond (as_a <gcond *> (stmt));

    case GIMPLE_CALL:
      return rewrite_call (as_a <gcall *> (stmt));

    default:
      break;
    }

  return false;
}

bool
ipa_struct_relayout::analyze_phi (gphi *stmt)
{
  if (!analyze_ssa (gimple_phi_result (stmt)))
    return false;

  for (unsigned i = 0; i < gimple_phi_num_args (stmt); i++)
    {
      tree arg = gimple_phi_arg_def (stmt, i);

      if (!analyze_expr (arg))
	return false;
    }

  return true;
}

bool
ipa_struct_relayout::rewrite_phi (gphi *stmt)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Rewrite phi:\n");
      print_gimple_stmt (dump_file, stmt, 0);
      fprintf (dump_file, "to\n");
    }

  for (unsigned i = 0; i < gimple_phi_num_args (stmt); i++)
    {
      tree &arg = *gimple_phi_arg_def_ptr (stmt, i);

      rewrite_expr (arg);
      SET_PHI_ARG_DEF (stmt, i, arg);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      print_gimple_stmt (dump_file, stmt, 0);
      fprintf (dump_file, "\n");
    }

  return false;
}

bool
ipa_struct_relayout::analyze_cond (gcond *stmt)
{
  return analyze_expr_pair (gimple_cond_lhs (stmt), gimple_cond_rhs (stmt));
}

bool
ipa_struct_relayout::rewrite_cond (gcond *stmt)
{
  if (!addr_to_index)
    return false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Rewrite if-statement:\n");
      print_gimple_stmt (dump_file, stmt, 0);
      fprintf (dump_file, "to\n");
    }

  rewrite_expr (*gimple_cond_lhs_ptr (stmt));
  rewrite_expr (*gimple_cond_rhs_ptr (stmt));

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      print_gimple_stmt (dump_file, stmt, 0);
      fprintf (dump_file, "\n");
    }

  return false;
}

bool
ipa_struct_relayout::rewrite_debug (gimple *stmt)
{
  /* Delete debug gimple now.  */
  return (true || stmt);
}

bool
ipa_struct_relayout::handled_allocation_stmt (gcall *stmt)
{
  if (gimple_call_builtin_p (stmt, BUILT_IN_CALLOC))
    {
      return true;
    }
  return false;
}

void
ipa_struct_relayout::init_global_ptrs (gcall *stmt, gimple_stmt_iterator *gsi)
{
  gimple_stmt_iterator prev_gsi = *gsi;
  tree lhs = gimple_call_lhs (stmt);

  gcc_assert (handled_allocation_stmt (stmt));

  /* Case that gimple is at the end of bb.  */
  if (gsi_one_before_end_p (*gsi))
    gsi_insert_after (gsi, gimple_build_nop (), GSI_NEW_STMT);
  else
    gsi_next (gsi);

  /* Emit gimple gptr0 = _X and gptr1 = _X.  */
  if (gptr[0])
    {
      gassign *gptr0 = gimple_build_assign (gptr[0], lhs);
      gsi_insert_before (gsi, gptr0, GSI_SAME_STMT);
    }

  gassign *gptr1 = gimple_build_assign (gptr[1], lhs);
  gsi_insert_before (gsi, gptr1, GSI_SAME_STMT);

  /* Emit gimple gptr_[i] = gptr_[i-1] + _Y[gap].  */
  for (unsigned i = 2; i <= ctype.field_count; i++)
    {
      gimple *new_stmt = NULL;
      tree gptr_i_prev_ssa = create_ssa (gptr[i-1], gsi);
      tree gptr_i_ssa = make_ssa_name (TREE_TYPE (gptr[i-1]));

      /* Emit gimple _Y[gap] = N * sizeof (member).  */
      tree member_gap = gimplify_build2 (gsi, MULT_EXPR,
					 long_unsigned_type_node,
					 gimple_call_arg (stmt, 0),
					 GPTR_SIZE (i-1));

      new_stmt = gimple_build_assign (gptr_i_ssa, POINTER_PLUS_EXPR,
				      gptr_i_prev_ssa, member_gap);
      gsi_insert_before (gsi, new_stmt, GSI_SAME_STMT);

      if (addr_to_index == ATOI_OFFSET_GPTR)
	{
	  tree adjustment = fold_build1 (NEGATE_EXPR, long_unsigned_type_node,
					 GPTR_SIZE (i-1));
	  gptr_i_prev_ssa = gimplify_build2 (gsi, POINTER_PLUS_EXPR,
					     TREE_TYPE (gptr_i_prev_ssa),
					     gptr_i_prev_ssa, adjustment);
	  gassign *gptr_i_prev = gimple_build_assign (gptr[i-1],
						      gptr_i_prev_ssa);
	  gsi_insert_before (gsi, gptr_i_prev, GSI_SAME_STMT);
	}

      gassign *gptr_i = gimple_build_assign (gptr[i], gptr_i_ssa);
      gsi_insert_before (gsi, gptr_i, GSI_SAME_STMT);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Insert init_global_ptr:\n");

      for (gsi_next (&prev_gsi); gsi_stmt (prev_gsi) != gsi_stmt (*gsi);
	   gsi_next (&prev_gsi))
	print_gimple_stmt (dump_file, gsi_stmt (prev_gsi), 0);
      fprintf (dump_file, "\n");
    }
}

bool
ipa_struct_relayout::check_call_uses (gcall *stmt)
{
  gcc_assert (current_node);
  srfunction *fn = sr->find_function (current_node);
  tree lhs = gimple_call_lhs (stmt);

  if (fn == NULL)
    {
      return false;
    }

  srdecl *d = fn->find_decl (lhs);
  if (d == NULL)
    {
      return false;
    }

  return is_ctype_p (d->type->type);
}

bool
ipa_struct_relayout::analyze_call (gcall *stmt)
{
  if (handled_allocation_stmt (stmt))
    {
      tree lhs = gimple_call_lhs (stmt);

      if (!lhs || !analyze_ssa (lhs))
	return false;

      tree size = gimple_call_arg (stmt, 1);

      if (!tree_int_cst_equal (size, ctype.struct_size))
	{
	  if (dump_file)
	    {
	      fprintf (dump_file, "Expected size to be ");
	      print_generic_expr (dump_file, ctype.struct_size);
	      fprintf (dump_file, " at stmt: ");
	      print_gimple_stmt (dump_file, stmt, 0);
	    }
	  return false;
	}
    }
  else if (gimple_call_builtin_p (stmt, BUILT_IN_FREE))
    {
      if (!analyze_ssa (gimple_call_arg (stmt, 0)))
	return false;
    }
  else
    return false;

  return true;
}

static tree
replace_with_increment (tree expr, HOST_WIDE_INT inc,
			gimple_stmt_iterator *gsi)
{
  tree type = TREE_TYPE (expr);

  if (TREE_CODE (expr) == INTEGER_CST)
    return fold_binary (PLUS_EXPR, type, expr, build_int_cst (type, inc));

  gimple *stmt = SSA_NAME_DEF_STMT (expr);

  if (!is_gimple_assign (stmt))
    return gimplify_build2 (gsi, PLUS_EXPR, type, expr,
			  build_int_cst (type, inc));

  enum tree_code code = gimple_assign_rhs_code (stmt);
  tree rhs1 = gimple_assign_rhs1 (stmt);
  tree rhs1_type = TREE_TYPE (rhs1);

  if (code == SSA_NAME
      || (CONVERT_EXPR_CODE_P (code)
	  && TREE_CODE (rhs1) == SSA_NAME
	  && TYPE_PRECISION (rhs1_type) >= TYPE_PRECISION (type)
	  && INTEGRAL_TYPE_P (rhs1_type)))
    {
      gimple_stmt_iterator rhs1_gsi = gsi_for_stmt (stmt);

      rhs1 = replace_with_increment (rhs1, inc, &rhs1_gsi);

      if (has_single_use (expr))
	{
	  gimple_assign_set_rhs1 (stmt, rhs1);
	  update_stmt (stmt);
	  return expr;
	}

      return gimplify_build1 (gsi, code, type, rhs1);
    }

  if (code == PLUS_EXPR || code == MINUS_EXPR)
    {
      tree rhs2 = gimple_assign_rhs2 (stmt);

      if (TREE_CODE (rhs1) == INTEGER_CST)
	{
	  rhs1 = fold_binary (PLUS_EXPR, type, rhs2,
			      build_int_cst (type, inc));

	  if (integer_zerop (rhs1) && code == PLUS_EXPR)
	    return rhs2;
	}
      else if (TREE_CODE (rhs2) == INTEGER_CST)
	{
	  rhs2 = fold_binary (code, type, rhs2,
			      build_int_cst (type, inc));

	  if (integer_zerop (rhs2))
	    return rhs1;
	}
      else
	goto end;

      if (has_single_use (expr))
	{
	  gimple_assign_set_rhs2 (stmt, rhs1);
	  gimple_assign_set_rhs2 (stmt, rhs2);
	  update_stmt (stmt);
	  return expr;
	}

      return gimplify_build2 (gsi, code, type, rhs1, rhs2);
    }

end:
  return gimplify_build2 (gsi, PLUS_EXPR, type, expr,
			  build_int_cst (type, inc));
}

static bool
compare_null_stmt_p (gcond *stmt, tree ssa, edge &e_good, edge &e_null)
{
  tree opnd0 = gimple_cond_lhs (stmt);
  tree opnd1 = gimple_cond_rhs (stmt);

  if ((opnd0 != ssa || !integer_zerop (opnd1))
      && (opnd1 != ssa || !integer_zerop (opnd0)))
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

static void
create_new_def_at_edge (tree ssa, tree val, edge e)
{
  tree new_ssa = copy_ssa_name (ssa);
  gimple *stmt = gimple_build_assign (new_ssa, val);
  imm_use_iterator imm_iter;
  gimple *use_stmt;

  gsi_insert_on_edge_immediate (e, stmt);

  basic_block bb = gimple_bb (stmt);

  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, ssa)
    {
      if (use_stmt == stmt)
	continue;

      if (gphi *phi = dyn_cast <gphi *> (use_stmt))
	{
	  for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
	    {
	      tree arg = gimple_phi_arg_def (phi, i);

	      if (arg != ssa)
		continue;

	      edge e = gimple_phi_arg_edge (phi, i);

	      if (dominated_by_p (CDI_DOMINATORS, e->src, bb))
		add_phi_arg (phi, new_ssa, e,
			     gimple_phi_arg_location (phi, i));
	    }
	}
      else if (dominated_by_p (CDI_DOMINATORS, gimple_bb (use_stmt), bb))
	{
	  use_operand_p use_p;

	  FOR_EACH_IMM_USE_ON_STMT (use_p, imm_iter)
	    SET_USE (use_p, new_ssa);
	}
    }

  if (has_zero_uses (new_ssa))
    {
      gimple_stmt_iterator gsi = gsi_for_stmt (stmt);

      gsi_remove (&gsi, true);
      release_ssa_name (new_ssa);
    }
}

bool
ipa_struct_relayout::rewrite_call (gcall *stmt)
{
  if (handled_allocation_stmt (stmt))
    {
      if (!check_call_uses (stmt))
	return false;

      /* Rewrite stmt _X = calloc (N, sizeof (struct)).  */
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Rewrite allocation call:\n");
	  print_gimple_stmt (dump_file, stmt, 0);
	  fprintf (dump_file, "to\n");
	}

      gcc_assert (tree_int_cst_equal (gimple_call_arg (stmt, 1),
				      ctype.struct_size));

      gimple_stmt_iterator gsi = gsi_for_stmt (stmt);

      if (addr_to_index == ATOI_EXTRA_ALLOCATION)
	{
	  tree cnt = gimple_call_arg (stmt, 0);
	  tree new_cnt = replace_with_increment (cnt, 1, &gsi);

	  if (new_cnt != cnt)
	    {
	      gimple_call_set_arg (stmt, 0, new_cnt);
	      update_stmt (stmt);
	    }

	  if (dump_file && (dump_flags & TDF_DETAILS)
	      && TREE_CODE (new_cnt) == SSA_NAME)
	    print_gimple_stmt (dump_file, SSA_NAME_DEF_STMT (new_cnt), 0);
	}

      if (addr_to_index)
	{
	  tree lhs = gimple_call_lhs (stmt);
	  tree new_lhs = make_ssa_name (ptr_type_node);
	  tree val_one = build_one_cst (index_type);
	  tree val_zero = build_zero_cst (index_type);
	  tree cond;

	  gcc_checking_assert (classify_type (lhs) == CTYPE_PTR);

	  gimple_call_set_lhs (stmt, new_lhs);

	  cond = fold_build2 (NE_EXPR, boolean_type_node, new_lhs,
			      null_pointer_node);
	  cond = fold_build3 (COND_EXPR, index_type, cond, val_one, val_zero);
	  cond = force_gimple_operand_gsi (&gsi, cond, false, NULL_TREE, false,
					   GSI_NEW_STMT);
	  gsi_insert_after (&gsi, gimple_build_assign (lhs, cond),
			    GSI_NEW_STMT);

	  basic_block bb = gimple_bb (stmt);

	  while (single_succ_p (bb))
	    bb = single_succ (bb);

	  if (gcond *cond = safe_dyn_cast <gcond *> (last_stmt (bb)))
	    {
	      edge e_good, e_null;

	      if (compare_null_stmt_p (cond, lhs, e_good, e_null))
		{
		  calculate_dominance_info (CDI_DOMINATORS);
		  create_new_def_at_edge (lhs, val_one, e_good);
		  create_new_def_at_edge (lhs, val_zero, e_null);
		}
	    }
	}

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  print_gimple_stmt (dump_file, stmt, 0);
	  if (addr_to_index)
	    print_gimple_stmt (dump_file, gsi_stmt (gsi), 0);
	  fprintf (dump_file, "\n");
	}

      init_global_ptrs (stmt, &gsi);
    }
  else if (!addr_to_index)
    return false;

  if (gimple_call_builtin_p (stmt, BUILT_IN_FREE))
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Rewrite free call:\n");
	  print_gimple_stmt (dump_file, stmt, 0);
	  fprintf (dump_file, "to\n");
	}

      gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
      tree addr = create_ssa (gptr[0] ? gptr[0] : gptr[1], &gsi);

      gimple_call_set_arg (stmt, 0, addr);
      update_stmt (stmt);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  print_gimple_stmt (dump_file, SSA_NAME_DEF_STMT (addr), 0);
	  print_gimple_stmt (dump_file, stmt, 0);
	  fprintf (dump_file, "\n");
	}
    }

  return false;
}

bool
ipa_struct_relayout::is_candidate (tree xhs)
{
  if (TREE_CODE (xhs) == COMPONENT_REF)
    {
      tree mem = TREE_OPERAND (xhs, 0);

      if (TREE_CODE (mem) == MEM_REF)
	return is_ctype_p (TREE_TYPE (mem));
    }

  return false;
}

bool
ipa_struct_relayout::analyze_memref (tree memref)
{
  if (!refer_ctype_p (memref))
    return true;

  if (TREE_CODE (memref) != COMPONENT_REF)
    return false;

  tree field = TREE_OPERAND (memref, 1);
  int kind = classify_type (memref);

  if (kind > CTYPE_PTR)
    return false;

  if (kind != classify_type (TREE_OPERAND (memref, 1)))
    return false;

  while (true)
    {
      memref = TREE_OPERAND (memref, 0);

      if (TREE_CODE (memref) != COMPONENT_REF)
	break;
    }

  if (TREE_CODE (memref) == MEM_REF)
    {
      tree addr = TREE_OPERAND (memref, 0);

      if (!analyze_ssa (addr))
	{
	  if (refer_ctype_p (memref))
	    return false;
	}
      else if (!is_ctype_p (TREE_TYPE (memref)))
	return false;
      else
	{
	  tree offset = TREE_OPERAND (memref, 1);
	  tree num;

	  if (!is_result_of_mult (offset, &num, ctype.struct_size))
	    return false;

	  if (!is_ctype_p (DECL_CONTEXT (field)))
	    return false;
	}
    }
  else if (TREE_CODE (memref) != VAR_DECL)
    return false;
  else if (is_ctype_p (TREE_TYPE (memref)))
    return false;

  return true;
}

tree
ipa_struct_relayout::rewrite_address (tree xhs, gimple_stmt_iterator *gsi)
{
  tree mem_ref = TREE_OPERAND (xhs, 0);
  tree pointer = TREE_OPERAND (mem_ref, 0);
  tree pointer_offset = TREE_OPERAND (mem_ref, 1);
  tree field = TREE_OPERAND (xhs, 1);
  tree opnd_type = pointer_sized_int_node;
  tree step;

  gcc_checking_assert (classify_type (pointer) == CTYPE_PTR);

  if (addr_to_index)
    {
      gcc_checking_assert (TREE_CODE (pointer) == SSA_NAME);
      opnd_type = rewrite_type (TREE_TYPE (pointer));

      if (addr_to_index == ATOI_NORMAL)
	step = gimplify_build2 (gsi, MINUS_EXPR, opnd_type, pointer,
				build_one_cst (opnd_type));
      else
	step = pointer;
    }
  else
    {
      tree pointer_ssa = fold_convert (opnd_type, pointer);
      tree gptr0_ssa = fold_convert (opnd_type, gptr[0]);

      /* Emit gimple _X1 = ptr - gptr0.  */
      step = gimplify_build2 (gsi, MINUS_EXPR, opnd_type, pointer_ssa,
			      gptr0_ssa);

      /* Emit gimple _X2 = _X1 / sizeof (struct).  */
      step = gimplify_build2 (gsi, TRUNC_DIV_EXPR, opnd_type, step,
			      ctype.struct_size);
    }

  unsigned field_num = ctype.calculate_field_num (field);
  gcc_assert (field_num > 0 && field_num <= ctype.field_count);

  /* Emit gimple _X3 = _X2 * sizeof (member).  */
  step = gimplify_build2 (gsi, MULT_EXPR, opnd_type, step,
			  GPTR_SIZE (field_num));

  /* Emit gimple _X4 = gptr[I].  */
  tree gptr_field_ssa = create_ssa (gptr[field_num], gsi);
  tree new_address_type = TREE_TYPE (gptr[field_num]);
  tree new_address = make_ssa_name (new_address_type);
  tree new_type = TREE_TYPE (new_address_type);
  HOST_WIDE_INT new_offset = 0;
  gassign *new_stmt = gimple_build_assign (new_address, POINTER_PLUS_EXPR,
					   gptr_field_ssa, step);
  gsi_insert_before (gsi, new_stmt, GSI_SAME_STMT);

  /* MEM_REF with nonzero offset like
       MEM[ptr + sizeof (struct)] = 0B
     should be transformed to
       MEM[gptr + sizeof (member)] = 0B
  */
  if (!integer_zerop (pointer_offset))
    {
      tree num = NULL_TREE;
      bool res = is_result_of_mult (pointer_offset, &num, ctype.struct_size);
      HOST_WIDE_INT new_size = tree_to_shwi (TYPE_SIZE_UNIT (new_type));

      gcc_checking_assert (res);
      new_offset = tree_to_shwi (num) * new_size;
    }

  /* Update mem_ref pointer.  */
  TREE_OPERAND (mem_ref, 0) = new_address;
  TREE_OPERAND (mem_ref, 1) = build_int_cst (new_address_type, new_offset);

  /* Update mem_ref TREE_TYPE.  */
  TREE_TYPE (mem_ref) = new_type;

  return mem_ref;
}

void
ipa_struct_relayout::rewrite_memref (tree &memref, gimple *stmt)
{
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);

  gcc_checking_assert (TREE_CODE (memref) == COMPONENT_REF);
  gcc_checking_assert (is_gimple_assign (stmt));

  if (is_candidate (memref))
    {
      memref = rewrite_address (memref, &gsi);
      update_stmt (stmt);
    }
  else if (addr_to_index && classify_type (memref))
    rewrite_expr (memref);
}

bool
ipa_struct_relayout::analyze_assign (gassign *stmt)
{
  tree lhs = gimple_assign_lhs (stmt);
  tree rhs1 = gimple_assign_rhs1 (stmt);
  tree rhs2 = gimple_assign_rhs2 (stmt);
  tree rhs3 = NULL_TREE;
  enum tree_code code = gimple_assign_rhs_code (stmt);
  int lhs_kind = classify_type (lhs);

  if (lhs_kind > CTYPE_PTR)
    return false;

  if (TREE_CODE (lhs) != SSA_NAME)
    {
      gcc_assert (gimple_vdef (stmt));

      if (!analyze_memref (lhs))
	return false;
    }
  else if (gimple_vuse (stmt))
    {
      gcc_assert (!gimple_vdef (stmt));

      if (!analyze_memref (rhs1))
	return false;

      return lhs_kind == classify_type (rhs1);
    }

  switch (code)
    {
    case SSA_NAME:
    CASE_CONVERT:
    case INTEGER_CST:
    case CONSTRUCTOR:
      if (lhs_kind == CTYPE_PTR)
	return analyze_expr (rhs1) || TREE_CLOBBER_P (rhs1);

      if (refer_ctype_p (rhs1))
	return false;

      gcc_assert (gimple_vuse (stmt));
      break;

    case POINTER_PLUS_EXPR:
      if (lhs_kind == CTYPE_PTR && analyze_ssa (rhs1))
	{
	  tree num = NULL_TREE;

	  return is_result_of_mult (rhs2, &num, ctype.struct_size);
	}
      return false;

    case MIN_EXPR:
    case MAX_EXPR:
      if (lhs_kind == CTYPE_PTR)
	return analyze_expr_pair (rhs1, rhs2);
      return false;

    case NE_EXPR:
    case EQ_EXPR:
    case LE_EXPR:
    case LT_EXPR:
    case GE_EXPR:
    case GT_EXPR:
      gcc_assert (lhs_kind != CTYPE_PTR);
      return analyze_expr_pair (rhs1, rhs2);

    case POINTER_DIFF_EXPR:
      gcc_assert (lhs_kind != CTYPE_PTR);
      return analyze_ssa (rhs1) && analyze_ssa (rhs2);

    case COND_EXPR:
      if (COMPARISON_CLASS_P (rhs1) && refer_ctype_p (rhs1)
	  && !analyze_expr_pair (TREE_OPERAND (rhs1, 0),
				 TREE_OPERAND (rhs1, 1)))
	return false;

      rhs3 = gimple_assign_rhs3 (stmt);
      if (lhs_kind == CTYPE_PTR)
	return analyze_expr_pair (rhs2, rhs3);
      return !refer_ctype_p (rhs2) && !refer_ctype_p (rhs3);

    default:
      return false;
    }

  return true;
}

bool
ipa_struct_relayout::rewrite_pointer_diff (gassign *stmt)
{
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  tree lhs = gimple_assign_lhs (stmt);
  tree type = TREE_TYPE (lhs);
  tree rhs1 = gimple_assign_rhs1 (stmt);
  tree rhs2 = gimple_assign_rhs2 (stmt);
  tree diff;
  gimple *use_stmt;
  imm_use_iterator imm_iter;

  gcc_checking_assert (analyze_ssa (rhs1) && analyze_ssa (rhs2));

  diff = fold_build2 (MINUS_EXPR, index_type, rhs1, rhs2);
  diff = fold_convert (type, diff);
  diff = force_gimple_operand_gsi (&gsi, diff, true, NULL, true,
				   GSI_SAME_STMT);

  gimple_assign_set_rhs1 (stmt, diff);
  gimple_assign_set_rhs2 (stmt, fold_convert (type, ctype.struct_size));
  gimple_assign_set_rhs_code (stmt, MULT_EXPR);
  update_stmt (stmt);

  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, lhs)
    {
      if (is_gimple_assign (use_stmt)
	  && gimple_assign_rhs_code (use_stmt) == EXACT_DIV_EXPR
	  && gimple_assign_rhs1 (use_stmt) == lhs
	  && tree_int_cst_equal (gimple_assign_rhs2 (use_stmt),
				 ctype.struct_size))
	{
	  gimple_assign_set_rhs1 (use_stmt, diff);
	  gimple_assign_set_rhs2 (use_stmt, NULL_TREE);
	  gimple_assign_set_rhs_code (use_stmt, TREE_CODE (diff));
	  gimple_set_num_ops (use_stmt, 2);
	  update_stmt (use_stmt);
	}
    }

  return false;
}

/*       COMPONENT_REF  = exp  =>     MEM_REF = exp
	  /       \		      /     \
       MEM_REF   field		    gptr   offset
       /    \
   pointer offset
*/

bool
ipa_struct_relayout::rewrite_assign (gassign *stmt)
{
  gimple_stmt_iterator prev_gsi;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Rewrite assign:\n");
      print_gimple_stmt (dump_file, stmt, 0);
      fprintf (dump_file, "to\n");

      prev_gsi = gsi_for_stmt (stmt);
      gsi_prev (&prev_gsi);
    }

  tree &lhs = *gimple_assign_lhs_ptr (stmt);
  tree &rhs1 = *gimple_assign_rhs1_ptr (stmt);
  enum tree_code code = gimple_assign_rhs_code (stmt);

  if (TREE_CODE (lhs) != SSA_NAME)
    {
      gcc_assert (gimple_vdef (stmt));
      rewrite_memref (lhs, stmt);
    }
  else if (gimple_vuse (stmt))
    {
      gcc_assert (!gimple_vdef (stmt));
      rewrite_memref (rhs1, stmt);
      goto end;
    }

  if (!addr_to_index)
    goto end;

  switch (code)
    {
    CASE_CONVERT:
    case INTEGER_CST:
    case CONSTRUCTOR:
      if (!gimple_vdef (stmt) || classify_type (rhs1))
	rewrite_expr (rhs1);
      break;

    case POINTER_PLUS_EXPR:
      {
	gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
	tree num = NULL_TREE;
	bool res = is_result_of_mult (gimple_assign_rhs2 (stmt), &num,
				      ctype.struct_size);
	gcc_checking_assert (res);

	num = fold_convert (index_type, num);
	num = force_gimple_operand_gsi (&gsi, num, false, NULL_TREE,
					true, GSI_SAME_STMT);
	gimple_assign_set_rhs2 (stmt, num);
	gimple_assign_set_rhs_code (stmt, PLUS_EXPR);
	update_stmt (stmt);
      }
      break;

    case MIN_EXPR:
    case MAX_EXPR:
    case NE_EXPR:
    case EQ_EXPR:
    case LE_EXPR:
    case LT_EXPR:
    case GE_EXPR:
    case GT_EXPR:
      {
	tree &rhs2 = *gimple_assign_rhs2_ptr (stmt);

	rewrite_expr (rhs1);
	rewrite_expr (rhs2);
      }
      break;

    case POINTER_DIFF_EXPR:
      rewrite_pointer_diff (stmt);
      break;

    case COND_EXPR:
      if (COMPARISON_CLASS_P (rhs1) && refer_ctype_p (rhs1))
	{
	  rewrite_expr (TREE_OPERAND (rhs1, 0));
	  rewrite_expr (TREE_OPERAND (rhs1, 1));
	}

      if (classify_type (lhs))
	{
	  rewrite_expr (*gimple_assign_rhs2_ptr (stmt));
	  rewrite_expr (*gimple_assign_rhs3_ptr (stmt));
	}
      break;

    default:
      break;
    }

end:
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      if (gsi_end_p (prev_gsi))
	prev_gsi = gsi_start_bb (gimple_bb (stmt));
      else
	gsi_next (&prev_gsi);

      for (; ; gsi_next (&prev_gsi))
	{
	  gimple *prev_stmt = gsi_stmt (prev_gsi);

	  print_gimple_stmt (dump_file, prev_stmt, 0);
	  if (prev_stmt == stmt)
	    break;
	}
      fprintf (dump_file, "\n");
    }
  return false;
}

/* The trigger point of CSR: to find whether it is beneficial to do complete
   struct relayout.  If only a few number of fields are accessed in a loop, it
   should be beneficial, otherwise it should be non-beneficial.  */

bool
ipa_struct_relayout::find_hot_access (void)
{
  unsigned i, j;
  srfunction *srfn;
  int num_good = 0, num_bad = 0;

  /* If the number of fields accessed in a loop is less equal to the threshold,
     we think it is beneficial.  */
  int benefit_threshold = ctype.field_count >> 2;
  gcc_checking_assert (benefit_threshold >= 1);

  FOR_EACH_VEC_ELT (sr->functions, i, srfn)
    {
      cfun_context ctx (srfn->node);

      calculate_dominance_info (CDI_DOMINATORS);
      loop_optimizer_init (LOOPS_NORMAL);

      for (auto loop : loops_list (cfun, LI_ONLY_INNERMOST))
	{
	  hash_set<tree> seen_flds;
	  basic_block *bbs = get_loop_body (loop);

	  for (j = 0; j < loop->num_nodes; j++)
	    {
	      basic_block bb = bbs[j];

	      /* Scan the block to find read and writes for all dco_fields. */
	      for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si);
		   gsi_next (&si))
		{
		  gimple *stmt = gsi_stmt (si);
		  if (!is_gimple_assign (stmt) || gimple_num_ops (stmt) != 2)
		    continue;

		  tree lhs = gimple_assign_lhs (stmt);
		  tree rhs = gimple_assign_rhs1 (stmt);

		  tree field = NULL_TREE;
		  if (is_candidate (lhs))
		    field = TREE_OPERAND (lhs, 1);
		  else if (is_candidate (rhs))
		    field = TREE_OPERAND (rhs, 1);
		  else
		    continue;

		  seen_flds.add (field);
		}
	    }
	  free (bbs);

	  int num_flds = seen_flds.elements ();
	  if (num_flds > 0)
	    {
	      num_flds <= benefit_threshold ? num_good++ : num_bad++;

	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "Found %d fields in loop %d (%s)\n",
			   num_flds, loop->num, srfn->node->name ());
		}
	    }
	}
      free_dominance_info (CDI_DOMINATORS);
      loop_optimizer_finalize ();
    }
  if (!num_good)
    return false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Number of beneficial loops: %d\n", num_good);
      fprintf (dump_file, "Number of non-beneficial loops: %d\n", num_bad);
    }

  if (num_bad == 0)
    num_bad = 1;
  return num_good > num_bad * 2;
}

unsigned int
ipa_struct_relayout::execute (void)
{
  if (!analyze ())
    return 0;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Complete Struct Relayout Type: ");
      print_generic_expr (dump_file, ctype.type);
      fprintf (dump_file, "\n");
    }
  transformed++;

  create_global_ptrs ();
  return rewrite ();
}

} // anon namespace

namespace {

/* Methods for ipa_struct_reorg.  */

/* Dump all of the recorded types to file F. */

void
ipa_struct_reorg::dump_types (FILE *f)
{
  unsigned i;
  srtype *type;
  FOR_EACH_VEC_ELT (types, i, type)
    {
      fprintf (f, "======= the %dth type: ======\n", i);
      type->dump(f);
      fprintf (f, "\n");
    }
}

/* Dump all of the recorded types to file F. */

void
ipa_struct_reorg::dump_types_escaped (FILE *f)
{
  unsigned i;
  srtype *type;
  FOR_EACH_VEC_ELT (types, i, type)
    {
      if (type->has_escaped ())
	{
	  type->simple_dump (f);
	  fprintf (f, " has escaped. \n");
	}
    }
  fprintf (f, "\n");
}


/* Dump all of the record functions to file F. */

void
ipa_struct_reorg::dump_functions (FILE *f)
{
  unsigned i;
  srfunction *fn;

  globals.dump (f);
  fprintf (f, "\n\n");
  FOR_EACH_VEC_ELT (functions, i, fn)
    {
      fn->dump(f);
      fprintf (f, "\n");
    }
  fprintf (f, "\n\n");
}

/* Find the recorded srtype corresponding to TYPE.  */

srtype *
ipa_struct_reorg::find_type (tree type)
{
  unsigned i;
  /* Get the main variant as we are going
     to find that type only. */
  type = TYPE_MAIN_VARIANT (type);

  srtype *type1;
  // Search for the type to see if it is already there.
  FOR_EACH_VEC_ELT (types, i, type1)
    {
      if (types_compatible_p (type1->type, type))
	return type1;
    }
  return NULL;
}

/*  Is TYPE a pointer to another pointer. */

bool isptrptr (tree type)
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

/* Record field type.  */

void
ipa_struct_reorg::record_field_type (tree field, srtype *base_srtype)
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
ipa_struct_reorg::record_struct_field_types (tree base_type,
					     srtype *base_srtype)
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
ipa_struct_reorg::record_type (tree type)
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
      fprintf (dump_file, "Recording new type: ");
      print_generic_expr (dump_file, type);
      fprintf (dump_file, "(%u)\n", typeuid);
    }

  type1 = new srtype (type);
  types.safe_push (type1);

  record_struct_field_types (type, type1);

  return type1;
}

/* Record var DECL; optionally specify the argument number in a function. */

srdecl *
ipa_struct_reorg::record_var (tree decl, int arg)
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
	  gcc_assert (current_function);
          sd = current_function->record_decl (type, decl, arg);
	}

      /* Separate instance is hard to trace in complete struct
	 relayout optimization.  */
      if ((current_mode == COMPLETE_STRUCT_RELAYOUT)
	  && TREE_CODE (TREE_TYPE (decl)) == RECORD_TYPE)
	{
	  type->mark_unsupported ();
	}
    }

  return sd;
}

/* Mark the inner type of TYPE as unsupported. */

void
ipa_struct_reorg::mark_type_unsupported (tree type, gimple *stmt)
{
  if (!handled_type (type))
    return;
  srtype *stype = record_type (inner_type (type));
  if (!stype)
    return;

  stype->mark_unsupported (stmt);
}

/* Find void* ssa_names which are used inside MEM[]. */

void
ipa_struct_reorg::find_var (tree expr)
{
  tree base;
  bool indirect;
  srtype *type;
  srfield *field;
  bool realpart, imagpart, address;
  /* The should_create flag is true, the declaration can be recorded.  */
  get_type_field (expr, base, indirect, type, field, realpart, imagpart,
		  address, true);
}

void
ipa_struct_reorg::find_vars (gimple *stmt)
{
  gasm *astmt;
  switch (gimple_code (stmt))
    {
    case GIMPLE_ASSIGN:
      if (gimple_assign_rhs_class (stmt) == GIMPLE_SINGLE_RHS
	  || gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR
	  || gimple_assign_rhs_code (stmt) == NOP_EXPR)
	{
	  tree lhs = gimple_assign_lhs (stmt);
	  tree rhs = gimple_assign_rhs1 (stmt);
	  find_var (gimple_assign_lhs (stmt));
	  find_var (gimple_assign_rhs1 (stmt));

	  /* Add a safe func mechanism.  */
	  bool l_find = true;
	  bool r_find = true;

	  if ((TREE_CODE (lhs) == SSA_NAME)
	      && VOID_POINTER_P (TREE_TYPE (lhs))
	      && handled_type (TREE_TYPE (rhs)) && l_find)
	    {
	      srtype *t = find_type (inner_type (TREE_TYPE (rhs)));
	      srdecl *d = find_decl (lhs);
	      if (!d && t)
		{
		  current_function->record_decl (t, lhs, -1,
			isptrptr (TREE_TYPE (rhs)) ? TREE_TYPE (rhs) : NULL);
		  tree var = SSA_NAME_VAR (lhs);
		  if (var && VOID_POINTER_P (TREE_TYPE (var)))
		    current_function->record_decl (t, var, -1,
			isptrptr (TREE_TYPE (rhs)) ? TREE_TYPE (rhs) : NULL);
		}
	    }
	  /* find void ssa_name such as:
	     void * _1; 
             struct a * _2;
	     _2 = _1 + _3; 
             _1 = calloc (100, 40).  */
	  if (TREE_CODE (rhs) == SSA_NAME
	      && VOID_POINTER_P (TREE_TYPE (rhs))
	      && handled_type (TREE_TYPE (lhs)) && r_find)
	    {
	      srtype *t = find_type (inner_type (TREE_TYPE (lhs)));
	      srdecl *d = find_decl (rhs);
	      if (!d && t)
		{
		  current_function->record_decl (t, rhs, -1,
			isptrptr (TREE_TYPE (lhs)) ? TREE_TYPE (lhs) : NULL);
		  tree var = SSA_NAME_VAR (rhs);
		  if (var && VOID_POINTER_P (TREE_TYPE (var)))
		    current_function->record_decl (t, var, -1,
			isptrptr (TREE_TYPE (lhs)) ? TREE_TYPE (lhs) : NULL);
		}
	    }
	}
      else if ((current_mode == COMPLETE_STRUCT_RELAYOUT)
	       && gimple_assign_rhs_code (stmt) == EQ_EXPR)
	{
	  find_var (gimple_assign_rhs1 (stmt));
	  find_var (gimple_assign_rhs2 (stmt));
	}
      else
	{
	  /* Because we won't handle these stmts in rewrite phase, mark on
	     the types.  */
	  mark_type_unsupported (TREE_TYPE (gimple_assign_lhs (stmt)), stmt);
	  for (unsigned j = 1; j < gimple_num_ops (stmt); ++j)
	    mark_type_unsupported (TREE_TYPE (gimple_op (stmt, j)), stmt);
	}
      break;

    case GIMPLE_CALL:
      if (gimple_call_lhs (stmt))
	find_var (gimple_call_lhs (stmt));

      if (gimple_call_chain (stmt))
	find_var (gimple_call_chain (stmt));

      for (unsigned i = 0; i < gimple_call_num_args (stmt); i++)
	find_var (gimple_call_arg (stmt, i));
      break;

    case GIMPLE_ASM:
      astmt = as_a <gasm*>(stmt);
      for (unsigned i = 0; i < gimple_asm_ninputs (astmt); i++)
	find_var (TREE_VALUE (gimple_asm_input_op (astmt, i)));
      for (unsigned i = 0; i < gimple_asm_noutputs (astmt); i++)
	find_var (TREE_VALUE (gimple_asm_output_op (astmt, i)));
      break;

    case GIMPLE_RETURN:
      {
	tree expr = gimple_return_retval (as_a<greturn*>(stmt));
	if (expr)
          find_var (expr);
      }
      break;

    default:
      break;
    }
}

/* Maybe record access of statement for further analysis. */

void
ipa_struct_reorg::maybe_record_stmt (gimple *stmt)
{
  switch (gimple_code (stmt))
    {
    case GIMPLE_ASSIGN:
      maybe_record_assign (as_a <gassign *> (stmt));
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

/* Calculate the multiplier.  */

static bool
calculate_mult_num (tree arg, tree *num, tree struct_size)
{
  gcc_assert (TREE_CODE (arg) == INTEGER_CST);
  bool sign = false;
  HOST_WIDE_INT size = TREE_INT_CST_LOW (arg);
  if (size < 0)
    {
      size = -size;
      sign = true;
    }
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

/* Trace and calculate the multiplier of PLUS_EXPR.  */

static bool
trace_calculate_plus (gimple *size_def_stmt, tree *num, tree struct_size)
{
  gcc_assert (gimple_assign_rhs_code (size_def_stmt) == PLUS_EXPR);

  tree num1 = NULL_TREE;
  tree num2 = NULL_TREE;
  tree arg0 = gimple_assign_rhs1 (size_def_stmt);
  tree arg1 = gimple_assign_rhs2 (size_def_stmt);
  if (!is_result_of_mult (arg0, &num1, struct_size) || num1 == NULL_TREE)
    {
      return false;
    }
  if (!is_result_of_mult (arg1, &num2, struct_size) || num2 == NULL_TREE)
    {
      return false;
    }
  *num = size_binop (PLUS_EXPR, num1, num2);
  return true;
}

/* Trace and calculate the multiplier of MULT_EXPR.  */

static bool
trace_calculate_mult (gimple *size_def_stmt, tree *num, tree struct_size)
{
  gcc_assert (gimple_assign_rhs_code (size_def_stmt) == MULT_EXPR);

  tree arg0 = gimple_assign_rhs1 (size_def_stmt);
  tree arg1 = gimple_assign_rhs2 (size_def_stmt);
  tree num1 = NULL_TREE;

  if (is_result_of_mult (arg0, &num1, struct_size) && num1 != NULL_TREE)
    {
      *num = size_binop (MULT_EXPR, arg1, num1);
      return true;
    }
  if (is_result_of_mult (arg1, &num1, struct_size) && num1 != NULL_TREE)
    {
      *num = size_binop (MULT_EXPR, arg0, num1);
      return true;
    }
  *num = NULL_TREE;
  return false;
}

/* This function checks whether ARG is a result of multiplication
   of some number by STRUCT_SIZE.  If yes, the function returns true
   and this number is filled into NUM.  */

static bool
is_result_of_mult (tree arg, tree *num, tree struct_size)
{
  if (!struct_size
      || TREE_CODE (struct_size) != INTEGER_CST
      || integer_zerop (struct_size))
    return false;

  /* If we have a integer, just check if it is a multiply of STRUCT_SIZE.  */
  if (TREE_CODE (arg) == INTEGER_CST)
    {
      return calculate_mult_num (arg, num, struct_size);
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
	  return trace_calculate_plus (size_def_stmt, num, struct_size);
	}
      else if (rhs_code == MULT_EXPR)
	{
	  return trace_calculate_mult (size_def_stmt, num, struct_size);
	}
      else if (rhs_code == SSA_NAME)
	{
	  arg = gimple_assign_rhs1 (size_def_stmt);
	  size_def_stmt = SSA_NAME_DEF_STMT (arg);
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

/* Return TRUE if STMT is an allocation statement that is handled. */

bool
ipa_struct_reorg::handled_allocation_stmt (gimple *stmt)
{
  if ((current_mode == COMPLETE_STRUCT_RELAYOUT)
      && gimple_call_builtin_p (stmt, BUILT_IN_CALLOC))
    return true;
  if ((current_mode == NORMAL)
      && (gimple_call_builtin_p (stmt, BUILT_IN_REALLOC)
	  || gimple_call_builtin_p (stmt, BUILT_IN_MALLOC)
	  || gimple_call_builtin_p (stmt, BUILT_IN_CALLOC)
	  || gimple_call_builtin_p (stmt, BUILT_IN_ALIGNED_ALLOC)
	  || gimple_call_builtin_p (stmt, BUILT_IN_ALLOCA)
	  || gimple_call_builtin_p (stmt, BUILT_IN_ALLOCA_WITH_ALIGN)))
    return true;
  return false;
}


/* Returns the allocated size / T size for STMT.  That is the number of
   elements in the array allocated.   */

tree
ipa_struct_reorg::allocate_size (srtype *type, srdecl *decl, gimple *stmt)
{
  if (!stmt
      || gimple_code (stmt) != GIMPLE_CALL
      || !handled_allocation_stmt (stmt))
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\nNot an allocate statement:\n");
	  print_gimple_stmt (dump_file, stmt, 0);
	  fprintf (dump_file, "\n");
	}
      return NULL;
    }

  if (type->has_escaped ())
    return NULL;

  tree struct_size = TYPE_SIZE_UNIT (type->type);

  /* Specify the correct size to relax multi-layer pointer.  */
  if (TREE_CODE (decl->decl) == SSA_NAME && isptrptr (decl->orig_type))
    {
      struct_size = TYPE_SIZE_UNIT (decl->orig_type);
    }

  tree size = gimple_call_arg (stmt, 0);

  if (gimple_call_builtin_p (stmt, BUILT_IN_REALLOC)
      || gimple_call_builtin_p (stmt, BUILT_IN_ALIGNED_ALLOC))
    size = gimple_call_arg (stmt, 1);
  else if (gimple_call_builtin_p (stmt, BUILT_IN_CALLOC))
    {
      tree arg1;
      arg1 = gimple_call_arg (stmt, 1);
      /* Check that second argument is a constant equal to the size of structure.  */
      if (operand_equal_p (arg1, struct_size, 0))
	return size;
      /* ??? Check that first argument is a constant
      equal to the size of structure.  */
      /* If the allocated number is equal to the value of struct_size,
	 the value of arg1 is changed to the allocated number.  */
      if (operand_equal_p (size, struct_size, 0))
	return arg1;
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\ncalloc the correct size:\n");
	  print_gimple_stmt (dump_file, stmt, 0);
	  fprintf (dump_file, "\n");
	}
      return NULL;
    }

  tree num;
  if (!is_result_of_mult (size, &num, struct_size))
    return NULL;

  return num;

}


void
ipa_struct_reorg::maybe_record_other_side (tree side, tree other)
{
  gcc_assert (TREE_CODE (side) == SSA_NAME || TREE_CODE (side) == ADDR_EXPR);
  srtype *type = NULL;
  if (handled_type (TREE_TYPE (other)))
    type = record_type (inner_type (TREE_TYPE (other)));
  if (TREE_CODE (side) == ADDR_EXPR)
    side = TREE_OPERAND (side, 0);
  srdecl *d = find_decl (side);
  if (!type)
    return;

  if (!d)
    {
      if (VOID_POINTER_P (TREE_TYPE (side))
	  && TREE_CODE (side) == SSA_NAME)
	{
	  /* The type is other, the declaration is side.  */
	  current_function->record_decl (type, side, -1,
		isptrptr (TREE_TYPE (other)) ? TREE_TYPE (other) : NULL);
	}
    }
}

/* Record accesses in an assignment statement STMT.  */

void
ipa_struct_reorg::maybe_record_assign (gassign *stmt)
{
  if (gimple_clobber_p (stmt))
    {
      return;
    }

  if (gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR)
    {
      return;
    }
  /* Copies, References, Taking addresses. */
  if (gimple_assign_rhs_class (stmt) == GIMPLE_SINGLE_RHS)
    {
      tree lhs = gimple_assign_lhs (stmt);
      tree rhs = gimple_assign_rhs1 (stmt);
      /* a = &b.c  */
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
  tree size = isptrptr (TREE_TYPE (tmp))
			? TYPE_SIZE_UNIT (TREE_TYPE (tmp))
			: TYPE_SIZE_UNIT (inner_type (TREE_TYPE (tmp)));
  ret = is_result_of_mult (field_off, num, size);
  return ret;
}

tree
get_ref_base_and_offset (tree &e, HOST_WIDE_INT &offset,
			 bool &realpart, bool &imagpart,
			 tree &accesstype, tree *num)
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

/* Return true if EXPR was accessing the whole type T.  */

bool
ipa_struct_reorg::wholeaccess (tree expr, tree base, tree accesstype, srtype *t)
{
  if (expr == base)
    return true;

  if (TREE_CODE (expr) == ADDR_EXPR && TREE_OPERAND (expr, 0) == base)
    return true;

  if (!accesstype)
    return false;

  if (!types_compatible_p (TREE_TYPE (expr), TREE_TYPE (accesstype)))
    return false;

  if (!handled_type (TREE_TYPE (expr)))
    return false;

  srtype *other_type = find_type (inner_type (TREE_TYPE (expr)));

  if (t == other_type)
    return true;

  return false;
}

bool
ipa_struct_reorg::get_type_field (tree expr, tree &base, bool &indirect,
				  srtype *&type, srfield *&field,
				  bool &realpart, bool &imagpart, bool &address,
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
  base = get_ref_base_and_offset (expr, offset, realpart, imagpart,
				  accesstype, &num);

  /* Variable access, unkown type. */
  if (base == NULL)
    return false;

  if (TREE_CODE (base) == ADDR_EXPR)
    {
      address = true;
      base = TREE_OPERAND (base, 0);
    }

  if (offset != 0 && accesstype)
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Non zero offset (%d) with MEM.\n", (int)offset);
	  print_generic_expr (dump_file, expr);
	  fprintf (dump_file, "\n");
	  print_generic_expr (dump_file, base);
	  fprintf (dump_file, "\n");
	}
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
   * it.  */
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

      if (!(VOID_POINTER_P (TREE_TYPE (base))))
	{
	  return false;
	}
      if (TREE_CODE (base) == SSA_NAME)
	{
	  /* Add auxiliary information of the multi-layer pointer
	     type.  */
	  current_function->record_decl (t, base, -1,
					 isptrptr (accesstype) ? accesstype
							       : NULL);
	}
    }
  else if (!d)
    return false;
  else
    t = d->type;

  if (t->has_escaped () || mark_as_bit_field)
    {
      return false;
    }

  if (current_mode != NORMAL
      && (TREE_CODE (expr) == MEM_REF) && (offset != 0))
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

  srfield *f = t->find_field (offset);
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
  if (!types_compatible_p (f->fieldtype, TREE_TYPE (expr)))
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
ipa_struct_reorg::find_function (cgraph_node *node)
{
  for (unsigned i = 0; i < functions.length (); i++)
    if (functions[i]->node == node)
	return functions[i];
  return NULL;
}

void
ipa_struct_reorg::check_type_and_push (tree newdecl, srdecl *decl,
				       vec<srdecl *> &worklist)
{
  srtype *type = decl->type;
  if (integer_zerop (newdecl))
    return;

  if (TREE_CODE (newdecl) == ADDR_EXPR)
    return;

  srdecl *d = find_decl (newdecl);
  if (!d)
    {
      if (TREE_CODE (newdecl) == INTEGER_CST)
	{
	  return;
	}
      if (!VOID_POINTER_P (TREE_TYPE (newdecl))
	  || DECL_P (newdecl))
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
      d = current_function->record_decl (type, newdecl, -1);
      worklist.safe_push (d);
      return;
    }

  /* Only add to the worklist if the decl is a SSA_NAME.  */
  if (TREE_CODE (newdecl) == SSA_NAME)
    worklist.safe_push (d);
}

void
ipa_struct_reorg::check_alloc_num (gimple *stmt, srtype *type)
{
  if (current_mode == COMPLETE_STRUCT_RELAYOUT
      && handled_allocation_stmt (stmt))
    {
      tree arg0 = gimple_call_arg (stmt, 0);
      basic_block bb = gimple_bb (stmt);
      cgraph_node *node = current_function->node;
      if (integer_onep (arg0))
	{
	  /* Actually NOT an array, but may ruin other array.  */
	  type->has_alloc_array = -1;
	}
      else if (bb->loop_father != NULL
	       && loop_outer (bb->loop_father) != NULL)
	{
	  /* The allocation is in a loop.  */
	  type->has_alloc_array = -2;
	}
      else if (node->callers != NULL)
	{
	  type->has_alloc_array = -3;
	}
      else
	{
	  type->has_alloc_array = type->has_alloc_array < 0
				  ? type->has_alloc_array
				  : type->has_alloc_array + 1;
	}
    }
}

/* Check the definition of gimple assign.  */

void
ipa_struct_reorg::check_definition_assign (srdecl *decl, vec<srdecl*> &worklist)
{
  tree ssa_name = decl->decl;
  gimple *stmt = SSA_NAME_DEF_STMT (ssa_name);
  gcc_assert (gimple_code (stmt) == GIMPLE_ASSIGN);
  /* a) if the SSA_NAME is sourced from a pointer plus, record the pointer.  */
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
ipa_struct_reorg::check_definition_call (srdecl *decl, vec<srdecl*> &worklist)
{
  tree ssa_name = decl->decl;
  srtype *type = decl->type;
  gimple *stmt = SSA_NAME_DEF_STMT (ssa_name);
  gcc_assert (gimple_code (stmt) == GIMPLE_CALL);

  /* For realloc, check the type of the argument.  */
  if (gimple_call_builtin_p (stmt, BUILT_IN_REALLOC))
    {
      check_type_and_push (gimple_call_arg (stmt, 0), decl, worklist);
    }

  check_alloc_num (stmt, type);
  return;
}

/*
  2) Check SSA_NAMEs for non type usages (source or use) (worklist of srdecl)
     a) if the SSA_NAME is sourced from a pointer plus, record the pointer and
	check to make sure the addition was a multiple of the size.
	check the pointer type too.
     b) If the name is sourced from an allocation check the allocation
	i) Add SSA_NAME (void*) to the worklist if allocated from realloc
     c) if the name is from a param, make sure the param type was of the original type
     d) if the name is from a cast/assignment, make sure it is used as that type or void*
	i) If void* then push the ssa_name into worklist
*/
void
ipa_struct_reorg::check_definition (srdecl *decl, vec<srdecl*> &worklist)
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
  /* If the SSA_NAME is sourced from an inline-asm, the type is escaping.  */
  if (gimple_code (stmt) == GIMPLE_ASM)
    {
      return;
    }

  /* If the SSA_NAME is sourced from a PHI check add each name to the worklist and
     check to make sure they are used correctly.  */
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
ipa_struct_reorg::check_other_side (srdecl *decl, tree other,
				    vec<srdecl *> &worklist)
{
  if (TREE_CODE (other) == SSA_NAME || DECL_P (other)
      || TREE_CODE (other) == INTEGER_CST)
    {
      check_type_and_push (other, decl, worklist);
    }
}

void
ipa_struct_reorg::check_use (srdecl *decl, gimple *stmt, vec<srdecl*> &worklist)
{
  if (gimple_code (stmt) == GIMPLE_RETURN || gimple_code (stmt) == GIMPLE_ASM)
    return;

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
    return;

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
      return;
    }

}

/*
   2) Check SSA_NAMEs for non type usages (source or use) (worklist of srdecl)
	d) if the name is used in a cast/assignment, make sure it is used as that type or void*
	  i) If void* then push the ssa_name into worklist
	e) if used in conditional check the other side
	  i) If the conditional is non NE/EQ then mark the type as non rejecting
	f) Check if the use in a Pointer PLUS EXPR Is used by multiplication of its size
  */
void
ipa_struct_reorg::check_uses (srdecl *decl, vec<srdecl*> &worklist)
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
ipa_struct_reorg::record_function (cgraph_node *node)
{
  function *fn;
  tree parm, var;
  unsigned int i;
  srfunction *sfn;

  sfn = new srfunction (node);
  functions.safe_push (sfn);

  if (dump_file  && (dump_flags & TDF_DETAILS))
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

  current_function = sfn;
  basic_block bb;
  gimple_stmt_iterator si;

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
  for (parm = DECL_ARGUMENTS (node->decl), i = 0;
       parm;
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
    {
      current_function = NULL;
      return sfn;
    }

  /* The following order is done for recording stage:
     0) Record all variables/SSA_NAMES that are of struct type
     1) Record MEM_REF/COMPONENT_REFs
	a) Record SSA_NAMEs (void*) and record that as the accessed type.
  */

  cfun_context ctx (fn);

  FOR_EACH_LOCAL_DECL (cfun, i, var)
    {
      if (TREE_CODE (var) != VAR_DECL)
        continue;

      record_var (var);
    }

  for (i = 1; i < num_ssa_names; ++i)
    {
      tree name = ssa_name (i);
      if (!name
          || has_zero_uses (name)
          || virtual_operand_p (name))
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
  for (unsigned i = 0; i < current_function->decls.length (); i++)
    {
      srdecl *decl = current_function->decls[i];
      if (TREE_CODE (decl->decl) == SSA_NAME)
	{
	  decl->visited = false;
	  worklist.safe_push (decl);
	}
    }

  /*
     2) Check SSA_NAMEs for non type usages (source or use) (worklist of srdecl)
	a) if the SSA_NAME is sourced from a pointer plus, record the pointer and
	   check to make sure the addition was a multiple of the size.
	   check the pointer type too.
	b) If the name is sourced from an allocation check the allocation
	  i) Add SSA_NAME (void*) to the worklist if allocated from realloc
	c) if the name is from a param, make sure the param type was of the original type
	d) if the name is used in a cast/assignment, make sure it is used as that type or void*
	  i) If void* then push the ssa_name into worklist
	e) if used in conditional check the other side
	  i) If the conditional is non NE/EQ then mark the type as non rejecting
	f) Check if the use in a POinter PLUS EXPR Is used by multiplication of its size
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

  current_function = NULL;
  return sfn;
}

/* Record all accesses for all types including global variables. */

void
ipa_struct_reorg::record_accesses (void)
{
  varpool_node *var;
  cgraph_node *cnode;

  /* Record global (non-auto) variables first. */
  FOR_EACH_VARIABLE (var)
    {
      if (!var->real_symbol_p ())
	continue;

      /* Record all variables including the accesses inside a variable. */
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Recording global variable: ");
	  print_generic_expr (dump_file, var->decl);
	  fprintf (dump_file, "\n");
	}
      record_var (var->decl);
    }

  FOR_EACH_FUNCTION (cnode)
    {
      if (!cnode->real_symbol_p ())
        continue;

      /* Record accesses inside a function. */
      if(cnode->definition)
	record_function (cnode);
    }

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
}

/* Clear visited on all types.  */

void
ipa_struct_reorg::clear_visited (void)
{
  for (unsigned i = 0; i < types.length (); i++)
    types[i]->visited = false;
}

/* Prune the escaped types and their decls from what was recorded.  */

void
ipa_struct_reorg::prune_escaped_types (bool save_all_types)
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
  for (unsigned i = 0; i < functions.length (); )
    {
      srfunction *function = functions[i];

      /* Prune function arguments of types that escape. */
      for (unsigned j = 0; j < function->args.length ();)
	{
	  if (function->args[j]->type->has_escaped ())
	    function->args.ordered_remove (j);
	  else
	    j++;
	}

      /* Prune global variables that the function uses of types that escape. */
      for (unsigned j = 0; j < function->globals.length ();)
	{
	  if (function->globals[j]->type->has_escaped ())
	    function->globals.ordered_remove (j);
	  else
	    j++;
	}

      /* Prune variables that the function uses of types that escape. */
      for (unsigned j = 0; j < function->decls.length ();)
	{
	  srdecl *decl = function->decls[j];
	  if (decl->type->has_escaped ())
	    {
	      function->decls.ordered_remove (j);
	      delete decl;
	    }
	  else
	    j++;
	}

      /* Prune functions which don't refer to any variables any more.  */
      if (function->args.is_empty ()
	  && function->decls.is_empty ()
	  && function->globals.is_empty ())
	{
	  delete function;
	  functions.ordered_remove (i);
	}
      else
	i++;
    }

  /* Prune globals of types that escape, all references to those decls
     will have been removed in the first loop.  */
  for (unsigned j = 0; j < globals.decls.length ();)
    {
      srdecl *decl = globals.decls[j];
      if (decl->type->has_escaped ())
        {
          globals.decls.ordered_remove (j);
          delete decl;
        }
      else
        j++;
    }

  /* Prune types that escape.  */
  /* First, clean references in records' fields.  */
  for (unsigned i = 0; i < types.length (); i++)
    {
      if (types[i]->has_escaped ())
	continue;

      srfield *field;
      unsigned int j;
      FOR_EACH_VEC_ELT (types[i]->fields, j, field)
	{
	  if (field->type && field->type->has_escaped ())
	    field->type = NULL;
	}
    }

  for (unsigned i = 0; i < types.length ();)
    {
      srtype *type = types[i];

      if (save_all_types)
	all_types.safe_push (type->type);

      if (type->has_escaped ())
	{
	  /* All references to this type should have been removed now.  */
	  delete type;
	  types.ordered_remove (i);
	}
      else
	{
	  i++;
	}
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "==============================================\n\n");
      fprintf (dump_file, "========= all types (after pruning): =========\n\n");
      dump_types (dump_file);
      fprintf (dump_file, "======== all functions (after pruning): ========\n");
      dump_functions (dump_file);
    }
}

/* Analyze all of the types. */

void
ipa_struct_reorg::analyze_types (void)
{
  for (unsigned i = 0; i < types.length (); i++)
    {
      if (!types[i]->has_escaped ())
        types[i]->analyze();
    }
}

/* Create all new types we want to create. */

bool
ipa_struct_reorg::create_new_types (void)
{
  int newtypes = 0;
  clear_visited ();
  for (unsigned i = 0; i < types.length (); i++)
    newtypes += types[i]->create_new_type ();

  if (dump_file)
    {
      if (newtypes)
	fprintf (dump_file, "\nNumber of structures to transform is %d\n", newtypes);
      else
	fprintf (dump_file, "\nNo structures to transform.\n");
    }

  return newtypes != 0;
}

/* Create all the new decls except for the new arguments
   which create_new_functions would have created. */

void
ipa_struct_reorg::create_new_decls (void)
{
  globals.create_new_decls ();
  for (unsigned i = 0; i < functions.length (); i++)
    functions[i]->create_new_decls ();
}

/* Create the new arguments for the function corresponding to NODE. */

void
ipa_struct_reorg::create_new_args (cgraph_node *new_node)
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
      if (!t
	  || t->has_escaped ()
	  || !t->has_new_type ())
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
      adj.param_prefix_index = IPA_PARAM_PREFIX_REORG;
      for (unsigned j = 0; j < max_split && t->newtype[j]; j++)
	{
	  adj.type = reconstruct_complex_type (TREE_TYPE (parm), t->newtype[j]);
	  vec_safe_push (adjs, adj);
	}
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
      unsigned j = 0;
      while (j < max_split && d->newdecl[j])
	j++;
      d->newdecl[j] = new_params[i];
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
  gcc_assert (!type->newtype[1]);
  tree new_name = NULL;
  char *name = NULL;
  if (tname)
    {
      name = concat (tname, ".reorg.0", NULL);
      new_name = get_identifier (name);
      free (name);
    }
  tree newtype1 = reconstruct_complex_type (TREE_TYPE (orig_var), type->newtype[0]);
  chain->newdecl[0] = build_decl (DECL_SOURCE_LOCATION (orig_var),
				  PARM_DECL, new_name, newtype1);
  copy_var_attributes (chain->newdecl[0], orig_var);
  fn->static_chain_decl = chain->newdecl[0];

}

/* Find the refered DECL in the current function or globals.
   If this is a global decl, record that as being used
   in the current function.  */

srdecl *
ipa_struct_reorg::find_decl (tree decl)
{
  srdecl *d;
  d = globals.find_decl (decl);
  if (d)
    {
      /* Record the global usage in the current function.  */
      if (!done_recording && current_function)
	{
	  bool add = true;
	  /* No reason to add it to the current function if it is
	     already recorded as such. */
	  for (unsigned i = 0; i < current_function->globals.length (); i++)
	    {
	      if (current_function->globals[i] == d)
		{
		  add = false;
		  break;
		}
	    }
	  if (add)
	    current_function->globals.safe_push (d);
	}
      return d;
    }
  if (current_function)
    return current_function->find_decl (decl);
  return NULL;
}

/* Create new function clones for the cases where the arguments
   need to be changed.  */

void
ipa_struct_reorg::create_new_functions (void)
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
      new_node = node->create_version_clone_with_body (
				vNULL, NULL, NULL, NULL, NULL,
				"struct_reorg");
      new_node->can_change_signature = node->can_change_signature;
      new_node->make_local ();
      f->newnode = new_node;
      srfunction *n = record_function (new_node);
      current_function = n;
      n->old = f;
      f->newf = n;
      /* Create New arguments. */
      create_new_args (new_node);
      current_function = NULL;
    }
}

bool
ipa_struct_reorg::rewrite_lhs_rhs (tree lhs, tree rhs, tree newlhs[max_split], tree newrhs[max_split])
{
  bool l = rewrite_expr (lhs, newlhs);
  bool r = rewrite_expr (rhs, newrhs);

  /* Handle NULL pointer specially. */
  if (l && !r && integer_zerop (rhs))
    {
      r = true;
      for (unsigned i = 0; i < max_split && newlhs[i]; i++)
	newrhs[i] = fold_convert (TREE_TYPE (newlhs[i]), rhs);
    }

  return l || r;
}

bool
ipa_struct_reorg::rewrite_expr (tree expr, tree newexpr[max_split], bool ignore_missing_decl)
{
  tree base;
  bool indirect;
  srtype *t;
  srfield *f;
  bool realpart, imagpart;
  bool address;

  tree newbase[max_split];
  memset (newexpr, 0, sizeof(tree[max_split]));

  if (TREE_CODE (expr) == CONSTRUCTOR)
    {
      srtype *t = find_type (TREE_TYPE (expr));
      if (!t)
	return false;
      gcc_assert (CONSTRUCTOR_NELTS (expr) == 0);
      if (!t->has_new_type ())
	return false;
      for (unsigned i = 0; i < max_split && t->newtype[i]; i++)
	newexpr[i] = build_constructor (t->newtype[i], NULL);
      return true;
    }

  if (!get_type_field (expr, base, indirect, t, f, realpart, imagpart, address))
    return false;

  /* If the type is not changed, then just return false. */
  if (!t->has_new_type ())
    return false;

  /*  NULL pointer handling is "special".  */
  if (integer_zerop (base))
    {
      gcc_assert (indirect && !address);
      for (unsigned i = 0; i < max_split && t->newtype[i]; i++)
	{
	  tree newtype1 = reconstruct_complex_type (TREE_TYPE (base), t->newtype[i]);
	  newbase[i] = fold_convert (newtype1, base);
	}
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
      memcpy (newbase, d->newdecl, sizeof(d->newdecl));
    }

  if (f == NULL)
    {
      memcpy (newexpr, newbase, sizeof(newbase));
      for (unsigned i = 0; i < max_split && newexpr[i]; i++)
	{
	  if (address)
	    newexpr[i] = build_fold_addr_expr (newexpr[i]);
	  if (indirect)
	    newexpr[i] = build_simple_mem_ref (newexpr[i]);
	  if (imagpart)
	    newexpr[i] = build1 (IMAGPART_EXPR, TREE_TYPE (TREE_TYPE (newexpr[i])), newexpr[i]);
	  if (realpart)
	    newexpr[i] = build1 (REALPART_EXPR, TREE_TYPE (TREE_TYPE (newexpr[i])), newexpr[i]);
	}
      return true;
    }

  tree newdecl = newbase[f->clusternum];
  for (unsigned i = 0; i < max_split && f->newfield[i]; i++)
    {
      tree newbase1 = newdecl;
      if (address)
        newbase1 = build_fold_addr_expr (newbase1);
      if (indirect)
	{
	  newbase1 = build_simple_mem_ref (newbase1);
	}
      newexpr[i] = build3 (COMPONENT_REF, TREE_TYPE (f->newfield[i]),
			   newbase1, f->newfield[i], NULL_TREE);
      if (imagpart)
	newexpr[i] = build1 (IMAGPART_EXPR, TREE_TYPE (TREE_TYPE (newexpr[i])), newexpr[i]);
      if (realpart)
	newexpr[i] = build1 (REALPART_EXPR, TREE_TYPE (TREE_TYPE (newexpr[i])), newexpr[i]);
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "cluster: %d. decl = ", (int)f->clusternum);
	  print_generic_expr (dump_file, newbase1);
	  fprintf (dump_file, "\nnewexpr = ");
	  print_generic_expr (dump_file, newexpr[i]);
	  fprintf (dump_file, "\n");
	}
    }
  return true;
}

bool
ipa_struct_reorg::rewrite_assign (gassign *stmt, gimple_stmt_iterator *gsi)
{
  bool remove = false;
  if (gimple_clobber_p (stmt))
    {
      tree lhs = gimple_assign_lhs (stmt);
      tree newlhs[max_split];
      if (!rewrite_expr (lhs, newlhs))
	return false;
      for (unsigned i = 0; i < max_split && newlhs[i]; i++)
	{
	  tree clobber = build_constructor (TREE_TYPE (newlhs[i]), NULL);
	  TREE_THIS_VOLATILE (clobber) = true;
	  gimple *newstmt = gimple_build_assign (newlhs[i], clobber);
	  gsi_insert_before (gsi, newstmt, GSI_SAME_STMT);
	  remove = true;
	}
      return remove;
    }

  if ((gimple_assign_rhs_code (stmt) == EQ_EXPR
	   || gimple_assign_rhs_code (stmt) == NE_EXPR))
    {
      tree rhs1 = gimple_assign_rhs1 (stmt);
      tree rhs2 = gimple_assign_rhs2 (stmt);
      tree newrhs1[max_split];
      tree newrhs2[max_split];
      tree_code rhs_code = gimple_assign_rhs_code (stmt);
      tree_code code = rhs_code == EQ_EXPR ? BIT_AND_EXPR : BIT_IOR_EXPR;

      if (!rewrite_lhs_rhs (rhs1, rhs2, newrhs1, newrhs2))
	return false;
      tree newexpr = NULL_TREE;
      for (unsigned i = 0; i < max_split && newrhs1[i]; i++)
	{
	  tree expr = gimplify_build2 (gsi, rhs_code, boolean_type_node, newrhs1[i], newrhs2[i]);
          if (!newexpr)
	    newexpr = expr;
	  else
	    newexpr = gimplify_build2 (gsi, code, boolean_type_node, newexpr, expr);
	}

      if (newexpr)
	{
	  newexpr = fold_convert (TREE_TYPE (gimple_assign_lhs (stmt)), newexpr);
	  gimple_assign_set_rhs_from_tree (gsi, newexpr);
	  update_stmt (stmt);
	}
      return false;
    }

  if (gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR)
    {
      tree lhs = gimple_assign_lhs (stmt);
      tree rhs1 = gimple_assign_rhs1 (stmt);
      tree rhs2 = gimple_assign_rhs2 (stmt);
      tree newlhs[max_split];
      tree newrhs[max_split];

      if (!rewrite_lhs_rhs (lhs, rhs1, newlhs, newrhs))
	return false;
      tree size = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (lhs)));
      tree num;
      /* Check if rhs2 is a multiplication of the size of the type. */
      if (!is_result_of_mult (rhs2, &num, size))
	internal_error ("the rhs of pointer was not a multiplicate and it slipped through");

      /* Add the judgment of num, support for POINTER_DIFF_EXPR.
	 _6 = _4 + _5;
	 _5 = (long unsigned int) _3;
	 _3 = _1 - old_2.  */
      num = gimplify_build1 (gsi, NOP_EXPR, sizetype, num);

      for (unsigned i = 0; i < max_split && newlhs[i]; i++)
	{
	  gimple *new_stmt;

	  if (num != NULL)
	    {
	      tree newsize = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (newlhs[i])));
	      newsize = gimplify_build2 (gsi, MULT_EXPR, sizetype, num,
					 newsize);
	      new_stmt = gimple_build_assign (newlhs[i], POINTER_PLUS_EXPR,
					      newrhs[i], newsize);
	    }
	  else
	    {
	      new_stmt = gimple_build_assign (newlhs[i], POINTER_PLUS_EXPR,
					      newrhs[i], rhs2);
	    }
	  gsi_insert_before (gsi, new_stmt, GSI_SAME_STMT);
	  remove = true;
	}
      return remove;
    }

  if (gimple_assign_rhs_class (stmt) == GIMPLE_SINGLE_RHS)
    {
      tree lhs = gimple_assign_lhs (stmt);
      tree rhs = gimple_assign_rhs1 (stmt);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\nrewriting statement:\n");
	  print_gimple_stmt (dump_file, stmt, 0);
	}
      tree newlhs[max_split];
      tree newrhs[max_split];
      if (!rewrite_lhs_rhs (lhs, rhs, newlhs, newrhs))
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    fprintf (dump_file, "Did nothing to statement.\n");
	  return false;
	}

      if (dump_file && (dump_flags & TDF_DETAILS))
	fprintf (dump_file, "replaced with:\n");
      for (unsigned i = 0; i < max_split && (newlhs[i] || newrhs[i]); i++)
	{
	  gimple *newstmt = gimple_build_assign (newlhs[i] ? newlhs[i] : lhs, newrhs[i] ? newrhs[i] : rhs);
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      print_gimple_stmt (dump_file, newstmt, 0);
	      fprintf (dump_file, "\n");
	    }
	  gsi_insert_before (gsi, newstmt, GSI_SAME_STMT);
	  remove = true;
	}
      return remove;
    }

  if ((current_mode == COMPLETE_STRUCT_RELAYOUT)
      && gimple_assign_rhs_code (stmt) == EQ_EXPR)
    {
      tree rhs1 = gimple_assign_rhs1 (stmt);
      tree rhs2 = gimple_assign_rhs2 (stmt);
      tree newrhs1[max_split];
      tree newrhs2[max_split];

      rewrite_expr (rhs1, newrhs1);
      rewrite_expr (rhs2, newrhs2);
      return false;
    }

  if (gimple_assign_cast_p (stmt))
    {
      tree rhs = gimple_assign_rhs1 (stmt);
      tree newrhs[max_split];
      if (!rewrite_expr (rhs, newrhs))
	return false;

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\nrewriting cast statement:\n");
	  print_gimple_stmt (dump_file, stmt, 0);
	}

      tree lhs = gimple_assign_lhs (stmt);
      tree conv_rhs = fold_convert (TREE_TYPE (lhs), newrhs[0]);
      gimple *newstmt = gimple_build_assign (lhs, conv_rhs);
      gsi_insert_before (gsi, newstmt, GSI_SAME_STMT);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "replaced with:\n");
	  print_gimple_stmt (dump_file, newstmt, 0);
	  fprintf (dump_file, "\n");
	}
      return true;
    }

  return remove;
}

/* Rewrite function call statement STMT.  Return TRUE if the statement
   is to be removed. */

bool
ipa_struct_reorg::rewrite_call (gcall *stmt, gimple_stmt_iterator *gsi)
{
  /* Handled allocation calls are handled seperately from normal
     function calls. */
  if (handled_allocation_stmt (stmt))
    {
      tree lhs = gimple_call_lhs (stmt);
      tree newrhs1[max_split];
      srdecl *decl = find_decl (lhs);
      if (!decl || !decl->type)
	return false;
      srtype *type = decl->type;
      tree num = allocate_size (type, decl, stmt);
      gcc_assert (num);
      memset (newrhs1, 0, sizeof (newrhs1));

      /* The realloc call needs to have its first argument rewritten. */
      if (gimple_call_builtin_p (stmt, BUILT_IN_REALLOC))
	{
	  tree rhs1 = gimple_call_arg (stmt, 0);
	  if (integer_zerop (rhs1))
	    {
	      for (unsigned i = 0; i < max_split; i++)
		newrhs1[i] = rhs1;
	    }
	  else if (!rewrite_expr (rhs1, newrhs1))
	    internal_error ("rewrite failed for realloc");
	}

      /* Go through each new lhs.  */
      for (unsigned i = 0; i < max_split && decl->newdecl[i]; i++)
	{
	  /* Specify the correct size for the multi-layer pointer.  */
	  tree newsize = isptrptr (decl->orig_type)
			 ? TYPE_SIZE_UNIT (decl->orig_type)
			 : TYPE_SIZE_UNIT (type->newtype[i]);
	  gimple *g;
	  /* Every allocation except for calloc needs the size multiplied out. */
	  if (!gimple_call_builtin_p (stmt, BUILT_IN_CALLOC))
	    newsize = gimplify_build2 (gsi, MULT_EXPR, sizetype, num, newsize);

	  if (gimple_call_builtin_p (stmt, BUILT_IN_MALLOC)
	      || gimple_call_builtin_p (stmt, BUILT_IN_ALLOCA))
	    g = gimple_build_call (gimple_call_fndecl (stmt),
				   1, newsize);
	  else if (gimple_call_builtin_p (stmt, BUILT_IN_CALLOC))
	    g = gimple_build_call (gimple_call_fndecl (stmt),
				   2, num, newsize);
	  else if (gimple_call_builtin_p (stmt, BUILT_IN_REALLOC))
	    g = gimple_build_call (gimple_call_fndecl (stmt),
				   2, newrhs1[i], newsize);
	  else
	    gcc_assert (false);
	  gimple_call_set_lhs (g, decl->newdecl[i]);
	  gsi_insert_before (gsi, g, GSI_SAME_STMT);
	}
      return true;
    }

  /* The function call free needs to be handled special. */
  if (gimple_call_builtin_p (stmt, BUILT_IN_FREE))
    {
      tree expr = gimple_call_arg (stmt, 0);
      tree newexpr[max_split];
      if (!rewrite_expr (expr, newexpr))
	return false;

      if (newexpr[1] == NULL)
	{
	  gimple_call_set_arg (stmt, 0, newexpr[0]);
	  update_stmt (stmt);
	  return false;
	}

      for (unsigned i = 0; i < max_split && newexpr[i]; i++)
	{
	  gimple *g = gimple_build_call (gimple_call_fndecl (stmt),
					 1, newexpr[i]);
	  gsi_insert_before (gsi, g, GSI_SAME_STMT);
	}
      return true;
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

  /* Did not find the function or had not cloned it return saying don't
     change the function call. */
  if (!f || !f->newf)
    return false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Changing arguments for function call :\n");
      print_gimple_expr (dump_file, stmt, 0);
      fprintf (dump_file, "\n");
    }

  /* Move over to the new function. */
  f = f->newf;

  tree chain = gimple_call_chain (stmt);
  unsigned nargs = gimple_call_num_args (stmt);
  auto_vec<tree> vargs (nargs);

  if (chain)
    {
      tree newchains[max_split];
      if (rewrite_expr (chain, newchains))
	{
	  /* Chain decl's type cannot be split and but it can change. */
	  gcc_assert (newchains[1] == NULL);
	  chain = newchains[0];
	}
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
      tree newargs[max_split];
      if (!rewrite_expr (arg, newargs))
	continue;

      /* If this ARG has a replacement handle the replacement.  */
      for (unsigned j = 0; j < max_split && d->newdecl[j]; j++)
	{
	  gcc_assert (newargs[j]);
	  /* If this is the first replacement of the argument,
	     then just replace it.  */
	  if (j == 0)
	    vargs[d->argumentnum + extraargs] = newargs[j];
	  else
	    {
	      /* More than one replacement, we need to insert into the array. */
	      extraargs++;
	      vargs.safe_insert(d->argumentnum + extraargs, newargs[j]);
	    }
	}
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

  if (gimple_vdef (new_stmt)
      && TREE_CODE (gimple_vdef (new_stmt)) == SSA_NAME)
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

  return true;
}

/* Rewrite the conditional statement STMT.  Return TRUE if the
   old statement is to be removed. */

bool
ipa_struct_reorg::rewrite_cond (gcond *stmt)
{
  tree_code rhs_code = gimple_cond_code (stmt);

  /* Handle only equals or not equals conditionals. */
  if (rhs_code != EQ_EXPR && rhs_code != NE_EXPR)
    return false;
  tree lhs = gimple_cond_lhs (stmt);
  tree rhs = gimple_cond_rhs (stmt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\nCOND: Rewriting\n");
      print_gimple_stmt (dump_file, stmt, 0);
      print_generic_expr (dump_file, lhs);
      fprintf (dump_file, "\n");
      print_generic_expr (dump_file, rhs);
      fprintf (dump_file, "\n");
    }

  tree newlhs[max_split] = {};
  tree newrhs[max_split] = {};
  if (!rewrite_lhs_rhs (lhs, rhs, newlhs, newrhs))
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Did nothing to statement.\n");
	}
      return false;
    }

  /*  Old rewrite: if (x_1 != 0B)
		-> _1 = x.reorg.0_1 != 0B; if (_1 != 1)
		   The logic is incorrect.
      New rewrite: if (x_1 != 0B)
		-> if (x.reorg.0_1 != 0B)；*/
  for (unsigned i = 0; i < max_split && (newlhs[i] || newrhs[i]); i++)
    {
      if (newlhs[i])
	{
	  gimple_cond_set_lhs (stmt, newlhs[i]);
	}
      if (newrhs[i])
	{
	  gimple_cond_set_rhs (stmt, newrhs[i]);
	}
      update_stmt (stmt);

      if (dump_file && (dump_flags & TDF_DETAILS))
      {
	fprintf (dump_file, "replaced with:\n");
	print_gimple_stmt (dump_file, stmt, 0);
	fprintf (dump_file, "\n");
      }
    }
  return false;
}

/* Rewrite debug statements if possible.  Return TRUE if the statement
   should be removed. */

bool
ipa_struct_reorg::rewrite_debug (gimple *stmt, gimple_stmt_iterator *)
{
  bool remove = false;
  if (gimple_debug_bind_p (stmt))
    {
      tree var = gimple_debug_bind_get_var (stmt);
      tree newvar[max_split];
      if (rewrite_expr (var, newvar, true))
	remove = true;
      if (gimple_debug_bind_has_value_p (stmt))
	{
          var = gimple_debug_bind_get_value (stmt);
	  if (TREE_CODE (var) == POINTER_PLUS_EXPR)
	    var = TREE_OPERAND (var, 0);
	  if (rewrite_expr (var, newvar, true))
	    remove = true;
	}
    }
  else if (gimple_debug_source_bind_p (stmt))
    {
      tree var = gimple_debug_source_bind_get_var (stmt);
      tree newvar[max_split];
      if (rewrite_expr (var, newvar, true))
	remove = true;
      var = gimple_debug_source_bind_get_value (stmt);
      if (TREE_CODE (var) == POINTER_PLUS_EXPR)
	var = TREE_OPERAND (var, 0);
      if (rewrite_expr (var, newvar, true))
	remove = true;
    }

  return remove;
}

/* Rewrite PHI nodes, return true if the PHI was replaced. */

bool
ipa_struct_reorg::rewrite_phi (gphi *phi)
{
  tree newlhs[max_split];
  gphi *newphi[max_split];
  tree result = gimple_phi_result (phi);
  gphi_iterator gsi;

  memset(newphi, 0, sizeof(newphi));

  if (!rewrite_expr (result, newlhs))
    return false;

  if (newlhs[0] == NULL)
    return false;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "\nrewriting PHI:\n");
      print_gimple_stmt (dump_file, phi, 0);
    }

  for (unsigned i = 0; i < max_split && newlhs[i]; i++)
    newphi[i] = create_phi_node (newlhs[i], gimple_bb (phi));

  for(unsigned i = 0; i  < gimple_phi_num_args (phi); i++)
    {
      tree newrhs[max_split];
      phi_arg_d rhs = *gimple_phi_arg (phi, i);
      edge e = gimple_phi_arg_edge (phi, i);

      /* Handling the NULL phi Node.  */
      bool r = rewrite_expr (rhs.def, newrhs);
      if (!r && integer_zerop (rhs.def))
	{
	  for (unsigned i = 0; i < max_split && newlhs[i]; i++)
	    {
	      newrhs[i] = fold_convert (TREE_TYPE (newlhs[i]), rhs.def);
	    }
	}

      for (unsigned j = 0; j < max_split && newlhs[j]; j++)
	add_phi_arg (newphi[j], newrhs[j], e, rhs.locus);
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "into:\n");
      for (unsigned i = 0; i < max_split && newlhs[i]; i++)
	{
	  print_gimple_stmt (dump_file, newphi[i], 0);
	  fprintf (dump_file, "\n");
	}
    }

  gsi = gsi_for_phi (phi);
  remove_phi_node (&gsi, false);

  return true;
}

/* Rewrite gimple statement STMT, return true if the STATEMENT
   is to be removed. */

bool
ipa_struct_reorg::rewrite_stmt (gimple *stmt, gimple_stmt_iterator *gsi)
{
  switch (gimple_code (stmt))
    {
    case GIMPLE_ASSIGN:
      return rewrite_assign (as_a <gassign *> (stmt), gsi);
    case GIMPLE_CALL:
      return rewrite_call (as_a <gcall *> (stmt), gsi);
    case GIMPLE_COND:
      return rewrite_cond (as_a <gcond *> (stmt));
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

/* Does the function F uses any decl which has changed. */

bool
ipa_struct_reorg::has_rewritten_type (srfunction *f)
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

/* Rewrite the functions if needed, return
   the TODOs requested.  */

unsigned
ipa_struct_reorg::rewrite_functions (void)
{
  unsigned retval = 0;

  /* Create new types, if we did not create any new types,
     then don't rewrite any accesses. */
  if (!create_new_types ())
    {
      return 0;
    }

  if (functions.length ())
    {
      retval = TODO_remove_functions;
      create_new_functions ();
    }

  create_new_decls ();

  for (unsigned i = 0; i < functions.length (); i++)
    {
      srfunction *f = functions[i];
      if (f->newnode)
	continue;

      /* Function uses no rewriten types so don't cause a rewrite. */
      if (!has_rewritten_type (f))
	continue;

      cgraph_node *node = f->node;
      basic_block bb;
      cfun_context ctx (node);

      current_function = f;

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\nBefore rewrite: %dth_%s\n",
		   i, f->node->name ());
	  dump_function_to_file (current_function_decl, dump_file,
				 dump_flags | TDF_VOPS);
	  fprintf (dump_file, "\n======== Start to rewrite: %dth_%s ========\n",
		   i, f->node->name ());
	}
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gphi_iterator si = gsi_start_phis (bb); !gsi_end_p (si); )
	    {
	      if (rewrite_phi (si.phi ()))
		si = gsi_start_phis (bb);
	      else
		gsi_next (&si);
	    }

	  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si); )
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (rewrite_stmt (stmt, &si))
		gsi_remove (&si, true);
	      else
		gsi_next (&si);
	    }
        }

      /* Debug statements need to happen after all other statements
	 have changed. */
      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gimple_stmt_iterator si = gsi_start_bb (bb); !gsi_end_p (si); )
	    {
	      gimple *stmt = gsi_stmt (si);
	      if (gimple_code (stmt) == GIMPLE_DEBUG
		  && rewrite_debug (stmt, &si))
		gsi_remove (&si, true);
	      else
		gsi_next (&si);
	    }
	}

      /* Release the old SSA_NAMES for old arguments.  */
      if (f->old)
	{
	  for (unsigned i = 0; i < f->args.length (); i++)
	    {
	      srdecl *d = f->args[i];
	      if (d->newdecl[0] != d->decl)
		{
		  tree ssa_name = ssa_default_def (cfun, d->decl);
		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      fprintf (dump_file, "Found ");
		      print_generic_expr (dump_file, ssa_name);
		      fprintf (dump_file, " to be released.\n");
		    }
		  release_ssa_name (ssa_name);
		}
	    }
	}

      update_ssa (TODO_update_ssa_only_virtuals);

      if (flag_tree_pta)
	compute_may_aliases ();

      remove_unused_locals ();

      cgraph_edge::rebuild_edges ();

      free_dominance_info (CDI_DOMINATORS);

      if (dump_file)
	{
	  fprintf (dump_file, "\nAfter rewrite: %dth_%s\n",
		   i, f->node->name ());
	  dump_function_to_file (current_function_decl, dump_file,
				 dump_flags | TDF_VOPS);
	}

      current_function = NULL;
    }

  return retval | TODO_verify_all;
}

unsigned int
ipa_struct_reorg::execute_struct_relayout (void)
{
  unsigned retval = 0;
  for (unsigned i = 0; i < types.length (); i++)
    {
      tree type = types[i]->type;
      if (TYPE_FIELDS (type) == NULL)
	{
	  continue;
	}
      if (types[i]->has_alloc_array != 1)
	{
	  continue;
	}
      if (types[i]->chain_type)
	{
	  continue;
	}

      ipa_struct_relayout csr (type, this);

      if (!csr.ctype.init_type_info())
        continue;

      if (!csr.find_hot_access())
        continue;

      retval |= csr.execute ();
    }

  if (dump_file)
    {
      if (transformed)
	{
	  fprintf (dump_file, "\nNumber of structures to transform in "
		   "Complete Structure Relayout is %d\n", transformed);
	}
      else
	{
	  fprintf (dump_file, "\nNo structures to transform in "
		   "Complete Structure Relayout.\n");
	}
    }

  return retval;
}

unsigned int
ipa_struct_reorg::execute (enum srmode mode)
{
  unsigned int ret = 0;

  if (mode == NORMAL)
    {
      current_mode = mode;
      /* If there is a top-level inline-asm,
	 the pass immediately returns.  */
      if (symtab->first_asm_symbol ())
	{
	  return 0;
	}
      record_accesses ();
      prune_escaped_types ();
      if (current_mode == NORMAL)
	{
	  analyze_types ();
	}

      ret = rewrite_functions ();
    }
  else if (mode == COMPLETE_STRUCT_RELAYOUT)
    {
      if (dump_file)
	{
	  fprintf (dump_file, "\n\nTry Complete Struct Relayout:\n");
	}
      current_mode = COMPLETE_STRUCT_RELAYOUT;
      if (symtab->first_asm_symbol ())
	{
	  return 0;
	}
      record_accesses ();
      prune_escaped_types (true);

      ret = execute_struct_relayout ();
    }

  return ret;
}

const pass_data pass_data_ipa_struct_reorg =
{
  SIMPLE_IPA_PASS, /* type */
  "struct_reorg", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_IPA_STRUCT_REORG, /* tv_id */
  0, /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_ipa_struct_reorg : public simple_ipa_opt_pass
{
public:
  pass_ipa_struct_reorg (gcc::context *ctxt)
    : simple_ipa_opt_pass (pass_data_ipa_struct_reorg, ctxt)
  {}

  /* opt_pass methods: */
  virtual bool gate (function *);
  virtual unsigned int execute (function *)
  {
    unsigned int ret = 0;

    {
      push_dump_file save (NULL, TDF_NONE);
      ipa_type_escape_analysis_init ();
    }

    ret = ipa_struct_reorg ().execute (COMPLETE_STRUCT_RELAYOUT);

    {
      push_dump_file save (NULL, TDF_NONE);
      ipa_type_escape_analysis_exit ();
    }

    return ret;
  }
}; // class pass_ipa_struct_reorg

bool
pass_ipa_struct_reorg::gate (function *)
{
  return optimize >= 3 && flag_ipa_struct_reorg
	 /* Only enable struct optimizations in C since other
	    languages' grammar forbid.  */
	 && lang_c_p ();
}

} // anon namespace

simple_ipa_opt_pass *
make_pass_ipa_struct_reorg (gcc::context *ctxt)
{
  return new pass_ipa_struct_reorg (ctxt);
}
