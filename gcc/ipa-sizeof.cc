/* Copyright (C) 2017-2022 Free Software Foundation, Inc.

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
#include "gimple.h"
#include "tree-pass.h"
#include "cgraph.h"
#include "tree-pretty-print.h"
#include "ssa.h"
#include "data-streamer.h"
#include "ipa-type-escape-analysis.h"
#include "ipa-lto-utils.h"

static hash_map<tree, bool> used_in_alloc;
static hash_set<tree> memoized;
bool sizeof_analysis_succeeds = true;

class array_index_walker : public type_walker
{
public:
  array_index_walker () {};

private:
  virtual void _walk_ARRAY_TYPE_pre (tree t);
  virtual void _walk_RECORD_TYPE_pre (tree t);
  virtual void _walk_POINTER_TYPE_pre (tree t);
  virtual bool is_memoized (tree t);
};

bool
array_index_walker::is_memoized (tree t)
{
  return memoized.contains (t);
}

void
array_index_walker::_walk_RECORD_TYPE_pre (tree t)
{
  memoized.add (t);
}

void
array_index_walker::_walk_POINTER_TYPE_pre (tree t)
{
  memoized.add (t);
}

void
array_index_walker::_walk_ARRAY_TYPE_pre (tree t)
{
  memoized.add (t);
  tree domain = TYPE_DOMAIN (t);
  if (!domain)
    return;
  tree max_value = TYPE_MAX_VALUE (domain);
  if (!max_value)
    return;
  tree type_sizeof_type = TYPE_SIZEOF_TYPE (max_value);
  if (!type_sizeof_type)
    return;

  sizeof_analysis_succeeds &= type_sizeof_type != error_mark_node;
  if (type_sizeof_type == error_mark_node)
    {
      TYPE_SIZEOF_TYPE (max_value) = NULL;
    }
  used_in_alloc.put (type_sizeof_type, false);
}

class expr_integer_cst_collector : public expr_walker
{
public:
  bool _seen;
  array_index_walker array_walker;

  expr_integer_cst_collector () : _seen (false), array_walker () {};

private:
  virtual void _walk_post (tree t);
  virtual void _walk_CONSTRUCTOR_pre (tree e);
};

void
expr_integer_cst_collector::_walk_post (tree t)
{
  array_walker.walk (TREE_TYPE (t));
  if (TREE_CODE (t) != INTEGER_CST)
    return;
  if (TYPE_SIZEOF_TYPE (t) == NULL)
    return;
  _seen = true;
}

void
expr_integer_cst_collector::_walk_CONSTRUCTOR_pre (tree e)
{
  if (TREE_CLOBBER_P (e))
    return;

  sizeof_analysis_succeeds = false;
}

class gimple_integer_cst_collector : public gimple_walker
{
private:
  virtual void _walk_pre_tree (tree);
  virtual void _walk_pre_gassign (gassign *);
  virtual void _walk_pre_greturn (greturn *);
  virtual void _walk_pre_gcond (gcond *);
  virtual void _walk_pre_gcall (gcall *);
  virtual void _walk_pre_gdebug (gdebug *);

  expr_integer_cst_collector _expr_collector;
};

static void
print_map (void)
{
  if (!dump_file)
    return;

  for (auto i = used_in_alloc.begin (), e = used_in_alloc.end (); i != e; ++i)
    {
      tree t = (*i).first;
      bool a = (*i).second;
      print_generic_expr (dump_file, t, TDF_NONE);
      fprintf (dump_file, " %s\n", a ? "T" : "F");
    }
}

static bool
is_alloc_fn (tree fndecl)
{
  if (!fndecl)
    return false;
  if (!fndecl_built_in_p (fndecl, BUILT_IN_NORMAL))
    return false;
  switch (DECL_FUNCTION_CODE (fndecl))
    {
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

static void
check_sizeof_type (tree &type, bool in_alloc = false,
		   bool reset_type = false)
{
  if (type == error_mark_node)
    {
      sizeof_analysis_succeeds = false;
      if (reset_type)
	type = NULL_TREE;
    }
  else if (type)
    used_in_alloc.put (type, in_alloc);
}

static void
check_sizeof_type_of_expr (tree expr, bool in_alloc = false)
{
  check_sizeof_type (TYPE_SIZEOF_TYPE (expr), in_alloc, true);
}

static void
find_sink (tree var, tree type)
{
  gcc_assert (var);
  gimple *use_stmt = NULL;
  gimple *last_stmt = NULL;
  imm_use_iterator iterator;
  unsigned count = 0;
  if (TREE_CODE (var) != SSA_NAME)
    {
      check_sizeof_type (type);
      return;
    }

  FOR_EACH_IMM_USE_STMT (use_stmt, iterator, var)
    {
      count++;
      last_stmt = use_stmt;
    }

  if (count > 1)
    check_sizeof_type(type);
  else if (count < 1)
    {
      check_sizeof_type (type);
      gcc_unreachable ();
    }
  else
    {
      gcall *call = dyn_cast<gcall *> (last_stmt);

      if (!call)
	{
	  check_sizeof_type (type);
	  return;
	}

      tree fndecl = gimple_call_fndecl (call);
      if (!fndecl)
	{
	  check_sizeof_type (type);
	  return;
	}

      if (!fndecl_built_in_p (fndecl))
	{
	  check_sizeof_type (type);
	  return;
	}

      bool is_alloc = is_alloc_fn (fndecl);
      if (!is_alloc)
	{
	  check_sizeof_type (type);
	  return;
	}

      bool *in_alloc = used_in_alloc.get (type);

      if (in_alloc && !*in_alloc)
	return;

      check_sizeof_type (type, true);
      gimple_call_set_type_sizeof_type (call, type);
    }
}

void
gimple_integer_cst_collector::_walk_pre_tree (tree t)
{
  if (!t)
    return;
  _expr_collector._seen = false;
  _expr_collector.walk (t);
  if (!_expr_collector._seen)
    return;

  check_sizeof_type_of_expr (t);
}

void
gimple_integer_cst_collector::_walk_pre_gassign (gassign *stmt)
{
  tree lhs = gimple_assign_lhs (stmt);
  _expr_collector._seen = false;
  _expr_collector.walk (lhs);
  tree type_sizeof_type3 = NULL;
  tree type_sizeof_type2 = NULL;
  tree type_sizeof_type1 = NULL;
  tree rhs3 = NULL;
  tree rhs2 = NULL;
  tree rhs1 = NULL;

  const enum gimple_rhs_class gclass = gimple_assign_rhs_class (stmt);
  switch (gclass)
    {
    case GIMPLE_TERNARY_RHS:
      {
	_expr_collector._seen = false;
	rhs3 = gimple_assign_rhs3 (stmt);
	_expr_collector.walk (rhs3);
	type_sizeof_type3
	  = _expr_collector._seen ? TYPE_SIZEOF_TYPE (rhs3) : type_sizeof_type3;
      }
    /* fall-through */
    case GIMPLE_BINARY_RHS:
      {
	_expr_collector._seen = false;
	rhs2 = gimple_assign_rhs2 (stmt);
	_expr_collector.walk (rhs2);
	type_sizeof_type2
	  = _expr_collector._seen ? TYPE_SIZEOF_TYPE (rhs2) : type_sizeof_type2;
      }
    /* fall-through */
    case GIMPLE_UNARY_RHS:
    case GIMPLE_SINGLE_RHS:
      {
	_expr_collector._seen = false;
	rhs1 = gimple_assign_rhs1 (stmt);
	_expr_collector.walk (rhs1);
	type_sizeof_type1
	  = _expr_collector._seen ? TYPE_SIZEOF_TYPE (rhs1) : type_sizeof_type1;
      }
      /* fall-through */
      break;
    default:
      gcc_unreachable ();
      break;
    }

  bool is_sizeof_cst
    = type_sizeof_type3 || type_sizeof_type2 || type_sizeof_type1;
  if (!is_sizeof_cst)
    return;

  if (type_sizeof_type3)
    {
      check_sizeof_type_of_expr (rhs3);
      if (type_sizeof_type2)
	check_sizeof_type_of_expr (rhs2);
      if (type_sizeof_type1)
	check_sizeof_type_of_expr (rhs1);
      return;
    }

  if (type_sizeof_type2 && type_sizeof_type1
      && type_sizeof_type2 != type_sizeof_type1)
    {
      check_sizeof_type_of_expr (rhs1);
      check_sizeof_type_of_expr (rhs2);
      return;
    }

  if (type_sizeof_type2 == error_mark_node)
    {
      TYPE_SIZEOF_TYPE (rhs2) = NULL;
    }
  if (type_sizeof_type1 == error_mark_node)
    {
      TYPE_SIZEOF_TYPE (rhs1) = NULL;
    }
  tree type = type_sizeof_type2 ? type_sizeof_type2 : type_sizeof_type1;

  find_sink (lhs, type);
}

void
gimple_integer_cst_collector::_walk_pre_greturn (greturn *stmt)
{
  _expr_collector._seen = false;
  tree retval = gimple_return_retval (stmt);
  if (!retval)
    return;

  _expr_collector.walk (retval);

  if (_expr_collector._seen)
    check_sizeof_type_of_expr (retval);
}

void
gimple_integer_cst_collector::_walk_pre_gcond (gcond *stmt)
{
  _expr_collector._seen = false;
  tree lhs = gimple_cond_lhs (stmt);
  tree rhs = gimple_cond_rhs (stmt);

  _expr_collector.walk (lhs);
  if (_expr_collector._seen)
    check_sizeof_type_of_expr (lhs);
  _expr_collector._seen = false;

  _expr_collector.walk (rhs);
  if (_expr_collector._seen)
    check_sizeof_type_of_expr (rhs);
  _expr_collector._seen = false;
}

void
gimple_integer_cst_collector::_walk_pre_gcall (gcall *stmt)
{
  tree fndecl = gimple_call_fndecl (stmt);
  bool is_alloc = fndecl && is_alloc_fn (fndecl);
  /* Walk over the arguments.  */
  unsigned n = gimple_call_num_args (stmt);
  for (unsigned i = 0; i < n; i++)
    {
      _expr_collector._seen = false;
      tree a = gimple_call_arg (stmt, i);
      _expr_collector.walk (a);
      if (_expr_collector._seen)
	{
	  tree type = TYPE_SIZEOF_TYPE (a);
	  gimple_call_set_type_sizeof_type (stmt, type);
	  if (!is_alloc)
	    check_sizeof_type_of_expr (a);
	  else if (type && !used_in_alloc.get (type))
	    check_sizeof_type_of_expr (a, true);
	}
    }
}

void
gimple_integer_cst_collector::_walk_pre_gdebug (__attribute__ ((unused))
						gdebug *stmt)
{}

static void
ipa_sizeof_generate_summary (void)
{
  gimple_integer_cst_collector collector;

  collector.walk ();
  print_map ();
}

static void
ipa_write_summary (void)
{
  if (dump_file)
    {
      fprintf (dump_file, "Writing sizeof...\n");
      print_map ();
    }
  struct output_block *ob = create_output_block (LTO_section_ipa_sizeof);
  if (!sizeof_analysis_succeeds)
    {
      streamer_write_uhwi (ob, -1);
      return;
    }
  streamer_write_uhwi (ob, used_in_alloc.elements ());
  for (auto i = used_in_alloc.begin (), e = used_in_alloc.end (); i != e; ++i)
    {
      tree type = (*i).first;
      bool used_only_in_alloc = (*i).second;
      if (!TYPE_P (type))
	stream_write_tree_ref (ob, NULL_TREE);
      else
	stream_write_tree_ref (ob, type);
      streamer_write_uhwi (ob, used_only_in_alloc);
    }
  produce_asm (ob, NULL);
  destroy_output_block (ob);
  used_in_alloc.empty ();
}

static void
clean_type_sizeof_p (void)
{
  print_map ();
  for (auto i = used_in_alloc.begin (), e = used_in_alloc.end (); i != e; ++i)
    {
      tree type = (*i).first;
      if (!TYPE_P (type))
	continue;
      tree mtype = TYPE_MAIN_VARIANT (type);
      bool used_only_in_alloc = (*i).second;
      for (tree variant = mtype; variant; variant = TYPE_NEXT_VARIANT (variant))
	{
	  TYPE_SIZEOF_P (variant) = !used_only_in_alloc;
	}
    }
}

static void
read_allocation_uses (struct lto_file_decl_data *file_data, const char *data,
		      size_t len)
{
  const struct lto_function_header *header
    = (const struct lto_function_header *) data;
  const int cfg_offset = sizeof (struct lto_function_header);
  const int main_offset = cfg_offset + header->cfg_size;
  const int string_offset = main_offset + header->main_size;
  class data_in *data_in;
  int i;
  int count;

  lto_input_block ib_main ((const char *) data + main_offset, header->main_size,
			   file_data->mode_table);

  data_in = lto_data_in_create (file_data, (const char *) data + string_offset,
				header->string_size, vNULL);

  count = streamer_read_uhwi (&ib_main);
  if (count == -1)
    {
      sizeof_analysis_succeeds = false;
    }
  for (i = 0; i < count; i++)
    {
      tree type = stream_read_tree_ref (&ib_main, data_in);
      bool used_only_in_alloc = streamer_read_uhwi (&ib_main);
      bool *is_used_only_in_alloc_so_far = used_in_alloc.get (type);
      if (!is_used_only_in_alloc_so_far)
	{
	  used_in_alloc.put (type, used_only_in_alloc);
	  continue;
	}

      if (!used_only_in_alloc)
	{
	  used_in_alloc.put (type, false);
	}
    }

  lto_free_section_data (file_data, LTO_section_ipa_sizeof, NULL, data, len);
  lto_data_in_delete (data_in);
}

static void
ipa_read_summary (void)
{
  used_in_alloc.empty ();
  struct lto_file_decl_data **file_data_vec = lto_get_file_decl_data ();
  struct lto_file_decl_data *file_data;
  unsigned int j = 0;

  while ((file_data = file_data_vec[j++]))
    {
      size_t len;
      const char *data
	= lto_get_summary_section_data (file_data, LTO_section_ipa_sizeof,
					&len);
      if (data)
	read_allocation_uses (file_data, data, len);
    }

  clean_type_sizeof_p ();
}

namespace {

const pass_data pass_data_ipa_sizeof = {
  IPA_PASS,				      /* type */
  "sizeof",				      /* name */
  OPTGROUP_NONE,			      /* optinfo_flags */
  TV_IPA_CONSTANT_PROP,			      /* tv_id */
  0,					      /* properties_required */
  0,					      /* properties_provided */
  0,					      /* properties_destroyed */
  0,					      /* todo_flags_start */
  (TODO_dump_symtab | TODO_remove_functions), /* todo_flags_finish */
};

class pass_ipa_sizeof : public ipa_opt_pass_d
{
public:
  pass_ipa_sizeof (gcc::context *ctxt)
    : ipa_opt_pass_d (pass_data_ipa_sizeof, ctxt,
		      ipa_sizeof_generate_summary, /* generate_summary */
		      ipa_write_summary,	   /* write_summary */
		      ipa_read_summary,		   /* read_summary */
		      NULL,		 /* write_optimization_summary */
		      NULL,		 /* read_optimization_summary */
		      NULL,		 /* stmt_fixup */
		      0,    /* function_transform_todo_flags_start */
		      NULL, /* function_transform */
		      NULL) /* variable_transform */
  {}

  /* opt_pass methods: */
  virtual bool gate (function *)
  {
    return flag_ipa_sizeof && lang_c_p ();
  }

}; // class pass_ipa_sizeof

} // anon namespace

ipa_opt_pass_d *
make_pass_ipa_sizeof (gcc::context *ctxt)
{
  return new pass_ipa_sizeof (ctxt);
}
