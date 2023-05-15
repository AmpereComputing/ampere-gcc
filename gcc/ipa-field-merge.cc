/* IPA Type-based Field Merge Optimization
   Copyright (C) 2021-2022 Free Software Foundation, Inc.

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
#include "rtl.h"
#include "tree.h"
#include "gimple.h"
#include "tree-pass.h"
#include "ssa.h"
#include "gimple-pretty-print.h"
#include "fold-const.h"
#include "gimple-iterator.h"
#include "gimplify-me.h"
#include "tree-cfg.h"
#include "tree-dfa.h"
#include "domwalk.h"
#include "tree-cfgcleanup.h"
#include "alias.h"
#include "tree-ssa-loop.h"
#include "tree-ssa-dse.h"
#include "tree-ssa-dce.h"
#include "builtins.h"
#include "gimple-fold.h"
#include "gimplify.h"
#include "cgraph.h"
#include "ipa-utils.h"
#include "cfgloop.h"
#include "cfganal.h"
#include "cfghooks.h"
#include "tree-affine.h"
#include "tree-hash-traits.h"
#include "tree-vectorizer.h"
#include "tree-into-ssa.h"
#include "langhooks.h"
#include "stor-layout.h"
#include "attribs.h"
#include "calls.h"
#include "demangle.h"
#include "alloc-pool.h"
#include "symbol-summary.h"
#include "symtab-thunks.h"

class target_type_info;
class merge_type_info;

static target_type_info *targ_type;
static merge_type_info *merge_type;
static unsigned num_vecs;
static bool flag_enable_type_analysis = true;
static bool strict_type_analysis;

#define MAX_NUM_DYN_VECS 8
#define MIN_NUM_DYN_VECS 3

enum VEC_FIELD_KIND
{
  VEC_FLD_START,
  F_ELT_LIST = VEC_FLD_START,
  F_CUR_CNT,
  F_MAX_CNT,
  F_MEM_POOL,
  F_DEL_ELT_P,
  VEC_FLD_LEN
};

static const char *vec_field_names[VEC_FLD_LEN]
  = { "ELT_LIST", "CUR_COUNT", "MAX_COUNT", "MEM_POOL", "DEL_ELT_P" };

enum ACCESS_KIND
{
  LOAD_P,
  STORE_P
};
enum ALLOC_KIND
{
  ALLOC_P,
  DEALLOC_P
};

#define CHECK(cond) \
  if (!(cond)) \
    return false;

#define TEST(cond) \
  if (!(cond)) \
    return false;

class dyn_vec_info
{
public:
  unsigned vid;

  unsigned param_id;

  tree vec_type;
  HOST_WIDE_INT type_size_hwi;

  tree field_decls[VEC_FLD_LEN];

  tree elt_size;
  HOST_WIDE_INT elt_size_hwi;

  bool replic_elt_p;

  bool derive_fld_p;
  tree child_type;

  bool field_p (tree, VEC_FIELD_KIND);
  bool find_field (tree, VEC_FIELD_KIND &);
  tree get_field (VEC_FIELD_KIND vf_kind) { return field_decls[vf_kind]; }

  bool extract_comp_ref_field (tree ref, tree vec_base, VEC_FIELD_KIND &);
  bool extract_ref_field (tree ref, tree ptr, tree offset, VEC_FIELD_KIND &);

  bool set_vec_type (tree, bool child_p = false);
  bool set_field (VEC_FIELD_KIND, tree);

  dyn_vec_info (unsigned vid)
    : vid (vid), param_id (0), vec_type (NULL_TREE), replic_elt_p (false),
      derive_fld_p (false), child_type (NULL_TREE)
  {
    memset (field_decls, 0, sizeof (field_decls));
  }
};

class otr_alloc_func
{
public:
  tree vptr_offset;
  tree token;
  tree f_vptr;
  tree func_type;

  otr_alloc_func () : func_type (NULL_TREE) {}
};

static bool types_matched_p (tree t1, tree t2);

class target_use_info;
class pattern_info;

class target_type_info
{
public:
  tree root_struct;

  unsigned nvec;
  auto_vec<tree> vec_decls;
  auto_vec<HOST_WIDE_INT> vec_offsets;
  tree f_mem_pool;
  HOST_WIDE_INT mp_offset;

  auto_delete_vec<dyn_vec_info> dyn_vecs;

  auto_delete_vec<target_use_info> targ_uses;
  auto_delete_vec<pattern_info> targ_patts;

  otr_alloc_func mem_alloc;
  otr_alloc_func mem_dealloc;

  bool valid_p;

private:
  hash_map<tree, dyn_vec_info *> fld_to_vec;

public:
  bool extract_otr_mem_func (gimple *, ALLOC_KIND, tree &expr, tree &vptr,
			     tree &arg0, tree &arg1);
  bool check_otr_mem_func (gimple *, ALLOC_KIND alloc_kind);
  bool otr_mem_func_p (gimple *, target_use_info *, ALLOC_KIND,
		       unsigned vid = UINT_MAX);
  target_use_info *create_targ_use (tree);

  void dump_targ_type ();

  bool init_dyn_vecs (auto_vec<std::pair<tree, HOST_WIDE_INT> > &);
  bool set_mempool (tree);

  bool fld_vec_p (tree f_vec) { return fld_to_vec.get (f_vec); }

  bool get_vec_index (HOST_WIDE_INT offset, unsigned &vid)
  {
    TEST (offset % POINTER_SIZE == 0)

    vid = (offset - vec_offsets[0]) / POINTER_SIZE;
    return vid < nvec;
  }

  inline dyn_vec_info *get_vec (unsigned vid) { return dyn_vecs[vid]; }

  bool replic_elt_p (unsigned vid) { return dyn_vecs[vid]->replic_elt_p; }

  inline bool targ_type_ptr_p (tree base)
  {
    tree ptr_type = TREE_TYPE (base);
    return POINTER_TYPE_P (ptr_type)
	   && types_matched_p (TREE_TYPE (ptr_type), this->root_struct);
  }

  inline bool targ_type_ref_p (tree base)
  {
    return types_matched_p (TREE_TYPE (base), this->root_struct);
  }

  target_type_info (tree root_struct)
    : root_struct (root_struct), nvec (num_vecs), f_mem_pool (NULL_TREE),
      valid_p (true)
  {
    vec_decls.safe_grow_cleared (nvec, true);
    vec_offsets.safe_grow_cleared (nvec, true);
  }
};

class merge_type_info
{
public:
  tree new_struct;
  tree fld_decls[VEC_FLD_LEN];

  tree elt_tuple_type;
  tree elt_tuple_size;
  auto_vec<tree> elt_decls;

  merge_type_info ();

  tree build_field_ref (tree, VEC_FIELD_KIND);
  tree build_count_cst (int);

  tree get_field (VEC_FIELD_KIND vf_kind) { return fld_decls[vf_kind]; }
  tree get_elt_decl (unsigned vid) { return elt_decls[vid]; }
  tree get_elt_list_type () { return build_pointer_type (elt_tuple_type); }

private:
  void create_elt_tuple ();
};

enum VEC_USE_KIND
{
  VU_VEC_FIELD,
  VU_INDEXED_ELT,
  VU_VEC_INIT_CHECK,
  VU_OTHER
};

enum VEC_TRANS_STATUS
{
  VT_INIT,
  VT_TODO,
  VT_DONE
};

class vec_use_info
{
public:
  gimple *vec_stmt;
  unsigned vid;
  VEC_USE_KIND vu_kind;
  VEC_TRANS_STATUS vt_status;

  virtual void transform_vec_use (target_use_info *) { gcc_unreachable (); };
  virtual void remove_vec_use (target_use_info *targ_use);

  virtual void dump_vec_use () = 0;

  vec_use_info (gimple *vec_stmt, unsigned vid, VEC_USE_KIND vu_kind)
    : vec_stmt (vec_stmt), vid (vid), vu_kind (vu_kind), vt_status (VT_INIT)
  {}
  virtual ~vec_use_info () {}
};

class other_vec_use : public vec_use_info
{
public:
  void dump_vec_use ();

  other_vec_use (gimple *vec_stmt, unsigned vid)
    : vec_use_info (vec_stmt, vid, VU_OTHER)
  {}
  virtual ~other_vec_use () {}
};

class field_vec_use : public vec_use_info
{
public:
  VEC_FIELD_KIND vf_kind;
  ACCESS_KIND acc_kind;

  void transform_vec_use (target_use_info *);

  virtual void dump_vec_use ()
  {
    fprintf (dump_file, "%s (%d): ", vec_field_names[(unsigned) vf_kind],
	     vt_status);
    print_gimple_stmt (dump_file, vec_stmt, 0, TDF_NONE);
  }

  field_vec_use (gimple *vec_stmt, unsigned vid, VEC_FIELD_KIND vf_kind,
		 ACCESS_KIND acc_kind)
    : vec_use_info (vec_stmt, vid, VU_VEC_FIELD), vf_kind (vf_kind),
      acc_kind (acc_kind)
  {}

  virtual ~field_vec_use () {}
};

class init_check_vec_use : public vec_use_info
{
public:
  edge e_true;
  edge e_false;

  void transform_vec_use (target_use_info *);

  virtual void dump_vec_use ()
  {
    fprintf (dump_file, "INIT_CHECK (%d): ", vt_status);
    print_gimple_stmt (dump_file, vec_stmt, 0, TDF_NONE);
  }

  init_check_vec_use (gimple *vec_stmt, unsigned vid, edge e_true, edge e_false)
    : vec_use_info (vec_stmt, vid, VU_VEC_INIT_CHECK), e_true (e_true),
      e_false (e_false)
  {}
};

class idx_elt_vec_use : public vec_use_info
{
public:
  gimple *offset_stmt;
  gimple *ptr_plus_stmt;
  tree elt_ptr;
  tree elt_idx;
  ACCESS_KIND acc_kind;

  void transform_vec_use (target_use_info *);
  void remove_vec_use (target_use_info *);

  virtual void dump_vec_use ()
  {
    fprintf (dump_file, "INDEXED_ELEMENT (%d):\n", vt_status);
    print_gimple_stmt (dump_file, offset_stmt, 0, TDF_NONE);
    print_gimple_stmt (dump_file, ptr_plus_stmt, 0, TDF_NONE);
    print_gimple_stmt (dump_file, vec_stmt, 0, TDF_NONE);
  }

  idx_elt_vec_use (gimple *vec_stmt, unsigned vid, ACCESS_KIND acc_kind)
    : vec_use_info (vec_stmt, vid, VU_INDEXED_ELT), acc_kind (acc_kind)
  {}
  idx_elt_vec_use ()
    : vec_use_info (NULL, UINT_MAX, VU_INDEXED_ELT), offset_stmt (NULL),
      ptr_plus_stmt (NULL), elt_idx (NULL_TREE)
  {}
  virtual ~idx_elt_vec_use () {}
};

class vec_use_group
{
public:
  unsigned vid;
  target_use_info *targ_use;

  auto_vec<gimple *> root_stmts;
  ACCESS_KIND root_acc_kind;

  auto_vec<tree> vec_bases;

  auto_delete_vec<vec_use_info> vec_uses;
  bool add_root_stmt (gimple *root_stmt);

  virtual bool collect_vec_uses () = 0;
  bool collect_uses_from_base (tree);
  bool find_idx_elt_use (gimple *elt_ptr_def);
  bool find_idx_elt_use_from (gimple *, idx_elt_vec_use *&);
  bool find_idx_elt_reverse (gimple *, idx_elt_vec_use *&);
  bool all_uses_checked_p ();

  void transform_use_group ();
  void remove_store_vec_uses ();

  void add_field_use (gimple *, VEC_FIELD_KIND, ACCESS_KIND);
  void add_other_use (gimple *);
  void add_init_check_use (gimple *, edge, edge);
  void add_idx_elt_use (idx_elt_vec_use *);

  void dump_vec_uses ();

  vec_use_group (unsigned vid, target_use_info *targ_use, ACCESS_KIND root_ak)
    : vid (vid), targ_use (targ_use), root_acc_kind (root_ak)
  {}
  virtual ~vec_use_group () {}
};

class read_vu_group : public vec_use_group
{
public:
  virtual bool collect_vec_uses ();

  read_vu_group (unsigned vid, target_use_info *targ_use)
    : vec_use_group (vid, targ_use, LOAD_P)
  {}
};

class write_vu_group : public vec_use_group
{
public:
  auto_vec<gimple *> vec_allocs;
  auto_vec<gimple *> ptr_plus_stmts;
  auto_vec<tree> ptrs;
  auto_vec<tree> offsets;

  virtual bool collect_vec_uses ();
  bool collect_uses_from_ptr_plus (tree, tree, tree);

  write_vu_group (unsigned vid, target_use_info *targ_use)
    : vec_use_group (vid, targ_use, STORE_P)
  {}
};

class target_use_info
{
public:
  tree root_ref;

  auto_delete_vec<read_vu_group> read_groups;
  auto_delete_vec<write_vu_group> write_groups;
  auto_vec<gimple *> write_nulls;

  unsigned num_reads;
  unsigned num_writes;
  unsigned num_null_writes;
  bool read_only_p;

private:
  hash_map<gimple *, vec_use_info *> vec_use_map;
  hash_set<gimple *> extra_del_stmts_set;
  auto_vec<gimple *> extra_del_stmts;
  auto_bitmap read_bm;
  auto_bitmap write_bm;
  auto_bitmap zero_write_bm;
  auto_bitmap release_ssa_bm;

public:
  void transform_targ_use ();
  void dump_target_use ();

  bool no_vec_use ()
  {
    return num_reads == 0 && num_writes == 0 && num_null_writes == 0;
  }

  void init_vec_use_group (ACCESS_KIND);
  bool add_root_stmt (gimple *, unsigned, ACCESS_KIND);
  void map_vec_use (gimple *, vec_use_info *);

  void mark_release_ssa (gimple *);

  vec_use_info *get_vec_use (gimple *);
  bool contains (gimple *stmt);
  vec_use_info *get_vec_use (tree);
  bool collect_vec_uses ();
  bool add_extra_del (gimple *);
  bool add_extra_del (tree);

  bool other_use_p (gimple *stmt, unsigned vid = UINT_MAX);
  bool other_use_p (tree var, unsigned vid = UINT_MAX);
  bool mem_pool_ssa_p (tree);
  bool load_from_mem_pool_p (tree);
  bool vec_field_ssa_p (tree, VEC_FIELD_KIND, unsigned vid = UINT_MAX);
  bool vec_field_p (gimple *, VEC_FIELD_KIND, unsigned, ACCESS_KIND);
  bool vec_idx_elt_ssa_p (tree, unsigned, tree);

  bool extract_vec_idx (tree, VEC_FIELD_KIND, unsigned &);
  bool extract_vec_field_idx (gimple *, VEC_FIELD_KIND &, unsigned &);

  bool extract_use (gimple *, other_vec_use *&);
  bool extract_use (gimple *, unsigned, field_vec_use *&);
  bool extract_use (gimple *, field_vec_use *&);
  bool extract_use (gimple *, unsigned, idx_elt_vec_use *&);

  bool extract_init_check (basic_block, edge &, edge &, unsigned *vid = NULL);

  bool all_uses_checked_p ();

  bool each_vec_def_p (ACCESS_KIND acc_kind)
  {
    return acc_kind == LOAD_P ? bitmap_count_bits (read_bm) == num_vecs
			      : bitmap_count_bits (write_bm) == num_vecs;
  }

  bool once_each_vec_write_null_p ()
  {
    return bitmap_count_bits (zero_write_bm) == num_vecs
	   && num_null_writes == num_vecs;
  }

  bool once_each_vec_def_p (ACCESS_KIND acc_kind)
  {
    TEST (each_vec_def_p (acc_kind))
    return acc_kind == LOAD_P ? num_reads == num_vecs : num_writes == num_vecs;
  }

  target_use_info (tree root_ref)
    : root_ref (root_ref), num_reads (0), num_writes (0), num_null_writes (0),
      read_only_p (true)
  {}
};

template <>
template <>
inline bool
is_a_helper<field_vec_use *>::test (vec_use_info *vu)
{
  return vu->vu_kind == VU_VEC_FIELD;
}

template <>
template <>
inline bool
is_a_helper<init_check_vec_use *>::test (vec_use_info *vu)
{
  return vu->vu_kind == VU_VEC_INIT_CHECK;
}

template <>
template <>
inline bool
is_a_helper<idx_elt_vec_use *>::test (vec_use_info *vu)
{
  return vu->vu_kind == VU_INDEXED_ELT;
}

template <>
template <>
inline bool
is_a_helper<other_vec_use *>::test (vec_use_info *vu)
{
  return vu->vu_kind == VU_OTHER;
}

struct base_info_hasher : nofree_ptr_hash<target_use_info>
{
  static inline hashval_t hash (const target_use_info *ui)
  {
    inchash::hash hstate;
    inchash::add_expr (ui->root_ref, hstate, OEP_ADDRESS_OF);
    return hstate.end ();
  }

  static inline bool equal (const target_use_info *ui1,
			    const target_use_info *ui2)
  {
    return operand_equal_p (ui1->root_ref, ui2->root_ref, OEP_ADDRESS_OF);
  }
};

class piece_info
{
public:
  unsigned vid;
  basic_block entry_bb;
  edge taken_edge;
  edge other_edge;

  void init (unsigned vid, basic_block entry_bb)
  {
    this->vid = vid;
    this->entry_bb = entry_bb;
  }

  piece_info () : vid (UINT_MAX), entry_bb (NULL) {}
};

class zeroing_piece : public piece_info
{
public:
  gimple *memset_zero_call;
  idx_elt_vec_use *set_zero_idx_elt;

  zeroing_piece () : memset_zero_call (NULL), set_zero_idx_elt (NULL) {}
};

class init_vec_piece : public piece_info
{
public:
  gimple_stmt_iterator start_gsi;
  gimple_stmt_iterator end_gsi;
  gimple *alloc_stmt;

  tree num_maxcnt;
  gimple *vec_alloc;
  gimple *list_alloc;

  zeroing_piece zero_piece;

  init_vec_piece () : num_maxcnt (NULL_TREE) {}
};

class init_vecs_piece : public piece_info
{
public:
  auto_vec<init_vec_piece> init_pieces;
};

class idx_of_elt_piece : public piece_info
{
public:
  tree found_idx;
  idx_of_elt_piece () : found_idx (NULL_TREE) {}
};

class ensure_cap_piece : public piece_info
{
public:
  gimple *list_alloc;
  idx_elt_vec_use *old_elt_load;
  idx_elt_vec_use *new_elt_store;
  zeroing_piece zero_piece;

  ensure_cap_piece ()
    : list_alloc (NULL), old_elt_load (NULL), new_elt_store (NULL)
  {}
};

class replic_elt_piece : public piece_info
{
public:
  gphi *new_elt;
  tree src_elt;
  replic_elt_piece () : new_elt (NULL), src_elt (NULL_TREE) {}
};

class add_elt_piece : public piece_info
{
public:
  idx_elt_vec_use *elt_store;
  field_vec_use *curcnt_update;

  ensure_cap_piece ensure_piece;
  replic_elt_piece replic_piece;
};

class free_elt_piece : public piece_info
{
public:
  gimple *elt_dealloc;

  free_elt_piece () : elt_dealloc (NULL) {}
};

class set_elt_piece : public piece_info
{
public:
  replic_elt_piece replic_piece;
  free_elt_piece free_piece;
};

class vec_dtor_piece : public piece_info
{
public:
  gimple *vec_dealloc;
  gimple *list_dealloc;
  free_elt_piece free_piece;
  vec_dtor_piece () : vec_dealloc (NULL), list_dealloc (NULL) {}
};

class copy_vec_piece : public piece_info
{
public:
  basic_block end_bb;

  gimple *vec_alloc;
  gimple *list_alloc;
  idx_elt_vec_use *copy_from_elt;
  idx_elt_vec_use *copy_to_elt;
  vec_use_info *update_curcnt;

  replic_elt_piece replic_piece;
  ensure_cap_piece ensure_piece;
  zeroing_piece zero_piece;

  copy_vec_piece ()
    : end_bb (NULL), vec_alloc (NULL), list_alloc (NULL), copy_from_elt (NULL),
      copy_to_elt (NULL)
  {}
};

enum FMO_PATT_KIND
{
  PATT_INSERT_ELTS,
  PATT_INIT_CTOR,
  PATT_COPY_CTOR,
  PATT_DTOR,
  PATT_PURE,
  PATT_LEN
};

static const char *patt_names[PATT_LEN]
  = { "INSERT ELTS", "INIT CTOR", "COPY CTOR", "DTOR", "PURE" };

class pattern_info
{
public:
  function *fun;
  target_use_info *targ_use;
  FMO_PATT_KIND pt_kind;

private:
  bool init_loop_p;

public:
  virtual void transform_patt () = 0;
  virtual void dump_patt ();

  pattern_info (target_use_info *targ_use, FMO_PATT_KIND pt_kind,
		bool init_loop_p = false)
    : fun (cfun), targ_use (targ_use), pt_kind (pt_kind),
      init_loop_p (init_loop_p)
  {
    if (init_loop_p)
      loop_optimizer_init (LOOPS_NORMAL | LOOPS_HAVE_RECORDED_EXITS);
  }

  virtual ~pattern_info ()
  {
    if (init_loop_p)
      {
	cfun_context ctx (fun);
	loop_optimizer_finalize ();
      }
  };
};

static void
dump_action_in_func (const char *action, const char *arg = NULL,
		     function *fun = NULL)
{
  if (!fun)
    fun = cfun;

  if (arg)
    fprintf (dump_file, action, arg);
  else
    fprintf (dump_file, "%s", action);

  fprintf (dump_file, " in func ");
  print_generic_expr (dump_file, fun->decl, TDF_SLIM);
  fprintf (dump_file, " (no %d):\n", fun->funcdef_no);
}

class dtor_pattern : public pattern_info
{
public:
  auto_vec<vec_dtor_piece> dtor_pieces;

  static bool find_dtor_patt (target_use_info *targ_use);
  bool check_patt ();
  bool check_destroy_one_vec (vec_dtor_piece &);
  bool check_free_all_elts (free_elt_piece &);
  void transform_patt ();

  dtor_pattern (target_use_info *targ_use)
    : pattern_info (targ_use, PATT_DTOR, /* init_loop_p */ true)
  {
    dtor_pieces.safe_grow_cleared (num_vecs, true);
  }
  virtual ~dtor_pattern () {};
};

class ctor_pattern : public pattern_info
{
public:
  void transform_init_zero ();

  ctor_pattern (target_use_info *targ_use, FMO_PATT_KIND pt_kind,
		bool init_loop_p = false)
    : pattern_info (targ_use, pt_kind, init_loop_p)
  {}
  virtual ~ctor_pattern () {}
};

class init_ctor_pattern : public ctor_pattern
{
public:
  static bool find_init_ctor_patt (target_use_info *);
  void transform_patt ();

  init_ctor_pattern (target_use_info *targ_use)
    : ctor_pattern (targ_use, PATT_INIT_CTOR)
  {}
  virtual ~init_ctor_pattern () {}
};

class copy_ctor_pattern : public ctor_pattern
{
public:
  target_use_info *other_use;
  auto_vec<copy_vec_piece> copy_pieces;

  static bool find_copy_ctor_patt (auto_vec<target_use_info *> &);
  bool check_patt ();
  void transform_patt ();

  void dump_patt ()
  {
    pattern_info::dump_patt ();
    other_use->dump_target_use ();
  }

  copy_ctor_pattern (target_use_info *targ_use, target_use_info *other_use)
    : ctor_pattern (targ_use, PATT_COPY_CTOR, true), other_use (other_use)
  {
    copy_pieces.safe_grow_cleared (num_vecs, true);
  }
  virtual ~copy_ctor_pattern () {}

private:
  bool check_copy_one_vec (copy_vec_piece &);
  bool check_copy_elt_loop (copy_vec_piece &, basic_block);
  bool check_copy_replic_elt_loop (copy_vec_piece &, basic_block);
  bool load_from_mem_pool_p (tree);
  bool vec_field_ssa_p (tree, VEC_FIELD_KIND);
};

class pure_pattern : public pattern_info
{
public:
  static bool find_pure_patt (target_use_info *, bool &);
  bool check_profitable ();
  void transform_patt ();

  pure_pattern (target_use_info *targ_use) : pattern_info (targ_use, PATT_PURE)
  {}
  virtual ~pure_pattern () {}
};

class collect_dom_bb_walker;

class insert_elts_pattern : public pattern_info
{
private:
  auto_vec<tree> src_elts;

  init_vecs_piece init_piece;
  idx_of_elt_piece idx_piece;
  auto_vec<add_elt_piece> add_pieces;
  auto_vec<set_elt_piece> set_pieces;

public:
  static bool find_insert_elts_patt (target_use_info *, auto_vec<tree> &);
  bool check_patt ();

  virtual void transform_patt ();

  unsigned get_src_elt_idx (tree src_elt)
  {
    for (unsigned i = 0; i < num_vecs; i++)
      if (this->src_elts[i] == src_elt)
	return i;
    return UINT_MAX;
  }

  bool check_init_vecs ();
  bool check_index_of_elt ();
  bool check_add_elts ();
  bool check_set_elts ();

  bool check_init_one_vec (unsigned, hash_set<basic_block> &);
  bool check_add_one_elt (basic_block, add_elt_piece &, unsigned);
  bool check_set_one_elt (basic_block &, set_elt_piece &);
  bool check_free_one_elt (free_elt_piece &);

  void transform_init_vecs ();
  void transform_set_elts ();
  void transform_add_elts ();

  insert_elts_pattern (target_use_info *targ_use, auto_vec<tree> &src_elts)
    : pattern_info (targ_use, PATT_INSERT_ELTS, true)
  {
    this->src_elts.safe_splice (src_elts);

    init_piece.init_pieces.safe_grow_cleared (num_vecs, true);
    set_pieces.safe_grow_cleared (num_vecs - 1, true);
    add_pieces.safe_grow_cleared (num_vecs, true);
  }
  virtual ~insert_elts_pattern () {}
};

#define SET_BOOL_JUST_ONCE(flag) \
  if (flag) \
    return false; \
  flag = true;

#define SET_BIT_JUST_ONCE(flag, bit) \
  if (flag & (1 << bit)) \
    return false; \
  flag |= (1 << bit);

#define B_0011 3
#define B_0111 7
#define B_0001_1111 31
#define B_0011_1111 63

#define SET_VAR_JUST_ONCE(var, value) \
  if (var) \
    return false; \
  var = value;

#define SET_SINGLE_VALUE(var, val) \
  if (var != NULL && var != val) \
    return false; \
  var = val;

bool
extract_hwi (tree val, HOST_WIDE_INT &hwi)
{
  TEST (cst_and_fits_in_hwi (val))
  hwi = int_cst_value (val);
  return true;
}

static inline bool
ssa_var_p (tree var)
{
  return TREE_CODE (var) == SSA_NAME;
}
static inline gimple *
get_ssa_def_stmt (tree opnd)
{
  return ssa_var_p (opnd) ? SSA_NAME_DEF_STMT (opnd) : NULL;
}

static inline bool
gimple_assign_store_p (gimple *stmt)
{
  return gimple_store_p (stmt) && gimple_assign_single_p (stmt);
}

static inline bool
get_ref_base_and_offset_hwi (tree ref, tree &base, HOST_WIDE_INT &offset)
{
  HOST_WIDE_INT size;
  bool reverse;
  base = get_ref_base_and_extent_hwi (ref, &offset, &size, &reverse);
  return base != NULL;
}

static void
dump_gimples (auto_vec<gimple *> &gimples)
{
  unsigned i;
  gimple *stmt;

  FOR_EACH_VEC_ELT (gimples, i, stmt)
    print_gimple_stmt (dump_file, stmt, 0, TDF_NONE);
}

static bool
ref_of_addr_p (tree ref, tree base)
{
  switch (TREE_CODE (ref))
    {
    case MEM_REF:
      {
	tree opnd0 = TREE_OPERAND (ref, 0);
	tree opnd1 = TREE_OPERAND (ref, 1);
	if (strict_type_analysis
	    && !types_matched_p (TREE_TYPE (ref),
				 TREE_TYPE (TREE_TYPE (base))))
	  return false;
	return operand_equal_p (opnd0, base, OEP_ADDRESS_OF)
	       && integer_zerop (opnd1);
      }
    case COMPONENT_REF:
      {
	HOST_WIDE_INT offset, size;
	bool reverse;
	tree bas = get_ref_base_and_extent_hwi (ref, &offset, &size, &reverse);
	TEST (bas != NULL_TREE && offset == 0)

	return ref_of_addr_p (bas, base);
      }
    default:
      return false;
    }
}

static bool
mem_ref_of_addr_p (tree mem_ref, tree ptr, tree offset)
{
  TEST (TREE_CODE (mem_ref) == MEM_REF)
  tree opnd0 = TREE_OPERAND (mem_ref, 0);
  tree opnd1 = TREE_OPERAND (mem_ref, 1);
  return operand_equal_p (opnd0, ptr, OEP_ADDRESS_OF)
	 && tree_int_cst_equal (opnd1, offset);
}

static bool
mem_ref_of_addr_p (tree mem_ref, tree ptr)
{
  TEST (TREE_CODE (mem_ref) == MEM_REF)
  tree opnd0 = TREE_OPERAND (mem_ref, 0);
  tree opnd1 = TREE_OPERAND (mem_ref, 1);
  return operand_equal_p (opnd0, ptr, OEP_ADDRESS_OF) && integer_zerop (opnd1);
}

static bool
extract_base_ref_of_addr (tree expr, tree base, tree &fld, tree &base_ref_type)
{
  TEST (TREE_CODE (expr) == COMPONENT_REF)
  tree base_ref = TREE_OPERAND (expr, 0);
  fld = TREE_OPERAND (expr, 1);
  base_ref_type = TREE_TYPE (base_ref);
  return ref_of_addr_p (base_ref, base);
}

static bool
get_field_bit_offset (tree fld, HOST_WIDE_INT &offset)
{
  HOST_WIDE_INT off_fld, boff_fld;
  TEST (extract_hwi (DECL_FIELD_OFFSET (fld), off_fld)
	&& extract_hwi (DECL_FIELD_BIT_OFFSET (fld), boff_fld))
  offset = off_fld * BITS_PER_UNIT + boff_fld;
  return true;
}

static bool
extract_mem_ref (tree mem_ref, tree &base, tree &offset)
{
  TEST (TREE_CODE (mem_ref) == MEM_REF)
  base = TREE_OPERAND (mem_ref, 0);
  offset = TREE_OPERAND (mem_ref, 1);
  return ssa_var_p (base) && POINTER_TYPE_P (TREE_TYPE (base));
}

static bool
extract_comp_ref (tree comp_ref, tree &base_ref, tree &field)
{
  TEST (TREE_CODE (comp_ref) == COMPONENT_REF)
  base_ref = TREE_OPERAND (comp_ref, 0);
  field = TREE_OPERAND (comp_ref, 1);
  return TREE_CODE (field) == FIELD_DECL;
}

bool
extract_succ_with_eh_edge (basic_block bb, edge &normal_edge, edge &eh_edge)
{
  TEST (EDGE_COUNT (bb->succs) == 2)
  normal_edge = eh_edge = NULL;
  edge e;
  edge_iterator ei;

  FOR_EACH_EDGE (e, ei, bb->succs)
    {
      if (e->flags & (EDGE_ABNORMAL | EDGE_EH))
	eh_edge = e;
      else
	normal_edge = e;
    }

  return eh_edge && normal_edge;
}

bool
extract_succ_with_eh_edge (basic_block bb, edge &eh_edge)
{
  edge normal_edge;
  return extract_succ_with_eh_edge (bb, normal_edge, eh_edge);
}

static inline bool
extract_store_ref (gimple *stmt, tree &ref)
{
  TEST (stmt != NULL && gimple_assign_store_p (stmt))
  ref = gimple_assign_lhs (stmt);
  return true;
}
static inline bool
extract_load_ref (gimple *stmt, tree &ref)
{
  TEST (stmt != NULL && gimple_assign_load_p (stmt))
  ref = gimple_assign_rhs1 (stmt);
  return true;
}
static inline bool
extract_ssa_load_ref (tree lhs, tree &ref)
{
  return extract_load_ref (get_ssa_def_stmt (lhs), ref);
}
static bool
extract_load_store_ref (gimple *stmt, tree &ref, ACCESS_KIND &acc_kind)
{
  acc_kind = LOAD_P;
  if (extract_load_ref (stmt, ref))
    return true;

  acc_kind = STORE_P;
  return extract_store_ref (stmt, ref);
}

static bool
extract_field_of_ssa_load (tree lhs, tree base, tree &field)
{
  tree load_ref, base_ref;
  TEST (extract_ssa_load_ref (lhs, load_ref))
  TEST (extract_comp_ref (load_ref, base_ref, field))

  return ref_of_addr_p (base_ref, base);
}

extern bool
gimple_assign_rhs_code_p (gimple *stmt, enum tree_code code)
{
  TEST (stmt != NULL && is_gimple_assign (stmt))
  return gimple_assign_rhs_code (stmt) == code;
}

static bool
extract_ptr_plus (tree lhs, tree &ptr, tree &offset)
{
  gimple *def_stmt = SSA_NAME_DEF_STMT (lhs);
  TEST (gimple_assign_rhs_code_p (def_stmt, POINTER_PLUS_EXPR))

  ptr = gimple_assign_rhs1 (def_stmt);
  offset = gimple_assign_rhs2 (def_stmt);
  return true;
}
static bool
extract_ptr_plus (gimple *stmt, tree &lhs, tree &ptr, tree &offset)
{
  TEST (gimple_assign_rhs_code_p (stmt, POINTER_PLUS_EXPR))

  lhs = gimple_assign_lhs (stmt);
  ptr = gimple_assign_rhs1 (stmt);
  offset = gimple_assign_rhs2 (stmt);
  return ssa_var_p (lhs) && ssa_var_p (ptr) && ssa_var_p (offset);
}

static bool
extract_mult_rhs (tree lhs, tree &rhs1, tree &rhs2)
{
  gimple *def_stmt = get_ssa_def_stmt (lhs);
  TEST (def_stmt != NULL && gimple_assign_rhs_code_p (def_stmt, MULT_EXPR))

  rhs1 = gimple_assign_rhs1 (def_stmt);
  rhs2 = gimple_assign_rhs2 (def_stmt);
  return true;
}

static bool
extract_plus_rhs (tree lhs, tree &rhs1, tree &rhs2)
{
  gimple *def_stmt = get_ssa_def_stmt (lhs);
  TEST (def_stmt != NULL && gimple_assign_rhs_code_p (def_stmt, PLUS_EXPR))

  rhs1 = gimple_assign_rhs1 (def_stmt);
  rhs2 = gimple_assign_rhs2 (def_stmt);
  return true;
}

static bool
extract_plus_one (tree lhs, tree &rhs1)
{
  gimple *def_stmt = get_ssa_def_stmt (lhs);
  TEST (def_stmt != NULL && gimple_assign_rhs_code_p (def_stmt, PLUS_EXPR))

  rhs1 = gimple_assign_rhs1 (def_stmt);
  tree rhs2 = gimple_assign_rhs2 (def_stmt);
  return integer_onep (rhs2);
}

static tree
strip_int_ssa_var_cast (tree opnd)
{
  gimple *stmt = get_ssa_def_stmt (opnd);
  if (!stmt || !is_gimple_assign (stmt))
    return opnd;

  tree rhs = gimple_assign_rhs1 (stmt);
  if (ssa_var_p (rhs) && gimple_assign_rhs_code_p (stmt, NOP_EXPR)
      && TREE_CODE (TREE_TYPE (rhs)) == INTEGER_TYPE)
    return rhs;

  return opnd;
}

static bool
unscale_offset (tree offset, tree factor, tree &unscaled)
{
  tree fac, input;
  TEST (extract_mult_rhs (offset, input, fac))
  TEST (tree_int_cst_equal (fac, factor))

  unscaled = strip_int_ssa_var_cast (input);
  return true;
}

static bool
vptr_field_p (tree field, tree type)
{
  gcc_checking_assert (TREE_CODE (field) == FIELD_DECL);

  if (!DECL_VIRTUAL_P (field))
    return false;

  return types_matched_p (DECL_CONTEXT (field), type);
}

extern bool
extract_gimple_cond (gimple *cond_stmt, tree_code exp_code, tree &lhs,
		     tree &rhs, bool &invert_p)
{
  tree_code code = gimple_cond_code (cond_stmt);
  invert_p = false;
  bool swap_p = false;

  if (code != exp_code)
    {
      tree_code invert_code = invert_tree_comparison (code, false);
      invert_p = (invert_code == exp_code);
      swap_p = (swap_tree_comparison (code) == exp_code);
      if (!invert_p && !swap_p)
	{
	  TEST (swap_tree_comparison (invert_code) == exp_code)
	  invert_p = swap_p = true;
	}
    }

  lhs = gimple_cond_lhs (cond_stmt);
  rhs = gimple_cond_rhs (cond_stmt);

  if (code != exp_code)
    if (swap_p)
      std::swap (lhs, rhs);

  return true;
}

extern bool
extract_block_cond (basic_block bb, tree_code exp_code, tree &lhs, tree &rhs,
		    basic_block &true_dest, basic_block &false_dest)
{
  gimple *stmt = last_stmt (bb);
  TEST (stmt != NULL && gimple_code (stmt) == GIMPLE_COND)

  bool invert_p;
  TEST (extract_gimple_cond (stmt, exp_code, lhs, rhs, invert_p))

  edge e_true, e_false;
  extract_true_false_edges_from_block (bb, &e_true, &e_false);
  true_dest = e_true->dest;
  false_dest = e_false->dest;

  if (invert_p)
    std::swap (true_dest, false_dest);

  return true;
}

static bool
extract_stmt_cond (gimple *stmt, tree_code exp_code, tree &lhs, tree &rhs,
		   edge &e_true, edge &e_false)
{
  TEST (stmt != NULL && gimple_code (stmt) == GIMPLE_COND)

  bool invert_p;
  TEST (extract_gimple_cond (stmt, exp_code, lhs, rhs, invert_p))

  extract_true_false_edges_from_block (gimple_bb (stmt), &e_true, &e_false);
  if (invert_p)
    std::swap (e_true, e_false);

  return true;
}
static inline bool
extract_block_cond (basic_block bb, tree_code exp_code, tree &lhs, tree &rhs,
		    edge &e_true, edge &e_false)
{
  return extract_stmt_cond (last_stmt (bb), exp_code, lhs, rhs, e_true,
			    e_false);
}
static bool
extract_block_cond (basic_block bb, tree_code exp_code, tree &lhs, tree &rhs)
{
  edge edges[2];
  TEST (extract_block_cond (bb, exp_code, lhs, rhs, edges[0], edges[1]))
  return true;
}
static bool
extract_zerop_cond (basic_block bb, tree &var, edge &e_true, edge &e_false)
{
  tree zero;
  TEST (extract_stmt_cond (last_stmt (bb), EQ_EXPR, var, zero, e_true, e_false))

  return integer_zerop (zero);
}

static inline tree
build_field_ref (tree base, tree field_decl)
{
  return build3 (COMPONENT_REF, TREE_TYPE (field_decl),
		 build_simple_mem_ref (base), field_decl, NULL_TREE);
}

static inline gassign *
build_assign_at_gsi (gimple_stmt_iterator *gsi, bool before, tree lhs, tree op1,
		     enum tree_code code = NOP_EXPR, tree op2 = NULL_TREE)
{
  gassign *stmt;

  if (op2)
    stmt = gimple_build_assign (lhs, code, op1, op2);
  else
    stmt = gimple_build_assign (lhs, op1);

  if (before)
    gsi_insert_before (gsi, stmt, GSI_NEW_STMT);
  else
    gsi_insert_after (gsi, stmt, GSI_NEW_STMT);
  return stmt;
}
static inline gimple *
build_assign_before_stmt (tree lhs, tree rhs, gimple *stmt)
{
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  return build_assign_at_gsi (&gsi, true, lhs, rhs);
}
static inline gimple *
build_assign_after_stmt (tree lhs, tree rhs, gimple *stmt)
{
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  return build_assign_at_gsi (&gsi, false, lhs, rhs);
}
static inline gimple *
build_assign_after_bb (basic_block bb, tree lhs, tree op1,
		       enum tree_code code = NOP_EXPR, tree op2 = NULL_TREE)
{
  gimple_stmt_iterator gsi = gsi_last_bb (bb);
  return build_assign_at_gsi (&gsi, false, lhs, op1, code, op2);
}

static bool
remove_stmt (gimple *stmt)
{
  TEST (gimple_bb (stmt))

  unlink_stmt_vdef (stmt);
  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
  return gsi_remove (&gsi, true);
}

static inline gimple *
build_assign_last_bb (basic_block bb, tree lhs, tree rhs)
{
  gimple_stmt_iterator gsi = gsi_last_bb (bb);
  return build_assign_at_gsi (&gsi, false, lhs, rhs);
}

static inline int
field_offset_cmp (const void *p, const void *q)
{
  HOST_WIDE_INT a = ((const std::pair<tree, HOST_WIDE_INT> *) p)->second;
  HOST_WIDE_INT b = ((const std::pair<tree, HOST_WIDE_INT> *) q)->second;

  if (a < b)
    return -1;
  if (a > b)
    return 1;
  return 0;
}

static void
remove_stmt (gimple *stmt, target_use_info *targ_use)
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> Removing: ");
      print_gimple_stmt (dump_file, stmt, 0, TDF_NONE);
    }

  vec_use_info *vec_use = targ_use->get_vec_use (stmt);
  if (vec_use)
    vec_use->vt_status = VT_DONE;

  targ_use->mark_release_ssa (stmt);
  remove_stmt (stmt);
}

static void
delete_block_with_vec_uses (basic_block bb, target_use_info *targ_use,
			    target_use_info *other_use = NULL)
{
  if (gphi *vphi = get_virtual_phi (bb))
    {
      gimple_stmt_iterator gsi = gsi_for_stmt (vphi);
      remove_phi_node (&gsi, false);
    }

  gimple_stmt_iterator gsi;
  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      unlink_stmt_vdef (stmt);

      vec_use_info *vec_use = targ_use->get_vec_use (stmt);
      if (!vec_use && other_use)
	vec_use = other_use->get_vec_use (stmt);

      if (vec_use)
	vec_use->vt_status = VT_DONE;
    }

  delete_basic_block (bb);
}

class collect_dom_bb_walker : public dom_walker
{
  basic_block end_bb;
  hash_set<basic_block> blocks_set;
  auto_vec<basic_block> blocks;

  bool add_bb (basic_block bb)
  {
    if (!blocks_set.add (bb))
      {
	blocks.safe_push (bb);
	return false;
      }
    return true;
  }

public:
  collect_dom_bb_walker (cdi_direction direction, basic_block end_bb = NULL,
			 bool add_end_p = false)
    : dom_walker (direction, REACHABLE_BLOCKS, NULL), end_bb (end_bb)
  {
    if (add_end_p && end_bb)
      add_bb (end_bb);
  }

  virtual edge before_dom_children (basic_block bb)
  {
    if (bb == end_bb)
      return STOP;
    add_bb (bb);
    return NULL;
  }

  void reset_and_walk (basic_block start_bb, basic_block end_bb,
		       bool add_end_p = false)
  {
    this->end_bb = end_bb;
    if (add_end_p)
      add_bb (end_bb);

    walk (start_bb);
  }

  void delete_bbs (target_use_info *targ_use, target_use_info *other_use = NULL)
  {
    for (auto bb : blocks)
      delete_block_with_vec_uses (bb, targ_use, other_use);
  }

  bool contains (gimple *stmt)
  {
    basic_block bb = gimple_bb (stmt);
    return blocks_set.contains (bb);
  }
};

class fallthru_bb_walker
{
  basic_block end_bb;

public:
  fallthru_bb_walker (basic_block end_bb) : end_bb (end_bb) {}

  bool collect_gimple_calls (basic_block &, auto_vec<gimple *> &,
			     auto_vec<edge> &)
  {
    return true;
  }
};

static void
remove_edge_and_dom_bbs (edge edge, target_use_info *targ_use)
{
  basic_block next_bb = edge->dest;
  if (!single_pred_p (next_bb))
    {
      remove_edge (edge);
      return;
    }

  collect_dom_bb_walker walker (CDI_DOMINATORS);
  walker.walk (next_bb);
  walker.delete_bbs (targ_use);
}

static bool
extract_otr_callee (gimple *gcall, tree &expr, tree &token, tree &vptr,
		    tree &vptr_offset)
{
  TEST (gimple_code (gcall) == GIMPLE_CALL)
  tree callee = gimple_call_fn (gcall);
  TEST (callee != NULL_TREE && TREE_CODE (callee) == OBJ_TYPE_REF)

  expr = OBJ_TYPE_REF_EXPR (callee);
  token = OBJ_TYPE_REF_TOKEN (callee);

  gimple *expr_stmt = get_ssa_def_stmt (expr);
  TEST (expr_stmt != NULL
	&& extract_mem_ref (gimple_assign_rhs1 (expr_stmt), vptr, vptr_offset))

  TEST (ssa_var_p (vptr) && TREE_CODE (vptr_offset) == INTEGER_CST)
  return true;
}

static bool
extract_single_call_in_bb (basic_block bb, gimple *&gcall)
{
  gimple_stmt_iterator gsi;
  gcall = NULL;

  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (gimple_code (stmt) == GIMPLE_CALL)
	{
	  SET_VAR_JUST_ONCE (gcall, stmt)
	}
    }
  return gcall != NULL;
}

static bool
extract_call_as_bb_last (basic_block bb, gimple *&gcall)

{
  gcall = last_stmt (bb);
  return gcall && gimple_code (gcall) == GIMPLE_CALL;
}

bool
extract_one_of_two_uses (tree var, gimple *other, gimple *&stmt)
{
  gcc_checking_assert (ssa_var_p (var));

  stmt = NULL;
  gimple *use_stmt;
  imm_use_iterator imm_iter;

  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, var)
    {
      if (is_gimple_debug (use_stmt))
	continue;

      if (use_stmt != other)
	stmt = use_stmt;
    }

  return true;
}

static bool
memset_call_p (gimple *stmt)
{
  return stmt && gimple_call_builtin_p (stmt, BUILT_IN_MEMSET);
}

static bool
extract_memset_zero (gimple *stmt, tree &ptr, tree &size)
{
  TEST (integer_zerop (gimple_call_arg (stmt, 1)))

  ptr = gimple_call_arg (stmt, 0);
  size = gimple_call_arg (stmt, 2);
  return true;
}

static bool
bb_return_p (basic_block next_bb)
{
  gimple_stmt_iterator gsi;

  for (gsi = gsi_start_bb (next_bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (!is_gimple_debug (stmt))
	return gimple_code (stmt) == GIMPLE_RETURN;
    }
  return false;
}

static bool
extract_simp_inner_loop (basic_block prehead, class loop *&loop,
			 edge &exit_edge)
{
  TEST (single_succ_p (prehead))

  basic_block head_bb = single_succ (prehead);
  loop = head_bb->loop_father;
  TEST (loop != NULL && loop->header == head_bb && loop->inner == NULL)

  auto_vec<edge> exits = get_loop_exit_edges (loop);
  TEST (exits.length () == 1)
  exit_edge = exits[0];
  return true;
}

static bool
extract_simp_innermost_loop_with_eh (basic_block prehead, class loop *&loop,
				     edge &exit_edge, edge &eh_edge)
{
  TEST (single_succ_p (prehead))

  basic_block head_bb = single_succ (prehead);
  loop = head_bb->loop_father;
  TEST (loop != NULL && loop->header == head_bb && loop->inner == NULL)

  auto_vec<edge> exits = get_loop_exit_edges (loop);
  if (exits.length () == 1)
    {
      exit_edge = exits[0];
    }
  else
    {
      TEST (exits.length () == 2)
      exit_edge = exits[0];
      eh_edge = exits[1];
      TEST (!(exit_edge->flags & (EDGE_ABNORMAL | EDGE_EH)))
      TEST ((eh_edge->flags & (EDGE_ABNORMAL | EDGE_EH)))
    }
  return true;
}

bool
check_loop_iter_plus_one (class loop *loop, tree var, tree &init)
{
  gimple *idx_def = get_ssa_def_stmt (var);
  TEST (idx_def != NULL && gimple_code (idx_def) == GIMPLE_PHI
	&& gimple_bb (idx_def) == loop->header)

  gphi *idx_phi = as_a<gphi *> (idx_def);
  tree inc_idx = PHI_ARG_DEF_FROM_EDGE (idx_phi, loop_latch_edge (loop));
  init = PHI_ARG_DEF_FROM_EDGE (idx_phi, loop_preheader_edge (loop));

  tree rhs1, rhs2;
  return extract_plus_rhs (inc_idx, rhs1, rhs2) && rhs1 == var
	 && integer_onep (rhs2);
}

bool
check_loop_iter_plus_one_from_zero (class loop *loop, tree var)
{
  tree init;
  return check_loop_iter_plus_one (loop, var, init) && integer_zerop (init);
}

static bool
extract_fallthru_bb_calls (basic_block next_bb, basic_block end_bb,
			   hash_set<basic_block> &fallthru_bbs, gimple *&gcall0,
			   gimple *&gcall1, auto_vec<edge> &eh_edges)
{
  auto_vec<gimple *> gcalls;
  gimple_stmt_iterator gsi;

  do
    {
      fallthru_bbs.add (next_bb);

      for (gsi = gsi_start_bb (next_bb); !gsi_end_p (gsi); gsi_next (&gsi))
	{
	  gimple *stmt = gsi_stmt (gsi);
	  if (gimple_code (stmt) == GIMPLE_CALL)
	    gcalls.safe_push (stmt);
	}

      if (single_succ_p (next_bb))
	next_bb = single_succ (next_bb);
      else
	{
	  edge normal_edge = NULL, eh_edge = NULL;
	  TEST (extract_succ_with_eh_edge (next_bb, normal_edge, eh_edge))
	  next_bb = normal_edge->dest;
	  eh_edges.safe_push (eh_edge);
	}
    }
  while (next_bb != end_bb || fallthru_bbs.contains (next_bb));

  TEST (gcalls.length () == 2)
  gcall0 = gcalls[0];
  gcall1 = gcalls[1];
  return true;
}

bool
target_type_info::otr_mem_func_p (gimple *stmt, target_use_info *targ_use,
				  ALLOC_KIND alloc_kind, unsigned vid)
{
  TEST (check_otr_mem_func (stmt, alloc_kind))
  tree otr_arg0 = gimple_call_arg (stmt, 0);

  return vid == UINT_MAX
	   ? targ_use->mem_pool_ssa_p (otr_arg0)
	   : targ_use->vec_field_ssa_p (otr_arg0, F_MEM_POOL, vid);
}

bool
target_type_info::check_otr_mem_func (gimple *stmt, ALLOC_KIND alloc_kind)
{
  tree expr, vptr, args[2];
  TEST (extract_otr_mem_func (stmt, alloc_kind, expr, vptr, args[0], args[1]))
  return true;
}

static inline bool
func_attr_match_alloc_kind_p (gcall *call_stmt, ALLOC_KIND alloc_kind)
{
  tree fntype = gimple_call_fntype (call_stmt);

  if (!fntype)
    return false;

  if (alloc_kind == ALLOC_P)
    {
      TEST (lookup_attribute ("cxx_new", TYPE_ATTRIBUTES (fntype)))
    }
  else
    {
      TEST (lookup_attribute ("cxx_delete", TYPE_ATTRIBUTES (fntype)))
    }
  return true;
}

bool
target_type_info::extract_otr_mem_func (gimple *stmt, ALLOC_KIND alloc_kind,
					tree &expr, tree &vptr, tree &arg0,
					tree &arg1)
{
  TEST ((alloc_kind == ALLOC_P) ^ (gimple_call_lhs (stmt) == NULL_TREE))

  gcall *call_stmt = as_a<gcall *> (stmt);
  TEST (func_attr_match_alloc_kind_p (call_stmt, alloc_kind))
  TEST (gimple_call_num_args (call_stmt) == 2)
  arg0 = gimple_call_arg (call_stmt, 0);
  arg1 = gimple_call_arg (call_stmt, 1);

  tree token = NULL_TREE, vptr_offset = NULL_TREE;
  TEST (extract_otr_callee (stmt, expr, token, vptr, vptr_offset))

  tree f_vptr;
  TEST (extract_field_of_ssa_load (vptr, arg0, f_vptr))
  TEST (vptr_field_p (f_vptr, TREE_TYPE (TREE_TYPE (arg0))))

  tree callee = gimple_call_fn (stmt);
  otr_alloc_func &mem_func = (alloc_kind == ALLOC_P) ? mem_alloc : mem_dealloc;
  if (mem_func.func_type)
    return operand_equal_p (vptr_offset, mem_func.vptr_offset)
	   && operand_equal_p (token, mem_func.token)
	   && operand_equal_p (f_vptr, mem_func.f_vptr)
	   && types_matched_p (TREE_TYPE (callee), mem_func.func_type);

  mem_func.vptr_offset = vptr_offset;
  mem_func.token = token;
  mem_func.f_vptr = f_vptr;
  mem_func.func_type = TREE_TYPE (callee);
  return true;
}

void
target_type_info::dump_targ_type ()
{
  print_generic_expr (dump_file, root_struct, TDF_SLIM);
  fprintf (dump_file, " {\n");

  for (unsigned vid = 0; vid < nvec; vid++)
    {
      dyn_vec_info *dyn_vec = get_vec (vid);

      fprintf (dump_file, "\n  ==== Vector %d (offset %ld): ", vid,
	       vec_offsets[vid]);
      print_generic_expr (dump_file, vec_decls[vid], TDF_SLIM);
      fprintf (dump_file, " ====\n  ");
      print_generic_expr (dump_file, dyn_vec->vec_type, TDF_SLIM);
      fprintf (dump_file, " {");

      for (int vf_kind = VEC_FLD_START; vf_kind < VEC_FLD_LEN; vf_kind++)
	{
	  fprintf (dump_file, "\n    %s: ", vec_field_names[vf_kind]);
	  tree fld = dyn_vec->get_field (static_cast<VEC_FIELD_KIND> (vf_kind));
	  print_generic_expr (dump_file, TREE_TYPE (fld), TDF_SLIM);
	  fprintf (dump_file, " ");
	  print_generic_expr (dump_file, fld, TDF_SLIM);

	  if (vf_kind + 1 != VEC_FLD_LEN)
	    fprintf (dump_file, ", ");
	}
      fprintf (dump_file, "\n  }\n");

      if (dyn_vec->replic_elt_p)
	fprintf (dump_file, "  replic_elt_p: true\n");
    }

  fprintf (dump_file, "\n}\n\n");
}

bool
target_type_info::init_dyn_vecs (
  auto_vec<std::pair<tree, HOST_WIDE_INT> > &cand_fields)
{
  cand_fields.qsort (field_offset_cmp);

  for (unsigned vid = 0; vid < num_vecs; vid++)
    {
      tree cur_field = cand_fields[vid].first;
      HOST_WIDE_INT cur_offset = cand_fields[vid].second;
      gcc_checking_assert (cur_offset % POINTER_SIZE == 0);

      CHECK (fld_to_vec.get (cur_field) == NULL)

      CHECK (vid == 0
	     || cur_offset == (cand_fields[vid - 1].second + POINTER_SIZE))

      dyn_vec_info *dyn_vec = new dyn_vec_info (vid);
      fld_to_vec.put (cur_field, dyn_vec);
      dyn_vecs.safe_push (dyn_vec);

      CHECK (root_struct == DECL_CONTEXT (cur_field))

      vec_decls[vid] = cur_field;
      vec_offsets[vid] = cur_offset;
    }

  return true;
}

bool
target_type_info::set_mempool (tree fld)
{
  CHECK (f_mem_pool == NULL && get_field_bit_offset (fld, mp_offset))
  f_mem_pool = fld;
  return true;
}

target_use_info *
target_type_info::create_targ_use (tree root_ref)
{
  target_use_info *targ_use = new target_use_info (root_ref);
  this->targ_uses.safe_push (targ_use);

  return targ_use;
}

static inline unsigned
index_of_field (tree field)
{
  tree type = DECL_CONTEXT (field);
  tree field1 = TYPE_FIELDS (type);
  unsigned index = 0;

  for (; field1; field1 = DECL_CHAIN (field1), index++)
    {
      if (field1 == field)
	break;
    }

  gcc_assert (field1);
  return index;
}

static bool
same_field_p (tree field1, tree field2)
{
  gcc_checking_assert (TREE_CODE (field1) == FIELD_DECL);
  gcc_checking_assert (TREE_CODE (field2) == FIELD_DECL);

  if (field1 == field2)
    return true;

  tree type1 = DECL_CONTEXT (field1);
  tree type2 = DECL_CONTEXT (field2);

  if (type1 == type2)
    return false;

  if (types_matched_p (type1, type2)
      && index_of_field (field1) == index_of_field (field2))
    return true;

  return false;
}

bool
dyn_vec_info::field_p (tree field, VEC_FIELD_KIND vf_kind)
{
  if (vf_kind < VEC_FLD_LEN)
    return same_field_p (field_decls[vf_kind], field);
  return false;
}

bool
dyn_vec_info::find_field (tree field, VEC_FIELD_KIND &vf_kind)
{
  for (int i = VEC_FLD_START; i < VEC_FLD_LEN; i++)
    if (same_field_p (field_decls[i], field))
      {
	vf_kind = (VEC_FIELD_KIND) i;
	return true;
      }

  return false;
}

bool
dyn_vec_info::extract_comp_ref_field (tree ref, tree vec_base,
				      VEC_FIELD_KIND &vf_kind)
{
  tree base_ref = NULL_TREE, field = NULL_TREE;
  TEST (extract_comp_ref (ref, base_ref, field))
  TEST (ref_of_addr_p (base_ref, vec_base))

  return find_field (field, vf_kind);
}

bool
dyn_vec_info::set_vec_type (tree type, bool child_p)
{
  CHECK (type != NULL_TREE && TREE_ADDRESSABLE (type))

  tree *to_set = child_p ? &child_type : &vec_type;
  if (*to_set)
    return types_matched_p (*to_set, type);
  *to_set = type;

  if (!child_p)
    CHECK (extract_hwi (TYPE_SIZE_UNIT (type), type_size_hwi))
  return true;
}

bool
dyn_vec_info::set_field (VEC_FIELD_KIND vf_kind, tree fld)
{
  CHECK (field_decls[vf_kind] == NULL)

  if (vf_kind == F_ELT_LIST)
    {
      elt_size = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (fld)));
      CHECK (extract_hwi (elt_size, elt_size_hwi))
    }

  field_decls[vf_kind] = fld;
  return true;
}

bool
dyn_vec_info::extract_ref_field (tree ref, tree ptr, tree offset,
				 VEC_FIELD_KIND &vf_kind)
{
  tree base_ref = NULL_TREE, field = NULL_TREE;
  TEST (extract_comp_ref (ref, base_ref, field))
  TEST (mem_ref_of_addr_p (base_ref, ptr, offset))

  return find_field (field, vf_kind);
}

void
target_use_info::transform_targ_use ()
{
  unsigned i;
  read_vu_group *rg;
  write_vu_group *wg;
  gimple *stmt;
  bitmap_iterator bi;

  FOR_EACH_VEC_ELT (read_groups, i, rg)
    rg->transform_use_group ();

  FOR_EACH_VEC_ELT (write_groups, i, wg)
    wg->transform_use_group ();

  FOR_EACH_VEC_ELT (extra_del_stmts, i, stmt)
    remove_stmt (stmt, this);

  EXECUTE_IF_SET_IN_BITMAP (release_ssa_bm, 0, i, bi)
    {
      if (tree var = ssa_name (i))
	{
	  gcc_checking_assert (num_imm_uses (var) == 0);
	  release_ssa_name (var);
	}
    }
}

bool
target_use_info::load_from_mem_pool_p (tree var)
{
  return mem_pool_ssa_p (var) || vec_field_ssa_p (var, F_MEM_POOL);
}

void
target_use_info::dump_target_use ()
{
  fprintf (dump_file, "> Target Use Info\n");

  unsigned i;
  read_vu_group *rg;
  write_vu_group *wg;

  FOR_EACH_VEC_ELT (read_groups, i, rg)
    rg->dump_vec_uses ();

  FOR_EACH_VEC_ELT (write_groups, i, wg)
    wg->dump_vec_uses ();

  if (num_null_writes)
    {
      fprintf (dump_file, ">> Vector Init Nulls:\n");
      dump_gimples (write_nulls);
    }
  if (!extra_del_stmts.is_empty ())
    {
      fprintf (dump_file, ">> Extra Stmts To Delete:\n");
      dump_gimples (extra_del_stmts);
    }
  fprintf (dump_file, "\n");
}

vec_use_info *
target_use_info::get_vec_use (gimple *stmt)
{
  if (stmt)
    {
      vec_use_info **slot = vec_use_map.get (stmt);
      return slot ? *slot : NULL;
    }
  return NULL;
}

bool
target_use_info::contains (gimple *stmt)
{
  vec_use_info *vu = get_vec_use (stmt);
  return vu ? true : extra_del_stmts_set.contains (stmt);
}

bool
target_use_info::other_use_p (gimple *stmt, unsigned vid)
{
  TEST (stmt != NULL)
  vec_use_info *vec_use = get_vec_use (stmt);
  TEST (vec_use && vec_use->vu_kind == VU_OTHER)
  TEST (vid == UINT_MAX || vec_use->vid == vid)

  vec_use->vt_status = VT_TODO;
  return true;
}

bool
target_use_info::other_use_p (tree var, unsigned vid)
{
  TEST (other_use_p (get_ssa_def_stmt (var), vid))
  return true;
}

bool
target_use_info::extract_use (gimple *stmt, unsigned vid,
			      field_vec_use *&vec_use)
{
  vec_use_info *vu = get_vec_use (stmt);
  TEST (vu != NULL && vu->vu_kind == VU_VEC_FIELD && vu->vid == vid)

  vu->vt_status = VT_TODO;
  vec_use = as_a<field_vec_use *> (vu);
  return true;
}

bool
target_use_info::extract_use (gimple *stmt, field_vec_use *&vec_use)
{
  vec_use_info *vu = get_vec_use (stmt);
  TEST (vu != NULL && vu->vu_kind == VU_VEC_FIELD)

  vu->vt_status = VT_TODO;
  vec_use = as_a<field_vec_use *> (vu);
  return true;
}

bool
target_use_info::extract_use (gimple *stmt, other_vec_use *&o_use)
{
  vec_use_info *vu = get_vec_use (stmt);
  TEST (vu != NULL && vu->vu_kind == VU_OTHER)

  vu->vt_status = VT_TODO;
  o_use = as_a<other_vec_use *> (vu);
  return true;
}

bool
target_use_info::vec_field_p (gimple *stmt, VEC_FIELD_KIND vf_kind,
			      unsigned vid, ACCESS_KIND acc_kind)
{
  vec_use_info *vec_use = get_vec_use (stmt);
  TEST (vec_use != NULL && vec_use->vu_kind == VU_VEC_FIELD)
  TEST (vid == UINT_MAX || vid == vec_use->vid)

  field_vec_use *use_field = as_a<field_vec_use *> (vec_use);
  use_field->vt_status = VT_TODO;
  return acc_kind == use_field->acc_kind && use_field->vf_kind == vf_kind;
}

bool
target_use_info::mem_pool_ssa_p (tree lhs)
{
  tree ref = NULL_TREE;
  TEST (extract_ssa_load_ref (lhs, ref))

  HOST_WIDE_INT offset;
  tree base_ref = NULL_TREE;
  TEST (get_ref_base_and_offset_hwi (ref, base_ref, offset))

  return operand_equal_p (root_ref, base_ref, OEP_ADDRESS_OF)
	 && offset == targ_type->mp_offset;
}

bool
target_use_info::vec_field_ssa_p (tree lhs, VEC_FIELD_KIND vf_kind,
				  unsigned vid)
{
  return vec_field_p (get_ssa_def_stmt (lhs), vf_kind, vid, LOAD_P);
}
bool
target_use_info::extract_vec_idx (tree vf_ssa, VEC_FIELD_KIND vf_kind,
				  unsigned &vid)
{
  vec_use_info *vec_use = get_vec_use (get_ssa_def_stmt (vf_ssa));
  TEST (vec_use != NULL && vec_use->vu_kind == VU_VEC_FIELD
	&& as_a<field_vec_use *> (vec_use)->vf_kind == vf_kind)
  vid = vec_use->vid;
  vec_use->vt_status = VT_TODO;
  return true;
}
bool
target_use_info::extract_vec_field_idx (gimple *stmt, VEC_FIELD_KIND &vf_kind,
					unsigned &vid)
{
  vec_use_info *vec_use = get_vec_use (stmt);
  TEST (vec_use != NULL && vec_use->vu_kind == VU_VEC_FIELD)

  vf_kind = as_a<field_vec_use *> (vec_use)->vf_kind;
  vid = vec_use->vid;
  vec_use->vt_status = VT_TODO;
  return true;
}
bool
target_use_info::vec_idx_elt_ssa_p (tree lhs, unsigned vid, tree elt_idx)
{
  idx_elt_vec_use *ie_use;
  TEST (ssa_var_p (lhs) && extract_use (get_ssa_def_stmt (lhs), vid, ie_use))
  TEST (vec_field_ssa_p (ie_use->elt_ptr, F_ELT_LIST, vid))

  ie_use->vt_status = VT_TODO;
  return ie_use->elt_idx == elt_idx;
}
bool
target_use_info::extract_use (gimple *stmt, unsigned vid,
			      idx_elt_vec_use *&ie_use)
{
  vec_use_info *vec_use = get_vec_use (stmt);
  TEST (vec_use != NULL && vec_use->vu_kind == VU_INDEXED_ELT
	&& vec_use->vid == vid)

  ie_use = as_a<idx_elt_vec_use *> (vec_use);
  vec_field_ssa_p (ie_use->elt_ptr, F_ELT_LIST, vid);
  ie_use->vt_status = VT_TODO;
  return true;
}

bool
target_use_info::extract_init_check (basic_block bb, edge &e_true,
				     edge &e_false, unsigned *vid)
{
  vec_use_info *vec_use = get_vec_use (last_stmt (bb));
  TEST (vec_use != NULL && vec_use->vu_kind == VU_VEC_INIT_CHECK)

  init_check_vec_use *init_check = as_a<init_check_vec_use *> (vec_use);

  e_true = init_check->e_true;
  e_false = init_check->e_false;
  if (vid)
    *vid = init_check->vid;
  init_check->vt_status = VT_TODO;
  return true;
}

bool
target_use_info::all_uses_checked_p ()
{
  unsigned i;
  read_vu_group *rg;
  write_vu_group *wg;

  FOR_EACH_VEC_ELT (read_groups, i, rg)
    CHECK (rg->all_uses_checked_p ())

  FOR_EACH_VEC_ELT (write_groups, i, wg)
    CHECK (wg->all_uses_checked_p ())

  return true;
}

void
target_use_info::init_vec_use_group (ACCESS_KIND acc_kind)
{
  if (acc_kind == LOAD_P)
    {
      gcc_checking_assert (read_groups.is_empty ());
      for (unsigned vid = 0; vid < num_vecs; vid++)
	{
	  read_vu_group *vu_group = new read_vu_group (vid, this);
	  read_groups.safe_push (vu_group);
	}
    }
  else
    {
      gcc_checking_assert (write_groups.is_empty ());
      for (unsigned vid = 0; vid < num_vecs; vid++)
	{
	  write_vu_group *vu_group = new write_vu_group (vid, this);
	  write_groups.safe_push (vu_group);
	}
    }
}

bool
target_use_info::add_root_stmt (gimple *stmt, unsigned vid,
				ACCESS_KIND acc_kind)
{
  tree vec_var
    = acc_kind == LOAD_P ? gimple_assign_lhs (stmt) : gimple_assign_rhs1 (stmt);
  read_only_p &= (acc_kind == LOAD_P);
  if (acc_kind == STORE_P && integer_zerop (vec_var))
    {
      num_null_writes++;
      write_nulls.safe_push (stmt);
      bitmap_set_bit (zero_write_bm, vid);
      return true;
    }

  TEST (ssa_var_p (vec_var))

  if (acc_kind == LOAD_P)
    {
      if (!num_reads)
	init_vec_use_group (acc_kind);

      TEST (read_groups[vid]->add_root_stmt (stmt))

      num_reads++;
      bitmap_set_bit (read_bm, vid);
      return true;
    }

  if (!num_writes)
    init_vec_use_group (acc_kind);

  TEST (write_groups[vid]->add_root_stmt (stmt))

  num_writes++;
  bitmap_set_bit (write_bm, vid);
  return true;
}

void
target_use_info::map_vec_use (gimple *vec_stmt, vec_use_info *vec_use)
{
  vec_use_map.put (vec_stmt, vec_use);
}

void
target_use_info::mark_release_ssa (gimple *stmt)
{
  tree def;
  ssa_op_iter iter;

  FOR_EACH_SSA_TREE_OPERAND (def, stmt, iter, SSA_OP_ALL_DEFS)
    if (TREE_CODE (def) == SSA_NAME)
      bitmap_set_bit (release_ssa_bm, SSA_NAME_VERSION (def));
}

bool
target_use_info::collect_vec_uses ()
{
  if (num_reads)
    {
      for (unsigned vid = 0; vid < num_vecs; vid++)
	{
	  TEST (read_groups[vid]->collect_vec_uses ())
	}
    }

  if (num_writes)
    {
      for (unsigned vid = 0; vid < num_vecs; vid++)
	{
	  TEST (write_groups[vid]->collect_vec_uses ())
	}
    }

  return true;
}

bool
target_use_info::add_extra_del (gimple *stmt)
{
  if (vec_use_info *vu = get_vec_use (stmt))
    {
      TEST (vu->vt_status == VT_TODO);
    }
  else if (!extra_del_stmts_set.add (stmt))
    extra_del_stmts.safe_push (stmt);
  return true;
}
bool
target_use_info::add_extra_del (tree var)
{
  return add_extra_del (get_ssa_def_stmt (var));
}

bool
vec_use_group::add_root_stmt (gimple *root_stmt)
{
  tree vec_base = root_acc_kind == LOAD_P ? gimple_assign_lhs (root_stmt)
					  : gimple_assign_rhs1 (root_stmt);
  TEST (ssa_var_p (vec_base))

  root_stmts.safe_push (root_stmt);
  targ_use->add_extra_del (root_stmt);
  vec_bases.safe_push (vec_base);
  return true;
}

bool
vec_use_group::all_uses_checked_p ()
{
  vec_use_info *vu;
  unsigned i;
  auto_vec<tree> to_del_defs;

  FOR_EACH_VEC_ELT (vec_uses, i, vu)
    {
      CHECK (vu->vt_status != VT_INIT)
      if (vu->vu_kind == VU_OTHER)
	{
	  tree lhs = gimple_get_lhs (vu->vec_stmt);
	  if (lhs && ssa_var_p (lhs))
	    to_del_defs.safe_push (lhs);
	}
    }

  tree def;
  FOR_EACH_VEC_ELT (to_del_defs, i, def)
    {
      gimple *use_stmt;
      imm_use_iterator imm_iter;

      FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, def)
	{
	  if (is_gimple_debug (use_stmt))
	    continue;
	  CHECK (targ_use->contains (use_stmt))

	  tree lhs = gimple_get_lhs (use_stmt);
	  if (lhs && ssa_var_p (lhs))
	    to_del_defs.safe_push (lhs);
	}
    }
  return true;
}

void
vec_use_group::remove_store_vec_uses ()
{
  vec_use_info *vec_use;
  unsigned i;

  FOR_EACH_VEC_ELT (vec_uses, i, vec_use)
    {
      switch (vec_use->vu_kind)
	{
	case VU_VEC_FIELD:
	  if (as_a<field_vec_use *> (vec_use)->acc_kind == STORE_P)
	    vec_use->remove_vec_use (targ_use);
	  break;
	case VU_INDEXED_ELT:
	  if (as_a<idx_elt_vec_use *> (vec_use)->acc_kind == STORE_P)
	    vec_use->remove_vec_use (targ_use);
	  break;
	default:
	  break;
	}
    }
}

void
vec_use_group::transform_use_group ()
{
  auto_vec<vec_use_info *> init_checks;
  vec_use_info *vec_use;
  unsigned i;

  FOR_EACH_VEC_ELT (vec_uses, i, vec_use)
    {
      switch (vec_use->vt_status)
	{
	case VT_INIT:
	case VT_TODO:
	  switch (vec_use->vu_kind)
	    {
	    case VU_OTHER:
	      vec_use->remove_vec_use (targ_use);
	      vec_use->vt_status = VT_DONE;
	      break;
	    case VU_VEC_INIT_CHECK:
	      init_checks.safe_push (vec_use);
	      break;
	    default:
	      vec_use->transform_vec_use (targ_use);
	      vec_use->vt_status = VT_DONE;
	      break;
	    }
	  break;
	case VT_DONE:
	  break;
	default:
	  gcc_unreachable ();
	}
    }

  FOR_EACH_VEC_ELT (init_checks, i, vec_use)
    vec_use->transform_vec_use (targ_use);
}

bool
vec_use_group::collect_uses_from_base (tree vec_base)
{
  dyn_vec_info *dyn_vec = targ_type->get_vec (vid);
  gimple *use_stmt;
  imm_use_iterator imm_iter;

  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, vec_base)
    {
      if (is_gimple_debug (use_stmt))
	continue;
      if (root_acc_kind == STORE_P && root_stmts.contains (use_stmt))
	continue;

      switch (gimple_code (use_stmt))
	{
	case GIMPLE_COND:
	  {
	    tree vec_bas, zero;
	    edge e_true, e_false;
	    TEST (extract_stmt_cond (use_stmt, EQ_EXPR, vec_bas, zero, e_true,
				     e_false))
	    TEST (vec_bas == vec_base && integer_zerop (zero))

	    add_init_check_use (use_stmt, e_false, e_true);
	    break;
	  }

	default:
	  {
	    ACCESS_KIND acc_kind;
	    tree ref;
	    VEC_FIELD_KIND vf_kind;

	    if (!extract_load_store_ref (use_stmt, ref, acc_kind))
	      {
		add_other_use (use_stmt);
		break;
	      }

	    if (!dyn_vec->extract_comp_ref_field (ref, vec_base, vf_kind))
	      {
		add_other_use (use_stmt);
		break;
	      }

	    add_field_use (use_stmt, vf_kind, acc_kind);

	    if (vf_kind == F_ELT_LIST && acc_kind == LOAD_P)
	      find_idx_elt_use (use_stmt);
	    break;
	  }
	}
    }

  return true;
}

void
vec_use_group::add_field_use (gimple *stmt, VEC_FIELD_KIND vf_kind,
			      ACCESS_KIND acc_kind)
{
  vec_use_info *vec_use = new field_vec_use (stmt, vid, vf_kind, acc_kind);
  vec_uses.safe_push (vec_use);
  targ_use->read_only_p &= (acc_kind == LOAD_P);
  targ_use->map_vec_use (stmt, vec_use);
}

void
vec_use_group::add_other_use (gimple *stmt)
{
  vec_use_info *vec_use = new other_vec_use (stmt, vid);
  vec_uses.safe_push (vec_use);
  targ_use->read_only_p = false;
  targ_use->map_vec_use (stmt, vec_use);
}

void
vec_use_group::add_init_check_use (gimple *stmt, edge e_true, edge e_false)
{
  vec_use_info *vec_use = new init_check_vec_use (stmt, vid, e_true, e_false);
  vec_uses.safe_push (vec_use);
  targ_use->map_vec_use (stmt, vec_use);
}

void
vec_use_group::add_idx_elt_use (idx_elt_vec_use *vec_use)
{
  vec_uses.safe_push (vec_use);
  targ_use->read_only_p &= (vec_use->acc_kind == LOAD_P);
  targ_use->map_vec_use (vec_use->vec_stmt, vec_use);
}

static bool
extract_idx_elt (gimple *elt_ptr_def, tree &idx, gimple *&offset_stmt,
		 gimple *&ptr_plus_stmt, gimple *&elt_stmt,
		 ACCESS_KIND &acc_kind)
{
  tree ptr_var = gimple_assign_lhs (elt_ptr_def);

  use_operand_p use_p;
  TEST (single_imm_use (ptr_var, &use_p, &ptr_plus_stmt))

  tree elt_addr, ptr, offset;
  TEST (extract_ptr_plus (ptr_plus_stmt, elt_addr, ptr, offset)
	&& ptr == ptr_var)

  offset_stmt = SSA_NAME_DEF_STMT (offset);
  tree type_size = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (ptr_var)));
  TEST (unscale_offset (offset, type_size, idx))

  TEST (single_imm_use (elt_addr, &use_p, &elt_stmt))

  tree ref;
  return extract_load_store_ref (elt_stmt, ref, acc_kind)
	 && ref_of_addr_p (ref, elt_addr);
}

bool
vec_use_group::find_idx_elt_use (gimple *elt_ptr_def)
{
  gcc_checking_assert (gimple_assign_load_p (elt_ptr_def));

  gimple *ptr_plus_stmt, *offset_stmt, *elt_stmt;
  ACCESS_KIND acc_kind;
  tree idx;

  TEST (extract_idx_elt (elt_ptr_def, idx, offset_stmt, ptr_plus_stmt, elt_stmt,
			 acc_kind))

  idx_elt_vec_use *ie_use = new idx_elt_vec_use (elt_stmt, vid, acc_kind);
  ie_use->offset_stmt = offset_stmt;
  ie_use->ptr_plus_stmt = ptr_plus_stmt;
  ie_use->elt_idx = idx;
  ie_use->elt_ptr = gimple_get_lhs (elt_ptr_def);

  add_idx_elt_use (ie_use);
  return true;
}

void
vec_use_group::dump_vec_uses ()
{
  if (root_stmts.is_empty ())
    return;

  fprintf (dump_file, ">> Vector Uses (%s):\n",
	   root_acc_kind == LOAD_P ? "read" : "write");

  vec_use_info *vec_use;
  gimple *stmt;
  unsigned i;

  FOR_EACH_VEC_ELT (root_stmts, i, stmt)
    print_gimple_stmt (dump_file, stmt, 0, TDF_NONE);

  FOR_EACH_VEC_ELT (vec_uses, i, vec_use)
    vec_use->dump_vec_use ();
}

bool
read_vu_group::collect_vec_uses ()
{
  tree base;
  unsigned i;

  FOR_EACH_VEC_ELT (vec_bases, i, base)
    {
      TEST (collect_uses_from_base (base))
    }

  return true;
}

bool
write_vu_group::collect_vec_uses ()
{
  tree base;
  unsigned i;

  FOR_EACH_VEC_ELT (vec_bases, i, base)
    {
      gimple *base_def = SSA_NAME_DEF_STMT (base);
      targ_use->add_extra_del (base_def);
      if (gimple_code (base_def) == GIMPLE_CALL)
	{
	  TEST (targ_type->check_otr_mem_func (base_def, ALLOC_P))

	  vec_allocs.safe_push (base_def);
	}
      else
	{
	  tree ptr, offset;
	  TEST (extract_ptr_plus (base, ptr, offset) && ssa_var_p (ptr)
		&& TREE_CODE (offset) == INTEGER_CST)

	  gimple *ptr_def = SSA_NAME_DEF_STMT (ptr);
	  TEST (targ_type->check_otr_mem_func (ptr_def, ALLOC_P))

	  ptr_plus_stmts.safe_push (SSA_NAME_DEF_STMT (base));
	  ptrs.safe_push (ptr);
	  offsets.safe_push (offset);
	  vec_allocs.safe_push (ptr_def);

	  TEST (collect_uses_from_ptr_plus (base, ptr, offset))
	}

      TEST (collect_uses_from_base (base))
    }

  return true;
}

#define CHECK_OR_UPDATE_TRANS_STATUS(status) \
  if (status == VT_DONE) \
    return; \
  status = VT_DONE;

void
vec_use_info::remove_vec_use (target_use_info *targ_use)
{
  CHECK_OR_UPDATE_TRANS_STATUS (vt_status)
  remove_stmt (vec_stmt, targ_use);
}

void
other_vec_use::dump_vec_use ()
{
  fprintf (dump_file, "OTHER (%d): ", vt_status);
  print_gimple_stmt (dump_file, vec_stmt, 0, TDF_NONE);
}

void
field_vec_use::transform_vec_use (target_use_info *targ_use)
{
  CHECK_OR_UPDATE_TRANS_STATUS (vt_status)

  if (dump_file && (dump_flags & TDF_DETAILS))
    print_gimple_stmt (dump_file, vec_stmt, 0, TDF_NONE);

  tree new_val;
  if (vf_kind == F_DEL_ELT_P)
    {
      if (acc_kind == STORE_P)
	{
	  remove_stmt (vec_stmt, targ_use);
	  return;
	}
      bool del_elt_p = targ_type->get_vec (vid)->replic_elt_p;
      new_val = del_elt_p ? boolean_true_node : boolean_false_node;
    }
  else
    new_val = merge_type->build_field_ref (targ_use->root_ref, vf_kind);

  if (acc_kind == LOAD_P)
    {
      gimple_assign_set_rhs1 (vec_stmt, new_val);
      if (vf_kind == F_ELT_LIST)
	{
	  tree lhs = gimple_assign_lhs (vec_stmt);
	  TREE_TYPE (lhs) = merge_type->get_elt_list_type ();
	}
    }
  else
    gimple_assign_set_lhs (vec_stmt, new_val);

  update_stmt (vec_stmt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "=>\n");
      print_gimple_stmt (dump_file, vec_stmt, 0, TDF_NONE);
      fprintf (dump_file, "\n");
    }
}

void
init_check_vec_use::transform_vec_use (target_use_info *targ_use)
{
  CHECK_OR_UPDATE_TRANS_STATUS (vt_status)

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      print_gimple_stmt (dump_file,
			 SSA_NAME_DEF_STMT (gimple_cond_lhs (vec_stmt)), 0,
			 TDF_NONE);
      print_gimple_stmt (dump_file, vec_stmt, 0, TDF_NONE);
    }

  ssa_op_iter i;
  use_operand_p use_p;

  tree field_decl = merge_type->get_field (F_ELT_LIST);
  tree lhs = make_ssa_name (TREE_TYPE (field_decl));
  tree fld_ref = merge_type->build_field_ref (targ_use->root_ref, F_ELT_LIST);
  build_assign_before_stmt (lhs, fld_ref, vec_stmt);

  FOR_EACH_SSA_USE_OPERAND (use_p, vec_stmt, i, SSA_OP_USE)
    SET_USE (use_p, lhs);

  update_stmt (vec_stmt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "=>\n");
      print_gimple_stmt (dump_file, SSA_NAME_DEF_STMT (lhs), 0, TDF_NONE);
      print_gimple_stmt (dump_file, vec_stmt, 0, TDF_NONE);
      fprintf (dump_file, "\n");
    }
}

void
idx_elt_vec_use::remove_vec_use (target_use_info *targ_use)
{
  CHECK_OR_UPDATE_TRANS_STATUS (vt_status)

  remove_stmt (ptr_plus_stmt, targ_use);
  remove_stmt (vec_stmt, targ_use);
}

void
idx_elt_vec_use::transform_vec_use (target_use_info *)
{
  CHECK_OR_UPDATE_TRANS_STATUS (vt_status)

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      print_gimple_stmt (dump_file, offset_stmt, 0, TDF_NONE);
      print_gimple_stmt (dump_file, ptr_plus_stmt, 0, TDF_NONE);
      print_gimple_stmt (dump_file, vec_stmt, 0, TDF_NONE);
    }

  tree field_decl = merge_type->get_field (F_ELT_LIST);
  gimple_assign_set_rhs2 (offset_stmt, merge_type->elt_tuple_size);
  update_stmt (offset_stmt);

  tree ptr_plus = make_ssa_name (TREE_TYPE (field_decl));
  release_defs (ptr_plus_stmt);
  gimple_assign_set_lhs (ptr_plus_stmt, ptr_plus);
  update_stmt (ptr_plus_stmt);

  tree elt_ref = build_field_ref (ptr_plus, merge_type->get_elt_decl (vid));
  if (acc_kind == LOAD_P)
    gimple_assign_set_rhs1 (vec_stmt, elt_ref);
  else
    gimple_assign_set_lhs (vec_stmt, elt_ref);
  update_stmt (vec_stmt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "=>\n");
      print_gimple_stmt (dump_file, offset_stmt, 0, TDF_NONE);
      print_gimple_stmt (dump_file, ptr_plus_stmt, 0, TDF_NONE);
      print_gimple_stmt (dump_file, vec_stmt, 0, TDF_NONE);
      fprintf (dump_file, "\n");
    }
}

static bool
extract_targ_ref_and_offset (tree ldst_ref, tree &targ_ref,
			     HOST_WIDE_INT &offset)
{
  switch (TREE_CODE (ldst_ref))
    {
    case MEM_REF:
      if (!strict_type_analysis)
	{
	  tree opnd0 = TREE_OPERAND (ldst_ref, 0);
	  TEST (targ_type->targ_type_ptr_p (opnd0))
	  TEST (extract_hwi (TREE_OPERAND (ldst_ref, 1), offset))
	  targ_ref = build_simple_mem_ref (opnd0);
	  return true;
	}
      return false;

    case COMPONENT_REF:
      {
	targ_ref = TREE_OPERAND (ldst_ref, 0);
	if (TREE_CODE (targ_ref) == COMPONENT_REF)
	  {
	    tree base_ref;
	    HOST_WIDE_INT tmp_offset;

	    TEST (targ_type->targ_type_ref_p (targ_ref))
	    TEST (get_field_bit_offset (TREE_OPERAND (ldst_ref, 1), offset))
	    TEST (get_ref_base_and_offset_hwi (targ_ref, base_ref, tmp_offset)
		  && TREE_CODE (base_ref) == MEM_REF
		  && extract_hwi (TREE_OPERAND (base_ref, 1), tmp_offset))
	    return true;
	  }

	HOST_WIDE_INT size;
	bool reverse;
	targ_ref
	  = get_ref_base_and_extent_hwi (ldst_ref, &offset, &size, &reverse);

	TEST (targ_ref != NULL && targ_type->targ_type_ref_p (targ_ref))
	return true;
      }
    default:
      return false;
    }
}

static bool
collect_vec_defs (auto_vec<target_use_info *> &targ_uses)
{
  hash_table<base_info_hasher> m_seen_vecs (8);
  hash_set<gimple *> vec_defs;
  basic_block bb;

  FOR_EACH_BB_FN (bb, cfun)
    {
      gimple_stmt_iterator gsi;
      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	{
	  gimple *stmt = gsi_stmt (gsi);
	  if (gimple_clobber_p (stmt) || is_gimple_debug (stmt))
	    continue;

	  ACCESS_KIND acc_kind;
	  tree ldst_ref = NULL_TREE;
	  if (!extract_load_store_ref (stmt, ldst_ref, acc_kind))
	    continue;

	  HOST_WIDE_INT offset;
	  tree root_ref = NULL_TREE;
	  if (!extract_targ_ref_and_offset (ldst_ref, root_ref, offset))
	    continue;

	  target_use_info bas_info (root_ref);
	  target_use_info **slot = m_seen_vecs.find_slot (&bas_info, INSERT);
	  target_use_info *targ_use = *slot;

	  if (!targ_use)
	    {
	      targ_use = targ_type->create_targ_use (root_ref);
	      *slot = targ_use;
	      targ_uses.safe_push (targ_use);
	    }

	  unsigned vid = UINT_MAX;
	  if (!targ_type->get_vec_index (offset, vid))
	    continue;

	  tree fld_vec = targ_type->vec_decls[vid];
	  TEST (types_matched_p (TREE_TYPE (fld_vec), TREE_TYPE (ldst_ref)))
	  TEST (targ_use->add_root_stmt (stmt, vid, acc_kind))
	  vec_defs.add (stmt);
	}
    }

  if (targ_type->vec_offsets[0] != 0)
    return true;

  target_use_info *targ_use;
  unsigned i;

  FOR_EACH_VEC_ELT (targ_uses, i, targ_use)
    {
      tree root_ref = targ_use->root_ref;
      tree opnd0 = TREE_OPERAND (root_ref, 0);
      if (!ssa_var_p (opnd0))
	continue;

      gimple *use_stmt;
      imm_use_iterator imm_iter;

      FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, opnd0)
	{
	  if (vec_defs.contains (use_stmt) || gimple_clobber_p (use_stmt)
	      || is_gimple_debug (use_stmt))
	    continue;

	  ACCESS_KIND acc_kind;
	  tree ldst_ref;
	  if (!extract_load_store_ref (use_stmt, ldst_ref, acc_kind))
	    continue;

	  tree base, offset;
	  if (extract_mem_ref (ldst_ref, base, offset) && base == opnd0
	      && tree_int_cst_equal (TREE_OPERAND (root_ref, 1), offset))
	    targ_use->add_root_stmt (use_stmt, 0, acc_kind);
	}
    }

  FOR_EACH_VEC_ELT (targ_uses, i, targ_use)
    {
      if (targ_use->no_vec_use ())
	targ_uses.unordered_remove (i--);
    }

  return true;
}

bool
write_vu_group::collect_uses_from_ptr_plus (tree vec_base, tree ptr,
					    tree offset)
{
  dyn_vec_info *dyn_vec = targ_type->get_vec (vid);
  gimple *use_stmt;
  imm_use_iterator iter;
  tree ldst_ref;
  ACCESS_KIND acc_kind;
  VEC_FIELD_KIND vf_kind;

  FOR_EACH_IMM_USE_STMT (use_stmt, iter, ptr)
    {
      if (is_gimple_debug (use_stmt))
	continue;

      if (extract_load_store_ref (use_stmt, ldst_ref, acc_kind))
	{
	  if (!dyn_vec->extract_ref_field (ldst_ref, ptr, offset, vf_kind))
	    {
	      add_other_use (use_stmt);
	      continue;
	    }

	  add_field_use (use_stmt, vf_kind, acc_kind);

	  if (vf_kind == F_ELT_LIST && acc_kind == LOAD_P)
	    find_idx_elt_use (use_stmt);
	}
      else
	{
	  TEST (use_stmt == get_ssa_def_stmt (vec_base))
	}
    }

  return true;
}

bool
vec_use_group::find_idx_elt_reverse (gimple *elt_stmt, idx_elt_vec_use *&ie_use)
{
  tree mem_ref;
  ACCESS_KIND acc_kind;
  TEST (extract_load_store_ref (elt_stmt, mem_ref, acc_kind))

  tree elt_addr, opnd1;
  TEST (extract_mem_ref (mem_ref, elt_addr, opnd1) && integer_zerop (opnd1))

  gimple *ptr_plus_stmt = SSA_NAME_DEF_STMT (elt_addr);

  tree ptr_var, offset, idx;
  TEST (extract_ptr_plus (ptr_plus_stmt, elt_addr, ptr_var, offset))
  TEST (unscale_offset (offset, targ_type->get_vec (vid)->elt_size, idx))

  ie_use = new idx_elt_vec_use (elt_stmt, vid, acc_kind);
  ie_use->offset_stmt = SSA_NAME_DEF_STMT (offset);
  ie_use->ptr_plus_stmt = ptr_plus_stmt;
  ie_use->elt_idx = idx;
  ie_use->elt_ptr = ptr_var;
  ie_use->vt_status = VT_TODO;

  add_idx_elt_use (ie_use);
  return true;
}

bool
vec_use_group::find_idx_elt_use_from (gimple *ptr_plus_stmt,
				      idx_elt_vec_use *&ie_use)
{
  tree addr = gimple_get_lhs (ptr_plus_stmt);
  use_operand_p use_p;
  gimple *elt_stmt;

  TEST (ssa_var_p (addr) && single_imm_use (addr, &use_p, &elt_stmt))

  tree mem_ref;
  ACCESS_KIND acc_kind;
  TEST (extract_load_store_ref (elt_stmt, mem_ref, acc_kind)
	&& mem_ref_of_addr_p (mem_ref, addr))

  tree elt_addr, ptr_var, offset, idx;
  TEST (extract_ptr_plus (ptr_plus_stmt, elt_addr, ptr_var, offset)
	&& elt_addr == addr)

  TEST (unscale_offset (offset, targ_type->get_vec (vid)->elt_size, idx))

  ie_use = new idx_elt_vec_use (elt_stmt, vid, acc_kind);
  ie_use->offset_stmt = SSA_NAME_DEF_STMT (offset);
  ie_use->ptr_plus_stmt = ptr_plus_stmt;
  ie_use->elt_idx = idx;
  ie_use->elt_ptr = ptr_var;
  ie_use->vt_status = VT_TODO;

  add_idx_elt_use (ie_use);
  return true;
}

void
pattern_info::dump_patt ()
{
  dump_action_in_func ("> %s pattern", patt_names[pt_kind], fun);
  targ_use->dump_target_use ();
}

bool
insert_elts_pattern::find_insert_elts_patt (target_use_info *targ_use, auto_vec<tree> &src_elts)
{
  insert_elts_pattern *ins_patt = new insert_elts_pattern (targ_use, src_elts);
  if (!ins_patt->check_patt ())
    {
      delete ins_patt;
      return false;
    }

  targ_type->targ_patts.safe_push (ins_patt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    ins_patt->dump_patt ();

  return true;
}

bool
check_delete_vec (target_use_info *targ_use, basic_block eh_block,
		  unsigned &vid)
{
  gimple_stmt_iterator gsi;
  for (gsi = gsi_start_bb (eh_block); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      vec_use_info *vec_use = targ_use->get_vec_use (stmt);
      if (vec_use)
	{
	  if (vec_use->vu_kind == VU_OTHER)
	    {
	      vid = vec_use->vid;
	      return true;
	    }
	}
    }

  return true;
}

static bool
stmt_is_before_p (const gimple *stmt1, const gimple *stmt2)
{
  basic_block bb1 = gimple_bb (stmt1);
  basic_block bb2 = gimple_bb (stmt2);
  if (bb1 != bb2)
    return dominated_by_p (CDI_DOMINATORS, bb2, bb1);

  bool stmt1_is_phi = gimple_code (stmt1) == GIMPLE_PHI;
  basic_block bb = gimple_bb (stmt1);

  gcc_checking_assert (bb == gimple_bb (stmt2));

  if (stmt1_is_phi ^ (gimple_code (stmt2) == GIMPLE_PHI))
    return stmt1_is_phi;

  gimple_stmt_iterator gsi;

  if (stmt1_is_phi)
    gsi = gsi_start_phis (bb);
  else
    gsi = gsi_start_bb (bb);

  for (; !gsi_end_p (gsi); gsi_next (&gsi))
    {
      if (gsi_stmt (gsi) == stmt1)
	return true;

      if (gsi_stmt (gsi) == stmt2)
	return false;
    }

  gcc_unreachable ();
  return false;
}

static bool
decl_is_operator_delete_p (tree decl);

static bool
check_eh_delete_vec (target_use_info *targ_use, edge eh_edge, unsigned vid)
{
  gimple *stmt = NULL;
  CHECK (extract_single_call_in_bb (eh_edge->dest, stmt)
	 && targ_use->other_use_p (stmt, vid))

  tree decl = gimple_call_fndecl (stmt);
  CHECK (decl && decl_is_operator_delete_p (decl))
  return true;
}

bool
insert_elts_pattern::check_init_one_vec (unsigned vid,
				 hash_set<basic_block> &fallthru_bbs)
{
  dyn_vec_info *dyn_vec = targ_type->get_vec (vid);
  write_vu_group *write_group = targ_use->write_groups[vid];
  init_vec_piece &piece = init_piece.init_pieces[vid];
  piece.vid = vid;

  gimple *vec_alloc = piece.vec_alloc = write_group->vec_allocs[0];
  CHECK (fallthru_bbs.contains (gimple_bb (vec_alloc)))

  tree vec_base = write_group->vec_bases[0];
  tree ptr = write_group->ptrs[0];
  piece.num_maxcnt = NULL_TREE;

  vec_use_info *vec_use;
  unsigned i, check_flag = 0;
  gimple *elts_init_zero = NULL, *elts_init_store = NULL;
  auto_vec<vec_use_info *> others_to_check;

  FOR_EACH_VEC_ELT (write_group->vec_uses, i, vec_use)
    {
      if (vec_use->vu_kind == VU_OTHER)
	{
	  others_to_check.safe_push (vec_use);
	  continue;
	}

      CHECK (vec_use->vu_kind == VU_VEC_FIELD)

      gimple *vec_stmt = vec_use->vec_stmt;
      field_vec_use *field_vu = as_a<field_vec_use *> (vec_use);
      if (field_vu->acc_kind == LOAD_P)
	continue;

      CHECK (fallthru_bbs.contains (gimple_bb (vec_stmt)))

      tree rhs = gimple_assign_rhs1 (vec_stmt);
      field_vu->vt_status = VT_TODO;

      switch (field_vu->vf_kind)
	{
	case F_MAX_CNT:
	  CHECK (TREE_CODE (rhs) == INTEGER_CST)

	  if (!piece.num_maxcnt)
	    piece.num_maxcnt = rhs;
	  else
	    {
	      CHECK (tree_int_cst_equal (piece.num_maxcnt, rhs))
	    }

	  SET_BIT_JUST_ONCE (check_flag, F_MAX_CNT);
	  break;
	case F_CUR_CNT:
	  CHECK (integer_zerop (rhs))
	  SET_BIT_JUST_ONCE (check_flag, F_CUR_CNT);
	  break;
	case F_DEL_ELT_P:
	  if (dyn_vec->replic_elt_p)
	    {
	      CHECK (integer_onep (rhs))
	    }
	  else
	    {
	      CHECK (integer_zerop (rhs))
	    }
	  SET_BIT_JUST_ONCE (check_flag, F_DEL_ELT_P);
	  field_vu->vt_status = VT_TODO;
	  break;
	case F_ELT_LIST:
	  if (TREE_CODE (rhs) == INTEGER_CST)
	    {
	      CHECK (integer_zerop (rhs))
	      elts_init_zero = vec_stmt;
	    }
	  else
	    {
	      CHECK (ssa_var_p (rhs))
	      SET_BIT_JUST_ONCE (check_flag, F_ELT_LIST);
	      elts_init_store = vec_stmt;
	    }
	  break;
	case F_MEM_POOL:
	  CHECK (ssa_var_p (rhs) && targ_use->mem_pool_ssa_p (rhs))
	  SET_BIT_JUST_ONCE (check_flag, F_MEM_POOL);
	  field_vu->vt_status = VT_TODO;
	  break;
	default:
	  return false;
	}
    }
  CHECK (check_flag == B_0001_1111)
  CHECK (!elts_init_zero || stmt_is_before_p (elts_init_zero, elts_init_store))

  bool other_flag = false;
  tree base_type = NULL_TREE;
  tree derive_type = NULL_TREE;

  FOR_EACH_VEC_ELT (others_to_check, i, vec_use)
    {
      gimple *vec_stmt = vec_use->vec_stmt;
      vec_use->vt_status = VT_TODO;

      if (gimple_clobber_p (vec_stmt))
	continue;
      if (ptr && vec_stmt == SSA_NAME_DEF_STMT (vec_base))
	continue;

      tree store_ref = NULL_TREE;
      if (!extract_store_ref (vec_stmt, store_ref))
	{
	  vec_use->vt_status = VT_INIT;
	  continue;
	}

      if (mem_ref_of_addr_p (store_ref, ptr))
	{
	  tree rhs = gimple_assign_rhs1 (vec_stmt);
	  CHECK (targ_use->load_from_mem_pool_p (rhs))
	  SET_BOOL_JUST_ONCE (other_flag);
	}
      else
	{
	  tree base = NULL_TREE, fld = NULL_TREE;
	  CHECK (extract_comp_ref (store_ref, base, fld))

	  tree type = TREE_TYPE (base);
	  CHECK (vptr_field_p (fld, type))

	  tree vtable = gimple_assign_rhs1 (vec_stmt);
	  unsigned HOST_WIDE_INT offset;

	  CHECK (vtable_pointer_value_to_vtable (vtable, &vtable, &offset))
	  CHECK (TREE_CODE (vtable) == VAR_DECL && DECL_VIRTUAL_P (vtable))

	  tree binfo = TYPE_BINFO (DECL_CONTEXT (vtable));
	  bool base_type_p = true;

	  gcc_assert (binfo);

	  for (unsigned i = 0; i < BINFO_N_BASE_BINFOS (binfo); i++)
	    {
	      tree tmp_base_type = TREE_TYPE (BINFO_BASE_BINFO (binfo, i));
	      tree tmp_base_binfo = TYPE_BINFO (tmp_base_type);

	      if (tmp_base_binfo && polymorphic_type_binfo_p (tmp_base_binfo))
		{
		  base_type_p = false;
		  break;
		}
	    }

	  if (base_type_p)
	    {
	      CHECK (!base_type)
	      base_type = DECL_CONTEXT (vtable);
	    }
	  else
	    {
	      CHECK (!derive_type)
	      derive_type = DECL_CONTEXT (vtable);

	      while (handled_component_p (base))
		{
		  CHECK (TREE_CODE (base) == COMPONENT_REF)
		  base = TREE_OPERAND (base, 0);
		}

	      CHECK (TREE_CODE (base) == MEM_REF)

	      tree addr = TREE_OPERAND (base, 0);
	      tree data_type = TREE_TYPE (base);

	      CHECK (TREE_CODE (addr) == SSA_NAME)

	      if (strict_type_analysis)
		data_type = TREE_TYPE (TREE_TYPE (addr));

	      CHECK (types_matched_p (data_type, derive_type))
	      CHECK (dyn_vec->set_vec_type (derive_type, true))
	    }

	  dyn_vec->derive_fld_p = true;
	}
    }

  CHECK (other_flag)

  if (dyn_vec->derive_fld_p)
    {
      CHECK (base_type && derive_type)

      tree binfo = TYPE_BINFO (derive_type);

      gcc_assert (binfo);

      CHECK (BINFO_N_BASE_BINFOS (binfo) == 1);
      tree type = TREE_TYPE (BINFO_BASE_BINFO (binfo, 0));

      CHECK (types_matched_p (type, base_type))
    }

  tree list_var = gimple_assign_rhs1 (elts_init_store);
  gimple *list_alloc = piece.list_alloc = SSA_NAME_DEF_STMT (list_var);
  CHECK (fallthru_bbs.contains (gimple_bb (list_alloc))
	 && targ_type->check_otr_mem_func (list_alloc, ALLOC_P))

  tree alloc_sz = gimple_call_arg (list_alloc, 1);
  tree exp_sz = fold_build2 (MULT_EXPR, size_type_node, dyn_vec->elt_size,
			     piece.num_maxcnt);
  CHECK (TREE_CODE (alloc_sz) == INTEGER_CST
	 && tree_int_cst_equal (alloc_sz, exp_sz))

  if (!single_succ_p (gimple_bb (list_alloc)))
    {
      edge eh_edge = NULL;
      CHECK (extract_succ_with_eh_edge (gimple_bb (list_alloc), eh_edge))
      CHECK (check_eh_delete_vec (targ_use, eh_edge, vid))
    }

  gimple *elt_list_use = NULL;
  CHECK (extract_one_of_two_uses (list_var, elts_init_store, elt_list_use))

  if (memset_call_p (elt_list_use))
    {
      tree ptr = NULL_TREE, size = NULL_TREE;
      CHECK (extract_memset_zero (elt_list_use, ptr, size) || ptr != list_var)

      if (TREE_CODE (size) == INTEGER_CST)
	{
	  CHECK (tree_int_cst_equal (size, exp_sz))
	}
      else
	{
	  tree unscaled = NULL_TREE;
	  CHECK (unscale_offset (size, dyn_vec->elt_size, unscaled)
		 && targ_use->vec_field_ssa_p (unscaled, F_MAX_CNT, vid))
	}

      piece.zero_piece.entry_bb = gimple_bb (elt_list_use);
      piece.zero_piece.memset_zero_call = elt_list_use;
    }
  else
    {
      idx_elt_vec_use *ie_use = NULL;
      CHECK (write_group->find_idx_elt_use_from (elt_list_use, ie_use))
      CHECK (ie_use->acc_kind == STORE_P && ie_use->elt_ptr == list_var
	     && integer_zerop (gimple_assign_rhs1 (ie_use->vec_stmt)))

      basic_block head_bb = gimple_bb (elt_list_use);
      class loop *loop = head_bb->loop_father;
      CHECK (loop && check_loop_iter_plus_one_from_zero (loop, ie_use->elt_idx))

      piece.zero_piece.entry_bb = head_bb;
      piece.zero_piece.set_zero_idx_elt = ie_use;
    }

  return true;
}

bool
extract_fallthru_bbs (basic_block start_bb, basic_block end_bb,
		      hash_set<basic_block> &fallthru_bbs)
{
  basic_block next_bb = start_bb;
  do
    {
      fallthru_bbs.add (next_bb);
      if (single_succ_p (next_bb))
	{
	  class loop *loop = NULL;
	  edge ex = NULL;
	  if (extract_simp_inner_loop (next_bb, loop, ex))
	    next_bb = ex->dest;
	  else
	    next_bb = single_succ (next_bb);
	}
      else
	{
	  edge normal_edge = NULL, eh_edge = NULL;
	  TEST (extract_succ_with_eh_edge (next_bb, normal_edge, eh_edge))
	  next_bb = normal_edge->dest;
	}
    }
  while (next_bb != end_bb || fallthru_bbs.contains (next_bb));

  TEST (next_bb == end_bb)
  return true;
}

bool
insert_elts_pattern::check_init_vecs ()
{
  basic_block next_bb = ENTRY_BLOCK_PTR_FOR_FN (cfun)->next_bb;
  CHECK (targ_use->extract_init_check (next_bb, init_piece.other_edge,
				       init_piece.taken_edge))

  hash_set<basic_block> fallthru_bbs;
  CHECK (extract_fallthru_bbs (init_piece.taken_edge->dest,
			       init_piece.other_edge->dest, fallthru_bbs))

  for (unsigned vid = 0; vid < num_vecs; vid++)
    {
      CHECK (check_init_one_vec (vid, fallthru_bbs))
    }
  return true;
}

bool
insert_elts_pattern::check_index_of_elt ()
{
  idx_piece.entry_bb = init_piece.other_edge->dest;
  unsigned vid = UINT_MAX;
  CHECK (targ_use->extract_init_check (idx_piece.entry_bb, idx_piece.taken_edge,
				       idx_piece.other_edge, &vid))

  basic_block out_bb[3];
  out_bb[0] = idx_piece.other_edge->dest;
  idx_piece.vid = vid;
  dyn_vec_info *dyn_vec = targ_type->get_vec (vid);
  basic_block prehead_bb = idx_piece.taken_edge->dest;
  CHECK (single_succ_p (prehead_bb))

  basic_block head_bb = single_succ (prehead_bb);
  class loop *loop = head_bb->loop_father;
  CHECK (loop && loop->header == head_bb && loop_depth (loop) == 1
	 && !loop->inner)


  auto_vec<edge> exits = get_loop_exit_edges (loop);
  unsigned i;
  edge ex;
  basic_block loop_bb[2];
  tree elt_idx = NULL_TREE, curcnt = NULL_TREE, elt = NULL_TREE,
       src_key = NULL_TREE;
  unsigned done_flag = 0;

  FOR_EACH_VEC_ELT (exits, i, ex)
    if (ex->dest == out_bb[0])
      {
	SET_BIT_JUST_ONCE (done_flag, 0)
	CHECK (extract_block_cond (ex->src, LT_EXPR, elt_idx, curcnt,
				   loop_bb[0], out_bb[1])
	       && ex->dest == out_bb[1])
      }
    else
      {
	SET_BIT_JUST_ONCE (done_flag, 1)
	CHECK (extract_block_cond (ex->src, EQ_EXPR, elt, src_key, out_bb[2],
				   loop_bb[1])
	       && ex->dest == out_bb[2])

	if (elt == this->src_elts[dyn_vec->vid])
	  std::swap (elt, src_key);
	else
	  {
	    CHECK (src_key == this->src_elts[dyn_vec->vid])
	  }
      }

  CHECK (done_flag == B_0011 && just_once_each_iteration_p (loop, loop_bb[0])
	 && just_once_each_iteration_p (loop, loop_bb[1]))
  CHECK (targ_use->vec_field_ssa_p (curcnt, F_CUR_CNT, vid))
  CHECK (check_loop_iter_plus_one_from_zero (loop, elt_idx))
  CHECK (targ_use->vec_idx_elt_ssa_p (elt, vid, elt_idx))

  edge e_true = NULL, e_false = NULL;
  tree var = NULL_TREE, minus_one = NULL_TREE;
  if (single_succ_p (out_bb[2]))
    {
      CHECK (extract_block_cond (single_succ (out_bb[2]), EQ_EXPR, var,
				 minus_one, e_true, e_false))
      CHECK (integer_minus_onep (minus_one))
      idx_piece.found_idx = var;
    }
  else
    {
      CHECK (extract_block_cond (out_bb[2], EQ_EXPR, var, minus_one, e_true,
				 e_false))
      CHECK (var == elt_idx && integer_minus_onep (minus_one))
      CHECK (e_true->dest == out_bb[0])
      idx_piece.found_idx = elt_idx;
    }

  add_pieces[0].entry_bb = e_true->dest;
  set_pieces[0].entry_bb = e_false->dest;
  return true;
}

bool
insert_elts_pattern::check_free_one_elt (free_elt_piece &piece)
{
  tree var_free_p = NULL_TREE;
  unsigned vid = piece.vid;
  CHECK (extract_zerop_cond (piece.entry_bb, var_free_p, piece.other_edge,
			     piece.taken_edge))
  CHECK (targ_use->vec_field_ssa_p (var_free_p, F_DEL_ELT_P, vid))

  gimple *gcall = NULL;
  CHECK (extract_call_as_bb_last (piece.taken_edge->dest, gcall))

  CHECK (targ_type->otr_mem_func_p (gcall, targ_use, DEALLOC_P, vid))
  tree arg1 = gimple_call_arg (gcall, 1);
  CHECK (targ_use->vec_idx_elt_ssa_p (arg1, vid, idx_piece.found_idx))
  return true;
}

static bool
check_replic_elt (basic_block &next_bb, replic_elt_piece &piece,
		  target_use_info *)
{
  if (!extract_zerop_cond (next_bb, piece.src_elt, piece.other_edge,
			   piece.taken_edge))
    return true;

  piece.entry_bb = next_bb;
  next_bb = piece.other_edge->dest;

  for (gphi_iterator gsi = gsi_start_nonvirtual_phis (next_bb);
       !gsi_end_p (gsi); gsi_next_nonvirtual_phi (&gsi))
    {
      SET_VAR_JUST_ONCE (piece.new_elt, gsi.phi ())
    }

  return piece.new_elt;
}

static bool
check_ensure_capacity (ensure_cap_piece &piece, target_use_info *targ_use)
{
  basic_block next_bb = piece.entry_bb;
  unsigned &vid = piece.vid;
  tree req_cnt = NULL_TREE, maxcnt = NULL_TREE;
  CHECK (extract_block_cond (next_bb, LE_EXPR, req_cnt, maxcnt,
			     piece.other_edge, piece.taken_edge))

  tree curcnt = NULL_TREE, one = NULL_TREE;
  CHECK (extract_plus_rhs (req_cnt, curcnt, one) && integer_onep (one))
  CHECK (targ_use->extract_vec_idx (curcnt, F_CUR_CNT, vid))
  CHECK (targ_use->vec_field_ssa_p (maxcnt, F_MAX_CNT, vid))

  dyn_vec_info *dyn_vec = targ_type->get_vec (vid);
  gimple_stmt_iterator gsi;
  next_bb = piece.taken_edge->dest;

  gimple *&list_alloc = piece.list_alloc;
  CHECK (extract_call_as_bb_last (next_bb, list_alloc))
  CHECK (targ_type->otr_mem_func_p (list_alloc, targ_use, ALLOC_P, vid))

  tree list_var = gimple_call_lhs (list_alloc);
  tree newmax = NULL_TREE;
  CHECK (
    unscale_offset (gimple_call_arg (list_alloc, 1), dyn_vec->elt_size, newmax))

  basic_block prehead_bb;
  if (single_succ_p (next_bb))
    prehead_bb = next_bb;
  else
    {
      CHECK (EDGE_COUNT (next_bb->succs) == 2)

      edge normal_edge = NULL, eh_edge = NULL;
      CHECK (extract_succ_with_eh_edge (next_bb, normal_edge, eh_edge))
      CHECK (single_succ_p (normal_edge->dest))
      prehead_bb = normal_edge->dest;
    }

  class loop *loop = NULL;
  edge ex = NULL;
  CHECK (extract_simp_inner_loop (prehead_bb, loop, ex))

  tree iter1 = NULL_TREE;
  edge true_edge = NULL, false_edge = NULL;
  CHECK (extract_block_cond (loop->header, LT_EXPR, iter1, curcnt, true_edge,
			     false_edge))

  basic_block copy_elt_bb = true_edge->dest;
  basic_block out_bb = false_edge->dest;
  CHECK (copy_elt_bb == loop->latch && false_edge == ex)
  CHECK (check_loop_iter_plus_one_from_zero (loop, iter1))
  CHECK (targ_use->vec_field_ssa_p (curcnt, F_CUR_CNT, vid))

  bool found = false;
  idx_elt_vec_use *ie_use;

  for (gsi = gsi_start_bb (copy_elt_bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (!targ_use->extract_use (stmt, vid, ie_use))
	continue;

      CHECK (ie_use->acc_kind == LOAD_P && ie_use->elt_idx == iter1)
      piece.old_elt_load = ie_use;

      tree elem_var = gimple_assign_lhs (ie_use->vec_stmt);
      use_operand_p use_p;
      gimple *store_stmt = NULL;
      CHECK (single_imm_use (elem_var, &use_p, &store_stmt)
	     && gimple_bb (store_stmt) == copy_elt_bb)

      CHECK (
	targ_use->read_groups[vid]->find_idx_elt_reverse (store_stmt, ie_use))
      CHECK (ie_use->elt_ptr == list_var && ie_use->elt_idx == iter1)

      piece.new_elt_store = ie_use;
      SET_BOOL_JUST_ONCE (found)
      break;
    }
  CHECK (found)

  if (gsi_end_p (gsi_start_bb (out_bb)))
    {
      piece.zero_piece.entry_bb = out_bb;
      class loop *loop = NULL;
      edge exit_edge = NULL;
      CHECK (extract_simp_inner_loop (out_bb, loop, exit_edge))

      tree iter2 = NULL_TREE, bound = NULL_TREE;
      CHECK (extract_block_cond (loop->header, LT_EXPR, iter2, bound, true_edge,
				 false_edge))
      CHECK (true_edge->dest == loop->latch && bound == newmax)

      tree init = NULL_TREE;
      CHECK (check_loop_iter_plus_one (loop, iter2, init) && init == iter1)

      found = false;
      for (gsi = gsi_start_bb (loop->latch); !gsi_end_p (gsi); gsi_next (&gsi))
	{
	  gimple *stmt = gsi_stmt (gsi);
	  if (!gimple_assign_store_p (stmt))
	    continue;

	  CHECK (integer_zerop (gimple_assign_rhs1 (stmt)))
	  CHECK (
	    targ_use->read_groups[vid]->find_idx_elt_reverse (stmt, ie_use))
	  CHECK (ie_use->elt_ptr == list_var && ie_use->elt_idx == iter2)

	  piece.zero_piece.set_zero_idx_elt = ie_use;
	  SET_BOOL_JUST_ONCE (found)
	}

      CHECK (found)
    }

  out_bb = false_edge->dest;
  unsigned check_flag = 0;
  for (gsi = gsi_start_bb (out_bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
    continue_next_bb:
      gimple *stmt = gsi_stmt (gsi);
      if (check_flag)
	{
	  if (targ_use->vec_field_p (stmt, F_ELT_LIST, vid, STORE_P))
	    {
	      CHECK (gimple_assign_rhs1 (stmt) == list_var)

	      SET_BIT_JUST_ONCE (check_flag, 1);
	      continue;
	    }
	  if (targ_use->vec_field_p (stmt, F_MAX_CNT, vid, STORE_P))
	    {
	      SET_BIT_JUST_ONCE (check_flag, 2);
	      continue;
	    }
	}

      if (gimple_code (stmt) != GIMPLE_CALL)
	continue;

      CHECK (targ_type->otr_mem_func_p (stmt, targ_use, DEALLOC_P, vid))

      tree arg1 = gimple_call_arg (stmt, 1);
      CHECK (targ_use->vec_field_ssa_p (arg1, F_ELT_LIST, vid))

      SET_BIT_JUST_ONCE (check_flag, 0);

      if (stmt == last_stmt (out_bb))
	{
	  edge normal_edge = NULL, eh_edge = NULL;
	  CHECK (extract_succ_with_eh_edge (out_bb, normal_edge, eh_edge))

	  gsi = gsi_start_bb (normal_edge->dest);
	  goto continue_next_bb;
	}
    }

  CHECK (check_flag == B_0111)
  return true;
}

static bool
check_throw_except_edge (target_use_info *targ_use, edge edge, unsigned vid)
{
  gimple *gcall = NULL;
  CHECK (extract_call_as_bb_last (edge->dest, gcall)
	 && gimple_call_num_args (gcall) > 0)

  tree last_arg = gimple_call_arg (gcall, gimple_call_num_args (gcall) - 1);
  CHECK (targ_use->vec_field_ssa_p (last_arg, F_MEM_POOL, vid))
  return true;
}

bool
insert_elts_pattern::check_set_one_elt (basic_block &next_bb, set_elt_piece &piece)
{
  tree curcnt = NULL_TREE, elt_idx = NULL_TREE;
  piece.entry_bb = next_bb;
  CHECK (extract_block_cond (next_bb, LT_EXPR, elt_idx, curcnt,
			     piece.taken_edge, piece.other_edge))

  CHECK (targ_use->extract_vec_idx (curcnt, F_CUR_CNT, piece.vid))
  unsigned vid = piece.vid;

  if (elt_idx != idx_piece.found_idx)
    {
      CHECK (strip_int_ssa_var_cast (elt_idx) == idx_piece.found_idx)
      idx_piece.found_idx = elt_idx;
    }
  CHECK (check_throw_except_edge (targ_use, piece.other_edge, vid))

  next_bb = piece.taken_edge->dest;
  if (targ_type->get_vec (vid)->replic_elt_p)
    {
      free_elt_piece &fe_piece = piece.free_piece;
      fe_piece.entry_bb = next_bb;
      fe_piece.vid = vid;
      CHECK (check_free_one_elt (fe_piece))
      next_bb = fe_piece.other_edge->dest;
    }

  idx_elt_vec_use *ie_use = NULL;
  gimple_stmt_iterator gsi;

  for (gsi = gsi_start_bb (next_bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      idx_elt_vec_use *vec_use;
      if (targ_use->extract_use (stmt, vid, vec_use))
	{
	  SET_SINGLE_VALUE (ie_use, vec_use)
	}
    }

  CHECK (ie_use && ie_use->elt_idx == idx_piece.found_idx)
  return true;
}

bool
insert_elts_pattern::check_set_elts ()
{
  basic_block next_bb = set_pieces[0].entry_bb;
  auto_bitmap visited;
  bitmap_set_bit (visited, idx_piece.vid);

  for (unsigned i = 0; i < num_vecs - 1; i++)
    {
      set_elt_piece &set_piece = set_pieces[i];
      set_piece.entry_bb = next_bb;
      unsigned &vid = set_piece.vid = UINT_MAX;

      replic_elt_piece &rep_piece = set_piece.replic_piece;
      CHECK (check_replic_elt (next_bb, rep_piece, targ_use))

      CHECK (check_set_one_elt (next_bb, set_piece))

      if (rep_piece.src_elt)
	{
	  rep_piece.vid = get_src_elt_idx (rep_piece.src_elt);
	  CHECK (rep_piece.vid == vid && targ_type->get_vec (vid)->replic_elt_p)
	}
      else
	{
	  CHECK (targ_type->get_vec (vid)->replic_elt_p == false)
	}

      CHECK (bitmap_set_bit (visited, vid))
    }

  CHECK (single_succ_p (next_bb) && bb_return_p (single_succ (next_bb)))
  return true;
}

bool
insert_elts_pattern::check_add_one_elt (basic_block next_bb, add_elt_piece &piece,
				unsigned vid)
{
  gimple_stmt_iterator gsi;
  unsigned check_flag = 0;

  for (gsi = gsi_start_bb (next_bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (!gimple_assign_store_p (stmt))
	continue;

      idx_elt_vec_use *ie_use;
      if (targ_use->extract_use (stmt, vid, ie_use))
	{
	  tree rhs = gimple_assign_rhs1 (stmt);
	  if (targ_type->get_vec (vid)->replic_elt_p)
	    {
	      CHECK (rhs == gimple_phi_result (piece.replic_piece.new_elt))
	    }
	  else
	    {
	      CHECK (get_src_elt_idx (rhs) == vid)
	    }

	  CHECK (targ_use->vec_field_ssa_p (ie_use->elt_idx, F_CUR_CNT, vid))

	  piece.elt_store = ie_use;
	  SET_BIT_JUST_ONCE (check_flag, 0);
	}
      else
	{
	  field_vec_use *fld_use = NULL;
	  CHECK (targ_use->extract_use (stmt, vid, fld_use))
	  CHECK (fld_use->acc_kind == STORE_P && fld_use->vf_kind == F_CUR_CNT)

	  piece.curcnt_update = fld_use;
	  SET_BIT_JUST_ONCE (check_flag, 1);
	}
    }

  CHECK (check_flag == B_0011)
  return true;
}

bool
insert_elts_pattern::check_add_elts ()
{
  basic_block next_bb = add_pieces[0].entry_bb;
  auto_bitmap visited;

  for (unsigned i = 0; i < num_vecs; i++)
    {
      add_elt_piece &piece = add_pieces[i];
      piece.entry_bb = next_bb;

      replic_elt_piece &rep_piece = piece.replic_piece;
      CHECK (check_replic_elt (next_bb, rep_piece, targ_use))

      ensure_cap_piece &ens_piece = piece.ensure_piece;
      ens_piece.entry_bb = next_bb;
      CHECK (check_ensure_capacity (ens_piece, targ_use))

      next_bb = ens_piece.other_edge->dest;
      unsigned vid = piece.vid = ens_piece.vid;
      if (rep_piece.src_elt)
	{
	  rep_piece.vid = get_src_elt_idx (rep_piece.src_elt);
	  CHECK (rep_piece.vid == vid && targ_type->get_vec (vid)->replic_elt_p)
	}
      else
	{
	  CHECK (targ_type->get_vec (vid)->replic_elt_p == false)
	}

      CHECK (check_add_one_elt (next_bb, piece, vid))
      CHECK (bitmap_set_bit (visited, vid))
    }

  CHECK (single_succ_p (next_bb) && bb_return_p (single_succ (next_bb)));
  return true;
}

bool
insert_elts_pattern::check_patt ()
{
  if (dump_file && (dump_flags & TDF_DETAILS))
    dump_action_in_func ("> Checking");

  CHECK (targ_use->once_each_vec_def_p (STORE_P)
	 && targ_use->each_vec_def_p (LOAD_P))

  CHECK (check_init_vecs ())

  CHECK (check_index_of_elt ())

  CHECK (check_add_elts ())

  CHECK (check_set_elts ())

  CHECK (targ_use->all_uses_checked_p ())
  return true;
}

static void
update_size_scale_in_call (gimple *gcall, unsigned no)
{
  gcc_checking_assert (gimple_code (gcall) == GIMPLE_CALL
		       && gimple_call_num_args (gcall) > no);

  tree size = gimple_call_arg (gcall, no);
  gcc_checking_assert (ssa_var_p (size));

  gimple *size_def = SSA_NAME_DEF_STMT (size);
  gimple_assign_set_rhs2 (size_def, merge_type->elt_tuple_size);
  update_stmt (size_def);
}

static void
transform_ensure_piece (ensure_cap_piece &piece, target_use_info *targ_use,
			bool del_p = false)
{
  if (!piece.entry_bb)
    return;

  if (del_p)
    {
      basic_block pred_bb = piece.entry_bb;
      basic_block cond_bb = split_block_before_cond_jump (pred_bb);
      remove_edge_and_dom_bbs (piece.taken_edge, targ_use);

      basic_block next_bb = piece.other_edge->dest;
      delete_block_with_vec_uses (cond_bb, targ_use);
      make_edge (pred_bb, next_bb, EDGE_FALLTHRU);
      return;
    }

  update_size_scale_in_call (piece.list_alloc, 1);

  idx_elt_vec_use *elt_load = piece.old_elt_load;
  idx_elt_vec_use *elt_store = piece.new_elt_store;
  elt_load->transform_vec_use (targ_use);
  elt_store->transform_vec_use (targ_use);
  tree from_addr = gimple_assign_lhs (elt_load->ptr_plus_stmt);
  tree to_addr = gimple_assign_lhs (elt_store->ptr_plus_stmt);

  for (unsigned vid = 0; vid < num_vecs; vid++)
    {
      if (vid == piece.vid)
	continue;

      tree load_ref = build_field_ref (unshare_expr (from_addr),
				       merge_type->get_elt_decl (vid));
      tree elt = make_ssa_name (TREE_TYPE (merge_type->get_elt_decl (vid)));
      build_assign_after_stmt (elt, load_ref, elt_load->vec_stmt);

      tree store_ref = build_field_ref (unshare_expr (to_addr),
					merge_type->get_elt_decl (vid));
      build_assign_after_stmt (store_ref, elt, elt_store->vec_stmt);
    }
}

static void
transform_zeroing_piece (zeroing_piece &piece, target_use_info *targ_use,
			 bool del_p = false)
{
  if (!piece.entry_bb)
    return;

  gimple *gcall = piece.memset_zero_call;

  if (del_p)
    {
      if (gcall)
	remove_stmt (gcall, targ_use);
      else
	{
	  gcc_checking_assert (piece.set_zero_idx_elt);
	  piece.set_zero_idx_elt->remove_vec_use (targ_use);
	}
      return;
    }

  update_size_scale_in_call (gcall, 2);
}

void
insert_elts_pattern::transform_init_vecs ()
{
  for (unsigned i = 0; i < num_vecs; i++)
    {
      init_vec_piece &piece = init_piece.init_pieces[i];

      transform_zeroing_piece (piece.zero_piece, targ_use, /* del_p */ i != 0);
      remove_stmt (piece.vec_alloc, targ_use);

      if (i == 0)
	{
	  tree new_alloc_sz
	    = fold_build2 (MULT_EXPR, size_type_node,
			   merge_type->elt_tuple_size, piece.num_maxcnt);
	  gimple_call_set_arg (piece.list_alloc, 1, new_alloc_sz);
	}
      else
	{
	  remove_stmt (piece.list_alloc, targ_use);
	  targ_use->write_groups[piece.vid]->remove_store_vec_uses ();
	}
    }
}

void
insert_elts_pattern::transform_set_elts ()
{
  for (unsigned i = 0; i < num_vecs - 1; i++)
    {
      set_elt_piece &piece = set_pieces[i];
      remove_edge_and_dom_bbs (piece.other_edge, targ_use);

      basic_block cond_bb = split_block_before_cond_jump (piece.entry_bb);
      basic_block next_bb = piece.taken_edge->dest;
      delete_block_with_vec_uses (cond_bb, targ_use);

      edge fallthru = make_edge (piece.entry_bb, next_bb, EDGE_FALLTHRU);
      gcc_checking_assert (fallthru);
    }
}

void
insert_elts_pattern::transform_add_elts ()
{
  for (unsigned i = 0; i < num_vecs; i++)
    {
      add_elt_piece &piece = add_pieces[i];

      transform_ensure_piece (piece.ensure_piece, targ_use, i > 0);
      if (i != num_vecs - 1)
	piece.curcnt_update->remove_vec_use (targ_use);
    }
}

void
insert_elts_pattern::transform_patt ()
{
  transform_init_vecs ();
  transform_add_elts ();
  transform_set_elts ();

  targ_use->transform_targ_use ();
}

bool
pure_pattern::check_profitable ()
{
  vec_use_info *vec_use;
  unsigned i;
  hash_map<tree, unsigned> ei_to_vi;

  for (unsigned vid = 0; vid < num_vecs; vid++)
    {
      FOR_EACH_VEC_ELT (targ_use->read_groups[vid]->vec_uses, i, vec_use)
	{
	  if (vec_use->vu_kind != VU_INDEXED_ELT)
	    continue;

	  idx_elt_vec_use *ie_use = as_a<idx_elt_vec_use *> (vec_use);
	  gimple *idx_def = get_ssa_def_stmt (ie_use->elt_idx);
	  if (!idx_def)
	    continue;

	  basic_block bb = gimple_bb (idx_def);
	  class loop *loop = bb->loop_father;
	  if (!loop && loop_depth (loop) < 2)
	    continue;

	  if (unsigned *pre_vi = ei_to_vi.get (ie_use->elt_idx))
	    {
	      if (*pre_vi != ie_use->vid)
		return true;
	    }
	  else
	    ei_to_vi.put (ie_use->elt_idx, ie_use->vid);
	}
    }

  return false;
}

bool
pure_pattern::find_pure_patt (target_use_info *targ_use, bool &profitable_p)
{
  TEST (targ_use->read_only_p)

  pure_pattern *pure_patt = new pure_pattern (targ_use);
  targ_type->targ_patts.safe_push (pure_patt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    pure_patt->dump_patt ();

  if (pure_patt->check_profitable ())
    {
      profitable_p = true;
      if (dump_file && (dump_flags & TDF_DETAILS))
	dump_action_in_func ("> profitable to do FMO");
    }

  return true;
}

void
pure_pattern::transform_patt ()
{
  targ_use->transform_targ_use ();
}

bool
dtor_pattern::find_dtor_patt (target_use_info *targ_use)
{
  TEST (targ_use->num_writes == 0 && targ_use->num_null_writes == 0
	&& targ_use->once_each_vec_def_p (LOAD_P))

  dtor_pattern *dtor_patt = new dtor_pattern (targ_use);
  if (!dtor_patt->check_patt ())
    {
      delete dtor_patt;
      return false;
    }

  targ_type->targ_patts.safe_push (dtor_patt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    dtor_patt->dump_patt ();
  return true;
}

static inline int
stmt_before_cmp (const void *p, const void *q)
{
  const gimple *a = *(const gimple *const *) (p);
  const gimple *b = *(const gimple *const *) (q);

  if (a == b)
    return 0;
  return stmt_is_before_p (a, b) ? -1 : 1;
}

bool
dtor_pattern::check_free_all_elts (free_elt_piece &piece)
{
  tree free_var = NULL_TREE;
  CHECK (extract_zerop_cond (piece.entry_bb, free_var, piece.other_edge,
			     piece.taken_edge))
  CHECK (targ_use->extract_vec_idx (free_var, F_DEL_ELT_P, piece.vid))
  unsigned vid = piece.vid;

  basic_block prehead = piece.taken_edge->dest;
  class loop *loop = NULL;
  edge exit_edge = NULL, eh_edge = NULL;

  CHECK (extract_simp_innermost_loop_with_eh (prehead, loop, exit_edge, eh_edge)
	 && exit_edge->dest == piece.other_edge->dest)
  if (eh_edge != NULL)
    {
      CHECK (check_eh_delete_vec (targ_use, eh_edge, vid))
    }

  tree iter = NULL_TREE, curcnt = NULL_TREE;
  edge taken_edge = NULL, other_edge = NULL;
  CHECK (extract_block_cond (exit_edge->src, LT_EXPR, iter, curcnt, taken_edge,
			     other_edge))
  CHECK (other_edge == exit_edge)
  CHECK (check_loop_iter_plus_one_from_zero (loop, iter))
  CHECK (targ_use->vec_field_ssa_p (curcnt, F_CUR_CNT, vid))

  gimple *gcall = NULL;
  CHECK (extract_single_call_in_bb (taken_edge->dest, gcall))

  CHECK (targ_type->otr_mem_func_p (gcall, targ_use, DEALLOC_P, vid))
  CHECK (targ_use->vec_idx_elt_ssa_p (gimple_call_arg (gcall, 1), vid, iter))

  piece.elt_dealloc = gcall;
  return true;
}

static bool
store_vptr_p (gimple *stmt)
{
  tree store_ref, base, fld;
  TEST (extract_store_ref (stmt, store_ref))
  TEST (extract_comp_ref (store_ref, base, fld))
  return vptr_field_p (fld, TREE_TYPE (base));
}

bool
dtor_pattern::check_destroy_one_vec (vec_dtor_piece &piece)
{
  unsigned &vid = piece.vid;
  edge &taken_edge = piece.taken_edge, &other_edge = piece.other_edge;
  hash_set<basic_block> fallthru_bbs;

  CHECK (
    targ_use->extract_init_check (piece.entry_bb, taken_edge, other_edge, &vid))
  basic_block next_bb = taken_edge->dest;
  fallthru_bbs.add (next_bb);

  if (targ_type->replic_elt_p (vid))
    {
      free_elt_piece &fe_piece = piece.free_piece;
      fe_piece.entry_bb = next_bb;
      CHECK (check_free_all_elts (fe_piece) && fe_piece.vid == vid)

      next_bb = fe_piece.other_edge->dest;
      fallthru_bbs.add (next_bb);
    }

  gimple *&vec_dealloc = piece.vec_dealloc;
  gimple *&list_dealloc = piece.list_dealloc;
  auto_vec<edge> eh_edges;
  CHECK (extract_fallthru_bb_calls (next_bb, other_edge->dest, fallthru_bbs,
				    list_dealloc, vec_dealloc, eh_edges))
  if (!eh_edges.is_empty ())
    {
      CHECK (eh_edges.length () <= 2)
      CHECK (check_eh_delete_vec (targ_use, eh_edges[0], vid))
    }

  tree expr = NULL_TREE, vptr = NULL_TREE, args[2] = { NULL_TREE, NULL_TREE };
  CHECK (targ_type->extract_otr_mem_func (list_dealloc, DEALLOC_P, expr, vptr,
					  args[0], args[1]))
  CHECK (targ_use->vec_field_ssa_p (args[0], F_MEM_POOL, vid))
  CHECK (targ_use->vec_field_ssa_p (args[1], F_ELT_LIST, vid))

  CHECK (targ_type->extract_otr_mem_func (vec_dealloc, DEALLOC_P, expr, vptr,
					  args[0], args[1]))
  CHECK (targ_use->other_use_p (args[0], vid)
	 && targ_use->other_use_p (args[1], vid))

  CHECK (targ_use->add_extra_del (vec_dealloc) && targ_use->add_extra_del (expr)
	 && targ_use->add_extra_del (vptr))

  vec_use_info *vu;
  unsigned i;
  fallthru_bbs.add (other_edge->dest);

  FOR_EACH_VEC_ELT (targ_use->read_groups[vid]->vec_uses, i, vu)
    {
      if (vu->vu_kind == VU_OTHER && vu->vt_status == VT_INIT)
	{
	  CHECK (fallthru_bbs.contains (gimple_bb (vu->vec_stmt)))
	  if (!gimple_clobber_p (vu->vec_stmt))
	    {
	      CHECK (targ_type->get_vec (vid)->derive_fld_p
		     && store_vptr_p (vu->vec_stmt))
	    }
	  vu->vt_status = VT_TODO;
	}
    }
  return true;
}

bool
dtor_pattern::check_patt ()
{
  auto_vec<gimple *> def_stmts;
  for (unsigned vid = 0; vid < num_vecs; vid++)
    def_stmts.safe_push (targ_use->read_groups[vid]->root_stmts[0]);
  def_stmts.qsort (stmt_before_cmp);

  for (unsigned i = 0; i < num_vecs; i++)
    {
      basic_block entry_bb = gimple_bb (def_stmts[i]);
      dtor_pieces[i].entry_bb = entry_bb;
      CHECK (i == 0 || dtor_pieces[i - 1].other_edge->dest == entry_bb)

      CHECK (check_destroy_one_vec (dtor_pieces[i]))
    }

  CHECK (targ_use->all_uses_checked_p ())
  return true;
}

void
dtor_pattern::transform_patt ()
{
  for (unsigned i = 0; i < num_vecs; i++)
    {
      vec_dtor_piece &piece = dtor_pieces[i];

      remove_stmt (piece.vec_dealloc, targ_use);

      if (i != num_vecs - 1)
	remove_stmt (piece.list_dealloc, targ_use);
    }

  targ_use->transform_targ_use ();
}

void
ctor_pattern::transform_init_zero ()
{
  auto_vec<gimple *> &write_nulls = targ_use->write_nulls;
  if (dump_file && (dump_flags & TDF_DETAILS))
    dump_gimples (write_nulls);

  gimple *stmt = write_nulls[0];
  tree lhs = merge_type->build_field_ref (targ_use->root_ref, F_ELT_LIST);
  gimple_assign_set_lhs (stmt, lhs);
  update_stmt (stmt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "=>\n");
      print_gimple_stmt (dump_file, stmt, 0, TDF_NONE);
      fprintf (dump_file, "\n");
    }

  unsigned i;
  FOR_EACH_VEC_ELT_FROM (write_nulls, i, stmt, 1)
    remove_stmt (stmt);
}

static bool
consecutive_stmts_p (auto_vec<gimple *> &stmts)
{
  stmts.qsort (stmt_before_cmp);
  unsigned i;
  gimple *stmt;
  gimple_stmt_iterator gsi = gsi_for_stmt (stmts[0]);

  FOR_EACH_VEC_ELT_FROM (stmts, i, stmt, 1)
    {
      gsi_next (&gsi);
      TEST (!gsi_end_p (gsi) && gsi_stmt (gsi) == stmt)
    }
  return true;
}

bool
init_ctor_pattern::find_init_ctor_patt (target_use_info *targ_use)
{
  TEST (targ_use->num_reads == 0 && targ_use->num_writes == 0
	&& targ_use->once_each_vec_write_null_p ())
  TEST (consecutive_stmts_p (targ_use->write_nulls))

  init_ctor_pattern *init_ctor_patt = new init_ctor_pattern (targ_use);
  targ_type->targ_patts.safe_push (init_ctor_patt);

  if (dump_file && (dump_flags & TDF_DETAILS))
    init_ctor_patt->dump_patt ();
  return true;
}

void
init_ctor_pattern::transform_patt ()
{
  transform_init_zero ();
}

bool
copy_ctor_pattern::load_from_mem_pool_p (tree var)
{
  return targ_use->load_from_mem_pool_p (var)
	 || other_use->load_from_mem_pool_p (var);
}

bool
copy_ctor_pattern::vec_field_ssa_p (tree var, VEC_FIELD_KIND vf_kind)
{
  return targ_use->vec_field_ssa_p (var, vf_kind, UINT_MAX)
	 || other_use->vec_field_ssa_p (var, vf_kind, UINT_MAX);
}

bool
copy_ctor_pattern::check_copy_elt_loop (copy_vec_piece &piece,
					basic_block next_bb)
{
  class loop *loop = NULL;
  edge ex = NULL;
  CHECK (extract_simp_inner_loop (next_bb, loop, ex))

  piece.end_bb = ex->dest;
  CHECK (!flow_bb_inside_loop_p (loop, piece.end_bb))

  tree idx = NULL_TREE, curcnt = NULL_TREE;
  edge e_true = NULL, e_false = NULL;
  CHECK (
    extract_block_cond (loop->header, LT_EXPR, idx, curcnt, e_true, e_false))
  CHECK (e_false == ex && loop->latch == e_true->dest)

  unsigned vid = piece.vid;
  CHECK (check_loop_iter_plus_one_from_zero (loop, idx)
	 && targ_use->vec_field_ssa_p (curcnt, F_CUR_CNT, vid))

  idx_elt_vec_use *&ie_from = piece.copy_from_elt;
  idx_elt_vec_use *&ie_to = piece.copy_to_elt;
  idx_elt_vec_use *tmp_use;
  gimple_stmt_iterator gsi;

  for (gsi = gsi_start_bb (loop->latch); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (is_gimple_debug (stmt))
	continue;

      if (targ_use->extract_use (stmt, vid, tmp_use))
	{
	  SET_SINGLE_VALUE (ie_to, tmp_use)
	  CHECK (tmp_use->acc_kind == STORE_P)
	}
      else if (other_use->extract_use (stmt, vid, tmp_use))
	{
	  SET_SINGLE_VALUE (ie_from, tmp_use)
	  CHECK (tmp_use->acc_kind == LOAD_P)
	}
    }

  CHECK (ie_from && ie_to)

  tree other_elt = gimple_assign_lhs (ie_from->vec_stmt);
  CHECK (gimple_assign_rhs1 (ie_to->vec_stmt) == other_elt)

  CHECK (targ_use->write_groups[vid]->root_stmts[0] == first_stmt (ex->dest))
  return true;
}

bool
copy_ctor_pattern::check_copy_replic_elt_loop (copy_vec_piece &piece,
					       basic_block next_bb)
{
  unsigned vid = piece.vid;
  next_bb = single_succ (next_bb);
  class loop *loop = next_bb->loop_father;

  CHECK (loop && loop->header == next_bb)

  tree iter = NULL_TREE, curcnt = NULL_TREE;
  edge taken_edge = NULL, other_edge = NULL;
  CHECK (
    extract_block_cond (next_bb, LT_EXPR, iter, curcnt, taken_edge, other_edge))

  piece.end_bb = other_edge->dest;
  CHECK (other_use->vec_field_ssa_p (curcnt, F_CUR_CNT, vid))

  next_bb = taken_edge->dest;
  tree iter2 = NULL_TREE, curcnt2 = NULL_TREE;
  CHECK (extract_block_cond (next_bb, LT_EXPR, iter2, curcnt2, taken_edge,
			     other_edge))
  CHECK (check_throw_except_edge (other_use, other_edge, vid))

  CHECK (iter2 == iter && other_use->vec_field_ssa_p (curcnt2, F_CUR_CNT, vid))

  next_bb = taken_edge->dest;
  CHECK (flow_bb_inside_loop_p (loop, next_bb))

  idx_elt_vec_use *&ie_from = piece.copy_from_elt;
  tree &src_elt = piece.replic_piece.src_elt;

  CHECK (check_replic_elt (next_bb, piece.replic_piece, targ_use))
  CHECK (other_use->extract_use (get_ssa_def_stmt (src_elt), vid, ie_from)
	 && ie_from->elt_idx == iter)

  piece.ensure_piece.entry_bb = next_bb;
  CHECK (check_ensure_capacity (piece.ensure_piece, targ_use)
	 && piece.ensure_piece.vid == vid)
  next_bb = piece.ensure_piece.other_edge->dest;

  tree new_elt = gimple_phi_result (piece.replic_piece.new_elt);
  use_operand_p use_p;
  gimple *store_stmt;
  CHECK (single_imm_use (new_elt, &use_p, &store_stmt)
	 && gimple_bb (store_stmt) == next_bb)

  idx_elt_vec_use *&ie_to = piece.copy_to_elt;
  CHECK (targ_use->extract_use (store_stmt, vid, ie_to))
  CHECK (targ_use->vec_field_ssa_p (ie_to->elt_idx, F_CUR_CNT, vid))

  gimple_stmt_iterator gsi;
  bool check_flag = false;
  for (gsi = gsi_start_bb (next_bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      if (targ_use->vec_field_p (stmt, F_CUR_CNT, vid, STORE_P))
	{
	  SET_BOOL_JUST_ONCE (check_flag);

	  tree rhs = gimple_assign_rhs1 (stmt);
	  tree old_cnt = NULL_TREE;
	  CHECK (extract_plus_one (rhs, old_cnt)
		 && targ_use->vec_field_ssa_p (old_cnt, F_CUR_CNT, vid)
		 && gimple_bb (get_ssa_def_stmt (old_cnt)) == next_bb)

	  piece.update_curcnt = targ_use->get_vec_use (stmt);
	}
    }
  CHECK (check_flag)

  return true;
}

static inline bool
find_vid_from_ptr (auto_vec<write_vu_group *> &groups, tree ptr, unsigned &vid)
{
  for (vid = 0; vid < num_vecs; vid++)
    if (groups[vid]->ptrs.contains (ptr))
      return true;
  return false;
}

bool
copy_ctor_pattern::check_copy_one_vec (copy_vec_piece &piece)
{
  hash_set<basic_block> fallthru_bbs;
  basic_block next_bb = piece.entry_bb;
  fallthru_bbs.add (next_bb);

  gimple *&vec_alloc = piece.vec_alloc;
  CHECK (extract_call_as_bb_last (next_bb, vec_alloc))

  tree expr = NULL_TREE, vptr = NULL_TREE, mp_var = NULL_TREE,
       alloc_sz = NULL_TREE;
  CHECK (targ_type->extract_otr_mem_func (vec_alloc, ALLOC_P, expr, vptr,
					  mp_var, alloc_sz))
  CHECK (load_from_mem_pool_p (mp_var))

  tree vec_ptr = gimple_call_lhs (vec_alloc);
  unsigned &vid = piece.vid;
  CHECK (find_vid_from_ptr (targ_use->write_groups, vec_ptr, vid))

  dyn_vec_info *dyn_vec = targ_type->get_vec (vid);
  HOST_WIDE_INT size_hwi;
  CHECK (extract_hwi (alloc_sz, size_hwi)
	 && size_hwi == dyn_vec->type_size_hwi + POINTER_SIZE_UNITS)

  edge normal_edge, eh_edge;
  if (single_succ_p (next_bb))
    next_bb = single_succ (next_bb);
  else
    {
      CHECK (extract_succ_with_eh_edge (next_bb, normal_edge, eh_edge))
      next_bb = normal_edge->dest;
    }
  fallthru_bbs.add (next_bb);

  unsigned check_flag = 0;
  gimple_stmt_iterator gsi;

  for (gsi = gsi_start_bb (next_bb); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *stmt = gsi_stmt (gsi);
      field_vec_use *vu = NULL;
      if (is_gimple_debug (stmt) || !targ_use->extract_use (stmt, vu))
	continue;

      CHECK (vu->acc_kind == STORE_P && vu->vid == vid)

      SET_BIT_JUST_ONCE (check_flag, vu->vf_kind);
      tree src = gimple_assign_rhs1 (stmt);

      if (vu->vf_kind == F_ELT_LIST)
	{
	  CHECK (integer_zerop (src))
	  continue;
	}
      if (!dyn_vec->replic_elt_p)
	{
	  CHECK (other_use->vec_field_ssa_p (src, vu->vf_kind, vid))
	  continue;
	}

      switch (vu->vf_kind)
	{
	case F_DEL_ELT_P:
	  CHECK (integer_onep (src))
	  break;
	case F_CUR_CNT:
	  CHECK (integer_zerop (src))
	  break;
	case F_MEM_POOL:
	  CHECK (targ_use->mem_pool_ssa_p (src))
	  break;
	default:
	  CHECK (other_use->vec_field_ssa_p (src, vu->vf_kind))
	  break;
	}
    }
  CHECK (check_flag == B_0001_1111)

  gimple *&list_alloc = piece.list_alloc;
  CHECK (extract_call_as_bb_last (next_bb, list_alloc))
  CHECK (targ_type->extract_otr_mem_func (list_alloc, ALLOC_P, expr, vptr,
					  mp_var, alloc_sz))
  CHECK (load_from_mem_pool_p (mp_var))

  tree maxcnt = NULL_TREE;
  CHECK (unscale_offset (alloc_sz, dyn_vec->elt_size, maxcnt)
	 && vec_field_ssa_p (maxcnt, F_MAX_CNT))

  if (single_succ_p (next_bb))
    next_bb = single_succ (next_bb);
  else
    {
      CHECK (extract_succ_with_eh_edge (next_bb, normal_edge, eh_edge))
      CHECK (check_eh_delete_vec (targ_use, eh_edge, vid))
      next_bb = normal_edge->dest;
    }
  fallthru_bbs.add (next_bb);

  tree list_var = gimple_call_lhs (list_alloc);
  CHECK (num_imm_uses (list_var) == 2)
  gimple *use_stmt;
  imm_use_iterator imm_iter;
  check_flag = 0;
  write_vu_group *write_group = targ_use->write_groups[vid];

  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, list_var)
    {
      vec_use_info *vec_use = targ_use->get_vec_use (use_stmt);
      if (vec_use)
	{
	  CHECK (gimple_bb (use_stmt) == next_bb
		 && vec_use->vu_kind == VU_VEC_FIELD)
	  vec_use->vt_status = VT_TODO;

	  field_vec_use *fld_use = as_a<field_vec_use *> (vec_use);
	  CHECK (fld_use->acc_kind == STORE_P && fld_use->vf_kind == F_ELT_LIST
		 && gimple_assign_rhs1 (use_stmt) == list_var)
	  SET_BIT_JUST_ONCE (check_flag, 0);
	}
      else if (memset_call_p (use_stmt))
	{
	  CHECK (gimple_bb (use_stmt) == next_bb)
	  CHECK (gimple_call_arg (use_stmt, 0) == list_var
		 && integer_zerop (gimple_call_arg (use_stmt, 1)))

	  tree zero_size = gimple_call_arg (use_stmt, 2);
	  CHECK (unscale_offset (zero_size, dyn_vec->elt_size, maxcnt)
		 && vec_field_ssa_p (maxcnt, F_MAX_CNT))

	  SET_BIT_JUST_ONCE (check_flag, 1);
	  piece.zero_piece.entry_bb = gimple_bb (use_stmt);
	  piece.zero_piece.memset_zero_call = use_stmt;
	}
      else
	{
	  class loop *loop = NULL;
	  edge ex = NULL;
	  CHECK (extract_simp_inner_loop (next_bb, loop, ex))
	  CHECK (flow_bb_inside_loop_p (loop, gimple_bb (use_stmt)))

	  idx_elt_vec_use *ie_use = NULL;
	  CHECK (write_group->find_idx_elt_use_from (use_stmt, ie_use))

	  CHECK (ie_use->acc_kind == STORE_P
		 && integer_zerop (gimple_assign_rhs1 (ie_use->vec_stmt)))
	  CHECK (check_loop_iter_plus_one_from_zero (loop, ie_use->elt_idx))

	  tree idx = NULL_TREE, maxcnt = NULL_TREE;
	  CHECK (extract_block_cond (ex->src, LT_EXPR, idx, maxcnt)
		 && vec_field_ssa_p (maxcnt, F_MAX_CNT))

	  next_bb = ex->dest;

	  SET_BIT_JUST_ONCE (check_flag, 1);
	  piece.zero_piece.entry_bb = gimple_bb (use_stmt);
	  piece.zero_piece.set_zero_idx_elt = ie_use;
	}
    }
  CHECK (check_flag == B_0011 && single_succ_p (next_bb))

  fallthru_bbs.add (next_bb);
  if (dyn_vec->replic_elt_p)
    {
      CHECK (check_copy_replic_elt_loop (piece, next_bb))
    }
  else
    {
      CHECK (check_copy_elt_loop (piece, next_bb))
    }

  fallthru_bbs.add (piece.end_bb);
  unsigned i;
  vec_use_info *vu;
  tree ptr = write_group->ptrs[0];

  FOR_EACH_VEC_ELT (write_group->vec_uses, i, vu)
    {
      if (vu->vu_kind == VU_OTHER && vu->vt_status == VT_INIT)
	{
	  gimple *vec_stmt = vu->vec_stmt;
	  CHECK (fallthru_bbs.contains (gimple_bb (vec_stmt)))

	  if (!gimple_clobber_p (vec_stmt))
	    {
	      CHECK (gimple_assign_store_p (vec_stmt))
	      if (load_from_mem_pool_p (gimple_assign_rhs1 (vec_stmt)))
		{
		  tree store_ref = NULL_TREE;
		  CHECK (extract_store_ref (vec_stmt, store_ref)
			 && mem_ref_of_addr_p (store_ref, ptr))
		}
	      else
		{
		  CHECK (dyn_vec->derive_fld_p && store_vptr_p (vec_stmt))
		}
	    }
	  vu->vt_status = VT_TODO;
	}
    }
  return true;
}

bool
copy_ctor_pattern::find_copy_ctor_patt (auto_vec<target_use_info *> &targ_uses)
{
  tree parm = DECL_ARGUMENTS (cfun->decl);
  TEST (targ_uses.length () == 2 && list_length (parm) == 2)

  tree root_base = ssa_default_def (cfun, parm);
  TEST (root_base && targ_type->targ_type_ptr_p (root_base))

  tree other_base = ssa_default_def (cfun, TREE_CHAIN (parm));
  TEST (other_base && targ_type->targ_type_ptr_p (other_base))

  target_use_info *targ_use = targ_uses[0];
  target_use_info *other_use = targ_uses[1];

  TEST (other_use->read_only_p)
  TEST (ref_of_addr_p (targ_use->root_ref, root_base)
	&& ref_of_addr_p (other_use->root_ref, other_base))
  TEST (targ_use->num_writes == num_vecs
	&& targ_use->num_null_writes == num_vecs
	&& other_use->each_vec_def_p (LOAD_P))

  copy_ctor_pattern *ctor_patt = new copy_ctor_pattern (targ_use, other_use);
  if (!ctor_patt->check_patt ())
    {
      delete ctor_patt;
      return false;
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    ctor_patt->dump_patt ();

  targ_type->targ_patts.safe_push (ctor_patt);
  return true;
}

static inline int
dominate_info_pair_cmp (const void *p, const void *q)
{
  const basic_block a = ((const std::pair<basic_block, unsigned> *) p)->first;
  const basic_block b = ((const std::pair<basic_block, unsigned> *) q)->first;
  return dominated_by_p (CDI_DOMINATORS, b, a) ? -1 : 1;
}

bool
copy_ctor_pattern::check_patt ()
{
  basic_block next_bb = ENTRY_BLOCK_PTR_FOR_FN (cfun)->next_bb;
  TEST (consecutive_stmts_p (targ_use->write_nulls)
	&& next_bb == gimple_bb (*(targ_use->write_nulls.begin ())))

  edge start_edge, other_edge;
  TEST (other_use->extract_init_check (next_bb, start_edge, other_edge)
	&& bb_return_p (other_edge->dest))

  for (unsigned i = 0; i < num_vecs; i++)
    {
      if (i == 0)
	copy_pieces[i].entry_bb = start_edge->dest;
      else
	copy_pieces[i].entry_bb = copy_pieces[i - 1].end_bb;

      CHECK (check_copy_one_vec (copy_pieces[i]))
      CHECK (i != 0 || copy_pieces[i].zero_piece.memset_zero_call != NULL)
    }

  CHECK (targ_use->all_uses_checked_p () && other_use->all_uses_checked_p ())
  return true;
}

void
copy_ctor_pattern::transform_patt ()
{
  transform_init_zero ();

  for (unsigned i = 0; i < num_vecs; i++)
    {
      copy_vec_piece &piece = copy_pieces[i];
      unsigned vid = piece.vid;

      transform_zeroing_piece (piece.zero_piece, targ_use, i != 0);
      transform_ensure_piece (piece.ensure_piece, targ_use, true);
      piece.copy_to_elt->transform_vec_use (targ_use);
      remove_stmt (piece.vec_alloc, targ_use);

      if (i == 0)
	update_size_scale_in_call (piece.list_alloc, 1);
      else
	{
	  remove_stmt (piece.list_alloc, targ_use);
	  targ_use->write_groups[vid]->remove_store_vec_uses ();
	}

      if (targ_type->get_vec (vid)->replic_elt_p)
	{
	  piece.copy_from_elt->transform_vec_use (targ_use);
	  piece.copy_to_elt->transform_vec_use (targ_use);
	  gimple *ptr_plus_stmt = piece.copy_to_elt->ptr_plus_stmt;

	  tree new_offset
	    = gimple_assign_lhs (piece.copy_from_elt->offset_stmt);
	  gimple_assign_set_rhs2 (ptr_plus_stmt, new_offset);
	  update_stmt (ptr_plus_stmt);

	  gcc_checking_assert (piece.update_curcnt);
	  piece.update_curcnt->remove_vec_use (targ_use);
	}
    }
  targ_use->transform_targ_use ();
  other_use->transform_targ_use ();
}

static inline tree
get_suffix_id (const char *name, unsigned suffix)
{
  char str[32];
  sprintf (str, "_%d", suffix);
  char *tmp_name = concat (name, str, NULL);

  tree id = get_identifier (tmp_name);
  free (tmp_name);
  return id;
}

static unsigned fmo_name_suffix_id = 0;

static void
dump_record_type (tree record_type)
{
  print_generic_expr (dump_file, record_type, TDF_SLIM);
  fprintf (dump_file, " {\n");

  for (tree fld = TYPE_FIELDS (record_type); fld; fld = DECL_CHAIN (fld))
    {
      fprintf (dump_file, "  ");
      print_generic_expr (dump_file, TREE_TYPE (fld), TDF_SLIM);
      fprintf (dump_file, " ");
      print_generic_expr (dump_file, fld, TDF_SLIM);
      fprintf (dump_file, "\n");
    }
  fprintf (dump_file, "};\n");
}

void
merge_type_info::create_elt_tuple ()
{
  elt_tuple_type = make_node (RECORD_TYPE);
  tree last_decl = NULL_TREE;
  auto_vec<dyn_vec_info *> sorted_dyn_vecs;

  sorted_dyn_vecs.safe_grow_cleared (targ_type->dyn_vecs.length (), true);

  for (unsigned vid = 0; vid < num_vecs; vid++)
    {
      dyn_vec_info *vec = targ_type->dyn_vecs[vid];
      sorted_dyn_vecs[vec->param_id - 1] = vec;
    }

  for (unsigned i = 0; i < num_vecs; i++)
    {
      dyn_vec_info *vec = sorted_dyn_vecs[i];

      gcc_checking_assert (vec);

      tree f_elt_list = vec->get_field (F_ELT_LIST);
      tree elt_type = TREE_TYPE (TREE_TYPE (f_elt_list));
      tree elt_name = get_suffix_id ("_elt", i);
      tree elt_decl
	= build_decl (UNKNOWN_LOCATION, FIELD_DECL, elt_name, elt_type);
      DECL_CONTEXT (elt_decl) = elt_tuple_type;

      if (!i)
	TYPE_FIELDS (elt_tuple_type) = elt_decl;
      else
	DECL_CHAIN (last_decl) = elt_decl;

      last_decl = elt_decl;
      elt_decls[vec->vid] = elt_decl;
    }

  tree name = get_suffix_id ("_elt_tuple", fmo_name_suffix_id);
  tree decl = build_decl (BUILTINS_LOCATION, TYPE_DECL, name, elt_tuple_type);

  DECL_IGNORED_P (decl) = 1;
  DECL_ARTIFICIAL (decl) = 1;
  TYPE_NAME (elt_tuple_type) = name;
  TYPE_STUB_DECL (elt_tuple_type) = decl;
  TYPE_ARTIFICIAL (elt_tuple_type) = 1;
  layout_type (elt_tuple_type);

  elt_tuple_size = TYPE_SIZE_UNIT (elt_tuple_type);
}

static tree
build_decl_of_type (const char *name, tree type)
{
  tree decl
    = build_decl (UNKNOWN_LOCATION, FIELD_DECL, get_identifier (name), type);
  return decl;
}

merge_type_info::merge_type_info ()
{
  elt_decls.safe_grow_cleared (num_vecs, true);
  create_elt_tuple ();

  tree root_struct = targ_type->root_struct;
  new_struct = make_node (RECORD_TYPE);

  tree cnt_type = TREE_TYPE (targ_type->get_vec (0)->get_field (F_CUR_CNT));
  HOST_WIDE_INT cnt_size = tree_to_shwi (TYPE_SIZE_UNIT (cnt_type));
  HOST_WIDE_INT padding_size
    = (num_vecs * POINTER_SIZE_UNITS) - (2 * cnt_size + POINTER_SIZE_UNITS);
  gcc_checking_assert (padding_size >= 0 && padding_size % cnt_size == 0);
  unsigned num_padding = padding_size / cnt_size;

  auto_vec<tree> decls;
  for (tree fld = TYPE_FIELDS (root_struct); fld; fld = DECL_CHAIN (fld))
    {
      if (fld != targ_type->vec_decls[0])
	{
	  if (integer_zerop (DECL_SIZE (fld)))
	    continue;

	  tree new_fld = copy_node (fld);
	  decls.safe_push (new_fld);

	  if (fld == targ_type->f_mem_pool)
	    fld_decls[F_MEM_POOL] = new_fld;
	  continue;
	}

      fld_decls[F_ELT_LIST]
	= build_decl_of_type ("_f_elt_list", get_elt_list_type ());
      fld_decls[F_CUR_CNT] = build_decl_of_type ("_f_cur_cnt", cnt_type);
      fld_decls[F_MAX_CNT] = build_decl_of_type ("_f_max_cnt", cnt_type);

      decls.safe_push (fld_decls[F_ELT_LIST]);
      decls.safe_push (fld_decls[F_CUR_CNT]);
      decls.safe_push (fld_decls[F_MAX_CNT]);

      for (unsigned i = 1; i < num_vecs; i++)
	fld = DECL_CHAIN (fld);

      if (num_padding)
	{
	  tree array_type = build_index_type (size_int (num_padding - 1));
	  array_type = build_array_type (cnt_type, array_type);
	  tree f_padding
	    = build_decl (UNKNOWN_LOCATION, FIELD_DECL, NULL_TREE, array_type);
	  decls.safe_push (f_padding);
	}
    }

  tree new_fld = decls[0];
  unsigned i;

  TYPE_FIELDS (new_struct) = new_fld;
  DECL_CONTEXT (new_fld) = new_struct;
  DECL_ATTRIBUTES (new_fld) = tree_cons (get_identifier ("vec_fld_elt_list"),
					 NULL_TREE,
					 DECL_ATTRIBUTES (new_fld));

  FOR_EACH_VEC_ELT_FROM (decls, i, new_fld, 1)
    {
      DECL_CHAIN (decls[i - 1]) = new_fld;
      DECL_CONTEXT (new_fld) = new_struct;
    }

  tree name = get_suffix_id ("_fmo_st", fmo_name_suffix_id);
  tree decl = build_decl (BUILTINS_LOCATION, TYPE_DECL, name, new_struct);

  DECL_IGNORED_P (decl) = 1;
  DECL_ARTIFICIAL (decl) = 1;
  TYPE_NAME (new_struct) = name;
  TYPE_STUB_DECL (new_struct) = decl;
  TYPE_ARTIFICIAL (new_struct) = 1;
  layout_type (new_struct);
  ++fmo_name_suffix_id;

  gcc_checking_assert (tree_int_cst_equal (TYPE_SIZE_UNIT (new_struct),
					   TYPE_SIZE_UNIT (root_struct)));

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "> Created new types for merged fields:\n");
      dump_record_type (root_struct);
      fprintf (dump_file, "=>\n");
      dump_record_type (elt_tuple_type);
      dump_record_type (new_struct);
    }
}

tree
merge_type_info::build_field_ref (tree root_ref, VEC_FIELD_KIND vf_kind)
{
  tree base_ref;
  HOST_WIDE_INT offset;

  if (!get_ref_base_and_offset_hwi (root_ref, base_ref, offset)
      || TREE_CODE (base_ref) != MEM_REF)
    gcc_unreachable ();

  gcc_assert ((offset % BITS_PER_UNIT) == 0);

  offset /= BITS_PER_UNIT;
  offset += tree_to_shwi (TREE_OPERAND (base_ref, 1));
  base_ref = fold_build2 (MEM_REF, new_struct,
			  TREE_OPERAND (base_ref, 0),
			  build_int_cst (build_pointer_type (new_struct),
					 offset));

  tree field_decl = fld_decls[vf_kind];
  tree fov_ref = build3 (COMPONENT_REF, TREE_TYPE (field_decl), base_ref,
			 field_decl, NULL_TREE);
  return fov_ref;
}

tree
merge_type_info::build_count_cst (int val)
{
  return build_int_cst (TREE_TYPE (fld_decls[F_CUR_CNT]), val);
}

static bool
find_cand_vecs (tree root_base)
{
  auto_vec<std::pair<tree, HOST_WIDE_INT> > cand_fields;
  gimple *use_stmt;
  imm_use_iterator imm_iter;
  unsigned num_flds = 0;

  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, root_base)
    {
      if (!gimple_assign_store_p (use_stmt))
	continue;

      tree lhs = gimple_assign_lhs (use_stmt);
      TEST (TREE_CODE (lhs) == COMPONENT_REF
	    && ref_of_addr_p (TREE_OPERAND (lhs, 0), root_base))

      tree fld_vec = TREE_OPERAND (lhs, 1);

      if (!POINTER_TYPE_P (TREE_TYPE (fld_vec))
	  || TREE_CODE (TREE_TYPE (TREE_TYPE (fld_vec))) != RECORD_TYPE)
	continue;

      HOST_WIDE_INT offset;
      tree root_ref = NULL_TREE;
      TEST (get_ref_base_and_offset_hwi (lhs, root_ref, offset)
	    && ref_of_addr_p (root_ref, root_base))

      cand_fields.safe_push (std::make_pair (fld_vec, offset));

      num_flds++;
      TEST (num_flds <= num_vecs)
    }

  TEST (num_flds == num_vecs && targ_type->init_dyn_vecs (cand_fields))
  return true;
}

static bool
find_vec_other_flds ()
{
  dyn_vec_info *dyn_vec;
  unsigned vid;

  FOR_EACH_VEC_ELT (targ_type->dyn_vecs, vid, dyn_vec)
    {
      for (tree fld = TYPE_FIELDS (dyn_vec->vec_type); fld;
	   fld = DECL_CHAIN (fld))
	{
	  if (TREE_CODE (fld) != FIELD_DECL)
	    continue;

	  switch (TREE_CODE (TREE_TYPE (fld)))
	    {
	    case INTEGER_TYPE:
	      if (dyn_vec->field_p (fld, F_CUR_CNT))
		continue;
	      TEST (dyn_vec->set_field (F_MAX_CNT, fld))
	      break;

	    case BOOLEAN_TYPE:
	      TEST (dyn_vec->set_field (F_DEL_ELT_P, fld))
	      break;

	    case POINTER_TYPE:
	    case REFERENCE_TYPE:
	      if (dyn_vec->field_p (fld, F_ELT_LIST)
		  || vptr_field_p (fld, dyn_vec->vec_type))
		continue;
	      TEST (dyn_vec->set_field (F_MEM_POOL, fld))
	      break;

	    default:
	      break;
	    }
	}

      TEST (dyn_vec->get_field (F_MAX_CNT) && dyn_vec->get_field (F_MEM_POOL)
	    && dyn_vec->get_field (F_DEL_ELT_P))
    }

  tree uniq_type = NULL;
  FOR_EACH_VEC_ELT (targ_type->dyn_vecs, vid, dyn_vec)
    {
      tree type1 = TREE_TYPE (dyn_vec->get_field (F_CUR_CNT));
      tree type2 = TREE_TYPE ((dyn_vec->get_field (F_MAX_CNT)));
      TEST (types_matched_p (type1, type2))

      if (!uniq_type)
	uniq_type = type1;
      else
	{
	  TEST (types_matched_p (type1, uniq_type))
	}
    }

  for (tree fld = TYPE_FIELDS (targ_type->root_struct); fld;
       fld = DECL_CHAIN (fld))
    if (TREE_CODE (fld) == FIELD_DECL && POINTER_TYPE_P (TREE_TYPE (fld))
	&& !targ_type->fld_vec_p (fld))
      {
	TEST (targ_type->set_mempool (fld))
      }

  return targ_type->f_mem_pool;
}

static bool
extract_phi_with_zero_init (gimple *stmt, edge &zero_init_edge,
			    edge &other_edge)
{
  zero_init_edge = NULL;
  CHECK (stmt != NULL && gimple_code (stmt) == GIMPLE_PHI
	 && gimple_phi_num_args (stmt) == 2)

  for (unsigned i = 0; i < 2; ++i)
    {
      if (integer_zerop (gimple_phi_arg_def (stmt, i)))
	{
	  CHECK (zero_init_edge == NULL)
	  zero_init_edge = EDGE_PRED (gimple_bb (stmt), i);
	}
      else
	other_edge = EDGE_PRED (gimple_bb (stmt), i);
    }

  return true;
}

static unsigned
get_parameter_index (tree name)
{
  tree parm = DECL_ARGUMENTS (cfun->decl);

  gcc_checking_assert (SSA_NAME_IS_DEFAULT_DEF (name));

  for (unsigned index = 0; parm; parm = DECL_CHAIN (parm), index++)
    {
      if (parm == SSA_NAME_VAR (name))
	return index;
    }

  gcc_unreachable ();
  return -1;
}

static bool
find_orig_src_elt (auto_vec<tree> &src_elts, tree elt, unsigned vid)
{
  for (unsigned i = vid; i < num_vecs; i++)
    if (src_elts[i] == elt)
      {
	std::swap (src_elts[vid], src_elts[i]);
	targ_type->get_vec (vid)->param_id = get_parameter_index (elt);
	return true;
      }

  edge zero_init_edge = NULL, other_edge = NULL;
  CHECK (extract_phi_with_zero_init (get_ssa_def_stmt (elt), zero_init_edge,
				     other_edge))

  basic_block check_zero_bb = zero_init_edge->src;
  tree orig_elt = NULL_TREE;
  edge edges[2] = { NULL, NULL };
  CHECK (extract_zerop_cond (check_zero_bb, orig_elt, edges[0], edges[1]))

  for (unsigned i = vid; i < num_vecs; i++)
    if (src_elts[i] == orig_elt)
      {
	std::swap (src_elts[vid], src_elts[i]);
	targ_type->get_vec (vid)->replic_elt_p = true;
	targ_type->get_vec (vid)->param_id = get_parameter_index (orig_elt);
	return true;
      }

  return false;
}

static bool
find_fld_cur_cnt (gimple *store_stmt, tree vec_base, dyn_vec_info *dyn_vec)
{
  tree store_ref, load_ref;
  if (!extract_store_ref (store_stmt, store_ref))
    return true;

  tree curcnt;
  if (!extract_plus_one (gimple_assign_rhs1 (store_stmt), curcnt))
    return true;

  if (!extract_ssa_load_ref (curcnt, load_ref)
      || !operand_equal_p (store_ref, load_ref, OEP_ADDRESS_OF))
    return true;

  tree fld[2], base_ref_type[2];
  if (!extract_base_ref_of_addr (store_ref, vec_base, fld[0], base_ref_type[0])
      || !extract_base_ref_of_addr (load_ref, vec_base, fld[1],
				    base_ref_type[1]))
    return true;

  CHECK (fld[0] == fld[1]
	 && types_matched_p (base_ref_type[0], base_ref_type[1]))
  CHECK (dyn_vec->set_vec_type (base_ref_type[0])
	 && dyn_vec->set_field (F_CUR_CNT, fld[0]))
  return true;
}

static bool
find_fld_elt_list (gimple *load_stmt, tree vec_base, unsigned vid,
		   auto_vec<tree> &src_elts)
{
  tree load_ref;
  if (extract_load_ref (load_stmt, load_ref))
    {
      tree idx;
      gimple *offset_stmt = NULL, *ptr_plus_stmt = NULL, *elt_stmt = NULL;
      ACCESS_KIND acc_kind;
      if (extract_idx_elt (load_stmt, idx, offset_stmt, ptr_plus_stmt, elt_stmt,
			   acc_kind)
	  && acc_kind == STORE_P)
	{
	  tree stored_elt = gimple_assign_rhs1 (elt_stmt);
	  CHECK (find_orig_src_elt (src_elts, stored_elt, vid))

	  tree f_elt_list = NULL_TREE, base_ref_type = NULL_TREE;
	  dyn_vec_info *dyn_vec = targ_type->get_vec (vid);
	  CHECK (extract_base_ref_of_addr (load_ref, vec_base, f_elt_list,
					   base_ref_type))

	  CHECK (dyn_vec->set_vec_type (base_ref_type)
		 && dyn_vec->set_field (F_ELT_LIST, f_elt_list));
	}
    }
  return true;
}

static bool
find_cand_target (tree root_base, auto_vec<tree> &src_elts,
		  target_use_info *&targ_use)
{
  TEST (find_cand_vecs (root_base))

  auto_vec<target_use_info *> targ_uses;
  CHECK (collect_vec_defs (targ_uses) && targ_uses.length () == 1)

  targ_use = targ_uses[0];
  CHECK (targ_use->once_each_vec_def_p (STORE_P)
	 && targ_use->each_vec_def_p (LOAD_P))

  unsigned i;
  gimple *def_stmt, *use_stmt;
  imm_use_iterator imm_iter;

  for (unsigned vid = 0; vid < num_vecs; vid++)
    {
      dyn_vec_info *dyn_vec = targ_type->get_vec (vid);
      bool success = false;

      FOR_EACH_VEC_ELT (targ_use->read_groups[vid]->root_stmts, i, def_stmt)
	{
	  tree vec_base = gimple_assign_lhs (def_stmt);

	  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, vec_base)
	    {
	      if (!dyn_vec->get_field (F_ELT_LIST))
		{
		  CHECK (find_fld_elt_list (use_stmt, vec_base, vid, src_elts))
		}
	      if (!dyn_vec->get_field (F_CUR_CNT))
		{
		  CHECK (find_fld_cur_cnt (use_stmt, vec_base, dyn_vec))
		}
	    }

	  if (dyn_vec->get_field (F_ELT_LIST) && dyn_vec->get_field (F_CUR_CNT))
	    {
	      success = true;
	      break;
	    }
	}

      CHECK (dyn_vec->param_id && success)
    }

  CHECK (find_vec_other_flds ())
  CHECK (targ_use->collect_vec_uses ())
  return true;
}

static bool
check_type_unique (auto_vec<target_type_info *> &target_types,
		   target_type_info *targ_info)
{
  unsigned i;
  target_type_info *pre_targ;

  FOR_EACH_VEC_ELT (target_types, i, pre_targ)
    if (types_matched_p (targ_info->root_struct, pre_targ->root_struct))
      {
	pre_targ->valid_p = false;
	return false;
      }

  return true;
}

static bool
extract_func_parms (tree &root_struct, tree &root_base,
		    auto_vec<tree> &src_elts)
{
  tree parm = DECL_ARGUMENTS (cfun->decl);
  TEST (parm && TREE_TYPE (parm) && POINTER_TYPE_P (TREE_TYPE (parm)))

  num_vecs = list_length (parm) - 1;
  TEST (num_vecs >= MIN_NUM_DYN_VECS && num_vecs <= MAX_NUM_DYN_VECS)

  TEST (root_struct = TREE_TYPE (TREE_TYPE (parm)))
  TEST (TREE_CODE (root_struct) == RECORD_TYPE
	&& COMPLETE_TYPE_P (root_struct)
	&& TREE_CODE (TYPE_SIZE (root_struct)) == INTEGER_CST)

  TEST (root_base = ssa_default_def (cfun, parm))

  parm = TREE_CHAIN (parm);
  while (parm)
    {
      if (tree elt = ssa_default_def (cfun, parm))
	{
	  src_elts.safe_push (elt);
	  parm = TREE_CHAIN (parm);
	}
      else
	return false;
    }

  return true;
}

static bool
find_target_type_in_function (cgraph_node *node)
{
  cfun_context node_ctx (node);
  tree root_struct = NULL_TREE, root_base = NULL_TREE;
  auto_vec<tree> src_elts;

  if (node->get_availability () <= AVAIL_INTERPOSABLE
      || node->has_aliases_p ())
    return false;

  if (!extract_func_parms (root_struct, root_base, src_elts))
    return false;

  targ_type = new target_type_info (root_struct);
  target_use_info *targ_use = NULL;

  if (find_cand_target (root_base, src_elts, targ_use))
    {
      calculate_dominance_info (CDI_DOMINATORS);

      if (insert_elts_pattern::find_insert_elts_patt (targ_use, src_elts))
	return true;

      if (dump_file && (dump_flags & TDF_DETAILS))
	targ_use->dump_target_use ();
    }

  delete targ_type;
  targ_type = NULL;

  return false;
}

static int
find_target_type (auto_vec<target_type_info *> &target_types)
{
  struct cgraph_node *node;

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    {
      if (!find_target_type_in_function (node))
	continue;

      if (!check_type_unique (target_types, targ_type))
	{
	  delete targ_type;
	  targ_type = NULL;
	  continue;
	}

      target_types.safe_push (targ_type);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  cfun_context node_ctx (node);
	  dump_action_in_func ("> Find candidate target type");
	  targ_type->dump_targ_type ();
	}
    }

  return target_types.length ();
}

static bool
check_target_type ()
{
  bool profitable_p = true;
  struct cgraph_node *node;
  function *func_insert_elts = targ_type->targ_patts[0]->fun;
  target_use_info *targ_use = NULL;
  const char *fail_msg = "";
  unsigned i;

  DECL_ATTRIBUTES (func_insert_elts->decl)
	= tree_cons (get_identifier ("fmo_insert_func"),
		     NULL_TREE,
		     DECL_ATTRIBUTES (func_insert_elts->decl));

  FOR_EACH_DEFINED_FUNCTION (node)
    {
      if (!node->has_gimple_body_p () || node->inlined_to
	  || DECL_STRUCT_FUNCTION (node->decl) == func_insert_elts)
	continue;

      cfun_context node_ctx (node);
      auto_vec<target_use_info *> targ_uses;
      if (!collect_vec_defs (targ_uses))
	{
	  fail_msg = "unsupported target type use.";
	  goto check_failed;
	}
      if (targ_uses.is_empty ())
	continue;

      calculate_dominance_info (CDI_DOMINATORS);

      if (dump_file && (dump_flags & TDF_DETAILS))
	dump_action_in_func ("> Checking");

      FOR_EACH_VEC_ELT (targ_uses, i, targ_use)
	{
	  if (!targ_use->collect_vec_uses ())
	    {
	      fail_msg = "unsupported vector type use.";
	      goto check_failed;
	    }
	}

      if (copy_ctor_pattern::find_copy_ctor_patt (targ_uses))
	continue;

      FOR_EACH_VEC_ELT (targ_uses, i, targ_use)
	{
	  if (pure_pattern::find_pure_patt (targ_use, profitable_p))
	    continue;
	  if (dtor_pattern::find_dtor_patt (targ_use))
	    continue;
	  if (init_ctor_pattern::find_init_ctor_patt (targ_use))
	    continue;

	  fail_msg = "unsupported pattern.";
	  goto check_failed;
	}
      continue;

    check_failed:
      if (dump_file)
	{
	  dump_action_in_func ("> FMO failed");
	  fprintf (dump_file, "%s\n", fail_msg);

	  FOR_EACH_VEC_ELT (targ_uses, i, targ_use)
	    targ_use->dump_target_use ();
	}
      return false;
    }

  if (!profitable_p && dump_file)
    fprintf (
      dump_file,
      "> FMO failed as not profitable (%d target patterns are identified).\n",
      targ_type->targ_patts.length ());

  return profitable_p;
}

static void
transform_target_type ()
{
  if (flag_fmo_no_trans)
    {
      if (dump_file)
	fprintf (dump_file,
		 "> FMO failed as not transformed (%d target patterns are "
		 "identified).\n",
		 targ_type->targ_patts.length ());
      return;
    }

  merge_type = new merge_type_info ();
  int i;
  pattern_info *patt;

  FOR_EACH_VEC_ELT (targ_type->targ_patts, i, patt)
    {
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  dump_action_in_func ("\n>>>> Transforming %s <<<<\n",
			       patt_names[patt->pt_kind], patt->fun);
	  patt->dump_patt ();
	}

      cfun_context node_ctx (patt->fun);
      patt->transform_patt ();
    }

  FOR_EACH_VEC_ELT (targ_type->targ_patts, i, patt)
    {
      if (need_ssa_update_p (patt->fun))
	{
	  cfun_context node_ctx (patt->fun);
	  free_dominance_info (CDI_DOMINATORS);
	  cleanup_tree_cfg (TODO_update_ssa);
	}
    }

  if (dump_file)
    fprintf (dump_file, "> FMO done (%d target patterns).\n",
	     targ_type->targ_patts.length ());

  delete merge_type;
}

static bool flag_wild_array_field_access = true;

static inline
tree get_normalized_type (tree type)
{
  type = TYPE_MAIN_VARIANT (type);

  if (RECORD_OR_UNION_TYPE_P (type) && TYPE_CANONICAL (type))
    {
      tree canon_type = TYPE_CANONICAL (type);

      if (canon_type == type)
	return type;

      if (TYPE_CXX_LOCAL (canon_type) && TYPE_CXX_LOCAL (type))
	return canon_type;

      if (odr_type_p (type))
	return prevailing_odr_type (type);
    }

  return type;
}

static inline
int get_array_dimension (tree type)
{
  int dim;

  for (dim = 0; TREE_CODE (type) == ARRAY_TYPE; dim++)
    type = TREE_TYPE (type);

  return dim;
}

static inline
tree get_array_etype (tree type, tree may_etype = NULL_TREE)
{
  if (!may_etype || TREE_CODE (may_etype) != ARRAY_TYPE
      || TREE_CODE (type) != ARRAY_TYPE)
    {
      while (TREE_CODE (type) == ARRAY_TYPE)
	type = TREE_TYPE (type);

      return type;
    }

  int dim = get_array_dimension (may_etype);

  for (int i = get_array_dimension (type); i > dim; i--)
    type = TREE_TYPE (type);

  return type;
}

static inline
tree get_underlying_type (tree type)
{
  while (POINTER_TYPE_P (type) || TREE_CODE (type) == ARRAY_TYPE)
    type = TREE_TYPE (type);

  return type;
}

static inline offset_int
signed_offset (tree offset)
{
 tree type = TREE_TYPE (offset);
 return wi::sext (wi::to_offset (offset), TYPE_PRECISION (type));
}

static inline offset_int
memref_offset (tree memref)
{
  gcc_checking_assert (TREE_CODE (memref) == MEM_REF);
  return signed_offset (TREE_OPERAND (memref, 1));
}

static bool
types_matched_p (tree t1, tree t2)
{
  if (t1 == t2 || TYPE_MAIN_VARIANT (t1) == TYPE_MAIN_VARIANT (t2))
    return true;

  if (POINTER_TYPE_P (t1) && POINTER_TYPE_P (t2))
    {
      if (TYPE_ADDR_SPACE (TREE_TYPE (t1)) != TYPE_ADDR_SPACE (TREE_TYPE (t2)))
	return false;

      return types_matched_p (TREE_TYPE (t1), TREE_TYPE (t2));
    }

  if (TREE_CODE (t1) != TREE_CODE (t2))
    return false;

  if (RECORD_OR_UNION_TYPE_P (t1))
    return get_normalized_type (t1) == get_normalized_type (t2);

  return types_compatible_p (t1, t2);
}

static bool
types_assignable_p (tree src_type, tree dst_type)
{
  if (src_type == dst_type
      || TYPE_MAIN_VARIANT (src_type) == TYPE_MAIN_VARIANT (dst_type))
    return true;

  if (POINTER_TYPE_P (src_type) && POINTER_TYPE_P (dst_type))
    {
      dst_type = TREE_TYPE (dst_type);
      src_type = get_array_etype (TREE_TYPE (src_type), dst_type);

      if (TYPE_ADDR_SPACE (src_type) != TYPE_ADDR_SPACE (dst_type))
	return false;
    }

  if (TREE_CODE (src_type) == ARRAY_TYPE && TREE_CODE (dst_type) == ARRAY_TYPE)
    {
      tree src_domain = TYPE_DOMAIN (src_type);
      tree dst_domain = TYPE_DOMAIN (dst_type);

      if (src_domain && !dst_domain)
	return types_matched_p (TREE_TYPE (src_type), TREE_TYPE (dst_type));
    }

  return types_matched_p (src_type, dst_type);
}

static inline bool
value_assignable_p (tree src_val, tree dst_type)
{
  if (types_assignable_p (TREE_TYPE (src_val), dst_type))
    return true;

  if (integer_zerop (src_val)
      && (POINTER_TYPE_P (dst_type) || INTEGRAL_TYPE_P (dst_type)))
    return true;

  return false;
}

enum data_kind  {
  DT_OBJECT,
  DT_POINTER,
};

static inline tree
make_qualified_type (tree type, tree qual_type)
{
  return build_qualified_type (type, TYPE_QUALS (qual_type));
}

static tree
make_address_type (tree type, tree old_addr_type, data_kind kind = DT_OBJECT)
{
  int quals = TYPE_QUALS (TREE_TYPE (old_addr_type));

  gcc_assert (POINTER_TYPE_P (old_addr_type));

  if (kind == DT_POINTER)
    {
      gcc_assert (POINTER_TYPE_P (type));

      if (quals == TYPE_QUALS (TREE_TYPE (type))
	  && TREE_CODE (old_addr_type) == TREE_CODE (type))
	return type;

      type = TREE_TYPE (type);
    }

  type = build_qualified_type (type, quals);

  if (TREE_CODE (old_addr_type) == POINTER_TYPE)
    return build_pointer_type (type);

  return build_reference_type (type);
}

static tree
get_complete_type (tree type, bool fixed = true)
{
  if (!COMPLETE_TYPE_P (type))
    {
      type = get_normalized_type (type);

      if (!COMPLETE_TYPE_P (type))
	return NULL_TREE;
    }

  if (fixed && TREE_CODE (TYPE_SIZE (type)) != INTEGER_CST)
    return NULL_TREE;

  return type;
}

static tree
get_complete_record_type (tree type, data_kind kind = DT_OBJECT)
{
  tree record_type;

  if (kind == DT_OBJECT)
    record_type = type;
  else if (!POINTER_TYPE_P (type))
    return NULL_TREE;
  else
    record_type = get_array_etype (TREE_TYPE (type));

  if (!RECORD_OR_UNION_TYPE_P (record_type))
    return NULL_TREE;

  if (tree new_record_type = get_complete_type (record_type))
    {
      if (new_record_type == record_type)
	return type;

      if (kind == DT_OBJECT)
	return make_qualified_type (new_record_type, type);

      return make_address_type (new_record_type, type);
    }

  return NULL_TREE;
}

static inline bool
plain_pointee_type_p (tree type)
{
  if (VOID_TYPE_P (type))
    return true;

  if (TREE_CODE (type) == INTEGER_TYPE
      && tree_nop_conversion_p (type, char_type_node))
    return true;

  return false;
}

static inline bool
plain_pointer_type_p (tree type)
{
  if (!POINTER_TYPE_P (type))
    return false;

  return plain_pointee_type_p (TREE_TYPE (type));
}

static inline bool
polymorphic_type_p (tree type)
{
  if (RECORD_OR_UNION_TYPE_P (type))
    {
      tree binfo = TYPE_BINFO (get_normalized_type (type));

      if (binfo && polymorphic_type_binfo_p (binfo))
	return true;
    }

  return false;
}

static inline bool
polymorphic_local_type_p (tree type)
{
  if (TYPE_CXX_LOCAL (type))
    {
      gcc_assert (polymorphic_type_p (type));
      return true;
    }

  return false;
}

static void
print_decl (FILE *dump_file, tree decl)
{
  tree asm_name = DECL_ASSEMBLER_NAME_RAW (decl);

  if (asm_name)
    {
      char *dm_name = cplus_demangle_v3 (IDENTIFIER_POINTER (asm_name),
					 DMGL_PARAMS | DMGL_VERBOSE
					 | DMGL_ANSI | DMGL_TYPES
					 | DMGL_RET_POSTFIX| DMGL_GNU_V3);

      if (dm_name)
	{
	  fprintf (dump_file, "%s", dm_name);
	  free (dm_name);
	}
      else
	fprintf (dump_file, "%s", IDENTIFIER_POINTER (asm_name));
    }
  else if (DECL_NAME (decl))
    print_generic_expr (dump_file, DECL_NAME (decl), TDF_SLIM);
  else
    fprintf (dump_file, "unamed-decl %u", DECL_UID (decl));
}

static void
print_record_type (FILE *dump_file, tree type, bool details = false)
{
  tree name = TYPE_NAME (type);

  if (TREE_CODE (type) == RECORD_TYPE)
    fprintf (dump_file, "struct ");
  else
    fprintf (dump_file, "union ");

  if (!name)
    fprintf (dump_file, "unamed-type %u", TYPE_UID (type));
  else if (TREE_CODE (name) == TYPE_DECL)
    {
      if (!DECL_NAME (name) && !DECL_ASSEMBLER_NAME_RAW (name))
	fprintf (dump_file, "unamed-type %u", TYPE_UID (type));
      else
	print_decl (dump_file, name);
    }
  else
    print_generic_expr (dump_file, name, TDF_SLIM);

  if (details)
    {
      fprintf (dump_file, "  {  // size: ");
      print_generic_expr (dump_file, TYPE_SIZE (type));
      fprintf (dump_file, "\n");

      for (tree field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
	{
	  if (TREE_CODE (field) != FIELD_DECL)
	    continue;

	  tree field_type = TREE_TYPE (field);
	  poly_offset_int offset
		= wi::to_poly_offset (DECL_FIELD_OFFSET (field));

	  offset <<= LOG2_BITS_PER_UNIT;
	  offset += wi::to_poly_offset (DECL_FIELD_BIT_OFFSET (field));

	  print_generic_decl (dump_file, field, TDF_SLIM);

	  fprintf (dump_file, "  // offset: ");
	  print_generic_expr (dump_file, wide_int_to_tree (sizetype, offset));

	  fprintf (dump_file, ", size: ");

	  if (DECL_BIT_FIELD (field))
	    fprintf (dump_file, "%u", TYPE_PRECISION (field_type));
	  else
	    print_generic_expr (dump_file, TYPE_SIZE (field_type));

	  if (DECL_VIRTUAL_P (field))
	    fprintf (dump_file, ", vptr");

	  if (DECL_PADDING_P (field))
	    fprintf (dump_file, ", padding");

	  fprintf (dump_file, "\n");
	}

      fprintf (dump_file, "}\n");
    }
}

static void
gsi_insert_after_call_immediate (gcall *call_stmt, gimple *stmt)
{
  gimple_stmt_iterator gsi = gsi_for_stmt (call_stmt);

  gsi_next (&gsi);

  if (!gsi_end_p (gsi))
    gsi_insert_before (&gsi, stmt, GSI_SAME_STMT);
  else
    {
      edge e, insert_e = NULL;
      edge_iterator ei;

      FOR_EACH_EDGE (e, ei, gimple_bb (call_stmt)->succs)
	{
	  if (e->flags & (EDGE_ABNORMAL | EDGE_EH))
	    continue;

	  gcc_assert (!insert_e);
	  insert_e = e;
	}

      gcc_assert (insert_e);
      gsi_insert_on_edge_immediate (insert_e, stmt);
    }
}

class addr_base_classifier
{
  enum base_kind
  {
     BASE_NORMAL,
     BASE_SELF,
     BASE_UNKNOWN
  };

  class addr_group
  {
  public:
    int index;
    addr_group *parent;

    vec<tree> todo_source_addrs;
    vec<tree> source_addrs;
    vec<int> sources;

    vec<tree> members;

    void add_address (tree addr)
    {
      gcc_checking_assert (TREE_CODE (addr) == SSA_NAME);
      members.safe_push (addr);
    }

    void clear ()
    {
      todo_source_addrs.release ();
      source_addrs.release ();
      sources.release ();
      members.release ();
    }

    addr_group (tree addr, int index = 0)
    : index (index), parent (NULL), todo_source_addrs (vNULL)
    , source_addrs (vNULL), sources (vNULL), members (vNULL)
    {
      add_address (addr);
    }

    ~addr_group ()
    {
      clear ();
    }

    bool is_root () const { return !parent; }

    void combine (addr_group *other)
    {
      gcc_checking_assert (is_root () && other->is_root ());

      if (todo_source_addrs.is_empty ())
	std::swap (todo_source_addrs, other->todo_source_addrs);
      else
	todo_source_addrs.safe_splice (other->todo_source_addrs);

      if (source_addrs.is_empty ())
	std::swap (source_addrs, other->source_addrs);
      else
	source_addrs.safe_splice (other->source_addrs);

      if (sources.is_empty ())
	std::swap (sources, other->sources);
      else
	sources.safe_splice (other->sources);

      members.safe_splice (other->members);

      other->clear ();
      other->parent = this;
    }
  };

  auto_delete_vec<addr_group> group_graph;
  int used_group_count;

  auto_vec<vec<tree> > base_sets;
  int used_base_count;

  hash_map<tree, int> addr_to_index;

  int get_index (tree addr)
  {
    gcc_checking_assert (TREE_CODE (addr) == SSA_NAME);

    if (int *index = addr_to_index.get (addr))
      {
	gcc_checking_assert (*index != -1);
	return *index;
      }

    return -1;
  }

  int set_index (tree addr, int index)
  {
    gcc_checking_assert (TREE_CODE (addr) == SSA_NAME && index != -1);
    addr_to_index.put (addr, index);
    return index;
  }

  addr_group *get_group (int index)
  {
    gcc_checking_assert (-index - 2 < used_group_count);
    return group_graph[-index - 2];
  }

  int add_base (vec<tree> base_set)
  {
    int real_base_count = (int) base_sets.length ();

    if (used_base_count == real_base_count)
      base_sets.safe_push (base_set);
    else
      {
	base_sets[used_base_count].release ();
	base_sets[used_base_count] = base_set;
      }

    return ++used_base_count;
  }

  int add_base (tree base)
  {
    vec<tree> base_set = vNULL;

    base_set.reserve_exact (1);
    base_set.quick_push (base);

    return add_base (base_set);
  }

  vec<tree> get_base (int index)
  {
    gcc_checking_assert (index <= used_base_count);
    return base_sets[index - 1];
  }

  addr_group *create_group (tree addr)
  {
    bool existed;
    int &index = addr_to_index.get_or_insert (addr, &existed);
    int real_group_count = (int) group_graph.length ();
    addr_group *group;

    gcc_checking_assert (!existed);

    if (used_group_count == real_group_count)
      {
	group = new addr_group (addr);

	group_graph.safe_push (group);
      }
    else
      {
	group = group_graph[used_group_count];

	gcc_checking_assert (group);
	group->parent = NULL;
	group->clear ();
	group->add_address (addr);
      }

    used_group_count++;
    index = group->index = -used_group_count - 1;

    return group;
  }

  int assign_group_index (addr_group *group, int index)
  {
    unsigned i;
    tree member;

    FOR_EACH_VEC_ELT (group->members, i, member)
      set_index (member, index);

    return group->index = index;
  }

  int compute_group_base (addr_group *group)
  {
    int base_index;

    gcc_checking_assert (group->is_root ());
    gcc_checking_assert (group->todo_source_addrs.is_empty ());
    gcc_checking_assert (group->index < -1);

    if (group->sources.is_empty () && group->source_addrs.is_empty ())
      {
	base_index = 0;
      }
    else
      {
	vec<int> sources = group->sources;
	vec<tree> base_set = group->source_addrs;

	group->sources = vNULL;
	group->source_addrs = vNULL;

	for (unsigned i = 1; i < base_set.length (); i++)
	  {
	    tree base = base_set[i];

	    for (unsigned j = 0; j < i; j++)
	      {
		if (operand_equal_p (base, base_set[j]))
		  {
		    base_set.unordered_remove (i--);
		    break;
		  }
	      }
	  }

	for (unsigned i = 0; i < sources.length (); i++)
	  {
	    int index = sources[i];

	    gcc_checking_assert (!get_base (index).is_empty ());

	    for (unsigned j = 0; j < i; j++)
	      {
		if (index == sources[j])
		  {
		    sources.unordered_remove (i--);
		    break;
		  }
	      }
	  }

	if (!base_set.is_empty () || sources.length () > 1)
	  {
	    for (unsigned i = 0; i < sources.length (); i++)
	      {
		unsigned cmp_end = base_set.length ();
		vec<tree> src_base_set = get_base (sources[i]);

		for (unsigned j = 0; j < src_base_set.length (); j++)
		  {
		    tree src_base = src_base_set[j];
		    bool duplicated = false;

		    for (unsigned k = 0; k < cmp_end; k++)
		      {
			if (operand_equal_p (src_base, base_set[k]))
			  {
			    duplicated = true;
			    break;
			  }
		      }

		    if (!duplicated)
		      base_set.safe_push (src_base);
		  }
	      }
	    base_index = add_base (base_set);
	  }
	else
	  base_index = sources[0];

	sources.release ();
      }

    assign_group_index (group, base_index);

    group->members.release ();
    return base_index;
  }

  static int obtain_real_base (tree type, tree &addr);
  static int extract_source_base_addresses (tree addr, vec<tree> &src_addrs);

  int analyze_address (tree addr, int index = -1);

public:
  addr_base_classifier () : used_group_count (0), used_base_count (0) { }

  ~addr_base_classifier ()
  {
    for (unsigned i = 0; i < base_sets.length (); i++)
      base_sets[i].release ();
  }

  void initialize ()
  {
    used_base_count = 0;

    for (unsigned i = 0; i < base_sets.length (); i++)
      base_sets[i].release ();

    addr_to_index.empty ();
  }

  int get_address_base (tree addr, vec<tree> &base_set);
};

int
addr_base_classifier::obtain_real_base (tree type, tree &addr)
{
  if (TREE_CODE (addr) == ADDR_EXPR)
    {
      tree data_type = get_complete_type (TREE_TYPE (type));
      offset_int wi_size = wi::to_offset (TYPE_SIZE_UNIT (data_type));
      offset_int wi_offset = 0;
      tree real_addr = addr;
      tree memref = TREE_OPERAND (addr, 0);

      if (TREE_CODE (memref) == MEM_REF)
	{
	  tree offset = TREE_OPERAND (memref, 1);

	  if (TREE_CODE (offset) == INTEGER_CST)
	    {
	      real_addr = TREE_OPERAND (memref, 0);
	      wi_offset = signed_offset (offset);

	      gcc_assert (is_gimple_mem_ref_addr (real_addr));
	    }
	}

      if (value_assignable_p (real_addr, type))
	{
	  if (wi::multiple_of_p (wi_offset, wi_size, SIGNED))
	    {
	      addr = real_addr;
	      return BASE_NORMAL;
	    }

	  return BASE_UNKNOWN;
	}
    }
  else if (value_assignable_p (addr, type))
    return BASE_NORMAL;

  return BASE_SELF;
}

static bool
offset_is_multiple_of_p (tree offset, const offset_int &wi_size)
{
  if (TREE_CODE (offset) == INTEGER_CST)
    {
      offset_int wi_offset = signed_offset (offset);

      return wi::multiple_of_p (wi_offset, wi_size, SIGNED);
    }

  if (TREE_CODE (offset) != SSA_NAME)
    return false;

  gimple *offset_stmt = SSA_NAME_DEF_STMT (offset);

  if (gimple_assign_rhs_code_p (offset_stmt, MULT_EXPR))
    {
      tree scale = gimple_assign_rhs2 (offset_stmt);

      if (TREE_CODE (scale) == INTEGER_CST)
	{
	  offset_int wi_scale = signed_offset (scale);
	  if (wi::multiple_of_p (wi_scale, wi_size, SIGNED))
	    return true;
	}
    }
  else if (gimple_assign_rhs_code_p (offset_stmt, LSHIFT_EXPR))
    {
      tree bits = gimple_assign_rhs2 (offset_stmt);

      if (TREE_CODE (bits) == INTEGER_CST && tree_fits_uhwi_p (bits))
	{
	  unsigned HOST_WIDE_INT hwi_bits = tree_to_uhwi (bits);
	  offset_int wi_scale = offset_int (1) << hwi_bits;

	  if (wi::multiple_of_p (wi_scale, wi_size, SIGNED))
	    return true;
	}
    }
  else
    {
    }

  return false;
}

int
addr_base_classifier::extract_source_base_addresses (tree addr,
						     vec<tree> &src_addrs)
{
  tree type = TREE_TYPE (addr);
  tree data_type = get_complete_type (TREE_TYPE (type));

  if (!data_type)
    return BASE_UNKNOWN;

  if (SSA_NAME_IS_DEFAULT_DEF (addr))
    return BASE_SELF;

  offset_int wi_size = wi::to_offset (TYPE_SIZE_UNIT (data_type));
  gimple *stmt = SSA_NAME_DEF_STMT (addr);
  int kind;

  if (is_gimple_assign (stmt))
    {
      enum tree_code code = gimple_assign_rhs_code (stmt);
      tree rhs1 = gimple_assign_rhs1 (stmt);

      if (code == SSA_NAME || code == ADDR_EXPR || CONVERT_EXPR_CODE_P (code))
	{
	  if ((kind = obtain_real_base (type, rhs1)))
	    return kind;

	  src_addrs.safe_push (rhs1);
	}
      else if (code == POINTER_PLUS_EXPR)
	{
	  if ((kind = obtain_real_base (type, rhs1)))
	    return kind;

	  tree offset = gimple_assign_rhs2 (stmt);

	  if (!offset_is_multiple_of_p (offset, wi_size))
	    return BASE_UNKNOWN;

	  src_addrs.safe_push (rhs1);
	}
      else if (code == COND_EXPR || code == MAX_EXPR || code == MIN_EXPR)
	{
	  bool base_self_p = false;

	  for (unsigned i = 1; i < 3; i++)
	    {
	      tree opnd = gimple_op (stmt, gimple_num_ops (stmt) - i);

	      kind = obtain_real_base (type, opnd);

	      if (kind == BASE_UNKNOWN)
		{
		  src_addrs.release ();
		  return BASE_UNKNOWN;
		}

	      if (kind == BASE_SELF)
		base_self_p = true;
	      else if (!base_self_p)
		src_addrs.safe_push (opnd);
	    }

	  if (base_self_p)
	    {
	      src_addrs.release ();
	      return BASE_SELF;
	    }

	  if (operand_equal_p (src_addrs[0], src_addrs[1]))
	    src_addrs.pop ();
	}
      else
	return BASE_SELF;
    }
  else if (gimple_code (stmt) == GIMPLE_PHI)
    {
      gphi *phi = as_a <gphi *> (stmt);
      bool base_self_p = false;

      for (unsigned i = 0; i < gimple_phi_num_args (phi); ++i)
	{
	  tree arg = gimple_phi_arg_def (phi, i);

	  kind = obtain_real_base (type, arg);

	  if (kind == BASE_UNKNOWN)
	    {
	      src_addrs.release ();
	      return BASE_UNKNOWN;
	    }

	  if (kind == BASE_SELF)
	    base_self_p = true;
	  else if (!base_self_p)
	    {
	      for (unsigned j = 0; j < src_addrs.length (); j++)
		{
		  if (operand_equal_p (arg, src_addrs[j]))
		    {
		      arg = NULL_TREE;
		      break;
		    }
		}

	      if (arg)
		src_addrs.safe_push (arg);
	    }
	}

      if (base_self_p)
	{
	  src_addrs.release ();
	  return BASE_SELF;
	}
    }
  else if (gimple_call_builtin_p (stmt, BUILT_IN_NORMAL))
    {
      switch (DECL_FUNCTION_CODE (gimple_call_fndecl (stmt)))
	{
	case BUILT_IN_MEMPCPY:
	case BUILT_IN_MEMPCPY_CHK:
	  {
	    tree len = gimple_call_arg (stmt, 2);

	    if (!offset_is_multiple_of_p (len, wi_size))
	      return BASE_UNKNOWN;
	  }

	/* fall-through. */

	case BUILT_IN_MEMMOVE:
	case BUILT_IN_MEMMOVE_CHK:
	case BUILT_IN_MEMCPY:
	case BUILT_IN_MEMCPY_CHK:
	  {
	    tree dst = gimple_call_arg (stmt, 0);

	    if ((kind = obtain_real_base (type, dst)))
	      return kind;

	    src_addrs.safe_push (dst);
	    break;
	  }

	default:
	  return BASE_SELF;
	}
    }
  else
    return BASE_SELF;

  return BASE_NORMAL;
}

int
addr_base_classifier::analyze_address (tree addr, int index)
{
  vec<tree> src_addrs = vNULL;
  int kind = extract_source_base_addresses (addr, src_addrs);

  if (kind == BASE_SELF)
    {
      index = add_base (addr);
    }
  else if (kind)
    {
      gcc_checking_assert (kind == BASE_UNKNOWN);

      index = 0;
    }
  else if (index == -1)
    {
      addr_group *group = create_group (addr);

      group->todo_source_addrs = src_addrs;

      return group->index;
    }
  else
    {
      addr_group *group = get_group (index);

      group->members.safe_push (addr);

      if (group->todo_source_addrs.is_empty ())
	group->todo_source_addrs = src_addrs;
      else
	{
	  group->todo_source_addrs.safe_splice (src_addrs);
	  src_addrs.release ();
	}
    }

  set_index (addr, index);
  return index;
}

int
addr_base_classifier::get_address_base (tree addr, vec<tree> &base_set)
{
  int index = get_index (addr);

  if (index != -1)
    {
      if (index)
	base_set = get_base (index);
      return index;
    }

  used_group_count = 0;

  if ((index = analyze_address (addr)) >= 0)
    {
      if (index)
	base_set = get_base (index);
      return index;
    }

  auto_vec<addr_group *> stack;
  addr_group *start = get_group (index);
  addr_group *curr = start;

  stack.safe_push (start);

  while (true)
    {
      while (!curr->todo_source_addrs.is_empty ())
	{
	  tree src_addr = curr->todo_source_addrs.pop ();

	  if (TREE_CODE (src_addr) != SSA_NAME)
	    {
	      curr->source_addrs.safe_push (src_addr);
	      continue;
	    }

	  int src_index = get_index (src_addr);

	  if (src_index == -1)
	    {
	      if (curr->todo_source_addrs.is_empty ()
		  && curr->source_addrs.is_empty ()
		  && curr->sources.is_empty ())
		{
		  src_index = analyze_address (src_addr, curr->index);
		}
	      else if ((src_index = analyze_address (src_addr)) < -1)
		{
		  curr = get_group (src_index);
		  stack.safe_push (curr);
		  continue;
		}
	    }

	  if (!src_index)
	    {
	      for (; ; stack.pop (), curr = stack.last ())
		{
		  assign_group_index (curr, 0);
		  curr->clear ();

		  if (curr == start)
		    return 0;
		}
	    }
	  else if (src_index > 0)
	    {
	      curr->sources.safe_push (src_index);
	    }
	  else if (src_index != curr->index)
	    {
	      addr_group *src = get_group (src_index);

	      gcc_checking_assert (src->is_root ());

	      for (; curr != src; stack.pop (), curr = stack.last ())
		{
		  assign_group_index (curr, src_index);
		  src->combine (curr);
		}
	    }
	}

      index = compute_group_base (curr);

      if (curr == start)
	{
	  if (index)
	    base_set = get_base (index);
	  return index;
	}

      curr = (stack.pop (), stack.last ());
      curr->sources.safe_push (index);
    }
}

static bool
has_virtual_base_p (tree type)
{
  tree binfo = TYPE_BINFO (type);

  if (!binfo)
    return false;

  for (unsigned i = 0; i < BINFO_N_BASE_BINFOS (binfo); i++)
    {
      tree base_binfo = BINFO_BASE_BINFO (binfo, i);

      if (BINFO_VIRTUAL_P (base_binfo))
	return true;

      if (has_virtual_base_p (TREE_TYPE (base_binfo)))
	return true;
    }

  return false;
}

const enum plf_mask GF_TY_OK = GF_PLF_1;

class type_trans_analyzer {
  enum type_usage {
    TU_NONE     = 0,
    TU_FIXED    = 1 << 0,
    TU_UNION    = 1 << 1,
    TU_MIXUP    = 1 << 2,
    TU_IN_MIXUP = 1 << 3
  };

  enum rvalue_pflag {
    PF_NONE           = 0,
    PF_RECONCILE_ADDR = 1 << 0,
    PF_GIMPLIFY_ADDR  = 1 << 1,
    PF_ALWAYS_MATCH   = 1 << 2
  };

  class field_info {
  public:
    tree field;
    unsigned index;
    bool might_out_of_bound;
    bool check_out_of_bound;

    auto_vec<field_info *> defs;

    field_info (tree field, unsigned index)
    : field (field), index (index)
    , might_out_of_bound (false)
    , check_out_of_bound (false) { }
  };

  class type_info {
  public:
    unsigned index;
    tree type;
    bool excluded_for_field;
    int usage;

    auto_vec<tree> equiv_types;
    auto_vec<type_info *> referring_types;
    auto_vec<type_info *> mixup_rel_types;

    auto_bitmap addr_taken_fields;

    auto_delete_vec<field_info> addr_value_fields;
    hash_map<tree, field_info *> field_map;
    hash_map<tree, unsigned> field_to_index;

    type_info (tree type, unsigned index)
    : index (index), type (type), excluded_for_field (false), usage (0)
    {
      equiv_types.safe_push (type);
    }
  };

  auto_bitmap array_addr_names;

  auto_bitmap type_visited;
  hash_map<tree_type_hash, type_info *> record_type_map;
  unsigned max_record_type_index;

  addr_base_classifier base_classifier;

  type_info *get_record_type_info_1 (tree type)
  {
    type_info **tinfo_ptr = record_type_map.get (type);

    gcc_checking_assert (tinfo_ptr && *tinfo_ptr);

    return *tinfo_ptr;
  }

  type_info *get_record_type_info (tree type)
  {
    gcc_checking_assert (RECORD_OR_UNION_TYPE_P (type));

    process_type (type);

    return get_record_type_info_1 (get_normalized_type (type));
  }

  void print_record_type_usage (FILE *file, int usage)
  {
    int n = 0;

    fprintf (file, "(");
    if (usage & TU_FIXED)
      n += fprintf (file, "fixed");

    if (usage & TU_UNION)
      n += fprintf (file, "%sunion", n ? "," : "");

    if (usage & TU_MIXUP)
      n += fprintf (file, "%smixup", n ? "," : "");

    if (usage & TU_IN_MIXUP)
      n += fprintf (file, "%sin-mixup", n ? "," : "");
    fprintf (file, ")");
  }

  unsigned get_field_index (tree field)
  {
    bool existed;
    tree type = DECL_CONTEXT (field);
    type_info *tinfo = get_record_type_info (type);
    unsigned &index = tinfo->field_to_index.get_or_insert (field, &existed);

    if (!existed)
      {
	tree field1 = TYPE_FIELDS (type);
	unsigned index1;

	for (index1 = 0; field1; field1 = DECL_CHAIN (field1), index1++)
	  {
	    if (field1 == field)
	      {
		index = index1;
		return index1;
	      }
	  }

	gcc_unreachable ();
      }
    else
      return index;
  }

  field_info *get_field_info (tree field)
  {
    bool existed;
    type_info *tinfo = get_record_type_info (DECL_CONTEXT (field));
    field_info *&finfo = tinfo->field_map.get_or_insert (field, &existed);

    if (!existed)
      {
	unsigned index = get_field_index (field);
	unsigned i;
	field_info *addr_finfo;
	bool found = false;

	FOR_EACH_VEC_ELT (tinfo->addr_value_fields, i, addr_finfo)
	  {
	    if (index == addr_finfo->index)
	      {
		gcc_assert (types_matched_p (TREE_TYPE (field),
					     TREE_TYPE (addr_finfo->field)));
		found = true;
		break;
	      }
	  }

	if (!found)
	  {
	    addr_finfo = new field_info (field, index);
	    tinfo->addr_value_fields.safe_push (addr_finfo);
	  }

	finfo = addr_finfo;
      }

    return finfo;
  }

  void add_array_addr_name (tree addr)
  {
    tree type = get_underlying_type (TREE_TYPE (addr));

    if (RECORD_OR_UNION_TYPE_P (type))
      bitmap_set_bit (array_addr_names, SSA_NAME_VERSION (addr));
  }

  void add_record_type (tree);
  void process_type (tree);

  void mark_record_type (tree, int);
  void mark_possible_mixup_type (tree);
  void mark_mixup_type (tree);

  void exclude_type_as_field (tree type)
  {
    type_info *tinfo = get_record_type_info (type);

    tinfo->excluded_for_field = true;
  }

  int check_type_match (tree, tree);

  int check_type_match (tree src_type, tree dst_type, data_kind kind,
			vec<tree> *fields, bool dont_mark = false)
  {
    offset_int offset = 0;
    return check_type_match (src_type, dst_type, kind, offset, fields,
			     dont_mark);
  }

  int check_type_match (tree, tree, data_kind, offset_int &, vec<tree> *,
			bool = false);

  bool gimplify_operand (gimple *, tree &, const char * = NULL, bool = false);

  bool gimplify_addr_expr (gimple *stmt, tree &expr)
  {
    return gimplify_operand (stmt, expr, "addr_expr");
  }

  void process_init_expr (tree, tree);
  bool process_memref (tree &);
  bool process_rvalue (gimple *, tree &, tree = NULL_TREE,
		       int = PF_GIMPLIFY_ADDR);
  bool process_mem_rvalue (gimple *, tree &, tree = NULL_TREE,
			   int = PF_GIMPLIFY_ADDR);

  void process_comparison (gimple *, tree &, tree &);

  void process_memory_dealloc (gcall *);
  void process_assign_addr_expr (gassign *);
  void process_assign_pointer_plus (gassign *);
  void process_assign (gassign *);
  void process_phi (gphi *);
  bool process_call_arg (gcall *, tree, unsigned, int = PF_RECONCILE_ADDR);
  void process_call_arg_list (gcall *, tree = NULL , vec<int, va_gc> * = NULL);
  void process_call_retval (gcall *, tree);
  bool process_aggregate_operation (tree, tree, tree);
  void process_call_atexit (gcall *);
  void process_call_throw (gcall *);
  void process_call (gcall *);
  void process_asm (gasm *);
  void process_return (greturn *);
  void process_stmt (gimple *);
  void process_variable (varpool_node *);

  int get_base_as_field_load (tree, vec<tree> &);
  void check_array_addresses ();

  bool fixup_type_for_memory_alloc (gcall *);
  bool fixup_runtime_type_resolution (gcond *);
  bool fixup_type_in_thunk ();

  bool check_addr_load_from_field (tree);

  static bool free_type_info (tree const &type, type_info * const &tinfo,
			      void *)
   {
     gcc_assert (tinfo && tinfo->type == type);
     delete tinfo;
     return true;
   }

public:
  bool check_legality (tree);
  bool check_field_legality (tree);

  void process ();

  type_trans_analyzer () : max_record_type_index (0) { }

  ~type_trans_analyzer ()
  {
    record_type_map.traverse<void *, free_type_info> (NULL);
  }
};

void
type_trans_analyzer::add_record_type (tree type)
{
  type_info *tinfo = new type_info (type, ++max_record_type_index);
  bool existed = record_type_map.put (type, tinfo);
  int usage = 0;

  gcc_assert (!existed);

  if (!COMPLETE_TYPE_P (type))
    {
      tinfo->usage |= TU_MIXUP;
      return;
    }

  if (TREE_CODE (type) == UNION_TYPE || TREE_CODE (type) == QUAL_UNION_TYPE)
    usage |= TU_UNION;

  if (has_virtual_base_p (type))
    usage |= TU_MIXUP;

  for (tree field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
    {
      tree field_type = TREE_TYPE (field);
      bool is_pointer = false;

      if (TREE_CODE (field_type) == ARRAY_TYPE)
	{
	  if (flag_wild_array_field_access)
	    usage |= TU_MIXUP;

	  field_type = get_array_etype (field_type);

	  if (POINTER_TYPE_P (field_type))
	    is_pointer = true;
	}

      if (TREE_THIS_VOLATILE (field) && RECORD_OR_UNION_TYPE_P (field_type))
	mark_record_type (field_type, TU_FIXED);
      else
	{
	  field_type = get_underlying_type (field_type);
	  process_type (field_type);
	}

      if (RECORD_OR_UNION_TYPE_P (field_type))
	{
	  type_info *field_tinfo = get_record_type_info (field_type);

	  field_tinfo->referring_types.safe_push (tinfo);

	  if (is_pointer
	      && (!flag_strict_aliasing
		  || !polymorphic_local_type_p (field_type))
	      && !tinfo->mixup_rel_types.contains (field_tinfo))
	    tinfo->mixup_rel_types.safe_push (field_tinfo);
	}
    }

  mark_record_type (type, usage);
}

void
type_trans_analyzer::process_type (tree type)
{
  type = TYPE_MAIN_VARIANT (type);

  if (!bitmap_set_bit (type_visited, TYPE_UID (type)))
    return;

  if (RECORD_OR_UNION_TYPE_P (type))
    {
      tree main_type = get_normalized_type (type);

      if (main_type != type)
	{
	  if (bitmap_set_bit (type_visited, TYPE_UID (main_type)))
	    add_record_type (main_type);

	  get_record_type_info_1 (main_type)->equiv_types.safe_push (type);
	}
      else
	add_record_type (main_type);
    }
  else if (POINTER_TYPE_P (type) || TREE_CODE (type) == ARRAY_TYPE)
    process_type (TREE_TYPE (type));
  else if (FUNC_OR_METHOD_TYPE_P (type))
    {
      process_type (TREE_TYPE (type));

      for (tree param = TYPE_ARG_TYPES (type); param;
	   param = TREE_CHAIN (param))
	process_type (TREE_VALUE (param));
    }
}

void
type_trans_analyzer::mark_record_type (tree type, int usage)
{
  if (!usage)
    return;

  type_info *tinfo = get_record_type_info (type);

  if ((tinfo->usage & usage) == usage)
    return;

  int field_usage = usage & TU_FIXED;

  if (usage & (TU_UNION | TU_MIXUP | TU_IN_MIXUP))
    field_usage |= TU_IN_MIXUP;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Mark #%u ", tinfo->index);
      print_record_type (dump_file, tinfo->type);
      fprintf (dump_file, ": ");
      print_record_type_usage (dump_file, tinfo->usage);
      fprintf (dump_file, " -> ");
      print_record_type_usage (dump_file, tinfo->usage | usage);
      fprintf (dump_file, "\n");
    }

  tinfo->usage |= usage;

  for (tree field = TYPE_FIELDS (type); field; field = DECL_CHAIN (field))
    {
      tree field_type = get_array_etype (TREE_TYPE (field));

      if (RECORD_OR_UNION_TYPE_P (field_type))
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "Mark field in #%u: (", tinfo->index);
	      print_generic_expr (dump_file, TREE_TYPE (field), TDF_NONE);
	      fprintf (dump_file, ") ");
	      print_generic_expr (dump_file, field, TDF_NONE);
	      fprintf (dump_file, "\n");
	    }

	  mark_record_type (field_type, field_usage);
	}
      else if (usage & TU_UNION)
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "Mark field in #%u: (", tinfo->index);
	      print_generic_expr (dump_file, TREE_TYPE (field), TDF_NONE);
	      fprintf (dump_file, ") ");
	      print_generic_expr (dump_file, field, TDF_NONE);
	      fprintf (dump_file, "\n");
	    }

	  mark_mixup_type (field_type);
	}
    }

  if (usage & TU_MIXUP)
    {
      unsigned i;
      type_info *rel_tinfo;

      FOR_EACH_VEC_ELT (tinfo->mixup_rel_types, i, rel_tinfo)
	{
	  if (dump_file && (dump_flags & TDF_DETAILS))
	    fprintf (dump_file, "Mark mixup relevant #%u for #%u\n",
		     rel_tinfo->index, tinfo->index);

	  mark_record_type (rel_tinfo->type, TU_MIXUP);
	}
    }
}

void
type_trans_analyzer::mark_possible_mixup_type (tree type)
{
  gcc_assert (TYPE_P (type));

  type = get_array_etype (type);

  if (RECORD_OR_UNION_TYPE_P (type))
    mark_record_type (type, TU_MIXUP);
  else if (POINTER_TYPE_P (type))
    {
      type = get_underlying_type (type);

      if (!polymorphic_local_type_p (type))
	mark_possible_mixup_type (type);
    }
  else if (FUNC_OR_METHOD_TYPE_P (type))
    {
      mark_possible_mixup_type (TREE_TYPE (type));

      for (tree param = TYPE_ARG_TYPES (type); param;
	   param = TREE_CHAIN (param))
	mark_possible_mixup_type (TREE_VALUE (param));
    }
}

void
type_trans_analyzer::mark_mixup_type (tree type)
{
  gcc_assert (TYPE_P (type));

  type = get_underlying_type (type);

  if (RECORD_OR_UNION_TYPE_P (type))
    mark_record_type (type, TU_MIXUP);
  else if (FUNC_OR_METHOD_TYPE_P (type))
    {
      mark_possible_mixup_type (TREE_TYPE (type));

      for (tree param = TYPE_ARG_TYPES (type); param;
	   param = TREE_CHAIN (param))
	mark_possible_mixup_type (TREE_VALUE (param));
    }
}

static bool
offset_to_fields (tree ctype, tree type, offset_int offset,
		  vec<tree> *fields = NULL)
{
  if (offset == 0 && types_matched_p (ctype, type))
    return true;

  if (!RECORD_OR_UNION_TYPE_P (ctype))
    return false;

  for (tree field = TYPE_FIELDS (ctype); field; field = DECL_CHAIN (field))
    {
      /* C++ FE may introduces zero sized fields.  */
      if (DECL_SIZE (field) && integer_zerop (DECL_SIZE (field)))
	continue;

      offset_int field_offset = wi::to_offset (DECL_FIELD_OFFSET (field));

      field_offset += wi::to_offset (DECL_FIELD_BIT_OFFSET (field))
				     >> LOG2_BITS_PER_UNIT;

      if (offset < field_offset)
	return false;

      tree field_type = TREE_TYPE (field);
      offset_int field_size = wi::to_offset (TYPE_SIZE_UNIT (field_type));

      if (offset >= field_offset + field_size)
	continue;

      if (fields)
	fields->safe_push (field);

      offset -= field_offset;

      if (TREE_CODE (field_type) == ARRAY_TYPE)
	{
	  if (!(type = get_complete_type (type)))
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

	      if (fields)
		fields->safe_push (wide_int_to_tree (sizetype, index));

	      if (TREE_CODE (field_type) != ARRAY_TYPE)
		break;
	    }
	}

      return offset_to_fields (field_type, type, offset, fields);
    }

  return false;
}

struct typed_area
{
  offset_int start;
  offset_int end;
  tree type;
};

static bool
add_type_to_areas (vec<typed_area> &areas, tree type, const offset_int &start)
{
  offset_int end = start + wi::to_offset (TYPE_SIZE_UNIT (type));

  if (end > wi::to_offset (TYPE_MAX_VALUE (ssizetype)))
    return false;

  if (end < wi::to_offset (TYPE_MIN_VALUE (ssizetype)))
    return false;

  if (start < 0 || end <= start)
    return false;

  bool found = false;
  unsigned pos = 0;

  for (unsigned i = 0; i < areas.length (); i++)
    {
      auto &area = areas[i];

      if (area.end <= start)
	{
	  pos = i + 1;
	  continue;
	}

      if (end <= area.start)
	break;

      if (area.start == start)
	{
	  if (area.end == end)
	    {
	      if (!offset_to_fields (area.type, type, 0))
		{
		  if (!offset_to_fields (type, area.type, 0))
		    return false;
		  area.type = type;
		}
	      found = true;
	    }
	  else if (area.end < end)
	    {
	      if (!offset_to_fields (type, area.type, 0))
		return false;
	      pos = i + 1;
	    }
	  else if (area.end > end)
	    {
	      if (!offset_to_fields (area.type, type, 0))
		return false;
	    }
	}
      else if (area.start < start)
	{
	  if (end > area.end
	      || !offset_to_fields (area.type, type, start - area.start))
	    return false;
	  pos = i + 1;
	}
      else
	{
	  if (area.end > end
	      || !offset_to_fields (type, area.type, area.start - start))
	    return false;
	}
    }

  if (!found)
    {
      typed_area area = { start, end, type };

      areas.safe_insert (pos, area);
    }

  return true;
}

static bool
addr_plus_offset_p (tree expr, tree addr, offset_int &offset)
{
  if (expr == addr)
    offset = 0;
  else if (TREE_CODE (expr) == ADDR_EXPR)
    {
      HOST_WIDE_INT hwi_offset, size;
      bool reverse;
      tree memref = get_ref_base_and_extent_hwi (TREE_OPERAND (expr, 0),
						 &hwi_offset, &size, &reverse);

      if (!memref || TREE_CODE (memref) != MEM_REF
	  || TREE_OPERAND (memref, 0) != addr
	  || TREE_CODE (TREE_OPERAND (memref, 1)) != INTEGER_CST)
	return false;

      gcc_assert (!(hwi_offset % BITS_PER_UNIT));
      offset = memref_offset (memref) + (hwi_offset / BITS_PER_UNIT);
    }
  else
    return false;

  return true;
}

static bool
addr_plus_offset_p (gimple *stmt, tree addr, offset_int &offset)
{
  if (!is_gimple_assign (stmt))
    return false;

  tree lhs = gimple_assign_lhs (stmt);

  if (TREE_CODE (lhs) != SSA_NAME)
    return false;

  enum tree_code code = gimple_assign_rhs_code (stmt);
  tree rhs1 = gimple_assign_rhs1 (stmt);

  switch (code)
    {
    CASE_CONVERT:
      if (!types_compatible_p (TREE_TYPE (lhs), TREE_TYPE (rhs1)))
	return false;

      /* fall-through.  */

    case SSA_NAME:
    case ADDR_EXPR:
    case POINTER_PLUS_EXPR:
      break;

    default:
      return false;
    }

  if (!addr_plus_offset_p (rhs1, addr, offset))
    return false;

  if (code == POINTER_PLUS_EXPR)
    {
      tree rhs2 = gimple_assign_rhs2 (stmt);

      if (TREE_CODE (rhs2) != INTEGER_CST)
	{
	  return false;
	}

      offset += signed_offset (rhs2);
    }

  return true;
}

static tree
memory_alloc_size (gcall *call_stmt)
{
  if (tree decl = gimple_call_fndecl (call_stmt))
    {
      if (gimple_call_builtin_p (call_stmt, BUILT_IN_NORMAL))
	{
	  switch (DECL_FUNCTION_CODE (decl))
	    {
	    case BUILT_IN_ALLOCA:
	    case BUILT_IN_ALLOCA_WITH_ALIGN:
	    case BUILT_IN_ALLOCA_WITH_ALIGN_AND_MAX:
	    case BUILT_IN_MALLOC:
	      return gimple_call_arg (call_stmt, 0);

	    case BUILT_IN_CALLOC:
	      {
		tree arg0 = gimple_call_arg (call_stmt, 0);
		tree arg1 = gimple_call_arg (call_stmt, 1);

		if (TREE_CODE (arg0) != INTEGER_CST
		    || TREE_CODE (arg1) != INTEGER_CST)
		  return NULL_TREE;

		return  size_binop (MULT_EXPR, arg0, arg1);
	      }

	    case BUILT_IN_ALIGNED_ALLOC:
	      return gimple_call_arg (call_stmt, 1);

	    case BUILT_IN_POSIX_MEMALIGN:
	    case BUILT_IN_REALLOC:
	      return NULL_TREE;

	    default:
	      break;
	    }
	}
      else
	return gimple_call_arg (call_stmt, 0);
    }
  else if (func_attr_match_alloc_kind_p (call_stmt, ALLOC_P))
    {
      tree call_fn = gimple_call_fn (call_stmt);

      if (virtual_method_call_p (call_fn))
	return gimple_call_arg (call_stmt, 1);
      else
	return gimple_call_arg (call_stmt, 0);
    }

  gcc_unreachable ();
  return NULL_TREE;
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

static bool
call_is_memory_alloc_p (gcall *call_stmt)
{
  if (tree decl = gimple_call_fndecl (call_stmt))
    {
      if (gimple_call_builtin_p (call_stmt, BUILT_IN_NORMAL))
	{
	  switch (DECL_FUNCTION_CODE (decl))
	    {
	    case BUILT_IN_ALLOCA:
	    case BUILT_IN_ALLOCA_WITH_ALIGN:
	    case BUILT_IN_ALLOCA_WITH_ALIGN_AND_MAX:
	    case BUILT_IN_MALLOC:
	    case BUILT_IN_GOMP_ALLOC:
	    case BUILT_IN_CALLOC:
	    case BUILT_IN_ALIGNED_ALLOC:
	    case BUILT_IN_POSIX_MEMALIGN:
	    case BUILT_IN_REALLOC:
	    case BUILT_IN_STRDUP:
	    case BUILT_IN_STRNDUP:
	      return true;

	    default:
	      return false;
	    }
	}

      if (decl_is_operator_new_p (decl))
	return true;

      if (DECL_IS_MALLOC (decl)
	  && id_equal (DECL_NAME (decl), "__cxa_allocate_exception"))
	return true;

      return false;
    }

  return func_attr_match_alloc_kind_p (call_stmt, ALLOC_P);
}

static bool
call_is_memory_alloc_p (gimple *stmt)
{
  return is_gimple_call (stmt)
	 && call_is_memory_alloc_p (as_a <gcall *> (stmt));
}

static bool
call_is_memory_dealloc_p (gcall *call_stmt, bool skip_delete = false)
{
  if (tree decl = gimple_call_fndecl (call_stmt))
    {
      if (gimple_call_builtin_p (call_stmt, BUILT_IN_NORMAL))
	{
	  switch (DECL_FUNCTION_CODE (decl))
	    {
	    case BUILT_IN_FREE:
	      return true;

	    default:
	      return false;
	    }
	}

      if (!skip_delete && decl_is_operator_delete_p (decl))
	return true;

      if (id_equal (DECL_NAME (decl), "__cxa_free_exception"))
	return true;

      return false;
    }

  return func_attr_match_alloc_kind_p (call_stmt, DEALLOC_P);
}

static bool
deduce_addr_type (tree expr, tree addr, const offset_int &addr_offset,
		  vec<typed_area> &areas, tree type,
		  data_kind kind = DT_POINTER,
		  offset_int *extra_offset = NULL)
{
  offset_int offset;

  if (!addr_plus_offset_p (expr, addr, offset))
    return true;

  if (extra_offset)
    offset += *extra_offset;

  if (kind == DT_POINTER)
    {
      if (!POINTER_TYPE_P (type))
	return true;

      type = TREE_TYPE (type);
    }

  if (VOID_TYPE_P (type))
    return true;

  if (!(type = get_complete_type (type)))
    return true;

  return add_type_to_areas (areas, type, offset + addr_offset);
}

static bool
deduce_addr_type_from_call (gcall *call_stmt, tree addr,
			    const offset_int &addr_offset,
			    vec<typed_area> &areas)
{
  if (tree decl = gimple_call_fndecl (call_stmt))
    {
      if (TREE_THIS_VOLATILE (decl)
	  && id_equal (DECL_NAME (decl), "__cxa_throw"))
	{
	  if (gimple_call_num_args (call_stmt) != 3)
	    return true;

	  tree dtor = gimple_call_arg (call_stmt, 2);

	  if (TREE_CODE (dtor) != ADDR_EXPR)
	    return true;

	  dtor = TREE_OPERAND (dtor, 0);

	  if (TREE_CODE (dtor) != FUNCTION_DECL
	      || !DECL_CXX_DESTRUCTOR_P (dtor))
	    return true;

	  tree obj = gimple_call_arg (call_stmt, 0);

	  return deduce_addr_type (obj, addr, addr_offset, areas,
				   DECL_CONTEXT (dtor), DT_OBJECT);
	}

      if (decl_is_operator_delete_p (decl))
	{
	  tree obj = gimple_call_arg (call_stmt, 0);
	  offset_int offset;

	  if (addr_plus_offset_p (obj, addr, offset))
	    return true;
	}
      else if (fndecl_built_in_p (decl) || DECL_EXTERNAL (decl))
	return true;
    }

  if (call_is_memory_alloc_p (call_stmt))
    return true;

  if (call_is_memory_dealloc_p (call_stmt, true))
    return true;

  tree fntype = gimple_call_fntype (call_stmt);

  if (!prototype_p (fntype))
    return true;

  tree param = TYPE_ARG_TYPES (fntype);

  for (unsigned i = 0; i < gimple_call_num_args (call_stmt) && param; i++,
       param = TREE_CHAIN (param))
    {
      tree arg = gimple_call_arg (call_stmt, i);
      tree arg_type = TREE_VALUE (param);

      if (!deduce_addr_type (arg, addr, addr_offset, areas, arg_type))
	return false;
    }

  return true;
}

static bool
deduce_addr_type_from_memref (tree memref, tree addr,
			      const offset_int &addr_offset,
			      vec<typed_area> &areas)
{
  memref = get_base_address (memref);

  gcc_assert (memref);

  if (TREE_CODE (memref) == MEM_REF)
    {
      offset_int offset = memref_offset (memref);

      if (!deduce_addr_type (TREE_OPERAND (memref, 0), addr, addr_offset,
			     areas, TREE_TYPE (memref), DT_OBJECT, &offset))
	return false;
    }

  return true;
}

static bool
deduce_addr_type_from_stmt (gimple *stmt, tree addr,
			    const offset_int &addr_offset,
			    vec<typed_area> &areas)
{
  if (gimple_assign_single_p (stmt))
    {
      tree lhs = gimple_assign_lhs (stmt);
      tree rhs = gimple_assign_rhs1 (stmt);
      tree memref;

      if (!gimple_vuse (stmt) || gimple_clobber_p (stmt))
	return true;

      if (!gimple_vdef (stmt))
	memref = rhs;
      else if (!deduce_addr_type (rhs, addr, addr_offset, areas,
				  TREE_TYPE (lhs)))
	return false;
      else
	memref = lhs;

      if (!deduce_addr_type_from_memref (memref, addr, addr_offset, areas))
	return false;
    }
  else if (gphi *phi = dyn_cast <gphi *> (stmt))
    {
      tree type = TREE_TYPE (gimple_phi_result (phi));

      for (unsigned i = 0; i < gimple_phi_num_args (phi); ++i)
	{
	  tree arg = gimple_phi_arg_def (stmt, i);

	  if (!deduce_addr_type (arg, addr, addr_offset, areas, type))
	    return false;
	}
    }
  else if (greturn *ret = dyn_cast <greturn *> (stmt))
    {
      tree retval = gimple_return_retval (ret);
      tree fntype = TREE_TYPE (cfun->decl);

      return deduce_addr_type (retval, addr, addr_offset, areas,
			       TREE_TYPE (fntype));
    }
  else if (gcall *call = dyn_cast <gcall *> (stmt))
    {
      tree lhs = gimple_call_lhs (stmt);

      if (lhs && !is_gimple_reg_type (TREE_TYPE (lhs))
	  && !deduce_addr_type_from_memref (lhs, addr, addr_offset, areas))
	return false;

      return deduce_addr_type_from_call (call, addr, addr_offset, areas);
    }

  return true;
}

struct addr_normalizer_data {
  tree base;
  offset_int base_offset;
  hash_map <tree, offset_int> &map;
  bool changed;

  addr_normalizer_data (tree base, offset_int &base_offset,
			hash_map <tree, offset_int> &map)
  : base (base), base_offset (base_offset), map (map), changed (false) { }
};

static bool
normalize_addr_operand (tree &addr_opnd, tree &offset_opnd, tree base,
			const offset_int &base_offset,
			hash_map <tree, offset_int> &addr_map)
{
  if (TREE_CODE (addr_opnd) != SSA_NAME || addr_opnd == base)
    return false;

  if (offset_int *addr_offset_ptr = addr_map.get (addr_opnd))
    {
      offset_int offset = signed_offset (offset_opnd);

      offset += *addr_offset_ptr;
      offset -= base_offset;

      if (offset >= 0)
	{
	  addr_opnd = base;
	  offset_opnd = wide_int_to_tree (TREE_TYPE (offset_opnd), offset);
	  return true;
	}
    }

  return false;
}

static tree
normalize_addr_operands (tree *opnd_ptr, int *walk_subtrees ATTRIBUTE_UNUSED,
			 void *data)
{
  tree opnd = *opnd_ptr;

  if (TREE_CODE (opnd) == MEM_REF)
    {
      auto addr_data = (addr_normalizer_data *) data;

      if (normalize_addr_operand (TREE_OPERAND (opnd, 0),
				  TREE_OPERAND (opnd, 1),
				  addr_data->base,
				  addr_data->base_offset,
				  addr_data->map))
	addr_data->changed |= true;
    }

  return NULL_TREE;
}

class offset_type_map
{
  auto_vec<offset_int> offsets;
  auto_vec<tree> types;

public:
  offset_type_map () { }

  void put (const offset_int &offset, tree type)
  {
    for (unsigned i = 0; i < offsets.length (); i++)
      {
	if (offsets[i] == offset)
	  {
	    types[i] = type;
	    return;
	  }
      }

    offsets.safe_push (offset);
    types.safe_push (type);
  }

  tree get (const offset_int &offset)
  {
    for (unsigned i = 0; i < offsets.length (); i++)
      {
	if (offsets[i] == offset)
	  return types[i];
      }

    return NULL_TREE;
  }
};

static tree
check_ssa (tree *opnd_ptr, int *walk_subtrees ATTRIBUTE_UNUSED,
	   void *data)
{
  tree opnd = *opnd_ptr;
  tree ssa = (tree) data;

  if (opnd == ssa)
    return ssa;

  return NULL_TREE;
}

static bool
ssa_in_expr_p (tree ssa, tree expr)
{
  return walk_tree (&expr, check_ssa, ssa, NULL) != NULL_TREE;
}

bool
type_trans_analyzer::fixup_type_for_memory_alloc (gcall *call_stmt)
{
  tree base_addr = gimple_call_lhs (call_stmt);

  if (TREE_CODE (base_addr) != SSA_NAME)
    return false;

  if (!plain_pointer_type_p (TREE_TYPE (base_addr)))
    return false;

  tree alloc_size = memory_alloc_size (call_stmt);

  if (!alloc_size)
    return false;

  auto_vec<tree> worklist;
  auto_vec<typed_area> areas;
  hash_map<tree, offset_int> addr_map;
  auto_vec<tree> addrs;
  gimple *use_stmt;
  imm_use_iterator imm_iter;

  worklist.safe_push (base_addr);
  addr_map.put (base_addr, offset_int (0));
  addrs.safe_push (base_addr);

  do
    {
      tree addr = worklist.pop ();
      offset_int addr_offset = *addr_map.get (addr);

      FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, addr)
	{
	  offset_int offset;

	  if (addr_plus_offset_p (use_stmt, addr, offset))
	    {
	      tree lhs = gimple_assign_lhs (use_stmt);

	      worklist.safe_push (lhs);
	      addr_map.put (lhs, offset + addr_offset);
	      addrs.safe_push (lhs);
	    }
	  else if (!deduce_addr_type_from_stmt (use_stmt, addr, addr_offset,
						areas))
	    return false;
	}
    } while (!worklist.is_empty ());

  if (areas.is_empty ())
    return false;

  offset_type_map type_map;

  for (unsigned i = 0; i < areas.length (); i++)
    {
      auto &curr = areas[i];

      type_map.put (curr.start, curr.type);

      if (!i)
	continue;

      auto &prev = areas[i - 1];

      if (curr.start >= prev.end)
	continue;

      if (curr.start > prev.start)
	{
	  gcc_assert (curr.end <= prev.end);
	  areas.ordered_remove (i--);
	}
      else
	{
	  gcc_assert (curr.start == prev.start && curr.end > prev.end);
	  areas.ordered_remove (--i);
	}
    }

  bool has_meta_space = false;

  for (unsigned i = 1; i < areas.length (); i++)
    {
      auto &prev = areas[i - 1];
      auto &curr = areas[i];

      if (!types_matched_p (prev.type, curr.type))
	{
	  if (i > 1)
	    return false;

	  tree call_fn = gimple_call_fn (call_stmt);

	  if (!virtual_method_call_p (call_fn))
	    return false;

	  tree mm_obj = OBJ_TYPE_REF_OBJECT (call_fn);
	  bool found = false;

	  if (!types_matched_p (prev.type, TREE_TYPE (mm_obj)))
	    return false;

	  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, mm_obj)
	    {
	      if (!gimple_vdef (use_stmt)
		  || !gimple_assign_single_p (use_stmt))
		continue;

	      tree lhs = gimple_assign_lhs (use_stmt);
	      tree rhs = gimple_assign_rhs1 (use_stmt);

	      if (rhs != mm_obj)
		continue;

	      if (TREE_CODE (lhs) != MEM_REF
		  || TREE_OPERAND (lhs, 0) != base_addr)
		continue;

	      if (memref_offset (lhs) == prev.start)
		{
		  found = true;
		  break;
		}
	    }

	  if (!found)
	    return false;

	  has_meta_space = true;
	}
      else if (curr.start != prev.end)
	{
	  offset_int size = wi::to_offset (TYPE_SIZE_UNIT (curr.type));

	  gcc_assert (size > 0 && curr.start > prev.end);

	  if (((curr.start - prev.end) % size) != 0)
	    return false;
	}
    }

  if (has_meta_space)
    {
      tree real_addr = make_ssa_name (build_pointer_type (areas[1].type));
      addr_normalizer_data addr_data (real_addr, areas[1].start, addr_map);
      auto_bitmap may_unused_addrs;
      tree real_addr_expr = fold_build_pointer_plus (base_addr,
				wide_int_to_tree (sizetype, areas[1].start));
      gimple *real_addr_stmt = gimple_build_assign (real_addr, real_addr_expr);

      gsi_insert_after_call_immediate (call_stmt, real_addr_stmt);

      gimple_set_plf (real_addr_stmt, GF_TY_OK, true);
      gimple_set_visited (real_addr_stmt, true);

      for (unsigned i = 0; i < addrs.length (); i++)
	{
	  tree addr = addrs[i];

	  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, addr)
	    {
	      if (is_gimple_debug (use_stmt) || use_stmt == real_addr_stmt)
		continue;

	      bool changed = addr_data.changed = false;

	      for (unsigned j = 0; j < gimple_num_ops (use_stmt); ++j)
		{
		  walk_tree (gimple_op_ptr (use_stmt, j),
			     normalize_addr_operands, &addr_data, NULL);
		  changed |= addr_data.changed;
		}

	      if (is_gimple_assign (use_stmt)
		  && gimple_assign_rhs_code (use_stmt) == POINTER_PLUS_EXPR)
		{
		  tree &rhs1 = *gimple_assign_rhs1_ptr (use_stmt);
		  tree &rhs2 = *gimple_assign_rhs2_ptr (use_stmt);

		  if (TREE_CODE (rhs2) == INTEGER_CST
		      && normalize_addr_operand (rhs1, rhs2, real_addr,
						 areas[1].start, addr_map))
		    {
		      if (integer_zerop (rhs2))
			{
			  gimple_assign_set_rhs2 (use_stmt, NULL_TREE);
			  gimple_set_num_ops (use_stmt, 2);
			  if (useless_type_conversion_p (TREE_TYPE (addr),
							 TREE_TYPE (rhs1)))
			    gimple_assign_set_rhs_code (use_stmt, SSA_NAME);
			  else
			    gimple_assign_set_rhs_code (use_stmt, NOP_EXPR);
			}

		      changed |= true;
		    }
		}

	      if (changed)
		{
		  update_stmt (use_stmt);
		  bitmap_set_bit (may_unused_addrs, SSA_NAME_VERSION (addr));
		}
	    }
	}

      simple_dce_from_worklist (may_unused_addrs);

      if (SSA_NAME_IN_FREE_LIST (base_addr))
	return false;

      FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, base_addr)
	{
	  if (use_stmt == real_addr_stmt)
	    continue;

	  if (is_gimple_debug (use_stmt))
	    continue;

	  if (is_a <gcond *> (use_stmt))
	    continue;

	  if (gcall *call = dyn_cast <gcall *> (use_stmt))
	    {
	      if (call_is_memory_dealloc_p (call))
		continue;

	      if (gimple_call_builtin_p (call, BUILT_IN_NORMAL) && false)
		continue;
	    }
	  else if (is_gimple_assign (use_stmt) && gimple_vuse (use_stmt))
	    {
	      if (!gimple_vdef (use_stmt))
		continue;

	      if (!ssa_in_expr_p (base_addr, gimple_assign_rhs1 (use_stmt)))
		continue;
	    }

	  return false;
	}

      for (unsigned i = 1; i < addrs.length (); i++)
	{
	  tree addr = addrs[i];

	  if (SSA_NAME_IN_FREE_LIST (addr))
	    continue;

	  offset_int &addr_offset = *addr_map.get (addr);

	  if (addr_offset < areas[1].start)
	    return false;
	}
    }
  else if (areas[0].start != 0)
    return false;

  for (unsigned i = has_meta_space ? 1 : 0; i < addrs.length (); i++)
    {
      tree addr = addrs[i];

      if (SSA_NAME_IN_FREE_LIST (addr)
	  || !plain_pointer_type_p (TREE_TYPE (addr)))
	continue;

      offset_int &addr_offset = *addr_map.get (addr);
      tree type = type_map.get (addr_offset);

      if (!type)
	continue;

      gimple *addr_stmt = SSA_NAME_DEF_STMT (addr);

      if (is_gimple_assign (addr_stmt) &&
	  (gimple_assign_rhs_code (addr_stmt) == SSA_NAME
	   || CONVERT_EXPR_CODE_P (gimple_assign_rhs_code (addr_stmt))))
	{
	  tree rhs = gimple_assign_rhs1 (addr_stmt);

	  gcc_checking_assert (TREE_CODE (rhs) == SSA_NAME);

	  if (types_matched_p (TREE_TYPE (TREE_TYPE (rhs)), type))
	    {
	      FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, addr)
		{
		  use_operand_p use_p;

		  FOR_EACH_IMM_USE_ON_STMT (use_p, imm_iter)
		    SET_USE (use_p, rhs);

		  update_stmt (use_stmt);
		}

	      gimple_stmt_iterator gsi = gsi_for_stmt (addr_stmt);

	      gsi_remove (&gsi, true);
	      release_ssa_name (addr);
	      continue;
	    }
	}

      if (tree var = SSA_NAME_VAR (addr))
	SET_SSA_NAME_VAR_OR_IDENTIFIER (addr, DECL_NAME (var));

      TREE_TYPE (addr) = make_address_type (type, TREE_TYPE (addr));

      gimple_set_plf (addr_stmt, GF_TY_OK, true);
      gimple_set_visited (addr_stmt, true);
    }

  return true;
}

bool
type_trans_analyzer::gimplify_operand (gimple *stmt, tree &opnd,
				       const char *name,
				       bool include_const)
{
  if (TREE_CODE (opnd) == SSA_NAME)
    return false;

  if (TREE_CODE_CLASS (TREE_CODE (opnd)) == tcc_constant && !include_const)
    return false;

  tree old_opnd = opnd;
  tree new_opnd = opnd = make_ssa_name (TREE_TYPE (old_opnd));
  gassign *new_stmt = gimple_build_assign (new_opnd, old_opnd);

  if (name)
    SET_SSA_NAME_VAR_OR_IDENTIFIER (new_opnd, get_identifier (name));

  if (gimple_code (stmt) != GIMPLE_PHI)
    {
      gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
      gsi_insert_before (&gsi, new_stmt, GSI_SAME_STMT);
    }
  else
    {
      gphi *phi = as_a <gphi *> (stmt);
      edge insert_e = NULL;

      for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
	{
	  if (gimple_phi_arg_def (phi, i) == new_opnd)
	    {
	      insert_e = gimple_phi_arg_edge (phi, i);
	      gsi_insert_on_edge_immediate (insert_e, new_stmt);

	      SET_PHI_ARG_DEF (phi, i, new_opnd);
	      break;
	    }
	}
      gcc_checking_assert (insert_e);
    }

  process_assign_addr_expr (new_stmt);
  gimple_set_plf (new_stmt, GF_TY_OK, true);
  gimple_set_visited (new_stmt, true);
  gimple_set_modified (stmt, true);
  return true;
}

struct derived_class_data
{
  HOST_WIDE_INT token;
  tree derived_class;
  tree base_class;
};

static bool
get_derived_for_primary_base (cgraph_node *node, void *data)
{
  if (!DECL_VIRTUAL_P (node->decl))
    return 0;

  derived_class_data *dc_data = (derived_class_data *) data;
  tree type = DECL_CONTEXT (node->decl);
  tree binfo = TYPE_BINFO (type);

  if (!get_binfo_at_offset (binfo, 0, dc_data->base_class))
    return false;

  tree target = gimple_get_virt_method_for_binfo (dc_data->token, binfo);

  if (!target || fndecl_built_in_p (target, BUILT_IN_UNREACHABLE))
    return true;

  if (target != node->decl)
    return false;

  if (dc_data->derived_class)
    {
      dc_data->derived_class = NULL_TREE;
      return true;
    }

  dc_data->derived_class = type;
  return false;
}

bool
type_trans_analyzer::fixup_runtime_type_resolution (gcond *cond_stmt)
{
  if (gimple_cond_code (cond_stmt) != EQ_EXPR)
    return false;

  tree ptr_opnd = gimple_cond_lhs (cond_stmt);
  tree cst_opnd = gimple_cond_rhs (cond_stmt);

  if (TREE_CODE (cst_opnd) != ADDR_EXPR)
    {
      if (TREE_CODE (ptr_opnd) != ADDR_EXPR)
	return false;

      std::swap (ptr_opnd, cst_opnd);
    }

  if (TREE_CODE (ptr_opnd) != SSA_NAME)
    return false;

  gimple *stmt = SSA_NAME_DEF_STMT (ptr_opnd);

  if (!is_gimple_assign (stmt))
    return false;

  tree rhs = gimple_assign_rhs1 (stmt);
  tree object_ptr = NULL_TREE;
  tree real_class = NULL_TREE;

  if (virtual_method_call_p (rhs))
    {
      tree decl = TREE_OPERAND (cst_opnd, 0);

      if (TREE_CODE (decl) != FUNCTION_DECL)
	return false;

      tree base_class = obj_type_ref_class (rhs);
      HOST_WIDE_INT token = tree_to_shwi (OBJ_TYPE_REF_TOKEN (rhs));
      derived_class_data dc_data = { token, NULL_TREE, base_class };
      cgraph_node *node = cgraph_node::get_create (decl);

      node = node->ultimate_alias_target ();
      if (node->call_for_symbol_and_aliases (get_derived_for_primary_base,
					     &dc_data, true))
	return false;

      object_ptr = OBJ_TYPE_REF_OBJECT (rhs);
      real_class = dc_data.derived_class;

      if (!real_class)
	return false;
    }
  else if (TREE_CODE (rhs) == COMPONENT_REF)
    {
      tree memref = rhs;
      tree field = TREE_OPERAND (memref, 1);

      if (TREE_CODE (field) != FIELD_DECL || !DECL_VIRTUAL_P (field))
	return false;

      memref = TREE_OPERAND (memref, 0);

      while (TREE_CODE (memref) == COMPONENT_REF)
	{
	  field = TREE_OPERAND (memref, 1);
	  memref = TREE_OPERAND (memref, 0);

	  if (TYPE_FIELDS (TREE_TYPE (memref)) != field
	      || !DECL_ARTIFICIAL (field))
	    return false;
	}

      if (TREE_CODE (memref) != MEM_REF
	  || !integer_zerop (TREE_OPERAND (memref, 1)))
	return false;

      tree vtable;
      unsigned HOST_WIDE_INT offset;

      if (vtable_pointer_value_to_vtable (cst_opnd, &vtable, &offset))
	{
	  if (TREE_CODE (vtable) != VAR_DECL || !DECL_VIRTUAL_P (vtable))
	    return false;

	  tree binfo = TYPE_BINFO (DECL_CONTEXT (vtable));
	  tree vtable1;
	  unsigned HOST_WIDE_INT primary_offset;

	  if (!vtable_pointer_value_to_vtable (BINFO_VTABLE (binfo), &vtable1,
					       &primary_offset))
	    return false;

	  gcc_assert (vtable == vtable1);

	  if (offset != primary_offset)
	    return false;
	}
      else
	return false;

      varpool_node *vnode = varpool_node::get_create (vtable);

      if (vnode->has_aliases_p () || vnode->alias)
	return false;

      object_ptr = TREE_OPERAND (memref, 0);
      real_class = DECL_CONTEXT (vtable);
    }
  else
    return false;

  if (TREE_CODE (object_ptr) != SSA_NAME)
    return false;

  tree object_type = TREE_TYPE (object_ptr);

  if (RECORD_OR_UNION_TYPE_P (TREE_TYPE (object_type)))
    {
      tree binfo = TYPE_BINFO (real_class);

      if (!get_binfo_at_offset (binfo, 0, TREE_TYPE (object_type))
	  || types_matched_p (real_class, TREE_TYPE (object_type)))
	return false;
    }
  else if (!VOID_TYPE_P (TREE_TYPE (object_type)))
    return false;

  basic_block cond_bb = gimple_bb (cond_stmt);
  edge true_e = EDGE_SUCC (cond_bb, 0);

  if (true_e->flags & EDGE_FALSE_VALUE)
    true_e = EDGE_SUCC (cond_bb, 1);

  tree new_object_type = make_address_type (real_class, object_type);
  tree new_object_ptr = make_ssa_name (new_object_type);
  tree cvt_expr = build1 (NOP_EXPR, new_object_type, object_ptr);
  gimple *cvt_stmt = gimple_build_assign (new_object_ptr, cvt_expr);
  gimple *use_stmt;
  imm_use_iterator imm_iter;

  gsi_insert_on_edge_immediate (true_e, cvt_stmt);

  FOR_EACH_IMM_USE_STMT (use_stmt, imm_iter, object_ptr)
    {
      if (use_stmt == cvt_stmt)
	continue;

      if (gphi *phi = dyn_cast <gphi *> (use_stmt))
	{
	  for (unsigned i = 0; i < gimple_phi_num_args (phi); i++)
	    {
	      tree arg = gimple_phi_arg_def (phi, i);

	      if (arg != object_ptr)
		continue;

	      edge arg_e = gimple_phi_arg_edge (phi, i);

	      if (dominated_by_p (CDI_DOMINATORS, arg_e->src,
				  gimple_bb (cvt_stmt)))
		add_phi_arg (phi, new_object_ptr, arg_e,
			     gimple_phi_arg_location (phi, i));
	    }
	}
      else if (dominated_by_p (CDI_DOMINATORS, gimple_bb (use_stmt),
			       gimple_bb (cvt_stmt)))
	{
	  use_operand_p use_p;

	  FOR_EACH_IMM_USE_ON_STMT (use_p, imm_iter)
	    SET_USE (use_p, new_object_ptr);
	}
    }

  if (has_zero_uses (new_object_ptr))
    {
      gimple_stmt_iterator gsi = gsi_for_stmt (cvt_stmt);

      gsi_remove (&gsi, true);
      release_ssa_name (new_object_ptr);
      return false;
    }

  gimple_set_plf (cvt_stmt, GF_TY_OK, true);
  gimple_set_visited (cvt_stmt, true);
  return true;
}

bool
type_trans_analyzer::fixup_type_in_thunk ()
{
  tree fndecl = cfun->decl;

  if (!DECL_ARTIFICIAL (fndecl) || !DECL_VIRTUAL_P (fndecl))
    return false;

  cgraph_node *node = cgraph_node::get (fndecl);
  thunk_info *info = node ? thunk_info::get (node) : NULL;
  tree class_type = DECL_CONTEXT (fndecl);

  gcc_assert (class_type);

  if (!info)
    return false;

  return true;
}

int
type_trans_analyzer::check_type_match (tree src_type, tree dst_type)
{
  gcc_assert (TYPE_P (src_type) && TYPE_P (dst_type));

  if (types_assignable_p (src_type, dst_type))
    return -1;

  mark_mixup_type (src_type);
  mark_mixup_type (dst_type);
  return 0;
}

int
type_trans_analyzer::check_type_match (tree src_type, tree dst_type,
				       data_kind kind, offset_int &offset,
				       vec<tree> *fields,
				       bool dont_mark)
{
  gcc_checking_assert (TYPE_P (src_type) && TYPE_P (dst_type));

  if (offset == 0 && types_assignable_p (src_type, dst_type))
    return -1;

  if (kind == DT_POINTER)
    {
      if (!POINTER_TYPE_P (src_type) || !POINTER_TYPE_P (dst_type))
	goto fail;

      src_type = TREE_TYPE (src_type);
      dst_type = TREE_TYPE (dst_type);
    }

  if (tree sized_src_type = get_complete_type (src_type))
    {
      offset_int real_offset = offset;

      if (offset != 0)
	{
	  offset_int size = wi::to_offset (TYPE_SIZE_UNIT (sized_src_type));

	  if (offset >= size || offset < 0)
	    {
	      wi::overflow_type overflow;

	      real_offset = wi::mod_floor (offset, size, SIGNED, &overflow);

	      if (real_offset != 0
		  && !RECORD_OR_UNION_TYPE_P (sized_src_type))
		goto fail;
	    }
	}

      if (offset_to_fields (sized_src_type, dst_type, real_offset, fields))
	{
	  offset -= real_offset;
	  return fields->is_empty () ? -1 : 1;
	}

      fields->release ();
    }

fail:
  if (!dont_mark)
    {
      mark_mixup_type (src_type);
      mark_mixup_type (dst_type);
    }
  return 0;
}

void
type_trans_analyzer::process_init_expr (tree type, tree init)
{
  unsigned i;
  tree index, value;

  check_type_match (TREE_TYPE (init), type);

  if (TREE_CODE (init) != CONSTRUCTOR)
    return;

  FOR_EACH_CONSTRUCTOR_ELT (CONSTRUCTOR_ELTS (init), i, index, value)
    {
      if (TREE_CODE (type) == ARRAY_TYPE)
	process_init_expr (TREE_TYPE (type), value);
      else if (RECORD_OR_UNION_TYPE_P (type))
	{
	  gcc_assert (index && TREE_CODE (index) == FIELD_DECL);

	  if (!DECL_BIT_FIELD (index))
	    process_init_expr (TREE_TYPE (index), value);
	}
      else
	gcc_unreachable ();
    }
}

static tree
build_field_ref_chain (tree base, vec<tree> &fields,
		       tree qual_type = NULL_TREE)
{
  tree old_type = TREE_TYPE (base);
  tree new_type = DECL_CONTEXT (fields[0]);

  if (TYPE_MAIN_VARIANT (old_type) != new_type)
    {
      gcc_assert (new_type && types_matched_p (old_type, new_type));
      TREE_TYPE (base) = make_qualified_type (new_type, old_type);
    }

  unsigned i;
  tree field;

  FOR_EACH_VEC_ELT (fields, i, field)
    {
      if (TREE_CODE (field) == INTEGER_CST)
	base = build4 (ARRAY_REF, TREE_TYPE (TREE_TYPE (base)), base, field,
		       NULL_TREE, NULL_TREE);
      else
	base = build3 (COMPONENT_REF, TREE_TYPE (field), base, field,
		       NULL_TREE);
    }

  if (qual_type)
    TREE_TYPE (base) = make_qualified_type (TREE_TYPE (base), qual_type);

  return base;
}

bool
type_trans_analyzer::process_memref (tree &expr)
{
  tree *base_ptr = &expr;
  tree base = *base_ptr;

  gcc_assert (TREE_CODE (expr) != TARGET_MEM_REF);

  while (handled_component_p (base))
    {
      tree value = base;
      tree value_type = TREE_TYPE (value);

      process_type (value_type);
      base_ptr = &TREE_OPERAND (base, 0);
      base = *base_ptr;

      if (TREE_CODE (value) == COMPONENT_REF)
	{
	  tree field = TREE_OPERAND (value, 1);

	  check_type_match (TREE_TYPE (field), value_type);
	}
      else if (TREE_CODE (value) == BIT_FIELD_REF)
	{
	  mark_possible_mixup_type (TREE_TYPE (base));
	  mark_possible_mixup_type (value_type);
	}
      else if (TREE_CODE (value) == ARRAY_REF
	       || TREE_CODE (value) == ARRAY_RANGE_REF)
	{
	  tree array_type = TREE_TYPE (base);

	  gcc_assert (TREE_CODE (array_type) == ARRAY_TYPE);

	  if (TREE_CODE (value) == ARRAY_RANGE_REF)
	    {
	      gcc_assert (TREE_CODE (value_type) == ARRAY_TYPE);
	      value_type = TREE_TYPE (value_type);
	    }

	  if (TREE_CODE (base) == VAR_DECL && DECL_VIRTUAL_P (base))
	    return false;

	  if (check_type_match (TREE_TYPE (array_type), value_type))
	    {
	      if (flag_wild_array_field_access
		  && TREE_CODE (base) != ARRAY_REF
		  && TREE_CODE (base) != ARRAY_RANGE_REF
		  && TREE_CODE (base) != VAR_DECL
		  && TREE_CODE (base) != MEM_REF)
		mark_possible_mixup_type (value_type);
	    }
	}
      else if (TREE_CODE (value) == VIEW_CONVERT_EXPR)
	check_type_match (TREE_TYPE (base), value_type);
    }

  process_type (TREE_TYPE (base));

  if (TREE_CODE (base) == MEM_REF)
    {
      tree addr = TREE_OPERAND (base, 0);
      tree addr_type = TREE_TYPE (addr);
      tree data_type = TREE_TYPE (base);
      tree offset = TREE_OPERAND (base, 1);
      bool type_mixup_p = false;

      process_type (TREE_TYPE (addr_type));

      if (TREE_CODE (addr) == SSA_NAME)
	;
      else if (TREE_CODE (addr) == ADDR_EXPR)
	{
	  tree real_base = TREE_OPERAND (addr, 0);

	  gcc_assert (DECL_P (real_base) || CONSTANT_CLASS_P (real_base));

	  process_type (TREE_TYPE (real_base));

	  if (TREE_CODE (real_base) == VAR_DECL
	      && DECL_VIRTUAL_P (real_base))
	    return false;

	  addr_type = get_array_etype (TREE_TYPE (real_base), data_type);
	  addr_type = build_pointer_type (addr_type);
	}
      else if (TREE_CODE (addr) == INTEGER_CST)
	{
	  type_mixup_p = true;
	}
      else
	gcc_unreachable ();

      if (TREE_CODE (offset) != INTEGER_CST)
	type_mixup_p = true;
      else if (TREE_CODE (data_type) == ARRAY_TYPE)
	{
	  if (!integer_zerop (offset) || TREE_CODE (addr) != ADDR_EXPR)
	    type_mixup_p = true;
	}

      if (type_mixup_p)
	{
	  mark_possible_mixup_type (addr_type);
	  mark_possible_mixup_type (data_type);
	  return false;
	}

      offset_int wi_offset = signed_offset (offset);
      auto_vec<tree, 4> fields;

      if (!check_type_match (TREE_TYPE (addr_type), data_type, DT_OBJECT,
			     wi_offset, &fields))
	return false;

      tree mref_type = make_address_type (addr_type, TREE_TYPE (offset),
					  DT_POINTER);

      if (TREE_CODE (addr) == ADDR_EXPR)
	TREE_TYPE (addr) = addr_type;
      else if (wi_offset != 0)
	{
	  add_array_addr_name (addr);
	}

      TREE_TYPE (base) = TREE_TYPE (addr_type);
      TREE_OPERAND (base, 1) = wide_int_to_tree (mref_type, wi_offset);

      if (!fields.is_empty ())
	*base_ptr = build_field_ref_chain (base, fields, data_type);

      return true;
    }
  else
    {
      gcc_assert (is_gimple_id (base) && TREE_CODE (base) != SSA_NAME);
      return false;
    }
}

bool
type_trans_analyzer::process_rvalue(gimple *stmt, tree &expr, tree targ_type,
				    int flag)
{
  tree_code code = TREE_CODE (expr);
  tree type = TREE_TYPE (expr);
  bool always_match = (flag & PF_ALWAYS_MATCH);
  int matched = 1;

  if (TREE_CODE_CLASS (code) == tcc_constant)
    {
      process_type (type);

      if (integer_zerop (expr))
	;
      else if (targ_type && !types_assignable_p (type, targ_type))
	{
	  matched = 0;

	  if (!always_match)
	    {
	      mark_mixup_type (type);
	      mark_mixup_type (targ_type);
	    }
	}
      else if (POINTER_TYPE_P (type)
	       && TREE_CODE (TREE_TYPE (type)) != METHOD_TYPE)
	{
	  mark_mixup_type (type);
	}
    }
  else if (code == ADDR_EXPR)
    {
      tree &memref = TREE_OPERAND (expr, 0);

      process_type (type);

      if (process_memref (memref))
	TREE_TYPE (expr) = make_address_type (TREE_TYPE (memref), type);

      if (targ_type)
	{
	  auto_vec<tree, 4> fields;

	  if ((matched = check_type_match (TREE_TYPE (expr), targ_type,
					   DT_POINTER, &fields,
					   always_match)) > 0)
	    {
	      memref = build_field_ref_chain (memref, fields);
	      TREE_TYPE (expr)
			= make_address_type (TREE_TYPE (memref), type);
	    }
	}

      if (flag & PF_GIMPLIFY_ADDR)
	{
	  tree base = memref;

	  if (TREE_CODE (memref) == MEM_REF)
	    {
	      tree addr = TREE_OPERAND (memref, 0);

	      if (TREE_CODE (addr) == ADDR_EXPR)
		base = TREE_OPERAND (addr, 0);
	    }

	  if (TREE_CODE (base) != FUNCTION_DECL
	      && TREE_CODE (base) != LABEL_DECL
	      && !CONSTANT_CLASS_P (base)
	      && (!VAR_P (base) || !DECL_VIRTUAL_P (base)))
	    gimplify_addr_expr (stmt, expr);
	}
    }
  else if (code == SSA_NAME)
    {
      if (!targ_type)
	return true;

      if (flag & PF_RECONCILE_ADDR)
	{
	  auto_vec<tree, 4> fields;

	  if ((matched = check_type_match (TREE_TYPE (expr), targ_type,
					   DT_POINTER, &fields,
					   always_match)) > 0)
	    {
	      expr = build_simple_mem_ref (expr);
	      expr = build_field_ref_chain (expr, fields);
	      expr = build1 (ADDR_EXPR, targ_type, expr);

	      gimple_set_modified (stmt, true);

	      if (flag & PF_GIMPLIFY_ADDR)
		gimplify_addr_expr (stmt, expr);
	    }
	}
      else if (!(matched = types_assignable_p (type, targ_type))
	       && !always_match)
	{
	  mark_mixup_type (type);
	  mark_mixup_type (targ_type);
	}
    }
  else
    gcc_unreachable ();

  return matched || always_match;
}

bool
type_trans_analyzer::process_mem_rvalue(gimple *stmt, tree &expr,
					tree targ_type, int flag)
{
  if (TREE_CODE (expr) == SSA_NAME
      || TREE_CODE (expr) == ADDR_EXPR
      || TREE_CODE_CLASS (TREE_CODE (expr)) == tcc_constant)
    return process_rvalue (stmt, expr, targ_type, flag);

  process_memref (expr);

  if (!targ_type)
    return true;

  auto_vec<tree, 4> fields;
  bool always_match = (flag & PF_ALWAYS_MATCH);
  int matched;

  if ((matched = check_type_match (TREE_TYPE (expr), targ_type,
				   DT_POINTER, &fields, always_match)) > 0)
    {
      gimplify_operand (stmt, expr);
      process_rvalue (stmt, expr, targ_type, flag);
    }

  return matched || always_match;
}

void
type_trans_analyzer::process_memory_dealloc (gcall *call_stmt)
{
  tree call_fn = gimple_call_fn (call_stmt);
  bool vcall_p = virtual_method_call_p (call_fn);
  tree addr = gimple_call_arg (call_stmt, vcall_p ? 1 : 0);

  if (TREE_CODE (addr) != SSA_NAME || SSA_NAME_IS_DEFAULT_DEF (addr))
    return;

  gimple *addr_stmt = SSA_NAME_DEF_STMT (addr);

  if (is_gimple_assign (addr_stmt))
    {
      switch (gimple_assign_rhs_code (addr_stmt))
	{
	CASE_CONVERT:
	case SSA_NAME:
	case ADDR_EXPR:
	case POINTER_PLUS_EXPR:
	  break;

	default:
	  return;
	}
    }
  else if (gimple_code (addr_stmt) != GIMPLE_PHI)
    return;

  bool can_skip = true;
  imm_use_iterator use_iter;
  gimple *use_stmt;

  FOR_EACH_IMM_USE_STMT (use_stmt, use_iter, addr)
    {
      if (use_stmt == call_stmt)
	continue;

      if (is_gimple_debug (use_stmt))
	continue;

#if 0
      if (gimple_code (use_stmt) == GIMPLE_COND)
	continue;

      if (gimple_assign_rhs_code_p (use_stmt, COND_EXPR)
	  && ssa_in_expr_p (addr, gimple_assign_rhs1 (use_stmt))
	  && !ssa_in_expr_p (addr, gimple_assign_rhs2 (use_stmt))
	  && !ssa_in_expr_p (addr, gimple_assign_rhs3 (use_stmt)))
	continue;
#endif

      can_skip = false;
      break;
    }

  if (can_skip)
    {
      gimple_set_plf (addr_stmt, GF_TY_OK, true);
      gimple_set_visited (addr_stmt, true);
    }

  if (vcall_p && gimple_assign_rhs_code_p (addr_stmt, POINTER_PLUS_EXPR))
    {
      tree addr_rhs2 = gimple_assign_rhs2 (addr_stmt);

      if (TREE_CODE (addr_rhs2) != INTEGER_CST)
	return;

      offset_int addr_offset = signed_offset (addr_rhs2);

      if (addr_offset >= 0)
	return;

      tree mm_obj = OBJ_TYPE_REF_OBJECT (call_fn);
      gimple *mm_obj_stmt = SSA_NAME_DEF_STMT (mm_obj);

      if (!gimple_assign_rhs_code_p (mm_obj_stmt, MEM_REF))
	return;

      tree mm_obj_rhs1 = gimple_assign_rhs1 (mm_obj_stmt);
      offset_int mm_obj_offset = signed_offset (TREE_OPERAND (mm_obj_rhs1, 1));

      if ((mm_obj_offset + POINTER_SIZE_UNITS > 0)
	  || mm_obj_offset < addr_offset)
	return;

      tree orig_addr = gimple_assign_rhs1 (addr_stmt);

      if (TREE_CODE (orig_addr) != SSA_NAME
	  || orig_addr != TREE_OPERAND (mm_obj_rhs1, 0))
	return;

      tree type = TREE_TYPE (TREE_TYPE (orig_addr));
      bool type_mixup_p = false;

      if (RECORD_OR_UNION_TYPE_P (type))
	{
	  if (!(type = get_complete_record_type (type))
	      || (addr_offset + wi::to_offset (TYPE_SIZE_UNIT (type))) <= 0)
	    type_mixup_p = true;
	}
      else
	{
	  gcc_assert (TREE_CODE (type) != ARRAY_TYPE);
	}

      if (gimple_bb (mm_obj_stmt) != gimple_bb (call_stmt))
	type_mixup_p = true;

      if (type_mixup_p)
	mark_mixup_type (type);
      else
	{
	  exclude_type_as_field (obj_type_ref_class (call_fn));
	  gimple_set_plf (mm_obj_stmt, GF_TY_OK, true);
	}

      gimple_set_visited (mm_obj_stmt, true);
    }
}

void
type_trans_analyzer::process_assign_addr_expr (gassign *stmt)
{
  if (gimple_visited_p (stmt) || gimple_assign_rhs_code (stmt) != ADDR_EXPR)
    return;

  tree memref = TREE_OPERAND (gimple_assign_rhs1 (stmt), 0);
  tree base = memref;
  bool has_vce = false;

  while (handled_component_p (base))
    {
      if (TREE_CODE (base) == VIEW_CONVERT_EXPR)
	has_vce = true;

      base = TREE_OPERAND (base, 0);
    }

  if (has_vce)
    mark_mixup_type (TREE_TYPE (base));
  else if (TREE_CODE (memref) == COMPONENT_REF)
    {
      tree field = TREE_OPERAND (memref, 1);
      tree field_type = get_array_etype (TREE_TYPE (field));

      if (RECORD_OR_UNION_TYPE_P (field_type))
	{
	  type_info *tinfo = get_record_type_info (DECL_CONTEXT (field));
	  unsigned index = get_field_index (field);

	  if (bitmap_set_bit (tinfo->addr_taken_fields, index))
	    {
	      type_info *field_tinfo = get_record_type_info (field_type);

	      if (!field_tinfo->mixup_rel_types.contains (tinfo))
		{
		  field_tinfo->mixup_rel_types.safe_push (tinfo);

		  if (field_tinfo->usage & TU_MIXUP)
		    mark_record_type (tinfo->type, TU_MIXUP);
		}
	    }
	}
      else
	{
	  mark_mixup_type (DECL_CONTEXT (field));
	}
    }
  else if (TREE_CODE (memref) == ARRAY_REF
	   || TREE_CODE (memref) == ARRAY_RANGE_REF)
    {
    }
  else if (handled_component_p (memref))
    gcc_unreachable ();
}

void
type_trans_analyzer::process_assign_pointer_plus (gassign *stmt)
{
  tree &lhs = *gimple_assign_lhs_ptr (stmt);
  tree &rhs = *gimple_assign_rhs1_ptr (stmt);
  tree offset = gimple_assign_rhs2 (stmt);
  tree lhs_type = TREE_TYPE (lhs);
  tree rhs_type = TREE_TYPE (rhs);

  process_rvalue (stmt, rhs, lhs_type);

  if (TREE_CODE (offset) == SSA_NAME
      && types_assignable_p (rhs_type, lhs_type))
    {
      add_array_addr_name (lhs);
      return;
    }

  if (TREE_CODE (offset) == INTEGER_CST)
    {
      auto_vec<tree, 4> fields;
      offset_int wi_offset = signed_offset (offset);

      if (check_type_match (rhs_type, lhs_type, DT_POINTER,
			    wi_offset, &fields, true /* dont mark */))
	{
	  if (wi_offset != 0)
	    add_array_addr_name (lhs);

	  if (!fields.is_empty ())
	    {
	      gcc_assert (TREE_CODE (rhs) != ADDR_EXPR);

	      tree addr_expr = build2 (MEM_REF, TREE_TYPE (rhs_type), rhs,
				       wide_int_to_tree (rhs_type, wi_offset));

	      addr_expr = build_field_ref_chain (addr_expr, fields);
	      addr_expr = build1 (ADDR_EXPR, lhs_type, addr_expr);

	      gimple_assign_set_rhs1 (stmt, addr_expr);
	      gimple_assign_set_rhs2 (stmt, NULL_TREE);
	      gimple_assign_set_rhs_code (stmt, ADDR_EXPR);
	      gimple_set_num_ops (stmt, 2);
	      gimple_set_modified (stmt, true);
	    }

	  return;
	}
    }

  mark_mixup_type (lhs_type);
  mark_mixup_type (rhs_type);
}

static bool
get_indirect_call_targets (tree expr, vec<tree> *targets = NULL,
			   bool simple = true)
{
  tree type = TREE_TYPE (expr);

  gcc_checking_assert (POINTER_TYPE_P (type));

  if (!FUNC_OR_METHOD_TYPE_P (TREE_TYPE (type))
      && !VOID_TYPE_P (TREE_TYPE (type)))
    return false;

  auto_vec<tree> worklist;
  auto_bitmap visited;

  worklist.safe_push (expr);

  do
    {
      expr = worklist.pop ();

      if (TREE_CODE (expr) != SSA_NAME || SSA_NAME_IS_DEFAULT_DEF (expr))
	{
	  bool is_function = false;

	  if ((TREE_CODE (expr) == ADDR_EXPR
	       && TREE_CODE (TREE_OPERAND (expr, 0)) == FUNCTION_DECL)
	      || TREE_CODE (expr) == OBJ_TYPE_REF
	      || TREE_CODE (expr) == INTEGER_CST)
	    is_function = true;

	  if (simple && !is_function)
	    return false;

	  if (targets)
	    targets->safe_push (expr);
	  continue;
	}

      if (!bitmap_set_bit (visited, SSA_NAME_VERSION (expr)))
	continue;

      gimple *stmt = SSA_NAME_DEF_STMT (expr);

      if (is_gimple_assign (stmt))
	{
	  enum tree_code code = gimple_assign_rhs_code (stmt);

	  if (get_gimple_rhs_class (code) == GIMPLE_SINGLE_RHS
	      || CONVERT_EXPR_CODE_P (code))
	    worklist.safe_push (gimple_assign_rhs1 (stmt));
	  else if (code == COND_EXPR)
	    {
	      worklist.safe_push (gimple_assign_rhs2 (stmt));
	      worklist.safe_push (gimple_assign_rhs3 (stmt));
	    }
	}
      else if (gimple_code (stmt) == GIMPLE_PHI)
	{
	  for (unsigned i = 0; i < gimple_phi_num_args (stmt); i++)
	    worklist.safe_push (gimple_phi_arg_def (stmt, i));
	}
    } while (!worklist.is_empty ());

  return true;
}

void
type_trans_analyzer::process_comparison (gimple *stmt, tree &op1, tree &op2)
{
  tree type1 = TREE_TYPE (op1);
  tree type2 = TREE_TYPE (op2);

  gcc_assert (POINTER_TYPE_P (type1) == POINTER_TYPE_P (type2));

  if (!POINTER_TYPE_P (type1))
    return;

  process_rvalue (stmt, op1);
  process_rvalue (stmt, op2);

  if (value_assignable_p (op1, TREE_TYPE (op2))
      || value_assignable_p (op2, TREE_TYPE (op1)))
    return;

  if ((get_indirect_call_targets (op1) || is_gimple_min_invariant (op1))
      && (get_indirect_call_targets (op2) || is_gimple_min_invariant (op2)))
    return;

  mark_mixup_type (type1);
  mark_mixup_type (type2);
}

void
type_trans_analyzer::process_assign (gassign *stmt)
{
  tree &lhs = *gimple_assign_lhs_ptr (stmt);
  tree *rhs1_ptr = gimple_assign_rhs1_ptr (stmt);
  tree *rhs2_ptr = NULL;
  tree lhs_type = TREE_TYPE (lhs);
  tree rhs1_type = TREE_TYPE (*rhs1_ptr);
  enum tree_code code = gimple_assign_rhs_code (stmt);
  bool is_store = false;

  if (TREE_CODE (lhs) != SSA_NAME)
    {
      gcc_assert (gimple_vdef (stmt));

      if (gimple_clobber_p (stmt))
	return;

      is_store = true;
      process_memref (lhs);
    }
  else if (gimple_vuse (stmt))
    {
      gcc_assert (!gimple_vdef (stmt));

      process_type (lhs_type);
      process_memref (*rhs1_ptr);

      if (!types_assignable_p (rhs1_type, lhs_type))
	{
	  tree old_lhs = lhs;
	  tree new_lhs = make_ssa_name (rhs1_type);
	  tree copy = new_lhs;
	  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);

	  if (!useless_type_conversion_p (rhs1_type, lhs_type))
	    copy = build1 (NOP_EXPR, lhs_type, new_lhs);

	  gimple_assign_set_lhs (stmt, new_lhs);
	  gsi_insert_after (&gsi, gimple_build_assign (old_lhs, copy),
			    GSI_NEW_STMT);
	}
      return;
    }

  if (gimple_num_ops (stmt) >= 3)
    rhs2_ptr = gimple_assign_rhs2_ptr (stmt);

  switch (code)
    {
    case SSA_NAME:
    case ADDR_EXPR:
      {
	int flag = PF_RECONCILE_ADDR;

	if (is_store)
	  flag |= PF_GIMPLIFY_ADDR;

	process_rvalue (stmt, *rhs1_ptr, lhs_type, flag);

	if (code != TREE_CODE (*rhs1_ptr))
	  gimple_assign_set_rhs_code (stmt, TREE_CODE (*rhs1_ptr));
      }
      break;

    CASE_CONVERT:
      process_rvalue (stmt, *rhs1_ptr, lhs_type, PF_RECONCILE_ADDR);

      if (TREE_CODE (*rhs1_ptr) == ADDR_EXPR)
	{
	  if (useless_type_conversion_p (TREE_TYPE (*rhs1_ptr), lhs_type))
	    gimple_assign_set_rhs_code (stmt, ADDR_EXPR);
	  else
	    gimplify_addr_expr (stmt, *rhs1_ptr);
	}
      break;

    case ADDR_SPACE_CONVERT_EXPR:
      process_rvalue (stmt, *rhs1_ptr, lhs_type);
      break;

    case BIT_FIELD_REF:
      {
	tree &base = TREE_OPERAND (*rhs1_ptr, 0);

	gcc_assert (!handled_component_p (base));

	process_rvalue (stmt, base, void_type_node);
	mark_possible_mixup_type (lhs_type);
	mark_possible_mixup_type (rhs1_type);
	break;
      }

    case VIEW_CONVERT_EXPR:
      for (tree value = *rhs1_ptr; ; )
	{
	  tree &base = TREE_OPERAND (value, 0);

	  if (TREE_CODE (base) != VIEW_CONVERT_EXPR)
	    {
	      gcc_assert (!handled_component_p (base));

	      process_rvalue (stmt, base, lhs_type,
			      PF_RECONCILE_ADDR | PF_GIMPLIFY_ADDR);

	      if (value_assignable_p (base, lhs_type))
		{
		  gimple_assign_set_rhs1 (stmt, unshare_expr (base));
		  gimple_assign_set_rhs_code (stmt, TREE_CODE (base));
		  gimple_set_modified (stmt, true);
		}
	      break;
	    }
	  value = base;
	}
      break;

    case CONSTRUCTOR:
      process_init_expr (lhs_type, *rhs1_ptr);
      break;

    case OBJ_TYPE_REF:
      gcc_assert (POINTER_TYPE_P (lhs_type));
      gcc_assert (POINTER_TYPE_P (rhs1_type));
      break;

    case WITH_SIZE_EXPR:
      process_rvalue (stmt, *rhs1_ptr);
      break;

    case POINTER_PLUS_EXPR:
      process_assign_pointer_plus (stmt);
      break;

    case POINTER_DIFF_EXPR:
      process_comparison (stmt, *rhs1_ptr, *rhs2_ptr);
      break;

    case MAX_EXPR:
    case MIN_EXPR:
      if (POINTER_TYPE_P (lhs_type))
	{
	  process_rvalue (stmt, *rhs1_ptr, lhs_type);
	  process_rvalue (stmt, *rhs2_ptr, lhs_type);
	}
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
      if (POINTER_TYPE_P (lhs_type))
	{
	  mark_possible_mixup_type (lhs_type);
	  process_rvalue (stmt, *rhs1_ptr, void_type_node);
	  process_rvalue (stmt, *rhs2_ptr, void_type_node);
	}
      break;

    case COND_EXPR:
      if (COMPARISON_CLASS_P (*rhs1_ptr))
	process_comparison (stmt, TREE_OPERAND (*rhs1_ptr, 0),
				  TREE_OPERAND (*rhs1_ptr, 1));

      if (POINTER_TYPE_P (lhs_type))
	{
	  tree *rhs3_ptr = gimple_assign_rhs3_ptr (stmt);

	  process_rvalue (stmt, *rhs2_ptr, lhs_type);
	  process_rvalue (stmt, *rhs3_ptr, lhs_type);
	}
      break;

    default:
      if (TREE_CODE_CLASS (code) == tcc_comparison)
	process_comparison (stmt, *rhs1_ptr, *rhs2_ptr);
      else if (TREE_CODE_CLASS (code) == tcc_constant)
	process_rvalue (stmt, *rhs1_ptr, lhs_type);
      else
	{
	  gcc_assert (!POINTER_TYPE_P (lhs_type));
	  gcc_assert (!POINTER_TYPE_P (rhs1_type));
	}
    }

  process_assign_addr_expr (stmt);
}

void
type_trans_analyzer::process_phi (gphi *stmt)
{
  tree result = gimple_phi_result (stmt);
  tree type = TREE_TYPE (result);

  process_type (type);

  for (unsigned i = 0; i < gimple_phi_num_args (stmt); i++)
    {
      tree &arg = *gimple_phi_arg_def_ptr (stmt, i);

      process_rvalue (stmt, arg, type, PF_RECONCILE_ADDR | PF_GIMPLIFY_ADDR);
    }
}

bool
type_trans_analyzer::process_call_arg (gcall *stmt, tree param_type,
				       unsigned arg_index, int flag)
{
  tree &arg = *gimple_call_arg_ptr (stmt, arg_index);

  if (param_type)
    process_type (param_type);

  if (flag & PF_ALWAYS_MATCH)
    {
      tree arg_type = TREE_TYPE (arg);

      gcc_assert (param_type && POINTER_TYPE_P (param_type));
      gcc_assert (POINTER_TYPE_P (arg_type)
		  || TREE_CODE (arg_type) == ARRAY_TYPE);
    }

  return process_mem_rvalue (stmt, arg, param_type, flag | PF_GIMPLIFY_ADDR);
}

void
type_trans_analyzer::process_call_arg_list (gcall *stmt,
					    tree fntype,
					    vec<int, va_gc> *skip_match_args)
{
  if (!fntype || VOID_TYPE_P (fntype))
    {
      for (unsigned i = 0; i < gimple_call_num_args (stmt); ++i)
	process_call_arg (stmt, fntype, i);
      return;
    }

  tree param = TYPE_ARG_TYPES (fntype);

  for (unsigned i = 0; i < gimple_call_num_args (stmt); ++i)
    {
      tree param_type = void_type_node;
      int flag = PF_RECONCILE_ADDR;

      if (param)
	{
	  param_type = TREE_VALUE (param);
	  param = TREE_CHAIN (param);
	  gcc_checking_assert (param_type);

	  if (skip_match_args && skip_match_args->contains((int) i))
	    flag |= PF_ALWAYS_MATCH;
	}

      process_call_arg (stmt, param_type, i, flag);
    }
}

void
type_trans_analyzer::process_call_retval (gcall *stmt, tree type)
{
  tree &lhs = *gimple_call_lhs_ptr (stmt);

  if (!lhs)
    return;

  tree lhs_type = TREE_TYPE (lhs);

  if (!type)
    {
      gcc_assert (POINTER_TYPE_P (lhs_type));
      return;
    }

  auto_vec<tree, 4> fields;

  process_type (type);

  if (check_type_match (type, lhs_type, DT_POINTER, &fields) < 1)
    return;

  if (TREE_CODE (lhs) != SSA_NAME)
    {
      mark_possible_mixup_type (type);
      return;
    }

  tree old_lhs = lhs;
  tree cvt_lhs = make_ssa_name (type);
  tree cvt_expr = build_simple_mem_ref (cvt_lhs);

  cvt_expr = build_field_ref_chain (cvt_expr, fields);
  cvt_expr = build1 (ADDR_EXPR, lhs_type, cvt_expr);

  gimple_call_set_lhs (stmt, cvt_lhs);
  gsi_insert_after_call_immediate (stmt,
				   gimple_build_assign (old_lhs, cvt_expr));
}

bool
type_trans_analyzer::process_aggregate_operation (tree object1, tree object2,
						  tree size)
{
  tree type1 = TREE_TYPE (object1);
  tree type2 = TREE_TYPE (object2);

  gcc_assert (POINTER_TYPE_P (type1) && POINTER_TYPE_P (type2));

  type1 = get_array_etype (type1);
  type2 = get_array_etype (type2);

  if (!types_matched_p (type1, type2))
    {
      mark_possible_mixup_type (type1);
      mark_possible_mixup_type (type2);
      return false;
    }

  if (!(type1 = get_complete_type (type1)))
    return false;

  if (TREE_CODE (size) != INTEGER_CST
      || wi::to_offset (size) > wi::to_offset (TYPE_SIZE_UNIT (type1)))
    {
      if (TREE_CODE (object1) == SSA_NAME)
	add_array_addr_name (object1);

      if (TREE_CODE (object2) == SSA_NAME)
	add_array_addr_name (object2);
    }

  return true;
}

static inline enum availability
real_fndecl (tree &fndecl)
{
  cgraph_node *node = cgraph_node::get_create (fndecl);
  enum availability avail;

  if (node->alias)
    fndecl = node->ultimate_alias_target (&avail)->decl;
  else
    avail = node->get_availability ();

  return avail;
}

static inline tree
get_callback_fndecl (tree addr)
{
  if (TREE_CODE (addr) == ADDR_EXPR
      && TREE_CODE (TREE_OPERAND (addr, 0)) == FUNCTION_DECL)
    return TREE_OPERAND (addr, 0);

  return NULL_TREE;
}

static inline
bool function_has_body_p (tree fndecl)
{
  cgraph_node *node = cgraph_node::get (fndecl);

  if (!node)
    return false;

  if (node->definition || node->in_other_partition)
    return true;

  return false;
}

void
type_trans_analyzer::process_call_atexit (gcall *stmt)
{
  tree cb_fndecl = get_callback_fndecl (gimple_call_arg (stmt, 0));
  tree cb_param_type = void_type_node;

  if (real_fndecl (cb_fndecl) >= AVAIL_AVAILABLE)
    {
      tree cb_param = TYPE_ARG_TYPES (TREE_TYPE (cb_fndecl));

      if (!VOID_TYPE_P (TREE_VALUE (cb_param))
	  && VOID_TYPE_P (TREE_VALUE (TREE_CHAIN (cb_param))))
	cb_param_type = TREE_VALUE (cb_param);
    }

  if (process_call_arg (stmt, cb_param_type, 1))
    {
      process_call_arg (stmt, ptr_type_node, 0, PF_ALWAYS_MATCH);
      process_call_arg (stmt, ptr_type_node, 2, PF_ALWAYS_MATCH);
    }
  else
    {
      process_call_arg (stmt, void_type_node, 0);
      process_call_arg (stmt, void_type_node, 2);
    }
}

void
type_trans_analyzer::process_call_throw (gcall *stmt)
{
  tree throw_dtor = gimple_call_arg (stmt, 2);
  tree throw_type = void_type_node;

  if (integer_zerop (throw_dtor))
    throw_type = TREE_TYPE (gimple_call_arg (stmt, 0));
  else
    {
      tree fndecl = get_callback_fndecl (throw_dtor);

      if (fndecl && DECL_CXX_DESTRUCTOR_P (fndecl)
	  && real_fndecl (fndecl) >= AVAIL_AVAILABLE)
	throw_type = TREE_VALUE (TYPE_ARG_TYPES (TREE_TYPE (fndecl)));
    }

  if (process_call_arg (stmt, throw_type, 0, PF_NONE))
    process_call_arg (stmt, ptr_type_node, 2, PF_ALWAYS_MATCH);
  else
    process_call_arg (stmt, void_type_node, 2);

  process_call_arg (stmt, void_type_node, 1);
}

void
type_trans_analyzer::process_call (gcall *stmt)
{
  tree &lhs = *gimple_call_lhs_ptr (stmt);

  if (lhs)
    {
      if (TREE_CODE (lhs) == SSA_NAME)
	process_type (TREE_TYPE (lhs));
      else
	process_memref (lhs);
    }

  if (gimple_call_internal_p (stmt))
    {
      process_call_arg_list (stmt);
      return;
    }

  tree &fn = *gimple_call_fn_ptr (stmt);

  gcc_assert (fn);

  if (TREE_CODE (fn) != OBJ_TYPE_REF)
    process_rvalue (stmt, fn);
  else
    {
      process_rvalue (stmt, OBJ_TYPE_REF_EXPR (fn));
      process_rvalue (stmt, OBJ_TYPE_REF_OBJECT (fn));
    }

  tree fndecl = gimple_call_fndecl (stmt);
  tree fntype = gimple_call_fntype (stmt);
  tree &static_chain = *gimple_call_chain_ptr (stmt);
  enum availability avail = AVAIL_NOT_AVAILABLE;
  bool vcall_p = false;

  if (fndecl)
    avail = real_fndecl (fndecl);

  if (static_chain)
    {
      tree type = void_type_node;

      if (avail >= AVAIL_AVAILABLE)
	{
	  struct function *func = DECL_STRUCT_FUNCTION (fndecl);

	  if (!func)
	    gcc_assert (cgraph_node::get (fndecl)->in_other_partition);
	  else if (func->static_chain_decl)
	    type = TREE_TYPE (func->static_chain_decl);
	  else
	    type = NULL_TREE;
	}

      process_rvalue (stmt, static_chain, type);
    }

  vec<int, va_gc> *skip_match_args = NULL;
  tree ret_type = TREE_TYPE (fntype);

  if (fndecl)
    {
      fntype = TREE_TYPE (fndecl);
      ret_type = TREE_TYPE (fntype);

      if (gimple_call_builtin_p (stmt, BUILT_IN_NORMAL))
	{
	  switch (DECL_FUNCTION_CODE (fndecl))
	    {
	    case BUILT_IN_MEMPCPY:
	    case BUILT_IN_MEMPCPY_CHK:
	      if (lhs)
		add_array_addr_name (lhs);

	    /* fall-through.  */

	    case BUILT_IN_MEMMOVE:
	    case BUILT_IN_MEMMOVE_CHK:
	    case BUILT_IN_MEMCPY:
	    case BUILT_IN_MEMCPY_CHK:
	      ret_type = TREE_TYPE (gimple_call_arg (stmt, 0));

	    /* fall-through.  */

	    case BUILT_IN_BCMP:
	    case BUILT_IN_BCOPY:
	    case BUILT_IN_MEMCMP:
	    case BUILT_IN_MEMCMP_EQ:
	      vec_safe_push (skip_match_args, 0);
	      vec_safe_push (skip_match_args, 1);
	      process_aggregate_operation (gimple_call_arg (stmt, 0),
					   gimple_call_arg (stmt, 1),
					   gimple_call_arg (stmt, 2));
	      break;

	    case BUILT_IN_MEMSET:
	    case BUILT_IN_MEMSET_CHK:
	    case BUILT_IN_ASSUME_ALIGNED:
	      ret_type = TREE_TYPE (gimple_call_arg (stmt, 0));

	    /* fall-through.  */

	    case BUILT_IN_BZERO:
	    case BUILT_IN_PREFETCH:
	    case BUILT_IN_OBJECT_SIZE:
	    case BUILT_IN_UNWIND_RESUME:
	    case BUILT_IN_CLEAR_CACHE:
	      vec_safe_push (skip_match_args, 0);
	      break;

	    case BUILT_IN_EH_POINTER:
	    case BUILT_IN_EH_FILTER:
	      ret_type = NULL_TREE;
	      break;

	    case BUILT_IN_REALLOC:
	      vec_safe_push (skip_match_args, 0);

	      if (lhs)
		{
		  tree addr_arg = gimple_call_arg (stmt, 0);
		  tree size_arg = gimple_call_arg (stmt, 1);

		  if (!integer_zerop (addr_arg) && !integer_zerop (size_arg))
		    ret_type = TREE_TYPE (addr_arg);
		  else
		    ret_type = NULL_TREE;
		}
	      break;

	    default:
	      break;
	    }
	}
      else if (avail < AVAIL_AVAILABLE)
	{
	  if ((id_equal (DECL_NAME (fndecl), "__cxa_atexit")
	       || id_equal (DECL_NAME (fndecl), "__cxa_thread_atexit"))
	      && gimple_call_num_args (stmt) == 3)
	    {
	      process_call_atexit (stmt);
	      process_call_retval (stmt, ret_type);
	      return;
	    }

	  if (TREE_THIS_VOLATILE (fndecl)  /* noreturn function */
	      && id_equal (DECL_NAME (fndecl), "__cxa_throw")
	      && gimple_call_num_args (stmt) == 3 && !lhs)
	    {
	      process_call_throw (stmt);
	      return;
	    }

	  if (((DECL_PURE_P (fndecl)
		&& id_equal (DECL_NAME (fndecl), "__cxa_get_exception_ptr"))
	       || id_equal (DECL_NAME (fndecl), "__cxa_begin_catch"))
	      && gimple_call_num_args (stmt) == 1)
	    {
	      vec_safe_push (skip_match_args, 0);
	      ret_type = NULL_TREE;
	    }
	  else if (id_equal (DECL_NAME (fndecl), "__cxa_call_unexpected")
		   && gimple_call_num_args (stmt) == 1 && !lhs)
	    {
	      vec_safe_push (skip_match_args, 0);
	    }
	  else if (id_equal (DECL_NAME (fndecl), "__dynamic_cast")
		   && gimple_call_num_args (stmt) == 4)
	    {
	      vec_safe_push (skip_match_args, 0);
	      vec_safe_push (skip_match_args, 1);
	      vec_safe_push (skip_match_args, 2);
	      ret_type = NULL_TREE;
	    }
	}
      else if (TREE_CODE (fndecl) != FUNCTION_DECL)
	{
	  mark_mixup_type (fntype);

	  ret_type = fntype = void_type_node;
	}
    }
  else if (TREE_CODE (fn) != OBJ_TYPE_REF)
    {
      auto_vec<tree> targets;

      if (get_indirect_call_targets (fn, &targets))
	{
	  unsigned i;
	  tree target;

	  FOR_EACH_VEC_ELT (targets, i, target)
	    {
	      if (integer_zerop (target))
		continue;

	      gcc_checking_assert (TREE_CODE (target) == ADDR_EXPR);

	      tree target_fndecl = TREE_OPERAND (target, 0);

	      if (real_fndecl (target_fndecl) < AVAIL_AVAILABLE
		  || !types_assignable_p (TREE_TYPE (target_fndecl), fntype))
		{
		  mark_mixup_type (fntype);
		  fntype = void_type_node;
		  break;
		}
	    }
	}
      else
	{
	  mark_mixup_type (fntype);
	  ret_type = fntype = void_type_node;
	}
    }
  else if (virtual_method_call_p (fn))
    {
      vcall_p = true;
      vec_safe_push (skip_match_args, 0);
    }

  if (call_is_memory_alloc_p (stmt)
      && !gimple_call_builtin_p (stmt, BUILT_IN_REALLOC))
    ret_type = NULL_TREE;
  else if (call_is_memory_dealloc_p (stmt))
    vec_safe_push (skip_match_args, vcall_p ? 1 : 0);

  process_call_arg_list (stmt, fntype, skip_match_args);
  process_call_retval (stmt, ret_type);
  vec_free (skip_match_args);
}

void
type_trans_analyzer::process_asm (gasm *stmt)
{
  for (unsigned i = 0; i < gimple_asm_noutputs (stmt); ++i)
    {
      tree &asm_op = TREE_VALUE (gimple_asm_output_op (stmt, i));

      gcc_assert (is_gimple_lvalue (asm_op));

      if (TREE_CODE (asm_op) != SSA_NAME)
	process_memref (asm_op);

      mark_mixup_type (TREE_TYPE (asm_op));
    }

  for (unsigned i = 0; i < gimple_asm_ninputs (stmt); ++i)
    {
      tree &asm_op = TREE_VALUE (gimple_asm_input_op (stmt, i));

      if (is_gimple_lvalue (asm_op) && TREE_CODE (asm_op) != SSA_NAME)
	process_memref (asm_op);
      else
	process_rvalue (stmt, asm_op);

      mark_mixup_type (TREE_TYPE (asm_op));
    }
}

void
type_trans_analyzer::process_return (greturn *stmt)
{
  tree &retval = *gimple_return_retval_ptr (stmt);
  tree type = TREE_TYPE (TREE_TYPE (cfun->decl));

  gcc_assert (TREE_CODE (type) != ARRAY_TYPE);

  if (!retval)
    {
      if (!VOID_TYPE_P (type))
	mark_possible_mixup_type (type);
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

  process_mem_rvalue (stmt, retval, type);
}

void
type_trans_analyzer::process_stmt (gimple *stmt)
{
  if (gimple_visited_p (stmt))
    return;

  switch (gimple_code (stmt))
    {
    case GIMPLE_ASSIGN:
      process_assign (as_a <gassign *> (stmt));
      break;

    case GIMPLE_PHI:
      process_phi (as_a <gphi *> (stmt));
      break;

    case GIMPLE_COND:
      {
	gcond *cond = as_a <gcond *> (stmt);
	tree &cond_lhs = *gimple_cond_lhs_ptr (cond);
	tree &cond_rhs = *gimple_cond_rhs_ptr (cond);

	fixup_runtime_type_resolution (cond);
	process_comparison (cond, cond_lhs, cond_rhs);
      }
      break;

    case GIMPLE_CALL:
      process_call (as_a <gcall *> (stmt));
      break;

    case GIMPLE_ASM:
      process_asm (as_a <gasm *> (stmt));
      break;

    case GIMPLE_GOTO:
      {
	tree dest = gimple_goto_dest (stmt);

	if (TREE_CODE (dest) != LABEL_DECL)
	  {
	    process_rvalue (stmt, dest);

	    mark_possible_mixup_type (TREE_TYPE (dest));
	  }
      }
      break;

    case GIMPLE_RETURN:
      process_return (as_a <greturn *> (stmt));
      break;

    default:
      gcc_assert (!gimple_has_substatements (stmt));
    }

  update_stmt_if_modified (stmt);
  gimple_set_visited (stmt, true);
}

void
type_trans_analyzer::process_variable (varpool_node *vnode)
{
  tree decl = vnode->decl;
  tree type = TREE_TYPE (decl);

  process_type (type);

  if (vnode->externally_visible_p ())
    mark_mixup_type (type);

  tree init = ctor_for_folding (decl);

  if (!init)
    init = error_mark_node;

  if (init != error_mark_node || TREE_THIS_VOLATILE (decl))
    {
      tree elem_type = get_array_etype (type);

      if (RECORD_OR_UNION_TYPE_P (elem_type))
	mark_record_type (elem_type, TU_FIXED);
    }

  if (init == error_mark_node)
    return;

  if (DECL_ARTIFICIAL (decl))
    {
      ipa_ref *ref;

      if (DECL_VIRTUAL_P (decl))
	return;

      for (unsigned i = 0; vnode->iterate_reference (i, ref); i++)
	{
	  tree referred = ref->referred->decl;

	  gcc_assert (referred);

	  if (DECL_VIRTUAL_P (referred)
	      && (ref->use == IPA_REF_ADDR || ref->use == IPA_REF_ALIAS))
	    return;
	}
    }

  process_init_expr (type, init);
}

int
type_trans_analyzer::get_base_as_field_load (tree addr, vec<tree> &fields)
{
  vec<tree> base_set;
  int index = base_classifier.get_address_base (addr, base_set);
  unsigned i;
  tree base;

  if (!index)
    return 0;

  gcc_checking_assert (!base_set.is_empty ());

  FOR_EACH_VEC_ELT (base_set, i, base)
    {
      if (TREE_CODE (base) == SSA_NAME)
	{
	  if (SSA_NAME_IS_DEFAULT_DEF (base))
	    {
	      return -1;
	    }

	  gimple *base_stmt = SSA_NAME_DEF_STMT (base);

	  if (call_is_memory_alloc_p (base_stmt))
	    continue;

	  if (!gimple_assign_single_p (base_stmt))
	    {
	      return -1;
	    }

	  if (gimple_assign_rhs_code (base_stmt) == POINTER_PLUS_EXPR)
	    {
	      tree rhs1 = gimple_assign_rhs1 (base_stmt);
	      tree rhs2 = gimple_assign_rhs2 (base_stmt);

	      if (TREE_CODE (rhs1) == SSA_NAME
		  && TREE_CODE (rhs2) == INTEGER_CST
		  && call_is_memory_alloc_p (SSA_NAME_DEF_STMT (rhs1)))
		continue;

	      return -1;
	    }

	  base = gimple_assign_rhs1 (base_stmt);
	}

      if (TREE_CODE (base) == INTEGER_CST)
	continue;

      if (TREE_CODE (base) == ADDR_EXPR)
	{
	  tree memref = TREE_OPERAND (base, 0);

	  if (!flag_wild_array_field_access
	      && TREE_CODE (memref) == COMPONENT_REF)
	    {
	      tree field_type = TREE_TYPE (TREE_OPERAND (memref, 1));

	      if (TREE_CODE (field_type) == ARRAY_TYPE
		  && TYPE_DOMAIN (field_type))
		continue;
	    }
	  else if (TREE_CODE (memref) == VAR_DECL)
	    continue;

	  return -1;
	}

      if (TREE_CODE (base) != COMPONENT_REF)
	return -1;

      fields.safe_push (TREE_OPERAND (base, 1));
    }

  return 1;
}

bool
type_trans_analyzer::check_addr_load_from_field (tree field)
{
  auto_vec<field_info *> worklist;

  worklist.safe_push (get_field_info (field));

  do
    {
      field_info *finfo = worklist.pop ();

      if (finfo->might_out_of_bound)
	{
	  finfo->check_out_of_bound = true;
	  mark_possible_mixup_type (TREE_TYPE (field));
	  return false;
	}

      if (!finfo->check_out_of_bound)
	{
	  finfo->check_out_of_bound = true;
	  worklist.safe_splice (finfo->defs);
	}

    } while (!worklist.is_empty ());

  return true;
}

void
type_trans_analyzer::check_array_addresses ()
{
  unsigned i, j;
  bitmap_iterator bi;
  tree field;

  base_classifier.initialize ();

  EXECUTE_IF_SET_IN_BITMAP (array_addr_names, 0, i, bi)
    {
      tree name = ssa_name (i);
      auto_vec<tree> fields;

      if (get_base_as_field_load (name, fields) < 1)
	{
	  mark_possible_mixup_type (TREE_TYPE (name));
	  continue;
	}

      FOR_EACH_VEC_ELT (fields, j, field)
	check_addr_load_from_field (field);
    }

  basic_block bb;

  FOR_EACH_BB_FN (bb, cfun)
    {
      gimple_stmt_iterator gsi;

      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	{
	  gimple *stmt = gsi_stmt (gsi);

	  if (!gimple_store_p (stmt) || gimple_clobber_p (stmt))
	    continue;

	  if (call_is_memory_alloc_p (stmt))
	    continue;

	  tree lhs = gimple_get_lhs (stmt);
	  tree type = TREE_TYPE (lhs);

	  if (!POINTER_TYPE_P (type)
	      || !RECORD_OR_UNION_TYPE_P (get_underlying_type (type)))
	    continue;

	  if (TREE_CODE (lhs) != COMPONENT_REF)
	    continue;

	  tree rhs = gimple_assign_rhs1 (stmt);

	  if (TREE_CODE (rhs) == INTEGER_CST)
	    continue;

	  field_info *finfo = get_field_info (TREE_OPERAND (lhs, 1));
	  auto_vec<tree> fields;
	  int res = 0;

	  if (TREE_CODE (rhs) == SSA_NAME)
	    res = get_base_as_field_load (rhs, fields);

	  if (!res)
	    mark_possible_mixup_type (type);
	  else if (res < 0)
	    {
	      finfo->might_out_of_bound = true;

	      if (finfo->check_out_of_bound)
		mark_possible_mixup_type (type);
	    }
	  else
	    {
	      FOR_EACH_VEC_ELT (fields, j, field)
		{
		  if (finfo->check_out_of_bound
		      && !check_addr_load_from_field (field))
		    break;

		  field_info *base_finfo = get_field_info (field);

		  if (finfo != base_finfo
		      && !finfo->defs.contains (base_finfo))
		    finfo->defs.safe_push (base_finfo);
		}
	    }
	}
    }
}

void
type_trans_analyzer::process ()
{
  varpool_node *vnode;
  cgraph_node *node;

  FOR_EACH_VARIABLE (vnode)
    process_variable (vnode);

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    {
      cfun_context node_ctx (node);
      basic_block bb;
      gimple_stmt_iterator gsi;

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "\nProcess function (order=%d): ", node->order);
	  print_decl (dump_file, node->decl);
	  fprintf (dump_file, "\n");
	}

      process_type (TREE_TYPE (TREE_TYPE (cfun->decl)));

      for (tree param = DECL_ARGUMENTS (cfun->decl); param;
	   param = TREE_CHAIN (param))
	process_type (TREE_TYPE (param));

      if (cfun->static_chain_decl)
	process_type (TREE_TYPE (cfun->static_chain_decl));

      calculate_dominance_info (CDI_DOMINATORS);

      FOR_EACH_BB_FN (bb, cfun)
	{
	  for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	    {
	      gimple *stmt = gsi_stmt (gsi);

	      gimple_set_plf (stmt, GF_TY_OK, false);
	      gimple_set_visited (stmt, false);
	    }

	  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	    {
	      gimple *stmt = gsi_stmt (gsi);

	      gimple_set_plf (stmt, GF_TY_OK, false);
	      gimple_set_visited (stmt, false);
	    }
	}

      fixup_type_in_thunk ();

      cgraph_edge *callees[2] = { node->callees, node->indirect_calls };

      for (int i = 0; i < 2; i++)
	{
	  for (cgraph_edge *edge = callees[i]; edge; edge = edge->next_callee)
	    {
	      gcall *call_stmt = edge->call_stmt;

	      if (call_is_memory_alloc_p (call_stmt))
		fixup_type_for_memory_alloc (call_stmt);
	      else if (call_is_memory_dealloc_p (call_stmt))
		process_memory_dealloc (call_stmt);
	    }
	}

      int *bbs_rpo = XNEWVEC (int, n_basic_blocks_for_fn (cfun));
      int bbs_rpo_cnt = pre_and_rev_post_order_compute (NULL, bbs_rpo, false);

      bitmap_clear (array_addr_names);

      for (int i = 0; i < bbs_rpo_cnt; i++)
	{
	  bb = BASIC_BLOCK_FOR_FN (cfun, bbs_rpo[i]);

	  for (gsi = gsi_start_phis (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	    process_stmt (gsi_stmt (gsi));

	  for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
	    process_stmt (gsi_stmt (gsi));
	}

      check_array_addresses ();

      free (bbs_rpo);
    }
}

bool
type_trans_analyzer::check_legality (tree type)
{
  gcc_checking_assert (RECORD_OR_UNION_TYPE_P (type));

  type = get_complete_type (type);

  if (!type)
    return false;

  if (TYPE_USER_ALIGN (type))
    return false;

  auto_vec<type_info *> worklist;
  hash_set<type_info *> visited;
  auto_vec<tree> gate_types;

  worklist.safe_push (get_record_type_info (type));
  visited.add (worklist[0]);

  do
    {
      type_info *tinfo = worklist.pop ();

      if (tinfo->usage != TU_NONE)
	return false;

      if (TYPE_CXX_LOCAL (tinfo->type))
	gate_types.safe_push (tinfo->type);
      else
	{
	  for (unsigned i = 0; i < tinfo->referring_types.length (); i++)
	    {
	      type_info *ref_tinfo = tinfo->referring_types[i];

	      if (!visited.add (ref_tinfo))
		worklist.safe_push (ref_tinfo);
	    }
	}
    } while (!worklist.is_empty ());

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Check legality for ");
      print_record_type (dump_file, type);
      fprintf (dump_file, "\n");
      for (unsigned i = 0; i < gate_types.length (); i++)
	{
	  fprintf (dump_file, "Gate type: ");
	  print_record_type (dump_file, gate_types[i]);
	  fprintf (dump_file, "\n");
	}
    }

  return true;
}

bool
type_trans_analyzer::check_field_legality (tree field)
{
  gcc_checking_assert (TREE_CODE (field) == FIELD_DECL);

  if (DECL_VIRTUAL_P (field) || DECL_ARTIFICIAL (field)
      || DECL_PRESERVE_P (field) || DECL_USER_ALIGN (field)
      || DECL_PACKED (field) || TREE_THIS_VOLATILE (field))
    return false;

  type_info *record_tinfo = get_record_type_info (DECL_CONTEXT (field));
  unsigned index = get_field_index (field);

  if (bitmap_bit_p (record_tinfo->addr_taken_fields, index))
    return false;

  tree field_type = TREE_TYPE (field);
  auto_vec<tree> worklist;

  worklist.safe_push (field_type);

  do
    {
      tree type = get_array_etype (worklist.pop ());

      if (POINTER_TYPE_P (type))
	{
	  type = get_array_etype (TREE_TYPE (type));

	  if (RECORD_OR_UNION_TYPE_P (type)
	      && get_record_type_info (type)->excluded_for_field)
	    return false;
	}
      else if (RECORD_OR_UNION_TYPE_P (type))
	{
	  for (tree field1 = TYPE_FIELDS (type); field1;
	       field1 = DECL_CHAIN (field1))
	    worklist.safe_push (TREE_TYPE (field1));
	}
    } while (!worklist.is_empty ());

  if (TREE_CODE (field_type) == ARRAY_TYPE)
    return false;

  field_type = get_underlying_type (field_type);

  if (RECORD_OR_UNION_TYPE_P (field_type))
    {
      if (false && !check_legality (field_type))
	return false;
    }
  else if (VECTOR_TYPE_P (field_type))
    return false;

  return true;
}

static unsigned int
do_field_merge ()
{
  auto_delete_vec<target_type_info> target_types;
  int i;

  strict_type_analysis = false;

  if (!find_target_type (target_types))
    return 0;

  type_trans_analyzer analyzer;

  if (flag_enable_type_analysis)
    {
      analyzer.process ();
      strict_type_analysis = true;
    }

  FOR_EACH_VEC_ELT (target_types, i, targ_type)
    {
      if (!targ_type->valid_p)
	continue;

      if (flag_enable_type_analysis)
	{
	  if (!analyzer.check_legality (targ_type->root_struct))
	    continue;

	  tree fndecl = targ_type->targ_patts[0]->fun->decl;

	  delete targ_type;
	  target_types[i] = NULL;

	  if (!find_target_type_in_function (cgraph_node::get (fndecl)))
	    continue;

	  bool field_legal_p = true;

	  for (unsigned vid = 0; vid < targ_type->nvec; vid++)
	    {
	      tree field = targ_type->vec_decls[vid];

	      gcc_checking_assert (field);

	      if (!analyzer.check_field_legality (field))
		{
		  field_legal_p = false;
		  break;
		}
	    }

	  target_types[i] = targ_type;

	  if (!field_legal_p)
	    continue;
	}

      num_vecs = targ_type->nvec;
      if (check_target_type ())
	transform_target_type ();
    }

  return 0;
}

namespace {

const pass_data pass_data_ipa_field_merge = {
  SIMPLE_IPA_PASS,	 /* type */
  "field-merge",	 /* name */
  OPTGROUP_NONE,	 /* optinfo_flags */
  TV_IPA_STRUCT_MERGE,	 /* tv_id */
  (PROP_cfg | PROP_ssa), /* properties_required */
  0,			 /* properties_provided */
  0,			 /* properties_destroyed */
  0,			 /* todo_flags_start */
  0,			 /* todo_flags_finish */
};

class pass_ipa_field_merge : public simple_ipa_opt_pass
{
public:
  pass_ipa_field_merge (gcc::context *ctx)
    : simple_ipa_opt_pass (pass_data_ipa_field_merge, ctx)
  {}

  virtual bool gate (function *)
  {
    return optimize >= 3 && flag_ipa_field_merge;
  }

  virtual unsigned execute (function *) { return do_field_merge (); }

}; // class pass_ipa_field_merge

} // namespace

simple_ipa_opt_pass *
make_pass_ipa_field_merge (gcc::context *ctxt)
{
  return new pass_ipa_field_merge (ctxt);
}
