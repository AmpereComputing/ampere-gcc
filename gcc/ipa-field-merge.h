/* Copyright (C) 2016-2021 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3, or (at your option) any
later version.

GCC is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#ifndef IPA_FIELD_MERGE_H
#define IPA_FIELD_MERGE_H

extern bool
extract_block_cond (basic_block bb, tree_code exp_code, tree &lhs, tree &rhs,
                    basic_block &true_dest, basic_block &false_dest);

extern bool
extract_gimple_cond (gimple *cond_stmt, tree_code exp_code, tree &lhs,
                     tree &rhs, bool &invert_p);

extern bool
gimple_assign_rhs_code_p (gimple *stmt, enum tree_code code);

#endif
