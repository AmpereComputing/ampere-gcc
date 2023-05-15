/* IPA Dead Field Elimination
   Copyright (C) 2019-2020 Free Software Foundation, Inc.

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

#ifndef GCC_IPA_DFE
#define GCC_IPA_DFE

#include "ipa-type-escape-analysis.h"

/* Map RECORD_TYPE -> (FIELD_DECL -> delete).  */
typedef hash_map<tree, std::pair<tree, bool> > reorg_field_map2_t;

/* Get a set of all types pointing to types in RECORD_FIELD_OFFSET_MAP.  */
void
get_all_types_pointing_to (record_field_offset_map4_t &record_field_offset_map,
			   tpartitions2_t casting, hash_set<tree> &to_modify);

typedef std::pair<reorg_record_map2_t *, reorg_field_map2_t *> reorg_maps_t;

/* Substitute types.  */
void
substitute_types_in_program (reorg_record_map2_t &map,
			     reorg_field_map2_t &field_map, bool _delete);


const char * get_type_name (tree type);

#endif /* GCC_IPA_DFE.  */
