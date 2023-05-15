/* Copyright (C) 2019-2022 Free Software Foundation, Inc.

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

#include "langhooks.h"

/* Check whether in C language or LTO with only C language.  */
inline bool
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


void replace_sizeof_cst (gimple *stmt, hash_map <tree, tree> &type_map);
