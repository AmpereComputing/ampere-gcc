// -*- C++ -*-

// Copyright (C) 2005, 2006, 2009, 2011 Free Software Foundation, Inc.
//
// This file is part of the GNU ISO C++ Library.  This library is free
// software; you can redistribute it and/or modify it under the terms
// of the GNU General Public License as published by the Free Software
// Foundation; either version 3, or (at your option) any later
// version.

// This library is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.

// Under Section 7 of GPL version 3, you are granted additional
// permissions described in the GCC Runtime Library Exception, version
// 3.1, as published by the Free Software Foundation.

// You should have received a copy of the GNU General Public License and
// a copy of the GCC Runtime Library Exception along with this program;
// see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
// <http://www.gnu.org/licenses/>.

// Copyright (C) 2004 Ami Tavory and Vladimir Dreizin, IBM-HRL.

// Permission to use, copy, modify, sell, and distribute this software
// is hereby granted without fee, provided that the above copyright
// notice appears in all copies, and that both that copyright notice
// and this permission notice appear in supporting documentation. None
// of the above authors, nor IBM Haifa Research Laboratories, make any
// representation about the suitability of this software for any
// purpose. It is provided "as is" without express or implied
// warranty.

/**
 * @file binomial_heap_.hpp
 * Contains an implementation class for a binomial heap.
 */

/*
 * Binomial heap.
 * Vuillemin J is the mastah.
 * Modified from CLRS.
 */

#include <debug/debug.h>
#include <ext/pb_ds/detail/cond_dealtor.hpp>
#include <ext/pb_ds/detail/type_utils.hpp>
#include <ext/pb_ds/detail/binomial_heap_base_/binomial_heap_base_.hpp>

namespace __gnu_pbds
{
  namespace detail
  {

#define PB_DS_CLASS_T_DEC \
    template<typename Value_Type, class Cmp_Fn, class Allocator>

#define PB_DS_CLASS_C_DEC \
    binomial_heap_<Value_Type, Cmp_Fn, Allocator>

#define PB_DS_BASE_C_DEC \
    binomial_heap_base_<Value_Type, Cmp_Fn, Allocator>

    /**
     * class description = "8y|\|0|\/|i41 h34p 74813">
     **/
    template<typename Value_Type, class Cmp_Fn, class Allocator>
    class binomial_heap_ : public PB_DS_BASE_C_DEC
    {
    private:
      typedef PB_DS_BASE_C_DEC base_type;
      typedef typename base_type::node_pointer node_pointer;
      typedef typename base_type::const_node_pointer const_node_pointer;

    public:
      typedef Value_Type value_type;
      typedef typename Allocator::size_type size_type;
      typedef typename Allocator::difference_type difference_type;
      typedef typename base_type::pointer pointer;
      typedef typename base_type::const_pointer const_pointer;
      typedef typename base_type::reference reference;
      typedef typename base_type::const_reference const_reference;
      typedef typename base_type::const_point_iterator const_point_iterator;
      typedef typename base_type::point_iterator point_iterator;
      typedef typename base_type::const_iterator const_iterator;
      typedef typename base_type::iterator iterator;
      typedef typename base_type::cmp_fn cmp_fn;
      typedef typename base_type::allocator_type allocator_type;

      binomial_heap_();

      binomial_heap_(const Cmp_Fn& r_cmp_fn);

      binomial_heap_(const PB_DS_CLASS_C_DEC& other);

      ~binomial_heap_();

    protected:
#ifdef _GLIBCXX_DEBUG
      void
      assert_valid(const char* file, int line) const;
#endif 
    };

#define PB_DS_ASSERT_VALID(X)						\
  _GLIBCXX_DEBUG_ONLY(X.assert_valid(__FILE__, __LINE__);)

#include <ext/pb_ds/detail/binomial_heap_/constructors_destructor_fn_imps.hpp>
#include <ext/pb_ds/detail/binomial_heap_/debug_fn_imps.hpp>

#undef PB_DS_ASSERT_VALID
#undef PB_DS_CLASS_C_DEC

#undef PB_DS_CLASS_T_DEC

#undef PB_DS_BASE_C_DEC
  } // namespace detail
} // namespace __gnu_pbds
