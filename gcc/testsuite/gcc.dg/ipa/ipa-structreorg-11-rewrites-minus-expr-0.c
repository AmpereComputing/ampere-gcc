/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

#include <assert.h>
#include <stddef.h>

int
main ()
{
  struct astruct_s
  {
    _Bool a;
    _Bool b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
    _Bool c;
  };
  struct astruct_s astruct;
  _Bool *c_ptr = &(astruct.c);
  _Bool *a_ptr = &(astruct.a);
  ptrdiff_t diff = c_ptr - a_ptr;
  assert (diff == 1);
  return 0;
}
