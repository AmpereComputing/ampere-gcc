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
    _Bool d;
  };
  struct astruct_s astruct;
  _Bool *a = &(astruct.a);
  _Bool *c = &(astruct.c);
  _Bool *d = &(astruct.d);
  ptrdiff_t diff_1 = c - a;
  ptrdiff_t diff_2 = d - a;
  assert (diff_1 == 1);
  assert (diff_2 == 2);
}
