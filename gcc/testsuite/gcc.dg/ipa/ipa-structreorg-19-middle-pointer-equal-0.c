/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

#include <assert.h>

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
  _Bool *a = &astruct.a;
  _Bool *d = &astruct.d;
  _Bool *c = &astruct.c;
  _Bool *c_from_a = a + 1;
  _Bool *c_from_d = d - 1;
  assert (c == c_from_a);
  assert (c == c_from_d);
  assert (c_from_a == c_from_d);
  return 0;
}
