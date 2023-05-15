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
  };
  struct astruct_s b[2];
  _Bool *a_0_ptr = &(b[0].a);
  _Bool *c_0_ptr = &(b[0].c);
  _Bool *a_1_ptr = &(b[1].a);

  _Bool *c_0_ptr_from_a_0_ptr = a_0_ptr + 1;
  _Bool *c_0_ptr_from_a_1_ptr = a_1_ptr - 1;
  assert (c_0_ptr_from_a_0_ptr == c_0_ptr);
  assert (c_0_ptr_from_a_1_ptr == c_0_ptr);
}
