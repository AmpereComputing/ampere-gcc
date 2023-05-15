/* { dg-do run } */
/* { dg-options  "-w -flto -fipa-type-escape-analysis -fdump-ipa-type-escape-analysis -fipa-dlo-tests" } */

#include <assert.h>

int
main ()
{
  struct astruct_s
  {
    _Bool a;
    _Bool b;
    _Bool c;
    _Bool d;
  };
  struct astruct_s astruct;
  _Bool *c_ptr = &astruct.c;
  *c_ptr = 1;
  _Bool *a_ptr = &astruct.a;
  _Bool *d_ptr = &astruct.d;
  a_ptr++;
  d_ptr--;
  assert (*a_ptr == 1);
  assert (*d_ptr == 1);
  return 0;
}
