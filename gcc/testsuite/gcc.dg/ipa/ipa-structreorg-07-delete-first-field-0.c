/* { dg-do run } */
/* { dg-options  "-w -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */
// We can't remove -w because -Wno-compare-distinct-pointer-types  not working...

#include <assert.h>
#include <stdio.h>


int
main ()
{
  struct astruct_s
  {
    _Bool b;  // This one will be deleted but we can't test with -w
    _Bool a;
    _Bool c;
    _Bool d;
  };
  struct astruct_s astruct;

  printf ("%d %d %d\n", astruct.a, astruct.c, astruct.d);
  _Bool *a_ptr = &astruct.a;
  struct astruct_s *s_ptr = &astruct;
  // But this is the real test
  assert (a_ptr == s_ptr);
}
