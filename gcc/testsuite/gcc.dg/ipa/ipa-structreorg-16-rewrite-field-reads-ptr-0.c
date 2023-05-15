/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

#include <assert.h>
#include <stddef.h>
#include <stdio.h>

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
  struct astruct_s *astruct_p = &astruct;
  printf ("%d %d\n", astruct_p->a, astruct_p->c);
  _Bool *a = &(astruct.a);
  _Bool *c = &(astruct.c);
  assert (a + 1 == c);
  return 0;
}
