/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

#include <assert.h>
#include <stdio.h>
#include <stddef.h>

struct astruct_s
{
  _Bool a;
  _Bool b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
  _Bool c;
  _Bool d;
};

// PASS BY REFERENCE
_Bool
foo (struct astruct_s *astruct)
{
  assert (astruct);
  _Bool *a = &(astruct->a);
  assert (!*a);
  _Bool *c = a + 1;
  assert (*c);
  _Bool *d = a + 2;
  assert (*d);
  return *c;
}

int
main (int argc, char **argv)
{
  struct astruct_s astruct;
  astruct.a = 0;
  astruct.c = argc;
  astruct.d = 1;
  printf ("%d %d %d\n", astruct.a, astruct.c, astruct.d);
  foo (&astruct);
}

