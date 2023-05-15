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

// RETURN BY VALUE
struct astruct_s
foo (_Bool c)
{
  struct astruct_s astruct;
  astruct.a = 0;
  astruct.c = c;
  astruct.d = 1;
  return astruct;
}

int
main (int argc, char **argv)
{
  struct astruct_s astruct;
  astruct = foo (argc);
  printf ("%d %d %d\n", astruct.a, astruct.c, astruct.d);
  _Bool *a = &(astruct.a);
  assert (!*a);
  _Bool *c = a + 1;
  assert (*c == argc);
  _Bool *d = a + 2;
  assert (*d);
}
