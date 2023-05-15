/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

#include <assert.h>
#include <stdio.h>
#include <stddef.h>

int
main ()
{
  // unmodified { a = 1, b = 4; c = 5; d = 8; e = 12
  // modified { a = 1, c = 2; d = 4, e = 8
  struct astruct_s
  {
    _Bool a;
    int b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
    _Bool c;
    int d;
    _Bool e;
  };
  struct astruct_s astruct;
  _Bool *a = &(astruct.a);
  printf ("%d %d\n", astruct.c, astruct.d);
  _Bool *e = &(astruct.e);
  ptrdiff_t diff = e - a;
  assert (diff == 8);
}
