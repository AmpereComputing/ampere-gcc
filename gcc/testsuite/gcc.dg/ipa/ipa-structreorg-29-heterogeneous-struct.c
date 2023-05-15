/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

#include <assert.h>
#include <stdio.h>
#include <stddef.h>

int
main ()
{
  struct astruct_s
  {
    int a;
    _Bool b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
    int c;
  };
  struct astruct_s astruct;
  int *a = &(astruct.a);
  int *c = &(astruct.c);
  ptrdiff_t d = c - a;
  assert (d == 1);
}
