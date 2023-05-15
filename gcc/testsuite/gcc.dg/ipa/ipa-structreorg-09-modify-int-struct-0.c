/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

#include <assert.h>

int
main ()
{
  struct astruct_s
  {
    int a;
    int b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
    int c;
    int d;
  };
  struct astruct_s astruct;
  int *a = &(astruct.a);
  int *c = &(astruct.c);
  int *d = &(astruct.d);
  assert (c - 1 == a);
  assert (a + 2 == d);
}
