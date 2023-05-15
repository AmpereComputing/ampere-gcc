/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

// NOTE: This test is only possible due to -fipa-dlo-tests
// Which allows one to take the address of a field for testing
// purposes

#include <stddef.h>
#include <assert.h>

int
main (int argc, char **argv)
{
  struct astruct_s
  {
    int a;
    int b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
    int c;
  };
  struct astruct_s astruct;
  int *c = &astruct.c;
  int *a = &astruct.a;
  ptrdiff_t d = c - a;
  assert (d == 1);
}
