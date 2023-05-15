/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <assert.h>
#include <stdio.h>
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
  struct astruct_s a[2];
  struct astruct_s *a_0 = &(a[0]);
  struct astruct_s *a_1 = &(a[1]);
  struct astruct_s *a_1_from_a_0 = a_0 + 1;
  printf ("%d %d\n", a_0->a, a_0->c);
  //    old  new
  // 0   a    a
  // 1   b    c
  // 2   c    a
  // 3   a    c
  // 4   b    a
  // 5   c    c
  assert (a_1 == a_1_from_a_0);
}
