/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdio.h>
#include <assert.h>
#include <stdbool.h>

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
  struct astruct_s *t, copy;
  t = &astruct;
  t->a = true;
  t->c = true;
  copy = *t;
  printf ("%d %d", copy.a, copy.c);
  assert (astruct.a == true);
  assert (astruct.c == true);
  return 0;
}
