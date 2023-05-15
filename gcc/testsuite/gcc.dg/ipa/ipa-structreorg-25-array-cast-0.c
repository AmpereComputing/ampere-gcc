/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <assert.h>
#include <stdio.h>
#include <stddef.h>

int
main ()
{
  struct astruct_s
  {
    _Bool a;
    _Bool b;
    _Bool c;
    _Bool d;
  };
  struct astruct_s a[2];
  struct bstruct_s
  {
    _Bool a;
    _Bool c;
    _Bool d;
  };

  struct astruct_s *a_1 = &(a[1]);
  struct astruct_s *a_0 = a_1 - 1;
  struct bstruct_s *b_1 = (struct bstruct_s *) a_1; // Cast, therefore no transformation
  struct bstruct_s *b_0 = b_1 - 1;
  assert ((struct bstruct_s *) a_0 != b_0);
}
