/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <assert.h>
#include <stdio.h>
#include <stddef.h>

int
main (int argc, char **argv)
{
  struct astruct_s
  {
    _Bool a;
    _Bool b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
    _Bool c;
    _Bool d;
  };
  struct astruct_s a[2][2];

  struct astruct_s b = a[argc][argc];
  printf ("%d %d %d\n", b.a, b.c, b.d);
}

