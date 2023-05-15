/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <assert.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdio.h>

int
main (int argc, char **argv)
{
  struct astruct_s
  {
    _Bool a;
    _Bool delete_me;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'delete_me' in LTO" } */
    _Bool c;
  };
  struct astruct_s astruct;
  printf ("%d %d", astruct.a, astruct.c);
  astruct.delete_me = false;
  return 0;
}
