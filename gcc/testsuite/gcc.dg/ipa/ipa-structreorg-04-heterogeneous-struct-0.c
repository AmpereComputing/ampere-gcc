/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdio.h>

struct astruct_s
{
  float a;
  _Bool b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
  int c;
};
struct astruct_s astruct;

int
main ()
{
  printf ("%d\n", astruct.a);
  printf ("%d\n", astruct.c);
}

