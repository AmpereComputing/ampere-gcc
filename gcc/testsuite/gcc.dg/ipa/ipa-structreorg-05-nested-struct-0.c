/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdio.h>

struct astruct_s
{
  float a;
  _Bool b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
  int c;
};
struct ostruct_s
{
  struct astruct_s a;
  float b;
  float c;
};
struct ostruct_s ostruct;

int
main ()
{
  printf ("%d\n", ostruct.b);
  printf ("%d\n", ostruct.c);
  printf ("%f\n", ostruct.a.a);
  printf ("%d\n", ostruct.a.c);
}

