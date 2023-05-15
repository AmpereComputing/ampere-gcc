/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdio.h>

struct astruct_s
{
  _Bool a;
  _Bool b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
  _Bool c;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'c' in LTO" } */
};
struct astruct_s astruct;

int
main ()
{
  astruct.a++;
  astruct.a = 3;
}

