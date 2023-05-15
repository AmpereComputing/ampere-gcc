/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */
/* { dg-require-effective-target lto } */

#include <stddef.h>

struct astruct_s
{
  _Bool a;
  _Bool b;
  _Bool c;
};
__attribute__ ((externally_visible)) struct astruct_s astruct; // This should escape
struct bstruct_s
{
  _Bool a;  /* { dg-warning "RECORD TYPE 'struct bstruct_s' has dead field 'a' in LTO" } */
  _Bool b;
  _Bool c;  /* { dg-warning "RECORD TYPE 'struct bstruct_s' has dead field 'c' in LTO" } */
  _Bool d;  /* { dg-warning "RECORD TYPE 'struct bstruct_s' has dead field 'd' in LTO" } */
};
struct bstruct_s bstruct; // This should not escape

int
main ()
{
  astruct.a = 0;
  bstruct.b = 0;
  return bstruct.b;
}

