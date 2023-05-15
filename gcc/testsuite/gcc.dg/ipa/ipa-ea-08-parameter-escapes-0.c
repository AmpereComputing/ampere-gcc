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
struct astruct_s astruct; // This should not escape
struct bstruct_s
{
  _Bool a;  /* { dg-warning "RECORD TYPE 'struct bstruct_s' has dead field 'a' in LTO" } */
  _Bool b;  /* { dg-warning "RECORD TYPE 'struct bstruct_s' has dead field 'b' in LTO" } */
  _Bool c;  /* { dg-warning "RECORD TYPE 'struct bstruct_s' has dead field 'c' in LTO" } */
  _Bool d;  /* { dg-warning "RECORD TYPE 'struct bstruct_s' has dead field 'd' in LTO" } */
};
struct bstruct_s bstruct; // This should not escape

__attribute__ ((externally_visible)) void
escaping (struct astruct_s cstruct)
{}
void
non_escaping (struct bstruct_s dstruct)
{}

int
main ()
{
  escaping (astruct);
  non_escaping (bstruct);
}

