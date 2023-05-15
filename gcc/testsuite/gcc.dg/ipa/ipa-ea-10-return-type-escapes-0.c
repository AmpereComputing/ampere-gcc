/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

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

// This will make astruct_s escape
struct astruct_s __attribute__ ((externally_visible)) escaping ()
{
  struct astruct_s a;
  return a;
}
struct bstruct_s
non_escaping ()
{}

int
main ()
{
  astruct = escaping ();
  bstruct = non_escaping ();
}

