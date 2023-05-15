/* { dg-do run } */
/* { dg-options  "-Wno-implicit-int -Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdint.h>

void
foo (uint64_t a, uint64_t b)
{
  a + b;
}

struct a
{
  uint64_t b;
  uint8_t c; /* { dg-warning "RECORD TYPE 'struct a' has dead field 'c' in LTO" } */
} d ()
{
  // I think the problem here is with the const attribute...
  const struct a e;
  foo (0, e.b);
  return e;
}

main () {}
