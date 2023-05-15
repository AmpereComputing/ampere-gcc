/* { dg-do run } */
/* { dg-options  "-Wno-implicit-int -Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdint.h>
struct a
{
  int32_t b;  /* { dg-warning "RECORD TYPE 'struct a' has dead field 'b' in LTO" } */
} c;
d ()
{
  for (;; c.b = 0)
    ;
}
main () {}
