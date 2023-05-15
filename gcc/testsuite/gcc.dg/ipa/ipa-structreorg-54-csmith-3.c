/* { dg-do run } */
/* { dg-options  "-w -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdint.h>

struct
{
  uint64_t a
} b[];
struct
{
  unsigned : 5;
  unsigned a
} c;
d ()
{
  uint16_t e = b;
  int8_t f = c.a;
}
main () { return 0; }

