/* { dg-do run } */
/* { dg-options  "-w -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdint.h>
union a
{
  int16_t b
} c ()
{
  union a d;
  -d.b;
}
main () {}
