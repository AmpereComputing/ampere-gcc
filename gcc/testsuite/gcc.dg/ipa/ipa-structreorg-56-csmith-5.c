/* { dg-do run } */
/* { dg-options  "-w -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdint.h>
struct a
{
  int8_t b
};
struct c
{
  struct a d
} e[];

/* Analysis failed because e[2].d was considered not read
 * we were only looking at e[2].d.b which is considered read.
 * So we need to recurse
 */
f () { g (e[2].d.b, 0); }

void
g (int8_t a, int8_t b)
{
  a + b;
}
main () {}
