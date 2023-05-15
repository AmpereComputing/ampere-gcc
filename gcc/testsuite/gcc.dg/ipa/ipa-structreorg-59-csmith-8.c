/* { dg-do run } */
/* { dg-options  "-Wno-implicit-int -Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

struct a
{
  signed b;
};
struct
{
  struct a b;
} volatile c;
main () { c.b.b; }

// we will do nothing because volatile
