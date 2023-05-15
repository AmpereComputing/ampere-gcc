/* { dg-do link } */
/* { dg-options  "-Wno-incompatible-pointer-types -Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stddef.h>
#include <stdio.h>

struct astruct_s
{
  _Bool a;
  _Bool b;
  _Bool c;
};
struct bstruct_s
{
  _Bool a;
  _Bool b;
  _Bool c;
  _Bool d;
};
void
foo (struct bstruct_s *s){};

int
main (int argc, char **argv)
{
  struct astruct_s astruct;
  foo (&astruct);
}

