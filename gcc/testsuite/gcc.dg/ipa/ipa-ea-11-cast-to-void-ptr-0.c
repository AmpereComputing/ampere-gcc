/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stddef.h>

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

struct bstruct_s *
casting_to_void (struct astruct_s *s)
{
  return (struct bstruct_s *) (s);
}

int
main ()
{
  struct astruct_s astruct;
  struct bstruct_s bstruct;
  casting_to_void (&astruct);
}

