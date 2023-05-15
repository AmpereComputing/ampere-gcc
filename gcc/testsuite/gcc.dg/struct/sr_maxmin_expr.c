// { dg-do compile }

#include <stdlib.h>

struct S {
  unsigned long a;
  unsigned long b;
};

struct S* s;
struct S* t = (struct S*) 1000;

int
main ()
{
  s = (struct S*) calloc (1000, sizeof (struct S));
  s = s > t ? s : t;
  if (s == 0)
    {
      abort ();
    }
  return 0;
}

/* { dg-final { scan-ipa-dump "No structures to transform." "struct_reorg" } } */
