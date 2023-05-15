/* { dg-do run } */
/* { dg-options  "-flto -fipa-type-escape-analysis -fdump-ipa-type-escape-analysis " } */

#include <assert.h>
#include <stddef.h>
#include <stdio.h>

struct astruct_s
{
  _Bool a;
  _Bool b;
  _Bool c;
};

_Bool
returnLast (struct astruct_s astruct)
{
  return astruct.c;
}

_Bool
returnLast2 (struct astruct_s astruct)
{
  _Bool *ptr = &(astruct.a);
  ptr = ptr + 1;
  return *ptr;
}

int
main (int argc, char **argv)
{
  _Bool (*func1) (struct astruct_s);
  func1 = &returnLast;
  _Bool (*func2) (struct astruct_s);
  func2 = &returnLast2;
  struct astruct_s astruct;
  astruct.c = argc;
  printf ("%d %d", astruct.a, astruct.c);
  // These test means that things remain equal
  // A.k.a without an optimization.
  // Why? Because a function pointer can be a
  // pointer to anything
  assert (func1 (astruct) != func2 (astruct));
}
