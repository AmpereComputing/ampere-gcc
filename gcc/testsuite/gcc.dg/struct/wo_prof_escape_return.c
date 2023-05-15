/* { dg-do run } */
/* { dg-additional-options "-fno-ipa-sra" } */

#include <stdlib.h>

struct A {
  int d;
};

struct A a;

struct A foo () __attribute__((noinline));
struct A foo ()
{
  a.d = 5;
  return a;
}

int
main ()
{
  a.d = 0;
  foo ();

  if (a.d != 5)
    abort ();

  return 0;
}

/*--------------------------------------------------------------------------*/
/* { dg-final { scan-ipa-dump "has escaped: \"Type escapes via a return" "struct_reorg" } } */
