/* { dg-do link } */
/* { dg-options "-O2 -flto -flto-partition=one -fipa-type-escape-analysis -fno-strict-aliasing -fdump-tree-optimized -fdisable-ipa-dead-field-elimination -fmem-layout-trans" } */

#include <stdlib.h>
#include <stdio.h>

/* test: record in another record.  */

struct A
{
  int *f1;
  int f2;
};

struct B
{
  struct A fa;
  struct B *fb;
};

struct B *arrB;

__attribute_noinline__ int
foo (struct A *a_ptr, struct B *b_ptr)
{
  // may alias
  a_ptr->f2 = 1000;
  b_ptr->fa.f2 = 2000;

  if (a_ptr->f2 == 1000)
    return 999;

  return (b_ptr + 1)->fa.f2;
}

int
main (void)
{
  arrB = malloc (sizeof (struct B) * 10);
  printf ("%d\n", foo (&(arrB->fa), arrB + 1));
  printf ("%d\n", foo (&(arrB + 1)->fa, arrB + 1));
  printf ("%d\n", foo (&(arrB + 5)->fa, arrB + 3));

  return 0;
}

/* { dg-final { scan-ltrans-tree-dump "999" "optimized" } } */

