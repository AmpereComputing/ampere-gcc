/* { dg-do link } */
/* { dg-options "-O2 -flto -fipa-type-escape-analysis -fno-strict-aliasing -fdump-ipa-type-escape-analysis-details -fdump-tree-fre5 -fmem-layout-trans -fdisable-ipa-dead-field-elimination" } */

#include <stdlib.h>
#include <stdio.h>

/* test: pointers to different non-escaped types.  */

struct A
{
  int *f1;
  int f2;
};

struct B
{
  struct B *fb;
};

struct B *arrB;
struct A *arrA;

__attribute_noinline__ int
foo (struct A *a_ptr, struct B *b_ptr)
{
  struct B *new = malloc (sizeof (struct B));

  // no aliasing
  a_ptr->f2 = 1000;
  b_ptr->fb = new;

  if (a_ptr->f2 != 1000)
    return 999;

  return (a_ptr + 1)->f2;
}

int
main (void)
{
  arrB = malloc (sizeof (struct B) * 10);
  arrA = malloc (sizeof (struct A) * 10);
  printf ("%d\n", foo (arrA, arrB + 1));
  printf ("%d\n", foo (arrA, arrB));
  printf ("%d\n", foo (arrA + 1, arrB + 3));

  return 0;
}

/* { dg-final { scan-wpa-ipa-dump "struct A as non-escaping" "type-escape-analysis" } } */
/* { dg-final { scan-wpa-ipa-dump "struct B as non-escaping" "type-escape-analysis" } } */
/* { dg-final { scan-ltrans-tree-dump-not "999" "fre5" } } */

