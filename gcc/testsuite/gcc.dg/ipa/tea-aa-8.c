/* { dg-do link } */
/* { dg-options "-O2 -flto -fipa-type-escape-analysis -fdump-ipa-type-escape-analysis-details -fno-strict-aliasing -fdump-tree-fre5 -fmem-layout-trans" } */

#include <stdlib.h>
#include <stdio.h>

struct A
{
  int *f1;
  int f2;
};

struct B
{
  struct A* fa;
};

struct A *arrA;
struct B *arrB;

__attribute_noinline__ int
foo (struct A *a_ptr, struct B *b_ptr)
{
  // no aliasing
  a_ptr->f2 = 1000;
  b_ptr->fa->f1 = (int *) 2000;

  if (a_ptr->f2 != 1000)
    return 999;

  return *((b_ptr + 1)->fa->f1);
}

int
main (void)
{
  arrB = malloc (sizeof (struct B) * 10);
  arrA = malloc (sizeof (struct A) * 10);
  int *arr = malloc (sizeof (int) * 10);
  int i;
  for (i = 0; i < 10; i++)
    {
      (arrB + i)->fa = arrA + i;
      (arrA + i)->f1 = arr + i;
    }
  printf ("%d\n", foo (arrA + 6, arrB + 1));
  printf ("%d\n", foo (arrA + 5, arrB + 3));
  printf ("%d\n", foo (arrA + 1, arrB + 1));

  return 0;
}

/* { dg-final { scan-wpa-ipa-dump "struct A as non-escaping" "type-escape-analysis" } } */
/* { dg-final { scan-wpa-ipa-dump "struct B as non-escaping" "type-escape-analysis" } } */
/* { dg-final { scan-ltrans-tree-dump-not "999" "fre5" } } */

