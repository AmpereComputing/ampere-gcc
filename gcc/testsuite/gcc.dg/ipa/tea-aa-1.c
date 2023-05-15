/* { dg-do link } */
/* { dg-options "-O2 -flto -flto-partition=one -fno-strict-aliasing -fdump-tree-optimized -fipa-type-escape-analysis -fmem-layout-trans -fdisable-ipa-dead-field-elimination" } */

#include <stdlib.h>

/* test: same type, ptr and record field */

struct A
{
  int f1;
};

struct A* arr;

__attribute_noinline__ int
foo (int n, struct A* a_ptr)
{
  a_ptr->f1 = 1;

  int *int_ptr = &(a_ptr->f1);
  *int_ptr = 100;

  for (int i = 0; i < n; i++)
    a_ptr->f1 += 1;

   /* *int_ptr and a_ptr->f1 are aliases.  */
  if (*int_ptr != 100)
    a_ptr->f1 = 999;

  return a_ptr->f1;
}

int
main (void)
{
  arr = malloc (sizeof (struct A) * 10);
  foo (20, arr + 1);
  foo (8, arr);
  foo (7, arr + 3);
  return 0;
}

/* { dg-final { scan-ltrans-tree-dump "999" "optimized" } } */

