/* { dg-do link } */
/* { dg-options "-O3 -flto -flto-partition=one -fno-strict-aliasing -fdump-tree-optimized -fipa-type-escape-analysis -fmem-layout-trans -fdisable-ipa-dead-field-elimination" } */

#include <stdlib.h>
#include <stdio.h>

/* test: different type, ptr and record field */

struct A
{
  int *f1;
  int f2;
};

struct A* arr;

__attribute_noinline__ int
foo (int n, struct A* a_ptr)
{
  a_ptr->f2 = 1;

  long *long_ptr = (long *)(&(a_ptr->f2));
  *long_ptr = 100l;

  for (int i = 0; i < n; i++)
    a_ptr->f2 += 1;

  /* *long_ptr and a_ptr->f2 are aliases.  */
  if (*long_ptr != 100l)
    a_ptr->f2 = 999;

  return a_ptr->f2;
}

int main(void)
{
  arr = malloc (sizeof (struct A) * 10);
  printf ("%d\n", foo (20, arr + 1));
  printf ("%d\n", foo (8, arr));
  printf ("%d\n", foo (7, arr + 3));
  return 0;
}

/* FIXME: type struct A should be ruled out, so that refs_may_alias_p_2
   returns true for MEM[(long int *)a_ptr + 8B] and a_ptr->f2.  */

/* { dg-final { scan-ltrans-tree-dump "999" "optimized" } } */