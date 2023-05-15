/* { dg-do link } */
/* { dg-options "-O2 -flto -flto-partition=one -fno-strict-aliasing -fdump-tree-optimized -fipa-type-escape-analysis -fmem-layout-trans -fdisable-ipa-dead-field-elimination" } */

#include <stdlib.h>
#include <stdio.h>

/* test: same type, ptr and record field */

struct A
{
  int* f1;
  int f2;
};

struct A* arr;
int* int_arr;
int** ptrptr;

__attribute_noinline__ int
foo (int n, struct A *a_ptr)
{
  // aliasing
  a_ptr->f1 = int_arr + n;
  *ptrptr = NULL;

  /* Can't be optimized.  */
  if (a_ptr->f1 != int_arr + n)
    a_ptr->f2 = 999;

  return (a_ptr - 1)->f2;
}

int
main (void)
{
  arr = malloc (sizeof (struct A) * 10);
  int_arr = malloc (sizeof (int) * 10);

  printf ("%d\n", foo (20, arr + 1));

  //causing *ptrptr alias with arr->f1
  ptrptr = &(arr->f1);
  printf ("%d\n", foo (8, arr));

  printf ("%d\n", foo (7, arr + 2));
  return 0;
}

/* { dg-final { scan-ltrans-tree-dump "999" "optimized" } } */
