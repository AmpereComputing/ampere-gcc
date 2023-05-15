/* { dg-do link } */
/* { dg-options "-O2 -flto -fipa-type-escape-analysis -fno-strict-aliasing -fdump-ipa-type-escape-analysis-details -fdump-tree-fre5 -flto -fmem-layout-trans -fdisable-ipa-dead-field-elimination" } */

#include <stdlib.h>
#include <stdio.h>

/* test: int* and non-escaped type.  */
struct A
{
  struct A *f1;
};

struct A *arr;

__attribute_noinline__ int
foo (int *int_ptr, struct A *a_ptr)
{
  struct A *new = malloc (sizeof (struct A));

  // no aliasing
  *int_ptr = 100;
  a_ptr->f1 = new;

  if (*int_ptr != 100)
    return 999;

  return *(int_ptr + 1);
}

int
main (void)
{
  int *int_arr = malloc (sizeof (int) * 20);
  arr = malloc (sizeof (struct A) * 20);

  printf ("%d\n", foo (int_arr, arr));
  printf ("%d\n", foo (int_arr + 5, arr + 1));
  printf ("%d\n", foo (int_arr + 11, arr + 3));

  return 0;
}

/* { dg-final { scan-wpa-ipa-dump "struct A as non-escaping" "type-escape-analysis" } } */
/* { dg-final { scan-ltrans-tree-dump-not "999" "fre5" } } */

