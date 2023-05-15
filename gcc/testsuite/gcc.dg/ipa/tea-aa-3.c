/* { dg-do link } */
/* { dg-options "-O2 -flto -fno-strict-aliasing -fdump-tree-optimized -fipa-type-escape-analysis -fdump-ipa-type-escape-analysis-details -fmem-layout-trans -fdisable-ipa-dead-field-elimination" } */

#include <stdlib.h>

struct A
{
  int *f1;
  int f2;
};

struct B
{
  struct B *fb;
};

struct A a;

__attribute_noinline__ int
foo (struct B *b_ptr)
{
  /* A and B are escaped.  */
  struct A **pa = (struct A **)(&(b_ptr->fb));

  *pa = &a;

  /* alias with *pa.  */
  b_ptr->fb = b_ptr;

  if ((*pa)->f2 != a.f2)
    a.f2 = 999;

  return a.f2;
}

int
main (void)
{
  struct B* arr = malloc (sizeof (struct B) * 10);
  foo (arr + 1);
  foo (arr);
  foo (arr + 3);

  return 0;
}


/* { dg-final { scan-wpa-ipa-dump-not " as non-escaping" "type-escape-analysis" } } */
/* { dg-final { scan-ltrans-tree-dump "999" "optimized" } } */
