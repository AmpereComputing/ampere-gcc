/* { dg-do run } */
/* { dg-options  "-flto -fipa-sizeof -fipa-type-escape-analysis -fdump-ipa-type-escape-analysis " } */

#include <stdio.h>

#include <stdlib.h>

struct astruct_s
{
  _Bool a;
  _Bool b;
  _Bool c;
};
struct wrapper_s
{
  struct astruct_s *a;
};

void
foo (struct wrapper_s *wrapper){};

void
bar (struct wrapper_s *wrapper)
{
  foo (wrapper);
};

int
main ()
{
  struct wrapper_s a_wrapper;
  _Bool is_non_null = a_wrapper.a != NULL;
  printf ("%d %d %d", &a_wrapper.a, is_non_null ? a_wrapper.a->a : 0,
	  is_non_null ? a_wrapper.a->c : 0);
  bar (&a_wrapper);
}

/// { dg-final { scan-wpa-ipa-dump "replacing field a 0 with a 0" "type-escape-analysis" } } */
/// { dg-final { scan-wpa-ipa-dump "replacing field c 16 with a 8" "type-escape-analysis" } } */
