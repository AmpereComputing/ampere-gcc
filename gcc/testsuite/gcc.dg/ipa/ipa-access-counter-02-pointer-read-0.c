/* { dg-do link } */
/* { dg-options  "-fipa-type-escape-analysis -fdump-ipa-type-escape-analysis -flto -fipa-sizeof" } */

#include <stdio.h>

struct astruct_s
{
  _Bool a;
  _Bool b;
  _Bool c;
};
struct astruct_s *astruct = NULL;

int
main ()
{
  printf ("%d\n", astruct->a);
  printf ("%d\n", astruct->a);
}

// So, even if we have a pointer COMPONENT_REF counter still works...
/* { dg-final { scan-wpa-ipa-dump "astruct_s.a = 0x0001" "type-escape-analysis" } } */
