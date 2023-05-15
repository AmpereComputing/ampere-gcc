/* { dg-do link } */
/* { dg-options  "-fipa-dead-field-elimination -fipa-sizeof -flto -fdump-ipa-dead-field-elimination -Wno-dfa" } */

#include <stdio.h>
#include <stdlib.h>

struct astruct_s
{
  _Bool a;
  _Bool b;
  _Bool c;
};
struct astruct_s astruct;

int
main ()
{
  struct astruct_s *s0 = malloc (sizeof (struct astruct_s));

  _Bool s0a = s0->a;
  _Bool s0c = s0->c;

  printf ("%d\n", s0a);
  printf ("%d\n", s0c);
  return sizeof (struct astruct_s);
}

// Should fail because sizeof has an effect outside of memory management functions 
// In fact, the transformation will fail because of SIZEOF_P
/* { dg-final { scan-wpa-ipa-dump-not "change sizeof constant from 3 to 2" "dead-field-elimination" } } */
