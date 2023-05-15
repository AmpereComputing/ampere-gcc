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

struct bstruct_s
{
  int a;
  int b;
  int c;
};

int
main ()
{
  struct astruct_s *s0 = malloc (sizeof (struct astruct_s) * sizeof (struct bstruct_s));
  struct bstruct_s b0;

  _Bool s0a = s0->a;
  _Bool s0c = s0->c;
  int b0a = b0.a;
  int b0b = b0.b;
  int b0c = b0.c;

  printf ("%d\n", s0a);
  printf ("%d\n", s0c);
  printf ("%d\n", b0a);
  printf ("%d\n", b0b);
  printf ("%d\n", b0c);
}

/* { dg-final { scan-wpa-ipa-dump-not "change sizeof constant from 3 to 2" "dead-field-elimination" } } */
