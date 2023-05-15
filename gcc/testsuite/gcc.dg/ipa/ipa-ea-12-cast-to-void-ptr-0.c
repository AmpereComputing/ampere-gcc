/* { dg-do link } */
/* { dg-options  "-flto -fipa-type-escape-analysis -fdump-ipa-type-escape-analysis -Wno-dfa -fipa-sizeof" } */

#include <stddef.h>

struct astruct_s
{
  _Bool a;
  _Bool b;
  _Bool c;
};
struct astruct_s astruct; // This should not escape
struct bstruct_s
{
  _Bool a;
  _Bool b;
  _Bool c;
};
struct bstruct_s bstruct; // This should not escape

__attribute__ ((noinline)) void
casting_to_void (struct astruct_s *s)
{
  static void *nullify_non_escape;

  nullify_non_escape = s;
}

int
main (int argc, char *argv[])
{
  astruct.a = 0;
  bstruct.b = 0;
  if (argc == 3)
    casting_to_void (&astruct);
}

/// { dg-final { scan-wpa-ipa-dump "void_type. reason: e=1 g=0 p=0 r=0 c=1 v=0 u=0 i=0" "type-escape-analysis" } } */
// base type
/// { dg-final { scan-wpa-ipa-dump " record astruct_s .boolean_type a;boolean_type b;boolean_type c;. reason: e=1 g=0 p=0 r=0 c=1 v=0 u=0" "type-escape-analysis" } } */
// pointer
/// { dg-final { scan-wpa-ipa-dump " record astruct_s .boolean_type a;boolean_type b;boolean_type c;.. reason: e=1 g=0 p=0 r=0 c=1 v=0 u=0" "type-escape-analysis" } } */
