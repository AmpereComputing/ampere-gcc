/* { dg-do compile } */
/* { dg-do run } */

#include <stdlib.h>
typedef struct
{
  int a;
  float b;
}str_t;

#ifdef STACK_SIZE
#if STACK_SIZE > 8000
#define N 1000
#else
#define N (STACK_SIZE/8)
#endif
#else
#define N 1000
#endif

int
main ()
{
  int i;
  str_t A[N];
  str_t *p = A;

  for (i = 0; i < N; i++)
    p[i].a = 0;

  for (i = 0; i < N; i++)
    if (p[i].a != 0)
      abort ();

  return 0;
}

/* { dg-final { scan-ipa-dump "Number of structures to transform is 1" "struct_reorg" { xfail *-*-* } } } */
