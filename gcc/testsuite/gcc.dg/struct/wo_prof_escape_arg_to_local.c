/* { dg-do run } */

#include <stdlib.h>
struct str
{
  int a;
  float b;
};

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
foo (struct str * p_str)
{
  static int sum = 0;

  sum = sum + p_str->a;
  return sum;
}

int
main ()
{
  int i, sum;
  struct str * p = malloc (N * sizeof (struct str));
  if (p == NULL)
    return 0;
  for (i = 0; i < N; i++)
    sum = foo (p+i);

  return 0;
}

/*--------------------------------------------------------------------------*/
/* { dg-final { scan-ipa-dump "Number of structures to transform is 1" "struct_reorg"   } } */

