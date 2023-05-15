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
  long i, num;

  num = rand();
  num = num > N ? N : num; 
  str_t * p = malloc (num * sizeof (str_t));

  if (p == 0)
    return 0;

  for (i = 1; i <= num; i++)
    p[i-1].b = i;

  for (i = 1; i <= num; i++)
    p[i-1].a = p[i-1].b + 1;

  for (i = 0; i < num; i++)
    if (p[i].a != p[i].b + 1)
      abort ();
  
  return 0;
}

/*--------------------------------------------------------------------------*/
/* { dg-final { scan-ipa-dump "Number of structures to transform is 1" "struct_reorg" } } */
