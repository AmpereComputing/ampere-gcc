/* { dg-do compile } */
/* { dg-do run } */

#include <stdlib.h>
typedef struct
{
  int a;
  int *b;
}str_t;

#define N 3

str_t *p;

int
main ()
{
  str_t str;
  int i;
  int res = 1 << (1 << N);
  p = &str;
  str.a = 2;
 
  p->b = &(p->a);

  for (i=0; i < N; i++)
    p->a = *(p->b)*(*(p->b));

  if (p->a != res)
    abort ();
  
  /* POSIX ignores all but the 8 low-order bits, but other
     environments may not.  */
  return (p->a & 255);
}

/*--------------------------------------------------------------------------*/
/* { dg-final { scan-ipa-dump "has escaped...Type escapes a cast to a different" "struct_reorg" } } */
