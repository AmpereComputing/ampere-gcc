/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdlib.h>
#include <stdio.h>

typedef struct astruct astruct_t;
typedef struct astruct *astruct_p;

struct astruct
{
  int a;
  int b;
  astruct_p one;  /* { dg-warning "RECORD TYPE 'struct astruct' has dead field 'one' in LTO" } */
  astruct_p two;  /* { dg-warning "RECORD TYPE 'struct astruct' has dead field 'two' in LTO" } */
  int c;
  int d;
};

int
main ()
{
  int n = 10;
  astruct_p *astructs;
  register astruct_t *astructnew
    = (astruct_t *) malloc (n * sizeof (astruct_p));
  astructs = (astruct_p *) malloc (n * n * sizeof (astruct_p));
  astructs[n - 1][n - 1] = astructnew[0];
  printf ("%d %d %d %d\n", astructnew->a, astructnew->b, astructnew->c,
	  astructnew->d);
  return 0;
}
