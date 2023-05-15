#include <stdlib.h>
#include <stdio.h>

typedef struct node node_t;
typedef struct node* node_p;

struct node {
  unsigned long a;
  unsigned long b;
  node_p c;
  node_p d;
  long e;
  long f;
  long g;
  long h;
  long i;
  long j;
  long k;
  long l;
  int m;
  int n;
};

const int MAX = 100;
node_p n;
unsigned long y;

int
main ()
{
  n = (node_p) calloc (MAX, sizeof (node_t));

  for (int i = 0; i < MAX; i++)
    {
      n[i].b = 50;
    }

  node_p x = &n[5];
  y = (unsigned long) x;
  y += 8;

  if (*((unsigned long*) y) != 50)
    {
      abort ();
    }

  return 0;
}

/* { dg-final { scan-ipa-dump "struct node has escaped" "struct_reorg" } } */
