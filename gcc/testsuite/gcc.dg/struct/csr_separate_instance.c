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

const int MAX = 10000;
node_p n;
node_t t;

int
main ()
{
  n = (node_p) calloc (MAX, sizeof (node_t));
  t.a = 100;

  for (int i = 0; i < MAX; i++)
    {
      n[i].a = t.a;
    }
  for (int i = 0; i < MAX; i++)
    {
      if (n[i].a != 100)
	{
	  abort ();
	}
    }
  return 0;
}

/* { dg-final { scan-ipa-dump "struct node has escaped" "struct_reorg" } } */
