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

const int MAX = 10;
node_p n;
node_p m;

int main()
{
  int i;
  for (i = 0; i < MAX / 5; i++)
    {
      n = (node_p) calloc(MAX, sizeof(node_t));
      if (i == 0)
	{
	  m = n;
	}
    }

  for (int i = 0; i < MAX; i++)
    {
      n[i].a = 100;
    }
  for (int i = 0; i < MAX; i++)
    {
      m[i].a = 50;
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

/* { dg-final { scan-ipa-dump "No structures to transform in Complete Structure Relayout." "struct_reorg" } } */
