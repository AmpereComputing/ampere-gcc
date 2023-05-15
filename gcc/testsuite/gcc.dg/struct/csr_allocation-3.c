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

void test (int, int) __attribute__((noinline));

void
test (int num, int flag)
{
  if (num <= 0)
    {
      return;
    }
  n = (node_p) calloc (num, sizeof (node_t));
  if (flag)
    {
      m = n;
    }
  return;
}

int
main ()
{
  test (MAX, 1);
  test (MAX, 0);

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
  for (int i = 0; i < MAX; i++)
    {
      if (m[i].a != 50)
	{
	  abort ();
	}
    }
  return 0;
}

/* { dg-final { scan-ipa-dump "No structures to transform in Complete Structure Relayout." "struct_reorg" } } */
