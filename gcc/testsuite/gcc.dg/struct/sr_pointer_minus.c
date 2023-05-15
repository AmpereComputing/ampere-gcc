// { dg-do compile }

#include <stdlib.h>

typedef struct node node_t;
typedef struct node* node_p;

struct node {
  unsigned long a;
  unsigned long b;
};

int max;
int x;

node_p n;
node_p z;

int
main ()
{
  n = (node_p) calloc (max, sizeof (node_t));

  node_p xp = &n[x];

  if (xp - z == 10)
    {
      abort ();
    }
  return 0;
}

/* { dg-final { scan-ipa-dump "struct node has escaped: \"Type escapes via a unhandled rewrite stmt\"" "struct_reorg" } } */
