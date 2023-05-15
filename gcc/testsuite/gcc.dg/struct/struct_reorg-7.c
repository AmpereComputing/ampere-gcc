/* { dg-do run } */

#include <stdio.h>
#include <stdlib.h>

struct gki_elem {
  char            *key;
  int              idx;
};

typedef struct {
  struct gki_elem *table;

  int primelevel;
  int nhash;
  int nkeys;
} GKI;

void *
sre_malloc(size_t size)
{
  void *ptr = malloc (size);
  return ptr;
}

__attribute__((noinline)) int
GKIStoreKey(GKI *hash)
{
  hash->table = sre_malloc(sizeof(struct gki_elem));
}

int
main ()
{
  GKI *hash = malloc (sizeof(GKI));
  GKIStoreKey(hash);
  return 0;
}
