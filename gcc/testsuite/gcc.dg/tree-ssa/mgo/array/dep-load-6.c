/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Pruning may-trap dependent loads" "mgo" } } */

/* { dg-final { scan-tree-dump-not "Create field: .*L3_l3_vla" "mgo" } } */

#include "../mgo-common.h"

/* Prune may trapped load: variable-length array */

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L3 *l3p = array[j].l1_l2p->l2_l3p;
	  sum += l3p->l3_i2;
	  if (l3p->l3_i1)
	    sum += l3p->l3_vla[16];
	}
    }

  return sum;
}
