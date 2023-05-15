/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Pruning may-trap dependent loads" "mgo" } } */

/* { dg-final { scan-tree-dump-not "Create field: .*L3_l3_i2" "mgo" } } */

#include "../mgo-common.h"

/* prune may-trap dep load */

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (L1 *elem = array; elem < array + m; elem++)
	{
	  sum += elem->l1_i1;
	  sum += elem->l1_l2p->l2_i2;
	  sum += elem->l1_l2p->l2_i1;
	  if (sum % 3)
	    continue;
	  sum += elem->l1_l2p->l2_l3p->l3_i2;
	}
    }

  return sum;
}
