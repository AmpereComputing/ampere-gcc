/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Pruning dependent load" "mgo" } } */

/* { dg-final { scan-tree-dump "Create field: .*L3_l3_l" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L3_l3_l4p" "mgo" } } */
/* { dg-final { scan-tree-dump-not "Create field: .*L4_l4_i1" "mgo" } } */

#include "../mgo-common.h"

/* Loads after an alias store are pruned, while loads before an store are kept by adding runtime check */

int
foo (int n, signed m, L1 *array, int *other_val)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L1 *elem = &array[j];
	  sum += elem->l1_i1;
	  sum += elem->l1_l2p->l2_l3p->l3_i2;

	  *other_val = 1;
	  sum += elem->l1_l2p->l2_l3p->l3_l;
	  sum += elem->l1_l2p->l2_l3p->l3_l4p->l4_i1;
	}
    }

  return sum;
}
