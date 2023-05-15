/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Pruning dependent load" "mgo" } } */

/* { dg-final { scan-tree-dump-not "Create field: .*L2_l2_i1" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L3_l3_i2" "mgo" } } */

#include "../mgo-common.h"

/* Prune pre-clobbered fields (i.e. l2_i1) */

int
foo (int n, signed m, L1 *array, L1 *other_ptr)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L1 *elem = &array[j];
	  other_ptr->l1_l2p->l2_i1 = 1;
	  sum += elem->l1_l2p->l2_i1;
	  sum += elem->l1_l2p->l2_l3p->l3_i2;
	}
    }

  return sum;
}
