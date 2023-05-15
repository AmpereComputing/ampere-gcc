/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Create field: .*L4_l4_i1" "mgo" } } */

#include "../mgo-common.h"

/* runtime check for alias in outer loop */

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      array[i].l1_l2p->l2_l3p->l3_l = 1;
      for (int j = 0; j < m; j++)
	{
	  L1 *elem = &array[j];
	  sum += elem->l1_i1;
	  sum += elem->l1_l2p->l2_l3p->l3_l;
	  sum += elem->l1_l2p->l2_l3p->l3_l4p->l4_i1;
	}
    }

  return sum;
}
