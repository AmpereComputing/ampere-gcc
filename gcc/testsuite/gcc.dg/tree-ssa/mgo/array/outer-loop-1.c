/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Final mgo outer loop 1" "mgo" } } */

#include "../mgo-common.h"

/* Final outer loop is the outermost loop as it has the best performance */

int
foo (int n, signed m, signed o, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      array[i].l1_i1 = 1;
      for (int j = 0; j < m; j++)
	{
	  for (int k = 0; k < o; k++)
	    {
	      L1 *elem = &array[k];
	      sum += elem->l1_i1;
	      sum += elem->l1_l2p->l2_i1;
	      sum += elem->l1_l2p->l2_l3p->l3_i2;
	    }
	}
    }

  return sum;
}
