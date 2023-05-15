/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump-times "Create field: .*L2_l2_i2" 1 "mgo" } } */

#include "../mgo-common.h"

/* merge identical dep load  */

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L2 *l2p = array[j].l1_l2p;
	  int tmp = l2p->l2_i1;
	  sum += tmp;

	  if (tmp % 4)
	    sum += l2p->l2_i2;
	  else if (tmp % 5)
	    sum += l2p->l2_i2;
	}
    }

  return sum;
}
