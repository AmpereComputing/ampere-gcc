/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Create field: .*L3_l1_i1" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L2_l2_i1" "mgo" } } */

#include "stdlib.h"
#include "../mgo-common.h"

/* Different levels of local array loads */

void bar(L1 *);

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;
  L1 *local_array = (L1 *) calloc(m, sizeof(L1));
  bar(local_array);

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L2 *l2p = array[j].l1_l2p;
	  int tmp = l2p->l2_i2;
	  sum += local_array[tmp + 3].l1_i1;
	  sum += local_array[j].l1_l2p->l2_i1;
	}
    }

  return sum;
}
