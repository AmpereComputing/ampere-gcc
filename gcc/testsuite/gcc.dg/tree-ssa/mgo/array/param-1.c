/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details --param mgo-min-cache-array-length=32 --param mgo-max-cache-array-length=128 " } */

/* { dg-final { scan-tree-dump "\\+ 18446744073709551584" "mgo" } } */
/* { dg-final { scan-tree-dump "<= 96" "mgo" } } */

#include "../mgo-common.h"

/* MGO is disabled if the params of mgo-xxx-cache-array-length are unreasonable */

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L1 *elem = &array[j];
	  sum += elem->l1_l2p->l2_i1;
	  sum += elem->l1_l2p->l2_l3p->l3_i2;
	}
    }

  return sum;
}
