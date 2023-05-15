/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details --param mgo-max-dep-load-level=3" } */

/* { dg-final { scan-tree-dump "Apply mgo to dependent load" "mgo" } } */

/* { dg-final { scan-tree-dump-not "level 4" "mgo" } } */

#include "../mgo-common.h"

/* mgo-max-dep-load-level: to limit dep load level */

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L1 *elem = &array[j];
	  sum += elem->l1_l2p->l2_l3p->l3_i2;
	  sum += elem->l1_l2p->l2_l3p->l3_l4p->l4_i1;
	}
    }

  return sum;
}
