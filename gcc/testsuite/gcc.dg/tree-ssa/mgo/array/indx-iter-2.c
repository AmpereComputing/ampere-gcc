/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump-not "iterator found in loop" "mgo" } } */

#include "../mgo-common.h"

/* Unsupported iterator: stride should be integer const */

int
foo (int n, signed m, signed k, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j+=k)
	{
	  L1 *elem = &array[j];
	  sum += elem->l1_i1;
	  sum += elem->l1_l2p->l2_i1;
	  sum += elem->l1_l2p->l2_l3p->l3_i2;
	}
    }

  return sum;
}
