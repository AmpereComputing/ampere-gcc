/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Apply mgo to dependent load" "mgo" } } */

#include "../mgo-common.h"

/* Do not skip if there is func call without side effect */

__attribute__((const)) int bar(L1 *);

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      bar(array);

      for (int j = 0; j < m; j++)
	{
	  L1 *elem = &array[j];
	  sum += elem->l1_i1;
	  sum += elem->l1_l2p->l2_i1;
	  sum += elem->l1_l2p->l2_l3p->l3_i2;
	}
    }

  return sum;
}
