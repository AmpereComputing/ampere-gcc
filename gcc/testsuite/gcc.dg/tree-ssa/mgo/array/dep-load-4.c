/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Create field: .*L2_l2u_c" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L2_l2u_f" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L2_l2u_i" "mgo" } } */

#include "../mgo-common.h"

/* Dependent load of complex types: different types in a Union  */

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L2 *l2p = array[j].l1_l2p;
	  int tmp = l2p->l2u.l2u_c;
	  sum += tmp;

	  if (tmp % 4)
	    sum += l2p->l2u.l2u_i;
	  else if (tmp % 5)
	    sum += l2p->l2u.l2u_f;
	}
    }

  return sum;
}
