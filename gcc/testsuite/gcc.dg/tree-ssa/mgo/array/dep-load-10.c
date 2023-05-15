/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Create field: .*L3_same_id_i_cf_0" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L3_same_id_i_cf_1" "mgo" } } */

#include "../mgo-common.h"

/* Fields of different levels can have the same name, as each new field name is appended an unique prefix  */

int
foo (int n, signed m, int invar, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L1 *elem = &array[j];
	  sum += elem->l1_i1;
	  sum += elem->l1_l2p->l2_l3p->same_id_i;
	  sum += elem->l1_l2p->l2_l3op->same_id_i;
	}
    }

  return sum;
}
