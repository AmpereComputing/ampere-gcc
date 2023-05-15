/* { dg-do compile { target lp64 } } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Create field: .*L2_l2_bf" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L2_l2u_i" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L3.* for .*l3_ia" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L3.* for .*l3_ca" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L3_il3_i2" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L3.* for .*il3_ia" "mgo" } } */
/* { dg-final { scan-tree-dump "Cache element size is 20 bytes" "mgo" } } */

#include "../mgo-common.h"

/* Dependent load of complex types: bit-field, array, union, nested structure.
   Cache fields are also sorted by alignments to save memory space.  */

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L2 *l2p = array[j].l1_l2p;
	  sum += l2p->l2_bf;
	  sum += l2p->l2u.l2u_i;

	  L3 *l3p = l2p->l2_l3p;
	  sum += l3p->l3_ia[2];
	  sum += l3p->l3_ca[3];
	  sum += l3p->l3_is.il3_i2;
	  sum += l3p->l3_is.il3_ia[1];
	}
    }

  return sum;
}
