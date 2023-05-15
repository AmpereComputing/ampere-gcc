/* { dg-do compile { target lp64 } } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "iterator found in loop" "mgo" } } */

/* { dg-final { scan-tree-dump "Apply mgo to dependent load" "mgo" } } */
/* { dg-final { scan-tree-dump "level 1 .*not cached" "mgo" } } */
/* { dg-final { scan-tree-dump "l1_l2p" "mgo" } } */
/* { dg-final { scan-tree-dump "level 2:" "mgo" } } */
/* { dg-final { scan-tree-dump "l2_i1" "mgo" } } */
/* { dg-final { scan-tree-dump "level 2 .*not cached" "mgo" } } */
/* { dg-final { scan-tree-dump "l2_l3p" "mgo" } } */
/* { dg-final { scan-tree-dump "level 3:" "mgo" } } */
/* { dg-final { scan-tree-dump "l3_i2" "mgo" } } */

/* { dg-final { scan-tree-dump "Create field: .*L2_l2_i1" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L3_l3_i2" "mgo" } } */
/* { dg-final { scan-tree-dump "Cache element size is 12 bytes" "mgo" } } */

/* { dg-final { scan-tree-dump "Use new value: .*L2_l2_i1.* to replace origin dep load" "mgo" } } */
/* { dg-final { scan-tree-dump "Use new value: .*L3_l3_i2.* to replace origin dep load" "mgo" } } */

#include "../mgo-common.h"

/* A simple case of an array (integer as iterator) */

int
foo (int n, signed m, L1 *array)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int j = 0; j < m; j++)
	{
	  L1 *elem = &array[j];
	  /* Level 1 dependent load is not cached */
	  sum += elem->l1_i1;
	  /* Dependent loads are accessed multiple times */
	  sum += elem->l1_l2p->l2_i1;
	  sum += elem->l1_l2p->l2_l3p->l3_i2;
	}
    }

  return sum;
}
