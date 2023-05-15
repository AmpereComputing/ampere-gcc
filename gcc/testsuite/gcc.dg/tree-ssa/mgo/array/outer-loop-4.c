/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Final mgo outer loop 2" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* Final outer loop is affected by invariant */

void
bar (L1 *);

int
foo (int n, signed m, signed o)
{
  int sum = 0;

  for (int ii = 0; ii < n; ii++)
    {
      L1 *array = (L1 *) calloc (o, sizeof (L1));

      for (int i = 0; i < n; i++)
	{
	  for (int j = 0; j < m; j++)
	    {
	      for (int k = 0; k < o; k++)
		{
		  L1 *elem = &array[k];
		  sum += elem->l1_i1;
		  sum += elem->l1_l2p->l2_i1;
		  sum += elem->l1_l2p->l2_l3p->l3_i2;
		}
	    }
	}
    }

  return sum;
}
