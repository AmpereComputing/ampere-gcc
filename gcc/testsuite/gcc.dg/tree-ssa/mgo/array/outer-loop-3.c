/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details --param mgo-runtime-alias-check=1" } */

/* { dg-final { scan-tree-dump "Final mgo outer loop 1" "mgo" } } */

#include "../mgo-common.h"

/* Final outer loop is affected by cost */

void
bar ();

int
foo (int n, signed m, signed o, L1 *array, int *other_val)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      /* Dynamic alias check will introduce additional cost */
      *other_val = 1;
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

  return sum;
}
