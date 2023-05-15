/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

#include "../mgo-common.h"

int
foo (int n, Node *head)
{
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      Node *iterator = head;

      for (int j = 0; j < n; j++)
	{
	  sum += iterator->l1_l2p->l2_l3p->l3_ca[0];
	  sum += iterator->l1_l2p->l2_l3p->l3_i1;
	  sum += iterator->l1_l2p->l2_l3p->l3_ca[2];
	  iterator = iterator->next;
	}
    }

  return sum;
}

/* { dg-final { scan-tree-dump-times "Create field:" 3 "mgo" } } */
