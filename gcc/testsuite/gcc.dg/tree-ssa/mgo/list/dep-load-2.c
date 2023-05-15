/* { dg-do compile { target lp64 } } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "> Create field: .*L3_l3_i1" "mgo" } } */
/* { dg-final { scan-tree-dump "> Create field: .*L6_l3_i2" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* The dependent load value could be the address computation of next level */

int
foo (int n, L1 *array)
{
  Node *head = NULL;
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      Node *node = (Node *) calloc (1, sizeof (Node));
      node->next = head;
      head = node;

      Node *iterator = head;

      while (iterator)
	{
	  int l3i = iterator->l1_l2p->l2_l3p->l3_i1;
	  sum += l3i;
	  sum += array[l3i + 3].l1_l2p->l2_l3p->l3_i2;
	  iterator = iterator->next;
	}
    }

  return sum;
}
