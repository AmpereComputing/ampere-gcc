/* { dg-do compile { target lp64 } } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Create field: .*L3_l3_i1" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L4_l4_i2" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* None alias stores don't affect dependent loads */

int
foo (int n, int *other_val)
{
  Node *head = NULL;
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      /* Add a new node to the list head */
      Node *node = (Node *) calloc (1, sizeof (Node));
      node->next = head;
      head = node;

      Node *iterator = head;

      while (iterator)
	{
	  *other_val = 1;
	  /* Dependent loads are accessed multiple times */
	  sum += iterator->l1_l2p->l2_l3p->l3_i1;
	  sum += iterator->l1_l2p->l2_l3p->l3_l4p->l4_i2;
	  iterator = iterator->next;
	}
    }

  return sum;
}
