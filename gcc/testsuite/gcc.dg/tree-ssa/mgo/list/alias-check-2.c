/* { dg-do compile { target lp64 } } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Pruning" "mgo" } } */

/* { dg-final { scan-tree-dump "Create field: .*L3_l3_i1" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L3_l3_l4p" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* Prune dep load due to an alias store */

int
foo (int n)
{
  Node *head = NULL;
  int a = 5;
  L4 *other_l4p = NULL;
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
	  /* Dependent loads are accessed multiple times */
	  sum += iterator->l1_l2p->l2_l3p->l3_i1;

	  if (sum % 13)
	    {
	      other_l4p = iterator->l1_l2p->l2_l3p->l3_l4p;
	      other_l4p->l4_i2 = 1;
	    }

	  sum += iterator->l1_l2p->l2_l3p->l3_l4p->l4_i2;
	  iterator = iterator->next;
	}
    }

  return sum;
}
