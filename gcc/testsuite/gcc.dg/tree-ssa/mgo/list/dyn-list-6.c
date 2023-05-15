/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "iterator found in loop" "mgo" } } */
/* { dg-final { scan-tree-dump "list head_link_stmts:" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* The list can have multiple heads */

int
foo (int n, int m)
{
  Node *head1 = NULL;
  Node *head2 = NULL;
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      Node *node = (Node *) calloc (1, sizeof (Node));
      Node *head = sum % 3 ? head1 : head2;

      node->next = head;
      head = node;

      if (sum % 7)
	head1 = head;
      else
	head2 = head;

      for (int j = 0; j < m; j++)
	{
	  Node *iterator = head;

	  while (iterator)
	    {
	      sum += iterator->l1_l2p->l2_l3p->l3_i1;
	      sum += iterator->l1_l2p->l2_l3p->l3_l4p->l4_i2;
	      iterator = iterator->next;
	    }
	}
    }

  return sum;
}
