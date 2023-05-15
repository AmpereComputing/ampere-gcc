/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "iterator found in loop" "mgo" } } */
/* { dg-final { scan-tree-dump "list head_link_stmts:" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* There can be multiple allocs */

int
foo (int n)
{
  int sum = 0;
  Node *iterator;

  for (int i = 0; i < n; i++)
    {
      Node *head = (Node *) calloc (1, sizeof (Node));

      for (int j = 0; j < n; j++)
	{
	  Node *node = (Node *) malloc (sizeof (Node));
	  node->next = head;
	  head = node;

	  if (sum % 3)
	    {
	      Node *node = (Node *) calloc (1, sizeof (Node));
	      node->next = head;
	      head = node;
	    }

	  iterator = head;

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
