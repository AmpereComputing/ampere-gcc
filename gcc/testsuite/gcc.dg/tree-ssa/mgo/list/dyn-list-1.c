/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump-not "list head_link_stmts:" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* Unsupported iterator: each list node should be the same size of node type */

int
foo (int n)
{
  Node *head = NULL;
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      /* Add a new node to the list head */
      Node *node = (Node *) calloc (1, sizeof (Node) + 1);
      node->next = head;
      head = node;

      Node *iterator = head;

      while (iterator)
	{
	  sum += iterator->l1_l2p->l2_l3p->l3_i1;
	  sum += iterator->l1_l2p->l2_l3p->l3_l4p->l4_i2;
	  iterator = iterator->next;
	}
    }

  return sum;
}
