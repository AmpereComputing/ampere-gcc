/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "iterator found in loop" "mgo" } } */
/* { dg-final { scan-tree-dump "list head_link_stmts:" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* iterator can be initialized from any list node */

int
foo (int n)
{
  Node *head = NULL;
  int sum = 0;
  Node *iterator;

  for (int i = 0; i < n; i++)
    {
      if (i % 2)
	{
	  Node *node = (Node *) calloc (1, sizeof (Node));
	  node->next = head;
	  head = node;
	  iterator = head;
	}
      else if (i % 3)
	iterator = head->next->next;
      else
	iterator = head->next;

      while (iterator)
	{
	  sum += iterator->l1_l2p->l2_l3p->l3_i1;
	  sum += iterator->l1_l2p->l2_l3p->l3_l4p->l4_i2;
	  iterator = iterator->next;
	}
    }

  return sum;
}
