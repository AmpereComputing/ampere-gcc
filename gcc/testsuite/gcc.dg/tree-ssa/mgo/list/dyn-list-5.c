/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "list head_link_stmts:" "mgo" { xfail *-*-* } } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* Currently not supported iterator: a new element may be not added from head */

int
foo (int n)
{
  Node *head = NULL, *tail = NULL;
  int sum = 0;
  Node *iterator;

  for (int i = 0; i < n; i++)
    {
      Node *node = (Node *) calloc (1, sizeof (Node));
      if (head == NULL)
	head = tail = node;
      else if (n % 3)
	{
	  // add to tail
	  tail->next = node;
	  tail = node;
	}
      else if (n % 5)
	{
	  // add in middle
	  node->next = head->next;
	  head->next = node;
	}
      else
	{
	  // add to head
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

  return sum;
}
