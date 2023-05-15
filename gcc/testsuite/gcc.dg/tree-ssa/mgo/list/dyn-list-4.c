/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "list head_link_stmts:" "mgo" { xfail *-*-* } } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* TODO: iterator can be advanced in the target loop by any steps */

int
foo (int n)
{
  Node *head = NULL;
  int sum = 0;
  Node *iterator;

  for (int i = 0; i < n; i++)
    {
      Node *node = (Node *) calloc (1, sizeof (Node));
      node->next = head;
      head = node;
      iterator = head;

      while (iterator)
	{
	  sum += iterator->l1_l2p->l2_l3p->l3_i1;
	  sum += iterator->l1_l2p->l2_l3p->l3_l4p->l4_i2;

	  if (sum % 2)
	    iterator = iterator->next;
	  else if (sum % 3)
	    {
	      iterator = iterator->next;
	      if (iterator)
		iterator = iterator->next;
	      if (iterator)
		iterator = iterator->next;
	    }
	}
    }

  return sum;
}
