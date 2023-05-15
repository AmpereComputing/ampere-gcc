/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "list head_link_stmts:" "mgo" { xfail *-*-* } } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* Currently not supported: if list is initialized in the outermost loop (i.e. func) */

int
foo (int n)
{
  Node *head = (Node *) calloc (1, sizeof (Node));

  int sum = 0;
  Node *iterator;

  for (int i = 0; i < n; i++)
    {
      Node *node = (Node *) malloc (sizeof (Node));
      node->next = head;
      iterator = head = node;

      while (iterator)
	{
	  sum += iterator->l1_l2p->l2_l3p->l3_i1;
	  sum += iterator->l1_l2p->l2_l3p->l3_l4p->l4_i2;
	  iterator = iterator->next;
	}
    }

  return sum;
}
