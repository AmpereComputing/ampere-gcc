/* { dg-do compile { target lp64 } } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Cache element size is 8 bytes" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* Cache fields are appended to the original fields in the extended list element */

int
foo (int n)
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
	  sum += iterator->l1_l2p->l2_l3p->l3_ca[0];
	  sum += iterator->l1_l2p->l2_l3p->l3_i1;
	  sum += iterator->l1_l2p->l2_l3p->l3_ca[2];
	  iterator = iterator->next;
	}
    }

  return sum;
}
