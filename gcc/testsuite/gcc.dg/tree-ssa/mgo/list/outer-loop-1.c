/* { dg-do compile { target lp64 } } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" }
 */

/* { dg-final { scan-tree-dump-not "Final mgo outer loop" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* The outer loop must be the list init loop (i.e the loop of i < n).
   The list node data must be trackable, any clobber may change list data but we
   can not re-initialized the cache data in all list nodes. */

void
bar ();

int
foo (int n, int m)
{
  Node *head = NULL;
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      bar ();
      for (int j = 0; j < m; j++)
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
	      sum += iterator->l1_l2p->l2_l3p->l3_l4p->l4_i2;
	      iterator = iterator->next;
	    }
	}
    }

  return sum;
}
