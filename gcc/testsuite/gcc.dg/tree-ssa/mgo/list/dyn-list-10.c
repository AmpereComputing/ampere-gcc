/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "iterator found in loop" "mgo" } } */
/* { dg-final { scan-tree-dump "list head_link_stmts:" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* The number of list elements is not necessary */

int
foo (int n, int m)
{
  Node *head = NULL;
  int sum = 0;

  for (int i = 0; i < n; i++)
    {
      for (int k = 0; k < m; k++)
	{
	  int dep_k = k % 3 ? k / 2 : k / 3;
	  for (int l = 0; l < dep_k; l++)
	    {
	      Node *temp = (Node *) calloc (1, sizeof (Node));
	      temp->next = head;
	      head = temp;
	    }
	}

      Node *iterator = head;

      while (iterator)
	{
	  sum += iterator->l1_l2p->l2_l3p->l3_i1;
	  iterator = iterator->next;
	}
    }

  return sum;
}
