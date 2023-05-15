/* { dg-do compile { target lp64 } } */
/* { dg-options "-O3 -ftree-mem-gathering -fno-tree-pre -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "iterator found in loop" "mgo" } } */
/* { dg-final { scan-tree-dump "list head_link_stmts:" "mgo" } } */

/* { dg-final { scan-tree-dump "Apply mgo to dependent load" "mgo" } } */
/* { dg-final { scan-tree-dump "root" "mgo" } } */
/* { dg-final { scan-tree-dump "iterator" "mgo" } } */
/* { dg-final { scan-tree-dump "level 1 .*not cached" "mgo" } } */
/* { dg-final { scan-tree-dump "->l1_l2p" "mgo" } } */
/* { dg-final { scan-tree-dump "level 2 .*not cached" "mgo" } } */
/* { dg-final { scan-tree-dump "->l2_l3p" "mgo" } } */
/* { dg-final { scan-tree-dump "level 3:" "mgo" } } */
/* { dg-final { scan-tree-dump "->l3_i1" "mgo" } } */
/* { dg-final { scan-tree-dump "level 4:" "mgo" } } */
/* { dg-final { scan-tree-dump "->l4_i2" "mgo" } } */

/* { dg-final { scan-tree-dump "Create field: .*L3_l3_i1" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L4_l4_i2" "mgo" } } */
/* { dg-final { scan-tree-dump "Cache element size is 16 bytes" "mgo" } } */

/* { dg-final { scan-tree-dump "Replaced original list element def" "mgo" } } */
/* { dg-final { scan-tree-dump "calloc \\(1, 24\\)" "mgo" } } */
/* { dg-final { scan-tree-dump "with extended element def" "mgo" } } */
/* { dg-final { scan-tree-dump "calloc \\(1, 40\\)" "mgo" } } */

/* { dg-final { scan-tree-dump "Use new value: .*L3_l3_i1.* to replace origin dep load" "mgo" } } */
/* { dg-final { scan-tree-dump "Use new value: .*L4_l4_i2.* to replace origin dep load" "mgo" } } */

#include <stdlib.h>
#include "../mgo-common.h"

/* A simple case of creating a list and traversing from head */

int
foo (int n)
{
  Node *head = NULL;
  int sum = 0;

  for (int i = 0; i < n; i++)
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

  return sum;
}
