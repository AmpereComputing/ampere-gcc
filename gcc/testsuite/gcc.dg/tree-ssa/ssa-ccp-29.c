/* { dg-do compile } */
/* { dg-options "-O -fdump-tree-ccp3" } */

static double num;
int foo (void)
{
  return *(unsigned *)&num;
}

/* { dg-final { scan-tree-dump "return 0;" "ccp3" } } */
