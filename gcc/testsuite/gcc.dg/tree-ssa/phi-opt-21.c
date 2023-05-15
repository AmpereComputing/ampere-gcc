/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-phiopt5-details" } */

int f(unsigned s)
{
  int i;
  for (i = 0; i < s; ++i)
    ;

  return i;
}

/* { dg-final { scan-tree-dump "converted to straightline code" "phiopt5" } } */
/* Make sure we fold the detected MAX<s, 0>.  */
/* { dg-final { scan-tree-dump-not "MAX" "phiopt5" } } */
