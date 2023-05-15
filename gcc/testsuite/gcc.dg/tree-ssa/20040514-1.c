/* { dg-do compile } */
/* { dg-options "-O1 -fdump-tree-phiopt3-details" } */

int t( int i)
{
  int j;
  if(i ==0)
  {
   j = 1;
   goto end;
  }
  j = 0;
end:
  return j;
}

/* Should have no ifs left after straightening.  */
/* { dg-final { scan-tree-dump-times "if " 0 "phiopt3"} } */
