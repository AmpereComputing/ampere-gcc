/* { dg-options "-O3 -ftree-cond-sinking -fdump-tree-cond-sinking-details" } */

extern int printf (const char *, ...);

__attribute__((noinline)) int f(int x)
{
  return 2*x;
}

int a[2] = {0, 1};

__attribute__((noinline)) void g(int b, int c, int d)
{
  int i = 99;
  if (d<2) {
    for (i=0; i<c; i++) {
      if ((f(a[1]+i)>>2)>4)
        break;
      if (((b+i)%8)>4)
        break;
    }
  }
  printf("%d done\n", i);
}

int main(void)
{
  g(1,5,1);
  g(1,5,2);
  g(0,5,3);
  g(0,100,1);
  g(100,100,1);
  g(100,1,1);

  return 0;
}

/* { dg-final { scan-tree-dump "CSO: Cleanup block" "cond-sinking" } } */
