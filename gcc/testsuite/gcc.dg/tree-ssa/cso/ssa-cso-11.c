/* { dg-options "-O3 -ftree-cond-sinking -fdump-tree-cond-sinking-details" } */

extern int printf (const char *, ...);

__attribute__((noinline)) int f(int x)
{
  return 2*x;
}

int a[2] = {0, 1};

void g(int b, int c, int d)
{
  d = b ? c*2 : c<<2;
  if (f(a[1] + d)) {
    if (c == 1) {
      printf("case1\n");
    } else if (c == 2) {
      printf("case2\n");
    }
  }
  printf("done\n");
}

int main(void)
{
  g(1,1,0);
  g(1,2,1);
  g(0,1,0);
  g(0,1,1);

  return 0;
}

/* { dg-final { scan-tree-dump "CSO: Cleanup block" "cond-sinking" } } */
