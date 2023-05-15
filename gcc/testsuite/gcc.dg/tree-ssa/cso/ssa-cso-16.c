/* { dg-options "-O3 -ftree-cond-sinking -fdump-tree-cond-sinking-details" } */

extern int printf (const char *, ...);

__attribute__((noinline)) int f(int x)
{
  return 2*x;
}

__attribute__((noinline)) int m(int x)
{
  return 3*x;
}

int a[2] = {0, 1};
void g(int b, int c)
{
  int x = 1;
  if (f(a[1])) {
    x = 2;
    if (c == 1) {
      printf("case1 %d\n", x);
    } else if (c == 2) {
      printf("case2 %d\n", x);
    }
  }
  printf("%d done\n", m(x));
}

int main(void)
{
  g(1,1);
  g(1,2);
  g(0,1);
  a[1]=0;
  g(1,1);

  return 0;
}

/* { dg-final { scan-tree-dump-not "CSO: Cleanup block" "cond-sinking" } } */
