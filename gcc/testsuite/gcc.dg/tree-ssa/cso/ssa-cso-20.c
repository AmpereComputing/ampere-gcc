/* { dg-options "-O3 -ftree-cond-sinking -fdump-tree-cond-sinking-details" } */

extern int printf (const char *, ...);

__attribute__((noinline)) int f(int x)
{
  return 2*x;
}

int a[2] = {0, 1};

void g(int *b, int c)
{
  if (f(a[1])) {
    if (b[c] == 1) {
      printf("case1\n");
    } else if (b[c] == 2) {
      printf("case2\n");
    }
  }
  printf("done\n");
}

int main(void)
{
  int b[3] = {1,2,3};
  g(b,0);
  g(b,1);
  g(b,2);
  a[1]=0;
  g(0,4);

  return 0;
}

/* { dg-final { scan-tree-dump-not "CSO: Cleanup block" "cond-sinking" } } */
