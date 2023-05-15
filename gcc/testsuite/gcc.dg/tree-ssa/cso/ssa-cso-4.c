/* { dg-options "-O3 -ftree-cond-sinking -fdump-tree-cond-sinking-details" } */

extern int printf (const char *, ...);

__attribute__((noinline)) int f1(int x)
{
  return 2*x;
}

__attribute__((noinline)) int f2(int x)
{
  return 2*x;
}

int a[2] = {1, 2};

__attribute__((noinline)) void m(void)
{
  a[1] *= 2;
}

void g(int b1, int b2, int c1, int c2)
{
  if (f1(a[1])) {
    if (b1) {
      if (c1 == 1) {
        printf("case1\n");
      } else if (c2 == 2) {
        printf("case2\n");
      }
    }
  }
  printf("done1\n");

  m();

  if (f2(a[0])) {
    if (b2) {
      if (c2 == 1) {
        printf("case3\n");
      } else if (c2 == 2) {
        printf("case4\n");
      }
    }
  }
  printf("done2\n");
}

int main(void)
{
  g(1,1,1,1);
  g(1,2,1,2);
  g(0,1,0,1);

  return 0;
}

/* { dg-final { scan-tree-dump "CSO: Cleanup block" "cond-sinking" } } */
