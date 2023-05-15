/* { dg-options "-O3 -ftree-cond-sinking -fdump-tree-cond-sinking-details" } */

extern int printf (const char *, ...);

__attribute__((noinline)) int f(int x)
{
  return 2*x;
}

int a[2] = {0, 1};

void g(int b, int c)
{
  if (b) {
    if (f(a[1])) {
      if (c == 2) {
        goto B5;
      } else if (c == 1) {
        printf("case5\n");
      }
    }
  } else {
    printf("case3\n");
  }
  printf("case4\n");
B5:
  printf("done\n");
}

int main(void)
{
  g(1,1);
  g(1,2);
  g(1,3);
  g(0,1);

  return 0;
}

/* { dg-final { scan-tree-dump "CSO: Cleanup block" "cond-sinking" } } */
