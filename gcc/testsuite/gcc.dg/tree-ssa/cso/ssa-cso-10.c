/* { dg-options "-O3 -ftree-cond-sinking -fdump-tree-cond-sinking-details" } */

extern int printf (const char *, ...);

__attribute__((noinline)) int f(int x)
{
  return 2*x;
}

int a[2] = {0, 1};

void g(int b, int c)
{
  if (f(a[1])) {
    for (int i=0; i<10; i++) {
      if (b)
        break;
      else {
        if (c == 1)
          printf("case1\n");
        else
          continue;
      }
    }
  }
  printf("done\n");
}

int main(void)
{
  g(1,1);
  g(1,2);
  g(0,0);
  g(0,1);

  return 0;
}

/* { dg-final { scan-tree-dump "CSO: Cleanup block" "cond-sinking" } } */
