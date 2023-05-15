/* { dg-options "-O3 -ftree-cond-sinking -fdump-tree-cond-sinking-details" } */

extern int printf (const char *, ...);

__attribute__((noinline)) int f(int x)
{
  return 2*x;
}

int a[2] = {0, 1};

void g(int b, int c)
{
  int x;

  x = 1;
  if (f(a[1])) {
    for (int i=0; i<10; i++) {
      if (b)
        break;
      else {
        x = 2;
        if (c == 1)
          printf("case1 %d\n", x);
        else
          continue;
      }
    }
  }
  printf("%d done\n", x);
}

int main(void)
{
  g(1,1);
  g(1,2);
  g(0,0);
  g(0,1);
  a[1]=0;
  g(1,1);
  g(1,2);
  g(0,0);
  g(0,1);

  return 0;
}

/* { dg-final { scan-tree-dump "CSO: Cleanup block" "cond-sinking" } } */
