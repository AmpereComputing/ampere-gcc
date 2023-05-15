// { dg-do run }

#include <assert.h>

struct a
{
  int t;
  int t1;
};

__attribute__((noinline)) int f(int i, int j)
{
  struct a *t;
  struct a t1 = {i, j};
  t = &t1;
  auto int g(void) __attribute__((noinline));
  int g(void)
  {
    return t->t + t->t1;
  }
  return g();
}

int main()
{
  assert (f(1, 2) == 3);
}

/* { dg-final { scan-ipa-dump "Number of structures to transform is 2" "struct_reorg" } } */
