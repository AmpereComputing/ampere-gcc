// { dg-do compile }
// { dg-options "-O3 -flto-partition=one -fipa-struct-reorg -fdump-ipa-all -fwhole-program" }

struct a
{
  int t, t1;
};

static struct a *b;

void *xmalloc(int);


void f(void)
{
  b = xmalloc (sizeof(*b));
}

int g(void)
{
  return b->t;
}

int main()
{
  f ();
  return g ();
}

/* { dg-final { scan-ipa-dump "No structures to transform." "struct_reorg" } } */
