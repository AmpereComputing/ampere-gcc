/* { dg-do run } */

extern void abort (void);

struct S
{
  int b;
  int *c;
};
static int d, e;

static struct S s;

static int *
__attribute__((noinline, const))
foo (void)
{
  return &s.b;
}

int *
__attribute__((noinline))
bar (int **f)
{
  s.c = &d;
  *f = &e;
  /* As nothing ever takes the address of any int * field in struct S,
     the write to *f can't alias with the s.c field.  */
  return s.c;
}

int
__attribute__((noinline))
baz (int *x)
{
  s.b = 1;
  *x = 4;
  /* Function foo takes address of an int field in struct S,
     so *x can alias with the s.b field (and it does in this testcase).  */
  return s.b;
}

int
__attribute__((noinline))
t (void)
{
  int *f = (int *) 0;
  return 10 * (bar (&f) != &d) + baz (foo ());
}

int
main (void)
{
  if (t () != 4)
    abort ();
  return 0;
}

/* { dg-final { scan-ipa-dump "No structures to transform." "struct_reorg" } } */
