/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-fre1" } */

extern void bar(void);
extern void boo(void);
extern void foo(void);

/* Test temporary equivalences: basic.  */

void f (unsigned int a, unsigned int b)
{
  if (a == b)
    {
      for (unsigned i = 0; i < a; i++)
	{
	  bar ();
	  if (i >= b)
	    /* Unreachable.  */
	    foo ();
	}
    }
}

/* Test temporary equivalences: transitive.  */

void g (unsigned int a, unsigned int b, unsigned int c)
{
  for (unsigned i = 0; i < c; i++)
    {
      if (a == b)
	{
	  if (b == c)
	    {
	      boo ();
	      if (i >= a)
		/* Unreachable.  */
		foo ();
	    }
	}
    }
}

/* { dg-final { scan-tree-dump-not "foo" "fre1" } } */
/* { dg-final { scan-tree-dump "bar" "fre1" } } */
/* { dg-final { scan-tree-dump "boo" "fre1" } } */
