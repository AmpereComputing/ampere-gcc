

/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-fre1" } */

extern void bar(void);
extern void bag(void);
extern void foo(void);
int g;

/* Test temporary equivalences: optimize N-ary expressions.  */

void
f (unsigned int a, unsigned int b, unsigned int x, unsigned int y)
{
  if (a == b)
    {
      g = 100;
      if (a + x == 99)
	g = x + b; /* should be simplified to 99 */
    }
  else
    // a!= b
    {
      if (a == 100 - x)
	{
	  g++;
	  if (b == 100 - x)
	    foo (); /* should be removed */
	}
      else
	{
	  g--;
	  if (b == 100 - x)
	    bag (); /* should not be removed */
	  else
	    bar (); /* should not be removed */
	}
    }
}

/* { dg-final { scan-tree-dump "bag" "fre1" } } */
/* { dg-final { scan-tree-dump "bar" "fre1" } } */
/* { dg-final { scan-tree-dump-not "foo" "fre1" } } */
/* { dg-final { scan-tree-dump-not "= b_\[0-9]+\\(\[A-Z]+\\) \\+ x_" "fre1" } } */
