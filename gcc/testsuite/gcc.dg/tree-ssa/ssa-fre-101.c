/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-fre1" } */

extern void bar(void);
extern void bag(void);
extern void bas(void);
extern void foo(void);

void f (unsigned int a, unsigned int b)
{
  if (a == b)
    {
      for (unsigned i = a; i < 100; i++)
	{
	  if (i > b)
	    /* Should not be eliminated.  */
	    bar ();
	}
    }
}

/* Test temporary equivalences: derived condition.  */

int gg;

void g (int a, int b, int d)
{
  int c = 100;
  if (a > 0)
    {
      c = b;
      gg++;
    }
  else
    /* a <= 0 */
    {
      c = d;
      gg--;
    }
  for (int i = 0; i < c; i++)
    {
      if (a >= 0)
	{
	  if (i >= b)
	    /* Should not be eliminated. ("a >= 0" cannot derive "a > 0".)  */
	    bas ();
	}
      else
	/* a < 0 */
	{
	  if (i >= d)
	    /* Should be eliminated, as "a < 0" can derive "a <= 0".  */
	    foo ();
	}
    }
}

/* Test temporary equivalences: no domination.  */

void h (unsigned int a, unsigned int b)
{
  unsigned int c = 100;
  if (b % 2)
    {
      if (a != 0)
	c = b;
    }
  for (unsigned i = 0; i < c; i++)
    {
      if (a != 0)
	{
	  if (i >= b)
	    /* Should not be eliminated.  */
	    bag ();
	}
      i++;
    }
}

/* { dg-final { scan-tree-dump "bar" "fre1" } } */
/* { dg-final { scan-tree-dump "bas" "fre1" } } */
/* { dg-final { scan-tree-dump "bag" "fre1" } } */
/* { dg-final { scan-tree-dump-not "foo" "fre1" } } */
