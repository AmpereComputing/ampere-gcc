/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-pre" } */

extern void foo(void);
extern void bag(void);
extern void bas(void);

/* Test temporary equivalences: identical condition.  */

void h (int a, int b, int x, int y)
{
  int c = y;
  if (a != 0)
    c = x;
  while (b < 1000)
    {
      if (a != 0)
	{
	  if (c > x)
	    /* Unreachable.  */
	    foo ();
	}
      else
	bas ();
      b++;
    }
}

/* Test temporary equivalences: derived condition.  */

void k (int a, int b, int x, int y)
{
  int c = y;
  if (a != b)
    c = x;
  for (int i = 0; i < 1000; i++)
    {
      if (a < b)
	/* All paths reaching "a>0 is true" come from "a!=0 is true".  */
	{
	  if (c > x)
	    /* Unreachable.  */
	    foo ();
	}
      else
	bag ();
    }
}

/* { dg-final { scan-tree-dump-not "foo \\(\\)" "pre" } } */
/* { dg-final { scan-tree-dump "bag" "pre" } } */
/* { dg-final { scan-tree-dump "bas" "pre" } } */