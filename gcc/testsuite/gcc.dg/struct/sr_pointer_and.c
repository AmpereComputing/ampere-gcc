/* { dg-do compile } */

struct test {long val; struct test* next; };

unsigned long P_DATA;

void func (struct test*);

__attribute__((used)) static void
foo (struct test* pt)
{
  struct test t;

  t.next = (void *)((unsigned long)pt->next & P_DATA);
  func(&t);
  return;
}
