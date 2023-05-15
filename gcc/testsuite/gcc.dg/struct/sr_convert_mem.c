/* { dg-do compile } */

struct T1 {
  long var1;
  int  var2;
};

struct T2 {
  long var1;
  int  var2;
};

void test (void*);

__attribute__((used)) void
foo (struct T2 *t2)
{
  struct T1* t1 = (void *)(&t2[1]);
  void*  data   = (void *)(&t1[1]);

  test(data);
  return;
}
