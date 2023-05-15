/* { dg-do compile } */
/* { dg-options "-O3 -fwhole-program -flto-partition=one -fipa-struct-reorg -fdump-ipa-struct_reorg-details -S" } */

struct Foo { int foo; int a; };
Foo& ignoreSetMutex = *(new Foo);

struct Goo { int goo; int a; };

int main ()
{
  Goo* a;
  return a->goo = 90;
}
