/* { dg-do run } */
/* { dg-options "-O3 -fwhole-program -flto-partition=one -fipa-struct-reorg -fdump-ipa-struct_reorg-details" } */

#include <stdlib.h>

struct testg {
  int b;
  float c;
};

testg *testgvar;
int main ()
{
  testgvar = (testg*) calloc(10, sizeof(testg));
  int b = testgvar->b;
  return b;
}
