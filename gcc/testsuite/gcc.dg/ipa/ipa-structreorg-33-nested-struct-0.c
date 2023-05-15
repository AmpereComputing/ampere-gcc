/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <assert.h>

int
main ()
{
  struct astruct_s
  {
    _Bool _a;
    _Bool _b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field '_b' in LTO" } */
    _Bool _c;
    _Bool _d;
  };
  struct outerstruct_s
  {
    struct astruct_s a;
    struct astruct_s b;
    struct astruct_s c;
    struct astruct_s d;
  };
  struct outerstruct_s outerstruct;
  struct astruct_s a = outerstruct.a;
  struct astruct_s b = outerstruct.b;
  struct astruct_s c = outerstruct.c;
  struct astruct_s d = outerstruct.d;
  _Bool _a = a._a;
  _Bool _c = a._c;
  _Bool _d = a._d;
}
