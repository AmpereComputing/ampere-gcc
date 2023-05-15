/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

#include <assert.h>

int
main ()
{
  struct astruct_s
  {
    _Bool a;
    _Bool b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
    _Bool c;
  };
  struct astruct_s astruct;
  struct astruct_s *astruct_p = &astruct;
  astruct_p->c = 1;
  _Bool *a = &(astruct.a);
  _Bool *c_ptr = &(astruct.c);
  _Bool *c = a + 1;
  assert (*c == *c_ptr);
  return 0;
}
