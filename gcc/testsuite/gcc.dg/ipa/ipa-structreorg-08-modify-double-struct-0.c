/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

#include <assert.h>
#include <stdio.h>
int
main ()
{
  struct inner_s
  {
    _Bool a;
    _Bool b;
    _Bool c;
    _Bool d;
  };
  struct astruct_s
  {
    struct inner_s a;
    struct inner_s b;  /* { dg-warning "RECORD TYPE 'struct astruct_s' has dead field 'b' in LTO" } */
    struct inner_s c;
    struct inner_s d;
  };
  struct astruct_s astruct;
  // printf("%d %d %d\n", &astruct.a, &astruct.c, &astruct.d);
  struct inner_s *a_ptr = &(astruct.a);
  struct inner_s *c_ptr = &(astruct.c);
  struct inner_s *d_ptr = &(astruct.d);
  printf ("%d %d %d %d\n", a_ptr->a, a_ptr->b, a_ptr->c, a_ptr->d);
  struct inner_s *c_ptr_2 = a_ptr + 1;
  struct inner_s *a_ptr_2 = d_ptr - 2;
  assert (c_ptr_2 == c_ptr);
  assert (a_ptr == a_ptr_2);
}
