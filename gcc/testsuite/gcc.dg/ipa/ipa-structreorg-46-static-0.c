/* { dg-do run } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof -fipa-dlo-tests" } */

#include <assert.h>
#include <stddef.h>

struct a_s
{
  _Bool a;
  _Bool b;  /* { dg-warning "RECORD TYPE 'struct a_s' has dead field 'b' in LTO" } */
  _Bool c;
};

static struct a_s a_t;

int
main ()
{
  _Bool *a = &(a_t.a);
  _Bool *c = &(a_t.c);
  ptrdiff_t diff = c - a;
  assert (diff == 1);
}
