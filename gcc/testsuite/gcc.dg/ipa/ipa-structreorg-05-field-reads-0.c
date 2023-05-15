/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

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
  _Bool a = astruct.a;
  _Bool c = astruct.c;
  return 0;
}

