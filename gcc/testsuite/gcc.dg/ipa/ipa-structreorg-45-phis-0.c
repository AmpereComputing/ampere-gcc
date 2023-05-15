/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

struct a
{
  struct a_inner *b; /* { dg-warning "RECORD TYPE 'struct a' has dead field 'b' in LTO" } */
} c (struct a *d, struct a *e)
{
  while (e)
    d = d;
}
int
main ()
{}

