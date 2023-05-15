/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

struct a
{
  struct b *b; /* { dg-warning "RECORD TYPE 'struct a' has dead field 'b' in LTO" } */
} c (struct a *d)
{
  while (d)
    ;
}
void
main ()
{}

