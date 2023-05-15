/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stddef.h>
#include <stdio.h>

int
main (int argc, char **argv)
{
  struct astruct_s
  {
    _Bool a;
    _Bool b;
    _Bool c;
  };
  union outer
  {
    struct astruct_s a;
    double b;
  };
  union outer an_outer;
}

