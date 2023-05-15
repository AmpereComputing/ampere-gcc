/* { dg-do link } */
/* { dg-options  "-Wdfa -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stddef.h>
#include <stdio.h>

int
main (int argc, char **argv)
{
  char *filename = "helloworld.txt";
  FILE *f = fopen (filename, "r");
  fclose (f);
}

