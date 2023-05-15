/* { dg-do run } */
/* { dg-options  "-w -fipa-dead-field-elimination -flto -flto-partition=none -fipa-sizeof" } */

#include <stdint.h>
union a
{
  int8_t b
} c () { union a d = {4073709551608}; }
main () {}
