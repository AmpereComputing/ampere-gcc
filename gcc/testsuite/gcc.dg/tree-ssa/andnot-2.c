/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-forwprop5-raw -w -Wno-psabi" } */

typedef long vec __attribute__((vector_size(16)));
vec f(vec x){
  vec y = x < 10;
  return y & (y == 0);
}

/* { dg-final { scan-tree-dump-not "_expr" "forwprop5" } } */
