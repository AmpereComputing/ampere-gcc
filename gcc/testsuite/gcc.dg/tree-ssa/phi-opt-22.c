/* PR tree-optimization/97690 */
/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-phiopt3" } */

int foo (_Bool d) { return d ? 2 : 0; }
int bar (_Bool d) { return d ? 1 : 0; }
int baz (_Bool d) { return d ? -__INT_MAX__ - 1 : 0; }
int qux (_Bool d) { return d ? 1024 : 0; }

/* { dg-final { scan-tree-dump-not "if" "phiopt3" } } */
/* { dg-final { scan-tree-dump-times " << " 3 "phiopt3" } } */
