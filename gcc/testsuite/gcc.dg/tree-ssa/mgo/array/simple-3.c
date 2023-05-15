/* { dg-do compile } */
/* { dg-options "-O3 -ftree-mem-gathering -fdump-tree-mgo-details" } */

/* { dg-final { scan-tree-dump "Apply mgo to dependent load" "mgo" } } */
/* { dg-final { scan-tree-dump "Create field: .*L3_val" "mgo" } } */

typedef struct C { int val; } C;
typedef struct B { C *pc; } B;
typedef struct A { B *pb; } A;

/* A simple case from pr98598 (https://gcc.gnu.org/bugzilla/show_bug.cgi?id=98598) */

int foo (int n, int m, A *pa) {
  int sum;

  for (int i = 0; i < n; i++) {
    for (int j = 0; j < m; j++) {
      sum += pa[j].pb->pc->val;  // repeated "n" times
      sum %= 7;
    }
    sum %= 13;
  }

  return sum;
}
