/* { dg-do compile } */
/* { dg-options "-std=gnu++17 -Wno-builtin-declaration-mismatch -O3 -fwhole-program -flto-partition=one -fipa-struct-reorg -S" } */

struct S {
    int x;
    double y;
};
S f();

const auto [x0, y0] = f();
const auto [x1, y1] = f();

static union {
int a;
double b;
};

const auto [x2, y2] = f();
