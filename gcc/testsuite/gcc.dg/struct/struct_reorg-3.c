// { dg-do compile }
// { dg-options "-O3 -flto-partition=one -fipa-struct-reorg -fdump-ipa-all -fwhole-program" }

#include <stdlib.h>
typedef struct {
   long laststart_offset;
   unsigned regnum;
} compile_stack_elt_t;
typedef struct {
   compile_stack_elt_t *stack;
   unsigned size;
} compile_stack_type;
__attribute__((noinline)) void f (const char *p, const char *pend, int c)
{
  compile_stack_type compile_stack;
  while (p != pend)
    if (c)
      compile_stack.stack = realloc (compile_stack.stack,
				     (compile_stack.size << 1)
				       * sizeof (compile_stack_elt_t));
}

int main()
{
  f (NULL, NULL, 1);
}

/* { dg-final { scan-ipa-dump "Number of structures to transform is 1" "struct_reorg" } } */
