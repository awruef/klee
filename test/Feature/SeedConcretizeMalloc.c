// RUN: %clang -emit-llvm -c -g %s -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --output-dir=%t.klee-out --entry-point=SeedGen %t.bc
// RUN: test -f %t.klee-out/test000001.ktest
// RUN: not test -f %t.klee-out/test000002.ktest

// RUN: rm -rf %t.klee-out-2
// This test isolates seed concretization. P2 deliberately explores additional
// non-seed sizes in normal mode, so replay only the seed here.
// RUN: %klee --output-dir=%t.klee-out-2 --only-replay-seeds --seed-file %t.klee-out/test000001.ktest %t.bc | FileCheck --allow-empty %s
// RUN: %klee-stats --print-columns 'SolverQueries' --table-format=csv %t.klee-out-2 | FileCheck --check-prefix=CHECK-STATS %s

#include "klee/klee.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

void SeedGen() {
  size_t x;
  klee_make_symbolic(&x, sizeof(x), "x");
  klee_assume(x == 100);
}

int main(int argc, char **argv) {
  size_t s;
  klee_make_symbolic(&s, sizeof(s), "size");
  char *p = (char *)malloc(s);
  if (!p)
    return 0;

  if (s != 100)
    printf("Error\n");
    // CHECK-NOT: Error

  // CHECK-STATS: 3
  // Seed-only replay constrains s to 100 without exploring the residual
  // non-seed domain; the run uses three solver queries.
}
