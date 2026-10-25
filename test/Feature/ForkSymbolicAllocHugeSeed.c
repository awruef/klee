// RUN: %clang %s -emit-llvm %O0opt -g -c -o %t.bc
// RUN: rm -rf %t.seed %t.replay
// RUN: %klee --output-dir=%t.seed --entry-point=SeedGen %t.bc
// RUN: %klee --output-dir=%t.replay --only-replay-seeds --seed-file %t.seed/test000001.ktest %t.bc 2>&1 | FileCheck %s
// RUN: ls %t.replay | not grep '\.err$'

#include "klee/klee.h"

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

void SeedGen(void) {
  uint64_t size;
  klee_make_symbolic(&size, sizeof(size), "size");
  klee_assume(size == UINT64_MAX);
}

int main(void) {
  uint64_t size;
  klee_make_symbolic(&size, sizeof(size), "size");
  void *allocation = malloc((size_t)size);
  assert(allocation == 0);
  return 0;
}

// CHECK: NOTE: found huge malloc sample, returning 0
// CHECK: KLEE: done: completed paths = 1
// CHECK: KLEE: done: partially completed paths = 0
