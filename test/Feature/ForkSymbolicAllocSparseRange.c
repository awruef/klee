// RUN: %clang %s -emit-llvm %O0opt -g -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: env KLEE_DEBUG_ENUM=1 %klee --max-size-concretizations=5 --size-enumeration-strategy=range --output-dir=%t.klee-out %t.bc 2>&1 | FileCheck %s
// RUN: ls %t.klee-out | not grep '\.err$'

#include "klee/klee.h"

#include <stdint.h>
#include <stdlib.h>

int main(void) {
  uint8_t size;
  klee_make_symbolic(&size, sizeof(size), "size");
  klee_assume((size == 2) | (size == 3) | (size == 5) | (size == 7) |
              (size == 11) | (size == 13));

  void *allocation = malloc(size);
  if (allocation)
    free(allocation);
  return 0;
}

// The range samples include the infeasible value 9. It must not consume the
// fifth slot, which is then available for the remaining feasible value 11.
// CHECK: size-enum range: lo=3 hi=13 candidates: 3 13 5 7 9
// CHECK: KLEE: done: completed paths = 6
// CHECK: KLEE: done: partially completed paths = 0
