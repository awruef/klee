// REQUIRES: x86_64
// RUN: %clang %s -emit-llvm %O0opt -g -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: env KLEE_DEBUG_ENUM=1 %klee --max-time=10s --watchdog --max-size-concretizations=1 --size-enumeration-strategy=range --output-dir=%t.klee-out %t.bc 2>&1 | FileCheck %s

#include "klee/klee.h"

#include <stdint.h>
#include <stdlib.h>

int main(void) {
  uint64_t raw;
  klee_make_symbolic(&raw, sizeof(raw), "raw");

  // STP's zero model makes the first example UINT64_MAX; KLEE's small-example
  // heuristic reduces that example while leaving both range endpoints in the
  // remainder. The upper-midpoint search must therefore handle [0, UINT64_MAX].
  void *allocation = malloc((size_t)~raw);
  if (allocation)
    free(allocation);
  return 0;
}

// CHECK: size-enum range: lo=0 hi=18446744073709551615
// CHECK: KLEE: done:
