// RUN: %clang %s -fsanitize=vla-bound -emit-llvm -g %O0opt -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --output-dir=%t.klee-out --emit-all-errors --ubsan-runtime %t.bc 2>&1 | FileCheck %s
// P2 enumerates the bounded symbolic allocation instead of terminating the
// residual path with a model error. The ten input values therefore produce
// ten tests while preserving the pointer diagnostic on the invalid access.
// RUN: ls %t.klee-out/ | grep .ktest | wc -l | grep 10
// RUN: ls %t.klee-out/ | grep .ptr.err | wc -l | grep 1
// RUN: find %t.klee-out -maxdepth 1 -name '*.model.err' | wc -l | grep 0

#include "klee/klee.h"

int main() {
  int x;
  volatile int result;

  x = klee_range(-10, 10, "x");

  // CHECK: KLEE: ERROR: {{.*}}runtime/Sanitizer/ubsan/ubsan_handlers.cpp:{{[0-9]+}}: non-positive-vla-index
  int arr[x];
  result = arr[0];
  return 0;
}
