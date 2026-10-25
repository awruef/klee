// RUN: %clang %s -emit-llvm %O0opt -g -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --output-dir=%t.klee-out %t.bc 2>&1 | FileCheck %s --check-prefix=CHECK-EXEC
// RUN: %ktest-tool %t.klee-out/test000001.ktest > %t.ktest
// RUN: FileCheck %s --check-prefix=CHECK-KTEST --input-file=%t.ktest
// RUN: rm -rf %t.seed-reject %t.replay-reject
// RUN: not %klee --output-dir=%t.seed-reject --seed-file %t.klee-out/test000001.ktest %t.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SEED-REJECT
// RUN: not %klee --output-dir=%t.replay-reject --replay-ktest-file=%t.klee-out/test000001.ktest %t.bc 2>&1 | FileCheck %s --check-prefix=CHECK-REPLAY-REJECT

#include "klee/klee.h"

#include <assert.h>
#include <stdlib.h>

char global_buffer[4] = {'A', 'B', 'C', 'D'};

static void check_suffix(const char *buffer) {
  assert(buffer[2] == 'C');
  assert(buffer[3] == 'D');
}

int main(void) {
  char stack_buffer[4] = {'A', 'B', 'C', 'D'};
  char zero_buffer[4] = {'A', 'B', 'C', 'D'};
  char *heap_buffer = malloc(4);
  assert(heap_buffer != 0);
  heap_buffer[0] = 'A';
  heap_buffer[1] = 'B';
  heap_buffer[2] = 'C';
  heap_buffer[3] = 'D';

  klee_make_symbolic(stack_buffer, 2, "stack_prefix");
  klee_make_symbolic(heap_buffer, 2, "heap_prefix");
  klee_make_symbolic(global_buffer, 2, "global_prefix");
  klee_make_symbolic(zero_buffer, 0, "zero_prefix");

  assert(klee_is_symbolic(stack_buffer[0]));
  assert(klee_is_symbolic(heap_buffer[0]));
  assert(klee_is_symbolic(global_buffer[0]));
  assert(!klee_is_symbolic(zero_buffer[0]));

  check_suffix(stack_buffer);
  check_suffix(heap_buffer);
  check_suffix(global_buffer);
  assert(zero_buffer[0] == 'A');
  assert(zero_buffer[1] == 'B');
  check_suffix(zero_buffer);

  free(heap_buffer);
  return 0;
}

// CHECK-EXEC: KLEE: done: completed paths = 1
// CHECK-EXEC: KLEE: done: partially completed paths = 0
// CHECK-KTEST-DAG: name: 'stack_prefix'
// CHECK-KTEST-DAG: name: 'heap_prefix'
// CHECK-KTEST-DAG: name: 'global_prefix'
// CHECK-KTEST-NOT: name: 'zero_prefix'
// CHECK-SEED-REJECT: prefix symbolication does not support seeding
// CHECK-REPLAY-REJECT: prefix symbolication does not support KTest replay
