// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.bypass.bc
// RUN: rm -rf %t.bypass
// RUN: %klee --output-dir=%t.bypass %t.bypass.bc 2>&1 | FileCheck %s --check-prefix=CHECK-BYPASS
// RUN: ls %t.bypass/*.model.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.reselect.bc
// RUN: rm -rf %t.reselect
// RUN: %klee --output-dir=%t.reselect %t.reselect.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.reselect/*.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.blocked.bc
// RUN: rm -rf %t.blocked
// RUN: %klee --output-dir=%t.blocked %t.blocked.bc 2>&1 | FileCheck %s --check-prefix=CHECK-BLOCKED
// RUN: ls %t.blocked/*.model.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.finish.bc
// RUN: rm -rf %t.finish
// RUN: %klee --output-dir=%t.finish %t.finish.bc 2>&1 | FileCheck %s --check-prefix=CHECK-FINISH
// RUN: ls %t.finish/*.model.err

/* Once the scheduler has made a decision, klee_concurrency_set_thread may
 * only re-select the active thread. Direct selection of another thread would
 * bypass the preemption bound, the choice bytes, and declaration checks.
 * Blocked threads can be neither selected nor finished. */
#include <stdint.h>

#include "klee/klee.h"

static int shared;

int main(void) {
  klee_concurrency_create_thread(1);
#if CASE == 1
  if (klee_concurrency_schedule(0x3, 0, 1) != 0)
    klee_abort();
  klee_concurrency_set_thread(1);
#elif CASE == 2
  if (klee_concurrency_schedule(0x3, 0, 1) != 0)
    klee_abort();
  klee_concurrency_set_thread(0);
  klee_concurrency_write(&shared, sizeof(shared), 100);
#elif CASE == 3
  klee_concurrency_block(1, 0, 0);
  klee_concurrency_set_thread(1);
#elif CASE == 4
  klee_concurrency_block(0, 0, 0);
  klee_concurrency_finish_thread();
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-BYPASS: KLEE: ERROR: {{.*}}concurrency model error: direct logical thread selection after scheduling began
// CHECK-CLEAN: KLEE: done: completed paths = 1
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-BLOCKED: KLEE: ERROR: {{.*}}concurrency model error: selected logical thread is blocked
// CHECK-FINISH: KLEE: ERROR: {{.*}}concurrency model error: blocked logical thread cannot finish
