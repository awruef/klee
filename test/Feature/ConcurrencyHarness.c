// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.deadlock.bc
// RUN: rm -rf %t.deadlock
// RUN: %klee --output-dir=%t.deadlock %t.deadlock.bc 2>&1 | FileCheck %s --check-prefix=CHECK-DEADLOCK
// RUN: ls %t.deadlock/*.deadlock.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.blocked.bc
// RUN: rm -rf %t.blocked
// RUN: %klee --output-dir=%t.blocked %t.blocked.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.blocked/*.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.invalid-finish.bc
// RUN: rm -rf %t.invalid-finish
// RUN: %klee --output-dir=%t.invalid-finish %t.invalid-finish.bc 2>&1 | FileCheck %s --check-prefix=CHECK-INVALID-FINISH
// RUN: ls %t.invalid-finish/*.model.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.exhausted.bc
// RUN: rm -rf %t.exhausted
// RUN: %klee --output-dir=%t.exhausted %t.exhausted.bc 2>&1 | FileCheck %s --check-prefix=CHECK-EXHAUSTED
// RUN: ls %t.exhausted/*.model.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.omitted.bc
// RUN: rm -rf %t.omitted
// RUN: %klee --output-dir=%t.omitted %t.omitted.bc 2>&1 | FileCheck %s --check-prefix=CHECK-OMITTED
// RUN: ls %t.omitted/*.model.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.symbolic.bc
// RUN: rm -rf %t.symbolic
// RUN: %klee --output-dir=%t.symbolic %t.symbolic.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SYMBOLIC
// RUN: ls %t.symbolic/*.user.err

#include <stdint.h>

#include "klee/ConcurrencyHarness.h"

int main(void) {
  unsigned char choices[2];
  struct klee_concurrency_driver driver;
  uint64_t thread = UINT64_MAX;

  klee_make_symbolic(choices, sizeof(choices), "schedule_choices");
  klee_concurrency_create_thread(1);

#if CASE == 1
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x3, 2);
  klee_concurrency_driver_block(&driver, 0);
  klee_concurrency_driver_block(&driver, 1);
  (void)klee_concurrency_driver_next(&driver, &thread);
#elif CASE == 2
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x3, 1);
  klee_concurrency_driver_block(&driver, 1);
  if (klee_concurrency_driver_next(&driver, &thread) !=
          KLEE_CONCURRENCY_DRIVER_SCHEDULED ||
      thread != 0)
    klee_abort();
  klee_concurrency_driver_finish(&driver, thread);
  klee_concurrency_driver_unblock(&driver, 1);
  if (klee_concurrency_driver_next(&driver, &thread) !=
          KLEE_CONCURRENCY_DRIVER_SCHEDULED ||
      thread != 1)
    klee_abort();
  klee_concurrency_driver_finish(&driver, thread);
  if (klee_concurrency_driver_next(&driver, &thread) !=
      KLEE_CONCURRENCY_DRIVER_COMPLETE)
    klee_abort();
#elif CASE == 3
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x3, 1);
  klee_concurrency_driver_block(&driver, 0);
  klee_concurrency_driver_finish(&driver, 0);
#elif CASE == 4
  klee_concurrency_driver_init(&driver, choices, 0, 0x3, 1);
  (void)klee_concurrency_driver_next(&driver, &thread);
#elif CASE == 5
  /* Thread one is still live, so reporting only thread zero is invalid. */
  klee_concurrency_deadlock(0x1);
#elif CASE == 6
  uint64_t symbolic_mask;
  klee_make_symbolic(&symbolic_mask, sizeof(symbolic_mask), "blocked_mask");
  klee_concurrency_deadlock(symbolic_mask);
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-DEADLOCK: KLEE: ERROR: {{.*}}logical-thread deadlock: blocked mask 0x3
// CHECK-DEADLOCK: KLEE: done: partially completed paths = 1
// CHECK-CLEAN: KLEE: done: completed paths = 1
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-INVALID-FINISH: KLEE: ERROR: {{.*}}concurrency driver error: cannot finish a blocked thread
// CHECK-EXHAUSTED: KLEE: ERROR: {{.*}}concurrency driver error: schedule choices exhausted
// CHECK-OMITTED: KLEE: ERROR: {{.*}}concurrency model error: deadlock mask omits an unfinished logical thread
// CHECK-SYMBOLIC: KLEE: ERROR: {{.*}}klee_concurrency_deadlock requires a concrete blocked mask
