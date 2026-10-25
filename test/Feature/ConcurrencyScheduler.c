// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.fork.bc
// RUN: rm -rf %t.fork
// RUN: %klee --emit-all-errors --output-dir=%t.fork %t.fork.bc 2>&1 | FileCheck %s --check-prefix=CHECK-FORK
// RUN: find %t.fork -name '*.race.err' | count 2
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.bound.bc
// RUN: rm -rf %t.bound
// RUN: %klee --emit-all-errors --output-dir=%t.bound %t.bound.bc 2>&1 | FileCheck %s --check-prefix=CHECK-BOUND
// RUN: find %t.bound -name '*.race.err' | count 2
// RUN: find %t.bound -name '*.early' | count 0
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.single.bc
// RUN: rm -rf %t.single
// RUN: %klee --output-dir=%t.single %t.single.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SINGLE
// RUN: not ls %t.single/*.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.invalid.bc
// RUN: rm -rf %t.invalid
// RUN: %klee --output-dir=%t.invalid %t.invalid.bc 2>&1 | FileCheck %s --check-prefix=CHECK-INVALID
// RUN: ls %t.invalid/*.model.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.bound-change.bc
// RUN: rm -rf %t.bound-change
// RUN: %klee --output-dir=%t.bound-change %t.bound-change.bc 2>&1 | FileCheck %s --check-prefix=CHECK-BOUND-CHANGE
// RUN: ls %t.bound-change/*.model.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.no-preempt.bc
// RUN: rm -rf %t.no-preempt
// RUN: %klee --emit-all-errors --output-dir=%t.no-preempt %t.no-preempt.bc 2>&1 | FileCheck %s --check-prefix=CHECK-NO-PREEMPT
// RUN: not ls %t.no-preempt/*.err
// RUN: find %t.no-preempt -name '*.early' | count 0

#include <stdint.h>

#include "klee/klee.h"

static int shared_value;

int main(void) {
  uint64_t choices[2];
  klee_make_symbolic(choices, sizeof(choices), "schedule_choices");
  klee_concurrency_create_thread(1);

#if CASE == 1 || CASE == 2 || CASE == 6
  /* CASE 1: one preemption allowed. CASE 2: zero preemptions, but the first
   * thread is no longer offered as runnable, so the switch is free and both
   * race orders remain reachable. CASE 6: zero preemptions with the first
   * thread still runnable, so the scheduler must continue it. */
  uint64_t first = klee_concurrency_schedule(0x3, choices[0],
                                              CASE == 1 ? 1 : 0);
  uint64_t remaining;
  if (first == 0) {
    klee_concurrency_read(&shared_value, sizeof(shared_value), 100);
    remaining = CASE == 6 ? 0x3 : 0x2;
  } else {
    klee_concurrency_write(&shared_value, sizeof(shared_value), 200);
    remaining = CASE == 6 ? 0x3 : 0x1;
  }

  uint64_t second = klee_concurrency_schedule(remaining, choices[1],
                                               CASE == 1 ? 1 : 0);
  if (CASE == 6 && second != first)
    klee_abort();
  if (second == 0)
    klee_concurrency_read(&shared_value, sizeof(shared_value), 101);
  else
    klee_concurrency_write(&shared_value, sizeof(shared_value), 201);
#elif CASE == 3
  uint64_t selected = klee_concurrency_schedule(0x1, choices[0], 0);
  if (selected != 0)
    klee_abort();
#elif CASE == 4
  /* Bit two claims that nonexistent logical thread two is runnable. */
  (void)klee_concurrency_schedule(0x5, choices[0], 1);
#elif CASE == 5
  /* A run has one stable bound; changing it would make pruning ambiguous. */
  (void)klee_concurrency_schedule(0x3, choices[0], 1);
  (void)klee_concurrency_schedule(0x3, choices[1], 2);
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-FORK-DAG: data race: thread 1 site 201 write conflicts with thread 0 site 100 read
// CHECK-FORK-DAG: data race: thread 0 site 101 read conflicts with thread 1 site 200 write
// CHECK-FORK: KLEE: done: completed paths = 0
// CHECK-FORK: KLEE: done: partially completed paths = 2
// CHECK-BOUND-DAG: data race: thread 1 site 201 write conflicts with thread 0 site 100 read
// CHECK-BOUND-DAG: data race: thread 0 site 101 read conflicts with thread 1 site 200 write
// CHECK-BOUND: KLEE: done: completed paths = 0
// CHECK-BOUND: KLEE: done: partially completed paths = 2
// CHECK-NO-PREEMPT: KLEE: done: completed paths = 2
// CHECK-NO-PREEMPT: KLEE: done: partially completed paths = 0
// CHECK-SINGLE: KLEE: done: completed paths = 1
// CHECK-SINGLE: KLEE: done: partially completed paths = 0
// CHECK-INVALID: KLEE: ERROR: {{.*}}concurrency model error: runnable mask contains an unknown logical thread
// CHECK-BOUND-CHANGE: KLEE: ERROR: {{.*}}concurrency model error: scheduler switch bound changed during execution
