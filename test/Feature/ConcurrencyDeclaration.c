// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.match.bc
// RUN: rm -rf %t.match
// RUN: %klee --output-dir=%t.match %t.match.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.match/*.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.local-access.bc
// RUN: rm -rf %t.local-access
// RUN: %klee --output-dir=%t.local-access %t.local-access.bc 2>&1 | FileCheck %s --check-prefix=CHECK-LOCAL-ACCESS
// RUN: ls %t.local-access/*.model.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.read-write.bc
// RUN: rm -rf %t.read-write
// RUN: %klee --output-dir=%t.read-write %t.read-write.bc 2>&1 | FileCheck %s --check-prefix=CHECK-READ-WRITE
// RUN: ls %t.read-write/*.model.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.range.bc
// RUN: rm -rf %t.range
// RUN: %klee --output-dir=%t.range %t.range.bc 2>&1 | FileCheck %s --check-prefix=CHECK-RANGE
// RUN: ls %t.range/*.model.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.missing.bc
// RUN: rm -rf %t.missing
// RUN: %klee --output-dir=%t.missing %t.missing.bc 2>&1 | FileCheck %s --check-prefix=CHECK-MISSING
// RUN: ls %t.missing/*.model.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.opaque.bc
// RUN: rm -rf %t.opaque
// RUN: %klee --output-dir=%t.opaque %t.opaque.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.opaque/*.err
// RUN: %clang %s -DCASE=7 -emit-llvm %O0opt -g -c -o %t.mutex.bc
// RUN: rm -rf %t.mutex
// RUN: %klee --output-dir=%t.mutex %t.mutex.bc 2>&1 | FileCheck %s --check-prefix=CHECK-MUTEX
// RUN: ls %t.mutex/*.model.err
// RUN: %clang %s -DCASE=8 -emit-llvm %O0opt -g -c -o %t.consumed.bc
// RUN: rm -rf %t.consumed
// RUN: %klee --output-dir=%t.consumed %t.consumed.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CONSUMED
// RUN: ls %t.consumed/*.model.err
// RUN: %clang %s -DCASE=9 -emit-llvm %O0opt -g -c -o %t.blocked-active.bc
// RUN: rm -rf %t.blocked-active
// RUN: %klee --output-dir=%t.blocked-active %t.blocked-active.bc 2>&1 | FileCheck %s --check-prefix=CHECK-BLOCKED-ACTIVE
// RUN: ls %t.blocked-active/*.model.err
// RUN: %clang %s -DCASE=10 -emit-llvm %O0opt -g -c -o %t.deadlock-missing.bc
// RUN: rm -rf %t.deadlock-missing
// RUN: %klee --output-dir=%t.deadlock-missing %t.deadlock-missing.bc 2>&1 | FileCheck %s --check-prefix=CHECK-MISSING
// RUN: ls %t.deadlock-missing/*.model.err
// RUN: not ls %t.deadlock-missing/*.deadlock.err
// RUN: %clang %s -DCASE=11 -emit-llvm %O0opt -g -c -o %t.deadlock-observed.bc
// RUN: rm -rf %t.deadlock-observed
// RUN: %klee --output-dir=%t.deadlock-observed %t.deadlock-observed.bc 2>&1 | FileCheck %s --check-prefix=CHECK-DEADLOCK
// RUN: ls %t.deadlock-observed/*.deadlock.err
// RUN: not ls %t.deadlock-observed/*.model.err

#include <stdint.h>

#include "klee/ConcurrencyHarness.h"

static int shared[2];
static int mutexes[2];

static void schedule_declared(struct klee_concurrency_driver *driver,
                              enum klee_concurrency_transition_kind kind,
                              uintptr_t address, uint64_t size) {
  uint64_t thread = UINT64_MAX;
  klee_concurrency_driver_set_transition(driver, 0, kind, address, size);
  if (klee_concurrency_driver_next(driver, &thread) !=
          KLEE_CONCURRENCY_DRIVER_SCHEDULED ||
      thread != 0)
    klee_abort();
}

int main(void) {
  unsigned char choices[2] = {0};
  struct klee_concurrency_driver driver;
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x1, 0);

#if CASE == 1
  schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_WRITE,
                    (uintptr_t)&shared[0], sizeof(shared));
  klee_concurrency_read(&shared[0], sizeof(shared[0]), 100);
  klee_concurrency_write(&shared[1], sizeof(shared[1]), 101);
  klee_concurrency_driver_finish(&driver, 0);
#elif CASE == 2
  schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_LOCAL, 0, 0);
  klee_concurrency_read(&shared[0], sizeof(shared[0]), 200);
#elif CASE == 3
  schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_READ,
                    (uintptr_t)&shared[0], sizeof(shared[0]));
  klee_concurrency_write(&shared[0], sizeof(shared[0]), 300);
#elif CASE == 4
  schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_READ,
                    (uintptr_t)&shared[0], sizeof(shared[0]));
  klee_concurrency_read(&shared[1], sizeof(shared[1]), 400);
#elif CASE == 5
  schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_READ,
                    (uintptr_t)&shared[0], sizeof(shared[0]));
  klee_concurrency_driver_set_transition(
      &driver, 0, KLEE_CONCURRENCY_TRANSITION_LOCAL, 0, 0);
#elif CASE == 6
  schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_OPAQUE, 0, 0);
  klee_concurrency_read(&shared[0], sizeof(shared[0]), 600);
  klee_concurrency_write(&shared[1], sizeof(shared[1]), 601);
  klee_concurrency_mutex_lock(&mutexes[0]);
  klee_concurrency_mutex_unlock(&mutexes[0]);
  klee_concurrency_driver_finish(&driver, 0);
#elif CASE == 7
  schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_MUTEX,
                    (uintptr_t)&mutexes[0], 0);
  klee_concurrency_mutex_lock(&mutexes[1]);
#elif CASE == 8
  /* A declaration is consumed by its transition. Scheduling the thread again
   * without declaring must fail rather than reuse the stale declaration. */
  {
    uint64_t thread = UINT64_MAX;
    schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_WRITE,
                      (uintptr_t)&shared[0], sizeof(shared[0]));
    klee_concurrency_write(&shared[0], sizeof(shared[0]), 800);
    (void)klee_concurrency_driver_next(&driver, &thread);
  }
#elif CASE == 9
  /* A thread that blocks itself may not keep performing traced operations. */
  schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_OPAQUE, 0, 0);
  klee_concurrency_driver_block(&driver, 0);
  klee_concurrency_read(&shared[0], sizeof(shared[0]), 900);
#elif CASE == 10
  /* The terminal deadlock path must complete the active declaration first:
   * a READ that never read is a model error, not a deadlock. */
  schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_READ,
                    (uintptr_t)&shared[0], sizeof(shared[0]));
  klee_concurrency_driver_block(&driver, 0);
  (void)klee_concurrency_driver_next(&driver, 0);
#elif CASE == 11
  /* Positive twin: the read happened, so the all-blocked state is a
   * harness-declared deadlock. */
  schedule_declared(&driver, KLEE_CONCURRENCY_TRANSITION_READ,
                    (uintptr_t)&shared[0], sizeof(shared[0]));
  klee_concurrency_read(&shared[0], sizeof(shared[0]), 1100);
  klee_concurrency_driver_block(&driver, 0);
  (void)klee_concurrency_driver_next(&driver, 0);
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-CLEAN: KLEE: done: completed paths = 1
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-LOCAL-ACCESS: KLEE: ERROR: {{.*}}LOCAL transition executed a shared memory access
// CHECK-READ-WRITE: KLEE: ERROR: {{.*}}READ transition executed a write
// CHECK-RANGE: KLEE: ERROR: {{.*}}logical memory access exceeds its declared transition range
// CHECK-MISSING: KLEE: ERROR: {{.*}}declared logical transition did not execute its expected operation
// CHECK-MUTEX: KLEE: ERROR: {{.*}}logical mutex operation does not match its declaration
// CHECK-CONSUMED: KLEE: ERROR: {{.*}}scheduler selected a thread without a transition declaration
// CHECK-BLOCKED-ACTIVE: KLEE: ERROR: {{.*}}active logical thread is blocked
// CHECK-DEADLOCK: KLEE: ERROR: {{.*}}logical-thread deadlock: blocked mask 0x1; harness-declared
