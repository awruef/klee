// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.verified.bc
// RUN: rm -rf %t.verified
// RUN: %klee --output-dir=%t.verified %t.verified.bc 2>&1 | FileCheck %s --check-prefix=CHECK-VERIFIED
// RUN: ls %t.verified/*.deadlock.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.unowned.bc
// RUN: rm -rf %t.unowned
// RUN: %klee --output-dir=%t.unowned %t.unowned.bc 2>&1 | FileCheck %s --check-prefix=CHECK-UNOWNED
// RUN: ls %t.unowned/*.model.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.self.bc
// RUN: rm -rf %t.self
// RUN: %klee --output-dir=%t.self %t.self.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SELF
// RUN: ls %t.self/*.model.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.stale.bc
// RUN: rm -rf %t.stale
// RUN: %klee --output-dir=%t.stale %t.stale.bc 2>&1 | FileCheck %s --check-prefix=CHECK-STALE
// RUN: ls %t.stale/*.model.err
// RUN: not ls %t.stale/*.deadlock.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.runnable.bc
// RUN: rm -rf %t.runnable
// RUN: %klee --output-dir=%t.runnable %t.runnable.bc 2>&1 | FileCheck %s --check-prefix=CHECK-RUNNABLE
// RUN: ls %t.runnable/*.model.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.early-unblock.bc
// RUN: rm -rf %t.early-unblock
// RUN: %klee --output-dir=%t.early-unblock %t.early-unblock.bc 2>&1 | FileCheck %s --check-prefix=CHECK-EARLY-UNBLOCK
// RUN: ls %t.early-unblock/*.model.err
// RUN: %clang %s -DCASE=7 -emit-llvm %O0opt -g -c -o %t.unrecorded.bc
// RUN: rm -rf %t.unrecorded
// RUN: %klee --output-dir=%t.unrecorded %t.unrecorded.bc 2>&1 | FileCheck %s --check-prefix=CHECK-UNRECORDED
// RUN: ls %t.unrecorded/*.model.err
// RUN: not ls %t.unrecorded/*.deadlock.err

/* The deadlock oracle no longer trusts the harness blocked mask alone. Every
 * thread in the mask must have been blocked through the engine, mutex reasons
 * are checked against current mutex ownership, and only an all-mutex cycle is
 * reported as a verified deadlock. */
#include <stdint.h>

#include "klee/ConcurrencyHarness.h"

static int mutex0;
static int mutex1;

static void schedule_expect(struct klee_concurrency_driver *driver,
                            uint64_t expected) {
  uint64_t thread = UINT64_MAX;
  if (klee_concurrency_driver_next(driver, &thread) !=
          KLEE_CONCURRENCY_DRIVER_SCHEDULED ||
      thread != expected)
    klee_abort();
}

int main(void) {
  /* Concrete choices: ordinal 0 selects the lowest eligible thread, ordinal
   * 1 the next one. */
  unsigned char choices[8] = {0, 1, 0, 0, 0, 0, 0, 0};
  struct klee_concurrency_driver driver;
  klee_concurrency_create_thread(1);
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x3, 4);

#if CASE == 1
  schedule_expect(&driver, 0);
  klee_concurrency_mutex_lock(&mutex0);
  schedule_expect(&driver, 1);
  klee_concurrency_mutex_lock(&mutex1);
  klee_concurrency_driver_block_on_mutex(&driver, 0, &mutex1);
  klee_concurrency_driver_block_on_mutex(&driver, 1, &mutex0);
  (void)klee_concurrency_driver_next(&driver, 0);
#elif CASE == 2
  klee_concurrency_driver_block_on_mutex(&driver, 0, &mutex1);
#elif CASE == 3
  schedule_expect(&driver, 0);
  klee_concurrency_mutex_lock(&mutex0);
  klee_concurrency_driver_block_on_mutex(&driver, 0, &mutex0);
#elif CASE == 4
  /* Thread one releases the mutex but the harness never unblocks thread
   * zero; the resulting deadlock report is a harness bug, not a finding. */
  schedule_expect(&driver, 0);
  klee_concurrency_mutex_lock(&mutex0);
  schedule_expect(&driver, 1);
  klee_concurrency_mutex_lock(&mutex1);
  klee_concurrency_driver_block_on_mutex(&driver, 0, &mutex1);
  schedule_expect(&driver, 1);
  klee_concurrency_mutex_unlock(&mutex1);
  klee_concurrency_driver_block(&driver, 1);
  (void)klee_concurrency_driver_next(&driver, 0);
#elif CASE == 5
  /* The engine records the block even when the driver's mask does not. */
  klee_concurrency_block(1, KLEE_CONCURRENCY_BLOCK_HARNESS, 0);
  schedule_expect(&driver, 0);
#elif CASE == 6
  schedule_expect(&driver, 0);
  klee_concurrency_mutex_lock(&mutex0);
  schedule_expect(&driver, 1);
  klee_concurrency_mutex_lock(&mutex1);
  klee_concurrency_driver_block_on_mutex(&driver, 0, &mutex1);
  klee_concurrency_driver_unblock(&driver, 0);
#elif CASE == 7
  klee_concurrency_deadlock(0x3);
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-VERIFIED: KLEE: ERROR: {{.*}}logical-thread deadlock: blocked mask 0x3; verified: every blocked thread waits on a mutex, join, or condition that no runnable thread can release
// CHECK-UNOWNED: KLEE: ERROR: {{.*}}concurrency model error: logical thread blocked on an unowned mutex
// CHECK-SELF: KLEE: ERROR: {{.*}}concurrency model error: logical thread blocked on a mutex it owns
// CHECK-STALE: KLEE: ERROR: {{.*}}concurrency model error: deadlocked logical thread waits on a mutex that is no longer owned
// CHECK-RUNNABLE: KLEE: ERROR: {{.*}}concurrency model error: runnable mask contains a blocked logical thread
// CHECK-EARLY-UNBLOCK: KLEE: ERROR: {{.*}}concurrency model error: logical thread unblocked while its mutex is still owned by another thread
// CHECK-UNRECORDED: KLEE: ERROR: {{.*}}concurrency model error: deadlock mask contains a logical thread the engine does not record as blocked
