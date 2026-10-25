// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.block.bc
// RUN: rm -rf %t.block
// RUN: %klee --emit-all-errors --output-dir=%t.block %t.block.bc 2>&1 | FileCheck %s --check-prefix=CHECK-BLOCK
// RUN: ls %t.block/*.model.err
// RUN: not ls %t.block/*.bug.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.unblock.bc
// RUN: rm -rf %t.unblock
// RUN: %klee --emit-all-errors --output-dir=%t.unblock %t.unblock.bc 2>&1 | FileCheck %s --check-prefix=CHECK-UNBLOCK
// RUN: ls %t.unblock/*.model.err
// RUN: not ls %t.unblock/*.bug.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.self.bc
// RUN: rm -rf %t.self
// RUN: %klee --emit-all-errors --output-dir=%t.self %t.self.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.self/*.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.redeclare-block.bc
// RUN: rm -rf %t.redeclare-block
// RUN: %klee --emit-all-errors --output-dir=%t.redeclare-block %t.redeclare-block.bc 2>&1 | FileCheck %s --check-prefix=CHECK-BLOCK
// RUN: ls %t.redeclare-block/*.model.err
// RUN: not ls %t.redeclare-block/*.bug.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.redeclare-unblock.bc
// RUN: rm -rf %t.redeclare-unblock
// RUN: %klee --emit-all-errors --output-dir=%t.redeclare-unblock %t.redeclare-unblock.bc 2>&1 | FileCheck %s --check-prefix=CHECK-UNBLOCK
// RUN: ls %t.redeclare-unblock/*.model.err
// RUN: not ls %t.redeclare-unblock/*.bug.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.finish-unblock.bc
// RUN: rm -rf %t.finish-unblock
// RUN: %klee --emit-all-errors --output-dir=%t.finish-unblock %t.finish-unblock.bc 2>&1 | FileCheck %s --check-prefix=CHECK-UNBLOCK
// RUN: ls %t.finish-unblock/*.model.err
// RUN: not ls %t.finish-unblock/*.bug.err

/* The LOCAL-only reduction is sound only if a LOCAL transition cannot change
 * another thread's enabledness. Canonicalization forces thread zero's LOCAL
 * step first and discards the thread-one-first order, so a LOCAL step that
 * then blocks (or unblocks) thread one would silently hide thread one's bug.
 * The engine must reject such a step as a model error, including after the
 * harness redeclares the active thread for its next transition or finishes
 * the active thread before changing enabledness. A LOCAL step may still block
 * itself. */
#include <stdint.h>

#include "klee/ConcurrencyHarness.h"

static unsigned program_counter[2];
static int thread0_self_blocked;

static void describe(struct klee_concurrency_driver *driver, unsigned thread) {
  if (thread == 0 && program_counter[0] == 0)
    klee_concurrency_driver_set_transition(
        driver, 0, KLEE_CONCURRENCY_TRANSITION_LOCAL, 0, 0);
  else
    klee_concurrency_driver_set_transition(
        driver, thread, KLEE_CONCURRENCY_TRANSITION_OPAQUE, 0, 0);
}

static void step(struct klee_concurrency_driver *driver, unsigned thread) {
  if (thread == 0) {
    switch (program_counter[0]++) {
    case 0:
#if CASE == 1
      klee_concurrency_driver_block(driver, 1);
#elif CASE == 2
      klee_concurrency_driver_unblock(driver, 1);
#elif CASE == 4
      klee_concurrency_driver_set_transition(
          driver, 0, KLEE_CONCURRENCY_TRANSITION_OPAQUE, 0, 0);
      klee_concurrency_driver_block(driver, 1);
#elif CASE == 5
      klee_concurrency_driver_set_transition(
          driver, 0, KLEE_CONCURRENCY_TRANSITION_OPAQUE, 0, 0);
      klee_concurrency_driver_unblock(driver, 1);
#elif CASE == 6
      klee_concurrency_driver_finish(driver, 0);
      klee_concurrency_driver_unblock(driver, 1);
#else
      klee_concurrency_driver_block(driver, 0);
      thread0_self_blocked = 1;
#endif
      return;
    case 1:
      klee_concurrency_driver_finish(driver, 0);
      return;
    }
  } else {
    switch (program_counter[1]++) {
    case 0:
#if CASE == 3
      if (thread0_self_blocked) {
        klee_concurrency_driver_unblock(driver, 0);
        thread0_self_blocked = 0;
      }
      klee_concurrency_driver_finish(driver, 1);
#else
      klee_report_error(__FILE__, __LINE__,
                        "thread one ran first", "bug.err");
#endif
      return;
    }
  }
  klee_abort();
}

int main(void) {
  unsigned char choices[8];
  struct klee_concurrency_driver driver;
  klee_make_symbolic(choices, sizeof(choices), "schedule_choices");
  klee_concurrency_create_thread(1);
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x3, 2);
  klee_concurrency_driver_enable_canonicalization(&driver);
#if CASE == 2 || CASE == 5 || CASE == 6
  klee_concurrency_driver_block(&driver, 1);
#endif

  for (;;) {
    const uint64_t runnable =
        klee_concurrency_driver_runnable_mask(&driver);
    for (unsigned thread = 0; thread < 2; ++thread) {
      if ((runnable & (UINT64_C(1) << thread)) != 0)
        describe(&driver, thread);
    }
    uint64_t thread = UINT64_MAX;
    const int result = klee_concurrency_driver_next(&driver, &thread);
    if (result == KLEE_CONCURRENCY_DRIVER_COMPLETE)
      return 0;
    if (result != KLEE_CONCURRENCY_DRIVER_SCHEDULED)
      klee_abort();
    step(&driver, (unsigned)thread);
  }
}

// CHECK-BLOCK: KLEE: ERROR: {{.*}}concurrency model error: LOCAL transition blocked another logical thread
// CHECK-UNBLOCK: KLEE: ERROR: {{.*}}concurrency model error: LOCAL transition unblocked a logical thread
// CHECK-CLEAN: KLEE: done: completed paths = 1
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
