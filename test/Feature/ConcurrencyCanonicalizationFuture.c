// REQUIRES: not-darwin
// RUN: %clang %s -emit-llvm %O0opt -g -c -o %t.bc
// RUN: rm -rf %t.out
// RUN: %klee --emit-all-errors --output-dir=%t.out %t.bc 2>&1 | FileCheck %s
// RUN: find %t.out -name '*.bug.err' | count 1
// RUN: find %t.out -name '*.model.err' | count 0

/* A future conflict is reached only after thread one's currently independent
 * first transition. A next-transition dependency-component reduction prunes
 * that order; LOCAL-only reduction must retain it. All accesses to flag are
 * mutex ordered so this tests schedule preservation, not the race oracle. */
#include <stdint.h>

#include "klee/ConcurrencyHarness.h"

static int flag;
static int other;
static int mutex;
static int owner = -1;
static unsigned program_counter[2];
static int saw_flag;

static uint64_t blocked_mask(
    const struct klee_concurrency_driver *driver) {
  const uint64_t live = klee_concurrency_driver_live_mask(driver);
  uint64_t blocked = 0;
  if ((live & UINT64_C(1)) != 0 && program_counter[0] == 0 && owner == 1)
    blocked |= UINT64_C(1);
  if ((live & UINT64_C(2)) != 0 && program_counter[1] == 1 && owner == 0)
    blocked |= UINT64_C(2);
  return blocked;
}

static void describe(struct klee_concurrency_driver *driver,
                     unsigned thread) {
  if (thread == 0) {
    switch (program_counter[0]) {
    case 0:
    case 2:
      klee_concurrency_driver_set_transition(
          driver, 0, KLEE_CONCURRENCY_TRANSITION_MUTEX,
          (uintptr_t)&mutex, 0);
      return;
    case 1:
      klee_concurrency_driver_set_transition(
          driver, 0, KLEE_CONCURRENCY_TRANSITION_READ,
          (uintptr_t)&flag, sizeof(flag));
      return;
    case 3:
      klee_concurrency_driver_set_transition(
          driver, 0, KLEE_CONCURRENCY_TRANSITION_LOCAL, 0, 0);
      return;
    }
  } else {
    switch (program_counter[1]) {
    case 0:
      klee_concurrency_driver_set_transition(
          driver, 1, KLEE_CONCURRENCY_TRANSITION_WRITE,
          (uintptr_t)&other, sizeof(other));
      return;
    case 1:
    case 3:
      klee_concurrency_driver_set_transition(
          driver, 1, KLEE_CONCURRENCY_TRANSITION_MUTEX,
          (uintptr_t)&mutex, 0);
      return;
    case 2:
      klee_concurrency_driver_set_transition(
          driver, 1, KLEE_CONCURRENCY_TRANSITION_WRITE,
          (uintptr_t)&flag, sizeof(flag));
      return;
    }
  }
  klee_abort();
}

static void step(struct klee_concurrency_driver *driver, unsigned thread) {
  if (thread == 0) {
    switch (program_counter[0]++) {
    case 0:
      klee_concurrency_mutex_lock(&mutex);
      owner = 0;
      return;
    case 1:
      klee_concurrency_read(&flag, sizeof(flag), 100);
      saw_flag = flag;
      return;
    case 2:
      klee_concurrency_mutex_unlock(&mutex);
      owner = -1;
      return;
    case 3:
      if (saw_flag)
        klee_report_error(__FILE__, __LINE__,
                          "order-dependent bug reached", "bug.err");
      klee_concurrency_driver_finish(driver, 0);
      return;
    }
  } else {
    switch (program_counter[1]++) {
    case 0:
      klee_concurrency_write(&other, sizeof(other), 200);
      other = 7;
      return;
    case 1:
      klee_concurrency_mutex_lock(&mutex);
      owner = 1;
      return;
    case 2:
      klee_concurrency_write(&flag, sizeof(flag), 201);
      flag = 1;
      return;
    case 3:
      klee_concurrency_mutex_unlock(&mutex);
      owner = -1;
      klee_concurrency_driver_finish(driver, 1);
      return;
    }
  }
  klee_abort();
}

int main(void) {
  unsigned char choices[16];
  struct klee_concurrency_driver driver;
  klee_make_symbolic(choices, sizeof(choices), "schedule_choices");
  klee_concurrency_create_thread(1);
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x3, 2);
  klee_concurrency_driver_enable_canonicalization(&driver);

  for (;;) {
    klee_concurrency_driver_set_blocked_mask(&driver,
                                             blocked_mask(&driver));
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
    if (result == KLEE_CONCURRENCY_DRIVER_BOUND)
      return 0;
    step(&driver, (unsigned)thread);
  }
}

// CHECK: KLEE: ERROR: {{.*}}order-dependent bug reached
// CHECK: KLEE: done: partially completed paths = {{[1-9][0-9]*}}
