// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.baseline.bc
// RUN: rm -rf %t.baseline
// RUN: %klee --emit-all-errors --output-dir=%t.baseline %t.baseline.bc 2>&1 | FileCheck %s --check-prefix=CHECK-BASELINE
// RUN: find %t.baseline -name '*.ptr.err' | count 3
// RUN: not ls %t.baseline/*.early
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.canonical.bc
// RUN: rm -rf %t.canonical
// RUN: %klee --emit-all-errors --output-dir=%t.canonical %t.canonical.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CANONICAL
// RUN: find %t.canonical -name '*.ptr.err' | count 1
// RUN: not ls %t.canonical/*.early
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.owner.bc
// RUN: rm -rf %t.owner
// RUN: %klee --emit-all-errors --output-dir=%t.owner %t.owner.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.owner/*.err
// RUN: not ls %t.owner/*.early
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.strong.bc
// RUN: rm -rf %t.strong
// RUN: %klee --emit-all-errors --output-dir=%t.strong %t.strong.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.strong/*.err
// RUN: not ls %t.strong/*.early
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.locked.bc
// RUN: rm -rf %t.locked
// RUN: %klee --emit-all-errors --output-dir=%t.locked %t.locked.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.locked/*.err
// RUN: not ls %t.locked/*.early

#include <stdint.h>
#include <stdlib.h>

#include "klee/ConcurrencyHarness.h"

/*
 * Abstract lifetime calibration for the confirmed standard-system DBinder
 * TargetStubSendRequest versus OnDatabusSessionServerSideClosed UAF.
 *
 * Thread 0 is the dispatch worker. It obtains a raw stub pointer while holding
 * one invoker's object mutex and later reads the object's first word to model
 * virtual dispatch. Thread 1 is the session-close callback. It holds a
 * different invoker's object mutex, drops the app-auth strong pin, removes the
 * raw index entry in the modeled last-strong-reference callback, and frees the
 * stub. The vulnerable interleaving is lookup -> close/free -> virtual use.
 *
 * This deliberately models the relevant lifetime state, not IPCObjectStub or
 * RefBase implementation details. The retained native ASan harness remains
 * the real-source witness.
 */

enum model_mode {
  MODE_VULNERABLE = 0,
  MODE_EXTRA_OWNER = 1,
  MODE_ATOMIC_STRONG_ACQUIRE = 2,
  MODE_SHARED_LIFETIME_LOCK = 3,
};

struct stub_object {
  uintptr_t vtable_word;
  uintptr_t payload;
};

static struct stub_object *stub;
static struct stub_object *stub_index_entry;
static struct stub_object *dispatch_raw;
static unsigned strong_refs;
static unsigned app_auth_pin;
static unsigned dispatch_temp_pin;
static unsigned char program_counter[2];
static int dispatch_mutex;
static int close_mutex;
static int lifetime_mutex;
static int lifetime_mutex_owner = -1;

static void destroy_stub(void) {
  if (stub == 0 || strong_refs != 0)
    klee_abort();
  /* IPCObjectStub::OnLastStrongRef removes the raw stub-index entry before the
   * RefBase allocation is destroyed. The worker's already-captured raw pointer
   * intentionally remains unchanged. */
  stub_index_entry = 0;
  free(stub);
  stub = 0;
}

static void drop_strong_ref(void) {
  if (strong_refs == 0)
    klee_abort();
  --strong_refs;
  if (strong_refs == 0)
    destroy_stub();
}

static void finish_thread(struct klee_concurrency_driver *driver,
                          unsigned thread) {
  klee_concurrency_driver_finish(driver, thread);
}

static uint64_t blocked_mask(const struct klee_concurrency_driver *driver,
                             enum model_mode mode) {
  if (mode != MODE_SHARED_LIFETIME_LOCK || program_counter[1] != 1 ||
      lifetime_mutex_owner != 0 ||
      (klee_concurrency_driver_live_mask(driver) & UINT64_C(2)) == 0)
    return 0;
  return UINT64_C(2);
}

static void describe_transition(struct klee_concurrency_driver *driver,
                                unsigned thread, enum model_mode mode) {
  if (program_counter[thread] == 0) {
    klee_concurrency_driver_set_transition(
        driver, thread, KLEE_CONCURRENCY_TRANSITION_LOCAL, 0, 0);
    return;
  }

  if (thread == 0 && program_counter[thread] == 1) {
    /* Lookup changes future lifetime reachability, and the atomic-acquire
     * control also mutates ownership, so fail closed instead of pretending
     * this is merely a read of the index slot. */
    klee_concurrency_driver_set_transition(
        driver, thread, KLEE_CONCURRENCY_TRANSITION_OPAQUE, 0, 0);
    return;
  }
  if (thread == 0 && program_counter[thread] == 2) {
    /* The use step also unlocks the invoker mutex, and the atomic-acquire
     * control may drop its temporary final reference. It therefore has more
     * than one externally visible effect and must fail closed as OPAQUE. */
    klee_concurrency_driver_set_transition(
        driver, thread, KLEE_CONCURRENCY_TRANSITION_OPAQUE, 0, 0);
    return;
  }
  if (thread == 1 && program_counter[thread] == 1) {
    /* Close changes the auth map, strong count, stub index, and allocation
     * lifetime. One exact range cannot describe all of those effects. */
    klee_concurrency_driver_set_transition(
        driver, thread, KLEE_CONCURRENCY_TRANSITION_OPAQUE, 0, 0);
    return;
  }
  klee_abort();
}

static void step_dispatch(struct klee_concurrency_driver *driver,
                          enum model_mode mode) {
  switch (program_counter[0]) {
  case 0: /* worker-local preparation */
    program_counter[0] = 1;
    return;
  case 1: { /* real shape: lock this invoker and query the raw index */
    void *mutex = mode == MODE_SHARED_LIFETIME_LOCK
                      ? (void *)&lifetime_mutex
                      : (void *)&dispatch_mutex;
    klee_concurrency_mutex_lock(mutex);
    if (mode == MODE_SHARED_LIFETIME_LOCK)
      lifetime_mutex_owner = 0;
    klee_concurrency_read(&stub_index_entry, sizeof(stub_index_entry), 5100);
    dispatch_raw = stub_index_entry;
    if (dispatch_raw == 0) {
      klee_concurrency_mutex_unlock(mutex);
      if (mode == MODE_SHARED_LIFETIME_LOCK)
        lifetime_mutex_owner = -1;
      program_counter[0] = 3;
      finish_thread(driver, 0);
      return;
    }
    if (mode == MODE_ATOMIC_STRONG_ACQUIRE) {
      /* Model a dedicated lookup-and-promote operation whose ownership change
       * is atomic with respect to close. */
      ++strong_refs;
      dispatch_temp_pin = 1;
    }
    program_counter[0] = 2;
    return;
  }
  case 2: { /* virtual SendRequest dispatch reads the live object's vtable */
    volatile uintptr_t vtable_word = dispatch_raw->vtable_word;
    (void)vtable_word;
    klee_concurrency_read(dispatch_raw, sizeof(dispatch_raw->vtable_word),
                          5101);
    if (dispatch_temp_pin != 0) {
      dispatch_temp_pin = 0;
      drop_strong_ref();
    }
    void *mutex = mode == MODE_SHARED_LIFETIME_LOCK
                      ? (void *)&lifetime_mutex
                      : (void *)&dispatch_mutex;
    klee_concurrency_mutex_unlock(mutex);
    if (mode == MODE_SHARED_LIFETIME_LOCK)
      lifetime_mutex_owner = -1;
    program_counter[0] = 3;
    finish_thread(driver, 0);
    return;
  }
  default:
    klee_abort();
  }
}

static void step_close(struct klee_concurrency_driver *driver,
                       enum model_mode mode) {
  switch (program_counter[1]) {
  case 0: /* callback-local preparation */
    program_counter[1] = 1;
    return;
  case 1: { /* close handler lock, detach auth pin, and final DecStrongRef */
    void *mutex = mode == MODE_SHARED_LIFETIME_LOCK
                      ? (void *)&lifetime_mutex
                      : (void *)&close_mutex;
    klee_concurrency_mutex_lock(mutex);
    if (mode == MODE_SHARED_LIFETIME_LOCK)
      lifetime_mutex_owner = 1;
    if (app_auth_pin == 0)
      klee_abort();
    app_auth_pin = 0;
    drop_strong_ref();
    klee_concurrency_mutex_unlock(mutex);
    if (mode == MODE_SHARED_LIFETIME_LOCK)
      lifetime_mutex_owner = -1;
    program_counter[1] = 2;
    finish_thread(driver, 1);
    return;
  }
  default:
    klee_abort();
  }
}

static void run_model(enum model_mode mode, int canonical) {
  unsigned char choices[16];
  struct klee_concurrency_driver driver;

  stub = (struct stub_object *)malloc(sizeof(*stub));
  if (stub == 0)
    klee_abort();
  stub->vtable_word = UINT64_C(0x53545542);
  stub->payload = UINT64_C(0x4442494e);
  stub_index_entry = stub;
  dispatch_raw = 0;
  strong_refs = mode == MODE_EXTRA_OWNER ? 2 : 1;
  app_auth_pin = 1;
  dispatch_temp_pin = 0;
  program_counter[0] = 0;
  program_counter[1] = 0;
  lifetime_mutex_owner = -1;

  klee_make_symbolic(choices, sizeof(choices), "schedule_choices");
  klee_concurrency_create_thread(1);
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), UINT64_C(3),
                               4);
  if (canonical)
    klee_concurrency_driver_enable_canonicalization(&driver);

  for (;;) {
    klee_concurrency_driver_set_blocked_mask(&driver,
                                             blocked_mask(&driver, mode));
    if (canonical) {
      const uint64_t runnable =
          klee_concurrency_driver_runnable_mask(&driver);
      for (unsigned candidate = 0; candidate < 2; ++candidate) {
        if ((runnable & (UINT64_C(1) << candidate)) != 0)
          describe_transition(&driver, candidate, mode);
      }
    }

    uint64_t thread = UINT64_MAX;
    const int result = klee_concurrency_driver_next(&driver, &thread);
    if (result == KLEE_CONCURRENCY_DRIVER_COMPLETE)
      break;
    if (result == KLEE_CONCURRENCY_DRIVER_BOUND)
      klee_abort();
    if (thread == 0)
      step_dispatch(&driver, mode);
    else if (thread == 1)
      step_close(&driver, mode);
    else
      klee_abort();
  }

  if (mode == MODE_EXTRA_OWNER) {
    if (stub == 0 || strong_refs != 1)
      klee_abort();
    drop_strong_ref();
  }
  if (stub != 0 || stub_index_entry != 0 || strong_refs != 0 ||
      app_auth_pin != 0 || dispatch_temp_pin != 0)
    klee_abort();
}

int main(void) {
#if CASE == 1
  run_model(MODE_VULNERABLE, 0);
#elif CASE == 2
  run_model(MODE_VULNERABLE, 1);
#elif CASE == 3
  run_model(MODE_EXTRA_OWNER, 1);
#elif CASE == 4
  run_model(MODE_ATOMIC_STRONG_ACQUIRE, 1);
#elif CASE == 5
  run_model(MODE_SHARED_LIFETIME_LOCK, 1);
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-BASELINE: KLEE: ERROR: {{.*}}memory error: use after free
// CHECK-BASELINE: KLEE: done: completed paths = 7
// CHECK-BASELINE: KLEE: done: partially completed paths = 3
// CHECK-CANONICAL: KLEE: ERROR: {{.*}}memory error: use after free
// CHECK-CANONICAL: KLEE: done: completed paths = 2
// CHECK-CANONICAL: KLEE: done: partially completed paths = 1
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
