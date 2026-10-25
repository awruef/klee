// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.vulnerable.bc
// RUN: rm -rf %t.vulnerable
// RUN: %klee --output-dir=%t.vulnerable %t.vulnerable.bc 2>&1 | FileCheck %s --check-prefix=CHECK-VULNERABLE
// RUN: ls %t.vulnerable/*.race.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.locked.bc
// RUN: rm -rf %t.locked
// RUN: %klee --output-dir=%t.locked %t.locked.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.locked/*.race.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.eager.bc
// RUN: rm -rf %t.eager
// RUN: %klee --output-dir=%t.eager %t.eager.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.eager/*.race.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.scheduled-vulnerable.bc
// RUN: rm -rf %t.scheduled-vulnerable
// RUN: %klee --emit-all-errors --output-dir=%t.scheduled-vulnerable %t.scheduled-vulnerable.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SCHEDULED-VULNERABLE
// RUN: find %t.scheduled-vulnerable -name '*.race.err' | count 14
// RUN: not ls %t.scheduled-vulnerable/*.early
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.scheduled-locked.bc
// RUN: rm -rf %t.scheduled-locked
// RUN: %klee --emit-all-errors --output-dir=%t.scheduled-locked %t.scheduled-locked.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SCHEDULED-LOCKED
// RUN: not ls %t.scheduled-locked/*.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.canonical-vulnerable.bc
// RUN: rm -rf %t.canonical-vulnerable
// RUN: %klee --emit-all-errors --output-dir=%t.canonical-vulnerable %t.canonical-vulnerable.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CANONICAL-VULNERABLE
// RUN: find %t.canonical-vulnerable -name '*.race.err' | count 14
// RUN: not ls %t.canonical-vulnerable/*.early
// RUN: %clang %s -DCASE=7 -emit-llvm %O0opt -g -c -o %t.canonical-locked.bc
// RUN: rm -rf %t.canonical-locked
// RUN: %klee --emit-all-errors --output-dir=%t.canonical-locked %t.canonical-locked.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SCHEDULED-LOCKED
// RUN: not ls %t.canonical-locked/*.err

#include <stdint.h>

#include "klee/ConcurrencyHarness.h"

/* Abstract layout of the two machine words commonly carried by shared_ptr.
 * This is a race-oracle calibration, not a libc++ shared_ptr implementation. */
struct SharedPtrShape {
  uintptr_t object;
  uintptr_t control;
};

static struct SharedPtrShape session_buffer;
static int buffer_mutex;

#if CASE == 4 || CASE == 5 || CASE == 6 || CASE == 7
static unsigned char program_counter[2];
static int mutex_owner = -1;

static uint64_t blocked_mask(const struct klee_concurrency_driver *driver,
                             int vulnerable) {
  uint64_t mask = 0;
  for (unsigned thread = 0; thread < 2; ++thread) {
    const uint64_t bit = UINT64_C(1) << thread;
    if ((klee_concurrency_driver_live_mask(driver) & bit) == 0)
      continue;
    const unsigned lock_pc = vulnerable ? 1 : 0;
    if (program_counter[thread] == lock_pc && mutex_owner != -1 &&
        mutex_owner != (int)thread)
      mask |= bit;
  }
  return mask;
}

static void describe_transition(struct klee_concurrency_driver *driver,
                                unsigned thread, int vulnerable) {
  enum klee_concurrency_transition_kind kind;
  uintptr_t address;
  uint64_t size;
  if (vulnerable) {
    switch (program_counter[thread]) {
    case 0:
    case 2:
      kind = KLEE_CONCURRENCY_TRANSITION_READ;
      address = (uintptr_t)&session_buffer.object;
      size = sizeof(session_buffer.object);
      break;
    case 1:
    case 4:
      kind = KLEE_CONCURRENCY_TRANSITION_MUTEX;
      address = (uintptr_t)&buffer_mutex;
      size = 0;
      break;
    case 3:
      kind = KLEE_CONCURRENCY_TRANSITION_WRITE;
      address = (uintptr_t)&session_buffer;
      size = sizeof(session_buffer);
      break;
    case 5:
      kind = KLEE_CONCURRENCY_TRANSITION_READ;
      address = (uintptr_t)&session_buffer;
      size = sizeof(session_buffer);
      break;
    default:
      klee_abort();
    }
  } else {
    switch (program_counter[thread]) {
    case 0:
    case 3:
      kind = KLEE_CONCURRENCY_TRANSITION_MUTEX;
      address = (uintptr_t)&buffer_mutex;
      size = 0;
      break;
    case 1:
      /* The null check may publish, so describe the combined step as write. */
      kind = KLEE_CONCURRENCY_TRANSITION_WRITE;
      address = (uintptr_t)&session_buffer;
      size = sizeof(session_buffer);
      break;
    case 2:
      kind = KLEE_CONCURRENCY_TRANSITION_READ;
      address = (uintptr_t)&session_buffer;
      size = sizeof(session_buffer);
      break;
    default:
      klee_abort();
    }
  }
  klee_concurrency_driver_set_transition(driver, thread, kind, address, size);
}

static void finish_caller(struct klee_concurrency_driver *driver,
                          unsigned thread) {
  klee_concurrency_driver_finish(driver, thread);
}

static void step_vulnerable(struct klee_concurrency_driver *driver,
                            unsigned thread) {
  const uint64_t site = 3000 + 100 * thread + program_counter[thread];
  switch (program_counter[thread]) {
  case 0: /* unlocked outer null check */
    klee_concurrency_read(&session_buffer.object,
                          sizeof(session_buffer.object), site);
    program_counter[thread] = session_buffer.object == 0 ? 1 : 5;
    break;
  case 1: /* lock */
    klee_concurrency_mutex_lock(&buffer_mutex);
    mutex_owner = (int)thread;
    program_counter[thread] = 2;
    break;
  case 2: /* inner null check */
    klee_concurrency_read(&session_buffer.object,
                          sizeof(session_buffer.object), site);
    program_counter[thread] = session_buffer.object == 0 ? 3 : 4;
    break;
  case 3: /* shared_ptr publication */
    klee_concurrency_write(&session_buffer, sizeof(session_buffer), site);
    session_buffer.object = 1;
    session_buffer.control = 1;
    program_counter[thread] = 4;
    break;
  case 4: /* unlock */
    klee_concurrency_mutex_unlock(&buffer_mutex);
    mutex_owner = -1;
    program_counter[thread] = 5;
    break;
  case 5: /* unlocked returned shared_ptr copy */
    klee_concurrency_read(&session_buffer, sizeof(session_buffer), site);
    program_counter[thread] = 6;
    finish_caller(driver, thread);
    break;
  default:
    klee_abort();
  }
}

static void step_locked(struct klee_concurrency_driver *driver,
                        unsigned thread) {
  const uint64_t site = 4000 + 100 * thread + program_counter[thread];
  switch (program_counter[thread]) {
  case 0: /* lock before every member access */
    klee_concurrency_mutex_lock(&buffer_mutex);
    mutex_owner = (int)thread;
    program_counter[thread] = 1;
    break;
  case 1: /* null check and optional publication */
    klee_concurrency_read(&session_buffer.object,
                          sizeof(session_buffer.object), site);
    if (session_buffer.object == 0) {
      klee_concurrency_write(&session_buffer, sizeof(session_buffer), site);
      session_buffer.object = 1;
      session_buffer.control = 1;
    }
    program_counter[thread] = 2;
    break;
  case 2: /* returned shared_ptr copy remains under the mutex */
    klee_concurrency_read(&session_buffer, sizeof(session_buffer), site);
    program_counter[thread] = 3;
    break;
  case 3: /* unlock and finish */
    klee_concurrency_mutex_unlock(&buffer_mutex);
    mutex_owner = -1;
    program_counter[thread] = 4;
    finish_caller(driver, thread);
    break;
  default:
    klee_abort();
  }
}

static void run_scheduled_callers(int vulnerable, int canonical) {
  unsigned char choices[16];
  struct klee_concurrency_driver driver;
  klee_make_symbolic(choices, sizeof(choices), "schedule_choices");
  klee_concurrency_create_thread(1);
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x3,
                               vulnerable ? 2 : 1);
  if (canonical)
    klee_concurrency_driver_enable_canonicalization(&driver);
  for (;;) {
    klee_concurrency_driver_set_blocked_mask(&driver,
                                             blocked_mask(&driver, vulnerable));
    if (canonical) {
      const uint64_t runnable =
          klee_concurrency_driver_runnable_mask(&driver);
      for (unsigned candidate = 0; candidate < 2; ++candidate) {
        if ((runnable & (UINT64_C(1) << candidate)) != 0)
          describe_transition(&driver, candidate, vulnerable);
      }
    }
    uint64_t thread = UINT64_MAX;
    const int result = klee_concurrency_driver_next(&driver, &thread);
    if (result == KLEE_CONCURRENCY_DRIVER_COMPLETE ||
        result == KLEE_CONCURRENCY_DRIVER_BOUND)
      return;
    if (vulnerable)
      step_vulnerable(&driver, (unsigned)thread);
    else
      step_locked(&driver, (unsigned)thread);
  }
}
#endif

static void read_outer(unsigned thread, uint64_t site) {
  klee_concurrency_set_thread(thread);
  klee_concurrency_read(&session_buffer.object,
                        sizeof(session_buffer.object), site);
}

static void read_return(unsigned thread, uint64_t site) {
  klee_concurrency_set_thread(thread);
  klee_concurrency_read(&session_buffer, sizeof(session_buffer), site);
}

int main(void) {
#if CASE == 1
  /* Vulnerable double-checked publication: both callers inspect the member
   * without the writer's mutex, then thread zero publishes under the mutex. */
  klee_concurrency_create_thread(1);
  read_outer(0, 1000);
  read_outer(1, 2000);
  klee_concurrency_set_thread(0);
  klee_concurrency_mutex_lock(&buffer_mutex);
  klee_concurrency_read(&session_buffer.object,
                        sizeof(session_buffer.object), 1001);
  klee_concurrency_write(&session_buffer, sizeof(session_buffer), 1002);
#elif CASE == 2
  /* Candidate repair: every member access and returned copy uses the same
   * mutex, so its release/acquire edge orders the two callers. */
  klee_concurrency_create_thread(1);
  klee_concurrency_mutex_lock(&buffer_mutex);
  klee_concurrency_read(&session_buffer.object,
                        sizeof(session_buffer.object), 1100);
  klee_concurrency_write(&session_buffer, sizeof(session_buffer), 1101);
  klee_concurrency_read(&session_buffer, sizeof(session_buffer), 1102);
  klee_concurrency_mutex_unlock(&buffer_mutex);
  klee_concurrency_set_thread(1);
  klee_concurrency_mutex_lock(&buffer_mutex);
  klee_concurrency_read(&session_buffer.object,
                        sizeof(session_buffer.object), 2100);
  klee_concurrency_read(&session_buffer, sizeof(session_buffer), 2101);
  klee_concurrency_mutex_unlock(&buffer_mutex);
#elif CASE == 3
  /* Alternative repair: publish eagerly before creating workers and never
   * modify the member afterward. Spawn orders the initialized value. */
  klee_concurrency_write(&session_buffer, sizeof(session_buffer), 1200);
  klee_concurrency_create_thread(1);
  read_return(0, 1201);
  read_return(1, 2200);
#elif CASE == 4
  /* Symbolic, context-bounded scheduling of the vulnerable state machine. */
  run_scheduled_callers(1, 0);
#elif CASE == 5
  /* The same scheduler and two callers against the common-lock repair. */
  run_scheduled_callers(0, 0);
#elif CASE == 6
  /* Transition-aware canonical scheduling of the vulnerable state machine. */
  run_scheduled_callers(1, 1);
#elif CASE == 7
  /* Canonical scheduling of the common-lock repair. */
  run_scheduled_callers(0, 1);
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-VULNERABLE: KLEE: ERROR: {{.*}}data race: thread 0 site 1002 write conflicts with thread 1 site 2000 read
// CHECK-CLEAN: KLEE: done: completed paths = 1
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-SCHEDULED-VULNERABLE: KLEE: ERROR: {{.*}}data race:
// CHECK-SCHEDULED-VULNERABLE: KLEE: done: completed paths = 0
// CHECK-SCHEDULED-VULNERABLE: KLEE: done: partially completed paths = 14
// CHECK-CANONICAL-VULNERABLE: KLEE: ERROR: {{.*}}data race:
// CHECK-CANONICAL-VULNERABLE: KLEE: done: completed paths = 0
// CHECK-CANONICAL-VULNERABLE: KLEE: done: partially completed paths = 14
// CHECK-SCHEDULED-LOCKED: KLEE: done: completed paths = 2
// CHECK-SCHEDULED-LOCKED: KLEE: done: partially completed paths = 0
