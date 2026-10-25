// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.finish.bc
// RUN: rm -rf %t.finish
// RUN: %klee --emit-all-errors --output-dir=%t.finish %t.finish.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SIX
// RUN: find %t.finish -name '*.err' | count 0
// RUN: find %t.finish -name '*.early' | count 0
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.blocked.bc
// RUN: rm -rf %t.blocked
// RUN: %klee --emit-all-errors --output-dir=%t.blocked %t.blocked.bc 2>&1 | FileCheck %s --check-prefix=CHECK-TWO
// RUN: find %t.blocked -name '*.err' | count 0
// RUN: find %t.blocked -name '*.early' | count 0
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.preempt0.bc
// RUN: rm -rf %t.preempt0
// RUN: %klee --emit-all-errors --output-dir=%t.preempt0 %t.preempt0.bc 2>&1 | FileCheck %s --check-prefix=CHECK-TWO
// RUN: find %t.preempt0 -name '*.early' | count 0
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.preempt1.bc
// RUN: rm -rf %t.preempt1
// RUN: %klee --emit-all-errors --output-dir=%t.preempt1 %t.preempt1.bc 2>&1 | FileCheck %s --check-prefix=CHECK-FOUR
// RUN: find %t.preempt1 -name '*.early' | count 0
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.local-canonical.bc
// RUN: rm -rf %t.local-canonical
// RUN: %klee --emit-all-errors --output-dir=%t.local-canonical %t.local-canonical.bc 2>&1 | FileCheck %s --check-prefix=CHECK-TWO
// RUN: find %t.local-canonical -name '*.err' | count 0
// RUN: find %t.local-canonical -name '*.early' | count 0
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.local-plain.bc
// RUN: rm -rf %t.local-plain
// RUN: %klee --emit-all-errors --output-dir=%t.local-plain %t.local-plain.bc 2>&1 | FileCheck %s --check-prefix=CHECK-FOUR
// RUN: find %t.local-plain -name '*.err' | count 0
// RUN: find %t.local-plain -name '*.early' | count 0

/* max_switches is a preemption bound. A selection is charged only when the
 * previously running thread is still offered as runnable and a different
 * thread's non-LOCAL transition is selected. Switching away from a finished
 * or blocked thread is free, and declared LOCAL transitions are transparent
 * to the accounting, so the LOCAL-only canonicalizer cannot consume bound
 * budget by forcing a commuting step. */
#include <stdint.h>

#include "klee/ConcurrencyHarness.h"

enum action {
  ACTION_NONE,
  ACTION_WRITE_X,
  ACTION_READ_Y,
  ACTION_LOCK,
  ACTION_UNLOCK,
  ACTION_SET_FLAG,
};

struct step {
  enum klee_concurrency_transition_kind kind;
  enum action action;
  int wait_flag;
};

#define MAX_THREADS 3
#define MAX_STEPS 3

static int x;
static int y;
static int mutex;
static int owner = -1;
static int flag;
static unsigned program_counter[MAX_THREADS];
static const struct step *program[MAX_THREADS];
static unsigned program_length[MAX_THREADS];

static const struct step *next_step(unsigned thread) {
  return &program[thread][program_counter[thread]];
}

static uint64_t blocked_mask(const struct klee_concurrency_driver *driver) {
  const uint64_t live = klee_concurrency_driver_live_mask(driver);
  uint64_t blocked = 0;
  for (unsigned thread = 0; thread < MAX_THREADS; ++thread) {
    const uint64_t bit = UINT64_C(1) << thread;
    if ((live & bit) == 0)
      continue;
    const struct step *step = next_step(thread);
    if (step->action == ACTION_LOCK && owner != -1)
      blocked |= bit;
    if (step->wait_flag && !flag)
      blocked |= bit;
  }
  return blocked;
}

static void describe(struct klee_concurrency_driver *driver, unsigned thread) {
  const struct step *step = next_step(thread);
  switch (step->kind) {
  case KLEE_CONCURRENCY_TRANSITION_WRITE:
    klee_concurrency_driver_set_transition(driver, thread, step->kind,
                                           (uintptr_t)&x, sizeof(x));
    return;
  case KLEE_CONCURRENCY_TRANSITION_READ:
    klee_concurrency_driver_set_transition(driver, thread, step->kind,
                                           (uintptr_t)&y, sizeof(y));
    return;
  case KLEE_CONCURRENCY_TRANSITION_MUTEX:
    klee_concurrency_driver_set_transition(driver, thread, step->kind,
                                           (uintptr_t)&mutex, 0);
    return;
  default:
    klee_concurrency_driver_set_transition(driver, thread, step->kind, 0, 0);
    return;
  }
}

static void execute(struct klee_concurrency_driver *driver, unsigned thread) {
  const struct step *step = next_step(thread);
  switch (step->action) {
  case ACTION_NONE:
    break;
  case ACTION_WRITE_X:
    klee_concurrency_write(&x, sizeof(x), 100 + thread);
    x = (int)thread;
    break;
  case ACTION_READ_Y:
    klee_concurrency_read(&y, sizeof(y), 200 + thread);
    (void)y;
    break;
  case ACTION_LOCK:
    klee_concurrency_mutex_lock(&mutex);
    owner = (int)thread;
    break;
  case ACTION_UNLOCK:
    klee_concurrency_mutex_unlock(&mutex);
    owner = -1;
    break;
  case ACTION_SET_FLAG:
    flag = 1;
    break;
  }
  if (++program_counter[thread] == program_length[thread])
    klee_concurrency_driver_finish(driver, thread);
}

static void run(unsigned threads, uint64_t max_switches, int declare,
                int canonical) {
  unsigned char choices[16];
  struct klee_concurrency_driver driver;
  klee_make_symbolic(choices, sizeof(choices), "schedule_choices");
  for (unsigned thread = 1; thread < threads; ++thread)
    klee_concurrency_create_thread(thread);
  klee_concurrency_driver_init(&driver, choices, sizeof(choices),
                               (UINT64_C(1) << threads) - 1, max_switches);
  if (canonical)
    klee_concurrency_driver_enable_canonicalization(&driver);

  for (;;) {
    klee_concurrency_driver_set_blocked_mask(&driver, blocked_mask(&driver));
    const uint64_t runnable = klee_concurrency_driver_runnable_mask(&driver);
    if (declare) {
      for (unsigned thread = 0; thread < threads; ++thread) {
        if ((runnable & (UINT64_C(1) << thread)) != 0)
          describe(&driver, thread);
      }
    }
    uint64_t thread = UINT64_MAX;
    const int result = klee_concurrency_driver_next(&driver, &thread);
    if (result == KLEE_CONCURRENCY_DRIVER_COMPLETE)
      return;
    if (result != KLEE_CONCURRENCY_DRIVER_SCHEDULED)
      klee_abort();
    execute(&driver, (unsigned)thread);
  }
}

static const struct step single_opaque[] = {
    {KLEE_CONCURRENCY_TRANSITION_OPAQUE, ACTION_NONE, 0},
};
static const struct step two_opaque[] = {
    {KLEE_CONCURRENCY_TRANSITION_OPAQUE, ACTION_NONE, 0},
    {KLEE_CONCURRENCY_TRANSITION_OPAQUE, ACTION_NONE, 0},
};
static const struct step flag_setter[] = {
    {KLEE_CONCURRENCY_TRANSITION_OPAQUE, ACTION_NONE, 0},
    {KLEE_CONCURRENCY_TRANSITION_OPAQUE, ACTION_SET_FLAG, 0},
    {KLEE_CONCURRENCY_TRANSITION_OPAQUE, ACTION_NONE, 0},
};
static const struct step flag_waiter[] = {
    {KLEE_CONCURRENCY_TRANSITION_MUTEX, ACTION_LOCK, 0},
    {KLEE_CONCURRENCY_TRANSITION_MUTEX, ACTION_UNLOCK, 1},
    {KLEE_CONCURRENCY_TRANSITION_OPAQUE, ACTION_NONE, 0},
};
static const struct step two_writes[] = {
    {KLEE_CONCURRENCY_TRANSITION_WRITE, ACTION_WRITE_X, 0},
    {KLEE_CONCURRENCY_TRANSITION_WRITE, ACTION_WRITE_X, 0},
};
static const struct step local_then_read[] = {
    {KLEE_CONCURRENCY_TRANSITION_LOCAL, ACTION_NONE, 0},
    {KLEE_CONCURRENCY_TRANSITION_READ, ACTION_READ_Y, 0},
};

static void load(unsigned thread, const struct step *steps, unsigned length) {
  program[thread] = steps;
  program_length[thread] = length;
}

int main(void) {
#if CASE == 1
  /* Three undeclared single-step threads under a zero bound: every switch
   * follows a finished thread, so all six orders complete. */
  load(0, single_opaque, 1);
  load(1, single_opaque, 1);
  load(2, single_opaque, 1);
  run(3, 0, 0, 0);
#elif CASE == 2
  /* Zero bound. Thread one blocks on a harness condition after taking the
   * mutex; switching away from the blocked thread is free, so both first
   * choices complete. */
  load(0, flag_setter, 3);
  load(1, flag_waiter, 3);
  run(2, 0, 1, 0);
#elif CASE == 3
  /* Two runnable two-step threads under a zero bound: only the two
   * non-preemptive orders exist. */
  load(0, two_opaque, 2);
  load(1, two_opaque, 2);
  run(2, 0, 1, 0);
#elif CASE == 4
  /* The same program with one preemption: four orders. */
  load(0, two_opaque, 2);
  load(1, two_opaque, 2);
  run(2, 1, 1, 0);
#elif CASE == 5
  /* Canonicalization forces thread one's LOCAL step first. Under a zero
   * bound both non-preemptive continuations must survive, which requires
   * LOCAL steps to be transparent to the accounting. */
  load(0, two_writes, 2);
  load(1, local_then_read, 2);
  run(2, 0, 1, 1);
#elif CASE == 6
  /* Without canonicalization the LOCAL step may run at any point; it never
   * charges the bound, so four orders complete under a zero bound. */
  load(0, two_writes, 2);
  load(1, local_then_read, 2);
  run(2, 0, 1, 0);
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-SIX: KLEE: done: completed paths = 6
// CHECK-SIX: KLEE: done: partially completed paths = 0
// CHECK-TWO: KLEE: done: completed paths = 2
// CHECK-TWO: KLEE: done: partially completed paths = 0
// CHECK-FOUR: KLEE: done: completed paths = 4
// CHECK-FOUR: KLEE: done: partially completed paths = 0
