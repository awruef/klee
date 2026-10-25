// Harness-driver scheduler episodes (review F7). klee_concurrency_driver_init
// resets the preemption accounting through klee_concurrency_reset_scheduler,
// so a harness that drives several scheduling episodes in one path gives each
// episode its full bound, and the native replay shim resets the same state so
// it keeps reproducing the engine's selections. After scheduling begins,
// exactly one runnable logical coordinator must survive between episodes.
// Zero or multiple unfinished threads and a blocked sole survivor are model
// errors. The intrinsic also cannot be used by a native-thread state. A
// declared LOCAL kind left on the coordinator is cleared in both the engine
// and replay shim before the next episode.
//
// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.two.bc
// RUN: rm -rf %t.two
// RUN: %klee --search=dfs --output-dir=%t.two %t.two.bc 2>&1 | FileCheck %s --check-prefix=CHECK-TWO
// RUN: find %t.two -name '*.order.err' | count 1
// RUN: find %t.two -name '*.err' -not -name '*.order.err' | count 0
// RUN: find %t.two -name '*.ktest' | count 9
// Native replay must follow the same selections: the KTest behind the witness
// reaches the witness again, and a KTest without one exits cleanly.
// The RPATH (not RUNPATH) keeps the fork's replay library ahead of a stock
// library named by LD_LIBRARY_PATH; the stock one lacks the concurrency shim.
// RUN: %cc %s -DCASE=1 -DNATIVE_REPLAY %libkleeruntest -Wl,--disable-new-dtags -Wl,-rpath %libkleeruntestdir -o %t_runner
// RUN: test -f %t.two/test000005.order.err
// RUN: env KTEST_FILE=%t.two/test000005.ktest not --crash %t_runner 2>&1 | FileCheck %s --check-prefix=CHECK-REPLAY-WITNESS
// RUN: env KTEST_FILE=%t.two/test000001.ktest %t_runner 2>&1 | FileCheck %s --check-prefix=CHECK-REPLAY-FIRST
// RUN: env KTEST_FILE=%t.two/test000009.ktest %t_runner 2>&1 | FileCheck %s --check-prefix=CHECK-REPLAY-LAST
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.unfinished.bc
// RUN: rm -rf %t.unfinished
// RUN: %klee --output-dir=%t.unfinished %t.unfinished.bc 2>&1 | FileCheck %s --check-prefix=CHECK-UNFINISHED
// RUN: ls %t.unfinished/*.model.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.native.bc
// RUN: rm -rf %t.native
// RUN: %klee --output-dir=%t.native %t.native.bc 2>&1 | FileCheck %s --check-prefix=CHECK-NATIVE
// RUN: ls %t.native/*.model.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.zero.bc
// RUN: rm -rf %t.zero
// RUN: %klee --output-dir=%t.zero %t.zero.bc 2>&1 | FileCheck %s --check-prefix=CHECK-ZERO
// RUN: ls %t.zero/*.model.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.blocked.bc
// RUN: rm -rf %t.blocked
// RUN: %klee --output-dir=%t.blocked %t.blocked.bc 2>&1 | FileCheck %s --check-prefix=CHECK-BLOCKED
// RUN: ls %t.blocked/*.model.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.declarations.bc
// RUN: rm -rf %t.declarations
// RUN: %klee --output-dir=%t.declarations %t.declarations.bc 2>&1 | FileCheck %s --check-prefix=CHECK-DECLARATIONS
// RUN: not ls %t.declarations/*.err
// RUN: %cc %s -DCASE=6 -DNATIVE_REPLAY %libkleeruntest -Wl,--disable-new-dtags -Wl,-rpath %libkleeruntestdir -o %t_declarations_runner
// RUN: %t_declarations_runner 2>&1 | FileCheck %s --check-prefix=CHECK-DECLARATIONS-REPLAY

#include <assert.h>
#include <stdint.h>

#include "klee/ConcurrencyHarness.h"

#ifdef NATIVE_REPLAY
#include <stdio.h>
#endif

#if CASE == 3
#include <pthread.h>

static void *idle(void *argument) {
  (void)argument;
  return 0;
}
#endif

/* One episode: worker `a` has two steps and worker `b` has one, bound 1. The
 * orders are b,a,a (free), a,a,b (free), and a,b,a (one preemption, because
 * `a` is still runnable when `b` is selected). The order is encoded in base
 * 3 with a=1 and b=2, so a,b,a is 1*9 + 2*3 + 1 = 16. */
#define ORDER_PREEMPTED 16u

static unsigned run_episode(const unsigned char *choices, uint64_t a,
                            uint64_t b) {
  struct klee_concurrency_driver driver;
  unsigned a_steps = 0;
  unsigned order = 0;
  /* The initialization resets the scheduler and hands the active role back
   * to the only unfinished thread (main), which then creates this episode's
   * workers. Creating them first would fail: the previous episode's last
   * finished worker would still be the active thread. */
  klee_concurrency_driver_init(&driver, choices, 3,
                               (UINT64_C(1) << a) | (UINT64_C(1) << b), 1);
  klee_concurrency_create_thread(a);
  klee_concurrency_create_thread(b);
  for (;;) {
    uint64_t thread = UINT64_MAX;
    const int result = klee_concurrency_driver_next(&driver, &thread);
    if (result == KLEE_CONCURRENCY_DRIVER_COMPLETE)
      return order;
    if (result != KLEE_CONCURRENCY_DRIVER_SCHEDULED)
      klee_abort();
    order = order * 3 + (thread == a ? 1u : 2u);
    if (thread == a) {
      if (++a_steps == 2)
        klee_concurrency_driver_finish(&driver, a);
    } else {
      klee_concurrency_driver_finish(&driver, b);
    }
  }
}

static void finish_every_thread(struct klee_concurrency_driver *driver) {
  while (klee_concurrency_driver_live_mask(driver) != 0) {
    uint64_t thread = UINT64_MAX;
    if (klee_concurrency_driver_next(driver, &thread) !=
        KLEE_CONCURRENCY_DRIVER_SCHEDULED)
      klee_abort();
    klee_concurrency_driver_finish(driver, thread);
  }
}

static unsigned run_declaration_reset(void) {
  const unsigned char first_choices[1] = {0};
  const unsigned char second_choices[3] = {0, 1, 0};
  struct klee_concurrency_driver driver;
  uint64_t thread = UINT64_MAX;

  /* Complete an episode with main as its sole surviving coordinator. */
  klee_concurrency_create_thread(1);
  klee_concurrency_driver_init(&driver, first_choices, 1, UINT64_C(1) << 1,
                               0);
  if (klee_concurrency_driver_next(&driver, &thread) !=
          KLEE_CONCURRENCY_DRIVER_SCHEDULED ||
      thread != 1)
    klee_abort();
  klee_concurrency_driver_finish(&driver, 1);

  /* Leave an inactive LOCAL declaration on the coordinator. A correct reset
   * clears both the engine declaration map and the replay shim's kind table. */
  klee_concurrency_declare(0, KLEE_CONCURRENCY_TRANSITION_LOCAL, 0, 0);

  klee_concurrency_driver_init(&driver, second_choices, 3,
                               (UINT64_C(1) << 0) | (UINT64_C(1) << 2), 0);
  klee_concurrency_create_thread(2);
  unsigned main_steps = 0;
  unsigned order = 0;
  while (klee_concurrency_driver_live_mask(&driver) != 0) {
    if (klee_concurrency_driver_next(&driver, &thread) !=
        KLEE_CONCURRENCY_DRIVER_SCHEDULED)
      klee_abort();
    order = order * 3 + (thread == 0 ? 1u : 2u);
    if (thread == 0) {
      if (++main_steps == 2)
        klee_concurrency_driver_finish(&driver, 0);
    } else {
      klee_concurrency_driver_finish(&driver, 2);
    }
  }
  return order;
}

int main(void) {
#if CASE == 1
  unsigned char first[3];
  unsigned char second[3];
  klee_make_symbolic(first, sizeof(first), "schedule_choices_1");
  klee_make_symbolic(second, sizeof(second), "schedule_choices_2");
  const unsigned order1 = run_episode(first, 1, 2);
  const unsigned order2 = run_episode(second, 3, 4);
#ifdef NATIVE_REPLAY
  fprintf(stderr, "ORDERS %u %u\n", order1, order2);
#endif
  /* Reachable only when the second episode has its own preemption budget. */
  if (order1 == ORDER_PREEMPTED && order2 == ORDER_PREEMPTED)
    klee_report_error(__FILE__, __LINE__, "both episodes preempted",
                      "order.err");
#elif CASE == 2
  unsigned char choices[3];
  struct klee_concurrency_driver driver;
  uint64_t thread = UINT64_MAX;
  klee_make_symbolic(choices, sizeof(choices), "schedule_choices");
  klee_concurrency_create_thread(1);
  klee_concurrency_create_thread(2);
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x6, 1);
  if (klee_concurrency_driver_next(&driver, &thread) !=
      KLEE_CONCURRENCY_DRIVER_SCHEDULED)
    klee_abort();
  /* Both workers are still unfinished: starting a new episode here would
   * discard the bound they have already consumed. */
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x6, 1);
#elif CASE == 3
  pthread_t thread;
  pthread_create(&thread, 0, idle, 0);
  klee_concurrency_reset_scheduler();
#elif CASE == 4
  const unsigned char choices[2] = {0, 0};
  struct klee_concurrency_driver driver;
  klee_concurrency_create_thread(1);
  klee_concurrency_driver_init(&driver, choices, 2, UINT64_C(3), 0);
  finish_every_thread(&driver);
  /* No unfinished parent exists from which a fresh thread can be created. */
  klee_concurrency_driver_init(&driver, choices, 2, UINT64_C(1) << 2, 0);
#elif CASE == 5
  const unsigned char choices[2] = {0, 0};
  struct klee_concurrency_driver driver;
  uint64_t thread = UINT64_MAX;
  klee_concurrency_create_thread(1);
  klee_concurrency_driver_init(&driver, choices, 2, UINT64_C(3), 0);
  if (klee_concurrency_driver_next(&driver, &thread) !=
          KLEE_CONCURRENCY_DRIVER_SCHEDULED ||
      thread != 0)
    klee_abort();
  klee_concurrency_driver_block(&driver, 0);
  if (klee_concurrency_driver_next(&driver, &thread) !=
          KLEE_CONCURRENCY_DRIVER_SCHEDULED ||
      thread != 1)
    klee_abort();
  klee_concurrency_driver_finish(&driver, 1);
  klee_concurrency_driver_init(&driver, choices, 2, UINT64_C(1), 0);
#elif CASE == 6
  const unsigned order = run_declaration_reset();
#ifdef NATIVE_REPLAY
  fprintf(stderr, "DECL_ORDER %u\n", order);
#endif
  klee_assert(order == 14);
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-TWO: KLEE: ERROR: {{.*}}both episodes preempted
// CHECK-TWO: KLEE: done: completed paths = 8
// CHECK-TWO: KLEE: done: partially completed paths = 1
// CHECK-TWO: KLEE: done: generated tests = 9
// CHECK-REPLAY-WITNESS: ORDERS 16 16
// CHECK-REPLAY-WITNESS: KLEE_REPORT_ERROR: {{.*}}both episodes preempted (order.err)
// CHECK-REPLAY-FIRST: ORDERS {{[0-9]+}} {{[0-9]+}}
// CHECK-REPLAY-LAST: ORDERS {{[0-9]+}} {{[0-9]+}}
// CHECK-UNFINISHED: KLEE: ERROR: {{.*}}concurrency model error: logical thread scheduler reset while more than one logical thread is unfinished
// CHECK-NATIVE: KLEE: ERROR: {{.*}}concurrency model error: klee_concurrency_reset_scheduler is a harness-driver intrinsic and cannot be used once the state runs native threads
// CHECK-ZERO: KLEE: ERROR: {{.*}}concurrency model error: logical thread scheduler reset with no unfinished logical thread to coordinate the next episode
// CHECK-BLOCKED: KLEE: ERROR: {{.*}}concurrency model error: logical thread scheduler reset while the remaining logical thread is blocked
// CHECK-DECLARATIONS-NOT: KLEE: ERROR
// CHECK-DECLARATIONS: KLEE: done: completed paths = 1
// CHECK-DECLARATIONS: KLEE: done: partially completed paths = 0
// CHECK-DECLARATIONS-REPLAY: DECL_ORDER 14
