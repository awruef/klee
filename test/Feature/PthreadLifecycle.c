// Native pthread lifecycle: pthread_exit from a nested frame, main exiting
// while workers remain, return from main as process exit, self-join, and a
// verified cyclic join deadlock. CASE 6 checks that the harness scheduling
// intrinsics and the native model cannot be mixed in one state.
//
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.exit.bc
// RUN: rm -rf %t.exit
// RUN: %klee --emit-all-errors --output-dir=%t.exit %t.exit.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.exit/*.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.main-exit.bc
// RUN: rm -rf %t.main-exit
// RUN: %klee --emit-all-errors --output-dir=%t.main-exit %t.main-exit.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.main-exit/*.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.main-return.bc
// RUN: rm -rf %t.main-return
// RUN: %klee --emit-all-errors --output-dir=%t.main-return %t.main-return.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.main-return/*.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.self-join.bc
// RUN: rm -rf %t.self-join
// RUN: %klee --output-dir=%t.self-join %t.self-join.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SELF
// RUN: ls %t.self-join/*.model.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.cycle.bc
// RUN: rm -rf %t.cycle
// RUN: %klee --emit-all-errors --output-dir=%t.cycle %t.cycle.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CYCLE
// RUN: ls %t.cycle/*.deadlock.err
// RUN: find %t.cycle -name '*.err' -not -name '*.deadlock.err' | count 0
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.mixed.bc
// RUN: rm -rf %t.mixed
// RUN: %klee --output-dir=%t.mixed %t.mixed.bc 2>&1 | FileCheck %s --check-prefix=CHECK-MIXED
// RUN: ls %t.mixed/*.model.err
// RUN: %clang %s -DCASE=7 -emit-llvm %O0opt -g -c -o %t.mixed-native.bc
// RUN: rm -rf %t.mixed-native
// RUN: %klee --output-dir=%t.mixed-native %t.mixed-native.bc 2>&1 | FileCheck %s --check-prefix=CHECK-MIXED-NATIVE
// RUN: ls %t.mixed-native/*.model.err
// RUN: %clang %s -DCASE=8 -emit-llvm %O0opt -g -c -o %t.detach.bc
// RUN: rm -rf %t.detach
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=1 --output-dir=%t.detach %t.detach.bc 2>&1 | FileCheck %s --check-prefix=CHECK-DETACH
// RUN: ls %t.detach/*.schedule.err
// RUN: find %t.detach -name '*.err' -not -name '*.schedule.err' | count 0
// RUN: %clang %s -DCASE=9 -emit-llvm %O0opt -g -c -o %t.mixed-self.bc
// RUN: rm -rf %t.mixed-self
// RUN: %klee --output-dir=%t.mixed-self %t.mixed-self.bc 2>&1 | FileCheck %s --check-prefix=CHECK-MIXED-SELF
// RUN: ls %t.mixed-self/*.model.err

#include <assert.h>
#include <pthread.h>
#include <stdint.h>

#include "klee/klee.h"

static int progress;
static pthread_t peer_a;
static pthread_t peer_b;
static volatile int detach_phase;

#if CASE == 1
static void leave(void) {
  pthread_exit((void *)7);
}

static void *exiting_worker(void *argument) {
  (void)argument;
  progress = 1;
  leave();
  /* unreachable */
  progress = 99;
  return 0;
}
#endif

#if CASE == 2 || CASE == 3
static void *late_worker(void *argument) {
  (void)argument;
  klee_concurrency_yield();
  progress = 1;
  return 0;
}
#endif

#if CASE == 5
static void *join_b(void *argument) {
  (void)argument;
  klee_concurrency_yield();
  klee_assert(pthread_join(peer_b, 0) == 0);
  return 0;
}

static void *join_a(void *argument) {
  (void)argument;
  klee_concurrency_yield();
  klee_assert(pthread_join(peer_a, 0) == 0);
  return 0;
}
#endif

#if CASE == 6 || CASE == 7
static void *idle(void *argument) {
  (void)argument;
  return 0;
}
#endif

#if CASE == 8
static void *detached_worker(void *argument) {
  (void)argument;
  if (detach_phase == 1)
    klee_report_error(__FILE__, __LINE__,
                      "pthread_detach scheduling boundary reached",
                      "schedule.err");
  return 0;
}
#endif

int main(void) {
  pthread_t thread;
  void *result = 0;
#if CASE == 1
  klee_assert(pthread_create(&thread, 0, exiting_worker, 0) == 0);
  klee_assert(pthread_join(thread, &result) == 0);
  klee_assert(result == (void *)7);
  klee_assert(progress == 1);
#elif CASE == 2
  /* main leaves through pthread_exit; the path completes once the worker
   * has finished. */
  klee_assert(pthread_create(&thread, 0, late_worker, 0) == 0);
  pthread_exit(0);
#elif CASE == 3
  /* Returning from main is a process exit even with a live worker. */
  klee_assert(pthread_create(&thread, 0, late_worker, 0) == 0);
  return 0;
#elif CASE == 4
  pthread_join(pthread_self(), 0);
#elif CASE == 5
  klee_assert(pthread_create(&peer_a, 0, join_b, 0) == 0);
  klee_assert(pthread_create(&peer_b, 0, join_a, 0) == 0);
  klee_assert(pthread_join(peer_a, 0) == 0);
  klee_assert(pthread_join(peer_b, 0) == 0);
#elif CASE == 6
  klee_concurrency_create_thread(1);
  pthread_create(&thread, 0, idle, 0);
#elif CASE == 7
  klee_assert(pthread_create(&thread, 0, idle, 0) == 0);
  klee_concurrency_set_thread(1);
#elif CASE == 8
  klee_assert(pthread_create(&thread, 0, detached_worker, 0) == 0);
  detach_phase = 1;
  klee_assert(pthread_detach(thread) == 0);
  detach_phase = 2;
#elif CASE == 9
  klee_concurrency_create_thread(1);
  (void)pthread_self();
#endif
  return 0;
}

// CHECK-CLEAN-NOT: KLEE: ERROR
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-SELF: KLEE: ERROR: {{.*}}concurrency model error: pthread_join on the calling thread
// CHECK-CYCLE: KLEE: ERROR: {{.*}}logical-thread deadlock: blocked mask 0x7; verified
// CHECK-MIXED: KLEE: ERROR: {{.*}}concurrency model error: pthread_create is a native thread operation and cannot be used once the state is driven by harness scheduling intrinsics
// CHECK-MIXED-NATIVE: KLEE: ERROR: {{.*}}concurrency model error: klee_concurrency_set_thread is a harness-driver intrinsic and cannot be used once the state runs native threads
// CHECK-DETACH: KLEE: ERROR: {{.*}}pthread_detach scheduling boundary reached
// CHECK-MIXED-SELF: KLEE: ERROR: {{.*}}concurrency model error: pthread_self is a native thread operation and cannot be used once the state is driven by harness scheduling intrinsics
