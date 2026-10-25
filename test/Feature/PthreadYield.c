// Native pthread model: yield fairness (review F11). sched_yield is voluntary.
// A first pthread_mutex_trylock EBUSY preserves the legal immediate caller
// continuation; only a consecutive retry at the same call site requests
// fairness. Marks clear at the next non-yield operation, so the yielded thread
// can still be resumed between the other thread's operations (CASE 4), and a
// thread that is alone keeps running after a yield (CASE 3).
//
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.spin.bc
// RUN: rm -rf %t.spin
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=1 --max-time=60s --output-dir=%t.spin %t.spin.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SPIN
// RUN: not ls %t.spin/*.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.trylock.bc
// RUN: rm -rf %t.trylock
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=2 --max-time=60s --output-dir=%t.trylock %t.trylock.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SPIN
// RUN: not ls %t.trylock/*.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.alone.bc
// RUN: rm -rf %t.alone
// RUN: %klee --emit-all-errors --output-dir=%t.alone %t.alone.bc 2>&1 | FileCheck %s --check-prefix=CHECK-ALONE
// RUN: not ls %t.alone/*.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.resume.bc
// RUN: rm -rf %t.resume
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=1 --output-dir=%t.resume %t.resume.bc 2>&1 | FileCheck %s --check-prefix=CHECK-RESUME
// RUN: ls %t.resume/*.mid.err
// RUN: find %t.resume -name '*.err' -not -name '*.mid.err' | count 0
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.trylock-immediate.bc
// RUN: rm -rf %t.trylock-immediate
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=2 --output-dir=%t.trylock-immediate %t.trylock-immediate.bc 2>&1 | FileCheck %s --check-prefix=CHECK-TRYLOCK-IMMEDIATE
// RUN: ls %t.trylock-immediate/*.order.err
// RUN: find %t.trylock-immediate -name '*.err' -not -name '*.order.err' | count 0
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.all-yielded.bc
// RUN: rm -rf %t.all-yielded
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=0 --output-dir=%t.all-yielded %t.all-yielded.bc 2>&1 | FileCheck %s --check-prefix=CHECK-ALL-YIELDED
// RUN: ls %t.all-yielded/*.order.err
// RUN: find %t.all-yielded -name '*.err' -not -name '*.order.err' | count 0

#include <assert.h>
#include <errno.h>
#include <pthread.h>
#include <sched.h>

#include "klee/klee.h"

static volatile int flag;
static volatile int shared;
static volatile int done;
static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t second = PTHREAD_MUTEX_INITIALIZER;
static volatile int stage;

#if CASE == 1
static void *setter(void *argument) {
  (void)argument;
  flag = 1;
  return 0;
}
#endif

#if CASE == 5
static void *trylock_owner(void *argument) {
  (void)argument;
  klee_assert(pthread_mutex_lock(&mutex) == 0);
  stage = 1;
  klee_concurrency_yield();
  flag = 1;
  klee_assert(pthread_mutex_unlock(&mutex) == 0);
  return 0;
}
#endif

#if CASE == 6
static void *yielding_worker(void *argument) {
  (void)argument;
  sched_yield();
  flag = 1;
  return 0;
}
#endif

#if CASE == 2
static void *holder(void *argument) {
  (void)argument;
  klee_assert(pthread_mutex_lock(&mutex) == 0);
  /* A preemption point while the mutex is held lets main (bound 2) run and
   * fail its trylock; without yield fairness main would then spin forever
   * because the holder could no longer be selected. */
  klee_concurrency_yield();
  klee_assert(pthread_mutex_unlock(&mutex) == 0);
  return 0;
}
#endif

#if CASE == 4
static void *publisher(void *argument) {
  (void)argument;
  klee_assert(pthread_mutex_lock(&mutex) == 0);
  shared = 1;
  klee_assert(pthread_mutex_unlock(&mutex) == 0);
  /* A further operation is the boundary at which main may be resumed. */
  klee_assert(pthread_mutex_lock(&second) == 0);
  done = 1;
  klee_assert(pthread_mutex_unlock(&second) == 0);
  return 0;
}
#endif

int main(void) {
  pthread_t thread;
#if CASE == 1
  klee_assert(pthread_create(&thread, 0, setter, 0) == 0);
  while (!flag)
    sched_yield();
  klee_assert(pthread_join(thread, 0) == 0);
#elif CASE == 2
  klee_assert(pthread_create(&thread, 0, holder, 0) == 0);
  while (pthread_mutex_trylock(&mutex) == EBUSY)
    ;
  klee_assert(pthread_mutex_unlock(&mutex) == 0);
  klee_assert(pthread_join(thread, 0) == 0);
#elif CASE == 3
  sched_yield();
  sched_yield();
  klee_assert(1);
#elif CASE == 4
  klee_assert(pthread_create(&thread, 0, publisher, 0) == 0);
  sched_yield();
  /* Reachable only if main is resumed after the publisher's first unlock
   * and before it sets done: the yield mark must have been cleared by the
   * publisher's operations. */
  if (shared == 1 && !done)
    klee_report_error(__FILE__, __LINE__, "main resumed between operations",
                      "mid.err");
  klee_assert(pthread_join(thread, 0) == 0);
#elif CASE == 5
  klee_assert(pthread_create(&thread, 0, trylock_owner, 0) == 0);
  if (stage == 1) {
    int result = pthread_mutex_trylock(&mutex);
    if (result == EBUSY && flag == 0)
      klee_report_error(__FILE__, __LINE__, "immediate EBUSY continuation",
                        "order.err");
    if (result == 0)
      klee_assert(pthread_mutex_unlock(&mutex) == 0);
  }
  klee_assert(pthread_join(thread, 0) == 0);
#elif CASE == 6
  klee_assert(pthread_create(&thread, 0, yielding_worker, 0) == 0);
  sched_yield();
  if (!flag)
    klee_report_error(__FILE__, __LINE__, "voluntary switch returned to main",
                      "order.err");
  klee_assert(pthread_join(thread, 0) == 0);
#endif
  return 0;
}

// CHECK-SPIN-NOT: KLEE: ERROR
// CHECK-SPIN-NOT: HaltTimer invoked
// CHECK-SPIN: KLEE: done: completed paths = {{[0-9]+}}
// CHECK-SPIN: KLEE: done: partially completed paths = 0
// CHECK-ALONE-NOT: KLEE: ERROR
// CHECK-ALONE: KLEE: done: completed paths = 1
// CHECK-RESUME: KLEE: ERROR: {{.*}}main resumed between operations
// CHECK-TRYLOCK-IMMEDIATE: KLEE: ERROR: {{.*}}immediate EBUSY continuation
// CHECK-ALL-YIELDED: KLEE: ERROR: {{.*}}voluntary switch returned to main
