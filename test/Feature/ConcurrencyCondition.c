// Trace condition-variable intrinsics: they share the pthread condition
// protocol and the traced-mutex table, so a wait releases the traced mutex,
// blocks until notified, and reacquires it; signal forks over the woken
// waiter; broadcast wakes all; a wait nobody can notify is a verified
// deadlock; waiting without the traced mutex, or outside the native pthread
// model, is a model error; a notification outside native mode is a no-op.
//
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.handshake.bc
// RUN: rm -rf %t.handshake
// RUN: %klee --emit-all-errors --output-dir=%t.handshake %t.handshake.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.handshake/*.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.orphan.bc
// RUN: rm -rf %t.orphan
// RUN: %klee --emit-all-errors --output-dir=%t.orphan %t.orphan.bc 2>&1 | FileCheck %s --check-prefix=CHECK-DEADLOCK
// RUN: ls %t.orphan/*.deadlock.err
// RUN: find %t.orphan -name '*.err' -not -name '*.deadlock.err' | count 0
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.broadcast.bc
// RUN: rm -rf %t.broadcast
// RUN: %klee --emit-all-errors --output-dir=%t.broadcast %t.broadcast.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.broadcast/*.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.nomutex.bc
// RUN: rm -rf %t.nomutex
// RUN: %klee --output-dir=%t.nomutex %t.nomutex.bc 2>&1 | FileCheck %s --check-prefix=CHECK-NOMUTEX
// RUN: ls %t.nomutex/*.model.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.signal-two.bc
// RUN: rm -rf %t.signal-two
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=2 --output-dir=%t.signal-two %t.signal-two.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.signal-two/*.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.nomode.bc
// RUN: rm -rf %t.nomode
// RUN: %klee --output-dir=%t.nomode %t.nomode.bc 2>&1 | FileCheck %s --check-prefix=CHECK-NOMODE
// RUN: ls %t.nomode/*.model.err
// RUN: %clang %s -DCASE=7 -emit-llvm %O0opt -g -c -o %t.notify-order.bc
// RUN: rm -rf %t.notify-order
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=0 --output-dir=%t.notify-order %t.notify-order.bc 2>&1 | FileCheck %s --check-prefix=CHECK-NOTIFY-RACE
// RUN: ls %t.notify-order/*.race.err
// RUN: find %t.notify-order -name '*.err' -not -name '*.race.err' | count 0
// RUN: %clang %s -DCASE=8 -emit-llvm %O0opt -g -c -o %t.destroy-after-notify.bc
// RUN: rm -rf %t.destroy-after-notify
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=0 --output-dir=%t.destroy-after-notify %t.destroy-after-notify.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.destroy-after-notify/*.err

#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <stdint.h>
#include <stdlib.h>

#include "klee/klee.h"

/* The traced mutex and condition are plain storage: only their addresses
 * matter to the engine, as for the std::condition_variable model. */
static uint64_t traced_mutex;
static uint64_t traced_condition;
static int ready;
static int consumed;
static int payload;
static uint64_t *dynamic_condition;

static void *waiter(void *argument) {
  (void)argument;
  klee_concurrency_mutex_lock(&traced_mutex);
  while (!ready)
    klee_concurrency_cond_wait(&traced_condition, &traced_mutex);
  klee_assert(ready);
  klee_concurrency_mutex_unlock(&traced_mutex);
  return 0;
}

#if CASE == 5
static void *consumer(void *argument) {
  (void)argument;
  klee_concurrency_mutex_lock(&traced_mutex);
  while (ready == 0)
    klee_concurrency_cond_wait(&traced_condition, &traced_mutex);
  --ready;
  ++consumed;
  klee_concurrency_mutex_unlock(&traced_mutex);
  return 0;
}
#endif

#if CASE == 7
static void *publication_waiter(void *argument) {
  (void)argument;
  klee_concurrency_mutex_lock(&traced_mutex);
  klee_concurrency_cond_wait(&traced_condition, &traced_mutex);
  klee_concurrency_read(&payload, sizeof(payload), 7002);
  (void)payload;
  klee_concurrency_mutex_unlock(&traced_mutex);
  return 0;
}
#endif

#if CASE == 8
static void *lifetime_waiter(void *argument) {
  (void)argument;
  klee_concurrency_mutex_lock(&traced_mutex);
  klee_concurrency_cond_wait(dynamic_condition, &traced_mutex);
  klee_concurrency_mutex_unlock(&traced_mutex);
  return 0;
}
#endif

#if CASE == 4
static void *wait_without_mutex(void *argument) {
  (void)argument;
  klee_concurrency_cond_wait(&traced_condition, &traced_mutex);
  return 0;
}
#endif

int main(void) {
  pthread_t threads[2];
#if CASE == 1
  klee_assert(pthread_create(&threads[0], 0, waiter, 0) == 0);
  klee_concurrency_mutex_lock(&traced_mutex);
  ready = 1;
  klee_concurrency_mutex_unlock(&traced_mutex);
  klee_concurrency_cond_signal(&traced_condition);
  klee_assert(pthread_join(threads[0], 0) == 0);
#elif CASE == 2
  klee_assert(pthread_create(&threads[0], 0, waiter, 0) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
#elif CASE == 3
  klee_assert(pthread_create(&threads[0], 0, waiter, 0) == 0);
  klee_assert(pthread_create(&threads[1], 0, waiter, 0) == 0);
  klee_concurrency_mutex_lock(&traced_mutex);
  ready = 1;
  klee_concurrency_cond_broadcast(&traced_condition);
  klee_concurrency_mutex_unlock(&traced_mutex);
  klee_assert(pthread_join(threads[0], 0) == 0);
  klee_assert(pthread_join(threads[1], 0) == 0);
#elif CASE == 4
  klee_assert(pthread_create(&threads[0], 0, wait_without_mutex, 0) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
#elif CASE == 5
  klee_assert(pthread_create(&threads[0], 0, consumer, 0) == 0);
  klee_assert(pthread_create(&threads[1], 0, consumer, 0) == 0);
  for (int item = 0; item < 2; ++item) {
    klee_concurrency_mutex_lock(&traced_mutex);
    ++ready;
    klee_concurrency_cond_signal(&traced_condition);
    klee_concurrency_mutex_unlock(&traced_mutex);
  }
  klee_assert(pthread_join(threads[0], 0) == 0);
  klee_assert(pthread_join(threads[1], 0) == 0);
  klee_assert(consumed == 2);
#elif CASE == 6
  /* No pthread operation has run: a notification is a no-op and a wait can
   * never be woken, so the wait is rejected rather than blocking forever. */
  klee_concurrency_cond_signal(&traced_condition);
  klee_concurrency_cond_broadcast(&traced_condition);
  klee_concurrency_mutex_lock(&traced_mutex);
  klee_concurrency_cond_wait(&traced_condition, &traced_mutex);
  klee_concurrency_mutex_unlock(&traced_mutex);
#elif CASE == 7
  /* At bound zero the explicit yield must run the new worker until its wait
   * blocks. notify_one unblocks it but does not publish the unprotected
   * payload write: only the associated mutex could provide that edge. */
  klee_assert(pthread_create(&threads[0], 0, publication_waiter, 0) == 0);
  klee_assert(sched_yield() == 0);
  klee_concurrency_write(&payload, sizeof(payload), 7001);
  payload = 1;
  klee_concurrency_cond_signal(&traced_condition);
  klee_assert(pthread_join(threads[0], 0) == 0);
#elif CASE == 8
  /* Once notification removes the waiter from the condition, the condition
   * object may die while that waiter is still reacquiring the mutex. The
   * engine's re-execution of the wait intrinsic must not resolve it again. */
  dynamic_condition = malloc(sizeof(*dynamic_condition));
  klee_assert(dynamic_condition != 0);
  klee_assert(pthread_create(&threads[0], 0, lifetime_waiter, 0) == 0);
  klee_assert(sched_yield() == 0);
  klee_concurrency_mutex_lock(&traced_mutex);
  klee_concurrency_cond_signal(dynamic_condition);
  free(dynamic_condition);
  klee_concurrency_mutex_unlock(&traced_mutex);
  klee_assert(pthread_join(threads[0], 0) == 0);
#endif
  (void)threads;
  return 0;
}

// CHECK-CLEAN-NOT: KLEE: ERROR
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-DEADLOCK: KLEE: ERROR: {{.*}}logical-thread deadlock: blocked mask 0x3; verified: every blocked thread waits on a mutex, join, or condition that no runnable thread can release
// CHECK-NOMUTEX: KLEE: ERROR: {{.*}}concurrency model error: klee_concurrency_cond_wait without owning the associated mutex
// CHECK-NOMODE: KLEE: ERROR: {{.*}}concurrency model error: klee_concurrency_cond_wait requires the native pthread model
// CHECK-NOTIFY-RACE: KLEE: ERROR: {{.*}}data race: thread 1 site 7002 read conflicts with thread 0 site 7001 write
