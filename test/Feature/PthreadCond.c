// Native pthread condition variables: wait releases and reacquires the
// mutex, signal wakes one waiter (forking over which), broadcast wakes all,
// a wait nobody can signal is a verified deadlock, and waiting without the
// mutex is a model error.
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

#include <assert.h>
#include <pthread.h>
#include <stdint.h>

#include "klee/klee.h"

static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t condition = PTHREAD_COND_INITIALIZER;
static int ready;
static int consumed;

static void *waiter(void *argument) {
  (void)argument;
  klee_assert(pthread_mutex_lock(&mutex) == 0);
  while (!ready)
    klee_assert(pthread_cond_wait(&condition, &mutex) == 0);
  klee_assert(ready);
  klee_assert(pthread_mutex_unlock(&mutex) == 0);
  return 0;
}

#if CASE == 5
/* Each item must be consumed by exactly one waiter; a signal with two
 * waiters forks over which one wakes, and the loop guards against the
 * other waking spuriously. */
static void *consumer(void *argument) {
  (void)argument;
  klee_assert(pthread_mutex_lock(&mutex) == 0);
  while (ready == 0)
    klee_assert(pthread_cond_wait(&condition, &mutex) == 0);
  --ready;
  ++consumed;
  klee_assert(pthread_mutex_unlock(&mutex) == 0);
  return 0;
}
#endif

#if CASE == 4
static void *wait_without_mutex(void *argument) {
  (void)argument;
  pthread_cond_wait(&condition, &mutex);
  return 0;
}
#endif

int main(void) {
  pthread_t threads[2];
#if CASE == 1
  klee_assert(pthread_create(&threads[0], 0, waiter, 0) == 0);
  klee_assert(pthread_mutex_lock(&mutex) == 0);
  ready = 1;
  klee_assert(pthread_cond_signal(&condition) == 0);
  klee_assert(pthread_mutex_unlock(&mutex) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
#elif CASE == 2
  klee_assert(pthread_create(&threads[0], 0, waiter, 0) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
#elif CASE == 3
  klee_assert(pthread_create(&threads[0], 0, waiter, 0) == 0);
  klee_assert(pthread_create(&threads[1], 0, waiter, 0) == 0);
  klee_assert(pthread_mutex_lock(&mutex) == 0);
  ready = 1;
  klee_assert(pthread_cond_broadcast(&condition) == 0);
  klee_assert(pthread_mutex_unlock(&mutex) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
  klee_assert(pthread_join(threads[1], 0) == 0);
#elif CASE == 4
  klee_assert(pthread_create(&threads[0], 0, wait_without_mutex, 0) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
#elif CASE == 5
  klee_assert(pthread_create(&threads[0], 0, consumer, 0) == 0);
  klee_assert(pthread_create(&threads[1], 0, consumer, 0) == 0);
  for (int item = 0; item < 2; ++item) {
    klee_assert(pthread_mutex_lock(&mutex) == 0);
    ++ready;
    klee_assert(pthread_cond_signal(&condition) == 0);
    klee_assert(pthread_mutex_unlock(&mutex) == 0);
  }
  klee_assert(pthread_join(threads[0], 0) == 0);
  klee_assert(pthread_join(threads[1], 0) == 0);
  klee_assert(consumed == 2);
#endif
  return 0;
}

// CHECK-CLEAN-NOT: KLEE: ERROR
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-DEADLOCK: KLEE: ERROR: {{.*}}logical-thread deadlock: blocked mask 0x3; verified: every blocked thread waits on a mutex, join, or condition that no runnable thread can release
// CHECK-NOMUTEX: KLEE: ERROR: {{.*}}concurrency model error: pthread_cond_wait without owning the associated mutex
