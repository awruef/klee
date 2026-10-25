// Native pthread mutexes: blocking acquisition, happens-before for the race
// oracle, verified lock-order deadlocks, and misuse diagnostics.
//
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.locked.bc
// RUN: rm -rf %t.locked
// RUN: %klee --emit-all-errors --output-dir=%t.locked %t.locked.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.locked/*.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.unlocked.bc
// RUN: rm -rf %t.unlocked
// RUN: %klee --emit-all-errors --output-dir=%t.unlocked %t.unlocked.bc 2>&1 | FileCheck %s --check-prefix=CHECK-RACE
// RUN: ls %t.unlocked/*.race.err
// RUN: find %t.unlocked -name '*.err' -not -name '*.race.err' -not -name '*.assert.err' | count 0
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.order.bc
// RUN: rm -rf %t.order
// RUN: %klee --emit-all-errors --output-dir=%t.order %t.order.bc 2>&1 | FileCheck %s --check-prefix=CHECK-DEADLOCK
// RUN: ls %t.order/*.deadlock.err
// RUN: grep -q 'Thread 2 (blocked)' %t.order/*.deadlock.err
// RUN: not grep -q 'suspended' %t.order/*.deadlock.err
// RUN: find %t.order -name '*.err' -not -name '*.deadlock.err' | count 0
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.nonowner.bc
// RUN: rm -rf %t.nonowner
// RUN: %klee --output-dir=%t.nonowner %t.nonowner.bc 2>&1 | FileCheck %s --check-prefix=CHECK-NONOWNER
// RUN: ls %t.nonowner/*.model.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.relock.bc
// RUN: rm -rf %t.relock
// RUN: %klee --output-dir=%t.relock %t.relock.bc 2>&1 | FileCheck %s --check-prefix=CHECK-RELOCK
// RUN: ls %t.relock/*.model.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.trylock.bc
// RUN: rm -rf %t.trylock
// RUN: %klee --emit-all-errors --output-dir=%t.trylock %t.trylock.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.trylock/*.err
// RUN: %clang %s -DCASE=7 -emit-llvm %O0opt -g -c -o %t.reinit.bc
// RUN: rm -rf %t.reinit
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=0 --output-dir=%t.reinit %t.reinit.bc 2>&1 | FileCheck %s --check-prefix=CHECK-REINIT
// RUN: ls %t.reinit/*.race.err
// RUN: find %t.reinit -name '*.err' -not -name '*.race.err' | count 0
// RUN: %clang %s -DCASE=8 -emit-llvm %O0opt -g -c -o %t.destroyed.bc
// RUN: rm -rf %t.destroyed
// RUN: %klee --output-dir=%t.destroyed %t.destroyed.bc 2>&1 | FileCheck %s --check-prefix=CHECK-DESTROYED
// RUN: ls %t.destroyed/*.model.err
// RUN: %clang %s -DCASE=9 -emit-llvm %O0opt -g -c -o %t.double-init.bc
// RUN: rm -rf %t.double-init
// RUN: %klee --output-dir=%t.double-init %t.double-init.bc 2>&1 | FileCheck %s --check-prefix=CHECK-DOUBLE-INIT
// RUN: ls %t.double-init/*.model.err
// RUN: %clang %s -DCASE=10 -emit-llvm %O0opt -g -c -o %t.traced.bc
// RUN: rm -rf %t.traced
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=2 --output-dir=%t.traced %t.traced.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.traced/*.err

#include <errno.h>
#include <assert.h>
#include <pthread.h>
#include <stdint.h>

#include "klee/klee.h"

static int shared;
static pthread_mutex_t first_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t second_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t recycled_mutex = PTHREAD_MUTEX_INITIALIZER;
static int generation_shared;
static int traced_mutex;
static int traced_shared;

#if CASE == 1 || CASE == 2
static void *increment(void *argument) {
  (void)argument;
#if CASE == 1
  klee_assert(pthread_mutex_lock(&first_mutex) == 0);
#endif

  klee_concurrency_read(&shared, sizeof(shared), 1);
  int value = shared;
  klee_concurrency_yield();
  klee_concurrency_write(&shared, sizeof(shared), 2);
  shared = value + 1;
#if CASE == 1
  klee_assert(pthread_mutex_unlock(&first_mutex) == 0);
#endif
  return 0;
}
#endif

#if CASE == 10
static void *traced_increment(void *argument) {
  (void)argument;
  klee_concurrency_mutex_lock(&traced_mutex);
  klee_concurrency_read(&traced_shared, sizeof(traced_shared), 1001);
  int value = traced_shared;
  klee_concurrency_yield();
  klee_concurrency_write(&traced_shared, sizeof(traced_shared), 1002);
  traced_shared = value + 1;
  klee_concurrency_mutex_unlock(&traced_mutex);
  return 0;
}
#endif

#if CASE == 7
static void *write_new_generation(void *argument) {
  (void)argument;
  klee_assert(pthread_mutex_lock(&recycled_mutex) == 0);
  klee_concurrency_write(&generation_shared, sizeof(generation_shared), 702);
  generation_shared = 2;
  klee_assert(pthread_mutex_unlock(&recycled_mutex) == 0);
  return 0;
}
#endif

#if CASE == 3
static void *lock_first_then_second(void *argument) {
  (void)argument;
  klee_assert(pthread_mutex_lock(&first_mutex) == 0);
  klee_concurrency_yield();
  klee_assert(pthread_mutex_lock(&second_mutex) == 0);
  klee_assert(pthread_mutex_unlock(&second_mutex) == 0);
  klee_assert(pthread_mutex_unlock(&first_mutex) == 0);
  return 0;
}

static void *lock_second_then_first(void *argument) {
  (void)argument;
  klee_assert(pthread_mutex_lock(&second_mutex) == 0);
  klee_concurrency_yield();
  klee_assert(pthread_mutex_lock(&first_mutex) == 0);
  klee_assert(pthread_mutex_unlock(&first_mutex) == 0);
  klee_assert(pthread_mutex_unlock(&second_mutex) == 0);
  return 0;
}
#endif

#if CASE == 4
static void *unlock_foreign(void *argument) {
  (void)argument;
  pthread_mutex_unlock(&first_mutex);
  return 0;
}
#endif

#if CASE == 6
static int trylock_results[2];

static void *trylock_worker(void *argument) {
  const int index = (int)(intptr_t)argument;
  const int result = pthread_mutex_trylock(&first_mutex);
  klee_assert(result == 0 || result == EBUSY);
  trylock_results[index] = result;
  if (result == 0)
    klee_assert(pthread_mutex_unlock(&first_mutex) == 0);
  return 0;
}
#endif

int main(void) {
  pthread_t threads[2];
#if CASE == 1 || CASE == 2
  klee_assert(pthread_create(&threads[0], 0, increment, 0) == 0);
  klee_assert(pthread_create(&threads[1], 0, increment, 0) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
  klee_assert(pthread_join(threads[1], 0) == 0);
#if CASE == 1
  /* The mutex orders the two read-modify-write pairs. */
  klee_assert(shared == 2);
#endif
#elif CASE == 3
  klee_assert(pthread_create(&threads[0], 0, lock_first_then_second, 0) == 0);
  klee_assert(pthread_create(&threads[1], 0, lock_second_then_first, 0) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
  klee_assert(pthread_join(threads[1], 0) == 0);
#elif CASE == 4
  klee_assert(pthread_mutex_lock(&first_mutex) == 0);
  klee_assert(pthread_create(&threads[0], 0, unlock_foreign, 0) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
  klee_assert(pthread_mutex_unlock(&first_mutex) == 0);
#elif CASE == 5
  klee_assert(pthread_mutex_lock(&first_mutex) == 0);
  pthread_mutex_lock(&first_mutex);
#elif CASE == 6
  klee_assert(pthread_mutex_lock(&first_mutex) == 0);
  klee_assert(pthread_create(&threads[0], 0, trylock_worker, (void *)0) == 0);
  klee_assert(pthread_mutex_unlock(&first_mutex) == 0);
  klee_assert(pthread_create(&threads[1], 0, trylock_worker, (void *)1) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
  klee_assert(pthread_join(threads[1], 0) == 0);
#elif CASE == 7
  /* The child is created before the old generation's write but cannot run
   * under bound zero until main blocks in join. The new mutex generation
   * must not import the old unlock clock, so the writes remain unordered. */
  klee_assert(pthread_create(&threads[0], 0, write_new_generation, 0) == 0);
  klee_assert(pthread_mutex_lock(&recycled_mutex) == 0);
  klee_concurrency_write(&generation_shared, sizeof(generation_shared), 701);
  generation_shared = 1;
  klee_assert(pthread_mutex_unlock(&recycled_mutex) == 0);
  klee_assert(pthread_mutex_destroy(&recycled_mutex) == 0);
  klee_assert(pthread_mutex_init(&recycled_mutex, 0) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
#elif CASE == 8
  klee_assert(pthread_mutex_destroy(&recycled_mutex) == 0);
  pthread_mutex_lock(&recycled_mutex);
#elif CASE == 9
  pthread_mutex_t dynamic_mutex;
  klee_assert(pthread_mutex_init(&dynamic_mutex, 0) == 0);
  pthread_mutex_init(&dynamic_mutex, 0);
#elif CASE == 10
  klee_concurrency_mutex_lock(&traced_mutex);
  klee_concurrency_mutex_unlock(&traced_mutex);
  klee_assert(pthread_create(&threads[0], 0, traced_increment, 0) == 0);
  klee_assert(pthread_create(&threads[1], 0, traced_increment, 0) == 0);
  klee_assert(pthread_join(threads[0], 0) == 0);
  klee_assert(pthread_join(threads[1], 0) == 0);
  klee_assert(traced_shared == 2);
#endif
  return 0;
}

// CHECK-CLEAN-NOT: KLEE: ERROR
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-RACE: KLEE: ERROR: {{.*}}data race: thread {{[12]}} site {{[12]}} {{read|write}} conflicts with thread {{[12]}} site {{[12]}} {{read|write}}
// CHECK-DEADLOCK: KLEE: ERROR: {{.*}}logical-thread deadlock: blocked mask 0x7; verified: every blocked thread waits on a mutex, join, or condition that no runnable thread can release
// CHECK-NONOWNER: KLEE: ERROR: {{.*}}concurrency model error: logical mutex unlock by a non-owner
// CHECK-RELOCK: KLEE: ERROR: {{.*}}concurrency model error: pthread_mutex_lock: the calling thread already owns this non-recursive mutex
// CHECK-REINIT: KLEE: ERROR: {{.*}}data race: thread 1 site 702 write conflicts with thread 0 site 701 write
// CHECK-DESTROYED: KLEE: ERROR: {{.*}}concurrency model error: logical mutex lock after pthread_mutex_destroy
// CHECK-DOUBLE-INIT: KLEE: ERROR: {{.*}}concurrency model error: pthread_mutex_init on an initialized mutex
