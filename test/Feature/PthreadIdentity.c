// Native pthread model: pthread_self and pthread_equal are mode gates but not
// scheduling boundaries (review F12). With one preemption, a worker and a
// main thread that queries its identity eight times before joining give
// exactly two schedules (worker first, or main through to its join); if the
// queries were boundaries there would be ten.
//
// RUN: %clang %s -emit-llvm %O0opt -g -c -o %t.bc
// RUN: rm -rf %t.out
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=1 --output-dir=%t.out %t.bc 2>&1 | FileCheck %s
// RUN: not ls %t.out/*.err

#include <assert.h>
#include <pthread.h>

#include "klee/klee.h"

static volatile int progress;

static void *worker(void *argument) {
  (void)argument;
  klee_assert(!pthread_equal(pthread_self(), (pthread_t)0));
  progress = 1;
  return 0;
}

int main(void) {
  pthread_t thread;
  const pthread_t self = pthread_self();
  klee_assert(pthread_equal(self, (pthread_t)0));
  klee_assert(pthread_create(&thread, 0, worker, 0) == 0);
  for (int round = 0; round < 8; ++round) {
    klee_assert(pthread_equal(pthread_self(), self));
    klee_assert(!pthread_equal(thread, self));
  }
  klee_assert(pthread_join(thread, 0) == 0);
  klee_assert(progress == 1);
  return 0;
}

// CHECK-NOT: KLEE: ERROR
// CHECK: KLEE: done: completed paths = 2
// CHECK: KLEE: done: partially completed paths = 0
