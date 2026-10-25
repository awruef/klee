// Native pthread model: two threads are suspended inside nested calls while
// the other runs, and resume with their locals intact. The lost update
// (shared == 1) requires a thread to be preempted between its read and its
// write, so it is unreachable with a zero preemption bound and reachable
// with one.
//
// RUN: %clang %s -emit-llvm %O0opt -g -c -o %t.bc
// RUN: rm -rf %t.b0 %t.b1 %t.b2
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=0 --output-dir=%t.b0 %t.bc 2>&1 | FileCheck %s --check-prefix=CHECK-B0
// RUN: not ls %t.b0/*.err
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=1 --output-dir=%t.b1 %t.bc 2>&1 | FileCheck %s --check-prefix=CHECK-B1
// RUN: ls %t.b1/*.assert.err
// RUN: find %t.b1 -name '*.err' -not -name '*.assert.err' | count 0
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=2 --output-dir=%t.b2 %t.bc 2>&1 | FileCheck %s --check-prefix=CHECK-B2
// RUN: ls %t.b2/*.assert.err
// RUN: find %t.b2 -name '*.err' -not -name '*.assert.err' | count 0

#include <assert.h>
#include <pthread.h>
#include <stdint.h>

#include "klee/klee.h"

static int shared;

static int read_shared(void) {
  volatile int snapshot = shared;
  return snapshot;
}

static void step(int id, int *value) {
  /* Frame-local state that must survive a context switch. */
  int guard[4] = {id, id + 1, id + 2, id + 3};
  klee_concurrency_yield();
  klee_assert(guard[0] == id && guard[3] == id + 3);
  shared = *value + 1;
}

static void *worker(void *argument) {
  const int id = (int)(intptr_t)argument;
  int value = read_shared();
  step(id, &value);
  return (void *)(intptr_t)(id * 100);
}

int main(void) {
  pthread_t first, second;
  void *first_result = 0;
  void *second_result = 0;
  klee_assert(pthread_create(&first, 0, worker, (void *)1) == 0);
  klee_assert(pthread_create(&second, 0, worker, (void *)2) == 0);
  klee_assert(!pthread_equal(first, second));
  klee_assert(pthread_join(first, &first_result) == 0);
  klee_assert(pthread_join(second, &second_result) == 0);
  klee_assert(first_result == (void *)100);
  klee_assert(second_result == (void *)200);
  /* Fails exactly when one thread's write is lost to the other's. */
  klee_assert(shared == 2);
  return 0;
}

// Bound 0: main is the anchor from the start, so it keeps running until its
// first join blocks. The two workers may then run in either order. If the
// joined worker finishes first, main is woken and the decision forks over
// main versus the other worker (two schedules); if the other worker finishes
// first, main stays blocked and the joined worker is the only candidate (one
// schedule): three schedules in total.
// CHECK-B0: KLEE: done: completed paths = 3
// CHECK-B0: KLEE: done: partially completed paths = 0
// Error terminations count as partially completed paths.
// CHECK-B1: KLEE: ERROR: {{.*}}ASSERTION FAIL: shared == 2
// CHECK-B1: KLEE: done: completed paths = {{[0-9]+}}
// CHECK-B2: KLEE: ERROR: {{.*}}ASSERTION FAIL: shared == 2
// CHECK-B2: KLEE: done: completed paths = {{[0-9]+}}
