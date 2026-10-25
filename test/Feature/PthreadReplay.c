// Native pthread model: an engine-generated klee_sched_N decision can be
// replayed with --replay-ktest-file. Under replay the recorded choice byte is
// concrete, so the scheduler must select the recorded candidate without
// asking Executor::branch to add constant-false constraints (review F10).
//
// One decision (main versus worker at pthread_create) gives two paths. The
// worker-first path is an error, the main-first path is clean. Replaying
// both KTests must reproduce exactly one error and two single-path runs.
//
// RUN: %clang %s -emit-llvm %O0opt -g -c -o %t.bc
// RUN: rm -rf %t.out %t.r1 %t.r2
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=1 --output-dir=%t.out %t.bc 2>&1 | FileCheck %s --check-prefix=EXPLORE
// RUN: find %t.out -name '*.order.err' | count 1
// RUN: find %t.out -name '*.ktest' | count 2
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=1 --replay-ktest-file=%t.out/test000001.ktest --output-dir=%t.r1 %t.bc > %t.r1.log 2>&1
// RUN: %klee --emit-all-errors --concurrency-preemption-bound=1 --replay-ktest-file=%t.out/test000002.ktest --output-dir=%t.r2 %t.bc > %t.r2.log 2>&1
// RUN: cat %t.r1.log %t.r2.log | FileCheck %s --check-prefix=REPLAY
// RUN: find %t.r1 %t.r2 -name '*.order.err' | count 1
// RUN: find %t.r1 %t.r2 -name '*.ktest' | count 2

#include <assert.h>
#include <pthread.h>

#include "klee/klee.h"

static volatile int worker_ran;

static void *worker(void *argument) {
  (void)argument;
  worker_ran = 1;
  return 0;
}

int main(void) {
  pthread_t thread;
  klee_assert(pthread_create(&thread, 0, worker, 0) == 0);
  if (worker_ran)
    klee_report_error(__FILE__, __LINE__, "worker ran before main continued",
                      "order.err");
  klee_assert(pthread_join(thread, 0) == 0);
  return 0;
}

// EXPLORE: KLEE: ERROR: {{.*}}worker ran before main continued
// EXPLORE: KLEE: done: completed paths = 1
// EXPLORE: KLEE: done: partially completed paths = 1
// EXPLORE: KLEE: done: generated tests = 2

// Each replay follows its recorded decision: one path, one test, no fork.
// REPLAY-NOT: LLVM ERROR
// REPLAY-NOT: replay count mismatch
// REPLAY: KLEE: done: generated tests = 1
// REPLAY-NOT: LLVM ERROR
// REPLAY-NOT: replay count mismatch
// REPLAY: KLEE: done: generated tests = 1
