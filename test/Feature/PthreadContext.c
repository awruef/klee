// Native pthread context isolation: an open merge region belongs to the
// logical thread that opened it and must be suspended with that thread.
//
// The child-first pthread_create path is made infeasible. On the remaining
// path main opens a merge and yields to the child. The child's unmatched
// close must warn between its two markers; main's later close must consume
// its own saved merge without warning.
//
// RUN: %clang %s -emit-llvm %O0opt -g -c -o %t.bc
// RUN: rm -rf %t.out
// RUN: %klee --use-merge --search=dfs --concurrency-preemption-bound=1 --output-dir=%t.out %t.bc 2>&1 | FileCheck %s
// RUN: not ls %t.out/*.err

#include <assert.h>
#include <pthread.h>

#include "klee/klee.h"

static volatile int ready;
static volatile int worker_ran;

static void *worker(void *argument) {
  (void)argument;
  if (ready != 1)
    return 0;
  klee_warning("merge-worker-before");
  klee_close_merge();
  klee_warning("merge-worker-after");
  worker_ran = 1;
  return 0;
}

int main(void) {
  pthread_t thread;
  klee_assert(pthread_create(&thread, 0, worker, 0) == 0);
  ready = 1;
  klee_open_merge();
  klee_concurrency_yield();
  if (worker_ran != 1)
    return 0;
  klee_warning("merge-main-before");
  klee_close_merge();
  klee_warning("merge-main-after");
  klee_assert(pthread_join(thread, 0) == 0);
  return 0;
}

// CHECK: KLEE: WARNING: {{.*}}merge-worker-before
// CHECK: ran into a close at
// CHECK: KLEE: WARNING: {{.*}}merge-worker-after
// CHECK: KLEE: WARNING: {{.*}}merge-main-before
// CHECK-NOT: ran into a close at
// CHECK: KLEE: WARNING: {{.*}}merge-main-after
