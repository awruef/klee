// Native pthread model: thread, mutex, and condition attributes are not
// modeled and fail closed instead of being ignored (review F14). A recursive
// mutex type treated as non-recursive would turn a legitimate relock into a
// model error, and a detached thread treated as joinable would accept an
// invalid join, so a non-null attribute pointer is itself a model error.
//
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.mutex.bc
// RUN: rm -rf %t.mutex
// RUN: %klee --output-dir=%t.mutex %t.mutex.bc 2>&1 | FileCheck %s --check-prefix=CHECK-MUTEX
// RUN: ls %t.mutex/*.model.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.thread.bc
// RUN: rm -rf %t.thread
// RUN: %klee --output-dir=%t.thread %t.thread.bc 2>&1 | FileCheck %s --check-prefix=CHECK-THREAD
// RUN: ls %t.thread/*.model.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.cond.bc
// RUN: rm -rf %t.cond
// RUN: %klee --output-dir=%t.cond %t.cond.bc 2>&1 | FileCheck %s --check-prefix=CHECK-COND
// RUN: ls %t.cond/*.model.err

#include <assert.h>
#include <pthread.h>

#include "klee/klee.h"

/* The attribute objects are never initialized: the attribute-manipulation
 * functions are not modeled either, and only the non-null pointer matters. */
static pthread_mutexattr_t mutex_attributes;
static pthread_attr_t thread_attributes;
static pthread_condattr_t condition_attributes;

#if CASE == 2
static void *worker(void *argument) {
  (void)argument;
  return 0;
}
#endif

int main(void) {
#if CASE == 1
  pthread_mutex_t mutex;
  pthread_mutex_init(&mutex, &mutex_attributes);
#elif CASE == 2
  pthread_t thread;
  pthread_create(&thread, &thread_attributes, worker, 0);
#elif CASE == 3
  pthread_cond_t condition;
  pthread_cond_init(&condition, &condition_attributes);
#endif
  return 0;
}

// CHECK-MUTEX: KLEE: ERROR: {{.*}}concurrency model error: pthread_mutex_init: mutex attributes are not modeled; pass a null attribute
// CHECK-THREAD: KLEE: ERROR: {{.*}}concurrency model error: pthread_create: thread attributes are not modeled; pass a null attribute
// CHECK-COND: KLEE: ERROR: {{.*}}concurrency model error: pthread_cond_init: condition attributes are not modeled; pass a null attribute
