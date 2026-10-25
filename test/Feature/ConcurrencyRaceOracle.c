// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.case1.bc
// RUN: rm -rf %t.case1
// RUN: %klee --emit-all-errors --output-dir=%t.case1 %t.case1.bc 2>&1 | FileCheck %s --check-prefix=CHECK-RACE
// RUN: ls %t.case1/*.race.err
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.case2.bc
// RUN: rm -rf %t.case2
// RUN: %klee --output-dir=%t.case2 %t.case2.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.case2/*.race.err
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.case3.bc
// RUN: rm -rf %t.case3
// RUN: %klee --output-dir=%t.case3 %t.case3.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.case3/*.race.err
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.case4.bc
// RUN: rm -rf %t.case4
// RUN: %klee --output-dir=%t.case4 %t.case4.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.case4/*.race.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.case5.bc
// RUN: rm -rf %t.case5
// RUN: %klee --output-dir=%t.case5 %t.case5.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: not ls %t.case5/*.race.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.case6.bc
// RUN: rm -rf %t.case6
// RUN: %klee --emit-all-errors --output-dir=%t.case6 %t.case6.bc 2>&1 | FileCheck %s --check-prefix=CHECK-FORK
// RUN: ls %t.case6/*.race.err
// RUN: %clang %s -DCASE=7 -emit-llvm %O0opt -g -c -o %t.case7.bc
// RUN: rm -rf %t.case7
// RUN: %klee --emit-all-errors --output-dir=%t.case7 %t.case7.bc 2>&1 | FileCheck %s --check-prefix=CHECK-OVERLAP
// RUN: ls %t.case7/*.race.err
// RUN: %clang %s -DCASE=8 -emit-llvm %O0opt -g -c -o %t.case8.bc
// RUN: rm -rf %t.case8
// RUN: %klee --output-dir=%t.case8 %t.case8.bc 2>&1 | FileCheck %s --check-prefix=CHECK-NONOWNER
// RUN: ls %t.case8/*.model.err
// RUN: %clang %s -DCASE=9 -emit-llvm %O0opt -g -c -o %t.case9.bc
// RUN: rm -rf %t.case9
// RUN: %klee --output-dir=%t.case9 %t.case9.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SYMBOLIC-ID
// RUN: ls %t.case9/*.user.err

#include <stddef.h>
#include <stdint.h>
#include "klee/klee.h"

static int shared_values[2];
static int mutex_object;

int main(void) {
#if CASE == 1
  /* Calibration for GetSessionBuff: an unlocked read still races with a
     writer merely because the writer holds a mutex. */
  klee_concurrency_create_thread(1);
  klee_concurrency_read(&shared_values[0], sizeof(shared_values[0]), 100);
  klee_concurrency_set_thread(1);
  klee_concurrency_mutex_lock(&mutex_object);
  klee_concurrency_write(&shared_values[0], sizeof(shared_values[0]), 200);
  klee_concurrency_mutex_unlock(&mutex_object);
#elif CASE == 2
  /* Read/read overlap is not a race. */
  klee_concurrency_create_thread(1);
  klee_concurrency_read(&shared_values[0], sizeof(shared_values[0]), 300);
  klee_concurrency_set_thread(1);
  klee_concurrency_read(&shared_values[0], sizeof(shared_values[0]), 301);
#elif CASE == 3
  /* A release followed by an acquire orders conflicting accesses. */
  klee_concurrency_create_thread(1);
  klee_concurrency_mutex_lock(&mutex_object);
  klee_concurrency_write(&shared_values[0], sizeof(shared_values[0]), 400);
  klee_concurrency_mutex_unlock(&mutex_object);
  klee_concurrency_set_thread(1);
  klee_concurrency_mutex_lock(&mutex_object);
  klee_concurrency_read(&shared_values[0], sizeof(shared_values[0]), 401);
  klee_concurrency_mutex_unlock(&mutex_object);
#elif CASE == 4
  /* Adjacent, non-overlapping ranges must not conflict. */
  klee_concurrency_create_thread(1);
  klee_concurrency_write(&shared_values[0], sizeof(shared_values[0]), 500);
  klee_concurrency_set_thread(1);
  klee_concurrency_write(&shared_values[1], sizeof(shared_values[1]), 501);
#elif CASE == 5
  /* Spawn orders earlier parent accesses; join orders completed child
     accesses before later parent accesses. */
  klee_concurrency_write(&shared_values[0], sizeof(shared_values[0]), 600);
  klee_concurrency_create_thread(1);
  klee_concurrency_set_thread(1);
  klee_concurrency_read(&shared_values[0], sizeof(shared_values[0]), 601);
  klee_concurrency_write(&shared_values[1], sizeof(shared_values[1]), 602);
  klee_concurrency_finish_thread();
  klee_concurrency_set_thread(0);
  klee_concurrency_join_thread(1);
  klee_concurrency_read(&shared_values[1], sizeof(shared_values[1]), 603);
#elif CASE == 6
  /* The concurrency state must clone with a symbolic execution fork. One
     schedule shape is racy; the common-mutex shape is clean. */
  unsigned char schedule_shape;
  klee_make_symbolic(&schedule_shape, sizeof(schedule_shape), "schedule_shape");
  klee_assume(schedule_shape < 2);
  klee_concurrency_create_thread(1);
  if (schedule_shape == 0) {
    klee_concurrency_read(&shared_values[0], sizeof(shared_values[0]), 700);
    klee_concurrency_set_thread(1);
    klee_concurrency_mutex_lock(&mutex_object);
    klee_concurrency_write(&shared_values[0], sizeof(shared_values[0]), 701);
  } else {
    klee_concurrency_mutex_lock(&mutex_object);
    klee_concurrency_write(&shared_values[0], sizeof(shared_values[0]), 710);
    klee_concurrency_mutex_unlock(&mutex_object);
    klee_concurrency_set_thread(1);
    klee_concurrency_mutex_lock(&mutex_object);
    klee_concurrency_read(&shared_values[0], sizeof(shared_values[0]), 711);
    klee_concurrency_mutex_unlock(&mutex_object);
  }
#elif CASE == 7
  /* Overlap is byte-range based, not limited to equal start addresses. */
  klee_concurrency_create_thread(1);
  klee_concurrency_write(&shared_values[0], sizeof(shared_values[0]), 800);
  klee_concurrency_set_thread(1);
  klee_concurrency_write((char *)&shared_values[0] + 2, 2, 801);
#elif CASE == 8
  /* Impossible schedules are model errors, not false race reports. */
  klee_concurrency_create_thread(1);
  klee_concurrency_mutex_lock(&mutex_object);
  klee_concurrency_set_thread(1);
  klee_concurrency_mutex_unlock(&mutex_object);
#elif CASE == 9
  /* IDs select model entities, so unconstrained symbolic IDs are rejected. */
  uint64_t thread_id;
  klee_make_symbolic(&thread_id, sizeof(thread_id), "thread_id");
  klee_concurrency_create_thread(thread_id);
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-RACE: KLEE: ERROR: {{.*}}data race: thread 1 site 200 write conflicts with thread 0 site 100 read
// CHECK-CLEAN: KLEE: done: completed paths = 1
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-FORK: KLEE: ERROR: {{.*}}data race: thread 1 site 701 write conflicts with thread 0 site 700 read
// CHECK-FORK: KLEE: done: completed paths = 1
// CHECK-OVERLAP: KLEE: ERROR: {{.*}}data race: thread 1 site 801 write conflicts with thread 0 site 800 write
// CHECK-NONOWNER: KLEE: ERROR: {{.*}}concurrency model error: logical mutex unlock by a non-owner
// CHECK-SYMBOLIC-ID: KLEE: ERROR: {{.*}}klee_concurrency_create_thread requires a concrete thread id
