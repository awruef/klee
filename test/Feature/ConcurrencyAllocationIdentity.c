// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.default.bc
// RUN: rm -rf %t.default
// RUN: %klee --output-dir=%t.default %t.default.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: find %t.default -name '*.err' | count 0
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.mutex.bc
// RUN: rm -rf %t.mutex
// RUN: %klee --emit-all-errors --output-dir=%t.mutex %t.mutex.bc 2>&1 | FileCheck %s --check-prefix=CHECK-RACE
// RUN: find %t.mutex -name '*.race.err' | count 1
// RUN: find %t.mutex -name '*.model.err' | count 0
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.q0.bc
// RUN: rm -rf %t.q0
// RUN: %klee --kdalloc-quarantine=0 --output-dir=%t.q0 %t.q0.bc 2>&1 | FileCheck %s --check-prefix=CHECK-CLEAN
// RUN: find %t.q0 -name '*.err' | count 0

#include <stdint.h>
#include <stdlib.h>

#include "klee/klee.h"

static int shared;

static void require_reuse(uintptr_t first, uintptr_t reused) {
  if (first != reused)
    klee_report_error(__FILE__, __LINE__,
                      "deterministic allocator did not reuse expected address",
                      "model.err");
}

static void access_reuse_default(void) {
  uintptr_t first = 0;
  klee_concurrency_create_thread(1);
  for (int i = 0; i < 9; ++i) {
    char *allocation = (char *)malloc(16);
    if (allocation == 0)
      klee_abort();
    if (i == 0)
      first = (uintptr_t)allocation;
    klee_concurrency_write(allocation, 16, 100 + (uint64_t)i);
    free(allocation);
  }
  klee_concurrency_set_thread(1);
  char *reused = (char *)malloc(16);
  if (reused == 0)
    klee_abort();
  require_reuse(first, (uintptr_t)reused);
  klee_concurrency_write(reused, 16, 200);
  free(reused);
}

static void mutex_reuse_default(void) {
  klee_concurrency_create_thread(1);
  klee_concurrency_write(&shared, sizeof(shared), 300);

  void *first_allocation = malloc(16);
  if (first_allocation == 0)
    klee_abort();
  const uintptr_t first = (uintptr_t)first_allocation;
  klee_concurrency_mutex_lock(first_allocation);
  klee_concurrency_mutex_unlock(first_allocation);
  free(first_allocation);
  for (int i = 0; i < 8; ++i) {
    void *allocation = malloc(16);
    if (allocation == 0)
      klee_abort();
    free(allocation);
  }

  klee_concurrency_set_thread(1);
  void *reused = malloc(16);
  if (reused == 0)
    klee_abort();
  require_reuse(first, (uintptr_t)reused);
  klee_concurrency_mutex_lock(reused);
  klee_concurrency_write(&shared, sizeof(shared), 301);
}

static void access_reuse_without_quarantine(void) {
  klee_concurrency_create_thread(1);
  char *first_allocation = (char *)malloc(16);
  if (first_allocation == 0)
    klee_abort();
  const uintptr_t first = (uintptr_t)first_allocation;
  klee_concurrency_write(first_allocation, 16, 400);
  free(first_allocation);

  klee_concurrency_set_thread(1);
  char *reused = (char *)malloc(16);
  if (reused == 0)
    klee_abort();
  require_reuse(first, (uintptr_t)reused);
  klee_concurrency_write(reused, 16, 401);
  free(reused);
}

int main(void) {
#if CASE == 1
  access_reuse_default();
#elif CASE == 2
  mutex_reuse_default();
#elif CASE == 3
  access_reuse_without_quarantine();
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-CLEAN: KLEE: done: completed paths = 1
// CHECK-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-RACE: KLEE: ERROR: {{.*}}data race: thread 1 site 301 write conflicts with thread 0 site 300 write
// CHECK-RACE: KLEE: done: completed paths = 0
// CHECK-RACE: KLEE: done: partially completed paths = 1
