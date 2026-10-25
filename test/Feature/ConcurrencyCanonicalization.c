// REQUIRES: not-darwin
// RUN: %clang %s -DCASE=1 -emit-llvm %O0opt -g -c -o %t.local-base.bc
// RUN: rm -rf %t.local-base
// RUN: %klee --output-dir=%t.local-base %t.local-base.bc 2>&1 | FileCheck %s --check-prefix=CHECK-TWO-CLEAN
// RUN: %clang %s -DCASE=2 -emit-llvm %O0opt -g -c -o %t.local-canonical.bc
// RUN: rm -rf %t.local-canonical
// RUN: %klee --output-dir=%t.local-canonical %t.local-canonical.bc 2>&1 | FileCheck %s --check-prefix=CHECK-ONE-CLEAN
// RUN: %clang %s -DCASE=3 -emit-llvm %O0opt -g -c -o %t.conflict.bc
// RUN: rm -rf %t.conflict
// RUN: %klee --emit-all-errors --output-dir=%t.conflict %t.conflict.bc 2>&1 | FileCheck %s --check-prefix=CHECK-TWO-RACES
// RUN: find %t.conflict -name '*.race.err' | count 2
// RUN: %clang %s -DCASE=4 -emit-llvm %O0opt -g -c -o %t.disjoint.bc
// RUN: rm -rf %t.disjoint
// RUN: %klee --output-dir=%t.disjoint %t.disjoint.bc 2>&1 | FileCheck %s --check-prefix=CHECK-TWO-CLEAN
// RUN: not ls %t.disjoint/*.err
// RUN: %clang %s -DCASE=5 -emit-llvm %O0opt -g -c -o %t.missing.bc
// RUN: rm -rf %t.missing
// RUN: %klee --output-dir=%t.missing %t.missing.bc 2>&1 | FileCheck %s --check-prefix=CHECK-MISSING
// RUN: ls %t.missing/*.model.err
// RUN: %clang %s -DCASE=6 -emit-llvm %O0opt -g -c -o %t.opaque.bc
// RUN: rm -rf %t.opaque
// RUN: %klee --output-dir=%t.opaque %t.opaque.bc 2>&1 | FileCheck %s --check-prefix=CHECK-TWO-CLEAN
// RUN: %clang %s -DCASE=7 -emit-llvm %O0opt -g -c -o %t.transitive.bc
// RUN: rm -rf %t.transitive
// RUN: %klee --emit-all-errors --output-dir=%t.transitive %t.transitive.bc 2>&1 | FileCheck %s --check-prefix=CHECK-SIX-RACES
// RUN: find %t.transitive -name '*.race.err' | count 6

#include <stdint.h>

#include "klee/ConcurrencyHarness.h"

static int shared[2];

static void run_two_transitions(int canonical, int transition_case) {
  unsigned char choices[2];
  struct klee_concurrency_driver driver;
  klee_make_symbolic(choices, sizeof(choices), "schedule_choices");
  klee_concurrency_create_thread(1);
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x3, 1);
  if (canonical)
    klee_concurrency_driver_enable_canonicalization(&driver);

  while (klee_concurrency_driver_live_mask(&driver) != 0) {
    for (uint64_t candidate = 0; candidate < 2; ++candidate) {
      const uint64_t bit = UINT64_C(1) << candidate;
      if ((klee_concurrency_driver_live_mask(&driver) & bit) == 0)
        continue;
      switch (transition_case) {
      case 0:
        klee_concurrency_driver_set_transition(
            &driver, candidate, KLEE_CONCURRENCY_TRANSITION_LOCAL, 0, 0);
        break;
      case 1:
        klee_concurrency_driver_set_transition(
            &driver, candidate,
            candidate == 0 ? KLEE_CONCURRENCY_TRANSITION_READ
                           : KLEE_CONCURRENCY_TRANSITION_WRITE,
            (uintptr_t)&shared[0], sizeof(shared[0]));
        break;
      case 2:
        klee_concurrency_driver_set_transition(
            &driver, candidate, KLEE_CONCURRENCY_TRANSITION_WRITE,
            (uintptr_t)&shared[candidate], sizeof(shared[candidate]));
        break;
      case 3:
        klee_concurrency_driver_set_transition(
            &driver, candidate, KLEE_CONCURRENCY_TRANSITION_OPAQUE, 0, 0);
        break;
      default:
        klee_abort();
      }
    }

    uint64_t thread = UINT64_MAX;
    if (klee_concurrency_driver_next(&driver, &thread) !=
        KLEE_CONCURRENCY_DRIVER_SCHEDULED)
      klee_abort();
    if (transition_case == 1) {
      if (thread == 0)
        klee_concurrency_read(&shared[0], sizeof(shared[0]), 100);
      else
        klee_concurrency_write(&shared[0], sizeof(shared[0]), 200);
    } else if (transition_case == 2) {
      klee_concurrency_write(&shared[thread], sizeof(shared[thread]),
                             300 + thread);
    }
    klee_concurrency_driver_finish(&driver, thread);
  }
}

static void run_transitive_dependency_chain(void) {
  unsigned char choices[3];
  struct klee_concurrency_driver driver;
  klee_make_symbolic(choices, sizeof(choices), "schedule_choices");
  klee_concurrency_create_thread(1);
  klee_concurrency_create_thread(2);
  klee_concurrency_driver_init(&driver, choices, sizeof(choices), 0x7, 2);
  klee_concurrency_driver_enable_canonicalization(&driver);

  while (klee_concurrency_driver_live_mask(&driver) != 0) {
    for (uint64_t candidate = 0; candidate < 3; ++candidate) {
      const uint64_t bit = UINT64_C(1) << candidate;
      if ((klee_concurrency_driver_live_mask(&driver) & bit) == 0)
        continue;
      const uintptr_t address =
          candidate == 2 ? (uintptr_t)&shared[1] : (uintptr_t)&shared[0];
      const uint64_t size =
          candidate == 1 ? sizeof(shared) : sizeof(shared[0]);
      klee_concurrency_driver_set_transition(
          &driver, candidate, KLEE_CONCURRENCY_TRANSITION_WRITE, address,
          size);
    }
    uint64_t thread = UINT64_MAX;
    if (klee_concurrency_driver_next(&driver, &thread) !=
        KLEE_CONCURRENCY_DRIVER_SCHEDULED)
      klee_abort();
    if (thread == 1)
      klee_concurrency_write(&shared[0], sizeof(shared), 410);
    else
      klee_concurrency_write(&shared[thread == 2], sizeof(shared[0]),
                             400 + thread);
    klee_concurrency_driver_finish(&driver, thread);
  }
}

int main(void) {
#if CASE == 1
  run_two_transitions(0, 0);
#elif CASE == 2
  run_two_transitions(1, 0);
#elif CASE == 3
  run_two_transitions(1, 1);
#elif CASE == 4
  run_two_transitions(1, 2);
#elif CASE == 5
  unsigned char choice;
  struct klee_concurrency_driver driver;
  uint64_t thread = UINT64_MAX;
  klee_make_symbolic(&choice, sizeof(choice), "schedule_choice");
  klee_concurrency_create_thread(1);
  klee_concurrency_driver_init(&driver, &choice, 1, 0x3, 1);
  klee_concurrency_driver_enable_canonicalization(&driver);
  klee_concurrency_driver_set_transition(
      &driver, 0, KLEE_CONCURRENCY_TRANSITION_LOCAL, 0, 0);
  (void)klee_concurrency_driver_next(&driver, &thread);
#elif CASE == 6
  run_two_transitions(1, 3);
#elif CASE == 7
  run_transitive_dependency_chain();
#else
#error "unknown CASE"
#endif
  return 0;
}

// CHECK-TWO-CLEAN: KLEE: done: completed paths = 2
// CHECK-TWO-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-ONE-CLEAN: KLEE: done: completed paths = 1
// CHECK-ONE-CLEAN: KLEE: done: partially completed paths = 0
// CHECK-TWO-RACES: KLEE: done: completed paths = 0
// CHECK-TWO-RACES: KLEE: done: partially completed paths = 2
// CHECK-MISSING: KLEE: ERROR: {{.*}}concurrency driver error: runnable thread has no transition descriptor
// CHECK-SIX-RACES: KLEE: done: completed paths = 0
// CHECK-SIX-RACES: KLEE: done: partially completed paths = 6
