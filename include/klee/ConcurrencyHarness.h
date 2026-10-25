//===-- ConcurrencyHarness.h ------------------------------------*- C -*-===//
//
// Small cooperative driver for bounded logical-thread KLEE harnesses.
// This is harness support, not an operating-system thread implementation.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_CONCURRENCY_HARNESS_H
#define KLEE_CONCURRENCY_HARNESS_H

#include "klee/klee.h"

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

enum klee_concurrency_driver_result {
  KLEE_CONCURRENCY_DRIVER_BOUND = -1,
  KLEE_CONCURRENCY_DRIVER_COMPLETE = 0,
  KLEE_CONCURRENCY_DRIVER_SCHEDULED = 1,
};

enum klee_concurrency_transition_kind {
  /* Opaque transitions may perform arbitrary traced operations. */
  KLEE_CONCURRENCY_TRANSITION_OPAQUE = 0,
  /* Local transitions may not perform a traced access or synchronization. */
  KLEE_CONCURRENCY_TRANSITION_LOCAL = 1,
  KLEE_CONCURRENCY_TRANSITION_READ = 2,
  KLEE_CONCURRENCY_TRANSITION_WRITE = 3,
  KLEE_CONCURRENCY_TRANSITION_MUTEX = 4,
};

struct klee_concurrency_transition {
  enum klee_concurrency_transition_kind kind;
  uintptr_t address;
  uint64_t size;
};

struct klee_concurrency_driver {
  const unsigned char *choices;
  uint64_t choice_count;
  uint64_t next_choice;
  uint64_t live_mask;
  uint64_t blocked_mask;
  uint64_t max_switches;
  uint64_t transition_valid_mask;
  struct klee_concurrency_transition transitions[64];
  uint64_t last_scheduled_thread;
  unsigned schedule_started;
  unsigned canonicalization_enabled;
};

__attribute__((noreturn)) static inline void
klee_concurrency_driver_error(const char *message) {
  klee_report_error(__FILE__, __LINE__, message, "model.err");
}

static inline uint64_t klee_concurrency_driver_thread_bit(uint64_t thread) {
  if (thread >= 64)
    klee_concurrency_driver_error(
        "concurrency driver error: thread id does not fit the scheduler mask");
  return UINT64_C(1) << thread;
}

/* Each driver initialization begins a scheduling episode: the engine and the
 * native replay shim both reset their preemption accounting, so a harness may
 * run several episodes in one path (with fresh logical thread identifiers)
 * and each receives its full bound. After scheduling begins, the harness must
 * keep exactly one runnable coordinator unfinished between episodes. */
static inline void klee_concurrency_driver_init(
    struct klee_concurrency_driver *driver, const unsigned char *choices,
    uint64_t choice_count, uint64_t live_mask, uint64_t max_switches) {
  if (driver == 0 || (choices == 0 && choice_count != 0))
    klee_concurrency_driver_error(
        "concurrency driver error: invalid initialization");
  klee_concurrency_reset_scheduler();
  driver->choices = choices;
  driver->choice_count = choice_count;
  driver->next_choice = 0;
  driver->live_mask = live_mask;
  driver->blocked_mask = 0;
  driver->max_switches = max_switches;
  driver->transition_valid_mask = 0;
  driver->last_scheduled_thread = 0;
  driver->schedule_started = 0;
  driver->canonicalization_enabled = 0;
}

static inline uint64_t klee_concurrency_driver_live_mask(
    const struct klee_concurrency_driver *driver) {
  return driver->live_mask;
}

static inline uint64_t klee_concurrency_driver_runnable_mask(
    const struct klee_concurrency_driver *driver) {
  return driver->live_mask & ~driver->blocked_mask;
}

/* Blocking reasons are forwarded to the engine. A harness-declared reason
 * (klee_concurrency_driver_block, klee_concurrency_driver_set_blocked_mask)
 * is accepted but a resulting deadlock is reported as harness-declared. A
 * mutex reason (klee_concurrency_driver_block_on_mutex) is checked: the mutex
 * must be owned by another thread when blocking, must be released before
 * unblocking, and a deadlock built only from mutex reasons is reported as
 * verified. The engine refuses to schedule, select, or finish a blocked
 * thread. */
#define KLEE_CONCURRENCY_BLOCK_HARNESS 0u
#define KLEE_CONCURRENCY_BLOCK_MUTEX 1u

static inline void klee_concurrency_driver_set_blocked_mask(
    struct klee_concurrency_driver *driver, uint64_t blocked_mask) {
  if ((blocked_mask & ~driver->live_mask) != 0)
    klee_concurrency_driver_error(
        "concurrency driver error: blocked mask contains a non-live thread");
  const uint64_t changed = driver->blocked_mask ^ blocked_mask;
  for (uint64_t thread = 0; thread < 64; ++thread) {
    const uint64_t bit = UINT64_C(1) << thread;
    if ((changed & bit) == 0)
      continue;
    if ((blocked_mask & bit) != 0)
      klee_concurrency_block(thread, KLEE_CONCURRENCY_BLOCK_HARNESS, 0);
    else
      klee_concurrency_unblock(thread);
  }
  driver->blocked_mask = blocked_mask;
  driver->transition_valid_mask &= ~(blocked_mask | changed);
}

static inline void klee_concurrency_driver_block_with_reason(
    struct klee_concurrency_driver *driver, uint64_t thread, uint32_t kind,
    const void *mutex) {
  const uint64_t bit = klee_concurrency_driver_thread_bit(thread);
  if ((driver->live_mask & bit) == 0)
    klee_concurrency_driver_error(
        "concurrency driver error: cannot block a non-live thread");
  if ((driver->blocked_mask & bit) != 0)
    klee_concurrency_driver_error(
        "concurrency driver error: thread is already blocked");
  klee_concurrency_block(thread, kind, mutex);
  driver->blocked_mask |= bit;
  driver->transition_valid_mask &= ~bit;
}

static inline void klee_concurrency_driver_block(
    struct klee_concurrency_driver *driver, uint64_t thread) {
  klee_concurrency_driver_block_with_reason(
      driver, thread, KLEE_CONCURRENCY_BLOCK_HARNESS, 0);
}

static inline void klee_concurrency_driver_block_on_mutex(
    struct klee_concurrency_driver *driver, uint64_t thread,
    const void *mutex) {
  klee_concurrency_driver_block_with_reason(
      driver, thread, KLEE_CONCURRENCY_BLOCK_MUTEX, mutex);
}

static inline void klee_concurrency_driver_unblock(
    struct klee_concurrency_driver *driver, uint64_t thread) {
  const uint64_t bit = klee_concurrency_driver_thread_bit(thread);
  if ((driver->live_mask & bit) == 0 ||
      (driver->blocked_mask & bit) == 0)
    klee_concurrency_driver_error(
        "concurrency driver error: cannot unblock a runnable thread");
  klee_concurrency_unblock(thread);
  driver->blocked_mask &= ~bit;
  driver->transition_valid_mask &= ~bit;
}

static inline void klee_concurrency_driver_finish(
    struct klee_concurrency_driver *driver, uint64_t thread) {
  const uint64_t bit = klee_concurrency_driver_thread_bit(thread);
  if ((driver->live_mask & bit) == 0)
    klee_concurrency_driver_error(
        "concurrency driver error: cannot finish a non-live thread");
  if ((driver->blocked_mask & bit) != 0)
    klee_concurrency_driver_error(
        "concurrency driver error: cannot finish a blocked thread");
  klee_concurrency_set_thread(thread);
  klee_concurrency_finish_thread();
  driver->live_mask &= ~bit;
  driver->transition_valid_mask &= ~bit;
}

static inline void klee_concurrency_driver_enable_canonicalization(
    struct klee_concurrency_driver *driver) {
  if (driver->schedule_started)
    klee_concurrency_driver_error(
        "concurrency driver error: canonicalization enabled after scheduling began");
  driver->canonicalization_enabled = 1;
}

static inline void klee_concurrency_driver_set_transition(
    struct klee_concurrency_driver *driver, uint64_t thread,
    enum klee_concurrency_transition_kind kind, uintptr_t address,
    uint64_t size) {
  if (klee_is_symbolic((uintptr_t)thread) ||
      klee_is_symbolic((uintptr_t)kind) || klee_is_symbolic(address) ||
      klee_is_symbolic((uintptr_t)size))
    klee_concurrency_driver_error(
        "concurrency driver error: transition descriptor must be concrete");
  const uint64_t bit = klee_concurrency_driver_thread_bit(thread);
  if ((driver->live_mask & bit) == 0)
    klee_concurrency_driver_error(
        "concurrency driver error: transition belongs to a non-live thread");
  if ((driver->blocked_mask & bit) != 0)
    klee_concurrency_driver_error(
        "concurrency driver error: blocked thread has a transition descriptor");
  if (kind < KLEE_CONCURRENCY_TRANSITION_OPAQUE ||
      kind > KLEE_CONCURRENCY_TRANSITION_MUTEX)
    klee_concurrency_driver_error(
        "concurrency driver error: invalid transition kind");
  if ((kind == KLEE_CONCURRENCY_TRANSITION_READ ||
       kind == KLEE_CONCURRENCY_TRANSITION_WRITE) &&
      (size == 0 || (uint64_t)address > UINT64_MAX - size))
    klee_concurrency_driver_error(
        "concurrency driver error: invalid transition memory range");
  if ((kind == KLEE_CONCURRENCY_TRANSITION_LOCAL ||
       kind == KLEE_CONCURRENCY_TRANSITION_OPAQUE ||
       kind == KLEE_CONCURRENCY_TRANSITION_MUTEX) &&
      size != 0)
    klee_concurrency_driver_error(
        "concurrency driver error: non-memory transition has a size");
  driver->transitions[thread].kind = kind;
  driver->transitions[thread].address = address;
  driver->transitions[thread].size = size;
  klee_concurrency_declare(thread, (uint32_t)kind, (const void *)address,
                           size);
  driver->transition_valid_mask |= bit;
}

static inline uint64_t klee_concurrency_driver_first_thread(uint64_t mask) {
  for (uint64_t thread = 0; thread < 64; ++thread) {
    if ((mask & (UINT64_C(1) << thread)) != 0)
      return thread;
  }
  klee_concurrency_driver_error(
      "concurrency driver error: cannot select from an empty mask");
}

static inline uint64_t klee_concurrency_driver_canonical_mask(
    const struct klee_concurrency_driver *driver, uint64_t runnable) {
  if ((driver->transition_valid_mask & runnable) != runnable)
    klee_concurrency_driver_error(
        "concurrency driver error: runnable thread has no transition descriptor");

  uint64_t local = 0;
  for (uint64_t thread = 0; thread < 64; ++thread) {
    const uint64_t bit = UINT64_C(1) << thread;
    if ((runnable & bit) != 0 &&
        driver->transitions[thread].kind ==
            KLEE_CONCURRENCY_TRANSITION_LOCAL)
      local |= bit;
  }
  if (local == 0)
    return runnable;
  /* LOCAL is the only pruning primitive. It commutes with every other
   * transition and may not change another thread's enabledness. Non-local
   * transitions all remain eligible because next-step independence alone is
   * not a persistent-set condition. */
  if (driver->schedule_started &&
      (local & (UINT64_C(1) << driver->last_scheduled_thread)) != 0)
    return UINT64_C(1) << driver->last_scheduled_thread;
  return UINT64_C(1) << klee_concurrency_driver_first_thread(local);
}

static inline int klee_concurrency_driver_next(
    struct klee_concurrency_driver *driver, uint64_t *thread) {
  if (driver->live_mask == 0)
    return KLEE_CONCURRENCY_DRIVER_COMPLETE;
  uint64_t runnable = driver->live_mask & ~driver->blocked_mask;
  if (runnable == 0)
    klee_concurrency_deadlock(driver->blocked_mask);
  if (driver->canonicalization_enabled)
    runnable = klee_concurrency_driver_canonical_mask(driver, runnable);
  if (driver->next_choice >= driver->choice_count)
    klee_concurrency_driver_error(
        "concurrency driver error: schedule choices exhausted");
  const uint64_t selected = klee_concurrency_schedule(
      runnable, driver->choices[driver->next_choice++], driver->max_switches);
  if (selected == UINT64_MAX)
    return KLEE_CONCURRENCY_DRIVER_BOUND;
  driver->transition_valid_mask &=
      ~klee_concurrency_driver_thread_bit(selected);
  driver->last_scheduled_thread = selected;
  driver->schedule_started = 1;
  if (thread != 0)
    *thread = selected;
  return KLEE_CONCURRENCY_DRIVER_SCHEDULED;
}

#ifdef __cplusplus
}
#endif

#endif // KLEE_CONCURRENCY_HARNESS_H
