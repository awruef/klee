//===-- intrinsics.c ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

/* Straight C for linking simplicity */

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <time.h>

#include "klee/klee.h"

#include "klee/ADT/KTest.h"

static KTest *testData = 0;
static unsigned testPosition = 0;

static unsigned char rand_byte(void) {
  unsigned x = rand();
  x ^= x >> 16;
  x ^= x >> 8;
  return x & 0xFF;
}

static void report_internal_error(const char *msg, ...)
    __attribute__((format(printf, 1, 2)));
static void report_internal_error(const char *msg, ...) {
  fprintf(stderr, "KLEE_RUN_TEST_ERROR: ");
  va_list ap;
  va_start(ap, msg);
  vfprintf(stderr, msg, ap);
  va_end(ap);
  fprintf(stderr, "\n");
  char *testErrorsNonFatal = getenv("KLEE_RUN_TEST_ERRORS_NON_FATAL");
  if (testErrorsNonFatal) {
    fprintf(stderr, "KLEE_RUN_TEST_ERROR: Forcing execution to continue\n");
  } else {
    exit(1);
  }
}

void klee_make_symbolic(void *array, size_t nbytes, const char *name) {

  if (!name)
    name = "unnamed";

  static int rand_init = -1;

  if (rand_init == -1) {
    if (getenv("KLEE_RANDOM")) {
      struct timeval tv;
      gettimeofday(&tv, 0);
      rand_init = 1;
      srand(tv.tv_sec ^ tv.tv_usec);
    } else {
      rand_init = 0;
    }
  }

  if (rand_init) {
    if (!strcmp(name, "syscall_a0")) {
      unsigned long long *v = array;
      assert(nbytes == 8);
      *v = rand() % 69;
    } else {
      char *c = array;
      size_t i;
      for (i = 0; i < nbytes; i++)
        c[i] = rand_byte();
    }
    return;
  }

  if (!testData) {
    char tmp[256];
    char *name = getenv("KTEST_FILE");

    if (!name) {
      fprintf(stdout, "KLEE-RUNTIME: KTEST_FILE not set, please enter .ktest path: ");
      fflush(stdout);
      name = tmp;
      if (!fgets(tmp, sizeof tmp, stdin) || !strlen(tmp)) {
        fprintf(stderr, "KLEE-RUNTIME: cannot replay, no KTEST_FILE or user input\n");
        exit(1);
      }
      tmp[strlen(tmp) - 1] = '\0'; /* kill newline */
    }
    testData = kTest_fromFile(name);
    if (!testData) {
      fprintf(stderr, "KLEE-RUNTIME: unable to open .ktest file\n");
      exit(1);
    }
  }

  for (;; ++testPosition) {
    if (testPosition >= testData->numObjects) {
      report_internal_error("out of inputs. Will use zero if continuing.");
      memset(array, 0, nbytes);
      break;
    } else {
      KTestObject *o = &testData->objects[testPosition];
      /* Engine-generated schedule decisions (native pthread model) are
       * interleaved with the harness objects; native replay runs real
       * threads and does not consume them. */
      if (strncmp(o->name, "klee_sched_", 11) == 0 &&
          strcmp(name, o->name) != 0)
        continue;
      if (strcmp(name, o->name) != 0) {
        report_internal_error(
            "object name mismatch. Requesting \"%s\" but returning \"%s\"",
            name, o->name);
      }
      memcpy(array, o->bytes, nbytes < o->numBytes ? nbytes : o->numBytes);
      if (nbytes != o->numBytes) {
        report_internal_error("object sizes differ. Expected %zu but got %u",
                              nbytes, o->numBytes);
        if (o->numBytes < nbytes)
          memset((char *)array + o->numBytes, 0, nbytes - o->numBytes);
      }
      ++testPosition;
      break;
    }
  }
}

void klee_silent_exit(int x) { exit(x); }

uintptr_t klee_choose(uintptr_t n) {
  uintptr_t x;
  klee_make_symbolic(&x, sizeof x, "klee_choose");
  if (x >= n)
    report_internal_error("klee_choose failure. max = %ld, got = %ld\n", n, x);
  return x;
}

unsigned klee_is_replay() { return 1; }

void klee_assume(uintptr_t x) {
  if (!x) {
    report_internal_error("invalid klee_assume");
  }
}

#define KLEE_GET_VALUE_STUB(suffix, type)                                      \
  type klee_get_value##suffix(type x) { return x; }

KLEE_GET_VALUE_STUB(f, float)
KLEE_GET_VALUE_STUB(d, double)
KLEE_GET_VALUE_STUB(l, long)
KLEE_GET_VALUE_STUB(ll, long long)
KLEE_GET_VALUE_STUB(_i32, int32_t)
KLEE_GET_VALUE_STUB(_i64, int64_t)

#undef KLEE_GET_VALUE_STUB

int klee_range(int begin, int end, const char *name) {
  int x;
  klee_make_symbolic(&x, sizeof x, name);
  if (x < begin || x >= end) {
    report_internal_error("invalid klee_range(%u,%u,%s) value, got: %u\n",
                          begin, end, name, x);
  }
  return x;
}

void klee_prefer_cex(void *object, uintptr_t condition) {}

void klee_abort() { abort(); }

void klee_report_error(const char *file, int line, const char *message,
                       const char *suffix) {
  fprintf(stderr, "KLEE_REPORT_ERROR: %s:%d: %s (%s)\n", file, line,
          message, suffix);
  abort();
}

void klee_print_expr(const char *msg, ...) {}

void klee_set_forking(unsigned enable) {}

unsigned klee_is_symbolic(uintptr_t n) {
  (void)n;
  return 0;
}

void klee_open_merge() {}
void klee_close_merge() {}

void klee_concurrency_create_thread(uint64_t thread_id) { (void)thread_id; }
/* Native replay links the real pthread library; the recorded schedule is not
 * enforced (see the prototype report, replay isolation). */
void klee_concurrency_yield(void) {}
void klee_concurrency_deadlock(uint64_t blocked_mask) {
  fprintf(stderr, "KLEE_CONCURRENCY_DEADLOCK: blocked mask 0x%llx\n",
          (unsigned long long)blocked_mask);
  abort();
}
void klee_concurrency_set_thread(uint64_t thread_id) { (void)thread_id; }
void klee_concurrency_block(uint64_t thread_id, uint32_t kind,
                            const void *mutex) {
  (void)thread_id;
  (void)kind;
  (void)mutex;
}
void klee_concurrency_unblock(uint64_t thread_id) { (void)thread_id; }
void klee_concurrency_finish_thread(void) {}
void klee_concurrency_join_thread(uint64_t thread_id) { (void)thread_id; }
/* Mirrors the engine's preemption accounting: declared LOCAL transitions are
 * transparent to the bound, so the shim must remember each thread's kind. */
static uint32_t klee_concurrency_declared_kind[64];
static int klee_concurrency_declarations_enabled;

void klee_concurrency_declare(uint64_t thread_id, uint32_t kind,
                              const void *address, size_t size) {
  (void)address;
  (void)size;
  if (thread_id < 64) {
    klee_concurrency_declared_kind[thread_id] = kind;
    klee_concurrency_declarations_enabled = 1;
  }
}

static int klee_concurrency_shim_is_local(uint64_t thread) {
  return klee_concurrency_declarations_enabled && thread < 64 &&
         klee_concurrency_declared_kind[thread] == 1;
}
void klee_concurrency_mutex_lock(const void *mutex) { (void)mutex; }
void klee_concurrency_mutex_unlock(const void *mutex) { (void)mutex; }
void klee_concurrency_cond_wait(const void *condition, const void *mutex) {
  (void)condition;
  (void)mutex;
}
void klee_concurrency_cond_signal(const void *condition) { (void)condition; }
void klee_concurrency_cond_broadcast(const void *condition) {
  (void)condition;
}
void klee_concurrency_read(const void *address, size_t size, uint64_t site_id) {
  (void)address;
  (void)size;
  (void)site_id;
}
void klee_concurrency_write(const void *address, size_t size,
                            uint64_t site_id) {
  (void)address;
  (void)size;
  (void)site_id;
}
/* Scheduler replay state. A harness may run several scheduling episodes in
 * one process (one driver initialization each); klee_concurrency_reset_scheduler
 * clears this state exactly where the engine clears its own. */
static uint64_t anchor_thread;
static int anchor_valid;
static uint64_t context_switches;

void klee_concurrency_reset_scheduler(void) {
  anchor_thread = 0;
  anchor_valid = 0;
  context_switches = 0;
  memset(klee_concurrency_declared_kind, 0,
         sizeof(klee_concurrency_declared_kind));
  klee_concurrency_declarations_enabled = 0;
}

uint64_t klee_concurrency_schedule(uint64_t runnable_mask, uint64_t choice,
                                   uint64_t max_switches) {
  uint64_t eligible = runnable_mask;
  const int preemptible =
      anchor_valid && anchor_thread < 64 &&
      (runnable_mask & (UINT64_C(1) << anchor_thread)) != 0;
  if (preemptible && context_switches >= max_switches) {
    uint64_t kept = UINT64_C(1) << anchor_thread;
    for (uint64_t thread = 0; thread < 64; ++thread) {
      if ((runnable_mask & (UINT64_C(1) << thread)) != 0 &&
          klee_concurrency_shim_is_local(thread))
        kept |= UINT64_C(1) << thread;
    }
    eligible &= kept;
  }
  if (eligible == 0)
    return UINT64_MAX;

  uint64_t count = 0;
  for (uint64_t bits = eligible; bits != 0; bits &= bits - 1)
    ++count;
  uint64_t ordinal = choice % count;
  uint64_t selected = 0;
  for (; selected < 64; ++selected) {
    if ((eligible & (UINT64_C(1) << selected)) == 0)
      continue;
    if (ordinal-- == 0)
      break;
  }
  if (!klee_concurrency_shim_is_local(selected)) {
    if (preemptible && selected != anchor_thread)
      ++context_switches;
    anchor_valid = 1;
    anchor_thread = selected;
  }
  /* The engine consumes a declaration when its transition completes; the
   * next decision therefore sees the selected thread as undeclared unless
   * the harness declares again. Clearing at selection is equivalent for
   * eligibility purposes. */
  if (selected < 64)
    klee_concurrency_declared_kind[selected] = 0;
  return selected;
}
