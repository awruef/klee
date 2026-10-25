// RUN: %clang %s -emit-llvm %O0opt -g -DTEST_CONCRETE -c -o %t.concrete.bc
// RUN: rm -rf %t.concrete.klee-out
// RUN: %klee --output-dir=%t.concrete.klee-out --exit-on-error --libc=klee --external-calls=none --write-no-tests %t.concrete.bc 2>&1 | FileCheck --check-prefix=CONCRETE %s
// RUN: %clang %s -emit-llvm %O0opt -g -DTEST_SYMBOLIC -c -o %t.symbolic.bc
// RUN: rm -rf %t.symbolic.klee-out
// RUN: %klee --output-dir=%t.symbolic.klee-out --exit-on-error --libc=klee --external-calls=none --write-no-tests %t.symbolic.bc 2>&1 | FileCheck --check-prefix=SYMBOLIC %s

// Validate the P4 klee-libc implementation.  Concrete cases check a small,
// representative part of the musl strtod contract.  The symbolic case checks
// KLEE's documented behavior: floating-point conversion concretizes the
// symbolic digit, so this is one representative execution, not exhaustive
// exploration of both allowed digits.

#include "klee/klee.h"

#include <assert.h>
#include <errno.h>
#include <stdlib.h>

#if defined(TEST_CONCRETE)

int main(void) {
  char *end = 0;

  const char decimal[] = " \t-12.5e+1tail";
  errno = 0;
  double d = strtod(decimal, &end);
  assert(d == -125.0);
  assert(end == decimal + 10);
  assert(errno == 0);

  const char hex[] = "0x1.8p+1!";
  errno = 0;
  d = strtod(hex, &end);
  assert(d == 3.0);
  assert(end == hex + 8);
  assert(errno == 0);

  const char invalid[] = "not-a-number";
  errno = 0;
  d = strtod(invalid, &end);
  assert(d == 0.0);
  assert(end == invalid);
  assert(errno == EINVAL);

  return 0;
}

// CONCRETE: KLEE: done: completed paths = 1
// CONCRETE: KLEE: done: partially completed paths = 0

#elif defined(TEST_SYMBOLIC)

int main(void) {
  char text[] = "1";
  klee_make_symbolic(&text[0], 1, "digit");
  klee_assume((text[0] == '1') | (text[0] == '2'));

  char *end = 0;
  double d = strtod(text, &end);
  assert(end == text + 1);
  assert((d == 1.0) | (d == 2.0));
  return 0;
}

// SYMBOLIC: silently concretizing (reason: floating point)
// SYMBOLIC: KLEE: done: completed paths = 1
// SYMBOLIC: KLEE: done: partially completed paths = 0

#else
#error Select TEST_CONCRETE or TEST_SYMBOLIC
#endif
