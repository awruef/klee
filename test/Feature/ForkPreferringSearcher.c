// RUN: %clang %s -emit-llvm -g -O0 -Xclang -disable-O0-optnone -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --output-dir=%t.klee-out --search=pref:dfs %t.bc 2>%t.log
// RUN: FileCheck --check-prefix=PREF --input-file=%t.log %s

#include "klee/klee.h"

extern void klee_mark_interesting(void);

int main(void) {
  unsigned char first, second;
  volatile unsigned sink = 0;
  klee_make_symbolic(&first, sizeof(first), "first");
  klee_make_symbolic(&second, sizeof(second), "second");
  klee_assume(first <= 1);
  klee_assume(second <= 1);

  if (first) {
    klee_mark_interesting();
    if (second)
      sink = 1;
    else
      sink = 2;
  } else {
    sink = 3;
  }

  // PREF: completed paths = 3
  // PREF: partially completed paths = 0
  return sink == 0;
}
