/* The in-order walk as a recursive function adding each key's value to an accumulator. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int32_t value(int32_t k, int32_t r) { return (int32_t)((uint32_t)k * 7919u + (uint32_t)r) % 1000; }

static void walk(int32_t lo, int32_t hi, int32_t r, int64_t *s) {
  if (lo < hi) {
    int32_t m = lo + (hi - lo) / 2;
    walk(lo, m, r, s);
    *s += value(m, r);
    walk(m + 1, hi, r, s);
  }
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 1000;
  int reps = argc > 2 ? atoi(argv[2]) : 1;
  int64_t acc = 0;
  for (int r = 0; r < reps; r++) { int64_t s = 0; walk(0, n, r, &s); acc += s; }
  printf("%lld\n", (long long)acc);
  return 0;
}
