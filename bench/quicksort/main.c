#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

/* Element i of the input: bits 16..30 of an LCG step, centred on 0. */
static int32_t data(int32_t i) {
  uint32_t x = ((uint32_t)i * 1103515245u + 12345u) & 2147483647u;
  return (int32_t)(x >> 16) - 16384;
}

static void swap(int32_t *v, int i, int j) { int32_t t = v[i]; v[i] = v[j]; v[j] = t; }

/* Lomuto's partition of [lo, hi] around its middle element, moved to hi first. */
static int partition(int32_t *v, int lo, int hi) {
  swap(v, lo + (hi - lo) / 2, hi);
  int32_t p = v[hi];
  int i = lo;
  for (int j = lo; j < hi; j++)
    if (v[j] < p) swap(v, i++, j);
  swap(v, i, hi);
  return i;
}

static void quicksort(int32_t *v, int lo, int hi) {
  if (lo < hi) {
    int p = partition(v, lo, hi);
    quicksort(v, lo, p - 1);
    quicksort(v, p + 1, hi);
  }
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 2000;
  int reps = argc > 2 ? atoi(argv[2]) : 1;
  int bad = 0;
  int32_t check = 0;
  int32_t *a = malloc(sizeof(int32_t) * n);
  for (int r = 0; r < reps; r++) {
    for (int i = 0; i < n; i++) a[i] = data(i);
    quicksort(a, 0, n - 1);
    for (int i = 1; i < n; i++) bad += a[i] < a[i - 1];
    check = (int32_t)((uint32_t)check + (uint32_t)a[n / 2]);
  }
  printf("%d %d\n", bad, check);
  free(a);
  return 0;
}
