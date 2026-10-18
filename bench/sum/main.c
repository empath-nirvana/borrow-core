#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 1000;
  int reps = argc > 2 ? atoi(argv[2]) : 1;
  int64_t *a = malloc(sizeof(int64_t) * (n > 0 ? n : 1));
  for (int i = 0; i < n; i++) a[i] = (int64_t)(((int32_t)((uint32_t)i * 7919u)) % 1000);
  int64_t acc = 0;
  for (int r = 0; r < reps; r++) {
    int64_t s = 0;
    for (int i = 0; i < n; i++) s += a[i];
    acc += s;
  }
  printf("%lld\n", (long long)acc);
  free(a);
  return 0;
}
