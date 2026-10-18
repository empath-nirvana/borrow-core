#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int main(int argc, char **argv) {
  int64_t n = argc > 1 ? atoi(argv[1]) : 1000;
  int64_t s = 0;
  for (int64_t x = 0; x < n; x++) {
    int64_t y = x * 3 + 1;
    if (y % 7 != 0) s += y;
  }
  printf("%lld\n", (long long)s);
  return 0;
}
