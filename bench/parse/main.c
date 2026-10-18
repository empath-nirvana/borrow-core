#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

/* The numbers of standard input, one per line: their count and their sum. */
int main(void) {
  size_t cap = 1 << 16, n = 0, r;
  char *buf = malloc(cap + 1);
  while ((r = fread(buf + n, 1, cap - n, stdin)) > 0) {
    n += r;
    if (n == cap) { cap *= 2; buf = realloc(buf, cap + 1); }
  }
  buf[n] = 0;
  long count = 0;
  int64_t acc = 0;
  char *p = buf, *end;
  for (;;) {
    long long x = strtoll(p, &end, 10);
    if (end == p) break;
    count++;
    acc += x;
    p = end;
  }
  printf("%ld %lld\n", count, (long long)acc);
  free(buf);
  return 0;
}
