#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* The number of primes below n: the sieve of Eratosthenes over a flag per number. */
static int sieve(int n) {
  unsigned char *a = malloc(n);
  memset(a, 1, n);
  for (int i = 2; i * i < n; i++)
    if (a[i])
      for (int j = i * i; j < n; j += i) a[j] = 0;
  int count = 0;
  for (int i = 0; i < n; i++) count += a[i];
  free(a);
  return count - 2;
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 1000;
  int reps = argc > 2 ? atoi(argv[2]) : 1;
  int c = 0;
  for (int r = 0; r < reps; r++) c = sieve(n);
  printf("%d\n", c);
  return 0;
}
