#include <stdio.h>
#include <stdlib.h>

/* The product of two n by n matrices, row-major. */
static void matmul(const double *a, const double *b, double *c, int n) {
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) {
      double s = 0.0;
      for (int k = 0; k < n; k++) s += a[i * n + k] * b[k * n + j];
      c[i * n + j] = s;
    }
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 10;
  double *a = malloc(sizeof(double) * n * n), *b = malloc(sizeof(double) * n * n);
  double *c = malloc(sizeof(double) * n * n);
  for (int k = 0; k < n * n; k++) { a[k] = k % 7; b[k] = k % 5 - 2; }
  matmul(a, b, c, n);
  double s = 0.0;
  for (int k = 0; k < n * n; k++) s += c[k];
  printf("%lld\n", (long long)s);
  free(a); free(b); free(c);
  return 0;
}
