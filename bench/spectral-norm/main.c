/* Spectral norm (the Benchmarks Game's): ten rounds of the power method on the infinite matrix
   A(i, j) = 1 / ((i + j)(i + j + 1) / 2 + i + 1), cut to n x n. Prints the norm times 1e9,
   truncated, so that every side prints the same digits. */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

static double a(int i, int j) {
  int ij = i + j;
  return 1.0 / (ij * (ij + 1) / 2 + i + 1);
}

static void mul_av(int n, const double *u, double *out) {
  for (int i = 0; i < n; i++) {
    double s = 0;
    for (int j = 0; j < n; j++) s += a(i, j) * u[j];
    out[i] = s;
  }
}

static void mul_atv(int n, const double *u, double *out) {
  for (int i = 0; i < n; i++) {
    double s = 0;
    for (int j = 0; j < n; j++) s += a(j, i) * u[j];
    out[i] = s;
  }
}

static void mul_atav(int n, const double *u, double *out, double *tmp) {
  mul_av(n, u, tmp);
  mul_atv(n, tmp, out);
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 100;
  double *u = malloc(n * sizeof *u), *v = malloc(n * sizeof *v), *t = malloc(n * sizeof *t);
  for (int i = 0; i < n; i++) u[i] = 1, v[i] = 0, t[i] = 0;
  for (int k = 0; k < 10; k++) {
    mul_atav(n, u, v, t);
    mul_atav(n, v, u, t);
  }
  double vbv = 0, vv = 0;
  for (int i = 0; i < n; i++) vbv += u[i] * v[i], vv += v[i] * v[i];
  printf("%lld\n", (long long)(sqrt(vbv / vv) * 1e9));
  free(u); free(v); free(t);
  return 0;
}
