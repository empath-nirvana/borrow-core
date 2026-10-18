/* Mandelbrot (the Benchmarks Game's): the points of an n×n grid over [-1.5, 0.5] × [-1, 1]
   that stay within |z| <= 2 for 50 iterations of z <- z^2 + c. Prints how many do. */
#include <stdio.h>
#include <stdlib.h>

static int inside(double cr, double ci) {
  double zr = 0, zi = 0, tr = 0, ti = 0;
  for (int i = 0; i < 50; i++) {
    if (tr + ti > 4.0) return 0;
    zi = 2.0 * zr * zi + ci;
    zr = tr - ti + cr;
    tr = zr * zr;
    ti = zi * zi;
  }
  return tr + ti <= 4.0;
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 200;
  double fn = n;
  int count = 0;
  for (int y = 0; y < n; y++) {
    double ci = 2.0 * y / fn - 1.0;
    for (int x = 0; x < n; x++) {
      double cr = 2.0 * x / fn - 1.5;
      count += inside(cr, ci);
    }
  }
  printf("%d\n", count);
  return 0;
}
