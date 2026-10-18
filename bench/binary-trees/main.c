/* Binary trees (the Benchmarks Game's): complete binary trees built bottom-up and counted,
   many short-lived ones at each depth from 4 to n in steps of 2, beside one long-lived tree.
   A node is one malloc. */
#include <stdio.h>
#include <stdlib.h>

struct node { struct node *left, *right; };

static struct node *make(int d) {
  struct node *t = malloc(sizeof *t);
  if (d == 0) { t->left = t->right = NULL; }
  else { t->left = make(d - 1); t->right = make(d - 1); }
  return t;
}

static int check(const struct node *t) {
  return 1 + (t->left ? check(t->left) : 0) + (t->right ? check(t->right) : 0);
}

static void destroy(struct node *t) {
  if (t->left) destroy(t->left);
  if (t->right) destroy(t->right);
  free(t);
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 10;
  int min_depth = 4;
  int max_depth = min_depth + 2 > n ? min_depth + 2 : n;
  struct node *s = make(max_depth + 1);
  printf("stretch tree of depth %d\t check: %d\n", max_depth + 1, check(s));
  destroy(s);
  struct node *long_lived = make(max_depth);
  for (int d = min_depth; d <= max_depth; d += 2) {
    int iterations = 1 << (max_depth - d + min_depth);
    int c = 0;
    for (int i = 0; i < iterations; i++) {
      struct node *t = make(d);
      c += check(t);
      destroy(t);
    }
    printf("%d\t trees of depth %d\t check: %d\n", iterations, d, c);
  }
  printf("long lived tree of depth %d\t check: %d\n", max_depth, check(long_lived));
  destroy(long_lived);
  return 0;
}
