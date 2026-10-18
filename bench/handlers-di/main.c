/* Dependency injection in C: the logger and the clock as structs of function pointers and
   state, the logger chosen at run time by the third argument. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef struct Logger { void (*log)(struct Logger *, int64_t); int64_t state; } Logger;
typedef struct Clock { int64_t (*now_ns)(struct Clock *); int64_t t; } Clock;

static void summing(Logger *l, int64_t x) { l->state += x; }
static void hashing(Logger *l, int64_t x) { l->state = (int64_t)((uint64_t)l->state * 31u + (uint64_t)x); }
static int64_t fake_now(Clock *c) { c->t += 3; return c->t; }

static int64_t value(int32_t k) { return (int64_t)((int32_t)((uint32_t)k * 7919u) % 1000); }

static int64_t work(int32_t n, Logger *log, Clock *clock) {
  int64_t acc = 0;
  for (int32_t i = 0; i < n; i++) {
    int64_t t = clock->now_ns(clock);
    int64_t v = value(i);
    if ((i & 7) == 0) log->log(log, t + v);
    acc += v;
  }
  return acc;
}

int main(int argc, char **argv) {
  int n = argc > 1 ? atoi(argv[1]) : 1000;
  int reps = argc > 2 ? atoi(argv[2]) : 1;
  int mode = argc > 3 ? atoi(argv[3]) : 0;
  Logger log = { mode == 0 ? summing : hashing, 0 };
  Clock clock = { fake_now, 0 };
  int64_t acc = 0;
  for (int r = 0; r < reps; r++) acc += work(n, &log, &clock);
  printf("%lld %lld %lld\n", (long long)acc, (long long)log.state, (long long)clock.t);
  return 0;
}
