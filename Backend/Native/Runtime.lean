/-!
# Backend — the native runtime  `[spec §40]`

The allocator and the POSIX platform of the native target, written in C and compiled with the
program's LLVM IR (`Backend/Native/Lower.lean`). They are the trusted part of the target, with
the specification of the Wasm runtime's (`Backend/Wasm/Runtime.lean`, `Backend/README.md`, The
allocator), so that `live` and the counts agree:

- `bc_alloc n` (`n ≥ 1` words) returns an 8-aligned address `a` such that `[a, a + 8n)` is
  disjoint from every live range, and adds one to `bc_live` and `bc_allocs`. As the Wasm
  runtime does, a range of `s < 1024` words is preceded by a word holding `s` and is taken from
  the free list of its size, or else bumped from an arena of 1 MiB chunks; a larger one is a
  `malloc` of its own.
- `bc_free a`, for `a` returned by `bc_alloc` and not freed since, ends the range's life and
  subtracts one from `bc_live`; a range of `s < 1024` words goes on the free list of its size,
  a larger one back to `free`. The address `0` and an address in the program's data (a
  literal's view; `bc_init` gives its bounds) are not freed.
- `bc_putc fd b` writes the low byte of `b` to `fd`, and `bc_putv fd p n` the `n` bytes at `p`,
  calling `write(2)` again after a short write; both are unbuffered, as the Wasm runtime's are,
  and a write's error is dropped (`SIGPIPE` is ignored).
- `bc_getc fd` reads one byte with `read(2)`, or answers `-1` at the end or on an error;
  `bc_getv fd p n` reads into the `n` bytes at `p` until they are full or a read answers
  nothing, and answers the count.
- The stream `0xFFFFFFFF` is the program's arguments, each followed by `0`, its own name left
  out (SPEC §34). Its first read copies them into memory that is no range and is never freed,
  counted as one allocation in `bc_allocs`, as the Wasm runtime's `$args` counts it.
- `bc_now c` answers the nanoseconds of `CLOCK_MONOTONIC` since the clock's first use,
  saturating at `2^63 − 1`, and `bc_sleep c ns` waits at least `ns` nanoseconds when `ns > 0`
  (`nanosleep`, again after an interruption); the cell `c` is the model's and is not read.
- `bc_status code` is the exit status the run ends with once the entry returns (SPEC §39).

`main` runs the program's entry on a thread whose stack is 512 MiB (reserved, not committed),
well past the Wasm target's 64 MiB, so that the recursions the Wasm target runs (`bounded`'s
budget, SPEC §20, `fold_imm`) run natively too. The environment variable `BC_STACK` sets
another size in bytes: the tests run loops of tail calls in 64 KiB (`bcc tailcalls`).
-/

namespace Backend.Native

def runtimeC : String := r##"/* borrow-core native runtime (Backend/Native/Runtime.lean) */
#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define BC_CLASSES 1024
#define BC_CHUNK (1 << 20)
#define BC_STACK ((size_t)512 << 20)

int64_t bc_live, bc_allocs, bc_indirect, bc_copies;

static uintptr_t data_lo, data_hi;
static int32_t status;
static uint64_t *freelist[BC_CLASSES];
static char *arena_p, *arena_end;

void bc_init(void *data, int64_t len) {
  data_lo = (uintptr_t)data;
  data_hi = data_lo + (uint64_t)len;
}

int64_t bc_alloc(int64_t n) {
  uint64_t s = (uint64_t)n;
  uint64_t *h;
  if (s == 0) s = 1;
  bc_live++;
  bc_allocs++;
  if (s < BC_CLASSES) {
    uint64_t *p = freelist[s];
    if (p) {
      freelist[s] = (uint64_t *)(uintptr_t)p[0];
      return (int64_t)(uintptr_t)p;
    }
    size_t bytes = 8 * (s + 1);
    if ((size_t)(arena_end - arena_p) < bytes) {
      arena_p = malloc(BC_CHUNK);
      if (!arena_p) abort();
      arena_end = arena_p + BC_CHUNK;
    }
    h = (uint64_t *)arena_p;
    arena_p += bytes;
  } else {
    h = malloc(8 * (s + 1));
    if (!h) abort();
  }
  h[0] = s;
  return (int64_t)(uintptr_t)(h + 1);
}

void bc_free(int64_t a) {
  uintptr_t p = (uintptr_t)a;
  if (p == 0 || (p >= data_lo && p < data_hi)) return;
  uint64_t *q = (uint64_t *)p;
  uint64_t s = q[-1];
  bc_live--;
  if (s < BC_CLASSES) {
    q[0] = (uint64_t)(uintptr_t)freelist[s];
    freelist[s] = q;
  } else {
    free(q - 1);
  }
}

void bc_putc(int64_t fd, int64_t b) {
  unsigned char c = (unsigned char)b;
  while (write((int)fd, &c, 1) < 0 && errno == EINTR) {}
}

void bc_putv(int64_t fd, int64_t p, int64_t n) {
  const unsigned char *a = (const unsigned char *)(uintptr_t)p;
  uint64_t k = (uint64_t)n;
  while (k > 0) {
    ssize_t w = write((int)fd, a, k);
    if (w < 0 && errno == EINTR) continue;
    if (w <= 0) return;
    a += w;
    k -= (uint64_t)w;
  }
}

static int argc_;
static char **argv_;
static unsigned char *argbuf;
static size_t argp, arge;
static int argsRead;

static void args(void) {
  if (argsRead) return;
  argsRead = 1;
  bc_allocs++;
  size_t size = 0;
  for (int i = 1; i < argc_; i++) size += strlen(argv_[i]) + 1;
  argbuf = malloc(size + 1);
  if (!argbuf) abort();
  size_t k = 0;
  for (int i = 1; i < argc_; i++) {
    size_t l = strlen(argv_[i]) + 1;
    memcpy(argbuf + k, argv_[i], l);
    k += l;
  }
  argp = 0;
  arge = size;
}

#define ARGS_FD 0xFFFFFFFFu

int64_t bc_getc(int64_t fd) {
  if ((uint64_t)fd == ARGS_FD) {
    args();
    if (argp >= arge) return -1;
    return argbuf[argp++];
  }
  unsigned char b;
  ssize_t r;
  while ((r = read((int)fd, &b, 1)) < 0 && errno == EINTR) {}
  return r == 1 ? (int64_t)b : -1;
}

int64_t bc_getv(int64_t fd, int64_t p, int64_t n) {
  unsigned char *a = (unsigned char *)(uintptr_t)p;
  uint64_t k = (uint64_t)n;
  if ((uint64_t)fd == ARGS_FD) {
    args();
    uint64_t r = arge - argp;
    if (k < r) r = k;
    memcpy(a, argbuf + argp, r);
    argp += r;
    return (int64_t)r;
  }
  uint64_t got = 0;
  while (k > 0) {
    ssize_t r = read((int)fd, a, k);
    if (r < 0 && errno == EINTR) continue;
    if (r <= 0) break;
    a += r;
    k -= (uint64_t)r;
    got += (uint64_t)r;
  }
  return (int64_t)got;
}

static int64_t t0 = -1;

static int64_t mono(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t)ts.tv_sec * 1000000000 + ts.tv_nsec;
}

int64_t bc_now(int64_t c) {
  (void)c;
  if (t0 == -1) t0 = mono();
  uint64_t ns = (uint64_t)(mono() - t0);
  return ns > (uint64_t)INT64_MAX ? INT64_MAX : (int64_t)ns;
}

void bc_sleep(int64_t c, int64_t ns) {
  (void)c;
  if (t0 == -1) t0 = mono();
  if (ns <= 0) return;
  struct timespec r = { (time_t)(ns / 1000000000), (long)(ns % 1000000000) };
  while (nanosleep(&r, &r) == -1 && errno == EINTR) {}
}

void bc_status(int64_t code) { status = (int32_t)(uint32_t)code; }

extern void bc_entry(void);

static void *run(void *x) {
  (void)x;
  bc_entry();
  return 0;
}

int main(int argc, char **argv) {
  argc_ = argc;
  argv_ = argv;
  signal(SIGPIPE, SIG_IGN);
  pthread_attr_t at;
  pthread_t t;
  size_t stack = BC_STACK;
  const char *env = getenv("BC_STACK");
  if (env) stack = (size_t)strtoull(env, 0, 10);
  pthread_attr_init(&at);
  if (pthread_attr_setstacksize(&at, stack) != 0 || pthread_create(&t, &at, run, 0) != 0) {
    run(0);
  } else {
    pthread_join(t, 0);
  }
  return status;
}
"##

end Backend.Native
