/* B2.2, UNCHECKED: the cached form of `p1-r3-owned-reborrow.bc`'s resume (`adv`).

   Nothing here is typed or checked by the kernel. `cache_edit.py` puts this in place of the
   proven form's `adv` in the emitted LLVM IR; everything else (the build, the first segment
   `spawn0`, the scheduler) is the compiled proven program.

   The optimisation is loop-invariant code motion of the re-derived views: instead of lending the
   tree's cell and walking the path from the root at every resume, the state keeps a stack of node
   pointers across resumes (Rust's `Vec<&Node>`), in the path array's memory.

   Representation (read off the emitted IR of the new backend): a `Tree` cell (`ref Tree`) is four
   words, `tag | left cell | key | right cell`, tag 0 a leaf, 1 a node; the path (`array i32`, 64
   slots) is a pointer and a length, its slots packed 4 bytes each (256 bytes: room for 32
   pointers; a tree of 2^20 keys has depth 21). The state `St` arrives as
   `c, path, len, d, key, r, s`, and the answer `i64 + St` leaves as `tag, …`.

   Mode: the proven form's `d` is the current node's depth (>= 0). At the first resume the stack is
   rebuilt once from the path (the ancestors entered to the left, then the current node); from
   then on `d` holds `-1 - sp`. */
#include <stdint.h>

extern void bc_free(int64_t a);

/* With `-DCHECK_STALE`, each popped position is checked: a live node's cell holds tag 1, and a
   freed cell holds the allocator's free-list link in that word, so a pop of a freed cell counts in
   `cached_stale` (printed at exit). */
#ifdef CHECK_STALE
#include <stdio.h>
#include <stdlib.h>
int64_t cached_stale;
static void stale_report(void) { fprintf(stderr, "stale pops %lld\n", (long long)cached_stale); }
__attribute__((constructor)) static void stale_init(void) { atexit(stale_report); }
#endif

typedef struct cell { int64_t tag; struct cell *l; int64_t key; struct cell *r; } cell;

static int64_t value(int64_t k, int64_t r) {
  int32_t x = (int32_t)((uint32_t)(int32_t)k * 7919u + (uint32_t)(int32_t)r);
  return (int64_t)(x % 1000);
}

/* The tree's destructor, as the proven form's (each node's cells, then the cell). */
static void drop(cell *q) {
  if (q->tag == 1) { drop(q->l); drop(q->r); }
  bc_free((int64_t)(intptr_t)q);
}

void cached_adv(int64_t *out, int64_t c, int64_t path, int64_t len, int64_t d, int64_t key,
                int64_t r, int64_t s) {
  cell **stk = (cell **)(intptr_t)path;
  int64_t sp;
  if (d >= 0) {
    int32_t dirs[64];
    const int32_t *p32 = (const int32_t *)(intptr_t)path;
    for (int64_t i = 0; i < d; i++) dirs[i] = p32[i];
    cell *q = (cell *)(intptr_t)c;
    sp = 0;
    for (int64_t i = 0; i < d; i++) {
      if (dirs[i] <= 0) { stk[sp++] = q; q = q->l; } else { q = q->r; }
    }
    stk[sp++] = q;
  } else {
    sp = -1 - d;
  }
  cell *p = stk[--sp];
#ifdef CHECK_STALE
  if (p->tag != 1) cached_stale++;
#endif
  s += value(p->key, r);
  for (cell *q = p->r; q->tag == 1; q = q->l) stk[sp++] = q;
  if (sp == 0) {
    drop((cell *)(intptr_t)c);
    if (len > 0) bc_free(path);
    out[0] = 0; out[1] = s;
    for (int i = 2; i < 8; i++) out[i] = 0;
    return;
  }
  out[0] = 1; out[1] = c; out[2] = path; out[3] = len;
  out[4] = -1 - sp; out[5] = stk[sp - 1]->key; out[6] = r; out[7] = s;
}

/* For `inv-c-owner-moved.bc`, whose `change` the backend inlines into `adv`: the same move
   written here (`free` the cell, then `alloc` a cell with its four words, as the compiled
   `change` does) at the node of key `at`, then the cached step. */
extern int64_t bc_alloc(int64_t n);

void cached_adv_moving(int64_t *out, int64_t c, int64_t path, int64_t len, int64_t d, int64_t key,
                       int64_t r, int64_t s, int64_t at) {
  if (key == at) {
    int64_t w[4];
    for (int i = 0; i < 4; i++) w[i] = ((int64_t *)(intptr_t)c)[i];
    bc_free(c);
    c = bc_alloc(4);
    for (int i = 0; i < 4; i++) ((int64_t *)(intptr_t)c)[i] = w[i];
  }
  cached_adv(out, c, path, len, d, key, r, s);
}

/* For `inv-c2-owner-moved-fresh.bc`: its `change` (the contents swapped out, a new cell allocated
   with them, then the old cell freed) at the node of key `at`, then the cached step. */
void cached_adv_moving_fresh(int64_t *out, int64_t c, int64_t path, int64_t len, int64_t d,
                             int64_t key, int64_t r, int64_t s, int64_t at) {
  if (key == at) {
    int64_t c2 = bc_alloc(4);
    for (int i = 0; i < 4; i++) ((int64_t *)(intptr_t)c2)[i] = ((int64_t *)(intptr_t)c)[i];
    bc_free(c);
    c = c2;
  }
  cached_adv(out, c, path, len, d, key, r, s);
}
