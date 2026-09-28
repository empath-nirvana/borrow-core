/-!
# Backend — the Wasm runtime

The allocator and output, written in WAT. They are the trusted part of the target, specified
in `Backend/README.md`:

- `$alloc n` (`n ≥ 1` words) returns an 8-aligned address `a ≥ 16384` such that
  `[a, a + 8n)` is disjoint from every live range and from the runtime's own memory
  (`[0, 16384)` and each range's size word at `a - 8`), and adds one to the live count.
- `$free a`, for `a` returned by `$alloc` and not freed since, ends that range's life and
  subtracts one from the live count.
- `$live` is the live count, and is exported as `live_objects`.
- `$putc b` writes the low byte of `b` to standard output, and `$putfd fd b` to the stream
  `fd` (WASI `fd_write`; `write(2)` in libc).
- `$getc fd` reads one byte of the stream `fd`, or answers `-1` at its end or on an error
  (WASI `fd_read`; `read(2)` in libc).

Layout: bytes `0–31` hold `$putfd`'s I/O vector and byte, bytes `32–63` `$getc`'s; `1024 + 4s` holds the head of the
free list of ranges of `s` words, for `s < 1024`; ranges start at `16384`, each preceded by a
word holding its size. `$alloc` pops the free list of its size, or else bumps `$heap`, growing
memory as needed. A freed range of `s < 1024` words is pushed onto its free list (its first
word links the list); a larger one is not reused.
-/

namespace Backend.Wasm

def runtimeWat : String := "
  (import \"wasi_snapshot_preview1\" \"fd_write\"
    (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"fd_read\"
    (func $fd_read (param i32 i32 i32 i32) (result i32)))
  (memory (export \"memory\") 1)
  (global $heap (mut i32) (i32.const 16376))
  (global $live (mut i64) (i64.const 0))

  (func $alloc (param $n i64) (result i64)
    (local $s i32) (local $head i32) (local $p i32) (local $top i32) (local $have i32)
    (local.set $s (i32.wrap_i64 (local.get $n)))
    (global.set $live (i64.add (global.get $live) (i64.const 1)))
    (if (i32.lt_u (local.get $s) (i32.const 1024))
      (then
        (local.set $head (i32.add (i32.const 1024) (i32.shl (local.get $s) (i32.const 2))))
        (local.set $p (i32.load (local.get $head)))
        (if (local.get $p)
          (then
            (i32.store (local.get $head) (i32.load (local.get $p)))
            (return (i64.extend_i32_u (local.get $p)))))))
    (local.set $p (i32.add (global.get $heap) (i32.const 8)))
    (local.set $top (i32.add (local.get $p) (i32.shl (local.get $s) (i32.const 3))))
    (local.set $have (i32.shl (memory.size) (i32.const 16)))
    (if (i32.gt_u (local.get $top) (local.get $have))
      (then
        (if (i32.eq
              (memory.grow (i32.add (i32.shr_u (i32.sub (local.get $top) (local.get $have))
                                               (i32.const 16))
                                    (i32.const 1)))
              (i32.const -1))
          (then unreachable))))
    (i64.store (i32.sub (local.get $p) (i32.const 8)) (local.get $n))
    (global.set $heap (local.get $top))
    (i64.extend_i32_u (local.get $p)))

  (func $free (param $a i64)
    (local $p i32) (local $s i32) (local $head i32)
    (local.set $p (i32.wrap_i64 (local.get $a)))
    (local.set $s (i32.wrap_i64 (i64.load (i32.sub (local.get $p) (i32.const 8)))))
    (global.set $live (i64.sub (global.get $live) (i64.const 1)))
    (if (i32.lt_u (local.get $s) (i32.const 1024))
      (then
        (local.set $head (i32.add (i32.const 1024) (i32.shl (local.get $s) (i32.const 2))))
        (i32.store (local.get $p) (i32.load (local.get $head)))
        (i32.store (local.get $head) (local.get $p)))))

  (func $live (export \"live_objects\") (result i64)
    (global.get $live))

  (func $putc (param $b i64)
    (call $putfd (i64.const 1) (local.get $b)))

  (func $putfd (param $fd i64) (param $b i64)
    (i32.store8 (i32.const 16) (i32.wrap_i64 (local.get $b)))
    (i32.store (i32.const 0) (i32.const 16))
    (i32.store (i32.const 4) (i32.const 1))
    (drop (call $fd_write (i32.wrap_i64 (local.get $fd))
      (i32.const 0) (i32.const 1) (i32.const 24))))

  (func $getc (param $fd i64) (result i64)
    (i32.store (i32.const 32) (i32.const 48))
    (i32.store (i32.const 36) (i32.const 1))
    (i32.store (i32.const 40) (i32.const 0))
    (if (i32.or
          (call $fd_read (i32.wrap_i64 (local.get $fd)) (i32.const 32) (i32.const 1) (i32.const 40))
          (i32.eqz (i32.load (i32.const 40))))
      (then (return (i64.const -1))))
    (i64.load8_u (i32.const 48)))
"

end Backend.Wasm
