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
- `$allocs` counts the calls of `$alloc`, `$indirect` the dispatched calls (closure calls
  whose code a switch chooses at run time), and `$copies` the copies of a variable at a
  non-trivial type (a generated copy, which allocates); the compiled code counts the last two
  when it is compiled for counting.
- `$putc b` writes the low byte of `b` to standard output, and `$putfd fd b` to the stream
  `fd` (WASI `fd_write`; `write(2)` in libc).
- `$getc fd` reads one byte of the stream `fd`, or answers `-1` at its end or on an error
  (WASI `fd_read`; `read(2)` in libc).
- `$putv fd p n` writes the `n` bytes at `p` to the stream `fd`, calling `fd_write` again after a
  short write (`write_all`).
- `$getv fd p n` reads bytes of the stream `fd` into the `n` bytes at `p` until they are full or
  the stream ends or fails, and answers how many it read (`read_into`).

Layout: bytes `0–31` hold `$putfd`'s and `$putv`'s I/O vector and byte, bytes `32–63` `$getc`'s
and `$getv`'s; `1024 + 4s` holds the head of the
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
  (global $allocs (mut i64) (i64.const 0))
  (global $indirect (mut i64) (i64.const 0))
  (global $copies (mut i64) (i64.const 0))

  (func $alloc (param $n i64) (result i64)
    (local $s i32) (local $head i32) (local $p i32) (local $top i32) (local $have i32)
    (local.set $s (i32.wrap_i64 (local.get $n)))
    (global.set $live (i64.add (global.get $live) (i64.const 1)))
    (global.set $allocs (i64.add (global.get $allocs) (i64.const 1)))
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

  (func $putv (param $fd i64) (param $p i64) (param $n i64)
    (local $a i32) (local $k i32) (local $w i32)
    (local.set $a (i32.wrap_i64 (local.get $p)))
    (local.set $k (i32.wrap_i64 (local.get $n)))
    (block $done
      (loop $again
        (br_if $done (i32.eqz (local.get $k)))
        (i32.store (i32.const 0) (local.get $a))
        (i32.store (i32.const 4) (local.get $k))
        (br_if $done (call $fd_write (i32.wrap_i64 (local.get $fd))
          (i32.const 0) (i32.const 1) (i32.const 24)))
        (local.set $w (i32.load (i32.const 24)))
        (br_if $done (i32.eqz (local.get $w)))
        (local.set $a (i32.add (local.get $a) (local.get $w)))
        (local.set $k (i32.sub (local.get $k) (local.get $w)))
        (br $again))))

  (func $getv (param $fd i64) (param $p i64) (param $n i64) (result i64)
    (local $a i32) (local $k i32) (local $r i32) (local $got i32)
    (local.set $a (i32.wrap_i64 (local.get $p)))
    (local.set $k (i32.wrap_i64 (local.get $n)))
    (block $done
      (loop $again
        (br_if $done (i32.eqz (local.get $k)))
        (i32.store (i32.const 32) (local.get $a))
        (i32.store (i32.const 36) (local.get $k))
        (i32.store (i32.const 40) (i32.const 0))
        (br_if $done (call $fd_read (i32.wrap_i64 (local.get $fd))
          (i32.const 32) (i32.const 1) (i32.const 40)))
        (local.set $r (i32.load (i32.const 40)))
        (br_if $done (i32.eqz (local.get $r)))
        (local.set $a (i32.add (local.get $a) (local.get $r)))
        (local.set $k (i32.sub (local.get $k) (local.get $r)))
        (local.set $got (i32.add (local.get $got) (local.get $r)))
        (br $again)))
    (i64.extend_i32_u (local.get $got)))
"

end Backend.Wasm
