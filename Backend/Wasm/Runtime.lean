/-!
# Backend — the Wasm runtime

The allocator and output, written in WAT. They are the trusted part of the target, specified
in `Backend/README.md`:

- `$alloc n` (`n ≥ 1` words) returns an 8-aligned address `a ≥ 16384` such that
  `[a, a + 8n)` is disjoint from every live range and from the runtime's own memory
  (`[0, 16384)` and each range's size word at `a - 8`), and adds one to the live count.
- `$free a`, for `a` returned by `$alloc` and not freed since, ends that range's life and
  subtracts one from the live count. An address below the heap, in the program's read-only data
  (a literal's view), is not freed.
- `$live` is the live count, and is exported as `live_objects`.
- `$allocs` counts the calls of `$alloc` and the arguments' reservation (below), `$indirect`
  the dispatched calls (closure calls whose code a switch chooses at run time), and `$copies`
  the copies of a variable at a non-trivial type (a generated copy, which allocates); the
  compiled code counts the last two when it is compiled for counting.
- `$putc b` writes the low byte of `b` to standard output, and `$putfd fd b` to the stream
  `fd` (WASI `fd_write`; `write(2)` in libc).
- `$getc fd` reads one byte of the stream `fd`, or answers `-1` at its end or on an error
  (WASI `fd_read`; `read(2)` in libc).
- `$putv fd p n` writes the `n` bytes at `p` to the stream `fd`, calling `fd_write` again after a
  short write (`write_all`).
- `$getv fd p n` reads bytes of the stream `fd` into the `n` bytes at `p` until they are full or
  the stream ends or fails, and answers how many it read (`read_into`).
- The stream `0xFFFFFFFF` is the program's arguments, each followed by `0`, the program's own name
  left out (SPEC §34): `$args` reads them once, with `args_sizes_get` and `args_get`, into memory
  `$reserve` takes from the heap (it is no range, and is never freed, but counts as one
  allocation in `$allocs`), and `$getc` and `$getv` read from there.
- `$exit code` ends the run with the exit status `code` (WASI `proc_exit`; `exit(3)` in libc):
  the entry's last act when a division's error reached `main` (SPEC §39).
- `$sp` is the stack pointer of the frames of scoped cells (SPEC §35): a function with a frame
  lowers it by the frame's size on entry, trapping when it would pass `$stackLimit`, and raises it
  back before it returns or tail-calls (`Backend/Wasm/Lower.lean`, `lowerFn`). A slot is no range
  and is never given to `$free`.
- `$now c` answers the nanoseconds of the monotonic clock since the clock's first use, saturating
  at `2^63 − 1`, and `$sleep c ns` waits at least `ns` nanoseconds when `ns > 0` (`poll_oneoff`
  on one relative clock subscription); `c` is the clock's cell, whose content is the model's and
  is not read (SPEC §34, `clock_now`, `clock_sleep`).

- `$file op x p n` is a file operation (SPEC §34), the native runtime's `bc_file` over WASI:
  `0` opens the path of `n` bytes at `p` (`path_open`), resolved against the preopened
  directories as wasi-libc resolves it: the walk of descriptors `3, 4, …` while `fd_prestat_get`
  answers a directory, choosing the one whose name is the longest prefix of the path ending at a
  `/` or at its end (a name `.` is the empty prefix of every relative path), and opening the rest
  of the path under it; no preopen covers it: `-1`, not found. `1` is one `fd_read`, `2`
  `fd_write`s until the view is written, `3` `fd_filestat_get`'s size, `4` `fd_close`. The
  answers and the kinds are `bc_file`'s, from WASI's error numbers. An empty path names no
  file (`-1`), as natively. A read of a directory, which WASI answers with `EBADF`, is `-3` (a
  directory) as natively: on that error, one `fd_filestat_get` tells it.

Layout: bytes `0–31` hold `$putfd`'s and `$putv`'s I/O vector and byte, bytes `32–63` `$getc`'s
and `$getv`'s, bytes `64–71` the clock's reading, `72–79` `$args`'s sizes, `128–175` `$sleep`'s
subscription, `192–231` its event and count, `256–263` a preopen's description, `264–267` an opened
descriptor, `272–283` a file read's or write's I/O vector and count, `320–383` a file's
`filestat`, `508` the path `.`, `512–1023` a preopen's name; `1024 + 4s` holds the head of the
free list of ranges of `s` words, for `s < 1024`; the program's data (its literals' bytes, then a
word for each capability's cell) starts at `16384`; a module with frames has its stack after the
data (`Backend/Wasm/Print.lean`, `stackBytes`), growing down from its top; ranges start after
that, each preceded by a word holding its size. `$alloc` pops the free list of its size, or else bumps `$heap`, growing
memory as needed. A freed range of `s < 1024` words is pushed onto its free list (its first
word links the list); a larger one is not reused.
-/

namespace Backend.Wasm

def runtimeWat : String := "
  (import \"wasi_snapshot_preview1\" \"fd_write\"
    (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"fd_read\"
    (func $fd_read (param i32 i32 i32 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"clock_time_get\"
    (func $clock_time_get (param i32 i64 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"poll_oneoff\"
    (func $poll_oneoff (param i32 i32 i32 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"args_sizes_get\"
    (func $args_sizes_get (param i32 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"args_get\"
    (func $args_get (param i32 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"proc_exit\"
    (func $proc_exit (param i32)))
  (import \"wasi_snapshot_preview1\" \"path_open\"
    (func $path_open (param i32 i32 i32 i32 i32 i64 i64 i32 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"fd_prestat_get\"
    (func $fd_prestat_get (param i32 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"fd_prestat_dir_name\"
    (func $fd_prestat_dir_name (param i32 i32 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"fd_filestat_get\"
    (func $fd_filestat_get (param i32 i32) (result i32)))
  (import \"wasi_snapshot_preview1\" \"fd_close\"
    (func $fd_close (param i32) (result i32)))
  (memory (export \"memory\") 1)
  (global $heap (mut i32) (i32.const 16376))
  (global $sp (mut i64) (i64.const 0))
  (global $stackLimit i64 (i64.const 0))
  (global $live (mut i64) (i64.const 0))
  (global $allocs (mut i64) (i64.const 0))
  (global $indirect (mut i64) (i64.const 0))
  (global $copies (mut i64) (i64.const 0))
  (global $t0 (mut i64) (i64.const -1))
  (global $argp (mut i32) (i32.const 0))
  (global $arge (mut i32) (i32.const 0))
  (global $argsRead (mut i32) (i32.const 0))

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
    (if (i32.lt_u (local.get $p) (i32.const STATIC_END)) (then return))
    (local.set $s (i32.wrap_i64 (i64.load (i32.sub (local.get $p) (i32.const 8)))))
    (global.set $live (i64.sub (global.get $live) (i64.const 1)))
    (if (i32.lt_u (local.get $s) (i32.const 1024))
      (then
        (local.set $head (i32.add (i32.const 1024) (i32.shl (local.get $s) (i32.const 2))))
        (i32.store (local.get $p) (i32.load (local.get $head)))
        (i32.store (local.get $head) (local.get $p)))))

  (func $live (export \"live_objects\") (result i64)
    (global.get $live))

  (func $exit (param $code i64)
    (call $proc_exit (i32.wrap_i64 (local.get $code))))

  (func $putc (param $b i64)
    (call $putfd (i64.const 1) (local.get $b)))

  (func $putfd (param $fd i64) (param $b i64)
    (i32.store8 (i32.const 16) (i32.wrap_i64 (local.get $b)))
    (i32.store (i32.const 0) (i32.const 16))
    (i32.store (i32.const 4) (i32.const 1))
    (drop (call $fd_write (i32.wrap_i64 (local.get $fd))
      (i32.const 0) (i32.const 1) (i32.const 24))))

  (func $reserve (param $n i32) (result i32)
    (local $p i32) (local $top i32) (local $have i32)
    (local.set $p (i32.add (global.get $heap) (i32.const 8)))
    (local.set $top (i32.add (local.get $p)
      (i32.and (i32.add (local.get $n) (i32.const 7)) (i32.const -8))))
    (local.set $have (i32.shl (memory.size) (i32.const 16)))
    (if (i32.gt_u (local.get $top) (local.get $have))
      (then
        (if (i32.eq
              (memory.grow (i32.add (i32.shr_u (i32.sub (local.get $top) (local.get $have))
                                               (i32.const 16))
                                    (i32.const 1)))
              (i32.const -1))
          (then unreachable))))
    (global.set $heap (local.get $top))
    (local.get $p))

  (func $args
    (local $argc i32) (local $size i32) (local $argv i32) (local $buf i32)
    (if (global.get $argsRead) (then return))
    (global.set $argsRead (i32.const 1))
    (global.set $allocs (i64.add (global.get $allocs) (i64.const 1)))
    (if (call $args_sizes_get (i32.const 72) (i32.const 76)) (then return))
    (local.set $argc (i32.load (i32.const 72)))
    (local.set $size (i32.load (i32.const 76)))
    (local.set $argv (call $reserve (i32.shl (i32.add (local.get $argc) (i32.const 1)) (i32.const 2))))
    (local.set $buf (call $reserve (i32.add (local.get $size) (i32.const 1))))
    (if (call $args_get (local.get $argv) (local.get $buf)) (then return))
    (global.set $arge (i32.add (local.get $buf) (local.get $size)))
    (global.set $argp (global.get $arge))
    (if (i32.gt_u (local.get $argc) (i32.const 1))
      (then (global.set $argp (i32.load (i32.add (local.get $argv) (i32.const 4)))))))

  (func $getc (param $fd i64) (result i64)
    (local $b i64)
    (if (i64.eq (local.get $fd) (i64.const 4294967295))
      (then
        (call $args)
        (if (i32.ge_u (global.get $argp) (global.get $arge)) (then (return (i64.const -1))))
        (local.set $b (i64.load8_u (global.get $argp)))
        (global.set $argp (i32.add (global.get $argp) (i32.const 1)))
        (return (local.get $b))))
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
    (if (i64.eq (local.get $fd) (i64.const 4294967295))
      (then
        (call $args)
        (local.set $r (i32.sub (global.get $arge) (global.get $argp)))
        (if (i32.lt_u (local.get $k) (local.get $r)) (then (local.set $r (local.get $k))))
        (memory.copy (local.get $a) (global.get $argp) (local.get $r))
        (global.set $argp (i32.add (global.get $argp) (local.get $r)))
        (return (i64.extend_i32_u (local.get $r)))))
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

  (func $mono (result i64)
    (drop (call $clock_time_get (i32.const 1) (i64.const 1000) (i32.const 64)))
    (i64.load (i32.const 64)))

  (func $now (param $c i64) (result i64)
    (local $ns i64)
    (if (i64.eq (global.get $t0) (i64.const -1)) (then (global.set $t0 (call $mono))))
    (local.set $ns (i64.sub (call $mono) (global.get $t0)))
    (if (result i64) (i64.gt_u (local.get $ns) (i64.const 9223372036854775807))
      (then (i64.const 9223372036854775807)) (else (local.get $ns))))

  (func $fs_ans (param $r i32) (result i64)
    (i64.extend_i32_u (local.get $r)))

  (func $fs_err (param $e i32) (result i64)
    (if (i32.or (i32.eq (local.get $e) (i32.const 44)) (i32.eq (local.get $e) (i32.const 54)))
      (then (return (call $fs_ans (i32.const -1)))))
    (if (i32.or (i32.or (i32.eq (local.get $e) (i32.const 2)) (i32.eq (local.get $e) (i32.const 63)))
                (i32.or (i32.eq (local.get $e) (i32.const 69)) (i32.eq (local.get $e) (i32.const 76))))
      (then (return (call $fs_ans (i32.const -2)))))
    (if (i32.eq (local.get $e) (i32.const 31)) (then (return (call $fs_ans (i32.const -3)))))
    (if (i32.eq (local.get $e) (i32.const 8)) (then (return (call $fs_ans (i32.const -4)))))
    (if (i32.or (i32.or (i32.eq (local.get $e) (i32.const 37)) (i32.eq (local.get $e) (i32.const 61)))
                (i32.eq (local.get $e) (i32.const 22)))
      (then (return (call $fs_ans (i32.const -5)))))
    (call $fs_ans (i32.sub (i32.const -16) (local.get $e))))

  (func $fs_open (param $mode i32) (param $a i32) (param $k i32) (result i64)
    (local $d i32) (local $best i32) (local $blen i32) (local $nl i32) (local $abs i32)
    (local $i i32) (local $ok i32) (local $r i32) (local $rl i32) (local $e i32)
    (if (i32.eqz (local.get $k)) (then (return (call $fs_ans (i32.const -1)))))
    (local.set $best (i32.const -1))
    (local.set $blen (i32.const -1))
    (local.set $abs (i32.and (i32.gt_u (local.get $k) (i32.const 0))
      (i32.eq (i32.load8_u (local.get $a)) (i32.const 47))))
    (local.set $d (i32.const 3))
    (block $walked
      (loop $next
        (br_if $walked (call $fd_prestat_get (local.get $d) (i32.const 256)))
        (local.set $nl (i32.load (i32.const 260)))
        (if (i32.and (i32.eqz (i32.load8_u (i32.const 256)))
              (i32.le_u (local.get $nl) (i32.const 512)))
          (then
            (if (i32.eqz (call $fd_prestat_dir_name (local.get $d) (i32.const 512) (local.get $nl)))
              (then
                ;; a trailing NUL, then trailing `/`s (but a lone `/`), are not the name's
                (if (i32.and (i32.gt_u (local.get $nl) (i32.const 0))
                      (i32.eqz (i32.load8_u (i32.add (i32.const 511) (local.get $nl)))))
                  (then (local.set $nl (i32.sub (local.get $nl) (i32.const 1)))))
                (block $trimmed
                  (loop $trim
                    (br_if $trimmed (i32.le_u (local.get $nl) (i32.const 1)))
                    (br_if $trimmed (i32.ne (i32.load8_u (i32.add (i32.const 511) (local.get $nl)))
                      (i32.const 47)))
                    (local.set $nl (i32.sub (local.get $nl) (i32.const 1)))
                    (br $trim)))
                (local.set $ok (i32.const 0))
                (if (i32.and (i32.eq (local.get $nl) (i32.const 1))
                      (i32.eq (i32.load8_u (i32.const 512)) (i32.const 46)))
                  (then
                    (if (i32.eqz (local.get $abs))
                      (then (local.set $ok (i32.const 1)) (local.set $nl (i32.const 0)))))
                  (else
                    (if (i32.and
                          (i32.eq (local.get $abs)
                            (i32.and (i32.gt_u (local.get $nl) (i32.const 0))
                              (i32.eq (i32.load8_u (i32.const 512)) (i32.const 47))))
                          (i32.le_u (local.get $nl) (local.get $k)))
                      (then
                        (local.set $ok (i32.const 1))
                        (local.set $i (i32.const 0))
                        (block $cmp
                          (loop $byte
                            (br_if $cmp (i32.ge_u (local.get $i) (local.get $nl)))
                            (if (i32.ne (i32.load8_u (i32.add (i32.const 512) (local.get $i)))
                                        (i32.load8_u (i32.add (local.get $a) (local.get $i))))
                              (then (local.set $ok (i32.const 0)) (br $cmp)))
                            (local.set $i (i32.add (local.get $i) (i32.const 1)))
                            (br $byte)))
                        ;; the prefix ends at a `/` of the path, at its end, or is `/` itself
                        (if (i32.and (local.get $ok)
                              (i32.lt_u (local.get $nl) (local.get $k)))
                          (then
                            (if (i32.and
                                  (i32.ne (i32.load8_u (i32.add (local.get $a) (local.get $nl)))
                                    (i32.const 47))
                                  (i32.ne (i32.load8_u (i32.add (i32.const 511) (local.get $nl)))
                                    (i32.const 47)))
                              (then (local.set $ok (i32.const 0))))))))))
                (if (i32.and (local.get $ok) (i32.gt_s (local.get $nl) (local.get $blen)))
                  (then (local.set $best (local.get $d)) (local.set $blen (local.get $nl))))))))
        (local.set $d (i32.add (local.get $d) (i32.const 1)))
        (br $next)))
    (if (i32.lt_s (local.get $best) (i32.const 0)) (then (return (call $fs_ans (i32.const -1)))))
    (local.set $r (i32.add (local.get $a) (local.get $blen)))
    (local.set $rl (i32.sub (local.get $k) (local.get $blen)))
    (block $skipped
      (loop $skip
        (br_if $skipped (i32.eqz (local.get $rl)))
        (br_if $skipped (i32.ne (i32.load8_u (local.get $r)) (i32.const 47)))
        (local.set $r (i32.add (local.get $r) (i32.const 1)))
        (local.set $rl (i32.sub (local.get $rl) (i32.const 1)))
        (br $skip)))
    (if (i32.eqz (local.get $rl))
      (then
        (i32.store8 (i32.const 508) (i32.const 46))
        (local.set $r (i32.const 508))
        (local.set $rl (i32.const 1))))
    (local.set $e (call $path_open (local.get $best) (i32.const 1) (local.get $r) (local.get $rl)
      (select (i32.const 9) (i32.const 0) (local.get $mode))
      (select (i64.const 2097220) (i64.const 2097158) (local.get $mode))
      (select (i64.const 2097220) (i64.const 2097158) (local.get $mode))
      (i32.const 0) (i32.const 264)))
    (if (local.get $e) (then (return (call $fs_err (local.get $e)))))
    (call $fs_ans (i32.load (i32.const 264))))

  (func $file (param $op i64) (param $x i64) (param $p i64) (param $n i64) (result i64)
    (local $a i32) (local $k i32) (local $fd i32) (local $e i32) (local $w i32) (local $sz i64)
    (local.set $a (i32.wrap_i64 (local.get $p)))
    (local.set $k (i32.wrap_i64 (local.get $n)))
    (if (i64.eqz (local.get $op))
      (then (return (call $fs_open (i32.wrap_i64 (local.get $x)) (local.get $a) (local.get $k)))))
    (if (i64.gt_u (local.get $x) (i64.const 2147483647))
      (then (return (call $fs_ans (i32.const -4)))))
    (local.set $fd (i32.wrap_i64 (local.get $x)))
    (if (i64.eq (local.get $op) (i64.const 1))
      (then
        (i32.store (i32.const 272) (local.get $a))
        (i32.store (i32.const 276) (local.get $k))
        (local.set $e (call $fd_read (local.get $fd) (i32.const 272) (i32.const 1) (i32.const 280)))
        ;; WASI answers a read of a directory with `EBADF`: the kind is `IsDir`, as natively, which
        ;; one `fd_filestat_get` on that error path tells (its file type `3`, a directory)
        (if (i32.eq (local.get $e) (i32.const 8))
          (then
            (if (i32.eqz (call $fd_filestat_get (local.get $fd) (i32.const 320)))
              (then
                (if (i32.eq (i32.load8_u (i32.const 336)) (i32.const 3))
                  (then (return (call $fs_ans (i32.const -3)))))))))
        (if (local.get $e) (then (return (call $fs_err (local.get $e)))))
        (return (call $fs_ans (i32.load (i32.const 280))))))
    (if (i64.eq (local.get $op) (i64.const 2))
      (then
        (block $done
          (loop $again
            (br_if $done (i32.eqz (local.get $k)))
            (i32.store (i32.const 272) (local.get $a))
            (i32.store (i32.const 276) (local.get $k))
            (local.set $e (call $fd_write (local.get $fd) (i32.const 272) (i32.const 1) (i32.const 280)))
            (if (local.get $e) (then (return (call $fs_err (local.get $e)))))
            (local.set $w (i32.load (i32.const 280)))
            (if (i32.eqz (local.get $w)) (then (return (call $fs_err (i32.const 29)))))
            (local.set $a (i32.add (local.get $a) (local.get $w)))
            (local.set $k (i32.sub (local.get $k) (local.get $w)))
            (br $again)))
        (return (i64.const 0))))
    (if (i64.eq (local.get $op) (i64.const 3))
      (then
        (local.set $e (call $fd_filestat_get (local.get $fd) (i32.const 320)))
        (if (local.get $e) (then (return (call $fs_err (local.get $e)))))
        (local.set $sz (i64.load (i32.const 352)))
        (if (i64.gt_u (local.get $sz) (i64.const 2147483646))
          (then (return (call $fs_ans (i32.const -5)))))
        (return (local.get $sz))))
    (local.set $e (call $fd_close (local.get $fd)))
    (if (i32.and (i32.ne (local.get $e) (i32.const 0)) (i32.ne (local.get $e) (i32.const 27)))
      (then (return (call $fs_err (local.get $e)))))
    (i64.const 0))

  (func $sleep (param $c i64) (param $ns i64)
    (if (i64.eq (global.get $t0) (i64.const -1)) (then (global.set $t0 (call $mono))))
    (if (i64.le_s (local.get $ns) (i64.const 0)) (then return))
    (memory.fill (i32.const 128) (i32.const 0) (i32.const 104))
    (i64.store (i32.const 152) (local.get $ns))
    (i32.store (i32.const 144) (i32.const 1))
    (drop (call $poll_oneoff (i32.const 128) (i32.const 192) (i32.const 1) (i32.const 224))))
"

end Backend.Wasm
