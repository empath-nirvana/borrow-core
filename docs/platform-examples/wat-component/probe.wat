;; Probe: a hand-written core module in the shape our backend emits (WAT, one memory, no
;; function table), importing WASI 0.2 functions by their canonical-ABI core signatures and
;; exporting `wasi:cli/run`. `wasm-tools component embed` + `component new` wrap it as a
;; component. It writes a line, sleeps 100 ms on a monotonic-clock pollable, writes another.
(module
  (import "wasi:cli/stdout@0.2.12" "get-stdout" (func $get_stdout (result i32)))
  (import "wasi:io/streams@0.2.12" "[method]output-stream.blocking-write-and-flush"
    (func $write_flush (param i32 i32 i32 i32)))
  (import "wasi:io/streams@0.2.12" "[resource-drop]output-stream" (func $drop_out (param i32)))
  (import "wasi:clocks/monotonic-clock@0.2.12" "subscribe-duration"
    (func $subscribe_duration (param i64) (result i32)))
  (import "wasi:io/poll@0.2.12" "[method]pollable.block" (func $block (param i32)))
  (import "wasi:io/poll@0.2.12" "[resource-drop]pollable" (func $drop_pollable (param i32)))
  (memory (export "memory") 1)
  (data (i32.const 16) "before sleep\n")
  (data (i32.const 32) "after 100 ms\n")
  ;; The result area of a call returning `result<_, stream-error>` is at 64.
  (func (export "wasi:cli/run@0.2.12#run") (result i32)
    (local $out i32) (local $p i32)
    (local.set $out (call $get_stdout))
    (call $write_flush (local.get $out) (i32.const 16) (i32.const 13) (i32.const 64))
    (local.set $p (call $subscribe_duration (i64.const 100000000)))
    (call $block (local.get $p))
    (call $drop_pollable (local.get $p))
    (call $write_flush (local.get $out) (i32.const 32) (i32.const 13) (i32.const 64))
    (call $drop_out (local.get $out))
    (i32.const 0)))
