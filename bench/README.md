# Benchmarks against Rust and C

Each directory here is one program written three times: in our language (`main.bc`), in Rust
(`main.rs`) and, where C is natural, in C (`main.c`). They have the same inputs and the same
output. `make bench` (`bench/bench.py`) builds every side, runs each one, and writes the table
below to `bench/out/results.md`. It is not part of the gate. The work is issue #537 (part of
#530 and #213). Fixes are listed at the end, ranked; none of them is made here.

## How it is measured

- **Ours**: `bcc compile --target native`, then `clang -O2 -w -pthread` with the native
  runtime (`Backend/Native/Runtime.lean`). This is what `bcc run --native` does (SPEC §40).
- **Rust**: idiomatic safe Rust, std only, no `unsafe`. Iterators are used where a Rust
  programmer would use them. It is built with the flags `cargo build --release` passes to rustc
  1.97.1: `--edition=2024 -C opt-level=3 -C embed-bitcode=no -C strip=debuginfo`. That is the
  default target, with no `target-cpu=native`.
- **C**: plain single-threaded C at `clang -O2`.
- **Toolchain and machine**: Apple clang 21.0.0 on an Apple M4 Pro (arm64, macOS).
- **Inputs**:
  - Sizes come from the program's arguments (`args`). Standard input comes from `gen.py` and is
    read at run time, so no side can fold the work away at compile time.
  - Every run of the Rust side takes about 100 ms or more.
  - All sides print the same bytes, and the harness fails if they do not. Our runtime's lines
    after the output (the value of `main`, `live 0`) are not compared.
- **Time**: the median of 11 runs after one warm-up. The spread is the fastest and slowest run.
- **Code**: the bytes of `__TEXT,__text`.
- **File**: the stripped executable.
- **Build**: wall time. Ours is split into `bcc` and `clang`.
- **Our programs** are written as a user writes them today: surface syntax and library
  functions (`at`, `array_set`, `peek`, `for`, `while`, generators, `|>`, `with`). Where today's
  language forces a shape, the program's comments say so (below, *What the language forced*).

## Results

Ratios above 1 are ours slower. *Library* marks a row that measures a library data structure
rather than the language. #213 asks for those to be reported separately.

| benchmark | ours ms (spread) | Rust ms (spread) | C ms (spread) | ours/Rust | ours/C | code ours / Rust / C | file ours / Rust / C | build s: ours (bcc + clang) / Rust / C |
|---|---|---|---|---|---|---|---|---|
| sum | 203 (202–204) | 108 (107–111) | 108 (107–109) | **1.88×** | 1.89× | 4.2K / 214K / 0.6K | 50K / 334K / 33K | 0.37 (0.17 + 0.20) / 0.12 / 0.05 |
| prefix | 135 (135–137) | 125 (124–126) | 123 (121–125) | 1.09× | 1.10× | 4.2K / 214K / 0.7K | 50K / 334K / 33K | 0.37 (0.18 + 0.20) / 0.12 / 0.05 |
| sieve | 507 (504–510) | 89.9 (88.8–91.1) | 89.6 (88.7–91.6) | **5.63×** | 5.65× | 5.9K / 214K / 0.5K | 50K / 334K / 33K | 0.42 (0.20 + 0.22) / 0.12 / 0.05 |
| sieve-for | 116 (115–118) | 89.7 (88.6–90.7) | 90.9 (89.1–92.2) | 1.30× | 1.28× | 4.6K / 214K / 0.5K | 50K / 334K / 33K | 0.89 (0.66 + 0.23) / 0.12 / 0.05 |
| matmul | 139 (138–140) | 133 (131–135) | 148 (147–149) | 1.05× | 0.94× | 4.0K / 215K / 0.7K | 50K / 350K / 33K | 0.78 (0.62 + 0.16) / 0.14 / 0.05 |
| quicksort | 133 (131–135) | 107 (106–108) | 106 (104–108) | 1.24× | 1.25× | 4.8K / 215K / 1.2K | 50K / 334K / 33K | 0.42 (0.20 + 0.22) / 0.13 / 0.05 |
| chain-for | 143 (142–144) | 145 (144–147) | 138 (137–139) | 0.99× | 1.04× | 3.4K / 214K / 0.4K | 50K / 334K / 33K | 0.27 (0.14 + 0.14) / 0.11 / 0.04 |
| chain-yield | 311 (306–314) | 148 (147–149) | 142 (141–146) | **2.10×** | 2.19× | 3.3K / 214K / 0.4K | 50K / 334K / 33K | 0.31 (0.16 + 0.15) / 0.12 / 0.04 |
| chain-gen | 3112 (3110–3116) | 145 (144–145) | 138 (138–139) | **21.5×** | 22.5× | 4.6K / 214K / 0.4K | 50K / 334K / 33K | 0.49 (0.24 + 0.25) / 0.11 / 0.05 |
| sort-generic | 201 (200–203) | 156 (153–157) | — | 1.29× | — | 4.8K / 215K / — | 50K / 334K / — | 0.43 (0.21 + 0.23) / 0.13 / — |
| parse | 155 (152–157) | 127 (126–128) | 139 (137–144) | 1.22× | 1.11× | 2.8K / 213K / 0.3K | 50K / 334K / 33K | 0.24 (0.13 + 0.11) / 0.10 / 0.04 |
| binary-trees | 398 (385–404) | 1004 (957–1028) | 863 (850–887) | 0.40× | 0.46× | 5.7K / 214K / 0.5K | 50K / 334K / 33K | 0.43 (0.22 + 0.21) / 0.10 / 0.04 |
| n-body | 352 (350–353) | 197 (196–198) | 302 (300–303) | **1.78×** | 1.16× | 5.0K / 215K / 1.1K | 50K / 350K / 49K | 1.05 (0.79 + 0.26) / 0.12 / 0.06 |
| mandelbrot | 494 (491–496) | 490 (488–495) | 434 (432–436) | 1.01× | 1.14× | 3.2K / 213K / 0.3K | 50K / 334K / 33K | 0.78 (0.63 + 0.15) / 0.09 / 0.04 |
| spectral-norm | 222 (220–224) | 225 (223–227) | 256 (256–259) | 0.99× | 0.86× | 3.9K / 213K / 0.8K | 50K / 334K / 33K | 0.84 (0.65 + 0.19) / 0.12 / 0.05 |
| wordcount (library) | 130 (128–132) | 105 (104–107) | — | 1.24× | — | 4.4K / 215K / — | 50K / 350K / — | 0.46 (0.22 + 0.25) / 0.14 / — |
| gen-tree | 178 (146–198) | 104 (103–105) | — | **1.72×** | — | 4.1K / 214K / — | 50K / 334K / — | 0.38 (0.19 + 0.20) / 0.12 / — |
| gen-tree-dyn | 167 (161–197) | 3999 (3972–4020) | — | 0.04× | — | 4.1K / 216K / — | 50K / 350K / — | 0.38 (0.19 + 0.20) / 0.14 / — |
| gen-tree-cb | 178 (161–188) | 90.8 (90.4–94.8) | 89.7 (87.7–93.0) | **1.96×** | 1.98× | 4.1K / 214K / 0.3K | 50K / 334K / 33K | 0.38 (0.19 + 0.20) / 0.11 / 0.04 |
| async-tree | 253 (246–257) | 301 (297–308) | — | 0.84× | — | 12K / 216K / — | 50K / 351K / — | 0.70 (0.27 + 0.43) / 0.15 / — |
| raise-small | 159 (159–160) | 123 (123–124) | — | 1.30× | — | 4.2K / 214K / — | 50K / 334K / — | 0.39 (0.18 + 0.21) / 0.11 / — |
| raise-large | 126 (126–127) | 123 (122–124) | — | 1.03× | — | 4.1K / 214K / — | 50K / 334K / — | 0.40 (0.19 + 0.21) / 0.12 / — |
| handlers-di | 111 (110–112) | 113 (112–113) | 182 (182–183) | 0.98× | 0.61× | 5.6K / 214K / 0.5K | 50K / 334K / 33K | 0.51 (0.24 + 0.27) / 0.12 / 0.04 |
| handlers-di-generic | 111 (110–112) | 205 (203–206) | — | 0.54× | — | 5.6K / 214K / — | 50K / 334K / — | 0.52 (0.24 + 0.27) / 0.12 / — |

**The breakdown #213 asks for.**

- **On par.** Counted loops, element access, floats, calls, handlers and errors run within about
  1.3× of Rust, often at parity:
  - prefix, matmul, chain-for, mandelbrot and spectral-norm are within 10%;
  - quicksort, sort-generic, parse, raise-small, and sieve once its loops are counted, are within
    1.3×.
- **Not on par.** Two causes, both in the backend and both shown below:
  - **Loops that may diverge** (`while`, `loop`, a generator's body) run as a state machine
    driven one turn at a time. That costs 2–22×: sieve, chain-yield, chain-gen.
  - **Specific missed optimisations** cost 1.7–2×: a sum loop that does not vectorise, bounds
    checks, a recursive call that is not a tail call. These are sum, n-body and gen-tree.
- **Nothing structural** stands between us and Rust:
  - The counts show no garbage collector, no boxing per element, no reference counting and no
    dispatched calls in any of these loops: `indirect 0` everywhere except async-tree's resumes.
  - Allocation follows the source: binary-trees allocates one box per node and wins.

### Table A: where Rust is famously good

| benchmark | what it tests | how ours is written |
|---|---|---|
| sum | a tight loop, bounds checks | `for p in v { s = s + *p }` over an `array_imm` view, repeated |
| prefix | a loop writing through a `mut` view | `for p in v { s = modify p { x -> (x + s, x + s) } }` |
| sieve | nested loops with strides | `while` loops (a stride has no counted form), owned array, `at`/`array_set` |
| sieve-for | the same with counted loops only | the stride counted by a division, `for k in 0..m` |
| matmul | three nested loops of float multiply–adds | owned arrays threaded through `dot` and `row`, `at(&a, …)` |
| quicksort | reads through `mut` views (#213 item 1) | recursive Lomuto, `peek` and `swap_at` on an `array_mut` |
| chain-for / chain-yield / chain-gen | map/filter/fold against Rust's iterator chain | a counted `for` with an `if`; one generator with `while`, body maps and filters; `range(…) \|> map(…) \|> filter(…)` with the library adapters |
| sort-generic | monomorphisation | sort-generic is quicksort generic in `T`, at pairs ordered by `poly (<) at Key` |
| parse | bytes and strings | `read_input()` and `fold_i64s` (`lib/text.bc`) |
| binary-trees | `match`, a box per node, allocation | `mu X. 1 + (X * X)`, the bounded recursion; counting a tree consumes and frees it |
| n-body, mandelbrot, spectral-norm | floats | bodies as 7 `f64`s each in one array (no records yet); `at`/`array_set` |
| wordcount | the hash map (library) | `Map[text 't, i32]` keyed by views of the input, `map_lookup` then `map_insert` |

The Rust side of each is the iterator or slice code a Rust programmer writes. sum is
`a.iter().sum()`, sieve is `step_by`, the chains are `(0..n).map(…).filter(…).sum()`,
wordcount is `HashMap<&str, i32>` with `entry`, and n-body is `[Body; 5]` with
`split_at_mut`. quicksort and sort-generic have the same algorithm on every side, recursive
Lomuto with the middle pivot. That is what they measure, so the Rust side is not
`sort_unstable`.

### Table B: where we might beat Rust

| benchmark | hypothesis and mechanism | result |
|---|---|---|
| gen-tree, gen-tree-dyn, gen-tree-cb | A recursive generator (in-order `yield` over a tree) is a state machine with no allocation. Rust needs a `Box<dyn Iterator>` per level, or a hand-written stack. | **Supported against `Box<dyn Iterator>`**: 23× faster. Ours makes 0 allocations and 0 dispatched calls; Rust boxes every node. **Not supported** against Rust's hand-written stack iterator (1.72×), Rust's closure callback (1.96×) or C's recursion (1.98×). The cause is below. The tree is implicit (each node is a key range), so only the traversal is measured. |
| async-tree | Recursive async tasks are sized state machines, where Rust needs `Box::pin` per recursive call. | **Supported, 0.84×, but by another mechanism.** Ours allocates more, not less: 3 objects per `await` (`bcc-counts`: 3081 allocations at n = 1024, 6153 at 2048) and one dispatched call per resume. It wins because a resume jumps straight to the suspended frame, while Rust re-polls the chain of about 20 nested boxed futures on every wake. xctrace: Rust spends 62% in the poll closures and about 25% in malloc/free; ours spends 69% in one resume code and 11% in `bc_alloc`/`bc_free`. The Rust executor is a minimal std-only round robin. |
| raise-small, raise-large | `raise` four levels deep inside counted loops is an abort, against `Result` and `?` at every level plus `try_fold`. Two error sizes. | **Not supported.** After inlining, both sides are a branch per level, and Rust's `Result` costs nothing at either size (123 ms at both). Ours is at parity with the 64-byte error (1.03×) and 1.30× slower with the `i32` error. The cause is below. |
| handlers-di, handlers-di-generic | Handlers as dependency injection (a logger and a clock) are erased to direct calls, against `&mut dyn Trait` and against generic parameters. | **Parity with `dyn`** (0.98×). Rust devirtualises the clock after inlining, and its logger's `blr` runs only every eighth step. **0.54× against generics and 0.61× against C function pointers**, but the generic win is not dispatch: LLVM if-converted Rust's every-eighth-step update into a `csel` chain that runs every step. Ours is a direct inline loop with 0 indirect calls. The clock's state is loaded and stored through its cell on every step: `ldr x2,[x21]; add x2,x2,#3; str x2,[x21]`. |
| compile time and binary size | Measured honestly; #509's copies may make us lose. | **Size: we win against Rust, lose to C.** Our machine code is 3–6K (12K for async-tree) against Rust's 213K (std) and C's 0.3–1.2K. **Compile time: we lose**, 2–8× Rust's. See *Compile time and size*. |

## Diagnosis of every gap over 1.5×

Profiles are xctrace's Time Profiler. `sample` hangs on this machine, and `perf` is not
available. The IR excerpts come from `bench/out/<name>/main.ll` as emitted, and from clang's
optimised IR (`xcrun clang -O2 -S -emit-llvm`).

### Loops that may diverge are a state machine: sieve 5.6×, chain-yield 2.1×, chain-gen 21.5×

**Cause.** A `while` or `loop` is div (SPEC §14), and so is every generator's body. Its turns
are observations of a `delay` codata value. The flat IR's `drive` function runs them: it calls
the loop's step, receives the next state, and tail-calls itself (Backend README, *Stack*).
The state handed from turn to turn is the loop closure's environment. Because `main` is div here
(`next_arg` has a `while`), that environment is the union of every loop code in the program,
padded to the widest member with zero words (`Flat/Lower.lean`, `mkInj`).

| program | `drive`'s parameters (state words) | step's result buffer |
|---|---|---|
| sieve | 49 | `alloca [50 x i64]` |
| chain-yield | 36 | `alloca [37 x i64]` |
| chain-gen | 71 | `alloca [72 x i64]` |

Each turn of the loop is one step. The step returns the whole state through the result pointer,
since a result wider than 8 words goes through memory (SPEC §40). `drive` then passes it on in
its `musttail` self-call, which puts 63 of chain-gen's 71 words on the stack.

```llvm
; drive (chain-gen)
  %buf27720 = alloca [72 x i64], align 8
  call void @f169(ptr %buf27720, i64 %t27656, i64 %t27657, …)          ; the step
  %t27950 = musttail call {i64, i64, i64} @f357(i64 %t27879, …)        ; drive again, 71 words
```

In chain-gen the step writes the next state per element, about 45 stores, most of them zero
padding. It then returns to `drive`:

```asm
  mov  w16, #1
  dup.2d v0, x16
  str  q0, [x0]
  stp  xzr, x1, [x0, #16]
  …                                   ; 30 more stores of state words, most `xzr`/`q0 = 0`
  stp  x9, x8, [x0, #352]
  ret
```

In sieve, LLVM inlines the step into `drive`'s loop, so the state stays in registers and
spills. Every turn of the inner strike loop still runs the union's dispatch and resets about 15
registers to zero, with 5 spills:

```asm
LBB1_53:          ; the strike step, in the drive loop's header BB1_2
  mov x3, x12 ; mov x4, x9 ; mov w8, #0 ; mov w10, #0 ; mov x13, #0 ; mov x16, #0 ; mov x14, #0
  mov x11, #0 ; mov x9, #0 ; … ; stp xzr, x15, [sp, #56] ; stp x28, x22, [sp, #24] ; …
  cmp w4, w21 ; b.ge LBB1_2           ; back to the driver's dispatch
```

**Evidence that the loop form is the cause.**
- **sieve.** The same algorithm with counted loops (`sieve-for`, whose loops are `count_loop`
  tail calls inside one step) runs in 116 ms, against 507 ms. Its inner loop is 7 instructions
  with one bounds check:
  `mov w12,w11; cmp x12,x27; b.hs; strb wzr,[x12,x0]; add; subs; b.eq`.
- **The chains.**
  - chain-for (a counted `for`) runs at parity with Rust, 0.99×.
  - chain-yield is 2.1×: one `while` generator whose `yield` is a direct call of the body
    (`bcc-counts --sites`: `tail-resumptive [(1, 0)]`, no code that may suspend). The body's
    `if` resumes the generator at the end of each arm, so the clause is tail-resumptive (SPEC
    §19). What is left is the driven `while`.
  - chain-gen is 21.5×. The adapters' stored generators (`U (pull …)`) add a state machine
    each, which widens the state to 71 words.
- **Counts.** chain-gen's `bcc-counts` are 40 loads and 22 stores at every n: the flat IR does no
  memory traffic per element. The traffic comes from the native calling convention, which
  returns more than 8 words through memory and passes arguments past the 8th on the stack. So
  the flat-IR counts cannot see this cost.

### sum 1.88×: the loop is not vectorised

**Cause.** Our inner loop is scalar, interleaved by 2. Rust's and C's use NEON:
`ldp q4,q5; ldp q6,q7; add.2d ×4`.

```asm
LBB1_122:                     ; ours
  ldp  x17, x0, [x16], #16
  add  x13, x17, x13
  add  x14, x0, x14
  subs x15, x15, #2
  b.ne LBB1_122
```

The vectorizer's remark is `the cost-model indicates that vectorization is not beneficial`.

**Why the cost model refuses.** Every address is an integer: `inttoptr i64 (add (shl i, 3),
base)` (`Native/Lower.lean`, `ptrAt`). The optimised loop is

```llvm
%t69 = shl i64 %i, 3
%t70 = add i64 %t69, %base
%t52 = inttoptr i64 %t70 to ptr
%t53 = load i64, ptr %t52, align 8
```

Out of the program, the same loop written with `inttoptr` stays scalar, and written with
`getelementptr i64, ptr %base, i64 %i` vectorises to `add.2d` ×4. The two functions are
`@sum_int` and `@sum_gep` in `bench/repro/vectorize.ll`.

**Not diagnosed.**
- A prototype that rewrites the addresses of clang's optimised IR as `getelementptr` from an
  `inttoptr` base does vectorise one copy of the loop.
- But the copy that runs is another instance (#509), and it stays scalar.
- The prototype also re-optimises, and that alone gives 131 ms, so it does not isolate the
  rewrite. I have not measured the fix itself.
- Large arrays are 8 bytes off 16-byte alignment (`bc_alloc` returns `malloc + 8`). C with the
  same misalignment is 5% slower (115 against 109 ms).

### n-body 1.78× (1.16× against C)

**Against C, the gap is bounds checks.** C has the same layout, bodies in memory and loops not
unrolled. Our inner loop still has three bounds-check branches per pair of bodies, each
zeroing the default value and loading only when the index is in range:

```asm
movi.2d v1, #0
cmp     x13, #4
b.hi    LBB1_97
ldp     d3, d2, [x15, #56]
```

That is 24732 checks over 100 steps (`bcc-counts`).

**Rust is 1.56× faster than C because of fixed-size types.** `[Body; 5]` and `[f64; 3]` give
constant trip counts, so LLVM unrolls all 10 pairs and vectorises them in pairs: Rust's
assembly there has `fsqrt.2d` ×4, `fdiv.2d` ×4 and 70 `fmul.2d`. We have neither records nor
fixed-size arrays (#489, #72).

**Not diagnosed:** why LLVM declines to unroll our advance loops.

### gen-tree 1.72×, gen-tree-cb 1.96×: the right subtree's call is not a tail call

**Cause.** The generator itself is erased: `yield` becomes an inline add, with 0 allocations and
0 dispatched calls. The recursion is what costs.
- Our walk makes two `bl _f6` per node. C's makes one, because clang turns its right-subtree
  call into a loop.
- Ours cannot. After the right call returns, the flat IR does a `case` on the callee's
  `Exhausted` sum and rebuilds it word by word, zeroing the padding words on the `inl` side:

  ```llvm
  %t226 = icmp eq i64 %t225, 0
  …
  insertvalue … i64 0, 2
  …
  ret
  ```

- That rebuild is not an identity, so the call is not in return position.
- Each frame also carries the depth budget and its test (SPEC §20).

### Under 1.5×, for the record

- **quicksort 1.24×, sort-generic 1.29×.**
  - `peek`'s replace-and-restore is removed by LLVM here. The partition loop reads each element
    with one `ldr w13, [x13, x8]` and stores nothing on the read path.
  - The flat IR still shows two stores per read: quicksort has `loads 96889 stores 88843` in
    `corpus/counts.expected`.
  - What remains:
    - three bounds checks per step (`cmp x12, x3; b.hs` on `j`, and on both indices of the
      swap);
    - 8-byte slots for `i32`: the swap is `ldr x13, [x8, x22, lsl #3]`, twice Rust's footprint
      for 10⁶ elements.
- **raise-small 1.30×.**
  - With the `i32` error, the error path does not leave the loop. It writes the error word into
    the loop-carried state of `count_try_loop` and goes back to the latch.
  - So every iteration tests a flag, and LLVM cannot strength-reduce the key `c·len + j`. Our
    loop has `madd x3, x17, x0, x2; cbz x3` where Rust's has `add w2, w2, #7919`.
  - With the 64-byte error the error branch exits the loop directly (`cbz w7, LBB1_113`), and
    raise-large runs at parity.
- **binary-trees 0.40×: the win is the allocator.**
  - Rebuilt with our runtime's scheme (free lists by size over 1 MiB blocks, no locking) instead
    of `malloc`/`free`, the C program runs in 0.25 s instead of 0.86 s.
  - Against that C, ours is 1.58× slower:
    - the node is 4 words: a tag word plus a pointer per child, with no null-pointer niche
      (SPEC §35 *Open*);
    - `bc_alloc` is out of line and updates `bc_live` and `bc_allocs` on every call;
    - each call carries the recursion budget and returns an "exhausted" flag the caller tests.

## Compile time and size

- **Build time.** Ours is 0.24–1.05 s, against Rust's 0.09–0.15 s and C's 0.04–0.06 s.
  - **`bcc` is mostly the certifying checker.** `bcc compile --timings bench/sieve-for/main.bc`
    gives `check: 503 ms` of `total: 603 ms`, against `elaborate: 62 ms` and the backend under
    40 ms.
  - **It checks every included library declaration.** Programs that include `float` (668
    lines, for `sqrt_f64` or a conversion) take 0.6–0.8 s in `bcc`; the others take 0.13–0.27 s.
  - **#509: every use of a definition is a copy of its body.** It shows in the IR's size, not
    the binary's. `bench/sum` with one, two and three calls of its argument parser
    `arg_i32` (`next_arg` and `parse_i32`) emits 16784, 27573 and 38431 lines of LLVM IR, with
    195, 307 and 419 functions. Each call copies the whole call tree, about 10.8K lines.
  - **After clang the copies are small**: `__text` is 3488, 4296 and 5516 bytes.
- **Size.** Our machine code, runtime included, is 2.8–12K, against Rust's 213K (std's
  formatting and panic machinery) and C's 0.3–1.2K. Every executable rounds to 50K stripped,
  since Mach-O pads segments to 16K pages.

## The counts columns (#213 item 5)

`bcc-counts <file>` prints, besides `allocs`, `indirect` and `copies`, three counts taken at the
flat IR, and `corpus/counts.expected` records them per program:
- `loads`: every `load` and `load8` the flat-IR interpreter evaluates.
- `stores`: every `store` and `store8` it runs, heap and frame slots alike. Locals are never
  memory.
- `bounds`: every bounds check it runs.

**What counts as a bounds check.** A bounds check is a test of an index against an array's
length that an access makes. The counting build marks each one with `Stmt.tickBound`
(`Flat/Lower.lean`, `boundTick`) at three sites:
- `idx`, which covers `array_get`, `slice_get_mut`, and the terms over them: `array_replace`,
  `slice_replace_mut`, `slice_swap_mut`, `at`, `peek`, `set`;
- `split`;
- a literal's byte.

These are not bounds checks:
- the end-of-loop tests of `tab`, `drop`, `count` and `count_try`;
- the clamp of a length below 2³¹.

The non-counting build is unchanged, and so is every WAT and native `.ll`, byte for byte. The
gate fails when a count rises above its entry, as it does for the first three.

**What the counts are and are not.** They measure what the lowering emits, before LLVM.
- A replace-and-restore read shows as two stores, and an unremoved check as one bound per access.
- LLVM may remove either: quicksort's reads are single loads in the machine code.
- Memory traffic made by the native calling convention is not in them: a result wider than 8
  words, or a stack argument (the state machines above).

## What the language forced

Nothing in either table was skipped. These shapes were forced, and each program's comments say
where:
- **Nested loops.**
  - A `for` cannot be in the body of another `for`, and a div call cannot be in a counted
    `for` (#503).
  - So inner loops are functions of their own: sieve's `strike`, matmul's `dot` and `row`.
  - sieve's repetition loop is a `while`, because `sieve` is div.
- **Lends.**
  - A shared view cannot be used twice in a loop body (#58, #142). Arrays are therefore owned
    and threaded, and read with `at(&a, …)`, one lend per `let`.
  - A lend in an `if` arm off the spine is refused (#502, #538 filed here), so wordcount's map
    update is a function, and handlers-di has one function per logger.
- **Shadowing.** A loop-local binding that shadows an owner is refused (#493), so quicksort's
  loop rebinds `u`, not `w`.
- **Closures.** A `!` closure cannot capture a local (#9), so quicksort's input is the same on
  every repetition.
- **Recursion over a view.** `with exhausted_to_option` is used, since `on_exhausted`'s default
  cannot capture the view.
- **Records.** n-body's bodies are seven `f64`s in an array, since there are no records (#489).

## Ranked fix units

Ranked by measured impact. None is filed (#537: the list is agreed first).

1. **Lower div loops as loops (#213 item 3).**
   - A `while`/`loop`, or a generator's body, whose turn does not suspend becomes a native loop
     in its function, its state in locals. `drive` then runs only at real suspensions.
   - Expected:
     - sieve from 5.6× to sieve-for's 1.3×;
     - chain-yield from 2.1× toward chain-for's 1.0×;
     - every program that reads its arguments (`next_arg`) stops making `main` one state
       machine.
2. **Narrow the driver's state, and pad sums with `poison`.**
   - Hand a turn only the live code's environment instead of the union, and stop zero-filling
     padding words (`mkInj`/`mkCon`, an "undefined" flat-IR word lowered to `poison`).
   - Also: no result buffer for the loop state, and a convention that passes the state in
     registers (#535's padding is part of the 71 words).
   - Expected: most of chain-gen's remaining factor once (1) is in, where the stored
     generators' state machines still turn. Also gen-tree's padding writes.
3. **A call whose result is re-injected into the same sum is a tail call.**
   - This is the `Exhausted`/`Fail` pass-through, `case r { inl x → inl x | inr e → inr e }`.
     Pass the callee's words through.
   - Expected: gen-tree's right recursion becomes a loop, halving the calls per node, about
     1.7–2× toward C. It helps every recursive function that ends in a recursive call.
4. **Bounds checks eliminated by typing (#213 item 2).**
   - A `for` over a view's range, or `Fin` indices, accesses unchecked.
   - Expected:
     - n-body from 1.16× to about 1.0× of C;
     - quicksort and sort-generic lose 3 checks per partition step;
     - sieve-for and matmul lose 1–2 checks per access.
5. **Pointer-based addressing and aligned arrays.**
   - Emit `getelementptr` from a pointer base rather than `inttoptr` of integer arithmetic, and
     align large arrays to 16 bytes (`bc_alloc`).
   - Expected: sum's loop vectorises (the repro). The size of the gain is not measured, since
     the prototype could not reach the instance that runs.
6. **A `count_try` step's error exits the loop.** Error words would no longer share the
   loop-carried locals. Expected: raise-small from 1.30× to raise-large's 1.0×.
7. **Cheaper bounded recursion.**
   - Cut the per-call budget test and "exhausted" flag: elide them for non-escaping
     recursion, or test only every k levels.
   - Expected: up to about 1.3× on recursion-heavy code (binary-trees against the C with our
     allocator, gen-tree).
8. **Narrow `i32` array slots.** Slots of 4 bytes, as Rust's. Expected: half the footprint of
   `array i32`; quicksort's 10⁶ elements fit in 4 MB instead of 8.
9. **Handler state in a register for the duration of `with`.**
   - By scalar replacement, or `noalias` on the state cell (#531).
   - Expected: one load and one store fewer per operation; handlers-di would pass Rust's `dyn`.
10. **Async: one sized state object per task.** Not three allocations per `await`. Expected:
    a further gain on async-tree, which already wins at 0.84×; the allocator is 11% of its time.
11. **Allocator fast path inline, counters only in counting builds**, plus a null-pointer niche
    for boxed sum payloads (SPEC §35 *Open*). Expected: about 4% and 8% on binary-trees.
12. **Compile time.**
    - Check only what `main` reaches: unused library declarations are checked today.
    - Compile a definition once and call it (#509).
    - Expected: `bcc` for a program that includes `float` from about 0.6 s to the 0.15 s of one
      that does not, and IR that does not grow per call site.

Records and fixed-size arrays (#489, #72) are a language unit, not a backend one. They would
give n-body the constant trip counts that make Rust 1.56× faster than C.
