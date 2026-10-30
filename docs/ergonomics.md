# Ergonomics: the surface in real programs (#577)

A design unit for the surface's verbosity: an inventory of the patterns that make real programs
long, the mechanism under each proposed sugar, a ranking, the pitch's five examples rewritten, and
prior art. It changes no code and files no issues. Each claim is marked:

- **measured**: a run of `bcc check`, `bcc desugar` or `bcc run`, or a count by the script of §9;
- **by inspection**: read off the code or SPEC at `main` `1d75f3a`, with the line cited;
- **hypothesis**: argued here, not checked.

**The binary.** The worktree has no build. Every run used
`~/repos/borrow-core-l2b-base/.lake/build/bin/bcc`, built from `3b67803`, with `BCC_LIB` pointing
at this tree's `lib/` (identical to that tree's). `main` is 29 commits later: compiler C0–C3b,
`Div` in the kernel and loops U1. The binary predates U1, so `corpus/loop-labels.bc` and
`corpus/forms.bc` do not check with it. They are left out of every rewrite experiment. The other
278 program files of corpus and bench check with it (measured).

**The measured sets** (§9.1). *corpus*: `corpus/*.bc`, `corpus/aoc/`, `corpus/axes/`, without the
kernel-text `corpus/core-*.bc` (256 files). *lib*: `lib/*.bc` (22). *bench*: `bench/*/main.bc`
(24). *book*: every accepted ```` ```bc ```` block of `book/src` (90 blocks). Comments are blanked
before matching.

## 0. Summary

- **Much of the verbosity is sugar that already exists but that the corpus does not use**
  (measured, §1, §2.1). Each site was rewritten on its own and the variant re-checked and re-run
  (§9.3):

  | today | already provided | sites rewritten | accepted, same output |
  |---|---|---|---|
  | `else { () }` | `if c { S }` (`Parser.lean:1899–1909`) | 109 | 108, and 108 with identical core |
  | `i64[0]`, `u8[200]`, `i32[7]` | a bare literal where the type is expected | 402 | 356, identical core |
  | `let _ = free(c); v` | the drop at the scope's end (SPEC §12) | 22 | 22 |
  | `let (x, r) = f(x, …)` | `let r = f(&mut x, …)` (SPEC §11) | 177 | 149 |
  | `(inl e : A + B)` | `inl e` where the type is expected | 45 | 27 |
  | `borrow imm x { v -> f(v) }` | `f(&x)` (SPEC §11) | 43 | 17 |

  The pre-NLL borrow target also exists: `let r = &mut c` lends `c` to the end of the scope
  (SPEC §14, decision 40, `LoopLend.lean:394`). The corpus uses it once.
- **The new pure sugars** (§2.2) elaborate into existing core terms, with no kernel change:
  - borrowing a `let mut` value outside a call (`let r = &mut x`, `borrow mut x`, `with h(&mut x)`)
    through the scoped cell that calls already use;
  - `*m` and `*m = e` through a `mut` borrow, as `modify` (`withswap`);
  - compound assignment;
  - unary minus, bitwise operators and conversions, as SPEC §36 operator families;
  - a closure's `!` read off the expected type;
  - pattern parameters, `mut` parameters, a lend in tail position, and an inner-scope form.
- **What needs more than syntax** (§2.4):
  - named sums and records (#141);
  - a literal's width read off later uses;
  - missing type arguments and ascriptions (SPEC §31's inference gaps);
  - whether a `let mut` buffer lends the container or its elements;
  - the inferred-extent option;
  - #58's copies of `imm` borrows;
  - a generator stored by its expected type.
- **The borrow pass** (§3), one bounded pass:
  - The pre-NLL baseline exists for cells. The low-hanging fruit is the value place: of the 66
    corpus cells that are never moved, 12 run today as `let mut`. 41 more are refused at the missing
    branch: 30 by their message, and 11 R1 tasks by hypothesis.
  - Extending each corpus block whose scope does not use the place again to the end of that scope
    ran 70 of 78 blocks with the same output.
  - Under the inferred-extent option, 63 of the 77 remaining blocks are straight-line, where
    "close after the last mention" finds the block. The other 14 need U3's join points. Nothing
    there is proposed for now.
- **A defect** (§7.1): an assignment to a `let mut` inside an arm of an `if` (measured) or a
  `match` (by inspection) that is the head of a `let` is lost. `let a = if x == 1 { x = 5; 2 } else { … }; x * 10 + a`
  gives 12 instead of 52, with no error. The parser joins the arms' assignments only for a
  statement (`Parser.lean:1595–1605`).
- **The five pitch examples** (§5) are rewritten in the target surface. Each sugar was expanded by
  its rule, and every expansion runs with the golden output (measured).
- **Corrections to the issue's premises** (§7.2):
  - drops at the scope's end exist;
  - `*m` at a `mut` borrow does not need #58;
  - the bitwise operators do not exist at the surface.

## 1. Inventory

Counts are occurrences, with files in parentheses (measured, `ergo.py count`, §9.2).

### 1.1 The issue's table

| pattern | corpus | lib | bench | book | sites |
|---|---|---|---|---|---|
| a read through a `mut` borrow, `modify m { x -> (x, x) }` | 15 (7) | 0 | 0 | 0 | `corpus/async-logged.bc:24`, `corpus/async-r1-drain.bc:13` |
| `modify m { … }`, any | 46 (24) | 0 | 1 | 7 | `corpus/async-bank-inbox.bc:46`, `corpus/async-cancel.bc:30` |
| … a write, `modify m { v -> e }` | 20 (17) | 0 | 0 | 2 | `corpus/async-logged.bc:33`, `corpus/async-lend-slots.bc:26` |
| … a write that answers a result, `{ v -> (new, r) }` | 4 | 0 | 1 | 5 | `corpus/async-cancel.bc:30`, `bench/prefix/main.bc:16` |
| `alloc(…)` | 93 (62) | 0 | 4 | 19 | `corpus/clo-capture.bc:27`, `corpus/clo-counter.bc:19` |
| `free(…)` | 74 (47) | 0 | 4 | 15 | `corpus/clo-capture.bc:37`, `corpus/clo-depth.bc:43` |
| `let _ = free(c)` | 22 (17) | 0 | 0 | 0 | `corpus/async-logged.bc:38`, `corpus/async-cancel.bc:32` |
| a value handed back, `let (x, r) = f(x, …)` | 173 (54) | 130 (9) | 4 | 2 | `corpus/clo-counter.bc:29`, `corpus/div-unhandled.bc:24` |
| `host[op](…)` outside the kernel text | 42 (18) | 177 (7) | 27 (16) | 1 | `corpus/aoc/2021-10.bc:88`, `bench/handlers-di/main.bc:35` |
| a typed literal `i64[0]`, `u8[…]` | 376 (48) | 149 (7) | 46 (17) | 94 (30) | `corpus/clo-coerce.bc:19`, `bench/handlers-di/main.bc:31` |
| an ascribed injection `(inl e : A + B)` | 45 (19) | 21 (4) | 0 | 4 | `corpus/gen-adapters-fail.bc:34`, `corpus/async-timers.bc:63` |
| `else { () }` | 88 (45) | 23 (7) | 21 (13) | 12 (9) | `corpus/async-logged.bc:32`, `corpus/aoc/2020-08.bc:41` |
| `inl`/`inr` written | 1416 (140) | 647 (18) | 24 (7) | 110 (23) | `corpus/13-1-library.bc:11` |
| `match … { inl … \| inr … }` | 290 (93) | 152 (15) | 5 (3) | 12 (10) | `corpus/aoc/2020-08.bc:46` |
| `!{ x -> … }` | 202 (85) | 47 (6) | 10 (7) | 15 (10) | `corpus/gen-pipeline-pipe.bc:28`, `corpus/aoc/2020-08.bc:26` |
| `next_arg(string_new(…))` | 1 | 0 | 22 (22) | 0 | `corpus/io-args.bc:17`, `bench/handlers-di/main.bc:12` |
| `fn arg_i32` copied into a program | 0 | 0 | 22 (22) | 0 | the same body in every bench program |

`host[…]` in the kernel text, `(unbang host[add32]) (…)`, is left out: 137 corpus and 46 book
sites are in `def`s written in the core syntax. In user programs (corpus, bench and book), the 70
surface sites break down as follows:

| kind | ops | sites |
|---|---|---|
| conversions | `extend_s` 22, `wrap` 3, `extend_u` 3, float truncations 2, `f32_convert_i32_u` 1 | 31 |
| bitwise and shifts | `and32` 12, `shr_u32` 7, `and64` 2, `shl32` 1 | 22 |
| unsigned arithmetic and comparison | `div_u64` 2, `lt_u32` 2, `gt_u64` 2, `rem_u64` 1 | 7 |
| signed arithmetic that has an operator | `add32` 3, `mul32` 3, `div_s32` 2, `div_s64` 1, `rem_s32` 1 | 10 |

The last row includes deliberate uses: `div_s32` traps where `/` raises (SPEC §39).

### 1.2 Beyond the table

| pattern | corpus | lib | bench | book | sites |
|---|---|---|---|---|---|
| an update assignment `x = x + e` | 197 (93) | 23 (6) | 57 (21) | 35 (23) | `corpus/gen-pipeline-pipe.bc:26`, `bench/handlers-di/main.bc:36` |
| `0 - x`: no unary minus | 85 (55) | 33 (6) | 2 | 12 (11) | `corpus/async-logged.bc:36`, `lib/slice.bc:27` |
| an explicit borrow block | 187 (86) | 24 (5) | 27 (24) | 15 (11) | `corpus/async-logged.bc:23`, `corpus/aoc/2024-01.bc:33` |
| … naming its lifetime `{ 'x, v -> … }` | 116 (60) | 14 (2) | 0 | 1 | `corpus/clo-capture.bc:29` |
| … whose body is one call of the borrow | 53 | 15 | 1 | 4 | `corpus/aoc/2024-01.bc:33`, `bench/handlers-di/main.bc:13` |
| `let r = &x` / `&mut x` | 1 | 0 | 0 | 1 | `corpus/lend-config.bc:38` |
| `&mut x` / `&x` at a call | 206 / 95 | 12 / 25 | 10 / 55 | 37 / 7 | `corpus/div-unhandled.bc:21` |
| explicit type arguments at a call `f[A](…)` | 360 (120) | 236 (12) | 18 (11) | 24 (19) | `corpus/async-logged.bc:42`, `corpus/aoc/2020-08.bc:60` |
| a signature with lifetime parameters | 114 (53) | 107 (10) | 9 (5) | 11 (8) | `corpus/clo-coerce.bc:16` |
| … with exactly one | 100 | 91 | 9 | 11 | — |
| a CBPV type written at the surface `U (…)` | 137 (47) | 105 (9) | 0 | 7 (5) | `corpus/gen-adapters-fail.bc:66` |
| … a generator stored by ascription `let g : U (pull …) = …; g` | 36 (18) | 15 | 0 | 1 | `corpus/gen-adapters-fail.bc:66`, `corpus/async-r1-cancel.bc:28` |
| `let mut x = x;`: a value rebound to be assignable | 25 (17) | 28 (5) | 15 (6) | 0 | `corpus/aoc/2020-08.bc:36` |
| a pair parameter taken apart at once | 7 | 3 | 0 | 3 | `corpus/gen-pipeline-pipe.bc:21`, `corpus/gen-adapters-fail.bc:49` |
| a closure taking its argument apart at once | 4 | 0 | 0 | 0 | `corpus/text-wordfreq.bc:109` |
| `(x, ())`: a handed-back value paired with unit | 18 (14) | 13 (7) | 0 | 4 | `lib/io.bc:18` |
| an option with a default, `{ inl x -> x \| inr _ -> d }` | 40 (24) | 11 (4) | 0 | 2 | `corpus/aoc/2024-01.bc:48` |
| `print_byte(b' ')` / `putb(…, b'…')` | 69 (27) | 0 | 38 (24) | 5 | `bench/handlers-di/main.bc:63` |
| `cons(a, cons(b, …))`: a list written out | 45 (21) | 0 | 0 | 6 (5) | `corpus/text-wordfreq.bc:59` |
| `with on_exhausted(…)`: the recursion budget | 46 (33) | 1 | 7 (5) | 5 (4) | `corpus/text-wordfreq.bc:102` |
| `with default(d)` / `with to_result` | 83 (48) | 0 | 24 (22) | 15 (7) | `corpus/async-logged.bc:31` |
| `match unroll xs`: recursive data taken apart | 56 (23) | 23 (2) | 2 | 2 | `corpus/text-wordfreq.bc:39` |

### 1.3 Cells used as mutable locals

`ergo.py cells` classifies every `let c = alloc(e)` by how `c` is used in the rest of its
declaration (measured):

| set | never moved | moved (passed, paired, returned, captured) |
|---|---|---|
| corpus | 66 (in 52 files) | 15 |
| book | 15 | 1 |
| bench, lib | 0 | 0 (bench's 4 allocs are in a pair, `bench/handlers-di/main.bc:53`) |

The 66 never-moved corpus cells are used only by these forms (counts by shape):

- `&mut c` and `free` (16);
- `borrow mut` and `free` (9);
- `borrow mut` and `let _ = free` (9);
- `borrow imm` (6);
- `free` alone (5);
- `&c` (5);
- `&mut c` and `let _ = free` (5);
- the rest in combination (11).

So 66 of 81 corpus cells, in 52 programs, are mutable locals in all but name.

## 2. The mechanism under each pattern

### 2.1 Already provided: use it

| # | today | provided form | mechanism | measured |
|---|---|---|---|---|
| A1 | `if c { S } else { () }` | `if c { S }` | the parser supplies the `else` arm `return ()` (`Parser.lean:1899–1909`) | 108 of 109 program sites drop it with identical core; the 109th is `loop-labels.bc` (binary) |
| A2 | `i64[0]` | `0` where `i64` is expected | `VSugar.lit`, typed by the expected type (typed elaboration §5) | 356 of 402 (`u8` 71 of 72, `i64` 71 of 112, every `i32` outside kernel text). Of the 46 left, 40 are "expected `i32`, but this has type `i64`": the width comes from a later use (M2); 4 are in a program written in the kernel text (§7.3); 2 others |
| A3 | `let _ = free(c); v` | nothing: `c` is dropped at the end of its scope | SPEC §12's inserted destructor, `free` then the content's | 22 of 22 run with the same output |
| A3′ | `free(c)` read for its content | `*c` | `VSugar.deref` at a cell lends it `imm` around a `withload` (`Sugar.lean:3333–3355`) | by inspection |
| A4 | `let (x, r) = f(x, …)` | `let r = f(&mut x, …)` | SPEC §11's lend: `io_lend <- f(x, …); let (x, r) = io_lend` (`Comp.elab`, `Sugar.lean:124–135`) | 149 of 177 run with the same output. Refused: 14 where the threaded value is itself a view (`array_mut 'a i32`) or the call also takes a capability, so `&mut` would be a reborrow, which the surface does not provide; 5 results that mention the lent lifetime; 5 calls that also thread a capability; 2 inference gaps; 2 others |
| A5 | `borrow imm x { v -> f(v) }` | `f(&x)` | `lendCall`/`lendBorrow` (`Sugar.lean:2194`, `:2265`): `withbor1`/`withbor2` of a cell, `slice_borrow_*` of an array, or a cell scoped to the call for a value | 17 of 43. Refused: 13 where the block lends a buffer's initialised prefix or a record's fields and `&x` at the call lends the whole value ("expected `array u8`, but this has type `array u8 * i32`": M4's question at a call); 9 in an annotated binding (SPEC §11 forbids a lend there); 3 closures whose parameter type was read off the block; 1 outlives |
| A6 | `let v = borrow mut c { m -> S }; R` | `let m = &mut c; S′` to the end of the scope | `lendLet` (`LoopLend.lean:394`): `borrow mut c { m -> rest }`; SPEC §14, decision 40 | §3.3 |
| A7 | `(inl i : i32 + 1)` | `inl i` where the type is expected | typed elaboration | 27 of 45. Refused: 11 cannot synthesise, 3 at a value whose type is open, 3 at an operation's type arguments, 1 argument |
| A8 | nested adapter calls | `e \|> f(a)` | SPEC §33, decision 50 | in use |
| A9 | `while … { … }; ()` as a body's end, `{ s = s + x; () }` in a clause | `while …` last; `{ s = s + x }` | unit elision | measured on `gen-adapters-fail` and `handlers-di` (§5) |

**Why the corpus does not use them** (hypothesis): most corpus programs were written as tests of
one SPEC entry, before the later sugar existed. Each now spells the core form it exercises. The
book's guide teaches the short forms (`ownership.md`), and its examples use them more. A
mechanical rewrite of the corpus with A1–A4 leaves every golden unchanged (measured above) and is
a user choice (§8, choice 9).

### 2.2 New sugar that is pure elaboration

Each row says what the sugar elaborates to. None touches `Core/`, the checker or `CDerives`; each
is a surface rule whose output the checker derives, as SPEC §12 and §36 are.

| # | sugar | elaborates to | existing piece it reuses | notes |
|---|---|---|---|---|
| N1 | borrowing a `let mut` value `x : A` outside a call: `let r = &mut x; S`, `borrow mut x { r -> S }`, `with h(&mut x) { S }` | `let io_c = alloc(x); …withbor2 io_c (r -> S)…; x = free(io_c)` (a cell scoped to the lend; nothing to write back when `x` is not used after) | `lendBorrow`'s value branch (`Sugar.lean:2210–2215`), which calls already use; `lendLet` (`LoopLend.lean:394`) and the block cases (`Sugar.lean:3380–3648`) today refuse a value (`:3646`) | the core is the cell program the corpus writes by hand, so R1, unwinding and frame slots see what they see today (§3.2) |
| N2 | `*m` at `m : mut 'a A`, `A` persistent | `modify m { io_x -> (io_x, io_x) }`, the statement lifted before the one that reads it | `withswap` (SPEC §1), the `modify` case at a `mut` borrow (`Sugar.lean:3637`) | independent of #58: the read copies a persistent content, not the borrow |
| N2′ | `*m = e` | `modify m { io_x -> e[io_x/*m] }` | the same | one swap, not two, when `e` reads `*m` |
| N3 | `x += e` (and `-=`, `*=`, `/=`, `%=`) | `x = x + e` | the parser's assignment | 312 sites |
| N4 | `-e` | `neg(e)`, a family with cases `0 - e` at the integer widths and `neg_f64`/`neg_f32` at the floats | SPEC §36's operator families; `host[f64_neg]` (`lib/float.bc:17`) | not `0 - e` at floats: `0.0 - 0.0` is `+0.0`, `-(0.0)` is `-0.0` |
| N5 | `a & b`, `a ^ b`, `a << b`, `a >> b` | families `op_and`, … with cases at `i32`/`i64` that are `host[and32]`, …, as `(+)`'s are | SPEC §36, `poly (+) at H = S` | the spellings are choice 3; shifts mask (decided); `>>` signed vs logical is open |
| N6 | `to_i64(x)`, `to_i32(x)` at `i64`, `to_f64(x)`, … | a `poly` family per target type, cases over `extend_s`, `wrap`, … | SPEC §36; `to_i32 : u8 => i32` exists (`lib/prelude.bc:21`) | the family form is one provider per type; `x as i64` is the alternative (choice 7) |
| N7 | `{ x -> e }` where `!(A => B)` is expected | `!{ x -> e }` | decision 26 (type-directed sugar); the closure already takes its parameter types from the expected type | the closure must capture only `!` values, as `!{ }` must today; refused otherwise with the same message |
| N8 | `fn f((a, b): A * B)`, `for (a, b) in V { … }` | `fn f(io_p: A * B) = let (a, b) = io_p; …`; `for io_e in V { let (a, b) = io_e; … }` | the parser's patterns (`bindPat`) | `!{ (a, b) -> … }` already takes a pattern |
| N9 | `fn f(mut x: A)` | `fn f(x: A) = let mut x = x; …` | handlers' `mut` parameters | 68 rebinding sites |
| N10 | `f(&mut x)` as a body's last expression | `let io_t = f(&mut x); io_t` | SPEC §11's lend at the head of a bind | today "lends a place to one call: it may appear only in the head" (`Sugar.lean:96–99`) |
| N11 | an inner scope that runs: `scope { S }` (spelling open) | `S`'s value, with its bindings local | the parser's block | needed for the pre-NLL baseline: `{ S }` is a thunk at the surface (`let y = { x = x + 1; x }` is `U (F i32)`, measured) |
| N12 | lifetime elision: a signature with one lifetime parameter and borrows writes none | the parameter `'a` added and given to every borrow type | the parser | 211 of 241 signatures with lifetimes have one. The book says "lifetimes are not elided in signatures", so this is choice 8 |

### 2.3 Library additions (no syntax)

| # | today | proposed | where |
|---|---|---|---|
| L1 | `fn arg_i32` copied into 22 bench programs | `arg_i32(d)` | `lib/textio.bc`, beside `next_arg` |
| L2 | `match o { inl x -> x \| inr _ -> d }` (53) | `or(o, d)`, generic over `A + 1` | `lib/prelude.bc` |
| L3 | `with to_result[E, A] { … }` then `match r { inl x -> x \| inr e -> g(e) }` | `with recover(g) { … }`: `return(a) = a; raise(e) = g(e)` | `lib/fail.bc`, beside `default` and `map_err`. It is still `raise` plus a handler |
| L4 | `print_dec64(x); print_byte(b' ')` (112) | `print(x)` as a `poly` family per type, and `print_sp`, `println` | `lib/io.bc`. Format strings are a later design |

### 2.4 Needs more than syntax

| # | pattern | what is missing underneath | count | falls out of |
|---|---|---|---|---|
| M1 | raw sums and nested pairs: `inl`/`inr`, `match … { inl … \| inr … }`, `unroll` | named variants and fields need type declarations with identity: #141 | 2197 / 459 / 83 | #141 |
| M2 | `let mut acc = i64[0]` where only a later use fixes the width | a literal whose width is a placeholder until a later use fixes it, defaulting to `i32`: an inference change in the typed elaboration, not the kernel | 46 of the 402 program-file literals | none in flight |
| M3 | explicit type arguments `nil[u8]()`, `to_result[i32, i32]`, `recover[i32, i32](…)`; ascriptions the elaborator asks for | inference gaps (SPEC §31): type arguments read off later uses or the expected type. `len(&b)` at a buffer asks for `len[i32]` (measured) | 638 type-argument sites | partly #58's and the typed elaboration's later stages; none named |
| M4 | a `let mut` buffer or array lent outside a call | `&mut b` of an owned array lends its elements (`array_mut`); a cell `ref (buf A)` lends the container (`mut 'a (buf A)`). At a call the parameter type can choose (`lendCall` already reads it). A block or `let r = &mut b` has no parameter, so it needs a spelling | 12 of the 66 never-moved cells | — (choice 2) |
| M5 | explicit block ends where the rest uses the place | the inferred-extent option (§3.4) | 77 corpus blocks | U3 (live variables), J2 |
| M6 | `*r` read twice at `r : imm 'a A` (`*r * *r` is refused) | #58 E1: implicit copies of `imm` | not counted: programs avoid the form | #58 (U5) |
| M7 | `let g : U (pull i32 1 1) = range(0, n); g` to store a generator | storing a call by its expected type (`flat_map`'s parameter) instead of running it; type-directed elaboration of a call | 52 | — |
| M8 | `with on_exhausted(…)` around recursive data | the recursion budget of SPEC §20; not surface sugar | 59 | the recursion design |

## 3. The borrow pass

One bounded pass, as #577's last comment asks: the pre-NLL baseline, and the inferred-extent
option only as far as it finds cheap wins. No proof and no borrow-calculus change is proposed.

### 3.1 The baseline exists

By inspection, every form the user's decisions name is built for a cell or an array:

- `f(&mut x)` for one call (SPEC §11, `lendCall`). At a borrow parameter, the call is wrapped in
  `withbor2`. At an owned parameter, `x` is threaded and handed back. At a `let mut` value, the
  call gets a cell scoped to it. `corpus/div-unhandled.bc:21` (`push(&mut b, amount)`) and the
  book's `bump(&mut n)` (`ownership.md`) use it.
- `let r = &mut x` to the end of the enclosing scope (SPEC §14, decision 40, `lendLet`). After it,
  `x` may not be named: "`x` is lent to `r` for the rest of the block, so it cannot be used after
  `let r = &mut x`" (measured).
- drops at the scope's end (SPEC §12).

`corpus/async-logged.bc` written with `let m = &mut c` and without the block, the `else { () }`
and the `free` runs today with its golden output (measured; the program is in §9.4).

### 3.2 The low-hanging fruit: the value place

`ergo.py rewrite cell_to_local` rewrites each never-moved corpus cell. `let c = alloc(e)` becomes
`let mut c = e`, `free(c)` and `*c` become `c`, and `let _ = free(c)` is removed. Lends and blocks
are left as written. Results (measured):

| result | cells | what it needs |
|---|---|---|
| accepted, same output | 12 | nothing: `let mut` and `&mut x` at calls already work |
| "this borrow block's place has type `i32`" | 28 | N1 at a block |
| a record place lent fieldwise | 2 | N1 at the record case (`Sugar.lean:3547`) |
| "this borrow block's body performs the operation …, which resumes" | 11 | N1 on the effectful block's path. Every one is an R1 task (`async-*`); the cell program it would produce is the one the corpus runs today (hypothesis) |
| container vs elements (`expected mut 'a (buf …)`, found `array_mut 'a …`) | 12 | M4 |
| other | 1 | `corpus/lend-server.bc:36` destructures the cell's content through the cell |

**N1 is the low-hanging fruit.** It is pure elaboration: `lendBorrow` already builds the scoped
cell for a call, and the block and `lendLet` paths would build the same cell around their body.
The produced core is the hand-written cell program, so every acceptance the checker gives today
carries over. That includes R1's (`PinLaw`), unwinding's (`withbor2u`) and the backend's
frame-slot placement (`docs/compiler.md` N5). It would cover up to 41 of the 66 (hypothesis: the
28 and 2 by their message; the 11 because their message comes from the same missing branch on the
effectful path).

**The handler state** is the same branch. `with summing(&mut st) { … }` at an `i64` value `st` is
refused today with the block message (measured). Under N1 it is a scoped cell. A scoped cell
fresh in each arm of an `if` is accepted today (measured, the expansion of §5.2), so the value form
does not meet #538. #538 concerns one cell lent in both arms.

### 3.3 The baseline on the corpus's blocks

`ergo.py blocks` classifies each explicit block. The *rest* is the code after the block, to the
end of its enclosing scope (measured):

| corpus blocks | `imm` | `mut` | total |
|---|---|---|---|
| **tail**: the rest does not name the place, or only frees it | 87 | 20 | 107 |
| **reused, straight**: the rest names the place; every mention of the borrow is at the block's top level | 37 | 26 | 63 |
| **reused, nested**: some mention is inside a branch, loop, closure or handler body | 10 | 4 | 14 |
| total | 134 | 50 | 184 |

(lib: 14 tail, 6 straight, 4 nested; bench: 25 tail, 2 nested; book: 10 tail, 3 straight, 2
nested.)

A tail block is what `let m = &mut x` to the end of the scope gives, except that the rest moves
into the block. `ergo.py rewrite extend_tail` extends each tail block that is followed by a rest:
`let p = borrow k x { m -> S; e }; R` becomes `borrow k x { m -> S; let p = e; R }`. Results
(measured):

- 83 sites. 5 were not rewritten correctly by the script (it misplaces the scope's end), which
  leaves 78.
- 70 accepted, all with the same output.
- 8 refused, each where moving the rest into the lend changes what the lend covers:
  - 3: "the type of the block's result is not determined here" (`corpus/effects-map.bc:43`). The
    block's result is now the rest's, which the elaborator does not take from the function's
    result type (M3).
  - 2: a capability or cell used in the rest is now inside the block (`corpus/io-task.bc:26`).
  - 2: the rest uses a value from outside the block across a resumption, which R1 refuses
    (`corpus/async-cancel.bc:25`). This is the borrow guarantee working.
  - 1: the rest raises inside a buffer's block, which has no unwinding form
    (`corpus/aoc/2021-15.bc:92`).

So under the lexical baseline, the 107 tail blocks need no inner scope. For about nine in ten of
them, extending the block to the scope's end changes nothing observable. The 77 reused blocks
need an inner scope (N11) or an earlier end (§3.4).

### 3.4 The inferred-extent option (a hypothesis, not proposed now)

#577's comment of 2026-10-19 proposes inferring a block's end in the elaborator and checking the
result in the kernel. Measured only as far as it finds cheap wins:

- **Straight-line, 63 corpus blocks** (+6 lib, +3 book). Every mention of the borrow is at the
  block's top level. "Close the block after the last mention of the borrow" then finds a block
  that ends no later than the written one (by construction). The written block is one such
  extent, so the inference finds an extent whenever the written program has one (hypothesis).
- **What that needs** (by inspection):
  - The block must hand on the variables it binds that the code after it reads: the block's
    result becomes the tuple of its live-out variables, as `LoopLend`'s stretches already do
    ("a stretch hands on the names later code reads", decision 40).
  - Computing live variables with scope is U3's job (#550, `docs/loops.md` §6). With U3 in
    place, the straight-line case is an elaboration over U3's result.
- **Nested, 14 corpus blocks.** Ending a lend inside a branch means moving the rest into the arms
  (`normExits`' duplication) or a join point (J2). Deeper work; it falls out of U3 and J2.

**Left for deeper work, not examined further:**

1. whether moving the hand-back earlier is unobservable when the block contains a finaliser or
   an unwinding form (`withbor2u`). By inspection, the order of destructor calls on the unwinding
   path can change;
2. error messages that fall back to the lexical reading when an inferred extent is refused;
3. `imm` blocks after #58, where last use becomes liveness again.

**Recommendation.** Build N1, N10 and N11 (pure, small), and the corpus rewrite with A6. Leave the
inferred-extent option until U3 lands, then re-measure the 63 straight-line blocks against it.
That is where this pass stops.

## 4. Ranking

Frequency is the occurrences over the four sets. Obscurity is how much the pattern hides what the
program does in the pitch's five examples: **H** (the reader has to decode it), **M** (noise
around the intent), **L** (a few characters). The order weighs both, H first.

| rank | pattern | count | obscurity | class | in-flight work it falls out of |
|---|---|---|---|---|---|
| 1 | a mutable local through a heap cell (`alloc`, `borrow mut`, `free`) | 116 cells, 253 blocks, 93 frees | H | A3, A5, A6 today; N1 (pure) | none: N1 is new |
| 2 | raw sums `inl`/`inr` and nested pairs | 2197 | H | M1 | #141 |
| 3 | values handed back `let (x, r) = f(x, …)` | 309 | H | A4 today (149/177); N10 | — |
| 4 | host operations: bitwise, shifts, conversions | 247 (70 in programs) | H | N5, N6 (pure, §36) | — |
| 5 | reads and writes through a `mut` borrow by `modify` | 54 | H in `async-logged` | N2 (pure) | not #58 |
| 6 | typed literals | 665 | M | A2 today (356/402); M2 for 46 | — |
| 7 | explicit type arguments | 638 | M | M3 | — |
| 8 | the `!` closure sigil | 274 | M | N7 (pure, type-directed) | — |
| 9 | `x = x + e` | 312 | L | N3 (pure) | — |
| 10 | `else { () }` | 144 | L | A1 today (108/109) | — |
| 11 | `0 - x` | 132 | L | N4 (pure, §36) | — |
| 12 | argument plumbing (`next_arg`, `arg_i32` × 22) | 23 | M in `handlers-di` | L1 | — |
| 13 | pair parameters taken apart, `let mut x = x` | 17 + 68 | L | N8, N9 (pure) | — |
| 14 | a generator stored by ascription | 52 | H where it occurs | M7 | — |
| 15 | lifetime parameters in signatures | 241 | M | N12 (choice 8) | — |
| 16 | print plumbing, option defaults, `to_result` + `match` | 112, 53, 122 | M | L2–L4 | — |
| 17 | ascribed injections | 70 | M | A7 today (27/45); M3 | — |

**What in-flight work removes** (by inspection):

- **The typed term** (C0–C3b, `docs/compiler.md`, landed on `main`) removes none of these
  patterns. It is backend-facing: it carries the checker's types to the compiler. It does not
  change what the elaborator infers.
- **#58** (E1, loops U5) removes M6, `*r` read twice at `imm`, and `for` over shared data in the
  AA cell of `docs/loops.md`. It does not remove N2: a read through `mut` copies a persistent
  content and never copies the borrow.
- **U2–U4** (#549–#551):
  - U3's join points in heads (J1) are predicted to fix the defect of §7.1, an assignment lost in
    a `let`'s `if` head. This is #502's shape without the loop (hypothesis).
  - U3's live variables are the piece §3.4's inference needs.
  - U4's loops as values (`let r = loop { … break v }`, `while … else`) remove the flag variables
    that loops thread today. They are not counted here.
  - U2 removes no pattern of this inventory.

## 5. The five pitch examples

Each **target** below is target syntax: it does not parse today. Its expansion applies each
sugar's rule of §2.2 mechanically, and the expansion was run (measured, §9.4). The rules used:

| rule | from | to |
|---|---|---|
| N1 | `let mut x = e; …; let m = &mut x; S` (`x` a value) | `let x = e; …; let io_c = alloc(x); borrow mut io_c { m -> S }` |
| N1 | `with h(&mut x) { S }` (`x` a value) | `let io_c = alloc(x); let io_r = with h(&mut io_c) { S }; x = free(io_c); io_r` |
| N2 | `S[*m]`, `m : mut 'a A`, `A` persistent | `let io_r = modify m { io_x -> (io_x, io_x) }; S[io_r]` |
| N2′ | `*m = e[*m]` | `modify m { io_x -> e[io_x] }` |
| N3 | `x += e` | `x = x + e` |
| N4 | `-e` at `i32` | `0 - e` |
| N5 | `a & b` at `i32` | `host[and32](a, b)` (the family's case at `i32`) |
| N6 | `to_i64(k)` at `i32` | `host[extend_s](k)` (the family's case at `i32`) |
| N7 | `{ x -> e }` at `!(A => B)` | `!{ x -> e }` |
| N8 | `fn f((a, b): A * B) = e` | `fn f(io_p: A * B) = let (a, b) = io_p; e` |
| N8 | `for (a, b) in V { S }` | `for io_e in V { let (a, b) = io_e; S }` |
| N10 | `…; f(&mut x)` at a body's end | `…; let io_t = f(&mut x); io_t` |

The library additions (L1, L3) are defined in the expansion, as they would be in `lib/`.

### 5.1 `corpus/async-logged.bc`

<table><tr><th>today</th><th>target syntax</th></tr><tr><td>

```bc
fn careful(n: i32) -> i32 with Async =
  let c = alloc(n);
  let v = borrow mut c { m ->
    let a = modify m { x -> (x, x) };
    log(a);
    let p = (m, 10);
    await();
    let (m, k) = p;
    let b = modify m { x -> (x, x) };
    log(b);
    let r = with to_result[i32, i32] {
      if b == 2 { raise(b) } else { () };
      modify m { x -> x * k };
      modify m { x -> (x, x) }
    };
    match r { inl x -> x | inr e -> 0 - e }
  };
  let _ = free(c);
  v
```

</td><td>

```bc
fn careful(n: i32) -> i32 with Async =
  let mut c = n;
  let m = &mut c;
  log(*m);
  let p = (m, 10);
  await();
  let (m, k) = p;
  let b = *m;
  log(b);
  with recover[i32, i32]({ e -> -e }) {
    if b == 2 { raise(b) };
    *m = *m * k;
    *m
  }
```

</td></tr></table>

Sugars: N1, N2, N2′, N4, N7, A1, A3, L3. The view still crosses the `await` in a pair: R1
(SPEC §29) is unchanged, because the expansion is the corpus's own block over a cell. What stays:
- `[i32, i32]` (M3);
- the pair that carries `m` across the `await`, which is the relaxed lend as SPEC §29 states it.

### 5.2 `bench/handlers-di/main.bc`

<table><tr><th>today</th><th>target syntax</th></tr><tr><td>

```bc
fn arg_i32(d: i32) -> i32 =
  let (s, got) = next_arg(string_new(16));
  let n = borrow imm s { t ->
    with default(d) { parse_i32(t) } };
  if got { n } else { d }

effect Log { fn log(x: i64) }
effect Ticks { fn now_ns() -> i64 }

handler summing(mut s: i64): Log =
  { log(x) = { s = s + x; () } }
handler hashing(mut h: i64): Log =
  { log(x) = { h = h * 31 + x; () } }
handler fake_clock(mut t: i64): Ticks =
  { now_ns() = { t = t + 3; t } }

fn value(k: i32) -> i64 =
  host[extend_s]((k * 7919) % 1000)

fn work(n: i32) -> i64 with Log, Ticks =
  let mut acc = i64[0];
  for i in 0..n {
    let t = now_ns();
    let v = value(i);
    if host[and32](i, 7) == 0 { log(t + v) }
    else { () };
    acc = acc + v
  };
  acc

fn run_summing(logc: ref i64, clk: ref i64,
    n: i32) -> (ref i64 * ref i64) * i64 =
  let a = with summing(&mut logc) {
    with fake_clock(&mut clk) { work(n) } };
  ((logc, clk), a)

fn run_hashing(logc: ref i64, clk: ref i64,
    n: i32) -> (ref i64 * ref i64) * i64 =
  let a = with hashing(&mut logc) {
    with fake_clock(&mut clk) { work(n) } };
  ((logc, clk), a)

main -> i32 =
  let n = arg_i32(1000);
  let reps = arg_i32(1);
  let mode = arg_i32(0);
  let mut cells = (alloc(i64[0]), alloc(i64[0]));
  let mut acc = i64[0];
  for r in 0..reps {
    let (logc, clk) = cells;
    let (cs, a) = if mode == 0 {
      run_summing(logc, clk, n) }
      else { run_hashing(logc, clk, n) };
    cells = cs;
    acc = acc + a
  };
  let (logc, clk) = cells;
  print_dec64(acc);
  print_byte(b' ');
  print_dec64(free(logc));
  print_byte(b' ');
  print_dec64(free(clk));
  print_byte(b'\n');
  0
```

</td><td>

```bc
effect Log { fn log(x: i64) }
effect Ticks { fn now_ns() -> i64 }

handler summing(mut s: i64): Log =
  { log(x) = { s += x } }
handler hashing(mut h: i64): Log =
  { log(x) = { h = h * 31 + x } }
handler fake_clock(mut t: i64): Ticks =
  { now_ns() = { t += 3; t } }

fn value(k: i32) -> i64 = to_i64((k * 7919) % 1000)

fn work(n: i32) -> i64 with Log, Ticks =
  let mut acc: i64 = 0;
  for i in 0..n {
    let t = now_ns();
    let v = value(i);
    if i & 7 == 0 { log(t + v) };
    acc += v
  };
  acc

main -> i32 =
  let n = arg_i32(1000);
  let reps = arg_i32(1);
  let mode = arg_i32(0);
  let mut logc: i64 = 0;
  let mut clk: i64 = 0;
  let mut acc: i64 = 0;
  for r in 0..reps {
    if mode == 0 {
      acc += with summing(&mut logc) {
        with fake_clock(&mut clk) { work(n) } }
    } else {
      acc += with hashing(&mut logc) {
        with fake_clock(&mut clk) { work(n) } }
    }
  };
  print_dec64(acc); print_byte(b' ');
  print_dec64(logc); print_byte(b' ');
  print_dec64(clk); print_byte(b'\n');
  0
```

</td></tr></table>

Sugars: N1 (handler state at a value), N3, N5, N6, A1, A9, L1. The two `run_*` functions existed
because one cell lent in both arms of an `if` is refused (#538). The expansion gives each arm its
own scoped cells, which is accepted (measured), so they go. The `if` is a statement: as the head
of a `let`, it would lose the arms' assignments (§7.1). What stays: `: i64` on the `let mut`s
(M2).

### 5.3 `corpus/div-unhandled.bc`

<table><tr><th>today</th><th>target syntax</th></tr><tr><td>

```bc
fn split(amount: i32, parts: i32) -> i32 =
  let mut b = box buf[i32](2);
  push(&mut b, amount);
  let s = amount / parts;
  push(&mut b, s);
  let (b, n) = len_of(b);
  n
```

</td><td>

```bc
fn split(amount: i32, parts: i32) -> i32 =
  let mut b = box buf[i32](2);
  push(&mut b, amount);
  push(&mut b, amount / parts);
  len_of(&mut b)
```

</td></tr></table>

Sugars: N10 (and A4). Inlining `s` is not a sugar. The buffer is still live across the division,
so the run still ends `live 0` through the unwind, with exit status 1 (measured). A borrowing
`len(&b)` is refused today for want of `len`'s type argument (M3, measured).

### 5.4 `corpus/gen-adapters-fail.bc`

<table><tr><th>today</th><th>target syntax</th></tr><tr><td>

```bc
fn upto(lo: i32, hi: i32, bad: i32)
    -> i32 + 1 with Yield[i32] =
  let mut i = lo;
  while i < hi && i != bad
    { yield(i); i = i + 1 };
  if i == bad { (inl i : i32 + 1) }
  else { (inr () : i32 + 1) }

fn range(lo: i32, hi: i32)
    -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

fn add_up(p: i32 * i32) -> i32 * bool =
  let (s, x) = p;
  if s + x >= 10 { (s + x, true) }
  else { (s + x, false) }

main -> i32 =
  let mut t = 0;
  let mut es = 0;
  let e = for y in map(upto(0, 10, 4),
      !{ x -> x * x }) { t = t + y };
  es = es + err(e);
  …
  let e = for p in enumerate(upto(1, 10, 4))
    { let (i, x) = p; t = t + i * x };
  es = es + err(e);
  …
  let e = for y in scan(upto(1, 10, 4), 0,
      !{ (s, x) -> s + x }) { t = t + y };
  es = es + err(e);
  …
```

</td><td>

```bc
fn upto(lo: i32, hi: i32, bad: i32)
    -> i32 + 1 with Yield[i32] =
  let mut i = lo;
  while i < hi && i != bad
    { yield(i); i += 1 };
  if i == bad { inl i } else { inr () }

fn range(lo: i32, hi: i32)
    -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i += 1 }

fn add_up((s, x): i32 * i32) -> i32 * bool =
  if s + x >= 10 { (s + x, true) }
  else { (s + x, false) }

main -> i32 =
  let mut t = 0;
  let mut es = 0;
  let e = for y in upto(0, 10, 4)
      |> map({ x -> x * x }) { t += y };
  es += err(e);
  …
  let e = for (i, x) in upto(1, 10, 4)
      |> enumerate { t += i * x };
  es += err(e);
  …
  let e = for y in upto(1, 10, 4)
      |> scan(0, { (s, x) -> s + x }) { t += y };
  es += err(e);
  …
```

</td></tr></table>

The whole file is in §9.4. Sugars: N3, N7, N8, A7, A8, A9. What stays:
- `let g : U (pull i32 1 1) = range(0, n); g` in `flat_map`'s closure (M7);
- the `fold_own[…]` algebras for the list lengths (M1: with named data these would be derived);
- `err(e)`'s `match` on `inl`/`inr` (M1, or L2's `or(e, 0)`).

### 5.5 `corpus/gen-pipeline-pipe.bc`

<table><tr><th>today</th><th>target syntax</th></tr><tr><td>

```bc
fn range(lo: i32, hi: i32)
    -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

fn times(p: i32 * i32) -> i32 =
  let (i, x) = p; i * x
fn even(x: i32) -> bool =
  host[and32] (x, 1) == 0

main -> i32 =
  let mut a = 0;
  for y in range(10, 20) |> enumerate
    |> map(times) |> filter(even)
    |> take(5) { a = a + y };
  let mut b = 0;
  for y in range(0, 10)
    |> map(!{ x -> x * x })
    |> filter(!{ x -> x > 5 })
    |> skip(2) |> take(3) {
    b = b + y
  };
  a * 1000 + b
```

</td><td>

```bc
fn range(lo: i32, hi: i32)
    -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i += 1 }

fn times((i, x): i32 * i32) -> i32 = i * x
fn even(x: i32) -> bool = x & 1 == 0

main -> i32 =
  let mut a = 0;
  for y in range(10, 20) |> enumerate
    |> map(times) |> filter(even)
    |> take(5) { a += y };
  let mut b = 0;
  for y in range(0, 10)
    |> map({ x -> x * x })
    |> filter({ x -> x > 5 })
    |> skip(2) |> take(3) {
    b += y
  };
  a * 1000 + b
```

</td></tr></table>

Sugars: N3, N5, N7, N8, A9. `x & 1 == 0` reads as `(x & 1) == 0` under choice 3's recommended
precedence.

## 6. Prior art, compared on fit

| convenience | Rust | Koka | Effekt | Swift | Hylo | Lean 4 `do` | fit here |
|---|---|---|---|---|---|---|---|
| mutable locals, borrowed in place | `let mut`, `&mut x`; lexical extents before the 2018 NLL, inferred after | `var x := …`, local state that cannot escape (a type rule), no borrows | `var` in a region | `var`, `inout` with `&x` for one call; exclusivity checked statically, dynamically where it cannot be | `inout` for one call or a projection; no first-class references | `let mut`, rebinding desugared to pure code | Rust's pre-NLL form, which the user chose. Swift's and Hylo's per-call `&x` is exactly A5 |
| destruction at the scope's end | `Drop`, at the scope's end, explicit `drop(x)` | reference counting (Perceus) | — | ARC | at the value's last use (hypothesis: not verified here) | GC | SPEC §12 is Rust's; Hylo's earlier placement is SPEC §12's *Open* item |
| compound assignment, unary minus, bitwise operators | all, by traits; `&` binds tighter than `==` | most, by overloading | most | all, by protocols | all | all | by §36 families, one provider per type, no traits |
| reading and writing through a reference | `*m`, `*m = e` | — | — | implicit (`inout` is a variable) | implicit | — | N2: Rust's spelling over `withswap` |
| lambda | `\|x\| e`; closure kind inferred from the body | `fn(x) e`, trailing lambdas | `{ x => e }`, second-class blocks | `{ x in e }`, `$0` | `{ x in e }` | `fun x => e` | N7: the kind from the expected type, as Rust infers it from the body |
| named variants | `enum` | `type` | `type` | `enum` with payloads | `enum` | `inductive` | #141 |
| literal width | unification over the function | inference | inference | literal protocols | inference | elaboration with defaults | A2 already; M2 is Rust's whole-function reading |
| error propagation | `?` over `Result` | effects | effects | `throws`/`try` | `throws` | `throw` in a monad | excluded: raise plus handlers only, no `?` |

What each costs them:
- Rust: the borrow checker is separate from the type system, and NLL and Polonius solve liveness
  over aliases.
- Koka: reference counting.
- Effekt: second-class functions.
- Swift: dynamic exclusivity checks.
- Hylo: no stored references.
- Lean: the `do` translation goes through a monad. Its technique, mutable variables and early
  exits desugared to join points (Ullrich and de Moura, *do unchained*, 2022), is the one this
  parser already uses for `let mut`. The surface here has no monad.

## 7. Defects and corrections

### 7.1 An assignment in a `let`'s `if` head is lost

Measured on the binary of `3b67803`:

```bc
main -> i32 =
  let mut x = 1;
  let a = if x == 1 { x = 5; 2 } else { x = 7; 3 };
  x * 10 + a
```

It prints `i32[12]`, and `bcc interp` agrees. The intended value is 52. `bcc desugar` shows each
arm's `x <- return i32[5]` bound locally and the outer `x` still 1. Inside a `for`, the same
shape gives 14 instead of 75. With the `if` as a statement it is correct (`if … { x = 5 } else {
x = 7 }; x` gives 5).

By inspection, `main` has the same code. The parser hands an `if`'s or `match`'s assignments on
to what follows only in the statement form `S; N` (`Parser.lean:1595–1605`, "A `match` or `if`
that assigns `let mut` variables hands them on to what follows"). The `let p = if …; N` and
`let p = match …; N` path (`Parser.lean:1512–1521`) binds the head and never reads `joined`.

It is a silent wrong value, not a refusal. It is close to #502 (a loop's rebinding in an arm),
and U3's join points in heads (J1) are predicted to fix it (hypothesis). It meets ergonomics
directly: the natural form of `handlers-di`'s loop body,
`let a = if mode == 0 { … logc = … } else { … }`, is this shape. §5.2 uses the statement form.
Not filed (this unit files no issues).

### 7.2 Corrections to the issue's premises

- **"Drops at scope end (implicit destruction against the explicitness rules)"** are SPEC §12,
  built. `let _ = free(c)` is removable at all 22 sites (measured). What SPEC §12 leaves open is
  earlier placement, and class-3 types (`U C`, type variables), which must be consumed.
- **"`*m` reads (#58, E1)"**: a read through a `mut` borrow of a persistent content is
  `modify m { x -> (x, x) }`. It needs no copy of the borrow, so it does not wait for #58 (N2).
  #58 is needed for an `imm` borrow read more than once (M6).
- **"`i & 7 == 0` (the operators exist)"**: there are no bitwise operators at the surface. The
  book says so ("The bitwise operations and shifts have no operators yet", `basics.md`), and the
  lexer has none. They are §36 families to add (N5).
- **"`f(&mut x)` … extending the `&c` rule to `let mut` locals"**: already done for calls
  (SPEC §11, `lendBorrow`'s value branch). The extension still missing is outside a call (N1).

### 7.3 Small findings

- 4 rewritten literals in `corpus/async-r1-cancel-finaliser-writes.bc`, which is written in the
  kernel text without the `core-` prefix, give "internal error: a surface form was not elaborated
  before checking" instead of a message.
- `bcc run <file> <args>` with the `3b67803` binary ignored the arguments in this pass:
  `handlers-di` printed the default output for `500 3 0`. The mode-1 path was therefore checked by
  editing the defaults (§9.4). This was not looked into further.

## 8. Open choices for the user

1. **The inner scope for the pre-NLL baseline** (N11). `{ S }` is a thunk at the surface, so
   Rust's bare inner block is taken. Options:
   - (a) a keyword, `scope { S }` or `block { S }`;
   - (b) `{ S }` runs when a value, not a function, is expected (type-directed, decision 26, but
     it changes the reading of existing braces);
   - (c) no inner scope: write a second borrow after the first's end.

   Recommendation: (a), spelled `scope`, provisional. Not `do`, which reads as a monad.
2. **Container or elements** for `let mut b` of a buffer or array lent outside a call (M4,
   12 cells). Options:
   - (a) by the type expected where the borrow is used (as at calls);
   - (b) two spellings, `&mut b` for the elements and `&mut b.all` (or similar) for the container;
   - (c) keep a cell for the container case.

   Recommendation: (a) at calls, which exists, and (c) for blocks until a program needs more.
3. **Bitwise operators** (N5). `&` binary versus `&x` prefix is resolved by position, as in Rust.
   `|` collides with the match-arm separator. Options for `|`:
   - (a) arms keep `|`, and bitwise or is `bor(a, b)` (4 uses, all in `lib/`);
   - (b) arms move to another separator.

   `>>` on `i32`/`i64`: arithmetic, with logical shift as `>>>` (Java's), or the reverse. User
   code uses `shr_u32` 7 times and `shr_s32` once. Precedence: recommend Rust's, where `&`, `^`
   and shifts bind tighter than comparisons, so `x & 1 == 0` is `(x & 1) == 0`.
4. **Compound assignment set** (N3): `+= -= *= /= %=` now, and the bitwise ones with N5.
   Recommendation: all five now.
5. **Lambdas** (N7). Options:
   - (a) keep `{ x -> e }` and read `!` off the expected type;
   - (b) a new spelling (`|x| e`, `fn(x) e`, `x => e`).

   Recommendation: (a). It removes the sigil at 274 sites with no new token, and `!{ }` stays for
   a closure bound without an expected type.
6. **The inferred-extent option** (§3.4). Recommendation: not now. Re-measure the 63 straight-line
   blocks after U3.
7. **Conversions** (N6): a `poly` family per target type (`to_i64(x)`) or a cast form
   (`x as i64`). Recommendation: the family, which is §36's mechanism and one provider per type.
8. **Lifetime elision** (N12): one lifetime parameter written implicitly (211 of 241 signatures).
   The book currently promises none. Recommendation: defer until the pitch is rewritten; it is
   pure sugar either way.
9. **Rewrite the corpus with A1–A4 and A6.** Every golden is unchanged (measured for A1–A4). The
   corpus programs that test the core form (`core-*`, the SPEC §11/§14 tests) keep it.
   Recommendation: rewrite the guide-facing programs and the bench; keep the entry tests.

## 9. Reproduction

All commands run from the repository root, with
`BCC=~/repos/borrow-core-l2b-base/.lake/build/bin/bcc` and `BCC_LIB=$PWD/lib`. `ergo.py` is
below (§9.5). `$T` is a scratch directory.

### 9.1 The sets and the baseline

    python3 ergo.py book $T                  # 90 blocks
    for f in $(ls corpus/*.bc corpus/aoc/*.bc corpus/axes/*.bc | grep -v '^corpus/core-') bench/*/main.bc; do
      BCC_LIB=$PWD/lib $BCC check $f >/dev/null 2>&1 || echo "FAIL $f"; done
    # FAIL corpus/forms.bc, FAIL corpus/loop-labels.bc (newer than the binary)

### 9.2 Counts (§1)

    python3 ergo.py count $T                 # §1.1, §1.2, the host operations
    python3 ergo.py cells $T                 # §1.3
    python3 ergo.py blocks $T                # §3.3

### 9.3 Rewrites (§2.1, §3)

    python3 ergo.py rewrite $T else_unit free_unit inj_ascribe typed_lit hand_back \
      one_call_block cell_to_local extend_tail
    # else_unit: sites 109, accepted 108, same core 108, same run 108, run differs 0
    # free_unit: sites 22, accepted 22, same core 0, same run 22, run differs 0
    # inj_ascribe: sites 45, accepted 27, same core 0, same run 27, run differs 0
    # typed_lit: sites 402, accepted 356, same core 356, same run 356, run differs 0
    # hand_back: sites 177, accepted 149, same core 0, same run 149, run differs 0
    # one_call_block: sites 43, accepted 17, same core 0, same run 17, run differs 0
    # cell_to_local: sites 66, accepted 12, same core 0, same run 12, run differs 0
    # extend_tail: sites 83, accepted 70, same core 0, same run 70, run differs 0

Each variant's result, with the refusal's message, is in `$T/rw-<rewrite>.txt`. "Same core"
compares `bcc desugar` up to generated names that carry a source position. "Same run" compares
`bcc run`'s whole output, with the program's `.in`.

### 9.4 The pitch expansions and the defect

Each expansion is the target with every sugar expanded by §5's rules. Each was run with `bcc run`
and compared with the golden or with the original's output:

- `corpus/async-logged.bc`: identical to `async-logged.out`;
- `bench/handlers-di/main.bc`: identical output `499500 248375 3000`, and identical with the
  defaults changed to `reps = 3, mode = 1` (`1498500 -6528656884609773125 9000`);
- `corpus/div-unhandled.bc`: identical, `before`, `error: division by zero`, `live 0`, status 1;
- `corpus/gen-adapters-fail.bc`: `i32[118052]`;
- `corpus/gen-pipeline-pipe.bc`: `i32[320110]`.

<details><summary><code>async-logged</code>, expanded</summary>

```bc
include async
include fail

handler recover[E, A](f: !(E => A)): Fail[E], A -> A = {
  return(a) = a;
  raise(e) = f(e)
}

fn careful(n: i32) -> i32 with Async =
  let c = n;
  let io_c = alloc(c);
  borrow mut io_c { m ->
    let io_r1 = modify m { io_x -> (io_x, io_x) };
    log(io_r1);
    let p = (m, 10);
    await();
    let (m, k) = p;
    let b = modify m { io_x -> (io_x, io_x) };
    log(b);
    with recover[i32, i32](!{ e -> 0 - e }) {
      if b == 2 { raise(b) };
      modify m { io_x -> io_x * k };
      modify m { io_x -> (io_x, io_x) }
    }
  }

main -> List[i32] * List[i32] =
  let q = lqueue[i32]();
  let q = lpush(q, with spawn_logged { careful(3) });
  let q = lpush(q, with spawn_logged { careful(2) });
  run_logged(q)
```

Written today with a cell (A3, A6, A1 only), the same program also runs with the golden output:

```bc
fn careful(n: i32) -> i32 with Async =
  let c = alloc(n);
  let m = &mut c;
  let a = modify m { x -> (x, x) };
  log(a);
  let p = (m, 10);
  await();
  let (m, k) = p;
  let b = modify m { x -> (x, x) };
  log(b);
  let r = with to_result[i32, i32] {
    if b == 2 { raise(b) };
    modify m { x -> x * k };
    modify m { x -> (x, x) }
  };
  match r { inl x -> x | inr e -> 0 - e }
```

</details>

<details><summary><code>handlers-di</code>, expanded</summary>

```bc
include textio
include io

fn arg_i32(d: i32) -> i32 =
  let (s, got) = next_arg(string_new(16));
  let n = borrow imm s { t -> with default(d) { parse_i32(t) } };
  if got { n } else { d }

effect Log { fn log(x: i64) }
effect Ticks { fn now_ns() -> i64 }

handler summing(mut s: i64): Log = { log(x) = { s = s + x } }
handler hashing(mut h: i64): Log = { log(x) = { h = h * 31 + x } }
handler fake_clock(mut t: i64): Ticks = { now_ns() = { t = t + 3; t } }

fn value(k: i32) -> i64 = host[extend_s]((k * 7919) % 1000)

fn work(n: i32) -> i64 with Log, Ticks =
  let mut acc: i64 = 0;
  for i in 0..n {
    let t = now_ns();
    let v = value(i);
    if host[and32](i, 7) == 0 { log(t + v) };
    acc = acc + v
  };
  acc

main -> i32 =
  let n = arg_i32(1000);
  let reps = arg_i32(1);
  let mode = arg_i32(0);
  let mut logc: i64 = 0;
  let mut clk: i64 = 0;
  let mut acc: i64 = 0;
  for r in 0..reps {
    if mode == 0 {
      let io_c1 = alloc(logc);
      let io_r1 = with summing(&mut io_c1) {
        let io_c2 = alloc(clk);
        let io_r2 = with fake_clock(&mut io_c2) { work(n) };
        clk = free(io_c2);
        io_r2
      };
      logc = free(io_c1);
      acc = acc + io_r1
    } else {
      let io_c1 = alloc(logc);
      let io_r1 = with hashing(&mut io_c1) {
        let io_c2 = alloc(clk);
        let io_r2 = with fake_clock(&mut io_c2) { work(n) };
        clk = free(io_c2);
        io_r2
      };
      logc = free(io_c1);
      acc = acc + io_r1
    }
  };
  print_dec64(acc); print_byte(b' ');
  print_dec64(logc); print_byte(b' ');
  print_dec64(clk); print_byte(b'\n');
  0
```

</details>

<details><summary><code>div-unhandled</code>, expanded</summary>

```bc
include buf
include textio

fn split(amount: i32, parts: i32) -> i32 =
  let mut b = box buf[i32](2);
  push(&mut b, amount);
  push(&mut b, amount / parts);
  let io_t = len_of(&mut b);
  io_t

main -> i32 =
  print_lit("before\n");
  split(100, 0)
```

</details>

<details><summary><code>gen-adapters-fail</code>: the whole target, and its expansion</summary>

The target (target syntax):

```bc
include adapters

type List = mu X. 1 + (i32 * X)
type Line = mu X. 1 + (u8 * X)

fn upto(lo: i32, hi: i32, bad: i32) -> i32 + 1 with Yield[i32] =
  let mut i = lo;
  while i < hi && i != bad { yield(i); i += 1 };
  if i == bad { inl i } else { inr () }

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i += 1 }

fn err(e: i32 + 1) -> i32 = match e { inl b -> b | inr u -> 0 }

fn len_alg(r: 1 + i32 * i32) -> i32 = match r { inl _ -> 0 | inr (x, n) -> n + 1 }
def len : !(List => i32) = fold_own[1 + i32 * X, i32] len_alg

fn len8_alg(r: 1 + u8 * i32) -> i32 = match r { inl _ -> 0 | inr (x, n) -> n + 1 }
def len8 : !(Line => i32) = fold_own[1 + u8 * X, i32] len8_alg

fn add_up((s, x): i32 * i32) -> i32 * bool =
  if s + x >= 10 { (s + x, true) } else { (s + x, false) }

main -> i32 =
  let mut t = 0;
  let mut es = 0;
  let e = for y in upto(0, 10, 4) |> map({ x -> x * x }) { t += y };
  es += err(e);
  let e = for y in upto(0, 10, 5) |> filter({ x -> x > 1 }) { t += y };
  es += err(e);
  let e = for y in upto(0, 10, 5) |> skip(2) { t += y };
  es += err(e);
  let e = for (i, x) in upto(1, 10, 4) |> enumerate { t += i * x };
  es += err(e);
  let e = for y in upto(0, 10, 3) |> chain(range(10, 12)) { t += y };
  es += err(e);
  let e = for y in upto(0, 10, 3) |> flat_map({ n -> let g : U (pull i32 1 1) = range(0, n); g }) { t += y };
  es += err(e);
  let e = for y in upto(1, 10, 4) |> scan(0, { (s, x) -> s + x }) { t += y };
  es += err(e);
  let e = for l in upto(1, 10, 6) |> chunks(2) { t += len(l) };
  es += err(e);
  let e = for y in upto(1, 10, 6) |> batch(0, add_up) { t += y };
  es += err(e);
  let mut n = 0;
  let mut m = 0;
  let e = for l in upto(8, 14, 12) |> map({ x -> to_u8(x) }) |> lines { n += 1; m += len8(l) };
  es += err(e);
  (t + n * 10 + m) * 1000 + es
```

The expansion differs only where a rule applies: `x += e` is `x = x + e`; each closure passed to
`map`, `filter`, `flat_map` and `scan` is `!{ … }`; `add_up` takes `io_p` and starts
`let (s, x) = io_p;`; the `enumerate` loop is
`for io_e in upto(1, 10, 4) |> enumerate { let (i, x) = io_e; t = t + i * x }`.

</details>

<details><summary><code>gen-pipeline-pipe</code>, expanded</summary>

```bc
include adapters

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 }

fn times(io_p: i32 * i32) -> i32 = let (i, x) = io_p; i * x
fn even(x: i32) -> bool = host[and32](x, 1) == 0

main -> i32 =
  let mut a = 0;
  for y in range(10, 20) |> enumerate |> map(times) |> filter(even) |> take(5) { a = a + y };
  let mut b = 0;
  for y in range(0, 10) |> map(!{ x -> x * x }) |> filter(!{ x -> x > 5 }) |> skip(2) |> take(3) {
    b = b + y
  };
  a * 1000 + b
```

</details>

The defect of §7.1:

    printf 'main -> i32 =\n  let mut x = 1;\n  let a = if x == 1 { x = 5; 2 } else { x = 7; 3 };\n  x * 10 + a\n' > $T/j1.bc
    BCC_LIB=$PWD/lib $BCC run $T/j1.bc        # i32[12]; intended i32[52]
    BCC_LIB=$PWD/lib $BCC desugar $T/j1.bc    # each arm's `x <- return …` is local to the arm

The facts of §3.1 and §2.2 (each a few lines, each measured):

- `let y = { x = x + 1; x }; y` is refused: "expected `i32`, but this has type `U (F i32)`";
- `let mut x = 3; let v = borrow mut x { m -> … }` is refused: "this borrow block's place has
  type `i32`";
- `let c = alloc(3); let v = borrow mut c { m -> let a = *m; a }` is refused: "`*` reads an `imm`
  borrow or a cell, but this has type `mut 'l1 i32`";
- `let mut x = 1; let r = &mut x; x` is refused: "`x` is lent to `r` for the rest of the block";
- `let c = alloc(5); let r = &mut c; modify r { v -> v + 1 }; modify r { v -> (v, v) }` gives
  `i32[6]`;
- `twice({ x -> x + 1 }, 0)` at `!(i32 => i32)` is refused: "the type of the closure's parameter
  `x` is not determined here";
- `let mut acc = 0; acc = acc + g(5)` with `g : i64 => i64` is refused: "expected `i32`, but this
  has type `i64`";
- `fn f(mut x: i32)` and `fn f((a, b): i32 * i32)` are parse errors;
- `0 - (-3)`: "expected a value, found `-`".

### 9.5 `ergo.py`

<details><summary>the script</summary>

```python
"""The measurements of docs/ergonomics.md. Run from the repository root.

  python3 ergo.py book    <dir>               extract every accepted ```bc block of book/src into <dir>
  python3 ergo.py count   <dir>               count the patterns over corpus, lib, bench and the book blocks
  python3 ergo.py cells   <dir>               classify every `let c = alloc(e)` by how `c` is used
  python3 ergo.py blocks  <dir>               classify every explicit borrow block
  python3 ergo.py rewrite <dir> <rewrite> …   rewrite one site at a time and test each variant

<dir> is a scratch directory (the book blocks are read from it). `rewrite` needs `bcc` at $BCC
(default ~/repos/borrow-core-l2b-base/.lake/build/bin/bcc) and reads lib/ through BCC_LIB.
Comments (`--` to the end of the line, outside strings) are blanked before matching.
"""
import concurrent.futures as cf, collections, glob, os, re, subprocess, sys

# ---------------------------------------------------------------- the measured sets

def corpus_files():
    return sorted(p for p in glob.glob('corpus/*.bc') + glob.glob('corpus/aoc/*.bc') + glob.glob('corpus/axes/*.bc')
                  if not os.path.basename(p).startswith('core-'))     # core-*.bc are written in the kernel text

def sets(d):
    return {'corpus': corpus_files(), 'lib': sorted(glob.glob('lib/*.bc')),
            'bench': sorted(glob.glob('bench/*/*.bc')), 'book': sorted(glob.glob(os.path.join(d, 'book', '*.bc')))}

def book(d):
    out = os.path.join(d, 'book'); os.makedirs(out, exist_ok=True); n = 0
    for p in sorted(glob.glob('book/src/**/*.md', recursive=True)):
        lines = open(p).read().split('\n'); i = 0
        while i < len(lines):
            if lines[i].strip() == '```bc':
                first, body = i + 2, []; i += 1
                while not lines[i].startswith('```'): body.append(lines[i]); i += 1
                name = p.replace('/', '__') + f'-L{first}.bc'
                open(os.path.join(out, name), 'w').write('\n'.join(body) + '\n'); n += 1
            i += 1
    print(n, 'blocks')

def site(path, text, pos):
    """`file:line` of a match; a book block's is its line in the chapter."""
    line = text.count('\n', 0, pos) + 1
    b = os.path.basename(path)
    if '__' in b:
        md, l0 = b[:-3].rsplit('-L', 1)
        return f"{md.replace('__', '/')}:{int(l0) + line - 1}"
    return f'{path}:{line}'

def strip(src):
    out = []
    for line in src.split('\n'):
        s, q, i = [], False, 0
        while i < len(line):
            ch = line[i]
            if q:
                s.append(ch)
                if ch == '\\' and i + 1 < len(line): s.append(line[i + 1]); i += 2; continue
                if ch == '"': q = False
            elif ch == '"': q = True; s.append(ch)
            elif line.startswith('--', i): s.append(' ' * (len(line) - i)); break
            else: s.append(ch)
            i += 1
        out.append(''.join(s))
    return '\n'.join(out)

def close(t, i):
    """The index of the bracket closing the one at t[i]."""
    o = t[i]; c = {'(': ')', '{': '}', '[': ']'}[o]; d = 0
    for j in range(i, len(t)):
        if t[j] == o: d += 1
        elif t[j] == c:
            d -= 1
            if d == 0: return j
    return None

def top_level(s, ch):
    d, out = 0, []
    for j, c in enumerate(s):
        if c in '([{': d += 1
        elif c in ')]}': d -= 1
        elif c == ch and d == 0: out.append(j)
    return out

DECL = re.compile(r'^(fn|main|def|handler|poly|effect|type)\b', re.M)

# ---------------------------------------------------------------- count

PATTERNS = []
def P(key, rx, pred=None): PATTERNS.append((key, re.compile(rx, re.M), pred))

P('read-pair', r'modify\s+\w+\s*\{\s*(\w+)\s*->\s*\(\s*\1\s*,\s*\1\s*\)\s*\}')
P('modify', r'\bmodify\s+(&mut\s+)?\w+\s*\{')
P('modify-update', r'\bmodify\s+(&mut\s+)?\w+\s*\{\s*(\w+)\s*->\s*(?![\s(])[^{};]*\}')
P('modify-result', r'\bmodify\s+(&mut\s+)?\w+\s*\{\s*(\w+)\s*->\s*\((?!\s*\2\s*,\s*\2\s*\))')
P('deref', r'\*[a-z_(]', lambda t, m: re.search(r'(^|[=(,{;|>\[]|->|[-+*/%<>=!&|]\s)\s*$', t[max(0, m.start() - 4):m.start()]) is not None)
P('alloc', r'\balloc\s*\(')
P('free', r'\bfree\s*\(')
P('let-_-free', r'let\s+_\s*=\s*free\s*\(')
P('hand-back', r'let\s+\(\s*(\w+)\s*,\s*\w+\s*\)\s*=\s*[\w.]+(\[[^\]]*\])?\s*\(\s*\1\b')
P('host', r'\bhost\s*\[\s*\w+\s*\]')
P('host-surface', r'(?<!unbang )\bhost\s*\[\s*\w+\s*\]')
P('typed-lit', r'\b(i8|i16|i32|i64|u8|u16|u32|u64|f32|f64)\[')
P('ascribed-inj', r'\(\s*(inl|inr)\b[^()]*(\([^()]*\)[^()]*)*:\s')
P('else-unit', r'else\s*\{\s*\(\s*\)\s*\}')
P('inl-inr', r'\b(inl|inr)\b')
P('match-sum', r'\bmatch\b[^{]*\{\s*inl\b')
P('unroll', r'\bunroll\b')
P('bang-closure', r'!\{')
P('next-arg', r'next_arg\s*\(\s*string_new')
P('fn-arg_i32', r'\bfn\s+arg_i32\b')
P('borrow-block', r'\bborrow\s+(mut|imm)\b')
P('borrow-block-mut', r'\bborrow\s+mut\b')
P('borrow-block-imm', r'\bborrow\s+imm\b')
P('borrow-block-life', r"\bborrow\s+(mut|imm)\s+[^{]*\{\s*'\w+\s*,")
P('let-r-lend', r'\blet\s+\w+\s*=\s*&(mut\s+)?\w+\s*;')
P('lend-mut', r'&mut\s+\w+')
P('lend-imm', r'(?<![&\w])&(?!mut\b)\w+')
P('zero-minus', r'(?<![\w.])0\s*-\s*[\w(]')
P('compound-assign', r'(?<![\w.=!<>])(\w+)\s*=\s*\1\s*[-+*/%]\s', lambda t, m: not re.search(r'\blet\s+(mut\s+)?$', t[max(0, m.start() - 12):m.start()]))
P('let-mut-rebind', r'let\s+mut\s+(\w+)\s*(:[^=]*)?=\s*\1\s*;')
P('destructure-param', r'\bfn\s+\w+[^(]*\((\w+)\s*:[^)]*\*[^)]*\)[^=]*=\s*let\s+\(\s*\w+\s*,\s*\w+\s*\)\s*=\s*\1\s*;')
P('destructure-closure', r'\{\s*(\w+)\s*->\s*let\s+\([^)]*\)\s*=\s*\1\s*;')
P('unit-pair', r',\s*\(\s*\)\s*\)')
P('type-args', r'(?<!fn )(?<!poly )\b(?!host\b|i8\b|i16\b|i32\b|i64\b|u8\b|u16\b|u32\b|u64\b|f32\b|f64\b)[a-z_]\w*\[[^\]\n]+\]\s*\(')
P('lifetime-sig', r"^(fn|poly)\s+\w+(\[[^\]]*\])?<'")
P('lifetime-sig-one', r"^(fn|poly)\s+\w+(\[[^\]]*\])?<'\w+>")
P('cbpv-type', r'\bU\s*\(')
P('stored-gen-ascribe', r':\s*U\s*\(\s*pull\b')
P('print-byte', r"\b(print_byte|putb)\s*\([^)]*b'")
P('option-default', r'\{\s*inl\s+(\w+)\s*->\s*\1\s*\|\s*inr\s+\w+\s*->')
P('on-exhausted', r'\bon_exhausted\b')
P('to_result-default', r'with\s+(default|to_result)\b')
P('cons-chain', r'\bcons\s*\([^()]*,\s*cons\s*\(')
P('to-conv', r'\bto_(i32|u8)\s*\(')
P('clone', r'\bclone\s*\(')

def count(d):
    S = {k: [(p, strip(open(p).read())) for p in v] for k, v in sets(d).items()}
    print('files:', {k: len(v) for k, v in S.items()})
    for key, rx, pred in PATTERNS:
        c, sites = {}, []
        for s, files in S.items():
            occ = nf = 0
            for p, t in files:
                k = 0
                for m in rx.finditer(t):
                    if pred and not pred(t, m): continue
                    k += 1
                    if len(sites) < 4: sites.append(site(p, t, m.start()))
                occ += k; nf += bool(k)
            c[s] = (occ, nf)
        print(f"{key:20s} {sum(o for o, _ in c.values()):5d} | " + ' '.join(f'{s} {o}/{n}f' for s, (o, n) in c.items())
              + ' | ' + ', '.join(sites))
    # host operations in user code (corpus, bench, book), outside the kernel text's `unbang host[…]`
    ops = collections.Counter()
    for s in ('corpus', 'bench', 'book'):
        for p, t in S[s]:
            ops.update(m.group(1) for m in re.finditer(r'(?<!unbang )\bhost\s*\[\s*(\w+)\s*\]', t))
    print('host ops in user code:', dict(ops.most_common()))

# ---------------------------------------------------------------- cells

USES = [('let-free', r'let\s+_\s*=\s*free\s*\(\s*{x}\s*\)'), ('borrow-mut', r'\bborrow\s+mut\s+{x}\b'),
        ('borrow-imm', r'\bborrow\s+imm\s+{x}\b'), ('modify-lend', r'modify\s+&mut\s+{x}\b'),
        ('lend-mut', r'&mut\s+{x}\b'), ('lend-imm', r'&{x}\b'), ('deref', r'\*{x}\b'), ('free', r'\bfree\s*\(\s*{x}\s*\)')]

def cells(d):
    tot, shapes, ex = collections.Counter(), collections.Counter(), collections.defaultdict(list)
    for s, fs in sets(d).items():
        for p in fs:
            t = strip(open(p).read()); ends = [m.start() for m in DECL.finditer(t)] + [len(t)]
            for m in re.finditer(r'\blet\s+(\w+)\s*=\s*alloc\s*\(', t):
                x = m.group(1); rest = t[m.end():min(e for e in ends if e > m.start())]
                uses, spans = collections.Counter(), []
                for k, rx in USES:
                    for u in re.finditer(rx.format(x=re.escape(x)), rest):
                        if any(a <= u.start() < b for a, b in spans): continue
                        spans.append((u.start(), u.end())); uses[k] += 1
                uses['moved'] += sum(1 for u in re.finditer(r'\b%s\b' % re.escape(x), rest)
                                     if not any(a <= u.start() < b for a, b in spans))
                kind = 'moved' if uses['moved'] else 'never-moved'
                key = (s, kind, '+'.join(sorted(k for k in uses if uses[k])) or '(unused)')
                tot[(s, kind)] += 1; shapes[key] += 1
                if len(ex[key]) < 3: ex[key].append(site(p, t, m.start()))
    for k in sorted(tot): print(k, tot[k])
    for k, n in sorted(shapes.items(), key=lambda kv: (kv[0][:2], -kv[1])): print(f'  {k[0]:6s} {k[1]:11s} {n:3d} {k[2]:30s} {", ".join(ex[k])}')

# ---------------------------------------------------------------- blocks

def blocks(d):
    """tail: the rest of the block's scope does not name the place (or only frees it);
    reused: it does, split by whether every mention of the borrow is at the block's top level."""
    C, ex = collections.Counter(), collections.defaultdict(list)
    for s, fs in sets(d).items():
        for p in fs:
            t = strip(open(p).read()); starts = [m.start() for m in DECL.finditer(t)] + [len(t)]
            for m in re.finditer(r"\bborrow\s+(mut|imm)\s+(\*?\w+|\"[^\"]*\"|\([^)]*\))\s*\{\s*(?:'\w+\s*,\s*)?(\w+)\s*->", t):
                k, x, v = m.groups()
                ob = t.index('{', m.start()); cb = close(t, ob) or len(t); body = t[m.end():cb]
                d0 = max(e for e in starts if e <= m.start()); d1 = min(e for e in starts if e > m.start())
                depth, opener = 0, None
                for j in range(m.start() - 1, d0 - 1, -1):
                    if t[j] == '}': depth += 1
                    elif t[j] == '{':
                        if depth == 0: opener = j; break
                        depth -= 1
                rest = t[cb + 1:(close(t, opener) if opener is not None else d1)]
                xs = re.escape(x.lstrip('*'))
                named = len(re.findall(r'\b%s\b' % xs, rest)) if re.match(r'\w', x.lstrip('*')) else 0
                frees = len(re.findall(r'\bfree\s*\(\s*%s\s*\)' % xs, rest)) if named else 0
                if named == frees: cls = 'tail'
                else:
                    nested = any(body[:u.start()].count('{') > body[:u.start()].count('}')
                                 for u in re.finditer(r'\b%s\b' % re.escape(v), body))
                    cls = 'reused-nested' if nested else 'reused-straight'
                C[(s, k, cls)] += 1
                if len(ex[(s, k, cls)]) < 3: ex[(s, k, cls)].append(site(p, t, m.start()))
                if re.fullmatch(r"\s*[\w.]+(\[[^\]]*\])?\s*\([^;{}]*\b%s\b[^;{}]*\)\s*" % re.escape(v), body):
                    C[(s, k, 'one-call')] += 1
    for key in sorted(C): print(f'{key[0]:6s} {key[1]:3s} {key[2]:16s} {C[key]:4d}  {", ".join(ex.get(key, []))}')

# ---------------------------------------------------------------- rewrite

def rw_else_unit(src):
    """`if c { S } else { () }` as `if c { S }`."""
    for m in re.finditer(r'\s*else\s*\{\s*\(\s*\)\s*\}', src): yield m.start(), m.end(), ''

def rw_free_unit(src):
    """`let _ = free(c);` removed: the cell is dropped at the end of its scope (SPEC §12)."""
    for m in re.finditer(r'\n[ \t]*let\s+_\s*=\s*free\s*\(\s*\w+\s*\)\s*;', src): yield m.start(), m.end(), ''

def rw_inj_ascribe(src):
    """`(inl e : A + B)` as `(inl e)`."""
    for m in re.finditer(r'\((?=\s*(inl|inr)\b)', src):
        j = close(src, m.start())
        if j is None: continue
        inner = src[m.start() + 1:j]; cs = [k for k in top_level(inner, ':') if inner[k - 1:k] == ' ']
        if cs: yield m.start(), j + 1, '(' + inner[:cs[-1]].strip() + ')'

def rw_typed_lit(src):
    """`i64[5]`, `u8[200]`, `i32[7]` as `5`, `200`, `7`."""
    for m in re.finditer(r'\b(i32|i64|u8)\[(\d+)\]', src): yield m.start(), m.end(), m.group(2)

def rw_hand_back(src):
    """`let (x, r) = f(…, x, …)` as `let r = f(…, &mut x, …)` (SPEC §11's lend)."""
    for m in re.finditer(r'let\s+\(\s*(\w+)\s*,\s*(\w+)\s*\)\s*=\s*([\w.]+(?:\[[^\]\n]*\])?)\s*\(', src):
        x, r = m.group(1), m.group(2); j = close(src, m.end() - 1)
        if j is None: continue
        args = src[m.end():j]; cuts = [-1] + top_level(args, ',') + [len(args)]
        parts = [args[cuts[k] + 1:cuts[k + 1]] for k in range(len(cuts) - 1)]
        hits = [k for k, a in enumerate(parts) if a.strip() == x]
        if len(hits) != 1 or len(re.findall(r'\b%s\b' % re.escape(x), args)) != 1: continue
        parts[hits[0]] = parts[hits[0]].replace(x, '&mut ' + x)
        yield m.start(), j + 1, f'let {r} = {m.group(3)}(' + ','.join(parts) + ')'

def rw_one_call_block(src):
    """`borrow k x { ['l,] v -> f(…, v, …) }` as `f(…, &x, …)` (`&mut x` at `mut`)."""
    for m in re.finditer(r"\bborrow\s+(mut|imm)\s+(\w+)\s*\{\s*(?:'\w+\s*,\s*)?(\w+)\s*->\s*", src):
        k, X, v = m.groups(); j = close(src, src.index('{', m.start())); body = src[m.end():j].strip()
        mm = re.fullmatch(r'([\w.]+(?:\[[^\]]*\])?)\s*\((.*)\)', body, re.S)
        if not mm or close(body, body.index('(')) != len(body) - 1: continue
        args = mm.group(2)
        if len(re.findall(r'\b%s\b' % re.escape(v), args)) != 1: continue
        cuts = [-1] + top_level(args, ',') + [len(args)]
        parts = [args[cuts[q] + 1:cuts[q + 1]] for q in range(len(cuts) - 1)]
        hit = [q for q, a in enumerate(parts) if a.strip() == v]
        if len(hit) != 1: continue
        parts[hit[0]] = parts[hit[0]].replace(v, ('&mut ' if k == 'mut' else '&') + X)
        yield m.start(), j + 1, mm.group(1) + '(' + ','.join(parts) + ')'

def rw_cell_to_local(src):
    """`let c = alloc(e)` whose `c` is never moved as `let mut c = e`: `free(c)` and `*c` read as
    `c`, `let _ = free(c);` removed; lends and borrow blocks of `c` left as written."""
    ends = [m.start() for m in DECL.finditer(src)] + [len(src)]
    for m in re.finditer(r'\blet\s+(\w+)\s*=\s*alloc\s*\(', src):
        x = m.group(1); X = re.escape(x); j = close(src, m.end() - 1); end = min(e for e in ends if e > m.start())
        rest = src[j + 1:end]
        known = (r'let\s+_\s*=\s*free\s*\(\s*X\s*\)\s*;|\bfree\s*\(\s*X\s*\)|\bborrow\s+(mut|imm)\s+X\b|'
                 r'modify\s+&mut\s+X\b|&mut\s+X\b|&X\b|\*X\b').replace('X', X)
        if re.search(r'\b%s\b' % X, re.sub(r'--[^\n]*', '', re.sub(known, '', rest))): continue
        new = re.sub(r'\n[ \t]*let\s+_\s*=\s*free\s*\(\s*X\s*\)\s*;'.replace('X', X), '', rest)
        new = re.sub(r'\bfree\s*\(\s*X\s*\)'.replace('X', X), x, new)
        new = re.sub(r'(?<![\w)\]])\*X\b'.replace('X', X), x, new)
        yield 0, len(src), src[:m.start()] + f'let mut {x} = ' + src[m.end():j] + new + src[end:], src.count('\n', 0, m.start()) + 1

def rw_extend_tail(src):
    """`let p = borrow k x { ['l,] m -> S; e }; R`, R the rest of the scope and not naming x, as
    `borrow k x { ['l,] m -> S; let p = e; R }`: what `let m = &mut x` to the end of the scope gives."""
    for m in re.finditer(r"(let\s+(\([^)]*\)|\w+)\s*=\s*)?\bborrow\s+(mut|imm)\s+(\w+)\s*\{(\s*(?:'\w+\s*,\s*)?\w+\s*->)", src):
        bind, pat, k, x, head = m.groups()
        ob = src.index('{', m.start() + (len(bind) if bind else 0)); cb = close(src, ob)
        if cb is None: continue
        dm = DECL.search(src, cb); lim = dm.start() if dm else len(src); dd, end = 0, lim
        for j in range(cb + 1, lim):
            if src[j] in '{([': dd += 1
            elif src[j] in '})]':
                if dd == 0: end = j; break
                dd -= 1
        after = src[cb + 1:end]
        if not after.lstrip().startswith(';'): continue
        X = re.escape(x)
        rest = re.sub(r'\n?[ \t]*let\s+_\s*=\s*free\s*\(\s*X\s*\)\s*;'.replace('X', X), '', after.lstrip()[1:])
        code = re.sub(r'--[^\n]*', '', rest)
        if re.search(r'\b%s\b' % X, code) or not code.strip(): continue
        body = src[m.end():cb]; cuts = top_level(body, ';')
        stmts, last = (body[:cuts[-1] + 1], body[cuts[-1] + 1:]) if cuts else ('', body)
        inner = f'{stmts} let {pat} = {last.strip()}; {rest.strip()}' if bind else f'{stmts} {last.strip()}; {rest.strip()}'
        yield 0, len(src), src[:m.start()] + f'borrow {k} {x} {{{head} {inner} }}\n' + src[end:], src.count('\n', 0, m.start()) + 1

BCC = os.environ.get('BCC', os.path.expanduser('~/repos/borrow-core-l2b-base/.lake/build/bin/bcc'))
ENV = dict(os.environ, BCC_LIB=os.path.abspath('lib'))
NAMES = re.compile(r'(io_[a-z]+?)\d+(?:_\d+)+')      # generated names carry a source position

def run(cmd, stdin=None, timeout=300):
    try:
        p = subprocess.run(cmd, stdin=stdin, capture_output=True, text=True, timeout=timeout, env=ENV)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return None, 'timeout'

def core(path):
    rc, out = run([BCC, 'desugar', path])
    return NAMES.sub(r'\1#', out) if rc == 0 else None

def output(path, orig):
    stdin = open(orig[:-3] + '.in') if os.path.exists(orig[:-3] + '.in') else subprocess.DEVNULL
    return run([BCC, 'run', path], stdin=stdin, timeout=120)

ORIG = {}
def test(job):
    path, var, where = job
    rc, msg = run([BCC, 'check', var])
    if rc != 0: return where, 'refused', msg.strip().split('\n')[-1].split('.bc:', 1)[-1]
    if path not in ORIG: ORIG[path] = (core(path), output(path, path))
    oc, oo = ORIG[path]
    same_core = oc is not None and core(var) == oc
    vo = output(var, path)
    return where, 'accepted', ('same-core ' if same_core else '') + ('same-run' if vo == oo and oo[0] is not None else 'RUN-DIFFERS')

def rewrite(d, names):
    files = corpus_files() + sorted(glob.glob('bench/*/*.bc'))
    for name in names:
        fn = globals()['rw_' + name]; vdir = os.path.join(d, 'var', name); os.makedirs(vdir, exist_ok=True); jobs = []
        for path in files:
            src = open(path).read(); code = strip(src)
            lead = lambda e: e[0] + len(src[e[0]:e[1]]) - len(src[e[0]:e[1]].lstrip())
            for k, e in enumerate(e for e in fn(src) if len(e) == 4 or code[lead(e)] != ' '):
                a, b, rep = e[:3]
                var = os.path.join(vdir, path.replace('/', '_')[:-3] + f'-{k}.bc'); open(var, 'w').write(src[:a] + rep + src[b:])
                line = e[3] if len(e) == 4 else src.count('\n', 0, a + len(src[a:b]) - len(src[a:b].lstrip())) + 1
                jobs.append((path, var, f'{path}:{line}'))
        with cf.ThreadPoolExecutor(8) as ex: res = list(ex.map(test, jobs))
        with open(os.path.join(d, f'rw-{name}.txt'), 'w') as f:
            for r in res: f.write(' | '.join(r) + '\n')
        acc = [r for r in res if r[1] == 'accepted']
        print(f"{name}: sites {len(res)}, accepted {len(acc)}, same core {sum('same-core' in r[2] for r in acc)}, "
              f"same run {sum('same-run' in r[2] for r in acc)}, run differs {sum('RUN-DIFFERS' in r[2] for r in acc)}")

if __name__ == '__main__':
    cmd, d = sys.argv[1], sys.argv[2]
    {'book': book, 'count': count, 'cells': cells, 'blocks': blocks}.get(cmd, lambda d: rewrite(d, sys.argv[3:]))(d)
```

</details>
