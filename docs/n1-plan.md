# N1: the new backend's pure fragment (#636)

The plan for unit N1 of `docs/compiler.md` §6.1: a backend that compiles the checked typed term
(`Checked.t : TExpr`), not its erasure. The old backend (`Backend/`) stays `bcc`'s default and is
the differential oracle until N6 (§4.2).

## The fragment

The programs whose typed term has no effect node: no `effPerform`, `effRaise`, `effHandle*`,
`effThen`, `effLet`, `effSub`, `lendR`, `lendLoopR`, `nilDead`, `…U` borrow, `iterate`,
`divFuel` or `reify`. The census (`scripts/kernel-census.sh`) finds 220 such programs of the 375
checked, all with goldens; I/O programs (capabilities as values) and codata (`unfold`) are among
them. Programs with effects go through the old backend, and N2 extends the fragment.

Some acceptance programs (Towers, `richards_mu`, binary-trees, quicksort's bench) raise
`Exhausted` or `Fail`, so they are outside the fragment. Each acceptance item is measured on the
fragment's programs, or on an effect-free reproduction, and the named programs are re-measured
when N2 lands.

## The LIR as built

`Backend2/` (name provisional). One typed IR between the typed term and the targets:

- **Types** (`Backend2/Types.lean`): `LTy`, a value type with lifetimes, `[@a]` and `!` erased:
  `1`, `0`, integers at their width, `⊗`, `⊕`, `μ`/type variables, `Ref A`, `Imm A`, `Mut A`, a
  family `[L]`, an opaque host type, and a closure `U K` of a computation type `K` (`F A`,
  `A ⊸ K`, `K & K`, `⊤`, `∀` as a unit argument, `ν`). Persistence is `VTy.persistent`'s.
- **Terms** (`Backend2/Syntax.lean`): named A-normal form. Every variable has its `LTy`. Closures
  are `clos c env` of codes (a `&`'s two components share one environment, one code each);
  calls, primitives, `case`, `letpair`, structured loops for `count_fold` and `count_try`, and
  explicit `copy` and `drop`. Every variable is consumed exactly once on every path.
- **Machine form**: the layout stage lowers LIR to the existing target-neutral word IR
  (`Backend/Flat/Syntax.lean`), so the Wasm and LLVM emitters (`Backend/Wasm/Lower.lean`,
  `Backend/Native/Lower.lean`) are shared with the old backend until N6. They are made
  independent of `Backend/Clos` (their two helpers move to a shared module) so the fence holds.

## Stages, and what each reads from `TExpr`

| stage | module | reads from the typed term |
|---|---|---|
| specialise | `Convert` | `use` nodes: one LIR body per key (declaration, type arguments, `TInfo.key`), shared by every use; a body whose free variables reach past the externs is compiled at its use |
| closure conversion | `Convert` | binder types and judgments (every variable's `LTy`); the split masks `u` at `tensorI`, `bind`, `app`, `unitE`, `tensorE`, `sumE`, `zeroE`, `lolliE`: a slot both parts use is copied, a live slot neither uses is dropped, every other is moved; `dtor A` as the drop of `A` |
| derived nodes | `Convert` | `selfCall` (a direct call of the group member), `litFn` (the literal's bytes), `divLit` (no error arm), `walk` (the index bound: no bounds check), `foldOwn`/`foldReuse`/`foldImm` (`F`, `R`), `unfoldN` (`C`, `S`), `arrReplace`/`sliceReplaceM`/`sliceSwapM` (a slot swap), `allocS`/`freeS`/`withborSM` (a block as one object), `lendCell` |
| constants | `Convert` | each constant node's type arguments: the primitive's layout |
| lint | `Lint` | verifies: every variable typed and consumed once, every node's type agreeing with its children's |
| interpreter | `Interp` | runs LIR against the goldens (`live 0`, unwritten reads, use after consume) |
| flow | `Flow` | the 0-CFA, run once on LIR: the codes each call reaches (a direct call where one does), and the closure classes (the components of its flow graph), which give closures their layout |
| layout | `Layout` | `LTy` and the classes: `i32` slots of 4 bytes, one box a node for `μ` (SPEC §35), a closure class's tag and widest environment |
| lowering | `Lower` | LIR to the word IR: copies and drops as LIR placed them, each deep copy counted under `copies` |
| targets | shared | Wasm and LLVM from the word IR |

## The gate

- `bcc compile --backend new` (and `run`, `interp --stage lir|lflat`) select the new backend.
- A step compiles every program of the fragment with the new backend at the LIR interpreter, the
  word IR and Wasm (and natively where there is a C compiler) and compares each with its golden;
  its counts are compared with the old backend's, which they may not exceed (`allocs`,
  `indirect`, `copies`).
- **The fence** (`scripts/check-backend2.sh`): `Backend2/` imports only the typed term, the
  checker's `Checked`, Core's types and the shared word IR and emitters; never `Frontend.Elab`,
  `Frontend.Sugar`, `Backend.Clos`, `Backend.Flat.Lower`.
- **The ban list**: no `TExpr.erase`, no match on `BoCa.Expr`'s constructors, none of the names
  §3.6 deletes (`isSwap`, `travShape?`, `fixBody?`, `litTable?`, `plan2`, `markScoped`, `polyLet`,
  unification).
- **The census**: a column of the TExpr constructors and facts the new backend reads, written by
  the backend itself on each run.

## Order

1. Shared emitters made independent of `Backend/Clos`; `Backend2` skeleton: types, syntax.
2. Conversion of the CBPV core and the integer constants; LIR printer and interpreter; first
   programs at their goldens through the interpreter.
3. Constants: cells and borrows, arrays and slices, counted loops, folds, codata, I/O externs.
4. Flow, layouts, lowering to the word IR; Wasm and LLVM.
5. The gate step, the fence, the ban list, the lint, the census column.
6. Acceptance items, in this order: NEW-c (#608, the slot swap), copies counted, L-6 (`i32`
   slots), L-3 (`walk`), `divLit`, #509 (one printer), U1's blocks as one object, NEW-b (the
   budget's stack-pointer compare, on the fragment's `bounded_fix`, or reported with N2).

## Kill criteria (§5.4)

- A stage needs a fact neither on the typed term nor the 0-CFA's: added to the typed term, not
  recovered (criterion 3).
- Any output, golden, exit status or `live 0` differs (criterion 4).
- A count of `counts.expected` rises on the fragment (criterion 6, applied early).

## As built

What the build changed from the plan above, and where each acceptance item stands.

- **Closure classes.** The plan's 0-CFA gives direct calls; it does not give closures their
  layout, since every place a value moves to must share its representation. The layout stage
  joins the places a value moves between (`Backend2/Layout.lean`, `join`): a closure place's
  class is the codes that reach it, with one argument and answer layout. No type is inferred: each
  node's former is read from the variable's `LTy`. The 0-CFA (`Backend2/Flow.lean`) runs once,
  after the layouts, for the calls.
- **Specialisation.** A `use` body is converted once per key; a body that takes a closure is
  converted at each use, as the old backend's substitution did, so its closures' classes stay each
  use's (the key with the argument codes of `docs/compiler.md` §3.1 is #541's).
- **Two passes over the LIR's ownership**, each reading an owner's one consumer: frame slots for
  `lendCell`'s cell (`Backend2/Frames.lean`) and literal views (`Backend2/LitViews.lean`).
- **The word IR** is the old backend's (`Backend/Flat/Syntax.lean`), with `load32`/`store32`.

| item | status |
|---|---|
| every effect-free corpus program at its golden, Wasm and native | met: 222 programs (`scripts/compile-backend2.sh`) |
| #509's reproduction compiles once | met: 21 calls of `print_f64`, 419 Wasm functions (old: 38706) |
| copies, moves and drops from the masks; `arrReplace`/`sliceReplaceM`/`sliceSwapM` a slot swap (#608) | met; the reproduction without recursion allocates 5 (old: 45). Towers and `richards_mu` raise `Exhausted` and `Fail`: outside the fragment (N2) |
| L-3: no bounds check at a walk's read | not met: the typed term does not say which read is the walk's (SPEC §43 *Open*) |
| L-6: 4-byte `i32` slots | met: a cell class of `i32`s or `f32`s (`load32`/`store32`) |
| NEW-b: the budget as a stack-pointer compare | not met: every `bounded_fix` program raises `Exhausted` (N2), and the compare changes when a budget is spent, which SPEC §20 fixes as a count |
| `divLit`: no error arm | met |
| every generated deep copy counted | met: an LIR copy at a heap type, and a read through `Imm̲` that copies |
| the census: N1's class-B rows class A | met for the fragment (`docs/kernel-usage.md` §1); `selfCall`, `effLet`'s rows and `C.top` are effectful (N2) |
| U1's block as one object | not met: a block's cells are freed one by one (SPEC §43 *Open*) |

## Part 2

The decisions recorded on #636 after part 1: a type-erasure rule for `Λ`, the codata derived node
pulled forward from N4, and the walk's typed fact (L-3). SPEC §44–§46.

| item | status |
|---|---|
| `Λ` erased by a proved rule (§44) | met: `allI_inst` (one β at every memory to the body's λ-value); `∀'x. C` is `C` in the LIR's types; no `∀` type in any program's LIR. Counts unchanged (the instantiations were direct calls) |
| codata's η-thunk as a derived node (§45) | met: `nuEta`, built by the checker at `thunkv`; `nuEta_obs`, `nuEta_var`, `nuEta_unfold`; at `f = unfold step` the call `f s` is made where the thunk is built. Every program's `indirect` at most the old backend's: 37 in all, equal on all 222 (part 1: 2024917). Two programs' rise was literal tables, now one code over the literal's offset and length |
| L-3: the walk's read (§46) | met: `walk`'s `read` (`walkReadB`), the marked read `walkGet`; the 33 programs of the fragment with a walk have no test at the walk's read. The step's tails handing the view on is fixed of the term, not proved of the runs (§46 *Open*) |
| NEW-b | not in reach: every `bounded_fix` program has an effect node, outside the fragment; counts are gated on Wasm |
| U1's block as one object | deferred (decision on #636) |

**The run-time gap.** The part-1 report attributed `parse` and `wordcount`'s gap to the
instantiation thunks. Erasing them changed neither time: LLVM had inlined them. The cause was the
generated counted loops' index, tested and stepped by the 32-bit host operations with their
truncations, which kept LLVM from relating the loop's test to the reads' tests. As words
(`cntLt`, `cntSucc`, §46) the two run at:

| bench | old | new | Rust | new / Rust | old / Rust |
|---|---|---|---|---|---|
| parse | 153 ms | 153 ms | 127 ms | 1.20× | 1.20× |
| wordcount | 127 ms | 132 ms | 104 ms | 1.27× | 1.22× |

(native, median of 11, interleaved). The tests LLVM removes once the loop's test is a word compare
are LLVM's: no annotation forces them.
