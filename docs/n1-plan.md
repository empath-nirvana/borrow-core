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
