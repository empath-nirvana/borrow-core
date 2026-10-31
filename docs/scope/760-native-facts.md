# #760: native facts from the kernel

Scope for #760, written before any code and read at `origin/main` 32bbf65d. Backend only: no
change to Core, `CDerives`, the checker or the language. Section 8 records the review.

**Kernel target.** None new. Each annotation emitted cites an existing Lean declaration on main, or
a named compiler assumption listed by `bcc trusted`. A candidate with neither is not emitted.

**Policy** (user, 2026-10-31, with the refinement of the same day):

- An LLVM annotation either **forces** an optimisation (LLVM must do it, or reject the module) or
  is **informational** (LLVM may use it). Only `musttail` and `alwaysinline` force anything today.
- An optimisation we need is done in our own compiler first, or forced by an annotation second.
  `llvm.loop.vectorize.enable` with `llvm.loop.parallel_accesses` is a hint, not forcing.
- For now we may rely on LLVM usually optimising from an informational annotation. Each such
  reliance is an **improvement candidate**: something to move into our compiler, or force, where
  gains remain. SPEC words it as "informational, relied on for now, improvement candidate".
- A false annotation is undefined behaviour, so soundness comes first. Below, every row puts the
  LangRef text (LLVM 21.x, `llvm/docs/LangRef.rst`, the release that matches the toolchain's
  `clang` 21) next to the fact that licenses it.

## 0. What is emitted today (SPEC §50, `Backend/Native/Lower.lean`, `Backend2/Lower.lean`)

| emitted | where | cited |
|---|---|---|
| `noalias nonnull dereferenceable(b)` | a `mut` borrow parameter word of a cell with words | `CellU.CompatS.kinds`, `adequacyD` (`citeMut`) |
| `noalias readonly nonnull dereferenceable(b)` | an `imm` borrow parameter word | `CellU.CompatS`, `adequacyD` (`citeImm`) |
| `noalias` (`readonly` at `imm` leaves) | a borrowed family's base | as above (`citeFam`) |
| `musttail` | every tail call | forcing; the verifier rejects a call it cannot honour |
| `alwaysinline` | `Fn.inline` (a call point's step) | forcing; `native-facts.sh` checks that no call is left |
| `nounwind` | **every** function and `bc_entry` | **uncited** (section 2, row N) |
| `"frame-pointer"="all"` | every function | not a fact: a profiling choice (#664) |

`nounwind` is emitted today with no citation. Row N below gives it one: a named compiler
assumption. It is not a kernel fact.

**A soundness finding in what main emits (section 3a: STOP for the coordinator).** The borrow
facts in the first two rows depend on a bridge: that a borrow parameter's lend is live, and its
owner unreachable, for the whole execution of the LIR function. That bridge is true where an LIR
function is a source function. It is false at the machine conversion's step functions. A
`cancel` step takes a `mut` borrow and its owner as two parameters of one function, writes
through the borrow, and frees the cell through the owner, so its `noalias` and `dereferenceable`
are violated. The citations are also incomplete (section 3a, M1).

## 1. Termination: is "a Div-free computation terminates" a kernel theorem?

**Yes, at the semantic level, and per call. Each statement below is a short corollary of
`fundamentalC` and the run lemmas on main. Each was elaborated against main's built `Core`
(`lake env lean` on a scratch file importing `Core.Totality`; `#print axioms` ⊆ `[propext,
Classical.choice, Quot.sound]`; no `sorry`). None is in the tree yet: adding them is a kernel
change, made in its own unit.** What remains for `willreturn` is the bridge to the native call, not
termination.

- **Closed programs (on main).** `Core/Totality.lean`, at `CDerives LifeCtx.empty [] e (.comp
  (.ret A))`:
  - `total_every_alloc`: under every allocator, from every count, the run reaches a value;
  - `total_run_prefix` and `total_every_run`: every run continues to a value;
  - `total_no_infinite_run`: there is no infinite run.

  `.ret A` carries no row (`CTy.eff` stacks over it), so this is the empty row. A program whose
  `main` loops is covered one prefix at a time (`externs_loop_every_run`, at `ioLoopE N bs n`).
- **`total_open` (elaborated; `fundamentalC` and then `total_every_alloc`'s unpacking).**
  Statement:

  ```lean
  theorem total_open {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {B : VTy}
      (h : CDerives Δ Γ e (.comp (.ret B)))
      {δ : LSub} {γ : List Val} {ls : List SRec} {ρ ρf fρ : WRes} {ps : List FrameRec} {μ : Heap}
      (hδ : Δ.Models δ) (hγ : gDenC ls δ Γ γ ρ)
      (h1 : ResU.Hash ρf ρ) (h2 : ResU.CompS ρf ρ fρ) (h3 : TW fρ ps (rsOf ls))
      (h4 : Tagged fρ ps ls) (hμ : ResU.Lower fρ μ) (Al : Alloc) (k : Nat) :
      ∃ (k' : Nat) (μ' : Heap) (v : Val), ARun (ℍ := ℍ) Al k μ (substAll γ e) k' μ' (.val v)
  ```

  Proof: `fundamentalC h δ γ ls ρ hδ hγ` is `wpTS`, which is instantiated at the frame
  `ρf, fρ, ps` and `Al k`. Its `Lower fρ μ₀` is identified with `hμ` by `ResU.Lower.functional`.
  The `ARun` conjunct is then the answer. It takes six lines.

  **`total_call`** is the instance `Γ = [⟨A, true⟩]`, `γ = [x]`: a computation of `F B` at the
  empty row over one argument `x` in the relation at `A`. That includes the call `f x` of a closed
  `f : U(A ⊸ F B)`. From a memory that lowers a tagged typed world modelling `x`, it returns
  under every allocator. The empty row is essential, not only the absence of `Div`. A Div-free
  row with an operation `op` is erased into a call of `op`'s clause, inside the function's native
  invocation (resume once is a call, SPEC §47), and that clause runs at its handler's outer row,
  which may hold `Div`.
- **`total_subrun` (elaborated; `total_every_run` and `steps_plug_inv`).** Statement:

  ```lean
  theorem total_subrun {e : Expr} {A : VTy} (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
      {μ₁ : Heap} (K : Kont) (hK : K.Plain = true) {a : Expr}
      (hs : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K.plug a)) :
      ∃ (μm : Heap) (v : Val), Steps (ℍ := ℍ) μ₁ a μm (.val v)
  ```

  Every redex a closed Div-free program reaches in a plain context runs to a value. This is
  "every call returns" for the run itself, with no relation premise to discharge. The proof is
  three lines: `total_every_run` from the reached configuration, then `steps_plug_inv`
  (`Core/Steps.lean`) to split off `a`'s run.

**What is left between these and `willreturn`.** It is not termination. `willreturn` is about every
native invocation, so these steps remain:

1. **From a native call to a kernel configuration (not derived; the exact step).** `total_call`
   needs its relation premises (`hγ`, `TW`, `Tagged`, `Lower`) at the call. Nothing on main says
   that a configuration reached mid-run satisfies them. The relation is compositional inside
   `fundamentalC`'s proof, not as a statement about reached configurations. `total_subrun` avoids
   the premises, but only:
   - for a **closed Div-free** program;
   - at a **plain** context `K`. A call under a `handle` or a catch frame is not covered. Covering
     it needs `steps_plug_inv` at a non-plain `K` for an `a` that performs and raises nothing,
     which would come from preservation at the empty row. That is not on main.

   For a program whose `main` loops, the kernel covers each finite observation `ioLoopE N bs n`.
   An observation is closed over the externs (`ExternsMeet`), not over `[]`. So it needs
   `total_subrun` at an extern closing substitution, from `fundamentalC` with `gDenC_of_meets`
   in place of `gDenC_nil`, as `externs_loop_every_run` uses. It also needs the backend
   correspondence that a native run up to a call is a prefix of the run of `ioLoopE N bs n` for
   some `n`. A call at the empty row consumes no fuel (it performs no `tick`), so the call returns
   within that observation. The correspondence is the LIR's faithfulness, which is unproved,
   tested, and the same assumption every native fact rests on.
2. **The row in the LIR.** `Backend2.Fn` and `LCTy` carry no row. A per-function "empty row" bit
   is needed from the source function, through the machine conversion. A function at the empty
   row becomes no machine, but it may be called from one.
3. **`HostReturns` (named compiler assumption).** It covers four things outside the model:
   - `bc_alloc` aborts when `malloc` fails;
   - `bc_getc`/`bc_getv` block in `read(2)`, and `bc_sleep` sleeps (capabilities are `mut`
     arguments, so an empty-row function can reach them);
   - the machine stack is finite;
   - the `trap` blocks are unreachable only by `adequacyD` together with the lowering's
     faithfulness.

   Or the rule excludes every function that reaches an extern, an allocation or unbounded
   recursion.

**Decision.** `willreturn` is still not emitted in this unit. The termination fact exists, as
`total_open`/`total_call`/`total_subrun`. Steps 1–3 are the work, and step 1 is the only one that
asks for kernel statements: the non-plain context split and the extern-closed `total_subrun`.
`mustprogress` is implied by `willreturn` ("Note that ``willreturn`` implies ``mustprogress``").
On its own it is wrong for a `Div` function, because a `Div` loop may run forever without I/O.
`fuel_total` (`Core/DivFuel.lean`) is a termination result for a fuelled loop at `ewpTS`, and is
not needed here. **For the user:** whether to land the three corollaries now (they are cheap), and
whether `willreturn`'s informational gain is worth steps 1–3.

## 2. The candidates

Columns: LangRef's definition; the licence; where the backend reads it; forcing or informational;
Wasm impact; the test; and whether it is an improvement candidate, with any gain measured
(section 7).

| # | annotation | LangRef (quoted) | licence | read from | kind | Wasm | test | decision (improvement candidate: section 7) |
|---|---|---|---|---|---|---|---|---|
| A | `memory(none)` / `memory(argmem: read)` | "`memory(none)`: Does not access any memory." / "`argmem`: … accesses that are based on pointer arguments"; "`read`: … Writing to the location is immediate undefined behavior." | **none today.** The row does not track allocation (alloc is not yet an effect), and every allocating function writes `bc_alloc`'s globals and arena. Capabilities are `mut` arguments, not row entries. | n/a | informational | none | n/a | **not emitted.** Licence would be: an allocation effect in the row (the decided alloc-is-an-effect direction) and the function's parameter types (no `mut`, no capability), read off `LTy`. Recorded as a candidate behind alloc-as-effect. |
| B | `willreturn` (+`mustprogress`) | "a call of this function will either exhibit undefined behavior or comes back …" | termination: `total_open`/`total_call`/`total_subrun`, **elaborated, not yet in the tree** (section 1); the bridge from a native call to their premises is **not derived** (section 1, step 1), and `HostReturns` is needed | would be an empty-row bit per LIR function (not carried) | informational | none | n/a | **not emitted** (section 1, steps 1–3). |
| N | `nounwind` (already emitted) | "the function never raises an exception. … functions marked nounwind may still trap" | **named compiler assumption `NoUnwind`**: the emitted IR has no `invoke`, `landingpad` or `resume`; errors and cancels are branches (SPEC §47, and the erasure count `corpus/erasure-backend2.expected` shows no `handle`/`perform` left); every extern is a C function of `Backend/Native/Runtime.lean`, and C does not unwind. `abort` and `llvm.trap` are traps, which LangRef permits. The runtime
runs the entry on a pthread and never calls `pthread_cancel`, so the forced unwinding at a
cancellation point (`read`, `write`, `nanosleep`) does not arise. That is part of `NoUnwind`. | the emitter (no unwinding instruction exists in `Backend/Native/Lower.lean`), and the runtime's source | informational | none | a grep of the emitted IR for `invoke`/`landingpad`/`resume` (none), in `native-facts.sh` | **keep; cite it** above each definition, and list `NoUnwind` in `bcc trusted`. |
| C | `captures(none)` on a borrow argument | "`provenance`: The ability to access the pointer for both read and write after the function returns." "`captures(none)`: Pointer not captured." | **none today** (section 4) | the parameter's lifetime is needed, and `LTy` erases lifetimes | informational | none | n/a | **not emitted.** Section 4 gives the rule and what it needs. |
| P | `llvm.loop.parallel_accesses` + `llvm.loop.vectorize.enable` | "If there is a loop-carried dependency, the behavior is undefined." / `vectorize.enable` "selectively enables … vectorization" (a hint) | for disjoint leaves of a `mut` family: `ResU.CompatS` disjointness (`ResU.CompatS.disjoint_of_immFree`) at the family's split; for `imm` leaves no write exists | would be the walk mark (`TExpr.walk`, `Convert.lean` `walkRead`) | **informational (hint)** | none | n/a | **not emitted here.** The vectorised loop of #537 is a candidate for our own lowering (section 6). Emitting `parallel_accesses` alone would also need a proof that the step's every access is to the current leaf, which `walk_index_lt` does not state. |
| S | `!noalias` / `!alias.scope` | "If accesses from different collections alias, the behavior is undefined." | the same as the parameter facts (`CellU.CompatS.kinds`, `CellU.CompatS`), at the scope of a call that `alwaysinline` inlines | `Fn.inline` and each parameter's `LTy` | informational | none | the differential run | **not emitted in this unit.** LLVM already turns `noalias` parameters into scopes when it inlines ("noalias function parameters are turned into noalias scope metadata"), so a scope we emit is only worth it where a parameter attribute is too coarse (SPEC §50 *Open*, #531). That needs a measured case first. Candidate. |
| I | `!invariant.load` through an `imm` borrow | "the memory location referenced by the load has to contain the same value **at all points in the program** where the memory location is dereferenceable" | **none.** `CellU.CompatS` holds the value fixed only while the `imm` lend is live. The owner writes the cell before the lend and after it, and the cell stays dereferenceable throughout. | n/a | informational | none | n/a | **dropped: no licence.** A program in which this rule would be wrong: `put r 1; withbor r (λb. *b); put r 2; withbor r (λb. *b)`. Both loads are through an `imm` borrow of one cell, at two values. The scoped form is `llvm.invariant.start`/`end` at the lend, and that is visible only in the lending function. Not a candidate until a case needs it. |
| R | `!range [0,2)` on a sum's tag load | "If the loaded … value is not in the specified range, a poison value is returned instead." | `adequacyD` (a `case` is never stuck, so the scrutinee is an `inj`), **plus** a layout fact: `mkInj` writes `0`/`1` at a sum's tag word (`Backend2/Lower.lean`), and every other write of a cell copies a whole value of the same node. That second fact is a compiler fact that is not proved (`LayoutCheck` is a checker, #674). | the layout node of the cell's contents (`L.sh`), its tag word | informational | none | the differential run | **not emitted.** Licensable only with a named assumption `LayoutTags` in `bcc trusted`. The LIR already tests a tag with one `eqz` (`ite`) and gives a `switch` a trapping default, so the gain is expected to be nil. Not a candidate. |
| U | `noundef` on parameter words | "If the value representation contains any undefined or poison bits, the behavior is undefined." | **none today.** A class's padded parameters are passed `poison` (`bc_entry`, and `classArity` widens a function's prototype to its tail-call class). A cell from `bc_alloc` is `malloc` memory, and whether every word of a cell (a narrower arm's padding) is written before it is read is not established. | n/a | informational | none | n/a | **not emitted.** Borrow words already have it: `dereferenceable(b)` "implies `noundef`". |
| W | `llvm.assume(i < n)` for a walk's read | "allows the optimizer to assume that the provided condition is true" | `walk_index_lt`, `walk_get_leaf` | the walk mark (`Convert.lean`, `walkRead`, `inRange`) | informational | none | n/a | **dropped: already done in our own compiler** (SPEC §46): a walk's read is converted with no test. That is the preferred form, and an `assume` on top would add an instruction that LLVM's passes have to carry. |
| O | an owned cell parameter (`Ref`): `noalias nonnull` | `noalias` as row S's parameter form; `nonnull`: "if the parameter … is null, poison … is passed instead" | **none that holds at the LIR.** The premise "while the owner is held no lend of it is live" holds for a source function, but not for the machine conversion's `suspend`, `resume entry` and `cancel` steps. Each takes the owner and its live borrow as two parameters (`async-r1-cancel-finaliser-writes.bc` `@f12`, section 3a). `nonnull` is also false for a cell of no words: its address is `0` (SPEC §35 `zeroCell`, `Backend2/Lower.lean` `.alloc`: `b == 0` gives `.c64 0`). | the parameter's `LTy` (`.ref`), never its layout node | informational | none | n/a | **not emitted** (review F2, F3). It would need section 3a's bridge, restricted to functions that are not machine steps, and a guard on cells with words, as `paramFacts`' `cellBytes` guards borrows. It would never get `dereferenceable`: the function may free the cell (`bc_free` returns a large object to `malloc`), and LangRef 21 does not restrict `dereferenceable` to function entry. |

Sources for row O: `withbor` lends an owner and hands it back after the callback (SPEC §12); the
LIR's `free` takes the owner (`Backend2/Syntax.lean`).

## 3. The `imm` copied twice (#756): two `readonly noalias` arguments to one cell

**At a source call, sound under LangRef's definition. At a machine step that ends the lend, the
premise fails: see section 3a.** LangRef, `noalias`:

> This indicates that memory locations accessed via pointer values based on the argument or return
> value are not also accessed, during the execution of the function, via pointer values not
> *based* on the argument or return value. **This guarantee only holds for memory locations that
> are *modified*, by any means, during the execution of the function.** If there are other
> accesses not based on the argument or return value, the behavior is undefined.

and `readonly`:

> This attribute indicates that the function does not write through this pointer argument, even
> though it may write to the memory that the pointer points to. If a function writes to a readonly
> pointer argument, the behavior is undefined.

Two arguments `%a0 = %a1 = c`, both `imm` borrows of one cell `c` at a lifetime `'a` that the
call does not end:

- **Nothing modifies `c` during the call.** While an `imm` lend of `c` is live, every entry of
  `c` in the resource is `imm` at one value: `▶◀` relates `imm` cells only, and at one value
  (`CellU.CompatS`, `CellU.CompatS.kinds`). So no `mut` borrow of `c` and no owner access exists
  anywhere: not in the callee, not in a callee of the callee, and not in a handler's clause
  inlined into it. The LIR's writes (`put`, `swap`, `slotPut`, `replace`) take a `mut` borrow or
  the owner, and the lend's lifetime `'a` encloses the call, because lends are lexical and the
  lend is made by the caller or above it.
- So `noalias`'s guarantee is **vacuous** at `c`. It "only holds for memory locations that are
  modified", and `c` is not modified. Accesses to `c` through `%a0` and through `%a1` violate
  nothing.
- `readonly` on each is the fact that the callee does not write through it, which is the LIR's
  write rule above.

For #756's case itself, no STOP: two `imm` copies passed to a function that is a source function
are consistent with LangRef. The tests are already in the corpus:
`corpus/imm-copy.bc` and `corpus/imm-copy-view.bc` are compiled with their `readonly noalias`
parameters (20 and 2 of them) and pass `native-facts.sh`'s differential run. After the copy, the
two copies are separate locals that hold one address. So the duplication is at run time, not one
SSA value passed twice.

**A related point, recorded for the reviewer and not an obstruction.** LangRef's list of *based on*
rules names `getelementptr`, `bitcast` and `inttoptr`, and not a round trip through memory. The
emitter stores every parameter in an `alloca` (`%l{i}`) and loads it back. So a `noalias`
parameter is accessed through a loaded pointer in every function. This is the C99 reading of
*based on*, which LangRef calls "intentionally similar to the definition of *based* in C99,
though it is slightly weaker". The weaker part may be exactly this round trip. It is the IR `clang -O0` itself emits
for a `restrict` parameter. LLVM's alias analysis treats a stored pointer as captured, and that is
consistent with this reading. I have not verified this against Alive2. It holds for every
`noalias` main emits, not only for #756's case.

## 3a. The bridge from the kernel facts to an LIR function (review F1, F2, M1)

**The finding.** Sections 0 and 3 rely on a premise: for the whole execution of the LIR function
that receives a borrow parameter, the borrow's lend is live and nothing reaches the cell except
through borrows of that lend. At a source function this follows from lexical lends: the lend is
made by the caller or above it. The machine conversion (SPEC §49, `Backend2/Convert.lean`)
produces step functions for which it does not hold.

- `corpus/async-r1-cancel-finaliser-writes.bc`, `@f12` ("cancel 1.0"), is emitted as
  `define internal void @f12(ptr noalias nonnull dereferenceable(4) %a0, ptr %a1)`. `%a0` is the
  `mut` borrow and `%a1` its owner: one cell (the reviewer's instrumented run reports
  `%a0 == %a1`).
- `@f12` calls `@f8(%a0)`, the borrower's finaliser, which stores through the borrow. It then
  calls `@f3(%a1)`, which reaches the cell through the owner's word and calls `bc_free`.
  `bc_free` writes the free-list link into the cell's first word (`Backend/Native/Runtime.lean`).
- So a location modified through `%a0` is accessed, during `@f12`'s execution, through pointers
  not based on `%a0`. That is LangRef's `noalias` undefined behaviour ("If there are other accesses
  not based on the argument or return value, the behavior is undefined"). The cell is also freed
  while `%a0` is `dereferenceable(4)`.
- At `clang -O2`, `@f12`'s callees are inlined and `bc_free`'s call carries `!noalias` of the
  `f12: %a0` scope. So LLVM may assume `bc_free` does not touch the cell. It did not reorder the
  store in this build. The attribute permits it.
- The reviewer reports the same shape in `async-r1-local-borrows` (`@f15`), and `noalias`
  parameters equal to another `ptr` parameter in the suspend and resume-entry steps of about ten
  async programs. There the steps make no accesses, so `noalias` is vacuous, but the premise is
  broken.

The kernel facts are not in question. `CellU.CompatS.kinds` holds while the lend is live. What
is missing is the step from "the lend is live" to "for the whole of this LIR function". Neither
SPEC §50 nor `paramFacts` states that step.

**What a fix needs (phase 2, not built here).** The test: a borrow parameter gets facts only at an
LIR function during whose execution the borrow's lend cannot end and its owner is neither a
parameter nor reachable. A list of function kinds does not meet that test. The second review
found that the relaxed lend's call-point steps (`pointK`, `alwaysinline`), its joins (`lendR`'s
`thenF`, `joinWith`), `resume N.M`, finalisers, `handled n`, the stack machine's
continue/return/unwind/step, `kappa`, `drive` and `tail` functions can all take a borrow together
with its owner. `prog/step-lend.bc` (a relaxed lend whose callback calls a yielding function) has
`@f18` receiving `m == o`. Today they carry no facts only because `classPtrs` types those
positions as `i64`.

So the rule is by construction, not by name:

- **Every function the conversion creates while converting a machine** (under `convK`,
  `genStackMach`, `kappa`, drive) is marked, and its parameters get no facts. This is an `Fn`
  field set where the function is made, not a test of its name.
- **The principled replacement** is for the LIR to carry, for each borrow parameter, whether its
  lend's scope encloses the function: the conversion knows where it opens and closes a lend. Then
  `paramFacts` reads that bit, and the bridge is a per-parameter fact rather than a property of
  function kinds.
- **STOP:** keeping facts at any machine-made function by a narrower rule, until the bridge is
  stated for that function.
- **The test** checks `Fn.facts` per LIR function: no fact at a marked function. It does not
  check the emitted attributes, which `classPtrs` filters, because a change to the tail-call
  classes would otherwise put facts back silently.

Each function that loses facts is measured (section 7).

**The citations, completed (M1).**

- `adequacyD` is stated at `CDerives LifeCtx.empty [] e (.comp (.ret .unit))`. A program with an
  R1/R2 site rests on `adequacyD_pin` (`Core/PinFundamental.lean`) under `PinLaw`'s `LendFrame`
  or `LoopFrame`, as `bcc trusted` already reports. An I/O program rests on `externs_main_safe`
  (`Core/Stdio.lean`). The cite strings `citeMut`/`citeImm` name the theorem that applies.
- `dereferenceable(b)` also rests on the width-class assumption marked UNPROVED at
  `Backend2/Lower.lean`'s `.alloc`: that a cell holds over its life only types of its class, so
  the class's widest bytes are allocated. It is named in the cite and listed by `bcc trusted`.
- **The bridge itself is a named compiler assumption, `LendEnclosesFn`**, with the LIR's write rule
  that `citeImm` states ("the LIR's writes take a `mut` borrow or the owner") and the conversion's
  faithfulness to the checked term. Neither is a Lean declaration. Until the per-parameter bit
  exists, `bcc trusted` lists `LendEnclosesFn` at every function with parameter facts.
- `citeMut`'s "`●` joins `imm` cells only: `CellU.CompatS.kinds`" also needs `CellU.CompS.compat`
  (`Support/Model/Composition.lean`): `kinds` is a fact about `▶◀`, and `●` is defined only where
  `▶◀` holds. Paths: `CellU.CompatS.kinds` (`Support/Model/Composition.lean`), `walk_index_lt`
  and `walk_get_leaf` (`Frontend/Check/Derived.lean`), `ResU.CompatS.disjoint_of_immFree`
  (`Paper/S6_1_StandardLemmas/Lemmas.lean`).
- `bcc trusted` lists today the Wasm runtime, the WAT printer and wasmtime. For the native target
  it also lists the native runtime (`Backend/Native/Runtime.lean`), `clang`, the width-class
  assumption, and `NoUnwind` (row N).

## 4. `captures(none)`: which rows license it

`captures(none)` says that no component of this copy of the pointer is captured: neither the
address nor the "ability to access the pointer … after the function returns".

**No row on its own licenses it.** The row says whether the call can suspend, but a borrow can
outlive the call without any suspension:

1. **Through the result.** `fn first(p: imm 'a (i32 * i32)) -> imm 'a i32`, at the empty row,
   returns a borrow derived from `p`. With `captures(none)` on `p`, the caller's later load
   through the result is an access through the provenance the attribute says was not kept. LLVM
   may then reorder a store to the cell's owner past it, in the caller, once the lend has ended.
2. **Through another argument.** `fn stash(o: mut 'b (imm 'a i32), p: imm 'a i32)` writes `p` into
   `o`'s cell, at the empty row.
3. **Through a suspension.** This is the case the issue names. A relaxed lend's callback
   (`LendFrame`, `withborUV`, at a `Row.ResumeO` row: `await`, `yield`) holds its `mut` view
   across a suspension. A `LoopFrame` generator's state holds views of the place across each
   observation. Converted to a machine, the suspend step returns the borrow in its result words, as part
   of the suspended computation (`async-r1-cancel` family, `@f12` of the reviewer's reduction),
   and a later step receives it again. That is channel (1), reached at a resuming row. A rule of
   "Div-free, or no `Div`" would mark that step's parameter `captures(none)`. The rule "no
   suspending operation in the row" is still not enough, because of (1) and (2).

**The licence a correct rule needs.** For a parameter at `imm 'a T` or `mut 'a T`:

- the function's row has no operation that can suspend while `'a` is live. That is no machine
  operation (`Convert.lean`'s machine rows), and so no `Row.ResumeO` lend or `LoopFrame` state
  over `'a`;
- `'a` occurs in neither the result type nor any other parameter's type;
- the kernel fact that a value at a type not mentioning `'a` holds no location reachable only
  through `'a`. This is a parametricity lemma of the relation. It is **not derived**, and I have
  not looked for a name for it beyond this search.

The backend cannot read the second condition: `LTy.imm`/`LTy.mut` carry no lifetime. So
`captures(none)` is not emitted. Its candidates are carrying lifetimes into `LTy` (backend) and
the parametricity lemma (kernel).

## 5. Forcing annotations beyond `musttail` and `alwaysinline`

Checked against LangRef. Hints are not counted.

- **`tailcc` (calling convention).** "ensures that calls in tail position will always be tail call
  optimized", but it "requires the prototype of all callees to exactly match". It forces nothing
  that `musttail` does not already force under the C convention, which the classes' padded
  prototypes satisfy (`classArity`). Whether `tailcc` would let a class's prototypes differ, and
  so drop the padding words, is a cost question for the backend. It is not a fact. **Not proposed.**
- **`llvm.loop.unroll.full`, `llvm.loop.vectorize.*`, `llvm.loop.distribute.enable`,
  `llvm.expect`.** Each "suggests" or "enables": these are hints, not forcing.
- **`llvm.memcpy.inline`.** It forces an inline copy rather than a library call. No zero-cost
  target asks for it: the LIR's copies are word moves.

**None applies.** No forcing annotation beyond `musttail` and `alwaysinline` serves a zero-cost
target today.

## 6. Needed optimisations that cannot be forced (candidates for our own lowering)

Listed, not built:

1. **#537's vectorised array loop.** A counted walk over a borrowed family whose step reads or
   writes only its current leaf. Vectorisation cannot be forced: `vectorize.enable` is a hint. The
   candidate is to emit vector operations (`<N x i64>` loads and stores over the leaves) for a
   walk the elaboration marks, licensed by `walk_index_lt`/`walk_get_leaf` and the family's
   disjointness. It needs a proof or test that the step touches only leaf `i`.
2. **Registers for a handler's state** (handlers-di's clock, SPEC §50 *Open*, #537 fix 9). Today
   it is kept in a register only when LLVM uses the facts. The candidate is the state as an LIR
   local, so that it is SSA from our lowering.
3. **Scalar replacement of the parameter and local `alloca`s.** Every local is an `alloca`, and
   SROA/mem2reg recovers SSA. The candidate is to emit SSA (`phi`) directly from the LIR, which
   §50's single exit block already does for results. It is informational today in effect,
   because SROA always runs at `-O2`, but it is not forced.

## 7. Measured: facts against `--no-facts`

Measured on the toolchain's `clang -O2` (Apple clang 21), `bcc run --backend new --native`, with
the facts and with `--no-facts`, best of 3 wall-clock runs at the bench arguments:

| program (`bench/`) | facts (s) | `--no-facts` (s) | `-O2` IR: stores / loads, facts vs none |
|---|---|---|---|
| handlers-di | 0.131 | 0.130 | 18/19, 26/28 |
| sieve | 0.421 | 0.421 | 11/11, 17/17 |
| matmul | 0.164 | 0.163 | 18/18, 16/16 |
| quicksort | 0.148 | 0.151 | 22/22, 26/26 |
| sum | 0.135 | 0.135 | 15/15, 17/17 |
| spectral-norm | 0.236 | 0.236 | 11/11, 31/31 |

The outputs agree. On these six programs the parameter facts make no measurable difference to
time. Only handlers-di's optimised IR changes, by one store and two loads, which is §50's
handler-state cell. No count (`bcc-counts`, `corpus/counts-backend2.expected`) reads native
output, so no count leans on a fact.

**Improvement candidates**, for every informational annotation that a target leans on:

| annotation | what leans on it | remaining gain, measured | candidate |
|---|---|---|---|
| `noalias`/`readonly`/`nonnull`/`dereferenceable` at borrows (§50) | handlers-di's clock in a register (§50 *Open*) | none measurable (0.131 s against 0.130 s); one store and two loads in the IR | section 6 item 2: the handler state as an LIR local |
| the borrow facts at machine steps (section 3a) | nothing measured: the six programs have no machines | to measure on the async corpus once the steps lose their facts | none expected |
| SROA of the `alloca`s (no annotation; LLVM's default pass) | every program's register allocation | not measurable without a build that omits the pass | section 6 item 3 |

The SPEC text for §50's table becomes "informational, relied on for now, improvement candidate",
in place of "no performance target rests on LLVM's use of them".

## 8. NOT-do list and shortcuts marked STOP

Not done in this unit:

- no change to Core, `CDerives`, the checker, the elaboration or the language;
- no `willreturn`/`mustprogress` until section 1's steps 1–3 are done;
- no `captures(none)` until lifetimes reach the LIR and the parametricity lemma exists (section 4);
- no vectorised lowering, no SSA emission and no handler-state register (section 6: candidates);
- no gate in phase 1.

**STOP** if any of these comes up:

- **STOP: emitting a fact "because LLVM would infer it anyway".** `memory(...)`, `nofree` or
  `nocapture` inferred by FunctionAttrs is LLVM's business. An annotation we write is our claim, so
  it needs our licence.
- **STOP: citing a fact at a type when the backend reads it from a layout shared by an owner and
  its borrows** (§50). A mode comes from the parameter's `LTy`, never from `L.sh`'s pointer node.
  Row O (owned `Ref`) must read `.ref` off the `LTy`, because the node of `ref`, `imm` and `mut`
  at one contents may be the same.
- **STOP: relying on an informational attribute for a count or a target without marking it.** A
  reliance is allowed only with its improvement-candidate entry and its measured gain.
- **STOP: `!invariant.load` at an `imm` borrow** (row I): LangRef's "at all points in the program"
  is not the lend's extent.
- **STOP: `captures(none)` from the row** (section 4, examples 1–3).
- **STOP: `dereferenceable` on an owner** (row O): the callee may free it.
- **STOP: a parameter fact at any function the machine conversion makes** (section 3a), and no
  narrower rule, until the bridge is stated for that function. Never key the rule to function
  names.

## 9. Review

One independent review, primarily of soundness. Findings and what was done:

- **F1 (Fatal):** the borrow facts are false at machine-converted `cancel` steps
  (`async-r1-cancel-finaliser-writes.bc` `@f12`). Confirmed by reading the emitted IR. Recorded
  as section 3a, a soundness finding in main's output, for the coordinator. A fix is scoped
  there, not built.
- **F2 (Fatal):** row O's owner `noalias` rests on a premise the LIR's steps refute. Row O dropped.
- **F3 (Fatal):** row O's `nonnull` is false for a cell of no words (address `0`). Row O dropped,
  and the guard recorded.
- **M1 (Major):** the citations are incomplete (`adequacyD_pin`/`LendFrame`, `externs_main_safe`,
  the width-class assumption, `bcc trusted`'s native list). Section 3a completes them.
- **m1–m4 (Minor):** the full LangRef sentence on *based on* is quoted; `NoUnwind` now covers
  thread cancellation; the suspension example's mechanism is corrected (the borrow goes out
  through the result words); `fuel_total` is noted in section 1.

The Fatal findings call for one more full review (section 10).

## 10. Second review

A fresh full review, as the Fatal findings required. It swept 419 programs' IR with
instrumentation. F1 reproduced, F2 and F3 are closed by dropping row O, and row N's facts hold
(no `invoke`/`landingpad`/`resume`, and no `pthread_cancel` in the runtime). Every citation exists.

- **FA (Fatal):** the first fix rule was a list of function kinds and missed call-point steps,
  joins, `resume`, finalisers and stack-machine functions, which also take a borrow together with
  its owner (`step-lend.bc` `@f18`). Applied: the rule is by construction (every machine-made
  function is marked), with a per-parameter lend-encloses bit as the principled form (section 3a).
- **MA (Major):** a narrower rule was left to the build. Applied: now a STOP.
- **MB (Major):** the bridge was cited nowhere. Applied: it is named `LendEnclosesFn` and goes in
  `bcc trusted`.
- **m1–m3 (Minor):** the test reads `Fn.facts`, not the emitted attributes; `CellU.CompS.compat`
  is added to `citeMut`'s citation; paths are given.

This was the extra full review that the brief allows. The fixes are in the document; there was no
further review.
