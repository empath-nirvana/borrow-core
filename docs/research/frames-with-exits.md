# Frames with typed exits: an exhaustive accounting of returns (#632, step 1)

Step 1 of #632: the laws, the target statements in Lean, and the design. Nothing in the library
is built or changed. The Lean is `experiments/Frames/` (`lake build Frames`, not a default
target). Claims are marked **proved** (in Lean, no `sorry`), **stated** (in Lean, with an
enumerated `sorry`), **by inspection** (read off code or SPEC, cited) or **hypothesis**.

## 0. Summary

- **The frame type is derived.** `Fr Σ Π E A ≜ Π ⊸ F_Σ (Π ⊗ (A ⊕ ⊕E))` (`frTy`). `Π` is the
  tuple of the frame's *slots*: owned cells `Ref A` (a `let mut`) and borrows `Mut @a A` (a
  `&mut` parameter). `E` is the **exit row**, a stack of the local exits the frame may leave by.
  `Σ` is Core's effect row. There is no new `VTy`, `CTy` or `CDerives` constructor, no new index
  on `CDerives`, and no change to the relation or the model.
- **Every exit returns the slots by the type's shape.** `Π ⊗ −` is a factor of every answer, so
  each exit carries `Π` once. Raise and abort are not in `E`. They are operations of `Σ`, and leave
  by §19's unwinding: every rule that runs Core code while it holds slots holds them under a
  `[then]` finaliser, or lends them through an unwinding borrow constant.
- **The rules are a closed set of 13 derived rules**, packaged as an inductive judgment
  `FDerives` whose elaborated Core term is an index, as `Affine`'s `ADerives` is. The rules are
  `core`, `exit`, `bind`, `case`, `catch`, `under`, `use`, `lend`, `new`, `loopCount`,
  `loopIter`, `callBlock` and `sub`. Every Core computation enters through the one `core` rule.
- **The accounting theorem is one induction over `FDerives`** (`accounting`, stated). Every run
  of a frame on slots `π` that reaches a value reaches `(π, x)`: the *same* slots, at the same
  positions, beside an exit tag. Every stop at an outer operation resumes into a term with the
  same property. The property is a coinductive invariant on machine runs (`Rets`), because a div
  loop stops at a tick on every turn.
- **The statements are not vacuous.** It is proved that a Core term at the frame type that swaps
  two slots of one type is typed (`swap_derives`) and fails the accounting (`not_returns_swap`).
  Typing alone does not give the accounting; the frame rules, which never hand `π` to Core code,
  do. A depth-4 nesting is proved to be a frame (`nested_derives`, no `sorry`). Its exit crosses a
  loop to the `catch` outside it, and its accounting is the general theorem's, with no case of
  its own (`nested_returns`).
- **Requirement 2.** None of the foreseen lemmas mentions two constructs (§4). **No kill
  criterion fired** (§9), with one reading the user should confirm: `FDerives` is a judgment
  that elaborates into `CDerives` (the `ADerives` precedent), and `Rets` is a unary property of
  runs, not a semantic relation of the model.
- **Every hand-written elaborator rule becomes sugar into frame terms** (§5): the joins of R2
  and R3, LoopLend, `mutCap`, `escapingWriter`, early return, and block and loop exits. One
  rewrite carries a language decision (D3): a borrow block over a div loop becomes per-use lends
  of the place.
- **#626's place model compiles with no join** (§6). The arms of a `case` are frames over the
  same slots, and the elaborator writes no hand-on.
- **Suspension.** At frame level, suspension needs no new exit kind: a stop is `Rets`'s second
  clause, and a cancelled continuation runs the slots' finalisers (§19). What suspension adds is
  exactly one exit kind, a stop *inside an open lend* (`use`/`lend` at a resuming row). That is
  T1 (#172), and nothing in the design blocks it (§7).

## 1. The design

### 1.1 Types (`Frames/Defs.lean`)

    slotsTy [P₀, …, Pₙ] = P₀ ⊗ (… ⊗ (Pₙ ⊗ 1))
    ⊕[(l₀, B₀), …]      = B₀ ⊕ (… ⊕ 0)                     (ExitRow.sumTy)
    Fr Σ Π E A          = Π ⊸ F_Σ (Π ⊗ (A ⊕ ⊕E))            (frTy)
    a block             = !U(B ⊸ Fr Σ Π E A)                (blockTy)

- A **slot** is `Ref A` with `HasDtor A`, or `Mut @a A` (`SlotOk`). Each has a destructor, so
  whoever holds the slots can finalise them on an unwind.
- The **exit row** is a stack, innermost catcher first. An exit is a de Bruijn index into the
  enclosing catchers. A `catch` (a labelled block, the function's `return`, a turn's `continue`)
  removes the head, and a loop removes the head (its `break`). Exits are caught in lexical order
  only, so no exit is ever compared with another by name.
- Labels are carried for messages. They are static, as handler names are (§19).

### 1.2 The rules and their exit rows (`Frames/Rules.lean`)

`FDerives Δ Γ Φ Π e Σ E A`. `Γ` is Core's context, and `Φ` is the program's frame-typed blocks.

| rule | premises | exit row of the conclusion | elaborates to |
|---|---|---|---|
| `core` | `Γ ⊢ N : F_Σ A` (Core) | any `E` | `λπ. N then x. (π, inl x) unwind dtor_Π π` |
| `exit k` | `E[k] = (l, B)`, `Γ ⊢ V : B` | `E` | `λπ. (π, inr (inj_k V))` |
| `bind` | `M : E, A`; `x : A ⊢ N : E, B` | `E` | `M π to (π', r). case r {inl a → N π' \| inr e → (π', inr e)}` |
| `case` | `V : A ⊕ B`; two arms at `E, C` | `E` | `case V {… → Mᵢ π}` |
| `catch` | `M : (l, B) :: E, A`; `b : B ⊢ H : E, A` | `E` (the head removed) | the head summand to `H`, the rest passed on |
| `under` | `M` over `Π` | `E` | the head slot held aside under `[then]` |
| `use` | `N : U(∀'x. Mut 'x A ⊸ F_Σ(['x] B))` (Core), `Σ` unwind-only | any `E` | `withborU` on the head slot, the rest under `[then]` |
| `lend` | `M` over `Mut 'x A :: Π`, `Σ` unwind-only | `E` (passed out of the lend) | `withborU` on the head slot, `M` in the callback |
| `new` | `Γ₁ ⊢ V : A`; `M` over `Ref A :: Π` | `E` | `alloc`, `M`, then `free` at the normal exit, `dtor` at the others |
| `loopCount` | turn `M : (l, B) :: E, S₀` at `F` | `E` (the head removed) | `count_try` over the state `Π ⊗ S₀` |
| `loopIter` | turn `M : (l, B) :: E, S₀` at a `Div` row | `E` (the head removed) | `iterate` over the state `Π ⊗ S₀`, `close` handing back `Π` |
| `callBlock` | `Φ[k] = b` | `b`'s row | `λπ. b V π` |
| `sub` | `M` at `Σ`, `Σ ≤ Σ'` | `E` | `λπ. M π` at `Σ'` |

The exit row stands to local exits as `Σ` stands to effects. `exit` is the `[perform]` of exits
and `catch` is their `[handle]`; every other rule passes `E` through unchanged, as Core's rules
pass `Σ`. Each conclusion's row is computed from its premises' rows by the one column above.

Two facts make this compose:

- **Core code never sees `π`.** `core`'s and `use`'s Core premises are typed in `Γ`, which does
  not hold the slots. The only door from a slot to Core code is `use`, which lends the slot
  through `withbor`. A callback's `['x] B` cannot return the borrow, and `withbor` hands back
  the source it was given (`withbor ≜ λx.λf.(x, f () x)`, `Paper/S2_Statics`).
- **The frame's slots are fixed across arms.** `case` takes both arms over the same `Π`. That is
  the join. It belongs to the kernel rule, and the elaborator does not write it.

### 1.3 Raise and abort (§19)

Raise and abort are not exits of `E`. While a frame holds its slots across Core code, the slots
sit in exactly one place:

- in a `[then]` finaliser's context, as in `core` and `under` (`dtor_Π`);
- in the source of an unwinding borrow constant, as in `use` and `lend` (`withborU` with the
  source's destructor, §19's own form);
- or inside a sub-frame, which holds them by the same rule.

So an unwind finalises every slot once. `new`'s cell is in its sub-frame's slots, so it is
finalised there and not by `new`. This is §19's "drop glue", produced by the kernel's rules
instead of being inserted by the elaborator. There is no frame rule for raise, so frames cannot
disagree with `[unwind]`/`[finalise]`. They *are* those rules, applied to the elaborated term.

### 1.4 The accounting invariant (`Frames/Theorems.lean`)

    RetsStep π R t ≜ (every run t ↦* w, w a value  ⇒  w = (π, x) for some x)
                   ∧ (every run t ↦* K[perform (n, v)], K free of n  ⇒  ∀ w, R (K[w]))
    Rets π t      ≜ ∃ R, R t ∧ ∀ t' ∈ R, RetsStep π R t'
    Returns e     ≜ ∀ π, Rets π (e π)

- **It is about runs.** It reads no type and no resource; it is a property of the machine at one
  value `π`.
- **It is coinductive** because a div loop ticks on every turn, forever.
- **Raise has no clause.** A run that ends in an uncaught raise has unwound, and §19 accounts
  for it (`frame_unwind_leakfree`).

## 2. The Lean targets

`experiments/Frames/`. `lake build Frames` succeeds with 30 enumerated `sorry`s, each with a note
on what it needs. Every proved result's axioms are `[propext, Classical.choice, Quot.sound]` or a
subset.

| name | statement | status |
|---|---|---|
| `frTy`, `exitsTy`, `ExitRow.sumTy`, `slotsTy`, `blockTy` | the frame type and the exit row | definitions |
| `frTy_eq`, `frTy_nil` | the frame type is Core's own arrow into `F_Σ` | proved (`rfl`) |
| `sumTy_get`, `SlotOk.hasDtor`, `SlotsOk.hasDtor` | the row's positions; the slots have a destructor | proved |
| `FDerives` | the 13 rules, with the elaborated term as index | definition |
| `CDerives.shift_dead` (O1) | weakening by a dead binder | stated: one induction over `CDerives`, no inversion |
| `FDerives.elab` | every frame is `CDerives` at `Fr Σ Π E A` | stated: 13 cases, one per rule |
| `frame_sound` | `SemC` at the elaboration (`fundamentalC`) | proved from `elab` |
| `runFrame_derives`, `frame_adequacy` | a closed frame program runs to a value at the empty memory (`adequacyD_obs`) | proved from `elab` and O1 |
| `core_embeds` | every Core computation is a frame (`core`) | proved |
| `core_conservative` | `core N` on `π` reaches `(π, inl v)` iff `N` reaches `v` | stated |
| `Rets`, `Returns`, `FBlock.Returns` | the accounting invariant | definitions |
| **`accounting`** | every frame's elaboration satisfies `Returns`, at every closing substitution, given blocks that do | stated: 13 cases, one per rule |
| `block_returns` | a block built from a frame satisfies it | stated |
| `frame_handled` | a frame under a handler is Core's `[handle]` | stated |
| `frame_unwind_leakfree` | a handled frame program, whether or not it raised, runs to a value at the empty memory | proved from `frame_handled` |
| `swap_derives`, `swap_runs`, `not_returns_swap` | a typed Core term at the frame type fails the accounting | **proved** |
| `nestedTurn_derives`, `nestedLoop_derives`, `nested_derives` | a depth-4 nesting `new ⊃ catch ⊃ bind ⊃ loopCount ⊃ case ⊃ exit` is a frame | **proved** |
| `nested_returns`, `nested_adequate` | its accounting and adequacy are the general theorems' | proved from `accounting` and `frame_adequacy` |

The `sorry`s are:

- O1 (1);
- `elab` (13);
- `core_conservative` (1);
- `accounting` (13);
- `block_returns` (1);
- `frame_handled` (1).

## 3. Why it is exhaustive by construction

- **`accounting` is one `induction h` over `FDerives`.** Lean checks that the match covers
  every constructor. A rule added to `FDerives` fails the build at `accounting` (and at `elab`)
  until its case is written. No list of cases is kept by hand.
- **Core is one case.** Every Core rule, present or future, enters through `core`. Its
  accounting is the same whatever the Core derivation is, because Core code does not see `π`.
  Adding a `CDerives` rule therefore adds no frame case. It adds a case to O1 and to
  `fundamentalC`, as it already does.
- **Depth does not matter.** Every case uses only its premises' hypotheses, and nesting at any
  depth is the same induction. `nested_returns` is the general theorem applied at a depth-4
  nesting whose innermost exit crosses a loop; it has no case of its own.

## 4. Requirement 2: every foreseen lemma, checked for two constructs

| lemma | constructs it mentions |
|---|---|
| O1 `CDerives.shift_dead`, one case per `CDerives` rule | each case, that rule only |
| `elab`'s case for rule *r* (13) | *r*; its premises' derivations |
| `accounting`'s case for rule *r* (13) | *r*; its premises' invariants |
| `injAt`'s typing against `E[k]` | the exit row only |
| `SlotsOk.hasDtor`, `dtor_wf` at `slotsTy` | the slot tuple only |
| **`rets_ctx`** (foreseen, not yet stated): `Rets π t ⇒ Rets π (K[t])` for an evaluation-context continuation that maps answers `(π, r)` to `(π, f r)` | one shape of `Kont`, generic in `t`; used by `bind`, `catch`, `core`, `under`, `use`, `lend`, `new` |
| `ubind` at a value and at a stop (`[then]`, `[finalise]`) | the `ubind` frame |
| `withborUE`'s answer `(r, b)` with `r` the source | the unwinding constant |
| `count_try`'s head step (`countTryNext`) | `count_try` |
| `iterate`'s head step, a tick as a stop | `iterate` |
| `alloc`, `free`, β, `let`, `case` steps | the machine's own |

**Result: no lemma mentions two constructs.** The cases most likely to tempt a pairwise lemma
are handled as follows:

- **A `break` inside a lend inside a loop.** It is `loopCount ⊃ lend ⊃ exit`. `lend`'s case
  passes its premise's answer `(ρ, r)` out of the callback, whatever `r` is. `loopCount`'s case
  reads the turn's answer, whatever produced it.
- **An exit past a loop.** The loop removes only the head of the row. The rest is the turn's
  `inr`, which `loopCount`'s case returns unread (`nested_derives` is this case).
- **A raise inside a `use`.** This is §19's lemma for the unwinding constant (`wpTS_M_frameU`,
  Core). The frame rule never sees the raise.
- **A deeper slot.** It is `under` applied k times around `use`. No lemma covers "slot k".

This check is made in advance of the proofs. It is repeated when the `sorry`s are written, and
it is the kill criterion then.

## 5. Each hand-written elaborator rule, rewritten as frame terms

"Sugar" here means the rewrite is a fixed function of the construct's syntax and R1's
resolution. It inserts only frame terms, and the kernel checks each one.

- **R2/R3 joins** (`if`, `match`, `case`, `let p = if …`, `x <- M` as a head; `handOn`,
  `handArms`, `joinBind`, `Sugar.thenGo`).
  - Before: each arm hands back the write set `W`, and the binding takes it apart and rebinds it.
  - After: `case V M₁ M₂` and `bind M (x. N)` over the frame's `Π`. No write set exists, the
    arms share `Π` by the rule, and a head is a `bind`.
  - Check: sugar. The join is in `case`'s elaboration, which is kernel-side (`caseE`).
- **R2 write sets** (`Parser.frame`, `assigned`).
  - After: gone. A construct does not compute what it writes. Each place is a slot index (R1's
    binder, de Bruijn into `Π`).
  - Check: resolution only, in scope by CLAUDE.md.
- **Loop turns, `break`, `continue`** (§14, §16's `count_try` exits, `DivSt.exits`).
  - After: `loopCount n s₀ M` or `loopIter s₀ M`. `break e` is `exit 0 e`, `continue` is
    `exit` to a `catch` around the turn, and an outer loop's `break` is `exit k` for its depth.
  - Check: sugar. The state `Π ⊗ S₀` is the rule's, not a threading the elaborator computes.
- **Early `return`** (`normExits`, moving loops onto the spine).
  - After: the function body is `catch M (r. core (return r))`, and `return e` at any depth is
    `exit k e`, with `k` the number of catchers between it and the body.
  - Check: sugar. `normExits`'s moves go: an exit passes every rule by the row.
- **Block exits** (leaving a `{ … }` scope; labelled exits, when a label is named).
  - After: a labelled block is `catch`. Leaving a scope is the end of the `new` frames the
    block opened: their normal exit frees the cell and their other exits destroy it.
  - Check: sugar, with no drop glue for places. §19's drop glue for owned non-place locals is
    unchanged: they are `Γ`, not slots.
- **LoopLend** (§14; `Frontend/Elab/LoopLend.lean`), a borrow block over a loop.
  - After, one of two (decision D3):
    - (a) `lend M`, the frame inside one lend. Core refuses it at a `Div` row (no borrow
      callback's row holds `Div`, `Row.Unwind.divB`), so this covers only total loops.
    - (b) the place model's meaning: `borrow mut t { b -> S }` is `S` with `b` resolved to `t`'s
      slot. Each use of `b` in `S` is a `use` of the slot, a lend for that one Core statement,
      and a div loop between uses holds the owner in its state.
  - Check: (b) is resolution plus the kernel's `use` rule. The extent of each lend is fixed by
    the rule (one Core statement), not chosen by an analysis, so LoopLend's stretch splitting,
    `vs`/`ws` hand-ons and copies-of-the-borrow tracking go.
  - A program that stores the borrow in a value held across a frame construct is refused by
    Core's box rule at the `use`, which is the same class of program LoopLend refuses
    (`escapeError`, `iterError`).
  - **Flag:** (b) changes the meaning of a borrow block from one lend to one lend per use. For a
    `mut` place, nothing else can use the place during the block. Equality of the two meanings
    is a two-run property, and `experiments/TwoRun` showed those do not follow from `wpTS`. It is
    a language decision, not a theorem here.
- **`mutCap`** (§41 R3 *In*; the callee copies with the writes as parameters).
  - After: a block that writes places is a frame-typed block `!U(B ⊸ Fr Σ Π E A)`, an entry
    of `Φ`, called by `callBlock` with the current slots.
  - A callee that calls a writing block is a frame definition instantiated at the caller's `Π`.
    Each instance is typed by the kernel as a frame, as `letPoly` retypes each occurrence of a
    λ-value at its own row.
  - Check: monomorphisation that the kernel checks, not threading the kernel could not express.
    The block type *is* R3's `!U(W ⊗ A ⊸ F_r (W ⊗ B))` with `W = Π`.
  - **Not settled:** how the callee's frame definition is written generic in `Π` (a place-row
    variable, as `Σ` is generic at `letPoly`) is not stated in Lean. Only first-order blocks,
    `callBlock` with `Φ` closed values, are. This is decision D4.
- **`escapingWriter`.**
  - After: deleted. A writer block is an entry of `Φ` (second class, as in System C,
    `docs/second-class-and-system-c.md`), never a Core value, so it cannot be stored or returned.
    Calling it needs its `Π` in scope (`callBlock`'s premise).
  - Check: the refusal becomes the kernel's typing.
- **`modify`, `with` (answering), `run`.**
  - `modify P { v -> S }` of a place is `use` with `S` as the callback over the swapped
    content.
  - `with h(e) { S }` answering is a `new` for the state's cell and `S` as a frame over it.
  - `run M` is `bind`.
  - Check: sugar. §41's in-place `modify` of a `let mut` value (`io_mu`) goes, because a place is
    a place.

**`STOP: KERNEL WORK`.** No rewrite above writes an elaboration rule of the kind the stop names,
so I did not stop on any. D3(b) and D4 are reported as decisions, not done.

## 6. #626's place model with frames: no join

- `let mut x = e; N` is `new e N`. The function body is one frame whose slots are its `let mut`s
  in scope, by R1's binder order.
- A read of `x` is `use` (under `under`s for its depth) with a callback that loads through
  `withswap` and copies. A write is `use` with a `withswap` store. `let (x, q) = f(…, x, …)` is
  one `use`.
- `if`/`match` are `case`, so both arms are over the same `Π` and the elaborator writes no
  hand-on.
- Loops are `loopCount` or `loopIter`, with `Π` in the state by the rule.
- `f(&mut x)` is `use` with the callback `λb. f(b)`.
- A block that writes is a `Φ` entry (the place model's A2 becomes `callBlock`).
- The place model's prototype refusals A1 (a resuming operation in a place's scope) came from
  lending the place over its whole scope (`borrow mut alloc(e) { x -> N }`). In frames the slot
  is the owner, and a lend is open only within one `use`.
  - So a resuming operation *between* uses holds the owner in its continuation, which Core
    already allows (`[then]` at an affine row, §35's heap cell that a suspension crosses).
  - Inside a `use` it is still refused (`Row.Unwind`). See §7, and decision D5 on whether this
    stage keeps A1 refused anyway.
- A3a (a moved linear content) and A3b (an `imm` view read twice) are unchanged: they are the
  `use` callback's Core typing.

What remains in the elaborator is each place's slot index (R1) and the construct-to-rule map
above.

## 7. Suspension, later

- **At frame level, suspension needs no new exit kind.**
  - A stop at an outer operation is already `Rets`'s second clause: the slots are in the
    continuation and come back at every resumption.
  - A cancelled continuation runs the finalisers of the slots its `[then]` frames hold, which is
    §19's cancel.
- **What suspension adds is exactly one exit kind: a stop inside an open lend.**
  - That is a `use` or `lend` whose callback row holds a resuming operation, refused today by
    `Row.Unwind`.
  - Its accounting needs the lend to survive the stop and end once at the resumption or the
    cancel. That is T1 and #172's spanning lend: a register of open lends that the model does
    not have (`experiments/LoopBorrow`, `refoldKripke_false`).
  - In the frame rules it would be one more premise form on `use`/`lend` and one more clause in
    `RetsStep`.
- **Nothing in the design blocks it.**
  - The frame type does not change, since a stop is not an answer.
  - The exit row does not change, since a stop is not a local exit.
  - The new obligations sit in the two lend rules' cases only.
- **The risk is the tier-2 history repeating:** a new relation for the lend register, built
  before conservativity.
  - Here conservativity is a stated theorem from day one.
  - The suspension stage should start with the analogue of `core_conservative`: Core's
    relation, unchanged wherever no stop sits inside a lend.

## 8. Prior art

The four papers were read from their PDFs with the Read tool and its `pages` parameter. The
reading was delegated to three readers that reported page-cited summaries. Page numbers are the
PDFs'.

- **Tang, Hillerström, Lindley, Morris, *Soundly Handling Linearity*, POPL 2024 (arXiv v2,
  pp. 1–51, all read).**
  - Control-flow linearity tracks how many times control may re-enter a context. The
    sequencing rule T-Seq (Fig. 4, p. 11) asks that `N`'s context and `M`'s row agree in
    linearity. T-SeqSub (p. 12) moves the condition onto `M`'s row only.
  - An operation whose continuation is discarded, such as `Fail`, is unlimited. That forces
    `N`'s context to be unlimited, so **an abort may happen only where no linear value is live**
    (pp. 2–3, 12). There is no unwinding or finaliser mechanism.
  - Soundness is syntactic: progress and preservation, plus Theorem 3.6's linear-safety and
    multiset-conservation invariant, proved by induction on reduction rules (pp. 15, 33–35). The
    proof of Theorem 3.4.2 is an induction over evaluation contexts spanning `do`, `let` and
    `handle` together (pp. 29–30).
  - For us:
    - local exits as data, as here, avoid their restriction, since the slots travel in the
      answer;
    - raise is the one unwinding exit, and needs §19's finalisers, which they do not have;
    - their context-decomposition lemma is the kind of multi-construct lemma requirement 2
      forbids. `rets_ctx` (§4) is one generic `Kont` shape, not a lemma over pairs of
      constructs.
- **Jung et al., *RustBelt*, POPL 2018 (pp. 1–34, all read; the technical appendix is not in
  the PDF and is unchecked).**
  - λRust is in CPS so that it can express labelled `break` and early `return` (p. 11).
  - A continuation's type `cont(L; x̄. T')` records the local lifetimes `L` and the whole typing
    context `T'` it expects back (pp. 13–14). F-JUMP requires the current context to coerce to
    it, and `L` to match exactly (p. 16). F-CALL passes the caller's frame to the return
    continuation (p. 16). This is the closest analogue of a typed exit.
  - The fundamental theorem is one semantic lemma per rule (Thm 7.1, p. 29). Unwinding after a
    panic is not modelled (p. 26 fn. 10, p. 31). Borrows may be dropped and are recovered by
    inheritance, so RustBelt gives affinity, not exactly-once (p. 23 fn. 9).
  - The lifetime logic's rules are LftL-borrow, -bor-acc and -reborrow, with inheritance used
    once (pp. 23–24).
  - For us:
    - `cont(L; x̄. T')` flows *down* (inherited by `letcont`'s premises). Our exit row has the
      same direction (a stack of enclosing catchers), so "computed from premises" here means as
      `Σ` is. RustBelt has no bottom-up row, and neither does this design.
    - Exactly-once is stronger than anything RustBelt proves, and here it rests on Core's
      linearity of `Mut` plus `Rets`.
    - RustBelt gives nothing for raise.
- **Tov and Pucella, *Practical Affine Types*, POPL 2011 (pp. 1–12, all read; the extended
  version with full proofs is unchecked).**
  - Affine rather than linear "interacts better with … exceptions" (p. 1).
  - "We anticipate that safely combining linearity with exceptions requires a type-and-effect
    system to track when raising an exception would implicitly discard linear values" (p. 11).
  - The calculus ᵃλ_ms has no exceptions (p. 4). Soundness is by progress and preservation
    (Thm 6, p. 10). Qualifiers are computed as the ⊔ of the parts, with principal qualifiers in
    Thm 3, p. 10.
  - For us: §19's row *is* that effect system. Raise in `Σ` with finalisers held by the frame
    rules is the mechanism they anticipate and do not build.
- **Bernardy et al., *Linear Haskell*, POPL 2018 (arXiv, pp. 1–36, read; §5's case studies
  skimmed).**
  - This version has no treatment of exceptions. The "linear values may leak on an exception"
    discussion is from later material, which I have not read: unchecked.
  - Linearity is conditional on the result being consumed, and is vacuous on divergence (p. 15).
  - An error exit that hands the token back in another state is shown at p. 25:
    `Either (Socket Bound) (Socket Unbound)`.
  - For us:
    - an accounting stated only at normal termination says nothing about raise. That is why
      `frame_unwind_leakfree` is a theorem of its own;
    - an error exit returning its token is an exit of our `E`.
- **Unchecked** (cited by the above, not read): Fähndrich et al. on Sing# (EuroSys 2006; the
  implicit close at any point is the nearest prior to "an abort ends every lend"); Mazurak, Zhao
  and Zdancewic, F° (TLDI 2010); Ahmed, Fluet and Morrisett, λURAL (ICFP 2005); Biernacki et al.
  2020 and Xie et al. 2022 on named handlers.

## 9. Kernel cost and kill criteria

**Kernel cost under the growth discipline:**

- `VTy`/`CTy` formers: 0. `CDerives` rules: 0. New indices on `CDerives`: 0.
- Relation and model changes: 0. `fundamentalC`, `adequacyC` and `adequacyD` are unchanged.
- New:
  - `FDerives`, 13 derived rules, with the elaborated term as index;
  - `elab`, 13 cases, each a composition of Core rules;
  - `accounting`, 13 cases;
  - O1, a weakening by a dead binder, one case per `CDerives` rule, no inversion. A rule
    later added to `CDerives` costs one O1 case beside its `fundamentalC` case. This is the
    "substitution over derivations" the growth rules ask to cost: about 90 mechanical cases,
    once.
- Estimate (hypothesis): about 1,500 lines of Lean when proved, most of it in `elab` and the
  machine steps of `accounting`.
- If frames move into `Core/`, they land with a SPEC entry and enter `CDerives`-checked programs
  through the checker, which builds `FDerives` derivations for frame forms in core text.

**Kill criteria:**

| criterion | status |
|---|---|
| a lemma needs two constructs at once | did not fire (§4), checked in advance of the proofs |
| two successive patches for individual exit kinds | did not fire: there are no per-exit-kind rules. Exits are one `exit` and one `catch`; loops use the same head-of-row rule. |
| a target needs a new relation rather than derived rules or one former | did not fire on my reading: `FDerives` is derived rules elaborating into `CDerives` (the `ADerives`/`KDem` precedent), and `Rets` is a unary property of runs that reads no type and no resource. **The user should confirm the reading.** If `FDerives` or `Rets` counts as a new relation, this criterion fires. |
| the algebra hard stop | did not fire: no effect equation is touched. Raise is §19's, by construction. |

## 10. SPEC draft entry (not in `SPEC.md`)

> ## 42. Entry 41 — frames with typed exits
>
> ### Motivation
> #632. Control flow with several exits, each returning every lend, is the kernel's work; the
> elaborator's joins (§41 R2/R3), LoopLend (§14), `mutCap` and `escapingWriter` did it by hand.
>
> ### Types
> No new former. `Fr Σ Π E A ≜ Π ⊸ F_Σ (Π ⊗ (A ⊕ ⊕E))`, with `Π` a tuple of slots (`Ref A` with
> a destructor, `Mut @a A`) and `E` an exit row: a stack of payload types, innermost catcher
> first. A block is `!U(B ⊸ Fr Σ Π E A)`.
>
> ### Typing
> `FDerives Δ Γ Φ Π e Σ E A` with the rules `core`, `exit`, `bind`, `case`, `catch`, `under`,
> `use`, `lend`, `new`, `loopCount`, `loopIter`, `callBlock` and `sub` (the table of
> `docs/research/frames-with-exits.md` §1.2). Each elaborates to a Core term (`e`), and
> `FDerives.elab` makes it a `CDerives` derivation at `Fr Σ Π E A`. Raise and abort are
> operations of `Σ`. The rules hold the slots under `[then]` finalisers or lend them through the
> unwinding borrow constants, so an unwind is §19's.
>
> ### Theorems
> - `FDerives.elab`; `frame_sound` (`fundamentalC`); `frame_adequacy` (`adequacyD_obs`).
> - `accounting`: every run of a frame on slots `π` that reaches a value reaches `(π, x)`, and
>   every stop resumes into a term of which the same holds (`Rets`, coinductive).
> - `frame_unwind_leakfree`: a handled frame program runs to a value at the empty memory,
>   whether or not it raised.
> - `core_conservative`: `core N` runs as `N`.
>
> ### Baseline
> No change to `CDerives`, the relation, the machine or `Paper/`. The corpus, goldens, counts,
> `mut-combos` and the renaming check are unchanged until the elaborator rules are converted
> (later steps, under the rule table).
>
> ### Open
> - Higher-order blocks generic in `Π` (D4).
> - A borrow block over a div loop as per-use lends (D3).
> - The counted loop at an effect row (`count_try` is pure).
> - Suspension inside a lend (T1, #172).

## 11. Decision menu

1. **D1. Adopt the design as the step-2 target** (prove O1, `elab`, then `accounting`, in that
   order). Or ask for changes first.
2. **D2. The kill-criterion reading** (§9). Is a derived-rules judgment with an elaborated-term
   index (`FDerives`) plus a unary run invariant (`Rets`) acceptable? The alternative that has no
   judgment of its own is the 13 rules as `CDerives` theorems at derived terms, as
   `Core/AffRules.lean` does for `Aff`. That alternative loses the single induction, and so
   requirement 1. The alternative with one former is `CTy.frame Π E C` with a relation clause.
   It costs about 20 match arms and a relation case, and buys a conservativity theorem that is
   a statement about the relation, not by construction.
3. **D3. Borrow blocks over loops.**
   - (a) `lend` only: one lend, total loops only. Div loops keep LoopLend.
   - (b) per-use lends of the place (§5), which deletes LoopLend and changes a borrow block's
     extent.
   - (c) both: `lend` where the body has no div loop, (b) where it does.
4. **D4. Callees that call writing blocks.**
   - (a) frame definitions instantiated per `Π` and retyped by the kernel (letPoly-style).
   - (b) a place-row variable in `blockTy` (row polymorphism over slots).
   - (c) `Aff` blocks (§22), as the place model's A2 suggested.
5. **D5. A1 in this stage.** Frames as designed accept a resuming operation *between* uses of a
   place, since Core already allows an owner in a continuation. Either keep that, which goes past
   the issue's "A1 stays refused", or restrict the frame row to abortive operations and `Div` for
   now. The restriction would refuse frames for programs that thread `let mut` across `await`
   today, so it could not be the end state without regressing the corpus.
6. **D6. Exits: positional (de Bruijn) or named.** Positional is what the Lean states and what
   makes `catch` remove a head. Named exits would need a row lookup, and a `catch` that removes
   by label would bring back comparison by name.

## 12. Reproduction

- `lake build Frames`: succeeds, with the `sorry` warnings in `Frames/Theorems.lean`.
- `#print axioms` of `swap_derives`, `not_returns_swap`, `nested_derives`, `core_embeds` and
  `sumTy_get`: within `[propext, Classical.choice, Quot.sound]`.
- `grep -cE '^\s*sorry\s*$' experiments/Frames/Frames/Theorems.lean` counts the enumerated
  `sorry`s (30), each after its note.
