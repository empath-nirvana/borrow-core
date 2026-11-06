# #835: only the scheduler catches a resuming operation performed under a live lend

The user's decision (#835, 2026-11-06): while a borrow is open, only the scheduler may catch a
resuming operation whose handler receives `κ` as a value. This document states that restriction
exactly, checks it against `main`, and says what it means for the scheduler. The Lean is in
`Core/Chain/Restrict835N.lean` (the restriction) and `Core/Chain/SI/ErwpK.lean` (the relation it
is read in). `scope-835-kripke-stop.md` is the cost map this follows.

## 1. Why a restriction is needed

`erwpK` (`ErwpK.lean`) lets a stop choose its floor: `contShareK` owes the continuation at the
worlds the entry allows at some `f ≤ lo`, `lo` the floor of the world the stop is at. A stop under
a live lend at `A` takes `f = A`. That is below the lender's floor, because the lender's Mut Frame
owes its stops only along `ExtP A` (`kw_owed_fold`, `scope-835-kripke-stop.md` §1, addition 1).

A handler that receives `κ` as a value reads it at `vN`'s `U`, along `ExtP` at its own floor (E10,
`scope-835-public.md` §5.1). If the stop chose a lower floor, `κ` is owed at fewer worlds than `U`
asks. So a handler that reads `κ` at `vN` must never see a stop taken under a live lend between the
`perform` and the handler. That means a lend frame inside `κ`.

A lend outside the handler is no problem. Its key is in the handler's own world, and the stop's
floor is the handler's. This covers a task that holds a borrow from its context across an `await`
(`spawn_in`, §28's BOXED-κ with `CtxOutlives`): that lend frame is not inside `κ`.

## 2. Tail and last handlers: unaffected

**Verdict: yes.** `handleT_compatN` and `handleL_compatN` already hold for operations performed
under a live lend. They do not read `κ` at `vN`, so they need no restriction.

The evidence at today's relation (Lean):
- `handleT_compatN` (`Core/Chain/HandleT835N.lean`) and `handleL_compatN`
  (`Core/Chain/HandleL835N.lean`) take the handled computation's `SemJN` with no premise about how
  it was typed.
- `fundamentalN_all` (`Core/Chain/Fundamental831N.lean`) applies them to every `CDerives`
  derivation. That includes handled computations built from `ctx791`'s constants, whose
  `Row.Suspend` callbacks perform the handled operation under the live lend.
- Their proofs (`erwp_handle_tail`, `erwp_handle_last`, `last_contN`) open the stop and resume `κ`
  in place after the clause's own run. They cancel it at the entry's own cancel obligation
  (`OpTabN.Sub`). Neither reads `κ` at `vN` (`scope-835-kripke-stop.md` §2, consumers).

At `erwpK` (by reading; the handlers are a later unit):
- A tail clause resumes `κ` at the world its answering function's value is posted at.
- A post keeps the location typing and the view and may only lower the floor (`KW.Post`).
- `KW.owed_of_post` (Lean) shows that such a world is owed **at every floor the stop could have
  chosen**. `KW.Owed` keeps `FoldInv f` ("if it held at the stop, it holds here") rather than
  asking for it, so a handler resuming in place needs no knowledge of `f`. The view premise
  `ConsistentX` at `κ`'s share is what `erwp_consistentPA` gives today.
- A last clause's work and exit are the same, and its cancel is at the entry's own obligation.

So the restriction is needed only for `effHandleV` and `effHandleVB`, the two forms that pass `κ`
to a clause as a value. `reify` waits on the same E10 step (#835).

## 3. The restriction

`Sched : UInt32 → Prop` is the set of the scheduler's operation names. At `Goal791SchedN` the
scheduler handles one name, `n₀` (`SchedOKNLe.names`), so `Sched = (· = n₀)`.

**(S1) The lends' rows** (`Row.SchedOnly`):

```lean
def Row.SchedOnly (Sched : UInt32 → Prop) (S : Row) : Prop :=
  ∀ o ∈ S, o.abort = false → Sched o.n
```

- Every resuming operation a lend's callback may perform, and so stop at under the live lend, is a
  scheduler operation.
- Abortive operations are unrestricted: a raise owes no continuation (`raiseStopK` reads no world
  and no floor).
- It is read on each `Const791` constant's callback row (`Const791.row`, `Const791.SchedOK`).
- `Row.Suspend` itself is unchanged.

**(S2) The program's handlers** (`Expr.HndAvoids`), read off the frames a term holds, which
`main` already computes (`Expr.hin`, `Core/HandledNames.lean`):

```lean
def Expr.HndAvoids (Sched : UInt32 → Prop) (e : Expr) : Prop :=
  ∀ n, Sched n → ¬ e.hin.HasHnd n
```

- The program, and every constant's finaliser, holds no handler frame of a scheduler name anywhere
  in it.
- A `handle` whose name is not a literal may be of any name (`HIn.top`), so it is refused. Every
  rule of `CDerives` that types a `handle` concludes at `hndExpr n …`, whose name is a literal.
- `hndAvoids_hndExpr` and `not_hndAvoids_hndExpr` are the two cases (Lean).
- `steps_frame_of_node`, the run invariant at `hin`, carries the condition to every handler frame a
  run of the program reaches. That is the form the relation needs.

**`Restrict835 Sched cs e`** is (S1) and (S2) together, on a program's constants and its term.

**Why it is placed there, and not in a typing rule.**
- **A premise on `CDerives.effHandleV`/`effHandleVB`** (`n ∉ Sched`) would be a new side condition
  on two of `main`'s rules. It would refuse kernel programs `main` accepts today (any
  `effHandleV` at a reserved name). That is a stop under the brief, and it is not needed.
- **A coordinate of the judgment's index** (the #798 consolidation) is the form this should take
  once that record exists. `main`'s `CDerives` has no index today
  (`Core/Fundamental.lean`, `inductive CDerives : LifeCtx → Ctx VTy → Expr → Jdg → Prop`), and a
  new judgment is refused by `scripts/check-judgments.sh`.
- **On the program and its constants**, as above. This is what is chosen. `Goal791SchedN`'s new
  statement will carry `Restrict835 (· = n₀) cs e₀`, which is decidable on the program.
  `FundamentalN`'s effHandleV/VB cases read `¬ Sched n` from it, and every other case passes it to
  the sub-terms.

**What (S2) refuses beyond what is needed.** The term does not say which rule typed a `handle`, so
(S2) also refuses `effHandleT` and `effHandleL` at a scheduler name (`not_hndAvoids_hndExpr`). By §2
they would be sound there.
- So a `for` over a generator that holds a borrow across its `yield` is outside the restriction:
  the lend row names `Yield` (S1), and the `for` is a `handle` at `Yield` (S2).
- Only the judgment knows which rule typed a `handle`. Telling tail and last clauses apart from the
  others needs the index coordinate above. With it, (S2) becomes "no `effHandleV`/`effHandleVB` at a
  scheduler name".

**How the interpretation reads it** (a later unit; `tabN`/`entN` at the world):
- A row entry's order at the stop's world `x` is `KW.Owed x f y ρ`, plus `f = x.lo` when the name is
  not in `Sched`.
- The lend frames produce stops at `f < lo` only at rows meeting (S1). So a `[handle]` at a name
  outside `Sched`, which (S2) guarantees, receives `κ` at its own floor, which is E10's reading.

**Cancel rows are not restricted.** The restriction reads no cancel row.
- A continuation captured under a live lend is caught only by the scheduler. Its cancel runs are at
  a table inside the scheduler's own (`SchedOKNLe.fin`: `en.fin = some (cancelOblN Φ T₁)`,
  `T₁.Sub T`), which is `Goal791SchedN`'s existing requirement.
- A handler inside a lend's callback that cancels its own `κ′` runs that cancel inside the
  callback. The resuming operations of that run reach the callback's row, which is (S1)'s row.
- Abortive operations, in a row or in a cancel row, are unrestricted.
- So effectful cleanup on cancel is untouched.

## 4. Checked against `main`

**`main`'s `CDerives`** (`git show origin/main:Core/Fundamental.lean`):
- Every lend constant runs its callback at a pure row (`withbor1/2/3`, `withload`,
  `sliceBorrowM/I`, `axWithbor*Ty`) or at a `Row.Unwind` row (`withbor1U/2U/3U`, `withloadU`,
  `sliceBorrowMU/IU`).
- `Row.Unwind` (`Core/EffBorrow.lean`) asks `o.abort = true` of every operation.
- So no resuming operation is ever performed under a live lend in a program `main` types. (S1)
  holds of every such row at every scheduler (`Row.schedOnly_of_unwind`, Lean).
- (S2) is not a premise of any `main` rule. `main`'s judgments, theorems and checker are unchanged.

**`main`'s R1 under `PinLaw`** (SPEC §29, `CDerivesP.lendR`, `Row.ResumeOC`):
- R1 lets a `mut` lend's callback perform resuming operations (`await`, `yield`, a marked
  cancellable wait). Any handler of `CDerivesP` may catch them, `effHandleV` and `effHandleVB`
  included.
- The restriction does not touch `CDerivesP`, `lendR`, `PinLaw` or the checker. So `main` refuses
  nothing it accepts today.
- **But every R1 program in `main`'s corpus is of the shape (S1)+(S2) excludes.** Each one's
  operation under the lend is caught by an in-program handler that receives `κ` as a value:

| Corpus program | Operation under the lend | Caught by |
|---|---|---|
| `async-r1-generator`, `async-r1-local-borrows`, `async-r1-step-lend`, `async-r1-effects`, `async-r1-nested`, `async-r1-cancel`, `async-r1-drain` | `yield` | a stored generator (`U (pull …)`): the elaborator's `handle` whose clause keeps `κ` (`effHandleV`, `Frontend/Elab/Effects.lean`, "stored generator") |
| `async-cancel`, `async-bank-inbox`, `async-logged` | `await` | `lib/async.bc`'s `spawn`/`spawn_logged`: BOXED-κ (`effHandleVB`, `rEffHandleB`) |
| `async-r1-cancel-finaliser-writes` | `perform[1.0]` | `handle_with[1]` in the core text (`effHandleV`), which cancels `κ` |

So the restriction refuses no program `main` accepts, because R1 and `PinLaw` stay. It also means
the stretch's proved constants cannot take any of these programs over from R1 as they are written.
Each would need its `yield`/`await` caught by the top-level scheduler, with no stored generator, no
`spawn` and no `handle_with` around the lend. If the stretch were meant to replace R1, the
restriction would refuse all eleven. That is a reading of the corpus and the elaborator, not a Lean
configuration. Whether it is the coverage the decision intends is the user's to confirm.

## 5. The scheduler's typing

**Today.** `Goal791SchedN` takes `SchedOKN` as a hypothesis on the scheduler value
`hndVal n₀ qs hr hs`. That is a contract (the premises of `erwp_handle_le` at the empty outer
table, each clause getting the stopped task as `KapRelN`), not a typing. `hs_schedOKN`
(`Core/Chain/PoolSpawnN.lean`) proves it for one scheduler, `HS`.

**Under the restriction** the scheduler is the only handler of a scheduler name. (S2) excludes
every `CDerives`-typed `handle` at those names, so the scheduler is never typed by `CDerives`.
What follows:
- **The kernel.** The scheduler stays outside the judgment, at the program's top. It meets
  `SchedOKN`, restated at `erwpK` in the handlers unit: each clause gets the stopped task's
  Kripke stop at a floor it does not know. The pool's moves (park, resume, cancel, reorder) resume
  in place, which `KW.owed_self` and `KW.owed_of_post` give at every floor.
- **The library.** `lib/async.bc`'s `spawn`, `push`, `run_until_empty` and their `_logged`/`_in`
  forms, and the elaborator's stored generators, are `CDerives`-typed handlers. Under the
  restriction they cannot catch an operation performed under a live lend. A task that lends across
  `await` would run under a top-level scheduler, not under `spawn`. A generator that lends across
  `yield` could not be stored or driven by `for`.
- **The surface.** The scheduler becomes a top-level handler supplied with the program, like §34's
  platform as the outermost handler. Its `SchedOKN` is proved once in Lean, as `hs_schedOKN` is for
  `HS`. A user-written scheduler would need its own Lean proof of `SchedOKN`: it is trusted
  library code with a proof, not checked code.
- **Typing it** would need a clause type for "`κ` owed at an unknown floor": a value former whose
  only eliminations are to store it and to resume or cancel it at the handler's own world. Those
  are `SchedOKN`'s moves, typed. It is not designed here.

## 6. What this unit built, and what is left

Built (`ErwpK.lean`, `Restrict835N.lean`, all in `scripts/AxiomCheck.lean`, axioms within
`[propext, Classical.choice, Quot.sound]`):

- **`erwpK`** over world-indexed location families, tables and posts. The Kripke stop chooses its
  floor (`contShareK`'s `∃ f ≤ lo`), and a table at a lower floor allows fewer stops
  (`opTableK_floor_le`).
- **The embedding**: `erwp_eq_erwpK` and `erwp_opTableN_eq_erwpK`, at any floor bound.
- **The generic laws** at `erwpK`: `erwpK_val`, `erwpK_of_rwp`, `erwpK_bindR`, `erwpK_mono`,
  `erwpK_bind`, `erwpK_frame_plain`, `erwpK_perform`, `erwpK_garbage`, `erwpK_le`, `erwpK_det` and
  `erwpK_shift`.
  - Each `erwp` law is proved again from its `erwpK` law at `Unit`, which shows that the old
    statement is that instance: `erwp_val_of_K`, `erwp_of_rwp_of_K`, `erwp_bindR_of_K`,
    `erwp_mono_of_K`, `erwp_bind_of_K`, `erwp_frame_plain_of_K` and `erwp_perform_of_K`.
  - Bind and the frame read their continuation premise at every world (DNB's Lemma 3). Along the
    post order they ask for the same location family and a table allowing no more stops.
- **The typed world `KW`** (`Θ`, `c`, `lo`):
  - `KW.Post` (same `Θ` and `c`, a floor no higher);
  - `KW.Owed` (`ExtP f`, `Θ.OK`, a consistent view, a floor no higher, `FoldInv f` kept), with
    `KW.owed_self`, `KW.owed_of_post`, `KW.Owed.trans` and `KW.Owed.foldInv`;
  - `kw_owed_fold`: the Mut Frame's fold premise, from `KW.Owed` at the lend's floor.
- **The restriction**: `Row.SchedOnly`, `Expr.HndAvoids` (at `Expr.hin`), `Const791.SchedOK` and
  `Restrict835`, with `Row.schedOnly_of_unwind`, `hardestRow_schedOnly`, `hin_hndExpr`,
  `hndAvoids_hndExpr` and `not_hndAvoids_hndExpr`.

`KStopSpike835N.lean` keeps its local copies. Its `erwpK_M_frame` is the template for the `mut`
frames unit, which re-proves it at `ErwpK`'s floor-choosing stop. The lender's stop chooses the
borrowed stop's floor.

**Not done here**: `cN`, `vN`, `gN` and `tabN` at worlds, and every producer. Note for the frames
unit: the borrowed run's view puts `ℓ` at `A`, so `KW.Owed`'s view clause at the borrowed share
reads the inner world's view, not the lender's.

**Estimate for what is left** (one agent run ≈ 1 unit):

| Item | Units |
|---|---|
| The 13 `mut` frames at the floor-choosing stop (`kw_owed_fold`, the inner view) | 1–2 |
| The `imm` fold analogue, the anti-frame share transfer and their 16 frames | 1–2 |
| The remaining mechanical producers (31 on the path), handlers included | 1 |
| `vN`'s `U` at a floor, `vN_extR` along `ExtP`, `gN` monotone, `tabN`/`entN` at `KW` with `Sched` read (§3), `SchedOKN` at `erwpK` | 1–2 |
| Re-pointing the 111 typed and compatibility lemmas | 2–3 |
| E10, `effHandleV`/`VB` at names outside `Sched`, `reify`; `Goal791SchedN` with `Restrict835` | 1 |
| Posts across a lend's exit (`scope-835-kripke-stop.md` §5) | 1–3 |
| **Total** | **8–14** |

`KW.Post`'s `y.lo ≤ x.lo` is §5's route 1. Under route 1, an in-program `[handle]` at a name
outside `Sched`, around a lender that has already exited a lend, sees stops at the lender's lowered
floor, so E10 does not reach it. Route 2, raising the floor for values whose cells lie above it,
would make `KW.Post` keep the floor. Neither is derived. **Not derived; obstruction not verified.**
Without that item the total is 7–11.
