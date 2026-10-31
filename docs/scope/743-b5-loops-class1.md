# Scope: #743 B5 (step 1′) — loops as the kernel's `Div`, with class 1, rebuilt from main

Step B5 of #743's build plan, approved by the user on 2026-10-30. This is a scoping note and changes
no code. The build is phase 2, after review.

**Kernel target.** The class-1 kernel rules, rebuilt on main with their proofs:

- a lend held across operations resumed in scope (the handler resumes tail-resumptively, inside the
  lend's world);
- a lend held across a loop's `tick` when the runtime or `div_fuel` drives the loop in scope.

The lemma family is `cwp_lendM`, `cwp_lendI`, `withbor2L_compatX` (with `withbor1L_compatX`) and
`handleT_compatC`. `fundamentalC`, `adequacyC` and `adequacyD` are extended to the changed rules
**with their statements unchanged**, and no `PinLaw` is involved. Surface loops elaborate to `Div`
(SPEC §14, *The effect `Div` in the kernel*), so P1–P4's class-1 shapes are typed by those rules.

**Decided, not reopened.**

- #743's plan, B5 row (user, 2026-10-30, "I approve the plan").
- Grades take the M1 shape (user, 2026-10-22, on #654). World is a lifetime bound on `eff` and
  replaces #654's `c : Bool`.
- Correct over consistent (user, 2026-10-21, on #646): "If we need to refuse we need to refuse."
  Programs that ran only through the elaborator's per-observation lend may move to refused by the
  kernel, each listed. They go to `corpus/pending/`, not `reject/`.
- `imm` is linear with a derived copy (#746 decision 3, 2026-10-29). The checker inserts the copy
  at a split (#756).
- `class1-revive`, `b2-div` (#646) and `call-grade` (#654) are not resumed, merged or
  cherry-picked. They were read for their proofs and their elaboration. Everything below is
  rebuilt from main.

**Sources read.**

- #743: the consolidation (§1–§7), the 10-29 plan, the "Step 1 progress" comment, the 10-30 spike
  and build plan, and `~/repos/scratch-archive/743/plan.md`.
- #644 and #646 with all their comments, including the 10-21 amendments and the 10-31 close.
- #649 and #654 with their comments, including the M1 decision and the 10-31 close.
- `~/repos/scratch-archive/grades-lit/report.md` §2.4 and §5. `~/repos/673-work/design.md` v3 §1.1
  (#673, closed with the abandoned rewriter plan) is read as evidence only.
- SPEC on main: §14 (*Borrow scopes over loops, per observation*, *The effect `Div` in the
  kernel*), §29 (R1 under `PinLaw`), §41, §47–§52.
- On main: `Frontend/Elab/LoopLend.lean`, `Frontend/Check/DerivedCopy.lean`, `Core/Classes.lean`,
  `Core/PinLaw.lean`, `Core/Fundamental.lean`, `Core/DivHandle.lean`, `Backend2/Convert.lean`, and
  `docs/scope/` for the format.
- `call-grade`: `Core/EffLend.lean`, `EffWp.lean`, `EffDefs.lean`, `EffBorrow.lean`, `EffFin.lean`,
  `DivHandle.lean`, `DivRuntime.lean`, `DivPrograms.lean`, `Fundamental.lean`.
- `b2-div`/`b2-main`: `Frontend/Sugar.lean` (the `Div` elaboration) and
  `Frontend/Elab/DivPlacement.lean`.
- `class1-revive`: its merge resolutions, `Backend2/Convert.lean`, `Frontend/Check/ImmCopies.lean`
  and SPEC §62–§66.
- `750a-kernel`: the `git diff --stat` against main, plus `Types.lean`, `EffRules.lean` and the
  pin template.

**Measurements** (read-only, no build). These are `bcc check`/`bcc run` with binaries already
built:

- main: `borrow-core-spec42` at 6d47bf7c. Its Frontend and Backend are identical to 32bbf65d.
- b2-div: ddc1d6de.
- call-grade: about ae50262c.
- class1-revive: built 10-29 from its working tree.

Every B5 result below is a **prediction**: there is no B5 binary.

---

## 1. The kernel rules

### 1.1 What class 1 is in the kernel: premises, not new constructors

#654 added **no `CDerives` constructor**. Its constructor lists are identical to `b2-div`'s:
`CDerives` 96, `CDerivesP` 99, `CDerivesAt` 96. Class 1 is a grade on operation signatures,
together with premise changes on five existing rules. B5 keeps that shape. The brief asks for every
new constructor: there are none. Every changed rule is listed below with its new premise.

`b2-div` changed nothing in `Core/`, `Support/` or `Paper/`. Every kernel part of class 1 is
#654's. Main already has `Div` in the kernel from #567:

- `divEff`, `tickSig`, `iterate`, `div_fuel`, `reify`, `cwp`, `Closing`;
- `effHandleT` and `handleT_compatC` in their ungraded forms;
- `effHandleL` (§51);
- `runtime_every_run` and `divFuel_every_run` at `[tickSig]`.

### 1.2 The grade under M1: the world axis only

M1 is a product of axes: count, position, storage and world. Class 1 needs **only world**:

- `Row.Lend` already reads count as `o.q = .lin` (must resume = count 1).
- Position and storage enter no class-1 premise.

B5 adds the world axis and nothing else. Count, position, storage and pending finalisers stay as
they are on main (`Qual`, `B = 0`, `fin`). The carrier is the two-point `{ℓ_op ⊑ ⊤}`, which is what
#654's `c` stood for. Whether the carrier is two points or a general lifetime is box Q1.

```lean
-- Core/Types.lean
/-- The world a stop's continuation is owed at (M1's world axis): `op`, the stop's own world,
or `top`, every extension of it. `[sub]` moves `top → op` only. -/
inductive World where
  | op
  | top
  deriving DecidableEq

structure OpSig where
  n : UInt32
  i : UInt32
  q : Qual
  A : VTy
  B : VTy
  fin : CTy := .ret .unit
  wld : World := .top          -- after #750 A's `rc` if A lands first (box Q4)

inductive CTy
  | eff (n i : UInt32) (q : Qual) (A B : VTy) (fin : CTy) (wld : World) (C : CTy)
  -- …
```

```lean
-- Core/EffDefs.lean (OpEnt gains `wld : World := .top`)
def Owed (en : OpEnt) (ls ls' : List SRec) (ρ : WRes) : Prop :=
  match en.wld with
  | .top => Ext ls ls' ρ
  | .op => ∀ x, x ∈ ls' ↔ x ∈ ls
-- contShare and KapRelT (EffRules.lean): `∀ ls', Ext ls ls' ρ →` becomes `∀ ls', Owed en ls ls' ρ →`
```

```lean
-- Core/EffFin.lean
def OpSig.LeF (o o' : OpSig) : Prop :=
  o.Sig o' ∧ (capB o.q o.B = true → FinLe o.fin o'.fin) ∧ (o.wld = .op → o'.wld = .op)
-- OpEnt.Le gains `∧ (en.wld = .op → en'.wld = .op)`
```

```lean
-- Core/EffBorrow.lean
def Row.Lend (S : Row) (x : LifeVar) : Prop :=
  ∀ o ∈ S, o.n ≠ 0 ∧ ¬ VFree x o.A ∧ (∀ Δ a, VOutlives Δ a o.A) ∧
    (o.abort = true ∨ (o.wld = .op ∧ o.q = .lin ∧ ¬ VFree x o.B ∧ ∀ Δ a, VOutlives Δ a o.B))
theorem Row.Unwind.lend {S : Row} {x : LifeVar} : S.Unwind x → S.Lend x
```

```lean
-- Core/DivDefs.lean, Core/DivFuel.lean
def tickSigW (w : World) : OpSig := ⟨divEff, 0, .lin, .unit, nextTy, .ret .unit, w⟩
abbrev tickSig : OpSig := tickSigW .top
abbrev divFuelTy (S : Row) (A : VTy) (w : World := .top) : VTy   -- inner row `tickSigW w :: S`
```

### 1.3 The changed rules, verbatim

The rules differ from main only in the marked premise.

```lean
  | divFuel {Δ Γ} {w : World} (S : Row) (A : VTy) (hS : ∀ o ∈ S, o.n ≠ divEff)
      (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val divFuelV) (.val (divFuelTy S A w))                        -- w: new
  | withbor1U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Lend x)  -- was S.Unwind x
      (hdc : closedAt 0 d = true) (hd : CDerives Δ Γ d (.val (.lolli (.ref A) .unit))) :
      CDerives Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S))
  | withbor2U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Lend x)                     -- was S.Unwind x
      (hdc : closedAt 0 d = true) (hd : CDerives Δ Γ d (.val (.lolli (.ref A) .unit))) :
      CDerives Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))
  | effHandleT {Δ Γ Γ₁ Γ₂} {Hr Hc e : Expr} {S SN : Row} {E : List (Qual × VTy × VTy)}
      {fs : Nat → CTy} {n : UInt32} {w : World} {A R : VTy}                              -- w: new
      (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁)
      (hHr : Hr.ValFormIn Γ₁) (hHc : Hc.ValFormIn Γ₁)
      (hc : CDerives Δ Γ₁ (.pair Hr Hc) (.val (.tensor (retTy S A R) (ansesTy S SN R E))))
      (hn0 : n ≠ 0) (hnd : n ≠ divEff) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
      (hCN : w = .op → ∀ o ∈ SN, o.wld = .op)                                            -- new
      (he : CDerives Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs w ++ S) A))) :           -- w: new
      CDerives Δ Γ (hndExpr n (E.map Prod.fst) (.pair Hr (tailTuple E 0 Hc)) e)
        (.comp (CTy.effOf S R))
```

**Rules that do not change:**

- `reify`: its tick stays at `tickSig` (world `top`). A stored loop owes its continuation at every
  extension, so no class-1 lend crosses a `reify`. This is what keeps class 2 (`gen-self-borrow`,
  `for-lend-resumes`) out.
- `effHandleL`, `effHandleV` and `effHandleVB` handle `top` rows. `Row.ofEff` defaults to `.top`.
- `iterate`.
- `withbor3U`, `withloadU`, `sliceBorrowMU` and `sliceBorrowIU` **keep `S.Unwind x`**, which is
  #654's own Open. Section 4 lists what this leaves refused.

The same premise changes appear in `CDerivesP` (generated from `scripts/pin/CDerivesP.tmpl.lean` by
`scripts/gen-pin.py`) and in `CDerivesAt` (`Core/Tied.lean`). Box Q3 covers what that does to
`PinLaw`.

### 1.4 Each rule's proof: source, port or rework

On main, `EffWp.lean`, `EffDefs.lean`, `EffBorrow.lean`, `Wp.lean`, `DivRuntime.lean`,
`DivPrograms.lean` and `DivIterate.lean` are unchanged since #654's merge-base 8dbe5892, by
`git diff`. `wpG`, `contShare`, `OpEnt`, `KapRelT`, `effWp`, `cwp`, `Closing`, `RowLe` and `Ext`
are byte-identical. The semantic proofs therefore port. The rework is the grade carrier, together
with the main-only users of the changed definitions.

| rule / lemma | source (`call-grade`) | on main | verdict |
|---|---|---|---|
| `wpG_M_frameAt`, `wpG_I_frameAt` (6.65/6.64 at a given lifetime) and the re-derived `wpG_*_frameX` | `Core/EffWp.lean:616`, `:267` | `frameX` only (`EffWp.lean:363`, `:75`) | **port as is** |
| `lendM_frame`, `lendI_frame` | `Core/EffLend.lean:365`, `:973` (new file, 1354 lines) | absent | **port**; re-key `OpTab.LendAt` from `call = true` to `wld = .op` |
| `cwp_lendM`, `cwp_lendI` (a lend across ticks at a `cwp` row) | `EffLend.lean` section `:693`/`:733`; `:1167` | absent | **port**, re-keyed |
| `withbor2L_compatX`, `withbor1L_compatX` (the `withbor2U`/`withbor1U` cases at `Row.Lend`) | `EffLend.lean:788`, `:1264` | unwind forms `withbor2U_compatX`/`withbor1U_compatX` (`EffBorrow.lean:281`, `:452`) | **port**, re-keyed |
| `Owed`, `Owed.*` | `EffDefs.lean:191` | absent | **rework**: match on `wld`, not on `call : Bool` |
| `contShare_ungraded`, `kapRelT_ungraded`, `KapRelT.owed` | `EffDefs.lean:316`, `EffRules.lean:736`, `DivHandle.lean:341` | absent | **port**; hypothesis `en.call = false` becomes `en.wld = .top` |
| `OpSig.LeF`, `OpEnt.Le`, `Row.gradeAt`, `rowLe_gradeAt`, `effWp_gradeAt` | `EffFin.lean:130`, `:996`–`:1017` | `LeF` without the grade | **rework**: M1's order; `OpSig.Sig`'s tuple changes again under #750 A's `rc` |
| `handleT_compatC` with `hCN` (the graded `effHandleT` case) | `DivHandle.lean:711` | ungraded (`DivHandle.lean:680`) | **rework**: `Row.ofEff … w`; `effHandleL`/`DivHandleLast.lean` (main only, `KapRelT` users at `:423`–`:878`) take the mechanical edits `class1-revive`'s merge shows (`Ext.refl` → `Owed.refl _`, `KapRelT.ext` → `KapRelT.ext rfl`) |
| `divFuel` graded, `runtime_every_run w`, `divFuel_every_run` | `DivFuel.lean:373`, `DivRuntime.lean:392`, `DivPrograms.lean:190` | at `[tickSig]` | **port** |
| `rtMain`, `runtime_main_every_run`, `io_rt_every_run`, `IORun.rt_every_run` (the runtime drives `main` in scope) | `DivRuntime.lean:418`, `:522`, `:542`; `Frontend/Check/Externs.lean:511` | absent; main's `IORun` has `loops`, not `rt` | **rework**: `Externs` and `IORun` changed on main |
| `withbor1U`/`withbor2U` callers | — | `DeclLend.lean:202` (main only, §42) | **edit**: `Sf_unwind.lend` |
| every `.eff` pattern (7 arguments become 8) | — | ~123 sites, plus main-only `Classes.lean:245`, `Dtor.lean:190`, `DivHandleLast` | **mechanical** |

The parts of main that the brief names, and what each needs:

- #746's `Tok` and `OwnFree`, `DerivedCopy` (`Classes.lean`), StackK (Backend2 only) and the §42
  lend (`DeclLend.lean`) do not enter the class-1 semantics. They need only the `.eff` arity and
  `DeclLend`'s premise.
- The `aff`→`cancel`, `Persistent`→`Ctx.Banged`, `Drop`→`OwnFree` and `Weak`→`Cancels` renames do
  not occur in `EffLend.lean`. They hit #654's edits to `DivHandle`, `EffFin` and `EffRules`.

### 1.5 The theorems

| theorem | statement |
|---|---|
| `fundamentalC` (`Fundamental.lean:593`), `adequacyC` (`:776`), `adequacyD` (`Demonic.lean:312`), `fundamentalD`, `total_every_run` | **unchanged**. The new cases are `withbor1L_compatX`, `withbor2L_compatX`, graded `handleT_compatC` and graded `divFuel` |
| `fundamentalC_pin`, `adequacyD_pin` | unchanged (box Q3) |
| `runtime_every_run`, `divFuel_every_run` | each gains `(w : World)`; the main-statement instance at `.top` is kept under the old name, so existing callers are unchanged |
| `runtime_main_every_run`, `io_rt_every_run`, `IORun.rt_every_run` | new. They state that `main`'s loop, driven by the runtime at world `op`, never gets stuck |
| conservativity: `contShare_ungraded`, `kapRelT_ungraded`, `rowLe_gradeAt`, `effWp_gradeAt` | new. At `wld = .top` the relation is today's |

---

## 2. The elaboration of surface loops to `Div`

### 2.1 What B5 builds, and what main already has

**On main:**

- the kernel `Div`;
- `TExpr.iterate`, `TExpr.divFuel` and `TExpr.reify` with their `TDerives` cases;
- `effHandleT` and `effHandleL`;
- `bounded_fix` at a resuming row, which Backend2 compiles (§48);
- the old backend's `expandIter`.

**Only on branches, so rebuilt here:**

- the core-text forms `iterate[…]` and `reify[…](res)`, and the `div` row spelling, in
  `Parser`/`Syntax`/`Print`;
- `TTied` emission of `iterate` and `reify`;
- the checker's emission of `handle_tail` and `handle_last` (`effHandleT`, `effHandleL`);
- the elaboration itself (`b2-main` `Sugar.lean:1047`–`:1960`);
- the deletion of `lendBind`, `lentDef` and `Env.lendCall`.

### 2.2 The rule table

There is one rule per construct, over the whole loop grammar of SPEC §14 *The loop node*. A rule
places its sub-terms by the rules for their own constructs and decides nothing about borrows.
There is no fallback and no trial elaboration.

`b2-div` decided whether a body performs `Div` by elaborating it once with a `machine` flag and
restoring the state, and `forYield` did the same with a `tryCatch`. Both are **replaced** by the
predicate `performsDiv`, read from the syntax and the inferred types. The `tryCatch` is a fallback,
and is not ported.

| # | construct | kernel form | reads |
|---|---|---|---|
| D0 | a div body (`performsDiv`: a `while`/`loop`, a drain, a `for` over a looping generator, or a direct-style call whose type is at a row holding `Div`) | the body at `F_{tick, Σ}(B ⊕ R)`; a terminal `return v` is `inl v` | syntax, inferred callee types |
| D1 | `while c { M }; N` | `iterate(step, s₀)`. The step is `<turn & close>`. The turn is `case c { false → inl (inl j) \| true → M; inr s′ }`. The close hands back the residual. The state is the variables of `c`, `M` and `N` by name, plus the held sources and capabilities | names in scope, their inferred types |
| D2 | `loop { M }; N` | D1 without the test. The join type is `0` when there is no `break` | as D1 |
| D3 | `for x in it`, over an iterator or a stored generator (a drain) | `iterate` holding `it`; the turn observes `it.1`, the close is `it.2` | the source's inferred type |
| D4 | `for x in D`, over data: a count, a view `fam (imm/mut)`, `&a`, an owned array of a persistent type, a sized iterator, or `imm 'a (array A)` / `mut 'a (array A)` (see D4′) | body not `performsDiv`: today's total counted loop (§16), unchanged. Body `performsDiv`: `bounded_fix` at the row `div, Σ` (#646 amendment: "a counted loop with `Div` in its body is `bounded_fix` at the row"). A lend around the source is held across the ticks, and the kernel decides | the source's type |
| D4′ | `for x in v` with `v : imm 'a (array A)` (or `mut`) | a reborrow through `withload` (the existing `borrow imm *v { 'y, w -> … }` sugar, `Sugar.lean:3760`) to the view `array_imm 'y A`, then D4 over the view. When the body does not tick, no lend crosses a tick. When it ticks, `withloadU` stays `Row.Unwind` and the kernel refuses | the source's type |
| D5 | `for x in g(e)`, over a generator | `handle_tail` (`effHandleT`) when every exit resumes and nothing raises; otherwise `handle_last` (`effHandleL`, §51), around `g`'s direct call. A clause whose work is `performsDiv` is a div body of its own (D0) | the clause's exits (syntax) |
| D6 | a direct-style call of a div function | inlined at the caller's row: the call, then `case inl/inr`. On `inr`, close what is held and leave with the residual (D9) | the callee's type |
| D7 | a loop used as a value (`U(Loop B R)` expected) | `reify_res[B, R, Σ](res)(thunk M)`, with `res` the closed residual function | the expected type |
| D8 | `main` that loops | `reify` of the body, driven by the runtime (`rtMain`). When the runtime is the only `Div` handler, the body runs in place at world `op` | `main`'s inferred row |
| D9 | `break`, `continue`, `return` | `inl (inl j)`, `inr s′`, `inl (inr a)`, each after closing the held sources, innermost first. The residual hands back **exactly what the loop holds, by name**. `b2-div`'s `eAbort` matched capabilities by type (`capOf`); that is not ported (box Q6) | names |
| D10 | a borrow block whose body is a div body; `let r = &x` before a loop; a lend at a direct-style call of a div function | the kernel's lend (`withbor1U`/`withbor2U`, or the slice/`withbor3U`/`withload` forms) with its callback a div body at the enclosing row. The elaborator neither splits it per turn nor refuses it. The kernel accepts (`Row.Lend`, class 1) or refuses (`Row.Unwind`) | the place's type |
| D11 | loops inside handler clauses and effect bodies | D0–D10 at the clause's row. A `[handle]` around a ticking computation is `effHandleT`/`effHandleL` only (§14) | — |
| D12 | an `imm` borrow used at every turn | threaded by name in the state (D1). Each turn is a split between the body's use and the back edge's `inr s′`, and #756's rule inserts the kernel copy there (section 3) | — |

**Tick placement.** The `iterate` primitive ticks at every back edge itself (§14). `b2-div` added a
forward placement: a tick at every move to a point, plus one tick before a terminal reached before
any point (#644 step 0). This keeps `div_fuel` budgets and observation counts equal to today's.
`sim_loop` (`b2-main` `DivPlacement.lean:240`) proves that placement over a transcription of runs,
but not over the emitted terms (§52 Open there). Whether to keep it is box Q5.

**World.** The elaborator writes rows with `tick` at `top`. Two places then type at world `op`:

- the runtime's clause (D8);
- `effHandleT`'s handled row when `hCN` holds (D5, D10).

Both are reached only through `[sub]` (`top → op`, `OpSig.LeF`). The kernel checks every one of
these premises: `Row.Lend`, `hCN`, and `reify`'s `top` tick. A wrong world in an emitted type
therefore makes the checker refuse the term. It never makes the checker accept one it shouldn't.
Where #654's frontend inferred the grade (`Row.lendB`) has not been read yet; see box Q2.

### 2.3 What it reads

The elaboration reads the syntax and the types that inference gives (`TCx`). It reads no borrow,
lifetime or linearity judgement, and makes none. Every such judgement is the checker's, made on the
core term that the elaboration emits.

The brief says "checked facts only". No pipeline exports checker facts to the elaboration: inference
runs before checking, on every branch. Box Q7 covers how this scope reads that requirement.

### 2.4 What retires

The per-observation lend in `Frontend/Elab/LoopLend.lean` retires. That code is kernel work done in
the elaborator: it decides each lend's extent per turn.

- `lendBind` (`:388`): splitting a borrow block per stretch and per `for` body.
- `lentDef` (`:495`): rewriting a div function over a borrow to take its owner.
- `Env.lendCall` (`:257`): rewriting `f(b)` to `f(&t)`.
- The error sites `iterError` (`:297`, `:342`) and the rename check (`:424`), with `lentDef`'s
  refusals (`:518`).

What stays:

- `lendLet` (`:439`), `let r = &x; S` as `borrow imm x { r -> S }`. It is used by programs with no
  loop.
- `escapeError` (`:290`), which every borrow block reuses (`Sugar.lean:3777`–`:4009`).

LoopLend shrinks to about 140 lines.

Also retired:

- The per-body `unfold` state machine for loops (`mWalk`, `mLoop`, `divMachine`, `divBody`). It is
  replaced by D0–D9.
- `forDataDiv` (`Sugar.lean:4935`), now D4.
- `io_hwf` (`:5197`), now D5.
- The spine rule S1 (`Sugar.lean:156`): a `while` is no longer confined to the spine, because a
  loop is a term, not a machine state.
- The refusal of `&a` or an owned array with a resuming body (`:4566`–`:4574`, `:4931`), now D4 and
  D10: the kernel decides.

**Docs made stale and edited:**

- SPEC §14, *Borrow scopes over loops, per observation*, and its *Elaboration* and *One state
  machine per body*.
- `Core/PinDerives.lean:17` and `:531`, which describe R2 as what "Core's elaboration (`LoopLend`)"
  requires. These are doc comments in a generated file. Box Q3 covers them.
- `lib/lend.bc:12`.

`lib/lend.bc`'s library (`loop_lend_*`, `pull_lend_*`, `array_each_imm`) is user code over
`unfold`, and stays.

---

## 3. The `imm` re-read at each turn

`iterate`'s step is `!U(S ⊸ …)`. `bangThunkV` asks every live slot to be `!A` (`Ctx.Banged`), and
`imm` is not persistent (`Core/Persistent.lean:49`). So an `imm` borrow cannot be a free variable
of the step, used again at each turn. It is threaded in the state, D12:

1. The turn binds it by name from `s`.
2. The body uses it, and the back edge `inr s′` mentions it again. Those are the two parts of a
   split.
3. #756's rule (`Frontend/Check/DerivedCopy.lean`, `Env.copyVars`) fires at that split and inserts
   `copyE`. The result is a `CDerives.copy` node at `Imm @a A` (or `CDerives.arrCopy` under
   `bangE` at `[Imm @a A]`) in `copy_derives`' shape (`Core/Classes.lean:342`).
4. The close component shares the turn's context: `&` is additive, so there is no split there. It
   drops the borrow by its derived drop.

So every copy is a rule node that `CDerives` licenses. The checker decides where it goes, by the
split's masks, and the elaborator inserts none.

`DerivedCopy` (`Core/Classes.lean:313`) is exactly:

```lean
inductive DerivedCopy : VTy → Prop where
  | imm (a : Lifetime.Life) (A : VTy) : DerivedCopy (.imm a A)
  | arrImm (a : Lifetime.Life) (A : VTy) : DerivedCopy (.fam (.imm a A))
```

It holds for every `A`. The `imm` borrow of a declared (`Tok`-owning) value is therefore
`DerivedCopy`. Copying it copies the borrow, not the owned value: #746 decisions Q11, "borrows of
declared types stay copyable".

A **pair** holding a borrow is not `DerivedCopy`. An example is `reject/lend-escape`'s
`q : imm 'x array i32 ⊗ i32`. Such a pair stays refused at the split. Widening `DerivedCopy` is a
kernel change, and is not in B5 (`746-imm-copy.md` §4).

> **STOP (linearity).** Stop on anything that makes a value copyable or droppable that was not, or
> that weakens a linear or owed obligation. B5 adds no copy, no drop and no persistence. A copy
> appears only where #756's rule fires, at `DerivedCopy`, and the kernel checks it.
>
> This was E1's failure on `class1-revive` (commit 4ad53247, `Frontend/Check/ImmCopies.lean`). E1
> was a source rewrite before checking (`Val.copyImm`, renaming to `x#d.i`). It copied an `imm`
> binder that the program had declared with `linear x <- M`, and let the copies drop.
>
> On main, the binder `linear x <- M` is gone (SPEC.md:10439), and the copy is a node of the typed
> term. If any program needs a copy that #756's rule does not insert, it is refused and listed in
> section 4. It is never repaired.

---

## 4. Programs whose acceptance changes

**Mechanisms:**

- **K-lend**: class 1 accepts a `withbor1U`/`withbor2U` lend whose callback ticks or performs at a
  row with world `op`, driven in scope by the runtime or a tail-resumptive `effHandleT`.
- **K-copy**: the `imm` re-read is #756's derived copy (section 3).
- **K-unwind**: a lend that stays `Row.Unwind` refuses a tick in its callback. These are the slice
  borrows (`&a` of an array, `borrow mut a` of an owned array), `withbor3U`, `withloadU`, and a
  buffer or literal place, which has no lend form at a row at all.
- **D-elab**: the `Div` elaboration with no lend involved.

The "main" and "branch" columns are measured. The "B5" column is predicted.

### 4.1 Accepted on main, accepted under B5 (the mechanism changes)

These seven ran through LoopLend's per-observation lend. They are exactly #646's set, less the
programs in 4.2. `class1-revive` measured each one on main's file.

| program | main | `class1-revive` | B5 | mechanism |
|---|---|---|---|---|
| `corpus/axes/borrow-across-loop` | i32[60] | i32[60] | i32[60] | K-lend + K-copy |
| `corpus/hygiene-borrow-loop` | i32[207] | i32[207] | runs | K-lend + K-copy |
| `corpus/lend-mut` | i32[604] | i32[604], Backend2 native | runs | K-lend (`mut`, no copy) |
| `corpus/lend-server` | i32[65] | i32[65] | runs | K-lend at the call + K-copy |
| `corpus/lend-shadow` | i32[105] | i32[105] | runs | K-lend + K-copy |
| `corpus/sugar/lend-block` | accepted | accepted | accepted; `.core.bc` rewritten | K-lend + K-copy |
| `corpus/sugar/lend-let` | accepted | accepted | accepted; `.core.bc` rewritten | K-lend + K-copy |

### 4.2 Accepted on main, refused or at risk under B5 (new refusals)

| program | main | `class1-revive` | B5 | why | recovered by |
|---|---|---|---|---|---|
| `corpus/lend-copy` | runs | refused 37:3: `borrow mut a { … while … }` over an owned array cannot hold its lend across the tick | **refused** → `pending/` | K-unwind (slice) | **B2** W-tick (`lendRT`) at `LendForm` fam; waits on #750 |
| `corpus/lend-pipeline` | runs | refused: "operation 1.0 has two signatures" | **refused** → `pending/` | One operation name is used at two signatures, once LoopLend's rewrite no longer separates them. This is not a borrow rule, and I have not verified its cause | **none** in the plan (box Q8) |
| `corpus/lend-config` | runs | refused 40:3: "`stdin` is not consumed in its scope" | **at risk** | `class1-revive`'s close did not hand back the capability that was lent. Under D9 (hand back by name) it is expected to run | B5 itself, by D9 as a rule. If D9 does not cover it, it is a listed refusal → `pending/`, with no per-program fix |
| `corpus/lend-div`, `corpus/sugar/lend-div` | runs / accepted | refused 42:7: "expected `i32`, but this has type `i32 + 1`" | **at risk** | `class1-revive` §62: a borrow block whose body is a direct div call was not typed at `B ⊕ R`. D10 composed with D6 places it at `B ⊕ R` | B5 itself, by D6/D10. If not, a listed refusal → `pending/` (`lend-div.core.bc` deleted) |

The firm count is 2 new refusals; 3 more are at risk. None is hidden, and none is repaired
program by program.

### 4.3 Refused on main, accepted under B5

| program | main | branches | B5 | mechanism |
|---|---|---|---|---|
| **P1** `scratch-743/t/p01-while-handler-op` | refused 3:1 (`escapeError`, per-observation rewrite) | `class1-revive`: i32[20], Backend2 native | **accepted** | K-lend: `&mut c` lent across `walk`'s ticks (runtime, `op`) and across `count`'s tail-resumptive `tick()` (`effHandleT`, `hCN`) |
| **P3** `scratch-743/t/p05-iter-borrowed-vec` | refused 20:12 (`iterError`) | `class1-revive`: refused 20:24, "`*` … has type `1`" | **accepted**, i32[6] (box Q9) | D4′: `imm 'a (array i32)` was not data (`dataSrcOf`, `Sugar.lean:2633`), fell to the drain path and gave `x` type `1`. D4′ makes it data. The loop is total, so no tick crosses the lend |
| `reject/lend-iter-borrow` | refused 28:5 (`iterError`) | `class1-revive`: i32[60] | → corpus | K-lend + K-copy |
| `reject/while-in-counted-for` | refused 10:5 (S1) | all three: i32[4] | → corpus | D-elab (S1 retired) |
| `reject/for-data-gen-loop` | refused 15:19 (S2) | all three: i32[30] | → corpus | D-elab |
| `pending/for-view-local` (#491) | refused 14:1 (`lentDef`) | all three: i32[3] | → corpus | D-elab: the counted walk over a view is total |
| #545 matrix RW, RL, RG | refused (S1, S2) | b2 and `class1-revive`: 241 | run | D-elab |
| new: `lend-imm-copy`, `lend-call-copy`, `lend-nest3`, `lend-depth3`, `lend-order3` (`call-grade`), `lend-shadow-core` (`class1-revive`) | absent | accepted | added, accepted | K-lend (+ K-copy); depth 3 and order 3 |

The matrix goes from 18/25 on main to 21/25.

`reject/lend-div-two` is refused at 14:14 by `lentDef`. It has `lend-div`'s gap: once D6/D10 type
it, it either moves to the corpus or is refused by the kernel, and the result is listed then.

### 4.4 Refused on main, still refused under B5

| program | main | B5 (predicted, from `class1-revive`'s measurement) | why | recovered by |
|---|---|---|---|---|
| **P2** `p02-lines-print`, `x02-lines-noprint`, `x02b` | refused 4:1 (`lentDef`); `x02b` 8:14 (`iterError`) | **refused** 11:11 (`x02b` 6:11): the borrow's place (a buffer or literal) has no unwinding form at a row | K-unwind (buffer place) | **B3** view case for the reborrow. **No plan step names a buffer/literal lend form at a row** (box Q8) |
| **P4** `p06`, `p06b` | refused 8:5, 9:5 (S1) | **refused** 6:3: `&a`'s slice lend cannot cross the inner `while`'s tick | K-unwind (slice) | **B2** W-tick at `fam` |
| #545 matrix AW, AL, AG | refused (S1, S2) | refused 9:3, the same as P4 | K-unwind (slice) | **B2** |
| `pending/for-buf-borrow` (#501) | refused 16:55 (`iterError`) | refused 16:11 (buffer place) | K-unwind | **B3**, plus a buffer lend form (box Q8) |
| `pending/parse-recover-gen` | refused 136:7 (`iterError`) | refused 136:5 (literal place; a generator holds the view) | K-unwind | **B3**, **B7** |
| `pending/aoc-2020-07` | refused 34:1 (`lentDef`) | refused 91:27: "`memo` consumed in one arm" | #492 | none in the plan (#492) |
| `pending/state-machine-audit` | refused 72:1 (`escapeError`) | refused: "operation 1.0 has two signatures" | as `lend-pipeline` | none (box Q8) |
| `reject/lend-escape` | refused 20:11 (`escapeError`) | refused 23:34: "`q` used twice … `imm 'x array i32 * i32` is not persistent" | a pair is not `DerivedCopy` (section 3) | none; stays a reject, message changes |
| `reject/lend-shadow` | refused (rename check) | refused 23:53 on a type error that the old check hid | — | stays a reject; `-- expect:` changes |
| `reject/gen-self-borrow`, `reject/for-lend-resumes` (P5) | refused | unchanged | class 2: `reify`'s tick is `top` | **B7** |

**Message-only changes:**

- `pending/{callbacks-in-data, map-div-fold, operator-reconcile}`: the type text `U (delay …)`
  becomes `F[div] (… + 1)`.
- Probably also `pending/{gen-adapters-io, gen-digits, gen-lines, gen-lazy}`. Unverified: the
  branches predate main's #746 wording.
- `reject/for-free-bound`.

**Unchanged** (measured on all four binaries): the `lendLet`-only programs (`data-particles`,
`data-turnstile`, `for-data`, `iter-mut`, `print-borrowed-array` and 4 book blocks),
`scope-loop-lend`, `lend-lib-*`, `lend-owner-*`, `for-in-if-lend`, `mut-lend-arm`,
`text-lend-lifetime`, `async-lend-slots`, `for-view-effect-copy` and `gen-pipeline`. The 34
"spanning lend" workaround notes keep their results: their programs do not use the per-observation
lend. No book doc-test block uses it (0 of 114).

**Counts:**

| change | count |
|---|---|
| keep running by a new mechanism | 7 |
| firm new refusals | 2 |
| at risk | 3 programs plus `reject/lend-div-two` |
| newly accepted | P1, P3, 3 rejects, 1 pending, 3 matrix cells |
| new programs | 6 |
| still refused | P2, P4, AW/AL/AG and 7 corpus programs |

**P1–P4, expected:**

| probe | B5 |
|---|---|
| P1 | **accepted** |
| P2 | refused (B3, plus a buffer lend form) |
| P3 | **accepted** (via D4′; refused as on `class1-revive` if D4′ is not taken) |
| P4 | refused (B2) |

`class1-revive` had P1 accepted and P2–P4 refused. B5 differs on P3 only.

---

## 5. NOT-do list

- **No `PinLaw` change.** `Core/PinLaw.lean`'s `LendFrame`, `LoopFrame` and `PinLaw` keep their
  statements and fields. The one edit B5 is forced into is box Q3/Q4: the arity of three `OpSig`
  literals.
- **No relaxed (asserted) rule.** Neither `lendR` nor `lendLoopR` is emitted. Nothing new is
  asserted.
- **No `LifeNatural`, and no stack-indexed relation.** These lines are closed by the user.
- **No change to `fundamentalC`, `adequacyC`, `adequacyD`, `fundamentalD` or `total_every_run`.**
- **No class 1 for `withbor3U`, `withloadU` or the slice borrows.** These are #654's Open, and the
  plan puts them at B2 and B3.
- **No checker or elaborator decision of a guarantee** (STOP: KERNEL WORK). The elaborator neither
  refuses on borrow grounds nor splits a lend per turn (#646 amendment; 0c800b7 reverted).
- **No per-program elaboration case.** The `tryCatch` fallback and the `machine` trial are not
  ported (section 2.2).
- **No copy outside #756's rule.** No `ImmCopies`, no `Val.copyImm`.
- **No Backend lowering that decides ownership.** Every Backend2 drop and copy names its
  `DropRule`/`CopyRule` and passes Lint's premise check (#746 step 3).
- **No count, position, storage or finaliser axis of M1.** These are later units.
- **No grading of user effects beyond what `effHandleT`'s `hCN` checks.** #654 Open.
- **Not resumed, merged or cherry-picked:** `class1-revive`, `b2-div`, `call-grade`. `750a-kernel`
  is not touched.

## 6. Tempting shortcuts, and the STOP each raises

| shortcut | STOP |
|---|---|
| Keep LoopLend's per-observation lend for the programs `Div` refuses (`lend-copy`, P2, P4) | **KERNEL WORK.** It decides a lend's extent in the elaborator. The programs go to `pending/` with the lend and the tick, as #646's amendment says |
| A checker copy where the copy rule does not apply: copying the pair in `lend-escape`, copying the state wholesale, or a copy for a non-`DerivedCopy` slot | **LINEARITY.** Refused and listed, never repaired |
| A grade special case for one handler (`count` in P1), or a world chosen per program | **KERNEL WORK.** World comes from `[sub]` and the kernel's premises only; one rule for every `effHandleT` |
| Fold B2's W-tick (`lendRT`) in early to recover P4, `lend-copy` or AW/AL/AG | **SCOPE.** B2 waits on #750 and is asserted under `LendFrame`; B5 asserts nothing |
| Give `sliceBorrowMU/IU` or `withbor3U` `Row.Lend` "since the proof is the same" | **SCOPE plus a new proof.** #654 left them Open; frames for them are not proved. Stop, report, do not assert |
| Give `reify`'s tick world `op` so that P5 or `gen-self-borrow` types | **SOUNDNESS.** A stored loop is owed at every extension (class 2, B7) |
| Repair `lend-config` or `lend-div` by a case that matches their shape | **PRINCIPLED.** Only D6, D9 and D10 as written. Otherwise they are listed refusals |
| Lower a stored loop (`reify` other than `main`'s) by a state machine where the program does not keep the generator | **COMPILER-FIRST.** Machines are the fallback only where a stored κ is real (decision 2026-10-21) |
| Port `class1-revive`'s Backend2 `genIter`/`genIterK` with their untyped `.drop` | **#746.** Every drop names its rule and is listed in `scripts/PinSites.lean` |
| Keep `b2-div`'s `eAbort` matching of residual capabilities by type | **PRINCIPLED.** The residual hands back what was lent, by name (D9) |

---

## 7. Lowering

**Backend2 on main does not compile `Div`.** `Backend2/Convert.lean:2722` sends `iterate`, `divFuel`,
`reify`, `effHandleT`, `lendR` and `lendLoopR` to `outside`. Loops compile today only as the
elaborator's `unfold` machines: §45's η-thunk `nuEta`, the runtime drive of `main`'s loop, and §48's
`bounded_fix` (`genFix`, `:1864`). B5 must therefore lower `Div` from the checked term, or every
looping program leaves Backend2's fragment ("compiler never stale").

**From the checked term**, under N2's effect erasure (§47, resume-once = call):

- `iterate` becomes one function per node, its back edge a tail call (`class1-revive`'s `genIter`,
  re-done under #746's drop discipline).
- `tick` under the runtime clause is erased and answered *next* (`tickTm`). That is the handler law
  for a tail-resumptive clause, read from the `effHandleT`/runtime node in the typed term.
- `main`'s `reify`, with the runtime as its only `Div` handler, runs in place (`convMain`). Its row
  is `F[div]` at world `op`.
- `effHandleT`/`effHandleL` around a ticking computation use §47's erasure (`handle_tail` → call;
  `[handle-last]` as §51's lowering, already on main for non-ticking bodies).
- `withbor1U`/`withbor2U` at a `Row.Lend` row are §29 *Lowering*: the lent cell is never moved
  (`genLendU` gains the row).
- A **stored loop** (a `reify` that is not `main`'s) is a state machine (`genIterK`). This is the
  sanctioned fallback where the program keeps the loop (§49).
- `div_fuel`'s kernel constant stays outside Backend2. The elaboration never emits it; the
  library's `div_fuel` over loop codata (`lib/div.bc`) is ordinary code.

**Replaced:** the per-body `unfold` machine lowering at elaborated loops (§45 `nuEta` and §49's
drive at `main`'s loop). Both remain for hand-written `unfold` and `pull`.

**The old backend:** `iterate` stays `expandIter` (`Backend/Clos/Convert.lean:894`). Each loop gains
one indirect call (`counts.expected`).

**Lint and StackK.** B5 changes neither `Backend2/Lint.lean` nor StackK:

- `Driver.lean:479` (`StackKHandOver`);
- `Convert.lean:1403` (`genStackMach`);
- `Syntax.lean:185`–`:211`;
- `Interp.lean:664`.

New drop and copy sites register through the existing `DropRule`/`CopyRule` and
`scripts/PinSites.lean`. **Conflict:** #746's recent commits touch exactly these files (c7ad8b21,
cf512491, e8024b25, 57d2cdf3), and 750a adds `effThenDiv`/`effAwait` nodes that Backend2 must also
send `outside` or lower. If B5 needs any Lint rule change, STOP and report.

---

## 8. The smallest change and its accounting

| file(s) | change | reason |
|---|---|---|
| `Core/Types.lean` | `World`; `OpSig.wld`; `CTy.eff … wld …` | M1 world axis (1.2) |
| `Core/EffDefs.lean`, `Core/EffRules.lean` | `OpEnt.wld`, `Owed`, `contShare`/`KapRelT` over `Owed`, `OpSig.ent`, `Row.ofEff … w`, `contShare_ungraded`, `kapRelT_ungraded` | 1.2, 1.4 |
| `Core/EffFin.lean` | `OpSig.LeF`, `OpEnt.Le`, `Row.gradeAt`, `rowLe_gradeAt`, `effWp_gradeAt` | `[sub]` `top → op` |
| `Core/EffBorrow.lean` | `Row.Lend`, `Row.Unwind.lend`, `Row.Lend.resumes/unwind` | 1.2 |
| `Core/EffWp.lean` | `wpG_M_frameAt`, `wpG_I_frameAt`; `frameX` re-derived, statements unchanged | 1.4 |
| `Core/EffLend.lean` (new) | `lendM_frame`, `lendI_frame`, `cwp_lendM`, `cwp_lendI`, `withbor1L_compatX`, `withbor2L_compatX` | 1.4 |
| `Core/DivDefs.lean`, `DivFuel.lean`, `DivHandle.lean`, `DivHandleLast.lean`, `DivRuntime.lean`, `DivPrograms.lean` | `tickSigW`; `divFuelTy … w`; `KapRelT.owed`; graded `handleT_compatC`; `effHandleL` mechanical; `runtime_every_run w`; `rtMain`, `runtime_main_every_run`, `io_rt_every_run`; `divFuel_every_run w` | 1.3, 1.5 |
| `Core/Fundamental.lean` | the premises of 1.3; the `fundamentalC` cases | 1.3 |
| `Core/Tied.lean` | `CDerivesAt` premises | mirrors `CDerives` |
| `scripts/pin/*.tmpl.lean` → `Core/PinDerives.lean`, `Core/PinFundamental.lean`, `Frontend/Check/{TDerives,TExpr,TLife}.lean` (generated) | the premises of 1.3; the `fundamentalC_pin` cases call the same compat lemmas | box Q3 |
| `Core/PinLaw.lean` | **only** `pinAwaitSig`/`pinYieldSig`/`pinRaiseSig`'s anonymous-constructor arity | box Q4 |
| `Core/DeclLend.lean:202` | `Sf_unwind.lend` | premise change |
| every `.eff` pattern (Core, Frontend/Check, Backend2) | one more argument | arity |
| `Frontend/Check/Externs.lean` | `IORun.rt`, `IORun.rt_every_run` | D8 |
| `Frontend/{Parser,Syntax,Print}.lean`, `Frontend/Check/TTied.lean` | core text `iterate[…]`, `reify[…](res)`, `div` row; the checker emits `iterate`/`reify`/`handle_tail`/`handle_last` | 2.1 |
| `Frontend/Sugar.lean` | D0–D12; delete the loop machine, `forDataDiv`, `io_hwf`, S1 | 2.2, 2.4 |
| `Frontend/Elab/LoopLend.lean` | delete `lendBind`, `lentDef`, `lendCall`, `iterError` | 2.4 |
| `Backend2/Convert.lean`, `Backend2/Driver.lean`, `scripts/PinSites.lean` | section 7 | lowering |
| `SPEC.md` | a new entry (version after #750 A's, 1.22 if A lands first, fixed at merge); §14's per-observation lend and machine sections rewritten; §29 cross-reference | spec-first |
| `corpus/` | section 4's moves; 6 new programs; the 12 programs' comments; `axes/README.md`; `-- expect:` and `-- now:` lines | section 4 |
| `corpus/*.expected` | `counts` (+1 indirect per loop, old backend); `counts-backend2` (rows for 4.2 out, 4.3 in); `erasure-backend2`; `handled` (`main` gains the `Div` name); `kinds` | measured diffs on `class1-revive` |
| `corpus/sugar/*.core.bc` | up to 22 pairs; `lend-div.core.bc` deleted | the emitted core changes. Each pair is re-checked, not just regenerated |
| `docs/kernel-usage/census.tsv`, `docs/kernel-usage.md`, `scripts/AxiomCheck.lean` | the new lemmas | census |
| `book/src/guide/iteration.md` ("Borrows and loops"), `book/src/elaboration/divergence.md`, `docs/internals/elaboration/divergence.md` | prose | docs |

**Theorem statements changed:** `runtime_every_run` and `divFuel_every_run` gain `w`, with the old
statements kept as the `.top` instances. `handleT_compatC` gains `w` and `hCN`.

**Hypotheses added:** `hCN`, a premise of the `effHandleT` rule, not of any theorem's conclusion.
It is non-vacuous at `w = .top`, where it is trivial and gives today's rule.

**Not changed:** any `fundamentalC`/adequacy statement, `PinLaw`'s fields, `LendFrame`,
`LoopFrame`, `fundamentalC_pin`, `adequacyD_pin`.

## 9. Phase-2 checks

1. `lake build` clean. Iterate with targeted `lake build Core.EffLend` and similar.
2. `scripts/check-hygiene.sh`: no `axiom`, `sorry`, `native_decide`, `implemented_by`, `opaque`,
   `partial` or `unsafe`.
3. `scripts/check-pins.sh`: the generated pin files match their templates.
4. `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]` for `fundamentalC`, `adequacyC`,
   `adequacyD`, `fundamentalC_pin`, `adequacyD_pin`, every lemma in 1.4, and
   `runtime_main_every_run` and `io_rt_every_run` (`scripts/AxiomCheck.lean`).
5. The golden and corpus checks: `scripts/check-corpus.sh`, sugar pairs, clause kinds, handled
   names, cell classes, both `counts` files, erasure, the Backend2 corpus, and native.
6. P1–P4 run by hand against section 4's table.
7. One `make gate`, run only as `~/repos/scripts-local/gate-serial.sh gate` from the worktree,
   once, at the end.

## 10. Open questions

> **Q1. World carrier: two points or a lifetime?** The M1 decision (2026-10-22) says "a lifetime
> bound `ℓ_r` on `eff`, in `CTy.all` form". The later design pass (#673 v3, review item S4)
> narrowed this to `{ℓ_op, ⊤}`: "a handler can never name an inner lend's lifetime, so intermediate
> worlds never fire". #673 was closed with the rewriter plan.
> *Recommendation:* two points, `World = op | top`. It is exactly what class 1 reads, and it is a
> sublattice of the lifetime form, so widening later is conservative. **Needs the user** if the
> decision's literal `ℓ_r` is meant.

> **Q2. Who writes the world?** The kernel checks it (`Row.Lend`, `hCN`, `reify`'s `top` tick).
> It is reached by `[sub]` at the runtime's and `effHandleT`'s nodes.
> *Answer from standing decisions* ("handlers default to the strictest mode that works",
> 2026-10-22; "compile from checked facts"): the checker types the node at `op` when its premises
> hold, and the elaborator writes `top` throughout. Phase 2 reads `call-grade`'s `Row.lendB` first.
> If it turns out that the elaborator must choose the world, STOP.

> **Q3. `CDerivesP` mirrors the class-1 premises, which widens what `LendFrame` quantifies over.**
> `LendFrame` (`PinLaw.lean:91`) quantifies over callbacks `M` with
> `CDerivesP Δb [⟨V, true⟩] M …`. `CDerivesP.ofC` (`PinFundamental.lean:36`) embeds `CDerives`, so
> `CDerivesP`'s `withbor1U`/`withbor2U` must take `S.Lend x` too. Then `LendFrame`'s domain includes
> callbacks that hold class-1 lends inside. Its statement text is unchanged, but the asserted
> schema covers more derivations.
> *Recommendation:* mirror. B1 stated `LendFrame` as uniform over every `CDerivesP` derivation ("a
> lend nested in `M` is part of `M`'s derivation"), and class 1 is proved, not asserted.
> **This is a widening of an assertion, and so the user's call.** The alternative, keeping
> `CDerivesP` at `Unwind`, breaks `ofC` for programs mixing R1 and class 1. If the user says no,
> STOP.

> **Q4. Collision with #750 A on `OpSig`/`CTy.eff`.** 750a adds `rc : Bool` in the same slot
> (`OpSig`'s 7th field, `CTy.eff`'s 7th argument, `Row.ofEff`'s argument after `fs`, which becomes
> `cs : Nat → Bool`). It also changes `OpSig.Sig`, edits `PinLaw.lean`'s three `OpSig` literals and
> the `CDerivesP` template, and adds SPEC §29a.
> *Answer:* B5 starts from main, adds `wld` after `fin`, and takes #750 A's layout at merge: `wld`
> after `rc`, a textual merge in every `.eff` pattern, `scripts/pin/*.tmpl.lean` and SPEC. The SPEC
> version is fixed at merge.
> The `PinLaw.lean` edit is the three literals' arity (`, .top⟩`), and nothing else. It is checked
> by a diff showing that only those three lines change. Any other `PinLaw.lean` edit is a STOP.

> **Q5. Tick placement.** The `iterate` primitive's back-edge ticks alone, or also `b2-div`'s
> forward placement? The forward placement keeps today's `div_fuel` budgets and observation counts.
> `sim_loop` proves it over a transcription of runs, not over the emitted terms.
> *Recommendation:* the primitive's ticks only (an inlined direct-style call ticks through its own
> `iterate`). That is per construct, simplest, and true to SPEC §14's primitive. Programs whose output depends on a
> `div_fuel` budget (`io-fuel`, `lend-lib-each`, `lend-lib-loop`, `sugar/hof-*`, `surface-defer`)
> are re-measured and listed if their output changes.
> *Answer from standing decisions* ("correct over consistent"): observation counts are not a
> guarantee, so matching old traces is not a reason to keep extra ticks. **Confirm with the
> user**, since outputs may move.

> **Q6. The residual at an exit (D9).** Handing back by name what the loop holds and what was lent
> replaces `eAbort`'s match by type. `lend-config` (and `lend-div`) test it. If D9 cannot express a
> program's residual, that program is a listed refusal.

> **Q7. "Reads checked facts only."** No pipeline exports checker facts to the elaborator.
> Inference runs before checking, and every branch read the inferred types.
> *Reading taken here:* the elaboration reads syntax and inferred types, decides no borrow,
> linearity or lifetime fact, and the checker judges everything on the emitted core. If the user
> means that the elaboration must run after a checking pass, that is a pipeline change outside B5.
> **Needs the user.**

> **Q8. Refusals with no recovery step in the plan.**
> - `lend-pipeline` and `state-machine-audit`: "operation 1.0 has two signatures".
> - A buffer or literal place lent at a row: P2, `for-buf-borrow`, `parse-recover-gen`. B3 covers
>   only the view-reborrow half.
> - `aoc-2020-07`: #492.
>
> These are listed and parked in `pending/`. *Recommendation:* note the buffer place under B3's
> scope, and the signature refusal on #743 for the foreman. The cause of "two signatures" has not
> been verified.

> **Q9. D4′ is in B5's grammar.** `for` over `imm 'a (array A)` was misclassified as a drain on
> every branch. That is a gap in "for over data over the whole grammar", which item 2 asks for, so
> D4′ is a rule for a type, not a case for P3. If the reviewer reads it as outside B5, P3 stays
> refused (20:24) and is listed.

## STOPs carried into phase 2

- **Q3:** `LendFrame`'s domain widens.
- **Q4:** `PinLaw.lean` needs more than the literal arity.
- **Q2:** the world is chosen by the elaborator.
- A class-1 port that needs a changed `fundamentalC`/adequacy statement, or a new hypothesis on
  them.
- A program accepted only with a copy that #756's rule does not insert.
- A Lint rule change.
- A stored-loop machine where the program does not keep the loop.
- Any frame for `withbor3U`, slices or `withload`.
