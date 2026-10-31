# Scope: #743 B5 (step 1′) — loops as the kernel's `Div`, with class 1, rebuilt from main

Step B5 of #743's build plan, approved by the user on 2026-10-30. This is a scoping note and changes
no code. The build is phase 2, after review.

**Kernel target.** The class-1 kernel rules, rebuilt on main with their proofs:

- a lend held across operations resumed in scope (the handler resumes tail-resumptively, inside the
  lend's world);
- a lend held across a loop's `tick` when the runtime or `div_fuel` drives the loop in scope.

The lemma family is `cwp_lendM`, `cwp_lendI`, `withbor2L_compatX` (with `withbor1L_compatX`) and
`handleT_compatC`. `fundamentalC`, `adequacyC` and `adequacyD` are extended to the changed rules
**with their statements unchanged**, and no `PinLaw` field is used. `CDerivesP` mirrors the changed
premises, so `LendFrame`'s domain grows with them (box Q3, decided). Surface loops elaborate to `Div`
(SPEC §14, *The effect `Div` in the kernel*), so P1–P4's class-1 shapes are typed by those rules.

**Decided, not reopened.**

- #743's plan, B5 row (user, 2026-10-30, "I approve the plan").
- Grades take the M1 shape (user, 2026-10-22, on #654). The world is a lifetime bound on `eff`,
  and replaces #654's `c : Bool`. B5 builds the world axis only, and the larger rework this needs
  is accepted.
- The answers to the first review (boxes Q1–Q9). Q3, `CDerivesP` mirroring class 1, rests on the
  decision that PinLaw's schemas are uniform in depth and holder.
- Written fixes (user, 2026-10-31): a program that should work may be refused only if it has a
  written fix, named in the refusal message, or if a named later step recovers it (section 4).
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

### 1.2 The grade under M1: the world axis, as a lifetime bound

This section follows the M1 decision (user, 2026-10-22): "world as a lifetime bound `ℓ_r` on `eff`,
in `CTy.all` form. This replaces #654's `c : Bool`; no new carrier." The world's order is the
lifetime order. The world is the bound on the worlds a stop's continuation is resumed in.

**Scope.** B5 builds the world axis only. M1's other axes, count, position, storage and pending
finalisers, are not in B5's scope and stay as they are on main (`Qual`, `B = 0`, `fin`). Class 1
reads count only as `o.q = .lin` (must resume, which is count 1).

**Reading.** A stop at an operation whose world is `some ℓ_r` owes its continuation only at
`Ext`-extensions that keep every record tagged strictly inside `ℓ_r`. A resumer whose own world is
`ℓ_r` can therefore resume it: whatever the resumer opens before resuming, it closes again.

A lend at `'x` survives such a stop whenever `'x` is strictly inside `ℓ_r`. This is M1's
implication "holds ℓ ⇒ ℓ_r bounds ℓ". `ℓ_r` is a lifetime that the handler names (one in its `Δ`),
and every lend the handled computation opens is inside every such lifetime (`'x ⊏ Δ.meetOfDom`). So
the bound is satisfiable exactly by a handler in scope. This is what #673 v3's review item S4 noted
("a handler can never name an inner lend's lifetime"); here it is a property of the order, not a
reason to collapse the carrier.

**The unbounded element.** Today's convention, owed at every `Ext`-extension, is the world that
constrains nothing. Under this reading that is a lifetime with nothing strictly inside it. The
syntax `Lifetime.Life` (`var | top | join | meet`, `Paper/S1_Syntax/Definitions.lean:276`, a
transcribed grammar) has no such element, and B5 does not add one to a printed grammar. So the field
is `Option Lifetime.Life`:

- `none` is unbounded, today's.
- `some ℓ` is the bound `ℓ`.
- `some .top` keeps every record (all are inside `⊤`), which is #654's `c = true`.

#654's Bool is therefore two points of this carrier (`none` and `some .top`), not the carrier. Every
lifetime in between, `some 'h` for a handler at `'h`, is new.

```lean
-- Core/Types.lean
structure OpSig where
  n : UInt32
  i : UInt32
  q : Qual
  A : VTy
  B : VTy
  fin : CTy := .ret .unit
  /-- M1's world: the bound of the worlds a continuation captured here is resumed in. `none`:
  every `Ext`-extension (unbounded). Placed after #750 A's `rc` if A lands first (box Q4). -/
  wld : Option Lifetime.Life := none

inductive CTy
  | eff (n i : UInt32) (q : Qual) (A B : VTy) (fin : CTy) (wld : Option Lifetime.Life) (C : CTy)
  -- …
```

```lean
-- Core/EffDefs.lean. `OpEnt.wld : Option Life` is the bound interpreted at `δ` (in
-- `OpSig.ent`), by the interpretation `CTy.all`'s bound uses.
def Owed (en : OpEnt) (ls ls' : List SRec) (ρ : WRes) : Prop :=
  Ext ls ls' ρ ∧ ∀ r, en.wld = some r → ∀ x : SRec, x.2 ⊏ r → (x ∈ ls ↔ x ∈ ls')
-- contShare and KapRelT (EffRules.lean): `∀ ls', Ext ls ls' ρ →` becomes `∀ ls', Owed en ls ls' ρ →`
theorem owed_unbounded {en : OpEnt} (h : en.wld = none) {ls ls' ρ} : Owed en ls ls' ρ ↔ Ext ls ls' ρ
theorem Owed.ext {en ls ls' ρ} : Owed en ls ls' ρ → Ext ls ls' ρ
theorem Owed.anti {en en' ls ls' ρ} : en.wld ≼ en'.wld → Owed en' ls ls' ρ → Owed en ls ls' ρ
-- `w ≼ w'`: `w = none`, or `w = some r ∧ w' = some r' ∧ r ⊑ r'` (inside-or-equal, the lifetime order)
```

```lean
-- Core/EffBorrow.lean. `Row.Lend` now reads the lifetime context; `LifeLt` is the lifetime-order
-- judgement `CTy.all`'s rules use (its name on main fixed in phase 2).
def Row.Lend (Δ : LifeCtx) (S : Row) (x : LifeVar) : Prop :=
  ∀ o ∈ S, o.n ≠ 0 ∧ ¬ VFree x o.A ∧ (∀ Δ a, VOutlives Δ a o.A) ∧
    (o.abort = true ∨
      (o.q = .lin ∧ ¬ VFree x o.B ∧ (∀ Δ a, VOutlives Δ a o.B) ∧
        ∃ r, o.wld = some r ∧ r.mentions x = false ∧ LifeLt (Δ.extend x Δ.meetOfDom) (.var x) r))
theorem Row.Unwind.lend {Δ S x} : S.Unwind x → S.Lend Δ x
```

```lean
-- Core/EffFin.lean. `[sub]` moves along the order: `none` to any bound, and a bound to a wider one.
-- The order needs a lifetime context, so `LeF` takes `Δ` (rework, 1.4).
def OpSig.LeF (Δ : LifeCtx) (o o' : OpSig) : Prop :=
  o.Sig o' ∧ (capB o.q o.B = true → FinLe o.fin o'.fin) ∧
    (∀ r, o.wld = some r → ∃ r', o'.wld = some r' ∧ LifeLe Δ r r')
```

```lean
-- Core/DivDefs.lean, Core/DivFuel.lean
def tickSigW (w : Option Lifetime.Life) : OpSig := ⟨divEff, 0, .lin, .unit, nextTy, .ret .unit, w⟩
abbrev tickSig : OpSig := tickSigW none
abbrev divFuelTy (S : Row) (A : VTy) (w : Option Lifetime.Life := none) : VTy  -- inner row `tickSigW w :: S`
```

The runtime handles `[tickSigW (some .top)]`. It opens nothing before it resumes, so it keeps every
record. `reify`'s tick stays `tickSigW none`.

### 1.3 The changed rules, verbatim

The rules differ from main only in the marked premises. `Life.wf Δ` is the existing
well-formedness (`Support/Lifetimes/Terms.lean:82`).

```lean
  | divFuel {Δ Γ} {w : Option Lifetime.Life} (S : Row) (A : VTy) (hS : ∀ o ∈ S, o.n ≠ divEff)
      (hw : ∀ r, w = some r → r.wf Δ = true)                                             -- new
      (hΓ : Ctx.DeadP Γ) :
      CDerives Δ Γ (.val divFuelV) (.val (divFuelTy S A w))                               -- w: new
  | withbor1U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
      (hS : S.Lend Δ x)                                                                   -- was S.Unwind x
      (hdc : closedAt 0 d = true) (hd : CDerives Δ Γ d (.val (.lolli (.ref A) .unit))) :
      CDerives Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S))
  | withbor2U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
      (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
      (hS : S.Lend Δ x)                                                                   -- was S.Unwind x
      (hdc : closedAt 0 d = true) (hd : CDerives Δ Γ d (.val (.lolli (.ref A) .unit))) :
      CDerives Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))
  | effHandleT {Δ Γ Γ₁ Γ₂} {Hr Hc e : Expr} {S SN : Row} {E : List (Qual × VTy × VTy)}
      {fs : Nat → CTy} {n : UInt32} {w : Option Lifetime.Life} {A R : VTy}                 -- w: new
      (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁)
      (hHr : Hr.ValFormIn Γ₁) (hHc : Hc.ValFormIn Γ₁)
      (hc : CDerives Δ Γ₁ (.pair Hr Hc) (.val (.tensor (retTy S A R) (ansesTy S SN R E))))
      (hn0 : n ≠ 0) (hnd : n ≠ divEff) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
      (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
      (hw : ∀ r, w = some r → r.wf Δ = true)                                             -- new
      (hCN : ∀ r, w = some r → ∀ o ∈ SN, ∃ r', o.wld = some r' ∧ LifeLe Δ r r')            -- new
      (he : CDerives Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs w ++ S) A))) :            -- w: new
      CDerives Δ Γ (hndExpr n (E.map Prod.fst) (.pair Hr (tailTuple E 0 Hc)) e)
        (.comp (CTy.effOf S R))
```

`hCN` says that a tail clause's own stops are resumed in a world at least as wide as the one it
promises. So the clause, which runs to its resume before `κ` is resumed, keeps every record inside
`r`.

**Rules that do not change:**

- `reify`: its tick stays `none`. A stored loop owes its continuation at every extension, so no
  class-1 lend crosses a `reify`. This keeps class 2 (`gen-self-borrow`, `for-lend-resumes`) out.
- `effHandleL`, `effHandleV` and `effHandleVB` handle `none` rows. `Row.ofEff`'s world defaults to
  `none`.
- `iterate`.
- `withbor3U`, `withloadU`, `sliceBorrowMU` and `sliceBorrowIU` **keep `S.Unwind x`** (#654's own
  Open). Section 4 lists what this leaves refused.

**`CDerivesP` and `CDerivesAt` carry the same premises** (decided, box Q3). They are generated from
`scripts/pin/CDerivesP.tmpl.lean` by `scripts/gen-pin.py`, and in `Core/Tied.lean` respectively.

### 1.4 Each rule's proof at the lifetime carrier: port or rework

On main, `EffWp.lean`, `EffDefs.lean`, `EffBorrow.lean`, `Wp.lean`, `DivRuntime.lean`,
`DivPrograms.lean` and `DivIterate.lean` are unchanged since #654's merge-base 8dbe5892. `wpG`,
`contShare`, `OpEnt`, `KapRelT`, `effWp`, `cwp`, `Closing`, `RowLe` and `Ext` are byte-identical.

What changes is the carrier. #654's graded `Owed` was **list equality** (`∀ x, x ∈ ls' ↔ x ∈ ls`).
At a lifetime bound it is **`Ext` plus equality of the records inside `r`**. Every proof that used
the equality must now rebuild what it held at the stop's list from `Ext` (the Kripke monotonicity of
`vC`, `RelationFacts.lean:269`), together with the kept records inside `r`. The accepted larger
rework is this.

| rule / lemma | source (`call-grade`) | at the lifetime carrier | the step that changes |
|---|---|---|---|
| `wpG_M_frameAt`, `wpG_I_frameAt`; `wpG_*_frameX` re-derived | `EffWp.lean:616`, `:267` | **port as is** | none: they mention no world |
| `Owed`, `owed_unbounded`, `Owed.ext`, `Owed.anti`, `owed_of_same` | `EffDefs.lean:191` | **rework** (new definition) | `Owed.anti` is the order's monotonicity; `owed_of_same` still holds (equality implies both conjuncts) |
| `contShare_ungraded`, `kapRelT_ungraded` | `EffDefs.lean:316`, `EffRules.lean:736` | **port**, at `wld = none` | — |
| `KapRelT.owed` | `DivHandle.lean:341` | **rework** | `hg : en.call → en'.call` becomes `en.wld ≼ en'.wld`, through `Owed.anti` |
| `lendM_frame` | `EffLend.lean:365` | **rework** | `hΨA` assumes `∀ x, x ∈ ls ↔ x ∈ ls₀` and rebuilds `viewCell l Tt δ ls₀ α v'' χ hχ hw₀` at `ls`. Now `ls` is only `Owed (some r)` from `ls₀`: `vC true Tt ls₀ δ v''` moves to `ls` by `Ext`, and the lend's own records (`frameList`/`lineageOf` at `α`, with `α ⊏ r`) are kept by the second conjunct. **The named risk:** every record the view cell's coherence reads is tagged inside `r`. If one is tagged at or outside `r`, this step does not go through as stated, and that is the STOP |
| `lendI_frame` | `EffLend.lean:973` | **rework** | as `lendM_frame`: `lsI = immL l Tt δ A v ρP lsO`, with the `immL` records at `A ⊏ r` |
| `cwp_lendM`, `cwp_lendI` | `EffLend.lean:733`, `:1167` | **rework**, through the two above | `OpTab.LendAt α` (`:181`) changes from `call = true ∧ q = .lin` to `q = .lin ∧ ∃ r, wld = some r ∧ α ⊏ r` |
| `withbor1L_compatX`, `withbor2L_compatX` | `EffLend.lean:1264`, `:788` | **rework** | `Row.Lend Δ` interpreted at `δ`: the syntactic `LifeLt Δx 'x r` gives `δ'x ⊏ δr` by the existing soundness of the order judgement (the one `CTy.all`'s case uses) |
| `OpSig.LeF`, `OpEnt.Le`, `Row.gradeAt`, `rowLe_gradeAt`, `effWp_gradeAt` | `EffFin.lean:130`, `:996`–`:1017` | **rework** | `LeF` takes `Δ`. `RowLe` and the `[sub]` rule's use of it gain the lifetime context. `gradeAt g S` grades to `some ℓ` for a given `ℓ` |
| `handleT_compatC` with `hw`, `hCN` | `DivHandle.lean:711` | **rework** | the clause keeps records inside `r`: its run is a `wpG` run whose stops are at `SN` (`hCN`: worlds `⊒ r`), and its own lends close before it resumes (`wpG`'s `↭`). Plus `effHandleL`/`DivHandleLast.lean`'s mechanical edits (`Ext.refl` → `Owed.refl`, `KapRelT.ext` with `none`) |
| graded `divFuel`, `runtime_every_run`, `divFuel_every_run` | `DivFuel.lean:373`, `DivRuntime.lean:392`, `DivPrograms.lean:190` | **port** | `div_fuel` and the runtime answer at once and open nothing, so `Owed (some r)` is met by list equality (`owed_of_same`) |
| `rtMain`, `runtime_main_every_run`, `io_rt_every_run`, `IORun.rt_every_run` | `DivRuntime.lean:418`, `:522`, `:542`; `Externs.lean:511` | **rework** | main's `IORun` has `loops`, not `rt` |
| callers of `withbor1U`/`withbor2U` | — | **edit** | `DeclLend.lean:202`: `Sf_unwind.lend` |
| `CTy.applyLSub` (`Types.lean:1601`), `VFree`/`CFree` (`:196`, `:214`), `VScoped`/`CScoped` (`:1894`), `Life.mentions` | — | **rework** | `wld` is a lifetime inside `CTy.eff`, so substitution, freeness and scoping each gain a clause for it (`.eff n i q A B fin w C` ↦ `… (w.map (·.applySub σ)) …`; `VFree x` includes `w.mentions x`) |
| the substitution lemmas behind ∀E/`CTy.all` (`applyLSub` of `vC`/`cC`, `CFree` after substitution, `Scoped` after extension) | `Core/Relation*.lean`, `Core/Compat*.lean` | **rework** | each `.eff` case gains the `wld` component. The interpretation of `wld` at `δ` must commute with `applyLSub` as `CTy.all`'s bound does |
| wf of rows carried in value types (`withbor1UTy x … S`, `withbor2UTy`, `divFuelTy … w`, `reifyTy`) | `Core/EffBorrow.lean`, `DivFuel.lean` | **rework** | a row in a value type now carries lifetimes, so `VScoped`, `VFree` and the `δ`-interpretation of these types read them |
| `sigsOkB` (`Frontend/Check/Tied.lean:691`), `Ξ`/`RowAt`/`SigsAt` (`Core/Tied.lean:6`–`:27`) | — | **no change, stated** | they compare `(q, A, B)` only, and ignore `wld` as they ignore `fin`. So a world never makes one operation two signatures |
| every `.eff` pattern (7 → 8 arguments) | — | **mechanical** | re-estimated: about **220** occurrences of `.eff`/`\| eff` over **36** files on main (grep), plus the generated pin files, plus main-only `Classes.lean:245`, `Dtor.lean:190`, `DivHandleLast` |

The renames `aff`→`cancel`, `Persistent`→`Ctx.Banged`, `Drop`→`OwnFree` and `Weak`→`Cancels` do not
occur in `EffLend.lean`. They hit #654's edits to `DivHandle`, `EffFin` and `EffRules`.

#746's `Tok`/`OwnFree`, `DerivedCopy`, StackK and the §42 lend do not enter the class-1 semantics.

If a lifetime carrier proves infeasible for a specific proof, the step is named and the work
stops. It does not fall back to two points.

### 1.5 The theorems

| theorem | statement |
|---|---|
| `fundamentalC` (`Fundamental.lean:593`), `adequacyC` (`:776`), `adequacyD` (`Demonic.lean:312`), `fundamentalD`, `total_every_run` | **unchanged**. The new cases are `withbor1L_compatX`, `withbor2L_compatX`, graded `handleT_compatC` and graded `divFuel` |
| `fundamentalC_pin`, `adequacyD_pin` | statements unchanged; their `CDerivesP` grows (box Q3) |
| `runtime_every_run`, `divFuel_every_run` | each gains `w`; the old statement is kept as the `none` instance |
| `runtime_main_every_run`, `io_rt_every_run`, `IORun.rt_every_run` | new: `main`'s loop, driven by the runtime at `some .top`, never gets stuck |
| `contShare_ungraded`, `kapRelT_ungraded`, `owed_unbounded`, `rowLe_gradeAt`, `effWp_gradeAt` | new: conservativity. At `wld = none` the relation is today's |

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
restoring the state, and `forYield` did the same with a `tryCatch`. Both are **replaced** by one
judgement, and the `tryCatch` fallback is not ported.

**`div ∈ row(M)`** is read off the row that inference assigns to the body (§14 *Inference and
markers*), computed bottom-up with one clause per construct over the whole grammar:

| construct | `div ∈ row(·)` |
|---|---|
| `while`, `loop` | always |
| `for x in it`, a drain | always |
| `for x in D`, data | `div ∈ row(body)` |
| `for x in g(e)` | `div` is in `g`'s row, or in the clause's work |
| an application `f V` | `div` is in the row of `f`'s inferred type |
| `x <- M; N`, `let`, `case`, `(V, W)`, a borrow block, `[then]` | the union over the parts |
| `with h { M }` | `row(M)` less what `h` handles; no surface handler handles `Div` |
| `λ`, a thunk, a stored generator | `∅`: `div` stays in the value's type |
| a terminal, a variable, a literal | `∅` |

The shapes listed in D0 are examples of this judgement, not its definition.

| # | construct | kernel form | reads |
|---|---|---|---|
| D0 | a div body: `div ∈ row(M)` (above; e.g. a `while`, a drain, a looping generator's `for`, a call at a row holding `Div`) | the body at `F_{tick, Σ}(B ⊕ R)`; a terminal `return v` is `inl v` | syntax, inferred callee types |
| D1 | `while c { M }; N` | `iterate(step, s₀)`. The step is `<turn & close>`. The turn is `case c { false → inl (inl j) \| true → M; inr s′ }`. The close hands back the residual. The state is the variables of `c`, `M` and `N` by name, plus the held sources and capabilities | names in scope, their inferred types |
| D2 | `loop { M }; N` | D1 without the test. The join type is `0` when there is no `break` | as D1 |
| D3 | `for x in it`, over an iterator or a stored generator (a drain) | `iterate` holding `it`; the turn observes `it.1`, the close is `it.2` | the source's inferred type |
| D4 | `for x in D`, over data: a count, a view `fam (imm/mut)`, `&a`, an owned array of a persistent type, a sized iterator, or `imm 'a (array A)` / `mut 'a (array A)` (see D4′) | body with `div ∉ row(body)`: today's total counted loop (§16), unchanged. Body with `div ∈ row(body)`: `bounded_fix` at the row `div, Σ` (#646 amendment: "a counted loop with `Div` in its body is `bounded_fix` at the row"). A lend around the source is held across the ticks, and the kernel decides | the source's type |
| D4′ | `for x in v` with `v : imm 'a (array A)` (or `mut`) | a reborrow through `withload` (the existing `borrow imm *v { 'y, w -> … }` sugar, `Sugar.lean:3760`) to the view `array_imm 'y A`, then D4 over the view. When the body does not tick, no lend crosses a tick. When it ticks, `withloadU` stays `Row.Unwind` and the kernel refuses | the source's type |
| D5 | `for x in g(e)`, over a generator | `handle_tail` (`effHandleT`) when every exit resumes and nothing raises; otherwise `handle_last` (`effHandleL`, §51), around `g`'s direct call. A clause whose work has `div` in its row is a div body of its own (D0). The loop's state is threaded through the clause's answer, so **the operation's signature carries the consumer's state** (`x × ws ~> ws`). This choice is forced by the kernel rule, not by the language: `effHandleT`'s clauses are closed values (`Hr.ValFormIn Γ₁`, `Hc.ValFormIn Γ₁`, `Ctx.DeadP Γ₁`), so the loop's live variables can reach the clause only through the operation. A generator's signature therefore depends on its consumer, which is why `makeInst` makes one instance per use, with or without borrows (box Q8). When the state holds a borrow, that signature mentions a lifetime, and decision R (one closed signature per operation, `Core/Tied.lean`) refuses it. That refusal is the kernel's and is listed in 4.2. D5 never threads the owner in place of the borrow: that is the per-observation lend | the clause's exits (syntax) |
| D6 | a direct-style call of a div function | inlined at the caller's row: the call, then `case inl/inr`. On `inr`, close what is held and leave with the residual (D9) | the callee's type |
| D7 | a loop used as a value (`U(Loop B R)` expected) | `reify_res[B, R, Σ](res)(thunk M)`, with `res` the closed residual function | the expected type |
| D8 | `main` that loops | `reify` of the body, driven by the runtime (`rtMain`). When the runtime is the only `Div` handler, the body runs in place, and the checker types it at the runtime's world `some .top` | `main`'s inferred row |
| D9 | `break`, `continue`, `return` | `inl (inl j)`, `inr s′`, `inl (inr a)`, each after closing the held sources, innermost first. The residual hands back **exactly what the loop holds, by name**. `b2-div`'s `eAbort` matched capabilities by type (`capOf`); that is not ported (box Q6) | names |
| D10 | a borrow block whose body is a div body; `let r = &x` before a loop; a lend at a direct-style call of a div function | the kernel's lend (`withbor1U`/`withbor2U`, or the slice/`withbor3U`/`withload` forms) with its callback a div body at the enclosing row. The elaborator neither splits it per turn nor refuses it. The kernel accepts (`Row.Lend`, class 1) or refuses (`Row.Unwind`) | the place's type |
| D11 | loops inside handler clauses and effect bodies | D0–D10 at the clause's row. A `[handle]` around a ticking computation is `effHandleT`/`effHandleL` only (§14) | — |
| D12 | an `imm` borrow used at every turn | threaded by name in the state (D1). Each turn is a split between the body's use and the back edge's `inr s′`, and #756's rule inserts the kernel copy there (section 3) | — |

**Tick placement (decided, box Q5).** Ticks are the ones the kernel rule fixes: `iterate`'s own
back-edge ticks (§14), and no others. `b2-div`'s forward placement (a tick at every move to a point,
plus one before a terminal reached before any point, #644 step 0) existed to match the old machine's
observation counts, and it is not ported. Section 4.5 lists the measured effect on outputs.

**World (decided, box Q2): the checker decides it, never the elaborator.**

- The elaborator writes every row with `tick` and every operation at world `none`.
- The checker types a lend's callback at `Row.Lend Δ x`, an `effHandleT` node's handled row at
  `some r` (with `hw` and `hCN`), and `main`'s row at the runtime's `some .top`. It reaches all of
  these only through `[sub]` (`none → some r`, `OpSig.LeF Δ`), choosing `r` as the handler's own
  innermost lifetime (`Δ.meetOfDom` at the node).
- The kernel re-checks every premise: `Row.Lend`, `hw`, `hCN`, and `reify`'s `none` tick.

A wrong world makes the checker refuse the term. It never makes the checker accept one it should
not. Phase 2 reads `call-grade`'s `Row.lendB` first. If the checker cannot decide the world without
the elaborator choosing it, STOP.

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
   drops the borrow by its derived drop: `imm` is `Forgettable`, `OwnFree ∧ HasDtor`
   (`forgettable_iff`, `Core/Classes.lean:390`).

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

- **K-lend**: class 1 accepts a `withbor1U`/`withbor2U` lend whose callback ticks, or performs, at a
  row where the world bounds the lend: driven in scope by the runtime or by a tail-resumptive
  `effHandleT`.
- **K-copy**: the `imm` re-read is #756's derived copy (section 3).
- **K-unwind**: a lend that stays `Row.Unwind` refuses a tick in its callback. These are the slice
  borrows (`&a` of an array, `borrow mut a` of an owned array, a buffer or literal's view),
  `withbor3U` and `withloadU`.
- **K-sig**: decision R, one closed signature per operation (`Core/Tied.lean`; SPEC §19).
- **D-elab**: the `Div` elaboration with no lend involved.

The "main" and "branch" columns are measured. The "B5" column is predicted, with
`borrow-core-spec42`'s binary for main (its Frontend and Backend are 32bbf65d's), and with b2-div's
and class1-revive's binaries.

**The written-fix rule** (user standing rule, 2026-10-31): a program that should work may be refused
only if it has a written fix. Each refusal below says one of:

- **(a)**: the fix available today, which the refusal message must name. The message text is given
  in 4.6.
- **(b)**: no fix until the recovery step. **⚑** marks a (b) that is an ordinary-looking loop.

### 4.1 Accepted on main, accepted under B5 (the mechanism changes)

These seven ran through LoopLend's per-observation lend. With the four programs in 4.2 they are
#646's set of eleven (the twelfth, `lend-div-iter`, is `sugar/lend-div` in 4.2). class1-revive
measured each of the seven on main's file.

| program | main | class1-revive | B5 | mechanism |
|---|---|---|---|---|
| `corpus/axes/borrow-across-loop` | i32[60] | i32[60] | i32[60] | K-lend + K-copy |
| `corpus/hygiene-borrow-loop` | i32[207] | i32[207] | runs | K-lend + K-copy |
| `corpus/lend-mut` | i32[604] | i32[604], Backend2 native | runs | K-lend (`mut`, no copy) |
| `corpus/lend-server` | i32[65] | i32[65] | runs | K-lend at the call + K-copy |
| `corpus/lend-shadow` | i32[105] | i32[105] | runs | K-lend + K-copy |
| `corpus/sugar/lend-block` | accepted | accepted | accepted; `.core.bc` rewritten | K-lend + K-copy |
| `corpus/sugar/lend-let` | accepted | accepted | accepted; `.core.bc` rewritten | K-lend + K-copy |

### 4.2 Accepted on main, refused or at risk under B5 (new refusals)

| program | main | class1-revive | B5 | why | fix | recovered by |
|---|---|---|---|---|---|---|
| `corpus/lend-copy` ⚑ | runs | refused 37:3: `borrow mut a { … while … }` over an owned array holds its lend across the tick | **refused** → `pending/` | K-unwind (slice) | **(a)** lend inside each turn: `while c { borrow mut a { 'x, v -> … } }` (message U) | **B2** W-tick (`lendRT`) at `LendForm` fam |
| `corpus/lend-pipeline` | i32[361] | refused 39:1: "operation 1.0 has two signatures" | **refused** → `pending/` | K-sig; cause below | **(a)** move the borrow into the body: `let v = borrow imm t { b -> get(b, x) }`. **Measured**: `lp-r1.bc` prints i32[361], `live 0`, on main's and class1-revive's binaries (message S) | no plan step; needs lifetime-polymorphic `Ξ` (box Q8) |
| `corpus/lend-config` | runs | refused 40:3: "`stdin` is not consumed in its scope" | **at risk** | class1-revive's close did not hand back the lent capability. Under D9 (hand back by name) it is expected to run | if refused: **(a)** borrow at each use instead of once: `for c in bytes(&mut stdin) { acc = scale(&config, …) }; cap(&config, acc)` (message U′) | B5 itself, by D9 as a rule; otherwise a listed refusal |
| `corpus/lend-div`, `corpus/sugar/lend-div` | runs / accepted | refused 42:7: "expected `i32`, but this has type `i32 + 1`" | **at risk** | class1-revive §62: a borrow block whose body is a direct div call was not typed at `B ⊕ R`. D10 composed with D6 places it at `B ⊕ R` | if refused: **(a)** bind the call's result inside the block, then return it | B5 itself, by D6/D10; otherwise a listed refusal |

**lend-pipeline's cause** (diagnosed from class1-revive's `bcc desugar`; the scratchpad files are
cited in the report):

1. D5's push elaboration threads the `for` site's state through the operation's answer:
   `x × ws ~> ws`.
2. With LoopLend gone, `ws` holds the borrow itself (`imm 'io_l5 array i32`). Main's LoopLend held
   the owner, `ref array i32`.
3. The generator is a generic instance, and §15's `makeInst` (`Sugar.lean:6257`–`:6305`) gives it
   its own lifetime binder `'io_q0`. So its `perform` is at `'io_q0`, while `main`'s handler is at
   `'io_l5`.
4. `sigsOkB` (`Frontend/Check/Tied.lean:691`) then reports one operation with two signatures
   (`Program.lean:156`).

This is **not a checker bug**. Instantiating the definition's signatures at the use's lifetime would
still leave a signature that mentions `main`'s lifetime, and decision R requires a closed one. So it
is an existing rule refusing what D5's threading produces. `pending/state-machine-audit` is the same
case: the handler capability `mut 'fx_l_audit …` is threaded, and class1-revive and b2-div refuse it
at 91:1.

### 4.3 Refused on main, accepted under B5

| program | main | branches | B5 | mechanism |
|---|---|---|---|---|
| **P1** `scratch-743/t/p01-while-handler-op` | refused 3:1 (`escapeError`, the per-observation rewrite) | class1-revive: i32[20], Backend2 native | **accepted** | K-lend: `&mut c` is lent across `walk`'s ticks (the runtime, `some .top`) and `count`'s tail-resumptive `tick()` (`effHandleT`, `some r`) |
| **P3** `scratch-743/t/p05-iter-borrowed-vec` | refused 20:12 (`iterError`) | class1-revive: refused 20:24, "`*` … has type `1`" | **accepted**, i32[6] | D4′ (decided in scope): `imm 'a (array i32)` was not data (`dataSrcOf`, `Sugar.lean:2633`), so it fell to the drain path and `x` got type `1`. The loop is total, so no tick crosses the lend; copies go only through #756's rule |
| `reject/lend-iter-borrow` | refused 28:5 (`iterError`) | class1-revive: i32[60] | → corpus | K-lend + K-copy |
| `reject/while-in-counted-for` | refused 10:5 (S1) | all three: i32[4] | → corpus | D-elab (S1 retired) |
| `reject/for-data-gen-loop` | refused 15:19 (S2) | all three: i32[30] | → corpus | D-elab |
| `pending/for-view-local` (#491) | refused 14:1 (`lentDef`) | all three: i32[3] | → corpus | D-elab: the counted walk over a view is total |
| #545 matrix RW, RL, RG | refused (S1, S2) | b2-div and class1-revive: 241 | run | D-elab |
| new: `lend-imm-copy`, `lend-call-copy`, `lend-nest3`, `lend-depth3`, `lend-order3` (from call-grade), `lend-shadow-core` (from class1-revive) | absent | accepted | added, accepted | K-lend (+ K-copy); depth 3 and order 3 |

The matrix goes from 18/25 to 21/25.

`reject/lend-div-two` is refused at 14:14 by `lentDef`. It has `lend-div`'s gap: once D6/D10 type
it, it either moves to the corpus or the kernel refuses it, and the result is listed.

### 4.4 Refused on main, still refused under B5

| program | main | B5 (predicted, from class1-revive) | why | fix | recovered by |
|---|---|---|---|---|---|
| **P2** ⚑ `p02-lines-print`, `x02-lines-noprint`, `x02b` | refused 4:1 (`lentDef`); `x02b` 8:14 (`iterError`) | **refused**: `s`'s view is lent across `main`'s ticks | K-unwind (buffer view); see below | **(a)** the loop is inside a callee: `echo` takes the owner `s` and walks it with a cursor, borrowing inside each turn (`borrow imm s { t -> print_str(line_at(t, i)); next_line(t, i) }`), or uses `lib/lend.bc`'s `loop_lend_imm` (message U′) | **B2** W-tick (`lendRT`) at `LendForm` fam; **B6** for the finite-observation shape only |
| **P4** ⚑ `p06`, `p06b` | refused 8:5, 9:5 (S1) | **refused** 6:3: `&a`'s slice lend crosses the inner `while`'s ticks | K-unwind (slice) | **(a)** index in each turn: `for i in 0..n { let x = a[i]; while … ; … a[i] … }` (message U) | **B2** at `fam` |
| #545 matrix AW, AL, AG | refused (S1, S2) | refused 9:3, the same as P4 | K-unwind | **(a)** as P4 | **B2** |
| `pending/for-buf-borrow` (#501) ⚑ | refused 16:55 (`iterError`) | refused 16:11 (buffer view) | K-unwind | **(a)** as P2 | **B2** at `fam` |
| `pending/parse-recover-gen` | refused 136:7 (`iterError`) | refused 136:5 (a literal's view held by a generator) | K-unwind, and class 2 (the generator is stored) | **(b) ⚑** | **B7** (generator holding a view), with B2 |
| `pending/state-machine-audit` | refused 72:1 (`escapeError`) | refused 91:1: "operation 1.0 has two signatures" | K-sig (4.2) | **(a)** `drive` owns the state and runs `with audit(&mut st) { … }` per event. **Measured**: `sma-r1.bc` prints the expected tuple, `live 0`, on both binaries (message S) | as `lend-pipeline` (box Q8) |
| `pending/aoc-2020-07` | refused 34:1 (`lentDef`) | refused 91:27: "`memo` consumed in one arm" | #492, not a lend | **(a)** consume `memo` in both arms; #492's message | #492 |
| `reject/lend-escape` | refused 20:11 (`escapeError`) | refused 23:34: "`q` used twice … `imm 'x array i32 * i32` is not persistent" | a pair is not `DerivedCopy` | **(a)** take the pair apart before the loop, `let (v, n) = q` (message C). After that the block's escape is refused, as the reject intends | stays a reject |
| `reject/lend-shadow` | refused (the rename check) | refused 23:53 on a type error the old check hid | — | stays a reject; `-- expect:` changes | — |
| `reject/for-lend-resumes` (P5) ⚑ | refused | unchanged: `for x in &a { yield(*x) }` in a generator | class 2 | **(a)** index in each turn, `for i in 0..n { yield(a[i]) }`: each read's lend ends before the `yield` (message R) | **B7** |
| `reject/gen-self-borrow` | refused | unchanged | class 2 (a self-borrow across `yield`) | **(b)** | **B7** |

⚑ marks an ordinary-looking loop. Every ⚑ program has a written fix (a), still to be measured
(check 6). The one (b) that is ordinary-looking is `parse-recover-gen` ⚑: a generator over a
literal's lines, which is ordinary in Rust.

**Two refusal classes beyond these programs.** Each is listed because ordinary programs fall into
it:

- **D4′ with a ticking body** ⚑: `for x in v` over `imm 'a (array A)` whose body has `div` in its
  row. The `withload` reborrow is `Row.Unwind`, so the kernel refuses (K-unwind).
  **(a)** index in each turn, `for i in 0..len(v) { … v[i] … }` (message U). Recovered by **B3**
  (the view case) or **B2**.
- **K-last**: a lend held across an operation handled by `effHandleL` (`[handle-last]`, a clause
  that works, then resumes or cancels). Its row has world `none`, so the continuation is owed at
  every extension and `Row.Lend` fails. **(a)** end the lend before the operation, or write the
  handler so that it resumes in tail position (message L). Recovered by **B2** (a `LendForm` at a
  cancellable row).

**A new reject test:** `reject/loop-linear-owner-each-turn.bc`. A declared (`Tok`-owning, linear)
owner is used by value at every turn of a `while`. It is refused at the turn's split, because its
type is not `DerivedCopy`. This pins that B5 never copies a linear value.

**P2 reconciled with spike round 4.**
`spike743/experiments/Spike743/bc/reify/p2-shape-iterator-over-view.bc` checks `unconditional`.
Its shape is this:

- The lend is `withbor1` of a cell, closed at a row **with no `Div`**.
- Inside it, `echo`'s loop is a `reify`d loop value.
- The block observes that value **a fixed number of times** (three `nu_out`s) and then closes it.

The loop holds the view, not a lend, so no tick crosses the lend.

P2 as written is different. `main` runs `borrow imm s { 't, t -> echo(t) }`, and `echo` drains
`lines(t)` to its end. Under D6, `echo(t)` is a direct-style div call, so the block's callback ticks
once per line at `main`'s row, driven by the runtime. Under D3/D7, a `reify` with a consumer that
drains it is still observed once per turn by a loop whose back edge ticks inside the block. So the
lend of `s`'s view (a buffer: a slice lend, `sliceBorrowIU`) is held across ticks whichever way the
loop is elaborated.

So B5's D-rules cannot produce the spike's shape for P2 or `x02`. The spike's shape needs an
observer that stops after a known number of observations inside the block, and P2 has none.

What recovers P2 is a lend form for the buffer's view across ticks:
- B2's `lendRT` at `LendForm` fam, asserted under `LendFrame`; or
- a class-1 frame for `sliceBorrowIU`. This is #654's Open, a new proof outside the plan.

B6's `for`-to-`reify` elaboration recovers only the variant that observes a fixed number of times
(the spike's). P2's fix today is (a).

### 4.5 Outputs under back-edge-only ticks (decided placement)

**Measured by simulation.** No binary implements back-edge-only ticks. class1-revive's `bcc desugar`
output had every explicit forward `perform[4294967295.0] ()` replaced by *next*, and was run with
class1-revive's binary. Under this, a `while` with k turns takes k observations instead of k+1.

Over all 381 corpus/axes/sugar programs and 49 book and internals blocks, **no output changes**.
Every difference was traced to a parser, printer or branch artefact, and the round-trip of
class1-revive's unmodified core gives the same result.

| program | effect | listed reason |
|---|---|---|
| `io-fuel` `count_lines` | budget 3 reads 4 bytes, not 3. The output is unchanged because byte 4 does not end a line | the comment at `io-fuel.bc:11`–`:12` ("three bytes read") becomes wrong and is corrected. `reify` runs the first turn when the loop value is built |
| `sugar/hof-{returned,closure,local}` | threshold 2 → 1 observations. Output unchanged at budget 10 | — |
| book `iteration.md:87` `collatz` | 112 → 111 observations. Output unchanged at budgets 200/50 | — |
| everything else in `#644`'s list | unchanged: hand-written `unfold`, counted loops, or generators at a row (which already tick only at back edges) | — |

### 4.6 Refusal messages that name the fix

Each message is the checker's text at the refusal it reports. It decides nothing.

- **U** (K-unwind, a slice, buffer, `withbor3` or `withload` lend whose callback ticks): "`a` is lent
  at L1 and the lend is still open at the loop's next turn (L2): a {slice | buffer view | reborrow}
  lend is held only across operations that abort. Borrow inside each turn instead, so that the lend
  ends before the turn does: index `a[i]` in the body, or put the borrow block inside the loop."
- **U′** (K-unwind or K-lend, where the loop is inside a callee): "`t` is lent to `echo` at L1, and
  `echo` loops (L2), so the lend is held across its turns: pass the owner `s` to `echo`, and borrow
  it inside each turn of the loop there; or borrow at each use (`f(&s)`) instead of once before the
  loop."
- **L** (K-last): "the lend of `x` at L1 is held across `op` at L2, whose handler works before it
  resumes, or may cancel (`[handle-last]`): end the borrow before `op`, or resume in tail position
  in the handler."
- **S** (K-sig at a threaded loop state): "operation `n.i` would carry the loop's borrow of `t` in
  its signature (`'l0` here, `'l1` at L2), and an operation has one closed signature: borrow `t`
  inside the loop's body (`let v = borrow imm t { b -> … }`) so that the loop holds the owner."
- **C** (a pair holding a borrow, used at two splits): "`q` is used twice and its type
  `imm 'x A * B` is not copyable: take it apart first (`let (v, n) = q`), so that the borrow is
  copied alone."
- **R** (class 2, a lend across a stored loop's or generator's stop): "the lend of `a` at L1 is held
  across `yield` at L2, whose continuation is stored: read `a[i]` inside each turn, so that no lend
  is open at the `yield`."

### 4.7 Counts

| change | count |
|---|---|
| keep running by a new mechanism | 7 |
| firm new refusals | 2 (`lend-copy`, `lend-pipeline`), each with a fix (a) |
| at risk | 3, plus `reject/lend-div-two` |
| newly accepted | P1, P3, 3 rejects, 1 pending, 3 matrix cells |
| new programs | 6, plus the reject `loop-linear-owner-each-turn` |
| still refused | P2, P4, AW/AL/AG and 7 corpus programs; all but `parse-recover-gen` and `gen-self-borrow` have a fix (a) |
| outputs changed | 0 (one comment) |

**P1–P4:**

| probe | B5 |
|---|---|
| P1 | **accepted** |
| P2 | refused (a); B2 |
| P3 | **accepted** |
| P4 | refused (a); B2 |


---

## 5. NOT-do list

- **No `PinLaw` change.** `Core/PinLaw.lean`'s `LendFrame`, `LoopFrame` and `PinLaw` keep their
  statements and fields. The one edit to `Core/PinLaw.lean` is the arity of three `OpSig`
  literals (box Q4). What grows is `CDerivesP`, and with it the derivations `LendFrame` ranges
  over (box Q3, decided). That is stated in SPEC and shown by `bcc trusted`.
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
- **No count, position, storage or finaliser axis of M1.** B5 builds the world axis only.
- **No two-point world.** The world is a lifetime bound (`Option Lifetime.Life`). If a proof does
  not go through at the lifetime carrier, the step is named and the work stops (1.4).
- **No grading of user effects beyond what `effHandleT`'s `hCN` checks.** #654 Open.
- **No premise beyond 1.3's** on `withbor1U`, `withbor2U` or `effHandleT`. The named-risk STOP
  (1.4) is not met by restricting the lend's lifetimes to inside `r`, or by any other added
  premise.
- **Not resumed, merged or cherry-picked:** `class1-revive`, `b2-div`, `call-grade`. `750a-kernel`
  is not touched.

## 6. Tempting shortcuts, and the STOP each raises

| shortcut | STOP |
|---|---|
| Keep LoopLend's per-observation lend for the programs `Div` refuses (`lend-copy`, P2, P4) | **KERNEL WORK.** It decides a lend's extent in the elaborator. The programs go to `pending/` with the lend and the tick, as #646's amendment says |
| A checker copy where the copy rule does not apply: copying the pair in `lend-escape`, copying the state wholesale, or a copy for a non-`DerivedCopy` slot | **LINEARITY.** Refused and listed, never repaired |
| A grade special case for one handler (`count` in P1), or a world chosen per program or by the elaborator | **KERNEL WORK.** The checker decides the world, by `[sub]` and the kernel's premises; one rule for every `effHandleT` |
| Collapse the world to `{op, top}` when a lifetime-carrier proof is hard | **DECISION.** M1's world is a lifetime bound; name the failing step and STOP |
| Meet the named risk in `lendM_frame` by an added premise (restricting `A`'s lifetimes inside `r`) | **PRINTED-RULES.** No premise beyond 1.3's; STOP and report the step |
| Thread the owner instead of the borrow through a generator's operation to avoid decision R (`lend-pipeline`) | **KERNEL WORK.** That is the per-observation lend; the refusal stands with its fix (a) |
| Fold B2's W-tick (`lendRT`) in early to recover P4, `lend-copy` or AW/AL/AG | **SCOPE.** B2 waits on #750 and is asserted under `LendFrame`; B5 asserts nothing |
| Give `sliceBorrowMU/IU` or `withbor3U` `Row.Lend` "since the proof is the same" | **SCOPE plus a new proof.** #654 left them Open; frames for them are not proved. Stop, report, do not assert |
| Give `reify`'s tick a bound so that P5 or `gen-self-borrow` types | **SOUNDNESS.** A stored loop is owed at every extension (class 2, B7) |
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
  is `F[div]` with `tick` at `some .top`. The world is erased with the row; nothing in Backend2
  reads it.
- `effHandleT`/`effHandleL` around a ticking computation use §47's erasure (`handle_tail` → call;
  `[handle-last]` as §51's lowering, already on main for non-ticking bodies).
- `withbor1U`/`withbor2U` at a `Row.Lend` row are §29 *Lowering*: the lent cell is never moved
  (`genLendU` gains the row).
- A `reify` whose loop value is **stored** (it escapes into data or a cell, or is held and stepped
  by hand) is a state machine (`genIterK`, §49). That is the sanctioned fallback where the program
  keeps the loop.
- A `reify` whose observer sites are static (a `for` over it, a direct drain) goes through the
  erasure pass (§47): no machine.
- `div_fuel`'s kernel constant stays outside Backend2. The elaboration never emits it; the
  library's `div_fuel` over loop codata (`lib/div.bc`) is ordinary code.

**Replaced:** the per-body `unfold` machine lowering at elaborated loops (§45 `nuEta` and §49's
drive at `main`'s loop). Both remain for hand-written `unfold` and `pull`.

**The old backend:** `iterate` stays `expandIter` (`Backend/Clos/Convert.lean:894`). Each looping
program gains one indirect call (`counts.expected`). The zero-cost target ("allocate or indirect only
where C/Rust would", measured by corpus counts) is held on Backend2, which has none of these calls.
Whether the old backend, retired at N6, is still held to it is **marked for the user**. If it is, B5
must lower `iterate` natively there too.

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
| `Core/Types.lean` | `OpSig.wld : Option Lifetime.Life`; `CTy.eff … wld …` | M1 world axis, a lifetime bound (1.2) |
| `Core/EffDefs.lean`, `Core/EffRules.lean` | `OpEnt.wld`, `Owed` (`Ext` + records inside the bound), `Owed.anti`, `owed_unbounded`, `contShare`/`KapRelT` over `Owed`, `OpSig.ent`, `Row.ofEff … w`, `contShare_ungraded`, `kapRelT_ungraded` | 1.2, 1.4 |
| `Core/EffFin.lean` | `OpSig.LeF`, `OpEnt.Le`, `Row.gradeAt`, `rowLe_gradeAt`, `effWp_gradeAt` | `[sub]` along the lifetime order (`none` → `some r` → wider) |
| `Core/EffBorrow.lean` | `Row.Lend Δ`, `Row.Unwind.lend`, `Row.Lend.resumes/unwind` | 1.2 |
| `Core/EffWp.lean` | `wpG_M_frameAt`, `wpG_I_frameAt`; `frameX` re-derived, statements unchanged | 1.4 |
| `Core/EffLend.lean` (new) | `lendM_frame`, `lendI_frame`, `cwp_lendM`, `cwp_lendI`, `withbor1L_compatX`, `withbor2L_compatX` | 1.4 |
| `Core/DivDefs.lean`, `DivFuel.lean`, `DivHandle.lean`, `DivHandleLast.lean`, `DivRuntime.lean`, `DivPrograms.lean` | `tickSigW`; `divFuelTy … w`; `KapRelT.owed`; graded `handleT_compatC`; `effHandleL` mechanical; `runtime_every_run w`; `rtMain`, `runtime_main_every_run`, `io_rt_every_run`; `divFuel_every_run w` | 1.3, 1.5 |
| `Core/Fundamental.lean` | the premises of 1.3; the `fundamentalC` cases | 1.3 |
| `Core/Tied.lean` | `CDerivesAt` premises | mirrors `CDerives` |
| `scripts/pin/*.tmpl.lean` → `Core/PinDerives.lean`, `Core/PinFundamental.lean`, `Frontend/Check/{TDerives,TExpr,TLife}.lean` (generated) | the premises of 1.3; the `fundamentalC_pin` cases call the same compat lemmas | box Q3 |
| `Core/PinLaw.lean` | **only** `pinAwaitSig`/`pinYieldSig`/`pinRaiseSig`'s anonymous-constructor arity | box Q4 |
| `Core/PinDerives.lean:17`, `:531` (via the template) | the doc comments that tie R2 to LoopLend; the `CDerivesP` docstring on `Row.Unwind` | stale under B5 |
| `Core/DeclLend.lean:202` | `Sf_unwind.lend` | premise change |
| every `.eff` pattern (Core, Frontend/Check, Backend2; ~220 occurrences in 36 files) | one more argument | arity |
| `Core/Types.lean` (`CTy.applyLSub`, `VFree`, `CFree`, `VScoped`), the substitution lemmas, the row-in-type wf | the `wld` clause | a lifetime inside `CTy.eff` (1.4) |
| `Frontend/Check/Externs.lean` | `IORun.rt`, `IORun.rt_every_run` | D8 |
| `Frontend/{Parser,Syntax,Print}.lean`, `Frontend/Check/TTied.lean` | core text `iterate[…]`, `reify[…](res)`, `div` row; the checker emits `iterate`/`reify`/`handle_tail`/`handle_last` | 2.1 |
| `Frontend/Sugar.lean` | D0–D12; delete the loop machine, `forDataDiv`, `io_hwf`, S1 | 2.2, 2.4 |
| `Frontend/Check/` (the refusal sites) | messages U, S, C, R naming the fix | 4.6 |
| `Frontend/Elab/LoopLend.lean` | delete `lendBind`, `lentDef`, `lendCall`, `iterError` | 2.4 |
| `Backend2/Convert.lean`, `Backend2/Driver.lean`, `scripts/PinSites.lean` | section 7 | lowering |
| `SPEC.md` | a new entry (version after #750 A's, 1.22 if A lands first, fixed at merge); §14's per-observation lend and machine sections rewritten; §29: `LendFrame`'s domain grows with `CDerivesP`'s rules, B5's included (Q3) | spec-first |
| `corpus/` | section 4's moves; 6 new programs; the falsifier's nested-lend programs (check 7); `reject/loop-linear-owner-each-turn.bc`; the measured (a) rewrites (check 6); `io-fuel.bc`'s comment (4.5); the 12 programs' comments; `axes/README.md`; `-- expect:` and `-- now:` lines | section 4 |
| `corpus/*.expected` | `counts` (+1 indirect per loop, old backend); `counts-backend2` (rows for 4.2 out, 4.3 in); `erasure-backend2`; `handled` (`main` gains the `Div` name); `kinds` | measured diffs on `class1-revive` |
| `corpus/sugar/*.core.bc` | up to 22 pairs; `lend-div.core.bc` deleted | the emitted core changes. Each pair is re-checked, not just regenerated |
| `docs/kernel-usage/census.tsv`, `docs/kernel-usage.md`, `scripts/AxiomCheck.lean` | the new lemmas | census |
| `book/src/guide/iteration.md` ("Borrows and loops"), `book/src/elaboration/divergence.md`, `docs/internals/elaboration/divergence.md` | prose | docs |

**Theorem statements changed:** `runtime_every_run` and `divFuel_every_run` gain `w`, with the old
statements kept as the `none` instances. `handleT_compatC` gains `w`, `hw` and `hCN`.

**Hypotheses added:** `hw` and `hCN`, premises of the `effHandleT` rule (and `hw` of `divFuel`),
not of any theorem. At `w = none` both are trivial and give today's rule; they are non-vacuous at
`w = some r`, where P1's `count` meets them.

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
6. P1–P4 run by hand against section 4's table. **Every (a) fix is written out and measured**, on
   main's binary and on B5's, and recorded in the PR with its output: `lend-copy`, `lend-config`
   (if refused), `lend-div` (if refused), P2/`x02`, P4/AW/AL/AG, `for-buf-borrow`, the D4′-with-tick
   class, K-last, `aoc-2020-07`, `lend-escape` and `for-lend-resumes`. `lp-r1.bc` and `sma-r1.bc`
   are already measured. **STOP:** an (a) that fails becomes (b) and is raised with the user.
7. **The falsifier on nested lends (condition of Q3; results go in B5's PR).** Programs, each run
   under `--check tags`, `--check fresh` and `--alloc least`, and the stress generator (several
   hundred seeds per mode, as in the 743 spike):
   - `nest-c1-in-r1`: a task's R1 `borrow mut` across `await`, whose callback holds a class-1 lend
     of a second local across a tail-resumptive handler's operation, and across a `while`'s ticks
     driven by the runtime.
   - `nest-r1-in-c1`: a class-1 `borrow mut x { while … { … } }` at `main`'s row, whose body spawns
     a task holding an R1 lend of its own local across `await`.
   - `nest-c1-r1-c1`: depth 3, alternating, with the inner lend read after the middle one's stop.
   - `nest-cancel`: `nest-c1-in-r1` with the task cancelled while the class-1 lend is open, and with
     an abortive operation raised inside the inner lend.
   - `nest-imm`: the `imm` variants, the re-read at each turn through #756's copy.
   - `nest-fin` (after #750 A): a `[then]` whose finaliser's row holds `Div` (`effThenDiv`), and
     whose finaliser holds a class-1 lend across a `while`'s ticks, run on the raise path and the
     normal path.

   Kill: a run that gets stuck, leaks, gives a wrong answer or trips the tag check. That is a hard
   stop, reported before the PR.
8. **`bcc trusted`** shows `LendFrame` at every R1 site whose callback contains a class-1 lend
   (`nest-c1-in-r1`, `nest-c1-r1-c1`), `PinFin` at `nest-fin`, and nothing new at class-1-only sites
   (`lend-mut`, P1).
9. One `make gate`, run only as `~/repos/scripts-local/gate-serial.sh gate` from the worktree,
   once, at the end.

## 10. Questions: decided, and still open

> **Q1. World carrier: DECIDED, a lifetime bound** (M1, user, 2026-10-22: "world as a lifetime bound
> ℓ_r on eff, in CTy.all form … no new carrier"; reconfirmed for B5 with the larger rework
> accepted). Section 1.2 gives the Lean form. The field is `Option Lifetime.Life`, because the
> unbounded element ("owed at every extension") has nothing strictly inside it, and the transcribed
> `Lifetime.Life` has no such lifetime. #654's Bool is two of its points.
> **Still open for the reviewer:** whether `none` is acceptable as the unbounded element. The
> alternative is a bottom lifetime, which would edit a printed grammar and is not proposed.

> **Q2. Who decides the world: DECIDED, the checker.** The elaborator writes `none` throughout. The
> checker reaches `some r` by `[sub]` at lends, `effHandleT` nodes and `main`. The kernel re-checks.
> STOP if the elaborator would have to choose.

> **Q3. `CDerivesP` mirrors `S.Lend`: DECIDED by the top foreman,** answering from the across-loops
> decision (2026-10-29/30: PinLaw's schemas are uniform in depth and holder, so a class-1 lend nested
> in an R1 callback is more depth and holders under the same schema, not a new assumption), with the
> conditions below. **The user is being told.**
> **Exactly what widens:**
> - `LendFrame` (`PinLaw.lean:91`) quantifies over callbacks `M` with
>   `CDerivesP Δb [⟨V, true⟩] M (.comp (CTy.effOf S (.box (.var x) B)))`.
> - Before B5, every `withbor1U`/`withbor2U` node inside such an `M` had a row of abortive
>   operations only (`S'.Unwind y`).
> - After B5, `M` may contain a `withbor1U`/`withbor2U` node at `S'.Lend Δ' y`: a lend of a local
>   `y`, inside the R1 callback, whose own callback performs non-abortive linear operations of world
>   `some r` with `'y ⊏ r`. These are tail-resumptive handler operations, and `Div` ticks driven by
>   an in-scope `div_fuel`. The R1 row itself is `ResumeO`, which holds no `tick`.
>
> Those derivations are the new members of `LendFrame`'s domain. Nothing else in `CDerivesP` changes.
> `LoopFrame`'s steps `N`, `K` and `s0` gain the same nested nodes inside handlers they contain: their
> own rows are `.ret`.
>
> **The same growth after #750 A** (`750a-kernel`'s `Core/PinLaw.lean`). There, `PinLaw` has three
> schemas:
> - `LendFrame` is over `LendForm` at `Row.ResumeOC S x` (SPEC §29a). Its `M` gains the same
>   class-1 nodes. `ResumeOC` holds no `tick` either.
> - `LoopFrame`: as on main.
> - `PinFin` (`:138`) is over `[then]` with `Row.divB SD = true` (`CDerivesP.effThenDiv`), and
>   quantifies over `CDerivesP` derivations of `M`, `N` and the finaliser `D`. After B5, `D` may hold
>   a class-1 lend across its own ticks (`Div` is in `SD`), and so may `M` and `N`. Those are new
>   members of `PinFin`'s domain.
>
> The statement in SPEC names all three.
> **Conditions:**
> - Phase 2's check 7: the falsifier on nested lends, with the results in the PR.
> - SPEC's B5 entry, and §29, say plainly: "`LendFrame`'s domain is every `CDerivesP` derivation of
>   the callback; it grows with the rules `CDerivesP` admits, and B5's class-1 premises are such
>   rules."
> - `bcc trusted` reports `LendFrame` at those sites, and `PinFin` at the `effThenDiv` sites with a
>   class-1 lend inside (check 8; `nest-fin` in check 7).

> **Q4. `PinLaw.lean`: DECIDED, the literals' arity only.** B5 adds `wld` after `fin` on main and
> takes #750 A's layout at merge (`wld` after `rc`). The textual merge covers every `.eff` pattern,
> `scripts/pin/*.tmpl.lean`, the `CDerivesP` template's stale docstring (`:14`, "at a row of abortive
> operations only") and SPEC. The SPEC version is fixed at merge (1.22 if A lands first). Any other
> `PinLaw.lean` edit is a STOP.

> **Q5. Tick placement: DECIDED, `iterate`'s own back-edge ticks** (correct over consistent).
> Measured by simulation: no output changes. `io-fuel`'s comment is corrected (4.5).

> **Q6. The residual at an exit (D9): hand back by name.** This is as written. `lend-config` and
> `lend-div` test it; a program it cannot express is a listed refusal with a fix (a).

> **Q7. "Reads checked facts": an interpretation, for the user.** The foreman confirmed the reading:
> the elaborator reads syntax and inferred types, and decides no guarantee. It is an interpretation of
> "checked facts only": no pipeline gives the elaborator checker output. It is **marked for the user**
> to confirm.

> **Decided (user, 2026-10-31): route (ii), handler-owned state on `effHandleT`, as its own unit after B5.**
>
> **Q8. K-sig: a generator's signature depends on its consumer. A menu.** The diagnosis (4.2) shows
> the root. D5 threads the consumer's loop state through the producer's operation (`x × ws ~> ws`),
> because `effHandleT`'s clauses are closed. So a generator's signature depends on whoever consumes
> it, and `makeInst` makes one instance per use, with or without borrows. A borrow in `ws` only makes
> the dependence visible, as a lifetime that decision R refuses.
>
> | option | kernel change | what it fixes | cost |
> |---|---|---|---|
> | **(i)** a lifetime-polymorphic `Ξ` | `Core/Tied` (1008 lines): `Ξ` indexed by the lifetime context, or signatures closed under `∀'l`; `RowAt`/`SigsAt` and `sig_prefix_of_rowAt` instantiate it. `Frontend/Check/Tied.lean`'s `sigsOkB` compares up to lifetime instantiation | `lend-pipeline` and `state-machine-audit` as written | the symptom only. Signatures still depend on the consumer, and `makeInst`'s per-use instances stay. Unestimated; it touches decision R |
> | **(ii)** handler-owned state on `effHandleT`: a parameterised tail clause `Hc : P × A → F(P × B)` | `effHandleT` gains a state type `P` and an initial state; the handler threads `P` from clause to clause and returns it with the result. `handleT_compatC` is restated with `P` in `KapRelT`'s answer. The erasure law (§47) becomes "resume-once = call with the state passed" | the root: operation signatures are the user's declared ones (`Yield[i32]: i32 ~> 1`), closed and independent of the consumer. `makeInst` needs one instance per generator, not per use. A borrow in the loop state lives in `P`, typed under the handler's `Δ`, never in a signature | a new rule's proof, about the size of `DivHandle.lean`'s `effHandleT` part (`DivHandle.lean` is 875 lines; `DivHandleLast.lean` 975), plus D5's emission, Backend2's lowering of `P` as a loop-carried variable, and the same for `effHandleL`. Parameterised handlers are the literature's standard form (Plotkin–Pretnar) [recalled] |
>
> **Is (ii) in B5's scope?** Not as B5 stands: it is a new kernel rule, with its proof and lowering,
> and B5's acceptance does not depend on it. *Recommendation:* (ii), as its own unit after B5, because
> it removes the cause, and (i) leaves it. **The user's call**, raised through the foreman.
>
> **What B5 does meanwhile:** D5 as written. `lend-pipeline` and `state-machine-audit` go to
> `pending/` with message S and their measured fix (a). D5 states that its state-in-signature choice
> is forced by closed clauses (2.2).
>
> **Other refusals with no step in the plan:** P2's buffer view is recovered by B2 (`lendRT` at fam),
> not B3 or B6 (4.4); `aoc-2020-07` is #492.

> **Q9. D4′: DECIDED, in scope,** as a rule by type, with copies only through #756's rule.

## STOPs carried into phase 2

- **Q3:** the falsifier on nested lends (check 7) breaks a run.
- **Q4:** `PinLaw.lean` needs more than the literal arity.
- **S2:** a written fix (a) fails when measured. It becomes (b) and is raised with the user.
- **1.4:** a class-1 proof does not go through at the lifetime carrier (the named risk:
  `lendM_frame`'s `hΨA` re-entry, where the view cell reads a record tagged at or outside `r`).
  The step is named and the work stops; it does not fall back to two points.
- **Q2:** the world is chosen by the elaborator.
- A class-1 port that needs a changed `fundamentalC`/adequacy statement, or a new hypothesis on
  them.
- A program accepted only with a copy that #756's rule does not insert.
- A Lint rule change.
- A stored-loop machine where the program does not keep the loop.
- Any frame for `withbor3U`, slices or `withload`.
