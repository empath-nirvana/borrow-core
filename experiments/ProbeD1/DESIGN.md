# ProbeD1: the fundamental lemma at W for the rules `genSelf` and `reconB′` use

**What this is.** The design of the tractability probe for design D1 (rows and ghost end), the
probe of `research/effects/src/synthesis.md` §11. It fixes the Lean statements, the definitions
they need, why each statement tests the question at full strength, what success and failure look
like, the arising check a counterexample must pass, and the stop rule. No proof is written.

**The Lean.** Every definition and statement below is in `experiments/ProbeD1/ProbeD1/*.lean`
(library `ProbeD1`, root `ProbeD1.lean`), and `lake build ProbeD1` elaborates it. The code blocks
here are copied from those files, with routine clauses elided as `…`. The files hold definitions
and `def … : Prop` statements only: no `theorem`, `sorry`, `axiom`, `native_decide`, `opaque`,
`partial`, `unsafe` or `implemented_by`.

**Worlds.** The tags are the notebook's. [Core σ=[]] is Core's relation. [GE] is a GhostEnd
relation (`vRLs`, `vRLa`, `vRLk`). [W] is this probe's relation (`ProbeD1.vRL`/`cRL`) at one of
its placements. A result at one of them is not a result at another unless a statement here
relates them.

**Rules this design keeps.**
- Nothing breaks the borrow calculus: its guarantees, not BoLo's text.
- The paper is not wrong; every refutation the probe can produce is of a statement of ours.
- An obstruction is only an elaborating `def … : Prop` with its negation proved at a configuration
  that arises (`Arises`, reachability from the nil index) and at values that arise (`ArisesV`)
  (§11). Otherwise the report says "not derived, no obstruction verified".
- No step-indexing: the relation is one `mutual` block, structural on the type.
- No relation family beside W's one relation. The three placements of §3 are candidates for that
  one relation. W is the placement that survives; if more than one does, the cuts order chooses
  (§3).
- Multi-shot is ignored. The core is linear.

---

## 0. The probe on one page

**The question** (synthesis §11): is FL at W provable for exactly the rules `genSelf` and `reconB′`
use, at one world, with the arising guard read from `TW`, with one future-world quantifier, and
with no relation family beside W?

**The order is fixed.** Statement 0 first. Its outcome decides OQ-8 (where the future-world
quantifier sits) and with it whether D1 meets "two algebras with interactions only at cuts"
(synthesis §2.5, §4.2, §8). Statements 1–4 follow, at the placement statement 0 leaves.

| statement | Lean (`ProbeD1.…`) | what it settles |
|---|---|---|
| 0. W's `U`, `⊸`, `∀` clauses fixed together | `vRL`, `cRL` at `Placement.{cbpv, binder0, binder}`; `Statement0 p` = `ExtPreW`, `FutReLend`, `MonoV`, `MonoG`, `NilSoundV`, `NilSoundC`, `CallbackExtMut`, `CallbackExtImm`, `ForceRow`, `ThawRelend`, `ThunkFRow`, `ThunkVRow`, `BangThunkFRow`, `BangThunkVRow`; beside it `MonoC`, `MonoHide` (`MonoHideFromMonoV`), `NilAgreesU`, `NilAgrees` | OQ-8; whether `U` and `⊸` take one quantifier; OQ-58, through `NilAgrees` (§6.3) |
| 1. the guard as `TW`'s run invariant | `Statement1 p` = `TabNil`, `TabParts`, `TabUpd`, `TabRuns`, `TabStart`, `TabHide`, `TabRelend`, `TabFut`, `TabResume`, `ArisesSound`, `LamRow`, `AllIRow`, `BelowRow`, `BelowExcluded`; beside it `TabOfTWPointwise` | OQ-45's first question, re-scoped (§5.2); `lam`, `allI` and `not_gfpAt_below`'s derivation at W |
| 2. the borrow-constant row at `σ·y` | `Statement2 p` = `SpanW2Row`, `SpanW1Row`, `RebFrameR`; beside it `SpanLoadRow`, `RebChooserNonVacuous` | #275; [TR] 6.150 at a resuming table (Law 2 for `withload`) |
| 3. `[handle]` with a lend open | `Statement3 p` = `HandleRow` | #278 |
| 4. `[allR-E]` at W | `Statement4 p` = `AllREW`, `AllRMono` | Law 1's elimination inside a borrow |
| 5. the programs | `GenSelfAccepted p`, `ReconAccepted p e` | `genSelf`, `reconB′` accepted at W |
| 6. the sample row | `ThenRow p` | `effThen` at a frozen frame's cancel |
| 7. the side check | `Targets.NotVDenNaturalArises` | whether naturality is available for live lends |
| the arising check | `ProbeRules`, `Arises`, `ArisesV`, `ArisesAt`, `ArisesNonVacuous` | what a refutation must reach (§11) |
| all | `Probe p`; `Survives e p`, `Placement.rank` | statements 0–6 at one placement; which placement is W (§3) |

**The stop rule** (§12.3): if `Statement0 p` is proved at no placement, the probe stops after
statement 0 and reports.

---

## 1. The question, and why these two programs

D1 keeps today's stop condition (conjuncts 37 and 40 of `wpG`). A lend opened inside a suspended
segment ends at the stop by its printed exit (ghost end), and resume re-lends it at a fresh
lifetime beneath the resumer's (Law 2). GhostEnd proves the pieces at [Core σ=[]] and at [GE]:
`ewpTS_M_frameR` (`Relend.lean:117`), `ewpTS_I_frameR` (`ImmLend.lean:175`),
`ewpTS_M_antiFrameR` (`Frames.lean:89`), `withborR_compat` (`Drop.lean:108`), the stacked steps
`stack_step_other`, `stack_step_reborrow`, `stack_step_imm` (`StackStep.lean:392, 563, 1003`), the
guarded relation's `lam_RLa` and `allI_RLa` (`gfp-arising:…/Arising.lean:478, 815`) and the
callback read at `σ·y`, `callback_ext` (`borrow-callbacks:…/Extend.lean:131`). What is open is
whether one relation at one world carries all of them through the rules a real program uses.

**`genSelf`** (`Targets/I/Programs.lean:199`, run by `genSelf_eval`) lends its state cell `Mut`
(`withbor` (2)'s term `withborUE dFlag`) to a generator body that reads the cell through
`withswap` (6.66) and yields twice at the affine `Yield : Flag ↠^aff 1`. The handler `orClause`
is outside the borrow and resumes. Today's kernel cannot type it: `withbor2U` needs `Row.Unwind`,
abortive operations only (`Core/EffBorrow.lean:133`).

**`reconB′`** (synthesis §11, to build) is the operator's shape:
`resumer wait (borrow imm cfg (λb. retry (λ_. *b; wait (); *b))) ; timeout (borrow imm cfg (λb. (λ_. *b; wait (); *b) ()))`.
The scheduler and `timeout` sit outside their borrows, so `wait` crosses an `Imm` lend (6.64).
`retry`'s handler of `exn` sits inside the first borrow, `retryR` is instantiated at a row inside
it (Law 1 with Law 2), and `timeout` cancels the second `wait`, which ends the 6.64 lend's owner
frame by its unwinding finaliser.

Between them the programs use: the spanning `withbor` (1) and (2) at a resuming affine row, their
callbacks at `σ·y`, `withswap` and `withload` inside a callback, `[perform]` and `[let]` with a
frame holding the view across a stop, `[handle]` outside a borrow and inside one, the cancel of a
continuation holding a lend's owner, `[allR-E]` inside a borrow, and the value rules around them.

---

## 2. The world W

### 2.1 What is reused

| from | what |
|---|---|
| Core | `vC`/`vCE`, `cC`, `wpTS`, `wpG`, `ewpTS`, `opTable`, `contShare`, `cancelOwed`, `KapRel`, `TW` and its constructors, `Tagged`, `Ext`, `Rel`, `Keeps`, `ptoMutS`, `ptoImmS`, `ptoImm`, `reborrow`, `RebChooseTW`, `wpG_reborrow`, `rebChooseTW_top`, `wpG_frame`, `wpTS_I_forget`, the borrow constants' terms and types (`withborUE`, `withbor1UTy`, `withbor2UTy`, `withload`, `withloadUTy`), `CDerives`'s rule shapes |
| GhostEnd (`targets`) | `LEnt`, `LStack`, `LKind`, `extS`, `depth`, `tabK`, `vwE`, `vwS`, `dropS`, `stratS`, `boxTop`, `ReLend`, `RelendableS`, `RelendableN`, `ghostS`, `stopS`, `bodyS`, `openFS`, `OpenS`, `rowTab`, `TabAtS`, `jdgCty`, `innerView` (`Stacked.lean`, `RLCompat.lean`); the lemmas of `StackStep.lean`, `Drop.lean`, `Relend.lean`, `ImmLend.lean`, `Frames.lean`, `Table.lean`, `Tree.lean`, `Descend.lean`, each at the rows whose hypotheses it meets (the fold lemmas need `LinResume` and `AllCross`, §6.2) |
| GhostEnd (branches; §2.6) | `Below.lean` (`gfp`), `Arising.lean` (`gfp-arising`), `Extend.lean` (`borrow-callbacks`): `tabAtS_comp`, `tabAtS_nil`, `wpG_tabAtS_one`, `tabAtS_start_one`, `force_RLa`, `relendableS_thunkA`, `thunkF_RLa`, `thunkE_RLa`, `lam_RLa`, `allI_RLa`, `vRLa_congr`, `below_excluded`, `stackFresh_of_fresh`, `stackTyFresh_of_fresh`, `callback_ext`, `callback_ext_one`, `all_elimK`, `tw_innerView`, `not_gfpAt_below` |
| Targets | `SemWorld` and its `B.BWorld`; `Idx`; `ExtPre`; `OpTabI`, `OpEntI`; `RowSpan`, `admClosedOp`, `RowClass`, `OutJ.core`; `TypingJ`, `ExtendsNU`, `SpanRule1`, `SpanRule2`, `SpanRuleLoad`; `SpanWithbor1`, `SpanWithbor2`, `SpanWithload`, `HandleCompat`, `SliceShape`, `Mono` (as the forms the probe's statements transcribe); `AcceptedAt`, `genSelf`; `NotVDenNaturalArises`; the open types `Inst.OVTy`, `Inst.OCTy` |

### 2.2 The index, the order and the guard (`World.lean`)

W's index is Targets' `Idx` at the stack `Stk := LStack × List Life`: GhostEnd's entries and their
current lifetimes, innermost first, beside the record list.

```lean
abbrev Stk := LStack × List Life
abbrev Ix := Targets.Idx Stk

def StackOK (σ : LStack) (αs : List Life) : Prop :=
  αs.length = σ.length ∧ List.IsChain (· < ·) αs ∧ (σ.map LEnt.x).Nodup
```

**Futures of the stack.** A value or a continuation can be used deeper than where it was made:
inside new lends and inside new handlers.
- A new lend is an entry inserted in the stack. It goes at the front when a value moves inside the
  lend. It goes at depth `k` when a continuation that ghost-ended its `k` innermost entries is
  resumed inside a lend the resumer opened (between lenders).
- A new handler hides its names from the stack's rows outside it. GhostEnd's stop depth reads each
  entry's lender row (`depth`, `Stacked.lean:115`), and inside a handler of `n` no stop of `n`
  reaches the lends outside the handler.

One step of a future does one insertion and one hiding. A future is any finite number of steps.

```lean
def hideS (N : UInt32 → Bool) (σ : LStack) : LStack :=
  σ.map fun e => { e with cross := fun n => e.cross n && !N n }

def futS (k : Nat) (τ : LStack) (N : Option (UInt32 → Bool)) (σ : LStack) : LStack :=
  σ.take k ++ τ ++ match N with
    | none => σ.drop k
    | some N => hideS N (σ.drop k)

def futL (k : Nat) (αt αs : List Life) : List Life := αs.take k ++ αt ++ αs.drop k

structure FutOK (δ : LSub) (σ : LStack) (αs : List Life) (k : Nat) (τ : LStack)
    (αt : List Life) (ρ : WRes) : Prop where
  len : αt.length = τ.length
  depth_le : k ≤ σ.length
  chain : List.IsChain (· < ·) (futL k αt αs)
  below : ∀ a ∈ αt, ρ.InStratum a
  vars_stack : ∀ e ∈ τ, e.x ∉ σ.map LEnt.x
  vars_sub : ∀ e ∈ τ, (extS δ σ αs).find? e.x = none
  nodup : (τ.map LEnt.x).Nodup
  places : ∀ e ∈ τ, e.l ∉ σ.map LEnt.l
  pay : ∀ e ∈ τ, ∀ y, VFree y e.T →
    (extS δ (σ.take k ++ τ ++ σ.drop k) (futL k αt αs)).find? y ≠ none

def nsBase : LifeVar := 2 ^ 32
def NsVar (x : LifeVar) : Prop := nsBase ≤ x
def NsFresh (τ : LStack) : Prop := ∀ e ∈ τ, NsVar e.x

def FutStep (δ : LSub) (ρ : WRes) (s s' : Stk) : Prop :=
  ∃ (k : Nat) (τ : LStack) (αt : List Life) (N : Option (UInt32 → Bool)),
    FutOK δ s.1 s.2 k τ αt ρ ∧ NsFresh τ ∧ s'.1 = futS k τ N s.1 ∧ s'.2 = futL k αt s.2

def Fut (δ : LSub) (ρ : WRes) : Stk → Stk → Prop := Relation.ReflTransGen (FutStep δ ρ)

def FutQ (fut : Bool) (δ : LSub) (ρ : WRes) (s s' : Stk) : Prop :=
  if fut then Fut δ ρ s s' else s' = s

def ExtQ (fut : Bool) (ls ls' : List SRec) (ρ : WRes) : Prop :=
  if fut then Ext ls ls' ρ else ls' = ls

def FutAvoids (C : CTy) (σ σ' : LStack) : Prop :=
  ∀ e ∈ σ', e.x ∉ σ.map LEnt.x → ¬ CFree e.x C ∧ e.x ∉ CTy.binders C

structure OwnOK (δ : LSub) (σ : LStack) (αs : List Life) (e : LEnt) (a : Life) (ρ : WRes) :
    Prop where
  chain : List.IsChain (· < ·) (a :: αs)
  below : ρ.InStratum a
  var : e.x ∉ σ.map LEnt.x
  place : e.l ∉ σ.map LEnt.l
  pay : ∀ y, VFree y e.T → (extS δ (e :: σ) (a :: αs)).find? y ≠ none

def OwnPush (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life) : Prop :=
  ∃ (x : LifeVar) (c : Lifetime.Life) (C' : CTy), C = .all x c C' ∧ e.x = x ∧
    x ∉ CTy.binders C' ∧ OwnOK δ s.1 s.2 e a ρ ∧ LtLife (extS δ s.1 s.2) c a

def OrdW (δ : LSub) (i i' : Ix) (ρ : WRes) : Prop :=
  Ext i.1 i'.1 ρ ∧ Fut δ ρ i.2 i'.2

def guardW (σ : LStack) (αs : List Life) (P : WProp) : WProp := fun ρ => TabAtS σ αs ρ → P ρ
```

**Why a future is a closure.** One step inserts one contiguous block at one depth and hides names
only outside it. Two legitimate steps at different depths give a stack no single step gives: from
`[a, b]`, inserting `t` at depth 1 and then `u` at depth 0 gives `[u, a, t, b]`. An order made of
single steps is therefore not transitive. Two things would follow. `WP p` would fail Targets'
`ExtPre`, which `WLaws` asks. And at `cbpv` a `U` value carried to a future would owe its
computation at the futures of that future, which are two-block futures of the original stack that
no hypothesis supplies. So `Fut` is the reflexive–transitive closure of `FutStep`, and
transitivity is by construction (`ExtPreW`, statement 0).

The stack a future gives is an order-preserving interleaving of `σ` with fresh entries. Each kept
entry's row is reduced by hiding sets that grow outward: a hiding at depth `k` reaches every kept
entry outside depth `k`. The lemmas the proofs need about it are stated where they are used:
`FutReLend` (§4.1) and `TabFut` (§5.1).

**The step's conditions.**
- `FutOK.below` is 6.112's `И`: the inserted lifetimes lie below the holder's resource.
- `FutOK.chain` is D-ORD: the whole vector stays in nesting order. So an insertion at depth
  `k > 0` needs the inner part re-lent below it first; the `U` clause and the share re-lend before
  they insert.
- `FutOK.pay`: every variable free in an inserted entry's payload type is read by the new stack's
  substitution. With `SemS`'s `SubDom` it gives `StackJ`'s payload scoping at the stacks the
  clauses produce (§2.5).
- The re-lend of the stack's own lifetimes is not part of `OrdW`. It is the hand-back the `U`
  clause and the share carry (`ReLend`, then the dropped views handed back).

**The own lend.** `OwnPush δ C ρ s e a` is the entry a callback's lend pushes on `s` at the type
`C = ∀'x ⊏ c. C'` the clause reads. It is named `x`, at a lifetime `a` meeting `c`, below the
innermost lend and below the holder's resource (`OwnOK`). It is the binder's instance read as the
lend the instance names, so it is relative to the type, and the clauses make it after a future,
never before one (§4.2). Its variable is the binder, which `extS` overrides at the pushed stack.
So `OwnOK` asks nothing of the reading substitution at it; `FutOK.vars_sub` asks that of an
inserted name only.

**Names.** Lifetime variables are names (`LifeVar := Nat`), and the stack binds its entries'
variables over the reading substitution (`extS`, which overrides `δ`). An entry a future inserts
takes its variable from the names no program binds (`NsVar`), and every judgement the probe reads
keeps its binders below them (`BindersLow`, §2.5). Without that, a future's entry could be named
by a binder of the code that later runs at the future, and the `∀` clause there would read its body
at the entry's lifetime instead of its instance: the `allE` row would have nothing to work with.
This is the representation item OQ-8 boxes (the draft spec's D-W, *Representation note*).
`nsBase` is a convention of the probe; its value matters only in being above every binder of the
two programs. The restriction `BindersLow` puts on FL at W is a guarantee gap with a stated
discharge (§14).

`FutAvoids C σ σ'` says that the entries `σ'` has and `σ` lacks are not read by `C`: their
variables are neither free nor bound in it. `FutAvoidsV` is the same at a value type, and
`CTy.binders` and `VTy.binders` are in `World.lean`.

### 2.3 The piece with the share over futures (`Piece.lean`)

GhostEnd's piece `OpenS` runs at one stack: a stop of depth `k` ghost-ends the innermost `k`
entries and owes its continuation, re-lent below them, at the same stack. The **share over
futures** owes the continuation also at every future of the kept part `σ.drop k`, since the
handler may resume it inside new lends and new handlers. The continuation then resumes at
`σ.take k ++ σo` for a future `σo` of `σ.drop k`, so the continuation variable carries its stack.

```lean
abbrev XTF := LStack → Nat → List Bool → List Life → List Life → List SRec → Expr → WProp

def RelendableNF (fut : Bool) (δ : LSub) (inner σ : LStack)
    (P : LStack → List Life → WProp) (αs : List Life) (ls : List SRec) : WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwS δ (inner.map LEnt.l) σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ αs', ReLend αs' αs → ∀ σ' αs'', FutQ fut δ ρz (σ, αs') (σ', αs'') →
      (∀ e ∈ σ', e.x ∉ σ.map LEnt.x → e.x ∉ inner.map LEnt.x ∧ e.l ∉ inner.map LEnt.l) →
      (vwS δ (inner.map LEnt.l) σ ds αs' ls ─⋆ P σ' αs'') ρz

def stopSF (fut : Bool) (δ : LSub) (σ : LStack) (Tab : OpTab) (X : XTF) (αs : List Life)
    (ls : List SRec) (t : Expr) : WProp :=
  ex fun k => ex fun ds => dropS [] (σ.take k) ds ⋆
    ghostS δ (σ.take k) (αs.take k) ls
      (opTable (tabK σ k Tab) ls t fun ls' e' =>
        RelendableNF fut δ (σ.take k) (σ.drop k)
          (fun σo αo => X (σ.take k ++ σo) k ds (αs.take k) αo ls' e') (αs.drop k) ls')

def bodySF (fut : Bool) (δ : LSub) (Tab : OpTab)
    (Q : LStack → List Life → List SRec → Val → WProp) (X : XTF) (σ : LStack) (αs : List Life) :
    List SRec → Expr → WProp :=
  fun ls e => wpG ls e fun ls'' t ρ => valPost (Q σ αs) ls'' t ρ ∨ stopSF fut δ σ Tab X αs ls'' t ρ

def openFSF (fut : Bool) (δ : LSub) (Tab : OpTab)
    (Q : LStack → List Life → List SRec → Val → WProp) (X : XTF) : XTF :=
  fun σ k ds αi αo ls e ρ =>
    ∀ αi', List.Forall₂ (· < ·) αi' αi → List.IsChain (· < ·) (αi' ++ αo) →
      boxTop αi' (vwS δ [] (σ.take k) ds αi' ls ─⋆ bodySF fut δ Tab Q X σ (αi' ++ αo) ls e) ρ

def OpenSF (fut : Bool) (δ : LSub) (Tab : OpTab)
    (Q : LStack → List Life → List SRec → Val → WProp) : XTF :=
  fun σ k ds αi αo ls e ρ =>
    ∀ X : XTF, (∀ σ k ds αi αo ls e ρ, openFSF fut δ Tab Q X σ k ds αi αo ls e ρ →
      X σ k ds αi αo ls e ρ) → X σ k ds αi αo ls e ρ
```

The reinstalled handler hides the stop's name from everything outside the continuation's own
lends. The share does not need the name: the future it is resumed at is one of `RelendableNF`'s,
the hiding of the name one of its steps.

### 2.4 The relation, its quantifier placed by `Placement` (`Relation.lean`)

One `mutual` block, structural on the type, the stack an index (as `vRLk`), the placement a fixed
parameter.

| placement | `U` | `⊸` | `∀` | the stop's share | the callback's own lend |
|---|---|---|---|---|---|
| `cbpv` (OQ-8 option 2) | futures | resources only | resources only | futures (`OpenSF`) | made at `U`, at every future, one level into the type |
| `binder0` (OQ-8 option 3, `vRLk`) | the stack itself (`RelendableS`) | resources only | resources only | the stack itself (`OpenS`) | made at `∀`, at the stack itself |
| `binder` (OQ-8 option 3, §17.6) | futures | futures | futures | futures (`OpenSF`) | made at `∀`, at every future |

The `U` clause over futures:

```lean
def RelendU (fut own : Bool) (δ : LSub) (σ : LStack) (C : CTy)
    (P : LStack → List Life → List SRec → WProp) (αs : List Life) (ls : List SRec) : WProp :=
  fun ρ =>
    ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwS δ [] σ ds αs ls ρn ∧ stratS αs ρz ∧
      ∀ ls', Ext ls ls' ρz → ∀ αs', ReLend αs' αs →
        ∀ σ' αs'', FutQ fut δ ρz (σ, αs') (σ', αs'') → FutAvoids C σ σ' →
          (vwS δ [] σ ds αs' ls' ─⋆ P σ' αs'' ls') ρz ∧
          (own = true → ∀ (e : LEnt) (a : Life), OwnPush δ C ρz (σ', αs'') e a →
            (vwS δ [] σ ds αs' ls' ─⋆ P (e :: σ') (a :: αs'') ls') ρz)
```

The block (the clauses not shown are `vRLs`'s: components at the relation, leaves at Core's `vC`
at `extS δ σ αs`):

```lean
mutual
def vRL (p : Placement) : LStack → LSub → VTy → List Life → List SRec → Val → WProp
  | σ, δ, .thunk C, αs, ls, f =>
      guardW σ αs
        (if p.uFut || p.uOwn then
          RelendU p.uFut p.uOwn δ σ C
            (fun σ' αs' ls' => cRL p σ' δ C αs' ls' (forceE C (.val f))) αs ls
        else
          RelendableS δ [] σ (fun αs' ls' => cRL p σ δ C αs' ls' (forceE C (.val f))) αs ls)
  …
def cRL (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Expr → WProp
  | σ, δ, .ret B, αs, ls, e => wpTS ls e fun ls'' v => vRL p σ δ B αs ls'' v
  | σ, δ, .eff n i q A B C, αs, ls, e =>
      if p.shareFut then
        bodySF true δ (rowTab n i q A B C δ) (fun σ' αs' ls v => effRet p σ' δ C αs' ls v)
          (OpenSF true δ (rowTab n i q A B C δ) (fun σ' αs' ls v => effRet p σ' δ C αs' ls v))
          σ αs ls e
      else
        bodyS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRet p σ δ C αs' ls v)
          (OpenS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRet p σ δ C αs' ls v)) αs ls e
  | σ, δ, .arr A C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQ p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.arr A C) σ σ' → ∀ v,
          (vRL p σ' δ A αs' ls' v ─⋆ guardW σ' αs' (cRL p σ' δ C αs' ls' (.app e (.val v)))) ρ
  …
  | σ, δ, .all x c C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQ p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.all x c C) σ σ' →
        (∀ α, (⌜LtLife (extS δ σ' αs') c α⌝ ─⋆
          guardW σ' αs' (cRL p σ' (δ.extend x α) C αs' ls' (.app e (.val .unit)))) ρ) ∧
        (p.allOwn = true → ∀ (en : LEnt) (α : Life), OwnPush δ (.all x c C) ρ (σ', αs') en α →
          guardW (en :: σ') (α :: αs')
            (cRL p (en :: σ') (δ.extend x α) C (α :: αs') ls' (.app e (.val .unit))) ρ)
  | σ, δ, .nu C, αs, ls, e => cC (.nu C) ls (extS δ σ αs) e
  …
end
```

At `bindFut = false` the `⊸` and `∀` clauses are read at the index itself (`ExtQ`, `FutQ` the
identity, `FutAvoids` vacuous), so `cbpv`'s and `binder0`'s are `vRLa`'s with, at `binder0`, the own
lend at `∀`.

**`binder0` against `vRLk` as built.** At `binder0` the `U` clause is `vRLk`'s and the share is
GhostEnd's `OpenS`. So `StackStep.lean`'s lemmas apply to the piece without restatement, at every
row whose hypotheses they meet. The fold lemmas (`stack_step_other`, `stack_step_imm`,
`stack_spans_mut`, `stack_spans_imm`) need `LinResume Tab` (every operation linear and resuming)
and `AllCross` (every stop crosses every entry). The programs' critical rows meet neither (§6.2).

The `∀` clause differs from `vRLk`'s in two ways:
- the extension is the callback's own lend only, one entry named by the binder at the instance's
  lifetime;
- that entry meets `OwnOK`: below the callback's resource, its variable and place new to the
  stack.

`vRLk`'s `∀` clause (`Extend.lean:92-96`) quantifies over every extension and every instance `α`.
For its own variable it reads the body at the extension's lifetime whatever `α` is, so its `allI`
row would owe the body at lifetimes that do not meet the bound. `callback_ext` uses only the
instance at the entry's lifetime, so it carries over.

**`cbpv`'s own lend.** At `cbpv` the `∀` clause is plain. A callback can then reach its own lend
only through `U`, so the `U` clause looks one level into its type. At every future it quantifies
over, it also pushes an entry named by the type's outermost `∀`, at a lifetime meeting its bound
(`OwnPush`). The plain `∀` clause at that stack reads its body at the stack's lifetime for its
binder (`extS` overrides `δ`). That is the instance `CallbackExt` uses, and the one `StackJ`'s
third kind admits (§2.5). This is what the `U` placement costs under GhostEnd's representation,
where entries carry the binder's variable.

The push follows the future because a `U` value carried to a future must keep its own lend there.
`MonoV cbpv` at a callback type `U(∀'y. Mut 'y T ⊸ D)`, at a future `σ'` of `σ`, needs the forced
body at `e :: σ''` for every future `σ''` of `σ'`. Every such `σ''` is a future of `σ`. A push
made at the stack itself would leave that case to `MonoC` at `⊸`, which `cbpv`'s `⊸` clause
(resources only) does not give.

### 2.5 The semantic judgement, and W as a `SemWorld` (`Sem.lean`)

```lean
def CtxAvoids (x : LifeVar) (Γ : Ctx VTy) : Prop :=
  ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty

def BindersLow (Γ : Ctx VTy) (C : CTy) : Prop :=
  (∀ x ∈ CTy.binders C, ¬ NsVar x) ∧ ∀ s ∈ Γ, s.live = true → ∀ x ∈ VTy.binders s.ty, ¬ NsVar x

def CScoped (Δ : LifeCtx) (C : CTy) : Prop := ∀ y, CFree y C → ∃ u, Δ.find? y = some u

def Scoped (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) : Prop :=
  CScoped Δ C ∧ ∀ s ∈ Γ, s.live = true → VScoped Δ s.ty

def SubDom (δ : LSub) (Δ : LifeCtx) : Prop := ∀ y, δ.find? y ≠ none → ∃ u, Δ.find? y = some u

def StackJ (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  (σ.map LEnt.x).Nodup ∧
  (∀ e ∈ σ, ∀ y, VFree y e.T → (∃ u, Δ.find? y = some u) ∨ y ∈ σ.map LEnt.x) ∧
  ∀ e ∈ σ,
    (∃ u, Δ.find? e.x = some u) ∨
    (NsVar e.x ∧ Δ.find? e.x = none ∧ ¬ CFree e.x C ∧ CtxAvoids e.x Γ) ∨
    (Δ.find? e.x = none ∧ σ.head? = some e ∧ CtxAvoids e.x Γ ∧
      ∃ c C', C = .all e.x c C' ∧ e.x ∉ CTy.binders C' ∧ ∀ a ∈ αs.head?, LtLife (extS δ σ αs) c a)

def SemS (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → StackJ σ αs δ Δ Γ (jdgCty j) → SubDom δ Δ → Δ.Models (extS δ σ αs) →
    TabAtS σ αs ρ → gRL p σ δ αs ls Γ γ ρ → cRL p σ δ (jdgCty j) αs ls (substAll γ e) ρ
```

`SemS` is GhostEnd's `SemA` (`Arising.lean`) at the placement's relation. FL at W for a rule is
that rule's compatibility lemma at `SemS`. `StackJ`'s first kind is GhostEnd's `LStack.WF`. Its
second and third kinds are the entries the placements' quantifiers insert.

**The hypotheses beside GhostEnd's.**
- **Payload scoping** (`StackJ`'s second line): every variable free in an entry's payload type is
  `Δ`'s or the stack's. Take `allI`'s binder `x`, new to `Δ` and not a stack variable. Then no
  payload type mentions it, which is `allI_RLa`'s `hσT`; `stackTyFresh_of_fresh` gives it the same
  way from payload types scoped in `Δ`. The stacks the clauses produce keep the scoping. A future's
  or an own lend's payload variables are read by the new stack's substitution (`FutOK.pay`,
  `OwnOK.pay`), and under `SubDom` that substitution reads only `Δ`'s variables and the stack's.
- **Scoping** (`Scoped`): the judgement's free variables are `Δ`'s. Typing provides it at a
  derivation's conclusion. A future's inserted variables are not mapped by `extS δ σ αs`
  (`FutOK.vars_sub`), which maps every variable of `Δ` (`Δ.Models`), so they are free in no type of
  the judgement; they are `NsVar`, so under `BindersLow` they are bound in none. That is the
  avoidance `MonoG` asks when a row carries the context to a future.
- **`SubDom`**: `δ` maps only `Δ`'s variables. The relation reads `δ` only at the type's free
  variables and the stack's payloads (`vRLa_congr`'s analogue), so this loses nothing. With it,
  `OwnOK` needs no freshness against `δ` at the binder: the binder is new to `Δ`, so `δ` does not
  map it.
- A row whose premises add types takes their `BindersLow` and `Scoped` as a hypothesis (the rule's
  binder, its intermediate type), as `allI_RLa` takes `hσx`.

**Why not Targets' `SemW`.** Targets' `SemW`/`FL` (`Targets/B/World.lean:116`,
`Targets/B/Guarantees.lean:68`) quantify over every index, with no hypothesis on its stack. At a
stack whose variables a binder of the judgement rebinds, or whose lifetimes do not model `Δ`, the
rows' proofs have nothing to work with. So the probe states FL at W with GhostEnd's index
hypotheses. At the nil index, at a scoped judgement, `SemS` and `SemW₀` read the same judgement:
`δ` off `Δ` is not read. Whether done's `FL M J` should be read at the nil index, or carry these
hypotheses, is recorded for RESTRUCTURE and not changed here.

**W as the interaction's world.**

```lean
def ExtW (i i' : Ix) (ρ : WRes) : Prop := OrdW LSub.empty i i' ρ

def WP (p : Placement) : Targets.SemWorld where
  Stk := Stk
  nil := ([], [])
  Fam fρ ps i := TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1 ∧ StackOK i.2.1 i.2.2
  Upd _ _ ρ _ π := ResU.UpdV ρ π
  Ext := ExtW                     -- OrdW at the empty substitution, a preorder (ExtPreW)
  payStk _ _ := ([], [])          -- OQ-46 (b): a stored payload read stack-free, as vRLs's leaves
  val b A i δ v := if b then vRL p i.2.1 δ A i.2.2 i.1 v else vC false A i.1 (extS δ i.2.1 i.2.2) v
  comp C i δ e := cRL p i.2.1 δ C i.2.2 i.1 e
  held _ := ([], [])
  Stop a b _ := (∀ q, q ∈ b.1 ↔ q ∈ a.1) ∧ (∀ x, x ∈ b.2.1 ↔ x ∈ a.2.1) ∧ b.2.2 = a.2.2
  share T en n i K Φ := contShare (OpTabI.at T i.2) ⟨…⟩ n i.1 K (fun ls t => Φ (ls, i.2) t)
```

These are D1's choices (synthesis D1.i3):
- `held = ([],[])`;
- the run-end relation is Core's `↭` at every index, FIX-RUN-END's field, so `updRefl_of_core` …
  `updLendBack_of_core` (`Targets/B/RunEnd.lean`) apply;
- the stop is R-T1, with the stack fixed by a run;
- the configurations are `TW`'s.

`share` is Core's `contShare` at the record list. At a stack index the ghost-end share is in the
relation's `F_Σ` clause, not in this field, so Targets' `EffInterp` at a stack index is not claimed.
Carrying the ghost-end share in the field would need the payload substitution of the stack's views
in the index (OQ-46's world for a stored payload); that is a step of building W proper, outside the
probe.

`ExtPre (WP p)` is claimed (`ExtPreW`, statement 0). `WLaws (WP p)` is not: Targets' `Mono` reads
a value at every `δ` and every type, with none of the index hypotheses `MonoV` carries.

### 2.6 Build step 0: GhostEnd's branch files

`Below.lean`, `Arising.lean` and `Extend.lean` are on `gfp`, `gfp-arising` and `borrow-callbacks`.
Since their merge base `8a1c326`, nothing in `Core/`, `Support/`, `Paper/` or `experiments/GhostEnd`
has changed on `targets`. The builder brings the three files onto `targets` verbatim from
`borrow-callbacks` 5cfe062, in a commit of their own:
`git checkout borrow-callbacks -- experiments/GhostEnd/GhostEnd/{Below,Arising,Extend}.lean`. It
edits no other GhostEnd file. `ProbeD1` imports `GhostEnd.Extend` where a proof reuses them. The
definitions in this design need none of them, so `lake build ProbeD1` passes without step 0.

---

## 3. The placements are candidates for one relation

`Placement` selects which clauses carry the future-world quantifier. It is not a family of
relations. Statement 0 is proved or refuted per placement. A placement survives when its bundle
and `reconB′`'s acceptance are proved (`Survives e p`, at the term `e` built for `reconB′`). W is
the surviving placement of least `rank`: the cuts order of synthesis §4.2, applied to the proved
bundles.

```lean
def Placement.rank : Placement → Nat
  | .cbpv => 0
  | .binder => 1
  | .binder0 => 2

def Survives (e : Expr) (p : Placement) : Prop :=
  Probe p ∧ ReconAccepted p e
```

A naturality placement (OQ-8 option 1) is not a clause set. It is the claim that the `binder0`
relation without its own-lend conjunct is natural under the freeze binder
(`Targets.FreezeBinderLife`). Statement 7 is its cheap check, and §4.4 records what follows.

---

## 4. Statement 0: W's `U`, `⊸` and `∀` clauses, fixed together

### 4.1 The statements (`Statement0.lean`)

```lean
def ExtPreW (p : Placement) : Prop := Targets.ExtPre (WP p).toBWorld

def FutReLend : Prop :=
  ∀ (δ : LSub) (ρ : WRes) (σ σ' : LStack) (αs αs' αs'' : List Life),
    StackOK σ αs → Fut δ ρ (σ, αs) (σ', αs') → ReLend αs'' αs' →
    ∃ αs₀, ReLend αs₀ αs ∧ Fut δ ρ (σ, αs₀) (σ', αs'')

def MonoV (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls ls' : List SRec) (v : Val) (ρ : WRes)
    (σ' : LStack) (αs' : List Life),
    StackOK σ αs → Ext ls ls' ρ → Fut δ ρ (σ, αs) (σ', αs') → FutAvoidsV A σ σ' →
    TabAtS σ αs ρ → vRL p σ δ A αs ls v ρ → vRL p σ' δ A αs' ls' v ρ

def MonoG (p : Placement) : Prop := …   -- the same for 𝒢⟦Γ⟧ (`gRL`)
def MonoC (p : Placement) : Prop := …   -- the same for the computation relation (`cRL`)

def MonoHide (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes)
    (N : UInt32 → Bool), StackOK σ αs → TabAtS σ αs ρ →
    vRL p σ δ A αs ls v ρ → vRL p (hideS N σ) δ A αs ls v ρ

def MonoHideFromMonoV : Prop := ∀ p : Placement, MonoV p → MonoHide p

def NilSoundV (p : Placement) : Prop :=
  ∀ (δ : LSub) (A : VTy) (ls : List SRec) (v : Val) (ρ : WRes),
    vRL p [] δ A [] ls v ρ → vC true A ls δ v ρ
def NilSoundC (p : Placement) : Prop :=
  ∀ (δ : LSub) (C : CTy) (ls : List SRec) (e : Expr) (ρ : WRes),
    cRL p [] δ C [] ls e ρ → cC C ls δ e ρ

def NilAgreesU (p : Placement) : Prop :=
  ∀ (δ : LSub) (C : CTy) (ls : List SRec) (f : Val) (ρ : WRes),
    vC true (.thunk C) ls δ f ρ → vRL p [] δ (.thunk C) [] ls f ρ
def NilAgrees (p : Placement) : Prop :=
  (∀ δ A ls v ρ, vRL p [] δ A [] ls v ρ ↔ vC true A ls δ v ρ) ∧
  (∀ δ C ls e ρ, cRL p [] δ C [] ls e ρ ↔ cC C ls δ e ρ)

def CallbackExtMut (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life) (T : VTy) (D : CTy)
    (αs : List Life) (ls : List SRec) (f w : Val) (ρf : WRes) (e : LEnt) (α : Life) (ρv ρ : WRes),
    StackOK σ αs → e.x = y → e.k = .mut → y ∉ CTy.binders (.arr (.mut (.var y) T) D) →
    OwnOK δ σ αs e α ρf → LtLife (extS δ σ αs) c α → TabAtS σ αs ρf →
    vRL p σ δ (.thunk (.all y c (.arr (.mut (.var y) T) D))) αs ls f ρf →
    vRL p (e :: σ) (δ.extend y α) (.mut (.var y) T) (α :: αs) ls w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    cRL p (e :: σ) (δ.extend y α) D (α :: αs) ls
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ
def CallbackExtImm (p : Placement) : Prop := …   -- 6.64: `e.k = .imm u`, the callback at a list
                                                  -- `ls'` with `Ext ls ls' ρf` (6.64's record,
                                                  -- `ext_add`), the argument at `Imm 'y T` there

def ForceRow (p : Placement) : Prop :=
  ∀ Δ Γ i C, Ctx.SoloP Γ i (.thunk C) → SemS p Δ Γ (forceE C (.var i)) (.comp C)

def ThawRelend (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec) (f : Val) (ρ : WRes),
    StackOK σ αs → TabAtS σ αs ρ → vRL p σ δ (.thunk C) αs ls f ρ →
    ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwS δ [] σ ds αs ls ρn ∧
      ∀ ls', Ext ls ls' ρz → ∀ αs', ReLend αs' αs →
        (vwS δ [] σ ds αs' ls' ─⋆ vRL p σ δ (.thunk C) αs' ls' f) ρz

def ThunkFRow (p : Placement) : Prop :=
  ∀ Δ Γ M A, SemS p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemS p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))
def ThunkVRow (p : Placement) : Prop :=
  ∀ Δ Γ N C, C.isRet = false →
    SemS p Δ Γ (.val (.lam N)) (.comp C) → SemS p Δ Γ (.val (.lam N)) (.val (.thunk C))
def BangThunkFRow (p : Placement) : Prop := …   -- `bangThunkF` at `SemS`
def BangThunkVRow (p : Placement) : Prop := …   -- `bangThunkV` at `SemS`

def Statement0 (p : Placement) : Prop :=
  ExtPreW p ∧ FutReLend ∧ MonoV p ∧ MonoG p ∧ NilSoundV p ∧ NilSoundC p ∧ CallbackExtMut p ∧
    CallbackExtImm p ∧ ForceRow p ∧ ThawRelend p ∧ ThunkFRow p ∧ ThunkVRow p ∧
    BangThunkFRow p ∧ BangThunkVRow p
```

### 4.2 Why each tests the real question at full strength

- **The clauses are fixed together.** `U`, `⊸` and `∀` are clauses of one `mutual` block, read at
  the guard. No clause is checked at another relation. The three placements differ exactly in the
  flags of `Placement`.
- **The order is W's, and a preorder.** `ExtPreW` is in the bundle. `WP p` is a Targets world only
  if its order composes, and the `U` clause's monotonicity at a future of a future needs it.
  `FutReLend` is the order's lemma that monotonicity at `U` turns on: the futures the clause
  quantifies over are taken after a re-lend, and a monotone value is re-lent at its future.
- **The `U`-clause thaw is proved at the guarded W.** `ForceRow`, `ThawRelend` and the four
  `U`-introduction rows are stated at `vRL p`, not transported from `vRLs`. At `cbpv` and `binder`
  the thunk rows owe the body at every future, and at `cbpv` the own lend at every future, so
  their proof is where the quantifier's cost shows.
- **Monotonicity is along the whole order.** That includes any number of insertions at any depths,
  which the share needs between lenders, and hiding, which `[handle]` needs. A front-only order
  would make `MonoV` easier and hide the between-lenders case. `MonoC` is named because `binder0`
  needs it where `cbpv` and `binder` have monotonicity at `U` by construction (§4.3). `MonoHide`
  is `MonoV`'s hiding instance (`MonoHideFromMonoV`), named because it is where `binder0` is
  tested hardest.
- **The nil slice is checked at every type.** That includes thunks, `∀` and `F_Σ`, which are the
  placements' quantifier sites.
- **The callback-extension fact is at any related argument.** The argument is any value of
  `Mut 'y T` (or `Imm 'y T`, its coherence with the records included) at the extended stack, so
  the `⊸` clause there is exercised, not only at the lend's own view. The callback is a value of
  the constant's callback type `cbUTy` (`Core/EffBorrow.lean`), not a premise. `CDerives` has the
  borrow operations as constants (`Below.lean`'s "What it measures"), so the row must get the
  callback's behaviour at `σ·y` from its value.
- **One quantifier.** Every clause reaches a stack other than its own only through `FutQ`, W's
  order `Fut` or the stack itself as the placement's flag says. At the clause that makes the
  callback's own lend, `OwnPush` at the type the clause reads may follow. This is a property of
  `Relation.lean`'s text, checked by reading it, and it holds at all three placements.
  - The own lend is not a second order. It is the outermost `∀`'s instance, read as the entry of
    the lend the instance names. It is named by the type's binder, so it cannot belong to a
    type-free order. `vRLk`'s extension is relative to the type in the same way
    (`e'.x = x ∨ ¬ CFree e'.x C`).
  - It comes after a future, so a value carried to a future keeps it.
  - The world's `Ext` is the type-free part, `OrdW`, since `Mono` reads no type.
  - At `binder0` neither `U` nor the share quantifies over futures (`FutQ false`). Its coherence
    with W's order is a theorem, not a clause: `MonoV binder0` and `MonoG binder0`, both in its
    bundle, say that its values are Kripke along `Fut`.
  - Failure (d) (§12.2) is a clause changed to reach other stacks by any other means.

### 4.3 Where each placement is expected to be tested hardest [unchecked]

These are readings that order the work. None is derived, and none is an obstruction.

- **`binder0`: monotonicity.** Its `U` clause ranges over the stack itself, so `MonoV` at a `U`
  value needs `MonoC` at its computation. `MonoC` at `⊸` needs the argument read back at the
  original stack, a contravariant step that monotonicity does not give. So at a callback type
  `binder0`'s monotonicity is expected to be "not derived". `MonoHide` is the hiding instance.
  Hiding a name that the stack's inner entries cross changes a stop's depth from `d ≥ 1` to `0`.
  - The piece at depth `d` owes its continuation only at a strictly fresh re-lend
    (`openFS`'s `Forall₂ (· < ·)`).
  - At depth `0` the share is owed at every `ReLend`, equality included (`RelendableN`'s
    `Forall₂ (· ≤ ·)`).
  - So the relation alone does not give the hidden reading.
  - A derivable value meets it by its own derivation, so no arising witness refutes it. The
    expected outcome is "not derived", and with it `binder0`'s `[handle]` row (statement 3), whose
    body is read at `hideS (· == n) σ`, has no context transport.
  - The two programs never hide a name their lenders cross: `reconB′`'s callback row is
    `{wait}`, and `retry` hides `exn`. Their instances do not test this.
- **`cbpv`.**
  - The own lend at `U` reads the thunk type's outermost `∀`, at every future the clause
    quantifies over. The candidate then matches OQ-8 option 2's reading: the `U` clause is Kripke
    over W's order, the callback's own lend included.
  - The plain `∀` at a stack that binds its binder reads the stack's lifetime (`extS`). That is
    consistent at `CallbackExt`'s instance and at `allI` under `StackJ`'s third kind.
  - Monotonicity at `U` is by construction: the clause quantifies over the futures and over the
    own lends at them, and a future of a future is a future (`Fut` is a closure). The work is the
    order's lemmas:
    - a re-lend of a future is a future of a re-lend (`FutReLend`);
    - a future's views are its stack's, the inserted entries' flags off;
    - `Ext` at a resource gives `Ext` at its parts;
    - the entries a composite inserted avoid the type when each step's do.
  - `MonoV` needs no `MonoC` there. The other formers are componentwise, and a leaf reads `vC` at
    `extS δ σ' αs'`, which agrees with `extS δ σ αs` at the type's free variables (`FutAvoidsV`),
    with `vC_local` along `Ext`.
  - The cost is downstream. Every `F_Σ` row must produce continuations at every future of the kept
    part (`OpenSF`), so GhostEnd's stacked lemmas are restated over `OpenSF` (§6.2).
- **`binder`.** As `cbpv` at `U` and in the share, with no type-directed `U` clause. Its `⊸` and
  `∀` clauses quantify over futures, so `MonoC` at them is by construction too, and the `∀`
  clause's own lend is made at every future. It adds obligations at `lam` and `allI`: the body at
  every future, from the induction hypothesis at the future with the context transported
  (`MonoG`).
- **The nil slice, at every placement.** `NilSoundV` and `NilSoundC` instantiate every
  quantifier at the reflexive future and are expected to be mechanical (`bodyS_nil_iff`,
  `vRLs_nil`'s pattern). `NilAgreesU` and `NilAgrees` ask Core's relation to carry obligations it
  has no notion of at the placement's quantifier sites:
  - `binder0`: the own lend at `∀`;
  - `cbpv`: futures and own lends at `U`, futures in the share;
  - `binder`: all of them.

  A Core-related callback keeps its view across a stop, where W re-lends it. So the old-in-new
  direction is not expected to follow from Core's relation at callback types. `NilAgrees` is a
  statement about the identity of two definitions, so a refutation of it at any inhabitant decides
  OQ-58 for the placement's definitions (§6.3). What FL needs at `σ = []` is the `U`-introduction
  rows, which are in `Statement0`. The expected answer to OQ-58 is that Core is not W's `σ = []`
  instance at those types: outcome (c), Core redefined (§12.2).

### 4.4 What statement 0 decides

- **OQ-8.**
  - `cbpv` is W (§3): OQ-8 option 2. D1 then meets "interactions only at cuts", with this cost
    recorded: the `U` clause reads its type's outermost `∀` to name the callback's own lend. That
    reading stays at `U`, the resume cut's value side. Every clause reads the stack's lifetimes at
    its leaves through `extS`, as Core's relation reads its record list; that is not a quantifier.
  - `binder` or `binder0` is W: option 3. Every `⊸` and `∀` clause, or the `∀` clause alone at
    `binder0`, carries a resume obligation away from the cuts. D1 then does not meet "only at the
    cuts". It keeps its rank against D2a and D3 (synthesis §8).
- **Option 1 (naturality).** It is not decided here. Statement 7 tells whether its known witness
  (`mut_not_natural`) arises. A placement that passes makes option 1 unnecessary for D1.
- **"Whether `U` and `⊸` take the same quantifier"** (02-experiments §1.3). Under `cbpv` they do
  not need to, since `⊸` takes none and the `U` clause carries it, as Core's relation does. Under
  `binder` they take the same. If statement 0 holds only after a clause is changed to reach other
  stacks than through `FutQ` and `OwnPush`, that is failure (d) (§12.2).

---

## 5. Statement 1: the guard as `TW`'s run invariant (OQ-45)

### 5.1 The statements (`Statement1.lean`)

```lean
def TabNil : Prop := ∀ ρ : WRes, TabAtS [] [] ρ
def TabParts : Prop :=
  ∀ σ αs ρ₁ ρ₂ ρ, ResU.CompS ρ₁ ρ₂ ρ → (TabAtS σ αs ρ ↔ TabAtS σ αs ρ₁ ∧ TabAtS σ αs ρ₂)

def TabUpd : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ρ π : WRes), StackOK σ αs → TabAtS σ αs ρ →
    ResU.UpdV ρ π → TabAtS σ αs π

def TabRuns : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ls : List SRec) (e : Expr) (Q : List SRec → Expr → WProp)
    (ρ : WRes), StackOK σ αs → TabAtS σ αs ρ → wpG ls e Q ρ →
    wpG ls e (fun ls' t ρ' => TabAtS σ αs ρ' ∧ Q ls' t ρ') ρ

def TabStart : Prop :=
  ∀ δ σ αs ls (e : LEnt) α (d : Bool) (ρ a R : WRes), StackOK σ αs → OwnOK δ σ αs e α ρ →
    TabAtS σ αs ρ → vwE δ e d α ls a → ResU.CompS ρ a R → TabAtS (e :: σ) (α :: αs) R

def TabHide : Prop :=
  ∀ (N : UInt32 → Bool) (σ : LStack) (αs : List Life) (ρ : WRes),
    TabAtS σ αs ρ → TabAtS (hideS N σ) αs ρ

def TabRelend : Prop :=
  ∀ δ σ ds αs αs' ls (ρz ρv R : WRes), StackOK σ αs → ReLend αs' αs → stratS αs ρz →
    vwS δ [] σ ds αs' ls ρv → ResU.CompS ρz ρv R → TabAtS σ αs' R

def TabFut : Prop :=
  ∀ (δ : LSub) (σ σ' : LStack) (αs αs' : List Life) (ρ : WRes), StackOK σ αs →
    Fut δ ρ (σ, αs) (σ', αs') → TabAtS σ αs ρ → TabAtS σ' αs' ρ

def TabResume : Prop :=
  ∀ (δ : LSub) (σi σo : LStack) (ds : List Bool) (αi αo : List Life) (ls : List SRec)
    (ρz ρv ρa R R' : WRes),
    StackOK (σi ++ σo) (αi ++ αo) → stratS (αi ++ αo) ρz → vwS δ [] σi ds αi ls ρv →
    TabAtS σo αo ρa → ResU.CompS ρz ρv R → ResU.CompS R ρa R' → TabAtS (σi ++ σo) (αi ++ αo) R'

def ArisesSound : Prop :=
  ∀ c : Cfg, Arises c → ArisesAt c.σ c.αs c.ls c.ps c.ρf c.ρ c.fρ

def HeldUnderTW (ρ : WRes) (ps : List FrameRec) (σ : LStack) : Prop :=
  ∀ (m : BoCa.Loc) (ψ : CellU BoCa.Loc Val), ρ.get m = some ψ → ψ.kind ≠ Kind.own →
    (∃ e ∈ σ, e.l = m ∧ ∀ u, e.k = .imm u → ∃ r ∈ ps, r.le = m) ∨ m ∉ σ.map LEnt.l

def TabOfTWPointwise : Prop :=
  ∀ (fρ ρf ρ : WRes) (ps : List FrameRec) (ls : List SRec) (σ : LStack) (αs : List Life),
    TW fρ ps (rsOf ls) → Tagged fρ ps ls → StackOK σ αs →
    (∀ e ∈ σ, ∀ u, e.k = .imm u → ∃ r ∈ ps, r.le = e.l) →
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → HeldUnderTW ρ ps σ → TabAtS σ αs ρ

def LamRow (p : Placement) : Prop :=
  ∀ Δ Γ M A C, SemS p Δ (⟨A, true⟩ :: Γ) M (.comp C) → SemS p Δ Γ (.val (.lam M)) (.comp (.arr A C))
def AllIRow (p : Placement) : Prop :=
  ∀ Δ Γ x b M S C, b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → Δ.find? x = none →
    SemS p (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C) →
    SemS p Δ Γ (.val (.lam M)) (.comp (.all x b C))

def BelowRow (p : Placement) : Prop := SemS p belowCtx [] belowTerm (.comp belowType)
def BelowExcluded (p : Placement) : Prop :=
  ∀ δ C ls f v (α αy : Life) (k : BoCa.Loc), αy < α → k ≠ belowEnt.l →
    guardW [belowEnt] [α] (cRL p [belowEnt] δ C [α] ls (.app f (.val v))) (innerView k αy)

def Statement1 (p : Placement) : Prop :=
  TabNil ∧ TabParts ∧ TabUpd ∧ TabRuns ∧ TabStart ∧ TabHide ∧ TabRelend ∧ TabFut ∧ TabResume ∧
    ArisesSound ∧ LamRow p ∧ AllIRow p ∧ BelowRow p ∧ BelowExcluded p
```

`belowEnt`, `belowCtx`, `belowTerm` and `belowType` are `Below.lean`'s `e₀`, `Δ₀`, `allBelowE` and
`allBelowC`, restated as data.

### 5.2 What statement 1 states, and why it is re-scoped

**The synthesis's statement.** Synthesis §11 statement 1 reads: "W's arising guard is read from
`TW`, not from GhostEnd's `TabAtS`. That is OQ-45's first question: is the lend table a `TW`
invariant at every depth (`tabAt_of_TW`, T-ARISE.0, not in Lean)?" T-ARISE.0 reads the table off
one `TW` world. That pointwise form is `TabOfTWPointwise`, and it is not in the bundle.

**What the bundle states instead.** The table holds at every configuration that arises
(`ArisesSound`: `Arises ⊆ ArisesAt`, §11), because every transition of W's semantics keeps it.
This changes the content of statement 1, for three reasons:
- Arising is historical. `TW` records no 6.65 lend (OQ-44), so one world cannot say that a cell
  was folded after a lend opened.
- The pointwise form is expected to fail at `innerView` (below), a configuration that does not
  arise. A refutation there is a fact about the pointwise statement, not about D1.
- Arising tests are directional: a coarser arising set is sound for proving and unsound for
  refuting. The run-invariant form is the one a proof can use, and it reads the guard off `TW`'s
  runs, not beside them.

W's configurations are `TW`'s (`WP p`'s `Fam`), as Core's are. The guard asks more of the local
resource at a stack: the stack's table. The bundle has one fact per transition of `Arises`:
- the nil index: `TabNil`;
- a run: `TabUpd`, [TR] 6.50 keeping every borrow cell's lifetime at its location through `↭`, at
  the innermost lend's `↓α` and at the outermost lend away from the stack's places (`tabAt_updV`
  twice), with `TabRuns` its `wpG` form;
- a part: `TabParts`;
- a lend's start: `TabStart`, 6.112's `И` putting the callback's resource above the fresh lifetime;
- a handler: `TabHide`.

And one fact per configuration the relation quantifies over:
- a re-lend: `TabRelend`;
- a future: `TabFut`;
- the resume composite: `TabResume`. The continuation's share is re-lent, the inner entries'
  views are handed to it, and the handler's answer, made at the kept part's future, is joined to
  it. That is the configuration at which the share's rows call their induction hypothesis. It
  follows from `TabRelend`, `TabParts` and `TabStart`'s argument at an empty view.

These are the synthesis's "It holds for one lend (`wpG_tabAt`) and for one entry
(`wpG_tabAtS_one`)", at every depth. Proved, they make `TabAtS` the stack's arising condition
derived from `TW`'s runs. A guard that some transition from an arising configuration does not
keep would be a guard beside `TW`: failure (b).

**The pointwise check.** The configuration to check `TabOfTWPointwise` against first:
- `innerView k αy` (`RLCompat.lean:381`) at the stack `[x]`, with `x` a `mut` entry at `α`,
  `αy < α` and `k ≠ x`'s place;
- its world is a `TW` world (`tw_innerView`: `TW.alloc`, then `TW.mutFold` at any lifetime);
- it holds a `mut` cell below the stack's lend at a place the stack does not lend.

Nothing in one `TW` world says that the cell was folded after `x`'s lend opened. A refutation there
is a fact about the pointwise statement, not an obstruction to D1: the witness does not arise at
the index `[x]`, since no run from a start that has the table reaches it
(`wpG_below_not_arises`, `Arising.lean:139`). `TabOfTWPointwise` is stated so that this first check
can be run.

### 5.3 Why the rows test the real question

`LamRow` and `AllIRow` are the rows GFP is refuted at in its unguarded form (`Below.lean`). At
`binder` they owe the body at every future, which `lam_RLa` and `allI_RLa` never meet. `BelowRow` is
exactly the refuted derivation. `BelowExcluded` is `below_excluded` at the placement's relation.

`AllIRow` takes the binder new to `Δ`. `allI_RLa`'s added hypotheses follow from it:
- `hσx` (the binder is not a stack variable), from `StackJ`'s kinds as `stackFresh_of_fresh` gives
  it from the first;
- `hσT` (no payload type mentions it), from `StackJ`'s payload scoping, as
  `stackTyFresh_of_fresh` gives it from payload types scoped in `Δ`.

At `cbpv` it also meets a stack whose innermost entry is the binder itself (`StackJ`'s third
kind). There the clause reads the stack's lifetime, and the induction hypothesis applies at
`Δ.extend x b`, where the entry is of the first kind.

---

## 6. Statement 2: the borrow-constant row at `σ·y`

### 6.1 The statements (`Statement2.lean`)

```lean
def SpanW2Row (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (S : Row) (d : Expr) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → (∃ b, Δ.Defines b ∧ OutJ.core.le Δ b A) →
    ¬ VFree x A → ¬ VFree x B → RowSpan admClosedOp Δ x S → RowClass.any.Admits S →
    closedAt 0 d = true →
    SemS p Δ Γ d (.val (.lolli (.ref A) .unit)) →
    SemS p Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))

def SpanW1Row (p : Placement) : Prop := …   -- `withbor1UTy`, with `VScoped Δ A`, as `SpanWithbor1`

def SpanLoadRow (p : Placement) : Prop :=
  ∀ Δ Γ a A B S x, Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    RowSpan admClosedOp Δ x S → RowClass.any.Admits S →
    SemS p Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B S))

def rebView (l : BoCa.Loc) (α : Life) (R : List SRec → Val → WRes → Prop)
    (P₀ : Life → Val → WProp) (ls : List SRec) : WProp :=
  ptoImm l α (fun v σ => R ls v σ ∧ fresh (fun b => reborrow b (P₀ b v)) σ)

def rebF (Tb : Table) (l : BoCa.Loc) (α : Life) (R : List SRec → Val → WRes → Prop)
    (P₀ : Life → Val → WProp) (P : List SRec → Life → Val → WProp) (Q : List SRec → Val → WProp)
    (X : List SRec → Expr → WProp) : List SRec → Expr → WProp :=
  fun ls e => fresh fun b => all fun v => P ls b v ─⋆ wpG ls e (fun ls' t => box b
    (rebView l α R P₀ ls' ─⋆ fun ρ => valPost Q ls' t ρ ∨
      Tb ls' t (fun ls'' e'' => rebView l α R P₀ ls'' ⋆ X ls'' e'') ρ))

def RebRelend (Tb : Table) l α R P₀ P Q (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ X, (∀ ls e ρ, rebF Tb l α R P₀ P Q X ls e ρ → X ls e ρ) → X ls e ρ

def RebFrameR : Prop :=
  ∀ (Tb : Table), Tb.Mono → ∀ (r : FrameRec) α R P₀ P Q ls e,
    r ∈ rsOf ls → (∀ ls', r ∈ rsOf ls' → RebChooseTW ls' r.le (R ls') P₀ (P ls')) →
    Entails (rebView r.le α R P₀ ls ⋆ RebRelend Tb r.le α R P₀ P Q ls e) (ewpTS ls e Tb Q)

def RebChooserNonVacuous : Prop :=
  ∃ (r : FrameRec) (x : LifeVar), r.T.immReborrow (.var x) ≠ r.T ∧ ¬ VFree x r.T ∧
    ∀ ls', r ∈ rsOf ls' →
      RebChooseTW ls' r.le (fun w σ => vC false r.T ls' r.δ w σ)
        (fun β w χ => vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) w χ)
        (fun β w χ => vC true (r.T.immReborrow (.var x)) ls' (r.δ.extend x β) w χ)

def Statement2 (p : Placement) : Prop := SpanW2Row p ∧ SpanW1Row p ∧ RebFrameR
```

`SpanW2Row` and `SpanW1Row` are Targets' `SpanWithbor2` and `SpanWithbor1`
(`Targets/I/Interface.lean:211, 203`) at `Adm = admClosedOp`, class `.any` and `O = OutJ.core`,
stated at `SemS`. Their done-form is `SpanWithbor2 (WP p) OutJ.core admClosedOp .any`, which reads
`SemW₀` at every index (§2.5).

### 6.2 The route, step by step, and what is new

For `withbor` (2) at a stack `σ` (`genSelf`'s at `σ = []`):
1. **The callback at `σ·y`.** `CallbackExtMut p` (statement 0). At `binder0` this is
   `callback_ext`'s argument, and at `σ = []` `callback_ext_one` discharges both tables from the
   callback's resource lying above the lend, as 6.172–6.174 discharge the fresh lifetime's
   quantifier (`⋔r`) at the callback's resource.
2. **The piece to the callback form** (#275's other half). The callback's piece at `σ·y` answers
   in `effRet (e :: σ)` at `['y] B`. It must become the form the fold consumes. Its proof
   re-instantiates `CallbackExtMut` at each fresh lend below `b`: that is `relend_of_openD`
   (`Descend.lean:174`) at a stack. **New**; stated when the route reaches it. At a `LinResume`
   table whose every stop crosses every entry the form is `stack_step_other`'s,
   `OpenS δ (e :: σ) Tab (cbQ δ (e :: σ) Qa) (σ.length + 1) (d :: ds) (b :: bs) [] ls e ρ`. At the
   programs' rows it is the form of item (ii) below.
3. **The fold.** `stack_step_other` (`StackStep.lean:392`), `stack_step_imm` (`:1003`) and
   `stack_spans_mut`/`stack_spans_imm` need `LinResume Tab` (every operation linear and
   non-abortive) and `AllCross` (every stop crosses every entry). So they apply only at linear,
   resuming rows whose stops cross the whole stack, and at `σ = []` there `openS_nil_ewp` closes
   them. `SpanW2Row` and `SpanW1Row` are at `RowClass.any` and at every stack: `genSelf`'s row is
   the affine `Yield`, and `reconB′`'s `timeout` cancels. On `genSelf`'s critical path three items
   are therefore **New**:
   - (i) the stacked commutation at a `ResumeAff` table with a cancel share: `stack_step_other`
     with `opTableO`'s owner hand-back at a cancel (`Drop.lean:49`), read at `σ·new`;
   - (ii) the conversion from the callback's `OpenS` at `[e]` to `Relend (opTableO Tab l T δ) …`,
     which `withborR_compat` consumes; or a route through `OpenD` and `relend_of_openD`, which
     holds at every monotone table, `opTableO` among them (`opTableO_mono`);
   - (iii) `AllCross` relaxed for `SpanW*Row` at `σ ≠ []`: the callback's row need not cross the
     outer entries, so its stops are at depths below `|σ| + 1`.

   At `cbpv` and `binder` each item is restated over `OpenSF`, the futures quantifier carried
   through each unfolding. **New**: GhostEnd's argument at a stack-indexed least fixed point.

   `stack_step_other`'s callback form puts the answer above the outermost lend (`cbQ`'s `boxTop`).
   An answer that keeps a view of `σ` (#276's shape) needs the form `bodyAtD` has. That is not
   needed at `σ = []`, the only stack the programs' borrows sit at, but `SpanW2Row` is at every
   stack.
4. **The unwinding frame and the cancel.** `withborR_compat` (`Drop.lean:108`) for 6.65, from
   (ii): `ewp_then_owner` puts the owner back at a cancel and `d` disposes of it.

For `withbor` (1) the same, with `CallbackExtImm`, `stack_step_imm` (under the same two hypotheses,
so (i)–(iii) at 6.64) and `ewpTS_I_frameR`. The cancel path over a 6.64 frame is **not built**
(p10 §5.1 X.4). It is the 6.64 analogue of `withborR_compat`:
- `RelendI` (`ImmLend.lean:128`) in place of `Relend`;
- `ownerI` in place of `owner`;
- an `opTableO` whose cancel hands back `ownerI`.

Its proof follows `withborR_compat`'s, with 6.64's exit at the cancel's end. `reconB′`'s second
borrow needs it.

**[TR] 6.150 at a resuming table** (`RebFrameR`). This is Law 2 for `withload`, in scope whatever
OQ-29 decides (synthesis D1.i5).

The lift is shaped as GhostEnd's three proved lifts, each of which hands the lender's resource
back through a wand in the frame's postcondition: `relendG` and `relendIF` by `ptoOwn ─⋆ …`,
`antiF` by `ptoMutS ─⋆ …`. In 6.150's printed proof the view `ρᵢ` ends in the garbage
(G5: `ρᵢ ● ρ_b ↭ ρ_Q ● ρᵢ ● ρ⁺′`), not in the callback's answer, and a `withload` callback is
handed only `P̂` at `β`. So the callback cannot owe the outer view at a stop. The lift keeps a copy
and hands it back.

The proof follows the printed proof of 6.150 once per unfolding of `RebRelend`, as
`ewpTS_M_frameR` follows 6.65's:
- the view is split by `ptoImm_dup` (`Frames.lean:110`): one copy for `wpG_reborrow`, one kept;
- `wpG_reborrow` (`Core/Reborrow.lean:232`) runs on the first copy. Its postcondition is over any
  term, so "a reborrow ends at a stopped operation as at a return": 6.52's subtraction at a stop is
  inside it;
- `wpG_frame` (`Core/EffWp.lean:1005`) carries the kept copy to the run's end, at a list with the
  same members;
- `rebF`'s wand takes the copy back. At a return the answer is in `Q`. At a stop the table owes the
  view at the resumption's list beside the next unfolding, which the induction hypothesis closes
  (`Tb.Mono`). The premise owes the view at that list; a row discharges it from the copy handed
  back when its `R` is carried along `Ext`, as 6.64's `hQ` carries its postcondition;
- the chooser is re-instantiated at each resumption's list, where `rebChooseTW_top` supplies it.
  The record stays on the list along the unfoldings' `Ext`s, since the kept view is an `imm` cell
  at its place (`Rel`, `Keeps`).

If the wand form does not close, the alternative puts the hand-back on the stop disjunct only and
forgets the copy at a return by 6.149 (`wpTS_I_forget`; its `wpG` form is not built).

`RebFrameR`'s chooser hypothesis is shaped as `rebChooseTW_top` supplies it: at every list that
holds the view's record, with `R` and `P` read at that list. `RebChooserNonVacuous` is its
non-vacuity at a record whose payload is not data (`r.T.immReborrow ≠ r.T`), the only place 6.150
does anything. Its proof is `rebChooseTW_top` at each such list, at `δ' = r.δ`.

**`SpanLoadRow`.** At a data payload `Imm̲ 'y A = A` (`VTy.immReborrow`, `Core/Types.lean:1447`).
The callback then gets data, and no entry spans the stop. That is the case `reconB′`'s reads are,
and they complete before the next `wait` (synthesis §11), so the programs do not exercise
`RebFrameR`. At a payload with inner places, 6.150's image holds views at the new lifetime at the
payload's chain positions. The stack then needs an entry for a reborrow, a kind GhostEnd's
`LEnt` lacks (`mut` and `imm v` only) and WorldW's `OEnt` has (`reb`). That would be a finding
about what `σ` holds (OQ-44), recorded, not a new relation.

### 6.3 OQ-58: Core as W's `σ = []` instance

`NilAgrees p` and `NilAgreesU p` are statement 0's (`Statement0.lean`), beside its bundle. OQ-58 is
decided there, after the bundle's work, at the placement W is.

`NilAgrees` states that two definitions are one relation at `σ = []`. A refutation of it at any
inhabitant, arising or not, decides OQ-58 (a) negatively for the placement's definitions. It is
therefore exempt from §11's items 2 and 3, which are about what a program reaches, not about what a
definition is. The outcomes:
- `NilAgrees p` proved: Core is W's `σ = []` instance (OQ-58 (a)).
- `NilAgrees p` refuted, with the sites at which it fails, each with the introduction rows that
  hold there at W: outcome (c) (§12.2). That is a cost, not an obstruction to D1 and not a stop.
  `NilSoundC` still carries W's programs to Core's adequacy (§9.1).
- Neither proved nor refuted: "not derived, no obstruction verified", and (c) is not entered.

---

## 7. Statement 3: `[handle]` with a lend open (#278)

```lean
def HandleRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ Γr Γc : Ctx VTy) (e : Expr) (S : Row)
    (E : List (Qual × VTy × VTy)) (n : UInt32) (A R : VTy) (ir ic : Nat),
    Targets.Row.NU (Row.ofEff n E 0 ++ S) →
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.SplitP Γ₁ Γr Γc → Ctx.SoloP Γr ir (retTy S A R) →
    Ctx.SoloP Γc ic (clausesTy S R E) → n ≠ 0 → (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 →
    SemS p Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A)) →
    SemS p Δ Γ (hndTerm n ir ic e) (.comp (CTy.effOf S R))

def Statement3 (p : Placement) : Prop := HandleRow p
```

`HandleRow` is Targets' `HandleCompat` (`Targets/I/Device.lean:83`) at `SemS`, at every stack.

**The route.**
- **The body is read at `hideS (· == n) σ`.** Inside the handler no stop of `n` reaches a lend
  outside it. So the body's stops of `n` are at depth `0`: the lend open, the continuation
  re-lendable over the stack. That is GhostEnd's "second kind of stop, at an operation handled
  inside the borrower" (step 3f).
- **The other stops.** They pass the handler frame and keep their depth. That is "a handler frame
  passing the lender's stops".
- **`AllCross` is relaxed.** `n` crosses no entry of the body's stack. `retry`'s `exn` is this
  case.
- **The induction.** `ewp_handle`'s inner least-fixed-point induction (`Core/EffRules.lean:615`)
  is run over the stacked piece. At each stop of `n` the clause gets `κ` at `kTy`.
- **`κ`'s side.**
  - At `binder0`, `κ` is a `U` value at the stack itself, and Core's `vC_kTy_of_kapRel` pattern
    applies at the stack.
  - At `cbpv` and `binder`, `κ`'s `U` clause ranges over futures of the handler's stack. The
    piece's share (`OpenSF` at `hideS (· == n) σ`) gives them: a future of the hidden stack is a
    future of the handler's, the hiding being one of its steps (`Fut` is a closure).
- **The context.** It is transported to the hidden stack by `MonoHide`, which statement 0's `MonoV`
  gives (`MonoHideFromMonoV`).

**Why full strength.** At every stack, so a stop handled inside a borrower and a stop passing the
handler to the lenders both occur. At every row of the class `.any`, so the affine cancel is
included.

---

## 8. Statement 4: `[allR-E]` at W

```lean
def ovalU (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Targets.Inst.OCTy → RowEnv → Val → WProp
  | .allR ρ k C, η, v => fun r => ∀ s : Row, k.cls.Admits s → (∀ o ∈ s, k.adm o) →
      ovalU p σ δ αs ls C (Function.update η ρ s) v r
  | C, η, v => vRL p σ δ (.thunk (Targets.Inst.OCTy.den η C)) αs ls v

def ovalW (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Targets.Inst.OVTy → RowEnv → Val → WProp
  | .thunk C, η, v => ovalU p σ δ αs ls C η v
  | .bang A, η, v => fun r => r = PMap.empty ∧ ovalW p σ δ αs ls A η v r
  | A, η, v => vRL p σ δ (Targets.Inst.OVTy.den η A) αs ls v

def AllREW (p : Placement) : Prop :=
  ∀ σ δ αs ls (ρv : RVar) (k : RowCon) (C C' : Targets.Inst.OCTy) (η : RowEnv)
    (s : RowEnv → Row) v r, k.cls.Admits (s η) → (∀ o ∈ s η, k.adm o) →
    (∀ η', Targets.Inst.OCTy.den η' C' = Targets.Inst.OCTy.den (Function.update η' ρv (s η')) C) →
    ovalW p σ δ αs ls (.thunk (.allR ρv k C)) η v r → ovalW p σ δ αs ls (.thunk C') η v r

def AllRMono (p : Placement) : Prop :=
  ∀ σ δ αs ls ls' ρv k C η v r σ' αs',
    StackOK σ αs → Ext ls ls' r → Fut δ r (σ, αs) (σ', αs') →
    (∀ η', FutAvoidsV (Targets.Inst.OVTy.den η' (.thunk (.allR ρv k C))) σ σ') → TabAtS σ αs r →
    ovalW p σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    ovalW p σ' δ αs' ls' (.thunk (.allR ρv k C)) η v r

def Statement4 (p : Placement) : Prop := AllREW p ∧ AllRMono p
```

`ovalW` is RESTRUCTURE §4.2's `I.ovalW` over W: the relation at `U(∀ρ:k. C)` is the intersection
over admissible rows on the same value. `AllREW` is elimination at every stack, with a lend open;
by the intersection it is instantiation. `AllRMono` is the step `reconB′` needs: `retryR` is made
at `σ = []` and instantiated inside the borrow's callback at `σ·y`. It follows from `MonoV` at
each instance, and at `binder0` from `MonoC` (§4.3). `J₁`'s syntactic `[allR-I]`/`[allR-E]`
(`RC_allRI`, `RC_allRE`, `Targets/Instance/Typing.lean`) are not built. The probe needs their
semantic counterpart only: `AllREW`, and the intersection at introduction, which is the λ-value's
`SemS` at every admissible instance.

---

## 9. Statement 5: the programs

### 9.1 The statements (`Programs.lean`)

```lean
def semTyping (p : Placement) : Targets.TypingJ :=
  ⟨fun Θ Δ Γ e j => ∀ η, Θ.Models η → SemS p Δ (Γ η) e (j η), Targets.OutJ.core⟩

def GenSelfAccepted (p : Placement) : Prop :=
  Targets.AcceptedAt (semTyping p) Targets.genSelf Flag (Val.inj₂ .unit)

def ReconAccepted (p : Placement) (e : Expr) : Prop :=
  Targets.AcceptedAt (semTyping p) e (.tensor Flag Flag) (Val.pair (Val.inj₂ .unit) (Val.inj₁ .unit))
```

`AcceptedAt` (`Targets/I/Programs.lean:259`) asks:
- the program typed at a data answer; here `SemS` at `[]`;
- every run under the platform with no operation safe, and terminating with the memory empty;
- some complete run answering `v`, the run exhibited.

**The route for the runs.** `SemS` at `σ = []` gives `cRL p [] …`. `NilSoundC` gives Core's `cC`,
which is `coreB`'s `comp`, and `adequateRetAt_core_none` (`Targets/B/BoLo.lean:195`) gives safety
and termination. The answer's run is written out, or read off an interpreter proved to agree with
`Step1`. `genSelf_eval` is evidence, not the run.

### 9.2 Building `reconB′`

- **The term.** It is synthesis §11's. `retryR` and `timeoutR` are at Core's encoding with A's
  types (RESTRUCTURE §4.2):
  - `retryR : !U(∀ρ ∌ exn. !U(1 → F (exn ⊙ ρ) bool) → F ρ bool)`;
  - `timeoutR : !U(∀ρ ∌ wait. U(1 → F (wait ⊙ ρ) bool) → F ρ bool)`.

  `*b` is `withload` at the data payload `Flag`. Answer `(tt, ff)`.
- **The typing question to settle first.** `retry` calls its body twice, once from its clause, so
  `retryR`'s body argument is `!U`, and `bangThunkV` types a `!U` thunk only over a persistent
  context (`Persistent Γ`); `vRL`'s `!` clause gives it the empty resource. `retry`'s body as
  written captures the `Imm` view `b`, which is not persistent, so the term does not type as
  written. Building `reconB′` chooses a shape that keeps the operator's structure (the scheduler
  and `timeout` outside their borrows, `retry`'s handler inside the first, a cancelled `wait`
  under `timeout`) and whose retried body does not capture the view, and records the choice with
  its reason. The choice changes the program, not the probe's statements; it may move `retryR`'s
  type, and with it the row family `AllREW` is instantiated at.
- **Its rows beyond `genSelf`'s.** `SpanW1Row` with the 6.64 cancel path (§6.2), `HandleRow` with
  the handler inside a borrow (`retry`), `AllREW`/`AllRMono`, and `SpanLoadRow` at a data payload.

### 9.3 `genSelf`'s rows

`genSelf` sits at `σ = []`, with one lend `[y]` inside the callback. Its rows are:
- `HandleRow` at `[]`;
- `SpanW2Row` at `[]` at the row `{Yield : Flag ↠^aff 1}`, with the affine cancel through
  `withborR_compat`. The row is affine, so `StackStep.lean`'s fold lemmas, which need
  `LinResume`, do not fold it: §6.2's items (i) and (ii) do;
- inside the callback at `[y]`:
  - `withswap`, 6.66 at `[y]`; its callback `dupFlag` is pure;
  - `[perform]` at depth 1;
  - `[let]`, whose frame holds the view and data across the yield (`bind_RL`'s step at the
    stacked relation);
  - `forget` at `Mut 'y Flag`;
  - `tensorE`, `sumE`, `var`;
- around the callback: `allI` and `lam`;
- around the borrow: `alloc`, `free`, `bind` and `app`.

Every row is stated at `SemS` (statements 0–4) or is a routine row of GhostEnd's step 3f table, to
be stated at `SemS` the same way (`[ret]`, the value rules, `alloc`, `free`, `forget`) when the
program is composed.

---

## 10. Statements 6 and 7

```lean
def ThenRow (p : Placement) : Prop :=
  ∀ Δ Γ Γ₁ Γ₂ M N D A B (S : Row), Ctx.SplitP Γ Γ₁ Γ₂ → S.NZ → S.Uniq → (S.Unr → Persistent Γ₂) →
    (∀ x ∈ VTy.binders A, ¬ NsVar x) →
    SemS p Δ Γ₁ M (.comp (CTy.effOf S A)) →
    SemS p Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)) →
    SemS p Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf S.abortOnly .unit)) →
    SemS p Δ Γ (thenE N D M) (.comp (CTy.effOf S B))
```

**Statement 6, the sample row.** `ThenRow` at every stack contains the case GhostEnd step 3f leaves
open: a finaliser frame the borrower wrote, frozen in `κ` with a lend open beneath it, unwinding
when an outer handler cancels `κ` at an affine row crossing the lend. Under ghost end the stop
dropped the lend's view. The cancel runs `κ`'s frozen frames through `cancelOwed`, which the
stopped piece owes without the views (`stopS`'s `opTable` share). So a finaliser `D` whose context
holds the view meets the cancel without it. The row tests whether the cancel re-lends for such a
finaliser, or whether `D`'s context must exclude the lend's views (a typing side condition
`effThen` does not carry today). Neither program uses `[then]` in the borrower. Statements 0–4 meet
the cancel cut only through the borrow constants' own owner frames, so this row tests whether
their pattern reaches a frame the program wrote.

**Statement 7, the side check.** `Targets.NotVDenNaturalArises` (`Targets/I/Binder.lean:235`), as it
stands: does `mut_not_natural`'s cell arise in a configuration Core's world reaches? It bears on OQ-8
option 1 and on K.2's binder form, not on statements 0–6.

---

## 11. The arising check (`Rules.lean`, `Arising.lean`)

A configuration that refutes a statement of this probe is reported as an obstruction only when all
of the following hold:

1. **The negation is proved in Lean.** It instantiates every hypothesis of the refuted statement at
   concrete values, as `not_gfpAt_below` does.
2. **The configuration arises**: `Arises c`, with the path exhibited, a proof built from its
   constructors. `Arises` is reachability from the nil index by the transitions of W's semantics:

   ```lean
   structure Cfg where
     fρ : WRes
     ρf : WRes
     ρ : WRes
     ps : List FrameRec
     ls : List SRec
     σ : LStack
     αs : List Life

   def RunEnd (c : Cfg) (e : Expr) (c' : Cfg) (t : Expr) : Prop := …  -- `wpG`'s run conjuncts,
                                     -- the stack fixed, the garbage joining the frame
   def LendMut (c c' : Cfg) (e : LEnt) : Prop := …   -- `TW.mutFold`'s premises; the entry pushed
                                     -- below the callback's resource; the view its cell
   def LendImm (c c' : Cfg) (e : LEnt) : Prop := …   -- `TW.immFrame`'s premises, the same

   mutual
   inductive Arises : Cfg → Prop where
     | nil {fρ ρf ρ ps ls} : TW fρ ps (rsOf ls) → Tagged fρ ps ls → ResU.Hash ρf ρ →
         ResU.CompS ρf ρ fρ → Arises ⟨fρ, ρf, ρ, ps, ls, [], []⟩
     | run {c c' Δ Γ e₀ j γ t} : Arises c → ProbeRules Δ Γ e₀ j → (∀ w ∈ γ, ArisesVal w) →
         RunEnd c (substAll γ e₀) c' t → Arises c'
     | part {c ρ₁ ρ₂ ρf'} : Arises c → ResU.CompS ρ₁ ρ₂ c.ρ → ResU.CompS c.ρf ρ₂ ρf' →
         ResU.Hash ρf' ρ₁ → Arises ⟨c.fρ, ρf', ρ₁, c.ps, c.ls, c.σ, c.αs⟩
     | lendMut {c c' e} : Arises c → LendMut c c' e → Arises c'
     | lendImm {c c' e} : Arises c → LendImm c c' e → Arises c'
     | hide {c} (N : UInt32 → Bool) :
         Arises c → Arises ⟨c.fρ, c.ρf, c.ρ, c.ps, c.ls, hideS N c.σ, c.αs⟩
   inductive ArisesV : Cfg → Val → Prop where
     | ret {c c' Δ Γ e₀ j γ v} : Arises c → ProbeRules Δ Γ e₀ j → (∀ w ∈ γ, ArisesVal w) →
         RunEnd c (substAll γ e₀) c' (.val v) → ArisesV c' v
     | view {c c' e} : Arises c → (LendMut c c' e ∨ LendImm c c' e) → ArisesV c' (.loc e.l)
   inductive ArisesVal : Val → Prop where
     | at {c v} : ArisesV c v → ArisesVal v
   end

   def ArisesNonVacuous : Prop := ∃ c : Cfg, Arises c ∧ c.σ ≠ []
   ```

   Each transition is a step of W's semantics:
   - at the nil index the arising set is `TW`'s, Core's settled one;
   - a run of a term the probe's rules derive, its captured values arising, ends as `wpG`'s run
     ends: the machine's run, `↭` on the local part, a tagged `TW` world at the end;
   - a part of the local resource is taken, the rest joining the frame;
   - a lend row opens a lend: `TW.mutFold`'s or `TW.immFrame`'s step, its entry pushed below the
     callback's resource (6.112's `И`);
   - a handler is installed.

   So `Arises` under-approximates what arises, which is the direction a refutation needs.
   - `ArisesAt` is the pointwise consequence: the world `TW`'s, the stack consistent with it, the
     local part consistent with the table. Statement 1 proves `Arises ⊆ ArisesAt` (`ArisesSound`).
     It is a necessary condition, used to exclude a witness, never to admit one.
   - `ArisesNonVacuous` (some configuration with an open lend arises) is proved first, so that the
     check can be passed at all.
   - A run inside a resumed continuation runs a reduct, not a derived term. So `Arises` reaches a
     continuation's re-lent start (a run to the resumption, a part, the re-lends), but not the
     configurations further inside it. A refutation that needs one of those is recorded as a fact
     about the statement until a transition for it is added with its justification.
3. **Its values arise**, when the refutation is about a value or a computation in the relation
   rather than about a derivation: `ArisesV c v`. The value is the answer of a run of a term the
   probe's rules derive, the `ProbeRules` derivation exhibited, or the place a lend row hands its
   callback. A relation-level value that no derived term produces does not arise (✓-valid is not
   reachable).
4. **The refuted statement is ours.** Every statement here is. A refutation is reported against
   the statement, with the printed lemma it reads named. The paper is not wrong.

**The rule set.** `ProbeRules` is the rule set items 2 and 3 read: Core's rules without resuming
`unr` operations, with the three spanning rules the probe validates.

```lean
def ProbeRules (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  ∀ J : TypingJ, J.out = OutJ.core → ExtendsNU J → SpanRule1 J admClosedOp →
    SpanRule2 J admClosedOp → SpanRuleLoad J admClosedOp → J.at Δ Γ e j
```

It is the least typing system at Core's outlives judgements that holds Core's unr-free fragment
and is closed under its rules (`ExtendsNU`, Targets' end-state pin) and under the spanning rules of
`withbor` (1), `withbor` (2) and `withload` at `admClosedOp`. A derivation is exhibited by
building the judgement from those closure properties.

A refutation that fails 2 or 3 is recorded as a fact about the statement, never as an obstruction to
D1. `TabOfTWPointwise` at `innerView` (§5.2) is the first instance: its world passes `ArisesAt`'s
`TW` part and fails the table, and it is not in `Arises`. `NilAgrees` is exempt from 2 and 3: it
is about the identity of two definitions (§6.3).

---

## 12. Success, failure, and the stop rule

### 12.1 Success

- `Survives e p` is proved at a placement `p`, at the term `e` built for `reconB′`. That is
  `Probe p` (statements 0–4, `GenSelfAccepted p` and `ThenRow p`) and `ReconAccepted p e`. W is
  the surviving placement of least `Placement.rank`.
- The placement is recorded with its consequence (§4.4):
  - `cbpv`: OQ-8 option 2, and D1 meets "two algebras with interactions only at cuts", with the
    own-lend cost at `U` recorded;
  - `binder` or `binder0`: option 3, with a resume obligation in the binder clauses.
- OQ-58's outcome is recorded (§6.3).
- Law 2 for `withload` is recorded: `RebFrameR` and `RebChooserNonVacuous` proved, and
  `SpanLoadRow` proved or its entry-kind finding stated.

The rules these two programs use then have their laws at W. What stays open even then: GFP's
induction over the rows the programs do not use, among them `unfoldN`, the other `*U` constants at
W, the reborrow followed by the outer continuation (#276), and a spanning borrow whose answer keeps
a view of the stack. One sample row (statement 6) does not bound them.

### 12.2 Failure

Each failure is machine-checked (§11):

- **(a)** A statement of `Probe p` is refuted at an arising configuration at every placement whose
  statement 0 holds. What D1 loses:
  - statement 1: the guard is beside `TW`, which is (b);
  - statement 2: ghost end does not carry a borrow constant across a stop, and D1 keeps tier 1
    only;
  - statement 3: handlers inside a borrower that suspends outward;
  - statement 4: row-polymorphic higher-order functions inside a borrower;
  - statement 6: user finalisers frozen with a lend open beneath them.

  A's S2 and S3 at `J₂` ride on FL at W (synthesis §2.5), so `J₂` drops the refuted rule and A's
  (S) properties hold for what remains. At `J₁` they are unaffected.
- **(b)** A statement is provable only with a guard beside `TW`, or a second relation family:
  - a guard beside `TW` is stronger than `TabAtS`, or one of statement 1's facts fails at an
    arising configuration;
  - a second relation family is a relation for callbacks or continuations apart from `vRL`/`cRL`.

  Stop and report.
- **(c)** `NilAgrees p` is refuted at the placement W is (§6.3). Core is then redefined as W's
  `σ = []` instance (OQ-58 (b)), a kernel change with a SPEC entry, and every Core theorem is
  re-proved through FL at W. Not a stop. The expected case (§4.3).
- **(d)** Statement 0 holds only after a clause is changed to reach a stack other than its own by
  something other than `FutQ`, followed at the own-lend clause by `OwnPush` at the type it reads
  (§4.2). W would then carry two quantifiers, a relation family in all but name. Stop and report.

A statement neither proved nor refuted is reported as "not derived, no obstruction verified",
with the step it stopped at.

### 12.3 The stop rule

Statement 0 works at `p` when `Statement0 p` is proved. Statement 1 is attempted only at
placements where statement 0 works, and statements 2–6 only where statements 0 and 1 work. **If
`Statement0 p` is proved at no placement, the probe stops after statement 0 and reports**, for each
placement:
- the facts proved;
- the facts refuted, each with its arising check;
- the facts not derived, each with the step it stopped at.

(b) and (d) stop the probe wherever they occur.

---

## 13. Order of work, and the build

Unknowns first:

1. **Step 0** (§2.6).
2. **Statement 0, the discriminating facts first**:
   - the order's lemmas: `ExtPreW` (by the closure and `Ext.trans`), then `FutReLend`;
   - `MonoHide binder0` and `MonoC binder0`;
   - at `cbpv`, `ThunkVRow` at the own lend at a future, and `AllIRow`'s third-kind stack;
   - at `binder`, `LamRow` at a future;
   - then `MonoV`/`MonoG`, `MonoHideFromMonoV`, `NilSound*`, `CallbackExt*`, `ForceRow`,
     `ThawRelend` and the thunk rows.

   Apply the stop rule. `NilAgrees` (OQ-58) is attempted after the bundle, at the placements where
   it holds.
3. **Statement 1**: `ArisesNonVacuous` first; then `TabUpd` (6.50 at both ends of the stack) and
   `TabRuns`, `TabStart`, `TabHide`, `TabRelend`, `TabFut`, `TabResume`, `ArisesSound`; the first
   check of `TabOfTWPointwise` (§5.2); then `LamRow`, `AllIRow`, `BelowRow`, `BelowExcluded`.
4. **Statement 2**:
   - the 6.64 cancel path, `RebFrameR` and `RebChooserNonVacuous` first, the items no proof has
     touched;
   - then #275's conversion and §6.2's items (i)–(iii), the fold, at `OpenS` or `OpenSF`;
   - then `SpanW2Row`, `SpanW1Row`, `SpanLoadRow`.
5. **Statement 3**, then **statement 4**.
6. **Statement 5**: compose `genSelf`; build `reconB′` (§9.2) and compose it.
7. **Statement 6**, then **statement 7**.

**The build.** Iterate with `lake build ProbeD1.<Module>`. `lake build ProbeD1` at milestones.
Every theorem's `#print axioms` is within `[propext, Classical.choice, Quot.sound]`; an
`Axioms.lean` prints them once theorems exist. No `sorry` or `axiom` lands in a finished file; an
unproved step in progress is an enumerated `sorry` in a scratch file, never committed. No `Core/`
edit. Work on `targets`; never push.

---

## 14. Report lists

**Printed hypotheses the routes must spend** (none is spent yet; there is no proof):
- 6.65's `P̂ ⊧ [β] P̂` at each re-lend (`wpG_M_frameX`'s `hP`);
- 6.64's `AdmWf` and its `hQ`, the postcondition carried along `Ext` (`opTable_extR`,
  `ewpPostR_ext`);
- 6.66's premises at `withswap` (`wpG_M_antiFrameX`);
- 6.150's H11 (`β` below the world) and H16 (the chooser) at each unfolding of `RebRelend`;
- 6.149 (`wp-I-forget`), in 6.150's alternative route only;
- 6.112's `И` at each lend's entry and each re-lend (`fresh_frame`, `FutOK.below`, `OwnOK.below`);
- 6.48 and 6.49 at every run's end through `Upd = ↭` (`updFrame_of_core`, `updSeq_of_core`);
- 6.50 at every run's end, for the table (`TabUpd`);
- 6.62, `G⟦Γ⟧δ(γ) ⊧ [@aδ] G⟦Γ⟧δ(γ)`, at the borrow rows: the callback's context above the fresh
  lend (`gSepC_outlives`, `frame_outlives`).

**Uniqueness and functionality results.**
- Expected to be used: `ResU.CompS.functional`, `ResU.Flat.functional`, `CellU.immOf_inj` (in
  `ptoImmS_join`), `dropC_disj`.
- Not expected: the machine's determinism (`AStep1.deterministic`). The measure is the piece's own
  least fixed point, the typing derivation and a loop's budget, as in GhostEnd step 3a.

**Printed lemmas in the run-up that are untranscribed.**
- [TR] 6.150 at a resuming table: `RebFrameR` states it, shaped as the other lifts. Its added step
  `ptoImm_dup` and its exit at a stop (inside `wpG_reborrow`) are proved; the `wpG` form of 6.149,
  which only the alternative route needs, is not built.
- 6.64, 6.65 and 6.66 at a resuming table are lifted (`ewpTS_I_frameR`, `ewpTS_M_frameR`,
  `ewpTS_M_antiFrameR`), at every monotone table. Their stacked folds (`stack_step_*`) are proved
  at `LinResume` tables only; the folds at `ResumeAff` tables are §6.2's new items.
- 6.172–6.176 are transcribed at Core's relation and restated at W as the rows of statements 2 and 4.
- The 6.64 cancel path is ours, not a printed lemma.

**Hypotheses added in the statements.**
- `AllIRow`'s `Δ.find? x = none`, the binder new to `Δ`, as `allI_RLa`'s `hσx` comes from it.
- `SemS`'s `BindersLow`, and `ThenRow`'s hygiene of its intermediate type: binder hygiene against
  the names futures give their entries (§2.2, *Names*). `BindersLow` constrains the judgement, not
  the stack. It holds at both programs' derivations, whose binders are small. It is a guarantee
  gap: FL at W says nothing about a program that binds a variable at or above `nsBase`. Its
  discharge is either of two things, neither built:
  - a renaming lemma (α-renaming a derivation's lifetime binders preserves `CDerives` and `SemS`),
    which puts every derivation's binders below `nsBase`;
  - a fresh-name supply relative to the judgement in place of the numeric bound.
- `SemS`'s `Scoped` and `SubDom`. Typing gives `Scoped` at a closed program's root; a row with an
  intermediate type takes it of that type, as it takes `BindersLow`. The gap is of the same kind:
  FL at W says nothing about a derivation with an unscoped intermediate type until a
  lifetime-substitution lemma on derivations replaces its free variables by `Δ`'s, which is not
  built. `SubDom` loses nothing, since the relation reads `δ` only at the type's free variables.
- `StackJ`'s payload scoping, with `FutOK.pay` and `OwnOK.pay`: added so that `allI_RLa`'s `hσT`
  holds at every stack `SemS` admits and at every stack the clauses produce. At `σ = []` they are
  vacuous. At the programs every payload type is scoped in its `Δ`.
- `RebFrameR`'s chooser at the lists that hold the view's record, with `R` and `P` read at the
  list (§6.2); its non-vacuity is `RebChooserNonVacuous`.
- `StackJ`'s second and third kinds, which widen GhostEnd's `LStack.WF` to the entries the
  placements' quantifiers insert. At `σ = []` they are vacuous.
