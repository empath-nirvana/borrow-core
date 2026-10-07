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

**Rules this design keeps.** Nothing breaks the borrow calculus: its guarantees, not BoLo's text.
The paper is not wrong; every refutation the probe can produce is of a statement of ours. An
obstruction is only an elaborating `def … : Prop` with its negation proved at a configuration
whose world arises in `TW` (§11); otherwise the report says "not derived, no obstruction
verified". No step-indexing: the relation is one `mutual` block, structural on the type. No
relation family beside W's one relation: the three placements of §3 are candidates for that one
relation, and exactly one survives. Multi-shot is ignored. The core is linear.

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
| 0. W's `U`, `⊸`, `∀` clauses fixed together | `vRL`, `cRL` at `Placement.{cbpv, binder0, binder}`; `Statement0 p` = `MonoV`, `MonoG`, `NilSoundV`, `NilSoundC`, `CallbackExtMut`, `CallbackExtImm`, `ForceRow`, `ThawRelend`, `ThunkFRow`, `ThunkVRow`, `BangThunkFRow`, `BangThunkVRow`; beside it `MonoC`, `MonoHide`, `NilAgreesU`, `NilAgrees`, `AgreeOnRules` | OQ-8; whether `U` and `⊸` take one quantifier; OQ-58's shape |
| 1. the guard from `TW` | `Statement1 p` = `TabNil`, `TabParts`, `TabRuns`, `TabStart`, `TabRelend`, `TabFut`, `LamRow`, `AllIRow`, `BelowRow`, `BelowExcluded`; beside it `TabOfTWPointwise` | OQ-45's first question; `lam`, `allI` and `not_gfpAt_below`'s derivation at W |
| 2. the borrow-constant row at `σ·y` | `Statement2 p` = `SpanW2Row`, `SpanW1Row`, `RebFrameR`; beside it `SpanLoadRow` | #275; OQ-58 through `NilAgrees`; [TR] 6.150 at a resuming table (Law 2 for `withload`) |
| 3. `[handle]` with a lend open | `Statement3 p` = `HandleRow`, `MonoHide` | #278 |
| 4. `[allR-E]` at W | `Statement4 p` = `AllREW`, `AllRMono` | Law 1's elimination inside a borrow |
| 5. the programs | `GenSelfAccepted p`, `ReconAccepted p e` | `genSelf`, `reconB′` accepted at W |
| 6. the sample row | `ThenRow p` | `effThen` at a frozen frame's cancel |
| 7. the side check | `Targets.NotVDenNaturalArises` | whether naturality is available for live lends |
| all | `Probe p` | statements 0–6 at one placement |

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
| Core | `vC`/`vCE`, `cC`, `wpTS`, `wpG`, `ewpTS`, `opTable`, `contShare`, `cancelOwed`, `KapRel`, `TW`, `Tagged`, `Ext`, `ptoMutS`, `ptoImmS`, `ptoImm`, `reborrow`, `RebChooseTW`, `wpG_reborrow`, `rebChooseTW_top`, the borrow constants' terms and types (`withborUE`, `withbor1UTy`, `withbor2UTy`, `withload`, `withloadUTy`), `CDerives`'s rule shapes |
| GhostEnd (`targets`) | `LEnt`, `LStack`, `LKind`, `extS`, `depth`, `tabK`, `vwE`, `vwS`, `dropS`, `stratS`, `boxTop`, `ReLend`, `RelendableS`, `RelendableN`, `ghostS`, `stopS`, `bodyS`, `openFS`, `OpenS`, `rowTab`, `TabAtS`, `jdgCty`, `innerView` (`Stacked.lean`, `RLCompat.lean`); every lemma of `StackStep.lean`, `Drop.lean`, `Relend.lean`, `ImmLend.lean`, `Frames.lean`, `Table.lean`, `Tree.lean`, `Descend.lean` |
| GhostEnd (branches; §2.6) | `Below.lean` (`gfp`), `Arising.lean` (`gfp-arising`), `Extend.lean` (`borrow-callbacks`): `tabAtS_comp`, `tabAtS_nil`, `wpG_tabAtS_one`, `tabAtS_start_one`, `force_RLa`, `relendableS_thunkA`, `thunkF_RLa`, `thunkE_RLa`, `lam_RLa`, `allI_RLa`, `vRLa_congr`, `below_excluded`, `stackFresh_of_fresh`, `callback_ext`, `callback_ext_one`, `all_elimK`, `tw_innerView`, `not_gfpAt_below` |
| Targets | `SemWorld` and its `B.BWorld`; `Idx`; `OpTabI`, `OpEntI`; `RowSpan`, `admClosedOp`, `RowClass`, `OutJ.core`; `SpanWithbor1`, `SpanWithbor2`, `SpanWithload`, `HandleCompat`, `SliceShape`, `Mono` (as the forms the probe's statements transcribe); `AcceptedAt`, `genSelf`; `TypingJ`; `NotVDenNaturalArises`; the open types `Inst.OVTy`, `Inst.OCTy` |

### 2.2 The index, the order and the guard (`World.lean`)

W's index is Targets' `Idx` at the stack `Stk := LStack × List Life`: GhostEnd's entries and their
current lifetimes, innermost first, beside the record list.

```lean
abbrev Stk := LStack × List Life
abbrev Ix := Targets.Idx Stk

def StackOK (σ : LStack) (αs : List Life) : Prop :=
  αs.length = σ.length ∧ List.IsChain (· < ·) αs ∧ (σ.map LEnt.x).Nodup
```

**Futures of the stack.** A value or a continuation can be used deeper than where it was made: inside
new lends and inside new handlers. A new lend is an entry inserted in the stack: at the front when
a value moves inside it, at depth `k` when a continuation that ghost-ended its `k` innermost
entries is resumed inside a lend the resumer opened (between lenders). A new handler hides its
names from the stack's rows outside it: GhostEnd's stop depth reads each entry's lender row
(`depth`, `Stacked.lean:115`), and inside a handler of `n` no stop of `n` reaches the lends outside
the handler.

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

def nsBase : LifeVar := 2 ^ 32
def NsVar (x : LifeVar) : Prop := nsBase ≤ x
def NsFresh (τ : LStack) : Prop := ∀ e ∈ τ, NsVar e.x

def FutQ (fut : Bool) (δ : LSub) (σ : LStack) (αs : List Life) (k : Nat) (τ : LStack)
    (αt : List Life) (N : Option (UInt32 → Bool)) (ρ : WRes) : Prop :=
  if fut then FutOK δ σ αs k τ αt ρ ∧ NsFresh τ else k = 0 ∧ τ = [] ∧ αt = [] ∧ N = none

def OrdW (δ : LSub) (i i' : Ix) (ρ : WRes) : Prop :=
  Ext i.1 i'.1 ρ ∧ ∃ k τ αt N, FutOK δ i.2.1 i.2.2 k τ αt ρ ∧ NsFresh τ ∧
    i'.2.1 = futS k τ N i.2.1 ∧ i'.2.2 = futL k αt i.2.2

def guardW (σ : LStack) (αs : List Life) (P : WProp) : WProp := fun ρ => TabAtS σ αs ρ → P ρ
```

`FutOK.below` is 6.112's `И`: the inserted lifetimes lie below the holder's resource.
`FutOK.chain` is D-ORD: the whole vector stays in nesting order, so an insertion at depth `k > 0`
needs the inner part re-lent below it first (the `U` clause and the share re-lend before they
insert). The re-lend of the stack's own lifetimes is not part of `OrdW`: it is the hand-back the
`U` clause and the share carry (`ReLend`, then the dropped views handed back).

**Names.** Lifetime variables are names (`LifeVar := Nat`), and the stack binds its entries'
variables over the reading substitution (`extS`, which overrides `δ`). An entry a future inserts
takes its variable from the names no program binds (`NsVar`), and every judgement the probe reads
keeps its binders below them (`BindersLow`, §2.5). Without that, a future's entry could be named
by a binder of the code that later runs at the future, and the `∀` clause there would read its body
at the entry's lifetime instead of its instance: the `allE` row would have nothing to work with.
This is the representation item OQ-8 boxes (the draft spec's D-W, *Representation note*).
`nsBase` is a convention of the probe; its value matters only in being above every binder of the
two programs.

`VarsAvoid C τ` (a pushed variable is neither free nor bound in `C`) and `CTy.binders` are in
`World.lean`.

### 2.3 The piece with the share over futures (`Piece.lean`)

GhostEnd's piece `OpenS` runs at one stack: a stop of depth `k` ghost-ends the innermost `k`
entries and owes its continuation, re-lent below them, at the same stack. The **share over
futures** owes the continuation also at every future of the kept part `σ.drop k`, since the
handler may resume it inside new lends and new handlers. The continuation then resumes at
`σ.take k ++ futS k' τ N (σ.drop k)`, so the continuation variable carries its stack.

```lean
abbrev XTF := LStack → Nat → List Bool → List Life → List Life → List SRec → Expr → WProp

def RelendableNF (fut : Bool) (δ : LSub) (inner σ : LStack)
    (P : LStack → List Life → WProp) (αs : List Life) (ls : List SRec) : WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwS δ (inner.map LEnt.l) σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ αs', ReLend αs' αs → ∀ k τ αt N, FutQ fut δ σ αs' k τ αt N ρz →
      (∀ e ∈ τ, e.x ∉ inner.map LEnt.x ∧ e.l ∉ inner.map LEnt.l) →
      (vwS δ (inner.map LEnt.l) σ ds αs' ls ─⋆ P (futS k τ N σ) (futL k αt αs')) ρz

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
with the name added to the hidden set and hidden from the inserted entries' rows.

### 2.4 The relation, its quantifier placed by `Placement` (`Relation.lean`)

One `mutual` block, structural on the type, the stack an index (as `vRLk`), the placement a fixed
parameter.

| placement | `U` | `⊸` | `∀` | the stop's share | the callback's own lend |
|---|---|---|---|---|---|
| `cbpv` (OQ-8 option 2) | futures | resources only | resources only | futures (`OpenSF`) | made at `U`, one level into the type |
| `binder0` (OQ-8 option 3, `vRLk`) | the stack itself (`RelendableS`) | resources only | resources only | the stack itself (`OpenS`) | made at `∀` |
| `binder` (OQ-8 option 3, §17.6) | futures | futures | futures | futures (`OpenSF`) | made at `∀` |

The `U` clause over futures:

```lean
def RelendU (fut own : Bool) (δ : LSub) (σ : LStack) (C : CTy)
    (P : LStack → List Life → List SRec → WProp) (αs : List Life) (ls : List SRec) : WProp :=
  fun ρ =>
    ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwS δ [] σ ds αs ls ρn ∧ stratS αs ρz ∧
      ∀ ls', Ext ls ls' ρz → ∀ αs', ReLend αs' αs →
        (vwS δ [] σ ds αs' ls' ─⋆ P σ αs' ls') ρz ∧
        (fut = true → ∀ k τ αt N, FutOK δ σ αs' k τ αt ρz → NsFresh τ → VarsAvoid C τ →
          (vwS δ [] σ ds αs' ls' ─⋆ P (futS k τ N σ) (futL k αt αs') ls') ρz) ∧
        (own = true → ∀ (x : LifeVar) (c : Lifetime.Life) (C' : CTy) (e : LEnt) (a : Life),
          C = .all x c C' → e.x = x → x ∉ CTy.binders C' → FutOK δ σ αs' 0 [e] [a] ρz →
          LtLife (extS δ σ αs') c a →
          (vwS δ [] σ ds αs' ls' ─⋆ P (e :: σ) (a :: αs') ls') ρz)
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
      (∀ v, (vRL p σ δ A αs ls v ─⋆ guardW σ αs (cRL p σ δ C αs ls (.app e (.val v)))) ρ) ∧
      (p.bindFut = true → ∀ ls' k τ αt N, Ext ls ls' ρ → FutOK δ σ αs k τ αt ρ → NsFresh τ →
        VarsAvoid (.arr A C) τ → ∀ v,
          (vRL p (futS k τ N σ) δ A (futL k αt αs) ls' v ─⋆
            guardW (futS k τ N σ) (futL k αt αs)
              (cRL p (futS k τ N σ) δ C (futL k αt αs) ls' (.app e (.val v)))) ρ)
  …
  | σ, δ, .all x c C, αs, ls, e => fun ρ =>
      (∀ α, (⌜LtLife (extS δ σ αs) c α⌝ ─⋆
        guardW σ αs (cRL p σ (δ.extend x α) C αs ls (.app e (.val .unit)))) ρ) ∧
      (p.allOwn = true → ∀ (en : LEnt) (α : Life), en.x = x → FutOK δ σ αs 0 [en] [α] ρ →
        LtLife (extS δ σ αs) c α →
        guardW (en :: σ) (α :: αs)
          (cRL p (en :: σ) (δ.extend x α) C (α :: αs) ls (.app e (.val .unit))) ρ) ∧
      (p.bindFut = true → ∀ ls' k τ αt N, Ext ls ls' ρ → FutOK δ σ αs k τ αt ρ → NsFresh τ →
        VarsAvoid (.all x c C) τ → ∀ α,
          (⌜LtLife (extS δ (futS k τ N σ) (futL k αt αs)) c α⌝ ─⋆
            guardW (futS k τ N σ) (futL k αt αs)
              (cRL p (futS k τ N σ) (δ.extend x α) C (futL k αt αs) ls' (.app e (.val .unit)))) ρ)
  | σ, δ, .nu C, αs, ls, e => cC (.nu C) ls (extS δ σ αs) e
  …
end
```

**`binder0` against `vRLk` as built.** At `binder0` the `U` clause is `vRLk`'s and the share is
GhostEnd's `OpenS`, so every lemma of `StackStep.lean` applies verbatim. The `∀` clause differs from
`vRLk`'s in two ways:
- the extension is the callback's own lend only, one entry named by the binder at the instance's
  lifetime;
- that entry meets `FutOK`: below the callback's resource, its variable new to the reading
  substitution.

`vRLk`'s `∀` clause (`Extend.lean:92-96`) quantifies over every extension and every instance `α`.
For its own variable it reads the body at the extension's lifetime whatever `α` is, so its `allI`
row would owe the body at lifetimes that do not meet the bound. `callback_ext` uses only the
instance at the entry's lifetime, so it carries over.

**`cbpv`'s own lend.** At `cbpv` the `∀` clause is plain. A callback can then reach its own lend
only through `U`, so the `U` clause looks one level into its type: it pushes an entry named by the
type's outermost `∀`, at a lifetime meeting its bound. The plain `∀` clause at that stack reads its
body at the stack's lifetime for its binder (`extS` overrides `δ`). That is the instance
`CallbackExt` uses, and the one `StackJ`'s third kind admits (§2.5). This is what the `U`
placement costs under GhostEnd's representation, where entries carry the binder's variable.

### 2.5 The semantic judgement, and W as a `SemWorld` (`Sem.lean`)

```lean
def CtxAvoids (x : LifeVar) (Γ : Ctx VTy) : Prop :=
  ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty

def BindersLow (Γ : Ctx VTy) (C : CTy) : Prop :=
  (∀ x ∈ CTy.binders C, ¬ NsVar x) ∧ ∀ s ∈ Γ, s.live = true → ∀ x ∈ VTy.binders s.ty, ¬ NsVar x

def StackJ (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  (σ.map LEnt.x).Nodup ∧ ∀ e ∈ σ,
    (∃ u, Δ.find? e.x = some u) ∨
    (NsVar e.x ∧ Δ.find? e.x = none ∧ ¬ CFree e.x C ∧ CtxAvoids e.x Γ) ∨
    (Δ.find? e.x = none ∧ σ.head? = some e ∧ CtxAvoids e.x Γ ∧
      ∃ c C', C = .all e.x c C' ∧ e.x ∉ CTy.binders C' ∧ ∀ a ∈ αs.head?, LtLife (extS δ σ αs) c a)

def SemS (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → StackJ σ αs δ Δ Γ (jdgCty j) → Δ.Models (extS δ σ αs) →
    TabAtS σ αs ρ → gRL p σ δ αs ls Γ γ ρ → cRL p σ δ (jdgCty j) αs ls (substAll γ e) ρ
```

`SemS` is GhostEnd's `SemA` (`Arising.lean`) at the placement's relation. FL at W for a rule is
that rule's compatibility lemma at `SemS`. `StackJ`'s first kind is GhostEnd's `LStack.WF`. Its
second and third kinds are the entries the placements' quantifiers insert. A row whose premises
add types takes their `BindersLow` as a hypothesis, the rule's binder or intermediate type, as
`allI_RLa` takes `hσx`.

**Why not Targets' `SemW`.** Targets' `SemW`/`FL` (`Targets/B/World.lean:116`,
`Targets/B/Guarantees.lean:68`) quantify over every index, with no hypothesis on its stack. At a
stack whose variables a binder of the judgement rebinds, or whose lifetimes do not model `Δ`, the
rows' proofs have nothing to work with. So the probe states FL at W with GhostEnd's index
hypotheses. At the nil index `SemS` and `SemW₀` read the same judgement. Whether done's `FL M J`
should be read at the nil index, or carry these hypotheses, is recorded for RESTRUCTURE and not
changed here.

**W as the interaction's world.**

```lean
def WP (p : Placement) : Targets.SemWorld where
  Stk := Stk
  nil := ([], [])
  Fam fρ ps i := TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1 ∧ StackOK i.2.1 i.2.2
  Upd _ _ ρ _ π := ResU.UpdV ρ π
  Ext := ExtW                     -- OrdW at the empty substitution
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
relations. Statement 0 is proved or refuted per placement, and W is the one placement that
survives. If two survive, the cuts criterion orders them: `cbpv` before `binder`, `binder` before
`binder0` (synthesis §4.2). A naturality placement (OQ-8 option 1) is not a clause set. It is the
claim that the `binder0` relation without its own-lend conjunct is natural under the freeze binder
(`Targets.FreezeBinderLife`). Statement 7 is its cheap check, and §4.4 records what follows.

---

## 4. Statement 0: W's `U`, `⊸` and `∀` clauses, fixed together

### 4.1 The statements (`Statement0.lean`)

```lean
def MonoV (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls ls' : List SRec) (v : Val) (ρ : WRes)
    (k : Nat) (τ : LStack) (αt : List Life) (N : Option (UInt32 → Bool)),
    StackOK σ αs → Ext ls ls' ρ → FutOK δ σ αs k τ αt ρ → NsFresh τ → VarsAvoidV A τ →
    TabAtS σ αs ρ → vRL p σ δ A αs ls v ρ → vRL p (futS k τ N σ) δ A (futL k αt αs) ls' v ρ

def MonoG (p : Placement) : Prop := …   -- the same for 𝒢⟦Γ⟧ (`gRL`)
def MonoC (p : Placement) : Prop := …   -- the same for the computation relation (`cRL`)

def MonoHide (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes)
    (N : UInt32 → Bool), StackOK σ αs → TabAtS σ αs ρ →
    vRL p σ δ A αs ls v ρ → vRL p (hideS N σ) δ A αs ls v ρ

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
    FutOK δ σ αs 0 [e] [α] ρf → LtLife (extS δ σ αs) c α → TabAtS σ αs ρf →
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

def AgreeOnRules (p q : Placement) (R : LifeCtx → Ctx VTy → Expr → Jdg → Prop) : Prop :=
  ∀ Δ Γ e j, R Δ Γ e j → (SemS p Δ Γ e j ↔ SemS q Δ Γ e j)

def Statement0 (p : Placement) : Prop :=
  MonoV p ∧ MonoG p ∧ NilSoundV p ∧ NilSoundC p ∧ CallbackExtMut p ∧ CallbackExtImm p ∧
    ForceRow p ∧ ThawRelend p ∧ ThunkFRow p ∧ ThunkVRow p ∧ BangThunkFRow p ∧ BangThunkVRow p
```

### 4.2 Why each tests the real question at full strength

- **The clauses are fixed together.** `U`, `⊸` and `∀` are clauses of one `mutual` block, read at
  the guard. No clause is checked at another relation. The three placements differ exactly in the
  flags of `Placement`.
- **The `U`-clause thaw is proved at the guarded W.** `ForceRow`, `ThawRelend` and the four
  `U`-introduction rows are stated at `vRL p`, not transported from `vRLs`. At `cbpv` and `binder`
  the thunk rows owe the body at every future, so their proof is where the quantifier's cost
  shows.
- **Monotonicity is along the whole order.** That includes insertion at any depth, which the
  share needs between lenders, and hiding, which `[handle]` needs. A front-only order would make
  `MonoV` easier and hide the between-lenders case. `MonoC` and `MonoHide` are named because
  `binder0` needs them proved where `cbpv` and `binder` have them by construction (§4.3).
- **The nil slice is checked at every type.** That includes thunks, `∀` and `F_Σ`, which are the
  placements' quantifier sites.
- **The callback-extension fact is at any related argument.** The argument is any value of
  `Mut 'y T` (or `Imm 'y T`, its coherence with the records included) at the extended stack, so
  the `⊸` clause there is exercised, not only at the lend's own view. The callback is a value of
  the constant's callback type `cbUTy` (`Core/EffBorrow.lean`), not a premise. `CDerives` has the
  borrow operations as constants (`Below.lean`'s "What it measures"), so the row must get the
  callback's behaviour at `σ·y` from its value.
- **One quantifier.** At `cbpv` and `binder` every quantifying clause ranges over `OrdW` with the
  same hand-back. At `binder0` the `U` clause ranges over the stack itself and the `∀` clause over
  the own lend: two restrictions of `OrdW`. Whether they cohere is `MonoV binder0` (then `U` is
  Kripke along futures), together with `AgreeOnRules binder0 binder` on the derivations the probe
  reads.

### 4.3 Where each placement is expected to be tested hardest [unchecked]

These are readings that order the work. None is derived, and none is an obstruction.

- **`binder0`: monotonicity.** Its `U` clause ranges over the stack itself, so `MonoV` at a `U`
  value needs `MonoC` at its computation; `MonoHide` is the hiding instance. Hiding a name that the
  stack's inner entries cross changes a stop's depth from `d ≥ 1` to `0`.
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
  - The own lend at `U` reads the thunk type's outermost `∀`.
  - The plain `∀` at a stack that binds its binder reads the stack's lifetime (`extS`). That is
    consistent at `CallbackExt`'s instance and at `allI` under `StackJ`'s third kind.
  - Monotonicity is by construction: the `U` clause quantifies over futures. The work is the
    transitivity lemmas:
    - a future of a future is a future (`FutOK` composes);
    - `futS` and `hideS` compose;
    - `hideS` distributes over `futS`.
  - The cost is downstream. Every `F_Σ` row must produce continuations at middle-inserted stacks
    (`OpenSF`), so GhostEnd's stacked lemmas are restated over `OpenSF` (§6.2).
- **`binder`.** As `cbpv` at `U` and in the share, with no type-directed `U` clause. It adds
  obligations at `lam` and `allI`: the body at every future, from the induction hypothesis at the
  future with the context transported (`MonoG`).
- **The nil slice, at every placement.** `NilSoundV` and `NilSoundC` instantiate every
  quantifier at the empty future and are expected to be mechanical (`bodyS_nil_iff`, `vRLs_nil`'s
  pattern). `NilAgreesU` and `NilAgrees` ask Core's relation to carry obligations it has no
  notion of at the placement's quantifier sites:
  - `binder0`: the own lend at `∀`;
  - `cbpv`: futures at `U` and in the share;
  - `binder`: all of them.

  A Core-related callback keeps its view across a stop, where W re-lends it. So the old-in-new
  direction is not expected to follow from Core's relation at callback types. It cannot be refuted
  at an arising value either, since a derivable value meets it through its derivation. What FL
  needs at `σ = []` is the `U`-introduction rows, which are in `Statement0`. The expected answer
  to OQ-58 is that Core is not W's `σ = []` instance at those types: failure (c), Core redefined
  (§12.2).

### 4.4 What statement 0 decides

- **OQ-8.**
  - `Statement0 cbpv` proved, with statements 1–4 at `cbpv`: OQ-8 option 2. D1 then meets
    "interactions only at cuts", with this cost recorded: the `U` clause reads its type's
    outermost `∀` to name the callback's own lend. That reading stays at `U`, the resume cut's
    value side. Every clause reads the stack's lifetimes at its leaves through `extS`, as Core's
    relation reads its record list; that is not a quantifier.
  - Proved only at `binder` or `binder0`: option 3. Every `⊸` and `∀` clause, or the `∀` clause
    alone at `binder0`, carries a resume obligation away from the cuts. D1 then does not meet
    "only at the cuts". It keeps its rank against D2a and D3 (synthesis §8).
- **Option 1 (naturality).** It is not decided here. Statement 7 tells whether its known witness
  (`mut_not_natural`) arises. A placement that passes makes option 1 unnecessary for D1.
- **"Whether `U` and `⊸` take the same quantifier"** (02-experiments §1.3). Under `cbpv` they do
  not need to, since `⊸` takes none and the `U` clause carries it, as Core's relation does. Under
  `binder` they take the same. If statement 0 holds only with `U` and `⊸` quantifying over
  different orders that no single definition reconciles, that is failure (d) (§12.2).

---

## 5. Statement 1: the guard read from `TW` (OQ-45)

### 5.1 The statements (`Statement1.lean`)

```lean
def TabNil : Prop := ∀ ρ : WRes, TabAtS [] [] ρ
def TabParts : Prop :=
  ∀ σ αs ρ₁ ρ₂ ρ, ResU.CompS ρ₁ ρ₂ ρ → (TabAtS σ αs ρ ↔ TabAtS σ αs ρ₁ ∧ TabAtS σ αs ρ₂)

def TabRuns : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ls : List SRec) (e : Expr) (Q : List SRec → Expr → WProp)
    (ρ : WRes), StackOK σ αs → TabAtS σ αs ρ → wpG ls e Q ρ →
    wpG ls e (fun ls' t ρ' => TabAtS σ αs ρ' ∧ Q ls' t ρ') ρ

def TabStart : Prop :=
  ∀ δ σ αs ls (e : LEnt) α (d : Bool) (ρ a R : WRes), StackOK σ αs → FutOK δ σ αs 0 [e] [α] ρ →
    TabAtS σ αs ρ → vwE δ e d α ls a → ResU.CompS ρ a R → TabAtS (e :: σ) (α :: αs) R

def TabRelend : Prop :=
  ∀ δ σ ds αs αs' ls (ρz ρv R : WRes), StackOK σ αs → ReLend αs' αs → stratS αs ρz →
    vwS δ [] σ ds αs' ls ρv → ResU.CompS ρz ρv R → TabAtS σ αs' R

def TabFut : Prop :=
  ∀ δ σ αs k τ αt N ρ, StackOK σ αs → FutOK δ σ αs k τ αt ρ → TabAtS σ αs ρ →
    TabAtS (futS k τ N σ) (futL k αt αs) ρ

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
  TabNil ∧ TabParts ∧ TabRuns ∧ TabStart ∧ TabRelend ∧ TabFut ∧
    LamRow p ∧ AllIRow p ∧ BelowRow p ∧ BelowExcluded p
```

`belowEnt`, `belowCtx`, `belowTerm` and `belowType` are `Below.lean`'s `e₀`, `Δ₀`, `allBelowE` and
`allBelowC`, restated as data.

### 5.2 Why this is "the guard read from `TW`", and what the pointwise form measures

W's configurations are `TW`'s (`WP p`'s `Fam`), as Core's are. The guard asks more of the local
resource at a stack: the stack's table. The table is not read off one `TW` world. It is what `TW`'s
runs keep from a lend's start:
- 6.112's `И` puts the callback's resource above the fresh lifetime (`TabStart`);
- [TR] 6.50 keeps every borrow cell's lifetime at its location through `↭` (`TabRuns`, at the
  innermost lend's `↓α` and at the outermost lend away from the stack's places: `tabAt_updV`
  twice);
- a re-lend and a future keep it (`TabRelend`, `TabFut`);
- it splits over parts (`TabParts`);
- it is empty at `[]` (`TabNil`).

These are the synthesis's statement 1: "is the lend table a `TW` invariant at every depth? It holds
for one lend (`wpG_tabAt`) and for one entry (`wpG_tabAtS_one`)". Both of those are run
invariants. Proved, they make `TabAtS` the stack's arising condition derived from `TW`'s runs. A
guard that some run from an arising configuration does not keep would be a guard beside `TW`:
failure (b).

`TabOfTWPointwise` is the draft spec's T-ARISE.0. It reads the table off one `TW` world with no run
behind it. The configuration to check against it first:
- `innerView k αy` (`RLCompat.lean:381`) at the stack `[x]`, with `x` a `mut` entry at `α`,
  `αy < α` and `k ≠ x`'s place;
- its world is a `TW` world (`tw_innerView`: `TW.alloc`, then `TW.mutFold` at any lifetime);
- it holds a `mut` cell below the stack's lend at a place the stack does not lend.

`TW` records no 6.65 lend (OQ-44), so nothing in one `TW` world says that the cell was folded after
`x`'s lend opened. A refutation there is a fact about the pointwise statement, not an obstruction to
D1: the witness does not arise at the index `[x]`, since no run from a start that has the table
reaches it (`wpG_below_not_arises`, `Arising.lean:139`). Arising tests are directional: a coarser
arising set is sound for proving and unsound for refuting. `TabOfTWPointwise` is stated so that
this first check can be run. It is not in `Statement1`.

### 5.3 Why the rows test the real question

`LamRow` and `AllIRow` are the rows GFP is refuted at in its unguarded form (`Below.lean`). At
`binder` they owe the body at every future, which `lam_RLa` and `allI_RLa` never meet. `BelowRow` is
exactly the refuted derivation. `BelowExcluded` is `below_excluded` at the placement's relation.
`AllIRow` takes the binder new to `Δ`, the freshness `allI_RLa`'s added hypotheses come from
(`stackFresh_of_fresh`, `Arising.lean:861`). At `cbpv` it also meets a stack whose innermost entry
is the binder itself (`StackJ`'s third kind). There the clause reads the stack's lifetime, and the
induction hypothesis applies at `Δ.extend x b`, where the entry is of the first kind.

---

## 6. Statement 2: the borrow-constant row at `σ·y`, with Core as W's `σ = []` instance

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

def rebView (l : BoCa.Loc) (α : Life) (R : Val → WRes → Prop) (P₀ : Life → Val → WProp) : WProp :=
  ptoImm l α (fun v σ => R v σ ∧ fresh (fun b => reborrow b (P₀ b v)) σ)

def rebF (Tb : Table) (l : BoCa.Loc) (α : Life) (R : Val → WRes → Prop)
    (P₀ P : Life → Val → WProp) (Q : List SRec → Val → WProp) (X : List SRec → Expr → WProp) :
    List SRec → Expr → WProp :=
  fun ls e => fresh fun b => all fun v => P b v ─⋆ wpG ls e (fun ls' t => box b (fun ρ =>
    valPost Q ls' t ρ ∨ Tb ls' t (fun ls'' e'' => rebView l α R P₀ ⋆ X ls'' e'') ρ))

def RebRelend (Tb : Table) l α R P₀ P Q (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ X, (∀ ls e ρ, rebF Tb l α R P₀ P Q X ls e ρ → X ls e ρ) → X ls e ρ

def RebFrameR : Prop :=
  ∀ (Tb : Table), Tb.Mono → ∀ l α R P₀ P Q ls e, (∀ ls', RebChooseTW ls' l R P₀ P) →
    Entails (rebView l α R P₀ ⋆ RebRelend Tb l α R P₀ P Q ls e) (ewpTS ls e Tb Q)

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
2. **The piece to the callback form** (#275's other half): from the callback's piece at `σ·y`,
   which answers in `effRet (e :: σ)` at `['y] B`, to the form `stack_step_other` consumes,
   `OpenS δ (e :: σ) Tab (cbQ δ (e :: σ) Qa) (σ.length + 1) (d :: ds) (b :: bs) [] ls e ρ`. Its
   proof re-instantiates `CallbackExtMut` at each fresh lend below `b`: that is
   `relend_of_openD` (`Descend.lean:174`) at a stack. **New**; stated when the route reaches it,
   its shape fixed by `stack_step_other`'s hypothesis.
3. **The fold**:
   - at `binder0`, `stack_step_other` (`StackStep.lean:392`), and at `σ = []` `openS_nil_ewp`;
   - at `cbpv` and `binder`, the same commutation over `OpenSF`, the futures quantifier carried
     through each unfolding. **New**: GhostEnd's argument at a stack-indexed least fixed point.

   `stack_step_other`'s callback form puts the answer above the outermost lend (`cbQ`'s `boxTop`).
   An answer that keeps a view of `σ` (#276's shape) needs the form `bodyAtD` has. That is not
   needed at `σ = []`, the only stack the programs' borrows sit at, but `SpanW2Row` is at every
   stack.
4. **The unwinding frame and the cancel.** `withborR_compat` (`Drop.lean:108`) for 6.65:
   `ewp_then_owner` puts the owner back at a cancel and `d` disposes of it.

For `withbor` (1) the same, with `CallbackExtImm`, `stack_step_imm` (`StackStep.lean:1003`) and
`ewpTS_I_frameR`. The cancel path over a 6.64 frame is **not built** (p10 §5.1 X.4). It is the
6.64 analogue of `withborR_compat`: `RelendI` (`ImmLend.lean:128`) in place of `Relend`, `ownerI`
in place of `owner`, and an `opTableO` whose cancel hands back `ownerI`. Its proof follows
`withborR_compat`'s, with 6.64's exit at the cancel's end. `reconB′`'s second borrow needs it.

**[TR] 6.150 at a resuming table** (`RebFrameR`). This is Law 2 for `withload`, in scope whatever
OQ-29 decides (synthesis D1.i5). The proof follows the printed proof of 6.150 once per unfolding of
`RebRelend`, as `ewpTS_M_frameR` follows 6.65's:
- each unfolding is `wpG_reborrow` (`Core/Reborrow.lean:232`), whose postcondition is over any
  term, so "a reborrow ends at a stopped operation as at a return" (6.52's subtraction at a stop
  is inside it);
- the step the lift adds is `ptoImm_dup` (`Frames.lean:110`): a copy of the view is kept beside
  the callback and handed to the continuation at the stop;
- the chooser is re-instantiated at each resumption's list, where `rebChooseTW_top` supplies it
  (the record persists along `Ext`).

`RebFrameR` takes the chooser at every list, a hypothesis wider than the record's lists. If the
proof shows the record's lists suffice, the statement narrows to them and the change is recorded.

**`SpanLoadRow`.** At a data payload `Imm̲ 'y A = A` (`VTy.immReborrow`, `Core/Types.lean:1447`).
The callback then gets data, and no entry spans the stop. That is the case `reconB′`'s reads are,
and they complete before the next `wait` (synthesis §11), so the programs do not exercise
`RebFrameR`. At a payload with inner places, 6.150's image holds views at the new lifetime at the
payload's chain positions. The stack then needs an entry for a reborrow, a kind GhostEnd's
`LEnt` lacks (`mut` and `imm v` only) and WorldW's `OEnt` has (`reb`). That would be a finding
about what `σ` holds (OQ-44), recorded, not a new relation.

### 6.3 OQ-58: Core as W's `σ = []` instance

`NilAgrees p` and `NilAgreesU p` (statement 0) are OQ-58 (a). §4.3 records the expected answer:
Core's relation lacks the re-lend obligations at each placement's quantifier sites. Statement 2
settles it in Lean: `NilAgrees p` proved, or the sites at which it fails, each with the
introduction rows that hold there at W. The cost of failure is (c), §12.2.

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

def Statement3 (p : Placement) : Prop := HandleRow p ∧ MonoHide p
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
    piece's share (`OpenSF` at `hideS (· == n) σ`) gives them, with `n` and the hidden set moved
    into the future (`hideS` distributing over `futS`).
- **The context.** It is transported to the hidden stack (`MonoHide`), which is why `MonoHide` is
  in the bundle.

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
  ∀ σ δ αs ls ls' ρv k C η v r kd τ αt N,
    StackOK σ αs → Ext ls ls' r → FutOK δ σ αs kd τ αt r → NsFresh τ →
    (∀ η', VarsAvoidV (Targets.Inst.OVTy.den η' (.thunk (.allR ρv k C))) τ) → TabAtS σ αs r →
    ovalW p σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    ovalW p (futS kd τ N σ) δ (futL kd αt αs) ls' (.thunk (.allR ρv k C)) η v r

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
  `withborR_compat`;
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

## 11. The arising check

A configuration that refutes a statement of this probe is reported as an obstruction only when all
of the following hold:

1. **The negation is proved in Lean.** It instantiates every hypothesis of the refuted statement at
   concrete values, as `not_gfpAt_below` does.
2. **Its world arises in `TW`**, checked by `ArisesAt` at the refuted statement's stack:

   ```lean
   def ArisesAt (σ : LStack) (αs : List Life) (ls : List SRec) (ps : List FrameRec)
       (ρf ρ fρ : WRes) : Prop :=
     TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls ∧ ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧
       StackOK σ αs ∧ (∀ e ∈ σ, ∀ u, e.k = .imm u → ∃ r ∈ ps, r.le = e.l) ∧
       (∀ e ∈ σ, e.k = .mut → ∃ ψ : CellU BoCa.Loc Val, fρ.get e.l = some ψ ∧ ψ.kind = Kind.mut) ∧
       TabAtS σ αs ρ
   ```

   The world is `TW`-reachable, by `TW`'s constructors. The stack is consistent with it: each 6.64
   entry among `TW`'s records, each 6.65 entry's place a `mut` cell. The local part has the
   stack's table, which statement 1 proves is what `TW`'s runs keep.
3. **Its values arise**, when the refutation is about a value or a computation in the relation
   rather than about a derivation. The value is the result of a term the probe's rules type: a
   derivable callback, closure or continuation, never an arbitrary inhabitant of the relation. A
   relation-level value that no typed term produces does not arise (✓-valid is not reachable).
4. **The refuted statement is ours.** Every statement here is. A refutation is reported against
   the statement, with the printed lemma it reads named. The paper is not wrong.

A refutation that fails 2 or 3 is recorded as a fact about the statement, never as an obstruction to
D1. `TabOfTWPointwise` at `innerView` (§5.2) is the first instance: its world passes the `TW` part
of 2 and fails the table.

---

## 12. Success, failure, and the stop rule

### 12.1 Success

- `Probe p` is proved at one placement `p`, and `ReconAccepted p reconB′` at the term built for
  `reconB′`. `Probe p` is statements 0–4, `GenSelfAccepted p` and `ThenRow p`.
- The placement is recorded with its consequence (§4.4):
  - `cbpv`: OQ-8 option 2, and D1 meets "two algebras with interactions only at cuts", with the
    own-lend cost at `U` recorded;
  - `binder` or `binder0`: option 3, with a resume obligation in the binder clauses.
- OQ-58's outcome is recorded: `NilAgrees p` proved, or the sites where it fails.
- Law 2 for `withload` is recorded: `RebFrameR` proved, and `SpanLoadRow` proved or its entry-kind
  finding stated.

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
  - a guard beside `TW` is stronger than `TabAtS`, or one of statement 1's run invariants fails at
    an arising configuration;
  - a second relation family is a relation for callbacks or continuations apart from `vRL`/`cRL`.

  Stop and report.
- **(c)** `NilAgrees p` fails at the placement that survives. Core is then redefined as W's
  `σ = []` instance (OQ-58 (b)), a kernel change with a SPEC entry, and every Core theorem is
  re-proved through FL at W. Not a stop. The expected case (§4.3).
- **(d)** Statement 0 holds only after the clauses are changed so that `U` and `⊸` (or `U` and the
  share) quantify over orders that are not restrictions of `OrdW` with one hand-back. Or it holds at
  `binder0` only, with `AgreeOnRules binder0 binder` refuted on a derivable judgement. W would then
  carry two quantifiers, a relation family in all but name. Stop and report.

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
   - `MonoHide binder0` and `MonoC binder0`;
   - at `cbpv`, `ThunkVRow` at the own-lend future and `AllIRow`'s third-kind stack;
   - at `binder`, `LamRow` at a future;
   - then the transitivity lemmas of `FutOK`, `futS`, `hideS`, then `MonoV`/`MonoG`, `NilSound*`,
     `CallbackExt*`, `ForceRow`, `ThawRelend` and the thunk rows.

   Apply the stop rule.
3. **Statement 1**: `TabRuns` (6.50 at both ends of the stack), `TabStart`, `TabRelend`, `TabFut`,
   the first check of `TabOfTWPointwise` (§5.2), then `LamRow`, `AllIRow`, `BelowRow`,
   `BelowExcluded`.
4. **Statement 2**:
   - the 6.64 cancel path and `RebFrameR` first, the two items no proof has touched;
   - then #275's conversion and the fold, at `OpenS` or `OpenSF`;
   - then `SpanW2Row`, `SpanW1Row`, `NilAgrees`, `SpanLoadRow`.
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
- 6.112's `И` at each lend's entry and each re-lend (`fresh_frame`, `FutOK.below`);
- 6.48 and 6.49 at every run's end through `Upd = ↭` (`updFrame_of_core`, `updSeq_of_core`);
- 6.62, `G⟦Γ⟧δ(γ) ⊧ [@aδ] G⟦Γ⟧δ(γ)`, at the borrow rows: the callback's context above the fresh
  lend (`gSepC_outlives`, `frame_outlives`).

**Uniqueness and functionality results.**
- Expected to be used: `ResU.CompS.functional`, `ResU.Flat.functional`, `CellU.immOf_inj` (in
  `ptoImmS_join`), `dropC_disj`.
- Not expected: the machine's determinism (`AStep1.deterministic`). The measure is the piece's own
  least fixed point, the typing derivation and a loop's budget, as in GhostEnd step 3a.

**Printed lemmas in the run-up that are untranscribed.**
- [TR] 6.150 at a resuming table: `RebFrameR` states it; its added step `ptoImm_dup` and its exit
  at a stop (inside `wpG_reborrow`) are proved.
- 6.64, 6.65 and 6.66 at a resuming table are lifted (`ewpTS_I_frameR`, `ewpTS_M_frameR`,
  `ewpTS_M_antiFrameR`).
- 6.172–6.176 are transcribed at Core's relation and restated at W as the rows of statements 2 and 4.
- The 6.64 cancel path is ours, not a printed lemma.

**Hypotheses added in the statements.**
- `AllIRow`'s `Δ.find? x = none`, the binder new to `Δ`, as `allI_RLa`'s `hσx` comes from it.
- `SemS`'s `BindersLow`, and `ThenRow`'s hygiene of its intermediate type: binder hygiene against
  the names futures give their entries (§2.2, *Names*). Both hold at `σ = []` and at the two
  programs, whose binders are small.
- `RebFrameR`'s chooser at every list (§6.2).
- `StackJ`'s second and third kinds, which widen GhostEnd's `LStack.WF` to the entries the
  placements' quantifiers insert. At `σ = []` they are vacuous.
