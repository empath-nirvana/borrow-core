# ProbeD1: the fundamental lemma at W for the rules `genSelf` and `reconB′` use

**What this is.** The design of the tractability probe for design D1 (rows and ghost end), the
probe of `research/effects/src/synthesis.md` §11. It fixes the Lean statements, the definitions
they need, why each statement tests the question at full strength, what success and failure look
like, the arising check a counterexample must pass, and the stop rule. The build's outcome is §15;
`README.md` reports it.

**The Lean.** Every definition and statement below is in `experiments/ProbeD1/ProbeD1/*.lean`
(library `ProbeD1`, root `ProbeD1.lean`), and `lake build ProbeD1` elaborates it. The code blocks
here are copied from those files, with routine clauses elided as `…`. The statement files
(`World`, `Piece`, `Relation`, `Sem`, `Rules`, `Arising`, `Statement*`, `Programs`) hold
definitions and `def … : Prop` statements. The proofs are in `Order`, `Bridge`, `Shared`, `Views`,
`Mono`, `Own`, `Rows0` and `Thunk` (§15). No file has `sorry`, `axiom`, `native_decide`, `opaque`,
`partial`, `unsafe` or `implemented_by`.

**Worlds.** The tags are the notebook's. [Core σ=[]] is Core's relation. [GE] is a GhostEnd
relation (`vRLs`, `vRLa`, `vRLk`). [W] is this probe's relation (`ProbeD1.vRL`/`cRL`) at one of
its placements. A result at one of them is not a result at another unless a statement here
relates them.

**Rules this design keeps.**
- Nothing breaks the borrow calculus: its guarantees, not BoLo's text.
- The paper is not wrong; every refutation the probe can produce is of a statement of ours.
- An obstruction is only an elaborating `def … : Prop` with its negation proved at a configuration
  that arises (`Arises`, reachability from the nil index) and at values that arise (`ArisesV`),
  with the closed program whose execution reaches them exhibited (§11). That `Arises`
  under-approximates what arises is not established, so the program is part of the evidence.
  Otherwise the report says "not derived, no obstruction verified".
- No step-indexing: the relation is one `mutual` block, structural on the type.
- No relation family beside W's one relation. The three placements of §3 are candidates for that
  one relation. W is the surviving placement first in the cuts order. It is decided only when
  every placement before it is refuted by a refutation that passes §11, and is provisional
  otherwise (§3).
- Multi-shot is ignored. The core is linear.

---

## 0. The probe on one page

**The question** (synthesis §11): is FL at W provable for exactly the rules `genSelf` and `reconB′`
use, at one world, with the arising guard read from `TW`, with one future-world quantifier, and
with no relation family beside W?

**The order is fixed.** Statement 0 first. Its outcome decides OQ-8 (where the future-world
quantifier sits) and with it whether D1 meets "two algebras with interactions only at cuts"
(synthesis §2.5, §4.2, §8), once W is decided rather than provisional (§3). Statements 1–4 follow,
at the placements statement 0 leaves.

| statement | Lean (`ProbeD1.…`) | what it settles |
|---|---|---|
| 0. W's `U`, `⊸`, `∀` clauses fixed together | `vRL`, `cRL` at `Placement.{cbpv, binder0, binder}`; the shared lemmas `Statement0Shared` = `ExtPreW`, `FutReLend`, `FutPart`, `FutAvoidsTrans`, `OpenSFBridge`, `NilSoundRet`; the per-placement facts `Statement0 p` = `MonoOwnG`, `MonoV`, `MonoG`, `CallbackExtMut`, `CallbackExtImm`, `ForceRow`, `ThawRelend`, `ThunkFRow`, `ThunkVRow`, `BangThunkFRow`, `BangThunkVRow`; beside them `MonoC`, `MonoHide` (`MonoHideFromMonoV`), `NilSoundV`, `NilSoundC`, `NilAgreesU`, `NilAgrees` | OQ-8; whether `U` and `⊸` take one quantifier; OQ-58, through `NilAgrees` (§6.3) |
| 1. the guard as `TW`'s run invariant | `Statement1 p` = `TabNil`, `TabParts`, `TabUpd`, `TabRuns`, `TabStart`, `TabHide`, `TabRelend`, `TabFut`, `TabResume`, `LamRow`, `AllIRow`, `BelowRow`, `BelowExcluded`; beside it `ArisesSound`, `TabOfTWPointwise` | OQ-45's first question, re-scoped (§5.2); `lam`, `allI` and `not_gfpAt_below`'s derivation at W |
| 2. the borrow-constant row at `σ·y` | `Statement2 p` = `SpanW2Row`, `SpanW1Row`, `RebFrameR` (its added hypotheses `RCarried`, `TabKeepsRec`); beside it `SpanLoadRow`, `RebChooserNonVacuous` | #275; [TR] 6.150 at a resuming table (Law 2 for `withload`) |
| 3. `[handle]` with a lend open | `Statement3 p` = `HandleRow` | #278 |
| 4. `[allR-E]` at W | `Statement4 p` = `AllREW`, `AllRMono` | Law 1's elimination inside a borrow |
| 5. the programs | `GenSelfAccepted p`, `ReconAccepted p e` | `genSelf`, `reconB′` accepted at W |
| 6. the sample row | `ThenRow p` | `effThen` at a frozen frame's cancel |
| 7. the side check | `Targets.NotVDenNaturalArises` | whether naturality is available for live lends |
| the arising check | `ProbeRules`, `Arises`, `ArisesV`, `ArisesCtx`, `ArisesAt`, `ArisesNonVacuous` | what a refutation must reach (§11) |
| all | `Probe p`; `Survives e p`, `Placement.rank` | statements 0–6 at one placement; which placement is W, decided or provisional (§3) |

**The stop rule** (§12.3). Statement 0's shared lemmas come first. A failure of one is a finding
about our definitions and stops the probe. If `Statement0 p` is proved at no placement, the probe
stops after statement 0 and reports. A fact that fails at every placement for one shared reason is
reported as a finding about our definitions, not as a comparison of placements.

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
| GhostEnd (`targets`) | `LEnt`, `LStack`, `LKind`, `extS`, `depth`, `tabK`, `vwE`, `vwS`, `dropS`, `stratS`, `boxTop`, `ReLend`, `RelendableS`, `RelendableN`, `ghostS`, `stopS`, `bodyS`, `openFS`, `OpenS`, `rowTab`, `TabAtS`, `jdgCty`, `innerView` (`Stacked.lean`, `RLCompat.lean`); the lemmas of `StackStep.lean`, `Drop.lean`, `Relend.lean`, `ImmLend.lean`, `Frames.lean`, `Table.lean`, `Tree.lean`, `Descend.lean`, each at the rows whose hypotheses it meets (the fold lemmas need `LinResume` and `AllCross`, and the 6.64 ones `Tab.Local`, §6.2); at `cbpv` and `binder` through `OpenSFBridge` or restated over `OpenSF` (§6.2) |
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

def FutStep (δ : LSub) (ρ : WRes) (s s' : Stk) : Prop :=
  ∃ (k : Nat) (τ : LStack) (αt : List Life) (N : Option (UInt32 → Bool)),
    FutOK δ s.1 s.2 k τ αt ρ ∧ s'.1 = futS k τ N s.1 ∧ s'.2 = futL k αt s.2

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
transitivity is by construction (`ExtPreW`, bookkeeping among statement 0's shared lemmas).

The stack a future gives is an order-preserving interleaving of `σ` with fresh entries. Each kept
entry's row is reduced by hiding sets that grow outward: a hiding at depth `k` reaches every kept
entry outside depth `k`. The lemmas the proofs need about it are stated where they are used:
`FutReLend`, `FutPart` and `FutAvoidsTrans` (§4.1), and `TabFut` (§5.1). They are stated at the
reading substitution `δ`, since `FutOK.vars_sub` and `FutOK.pay` read it.

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

The own push is the one-step future at depth `0` when its variable is new to the reading
substitution (`ownPush_futStep`, `Own.lean`): `OwnOK` gives `FutOK`'s fields, and `FutStep` admits
a variable that is not `NsVar` (*Names*, below). The type's own clause does not quantify over it as
a future: `FutAvoids` asks the type's binders avoided, and the push is named by one. A row that
calls its premise at the pushed stack carries its context there by `MonoOwnG` (statement 0), which
is `MonoG`'s instance at that future (`monoOwnG_of_monoG`): `ThunkVRow` and `BangThunkVRow` at
`cbpv`, `AllIRow` at `binder0` and `binder`. `MonoOwnG` asks the pushed variable to be neither free
nor bound in the context's live types (`CtxFresh`), and new to the reading substitution;
`StackJ`'s third kind asks the first of the judgement's context.

**Names.** Lifetime variables are names (`LifeVar := Nat`), and the stack binds its entries'
variables over the reading substitution (`extS`, which overrides `δ`). A step's inserted variables
are any new to the stack and to the reading substitution (`FutOK.vars_stack`, `FutOK.vars_sub`);
the clause quantifying over the future asks its own type to avoid them, free and bound
(`FutAvoids`). `NsVar` names no program binds: every judgement the probe reads keeps its binders
off them (`BindersLow`, §2.5), and `StackJ`'s second kind admits an inserted entry named by one.
`nsBase` is a convention of the probe; its value matters only in being above every binder of the
two programs. The restriction `BindersLow` puts on FL at W is a guarantee gap with a stated
discharge (§14). A future's entry named by a binder of the code that later runs at the future would
make the `∀` clause there read its body at the entry's lifetime instead of its instance: the `allE`
row would have nothing to work with. This is the representation item OQ-8 boxes (the draft spec's
D-W, *Representation note*).

**The change §13 step 2 made.** The design's first form asked every inserted variable to be
`NsVar` (`NsFresh τ`, a conjunct of `FutStep`). With it the own push, named by a program binder,
was no future, and `MonoOwnG` was not derived at a thunk slot at any placement, for that one reason
(§15.2). It was provable only with `FutStep` admitting a variable that is not `NsVar` when the
clause's type avoids it, free and bound: at `cbpv` and `binder` it is then `MonoG`'s instance at
the push. So `FutStep` was changed before any proof that depends on it beyond those of the order.
The cost this paragraph named in advance: with such insertions, `BindersLow` no longer keeps an
inserted variable off the binders of the code that runs at the future. An intermediate type of a
row's premise, or a type in a thunk's captured context, can bind it, and a row that meets such a
collision needs the renaming lemma §14 lists as `BindersLow`'s discharge inside its own proof. The
build found one more piece of the same cost: `StackJ`'s second kind admits only `NsVar` entries, so
a row that calls its premise at a future inserting another name meets a stack `SemS` does not
cover. Either `StackJ` admits the new names, with a hygiene the rows can discharge, or the row
renames the entry to an `NsVar` name, which is again the renaming lemma (§15.3).

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
The 6.64 folds also take `Tab.Local`, which every row's table meets (`Row.tab_local`).

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

The thunk's introduction (`ThunkVRow`) owes the body at `e :: σ'` and gets it from its premise
there, so its context must reach the pushed stack. No future does (§2.2, *The own lend*); that
transport is `MonoOwnG` (§4.1).

### 2.5 The semantic judgement, and W as a `SemWorld` (`Sem.lean`)

```lean
def CtxAvoids (x : LifeVar) (Γ : Ctx VTy) : Prop :=
  ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty

def CtxFresh (x : LifeVar) (Γ : Ctx VTy) : Prop :=
  ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty ∧ x ∉ VTy.binders s.ty

def OwnHyg (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) : Prop :=
  ∀ (x : LifeVar) (c : Lifetime.Life) (C' : CTy), C = .all x c C' →
    Δ.find? x = none ∧ CtxFresh x Γ

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
    (Δ.find? e.x = none ∧ σ.head? = some e ∧ CtxFresh e.x Γ ∧
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
- **The own lend's hygiene** (`CtxFresh` in `StackJ`'s third kind, `OwnHyg`): the entry named by
  the judgement's own binder is neither free nor bound in the context's live types. A slot's type
  that mentioned it free would read the entry's lifetime, and a `∀` of a slot's type that bound it
  would read its body at the entry's lifetime instead of its instance. `ThunkVRow` and
  `BangThunkVRow` take `OwnHyg` of their judgement, and `AllIRow` takes its binder bound in no live
  slot, because each calls its premise at a stack the own lend pushes and carries the context
  there by `MonoOwnG` (§4.1).
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
  Ext := ExtW                     -- OrdW at the empty substitution, a preorder by construction
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

`ExtPre (WP p)` holds by construction (`ExtPreW`, bookkeeping). `ExtW` is not the order the
clauses read: they read `Fut δ`, whose `FutOK.vars_sub` and `FutOK.pay` read the reading
substitution, so the order lemmas they use are stated at `δ` (§4.1). `WLaws (WP p)` is not
claimed: Targets' `Mono` reads a value at every `δ` and every type, with none of the index
hypotheses `MonoV` carries.

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
and `reconB′`'s acceptance are proved (`Survives e p`, at the term `e` fixed for `reconB′` before
statement 2's proofs start, §9.2). W is the surviving placement of least `rank`, the cuts order of
synthesis §4.2.

```lean
def Placement.rank : Placement → Nat
  | .cbpv => 0
  | .binder => 1
  | .binder0 => 2

def Survives (e : Expr) (p : Placement) : Prop :=
  Probe p ∧ ReconAccepted p e
```

**Decided or provisional.** A placement ranked before W counts against itself only through a
refutation. OQ-8 is decided against a placement only by a refutation of a statement of its `Probe`
or of `ReconAccepted` that passes §11: the negation proved, its configuration and values arising,
and the closed program whose execution reaches them exhibited. If a placement ranked before W is
only "not derived", W is **provisional**. The report then reads, for example, "cbpv: not derived,
no obstruction verified; W provisionally = binder". No consequence is drawn from a provisional W:
not for OQ-8, not for "interactions only at cuts", and not for D1's ranking against D2a and D3
(§4.4, §12.1).

A naturality placement (OQ-8 option 1) is not a clause set. It is the claim that the `binder0`
relation without its own-lend conjunct is natural under the freeze binder
(`Targets.FreezeBinderLife`). Statement 7 is its cheap check, and §4.4 records what follows.

---

## 4. Statement 0: W's `U`, `⊸` and `∀` clauses, fixed together

### 4.1 The statements (`Statement0.lean`)

The shared lemmas: definitions every placement shares.

```lean
def ExtPreW (p : Placement) : Prop := Targets.ExtPre (WP p).toBWorld

def FutReLend : Prop :=
  ∀ (δ : LSub) (ρ : WRes) (σ σ' : LStack) (αs αs' αs'' : List Life),
    StackOK σ αs → Fut δ ρ (σ, αs) (σ', αs') → ReLend αs'' αs' →
    ∃ αs₀, ReLend αs₀ αs ∧ Fut δ ρ (σ, αs₀) (σ', αs'')

def FutPart : Prop :=
  ∀ (δ : LSub) (ρz ρn ρ : WRes) (s s' : Stk), ResU.CompS ρz ρn ρ → Fut δ ρ s s' → Fut δ ρz s s'

def FutAvoidsTrans : Prop :=
  (∀ (C : CTy) (σ σ' σ'' : LStack), FutAvoids C σ σ' → FutAvoids C σ' σ'' → FutAvoids C σ σ'') ∧
  ∀ (A : VTy) (σ σ' σ'' : LStack), FutAvoidsV A σ σ' → FutAvoidsV A σ' σ'' → FutAvoidsV A σ σ''

def OpenSFBridge : Prop :=
  ∀ (δ : LSub) (Tab : OpTab) (Q : LStack → List Life → List SRec → Val → WProp) (σ : LStack)
    (k : Nat) (ds : List Bool) (αi αo : List Life) (ls : List SRec) (e : Expr) (ρ : WRes),
    OpenSF true δ Tab Q σ k ds αi αo ls e ρ → OpenS δ σ Tab (Q σ) k ds αi αo ls e ρ

def NilSoundRet (p : Placement) : Prop :=
  ∀ (δ : LSub) (S : Row) (A : VTy) (ls : List SRec) (e : Expr) (ρ : WRes), A.Data →
    cRL p [] δ (CTy.effOf S A) [] ls e ρ → cC (CTy.effOf S A) ls δ e ρ

def Statement0Shared : Prop :=
  (∀ p, ExtPreW p) ∧ FutReLend ∧ FutPart ∧ FutAvoidsTrans ∧ OpenSFBridge ∧ ∀ p, NilSoundRet p
```

The per-placement facts:

```lean
def MonoV (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls ls' : List SRec) (v : Val) (ρ : WRes)
    (σ' : LStack) (αs' : List Life),
    StackOK σ αs → Ext ls ls' ρ → Fut δ ρ (σ, αs) (σ', αs') → FutAvoidsV A σ σ' →
    TabAtS σ αs ρ → vRL p σ δ A αs ls v ρ → vRL p σ' δ A αs' ls' v ρ

def MonoG (p : Placement) : Prop := …   -- the same for 𝒢⟦Γ⟧ (`gRL`)

def MonoOwnG (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    StackOK σ αs → OwnPush δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    TabAtS σ αs ρ → gRL p σ δ αs ls Γ γ ρ → gRL p (e :: σ) δ (a :: αs) ls Γ γ ρ

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
  ∀ Δ Γ N C, C.isRet = false → OwnHyg Δ Γ C →
    SemS p Δ Γ (.val (.lam N)) (.comp C) → SemS p Δ Γ (.val (.lam N)) (.val (.thunk C))
def BangThunkFRow (p : Placement) : Prop := …   -- `bangThunkF` at `SemS`
def BangThunkVRow (p : Placement) : Prop := …   -- `bangThunkV` at `SemS`, with `OwnHyg`

def Statement0 (p : Placement) : Prop :=
  MonoOwnG p ∧ MonoV p ∧ MonoG p ∧ CallbackExtMut p ∧ CallbackExtImm p ∧ ForceRow p ∧
    ThawRelend p ∧ ThunkFRow p ∧ ThunkVRow p ∧ BangThunkFRow p ∧ BangThunkVRow p
```

Beside the bundles:

```lean
def MonoC (p : Placement) : Prop := …   -- `MonoV`'s form for the computation relation (`cRL`)

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
```

### 4.2 Why each tests the real question at full strength

- **The clauses are fixed together.** `U`, `⊸` and `∀` are clauses of one `mutual` block, read at
  the guard. No clause is checked at another relation. The three placements differ exactly in the
  flags of `Placement`.
- **The order: bookkeeping, and the lemmas the clauses read at `δ`.** `ExtPreW` is bookkeeping and
  tests nothing. `Fut` is a reflexive–transitive closure and `Ext` is reflexive and transitive, so
  `WP p` meets Targets' `ExtPre` by construction. It is among the shared lemmas because a Targets
  world must meet it. `WP p`'s `Ext` is `OrdW` at the empty substitution, which is not the order
  the clauses read: they read `Fut δ`, and `FutOK.vars_sub` and `FutOK.pay` read `δ`. The lemmas
  monotonicity at `U` turns on are therefore stated at `δ`:
  - `FutReLend`: the futures the clause quantifies over are taken after a re-lend, and a monotone
    value is re-lent at its future;
  - `FutPart`: a value is carried to a future at its whole resource, while the clause quantifies
    over futures at its part `ρz` strictly above the outermost lend (`FutOK.below` is downward
    closed along `CompS`);
  - `FutAvoidsTrans`: the futures of a future avoid the value's type only through each step's
    avoidance.
- **The `U`-clause thaw is proved at the guarded W.** `ForceRow`, `ThawRelend` and the four
  `U`-introduction rows are stated at `vRL p`, not transported from `vRLs`. At `cbpv` and `binder`
  the thunk rows owe the body at every future, and at `cbpv` the own lend at every future, so
  their proof is where the quantifier's cost shows.
- **Monotonicity is along the whole order, and across the own lend.** That includes any number of
  insertions at any depths, which the share needs between lenders, and hiding, which `[handle]`
  needs. A front-only order would make `MonoV` easier and hide the between-lenders case. `MonoC`
  is named because `binder0` needs it where `cbpv` and `binder` have monotonicity at `U` by
  construction (§4.3). `MonoHide` is `MonoV`'s hiding instance (`MonoHideFromMonoV`), named because
  it is where `binder0` is tested hardest. `MonoOwnG` is the transport across the callback's own
  lend (§2.2): `ThunkVRow` and `BangThunkVRow` at `cbpv`, and `AllIRow` at `binder0` and `binder`,
  call their premise at the pushed stack. It is what tests the claim that the own lend is not a
  second order (below). It is per placement, and it is the first per-placement fact attempted
  (§13). With `FutStep` as changed (§2.2, *The change §13 step 2 made*) the push is a one-step
  future, and `MonoOwnG` is `MonoG`'s instance there (§15.2).
- **The nil slice is checked where the programs read it.** `NilSoundRet` is W inside Core at
  `F_Σ A` with `A` data: the slice Targets' `AdequateRetAt` reads, and §9.1's route. No position
  of it is contravariant in W. The operation types are read by Core's `vC` in `rowTab` at both
  relations (`Stacked.lean:228`), and the answer is data. It instantiates the share's futures at
  the reflexive future (`OpenSFBridge`) and is expected to be mechanical (`bodyS_nil_iff`'s
  pattern). The nil slice at every type, `NilSoundV` and `NilSoundC`, is beside the bundles with
  `NilAgreesU` and `NilAgrees`. Core's `cC` at `⊸` reads its argument contravariantly
  (`∀ v, (vCE none true A ls δ v ─⋆ cC C …)`, `Core/Relation.lean:157`), so W inside Core at
  `A ⊸ C` needs Core inside W at `A`. At a thunk argument that is `NilAgreesU`, and the borrow
  constants' types have that shape: `withbor1UTy` and `withbor2UTy` are
  `U(Ref A ⊸ cbUTy ⊸ F_Σ …)`, with `cbUTy = U(∀'x. L ⊸ F_Σ …)` (`Core/EffBorrow.lean:177-190`), as
  does `retryR`'s `!U(1 → …)` argument. The expected failure of all four at those types is
  outcome (c), OQ-58's question, which is no stop (§6.3), so none of them is in a bundle.
- **The callback-extension fact is at any related argument.** The argument is any value of
  `Mut 'y T` (or `Imm 'y T`, its coherence with the records included) at the extended stack, so
  the `⊸` clause there is exercised, not only at the lend's own view. The callback is a value of
  the constant's callback type `cbUTy` (`Core/EffBorrow.lean`), not a premise. `CDerives` has the
  borrow operations as constants (`Below.lean`'s "What it measures"), so the row must get the
  callback's behaviour at `σ·y` from its value.
- **One quantifier, in the design's reading of synthesis §11 (d).** The synthesis words failure
  (d) as: "Statement 0 holds only with different future-world quantifiers at `U` and at `⊸`, which
  no single definition of W reconciles". The design reads "one quantifier" as a property of
  `Relation.lean`'s text, checked by reading it, which holds at all three placements: every clause
  reaches a stack other than its own only through `FutQ` (W's order `Fut`, or the stack itself as
  the placement's flag says), and at the clause that makes the callback's own lend `OwnPush` at the
  type the clause reads may follow. That reading is the design's, not the synthesis's text. It
  admits the type-directed own lend at `U` (`cbpv`) by definition, and with it OQ-8 option 2's
  claim of interactions only at cuts. So the outcome is reported against both (§12.2):
  - against the synthesis's wording: whether `OwnPush` at `U` is a second future-world quantifier.
    It is read from the type and sits at `U` and not at `⊸`. Its stack is a one-step future of the
    clause's stack (§2.2), which the clause's own futures do not reach (`FutAvoids` asks the
    type's binders avoided);
  - against the design's reading: whether every clause reaches other stacks only as above.

  The design's case that the own lend is not a second order:
  - It is the outermost `∀`'s instance, read as the entry of the lend the instance names. It is
    named by the type's binder, so it cannot belong to a type-free order. `vRLk`'s extension is
    relative to the type in the same way (`e'.x = x ∨ ¬ CFree e'.x C`).
  - It comes after a future, so a value carried to a future keeps it.
  - It coheres with the order when contexts are Kripke across it: `MonoOwnG`. It holds only once
    `FutStep` admits the push as a step (§2.2, *The change §13 step 2 made*), and then the push is
    a future and one order remains: at `cbpv` and `binder` `MonoOwnG` is `MonoG`'s instance
    (§15.2). At `binder0` it is not derived, with `MonoG binder0`.
  - The world's `Ext` is the type-free part, `OrdW`, since `Mono` reads no type.
  - At `binder0` neither `U` nor the share quantifies over futures (`FutQ false`). Its coherence
    with W's order is a theorem, not a clause: `MonoV binder0` and `MonoG binder0`, both in its
    bundle, say that its values are Kripke along `Fut`.
  - Failure (d) in the design's reading (§12.2) is a clause changed to reach other stacks by any
    other means.

### 4.3 Where each placement is expected to be tested hardest [unchecked]

These are readings that order the work. None is derived, and none is an obstruction. The build's
outcome for each is §15.

- **`MonoOwnG`, at every placement.** At a slot of data, of a reference or of a view it is the
  leaves' reading at the pushed stack, which agrees with the old one at the slot's free variables
  (`CtxFresh`). At a thunk slot `g : U C₁` it is expected not to follow at the current `FutStep`:
  - The push is no future of the stack (its variable is a program binder, not `NsVar`). So `g`'s
    `U` clause gives `g`'s body at no stack holding the pushed entry. At `cbpv` the clause gives
    the futures and `C₁`'s own lend, at `binder` the futures, and at `binder0` the stack itself.
  - The transport then needs `g`'s forced body monotone along an insertion the order does not
    contain, `MonoC` along the push, and at `⊸` that is the contravariant step `binder0`'s
    monotonicity meets (below).
  - So `MonoOwnG` is expected to be "not derived" at a thunk slot at every placement, for one
    reason shared by all three: our `Fut`, not the placement. With it go `ThunkVRow` and
    `BangThunkVRow` at `cbpv` (statement 0) and `AllIRow` at `binder0` and `binder`
    (statement 1).
  - The change the expectation points to is the one §2.2's *Names* states. `FutStep` would admit an
    inserted entry whose variable is not `NsVar` when the clause's type avoids it, free and bound
    (`FutAvoids`). The own push is then a one-step future at depth `0`: `OwnOK` gives `FutOK`'s
    fields at `k = 0`, and `vars_sub` follows from `SubDom` and the binder new to `Δ`. `MonoOwnG`
    is then `MonoG` at that future. Its cost is the *Names* guarantee at the code that runs at the
    future (§2.2).
  - A second candidate changes the representation instead. The own lend would be named by a
    future's name, and the type's binder read through `δ` (`δ.extend x a`). The push is then a
    one-step future followed by the plain `∀`'s instance, and `MonoOwnG` is `MonoG`'s instance. Its
    cost is GhostEnd's representation: `callback_ext` reads the entry named by the binder, so
    `CallbackExt*` and their proofs are restated.

  §13 step 2 orders the decision.
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
    - a future at a resource is a future at its parts (`FutPart`);
    - the entries a composite inserted avoid the type when each step's do (`FutAvoidsTrans`);
    - a future's views are its stack's, the inserted entries' flags off;
    - `Ext` at a resource gives `Ext` at its parts (Core's `Ext`, as `he.right hc`).

    The first three are statement 0's shared lemmas; the last two are stated where a proof first
    uses them.
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
- **The nil slice, at every placement.** `NilSoundRet` instantiates the share's futures at the
  reflexive future (`OpenSFBridge`) and reads a data answer, so it is expected to be mechanical
  (`bodyS_nil_iff`, `vRLs_nil`'s pattern). The nil slice at every type is not:
  - `NilSoundV` and `NilSoundC` meet Core's contravariant `⊸`. At an argument type `A` they need
    Core's `A` inside W's, which at a thunk `A` is `NilAgreesU`.
  - `NilAgreesU` and `NilAgrees` ask Core's relation to carry obligations it has no notion of at
    the placement's quantifier sites: at `binder0` the own lend at `∀`; at `cbpv` futures and own
    lends at `U`, and futures in the share; at `binder` all of them.

  A Core-related callback keeps its view across a stop, where W re-lends it. So the old-in-new
  direction is not expected to follow from Core's relation at callback types, and with it neither
  `NilSoundC` at the borrow constants' types nor `NilAgrees`. `NilAgrees` is a statement about the
  identity of two definitions, so a refutation of it at any inhabitant decides OQ-58 for the
  placement's definitions (§6.3). What FL needs at `σ = []` is the `U`-introduction rows, which
  are in `Statement0`, and `NilSoundRet`, which is in the shared lemmas. The expected answer to
  OQ-58 is that Core is not W's `σ = []` instance at those types: outcome (c), Core redefined
  (§12.2). That is no stop, which is why none of these four is in a bundle.

### 4.4 What statement 0 decides

- **OQ-8, when W is decided** (§3: every placement ranked before W refuted by a refutation that
  passes §11).
  - `cbpv` is W: OQ-8 option 2. D1 then meets "interactions only at cuts", with this cost
    recorded: the `U` clause reads its type's outermost `∀` to name the callback's own lend. That
    reading stays at `U`, the resume cut's value side. Every clause reads the stack's lifetimes at
    its leaves through `extS`, as Core's relation reads its record list; that is not a quantifier.
    The claim holds in the design's reading of (d) (§4.2). In the synthesis's wording it is
    reported with the own lend's status beside it.
  - `binder` or `binder0` is W, every placement before it refuted: option 3. Every `⊸` and `∀`
    clause, or the `∀` clause alone at `binder0`, carries a resume obligation away from the cuts.
    D1 then does not meet "only at the cuts". It keeps its rank against D2a and D3 (synthesis §8).
- **OQ-8, when W is provisional.** A placement ranked before W is only "not derived". The report
  records W as provisional ("cbpv: not derived, no obstruction verified; W provisionally =
  binder") and decides nothing: OQ-8 stays open, and nothing follows for "only at the cuts" or for
  D1's ranking against D2a and D3. Only a refutation that passes §11 counts against a placement.
- **Option 1 (naturality).** It is not decided here. Statement 7 tells whether its known witness
  (`mut_not_natural`) arises. A placement that passes makes option 1 unnecessary for D1.
- **"Whether `U` and `⊸` take the same quantifier"** (02-experiments §1.3). Under `cbpv` they do
  not need to, since `⊸` takes none and the `U` clause carries it, as Core's relation does. Under
  `binder` they take the same. If statement 0 holds only after a clause is changed to reach other
  stacks than through `FutQ` and `OwnPush`, that is failure (d) in the design's reading (§12.2).

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
  ∀ δ σ αs ls (e : LEnt) α (d : Bool) (ρ a R : WRes), StackOK σ αs →
    List.IsChain (· < ·) (α :: αs) → ρ.InStratum α → e.x ∉ σ.map LEnt.x → e.l ∉ σ.map LEnt.l →
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
    (∀ s ∈ Γ, s.live = true → x ∉ VTy.binders s.ty) →
    SemS p (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C) →
    SemS p Δ Γ (.val (.lam M)) (.comp (.all x b C))

def BelowRow (p : Placement) : Prop := SemS p belowCtx [] belowTerm (.comp belowType)
def BelowExcluded (p : Placement) : Prop :=
  ∀ δ C ls f v (α αy : Life) (k : BoCa.Loc), αy < α → k ≠ belowEnt.l →
    guardW [belowEnt] [α] (cRL p [belowEnt] δ C [α] ls (.app f (.val v))) (innerView k αy)

def Statement1 (p : Placement) : Prop :=
  TabNil ∧ TabParts ∧ TabUpd ∧ TabRuns ∧ TabStart ∧ TabHide ∧ TabRelend ∧ TabFut ∧ TabResume ∧
    LamRow p ∧ AllIRow p ∧ BelowRow p ∧ BelowExcluded p

def ArisesSound : Prop :=          -- beside the bundle
  ∀ c : Cfg, Arises c → ArisesAt c.σ c.αs c.ls c.ps c.ρf c.ρ c.fρ
```

`belowEnt`, `belowCtx`, `belowTerm` and `belowType` are `Below.lean`'s `e₀`, `Δ₀`, `allBelowE` and
`allBelowC`, restated as data.

### 5.2 What statement 1 states, and why it is re-scoped

**The synthesis's statement.** Synthesis §11 statement 1 reads: "W's arising guard is read from
`TW`, not from GhostEnd's `TabAtS`. That is OQ-45's first question: is the lend table a `TW`
invariant at every depth (`tabAt_of_TW`, T-ARISE.0, not in Lean)?" T-ARISE.0 reads the table off
one `TW` world. That pointwise form is `TabOfTWPointwise`, and it is not in the bundle.

**What the bundle states instead.** Every transition of W's semantics keeps the table: from a
configuration that has it, each transition yields one that has it. That is a run-invariant claim,
and it rests on the per-transition facts below, not on a set of configurations. This changes the
content of statement 1, for three reasons:
- Arising is historical. `TW` records no 6.65 lend (OQ-44), so one world cannot say that a cell
  was folded after a lend opened.
- The pointwise form is expected to fail at `innerView` (below), a configuration that does not
  arise. A refutation there is a fact about the pointwise statement, not about D1.
- Arising tests are directional: a coarser arising set is sound for proving and unsound for
  refuting. The run-invariant form is the one a proof can use, and it reads the guard off `TW`'s
  runs, not beside them.

W's configurations are `TW`'s (`WP p`'s `Fam`), as Core's are. The guard asks more of the local
resource at a stack: the stack's table. The bundle has one fact per transition of W's semantics:
- the nil index: `TabNil`;
- a run: `TabUpd`, [TR] 6.50 keeping every borrow cell's lifetime at its location through `↭`, at
  the innermost lend's `↓α` and at the outermost lend away from the stack's places (`tabAt_updV`
  twice), with `TabRuns` its `wpG` form;
- a part: `TabParts`;
- a lend's start: `TabStart`, 6.112's `И` putting the callback's resource above the fresh lifetime.
  It takes only the freshness fields the table reads: the fresh lifetime in nesting order and below
  the callback's resource, and the variable and place new to the stack. `LendMut` and `LendImm`
  carry exactly those. `OwnOK`'s payload scoping is not one of them;
- a handler: `TabHide`.

And one fact per configuration the relation quantifies over:
- a re-lend: `TabRelend`;
- a future: `TabFut`;
- the resume composite: `TabResume`. The continuation's share is re-lent, the inner entries'
  views are handed to it, and the handler's answer, made at the kept part's future, is joined to
  it. That is the configuration at which the share's rows call their induction hypothesis. It
  follows from `TabRelend`, `TabParts` and `TabStart`'s argument at an empty view.

These are the synthesis's "It holds for one lend (`wpG_tabAt`) and for one entry
(`wpG_tabAtS_one`)", at every depth. Proved, they make `TabAtS` the stack's run invariant, read
from `TW`'s runs transition by transition. A guard that some transition of W's semantics does not
keep would be a guard beside `TW`: failure (b).

`ArisesSound` (`Arises ⊆ ArisesAt`) is stated beside the bundle. It follows from the
per-transition facts by induction on `Arises`, and it is used only to exclude a witness from
`Arises`. The guard's claim does not rest on it. `Arises` is the refutation side's set, and its
direction is not established (§11). A set not shown to contain every configuration that arises
cannot carry a claim about all of them. No proving-direction set is needed, since the
run-invariant claim is per transition. If a proof ever needed one, it would be defined
separately, as an over-approximation.

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

At `binder0` and `binder` the `∀` clause pushes the own lend, an entry named by the binder
(`OwnPush`), and the row calls its premise at `en :: σ'`, at `δ.extend x α`. The context is
carried there by `MonoOwnG`, which asks the binder to be neither free nor bound in `Γ`'s live
types. So the row adds "bound in no live slot" to Core's rule's "free in no live slot". At the
pushed stack `δ.extend x α` and `δ` read the same lifetimes: the stack's entry overrides `x`, and
no payload type of `σ'` mentions `x` (`hσT`). That step is `vRLa_congr`'s.

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

def RCarried (R : List SRec → Val → WRes → Prop) : Prop :=
  ∀ (ls ls' : List SRec) (v : Val) (σ : WRes), Ext ls ls' σ → R ls v σ → R ls' v σ

def TabKeepsRec (Tb : Table) (r : FrameRec) (α : Life) (R : List SRec → Val → WRes → Prop)
    (P₀ : Life → Val → WProp) : Prop :=
  ∀ (ls : List SRec) (t : Expr) (X : List SRec → Expr → WProp) (ρ : WRes), r ∈ rsOf ls →
    Tb ls t (fun ls'' e'' => rebView r.le α R P₀ ls'' ⋆ X ls'' e'') ρ →
    Tb ls t (fun ls'' e'' ρ'' => r ∈ rsOf ls'' ∧ (rebView r.le α R P₀ ls'' ⋆ X ls'' e'') ρ'') ρ

def RebFrameR : Prop :=
  ∀ (Tb : Table), Tb.Mono → ∀ (r : FrameRec) α R P₀ P Q ls e,
    RCarried R → TabKeepsRec Tb r α R P₀ →
    r ∈ rsOf ls → (∀ ls', r ∈ rsOf ls' → RebChooseTW ls' r.le (R ls') P₀ (P ls')) →
    Entails (rebView r.le α R P₀ ls ⋆ RebRelend Tb r.le α R P₀ P Q ls e) (ewpTS ls e Tb Q)

def RebChooserNonVacuous : Prop :=
  ∃ (r : FrameRec) (x : LifeVar) (α : Life) (ls : List SRec) (ρ : WRes) (Tab : OpTab)
    (n i : UInt32) (en : OpEnt),
    r.T.immReborrow (.var x) ≠ r.T ∧ ¬ VFree x r.T ∧ r ∈ rsOf ls ∧
    Tab n i = some en ∧ en.abort = false ∧
    RCarried R₀ ∧ TabKeepsRec (opTable Tab) r α R₀ P₀ ∧
    (∀ ls', r ∈ rsOf ls' → RebChooseTW ls' r.le (R₀ ls') P₀ (P₀' ls')) ∧
    rebView r.le α R₀ P₀ ls ρ
  -- R₀ ls' := vC false r.T ls' r.δ;  P₀ β := vShape (r.T.immReborrow (.var x)) (r.δ.extend x β);
  -- P₀' ls' β := vC true (r.T.immReborrow (.var x)) ls' (r.δ.extend x β)  (written out in Lean)

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
   non-abortive) and `AllCross` (every stop crosses every entry). The 6.64 folds `stack_step_imm`
   and `stack_spans_imm` also take `hL : Tab.Local` (`:1003`, `:1129`): the table's operation types
   carried along `Ext`. `Tab.Local` holds at every row's table (`Row.tab_local`,
   `Core/EffRules.lean:733`, from `vC_local`), and the piece's table at `F_Σ R` is a row's
   (`rowTab` at `CTy.effOf S R` is `Row.tab S δ`, `effTab_effOf`). So the programs' rows meet it,
   `genSelf`'s affine `Yield` and `reconB′`'s `{wait}` with `timeout`'s cancel of it, and it
   restricts nothing they use. `LinResume` and `AllCross` are what restrict the folds: they apply
   only at linear, resuming rows whose stops cross the whole stack, and at `σ = []` there
   `openS_nil_ewp` closes them. `SpanW2Row` and `SpanW1Row` are at `RowClass.any` and at every
   stack: `genSelf`'s row is the affine `Yield`, and `reconB′`'s `timeout` cancels. On `genSelf`'s
   critical path three items are therefore **New**:
   - (i) the stacked commutation at a `ResumeAff` table with a cancel share: `stack_step_other`
     with `opTableO`'s owner hand-back at a cancel (`Drop.lean:49`), read at `σ·new`;
   - (ii) the conversion from the callback's `OpenS` at `[e]` to `Relend (opTableO Tab l T δ) …`,
     which `withborR_compat` consumes; or a route through `OpenD` and `relend_of_openD`, which
     holds at every monotone table, `opTableO` among them (`opTableO_mono`);
   - (iii) `AllCross` relaxed for `SpanW*Row` at `σ ≠ []`: the callback's row need not cross the
     outer entries, so its stops are at depths below `|σ| + 1`.

   **At `cbpv` and `binder`.** The piece is `OpenSF true`, whose share owes the continuation at
   every future of the kept part. The bridge back to GhostEnd's proved results is `OpenSFBridge`
   (statement 0's shared lemmas): `OpenSF true δ Tab Q σ … ⊧ OpenS δ σ Tab (Q σ) …`, every futures
   quantifier taken at the reflexive future. GhostEnd's lemmas then split three ways.
   - **Used unchanged**, since they do not mention the piece: the view, drop and owner
     bookkeeping (`vwS_*`, `vwE_*`, `dropS_*`, `ptoImmS_*`, `ownWandE_pass`, `ghostS_of_boxTop`),
     the table facts (`tabAt_start`, `tabAt_off`, `tabAt_viewI`), `opTable_shift`, `q64_ext`,
     `viewI_split`, Frames' `opTable_extR` and `ewpPostR_ext`, and Drop's `ewp_then_owner`,
     `cancel_then` and `opTableO_mono`.
   - **Used through the bridge**, since they consume a piece and produce something that is not W's
     piece at a stack: `openS_nil_ewp` and `bodyS_nil_iff`, for `NilSoundRet`'s `F_Σ` case at
     `σ = []`, whose output is Core's `ewpTS`.
   - **Restated over `OpenSF`**, since their output is W's piece at a stack, which at `cbpv` and
     `binder` must owe its continuations at futures: `stack_step_other`, `stack_step_reborrow`,
     `stack_step_imm`, `fold_other`, `fold_imm`, `stack_spans_mut`, `stack_spans_imm`,
     `openS_val_any`, `openS_yield_any`, `stopS_full` and `stopS_of_full`. The same goes for
     items (i)–(iii) above, for `relend_of_openD` at a stack, for `withborR_compat` (its conclusion
     is the borrow's computation, W's piece at the borrow's stack), and for the 6.64 cancel path
     below.

   Each restatement follows the GhostEnd proof it mirrors, step by step, with the futures
   quantifier carried through each unfolding (CLAUDE.md §1). A shorter route is recorded in the
   restatement's docstring with the GhostEnd technique it leaves unbuilt. **New**: GhostEnd's
   argument at a stack-indexed least fixed point. At `binder0` the piece is GhostEnd's `OpenS`
   itself, and every lemma is used unchanged at the rows whose hypotheses it meets.

   `stack_step_other`'s callback form puts the answer above the outermost lend (`cbQ`'s `boxTop`).
   An answer that keeps a view of `σ` (#276's shape) needs the form `bodyAtD` has. That is not
   needed at `σ = []`, the only stack the programs' borrows sit at, but `SpanW2Row` is at every
   stack.
4. **The unwinding frame and the cancel.** `withborR_compat` (`Drop.lean:108`) for 6.65, from
   (ii): `ewp_then_owner` puts the owner back at a cancel and `d` disposes of it.

For `withbor` (1) the same, with `CallbackExtImm`, `stack_step_imm` and `ewpTS_I_frameR`.
`stack_step_imm` takes `LinResume` and `AllCross`, as the 6.65 folds do, and `Tab.Local` besides,
which the programs' rows meet (item 3); so (i)–(iii) are needed at 6.64 too. `ewpTS_I_frameR`'s
`hTL` is `opTable_extR`, which takes `Tab.Local` as well. The cancel path over a 6.64 frame is
**not built** (p10 §5.1 X.4). It is the 6.64 analogue of `withborR_compat`:
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
- `wpG_frame` (`Core/EffWp.lean:1005`) carries the kept copy to the run's end. `wpG` chooses that
  list among those with the start's members (`Core/EffDefs.lean:27-40`), and `wpG_frame`'s
  `hR : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (R ls) (R ls')` asks the frame carried to each of
  them. The kept copy `rebView … ls` reads the payload input at `R ls`, so the step needs `R`
  carried. That is `RebFrameR`'s added hypothesis `RCarried` (`R` along `Ext`, 6.64's `hQ` form).
  Lists with the same members are `Ext`-related at every resource, so it gives `hR`;
- `rebF`'s wand takes the copy back. At a return the answer is in `Q`. At a stop the table owes the
  view at the resumption's list beside the next unfolding, which the induction hypothesis closes
  (`Tb.Mono`). The premise owes the view at that list; a row discharges it from the copy handed
  back, carried along `Ext` by `RCarried`;
- the next unfolding runs `wpG_reborrow` at the resumption's list `ls''`, which needs
  `RebChooseTW ls'' …`. The chooser hypothesis supplies it where `r ∈ rsOf ls''`, and a table with
  only `Tb.Mono` says nothing about the lists it resumes at. That is the second added hypothesis,
  `TabKeepsRec` (the shape of `ewpTS_I_frameR`'s `hTL` and `opTable_extR`): at a stop over a list
  holding `r`, whose continuation is owed the view, the table owes it only at lists holding `r`.
  `opTable` meets it at a table whose answers hold nothing. Its share is quantified over `Ext` at
  the share's resource (`contShare`), that share holds the view the continuation is owed, and
  `Ext` keeps a record relevant to it (`Keeps`, `Rel`). Then `rebChooseTW_top` supplies the
  chooser at each resumption's list.

If the wand form does not close, the alternative puts the hand-back on the stop disjunct only and
forgets the copy at a return by 6.149 (`wpTS_I_forget`; its `wpG` form is not built).

`RebFrameR`'s chooser hypothesis is shaped as `rebChooseTW_top` supplies it: at every list that
holds the view's record, with `R` and `P` read at that list. Its two other added hypotheses come
from the steps above that read them: `RCarried` from `wpG_frame`'s `hR`, and `TabKeepsRec` from the
next unfolding's chooser. `RebChooserNonVacuous` shows all three, with an inhabited `rebView`,
together at one record whose payload is not data (`r.T.immReborrow ≠ r.T`, the only place 6.150
does anything), at an operation table with a resuming entry:
- `RCarried` at `R = vC false r.T · r.δ`, by `vC_local`;
- `TabKeepsRec` at an `opTable` whose answers hold nothing, by `contShare`, `Keeps` and `Rel`;
- the chooser by `rebChooseTW_top` at each list holding the record, at `δ' = r.δ`;
- the view from the record's cell.

**`SpanLoadRow`.** At a data payload `Imm̲ 'y A = A` (`VTy.immReborrow`, `Core/Types.lean:1447`).
The callback then gets data, and no entry spans the stop. That is the case `reconB′`'s reads are,
and they complete before the next `wait` (synthesis §11), so the programs do not exercise
`RebFrameR`. At a payload with inner places, 6.150's image holds views at the new lifetime at the
payload's chain positions. The stack then needs an entry for a reborrow, a kind GhostEnd's
`LEnt` lacks (`mut` and `imm v` only) and WorldW's `OEnt` has (`reb`). That would be a finding
about what `σ` holds (OQ-44), recorded, not a new relation.

### 6.3 OQ-58: Core as W's `σ = []` instance

`NilAgrees p`, `NilAgreesU p`, `NilSoundV p` and `NilSoundC p` are statement 0's
(`Statement0.lean`), beside its bundles. OQ-58 is decided there, after the bundles' work, at the
placement W is. They are beside the bundles because their expected failure is this section's
outcome (c), which is no stop. `NilSoundC` meets Core's contravariant `⊸`, and at a thunk argument
it needs `NilAgreesU` (§4.2). What the programs' adequacy reads is `NilSoundRet`, in the shared
lemmas (§9.1).

`NilAgrees` states that two definitions are one relation at `σ = []`. A refutation of it at any
inhabitant, arising or not, decides OQ-58 (a) negatively for the placement's definitions. It is
therefore exempt from §11's items 2 and 3, which are about what a program reaches, not about what a
definition is. The outcomes:
- `NilAgrees p` proved: Core is W's `σ = []` instance (OQ-58 (a)).
- `NilAgrees p` refuted, with the sites at which it fails, each with the introduction rows that
  hold there at W: outcome (c) (§12.2). That is a cost, not an obstruction to D1 and not a stop.
  `NilSoundRet` still carries W's programs to Core's adequacy (§9.1), since it reads only a data
  answer.
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

**The route for the runs.** `SemS` at `σ = []` gives `cRL p [] δ (.ret A) …` at the program's data
answer `A`. `NilSoundRet` at `S = []` gives Core's `cC`, which is `coreB`'s `comp`, and
`adequateRetAt_core_none` (`Targets/B/BoLo.lean:195`) gives safety and termination. That lemma
reads every row it is handed as `[]` at `Platform.none` (`row_nil_of_le`), and `DivFree S A` is
`A.Data`, so `NilSoundRet`'s `F_Σ A` at a data `A` is all of the nil slice the route reads. The
answer's run is written out, or read off an interpreter proved to agree with `Step1`.
`genSelf_eval` is evidence, not the run.

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
- **The term is fixed before statement 2's proofs start.** `Survives e p` leaves `e` free, and
  `ReconAccepted p e` holds of any term accepted at `F (Flag ⊗ Flag)` answering `(tt, ff)`. So the
  term is committed to `Programs.lean` as a definition, `reconB'`, with the shape choice above and
  its reason, before any statement 2 proof is begun. From then on `Survives` is read only at it.
  The structural requirements it must meet, each checked against the committed term by reading it:
  - the scheduler (`resumer wait`) and `timeout` outside their borrows;
  - `retry`'s handler of `exn` inside the first borrow, with `retryR` instantiated at a row there;
  - a `wait` cancelled under `timeout`, inside a 6.64 lend (`withbor` (1)), so the cancel path
    over a 6.64 frame is exercised.

  A later change to the term is a new commit with its reason, and `ReconAccepted` is then read at
  the new term only.
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

   def Cfg.at (c : Cfg) (ρf ρ : WRes) : Cfg := ⟨c.fρ, ρf, ρ, c.ps, c.ls, c.σ, c.αs⟩

   def viewTy (e : LEnt) : VTy := match e.k with
     | .mut => .mut (.var e.x) e.T
     | .imm _ => .imm (.var e.x) e.T

   def RunEnd (c : Cfg) (e : Expr) (c' : Cfg) (t : Expr) : Prop := …  -- `wpG`'s run conjuncts,
                                     -- the stack fixed, the garbage joining the frame
   def LendMut (c c' : Cfg) (e : LEnt) : Prop := …   -- `TW.mutFold`'s premises; the entry pushed
                                     -- below the callback's resource; the view its cell
   def LendImm (c c' : Cfg) (e : LEnt) : Prop := …   -- `TW.immFrame`'s premises, the same

   mutual
   inductive Arises : Cfg → Prop where
     | nil {fρ ρf ρ ps ls} : TW fρ ps (rsOf ls) → Tagged fρ ps ls → ResU.Hash ρf ρ →
         ResU.CompS ρf ρ fρ → Arises ⟨fρ, ρf, ρ, ps, ls, [], []⟩
     | run {c c' Δ Γ e₀ j γ t} : Arises c → ProbeRules Δ Γ e₀ j → ArisesCtx c Γ γ →
         RunEnd c (substAll γ e₀) c' t → Arises c'
     | part {c ρ₁ ρ₂ ρf'} : Arises c → ResU.CompS ρ₁ ρ₂ c.ρ → ResU.CompS c.ρf ρ₂ ρf' →
         ResU.Hash ρf' ρ₁ → Arises ⟨c.fρ, ρf', ρ₁, c.ps, c.ls, c.σ, c.αs⟩
     | lendMut {c c' e} : Arises c → LendMut c c' e → Arises c'
     | lendImm {c c' e} : Arises c → LendImm c c' e → Arises c'
     | hide {c} (N : UInt32 → Bool) :
         Arises c → Arises ⟨c.fρ, c.ρf, c.ρ, c.ps, c.ls, hideS N c.σ, c.αs⟩
   inductive ArisesV : Cfg → Val → VTy → Prop where
     | ret {c c' Δ Γ e₀ j S A γ v} : Arises c → ProbeRules Δ Γ e₀ j → jdgCty j = CTy.effOf S A →
         ArisesCtx c Γ γ → RunEnd c (substAll γ e₀) c' (.val v) → ArisesV c' v A
     | view {c c' e ψ ρc ρf'} : Arises c → (LendMut c c' e ∨ LendImm c c' e) →
         ResU.CompS (ResU.single e.l ψ) ρc c'.ρ → ResU.CompS c'.ρf ρc ρf' →
         ArisesV (c'.at ρf' (ResU.single e.l ψ)) (.loc e.l) (viewTy e)
   inductive ArisesCtx : Cfg → Ctx VTy → List Val → Prop where
     | nil {c} : c.ρ = PMap.empty → ArisesCtx c [] []
     | dead {c s Γ w γ} : s.live = false → ArisesCtx c Γ γ → ArisesCtx c (s :: Γ) (w :: γ)
     | live {c s Γ w γ ρ₁ ρ₂ ρf₁ ρf₂} : s.live = true → ResU.CompS ρ₁ ρ₂ c.ρ →
         ResU.CompS c.ρf ρ₂ ρf₁ → ResU.CompS c.ρf ρ₁ ρf₂ → ArisesV (c.at ρf₁ ρ₁) w s.ty →
         ArisesCtx (c.at ρf₂ ρ₂) Γ γ → ArisesCtx c (s :: Γ) (w :: γ)
   end

   def ArisesNonVacuous : Prop := ∃ c : Cfg, Arises c ∧ c.σ ≠ []
   ```

   Each transition is a step of W's semantics:
   - at the nil index the arising set is `TW`'s, Core's settled one;
   - a run of a term the probe's rules derive ends as `wpG`'s run ends: the machine's run, `↭` on
     the local part, a tagged `TW` world at the end. Its captured values arise at its start
     (`ArisesCtx`): each live slot's value at the slot's type, holding its own part of the start's
     local resource, the parts composing to it, so a linear slot is used once and two slots do not
     share a cell;
   - a part of the local resource is taken, the rest joining the frame;
   - a lend row opens a lend: `TW.mutFold`'s or `TW.immFrame`'s step, its entry pushed below the
     callback's resource (6.112's `И`);
   - a handler is installed.

   **The direction is not established.** `Arises` is meant to under-approximate what arises, the
   direction a refutation needs. The definitions close what they can: a run's values are typed
   and tied to its start, and a value's type is kept. Two gaps remain, and no statement here closes
   them:
   - a run's values share its start's configuration (world, records, frames, stack and
     lifetimes), not its path. Each slot's value is witnessed by its own path to that
     configuration;
   - a lend, a handler and a part are taken at any arising configuration, not where a program's
     term opens the lend or installs the handler.

   So nothing here shows that every `Arises` configuration is reached by a closed derivable
   program's execution, and the design does not claim it. An `Arises` path is therefore not
   enough. A refutation is admitted only with the program as well: a closed `ProbeRules` program,
   its run from the nil index, and the path read along that run. Each run of the path is a run of
   the program's current term with the values that term holds, and each lend and handler sits at
   the term that opens or installs it. The Lean statement of that reading is a term-tracked
   arising, in which each run continues the previous run's end term and each lend and handler is
   taken at the term that opens it. It is written when a refutation is first offered as an
   obstruction; no proof needs it. Until then a refutation at an `Arises` configuration is a
   refutation at the probe's arising set, reported as a fact about the statement.
   - `ArisesAt` is the pointwise consequence: the world `TW`'s, the stack consistent with it, the
     local part consistent with the table. `Arises ⊆ ArisesAt` (`ArisesSound`, beside statement 1)
     follows from statement 1's per-transition facts. It is a necessary condition, used to exclude
     a witness, never to admit one. Statement 1's claim about the guard does not rest on it (§5.2).
   - `ArisesNonVacuous` (some configuration with an open lend arises) is proved first, so that the
     check can be passed at all.
   - A run inside a resumed continuation runs a reduct, not a derived term. So `Arises` reaches a
     continuation's re-lent start (a run to the resumption, a part, the re-lends), but not the
     configurations further inside it. A refutation that needs one of those is recorded as a fact
     about the statement until a transition for it is added with its justification.
3. **Its values arise**, when the refutation is about a value or a computation in the relation
   rather than about a derivation: `ArisesV c v A`, at the type the refuted statement reads `v` at.
   The value is the answer of a run of a term the probe's rules derive, at the judgement's answer
   type, with the `ProbeRules` derivation exhibited, or the view a lend row hands its callback at
   `Mut 'x T` or `Imm 'x T`. A relation-level value that no derived term produces does not arise
   (✓-valid is not reachable). Item 2's program is exhibited for the value's path too.
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
`TW` part and fails the table, and it is not in `Arises`. `NilAgrees`, `NilAgreesU`, `NilSoundV`
and `NilSoundC` are exempt from 2 and 3: they are about the identity of two definitions (§6.3).

---

## 12. Success, failure, and the stop rule

### 12.1 Success

- `Survives e p` is proved at a placement `p`, at the term `e` committed for `reconB′` (§9.2).
  That is `Probe p` (statement 0's shared lemmas, statements 0–4, `GenSelfAccepted p` and
  `ThenRow p`) and `ReconAccepted p e`. W is the surviving placement of least `Placement.rank`.
- W is recorded as decided or provisional (§3). It is decided when every placement ranked before
  it is refuted by a refutation that passes §11, and provisional when one is only "not derived".
- A decided W is recorded with its consequence (§4.4):
  - `cbpv`: OQ-8 option 2, and D1 meets "two algebras with interactions only at cuts", with the
    own-lend cost at `U` recorded and the outcome read against both wordings of (d) (§4.2);
  - `binder` or `binder0`: option 3, with a resume obligation in the binder clauses.

  A provisional W is recorded as such, for example "cbpv: not derived, no obstruction verified;
  W provisionally = binder", with the step each placement before it stopped at. No consequence is
  drawn from it for OQ-8, for "interactions only at cuts", or for D1's ranking against D2a and D3.
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
- **(d)** Two quantifiers, a relation family in all but name. Stop and report. Synthesis §11 words
  it: "Statement 0 holds only with different future-world quantifiers at `U` and at `⊸`, which no
  single definition of W reconciles". The design reads it as: statement 0 holds only after a clause
  is changed to reach a stack other than its own by something other than `FutQ`, followed at the
  own-lend clause by `OwnPush` at the type it reads (§4.2). The design's reading admits `cbpv`'s
  type-directed own lend at `U` by definition, and the synthesis's wording does not decide it. So
  the outcome is reported against both. One report says whether some clause had to be changed (the
  design's reading). The other says whether `OwnPush` at `U` was needed and how `MonoOwnG` came
  out: proved at the current `FutStep`, proved only after the push became a future, or not
  derived (the synthesis's wording).

A statement neither proved nor refuted is reported as "not derived, no obstruction verified",
with the step it stopped at.

### 12.3 The stop rule

Statement 0 has two bundles, and the rule treats them differently.
- **The shared lemmas** (`Statement0Shared`) are about definitions every placement shares: W's
  order, the bridge to GhostEnd's piece, and the nil slice the programs read. They are proved
  first. A shared lemma that is refuted or not derived is a finding about our definitions, not a
  comparison of placements. **The probe stops and reports it**, with the step it stopped at and
  the definition it reads.
- **The per-placement facts** (`Statement0 p`) feed the comparison. Statement 0 works at `p` when
  the shared lemmas and `Statement0 p` are proved. Statement 1 is attempted only at placements
  where statement 0 works, and statements 2–6 only where statements 0 and 1 work. **If
  `Statement0 p` is proved at no placement, the probe stops after statement 0 and reports**, for
  each placement:
  - the facts proved;
  - the facts refuted, each with its arising check;
  - the facts not derived, each with the step it stopped at.
- **One shared reason.** A per-placement fact can fail at every placement for one reason that
  does not depend on the placement. `MonoOwnG` at a thunk slot is the expected case: the own push
  is no future at any of them (§4.3). The report then states it as a finding about our definitions,
  with the changes §13 step 2 names. It does not state it as a comparison of the placements.

(b) and (d) stop the probe wherever they occur.

---

## 13. Order of work, and the build

Unknowns first:

1. **Step 0** (§2.6).
2. **Statement 0.**
   - **The shared lemmas first**: `ExtPreW` (bookkeeping: the closure and `Ext.trans`),
     `FutReLend`, `FutPart`, `FutAvoidsTrans`, `OpenSFBridge`, `NilSoundRet`. Apply the stop
     rule's shared clause (§12.3).
   - **`MonoOwnG`, at each placement, before `ThunkVRow`, `BangThunkVRow` or `AllIRow` is used to
     tell placements apart.** It is attempted at the current `FutStep`. If it is not derived at a
     thunk slot, it is attempted next with `FutStep` admitting an inserted entry whose variable is
     not `NsVar` when the clause's type avoids it, free and bound (§2.2, *Names*). This is done in
     a scratch file. Then:
     - if it is provable at the current `FutStep`, nothing changes;
     - if it is provable only with that change, `FutStep` is changed in `World.lean` before any
       other proof, and §2.2's *Names*, §4.2 and §14 are rewritten to say so, its cost included
       (the renaming lemma inside the rows that meet a collision);
     - if it is provable with neither, it is recorded "not derived, no obstruction verified" with
       the step it stopped at. The report names both candidate changes (§4.3), as a finding about
       our definitions under the stop rule's shared-reason clause. The second candidate, the own
       lend named by a future's name, is a change of representation, and it is not made without
       that report.
   - **The discriminating facts**: `MonoHide binder0` and `MonoC binder0`; at `cbpv`, `ThunkVRow`
     at the own lend at a future; at `binder`, `MonoG` at a future, the transport `LamRow` and
     `AllIRow` call.
   - **Then** `MonoV`/`MonoG` at the other placements, `MonoHideFromMonoV`, `CallbackExt*`,
     `ForceRow`, `ThawRelend` and the thunk rows.

   Apply the stop rule. `NilAgrees`, `NilAgreesU`, `NilSoundV` and `NilSoundC` (OQ-58) are
   attempted after the bundles, at the placements where they hold.
3. **Statement 1**: `ArisesNonVacuous` first; then `TabUpd` (6.50 at both ends of the stack) and
   `TabRuns`, `TabStart`, `TabHide`, `TabRelend`, `TabFut`, `TabResume`; `ArisesSound` beside them;
   the first check of `TabOfTWPointwise` (§5.2); then `LamRow` (at `binder`, at a future),
   `AllIRow` (at `cbpv` the third-kind stack, at `binder0` and `binder` the own push through
   `MonoOwnG`), `BelowRow`, `BelowExcluded`.
4. **Statement 2**:
   - `reconB′`'s term committed to `Programs.lean` before any proof here (§9.2);
   - the 6.64 cancel path, `RebFrameR` and `RebChooserNonVacuous` first, the items no proof has
     touched;
   - then #275's conversion and §6.2's items (i)–(iii), the fold, at `OpenS` or, restated after
     the GhostEnd proof each mirrors, at `OpenSF`;
   - then `SpanW2Row`, `SpanW1Row`, `SpanLoadRow`.
5. **Statement 3**, then **statement 4**.
6. **Statement 5**: compose `genSelf`; compose `reconB′` at the term committed in step 4.
7. **Statement 6**, then **statement 7**.

**The build.** Iterate with `lake build ProbeD1.<Module>`. `lake build ProbeD1` at milestones.
Every theorem's `#print axioms` is within `[propext, Classical.choice, Quot.sound]`; an
`Axioms.lean` prints them once theorems exist. No `sorry` or `axiom` lands in a finished file; an
unproved step in progress is an enumerated `sorry` in a scratch file, never committed. No `Core/`
edit. Work on `targets`; never push.

---

## 14. Report lists

**Printed hypotheses the routes must spend** (written before the build; §15.5 says which were
spent):
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
- GhostEnd's stacked folds at `OpenSF` (§6.2): not printed lemmas, but proved GhostEnd results
  that `cbpv` and `binder` restate. Each restatement follows the proof it mirrors, and
  `OpenSFBridge` is the way back to the proved `OpenS` results.

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
  list (§6.2).
- `RebFrameR`'s `RCarried` (the payload input carried along `Ext`). It comes from `wpG_frame`'s
  `hR`, which the step carrying the kept copy to the run's end reads (§6.2). Its scope: at the
  program's relation, `R = vC false r.T · r.δ`, it holds by `vC_local`.
- `RebFrameR`'s `TabKeepsRec` (the record kept on the lists the table resumes at). It comes from
  the next unfolding's `wpG_reborrow`, whose chooser is supplied only at lists holding the record
  (§6.2). Its scope: `opTable` at a table whose answers hold nothing, by `contShare`, `Keeps` and
  `Rel`. The three added hypotheses, the chooser and an inhabited view hold together at one record
  whose payload is not data, at a resuming table: `RebChooserNonVacuous`.
- `StackJ`'s second and third kinds, which widen GhostEnd's `LStack.WF` to the entries the
  placements' quantifiers insert. At `σ = []` they are vacuous. The third kind asks the own lend's
  variable to be neither free nor bound in the context's live types (`CtxFresh`): a slot's `∀` that
  bound it would read its body at the entry's lifetime.
- `ThunkVRow`'s and `BangThunkVRow`'s `OwnHyg`: when the thunk's type is `∀'x ⊏ c. C'`, its binder
  is new to `Δ` and neither free nor bound in `Γ`'s live types. It comes from the `U` clause's own
  push at `cbpv`, where the row calls its premise at the pushed stack (`StackJ`'s third kind) and
  carries its context there (`MonoOwnG`).
- `AllIRow`'s binder bound in no live slot of `Γ`, beside Core's "free in no live slot". It comes
  from the `∀` clause's own push at `binder0` and `binder`, carried by `MonoOwnG`. Both hygiene
  hypotheses are gaps of `BindersLow`'s kind, with the same discharge: a renaming lemma, which
  α-renames the binder away from the context. At the programs, binders are distinct from the
  context's.
- `MonoOwnG`'s `CtxFresh`, the hygiene the two above supply.
- `MonoOwnG`'s `δ.find? e.x = none`, added in the build. It is `FutOK.vars_sub` at the own push,
  which `OwnOK` does not ask and §4.3's route reads ("`vars_sub` follows from `SubDom` and the
  binder new to `Δ`"). Every use meets it: `OwnHyg` and `AllIRow` put the binder new to `Δ`, and
  `SubDom` keeps `δ` on `Δ`'s variables.
- `CallbackExtMut` and `CallbackExtImm` at `cbpv`: proved with `c.mentions y = false` beside the
  statement's hypotheses (`callbackExtMut_cbpv_of`, `callbackExtImm_cbpv_of`), not added to the
  statement. At `cbpv` the own lend is the `U` clause's, and the plain `∀` at the pushed stack
  reads the bound at the pushed stack's substitution, where `y` is the entry's. The borrow
  constants' callback type `∀'x ⊏ ⊓Δ` with `x` new to `Δ` meets it.

---

## 15. The build's outcome

The build ran §13 through step 2 and stopped there by the stop rule (§12.3): `Statement0 p` is
proved at no placement. Statements 1–7, `Survives` and OQ-58's four facts were not attempted.

### 15.1 Step 0 and the shared lemmas

- **Step 0** (§2.6): `Below.lean`, `Arising.lean` and `Extend.lean` brought verbatim from
  `borrow-callbacks` 5cfe062, in a commit of their own.
- **`Statement0Shared` is proved** (`statement0Shared`, `Shared.lean`), so the shared clause of the
  stop rule does not fire:
  - `ExtPreW` (`extPreW`): `Ext.refl`, `Ext.trans`, the closure;
  - `FutReLend` (`futReLend`): a re-lend of one step's lifetimes splits into the re-lend of the
    inner part, the inserted lifetimes and the outer part; the inserted ones stay below the
    resource (`ResU.InStratum.mono`); by induction from the future's end, the stack kept in shape
    (`FutStep.stackOK`);
  - `FutPart` (`futPart`): a step reads its resource only at `FutOK.below`
    (`ResU.CompS.inStratum_left`);
  - `FutAvoidsTrans` (`futAvoidsTrans`);
  - `OpenSFBridge` (`openSFBridge`): `OpenSF true` at `X σ' := OpenS δ σ' Tab (Q σ')`, each futures
    quantifier at the reflexive future (`relendableNF_refl`), closed by `openS_fold`;
  - `NilSoundRet` (`nilSoundRet`): a data type is read componentwise to Core's leaves at
    `extS δ [] [] = δ` (`vRL_data`); the piece at `[]` reaches GhostEnd's `OpenS` through the
    bridge and Core's `ewpTS` through `bodyS_nil_iff`.

### 15.2 Statement 0 per placement

| fact | `cbpv` | `binder` | `binder0` |
|---|---|---|---|
| `MonoOwnG` (with `δ.find? e.x = none` added, §14) | proved, `monoOwnG_cbpv` | proved, `monoOwnG_binder` | not derived (a thunk slot); proved at a context reaching no `U`, `monoOwnG_uFree` |
| `MonoV` | proved, `monoV_cbpv` | proved, `monoV_binder` | not derived |
| `MonoG` | proved, `monoG_cbpv` | proved, `monoG_binder` | not derived |
| `CallbackExtMut` | proved under `c.mentions y = false`, `callbackExtMut_cbpv_of`; not derived otherwise | proved, `callbackExtMut_binder` | proved, `callbackExtMut_binder0` |
| `CallbackExtImm` | as `CallbackExtMut`, `callbackExtImm_cbpv_of` | proved, `callbackExtImm_binder` | proved, `callbackExtImm_binder0` |
| `ForceRow` | proved, `forceRow` | proved | proved |
| `ThawRelend` | proved, `thawRelend` | proved | proved |
| `ThunkFRow` | not derived | not derived | not derived; proved given `CtxRelendableAt binder0` at the row's context, at `SemSR` (`thunkFRow_binder0_at`); that hypothesis discharged at `Γ = []` and at a `U` slot (§15.6) |
| `ThunkVRow` | not derived | not derived | not derived; the same (`thunkVRow_binder0_at`) |
| `BangThunkFRow` | not derived | not derived | not derived; the same (`bangThunkFRow_binder0_at`) |
| `BangThunkVRow` | not derived | not derived | not derived; the same (`bangThunkVRow_binder0_at`) |

Beside the bundles: `MonoHideFromMonoV` is proved at every placement (`monoHideFromMonoV`: hiding is
the one-step future that inserts nothing), so `MonoHide` holds at `cbpv` and `binder`
(`monoHide_cbpv`, `monoHide_binder`). `MonoC` was not attempted. No fact was refuted.

**How each proof goes.**
- `MonoV` at `cbpv` and `binder` (`Mono.lean`). At `U` by construction, as §4.3 read it: the new
  clause's futures, taken after a re-lend, are futures of the old stack after a re-lend
  (`futReLend`), at the share (`futPart`), avoiding the type (`futAvoidsTrans`); the witnesses are
  the old ones, the views at the future with the inserted entries' flags off (`futDs`, `vwS_fut`)
  and the share above the future's outermost lend (`stratS_fut`). A leaf reads `vC` at
  `extS δ σ' αs'`, which agrees with `extS δ σ αs` at the type's free variables
  (`extS_find_fut`), along `Ext` (`vC_local`). `MonoG` follows slot by slot.
- `MonoOwnG` (`Own.lean`): the own push is the one-step future at depth `0` (`ownPush_futStep`),
  and `MonoOwnG` is `MonoG`'s instance there (`monoOwnG_of_monoG`). This needs `FutStep` as changed
  (§2.2, *The change §13 step 2 made*) and the added `δ.find? e.x = none` (§14).
- `ForceRow`, `ThawRelend` (`Rows0.lean`): the `U` clause at the identity (`force_U`); the thaw by
  the original witnesses, every later re-lend and future one of the original's (GhostEnd's
  `relendableS_thunkA` at W). The context is a solo slot up to persistent ones (`gSepRL_soloP`).
- `CallbackExt*` at `binder0` and `binder`: the `U` clause at the identity, then the `∀` clause's
  own lend at the stack itself, then `⊸` at the argument (GhostEnd's `callback_ext` at W). At
  `cbpv` the own lend is the `U` clause's, and the plain `∀` at the pushed stack reads the bound at
  the pushed stack's substitution; the two readings of the bound agree when it does not mention
  the binder.

**`MonoOwnG` before the change.** With `FutStep` asking `NsFresh τ`, the attempt (§13 step 2's first
branch) went as §4.3 expected. At a thunk slot `g : U C₁`, `g`'s `U` clause at the pushed stack owes
`g`'s body at every future of the pushed stack, the pushed stack itself included. None of those
stacks is a future of the old one, since the pushed variable is a program binder, and `g`'s clause
gives the body only at the old stack's futures and, at `cbpv`, at `C₁`'s own pushes, which `C₁`'s
binder names. The transport would need `MonoC` along a non-future insertion. At `⊸` that reads the
argument back at the old stack, under the old stack's guard, which a resource holding a cell at the
pushed place does not meet. So it was not derived at any placement, for that one reason, and no
obstruction was verified. What held then (`7d20615`): `MonoOwnG` at a push named by an `NsVar` new
to `δ` (`MonoOwnGNs`, `MonoG`'s instance), at `cbpv` and `binder`, and at every placement at a
context reaching no `U`. With the change, the push is a future and the first case covers it, which
is §13 step 2's second branch. The second candidate (the own lend named by a future's name, its
binder read through `δ`) was not needed and not made.

**What is not derived, and where each stopped.**
- `MonoV binder0`, `MonoG binder0`: at `U` the clause ranges over the stack itself, so the forced
  computation must be carried along the future, `MonoC binder0`. At `⊸` the old clause gives its
  result only under the old stack's guard, and a resource holding an inserted entry's view at the
  future does not meet `TabAtS` at the old stack; the argument is read contravariantly (§4.3).
  `MonoOwnG binder0` at a thunk slot stops at the same step. `monoV_fut`'s other cases do not read
  the placement; only its `U` case does.
- `CallbackExtMut cbpv` and `CallbackExtImm cbpv` at a bound that mentions the binder: the plain
  `∀` at the pushed stack reads the binder at the entry's lifetime, and its body at another
  instance differs from the conclusion's only where W reads `δ` directly (`rowTab`, `vwE`). Not
  derived.
- The four `U` introductions: §15.3.

### 15.3 The `U` introductions: the needs every placement shares

`ThunkFRow`, `ThunkVRow`, `BangThunkFRow` and `BangThunkVRow` are not derived at any placement. Each
conclusion is the `U` clause of a closure over the context, so it owes the body at every re-lend of
the stack, and at `cbpv` and `binder` at every future of the re-lend. GhostEnd proves the clause's
half at its own relation (`thunkF_RLa`, `thunkE_RLa`) from two hypotheses. At W each is a fact
about the judgement, and neither is derived (`Thunk.lean`):

- **The context's re-lendability** (`CtxRelendable` at every context, `CtxRelendableAt` at the
  row's context and `SemS`'s index): the context, at a resource with the table, splits into the
  views it holds and a part above the outermost lend that, handed the views at any re-lend, is the
  context there. A `U` slot meets it (`thawRelend`, `ctxRelendableAt_thunk`). A leaf whose cell sits
  at a stack place but is not that entry's view does not: both forms are refuted at such a leaf
  (§15.6).
- **The body at every re-lend.** It comes from the premise's `SemS` at the re-lent stack, which
  asks `Δ.Models` there. A re-lend need not keep it at a configuration `SemS` admits
  (`models_reLend_fails`, Lean): a variable of `Δ` off the stack, bounded by a stack variable,
  keeps `δ`'s lifetime while the stack's is re-lent below it. So the premise does not supply the
  body at every re-lend the clause owes. Such a `Δ` is a `∀'z ⊏ x` opened inside the callback of a
  lend of `x`, and typing reaches it at an index `binder0`'s own clauses read (§15.6). No row is
  refuted.
- **The table** at the re-lend: statement 1's `TabRelend`, proved here (`tabRelend`: the share lies
  above every lend, the views above the re-lent innermost lend's predecessor and at the stack's
  places). At a future, `TabFut`, and at `cbpv`'s own push, `TabStart`'s argument at an empty view:
  not attempted.
- **At `binder0` the first two are all.** Given `CtxRelendableAt binder0` at the row's context,
  each of the four rows holds at the configurations whose re-lends keep `Δ`'s models
  (`thunkFRow_binder0_at`, `thunkVRow_binder0_at`, `bangThunkFRow_binder0_at`,
  `bangThunkVRow_binder0_at`, at `SemSR`: `SemS` with `ReLendModels` on the index). At `σ = []`
  `ReLendModels` is vacuous, the only re-lend of `[]` being `[]`. So at `binder0` the context's thaw
  and the models at a re-lend suffice for the `U` introductions; that they are needed is not shown.
  The rows first took `CtxRelendable binder0` at every context, which is false (§15.6), so those
  first results were vacuous; the per-row forms replace them.
- **At `cbpv` and `binder`, the context at a future of the re-lend.** `MonoG` asks the future at the
  context's resource, which holds the inner entries' re-lent views, and a step inserting at depth
  `k > 0` puts its lifetimes above them, so `FutOK.below` fails at that resource. The leaves do not
  read it and a `U` slot reads it only at its share, so a `MonoG` asking the future at the part
  above the outermost lend would serve; it is not stated.
- **The names the futures give.** With `FutStep` as changed, a future may insert a variable that is
  not `NsVar`, which `StackJ`'s second kind does not admit, so the premise is not available at
  that future either (§2.2, *The change §13 step 2 made*).

The first two are needs at every placement for reasons that do not depend on it: they are about
`SemS`'s hypotheses (the models, the table) and about the context's thaw. By the stop rule's
shared-reason clause (§12.3) they are a finding about our definitions, not a comparison of the
placements. The future and the names are needs of `cbpv` and `binder` only.

### 15.4 What statement 0 decides

- **The stop rule.** `Statement0 p` is proved at no placement, so the probe stops after statement 0.
  Statements 1–7 are not attempted, and neither is `Survives`. OQ-58's facts (`NilSoundV`,
  `NilSoundC`, `NilAgreesU`, `NilAgrees`) are attempted after the bundles at the placements where
  they hold, so they are not attempted.
- **OQ-8 is not decided.** No placement survives statement 0, and nothing is refuted, so W is
  neither decided nor provisional (§3). Nothing follows for "interactions only at cuts" or for
  D1's ranking against D2a and D3 (§4.4).
- **What separates the placements, and what does not.** `cbpv` and `binder` carry monotonicity at
  `U` by construction, the own lend's transport, the thaw and `[force]`; `binder0` stops at its
  monotonicity, as §4.3 expected. All three stop at the `U` introductions, for one reason.
- **"Whether `U` and `⊸` take the same quantifier."** Not settled: the `U` introductions, where the
  quantifier's cost was to show (§4.2), are not derived at any placement.
- **Failure (d).** In the design's reading (§12.2) no clause was changed to reach another stack by
  any means but `FutQ` and `OwnPush`. The change to `FutStep` changed which stacks `FutQ` reaches,
  not how a clause reaches them. In the synthesis's wording: `OwnPush` at `U` is what
  `callbackExtMut_cbpv_of` reads at `cbpv`, and `MonoOwnG` was not derived at the earlier `FutStep`
  and is proved once the push is a future (§15.2).
- **Failure (b).** Not met: no guard beside `TW` and no relation family beside W was introduced.

### 15.5 Report lists (CLAUDE.md §5)

- **Printed hypotheses spent**: 6.112's `И`, at `FutOK.below` (`futPart`, `stratS_fut`,
  `FutStep.reLend`) and `OwnOK.below` (`ownPush_futStep`). **Unspent**, since no row that reads
  them was reached: 6.65's `P̂ ⊧ [β] P̂`; 6.64's `AdmWf` and `hQ`; 6.66's premises; 6.150's H11 and
  H16; 6.149; 6.48 and 6.49 through `Upd`; 6.50 (`TabUpd`); 6.62.
- **Uniqueness and functionality results used**: `ResU.CompS.functional` (`gSepRL_soloP`, through
  GhostEnd's `relendableS_nil`-style steps). Not used: `ResU.Flat.functional`, `CellU.immOf_inj`,
  `dropC_disj`, the machine's determinism.
- **Printed lemmas in the run-up that are untranscribed**: [TR] 6.150 at a resuming table
  (`RebFrameR` stated, not proved; statement 2, not reached); the stacked folds at `ResumeAff`
  tables (§6.2's new items). The 6.64 cancel path is ours, not a printed lemma, and is not built.
- **Lemmas re-proved because the originals are private**: `substAll_forceE'` (Core's
  `substAll_forceE` is `private` in `Core/Compat.lean`), from GhostEnd's public `substAll_var_l`.

### 15.6 The two needs, settled at `binder0` (`Relendability.lean`)

**Q1: the context's thaw.**
- `not_ctxRelendable_binder0`: `CtxRelendable binder0` is false. The configuration `k` is one `mut`
  entry lending the place `0` at `'0`, payload type `Unk`, and the context `r : Mut '0 1, _ : 1`
  (dead) holding `0 ↦ mut(α, (), ∅, 𝒱⟦1⟧)` at the entry's lifetime `α`. The table admits the cell;
  no split of `RelendableS` places it, whatever predicate is re-lent (`k_not_relendableS`): it is
  not the entry's view, and it is not strictly above the outermost lend.
- `not_ctxRelendableAt_k`, `k_index`: the per-row form fails at `kΓ` too, and `k` meets every index
  hypothesis `SemS` has at `Δ = '0 ⊏ ⊤`. So restricting to the row's context and `SemS`'s index
  does not exclude `k`.
- `k_world_TW`, `k_world_tagged`: `k`'s world is a `TW` world (`alloc`, then `mutFold`), tagged at
  the empty list.
- `k_reached`: `Λ'0. λr. thunk (return r)` is derived closed at
  `∀'0 ⊏ ⊤. Mut '0 1 ⊸ F (U (F (Mut '0 1)))`. Read at `[]`, `binder0`'s `∀` clause owes the body at
  every own lend `OwnPush` admits, `k`'s entry among them, and at the pushed stack the `⊸` clause
  owes it at every related argument under the table, `r` at `k`'s cell among them.
  `k_thunk_not_vRL`: at `k`'s resource the `U` clause fails for every closure. Not derived: that
  the closed term's clause fails (the answer's resource is any `↭`-update of `k`'s), and so
  `ThunkFRow binder0` is not refuted.
- **The invariant that excludes `k`**: `PlaceViews`, every `mut` cell at a stack place the
  innermost lending entry's view. `not_placeViews_k`: `k` breaks it. `lendMut_placeView`: a 6.65 lend
  opens with it at its own place. `↭` keeps a `mut` cell's lifetime and predicate (`ResU.UpdMut`).
  Not proved: that it holds at every `Arises` configuration. It is not `TW`'s: `TW` does not see the
  stack. `TabAtS` asks only a stack place's stratum, and `OwnOK` ties the own lend's payload and
  place to nothing, so `SemS`'s index admits `k` and `binder0`'s clauses reach it.
- `ctxRelendableAt_nil` (every placement) and `ctxRelendableAt_thunk` (`binder0`): the per-row form
  holds at `Γ = []` and at a `U` slot. `thunkFRow_binder0_nil`, `thunkFRow_binder0_thunk`: the row
  with the hypothesis discharged there. Not proved: `CtxRelendableAt` at the contexts `PlaceViews`
  restricts to.

**Q2: `Δ`'s models at a re-lend.**
- `ReLendModels Δ δ σ αs`: every re-lend of the stack models `Δ`. It is what `SemSR` adds, the
  condition the rows' route needs.
- `BoundsStackFree Δ σ`: no bound of `Δ` mentions a stack variable.
  `reLendModels_of_boundsStackFree`: it gives `ReLendModels` (`extS_find_reLend`, `interp_congr`).
- `q2_reached`: `Λ'0. Λ'1 ⊏ '0. thunk (return ())` is derived closed, its `U` introduction at
  `mΔ = '0 ⊏ ⊤, '1 ⊏ '0`. At `binder0` the outer `∀` pushes the own lend of `'0` (`OwnPush`) and
  the inner `∀` instantiates `'1` at `2 ⊏ 1` (`LtLife`). There `mΔ` holds, `BoundsStackFree`
  fails, and the re-lend of `'0` at `2` breaks `'1 ⊏ '0`: `ReLendModels` fails. So typing reaches
  the configuration, at an index `binder0`'s own clauses read, where the premise's `SemS` is not
  available at a re-lend the `U` clause quantifies over. Not derived: that the clause fails there
  for some body.
- **The extra condition the re-lend needs.** The rows as proved need `ReLendModels`, which typing
  does not supply. Two ways to meet it, neither built, each a change to W's `U` clause and none to a
  printed BoLo definition: the re-lend also lowers every variable bounded by a stack variable (the
  re-lend substituting the bound), or the `U` clause quantifies only over the re-lends that keep the
  bounds. [unchecked] A resume re-lends at a fresh lifetime, below every lifetime in the world, so
  the second would exclude the resumes D1 needs whenever such a variable is in scope.

**What it means for D1.** No row is refuted, and no fallback is triggered. Both needs are now
located. The thaw fails at a configuration the guard admits and the relation's own clauses reach,
and the fact that keeps it out of a run (`PlaceViews`) is a lend-step invariant W's guard and own
lend do not carry. The models fail at a configuration typing reaches, so the ghost-end route needs
its re-lend to keep the bounds of variables bounded by the stack. Whether either change makes the
`U` introductions provable is not derived.

**Report lists for §15.6.** Printed hypotheses spent: none new; 6.48's `mut` clause of `↭`
(`ResU.UpdMut`) is cited for `PlaceViews`'s preservation, which is not proved, so it stays
unspent. Uniqueness and functionality results used: `ResU.CompS.functional`,
`ResU.CompS.get_left_of_ne_imm` and `get_right_of_ne_imm` (a `mut` cell comes from one side), and
the cell's stored predicate read back through `mutPred` (`mutPred_mutOf`). Not used:
`ResU.Flat.functional`, `CellU.immOf_inj`, the machine's determinism. Untranscribed in the run-up:
as §15.5; `PlaceViews` at every `Arises` configuration is ours and not built.

### 15.7 The freeze binder, built (`BINDER.md` §11)

The unit after statement 0 (`BINDER.md`) reads §15.6's two needs through the binder: a place the
stack lends is bound, and a borrow cell there is the binder's view (PlaceViews); a resume
instantiates every internal lifetime, preserving their order, and moves the records the frozen
computation made. Its build is `Binder{Inst,PV,PVRun,Refute,J,Rows,Arise,Risk}.lean`. The full
outcome, with the report lists, is `BINDER.md` §11. In brief:

**Item 1, PlaceViews.**
- The guard's local facts are proved at a part, a lend's start and end, a handler, the resume and an
  instantiation (`pvlParts`, `pvlStart`, `pvlEnd`, `pvlHide`, `pvlResume`, `guardInst`).
- `↭` and a run keep the guard at a stack whose places are distinct (`pvlUpdN`, `pvlRunsN`), by
  [TR] 6.48's case analysis with its ancestor transfer. Every `ArisesI` stack has distinct places
  (`placesNodupArises`).
- Not derived: `PVLUpd` and `PVLRuns` at repeated places. Not attempted: `PVLFut`, which `binder0`
  does not read.
- The arising check of `k` is proved. PlaceViews holds at the world of every `ArisesI`
  configuration (`pvArises`), so `k` is not in `ArisesI` (`kNotInArises`), and `k`'s slot fails W's
  `Mut` leaf (`kSlotNotW`). `k` is not shown not to arise: `ArisesI`'s direction is not established.

**Item 2, the lifetime binder.**
- The re-lend is an order-preserving instantiation at the stack's cut. It keeps every `Δ`'s models
  (`instModels`, `reLendModelsI_of`), which settles Q2 with no condition on `Δ`, and its bookkeeping,
  readings and records facts are proved.
- Refuted, each at a configuration not shown to arise, so each is a fact about our statement:
  - `ExtInst` (`not_extInst`): `Ext` keeps records without their tags;
  - `CohEInst` at an outermost lend at `⊤` (`not_cohEInst`);
  - the support conjunct of `MutPayloadInst` (`not_mutPayloadInst`), and with it `InstEquivLeaf`.
- `TyEqInst`, `CohEInst` and `ViewSlotInst` are proved at the types and indices the thaw reads
  (`tyEq_inst`, `cohE_inst`, `viewSlotInstCS`). `ViewTypeCoincidence` is proved.

**Item 3, `mut_not_natural`.**
- `Targets.NotVDenNaturalArises` is proved: Restrat's witness is a part of a tagged `TW` world.
  `mutFold` takes any predicate, so this is not arising in §11's sense.
- At the view slot the witness is re-established from the handed view (`mutWitnessThaws`), at
  hypotheses an exhibited configuration meets (`mutWitnessThaws_met`).
- At the retained part the mechanism appears as `not_mutPayloadInst`: a retained cell whose payload
  type reads an internal lifetime. It is not shown to arise, so it is evidence and not an
  obstruction.

**Item 4, the `U` introductions.**
- The design's targets at `vRLI` are refuted as stated (`not_statement0UThawFree`,
  `not_statement0UFull`), at a configuration not shown to arise.
- The build revised the draft relation (`vRLJ`, `BinderJ.lean`) in three places, each answering a
  refuted step: the `U` clause's extension keeps the retained records with their tags (`KeepsT`); a
  retained `Mut` or `Imm` leaf reads its payload type at external lifetimes (`RetainedPay`); the
  index's outermost lend is below `⊤` (`OuterBelowTop`).
- **Proved: `Statement0UThawFreeJ binder0`** (`statement0UThawFreeJ`). These are the four `U`
  introductions, the context's thaw at every `CtxThawFree` context, and `ThawInstJ`. No
  `ReLendModels` hypothesis remains.
- Not derived: the thaw at a `μ` or `fam` slot (`Statement0UFullJ`), guarantee gap R1. The
  revision's obligations at the other rows (`RetainedPay` at every row introducing a `Mut` or `Imm`
  value, `KeepsT` at the share, `OuterBelowTop` at the lends) are named and not proved.

**What it decides.**
- §15.3's two shared needs are met at `binder0` at `CtxThawFree` contexts, by changes to our
  definitions. The result is partial (R1), so no placement decision rests on it, and `binder0` still
  stops at its own `MonoV`, `MonoG` and `MonoOwnG`.
- OQ-8 is not decided. `cbpv` and `binder` owe `BINDER.md` §5.6's list, with the revision's three
  obligations added.
- No failure of type (a), (b) or (d) occurred: nothing was refuted at a configuration shown to
  arise, `vRLJ` replaces `vRLI` as the one draft relation, and no clause reaches another stack by a
  new means. The fallback is not triggered.

### 15.8 The instantiation's gap at `∀`, built (`GAP.md` §8)

The unit after the freeze binder (`GAP.md`) takes the step `BINDER.md` §11.2 left, `TyEqInst` at
every type, and the position-`∀` the task gave as the direction. Its build is
`Gap{Witness,Cover,Rows,Pos,Room}.lean`; the full outcome is `GAP.md` §8. In brief:

- **`TyEqInst` at every type: proved** (`tyEqInst`), by a threshold cover: `TyEq` compares lifetime
  terms by equality, which a chain decides threshold by threshold, so a lifetime in an
  instantiation's gap is covered by `⊤` or by a lifetime below the threshold. No relation changed.
- **The thaw and the four `U` rows at every payload type: proved at `binder0`**
  (`statement0UThawFreeKJ`). The `CoreStable` restriction on `Mut` and `Imm` payloads is gone; the
  only exclusion left is a slot with a `μ` or `fam` type outside a `Mut` or `Imm` payload (R1).
- **Core's `∀` reads the room between lifetimes: proved** (`coreAllAdjacent`, `coreAllNotNatural`).
  Core's relation is not invariant under an embedding that opens a gap.
- **The position-`∀`.** Read over the cuts below the stack's cut and realised by instantiations
  (`AllPosJ`), it is realisable, transported along instantiations, and Core's clause at `σ = []`
  both ways; W's `U` clause already is it (`wU_allPosJ`), and at the adjacency configuration it
  excludes the closure Core's `U` clause admits (`adj_not_wU`). Read over every cut of the whole
  order by renaming (`CutAllC`), it agrees with Core one way only. `cRLJ`'s `∀` is unchanged.
- **Open**: R1; `ViewSlotInst` without `OuterBelowTop`; everything §15.7 lists as owed.
- **What it decides**: the thaw's only guarantee gap is R1. OQ-8 is not decided. No failure of type
  (a), (b) or (d) occurred, and the fallback is not triggered.

---

## Unresolved: the reviews' findings, answered and not reviewed again

The second review ended with one blocker and five major findings. The text and the statement files
were revised in answer to each (`9b89b32`), before the build, and the revision was not reviewed
again. Whether a revision answers its finding has not been checked by the reviewer. Each entry
gives the finding, where the current text answers it, and what stays open.

1. **Blocker: `NilSoundV` and `NilSoundC` in `Statement0` at every type** (`Statement0.lean:94`,
   `:187`; §4.3, §6.3, §12.3). Their expected failure is outcome (c), which the design classes as
   no stop, so a bundle holding them would stop the probe after statement 0 without telling the
   placements apart.
   - Answered: the nil slice in the bundles is `NilSoundRet`, `F_Σ A` at a data `A`, the slice
     §9.1 reads, in `Statement0Shared` (§4.1). `NilSoundV`, `NilSoundC`, `NilAgreesU` and
     `NilAgrees` are beside the bundles (§4.2, §6.3). `NilSoundRet` is proved (§15.1).
   - Open: the four OQ-58 facts are not attempted (§15.4).
2. **Major: no statement transports a context under the callback's own lend** (`World.lean:100`,
   `:168`; `Statement0.lean:63`; `Sem.lean:75`; §4.2, §13 step 2). The own push was never a future,
   three rows call their premise at the pushed stack, and `StackJ`'s third kind asked only
   `CtxAvoids`.
   - Answered: `MonoOwnG` is in `Statement0` and is the first per-placement fact (§4.1, §13).
     `StackJ`'s third kind asks `CtxFresh`. The build attempted it at the current `FutStep`, found
     it not derived at a thunk slot at every placement, and made the `FutStep` change the finding
     names (§2.2, §15.2); `MonoOwnG` is then proved at `cbpv` and `binder`, with
     `δ.find? e.x = none` added (§14).
   - Open: `MonoOwnG binder0`; the change's cost at the rows that call their premise at a future
     (§15.3).
3. **Major: W chosen as the least-rank placement among those proved, so a lower-rank placement only
   "not derived" could decide OQ-8** (§3, §4.4, §12.1; `Programs.lean:80`).
   - Answered: OQ-8 is decided against a placement only by a refutation that passes §11; otherwise
     W is provisional and nothing follows (§3, §4.4, §12.1).
   - Open: nothing; no placement survives (§15.4).
4. **Major: `Arises.run` and `ArisesV.ret` take any `γ` with arising values, unrelated to `Γ`**
   (`Arising.lean:119`, `:138`; §11 item 2).
   - Answered: `ArisesV` is indexed by type, `ret` at the judgement's answer type, and `run` and
     `ret` take `ArisesCtx c Γ γ`, each live slot's value arising at the start configuration at
     the slot's type and holding its own part of the local resource (§11). §11 no longer claims
     the under-approximation; it says the direction is not established and admits a refutation
     only with the closed program and its run exhibited.
   - Open: the two gaps §11 names (values share the start's configuration, not its path; lends,
     handlers and parts are taken anywhere). The term-tracked arising is not written.
5. **Major: `RebFrameR`'s route needs hypotheses the statement did not carry** (`Statement2.lean`
   `RebFrameR`/`rebF`; §6.2): `wpG_frame`'s `hR` for `R`, and the chooser at the resumption lists.
   - Answered: `RCarried` and `TabKeepsRec` are added, each from the step that reads it, and
     `RebChooserNonVacuous` shows them with the chooser and an inhabited view at one record whose
     payload is not data (§6.1, §6.2, §14).
   - Open: `RebFrameR` and `RebChooserNonVacuous` are not proved (statement 2, not reached).
6. **Major: `Arises`'s direction is not established, and `ArisesSound` was used in the other
   direction** (`Arising.lean`; `Statement1.lean` `ArisesSound`; §5.2, §11 items 2–3).
   - Answered: §11 labels the direction as not established; §5.2 rests the guard's claim on the
     per-transition facts (`TabUpd` … `TabResume`), not on `ArisesSound`, which is beside the
     bundle and used only to exclude a witness.
   - Open: the same-path requirement (finding 4's gaps); `ArisesSound` and the per-transition
     facts are not proved (statement 1, not reached).
7. **Major (content review of statement 0): the `binder0` `U` results may be vacuous.** They took
   `CtxRelendable .binder0` at every context, with no proof that it is satisfiable.
   - Answered: it is false (`not_ctxRelendable_binder0`, §15.6), so they were vacuous. The rows now
     take `CtxRelendableAt` at their own context (`thunkFRow_binder0_at` and its siblings), which
     holds at `Γ = []` and at a `U` slot (`ctxRelendableAt_nil`, `ctxRelendableAt_thunk`) and fails
     at `k` (`not_ctxRelendableAt_k`).
   - Open: `CtxRelendableAt` at the contexts `PlaceViews` restricts to; `PlaceViews` at every
     `Arises` configuration.
   - Since (`BINDER.md` §11): PlaceViews holds at the world of every configuration of the revised
     arising set `ArisesI` (`pvArises`), and the thaw holds at the revised relation `vRLJ` at every
     `CtxThawFree` context (`ctxRelendsThawFreeJ`). Open: the thaw at a `μ` or `fam` slot.
   - Since (`GAP.md` §8): the thaw holds at every `CtxThawFreeK` context, every payload type
     admitted (`ctxRelendsThawFreeKJ`). Open: the thaw at a `μ` or `fam` slot.
