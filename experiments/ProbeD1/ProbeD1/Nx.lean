import ProbeD1.R1AllI
import ProbeD1.Statement34

/-!
# ProbeD1 — the two-cell guard gap, the unroll row (`NEXT.md`): the statements

`NEXT.md` is the design. This file holds its definitions and `def … : Prop` statements for item 1a
(§1.3) and item 2 (§2.1); the proofs are in `NxGuard.lean` and `NxUnroll.lean`.

* **Item 1a: the two-cell guard gap.** Where a callback's clause reads its argument's guard
  (`CbReading`: an instantiation of the stack, then an instance below the bound or an own push),
  the pair `Ref 1 ⊗ Ref 1` lent by a 6.64 entry (`PairCfg`), [TR] 6.150's reborrow of its record's
  payload (`PairReb`), and the gate `WithloadUPairGapReal`: at one configuration that arises, with
  the program typed at `withloadU`'s type, the reborrow at every reading's lifetime fails the guard
  where the callback's `⊸` reads it (`PairGuardRejectsU`). `withload`'s thunked form carries the
  answer's instantiations too (`PairGuardRejectsF`, `WithloadPairGapInst`). The guard lemmas:
  `PairRebCells`, `PairCallbackGuardFails`, `PairCallbackGuardFailsLe`, `PairBoundBelow`,
  `PairNilOldGuardHolds`. The same at a slice of two elements (`SliceCfg`, `SliceFrames`,
  `SliceGuardRejectsU`, `SliceUGapReal`, `SliceCallbackGuardFails`).
* **Item 2: `VRLMUnroll`.** `vRLM`'s substitution lemma, `vCE_some`, `vCE_rename`, `vCE_subst` and
  `vC_inst` at W's clauses (`VRLMSome`, `VRLMRename`, `VRLMSubst`, `VRLMInst`), and the rows
  `RollRowM` and `UnrollRowM`.

Definitions and `def … : Prop` statements only; no proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty stopS OpenS)

/-! ### Item 1a: the two-cell guard gap -/

/-- `Ref 1 ⊗ Ref 1`: a payload with two `Ref` leaves side by side. -/
abbrev pairTy : VTy := .tensor (.ref .unit) (.ref .unit)

/-- `'0 ⊏ ⊤`: the lend's binder, the lifetime context the program is typed in. -/
abbrev pairΔ : LifeCtx := LifeCtx.empty.extend 0 .top

/-- `p : Imm '0 (Ref 1 ⊗ Ref 1)`: the view, the one live slot. -/
abbrev pairΓ : Ctx VTy := [⟨.imm (.var 0) pairTy, true⟩]

/-- `withloadU`'s callback at the pair, at the empty row (`cbUTy`, with `CTy.effOf [] R = F R`), as
the computation type its `U` clause forces: `∀'x ⊏ ⊓Δ. Imm̲ 'x (Ref 1 ⊗ Ref 1) ⊸ F (['x] B)`. The
`⊸` is directly under the `∀`. -/
abbrev pairCbUC (x : LifeVar) (B : VTy) : CTy :=
  .all x pairΔ.meetOfDom (.arr (pairTy.immReborrow (.var x)) (.ret (.box (.var x) B)))

/-- `withload`'s callback at the pair (`axWithloadTy`), as the computation type its `U` clause
forces: `∀'x ⊏ ⊓Δ. F (Imm̲ 'x (Ref 1 ⊗ Ref 1) ⊸ ['x] B)`. The `⊸` is inside the `U` value the
instance's run answers. -/
abbrev pairCbC (x : LifeVar) (B : VTy) : CTy :=
  .all x pairΔ.meetOfDom (.ret (.lolli (pairTy.immReborrow (.var x)) (.box (.var x) B)))

/-- `withload p cb` at `withloadU`'s typing: `cb` is bound, then `withload` is bound, forced
(`forceE` at an arrow type is the variable itself) and applied to `p` and `cb` (`app` takes
variables). Under the second binder, slot `0` is `withload`, `1` the callback and `2` the view. -/
abbrev pairProgU (cbE : Expr) : Expr :=
  .app (.val (.lam (.app (.val (.lam (.app (.app (.var 0) (.var 2)) (.var 1)))) withload))) cbE

/-- **The pair configuration**: links (a)–(c) of `NEXT.md` §1.2 that concern `c` alone. `c` is in
the revised arising set, with one 6.64 entry `e` named `'0` at `α` over `Ref 1 ⊗ Ref 1`. Its local
part holds `e`'s view `ψ`, which arises there. `ψ`'s witness is the open frame's record's, and it
owns the payload's two places, which are distinct and lent by no entry. The judgement's index holds
at `c` at the reading `δ`, with the view as the context. -/
def PairCfg (c : Cfg) (e : LEnt) (α : Life) (ψ : CellU BoCa.Loc Val) (ρf' : WRes) (r : FrameRec)
    (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy) : Prop :=
  ArisesI (ℍ := ℍ) c ∧ c.σ = [e] ∧ c.αs = [α] ∧ e.x = 0 ∧ e.T = pairTy ∧
    c.ρ.get e.l = some ψ ∧
    ArisesVI (ℍ := ℍ) (c.at ρf' (ResU.single e.l ψ)) (.loc e.l) (viewTy e) ∧
    r ∈ c.ps ∧ r ∈ rsOf c.ls ∧ r.le = e.l ∧ r.T = pairTy ∧ r.v = .pair (.loc l₁) (.loc l₂) ∧
    ψ.wit = r.R ∧ r.R.get l₁ = some (CellU.ownOf .unit) ∧ r.R.get l₂ = some (CellU.ownOf .unit) ∧
    l₁ ≠ l₂ ∧ l₁ ∉ c.σ.map LEnt.l ∧ l₂ ∉ c.σ.map LEnt.l ∧
    SemIdxM pairΔ pairΓ (.ret B) δ c.σ c.αs c.ls (ResU.single e.l ψ) ∧
    gRLM (ℍ := ℍ) .binder0 c.σ δ c.αs c.ls pairΓ [.loc e.l] (ResU.single e.l ψ)

/-- **[TR] 6.150's reborrow of a record's payload at `β`** (`TW.reb`'s resource premises): `reb_β`
of the witness, with the reborrowed type's shape holding of the record's value at the reading
extended at `'x ↦ β`. -/
def PairReb (r : FrameRec) (x : LifeVar) (β : Life) (cb : WRes) : Prop :=
  ResU.Reb β r.R cb ∧ vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v cb

/-- **A reading that a callback's clause offers at an index** (`vRLM .binder0`'s `U` clause, then
the `∀` clause of `C = ∀'x ⊏ b. _`). First an instantiation `ι` of the stack (`RelendJ`'s
`InstAt`). Then the reading extended at `'x ↦ β`, where `β` is either an instance below the bound
at the instantiated reading, with the instantiated stack (the first conjunct), or the lifetime of
an own push at the instantiated index, with the pushed stack (the own-lend conjunct). `σ'` and
`αs'` are where a `⊸` directly under the `∀` reads its guard, and `ρk` is the resource the forced
computation holds there. -/
def CbReading (δ : LSub) (C : CTy) (x : LifeVar) (b : Lifetime.Life) (σ : LStack)
    (αs : List Life) (ρk : WRes) (δ' : LSub) (σ' : LStack) (αs' : List Life) (β : Life) : Prop :=
  ∃ ι : Inst, InstAt αs ι ∧ δ' = (ι.sub δ).extend x β ∧
    ((σ' = σ ∧ αs' = ι.life αs ∧ LtLife (extS (ι.sub δ) σ (ι.life αs)) b β) ∨
      ∃ en : LEnt, OwnPushI (ι.sub δ) C ρk (σ, ι.life αs) en β ∧ σ' = en :: σ ∧
        αs' = β :: ι.life αs)

/-- **Link (d) at `withloadU`'s callback.** At every reading that the clause of `U (pairCbUC x B)`
offers at the index, beside every resource the callback holds there, the record's payload
reborrowed at the reading's own lifetime ([TR] 6.175's route) fails the table where the `⊸` reads
it. -/
def PairGuardRejectsU (c : Cfg) (δ : LSub) (r : FrameRec) (x : LifeVar) (B : VTy) : Prop :=
  ∀ (ρk : WRes) (δ' : LSub) (σ' : LStack) (αs' : List Life) (β : Life) (cb ρ : WRes),
    CbReading δ (pairCbUC x B) x pairΔ.meetOfDom c.σ c.αs ρk δ' σ' αs' β →
    PairReb r x β cb → ResU.CompS ρk cb ρ → ¬ TabAtS σ' αs' ρ

/-- **Link (d) at `withload`'s callback**: `PairGuardRejectsU` at `U (pairCbC x B)`, with the
answer's `U` clause read as well. At every reading, every instantiation `ι₂` of the reading's
stack, every list and every resource beside it, the reborrow at the reading's lifetime is either
not related at the reborrowed type at the instantiated reading, or fails the instantiated table. -/
def PairGuardRejectsF (c : Cfg) (δ : LSub) (r : FrameRec) (x : LifeVar) (B : VTy) : Prop :=
  ∀ (ρk : WRes) (δ' : LSub) (σ' : LStack) (αs' : List Life) (β : Life) (cb : WRes),
    CbReading δ (pairCbC x B) x pairΔ.meetOfDom c.σ c.αs ρk δ' σ' αs' β → PairReb r x β cb →
    ∀ (ι₂ : Inst) (ls : List SRec) (ρz ρ : WRes), InstAt αs' ι₂ →
      vRLM (ℍ := ℍ) .binder0 none σ' (ι₂.sub δ') (r.T.immReborrow (.var x)) (ι₂.life αs') ls
        r.v cb →
      ResU.CompS ρz cb ρ → ¬ TabAtS σ' (ι₂.life αs') ρ

/-- **The reborrow's two cells** ([TR] p. 5's `reb_β`, `own` clause): a reborrow at `β` of a
resource owning `l₁` and `l₂`, at which the reborrowed type's shape holds of the pair, holds an
`imm` cell exactly at `β` at both places (the shape needs both cells; `RebAt` fixes their kind
and lifetime). -/
def PairRebCells : Prop :=
  ∀ (R cb : WRes) (β : Life) (l₁ l₂ : BoCa.Loc) (x : LifeVar) (s : LSub),
    R.get l₁ = some (CellU.ownOf .unit) → R.get l₂ = some (CellU.ownOf .unit) →
    ResU.Reb β R cb →
    vShape (pairTy.immReborrow (.var x)) (s.extend x β) (.pair (.loc l₁) (.loc l₂)) cb →
    (∃ (χ₁ : WRes) (h₁ : χ₁.InStratum (LSet.singleton β).join),
        cb.get l₁ = some (CellU.immOf (LSet.singleton β) .unit χ₁ h₁)) ∧
    (∃ (χ₂ : WRes) (h₂ : χ₂.InStratum (LSet.singleton β).join),
        cb.get l₂ = some (CellU.immOf (LSet.singleton β) .unit χ₂ h₂))

/-- **The guard rejects the reborrowed argument at both kinds of stack** (`loadGuardFails2`,
`tabAtS_comp`). Beside any closure resource, two `imm` cells exactly at `β`, at distinct places the
stack does not lend, fail the table at the stack itself when `β` is below its innermost lend, and
at every own-lend push at `β`. At `αs = []` the first part is vacuous: the table at `[]` holds of
every resource. A lemma for `PairGuardRejectsU` at each reading: an instantiation keeps the stack
and moves its lifetimes, so the lemma applies at `(σ, ι.life αs)`. -/
def PairCallbackGuardFails : Prop :=
  ∀ (σ : LStack) (αs : List Life) (β : Life) (cb ρc ρ : WRes) (l₁ l₂ : BoCa.Loc),
    l₁ ≠ l₂ → l₁ ∉ σ.map LEnt.l → l₂ ∉ σ.map LEnt.l →
    (∃ (v₁ : Val) (χ₁ : WRes) (h₁ : χ₁.InStratum (LSet.singleton β).join),
        cb.get l₁ = some (CellU.immOf (LSet.singleton β) v₁ χ₁ h₁)) →
    (∃ (v₂ : Val) (χ₂ : WRes) (h₂ : χ₂.InStratum (LSet.singleton β).join),
        cb.get l₂ = some (CellU.immOf (LSet.singleton β) v₂ χ₂ h₂)) →
    ResU.CompS ρc cb ρ →
      (∀ h, αs.head? = some h → β < h → ¬ TabAtS σ αs ρ) ∧
      ∀ en : LEnt, StackOK (en :: σ) (β :: αs) → ¬ TabAtS (en :: σ) (β :: αs) ρ

/-- **The guard rejects any two borrow cells no longer-lived than the outermost lend.** At a stack
with a lend, one such cell at a place the stack does not lend fails the table's second conjunct. At
every own-lend push, two of them at distinct places do, since the push lends at most one. Cells of
any kind but `own`, at any lifetime at or below the outermost lend `o`. At an instantiated stack,
`o` is the instantiated outermost lend. -/
def PairCallbackGuardFailsLe : Prop :=
  ∀ (σ : LStack) (αs : List Life) (o : Life) (cb ρk ρ : WRes) (l₁ l₂ : BoCa.Loc)
    (ψ₁ ψ₂ : CellU BoCa.Loc Val),
    l₁ ≠ l₂ → l₁ ∉ σ.map LEnt.l → l₂ ∉ σ.map LEnt.l →
    cb.get l₁ = some ψ₁ → cb.get l₂ = some ψ₂ → ψ₁.kind ≠ Kind.own → ψ₂.kind ≠ Kind.own →
    ψ₁.at ≤ o → ψ₂.at ≤ o → ResU.CompS ρk cb ρ →
      (αs.getLast? = some o → ¬ TabAtS σ αs ρ) ∧
      ∀ (en : LEnt) (β : Life), StackOK (en :: σ) (β :: αs) → (β :: αs).getLast? = some o →
        ¬ TabAtS (en :: σ) (β :: αs) ρ

/-- **Optional: every argument the row can hand over has its cells there.** A resource related, at
Core's relation, at `Imm̲ 'x (Ref 1 ⊗ Ref 1)` at the pair, with `'x` read below the `imm` cell whose
witness owns the two places, that composes into a valid typed world holding that cell, has both of
its cells at lifetimes at or below that cell's. With `PairCallbackGuardFailsLe` it would extend
"real" beyond the `reb_β` route, at the identity instantiation of the callback's `U` clause. -/
def PairArgCellsLe : Prop :=
  ∀ (s : LSub) (x : LifeVar) (β' : Life) (ls : List SRec) (l₁ l₂ le : BoCa.Loc)
    (ψ : CellU BoCa.Loc Val) (cb W W' : WRes) (ps rs : List FrameRec),
    TW W ps rs → W.get le = some ψ → ψ.kind = Kind.imm → β' < ψ.at →
    ψ.wit.get l₁ = some (CellU.ownOf .unit) → ψ.wit.get l₂ = some (CellU.ownOf .unit) →
    vC true (pairTy.immReborrow (.var x)) ls (s.extend x β') (.pair (.loc l₁) (.loc l₂)) cb →
    ResU.CompS W cb W' → ResU.Valid W' →
    ∀ (l : BoCa.Loc) (φ : CellU BoCa.Loc Val), (l = l₁ ∨ l = l₂) → cb.get l = some φ →
      φ.at ≤ ψ.at

/-- **`withload`'s bound reads below the lend**: inside a callback whose binder `'0` the stack reads
at `α`, every instance of `withload`'s `∀'x ⊏ ⊓Δ` (`Δ = '0 ⊏ ⊤`) is below `α`. It holds at every
reading and every `α`, so at every instantiation of `c`'s index, where `α` is the instantiated
lend. -/
def PairBoundBelow : Prop :=
  ∀ (δ : LSub) (e : LEnt) (α β : Life), e.x = 0 →
    LtLife (extS δ [e] [α]) pairΔ.meetOfDom β → β < α

/-- **Typing reaches `withload` at its thunked typing inside a lend**: under the lend's binder
`'0`, the view `p : Imm '0 (Ref 1 ⊗ Ref 1)` applied to `withload` with a callback, in the probe's
rule set. A lemma. -/
def PairWithloadTyped : Prop :=
  ∃ (cb : Expr) (B : VTy),
    ProbeRules pairΔ pairΓ (.app (.app withload (.var 0)) cb) (.comp (.ret B))

/-- **Typing reaches `withload` at its unwinding typing inside a lend**: `pairProgU` with the
callback at `withloadU`'s type at the empty row (`CDerivesNU.withloadU`, `bind` twice, `force`,
`app` twice). A lemma. -/
def PairWithloadUTyped : Prop :=
  ∃ (cbE : Expr) (B : VTy), ProbeRules pairΔ pairΓ (pairProgU cbE) (.comp (.ret B))

/-- **The two-cell gap is real at `withload`'s unwinding typing, at one configuration** (the gate
for item 1b). At a pair configuration:
- the program is typed, with `withload` at `withloadU`'s type at the empty row;
- one own push at the index has a closed payload type, and [TR] 6.150's step (`TW.reb`) reborrows
  the record's payload at that push's lifetime into a tagged typed world;
- at every reading the callback's clause offers (`CbReading`: each instantiation of the stack,
  then each instance below the bound or each own push), the reborrow at that reading's lifetime
  fails the guard (`PairGuardRejectsU`). The `⊸` is directly under the `∀`, so these are all the
  stacks its guard reads.

Real for [TR] 6.175's route. The claim is about `vRLM` before (E1)–(E4) (`NEXT.md` §1.2). -/
def WithloadUPairGapReal : Prop :=
  ∃ (c : Cfg) (e : LEnt) (α : Life) (ψ : CellU BoCa.Loc Val) (ρf' : WRes) (r : FrameRec)
      (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy) (cbE : Expr) (x : LifeVar) (en : LEnt)
      (β : Life) (ρc cb fρ' : WRes),
    PairCfg (ℍ := ℍ) c e α ψ ρf' r l₁ l₂ δ B ∧
    ProbeRules pairΔ pairΓ (pairProgU cbE) (.comp (.ret B)) ∧
    OwnPushI δ (pairCbUC x B) ρc (c.σ, c.αs) en β ∧ (∀ y, ¬ VFree y en.T) ∧
    ¬ VFree x r.T ∧ PairReb r x β cb ∧ StratumLe c.fρ β ∧
    ResU.CompS c.fρ cb fρ' ∧ TW fρ' c.ps (rsOf c.ls) ∧ Tagged fρ' c.ps c.ls ∧
    PairGuardRejectsU c δ r x B

/-- **`withload`'s thunked form, with the answer's instantiations** (decided in 1a; not a gate):
at every pair configuration, `PairGuardRejectsF`. -/
def WithloadPairGapInst : Prop :=
  ∀ (c : Cfg) (e : LEnt) (α : Life) (ψ : CellU BoCa.Loc Val) (ρf' : WRes) (r : FrameRec)
    (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy) (x : LifeVar),
    PairCfg (ℍ := ℍ) c e α ψ ρf' r l₁ l₂ δ B → ¬ VFree x r.T →
    PairGuardRejectsF (ℍ := ℍ) c δ r x B

/-- **At the empty stack the guard holds of every resource** (GhostEnd's `TabAtS` at `[]`;
`PVLNil`). So before (E1) the callback's first conjunct at the empty stack reads its run on the
reborrowed argument, at every instance below the bound, and there is no gap there. A fact about
`vRLM` before (E1). -/
def PairNilOldGuardHolds : Prop :=
  ∀ (s : LSub) (ls : List SRec) (ρ : WRes), TabAtS [] [] ρ ∧ PlaceViewsL s [] [] ls ρ

/-! #### Slices -/

/-- `a : Array 1`: the owned array, the one live slot. -/
abbrev sliceΓ : Ctx VTy := [⟨.array .unit, true⟩]

/-- `slice_borrow_imm`'s unwinding callback at `Array 1`, at the empty row (`sliceBorrowIUTy`'s
`cbUTy`), as the computation type its `U` clause forces: `∀'x ⊏ ⊓Δ. [Imm 'x 1] ⊸ F (['x] B)`. -/
abbrev sliceCbUC (x : LifeVar) (B : VTy) : CTy :=
  .all x pairΔ.meetOfDom (.arr (.arrayImm (.var x) .unit) (.ret (.box (.var x) B)))

/-- `slice_borrow_imm`'s callback at `Array 1` (`sliceBorrowITy`), as the computation type its
`U` clause forces. -/
abbrev sliceCbC (x : LifeVar) (B : VTy) : CTy :=
  .all x pairΔ.meetOfDom (.ret (.lolli (.arrayImm (.var x) .unit) (.box (.var x) B)))

/-- The slice borrow at `sliceBorrowIU`'s typing, with the finaliser `d`: `cb` is bound, then
`withborUE d` is bound, forced and applied to `a` and `cb`. -/
abbrev sliceProgU (d cbE : Expr) : Expr :=
  .app (.val (.lam (.app (.val (.lam (.app (.app (.var 0) (.var 2)) (.var 1)))) (withborUE d))))
    cbE

/-- **The slice configuration.** `c` is in the revised arising set, with one 6.64 entry named `'0`
at `α`. An owned array of two elements at `ℓ` and `ℓ + 1`, places no entry lends, arises there at
`Array 1` with the resource `ρa`. The judgement's index holds at `c` at the reading `δ`, with the
array as the context. -/
def SliceCfg (c : Cfg) (e : LEnt) (α : Life) (ℓ : BoCa.Loc) (ρa ρf' : WRes) (δ : LSub)
    (B : VTy) : Prop :=
  ArisesI (ℍ := ℍ) c ∧ c.σ = [e] ∧ c.αs = [α] ∧ e.x = 0 ∧
    ArisesVI (ℍ := ℍ) (c.at ρf' ρa) (Val.arr ℓ 2) (.array .unit) ∧
    (∀ i < 2, ℓ + i ∉ c.σ.map LEnt.l) ∧
    SemIdxM pairΔ sliceΓ (.ret (.tensor (.array .unit) B)) δ c.σ c.αs c.ls ρa ∧
    gRLM (ℍ := ℍ) .binder0 c.σ δ c.αs c.ls sliceΓ [Val.arr ℓ 2] ρa

/-- **Two 6.64 frames at `β` over the array's elements** (`TW.immFrame` twice, from `c`'s world).
The elements' owned cells are the array's (`ρa`). They become the family `ρs`: two `imm` cells
exactly at `β`, with empty witnesses. The frames' records head `ps'`, and `ls'` is `c.ls` with
them in front, tagged at `β`. -/
def SliceFrames (c : Cfg) (ρa : WRes) (ℓ : BoCa.Loc) (u₀ u₁ : Val) (δ₀ : LSub) (β : Life)
    (ρs W' : WRes) (ps' : List FrameRec) (ls' : List SRec) : Prop :=
  ρa.get ℓ = some (CellU.ownOf u₀) ∧ ρa.get (ℓ + 1) = some (CellU.ownOf u₁) ∧
    ∃ (X Z : WRes) (h₀ h₁ : ResU.InStratum (LSet.singleton β).join PMap.empty),
      ResU.CompS (ResU.single ℓ (CellU.ownOf u₀)) (ResU.single (ℓ + 1) (CellU.ownOf u₁)) X ∧
      ResU.CompS X Z c.fρ ∧
      ResU.CompS (ResU.single ℓ (CellU.immOf (LSet.singleton β) u₀ PMap.empty h₀))
        (ResU.single (ℓ + 1) (CellU.immOf (LSet.singleton β) u₁ PMap.empty h₁)) ρs ∧
      ResU.CompS ρs Z W' ∧
      ps' = ⟨ℓ + 1, u₁, PMap.empty, .unit, δ₀⟩ :: ⟨ℓ, u₀, PMap.empty, .unit, δ₀⟩ :: c.ps ∧
      ls' = (⟨ℓ + 1, u₁, PMap.empty, .unit, δ₀⟩, β) :: (⟨ℓ, u₀, PMap.empty, .unit, δ₀⟩, β) ::
        c.ls ∧
      TW W' ps' (rsOf ls') ∧ Tagged W' ps' ls'

/-- **Link (d) at `slice_borrow_imm`'s unwinding callback.** At every reading that the clause of
`U (sliceCbUC x B)` offers at the index, a family of two `imm` cells exactly at the reading's
lifetime at the array's elements, beside every resource the callback holds there, fails the table
where the `⊸` reads it. -/
def SliceGuardRejectsU (c : Cfg) (δ : LSub) (ℓ : BoCa.Loc) (x : LifeVar) (B : VTy) : Prop :=
  ∀ (ρk : WRes) (δ' : LSub) (σ' : LStack) (αs' : List Life) (β : Life) (ρs ρ : WRes),
    CbReading δ (sliceCbUC x B) x pairΔ.meetOfDom c.σ c.αs ρk δ' σ' αs' β →
    (∀ i < 2, ∃ ψ, ρs.get (ℓ + i) = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.at = β) →
    ResU.CompS ρk ρs ρ → ¬ TabAtS σ' αs' ρ

/-- **The two-cell gap is real at a two-element slice at its unwinding typing, at one
configuration** (the gate for item 1b, with `WithloadUPairGapReal`). At a slice configuration:
- the program is typed, with `withborUE d` at `sliceBorrowIU`'s type at the empty row;
- one own push at the index has a closed payload type, and two 6.64 frames at that push's lifetime
  turn the array's two owned elements into a family of `imm` cells in a tagged typed world, whose
  frames and records are `c`'s with the two new ones in front (`SliceFrames`);
- at every reading the callback's clause offers, such a family at the reading's lifetime fails the
  guard (`SliceGuardRejectsU`). -/
def SliceUGapReal : Prop :=
  ∃ (c : Cfg) (e : LEnt) (α : Life) (ℓ : BoCa.Loc) (ρa ρf' : WRes) (δ : LSub) (B : VTy)
      (d cbE : Expr) (x : LifeVar) (en : LEnt) (β : Life) (ρc : WRes) (u₀ u₁ : Val)
      (δ₀ : LSub) (ρs W' : WRes) (ps' : List FrameRec) (ls' : List SRec),
    SliceCfg (ℍ := ℍ) c e α ℓ ρa ρf' δ B ∧
    ProbeRules pairΔ sliceΓ (sliceProgU d cbE) (.comp (.ret (.tensor (.array .unit) B))) ∧
    OwnPushI δ (sliceCbUC x B) ρc (c.σ, c.αs) en β ∧ (∀ y, ¬ VFree y en.T) ∧
    SliceFrames c ρa ℓ u₀ u₁ δ₀ β ρs W' ps' ls' ∧
    SliceGuardRejectsU c δ ℓ x B

/-- **The guard rejects the family at both kinds of stack** (`sliceGuardFails` with `tabAtS_comp`,
and the old stack's first conjunct). A lemma for `SliceGuardRejectsU` at each reading. -/
def SliceCallbackGuardFails : Prop :=
  ∀ (σ : LStack) (αs : List Life) (β : Life) (ρs ρc ρ : WRes) (ℓ : BoCa.Loc),
    (∀ i < 2, ℓ + i ∉ σ.map LEnt.l) →
    (∀ i < 2, ∃ ψ, ρs.get (ℓ + i) = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.at = β) →
    ResU.CompS ρc ρs ρ →
      (∀ h, αs.head? = some h → β < h → ¬ TabAtS σ αs ρ) ∧
      ∀ en : LEnt, StackOK (en :: σ) (β :: αs) → ¬ TabAtS (en :: σ) (β :: αs) ρ

/-- **Typing reaches a slice borrow inside a lend** (`withbor` at `sliceBorrowITy`). A lemma. -/
def SliceTyped : Prop :=
  ∃ (cb : Expr) (B : VTy),
    ProbeRules pairΔ sliceΓ (.app (.app withbor (.var 0)) cb)
      (.comp (.ret (.tensor (.array .unit) B)))

/-- **Typing reaches a slice borrow at its unwinding typing inside a lend** (`sliceBorrowIU` at the
empty row, `d` a closed finaliser at `Array 1 ⊸ 1`). A lemma. -/
def SliceUTyped : Prop :=
  ∃ (d cbE : Expr) (B : VTy),
    ProbeRules pairΔ sliceΓ (sliceProgU d cbE) (.comp (.ret (.tensor (.array .unit) B)))

/-! ### Item 2: `VRLMUnroll` -/

/-- The environment a substitution moves into, at one index (`substEnv`'s analog). -/
def substEnvW (p : Placement) (ρ : Nat → WEnt) (τ : Nat → VTy) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls : List SRec) : Nat → WEnt :=
  fun n => ⟨(τ n).subst (fun k => (ρ k).ty), vRLM (ℍ := ℍ) p (some ρ) σ δ (τ n) αs ls⟩

/-- **The environment of a closed type is the empty one read explicitly** (`vCE_some`'s analog). -/
def VRLMSome : Prop :=
  ∀ (p : Placement) (η : Option (Nat → WEnt)) (A : VTy) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls : List SRec),
    vRLM (ℍ := ℍ) p η σ δ A αs ls = vRLM (ℍ := ℍ) p (some (wEnv η)) σ δ A αs ls

/-- **Renaming moves into the environment** (`vCE_rename`'s analog). -/
def VRLMRename : Prop :=
  ∀ (p : Placement) (A : VTy) (ρ : Nat → WEnt) (r : Nat → Nat) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls : List SRec),
    vRLM (ℍ := ℍ) p (some ρ) σ δ (A.rename r) αs ls = vRLM (ℍ := ℍ) p (some (ρ ∘ r)) σ δ A αs ls

/-- **Substitution moves into the environment** (`vCE_subst`'s analog), at a substitution of no
thunk: `vRLM`'s `!` clause reads the persistence box at a syntactic `!U C`, so a thunk substituted
for a variable directly under a `!` would move into the box. The unrolling substitutes a `μ`
(`VRLMInst`). Stated for every substitution before the box. -/
def VRLMSubst : Prop :=
  ∀ (p : Placement) (A : VTy) (ρ : Nat → WEnt) (τ : Nat → VTy) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls : List SRec), (∀ n C, τ n ≠ .thunk C) →
    vRLM (ℍ := ℍ) p (some ρ) σ δ (A.subst τ) αs ls =
      vRLM (ℍ := ℍ) p (some (substEnvW p ρ τ σ δ αs ls)) σ δ A αs ls

/-- **The unrolling is the body at the `μ` itself** (`vC_inst`'s analog). -/
def VRLMInst : Prop :=
  ∀ (p : Placement) (A : VTy) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec),
    vRLM (ℍ := ℍ) p none σ δ (VTy.inst (.mu A) A) αs ls =
      vRLM (ℍ := ℍ) p (some (VTy.scons ⟨.mu A, vRLM p none σ δ (.mu A) αs ls⟩ (wEnv none)))
        σ δ A αs ls

/-- **`roll` at W.** Its premises are the `roll` rule's own (`Targets/Base/Typing.lean`,
`roll {Δ Γ e A} (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0)`); it adds none. -/
def RollRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy), A.NoMut 0 → (VTy.mu A).Cl 0 →
    SemSM (ℍ := ℍ) p Δ Γ e (.val (VTy.inst (.mu A) A)) → SemSM (ℍ := ℍ) p Δ Γ e (.val (.mu A))

/-- **`unroll` at W.** The `unroll` rule has no premise beside its derivation. -/
def UnrollRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy),
    SemSM (ℍ := ℍ) p Δ Γ e (.val (.mu A)) → SemSM (ℍ := ℍ) p Δ Γ e (.val (VTy.inst (.mu A) A))

/-! ### Step 3.0: the edits' statements (`NEXT.md` §3.1)

(E1)–(E4) are in `R1.lean` (`InScope`, `OwnPushM`, `StackJM`, `CallbackExt*M`'s `¬ VFree y T`), with
`VAllFree`, `CAllFree` and the restated `RelMAgreesJ`. -/

/-- `⟦b⟧` is the value of one of `b`'s variables, or `⊤`'s: a meet or a join of two values is one
of them. At an instance below a bound, `⊤` is excluded, so the instance is in scope. -/
def InScopeOfInterp : Prop :=
  ∀ (s : LSub) (b : Lifetime.Life) (m : ℕ),
    b.interp s = some m → InScope s (OrderDual.toDual m) ∨ m = Lifetime.SLife.top

/-- **After (E1), `GAP.md` §4's adjacency closure is a `vRLM` value at W's own `μ`**: the negation
of `MuAdjNotVRLM`, decided right after (E1) lands. -/
def MuAdjVRLME1 : Prop := ¬ MuAdjNotVRLM (ℍ := ℍ)

/-! #### Item 1a′: the empty stack after (E1) -/

/-- **The pair configuration at the empty stack.** `c` is in the revised arising set at the empty
stack. Its world holds an open 6.64 frame over `Ref 1 ⊗ Ref 1`, whose record `r` owns two distinct
places, and its local part holds the frame's `imm` cell `ψ`. The judgement's index holds at `c` at
the reading `δ`, with the cell's place as the context. -/
def PairNilCfg (c : Cfg) (ψ : CellU BoCa.Loc Val) (r : FrameRec) (l₁ l₂ : BoCa.Loc) (δ : LSub)
    (B : VTy) : Prop :=
  ArisesI (ℍ := ℍ) c ∧ c.σ = [] ∧ c.αs = [] ∧ c.ρ.get r.le = some ψ ∧
    r ∈ c.ps ∧ r ∈ rsOf c.ls ∧ r.T = pairTy ∧ r.v = .pair (.loc l₁) (.loc l₂) ∧ ψ.wit = r.R ∧
    r.R.get l₁ = some (CellU.ownOf .unit) ∧ r.R.get l₂ = some (CellU.ownOf .unit) ∧ l₁ ≠ l₂ ∧
    SemIdxM pairΔ pairΓ (.ret B) δ [] [] c.ls (ResU.single r.le ψ) ∧
    gRLM (ℍ := ℍ) .binder0 [] δ [] c.ls pairΓ [.loc r.le] (ResU.single r.le ψ)

/-- **After (E1), the gap at the empty stack, at `withloadU`'s callback.** At a pair configuration
at the empty stack, at a reading `δ` whose only value is `ψ`'s lifetime:
- the program is typed; one own push is at `OwnPushM`, and `TW.reb` reborrows the record's payload
  at its lifetime;
- no instance in scope meets the bound, so the first conjunct reads nothing, and the empty stack
  has no other instantiation (`cutOf [] = none`);
- at every own push, beside every resource the callback holds, the reborrow at the push's lifetime
  fails the table at the push.

So after (E1) the own push is the only route, and it fails. Before (E1) the first conjunct read the
callback here (`PairNilOldGuardHolds`). The view is not shown to arise by `ArisesVI`: no transition
of the set makes an `Imm` value arise at the empty stack, other than a run's answer. What is shown
is the configuration's world and the index. -/
def WithloadUPairGapNilE1 : Prop :=
  ∃ (c : Cfg) (ψ : CellU BoCa.Loc Val) (r : FrameRec) (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy)
      (cbE : Expr) (x : LifeVar) (en : LEnt) (β : Life) (ρc cb fρ' : WRes),
    PairNilCfg (ℍ := ℍ) c ψ r l₁ l₂ δ B ∧
    ProbeRules pairΔ pairΓ (pairProgU cbE) (.comp (.ret B)) ∧
    OwnPushM δ (pairCbUC x B) ρc ([], []) en β ∧ ¬ VFree x r.T ∧ PairReb r x β cb ∧
    StratumLe c.fρ β ∧ ResU.CompS c.fρ cb fρ' ∧ TW fρ' c.ps (rsOf c.ls) ∧
    Tagged fρ' c.ps c.ls ∧
    (∀ β', LtLife δ pairΔ.meetOfDom β' → ¬ InScope δ β') ∧
    ∀ (ρk : WRes) (en' : LEnt) (β' : Life) (cb' ρ : WRes),
      OwnPushM δ (pairCbUC x B) ρk ([], []) en' β' → PairReb r x β' cb' →
      ResU.CompS ρk cb' ρ → ¬ TabAtS [en'] [β'] ρ

/-- **After (E1), the empty stack at `withload`'s callback, with the answer's instantiations**
(decided; not a gate). At every pair configuration at the empty stack, at every own push at
`OwnPushM` and every instantiation of the push's stack by the answer's `U` clause, the reborrow at
the push's lifetime is either not related at the instantiated reading, or fails the instantiated
table. -/
def WithloadPairGapNilInstE1 : Prop :=
  ∀ (c : Cfg) (ψ : CellU BoCa.Loc Val) (r : FrameRec) (l₁ l₂ : BoCa.Loc) (δ : LSub) (B : VTy)
    (x : LifeVar), PairNilCfg (ℍ := ℍ) c ψ r l₁ l₂ δ B → ¬ VFree x r.T →
    ∀ (ρk : WRes) (en : LEnt) (β : Life) (cb : WRes),
      OwnPushM δ (pairCbC x B) ρk ([], []) en β → PairReb r x β cb →
      ∀ (ι₂ : Inst) (ls : List SRec) (ρz ρ : WRes), InstAt [β] ι₂ →
        vRLM (ℍ := ℍ) .binder0 none [en] (ι₂.sub (δ.extend x β)) (r.T.immReborrow (.var x))
          (ι₂.life [β]) ls r.v cb →
        ResU.CompS ρz cb ρ → ¬ TabAtS [en] (ι₂.life [β]) ρ

/-! #### The non-unwinding constants' callback rows -/

/-- **The 6.65 callback at `σ·y`, at the non-unwinding constants' shape**: `CallbackExtMutM` with
the callback at `∀'y ⊏ c. F (Mut 'y T ⊸ B')` (`axWithbor2Ty`, `axWithbor3Ty`, with
`B' = ['y] B`). The own push's run of `f ()` answers a `U` value; `vRLM`'s `U` clause reads it at
the pushed stack, and at the identity instantiation its `⊸` takes the view. With (E4)'s
`¬ VFree y T`. -/
def CallbackExtMutMF (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life) (T B' : VTy)
    (αs : List Life) (ls : List SRec) (f w : Val) (ρf : WRes) (e : LEnt) (α : Life) (ρv ρ : WRes),
    ¬ VFree y T → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    e.x = y → e.k = .mut → e.T = T → y ∉ CTy.binders (.ret (.lolli (.mut (.var y) T) B')) →
    OwnOKI δ σ αs e α ρf → LtLife (extS δ σ αs) c α → RecsOutside (α :: αs) ls → SubFresh δ α →
    TabAtS σ αs ρf → PlaceViewsL (extS δ σ αs) σ αs ls ρf →
    vRLM (ℍ := ℍ) p none σ δ (VTy.all y c (.lolli (.mut (.var y) T) B')) αs ls f ρf →
    vRLM (ℍ := ℍ) p none (e :: σ) (δ.extend y α) (.mut (.var y) T) (α :: αs) ls w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    PlaceViewsL (extS (δ.extend y α) (e :: σ) (α :: αs)) (e :: σ) (α :: αs) ls ρ →
    cRLM (ℍ := ℍ) p (e :: σ) (δ.extend y α) (.ret B') (α :: αs) ls
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ

/-- **The 6.64 callback at `σ·y`, at the non-unwinding constants' shape**: `CallbackExtImmM` with
the callback at `∀'y ⊏ c. F (Imm 'y T ⊸ B')` (`axWithbor1Ty`; `axWithloadTy` at a `Ref` payload,
where `Imm̲ 'y (Ref T) = Imm 'y T`). With (E4)'s `¬ VFree y T`. -/
def CallbackExtImmMF (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life) (T B' : VTy)
    (αs : List Life) (ls ls' : List SRec) (f w : Val) (ρf : WRes) (e : LEnt) (u : Val) (α : Life)
    (ρv ρ : WRes),
    ¬ VFree y T → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    e.x = y → e.k = .imm u → e.T = T → y ∉ CTy.binders (.ret (.lolli (.imm (.var y) T) B')) →
    OwnOKI δ σ αs e α ρf → LtLife (extS δ σ αs) c α → RecsOutside (α :: αs) ls' →
    SubFresh δ α → TabAtS σ αs ρf → PlaceViewsL (extS δ σ αs) σ αs ls ρf →
    Ext ls ls' ρf → KeepsT ls ls' ρf →
    vRLM (ℍ := ℍ) p none σ δ (VTy.all y c (.lolli (.imm (.var y) T) B')) αs ls f ρf →
    vRLM (ℍ := ℍ) p none (e :: σ) (δ.extend y α) (.imm (.var y) T) (α :: αs) ls' w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    PlaceViewsL (extS (δ.extend y α) (e :: σ) (α :: αs)) (e :: σ) (α :: αs) ls' ρ →
    cRLM (ℍ := ℍ) p (e :: σ) (δ.extend y α) (.ret B') (α :: αs) ls'
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ

/-! ### Item 3: the `∀I` row's open cases (`NEXT.md` §3.2–§3.4) -/

/-- **`SubOutside` along a binding of the innermost entry's variable**, the entry pushed fresh below
the reading. -/
def SubOutsideExtendNamed : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (e : LEnt) (α a : Life),
    (σ.map LEnt.x).Nodup → σ.head? = some e → αs.head? = some a → SubFresh δ a →
    SubOutside σ αs δ → SubOutside σ αs (δ.extend e.x α)

/-- **`[allI]` at one context, at every index.** -/
def AllIRowMAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (M : Expr) (S : VTy) (C : CTy),
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → Δ.find? x = none →
    (∀ s ∈ Γ, s.live = true → x ∉ VTy.binders s.ty) →
    SemSM (ℍ := ℍ) p (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C) →
    SemSM (ℍ := ℍ) p Δ Γ (.val (.lam M)) (.comp (.all x b C))

/-- **The context at the reading extended at the innermost entry's variable**, which the stack
shadows: at a context reaching no `U`. `StackOK σ αs` (beside `NEXT.md`'s statement) keeps the
stack's lifetimes in step with its entries, so that the stack reads the head's variable. -/
def CtxExtendNamedMAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (e : LEnt) (α : Life),
    StackOK σ αs → σ.head? = some e → InScope (extS δ σ αs) α → CtxFresh e.x Γ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ (δ.extend e.x α) αs ls Γ γ ρ

/-- **The same at every context, at an instance in scope**: the entry's variable is read in no
entry's payload type (`StackJM`'s third kind gives it). `VRLMReadEquiv` with `X = {e.x}`. -/
def CtxExtendNamedMSAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (e : LEnt) (α : Life),
    StackOK σ αs → σ.head? = some e → δ.find? e.x = none → (∀ e' ∈ σ, ¬ VFree e.x e'.T) →
    InScope (extS δ σ αs) α → CtxFresh e.x Γ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ (δ.extend e.x α) αs ls Γ γ ρ

/-- **Two readings the relation cannot tell apart at a stack.** The base readings agree off `X`,
and so do the stack's (`extS` reads the stack's variables alike). The values in scope agree. A lend
below the innermost is fresh below one exactly when it is fresh below the other (at the empty
stack, every lend). -/
def ReadEquiv (X : LifeVar → Prop) (σ : LStack) (αs : List Life) (δ₁ δ₂ : LSub) : Prop :=
  (∀ y, ¬ X y → δ₁.find? y = δ₂.find? y) ∧
  (∀ α, InScope (extS δ₁ σ αs) α ↔ InScope (extS δ₂ σ αs) α) ∧
  ∀ a, (∀ h ∈ αs.head?, a < h) → (SubFresh δ₁ a ↔ SubFresh δ₂ a)

/-- **`vRLM` reads only what `ReadEquiv` fixes**, at every type and in both directions. `X` avoids
the type's free variables and binders, the environment's types, and the entries' payload types. -/
def VRLMReadEquiv : Prop :=
  ∀ (A : VTy) (η : Option (Nat → WEnt)) (X : LifeVar → Prop) (σ : LStack) (δ₁ δ₂ : LSub)
    (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    (∀ y, X y → ¬ VFree y A ∧ y ∉ VTy.binders A ∧ ∀ n, ¬ VFree y (wEnv η n).ty) →
    (∀ y, X y → ∀ e ∈ σ, ¬ VFree y e.T) → StackOK σ αs → ReadEquiv X σ αs δ₁ δ₂ →
    (vRLM (ℍ := ℍ) .binder0 η σ δ₁ A αs ls v ρ ↔ vRLM (ℍ := ℍ) .binder0 η σ δ₂ A αs ls v ρ)

/-- **`CtxExtendMAt` at an instance in scope.** -/
def CtxExtendMSAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (x : LifeVar) (α : Life),
    StackOK σ αs → x ∉ σ.map LEnt.x → δ.find? x = none → StackPayAvoids x σ →
    InScope (extS δ σ αs) α →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty ∧ x ∉ VTy.binders s.ty) →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ (δ.extend x α) αs ls Γ γ ρ

/-- **`CtxShadowMAt` with the facts the symmetric route reads**: the pushed stack in shape, and the
pushed entry's payload type not reading its own variable (`OwnPushM`'s `selfFree`). -/
def CtxShadowMSAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (e : LEnt) (α : Life),
    StackOK (e :: σ) (α :: αs) → δ.find? e.x = none → ¬ VFree e.x e.T →
    StackPayAvoids e.x σ →
    (∀ s ∈ Γ, s.live = true → ¬ VFree e.x s.ty ∧ e.x ∉ VTy.binders s.ty) →
    gRLM (ℍ := ℍ) p (e :: σ) δ (α :: αs) ls Γ γ ρ →
      gRLM (ℍ := ℍ) p (e :: σ) (δ.extend e.x α) (α :: αs) ls Γ γ ρ

/-- **The own push's view is outside the old guard**: beside any resource, a borrow cell exactly at
the pushed lifetime fails the old stack's table, so the old `⊸` clause says nothing about an
argument holding it. A fact about the clause, not an obstruction. -/
def PushedViewOutsideOldGuard : Prop :=
  ∀ (σ : LStack) (αs : List Life) (a : Life) (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val) (ρc ρ : WRes),
    αs ≠ [] → List.IsChain (· < ·) (a :: αs) → ψ.kind ≠ Kind.own → ψ.at = a →
    ResU.CompS ρc (ResU.single l ψ) ρ → ¬ TabAtS σ αs ρ

/-- A value type holding no owned cell (no `Ref`, at any depth W reads). -/
def RefFree : VTy → Prop
  | .ref _ => False
  | .tensor A B => RefFree A ∧ RefFree B
  | .sum A B => RefFree A ∧ RefFree B
  | .bang A => RefFree A
  | .box _ A => RefFree A
  | .mu A => RefFree A
  | .fam L => RefFree L
  | _ => True

mutual
/-- **A value type the own push carries by its clauses' shape.** -/
def PushStableV : VTy → Prop
  | .thunk C => PushStableC C
  | .tensor A B => PushStableV A ∧ PushStableV B
  | .sum A B => PushStableV A ∧ PushStableV B
  | .bang A => PushStableV A
  | .box _ A => PushStableV A
  | .ref A => PushStableV A
  | .mu A => PushStableV A
  | .fam L => PushStableV L
  | _ => True
/-- **A computation type the own push carries**: no lifetime `∀`, no effect layer, no `ν`, and
every argument reaching no `U` and holding no owned cell. -/
def PushStableC : CTy → Prop
  | .ret A => PushStableV A
  | .arr A C => UFreeM A ∧ RefFree A ∧ PushStableC C
  | .amp C D => PushStableC C ∧ PushStableC D
  | .top => True
  | .all _ _ _ => False
  | .nu _ => False
  | .eff _ _ _ _ _ _ => False
end

/-- **`MonoOwnGMAt` at a context whose live slots are push-stable.** -/
def MonoOwnGMAtPS (p : Placement) : Prop :=
  ∀ Γ : Ctx VTy, (∀ s ∈ Γ, s.live = true → PushStableV s.ty) → MonoOwnGMAt (ℍ := ℍ) p Γ

/-- **The `⊸` case of the push, at an argument holding the pushed view.** As stated it is expected
to fail at `gd`, a configuration not shown to arise, by the R1 unit's `gdG_pushed` and
`gd_run_fails_of` [unchecked: no `¬ PushArrStep` is built]. -/
def PushArrStep : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (D : CTy) (αs : List Life) (ls : List SRec) (e : Expr)
    (ρf : WRes) (en : LEnt) (a : Life) (w : Val) (ρv ρ : WRes) (ψ : CellU BoCa.Loc Val),
    StackOK (en :: σ) (a :: αs) → OuterBelowTop αs → RecsOutside (a :: αs) ls →
    SubOutside σ αs δ → SubFresh δ a → δ.find? en.x = none →
    ¬ CFree en.x (.arr A D) → en.x ∉ CTy.binders (.arr A D) → StackPayAvoids en.x σ →
    (∀ ψ', ¬ DeepAt ρf en.l ψ') → ρf.InStratum a → TabAtS σ αs ρf →
    PlaceViewsL (extS δ σ αs) σ αs ls ρf →
    cRLM (ℍ := ℍ) .binder0 σ δ (.arr A D) αs ls e ρf →
    vRLM (ℍ := ℍ) .binder0 none (en :: σ) δ A (a :: αs) ls w ρv →
    ρv.get en.l = some ψ → ψ.kind ≠ Kind.own → ψ.at = a →
    ResU.CompS ρf ρv ρ → TabAtS (en :: σ) (a :: αs) ρ →
    PlaceViewsL (extS δ (en :: σ) (a :: αs)) (en :: σ) (a :: αs) ls ρ →
    cRLM (ℍ := ℍ) .binder0 (en :: σ) δ D (a :: αs) ls (.app e (.val w)) ρ

/-- **`PushArrStep` under the Core-value restriction**, at types with no lifetime `∀`. -/
def PushArrStepC : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (D : CTy) (αs : List Life) (ls : List SRec) (e : Expr)
    (ρf : WRes) (en : LEnt) (a : Life) (w : Val) (ρv ρ : WRes),
    VAllFree A → CAllFree D →
    StackOK (en :: σ) (a :: αs) → OuterBelowTop αs → RecsOutside (a :: αs) ls →
    SubOutside σ αs δ → SubFresh δ a → δ.find? en.x = none →
    ¬ CFree en.x (.arr A D) → en.x ∉ CTy.binders (.arr A D) → StackPayAvoids en.x σ →
    (∀ ψ', ¬ DeepAt ρf en.l ψ') → ρf.InStratum a → TabAtS σ αs ρf →
    PlaceViewsL (extS δ σ αs) σ αs ls ρf →
    cRLM (ℍ := ℍ) .binder0 σ δ (.arr A D) αs ls e ρf → cC (.arr A D) ls (extS δ σ αs) e ρf →
    vRLM (ℍ := ℍ) .binder0 none (en :: σ) δ A (a :: αs) ls w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (en :: σ) (a :: αs) ρ →
    PlaceViewsL (extS δ (en :: σ) (a :: αs)) (en :: σ) (a :: αs) ls ρ →
    cRLM (ℍ := ℍ) .binder0 (en :: σ) δ D (a :: αs) ls (.app e (.val w)) ρ

/-- **The `⊸` case at an argument reaching a `U` that holds nothing** (the pop): a `U` value over
the empty resource, related at the pushed stack, is related at the stack. -/
def PopUStep : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec) (w : Val) (en : LEnt)
    (a : Life),
    StackOK (en :: σ) (a :: αs) → OuterBelowTop αs → RecsOutside (a :: αs) ls →
    SubOutside σ αs δ → SubFresh δ a → δ.find? en.x = none → ¬ CFree en.x C →
    en.x ∉ CTy.binders C → StackPayAvoids en.x σ →
    vRLM (ℍ := ℍ) .binder0 none (en :: σ) δ (.thunk C) (a :: αs) ls w PMap.empty →
    vRLM (ℍ := ℍ) .binder0 none σ δ (.thunk C) αs ls w PMap.empty

/-- **The `F_Σ` case of the push, at a stop.** -/
def PushEffStep : Prop :=
  ∀ (δ : LSub) (σ : LStack) (Tab : OpTab) (Q Q' : List Life → List SRec → Val → WProp)
    (αs : List Life) (ls : List SRec) (t : Expr) (ρ : WRes) (en : LEnt) (a : Life),
    StackOK (en :: σ) (a :: αs) → (∀ ψ, ¬ DeepAt ρ en.l ψ) → ρ.InStratum a → TabAtS σ αs ρ →
    (∀ (a' : Life) (αs' : List Life) (ls' : List SRec) (v : Val) (ρ' : WRes),
      Q αs' ls' v ρ' → Q' (a' :: αs') ls' v ρ') →
    stopS δ σ Tab (OpenS δ σ Tab Q) αs ls t ρ →
    stopS δ (en :: σ) Tab (OpenS δ (en :: σ) Tab Q') (a :: αs) ls t ρ

/-- **The `∀` case of the push.** -/
def PushAllStep : Prop :=
  ∀ (σ : LStack) (δ : LSub) (z : LifeVar) (c : Lifetime.Life) (C : CTy) (αs : List Life)
    (ls : List SRec) (e : Expr) (ρ : WRes) (en : LEnt) (a : Life),
    StackOK (en :: σ) (a :: αs) → OuterBelowTop αs → RecsOutside (a :: αs) ls →
    SubOutside σ αs δ → SubFresh δ a → δ.find? en.x = none → ¬ CFree en.x (.all z c C) →
    en.x ∉ CTy.binders (.all z c C) → StackPayAvoids en.x σ → (∀ ψ, ¬ DeepAt ρ en.l ψ) →
    ρ.InStratum a →
    cRLM (ℍ := ℍ) .binder0 σ δ (.all z c C) αs ls e ρ →
    cRLM (ℍ := ℍ) .binder0 (en :: σ) δ (.all z c C) (a :: αs) ls e ρ

/-- **`MonoOwnGMC` at one context**, with the pushed variable read in no entry's payload type. -/
def MonoOwnGMCAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (C : CTy) (e : LEnt) (a : Life),
    StackPayAvoids e.x σ → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls →
    SubOutside σ αs δ → OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    RecsOutside (a :: αs) ls → SubFresh δ a → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLMC (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLMC (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ

/-! ### Item 4: `MonoHide` at `vRLM`, and the consumers (`NEXT.md` §4) -/

/-- **A value inside a handler of the names `N`, at `vRLM`.** -/
def MonoHideM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes)
    (N : UInt32 → Bool), StackOK σ αs → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ → vRLM (ℍ := ℍ) p none (hideS N σ) δ A αs ls v ρ

/-- **A context inside a handler of the names `N`** (`[handle]`'s transport). -/
def MonoHideGM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (N : UInt32 → Bool), StackOK σ αs → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p (hideS N σ) δ αs ls Γ γ ρ

/-- **Hiding names no entry's row holds changes nothing.** -/
def HideInvisible : Prop :=
  ∀ (N : UInt32 → Bool) (σ : LStack), (∀ e ∈ σ, ∀ n, N n = true → e.cross n = false) →
    hideS N σ = σ

mutual
/-- **A value type carries the operation name `n`**: an effect layer of `n` under a `U`, through
the formers W reads itself (Core's leaves read no stack). -/
inductive CarriesV (n : UInt32) : VTy → Prop
  | thunk {C : CTy} : CarriesC n C → CarriesV n (.thunk C)
  | tensorL {A B : VTy} : CarriesV n A → CarriesV n (.tensor A B)
  | tensorR {A B : VTy} : CarriesV n B → CarriesV n (.tensor A B)
  | sumL {A B : VTy} : CarriesV n A → CarriesV n (.sum A B)
  | sumR {A B : VTy} : CarriesV n B → CarriesV n (.sum A B)
  | bang {A : VTy} : CarriesV n A → CarriesV n (.bang A)
  | box {a : Lifetime.Life} {A : VTy} : CarriesV n A → CarriesV n (.box a A)
  | ref {A : VTy} : CarriesV n A → CarriesV n (.ref A)
  | fam {L : VTy} : CarriesV n L → CarriesV n (.fam L)
  | mu {A : VTy} : CarriesV n A → CarriesV n (.mu A)
/-- **A computation type carries the operation name `n`.** -/
inductive CarriesC (n : UInt32) : CTy → Prop
  | eff {i : UInt32} {q : Qual} {A B : VTy} {C : CTy} : CarriesC n (.eff n i q A B C)
  | effIn {m i : UInt32} {q : Qual} {A B : VTy} {C : CTy} :
      CarriesC n C → CarriesC n (.eff m i q A B C)
  | ret {A : VTy} : CarriesV n A → CarriesC n (.ret A)
  | arrA {A : VTy} {C : CTy} : CarriesV n A → CarriesC n (.arr A C)
  | arrC {A : VTy} {C : CTy} : CarriesC n C → CarriesC n (.arr A C)
  | ampL {C D : CTy} : CarriesC n C → CarriesC n (.amp C D)
  | ampR {C D : CTy} : CarriesC n D → CarriesC n (.amp C D)
  | all {x : LifeVar} {c : Lifetime.Life} {C : CTy} : CarriesC n C → CarriesC n (.all x c C)
end

/-- **The relation reads an entry's row only at the names the type carries.** -/
def VRLMHideAvoid : Prop :=
  ∀ (p : Placement) (N : UInt32 → Bool) (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life)
    (ls : List SRec), (∀ n, N n = true → ¬ CarriesV n A) →
    vRLM (ℍ := ℍ) p none (hideS N σ) δ A αs ls = vRLM (ℍ := ℍ) p none σ δ A αs ls

/-- **`[handle]`'s context transport at `binder0`, where it is invisible**: the handled name crosses
no entry, or no live type carries it. -/
def MonoHideGMHandle0 : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (n : UInt32),
    ((∀ e ∈ σ, e.cross n = false) ∨ ∀ s ∈ Γ, s.live = true → ¬ CarriesV n s.ty) →
    gRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ ρ →
    gRLM (ℍ := ℍ) .binder0 (hideS (· == n) σ) δ αs ls Γ γ ρ

/-- **`MonoHideM`'s `F_Σ` case at a stop**, the step the general case reads: a stop at `σ` is a stop
at `hideS N σ`, with the piece's continuation carried along. -/
def HideStopStep : Prop :=
  ∀ (δ : LSub) (σ : LStack) (N : UInt32 → Bool) (Tab : OpTab)
    (Q : List Life → List SRec → Val → WProp) (αs : List Life) (ls : List SRec) (t : Expr)
    (ρ : WRes),
    StackOK σ αs → TabAtS σ αs ρ →
    stopS δ σ Tab (OpenS δ σ Tab Q) αs ls t ρ →
    stopS δ (hideS N σ) Tab (OpenS δ (hideS N σ) Tab Q) αs ls t ρ

/-- Statement 4's `ovalU` at `vRLM`. -/
def ovalUM (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Targets.Inst.OCTy → Targets.RowEnv → Val → WProp
  | .allR ρ k C, η, v => fun r => ∀ s : Row, k.cls.Admits s → (∀ o ∈ s, k.adm o) →
      ovalUM p σ δ αs ls C (Function.update η ρ s) v r
  | C, η, v => vRLM (ℍ := ℍ) p none σ δ (.thunk (Targets.Inst.OCTy.den η C)) αs ls v

/-- Statement 4's `ovalW` at `vRLM`. -/
def ovalWM (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Targets.Inst.OVTy → Targets.RowEnv → Val → WProp
  | .thunk C, η, v => ovalUM p σ δ αs ls C η v
  | .bang A, η, v => fun r => r = PMap.empty ∧ ovalWM p σ δ αs ls A η v r
  | A, η, v => vRLM (ℍ := ℍ) p none σ δ (Targets.Inst.OVTy.den η A) αs ls v

/-- **`AllRMono`'s record-order half at `vRLM .binder0`**: a row-polymorphic value carried along
an extension of the list that keeps the tags. -/
def AllRExtM0 : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls ls' : List SRec) (ρv : Targets.RVar)
    (k : Targets.RowCon) (C : Targets.Inst.OCTy) (η : Targets.RowEnv) (v : Val) (r : WRes),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → RecsOutside αs ls' →
    Ext ls ls' r → KeepsT ls ls' r → TabAtS σ αs r → PlaceViewsL (extS δ σ αs) σ αs ls r →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls' (.thunk (.allR ρv k C)) η v r

/-- **`AllRMono`'s own-push half**: carried across the callback's own push (`OwnPushM`, with the
`∀` clause's freshness). -/
def AllROwnM0 : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (ρv : Targets.RVar)
    (k : Targets.RowCon) (C : Targets.Inst.OCTy) (η : Targets.RowEnv) (v : Val) (r : WRes)
    (C' : CTy) (e : LEnt) (a : Life),
    StackPayAvoids e.x σ → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls →
    SubOutside σ αs δ → OwnPushM δ C' r (σ, αs) e a → δ.find? e.x = none →
    (∀ η', ¬ VFree e.x (Targets.Inst.OVTy.den η' (.thunk (.allR ρv k C))) ∧
      e.x ∉ VTy.binders (Targets.Inst.OVTy.den η' (.thunk (.allR ρv k C)))) →
    RecsOutside (a :: αs) ls → SubFresh δ a → TabAtS σ αs r →
    PlaceViewsL (extS δ σ αs) σ αs ls r →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    ovalWM (ℍ := ℍ) .binder0 (e :: σ) δ (a :: αs) ls (.thunk (.allR ρv k C)) η v r

/-- **`AllRMono`'s instantiation half**: the thaw (`RelendMValue`'s form) through the
intersection. A `U` introduction at `binder0` thaws every captured slot (`CtxRelendsAllM`, inside
`statement0UFullM`); this is that step at a slot holding a row-polymorphic value. -/
def AllRThawM0 : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (ρv : Targets.RVar)
    (k : Targets.RowCon) (C : Targets.Inst.OCTy) (η : Targets.RowEnv) (v : Val) (r : WRes),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs r →
    PlaceViewsL (extS δ σ αs) σ αs ls r →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    RelendJ δ σ
      (fun δ' αs' ls' => ovalWM (ℍ := ℍ) .binder0 σ δ' αs' ls' (.thunk (.allR ρv k C)) η v)
      αs ls r

/-- **`AllRMono`'s hiding half**: carried into a handler of the names `N`. -/
def AllRHideM0 : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (ρv : Targets.RVar)
    (k : Targets.RowCon) (C : Targets.Inst.OCTy) (η : Targets.RowEnv) (v : Val) (r : WRes)
    (N : UInt32 → Bool),
    StackOK σ αs → TabAtS σ αs r → PlaceViewsL (extS δ σ αs) σ αs ls r →
    ovalWM (ℍ := ℍ) .binder0 σ δ αs ls (.thunk (.allR ρv k C)) η v r →
    ovalWM (ℍ := ℍ) .binder0 (hideS N σ) δ αs ls (.thunk (.allR ρv k C)) η v r

/-- **Statement 4's `AllRMono` at `vRLM .binder0`**: a row-polymorphic value carried along the
four index changes between its making and its use inside a borrow's callback. -/
def AllRMonoM0 : Prop :=
  AllRExtM0 (ℍ := ℍ) ∧ AllROwnM0 (ℍ := ℍ) ∧ AllRThawM0 (ℍ := ℍ) ∧ AllRHideM0 (ℍ := ℍ)

/-- **An intersection commutes with `RelendJ`**: a resource meeting `RelendJ` at each member of a
nonempty family of clauses meets it at their intersection. The step `AllRThawM0` takes at a slot
that holds resource. -/
def RelendJInter : Prop :=
  ∀ (I : Type) (P : I → LSub → List Life → List SRec → WProp) (δ : LSub) (σ : LStack)
    (αs : List Life) (ls : List SRec) (ρ : WRes), Nonempty I →
    StackOK σ αs → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    (∀ i, RelendJ δ σ (P i) αs ls ρ) →
    RelendJ δ σ (fun δ' αs' ls' ρ' => ∀ i, P i δ' αs' ls' ρ') αs ls ρ

/-- **Statement 0 at `binder0`, read at the consumers the inventory finds.** Its conjuncts:
- the facts beside monotonicity;
- the record order;
- the `∀I` row (its context across the own push, to the binder's reading, and to the shadow);
- `[handle]`'s context into the hidden stack;
- statement 4's `AllRMono` at `vRLM .binder0`, which DESIGN derives from `MonoV` and `MonoC`: its
  four halves (record order, own push, the thaw, hiding). -/
def Statement0MAtConsumers0Full : Prop :=
  Statement0MBesideMono0 (ℍ := ℍ) ∧ MonoExtM (ℍ := ℍ) .binder0 ∧ AllIRowM (ℍ := ℍ) .binder0 ∧
    MonoHideGM (ℍ := ℍ) .binder0 ∧ AllRMonoM0 (ℍ := ℍ)

end ProbeD1

end
