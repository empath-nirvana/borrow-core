import ProbeD1.BinderRisk

/-!
# ProbeD1 — the instantiation's gap at `∀` (`GAP.md`)

`TyEqInst` is proved only at `CoreStable` types (`tyEq_inst`). The structural induction stops at
`CTyEq`'s `∀` clause: at a fixed instantiation `ι` the hypothesis reaches the instances in `ι`'s
image only (`Inst.sub_extend`), and a re-stratification leaves lifetimes with no preimage below
its cut. This file states what `GAP.md` designs. The proofs are in `GapWitness.lean` (§3c),
`GapCover.lean` (§2), `GapRows.lean` (§2's leaves and rows), `GapPos.lean` (§3) and
`GapRoom.lean` (W's `U` clause as reading (B)); `GAP.md` §8 is the outcome.

* **§1 The stop** (`InGap`, `TyEqGapStep`): the step the fixed-`ι` induction cannot take.
* **§2 `TyEq` reads no room.** `TyEq` and `CTyEq` (`Core/FrameRecords.lean`) are conjunctions of
  equalities `@aδ = @a′δ′` under an unbounded `∀`. Equality on a chain is decided threshold by
  threshold, and a lifetime term commutes with the two-point collapse at a threshold
  (`collapseN`, `InterpCollapse`, `EqOfCollapse`). The statements, argued in `GAP.md` §2.1 and
  proved in `GapCover.lean`: `TyEq` holds at every pair a family of `TyEq` pairs covers threshold
  by threshold (`TyCover`, `TyEqOfCover`), an instantiated pair is covered by its source
  (`CoverInst`), and a gap instance by the image instances (`CoverGap`); `TyEq` is invariant under
  every order embedding fixing `⊤` (`TyEqRoomBlind`). With `TyEqInst` at every type the leaves'
  `CoreStable` restriction goes (`CohEInstOB`, `ViewSlotInstOB`, `ThawFreeK`, `RelendJValueK`,
  `Statement0UThawFreeKJ`); `μ` and `fam` slots stay outside (R1).
* **§3 The position-`∀`.** The order of lifetimes in play, its positions, and the two readings:
  - (B) `AllPosJ`: the `∀` clause read at every instantiation of the stack, the views handed back,
    then at every lifetime below the bound. Every cut below the stack's cut is opened by an
    instantiation (`InstRealisesCut`), so it reads every position an admissible embedding can
    open; it is carried along an instantiation by composition (`AllPosJTransport`), implies the
    clause at the stack itself (`AllPosJSelf`), and is Core's clause at `σ = []` (`AllPosJNil`).
  - (A) `CutAllC`: Core's relation at every renaming of the whole configuration by an embedding
    fixing `⊤`, cells included. One way at `σ = []` (`CutAllNilSound`; the converse is refuted by
    `not_coreAllImpCutAll`).
  - The witness that Core's ℕ-`∀` reads the room between lifetimes (`CoreAllAdjacent`,
    `CoreAllNotNatural`, `NotCoreAllImpCutAll`; proved in `GapWitness.lean`).
* **§4 R1.** A `μ` slot read by Core's relation, holding a closure whose `∀` holds by adjacency at
  the outermost lend (`muΓ`, `MuSlotIndex`), and the thaw's expected failure there
  (`NotMuSlotThawCore`). Stated, not attempted (`GAP.md` §6.5 item 2).

Definitions and `def … : Prop` statements only.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS stratS TabAtS innerView)

/-! ### §1 The stop -/

/-- **A lifetime in an instantiation's gap**: no lifetime is sent to it. `Restrat.Emb.shift c k`
has `k` of them just below `c` (`Restrat.MutCounterexample.gap` at `c = ⊤`, `k = 1`). -/
def InGap (ι : Inst) (a : Life) : Prop := ∀ b, ι.life1 b ≠ a

/-- **The step the fixed-instantiation induction cannot take**, at `CTyEq`'s `∀` clause: from the
instances at the image of `ι`, which the induction hypothesis at `ι` gives through
`Inst.sub_extend`, to every instance, those in `ι`'s gap among them. -/
def TyEqGapStep : Prop :=
  ∀ (C C' : CTy) (x x' : LifeVar) (s s' : LSub) (ι : Inst),
    (∀ α : Life, CTyEq C ((ι.sub s).extend x (ι.life1 α)) C' ((ι.sub s').extend x' (ι.life1 α))) →
    ∀ α' : Life, CTyEq C ((ι.sub s).extend x α') C' ((ι.sub s').extend x' α')

/-! ### §2 `TyEq` reads no room -/

/-- **The two-point collapse at the threshold `t`**, on the naturals that carry `Life` (`⊤ = 0`):
a lifetime at or above `t` (`n ≤ t`) to `⊤`, one strictly below it to `1`. It is monotone and fixes
`⊤`, so it commutes with `⊔` (`min`) and `⊓` (`max`). -/
def collapseN (t : ℕ) (n : ℕ) : ℕ := if n ≤ t then 0 else 1

/-- **A lifetime term commutes with the collapse.** -/
def InterpCollapse : Prop :=
  ∀ (a : Lifetime.Life) (t : ℕ) (δ : LSub),
    a.interp (Restrat.LSub.mapN (collapseN t) δ) = (a.interp δ).map (collapseN t)

/-- **Two readings are equal when every collapse equates them**: a chain separates two of its
points by the threshold at the longer one. -/
def EqOfCollapse : Prop :=
  ∀ o o' : Option ℕ, (∀ t, o.map (collapseN t) = o'.map (collapseN t)) → o = o'

/-- **A family of reading pairs covers a pair**: at every threshold `t₂`, some member read at some
threshold `t₁` collapses, variable by variable, as the pair does at `t₂`. Domains agree, since
`Option.map` keeps `none`. The member may change with the threshold. -/
def TyCover (S : LSub → LSub → Prop) (s₂ s₂' : LSub) : Prop :=
  ∀ t₂ : ℕ, ∃ s₁ s₁', S s₁ s₁' ∧ ∃ t₁ : ℕ, ∀ y : LifeVar,
    (s₂.find? y).map (collapseN t₂) = (s₁.find? y).map (collapseN t₁) ∧
    (s₂'.find? y).map (collapseN t₂) = (s₁'.find? y).map (collapseN t₁)

/-- **`TyEq` holds at every pair a family of `TyEq` pairs covers**, at value and at computation
types. By induction on the type, the family generalised at `∀`: the family of the members
extended at the binder by every lifetime covers the pair extended by any one, since at each
threshold a member can be extended by `⊤` or by a lifetime below the threshold. At an equation
`@aδ = @a′δ′`: `EqOfCollapse`, then `InterpCollapse` at both sides and the member's equation. -/
def TyEqOfCover : Prop :=
  (∀ (A B : VTy) (S : LSub → LSub → Prop) (s₂ s₂' : LSub),
    (∀ s₁ s₁', S s₁ s₁' → TyEq A s₁ B s₁') → TyCover S s₂ s₂' → TyEq A s₂ B s₂') ∧
  ∀ (C D : CTy) (S : LSub → LSub → Prop) (s₂ s₂' : LSub),
    (∀ s₁ s₁', S s₁ s₁' → CTyEq C s₁ D s₁') → TyCover S s₂ s₂' → CTyEq C s₂ D s₂'

/-- **An instantiated pair is covered by its source**: a threshold of the image is the image of
the source's largest lifetime the instantiation sends at or above it. -/
def CoverInst : Prop :=
  ∀ (s s' : LSub) (ι : Inst), TyCover (fun r r' => r = s ∧ r' = s') (ι.sub s) (ι.sub s')

/-- **A gap instance is covered by the image instances**: at each threshold, the image of `⊤` or
of a lifetime below the threshold collapses as the gap lifetime does. With `TyEqOfCover` it gives
`TyEqGapStep`. -/
def CoverGap : Prop :=
  ∀ (x x' : LifeVar) (s s' : LSub) (ι : Inst) (α' : Life),
    TyCover (fun r r' => ∃ α : Life, r = (ι.sub s).extend x (ι.life1 α) ∧
      r' = (ι.sub s').extend x' (ι.life1 α)) ((ι.sub s).extend x α') ((ι.sub s').extend x' α')

/-- **`TyEq` is invariant under every order embedding fixing `⊤`**, those that open a gap
included. `Restrat.Emb ⊤` is every strictly monotone map fixing `⊤`; an instantiation's
re-stratification is one (`embLift`). Contrast `CoreAllNotNatural`. -/
def TyEqRoomBlind : Prop :=
  ∀ (A B : VTy) (s s' : LSub) (φ : Restrat.Emb (⊤ : Life)),
    TyEq A s B s' ↔ TyEq A (Restrat.LSub.mapN φ.toNat s) B (Restrat.LSub.mapN φ.toNat s')

/-! #### The leaves at every payload type -/

/-- **`CohEInst` at every type, the outermost lend below `⊤`**: `cohE_inst` with its `CoreStable`
hypothesis dropped. It reads `CoreStable` only through `tyEq_inst`. -/
def CohEInstOB : Prop :=
  ∀ (αs : List Life) (ι : Inst) (ls ls' : List SRec) (T : VTy) (s : LSub) (l : BoCa.Loc)
    (R : WRes), InstAt αs ι → OuterBelowTop αs → RecsOutside αs ls →
    (∃ ψ, R.get l = some ψ ∧ ψ.kind = Kind.imm) → KeepsS (ι.recs ls) ls' R →
    CohE (rsOf ls) l T s → CohE (rsOf ls') l T (ι.sub s)

/-- **`ViewSlotInst` at every slot type, the outermost lend below `⊤`**: `ViewSlotInstCS` with its
`CoreStable` hypothesis dropped. Its steps are `TyEqInst`, `vC_tyEq`, `CohEInstOB` and, at `Imm`,
the full payload implying the observable one (`vO_obs`). -/
def ViewSlotInstOB : Prop :=
  ∀ (σ : LStack) (αs : List Life) (s : LSub) (ls ls' : List SRec) (A : VTy) (l : BoCa.Loc)
    (e : LEnt) (α : Life) (ρ ρv : WRes) (ι : Inst), OuterBelowTop αs →
    innerAt σ αs l = some (e, α) → InstAt αs ι → RecsOutside αs ls → KeepsS (ι.recs ls) ls' ρ →
    vC true A ls s (.loc l) ρ → CohS σ αs s A (.loc l) ρ →
    vwEW (ι.sub s) e true (ι.life1 α) ls' ρv →
    vC true A ls' (ι.sub s) (.loc l) ρv ∧ CohS σ (ι.life αs) (ι.sub s) A (.loc l) ρv

/-- **A slot type the thaw handles once `TyEqInst` holds**: W's own formers down to `U`, which W
instantiates by construction, and `Mut` and `Imm` leaves at every payload type (a view is handed
back and read up to `TyEq`; a retained cell's payload reads external lifetimes, `RetainedPay`).
`μ` and `fam` are handed to Core's relation whole and stay outside (R1). -/
def ThawFreeK : VTy → Prop
  | .thunk _ => True
  | .tensor A B => ThawFreeK A ∧ ThawFreeK B
  | .sum A B => ThawFreeK A ∧ ThawFreeK B
  | .bang A => ThawFreeK A
  | .box _ A => ThawFreeK A
  | .ref A => ThawFreeK A
  | .mu _ => False
  | .fam _ => False
  | _ => True

/-- A context every live slot of which is `ThawFreeK`. -/
def CtxThawFreeK (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → ThawFreeK s.ty

/-- **The thaw of a slot at every `ThawFreeK` type** (`relendJ_value`'s statement at the wider
class). -/
def RelendJValueK : Prop :=
  ∀ (A : VTy), ThawFreeK A →
    ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLJ .binder0 σ δ A αs ls v ρ →
    RelendJ δ σ (fun δ' αs' ls' => vRLJ .binder0 σ δ' A αs' ls' v) αs ls ρ

/-- The context's thaw at every `CtxThawFreeK` context. -/
def CtxRelendsThawFreeKJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy), CtxThawFreeK Γ → CtxRelendableAtJ (ℍ := ℍ) p Δ Γ

def ThunkFRowKJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFreeK Γ →
    SemSJ (ℍ := ℍ) p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSJ (ℍ := ℍ) p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))

def ThunkVRowKJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxThawFreeK Γ → C.isRet = false →
    OwnHyg Δ Γ C → SemSJ (ℍ := ℍ) p Δ Γ (.val (.lam N)) (.comp C) →
    SemSJ (ℍ := ℍ) p Δ Γ (.val (.lam N)) (.val (.thunk C))

def BangThunkFRowKJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFreeK Γ → Persistent Γ →
    SemSJ (ℍ := ℍ) p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSJ (ℍ := ℍ) p Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))

def BangThunkVRowKJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxThawFreeK Γ → Persistent Γ →
    C.isRet = false → OwnHyg Δ Γ C → SemSJ (ℍ := ℍ) p Δ Γ (.val (.lam N)) (.comp C) →
    SemSJ (ℍ := ℍ) p Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-- **The `U` side of statement 0 at `vRLJ`, at the contexts `CtxThawFreeK` admits**:
`Statement0UThawFreeJ` with `CtxThawFree` widened to `CtxThawFreeK`. -/
def Statement0UThawFreeKJ (p : Placement) : Prop :=
  ThawInstJ (ℍ := ℍ) p ∧ CtxRelendsThawFreeKJ (ℍ := ℍ) p ∧ ThunkFRowKJ (ℍ := ℍ) p ∧
    ThunkVRowKJ (ℍ := ℍ) p ∧ BangThunkFRowKJ (ℍ := ℍ) p ∧ BangThunkVRowKJ (ℍ := ℍ) p

/-! ### §3 The position-`∀` -/

/-- **One position**: `α` stands among the lifetimes `L` as `α'` stands among their images under
`f`; each compares to the two alike. -/
def SamePos (L : List Life) (f : Life → Life) (α α' : Life) : Prop :=
  ∀ a ∈ L, (a < α ↔ f a < α') ∧ (α < a ↔ α' < f a)

/-- **Every cut below the stack's cut is realised at an instantiation**: for lifetimes `L` in play
with nothing strictly between `lo < hi ≤ c`, some re-stratification at `c` and some lifetime stand
strictly between the images of `L` at or below `lo` and those at or above `hi`. The witness is the
shift by one at `hi`, lifted to `c` (`embLift`), and the lifetime just below `hi`. A cut above
`c` is opened by no instantiation: every one fixes each lifetime at or above `c`. The proof does
not use the hypothesis that nothing in `L` lies strictly between `lo` and `hi`; it is kept so that
the statement names a cut. Nothing here ties `L` to the lifetimes an index reads, and `SamePos` is
read by no proof (`GAP.md` §6.1). -/
def InstRealisesCut : Prop :=
  ∀ (L : List Life) (c lo hi : Life), lo < hi → hi ≤ c → (∀ a ∈ L, a ≤ lo ∨ hi ≤ a) →
    ∃ (θ : Restrat.Emb c) (α : Life), ∀ a ∈ L, (a ≤ lo → θ a < α) ∧ (hi ≤ a → α < θ a)

/-- **The position-`∀` at W, reading (B)**: the `∀` clause read at every instantiation of the
stack's internal lifetimes, the views handed back there, the records moved with it, and then at
every lifetime below the bound at the instantiated reading. `P δ' αs' ls' α` is the body at the
reading `δ'` extended by `α`. By `InstRealisesCut` it reads every position of the lifetimes in
play below the stack's cut; above the cut it is the ℕ-`∀`, which no admissible embedding opens.
At `binder0` it would replace `cRLJ`'s first `∀` conjunct; `GAP.md` §3.4 records why that is not
done. -/
def AllPosJ (δ : LSub) (σ : LStack) (c : Lifetime.Life)
    (P : LSub → List Life → List SRec → Life → WProp) (αs : List Life) (ls : List SRec) : WProp :=
  fun ρ => ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwSL (extS δ σ αs) σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ ι, InstAt αs ι → RecsOutside (ι.life αs) (ι.recs ls) →
      (vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) (ι.recs ls) ─⋆
        fun ρ' => ∀ α, (⌜LtLife (extS (ι.sub δ) σ (ι.life αs)) c α⌝ ─⋆
          P (ι.sub δ) (ι.life αs) (ι.recs ls) α) ρ') ρz

/-- **At `σ = []` the position-`∀` is Core's clause**: the empty stack has no cut, so the only
instantiation is the identity, and there are no views. Both directions. -/
def AllPosJNil : Prop :=
  ∀ (δ : LSub) (c : Lifetime.Life) (P : LSub → List Life → List SRec → Life → WProp)
    (ls : List SRec) (ρ : WRes),
    AllPosJ δ [] c P [] ls ρ ↔ ∀ α, (⌜LtLife δ c α⌝ ─⋆ P δ [] ls α) ρ

/-- **The position-`∀` implies the ℕ-`∀` at the stack itself** (the identity instantiation, the
views handed back as they were). The `∀E` row reads this. -/
def AllPosJSelf : Prop :=
  ∀ (δ : LSub) (σ : LStack) (c : Lifetime.Life) (P : LSub → List Life → List SRec → Life → WProp)
    (αs : List Life) (ls : List SRec) (ρ : WRes), StackOK σ αs → RecsOutside αs ls →
    AllPosJ δ σ c P αs ls ρ → ∀ α, (⌜LtLife (extS δ σ αs) c α⌝ ─⋆ P δ αs ls α) ρ

/-- **The position-`∀` is carried along an instantiation, by transport**: a cut of the
instantiated index is the image of a cut of the index, and a realisation of it there is a
realisation at the composite instantiation (`instComp`). The views are the ones the clause drops,
handed back at the instantiated stack. -/
def AllPosJTransport : Prop :=
  ∀ (δ : LSub) (σ : LStack) (c : Lifetime.Life) (P : LSub → List Life → List SRec → Life → WProp)
    (αs : List Life) (ls : List SRec) (ρ : WRes), StackOK σ αs → AllPosJ δ σ c P αs ls ρ →
    ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwSL (extS δ σ αs) σ ds αs ls ρn ∧ stratS αs ρz ∧
      ∀ ι, InstAt αs ι → RecsOutside (ι.life αs) (ι.recs ls) →
        (vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) (ι.recs ls) ─⋆
          AllPosJ (ι.sub δ) σ c P (ι.life αs) (ι.recs ls)) ρz

/-! #### Reading (A), and the witness at Core -/

/-- `∀'0 ⊏ ⊤. F (Mut '0 1)`. -/
abbrev adjC : CTy := .all 0 .top (.ret (.mut (.var 0) .unit))

/-- `Λ. return ℓ₀`, the place `0`. -/
abbrev adjE : Expr := .val (.lam (.val (Val.loc 0)))

/-- The empty reading. -/
abbrev adjδ : LSub := ⟨[]⟩

/-- The re-stratification `n ↦ n + 1` below `⊤`. -/
abbrev adjθ : Restrat.Emb (⊤ : Life) := Restrat.Emb.shift ⊤ 1

/-- **The full position-`∀` around Core's relation**, reading (A): Core's relation at every
renaming of the configuration by an embedding fixing `⊤`: the reading by `mapN`, the records by
`srecRestrat`, the resource by `relRU`, which moves every cell and a `mut` cell's stored predicate
to its image. At `C = ∀'x ⊏ c. C'` it reads `C'` at every position of the whole order of lifetimes
in play, external ones included, each realised at a renaming that leaves room there. -/
def CutAllC (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) : WProp := fun ρ =>
  ∀ φ : Restrat.Emb (⊤ : Life),
    cC C (ls.map (Targets.srecRestrat φ)) (Restrat.LSub.mapN φ.toNat δ) e (φ.relRU ρ)

/-- **Reading (A) implies Core's clause at `σ = []`**: the identity renaming. -/
def CutAllNilSound : Prop :=
  ∀ (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes),
    CutAllC (ℍ := ℍ) C ls δ e ρ → cC (ℍ := ℍ) C ls δ e ρ

/-- **Core's `∀` distinguishes two configurations of one order type**: the clause holds at a `mut`
cell at `1`, adjacent to `⊤`, and fails at a `mut` cell at `2`. -/
def CoreAllAdjacent : Prop :=
  cC (ℍ := ℍ) adjC [] adjδ adjE (innerView 0 (lifeN 1)) ∧
    ¬ cC (ℍ := ℍ) adjC [] adjδ adjE (innerView 0 (lifeN 2))

/-- **Core's relation is not invariant under an embedding that opens a gap**: it holds at a
configuration and fails at its image under `shift ⊤ 1`, the reading, the records and the resource
moved together. -/
def CoreAllNotNatural : Prop :=
  ∃ (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes),
    cC (ℍ := ℍ) C ls δ e ρ ∧
      ¬ cC (ℍ := ℍ) C (ls.map (Targets.srecRestrat adjθ)) (Restrat.LSub.mapN adjθ.toNat δ) e
        (adjθ.relRU ρ)

/-- **Core's `∀` does not imply reading (A) at `σ = []`.** -/
def NotCoreAllImpCutAll : Prop :=
  ¬ ∀ (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes),
      cC (ℍ := ℍ) C ls δ e ρ → CutAllC (ℍ := ℍ) C ls δ e ρ

/-! ### §4 R1: a `μ` slot read by Core's relation -/

/-- `μX. U(∀'0 ⊏ ⊤. F (Mut '0 1))`, `X` unused. -/
abbrev muAdjTy : VTy := .mu (.thunk adjC)

/-- A 6.65 entry: the place `0` lent, the variable `1`, the payload `1`. -/
abbrev muEnt : LEnt := ⟨0, 1, .unit, .mut, fun _ => true⟩

abbrev muΓ : Ctx VTy := [⟨muAdjTy, true⟩]

/-- The slot's value: the closure `Λ. return ℓ₀`. -/
abbrev muγ : List Val := [Val.lam (.val (Val.loc 0))]

/-- **The configuration meets the thaw's hypotheses**: the stack `[muEnt]` at `1`, so its cut is
`⊤`; the resource the entry's view `0 ↦ mut(1, (), ∅, 𝒱⟦1⟧)`; the slot related by Core's
relation, whose `∀` holds there because `1` is adjacent to `⊤` (`adj_holds`). -/
def MuSlotIndex : Prop :=
  StackOK [muEnt] [lifeN 1] ∧ OuterBelowTop [lifeN 1] ∧ SubDom adjδ LifeCtx.empty ∧
    LifeCtx.empty.Models (extS adjδ [muEnt] [lifeN 1]) ∧ RecsOutside [lifeN 1] [] ∧
    SubOutside [muEnt] [lifeN 1] adjδ ∧ TabAtS [muEnt] [lifeN 1] (innerView 0 (lifeN 1)) ∧
    PlaceViewsL (extS adjδ [muEnt] [lifeN 1]) [muEnt] [lifeN 1] [] (innerView 0 (lifeN 1)) ∧
    gRLJ .binder0 [muEnt] adjδ [lifeN 1] [] muΓ muγ (innerView 0 (lifeN 1))

/-- **The thaw at a `μ` slot fails at that configuration** (R1 through Core's relation): at the
instantiation `shift ⊤ 1` the entry's view is handed back at `2`, and Core's `∀` inside the slot
then meets `α = 1`, in the gap. Stated, not attempted; a refutation of a statement of ours, which
counts against no route until DESIGN §11's arising check passes. -/
def NotMuSlotThawCore : Prop := ¬ CtxRelendableAtJ (ℍ := ℍ) .binder0 LifeCtx.empty muΓ

end ProbeD1

end
