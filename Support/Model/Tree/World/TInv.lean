import Support.Model.Tree.World.Images

/-!
# The typed world's invariant over the tree: `TIT`

`Core/Invariant.lean`'s `TI` and `Core/Images.lean`'s `ChainInv`, read over the tree carrier
with records at codes (`TreeWp/Records.lean`): `vShape T δ` is `T.interp Θ` read at `K`, `⊏` is
`K.lt`, `s.mem x` is `x ∈ s.set`. Definitions only.

`TWNT.InvHolds` is `TWN.inv`'s statement (`SI/TWN.lean`) over `TWNT`: every `TWNT` world
satisfies `TIT`. It is proved in `TreeWp/TInvHolds.lean` (`twnt_invHolds`), from the port of
`TWN.inv` and of `Core/Invariant.lean`'s preservation lemmas (`ti_frame`, `ti_reb`,
`ti_rebDeepN`, `ti_mutFold`, `ti_end`, `ti_endRebN`, `ti_of_ag`), with one case beyond them,
`reread` (`TreeWp/TInvReread.lean`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-- A root of a record: `ℓ ↦ own(u)` in the escrow at a `RefPos` of the recorded `(T, v)`. -/
def RootT (r : FrameRecT K) (S : KTy) (l : BoCa.Loc) (u : BoCa.Val) : Prop :=
  RefPosT r.T r.v l S ∧ r.R.get l = some (CellUT.ownOf u)

/-- `DeepInv`: every non-`own` view of `ag(W)` at a chain position is an `imm` view over a
typed piece of the escrow. -/
def DeepInvT (K : WCactus) (Θ : CodeTy) (W : TRes K) (r : FrameRecT K) : Prop :=
  ∀ p l S u, ChainT r.R r.T r.v p l S u → ∀ a, AgWT W a → ∀ ψ : TCell K,
    a.get l = some ψ → ψ.kind ≠ Kind.own →
    ψ.kind = Kind.imm ∧ (S.interp Θ).P K u ψ.wit ∧
    (∀ m w, ψ.wit.get m = some (CellUT.ownOf w) → r.R.get m = some (CellUT.ownOf w)) ∧
    (p = none → ∃ q, ResUT.Le q r.R ∧ (∃ ζ, q.get l = some ζ) ∧ ψ.wit = q.del l) ∧
    (∀ l₀, p = some l₀ → ∃ ψ₀ : TCell K, a.get l₀ = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧
       ∃ q, ResUT.Le q ψ₀.wit ∧ (∃ ζ, q.get l = some ζ) ∧ ψ.wit = q.del l)

/-- `JointAt`: the views at a record's roots come from one typed reborrow of the escrow. -/
def JointAtT (K : WCactus) (Θ : CodeTy) (W : TRes K) (r : FrameRecT K) : Prop :=
  (∃ S l u, RootT r S l u ∧ ∃ a, AgWT W a ∧ ∃ ψ : TCell K, a.get l = some ψ ∧
      ψ.kind ≠ Kind.own) →
  ∃ (β₀ : Life) (c₀ : TRes K), ResUT.Reb β₀ r.R c₀ ∧
    ((r.T.immReborrow β₀).interp Θ).P K r.v c₀ ∧ (∃ A, AgWT c₀ A) ∧
    ∀ S l u, RootT r S l u → ∀ a, AgWT W a → ∀ ψ : TCell K, a.get l = some ψ →
      ψ.kind ≠ Kind.own → ∃ ζ, c₀.get l = some ζ ∧ ψ.wit = ζ.wit

/-- `JointDeep`: the views at a chain position's children come from one typed reborrow of the
view at the position. -/
def JointDeepT (K : WCactus) (Θ : CodeTy) (W : TRes K) (r : FrameRecT K) : Prop :=
  ∀ p₀ l₀ S₀ u₀, ChainT r.R r.T r.v p₀ l₀ S₀ u₀ →
  (∃ l S u, ChainT r.R r.T r.v (some l₀) l S u ∧ ∃ a, AgWT W a ∧ ∃ ψ : TCell K,
      a.get l = some ψ ∧ ψ.kind ≠ Kind.own) →
  ∃ w₀ : TRes K, (∀ a, AgWT W a → ∃ ψ₀ : TCell K, a.get l₀ = some ψ₀ ∧
      ψ₀.kind ≠ Kind.own ∧ ψ₀.wit = w₀) ∧
    ∃ (β₀ : Life) (c₀ : TRes K), ResUT.Reb β₀ w₀ c₀ ∧
      ((S₀.immReborrow β₀).interp Θ).P K u₀ c₀ ∧ (∃ A, AgWT c₀ A) ∧
      ∀ l S u, ChainT r.R r.T r.v (some l₀) l S u → ∀ a, AgWT W a → ∀ ψ : TCell K,
        a.get l = some ψ → ψ.kind ≠ Kind.own → ∃ ζ, c₀.get l = some ζ ∧ ψ.wit = ζ.wit

/-- `ChainInv` over the tree. -/
def ChainInvT (K : WCactus) (Θ : CodeTy) (W : TRes K) (rs : List (FrameRecT K)) : Prop :=
  (∀ r ∈ rs, DeepInvT K Θ W r) ∧
  (∀ r ∈ rs, ∀ l u, r.R.get l = some (CellUT.ownOf u) → ∀ a, AgWT W a →
    ∃ ζ : TCell K, a.get l = some ζ) ∧
  (∀ r₁ ∈ rs, ∀ r₂ ∈ rs, ∀ l u₁ u₂, r₁.R.get l = some (CellUT.ownOf u₁) →
     r₂.R.get l = some (CellUT.ownOf u₂) → r₁ = r₂) ∧
  (∀ r ∈ rs, (r.T.interp Θ).P K r.v r.R) ∧
  (∀ r ∈ rs, JointAtT K Θ W r) ∧
  (∀ r ∈ rs, JointDeepT K Θ W r)

/-- `LeInv`: each record's cell is an `imm` view of `ag(W)` over the recorded value and
escrow. -/
def LeInvT (W : TRes K) (rs : List (FrameRecT K)) : Prop :=
  ∀ r ∈ rs, ∀ a, AgWT W a → ∃ ψ : TCell K, a.get r.le = some ψ ∧ ψ.kind = Kind.imm ∧
    ψ.erase = r.v ∧ ψ.wit = r.R

/-- `NestLife` read in `K`. -/
def NestLifeT (K : WCactus) (W : TRes K) (r : FrameRecT K) : Prop :=
  ∀ l₀ l S u, ChainT r.R r.T r.v (some l₀) l S u → ∀ a, AgWT W a → ∀ (ψ : TCell K) s,
    a.get l = some ψ → ψ.lsOfI = some s → ∀ x ∈ s.set,
    ∃ (ζ : TCell K) (t : TSet) (y : Life), a.get l₀ = some ζ ∧ ζ.lsOfI = some t ∧
      y ∈ t.set ∧ K.lt x y

/-- `MutAt`: a `mut` cell at `ℓ` sits in `ρ`, at the top or inside the witness of a non-`own`
cell. -/
inductive MutAtT : TRes K → BoCa.Loc → Prop
  | top {ρ : TRes K} {l : BoCa.Loc} {ψ : TCell K} :
      ρ.get l = some ψ → ψ.kind = Kind.mut → MutAtT ρ l
  | nest {ρ : TRes K} {l m : BoCa.Loc} {ψ : TCell K} :
      ρ.get m = some ψ → ψ.kind ≠ Kind.own → MutAtT ψ.wit l → MutAtT ρ l

/-- `NoMut` over the tree. -/
def NoMutT (W : TRes K) (ps rs : List (FrameRecT K)) : Prop :=
  (∀ r ∈ ps, ¬ MutAtT W r.le) ∧
  (∀ r ∈ rs, ∀ l u, r.R.get l = some (CellUT.ownOf u) → ¬ MutAtT W l)

/-- `Class` over the tree. -/
def ClassT (rs : List (FrameRecT K)) (m : BoCa.Loc) (ψ : TCell K) : Prop :=
  (∃ r ∈ rs, m = r.le ∧ ψ.erase = r.v ∧ ψ.wit = r.R) ∨
  (∃ r ∈ rs, ∃ p S u, ChainT r.R r.T r.v p m S u)

/-- `Coverage` over the tree. -/
def CoverageT (W : TRes K) (rs : List (FrameRecT K)) : Prop :=
  ∀ a, AgWT W a → ∀ m (ψ : TCell K), a.get m = some ψ → ψ.kind = Kind.imm → ClassT rs m ψ

/-- **`TI` over the tree.** -/
def TIT (K : WCactus) (Θ : CodeTy) (W : TRes K) (ps rs : List (FrameRecT K)) : Prop :=
  ChainInvT K Θ W rs ∧ LeInvT W ps ∧ (∀ r₁ ∈ ps, ∀ r₂ ∈ ps, r₁.le = r₂.le → r₁ = r₂) ∧
  (∀ r ∈ rs, ∀ r' ∈ rs, ∀ u, r'.R.get r.le ≠ some (CellUT.ownOf u)) ∧
  (∀ r ∈ rs, NestLifeT K W r) ∧ NoMutT W ps rs ∧
  (∀ x, x ∈ rs ↔ ∃ p ∈ ps, DescRT p x) ∧ CoverageT W rs

/-- **`TWN.inv`'s statement over `TWNT`**: every world of the typed world over the tree satisfies
`TIT` (`twnt_invHolds`, `TreeWp/TInvHolds.lean`). -/
def TWNT.InvHolds : Prop :=
  ∀ (K : WCactus) (Θ : CodeTy) (tc : TChoice K) (W : TRes K) (ps rs : List (FrameRecT K)),
    TWNT K Θ tc W ps rs → TIT K Θ W ps rs

end BoCa.Fig16.Tree.Wp

end
