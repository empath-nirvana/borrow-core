import Restrat
import Targets.Base.Machine

/-!
# System B — the freeze binder's machine half (DESIGN §2 D11, §5 I2.c)

The location action on terms, values,
contexts and heaps (`Expr.renameLoc`, `Val.renameLoc`, `Kont.renameLoc`, `Heap.renameLoc`, local
copies of TwoRun's, which does not build on this branch); the blocks a configuration's arrays name
(`Ranges`, `BlockAffine`, `arrRanges`, `RangesIn`, `StepsIn`); and `BinderMachine` (a run whose
arrays lie in blocks a permutation moves as blocks renames to a run).  The world half is the
interaction's (`Targets/I/Binder.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `e` with every location `ℓ` replaced by `π ℓ` (`TwoRun`'s `Expr.rename` at a permutation). -/
def _root_.BoCa.Expr.renameLoc (π : Equiv.Perm Loc) : Expr → Expr
  | .var i         => .var i
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (e₁.renameLoc π) (e₂.renameLoc π)
  | .inj₁ e        => .inj₁ (e.renameLoc π)
  | .inj₂ e        => .inj₂ (e.renameLoc π)
  | .lam b         => .lam (b.renameLoc π)
  | .loc ℓ         => .loc (π ℓ)
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (e₁.renameLoc π) (e₂.renameLoc π)
  | .letpair e₁ e₂ => .letpair (e₁.renameLoc π) (e₂.renameLoc π)
  | .case e e₁ e₂  => .case (e.renameLoc π) (e₁.renameLoc π) (e₂.renameLoc π)
  | .app f a       => .app (f.renameLoc π) (a.renameLoc π)

theorem isVal_renameLoc (π : Equiv.Perm Loc) {e : Expr} (h : IsVal e) : IsVal (e.renameLoc π) := by
  induction h with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | lam => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | storeV _ ih => exact .storeV ih

/-- `v` with every location `ℓ` replaced by `π ℓ`. -/
def _root_.BoCa.Val.renameLoc (π : Equiv.Perm Loc) (v : Val) : Val :=
  ⟨v.1.renameLoc π, isVal_renameLoc π v.2⟩

/-- `K` with every location `ℓ` replaced by `π ℓ` (`TwoRun`'s `Kont.rename`). -/
def _root_.BoCa.BoLo.Kont.renameLoc (π : Equiv.Perm Loc) : Kont → Kont
  | .hole          => .hole
  | .pairL K e     => .pairL (K.renameLoc π) (e.renameLoc π)
  | .pairR v K     => .pairR (v.renameLoc π) (K.renameLoc π)
  | .letpair K e   => .letpair (K.renameLoc π) (e.renameLoc π)
  | .case K e₁ e₂  => .case (K.renameLoc π) (e₁.renameLoc π) (e₂.renameLoc π)
  | .appR f K      => .appR (f.renameLoc π) (K.renameLoc π)
  | .appL K v      => .appL (K.renameLoc π) (v.renameLoc π)
  | .seq K e       => .seq (K.renameLoc π) (e.renameLoc π)
  | .inj₁ K        => .inj₁ (K.renameLoc π)
  | .inj₂ K        => .inj₂ (K.renameLoc π)

/-- The cell at `ℓ` moved to `π ℓ`, its value renamed (`TwoRun`'s `Heap.rename`). -/
def _root_.BoCa.BoLo.Heap.renameLoc (π : Equiv.Perm Loc) (μ : Heap) : Heap :=
  fun ℓ => (μ (π.symm ℓ)).map (Val.renameLoc π)

/-- A set of ranges `(ℓ, n)`, each the block `[ℓ, ℓ + n)`. -/
abbrev Ranges := Loc × Nat → Prop

/-- `π` moves each range of `rs` as a block. -/
def BlockAffine (π : Equiv.Perm Loc) (rs : Ranges) : Prop :=
  ∀ p, rs p → ∀ j, j < p.2 → π (p.1 + j) = π p.1 + j

/-- The ranges of the array values `Val.arr ℓ n` occurring in a term (under binders too). -/
def _root_.BoCa.Expr.arrRanges : Expr → Ranges
  | .pair (.loc ℓ) (.prim (.lit (.i32 n))), q => q = (ℓ, n.toNat)
  | .pair a b, q | .seq a b, q | .letpair a b, q | .app a b, q => a.arrRanges q ∨ b.arrRanges q
  | .inj₁ a, q | .inj₂ a, q | .lam a, q => a.arrRanges q
  | .case a b c, q => a.arrRanges q ∨ b.arrRanges q ∨ c.arrRanges q
  | _, _ => False

/-- In a heap: in a stored value. -/
def _root_.BoCa.BoLo.Heap.arrRanges (μ : Heap) : Ranges :=
  fun q => ∃ m v, μ m = some v ∧ v.1.arrRanges q

/-- In a context: in a term or value of one of its frames. -/
def _root_.BoCa.BoLo.Kont.arrRanges : Kont → Ranges
  | .hole, _ => False
  | .pairL K e, q | .letpair K e, q | .seq K e, q => K.arrRanges q ∨ e.arrRanges q
  | .pairR v K, q | .appL K v, q => K.arrRanges q ∨ v.1.arrRanges q
  | .case K e₁ e₂, q => K.arrRanges q ∨ e₁.arrRanges q ∨ e₂.arrRanges q
  | .appR f K, q => f.arrRanges q ∨ K.arrRanges q
  | .inj₁ K, q | .inj₂ K, q => K.arrRanges q

/-- A configuration every array of which lies within the ranges `rs`. -/
def RangesIn (rs : Ranges) (μ : Heap) (e : Expr) : Prop :=
  ∀ q, (e.arrRanges q ∨ μ.arrRanges q) → ∃ p, rs p ∧ p.1 ≤ q.1 ∧ q.1 + q.2 ≤ p.1 + p.2

/-- A run every configuration of which names arrays only within the ranges `rs`. -/
inductive StepsIn (rs : Ranges) : Heap → Expr → Heap → Expr → Prop
  | refl (μ : Heap) (e : Expr) : RangesIn rs μ e → StepsIn rs μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr} : RangesIn rs μ e → Step1 (ℍ := ℍ) μ e μ₁ e₁ →
      StepsIn rs μ₁ e₁ μ' e' → StepsIn rs μ e μ' e'


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The binder, location half, machine**: a run whose arrays lie in blocks `π` moves as blocks
renames to a run. -/
def BinderMachine : Prop :=
  ∀ (π : Equiv.Perm Loc) (rs : Ranges) μ e μ' e', BlockAffine π rs →
    StepsIn (ℍ := ℍ) rs μ e μ' e' →
    StepsIn (ℍ := ℍ) (fun q => ∃ p, rs p ∧ q = (π p.1, p.2)) (μ.renameLoc π) (e.renameLoc π)
      (μ'.renameLoc π) (e'.renameLoc π)

end Targets

end
