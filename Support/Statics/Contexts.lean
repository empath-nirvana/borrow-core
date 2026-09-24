/-!
# Support — Statics — Contexts

`[about ours]`.  Typing contexts as lists of slots with a liveness bit, and their splitting.
-/

noncomputable section

namespace BoCa

structure Slot (τ : Type) where
  ty   : τ
  live : Bool
  deriving Repr, DecidableEq, Inhabited

abbrev Ctx (τ : Type) := List (Slot τ)

/-- `Γ = Γ₁, Γ₂` — a partition of the live slots, positions preserved. -/
inductive Ctx.Split {τ : Type} : Ctx τ → Ctx τ → Ctx τ → Prop where
  | nil : Ctx.Split [] [] []
  | left  {Γ Γ₁ Γ₂ : Ctx τ} {T : τ} : Ctx.Split Γ Γ₁ Γ₂ →
      Ctx.Split (⟨T, true⟩ :: Γ) (⟨T, true⟩ :: Γ₁) (⟨T, false⟩ :: Γ₂)
  | right {Γ Γ₁ Γ₂ : Ctx τ} {T : τ} : Ctx.Split Γ Γ₁ Γ₂ →
      Ctx.Split (⟨T, true⟩ :: Γ) (⟨T, false⟩ :: Γ₁) (⟨T, true⟩ :: Γ₂)
  | dead  {Γ Γ₁ Γ₂ : Ctx τ} {T : τ} : Ctx.Split Γ Γ₁ Γ₂ →
      Ctx.Split (⟨T, false⟩ :: Γ) (⟨T, false⟩ :: Γ₁) (⟨T, false⟩ :: Γ₂)

end BoCa

end
