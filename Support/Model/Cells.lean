import Paper.S5_Model.Definitions

/-!
# Support — Model — Cells

`[about ours]`.  Facts about cells: the lifetime set of an `imm` cell, extensionality of `mut` cells, the constructor set of `Cell`, and the difference of lifetime sets.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The lifetime set of an `imm` cell. -/
def CellU.lsOf : CellU Loc Val → Option LSet
  | .imm i => some i.ls
  | _ => none

@[simp] theorem CellU.lsOf_immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : CellU.lsOf (CellU.immOf s v ρ h) = some s := rfl

@[simp] theorem CellU.lsOf_ownOf (v : Val) :
    CellU.lsOf (CellU.ownOf (Loc := Loc) v) = none := rfl

@[simp] theorem CellU.lsOf_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum b) (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    CellU.lsOf (CellU.mutOf b v ρ h P hw) = none := rfl

theorem MutU.ext {m n : MutU Loc Val} (hb : m.β = n.β) (hv : m.v = n.v)
    (hρ : m.ρ ≍ n.ρ) (hP : m.P ≍ n.P) : m = n := by
  obtain ⟨b₁, v₁, ρ₁, P₁, w₁⟩ := m
  obtain ⟨b₂, v₂, ρ₂, P₂, w₂⟩ := n
  simp only at hb hv hρ hP
  subst hb; subst hv
  simp only [heq_eq_eq] at hρ hP
  subst hρ; subst hP; rfl

/-- Every cell of `Cell` is an `own`, an `imm` or a `mut`. -/
theorem CellU.rep (ψ : CellU Loc Val) :
    (∃ v : Val, ψ = ownOf v) ∨
    (∃ (s : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum s.join),
        ψ = immOf s v ρ h) ∨
    (∃ (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
        (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩), ψ = mutOf b v ρ h P hw) := by
  cases ψ with
  | own v => exact Or.inl ⟨v, rfl⟩
  | imm i =>
      refine Or.inr (Or.inl ⟨i.ls, i.v, i.ρ.toU, i.ρ.toU_inStratum, ?_⟩)
      show CellU.imm i = CellU.imm _
      exact congrArg CellU.imm (ImmU.ext rfl rfl (by
        simp only [heq_eq_eq]
        exact (Res.toRes_toS i.ρ).symm))
  | «mut» m =>
      refine Or.inr (Or.inr ⟨m.β, m.v, m.ρ.toU, m.ρ.toU_inStratum,
        fun v r => m.P v r.toRes, ?_, ?_⟩)
      · show m.P m.v (ResS.toRes ⟨m.ρ.toU, m.ρ.toU_inStratum⟩)
        rw [show ResS.toRes ⟨m.ρ.toU, m.ρ.toU_inStratum⟩ = m.ρ from Res.toRes_toS m.ρ]
        exact m.hw
      · show CellU.mut m = CellU.mut _
        refine congrArg CellU.mut (MutU.ext rfl rfl ?_ ?_)
        · simp only [heq_eq_eq]; exact (Res.toRes_toS m.ρ).symm
        · simp only [heq_eq_eq]
          funext v r
          show m.P v r = m.P v r.toS.toRes
          rw [Res.toRes_toS]

end BoCa.Fig16

namespace BoCa.Fig16

/-- `ᾱ ∖ β̄ = γ̄`, as a graph: the difference may be empty, so it is not an
operation on `LSet`. -/
def LSet.Diff (s t u : LSet) : Prop := ∀ x, u.mem x ↔ (s.mem x ∧ ¬ t.mem x)

/-- `ᾱ ∖ β̄ = ∅`. -/
def LSet.DiffEmpty (s t : LSet) : Prop := ∀ x, s.mem x → t.mem x

end BoCa.Fig16

end
