import Support.Model.Tree.Port.Six49to52

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Paper/S6_2_NonStandardLemmas/Lemmas.lean:1790-1850`, `Paper/S6_2_NonStandardLemmas/Lemmas.lean:1918-1943`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.43 · `[TR]` p. 15 · `proved`

> ℓ ↦ imm(α ∪ β, v, ρ′) = ℓ ↦ imm(α, v, ρ′) ● ℓ ↦ imm(β, v, ρ′)

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.Tree.ResUT.compS_single_imm`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.43 (p. 15).  `[as printed]` -/
theorem ResUT.compS_single_imm (l : Loc) (s t : TSet) (v : Val) (ρ' : ResUT Loc Val K)
    (h : ρ'.InStratum s) (h' : ρ'.InStratum t)
    (h'' : ρ'.InStratum (s ∪ t)) :
    ResUT.CompS (ResUT.single l (CellUT.immOf s v ρ' h))
      (ResUT.single l (CellUT.immOf t v ρ' h'))
      (ResUT.single l (CellUT.immOf (s ∪ t) v ρ' h'')) := by
  classical
  constructor
  · intro l' ψ₁ ψ₂ e₁ e₂
    obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e₁
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₂
    exact ⟨s, t, v, ρ', h, h', rfl, rfl⟩
  · intro l'
    by_cases e : l' = l
    · subst e
      rw [ResUT.single_get_self, ResUT.single_get_self, ResUT.single_get_self]
      exact ⟨_, rfl, ⟨s, t, v, ρ', h, h', h'', rfl, rfl, rfl⟩⟩
    · rw [ResUT.single_get_ne _ e, ResUT.single_get_ne _ e, ResUT.single_get_ne _ e]
      rfl

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.44 · `[TR]` p. 16 · `proved`

> If ℓ ↦ imm(α, v₁, ρ′₁) ▸◂ ℓ ↦ imm(β, v₂, ρ′₂), then v₁ = v₂ and ρ′₁ = ρ′₂.

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.Tree.ResUT.compatS_single_imm_inv`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.44 (p. 16).  `[as printed]` -/
theorem ResUT.compatS_single_imm_inv {l : Loc} {s t : TSet} {v₁ v₂ : Val}
    {ρ₁ ρ₂ : ResUT Loc Val K} {h₁ : ρ₁.InStratum s} {h₂ : ρ₂.InStratum t}
    (h : ResUT.CompatS (ResUT.single l (CellUT.immOf s v₁ ρ₁ h₁))
      (ResUT.single l (CellUT.immOf t v₂ ρ₂ h₂))) : v₁ = v₂ ∧ ρ₁ = ρ₂ := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, e₁, e₂⟩ :=
    h l _ _ (ResUT.single_get_self _ _) (ResUT.single_get_self _ _)
  obtain ⟨-, hv₁, hρ₁⟩ := CellUT.immOf_inj e₁
  obtain ⟨-, hv₂, hρ₂⟩ := CellUT.immOf_inj e₂
  exact ⟨hv₁.trans hv₂.symm, hρ₁.trans hρ₂.symm⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree.BoLo
open BoCa.Fig16 BoCa.Fig16.Tree
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.46 · `[TR]` p. 16 · `proved`

> ρ₁ # ρ₂ ● ρ₃ if and only if ρ₁ ● ρ₂ # ρ₃.

**Printed proof, transcribed.** By unfolding `#` and Lemma 6.3.

**Lean.** `BoCa.Fig16.Tree.BoLo.hash_shift`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.46 (p. 16).  `[as printed]` (G4) -/
theorem hash_shift (ρ₁ ρ₂ ρ₃ : (ResUT BoCa.Loc BoCa.Val K)) :
    (∃ x, ResUT.CompS ρ₂ ρ₃ x ∧ ResUT.Hash ρ₁ x) ↔
    (∃ y, ResUT.CompS ρ₁ ρ₂ y ∧ ResUT.Hash y ρ₃) := by
  constructor
  · rintro ⟨x, hx, -, w, hw, hv⟩
    obtain ⟨y, hy, hyw⟩ := (ResUT.CompS.assoc ρ₁ ρ₂ ρ₃ w).mp ⟨x, hx, hw⟩
    exact ⟨y, hy, hyw.1, w, hyw, hv⟩
  · rintro ⟨y, hy, -, w, hw, hv⟩
    obtain ⟨x, hx, hxw⟩ := (ResUT.CompS.assoc ρ₁ ρ₂ ρ₃ w).mpr ⟨y, hy, hw⟩
    exact ⟨x, hx, hxw.1, w, hxw, hv⟩

end BoCa.Fig16.Tree.BoLo

end
