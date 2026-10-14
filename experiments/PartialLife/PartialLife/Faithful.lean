import PartialLife.Relation
import DenseCarrier.Faithful

/-!
# PartialLife — at `L = Life` and the identity reading, the relation is Core's

`vP Reading.id` and `cP Reading.id` are `DenseCarrier`'s `vD Slots.id` and `cD Slots.id` at every
type (`vP_eq_vD`, `cP_eq_cD`), and so Core's `vC true` and `cC` at every type of the fragment
(`vP_id`, `cP_id`, through `DenseCarrier.vD_id`, `cD_id`). `Life` is a chain, so its least upper and
greatest lower bounds always exist and are `⊔`, `⊓` (`interpP_life`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace PartialLife
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open DenseCarrier (LSubD FragV FragC Slots interpD atLifeD LtLifeD InStratumD OutlivesD boxD
  ptoMutD vD cD toLSub)

/-- At `Life` the reading of a lifetime term is `DenseCarrier`'s. -/
theorem interpP_life (δ : LSubD Life) : ∀ a : Lifetime.Life, interpP δ a = interpD δ a := by
  intro a
  induction a with
  | var y => rfl
  | top => rfl
  | join p q ihp ihq =>
      simp only [interpP, interpD, ihp, ihq]
      cases interpD δ p <;> cases interpD δ q <;> simp [lubOpt_eq]
  | meet p q ihp ihq =>
      simp only [interpP, interpD, ihp, ihq]
      cases interpD δ p <;> cases interpD δ q <;> simp [glbOpt_eq]

theorem atLifeP_life (δ : LSubD Life) (a : Lifetime.Life) (F : Life → WProp) :
    atLifeP δ a F = atLifeD δ a F := by
  funext ρ
  simp only [atLifeP, atLifeD, interpP_life]

theorem ltLifeP_life (δ : LSubD Life) (b : Lifetime.Life) (α : Life) :
    LtLifeP δ b α ↔ LtLifeD δ b α := by
  simp only [LtLifeP, LtLifeD, interpP_life]

theorem boxP_id (α : Life) (P : WProp) : boxP Reading.id α P = boxD Slots.id α P := by
  funext ρ
  refine propext (and_congr_right fun _ => ?_)
  exact forall_congr' fun _ => forall_congr' fun ψ => imp_congr_right fun _ => by
    cases ψ <;> exact Iff.rfl

theorem ptoMutP_id (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) :
    ptoMutP Reading.id l α ls P = ptoMutD Slots.id l α ls P := rfl

mutual
/-- **At `Life` and the identity reading the value relation is `DenseCarrier`'s**, at every type. -/
theorem vP_eq_vD : ∀ (A : VTy) (ls : List SRec) (δ : LSubD Life),
    vP (ℍ := ℍ) Reading.id A ls δ = vD (ℍ := ℍ) Slots.id A ls δ
  | .unit, _, _ => rfl
  | .tensor A B, ls, δ => by
      funext v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vP (ℍ := ℍ) Reading.id A ls δ v₁ ⋆ vP (ℍ := ℍ) Reading.id B ls δ v₂) =
        (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vD (ℍ := ℍ) Slots.id A ls δ v₁ ⋆ vD (ℍ := ℍ) Slots.id B ls δ v₂)
      simp only [vP_eq_vD A ls δ, vP_eq_vD B ls δ]
  | .thunk C, ls, δ => by
      funext v ρ
      show (∀ ls', Ext ls ls' ρ → cP (ℍ := ℍ) Reading.id C ls' δ (forceE C (.val v)) ρ) =
        (∀ ls', Ext ls ls' ρ → cD (ℍ := ℍ) Slots.id C ls' δ (forceE C (.val v)) ρ)
      simp only [cP_eq_cD C]
  | .ref A, ls, δ => by
      funext v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆
          vP (ℍ := ℍ) Reading.id A ls δ v') =
        (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vD (ℍ := ℍ) Slots.id A ls δ v')
      simp only [vP_eq_vD A ls δ]
  | .box a A, ls, δ => by
      funext v
      show atLifeP δ a (fun α => boxP Reading.id α (vP (ℍ := ℍ) Reading.id A ls δ v)) =
        atLifeD δ a (fun α => boxD Slots.id α (vD (ℍ := ℍ) Slots.id A ls δ v))
      rw [atLifeP_life, vP_eq_vD A ls δ]
      simp only [boxP_id]
  | .mut a A, ls, δ => by
      funext v
      show atLifeP δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutP Reading.id ℓ α ls (fun ls₀ => vP (ℍ := ℍ) Reading.id A ls₀ δ)) =
        atLifeD δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutD Slots.id ℓ α ls (fun ls₀ => vD (ℍ := ℍ) Slots.id A ls₀ δ))
      rw [atLifeP_life]
      simp only [ptoMutP_id, vP_eq_vD A]
  | .zero, _, _ | .sum _ _, _, _ | .imm _ _, _, _ | .bang _, _, _ | .unk, _, _
  | .tvar _, _, _ | .mu _, _, _ | .int _, _, _ | .fam _, _, _ | .opq _, _, _ => rfl

/-- **At `Life` and the identity reading the computation relation is `DenseCarrier`'s.** -/
theorem cP_eq_cD : ∀ (C : CTy) (ls : List SRec) (δ : LSubD Life) (e : Expr),
    cP (ℍ := ℍ) Reading.id C ls δ e = cD (ℍ := ℍ) Slots.id C ls δ e
  | .ret A, ls, δ, e => by
      show wpTS ls e (fun ls'' => vP (ℍ := ℍ) Reading.id A ls'' δ) =
        wpTS ls e (fun ls'' => vD (ℍ := ℍ) Slots.id A ls'' δ)
      simp only [vP_eq_vD]
  | .arr A C, ls, δ, e => by
      funext ρ
      show (∀ v, (vP (ℍ := ℍ) Reading.id A ls δ v ─⋆
          cP (ℍ := ℍ) Reading.id C ls δ (.app e (.val v))) ρ) =
        (∀ v, (vD (ℍ := ℍ) Slots.id A ls δ v ─⋆ cD (ℍ := ℍ) Slots.id C ls δ (.app e (.val v))) ρ)
      simp only [vP_eq_vD, cP_eq_cD C]
  | .top, _, _, _ => rfl
  | .all x c C, ls, δ, e => by
      funext ρ
      show (∀ α : Life, (⌜LtLifeP δ c α⌝ ─⋆
          cP (ℍ := ℍ) Reading.id C ls (δ.extend x α) (.app e (.val .unit))) ρ) =
        (∀ α : Life, (⌜LtLifeD δ c α⌝ ─⋆
          cD (ℍ := ℍ) Slots.id C ls (δ.extend x α) (.app e (.val .unit))) ρ)
      apply propext
      refine forall_congr' fun α => ?_
      rw [cP_eq_cD C ls (δ.extend x α)]
      simp only [ltLifeP_life]
  | .amp _ _, _, _, _ | .nu _, _, _, _ | .eff _ _ _ _ _ _ _, _, _, _ => rfl
end

/-- **At `Life` and the identity reading the value relation is Core's**, at every fragment type. -/
theorem vP_id (A : VTy) (hA : FragV A) (ls : List SRec) (δ : LSubD Life) :
    vP (ℍ := ℍ) Reading.id A ls δ = vC true A ls (toLSub δ) := by
  rw [vP_eq_vD]; exact DenseCarrier.vD_id A hA ls δ

/-- **At `Life` and the identity reading the computation relation is Core's**, at every fragment
type. -/
theorem cP_id (C : CTy) (hC : FragC C) (ls : List SRec) (δ : LSubD Life) (e : Expr) :
    cP (ℍ := ℍ) Reading.id C ls δ e = cC (ℍ := ℍ) C ls (toLSub δ) e := by
  rw [cP_eq_cD]; exact DenseCarrier.cD_id C hC ls δ e

end PartialLife

end
