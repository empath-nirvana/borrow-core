import DenseCarrier.Relation

/-!
# DenseCarrier — at `L = Life` and the identity slots, the relation is Core's

`vD Slots.id` and `cD Slots.id` agree with Core's `vC true` and `cC` at every type of the
fragment, every record list, reading and resource (`vD_id`, `cD_id`). The `δ` of Core is the
`ℕ`-valued `LSub`; `toLSub` reads an `LSubD Life` as one.

So the fragment is Core's relation with its lifetime order made a parameter: what `Gap.lean` and
`Shift.lean` prove at `L = Life` is a statement about Core.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx LSub)

/-- An `LSubD Life` as Core's `ℕ`-valued `LSub`. -/
def toLSub (δ : LSubD Life) : LSub := ⟨δ.entries.map fun p => (p.1, OrderDual.ofDual p.2)⟩

theorem toLSub_find? (δ : LSubD Life) (x : LifeVar) :
    (toLSub δ).find? x = (δ.find? x).map OrderDual.ofDual :=
  LSubD.assocFind_map (L := Life) OrderDual.ofDual x δ.entries

theorem toLSub_extend (δ : LSubD Life) (x : LifeVar) (α : Life) :
    toLSub (δ.extend x α) = (toLSub δ).extend x α := rfl

theorem interp_toLSub (δ : LSubD Life) :
    ∀ a : Lifetime.Life, a.interp (toLSub δ) = (interpD δ a).map OrderDual.ofDual := by
  intro a
  induction a with
  | var y => exact toLSub_find? δ y
  | top => rfl
  | join p q ihp ihq =>
      simp only [Lifetime.Life.interp, interpD, ihp, ihq]
      cases interpD δ p <;> cases interpD δ q <;> rfl
  | meet p q ihp ihq =>
      simp only [Lifetime.Life.interp, interpD, ihp, ihq]
      cases interpD δ p <;> cases interpD δ q <;> rfl

theorem atLife_toLSub (δ : LSubD Life) (a : Lifetime.Life) (F : Life → WProp) :
    atLife (toLSub δ) a F = atLifeD δ a F := by
  funext ρ
  simp only [atLife, atLifeD, interp_toLSub]
  apply propext
  constructor
  · rintro ⟨α, hα, hF⟩
    obtain ⟨β, hβ, rfl⟩ := Option.map_eq_some_iff.mp hα
    exact ⟨β, hβ, hF⟩
  · rintro ⟨α, hα, hF⟩
    exact ⟨α, by rw [hα]; rfl, hF⟩

theorem ltLife_toLSub (δ : LSubD Life) (b : Lifetime.Life) (α : Life) :
    LtLife (toLSub δ) b α ↔ LtLifeD δ b α := by
  simp only [LtLife, LtLifeD, interp_toLSub]
  constructor
  · rintro ⟨β, hβ, hlt⟩
    obtain ⟨γ, hγ, rfl⟩ := Option.map_eq_some_iff.mp hβ
    exact ⟨γ, hγ, hlt⟩
  · rintro ⟨β, hβ, hlt⟩
    exact ⟨β, by rw [hβ]; rfl, hlt⟩

theorem inStratumD_id (α : Life) (ψ : CellU Loc Val) : InStratumD Slots.id α ψ ↔ ψ.InStratum α := by
  cases ψ <;> exact Iff.rfl

theorem outlivesD_id (ρ : WRes) (α : Life) : OutlivesD Slots.id ρ α ↔ Outlives ρ α :=
  forall_congr' fun _ => forall_congr' fun ψ => imp_congr_right fun _ => inStratumD_id α ψ

theorem boxD_id (α : Life) (P : WProp) : boxD Slots.id α P = box α P := by
  funext ρ
  exact propext (and_congr_right fun _ => outlivesD_id ρ α)

theorem ptoMutD_id (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) :
    ptoMutD Slots.id l α ls P = ptoMutS l α ls P := rfl

/-- **At the identity slots the value relation is Core's**, at every fragment type. -/
theorem vD_id : ∀ (A : VTy), FragV A → ∀ (ls : List SRec) (δ : LSubD Life),
    vD Slots.id A ls δ = vC true A ls (toLSub δ)
  | .unit, _, _, _ => rfl
  | .box a A, hA, ls, δ => by
      funext v
      show atLifeD δ a (fun α => boxD Slots.id α (vD Slots.id A ls δ v)) =
        atLife (toLSub δ) a (fun α => box α (vC true A ls (toLSub δ) v))
      rw [atLife_toLSub, vD_id A hA ls δ]
      simp only [boxD_id]
  | .mut a A, hA, ls, δ => by
      funext v
      show atLifeD δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutD Slots.id ℓ α ls (fun ls₀ => vD Slots.id A ls₀ δ)) =
        atLife (toLSub δ) a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutS ℓ α ls (fun ls₀ => vC true A ls₀ (toLSub δ)))
      rw [atLife_toLSub]
      simp only [ptoMutD_id, vD_id A hA]

/-- **At the identity slots the computation relation is Core's**, at every fragment type. -/
theorem cD_id : ∀ (C : CTy), FragC C → ∀ (ls : List SRec) (δ : LSubD Life) (e : Expr),
    cD (ℍ := ℍ) Slots.id C ls δ e = cC (ℍ := ℍ) C ls (toLSub δ) e
  | .ret A, hA, ls, δ, e => by
      show wpTS ls e (fun ls'' => vD Slots.id A ls'' δ) =
        wpTS ls e (fun ls'' => vC true A ls'' (toLSub δ))
      simp only [vD_id A hA]
  | .arr A C, ⟨hA, hC⟩, ls, δ, e => by
      funext ρ
      show (∀ v, (vD Slots.id A ls δ v ─⋆ cD Slots.id C ls δ (.app e (.val v))) ρ) =
        (∀ v, (vC true A ls (toLSub δ) v ─⋆ cC C ls (toLSub δ) (.app e (.val v))) ρ)
      simp only [vD_id A hA, cD_id C hC]
  | .top, _, _, _, _ => rfl
  | .all x c C, hC, ls, δ, e => by
      funext ρ
      show (∀ α : Life, (⌜LtLifeD δ c α⌝ ─⋆
          cD Slots.id C ls (δ.extend x α) (.app e (.val .unit))) ρ) =
        (∀ α : Life, (⌜LtLife (toLSub δ) c α⌝ ─⋆
          cC C ls ((toLSub δ).extend x α) (.app e (.val .unit))) ρ)
      apply propext
      refine forall_congr' fun α => ?_
      rw [← toLSub_extend δ x α, ← cD_id C hC ls (δ.extend x α)]
      simp only [ltLife_toLSub]

end DenseCarrier

end
