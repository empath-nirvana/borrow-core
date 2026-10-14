import PartialLife.Relation

/-!
# PartialLife — the relation is invariant under the order automorphisms of a partial order

An order automorphism `π` of the lifetime order `L`, any partial order with a top, acts on what the
relation reads in `L`: the reading `δ ↦ δ.map π` and the slots' reading `ι ↦ ι.map π`. The
resource, the record list and the term are the model's and do not move. **Every clause of the
fragment is invariant** (`vP_map`, `cP_map`), and so is the semantic judgment (`semP_map`).

This is `DenseCarrier/Equivariance.lean`'s induction with the chain replaced by a partial order. Two
steps change: `@a ⊔ @b` and `@a ⊓ @b` are least upper and greatest lower bounds, which an order
automorphism carries (`interpP_map`, from `lubOpt_map`, `glbOpt_map`), in place of `max`/`min`
along a monotone map; and nothing else compares two lifetimes. The `∀` clause re-indexes its
quantifier by `α' = π α`, which needs `π` onto. On a chain carrying the cells (`Life`) the only
automorphism is the identity (`DenseCarrier.carrier_rigid`); a partial order can have others
(`PartialLife.swapBranches`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace PartialLife
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)
open DenseCarrier (LSubD)

variable {L : Type} [PartialOrder L] [OrderTop L]

theorem inStratumP_map (ι : Reading L) (π : L ≃o L) (α : L) (ψ : CellU Loc Val) :
    InStratumP (ι.map π) (π α) ψ ↔ InStratumP ι α ψ := by
  cases ψ with
  | own v => exact Iff.rfl
  | imm i => exact π.lt_iff_lt
  | «mut» m => exact π.lt_iff_lt

theorem outlivesP_map (ι : Reading L) (π : L ≃o L) (ρ : WRes) (α : L) :
    OutlivesP (ι.map π) ρ (π α) ↔ OutlivesP ι ρ α :=
  forall_congr' fun _ => forall_congr' fun ψ => imp_congr_right fun _ => inStratumP_map ι π α ψ

theorem boxP_map (ι : Reading L) (π : L ≃o L) (α : L) (P : WProp) :
    boxP (ι.map π) (π α) P = boxP ι α P := by
  funext ρ
  exact propext (and_congr_right fun _ => outlivesP_map ι π ρ α)

theorem ptoMutP_map (ι : Reading L) (π : L ≃o L) (l : Loc) (α : L) (ls : List SRec)
    (P : List SRec → Val → WProp) : ptoMutP (ι.map π) l (π α) ls P = ptoMutP ι l α ls P := by
  funext ρ
  simp only [ptoMutP, Reading.map_apply, π.le_iff_le]

mutual
/-- **The value relation is invariant under every order automorphism of the partial order.** -/
theorem vP_map (ι : Reading L) (π : L ≃o L) : ∀ (A : VTy) (ls : List SRec) (δ : LSubD L),
    vP (ℍ := ℍ) (ι.map π) A ls (δ.map π) = vP (ℍ := ℍ) ι A ls δ
  | .unit, _, _ => rfl
  | .tensor A B, ls, δ => by
      funext v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vP (ℍ := ℍ) (ι.map π) A ls (δ.map π) v₁ ⋆ vP (ℍ := ℍ) (ι.map π) B ls (δ.map π) v₂) =
        (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vP (ℍ := ℍ) ι A ls δ v₁ ⋆ vP (ℍ := ℍ) ι B ls δ v₂)
      simp only [vP_map ι π A ls δ, vP_map ι π B ls δ]
  | .thunk C, ls, δ => by
      funext v ρ
      show (∀ ls', Ext ls ls' ρ → cP (ℍ := ℍ) (ι.map π) C ls' (δ.map π) (forceE C (.val v)) ρ) =
        (∀ ls', Ext ls ls' ρ → cP (ℍ := ℍ) ι C ls' δ (forceE C (.val v)) ρ)
      simp only [cP_map ι π C]
  | .ref A, ls, δ => by
      funext v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆
          vP (ℍ := ℍ) (ι.map π) A ls (δ.map π) v') =
        (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vP (ℍ := ℍ) ι A ls δ v')
      simp only [vP_map ι π A ls δ]
  | .box a A, ls, δ => by
      funext v
      show atLifeP (δ.map π) a (fun α => boxP (ι.map π) α
          (vP (ℍ := ℍ) (ι.map π) A ls (δ.map π) v)) =
        atLifeP δ a (fun α => boxP ι α (vP (ℍ := ℍ) ι A ls δ v))
      rw [atLifeP_map, vP_map ι π A ls δ]
      simp only [boxP_map]
  | .mut a A, ls, δ => by
      funext v
      show atLifeP (δ.map π) a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutP (ι.map π) ℓ α ls (fun ls₀ => vP (ℍ := ℍ) (ι.map π) A ls₀ (δ.map π))) =
        atLifeP δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutP ι ℓ α ls (fun ls₀ => vP (ℍ := ℍ) ι A ls₀ δ))
      rw [atLifeP_map]
      simp only [vP_map ι π A, ptoMutP_map]
  | .zero, _, _ | .sum _ _, _, _ | .imm _ _, _, _ | .bang _, _, _ | .unk, _, _
  | .tvar _, _, _ | .mu _, _, _ | .int _, _, _ | .fam _, _, _ | .opq _, _, _ => rfl

/-- **The computation relation is invariant under every order automorphism of the partial order.**
At `∀` the quantifier over `L` is re-indexed by `π`, which needs `π` onto. -/
theorem cP_map (ι : Reading L) (π : L ≃o L) : ∀ (C : CTy) (ls : List SRec) (δ : LSubD L) (e : Expr),
    cP (ℍ := ℍ) (ι.map π) C ls (δ.map π) e = cP (ℍ := ℍ) ι C ls δ e
  | .ret A, ls, δ, e => by
      show wpTS ls e (fun ls'' => vP (ℍ := ℍ) (ι.map π) A ls'' (δ.map π)) =
        wpTS ls e (fun ls'' => vP (ℍ := ℍ) ι A ls'' δ)
      simp only [vP_map]
  | .arr A C, ls, δ, e => by
      funext ρ
      show (∀ v, (vP (ℍ := ℍ) (ι.map π) A ls (δ.map π) v ─⋆
          cP (ℍ := ℍ) (ι.map π) C ls (δ.map π) (.app e (.val v))) ρ) =
        (∀ v, (vP (ℍ := ℍ) ι A ls δ v ─⋆ cP (ℍ := ℍ) ι C ls δ (.app e (.val v))) ρ)
      simp only [vP_map, cP_map ι π C]
  | .top, _, _, _ => rfl
  | .all x c C, ls, δ, e => by
      funext ρ
      show (∀ α' : L, (⌜LtLifeP (δ.map π) c α'⌝ ─⋆
          cP (ℍ := ℍ) (ι.map π) C ls ((δ.map π).extend x α') (.app e (.val .unit))) ρ) =
        (∀ α : L, (⌜LtLifeP δ c α⌝ ─⋆
          cP (ℍ := ℍ) ι C ls (δ.extend x α) (.app e (.val .unit))) ρ)
      apply propext
      rw [π.surjective.forall]
      refine forall_congr' fun α => ?_
      rw [← LSubD.map_extend, cP_map ι π C ls (δ.extend x α)]
      simp only [ltLifeP_map]
  | .amp _ _, _, _, _ | .nu _, _, _, _ | .eff _ _ _ _ _ _ _, _, _, _ => rfl
end

theorem gSepP_map (ι : Reading L) (π : L ≃o L) (ls : List SRec) (δ : LSubD L) :
    ∀ (Γ : Ctx VTy) (γ : List Val), gSepP (ℍ := ℍ) (ι.map π) ls (δ.map π) Γ γ = gSepP ι ls δ Γ γ
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: Γ, v :: γ => by
      simp only [gSepP, vP_map, gSepP_map ι π ls δ Γ γ]

theorem gDenP_map (ι : Reading L) (π : L ≃o L) (ls : List SRec) (δ : LSubD L) (Γ : Ctx VTy)
    (γ : List Val) : gDenP (ℍ := ℍ) (ι.map π) ls (δ.map π) Γ γ = gDenP ι ls δ Γ γ := by
  simp only [gDenP, gSepP_map]

/-- **The semantic judgment is invariant under every order automorphism of the partial order.** -/
theorem semP_map (ι : Reading L) (π : L ≃o L) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) :
    SemP (ℍ := ℍ) (ι.map π) Δ Γ e C ↔ SemP (ℍ := ℍ) ι Δ Γ e C := by
  have hδ : ∀ δ : LSubD L, (δ.map π.symm).map π = δ := fun δ => by
    rw [LSubD.map_map]
    conv_rhs => rw [← LSubD.map_id δ]
    exact LSubD.map_congr fun p _ => π.apply_symm_apply p.2
  constructor
  · intro h δ γ ls ρ hm hg
    rw [← cP_map ι π]
    exact h (δ.map π) γ ls ρ ((modelsP_map π Δ δ).mpr hm) (by rw [gDenP_map]; exact hg)
  · intro h δ' γ ls ρ hm hg
    rw [← hδ δ'] at hm hg ⊢
    rw [cP_map ι π]
    exact h _ γ ls ρ ((modelsP_map π Δ _).mp hm) (by rw [gDenP_map] at hg; exact hg)

end PartialLife

end
