import DenseCarrier.Relation

/-!
# DenseCarrier — the relation is invariant under the order automorphisms of `L`

An order automorphism `π` of the lifetime order acts on what the relation reads in `L`: the
reading `δ ↦ δ.map π` and the slots `ι ↦ ι.map π`. The resource, the record list and the term
are the model's and do not move. **Every clause of the fragment is invariant** (`vD_map`,
`cD_map`), and so is the semantic judgment (`semD_map`).

The proof is one induction. The only clause that needs `π` to be onto is `∀`: the quantifier
over `α' : L` is re-indexed by `α' = π α`. An order embedding that is not onto leaves values of
`α'` with no preimage, which is where `coreAllNotNatural` lives; on `ℕᵒᵈ` the identity is the only
automorphism, so there the statement is empty.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)

variable {L : Type} [LinearOrder L] [OrderTop L]

theorem interpD_mapIso (π : L ≃o L) (δ : LSubD L) (a : Lifetime.Life) :
    interpD (δ.map π) a = (interpD δ a).map π :=
  interpD_map π.monotone (OrderIso.map_top π) δ a

theorem atLifeD_map (π : L ≃o L) (δ : LSubD L) (a : Lifetime.Life) (F : L → WProp) :
    atLifeD (δ.map π) a F = atLifeD δ a (fun α => F (π α)) := by
  funext ρ
  simp only [atLifeD, interpD_mapIso]
  apply propext
  constructor
  · rintro ⟨α', hα', hF⟩
    obtain ⟨α, hα, rfl⟩ := Option.map_eq_some_iff.mp hα'
    exact ⟨α, hα, hF⟩
  · rintro ⟨α, hα, hF⟩
    exact ⟨π α, by rw [hα]; rfl, hF⟩

theorem ltLifeD_map (π : L ≃o L) (δ : LSubD L) (b : Lifetime.Life) (α : L) :
    LtLifeD (δ.map π) b (π α) ↔ LtLifeD δ b α := by
  simp only [LtLifeD, interpD_mapIso]
  constructor
  · rintro ⟨β', hβ', hlt⟩
    obtain ⟨β, hβ, rfl⟩ := Option.map_eq_some_iff.mp hβ'
    exact ⟨β, hβ, π.lt_iff_lt.mp hlt⟩
  · rintro ⟨β, hβ, hlt⟩
    exact ⟨π β, by rw [hβ]; rfl, π.lt_iff_lt.mpr hlt⟩

theorem modelsD_map (π : L ≃o L) (Δ : LifeCtx) (δ : LSubD L) :
    ModelsD Δ (δ.map π) ↔ ModelsD Δ δ := by
  simp only [ModelsD, LSubD.find?_map, interpD_mapIso]
  refine forall_congr' fun x => forall_congr' fun u => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨m', n', hm', hn', hlt⟩
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hm'
    obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp hn'
    exact ⟨m, n, hm, hn, π.lt_iff_lt.mp hlt⟩
  · rintro ⟨m, n, hm, hn, hlt⟩
    exact ⟨π m, π n, by rw [hm]; rfl, by rw [hn]; rfl, π.lt_iff_lt.mpr hlt⟩

theorem inStratumD_map (ι : Slots L) (π : L ≃o L) (α : L) (ψ : CellU Loc Val) :
    InStratumD (ι.map π) (π α) ψ ↔ InStratumD ι α ψ := by
  cases ψ with
  | own v => exact Iff.rfl
  | imm i => exact π.lt_iff_lt
  | «mut» m => exact π.lt_iff_lt

theorem outlivesD_map (ι : Slots L) (π : L ≃o L) (ρ : WRes) (α : L) :
    OutlivesD (ι.map π) ρ (π α) ↔ OutlivesD ι ρ α :=
  forall_congr' fun _ => forall_congr' fun ψ => imp_congr_right fun _ => inStratumD_map ι π α ψ

theorem boxD_map (ι : Slots L) (π : L ≃o L) (α : L) (P : WProp) :
    boxD (ι.map π) (π α) P = boxD ι α P := by
  funext ρ
  exact propext (and_congr_right fun _ => outlivesD_map ι π ρ α)

theorem ptoMutD_map (ι : Slots L) (π : L ≃o L) (l : Loc) (α : L) (ls : List SRec)
    (P : List SRec → Val → WProp) : ptoMutD (ι.map π) l (π α) ls P = ptoMutD ι l α ls P := by
  funext ρ
  simp only [ptoMutD, Slots.map_apply, π.le_iff_le]

mutual
/-- **The value relation is invariant under every order automorphism of `L`.** -/
theorem vD_map (ι : Slots L) (π : L ≃o L) : ∀ (A : VTy) (ls : List SRec) (δ : LSubD L),
    vD (ℍ := ℍ) (ι.map π) A ls (δ.map π) = vD (ℍ := ℍ) ι A ls δ
  | .unit, _, _ => rfl
  | .tensor A B, ls, δ => by
      funext v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vD (ℍ := ℍ) (ι.map π) A ls (δ.map π) v₁ ⋆ vD (ℍ := ℍ) (ι.map π) B ls (δ.map π) v₂) =
        (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vD (ℍ := ℍ) ι A ls δ v₁ ⋆ vD (ℍ := ℍ) ι B ls δ v₂)
      simp only [vD_map ι π A ls δ, vD_map ι π B ls δ]
  | .thunk C, ls, δ => by
      funext v ρ
      show (∀ ls', Ext ls ls' ρ → cD (ℍ := ℍ) (ι.map π) C ls' (δ.map π) (forceE C (.val v)) ρ) =
        (∀ ls', Ext ls ls' ρ → cD (ℍ := ℍ) ι C ls' δ (forceE C (.val v)) ρ)
      simp only [cD_map ι π C]
  | .ref A, ls, δ => by
      funext v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆
          vD (ℍ := ℍ) (ι.map π) A ls (δ.map π) v') =
        (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vD (ℍ := ℍ) ι A ls δ v')
      simp only [vD_map ι π A ls δ]
  | .box a A, ls, δ => by
      funext v
      show atLifeD (δ.map π) a (fun α => boxD (ι.map π) α
          (vD (ℍ := ℍ) (ι.map π) A ls (δ.map π) v)) =
        atLifeD δ a (fun α => boxD ι α (vD (ℍ := ℍ) ι A ls δ v))
      rw [atLifeD_map, vD_map ι π A ls δ]
      simp only [boxD_map]
  | .mut a A, ls, δ => by
      funext v
      show atLifeD (δ.map π) a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutD (ι.map π) ℓ α ls (fun ls₀ => vD (ℍ := ℍ) (ι.map π) A ls₀ (δ.map π))) =
        atLifeD δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutD ι ℓ α ls (fun ls₀ => vD (ℍ := ℍ) ι A ls₀ δ))
      rw [atLifeD_map]
      simp only [vD_map ι π A, ptoMutD_map]
  | .zero, _, _ | .sum _ _, _, _ | .imm _ _, _, _ | .bang _, _, _ | .unk, _, _
  | .tvar _, _, _ | .mu _, _, _ | .int _, _, _ | .fam _, _, _ | .opq _, _, _ => rfl

/-- **The computation relation is invariant under every order automorphism of `L`.** At `∀` the
quantifier over `L` is re-indexed by `π`, which needs `π` onto. -/
theorem cD_map (ι : Slots L) (π : L ≃o L) : ∀ (C : CTy) (ls : List SRec) (δ : LSubD L) (e : Expr),
    cD (ℍ := ℍ) (ι.map π) C ls (δ.map π) e = cD (ℍ := ℍ) ι C ls δ e
  | .ret A, ls, δ, e => by
      show wpTS ls e (fun ls'' => vD (ℍ := ℍ) (ι.map π) A ls'' (δ.map π)) =
        wpTS ls e (fun ls'' => vD (ℍ := ℍ) ι A ls'' δ)
      simp only [vD_map]
  | .arr A C, ls, δ, e => by
      funext ρ
      show (∀ v, (vD (ℍ := ℍ) (ι.map π) A ls (δ.map π) v ─⋆
          cD (ℍ := ℍ) (ι.map π) C ls (δ.map π) (.app e (.val v))) ρ) =
        (∀ v, (vD (ℍ := ℍ) ι A ls δ v ─⋆ cD (ℍ := ℍ) ι C ls δ (.app e (.val v))) ρ)
      simp only [vD_map, cD_map ι π C]
  | .top, _, _, _ => rfl
  | .all x c C, ls, δ, e => by
      funext ρ
      show (∀ α' : L, (⌜LtLifeD (δ.map π) c α'⌝ ─⋆
          cD (ℍ := ℍ) (ι.map π) C ls ((δ.map π).extend x α') (.app e (.val .unit))) ρ) =
        (∀ α : L, (⌜LtLifeD δ c α⌝ ─⋆
          cD (ℍ := ℍ) ι C ls (δ.extend x α) (.app e (.val .unit))) ρ)
      apply propext
      rw [π.surjective.forall]
      refine forall_congr' fun α => ?_
      rw [← LSubD.map_extend, cD_map ι π C ls (δ.extend x α)]
      simp only [ltLifeD_map]
  | .amp _ _, _, _, _ | .nu _, _, _, _ | .eff _ _ _ _ _ _ _, _, _, _ => rfl
end

theorem gSepD_map (ι : Slots L) (π : L ≃o L) (ls : List SRec) (δ : LSubD L) :
    ∀ (Γ : Ctx VTy) (γ : List Val), gSepD (ι.map π) ls (δ.map π) Γ γ = gSepD ι ls δ Γ γ
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: Γ, v :: γ => by
      simp only [gSepD, vD_map, gSepD_map ι π ls δ Γ γ]

theorem gDenD_map (ι : Slots L) (π : L ≃o L) (ls : List SRec) (δ : LSubD L) (Γ : Ctx VTy)
    (γ : List Val) : gDenD (ι.map π) ls (δ.map π) Γ γ = gDenD ι ls δ Γ γ := by
  simp only [gDenD, gSepD_map]

/-- **The semantic judgment is invariant under every order automorphism of `L`.** -/
theorem semD_map (ι : Slots L) (π : L ≃o L) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) :
    SemD (ℍ := ℍ) (ι.map π) Δ Γ e C ↔ SemD (ℍ := ℍ) ι Δ Γ e C := by
  have hδ : ∀ δ : LSubD L, (δ.map π.symm).map π = δ := fun δ => by
    rw [LSubD.map_map]
    conv_rhs => rw [← LSubD.map_id δ]
    exact LSubD.map_congr fun p _ => π.apply_symm_apply p.2
  constructor
  · intro h δ γ ls ρ hm hg
    rw [← cD_map ι π]
    exact h (δ.map π) γ ls ρ ((modelsD_map π Δ δ).mpr hm) (by rw [gDenD_map]; exact hg)
  · intro h δ' γ ls ρ hm hg
    rw [← hδ δ'] at hm hg ⊢
    rw [cD_map ι π]
    exact h _ γ ls ρ ((modelsD_map π Δ _).mp hm) (by rw [gDenD_map] at hg; exact hg)

end DenseCarrier

end
