import Nominal.Relation

/-!
# Nominal — the relation is equivariant under every order automorphism

An order automorphism `π : L ≃o L` acts on the reading (`δ ↦ δ.map π`) and on resources
(`ρ ↦ π·ρ`, every cell's lifetimes, witness and stored predicate moved: `Action.lean`). The
term does not move: terms carry no lifetimes.

**`vN_map`, `cN_map`: `𝒱⟦A⟧(π·δ)(v)(π·ρ) ↔ 𝒱⟦A⟧δ(v)(ρ)` and `𝒞⟦C⟧(π·δ)(e)(π·ρ) ↔
𝒞⟦C⟧δ(e)(ρ)`, at every type of the fragment**, by one induction on types. Each clause is an
instance of `ModelEquiv.lean`:

* `1`, `⊗`, `Ref`: `⌜−⌝`, `⋆`, `∃`, `ℓ ↦ v` (`pureN_relRU_iff`, `sepN_relRU_iff`, …);
* `[@a]`: `@aδ` moves with `δ` (`interpN_map`) and survival moves with the cells
  (`survives_relRU`);
* `Mut`: the stored predicate of the moved cell is the image of `𝒱⟦A⟧δ`, which is `𝒱⟦A⟧(π·δ)` by
  the induction hypothesis because the image is the whole transport (`ptoMutN_relRU_iff`);
* `Imm`: the payload is the observable view, by the induction hypothesis (`ptoImmN_relRU_iff`);
* `U`: the induction hypothesis at the computation type;
* `F`: `wp` is invariant (`wpN_relRU_iff`): its frame quantifier is re-indexed by `π`;
* `⊸`: `─⋆`'s quantifier over resources is re-indexed by `π`;
* `∀`: the quantifier over lifetimes is re-indexed by `π`, which is onto.

`semN_map`: the semantic judgment is invariant.
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)
open BoCa.Fig16.LogRel.Core (VTy CTy forceE)
open BoCa.Lifetime (LifeVar LifeCtx)

set_option linter.unusedSectionVars false

section Interp
variable {L : Type} [PartialOrder L] [OrderTop L]

theorem joinN_map (π : L ≃o L) (m n : L) : joinN (π m) (π n) = (joinN m n).map π := by
  unfold joinN
  simp only [π.le_iff_le]
  split_ifs <;> rfl

theorem meetN_map (π : L ≃o L) (m n : L) : meetN (π m) (π n) = (meetN m n).map π := by
  unfold meetN
  simp only [π.le_iff_le]
  split_ifs <;> rfl

theorem interpN_map (π : L ≃o L) (δ : LSubN L) :
    ∀ a : Lifetime.Life, interpN (δ.map π) a = (interpN δ a).map π := by
  intro a
  induction a with
  | var y => exact LSubN.find?_map π δ y
  | top => simp [interpN]
  | join p q ihp ihq =>
      simp only [interpN, ihp, ihq]
      cases interpD : interpN δ p <;> cases interpN δ q <;> simp [joinN_map]
  | meet p q ihp ihq =>
      simp only [interpN, ihp, ihq]
      cases interpN δ p <;> cases interpN δ q <;> simp [meetN_map]

theorem ltLifeN_map (π : L ≃o L) (δ : LSubN L) :
    ∀ (b : Lifetime.Life) (α : L), LtLifeN (δ.map π) b (π α) ↔ LtLifeN δ b α := by
  intro b
  induction b with
  | var x =>
      intro α
      simp only [LtLifeN, LSubN.find?_map]
      constructor
      · rintro ⟨β', hβ', hlt⟩
        obtain ⟨β, hβ, rfl⟩ := Option.map_eq_some_iff.mp hβ'
        exact ⟨β, hβ, π.lt_iff_lt.mp hlt⟩
      · rintro ⟨β, hβ, hlt⟩
        exact ⟨π β, by rw [hβ]; rfl, π.lt_iff_lt.mpr hlt⟩
  | top =>
      intro α
      show π α < ⊤ ↔ α < ⊤
      conv_lhs => rw [← OrderIso.map_top π]
      exact π.lt_iff_lt
  | meet a b iha ihb => intro α; exact and_congr (iha α) (ihb α)
  | join a b iha ihb => intro α; exact or_congr (iha α) (ihb α)

theorem modelsN_map (π : L ≃o L) (Δ : LifeCtx) (δ : LSubN L) :
    ModelsN Δ (δ.map π) ↔ ModelsN Δ δ := by
  simp only [ModelsN, LSubN.find?_map]
  refine forall_congr' fun x => forall_congr' fun u => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨m', hm', hlt⟩
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hm'
    exact ⟨m, hm, (ltLifeN_map π δ u m).mp hlt⟩
  · rintro ⟨m, hm, hlt⟩
    exact ⟨π m, by rw [hm]; rfl, (ltLifeN_map π δ u m).mpr hlt⟩

end Interp

variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem atLifeN_map (π : L ≃o L) (δ : LSubN L) (a : Lifetime.Life) {F F' : L → WPropN L}
    (hF : ∀ α σ, F' (π α) (relRU π σ) ↔ F α σ) (ρ : ResU L) :
    atLifeN (δ.map π) a F' (relRU π ρ) ↔ atLifeN δ a F ρ := by
  simp only [atLifeN, interpN_map]
  constructor
  · rintro ⟨α', hα', hF'⟩
    obtain ⟨α, hα, rfl⟩ := Option.map_eq_some_iff.mp hα'
    exact ⟨α, hα, (hF α ρ).mp hF'⟩
  · rintro ⟨α, hα, h⟩
    exact ⟨π α, by rw [hα]; rfl, (hF α ρ).mpr h⟩

theorem boxE_relRU_iff (π : L ≃o L) (α : L) {P P' : WPropN L}
    (hP : ∀ σ, P' (relRU π σ) ↔ P σ) (ρ : ResU L) :
    boxE (π α) P' (relRU π ρ) ↔ boxE α P ρ :=
  and_congr (hP ρ) (survives_relRU π α ρ)

theorem boxS_relRU_iff (π : L ≃o L) (α : L) {P P' : WPropN L}
    (hP : ∀ σ, P' (relRU π σ) ↔ P σ) (ρ : ResU L) :
    boxS (π α) P' (relRU π ρ) ↔ boxS α P ρ :=
  and_congr (hP ρ) (inStratum_relRU_singleton π α ρ)

/-- The image of a predicate whose transport is `P′` is `P′`. -/
theorem img_eq_of (π : L ≃o L) {P : Val → WPropN L} {P' : Val → WPropN L}
    (hP : ∀ u σ, P' u (relRU π σ) ↔ P u σ) : img π P = P' := by
  funext u τ
  apply propext
  obtain ⟨σ, rfl⟩ := relRU_surjective π τ
  rw [img_apply, hP]

/-- **The `Mut` clause's cell is natural**: the moved cell stores the image of `P̂`, which is the
transported predicate. -/
theorem ptoMutN_relRU_iff (π : L ≃o L) (l : Loc) (α : L) {P P' : Val → WPropN L}
    (hP : ∀ u σ, P' u (relRU π σ) ↔ P u σ) (ρ : ResU L) :
    ptoMutN l (π α) P' (relRU π ρ) ↔ ptoMutN l α P ρ := by
  have himg : img π P = P' := img_eq_of π hP
  have hP' : ∀ u σ, P u (relRU π.symm σ) ↔ P' u σ := by
    intro u σ
    rw [← hP u (relRU π.symm σ), relRU_relRU_symm]
  have himg' : img π.symm P' = P := img_eq_of π.symm hP'
  constructor
  · rintro ⟨b', u, σ', h', hw', hαb, hstr, e⟩
    have e' : ρ = ResU.single l (relU π.symm (CellU.mutOf b' u σ' h' P' hw')) := by
      rw [← relRU_single, ← e, relRU_symm_relRU]
    rw [relU_mutOf] at e'
    subst himg'
    refine ⟨π.symm b', u, relRU π.symm σ', _, img_self π.symm hw', ?_, ?_, e'⟩
    · rw [← π.le_iff_le, π.apply_symm_apply]; exact hαb
    · intro u'' σ'' hσ''
      obtain ⟨σ₀, rfl, hσ₀⟩ := hσ''
      exact (inStratum_relRU_singleton π.symm b' σ₀).mpr (hstr u'' σ₀ hσ₀)
  · rintro ⟨b, u, σ, h, hw, hαb, hstr, rfl⟩
    subst himg
    refine ⟨π b, u, relRU π σ, (inStratum_relRU_singleton π b σ).mpr h, img_self π hw,
      π.le_iff_le.mpr hαb, ?_, ?_⟩
    · intro u'' σ'' hσ''
      obtain ⟨σ₀, rfl, hσ₀⟩ := hσ''
      exact (inStratum_relRU_singleton π b σ₀).mpr (hstr u'' σ₀ hσ₀)
    · rw [relRU_single, relU_mutOf]

theorem ptoImmN_relRU_iff (π : L ≃o L) (l : Loc) (α : L) {P P' : Val → WPropN L}
    (hP : ∀ u σ, P' u (relRU π σ) ↔ P u σ) (ρ : ResU L) :
    ptoImmN l (π α) P' (relRU π ρ) ↔ ptoImmN l α P ρ := by
  constructor
  · rintro ⟨s', hs', u, σ', h', hα, hpay, e⟩
    have e' : ρ = ResU.single l (relU π.symm (CellU.immOf s' hs' u σ' h')) := by
      rw [← relRU_single, ← e, relRU_symm_relRU]
    rw [relU_immOf] at e'
    refine ⟨mapS π.symm s', _, u, relRU π.symm σ', _, ?_, ?_, e'⟩
    · intro m hm
      obtain ⟨m', hm', rfl⟩ := mem_mapS.mp hm
      rw [← π.le_iff_le, π.apply_symm_apply]
      exact hα m' hm'
    · rw [← hP, relRU_relRU_symm]; exact hpay
  · rintro ⟨s, hs, u, σ, h, hα, hpay, rfl⟩
    refine ⟨mapS π s, mapS_nonempty.mpr hs, u, relRU π σ, (inStratum_relRU π s σ).mpr h, ?_,
      (hP u σ).mpr hpay, ?_⟩
    · intro m' hm'
      obtain ⟨m, hm, rfl⟩ := mem_mapS.mp hm'
      exact π.le_iff_le.mpr (hα m hm)
    · rw [relRU_single, relU_immOf]

mutual
/-- **The value relation is equivariant under every order automorphism.** -/
theorem vN_map (π : L ≃o L) : ∀ (b : Bool) (A : VTy) (δ : LSubN L) (v : Val) (ρ : ResU L),
    vN (ℍ := ℍ) b A (δ.map π) v (relRU π ρ) ↔ vN (ℍ := ℍ) b A δ v ρ
  | _, .unit, _, v, ρ => pureN_relRU_iff π (v = .unit) ρ
  | b, .tensor A B, δ, _, ρ =>
      exN_relRU_iff π (fun v₁ σ => exN_relRU_iff π (fun v₂ σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _)
          (sepN_relRU_iff π (vN_map π b A δ v₁) (vN_map π b B δ v₂)) σ') σ) ρ
  | true, .thunk C, δ, v, ρ => cN_map π C δ (forceE C (.val v)) ρ
  | false, .thunk _, _, _, _ => Iff.rfl
  | b, .ref A, δ, _, ρ =>
      exN_relRU_iff π (fun ℓ σ => exN_relRU_iff π (fun v' σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _)
          (sepN_relRU_iff π (ptoOwnN_relRU_iff π ℓ v') (vN_map π b A δ v')) σ') σ) ρ
  | b, .box a A, δ, v, ρ =>
      atLifeN_map π δ a (fun α σ => boxE_relRU_iff π α (vN_map π b A δ v) σ) ρ
  | _, .imm a A, δ, _, ρ =>
      atLifeN_map π δ a (fun α σ => exN_relRU_iff π (fun ℓ σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _)
          (ptoImmN_relRU_iff π ℓ α (vN_map π false A δ)) σ') σ) ρ
  | _, .mut a A, δ, _, ρ =>
      atLifeN_map π δ a (fun α σ => exN_relRU_iff π (fun ℓ σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _)
          (ptoMutN_relRU_iff π ℓ α (vN_map π true A δ)) σ') σ) ρ
  | _, .zero, _, _, _ | _, .sum _ _, _, _, _ | _, .bang _, _, _, _ | _, .unk, _, _, _
  | _, .tvar _, _, _, _ | _, .mu _, _, _, _ | _, .int _, _, _, _ | _, .fam _, _, _, _
  | _, .opq _, _, _, _ => Iff.rfl

/-- **The computation relation is equivariant under every order automorphism.** At `∀` the
quantifier over `L` is re-indexed by `π`. -/
theorem cN_map (π : L ≃o L) : ∀ (C : CTy) (δ : LSubN L) (e : Expr) (ρ : ResU L),
    cN (ℍ := ℍ) C (δ.map π) e (relRU π ρ) ↔ cN (ℍ := ℍ) C δ e ρ
  | .ret A, δ, e, ρ => wpN_relRU_iff π e (fun v σ => vN_map π true A δ v σ) ρ
  | .arr A C, δ, e, ρ =>
      forall_congr' fun v =>
        wandN_relRU_iff π (vN_map π true A δ v) (cN_map π C δ (.app e (.val v))) ρ
  | .top, _, _, _ => Iff.rfl
  | .all x c C, δ, e, ρ => by
      show (∀ α' : L, wandN (pureN (LtLifeN (δ.map π) c α'))
          (cN (ℍ := ℍ) C ((δ.map π).extend x α') (.app e (.val .unit))) (relRU π ρ)) ↔
        (∀ α : L, wandN (pureN (LtLifeN δ c α))
          (cN (ℍ := ℍ) C (δ.extend x α) (.app e (.val .unit))) ρ)
      rw [π.surjective.forall]
      refine forall_congr' fun α => ?_
      rw [← LSubN.map_extend]
      exact wandN_relRU_iff π (fun σ => by rw [pureN_relRU_iff, ltLifeN_map])
        (cN_map π C (δ.extend x α) _) ρ
  | .amp _ _, _, _, _ | .nu _, _, _, _ | .eff _ _ _ _ _ _ _, _, _, _ => Iff.rfl
end

theorem gSepN_map (π : L ≃o L) (δ : LSubN L) :
    ∀ (Γ : Ctx VTy) (γ : List Val) (ρ : ResU L),
      gSepN (ℍ := ℍ) (δ.map π) Γ γ (relRU π ρ) ↔ gSepN (ℍ := ℍ) δ Γ γ ρ
  | [], _, ρ => pureN_relRU_iff π True ρ
  | _ :: _, [], ρ => pureN_relRU_iff π True ρ
  | s :: Γ, v :: γ, ρ => by
      by_cases hs : s.live
      · simp only [gSepN, hs, if_true]
        exact sepN_relRU_iff π (vN_map π true s.ty δ v) (gSepN_map π δ Γ γ) ρ
      · simp only [gSepN, hs]
        exact gSepN_map π δ Γ γ ρ

theorem gDenN_map (π : L ≃o L) (δ : LSubN L) (Γ : Ctx VTy) (γ : List Val) (ρ : ResU L) :
    gDenN (ℍ := ℍ) (δ.map π) Γ γ (relRU π ρ) ↔ gDenN (ℍ := ℍ) δ Γ γ ρ :=
  sepN_relRU_iff π (pureN_relRU_iff π _) (gSepN_map π δ Γ γ) ρ

/-- **The semantic judgment is invariant under every order automorphism.** -/
theorem semN_map_iff (π : L ≃o L) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy)
    (δ : LSubN L) (γ : List Val) (ρ : ResU L) :
    (ModelsN Δ (δ.map π) → gDenN (ℍ := ℍ) (δ.map π) Γ γ (relRU π ρ) →
        cN (ℍ := ℍ) C (δ.map π) (BoCa.Fig16.LogRel.substAll γ e) (relRU π ρ)) ↔
      (ModelsN Δ δ → gDenN (ℍ := ℍ) δ Γ γ ρ →
        cN (ℍ := ℍ) C δ (BoCa.Fig16.LogRel.substAll γ e) ρ) := by
  rw [modelsN_map, gDenN_map, cN_map]

end Nominal

end
