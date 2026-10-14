import Nominal.Model

/-!
# Nominal — the model commutes with every order automorphism

For `π : L ≃o L`, with `π·ψ = relU π ψ` and `π·ρ = relRU π ρ`:

* cells: `▶◀`, `●`, `○` and `⋈` are carried by `π` (`compatS_relU`, `compS_relU`, `compR_relU`);
* resources: `◐`, `ρ∣ι`, `⨀`, both walks, `⦇ρ⦈`, `✓`, `⟦ρ⟧`, `#`, `↭`, `ρ∣own = ∅` are carried by
  `π` (`*_relRU`), and since `π⁻¹` undoes `π` they are **invariant** (`*_relRU_iff`);
* propositions: `⌜−⌝`, `⋆`, `─⋆`, `∃`, `ℓ ↦ v` and `wp` commute with the transport
  `P ↦ P ∘ π⁻¹` (`sepN_relRU_iff`, `wandN_relRU_iff`, `wpN_relRU_iff`, …), stated as: if `P′`
  at `π·σ` is `P` at `σ` for every `σ`, then the compound at `π·ρ` is the compound at `ρ`.

Each forward lemma is an induction over the printed definition with `π` applied to every cell;
each invariance is the forward lemma at `π` and at `π⁻¹`. `wp`'s frame quantifier is re-indexed by
`π`, which is onto.
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)

set_option linter.unusedSectionVars false

variable {L : Type} [PartialOrder L] [WellFoundedGT L]

/-! ### Cells -/

section Cells
variable (π : L ≃o L)

theorem compatS_relU {ψ₁ ψ₂ : CellU L} (h : CellU.CompatS ψ₁ ψ₂) :
    CellU.CompatS (relU π ψ₁) (relU π ψ₂) := by
  obtain ⟨k₁, k₂, he, hw⟩ := h
  exact ⟨by rw [kind_relU, k₁], by rw [kind_relU, k₂], by rw [erase_relU, erase_relU, he],
    by rw [wit_relU, wit_relU, hw]⟩

theorem compS_relU {ψ₁ ψ₂ ψ : CellU L} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    CellU.CompS (relU π ψ₁) (relU π ψ₂) (relU π ψ) := by
  obtain ⟨hc, k, he, hw, hl⟩ := h
  exact ⟨compatS_relU π hc, by rw [kind_relU, k], by rw [erase_relU, erase_relU, he],
    by rw [wit_relU, wit_relU, hw], by rw [lts_relU, lts_relU, lts_relU, hl, mapS_union]⟩

theorem isMut_relU {ψ : CellU L} {b : L} {v : Val} {ρ : ResU L} {P : Val → ResU L → Prop}
    (h : ψ.IsMut b v ρ P) : (relU π ψ).IsMut (π b) v (relRU π ρ) (img π P) := by
  obtain ⟨k, hl, he, hw, hp⟩ := h
  exact ⟨by rw [kind_relU, k], by rw [lts_relU, hl]; rfl, by rw [erase_relU, he],
    by rw [wit_relU, hw], by rw [pu_relU, hp]⟩

theorem isImm_relU {ψ : CellU L} {s : Finset L} {v : Val} {ρ : ResU L} (h : ψ.IsImm s v ρ) :
    (relU π ψ).IsImm (mapS π s) v (relRU π ρ) := by
  obtain ⟨k, hl, he, hw⟩ := h
  exact ⟨by rw [kind_relU, k], by rw [lts_relU, hl], by rw [erase_relU, he], by rw [wit_relU, hw]⟩

theorem isOwn_relU {ψ : CellU L} {v : Val} (h : ψ.IsOwn v) : (relU π ψ).IsOwn v :=
  ⟨by rw [kind_relU, h.1], by rw [erase_relU, h.2]⟩

theorem img_and (P Q : Val → ResU L → Prop) :
    img π (fun u σ => P u σ ∧ Q u σ) = fun u σ => img π P u σ ∧ img π Q u σ := by
  funext u σ
  apply propext
  constructor
  · rintro ⟨σ₀, e, hP, hQ⟩
    exact ⟨⟨σ₀, e, hP⟩, ⟨σ₀, e, hQ⟩⟩
  · rintro ⟨⟨σ₀, e₀, hP⟩, ⟨σ₁, e₁, hQ⟩⟩
    obtain rfl := relRU_injective π (e₁.trans e₀.symm)
    exact ⟨σ₁, e₁, hP, hQ⟩

theorem compR_relU {ψ₁ ψ₂ ψ : CellU L} (h : CellU.CompR ψ₁ ψ₂ ψ) :
    CellU.CompR (relU π ψ₁) (relU π ψ₂) (relU π ψ) := by
  cases h with
  | same => exact .same _
  | strict h => exact .strict (compS_relU π h)
  | mutMutL h₁ h₂ hab h =>
      refine .mutMutL (isMut_relU π h₁) (isMut_relU π h₂) (π.le_iff_le.mpr hab) ?_
      have := isMut_relU π h
      rwa [img_and] at this
  | mutMutR h₁ h₂ hab h =>
      refine .mutMutR (isMut_relU π h₁) (isMut_relU π h₂) (π.le_iff_le.mpr hab) ?_
      have := isMut_relU π h
      rwa [img_and] at this
  | mutOwn h₁ h₂ => exact .mutOwn (isMut_relU π h₁) (isOwn_relU π h₂)
  | ownMut h₁ h₂ => exact .ownMut (isOwn_relU π h₁) (isMut_relU π h₂)
  | immOwn h₁ h₂ => exact .immOwn (isImm_relU π h₁) (isOwn_relU π h₂)
  | ownImm h₁ h₂ => exact .ownImm (isOwn_relU π h₁) (isImm_relU π h₂)
  | immMut h₁ h₂ => exact .immMut (isImm_relU π h₁) (isMut_relU π h₂)
  | mutImm h₁ h₂ => exact .mutImm (isMut_relU π h₁) (isImm_relU π h₂)

theorem compatR_relU {ψ₁ ψ₂ : CellU L} (h : CellU.CompatR ψ₁ ψ₂) :
    CellU.CompatR (relU π ψ₁) (relU π ψ₂) :=
  let ⟨ψ, hψ⟩ := h; ⟨relU π ψ, compR_relU π hψ⟩

end Cells

/-! ### Resources, forward -/

section Resources
variable {π : L ≃o L}

theorem compat_relRU {R : CellU L → CellU L → Prop}
    (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R (relU π ψ₁) (relU π ψ₂)) {ρ₁ ρ₂ : ResU L}
    (h : Compat R ρ₁ ρ₂) : Compat R (relRU π ρ₁) (relRU π ρ₂) := by
  intro l ψ₁' ψ₂' e₁ e₂
  rw [relRU_get] at e₁ e₂
  obtain ⟨ψ₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp e₁
  obtain ⟨ψ₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp e₂
  exact hR _ _ (h l ψ₁ ψ₂ h₁ h₂)

theorem optComp_map {C : CellU L → CellU L → CellU L → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C (relU π ψ₁) (relU π ψ₂) (relU π ψ)) :
    ∀ {o₁ o₂ o : Option (CellU L)}, OptComp C o₁ o₂ o →
      OptComp C (o₁.map (relU π)) (o₂.map (relU π)) (o.map (relU π))
  | none, none, o, h => by
      change o = none at h
      subst h; rfl
  | some ψ, none, o, h => by
      change o = some ψ at h
      subst h; rfl
  | none, some ψ, o, h => by
      change o = some ψ at h
      subst h; rfl
  | some ψ₁, some ψ₂, o, h => by
      obtain ⟨ψ, rfl, hc⟩ := h
      exact ⟨_, rfl, hC _ _ _ hc⟩

theorem comp_relRU {R : CellU L → CellU L → Prop} {C : CellU L → CellU L → CellU L → Prop}
    (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R (relU π ψ₁) (relU π ψ₂))
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C (relU π ψ₁) (relU π ψ₂) (relU π ψ))
    {ρ₁ ρ₂ ρ : ResU L} (h : Comp R C ρ₁ ρ₂ ρ) : Comp R C (relRU π ρ₁) (relRU π ρ₂) (relRU π ρ) :=
  ⟨compat_relRU hR h.1, fun l => optComp_map hC (h.2 l)⟩

theorem natCompatS (π : L ≃o L) : ∀ ψ₁ ψ₂ : CellU L, CellU.CompatS ψ₁ ψ₂ →
    CellU.CompatS (relU π ψ₁) (relU π ψ₂) := fun _ _ h => compatS_relU π h
theorem natCompS (π : L ≃o L) : ∀ ψ₁ ψ₂ ψ : CellU L, CellU.CompS ψ₁ ψ₂ ψ →
    CellU.CompS (relU π ψ₁) (relU π ψ₂) (relU π ψ) := fun _ _ _ h => compS_relU π h
theorem natCompatR (π : L ≃o L) : ∀ ψ₁ ψ₂ : CellU L, CellU.CompatR ψ₁ ψ₂ →
    CellU.CompatR (relU π ψ₁) (relU π ψ₂) := fun _ _ h => compatR_relU π h
theorem natCompR (π : L ≃o L) : ∀ ψ₁ ψ₂ ψ : CellU L, CellU.CompR ψ₁ ψ₂ ψ →
    CellU.CompR (relU π ψ₁) (relU π ψ₂) (relU π ψ) := fun _ _ _ h => compR_relU π h

theorem compS_relRU {ρ₁ ρ₂ ρ : ResU L} (h : ResU.CompS ρ₁ ρ₂ ρ) :
    ResU.CompS (relRU π ρ₁) (relRU π ρ₂) (relRU π ρ) :=
  comp_relRU (natCompatS π) (natCompS π) h

theorem compR_relRU {ρ₁ ρ₂ ρ : ResU L} (h : ResU.CompR ρ₁ ρ₂ ρ) :
    ResU.CompR (relRU π ρ₁) (relRU π ρ₂) (relRU π ρ) :=
  comp_relRU (natCompatR π) (natCompR π) h

theorem restrict_relRU (ρ : ResU L) (k : Kind) :
    (relRU π ρ).restrict k = relRU π (ρ.restrict k) := by
  refine PMap.ext fun l => ?_
  show ((ρ.get l).map (relU π)).bind (fun ψ => if ψ.kind = k then some ψ else none) =
    ((ρ.get l).bind (fun ψ => if ψ.kind = k then some ψ else none)).map (relU π)
  cases ρ.get l with
  | none => rfl
  | some ψ =>
      simp only [Option.map_some, Option.bind_some, kind_relU]
      split_ifs <;> rfl

theorem sites_relRU (ρ : ResU L) (k : Kind) (d : List Loc) :
    ResU.Sites (relRU π ρ) k d ↔ ResU.Sites ρ k d := by
  unfold ResU.Sites
  refine and_congr_right fun _ => forall_congr' fun l => ?_
  rw [relRU_get]
  refine Iff.intro (fun h => ?_) (fun h => ?_) <;> constructor
  · intro hl
    obtain ⟨ψ', e, hk⟩ := h.mp hl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp e
    exact ⟨ψ, hψ, by rwa [kind_relU] at hk⟩
  · rintro ⟨ψ, hψ, hk⟩
    exact h.mpr ⟨relU π ψ, by rw [hψ]; rfl, by rw [kind_relU, hk]⟩
  · intro hl
    obtain ⟨ψ, hψ, hk⟩ := h.mp hl
    exact ⟨relU π ψ, by rw [hψ]; rfl, by rw [kind_relU, hk]⟩
  · rintro ⟨ψ', e, hk⟩
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp e
    exact h.mpr ⟨ψ, hψ, by rwa [kind_relU] at hk⟩

theorem bigComp_relRU {R : CellU L → CellU L → Prop} {C : CellU L → CellU L → CellU L → Prop}
    (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R (relU π ψ₁) (relU π ψ₂))
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C (relU π ψ₁) (relU π ψ₂) (relU π ψ)) :
    ∀ {σs : List (ResU L)} {b : ResU L}, BigComp R C σs b →
      BigComp R C (σs.map (relRU π)) (relRU π b)
  | _, _, .nil => by rw [List.map_nil, relRU_empty]; exact .nil
  | _, _, .cons h hc => .cons (bigComp_relRU hR hC h) (comp_relRU hR hC hc)

/-- Moving the second components of a tagged family. -/
def mapW (π : L ≃o L) (w : List (Loc × ResU L)) : List (Loc × ResU L) :=
  w.map fun p => (p.1, relRU π p.2)

theorem mapW_fst (w : List (Loc × ResU L)) : (mapW π w).map Prod.fst = w.map Prod.fst := by
  simp [mapW]

theorem mapW_snd (w : List (Loc × ResU L)) :
    (mapW π w).map Prod.snd = (w.map Prod.snd).map (relRU π) := by
  simp [mapW]

mutual
theorem exW_relRU {R : CellU L → CellU L → Prop} {C : CellU L → CellU L → CellU L → Prop}
    (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R (relU π ψ₁) (relU π ψ₂))
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C (relU π ψ₁) (relU π ψ₂) (relU π ψ)) :
    ∀ {ρ σ : ResU L}, ExW R C ρ σ → ExW R C (relRU π ρ) (relRU π σ)
  | _, _, .mk (w := w) hs hw hb hnm hσ => by
      refine .mk (w := mapW π w) ?_ (exWits_relRU hR hC hw) ?_ ?_ (comp_relRU hR hC hσ)
      · rw [mapW_fst]; exact (sites_relRU _ _ _).mpr hs
      · rw [mapW_snd]; exact bigComp_relRU hR hC hb
      · rw [restrict_relRU, restrict_relRU]; exact comp_relRU hR hC hnm

theorem exWits_relRU {R : CellU L → CellU L → Prop} {C : CellU L → CellU L → CellU L → Prop}
    (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R (relU π ψ₁) (relU π ψ₂))
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C (relU π ψ₁) (relU π ψ₂) (relU π ψ)) :
    ∀ {ρ : ResU L} {w : List (Loc × ResU L)}, ExWits R C ρ w →
      ExWits R C (relRU π ρ) (mapW π w)
  | _, _, .nil => .nil
  | _, _, .cons ψ hψ hk he hw =>
      .cons (relU π ψ) (by rw [relRU_get, hψ]; rfl) (by rw [kind_relU, hk])
        (by rw [wit_relU]; exact exW_relRU hR hC he) (exWits_relRU hR hC hw)
end

mutual
theorem agW_relRU : ∀ {ρ σ : ResU L}, AgW ρ σ → AgW (relRU π ρ) (relRU π σ)
  | _, _, .mk (a := a) (bm := bm) (bi := bi) (wm := wm) (wi := wi) hsm hsi hwm hwi hbm hbi
      ha hσ => by
      refine .mk (a := relRU π a) (bm := relRU π bm) (bi := relRU π bi) (wm := mapW π wm)
        (wi := mapW π wi) ?_ ?_ (agWitsM_relRU hwm) (agWitsI_relRU hwi) ?_ ?_ ?_
        (compR_relRU hσ)
      · rw [mapW_fst]; exact (sites_relRU _ _ _).mpr hsm
      · rw [mapW_fst]; exact (sites_relRU _ _ _).mpr hsi
      · rw [mapW_snd]; exact bigComp_relRU (natCompatR π) (natCompR π) hbm
      · rw [mapW_snd]; exact bigComp_relRU (natCompatR π) (natCompR π) hbi
      · rw [restrict_relRU]; exact compR_relRU ha

theorem agWitsM_relRU : ∀ {ρ : ResU L} {w : List (Loc × ResU L)}, AgWitsM ρ w →
    AgWitsM (relRU π ρ) (mapW π w)
  | _, _, .nil => .nil
  | _, _, .cons ψ hψ hk he hw =>
      .cons (relU π ψ) (by rw [relRU_get, hψ]; rfl) (by rw [kind_relU, hk])
        (by rw [wit_relU]; exact agW_relRU he) (agWitsM_relRU hw)

theorem agWitsI_relRU : ∀ {ρ : ResU L} {w : List (Loc × ResU L)}, AgWitsI ρ w →
    AgWitsI (relRU π ρ) (mapW π w)
  | _, _, .nil => .nil
  | _, _, .cons ψ hψ hk e a hex hag hp hw => by
      refine .cons (relU π ψ) (by rw [relRU_get, hψ]; rfl) (by rw [kind_relU, hk])
        (relRU π e) (relRU π a) ?_ ?_ (compR_relRU hp) (agWitsI_relRU hw)
      · rw [wit_relU]; exact exW_relRU (natCompatR π) (natCompR π) hex
      · rw [wit_relU]; exact agW_relRU hag
end

theorem flat_relRU {ρ σ : ResU L} (h : ρ.Flat σ) : (relRU π ρ).Flat (relRU π σ) := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  exact ⟨relRU π e, relRU π a,
    exW_relRU (natCompatS π) (natCompS π) he, agW_relRU ha,
    compS_relRU hc⟩

theorem valid_relRU {ρ : ResU L} (h : ρ.Valid) : (relRU π ρ).Valid :=
  let ⟨σ, hσ⟩ := h; ⟨relRU π σ, flat_relRU hσ⟩

theorem lower_relRU {ρ : ResU L} {m : Loc → Option Val} (h : ρ.Lower m) :
    (relRU π ρ).Lower m := by
  obtain ⟨σ, hσ, hm⟩ := h
  refine ⟨relRU π σ, flat_relRU hσ, fun l => ?_⟩
  rw [hm l, relRU_get, Option.map_map]
  congr 1
  funext ψ
  exact (erase_relU π ψ).symm

theorem hash_relRU {ρ₁ ρ₂ : ResU L} (h : ρ₁.Hash ρ₂) : (relRU π ρ₁).Hash (relRU π ρ₂) := by
  obtain ⟨hc, ρ, hρ, hv⟩ := h
  exact ⟨compat_relRU (natCompatS π) hc, relRU π ρ, compS_relRU hρ, valid_relRU hv⟩

theorem flatAt_relRU {ρ : ResU L} {l : Loc} {ψ : CellU L} (h : ρ.FlatAt l ψ) :
    (relRU π ρ).FlatAt l (relU π ψ) := by
  obtain ⟨σ, hσ, e⟩ := h
  exact ⟨relRU π σ, flat_relRU hσ, by rw [relRU_get, e]; rfl⟩

theorem noOwn_relRU {ρ : ResU L} (h : NoOwn ρ) : NoOwn (relRU π ρ) := by
  intro l ψ' e
  rw [relRU_get] at e
  obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp e
  rw [kind_relU]
  exact h l ψ hψ

end Resources

/-! ### Resources, invariance -/

section Invariance
variable (π : L ≃o L)

theorem compS_relRU_iff {ρ₁ ρ₂ ρ : ResU L} :
    ResU.CompS (relRU π ρ₁) (relRU π ρ₂) (relRU π ρ) ↔ ResU.CompS ρ₁ ρ₂ ρ := by
  refine ⟨fun h => ?_, compS_relRU⟩
  have := compS_relRU (π := π.symm) h
  rwa [relRU_symm_relRU, relRU_symm_relRU, relRU_symm_relRU] at this

theorem valid_relRU_iff {ρ : ResU L} : (relRU π ρ).Valid ↔ ρ.Valid := by
  refine ⟨fun h => ?_, valid_relRU⟩
  have := valid_relRU (π := π.symm) h
  rwa [relRU_symm_relRU] at this

theorem lower_relRU_iff {ρ : ResU L} {m : Loc → Option Val} : (relRU π ρ).Lower m ↔ ρ.Lower m := by
  refine ⟨fun h => ?_, lower_relRU⟩
  have := lower_relRU (π := π.symm) h
  rwa [relRU_symm_relRU] at this

theorem hash_relRU_iff {ρ₁ ρ₂ : ResU L} : (relRU π ρ₁).Hash (relRU π ρ₂) ↔ ρ₁.Hash ρ₂ := by
  refine ⟨fun h => ?_, hash_relRU⟩
  have := hash_relRU (π := π.symm) h
  rwa [relRU_symm_relRU, relRU_symm_relRU] at this

theorem flatAt_relRU_iff {ρ : ResU L} {l : Loc} {ψ : CellU L} :
    (relRU π ρ).FlatAt l (relU π ψ) ↔ ρ.FlatAt l ψ := by
  refine ⟨fun h => ?_, flatAt_relRU⟩
  have := flatAt_relRU (π := π.symm) h
  rwa [relRU_symm_relRU, relU_symm_relU] at this

theorem noOwn_relRU_iff {ρ : ResU L} : NoOwn (relRU π ρ) ↔ NoOwn ρ := by
  refine ⟨fun h => ?_, noOwn_relRU⟩
  have := noOwn_relRU (π := π.symm) h
  rwa [relRU_symm_relRU] at this

theorem updImm_relRU_iff {ρ₁ ρ₂ : ResU L} :
    (relRU π ρ₁).UpdImm (relRU π ρ₂) ↔ ρ₁.UpdImm ρ₂ := by
  constructor
  · intro h l ψ hk
    rw [← flatAt_relRU_iff π, ← flatAt_relRU_iff π (ρ := ρ₂)]
    exact h l _ (by rw [kind_relU, hk])
  · intro h l ψ' hk
    rw [← relU_relU_symm π ψ', flatAt_relRU_iff, flatAt_relRU_iff]
    refine h l _ ?_
    rw [← kind_relU π, relU_relU_symm]; exact hk

theorem img_injective : Function.Injective (img (L := L) π) := by
  intro P Q h
  funext u σ
  have := congrFun (congrFun h u) (relRU π σ)
  rw [img_apply, img_apply] at this
  exact this

theorem img_img_symm (P : Val → ResU L → Prop) : img π (img π.symm P) = P := by
  funext u σ
  apply propext
  conv_lhs => rw [← relRU_relRU_symm π σ]
  rw [img_apply, img_apply]

theorem updMut_key {ρ : ResU L} (l : Loc) (b : L) (P : Val → ResU L → Prop) :
    (∃ ψ', (relRU π ρ).FlatAt l ψ' ∧ ψ'.kind = .mut ∧ ψ'.lts = {π b} ∧ ψ'.pu = img π P) ↔
    (∃ ψ, ρ.FlatAt l ψ ∧ ψ.kind = .mut ∧ ψ.lts = {b} ∧ ψ.pu = P) := by
  constructor
  · rintro ⟨ψ', hf, hk, hl, hp⟩
    refine ⟨relU π.symm ψ', ?_, ?_, ?_, ?_⟩
    · rw [← flatAt_relRU_iff π, relU_relU_symm]; exact hf
    · rw [kind_relU]; exact hk
    · apply mapS_injective π
      rw [← lts_relU, relU_relU_symm, hl]; rfl
    · apply img_injective π
      rw [← pu_relU, relU_relU_symm, hp]
  · rintro ⟨ψ, hf, hk, hl, hp⟩
    refine ⟨relU π ψ, (flatAt_relRU_iff π).mpr hf, by rw [kind_relU, hk], ?_, ?_⟩
    · rw [lts_relU, hl]; rfl
    · rw [pu_relU, hp]

theorem updMut_relRU_iff {ρ₁ ρ₂ : ResU L} :
    (relRU π ρ₁).UpdMut (relRU π ρ₂) ↔ ρ₁.UpdMut ρ₂ := by
  constructor
  · intro h l b P
    rw [← updMut_key π l b P, ← updMut_key π (ρ := ρ₂) l b P]
    exact h l (π b) (img π P)
  · intro h l b' P'
    have hb : b' = π (π.symm b') := (π.apply_symm_apply b').symm
    have hP : P' = img π (img π.symm P') := (img_img_symm π P').symm
    rw [hb, hP, updMut_key π, updMut_key π]
    exact h l _ _

theorem updV_relRU_iff {ρ₁ ρ₂ : ResU L} :
    (relRU π ρ₁).UpdV (relRU π ρ₂) ↔ ρ₁.UpdV ρ₂ := by
  unfold ResU.UpdV
  rw [updImm_relRU_iff, updMut_relRU_iff, valid_relRU_iff, valid_relRU_iff]

end Invariance

/-! ### Propositions -/

section Props
variable (π : L ≃o L)

theorem pureN_relRU_iff (p : Prop) (ρ : ResU L) : pureN p (relRU π ρ) ↔ pureN p ρ := by
  unfold pureN
  rw [relRU_eq_empty]

theorem ptoOwnN_relRU_iff (l : Loc) (v : Val) (ρ : ResU L) :
    ptoOwnN l v (relRU π ρ) ↔ ptoOwnN l v ρ := by
  unfold ptoOwnN
  constructor
  · intro h
    rw [← relRU_symm_relRU π ρ, h, relRU_single]
    rfl
  · intro h
    rw [h, relRU_single]
    rfl

theorem sepN_relRU_iff {P P' Q Q' : WPropN L} (hP : ∀ σ, P' (relRU π σ) ↔ P σ)
    (hQ : ∀ σ, Q' (relRU π σ) ↔ Q σ) (ρ : ResU L) :
    sepN P' Q' (relRU π ρ) ↔ sepN P Q ρ := by
  constructor
  · rintro ⟨ρ₁', ρ₂', hc, h₁, h₂⟩
    obtain ⟨ρ₁, rfl⟩ := relRU_surjective π ρ₁'
    obtain ⟨ρ₂, rfl⟩ := relRU_surjective π ρ₂'
    exact ⟨ρ₁, ρ₂, (compS_relRU_iff π).mp hc, (hP ρ₁).mp h₁, (hQ ρ₂).mp h₂⟩
  · rintro ⟨ρ₁, ρ₂, hc, h₁, h₂⟩
    exact ⟨relRU π ρ₁, relRU π ρ₂, compS_relRU hc, (hP ρ₁).mpr h₁, (hQ ρ₂).mpr h₂⟩

theorem wandN_relRU_iff {P P' Q Q' : WPropN L} (hP : ∀ σ, P' (relRU π σ) ↔ P σ)
    (hQ : ∀ σ, Q' (relRU π σ) ↔ Q σ) (ρ : ResU L) :
    wandN P' Q' (relRU π ρ) ↔ wandN P Q ρ := by
  constructor
  · intro h ρ₁ ρ₂ h₁ hc
    exact (hQ ρ₂).mp (h (relRU π ρ₁) (relRU π ρ₂) ((hP ρ₁).mpr h₁) (compS_relRU hc))
  · intro h ρ₁' ρ₂' h₁ hc
    obtain ⟨ρ₁, rfl⟩ := relRU_surjective π ρ₁'
    obtain ⟨ρ₂, rfl⟩ := relRU_surjective π ρ₂'
    exact (hQ ρ₂).mpr (h ρ₁ ρ₂ ((hP ρ₁).mp h₁) ((compS_relRU_iff π).mp hc))

theorem exN_relRU_iff {A : Type} {Φ Φ' : A → WPropN L}
    (h : ∀ x σ, Φ' x (relRU π σ) ↔ Φ x σ) (ρ : ResU L) :
    exN Φ' (relRU π ρ) ↔ exN Φ ρ :=
  exists_congr fun x => h x ρ

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- `wp` is carried by `π`: the frame quantifier at the moved resource is the frame quantifier
at the original one, moved. -/
theorem wpN_relRU (e : Expr) {Q Q' : Val → WPropN L} (hQ : ∀ v σ, Q' v (relRU π σ) ↔ Q v σ)
    {ρ : ResU L} (h : wpN (ℍ := ℍ) e Q ρ) : wpN (ℍ := ℍ) e Q' (relRU π ρ) := by
  intro ρf' hf'
  obtain ⟨ρf, rfl⟩ := relRU_surjective π ρf'
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, πr, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁,
    h₁₂⟩ := h ρf ((hash_relRU_iff π).mp hf')
  exact ⟨relRU π ρ', relRU π ρp, relRU π fρ, relRU π fρ', relRU π fρ'p, relRU π πr, v, μ, μ',
    hash_relRU h₁, compS_relRU h₂, hash_relRU h₃, compS_relRU h₄, lower_relRU h₅,
    compS_relRU h₆, lower_relRU h₇, h₈, compS_relRU h₉, (updV_relRU_iff π).mpr h₁₀,
    noOwn_relRU h₁₁, (hQ v ρ').mpr h₁₂⟩

/-- **`wp` is invariant**: if `Q′` at `π·σ` is `Q` at `σ`, then `wp(e){Q′}` at `π·ρ` is
`wp(e){Q}` at `ρ`. -/
theorem wpN_relRU_iff (e : Expr) {Q Q' : Val → WPropN L} (hQ : ∀ v σ, Q' v (relRU π σ) ↔ Q v σ)
    (ρ : ResU L) : wpN (ℍ := ℍ) e Q' (relRU π ρ) ↔ wpN (ℍ := ℍ) e Q ρ := by
  refine ⟨fun h => ?_, wpN_relRU π e hQ⟩
  have hQ' : ∀ v σ, Q v (relRU π.symm σ) ↔ Q' v σ := by
    intro v σ
    rw [← hQ v (relRU π.symm σ), relRU_relRU_symm]
  have := wpN_relRU π.symm e hQ' h
  rwa [relRU_symm_relRU] at this

end Props

end Nominal

end
