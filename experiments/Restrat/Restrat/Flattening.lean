import Restrat.Propositions

/-!
# Restrat — naturality of flattening, `✓`, `⟦ρ⟧`, `#` and `↭`

The two walks of [TR] p. 5 (`ex(ρ)_◐`, row 5.20; `ag(ρ)`, row 5.21) are graphs defined by mutual
induction.  Each is preserved (`exW_fwd`, `agW_fwd`) and reflected with its value moved
(`exW_bwd`, `agW_bwd`): the walk of a moved resource is the moved walk.  From them:

* `⦇ρ⦈` (`flat_fwd`, `flat_bwd`), `⦇ρ⦈(ℓ)` (`flatAt_iff`, `flatAt_image`);
* `✓ρ` (`valid_iff`), `⟦ρ⟧` (`lower_iff`: lifetimes erase), `ρ₁ # ρ₂` (`hash_iff`);
* both clauses of `↭` (`updImm_iff`, `updMut_iff`), and `↭` guarded and unguarded
  (`upd_iff`, `updV_iff`); `ρ⁺∣own = ∅` (`noOwn_iff`).
-/

noncomputable section

namespace Restrat
open BoCa.Fig16 BoCa.Fig16.BoLo

namespace Emb
variable {c : Life} {e : Emb c} {Loc Val : Type}

/-- The moved index list of a walk family. -/
def relL (e : Emb c) (w : List (Loc × ResU Loc Val)) : List (Loc × ResU Loc Val) :=
  w.map fun p => (p.1, e.relRU p.2)

@[simp] theorem relL_fst (w : List (Loc × ResU Loc Val)) :
    (e.relL w).map Prod.fst = w.map Prod.fst := by
  simp [relL]

@[simp] theorem relL_snd (w : List (Loc × ResU Loc Val)) :
    (e.relL w).map Prod.snd = (w.map Prod.snd).map e.relRU := by
  simp [relL]

theorem relRU_get_eq_some {ρ : ResU Loc Val} {l : Loc} {χ : CellU Loc Val}
    (h : (e.relRU ρ).get l = some χ) : ∃ ψ, ρ.get l = some ψ ∧ χ = e.relU ψ := by
  rw [relRU_get] at h
  obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨ψ, hψ, rfl⟩

/-! ### The exclusive walk -/

section Ex
variable {R : CellU Loc Val → CellU Loc Val → Prop}
  {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

theorem exW_fwd (hR : e.Nat2 R) (hC : e.Nat3 C) {ρ σ : ResU Loc Val} (h : ExW R C ρ σ) :
    ExW R C (e.relRU ρ) (e.relRU σ) := by
  refine ExW.rec (motive_1 := fun ρ σ _ => ExW R C (e.relRU ρ) (e.relRU σ))
    (motive_2 := fun ρ w _ => ExWits R C (e.relRU ρ) (e.relL w)) ?_ ?_ ?_ h
  · intro ρ σ nm b w hs _ hb hnm hσ ihw
    refine ExW.mk (w := e.relL w) ?_ ihw ?_ ?_ (comp_fwd hR hC hσ)
    · rw [relL_fst]; exact (sites_iff ρ _ _).mpr hs
    · rw [relL_snd]; exact bigComp_fwd hR hC hb
    · rw [← relRU_restrict, ← relRU_restrict]; exact comp_fwd hR hC hnm
  · intro ρ; exact ExWits.nil
  · intro ρ e' l w ψ hψ hk _ _ ihe ihw
    refine ExWits.cons (e.relU ψ) (by rw [relRU_get, hψ]; rfl) (by rw [kind_relU]; exact hk)
      ?_ ihw
    rw [wit_relU]; exact ihe

theorem exW_bwd (hR : e.Nat2 R) (hC : e.Nat3 C) {ρ : ResU Loc Val} {σ : ResU Loc Val}
    (h : ExW R C (e.relRU ρ) σ) : ∃ σ₀, σ = e.relRU σ₀ ∧ ExW R C ρ σ₀ := by
  refine ExW.rec
    (motive_1 := fun ρ' σ _ => ∀ ρ, ρ' = e.relRU ρ → ∃ σ₀, σ = e.relRU σ₀ ∧ ExW R C ρ σ₀)
    (motive_2 := fun ρ' w _ => ∀ ρ, ρ' = e.relRU ρ → ∃ w₀, w = e.relL w₀ ∧ ExWits R C ρ w₀)
    ?_ ?_ ?_ h ρ rfl
  · intro ρ' σ nm b w hs _ hb hnm hσ ihw ρ hρ
    subst hρ
    obtain ⟨w₀, rfl, hw₀⟩ := ihw ρ rfl
    rw [relL_snd] at hb
    obtain ⟨b₀, rfl, hb₀⟩ := bigComp_bwd hR hC hb
    rw [← relRU_restrict, ← relRU_restrict] at hnm
    obtain ⟨nm₀, rfl, hnm₀⟩ := comp_bwd hR hC hnm
    obtain ⟨σ₀, rfl, hσ₀⟩ := comp_bwd hR hC hσ
    refine ⟨σ₀, rfl, ExW.mk (w := w₀) ?_ hw₀ hb₀ hnm₀ hσ₀⟩
    rw [relL_fst] at hs; exact (sites_iff ρ _ _).mp hs
  · intro ρ' ρ _; exact ⟨[], rfl, ExWits.nil⟩
  · intro ρ' e' l w ψ hψ hk _ _ ihe ihw ρ hρ
    subst hρ
    obtain ⟨ψ₀, hψ₀, rfl⟩ := relRU_get_eq_some hψ
    obtain ⟨e₀, rfl, he₀⟩ := ihe ψ₀.wit (wit_relU e ψ₀)
    obtain ⟨w₀, rfl, hw₀⟩ := ihw ρ rfl
    exact ⟨(l, e₀) :: w₀, rfl,
      ExWits.cons ψ₀ hψ₀ (by rw [kind_relU] at hk; exact hk) he₀ hw₀⟩

end Ex

/-! ### The aliasable walk -/

theorem agW_fwd {ρ σ : ResU Loc Val} (h : AgW ρ σ) : AgW (e.relRU ρ) (e.relRU σ) := by
  refine AgW.rec (motive_1 := fun ρ σ _ => AgW (e.relRU ρ) (e.relRU σ))
    (motive_2 := fun ρ w _ => AgWitsM (e.relRU ρ) (e.relL w))
    (motive_3 := fun ρ w _ => AgWitsI (e.relRU ρ) (e.relL w)) ?_ ?_ ?_ ?_ ?_ h
  · intro ρ σ a bm bi wm wi hsm hsi _ _ hbm hbi ha hσ ihm ihi
    refine AgW.mk (bm := e.relRU bm) (wm := e.relL wm) (wi := e.relL wi) ?_ ?_ ihm ihi ?_ ?_ ?_
      (comp_fwd e.nat2R e.nat3R hσ)
    · rw [relL_fst]; exact (sites_iff ρ _ _).mpr hsm
    · rw [relL_fst]; exact (sites_iff ρ _ _).mpr hsi
    · rw [relL_snd]; exact bigComp_fwd e.nat2R e.nat3R hbm
    · rw [relL_snd]; exact bigComp_fwd e.nat2R e.nat3R hbi
    · rw [← relRU_restrict]; exact comp_fwd e.nat2R e.nat3R ha
  · intro ρ; exact AgWitsM.nil
  · intro ρ e' l w ψ hψ hk _ _ ihe ihw
    refine AgWitsM.cons (e.relU ψ) (by rw [relRU_get, hψ]; rfl) (by rw [kind_relU]; exact hk)
      ?_ ihw
    rw [wit_relU]; exact ihe
  · intro ρ; exact AgWitsI.nil
  · intro ρ p l w ψ hψ hk ex a hex _ hp _ iha ihw
    refine AgWitsI.cons (e.relU ψ) (by rw [relRU_get, hψ]; rfl) (by rw [kind_relU]; exact hk)
      (e.relRU ex) (e.relRU a) ?_ ?_ (comp_fwd e.nat2R e.nat3R hp) ihw
    · rw [wit_relU]; exact exW_fwd e.nat2R e.nat3R hex
    · rw [wit_relU]; exact iha

theorem agW_bwd {ρ : ResU Loc Val} {σ : ResU Loc Val} (h : AgW (e.relRU ρ) σ) :
    ∃ σ₀, σ = e.relRU σ₀ ∧ AgW ρ σ₀ := by
  refine AgW.rec
    (motive_1 := fun ρ' σ _ => ∀ ρ, ρ' = e.relRU ρ → ∃ σ₀, σ = e.relRU σ₀ ∧ AgW ρ σ₀)
    (motive_2 := fun ρ' w _ => ∀ ρ, ρ' = e.relRU ρ → ∃ w₀, w = e.relL w₀ ∧ AgWitsM ρ w₀)
    (motive_3 := fun ρ' w _ => ∀ ρ, ρ' = e.relRU ρ → ∃ w₀, w = e.relL w₀ ∧ AgWitsI ρ w₀)
    ?_ ?_ ?_ ?_ ?_ h ρ rfl
  · intro ρ' σ a bm bi wm wi hsm hsi _ _ hbm hbi ha hσ ihm ihi ρ hρ
    subst hρ
    obtain ⟨wm₀, rfl, hwm₀⟩ := ihm ρ rfl
    obtain ⟨wi₀, rfl, hwi₀⟩ := ihi ρ rfl
    rw [relL_snd] at hbm hbi
    obtain ⟨bm₀, rfl, hbm₀⟩ := bigComp_bwd e.nat2R e.nat3R hbm
    obtain ⟨bi₀, rfl, hbi₀⟩ := bigComp_bwd e.nat2R e.nat3R hbi
    rw [← relRU_restrict] at ha
    obtain ⟨a₀, rfl, ha₀⟩ := comp_bwd e.nat2R e.nat3R ha
    obtain ⟨σ₀, rfl, hσ₀⟩ := comp_bwd e.nat2R e.nat3R hσ
    refine ⟨σ₀, rfl, AgW.mk (wm := wm₀) (wi := wi₀) ?_ ?_ hwm₀ hwi₀ hbm₀ hbi₀ ha₀ hσ₀⟩
    · rw [relL_fst] at hsm; exact (sites_iff ρ _ _).mp hsm
    · rw [relL_fst] at hsi; exact (sites_iff ρ _ _).mp hsi
  · intro ρ' ρ _; exact ⟨[], rfl, AgWitsM.nil⟩
  · intro ρ' e' l w ψ hψ hk _ _ ihe ihw ρ hρ
    subst hρ
    obtain ⟨ψ₀, hψ₀, rfl⟩ := relRU_get_eq_some hψ
    obtain ⟨e₀, rfl, he₀⟩ := ihe ψ₀.wit (wit_relU e ψ₀)
    obtain ⟨w₀, rfl, hw₀⟩ := ihw ρ rfl
    exact ⟨(l, e₀) :: w₀, rfl,
      AgWitsM.cons ψ₀ hψ₀ (by rw [kind_relU] at hk; exact hk) he₀ hw₀⟩
  · intro ρ' ρ _; exact ⟨[], rfl, AgWitsI.nil⟩
  · intro ρ' p l w ψ hψ hk ex a hex _ hp _ iha ihw ρ hρ
    subst hρ
    obtain ⟨ψ₀, hψ₀, rfl⟩ := relRU_get_eq_some hψ
    rw [wit_relU] at hex
    obtain ⟨ex₀, rfl, hex₀⟩ := exW_bwd e.nat2R e.nat3R hex
    obtain ⟨a₀, rfl, ha₀⟩ := iha ψ₀.wit (wit_relU e ψ₀)
    obtain ⟨p₀, rfl, hp₀⟩ := comp_bwd e.nat2R e.nat3R hp
    obtain ⟨w₀, rfl, hw₀⟩ := ihw ρ rfl
    exact ⟨(l, p₀) :: w₀, rfl,
      AgWitsI.cons ψ₀ hψ₀ (by rw [kind_relU] at hk; exact hk) ex₀ a₀ hex₀ ha₀ hp₀ hw₀⟩

/-! ### `⦇ρ⦈`, `✓`, `⟦ρ⟧`, `#` -/

theorem flat_fwd {ρ σ : ResU Loc Val} (h : ResU.Flat ρ σ) :
    ResU.Flat (e.relRU ρ) (e.relRU σ) := by
  obtain ⟨ex, a, hex, ha, hσ⟩ := h
  exact ⟨_, _, exW_fwd e.nat2S e.nat3S hex, agW_fwd ha, comp_fwd e.nat2S e.nat3S hσ⟩

theorem flat_bwd {ρ σ : ResU Loc Val} (h : ResU.Flat (e.relRU ρ) σ) :
    ∃ σ₀, σ = e.relRU σ₀ ∧ ResU.Flat ρ σ₀ := by
  obtain ⟨ex, a, hex, ha, hσ⟩ := h
  obtain ⟨ex₀, rfl, hex₀⟩ := exW_bwd e.nat2S e.nat3S hex
  obtain ⟨a₀, rfl, ha₀⟩ := agW_bwd ha
  obtain ⟨σ₀, rfl, hσ₀⟩ := comp_bwd e.nat2S e.nat3S hσ
  exact ⟨σ₀, rfl, ex₀, a₀, hex₀, ha₀, hσ₀⟩

theorem flat_iff (ρ σ : ResU Loc Val) : ResU.Flat (e.relRU ρ) (e.relRU σ) ↔ ResU.Flat ρ σ := by
  refine ⟨fun h => ?_, flat_fwd⟩
  obtain ⟨σ₀, hσ, h₀⟩ := flat_bwd h
  rwa [e.relRU_injective hσ]

theorem valid_iff (ρ : ResU Loc Val) : (e.relRU ρ).Valid ↔ ρ.Valid := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨σ₀, -, h₀⟩ := flat_bwd hσ
    exact ⟨σ₀, h₀⟩
  · rintro ⟨σ, hσ⟩; exact ⟨_, flat_fwd hσ⟩

theorem lower_iff (ρ : ResU Loc Val) (m : Loc → Option Val) :
    (e.relRU ρ).Lower m ↔ ρ.Lower m := by
  constructor
  · rintro ⟨σ, hσ, hm⟩
    obtain ⟨σ₀, rfl, h₀⟩ := flat_bwd hσ
    refine ⟨σ₀, h₀, fun l => ?_⟩
    rw [hm l, relRU_get, Option.map_map]
    congr 1; funext ψ; exact erase_relU e ψ
  · rintro ⟨σ, hσ, hm⟩
    refine ⟨_, flat_fwd hσ, fun l => ?_⟩
    rw [hm l, relRU_get, Option.map_map]
    congr 1; funext ψ; exact (erase_relU e ψ).symm

theorem hash_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.Hash (e.relRU ρ₁) (e.relRU ρ₂) ↔ ResU.Hash ρ₁ ρ₂ := by
  constructor
  · rintro ⟨hc, ρ, hρ, hv⟩
    obtain ⟨ρ₀, rfl, h₀⟩ := comp_bwd e.nat2S e.nat3S hρ
    exact ⟨(compat_iff e.nat2S _ _).mp hc, ρ₀, h₀, (valid_iff ρ₀).mp hv⟩
  · rintro ⟨hc, ρ, hρ, hv⟩
    exact ⟨(compat_iff e.nat2S _ _).mpr hc, _, comp_fwd e.nat2S e.nat3S hρ, (valid_iff ρ).mpr hv⟩

theorem flatAt_image {ρ : ResU Loc Val} {l : Loc} {χ : CellU Loc Val}
    (h : (e.relRU ρ).FlatAt l χ) : ∃ ψ, χ = e.relU ψ ∧ ρ.FlatAt l ψ := by
  obtain ⟨σ, hσ, hl⟩ := h
  obtain ⟨σ₀, rfl, h₀⟩ := flat_bwd hσ
  obtain ⟨ψ, hψ, rfl⟩ := relRU_get_eq_some hl
  exact ⟨ψ, rfl, σ₀, h₀, hψ⟩

theorem flatAt_iff (ρ : ResU Loc Val) (l : Loc) (ψ : CellU Loc Val) :
    (e.relRU ρ).FlatAt l (e.relU ψ) ↔ ρ.FlatAt l ψ := by
  constructor
  · intro h
    obtain ⟨ψ', hψ', h'⟩ := flatAt_image h
    rwa [e.relU_injective hψ']
  · rintro ⟨σ, hσ, hl⟩
    exact ⟨_, flat_fwd hσ, by rw [relRU_get, hl]; rfl⟩

/-! ### `↭` -/

theorem updImm_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.UpdImm (e.relRU ρ₁) (e.relRU ρ₂) ↔ ResU.UpdImm ρ₁ ρ₂ := by
  constructor
  · intro h l s v χ hχ
    have := h l (e.mapL s) v (e.relRU χ) ((e.inStratum_relRU _ _).mpr hχ)
    rw [← e.relU_immOf, flatAt_iff, flatAt_iff] at this
    exact this
  · intro h l s v χ hχ
    constructor
    · intro k
      obtain ⟨ψ, hψ, k₀⟩ := flatAt_image k
      rw [hψ]; refine (flatAt_iff _ _ _).mpr ?_
      rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s₀, u, τ, m, rfl⟩ | ⟨b, u, τ, m, Q, w, rfl⟩
      · exact absurd hψ.symm (by rw [relU_ownOf]; exact CellU.ownOf_ne_immOf)
      · exact (h l s₀ u τ m).mp k₀
      · rw [e.relU_mutOf] at hψ; exact absurd hψ CellU.immOf_ne_mutOf
    · intro k
      obtain ⟨ψ, hψ, k₀⟩ := flatAt_image k
      rw [hψ]; refine (flatAt_iff _ _ _).mpr ?_
      rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s₀, u, τ, m, rfl⟩ | ⟨b, u, τ, m, Q, w, rfl⟩
      · exact absurd hψ.symm (by rw [relU_ownOf]; exact CellU.ownOf_ne_immOf)
      · exact (h l s₀ u τ m).mpr k₀
      · rw [e.relU_mutOf] at hψ; exact absurd hψ CellU.immOf_ne_mutOf

theorem relS_injective (b : Life) :
    Function.Injective (e.relS (Loc := Loc) (Val := Val) b) := by
  intro P Q h
  funext x r
  have := congrFun (congrFun h x) ⟨e.relRU r.val, (e.inStratum_relRU _ _).mpr r.property⟩
  exact propext ((e.relS_iff P x r.val r.property _).symm.trans
    ((Iff.of_eq this).trans (e.relS_iff Q x r.val r.property _)))

/-- A `mut` cell of a moved flattening sits at a moved lifetime. -/
theorem flatAt_mut_lifetime {ρ : ResU Loc Val} {l : Loc} {b : Life} {v : Val}
    {χ : ResU Loc Val} {hχ : χ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, hχ⟩}
    (k : (e.relRU ρ).FlatAt l (CellU.mutOf b v χ hχ P hw)) : ∃ b₀, e b₀ = b := by
  obtain ⟨ψ, hψ, -⟩ := flatAt_image k
  have := congrArg CellU.at hψ
  rw [at_relU, CellU.at_mutOf] at this
  exact ⟨_, this.symm⟩

/-- …and it is the moved cell, invariant included. -/
theorem flatAt_mut_moved {ρ : ResU Loc Val} {l : Loc} {b₀ : Life} {v : Val}
    {χ : ResU Loc Val} {hχ : χ.InStratum (e b₀)} {P : Val → SPropS Loc Val (e b₀)}
    {hw : P v ⟨χ, hχ⟩} (k : (e.relRU ρ).FlatAt l (CellU.mutOf (e b₀) v χ hχ P hw)) :
    ∃ (Q : Val → SPropS Loc Val b₀) (χ₀ : ResU Loc Val) (hχ₀ : χ₀.InStratum b₀)
      (hw₀ : Q v ⟨χ₀, hχ₀⟩), P = e.relS b₀ Q ∧ χ = e.relRU χ₀ ∧
        ρ.FlatAt l (CellU.mutOf b₀ v χ₀ hχ₀ Q hw₀) := by
  obtain ⟨ψ, hψ, k₀⟩ := flatAt_image k
  rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s₀, u, τ, m, rfl⟩ | ⟨b₁, u, τ, m, Q, w, rfl⟩
  · exact absurd hψ.symm (by rw [relU_ownOf]; exact CellU.ownOf_ne_mutOf)
  · rw [e.relU_immOf] at hψ; exact absurd hψ.symm CellU.immOf_ne_mutOf
  · rw [e.relU_mutOf] at hψ
    have hb : e b₀ = e b₁ := CellU.mutOf_at hψ
    have hb' := e.injective hb
    subst hb'
    obtain ⟨hv, hτ, hQ⟩ := CellU.mutOf_inj hψ
    subst hv
    exact ⟨Q, τ, m, w, hQ, hτ, k₀⟩

theorem updMut_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.UpdMut (e.relRU ρ₁) (e.relRU ρ₂) ↔ ResU.UpdMut ρ₁ ρ₂ := by
  have moveIn : ∀ {ρ : ResU Loc Val} {l : Loc} {b : Life} {P : Val → SPropS Loc Val b},
      (∃ (v : Val) (χ : ResU Loc Val) (hχ : χ.InStratum b) (hw : P v ⟨χ, hχ⟩),
        ρ.FlatAt l (CellU.mutOf b v χ hχ P hw)) →
      (∃ (v : Val) (χ : ResU Loc Val) (hχ : χ.InStratum (e b)) (hw : e.relS b P v ⟨χ, hχ⟩),
        (e.relRU ρ).FlatAt l (CellU.mutOf (e b) v χ hχ (e.relS b P) hw)) := by
    rintro ρ l b P ⟨v, χ, hχ, hw, k⟩
    refine ⟨v, e.relRU χ, _, e.relS_holds hχ hw, ?_⟩
    have := (flatAt_iff (e := e) ρ l _).mpr k
    rw [e.relU_mutOf] at this
    exact this
  have moveOut : ∀ {ρ : ResU Loc Val} {l : Loc} {b : Life} {P : Val → SPropS Loc Val b},
      (∃ (v : Val) (χ : ResU Loc Val) (hχ : χ.InStratum (e b)) (hw : e.relS b P v ⟨χ, hχ⟩),
        (e.relRU ρ).FlatAt l (CellU.mutOf (e b) v χ hχ (e.relS b P) hw)) →
      (∃ (v : Val) (χ : ResU Loc Val) (hχ : χ.InStratum b) (hw : P v ⟨χ, hχ⟩),
        ρ.FlatAt l (CellU.mutOf b v χ hχ P hw)) := by
    rintro ρ l b P ⟨v, χ, hχ, hw, k⟩
    obtain ⟨Q, χ₀, hχ₀, hw₀, hPQ, -, k₀⟩ := flatAt_mut_moved k
    have := relS_injective b hPQ
    subst this
    exact ⟨v, χ₀, hχ₀, hw₀, k₀⟩
  constructor
  · intro h l b P
    exact ⟨fun k => moveOut ((h l (e b) (e.relS b P)).mp (moveIn k)),
      fun k => moveOut ((h l (e b) (e.relS b P)).mpr (moveIn k))⟩
  · intro h l b P
    constructor
    · intro k
      obtain ⟨v, χ, hχ, hw, k'⟩ := k
      obtain ⟨b₀, rfl⟩ := flatAt_mut_lifetime k'
      obtain ⟨Q, χ₀, hχ₀, hw₀, rfl, rfl, k₀⟩ := flatAt_mut_moved k'
      exact moveIn ((h l b₀ Q).mp ⟨v, χ₀, hχ₀, hw₀, k₀⟩)
    · intro k
      obtain ⟨v, χ, hχ, hw, k'⟩ := k
      obtain ⟨b₀, rfl⟩ := flatAt_mut_lifetime k'
      obtain ⟨Q, χ₀, hχ₀, hw₀, rfl, rfl, k₀⟩ := flatAt_mut_moved k'
      exact moveIn ((h l b₀ Q).mpr ⟨v, χ₀, hχ₀, hw₀, k₀⟩)

theorem upd_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.Upd (e.relRU ρ₁) (e.relRU ρ₂) ↔ ResU.Upd ρ₁ ρ₂ :=
  and_congr (updImm_iff ρ₁ ρ₂) (updMut_iff ρ₁ ρ₂)

theorem updV_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.UpdV (e.relRU ρ₁) (e.relRU ρ₂) ↔ ResU.UpdV ρ₁ ρ₂ :=
  and_congr (upd_iff ρ₁ ρ₂) (and_congr (valid_iff ρ₁) (valid_iff ρ₂))

theorem noOwn_iff (ρ : WRes) : NoOwn (e.relRU ρ) ↔ NoOwn ρ := by
  unfold NoOwn
  rw [← relRU_restrict]
  exact e.relRU_eq_empty

end Emb

end Restrat
