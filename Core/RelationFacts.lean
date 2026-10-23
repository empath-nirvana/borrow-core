import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Lifetimes.Interpretation
import Support.Lifetimes.Substitution
import Support.Lifetimes.Terms
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts
import Support.Model.AlgebraInstances
import Support.Model.Ancestors
import Support.Model.Cells
import Support.Model.FlatteningCells
import Support.Model.Outlives
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.ReborrowFrame
import Support.Model.Singletons
import Support.Model.Update
import Support.Model.Walks
import Core.Images
import Core.Invariant
import Core.FrameRecords
import Core.Relation
import Core.World
import Core.Wp
import Core.RelMu

/-!
# Core — RelationFacts  `[spec §3, §4]`

`Support/TypedWorld`'s layer `RelationFacts`, with records typed at `VTy`.  The repaired relation `vC` read at substitutions: monotonicity, the `imm` cell at the observable view, reading, writing and making a `mut` cell, 6.60 at `vC`, congruence in `δ`, and the choosers' inputs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A fresh extension on the left is invisible. -/
theorem TyEq.extend_left {S S' : VTy} {δ δ' : LSub} {x : LifeVar} (hx : ¬ VFree x S) (β : Life)
    (h : TyEq S δ S' δ') : TyEq S (δ.extend x β) S' δ' :=
  (TyEq.of_agree S (fun y hy => find?_extend_ne δ β (fun e => hx (by rw [e]; exact hy)))).trans h

/-- `Imm̲` with payload substitutions respects `TyEq`. -/
theorem TyEq.immG {c c' : Lifetime.Life} {δ δ' : LSub} (hc : c.interp δ = c'.interp δ') :
    ∀ (A : VTy) {A' : VTy} (pay pay' : Nat → VTy), TyEq A δ A' δ' →
      (∀ n, TyEq (pay n) δ (pay' n) δ') → TyEq (VTy.immG c pay A) δ (VTy.immG c' pay' A') δ' := by
  intro A
  induction A using VTy.recV with
  | unit => intro A' _ _ h _; cases A' <;> simp_all [TyEq, VTy.immG]
  | int w => intro A' _ _ h _; cases A' <;> simp_all [TyEq, VTy.immG]
  | opq k => intro A' _ _ h _; cases A' <;> simp_all [TyEq, VTy.immG]
  | zero => intro A' _ _ h _; cases A' <;> simp_all [TyEq, VTy.immG]
  | unk => intro A' _ _ h _; cases A' <;> simp_all [TyEq, VTy.immG]
  | thunk C => intro A' _ _ h _; cases A' <;> simp_all [TyEq, VTy.immG]
  | tvar n => intro A' _ _ h _; cases A' <;> simp_all [TyEq, VTy.immG]
  | tensor A B ihA ihB =>
      intro A' pay pay' h hp; cases A' <;> simp only [TyEq] at h
      exact ⟨ihA pay pay' h.1 hp, ihB pay pay' h.2 hp⟩
  | sum A B ihA ihB =>
      intro A' pay pay' h hp; cases A' <;> simp only [TyEq] at h
      exact ⟨ihA pay pay' h.1 hp, ihB pay pay' h.2 hp⟩
  | ref A _ =>
      intro A' pay pay' h hp; cases A' <;> simp only [TyEq] at h
      exact ⟨hc, TyEq.subst A pay pay' h hp⟩
  | bang A _ =>
      intro A' pay pay' h hp; cases A' <;> simp only [TyEq] at h
      exact TyEq.subst A pay pay' h hp
  | imm a A _ =>
      intro A' pay pay' h hp; cases A' <;> simp only [TyEq] at h
      exact ⟨h.1, TyEq.subst A pay pay' h.2 hp⟩
  | «mut» a A _ =>
      intro A' pay pay' h hp; cases A' <;> simp only [TyEq] at h
      exact ⟨hc, TyEq.subst A pay pay' h.2 hp⟩
  | box a A ih =>
      intro A' pay pay' h hp; cases A' <;> simp only [TyEq] at h
      simp only [VTy.immG]
      exact ih pay pay' h.2 hp
  | fam A ih =>
      intro A' pay pay' h hp; cases A' <;> simp only [TyEq] at h
      simp only [VTy.immG]
      exact ih pay pay' h hp
  | mu A ih =>
      intro A' pay pay' h hp; cases A' <;> simp only [TyEq] at h
      refine ih _ _ h (fun n => ?_)
      cases n with
      | zero => exact TyEq.subst (.mu A) pay pay' (show TyEq (.mu A) _ (.mu _) _ from h) hp
      | succ n => exact hp n

theorem TyEq.immReborrow {S S' : VTy} {δ δ' : LSub} {c c' : Lifetime.Life}
    (hc : c.interp δ = c'.interp δ') (h : TyEq S δ S' δ') :
    TyEq (S.immReborrow c) δ (S'.immReborrow c') δ' := by
  rw [VTy.immReborrow_eq_immG, VTy.immReborrow_eq_immG]
  exact TyEq.immG hc S _ _ h (fun n => show n = n from rfl)

mutual
/-- `Δ-subst` at `TyEq`: `vDen_applyLSub`'s induction, the `∀` case, now at `CTy`, with its
two branches. -/
theorem TyEq.applyLSub : ∀ (T : VTy) (σ : Lifetime.LSubst) (δ δ' : LSub),
    (∀ y, VFree y T → ((Lifetime.Life.var y).applySub σ).interp δ = δ'.find? y) →
      TyEq (T.applyLSub σ) δ T δ'
  | .unit, _, _, _, _ => trivial
  | .int _, _, _, _, _ => rfl
  | .opq _, _, _, _, _ => rfl
  | .zero, _, _, _, _ => trivial
  | .unk, _, _, _, _ => trivial
  | .ref T, σ, δ, δ', h => TyEq.applyLSub T σ δ δ' h
  | .bang T, σ, δ, δ', h => TyEq.applyLSub T σ δ δ' h
  | .fam T, σ, δ, δ', h => TyEq.applyLSub T σ δ δ' h
  | .thunk C, σ, δ, δ', h => CTyEq.applyLSub C σ δ δ' h
  | .sum T₁ T₂, σ, δ, δ', h =>
      ⟨TyEq.applyLSub T₁ σ δ δ' (fun y hy => h y (Or.inl hy)),
       TyEq.applyLSub T₂ σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .tensor T₁ T₂, σ, δ, δ', h =>
      ⟨TyEq.applyLSub T₁ σ δ δ' (fun y hy => h y (Or.inl hy)),
       TyEq.applyLSub T₂ σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .imm a T, σ, δ, δ', h =>
      ⟨interp_applySub a (fun y hy => h y (Or.inl hy)),
       TyEq.applyLSub T σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .mut a T, σ, δ, δ', h =>
      ⟨interp_applySub a (fun y hy => h y (Or.inl hy)),
       TyEq.applyLSub T σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .box a T, σ, δ, δ', h =>
      ⟨interp_applySub a (fun y hy => h y (Or.inl hy)),
       TyEq.applyLSub T σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .tvar _, _, _, _, _ => rfl
  | .mu T, σ, δ, δ', h => TyEq.applyLSub T σ δ δ' h
theorem CTyEq.applyLSub : ∀ (C : CTy) (σ : Lifetime.LSubst) (δ δ' : LSub),
    (∀ y, CFree y C → ((Lifetime.Life.var y).applySub σ).interp δ = δ'.find? y) →
      CTyEq (C.applyLSub σ) δ C δ'
  | .ret A, σ, δ, δ', h => TyEq.applyLSub A σ δ δ' h
  | .arr A C, σ, δ, δ', h =>
      ⟨TyEq.applyLSub A σ δ δ' (fun y hy => h y (Or.inl hy)),
       CTyEq.applyLSub C σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .amp C D, σ, δ, δ', h =>
      ⟨CTyEq.applyLSub C σ δ δ' (fun y hy => h y (Or.inl hy)),
       CTyEq.applyLSub D σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .top, _, _, _, _ => trivial
  | .nu C, σ, δ, δ', h => CTyEq.applyLSub C σ δ δ' h
  | .eff _ _ _ _ A B fin C, σ, δ, δ', h =>
      ⟨rfl, rfl, rfl, rfl, TyEq.applyLSub A σ δ δ' (fun y hy => h y (Or.inl hy)),
       TyEq.applyLSub B σ δ δ' (fun y hy => h y (Or.inr (Or.inl hy))),
       CTyEq.applyLSub fin σ δ δ' (fun y hy => h y (Or.inr (Or.inr (Or.inl hy)))),
       CTyEq.applyLSub C σ δ δ' (fun y hy => h y (Or.inr (Or.inr (Or.inr hy))))⟩
  | .all y b S, σ, δ, δ', h => by
      have hb : (b.applySub σ).interp δ = b.interp δ' :=
        interp_applySub b (fun w hw => h w (Or.inl hw))
      cases hcap : lsubCaptures (lsubDrop σ y) y with
      | false =>
          rw [CTy.applyLSub_all_not_captures hcap]
          refine ⟨hb, fun α => ?_⟩
          refine CTyEq.applyLSub S _ _ _ (fun w hw => ?_)
          by_cases hwy : w = y
          · subst hwy
            rw [applySub_var_none (assocFind_lsubDrop_self w σ)]
            show (δ.extend w α).find? w = (δ'.extend w α).find? w
            rw [find?_extend_self, find?_extend_self]
          · have hvar : (Lifetime.Life.var w).applySub (lsubDrop σ y)
                = (Lifetime.Life.var w).applySub σ := by
              simp only [Lifetime.Life.applySub, assocFind_lsubDrop_ne hwy σ]
            have hcm : ((Lifetime.Life.var w).applySub σ).mentions y = false := by
              cases hf : Lifetime.assocFind w (lsubDrop σ y) with
              | none =>
                  rw [← hvar, applySub_var_none hf]
                  simp only [Lifetime.Life.mentions, beq_eq_false_iff_ne, ne_eq]
                  exact Ne.symm hwy
              | some d =>
                  rw [← hvar, applySub_var_some hf]
                  exact not_mentions_of_lsubCaptures hcap hf
            rw [hvar, interp_extend_of_not_mentions hcm, h w (Or.inr ⟨hwy, hw⟩),
              find?_extend_ne δ' α (Ne.symm hwy)]
      | true =>
          obtain ⟨z, hzy, hzr, hzS, hty⟩ :
              ∃ z, y < z ∧ lsubRangeBound (lsubDrop σ y) ≤ z ∧ S.lifeBound ≤ z ∧
                (CTy.all y b S).applyLSub σ
                  = CTy.all z (b.applySub σ)
                      (S.applyLSub ((y, Lifetime.Life.var z) :: lsubDrop σ y)) :=
            ⟨_, Nat.lt_of_lt_of_le (Nat.lt_succ_self y) (Nat.le_max_left _ _),
              Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
              Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _),
              CTy.applyLSub_all_captures hcap⟩
          rw [hty]
          refine ⟨hb, fun α => ?_⟩
          refine CTyEq.applyLSub S _ _ _ (fun w hw => ?_)
          by_cases hwy : w = y
          · subst hwy
            rw [applySub_var_some
              (show Lifetime.assocFind w ((w, Lifetime.Life.var z) :: lsubDrop σ w)
                  = some (Lifetime.Life.var z) from by simp [Lifetime.assocFind])]
            show (δ.extend z α).find? z = (δ'.extend w α).find? w
            rw [find?_extend_self, find?_extend_self]
          · have hvar : (Lifetime.Life.var w).applySub
                  ((y, Lifetime.Life.var z) :: lsubDrop σ y)
                = (Lifetime.Life.var w).applySub σ := by
              simp only [Lifetime.Life.applySub, Lifetime.assocFind,
                if_neg (Ne.symm hwy), assocFind_lsubDrop_ne hwy σ]
            have hcm : ((Lifetime.Life.var w).applySub σ).mentions z = false := by
              cases hf : Lifetime.assocFind w (lsubDrop σ y) with
              | none =>
                  have hfσ : Lifetime.assocFind w σ = none := by
                    rw [← assocFind_lsubDrop_ne hwy σ]; exact hf
                  rw [applySub_var_none hfσ]
                  exact not_mentions_of_varBound_le
                    (Nat.lt_of_lt_of_le (lt_cLifeBound hw) hzS)
              | some d =>
                  have hfσ : Lifetime.assocFind w σ = some d := by
                    rw [← assocFind_lsubDrop_ne hwy σ]; exact hf
                  rw [applySub_var_some hfσ]
                  exact not_mentions_of_varBound_le
                    (Nat.le_trans (varBound_le_lsubRangeBound hf) hzr)
            rw [hvar, interp_extend_of_not_mentions hcm, h w (Or.inr ⟨hwy, hw⟩),
              find?_extend_ne δ' α (Ne.symm hwy)]
end

/-- The substitution `[@a/'x]` at `δ` is `δ['x↦@aδ]`, variable by variable. -/
theorem instLife_var (x : LifeVar) (a : Lifetime.Life) {δ : LSub} {α : Life}
    (ha : a.interp δ = some α) (y : LifeVar) :
    ((Lifetime.Life.var y).applySub [(x, a)]).interp δ = (δ.extend x α).find? y := by
  by_cases hxy : x = y
  · subst hxy
    rw [applySub_var_some
      (show Lifetime.assocFind x [(x, a)] = some a from by simp [Lifetime.assocFind])]
    rw [ha, find?_extend_self]
  · rw [applySub_var_none
      (show Lifetime.assocFind y [(x, a)] = none from by
        simp only [Lifetime.assocFind, if_neg hxy])]
    show δ.find? y = _
    rw [find?_extend_ne δ α hxy]

/-- `A[@a/'x]` at `δ` is `A` at `δ['x↦@aδ]`. -/
theorem TyEq.instLife (x : LifeVar) (a : Lifetime.Life) (T : VTy) {δ : LSub} {α : Life}
    (ha : a.interp δ = some α) : TyEq (VTy.instLife x a T) δ T (δ.extend x α) :=
  TyEq.applyLSub T [(x, a)] δ (δ.extend x α) (fun y _ => instLife_var x a ha y)

/-- `C[@a/'x]` at `δ` is `C` at `δ['x↦@aδ]`. -/
theorem CTyEq.instLife (x : LifeVar) (a : Lifetime.Life) (C : CTy) {δ : LSub} {α : Life}
    (ha : a.interp δ = some α) : CTyEq (CTy.instLife x a C) δ C (δ.extend x α) :=
  CTyEq.applyLSub C [(x, a)] δ (δ.extend x α) (fun y _ => instLife_var x a ha y)

theorem cohE_keeps {rs rs' : List FrameRec} {l : Loc} {S : VTy} {δ : LSub} {ψ : CellU Loc Val}
    (hk : Keeps rs rs' (ResU.single l ψ)) (hψ : ψ.kind = Kind.imm) (h : CohE rs l S δ) :
    CohE rs' l S δ := by
  obtain ⟨S₀, δ₀, he, hc⟩ := h
  exact ⟨S₀, δ₀, he, coh_keeps hk hψ hc⟩

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `vC` is stable along `Ext`, in both modes: at a `mut` cell the stored list is kept, so
the predicate stays equal; the `U` clause is Kripke in the list, and that of the
observable view is `True`. -/
theorem vC_local : ∀ (b : Bool) (T : VTy) {ls ls' : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    Ext ls ls' ρ → vC b T ls δ v ρ → vC b T ls' δ v ρ := by
  intro b T ls ls' δ v ρ hk h
  refine vC_ind δ (fun b T ls v ρ => ∀ ls', Ext ls ls' ρ → vC b T ls' δ v ρ) ?_ b T ls v ρ h ls' hk
  intro b T ls v ρ h ls' hk
  cases T with
  | unit => exact h
  | int w => exact h
  | opq k => exact h
  | tensor T₁ T₂ =>
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      have hk' := hk.right hc
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁.2 _ (hk'.left hc'), h₂.2 _ (hk'.right hc')⟩
  | sum T₁ T₂ =>
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, h₁.2 _ (hk.right hc)⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, h₂.2 _ (hk.right hc)⟩
  | zero => exact h
  | thunk C =>
      cases b
      · exact h
      · exact fun ls'' hk' => h ls'' (hk.trans hk')
  | bang T => exact ⟨h.1, h.2.2 _ hk⟩
  | box a T =>
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, hb.2 _ hk, ho⟩
  | ref T =>
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂.2 _ ((hk.right hc).right hc')⟩
  | imm a T =>
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, hcoh⟩, s, u, σ, hs, ls₀, hρ₁, hP, hαs, hls₀⟩ := h
      subst hρ₀
      have hρ₁' := eq_of_compS_empty_left hc
      subst hρ₁'
      subst hρ₁
      have hk₁ : Keeps (rsOf _) (rsOf _) _ := hk.1
      have hcell : CellIn (ResU.single ℓ (CellU.immOf s u σ hs)) s.meet :=
        CellIn.single (by simp)
      refine ⟨α, hα, ℓ, _, _, hc, ⟨rfl, hv, cohE_keeps hk₁ (CellU.kind_immOf _ _ _ _) hcoh⟩,
        s, u, σ, hs, ls₀, rfl, hP.1, hαs, fun x => ?_⟩
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mpr hx, hb⟩⟩
  | «mut» a T =>
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, hls₀,
        hunif⟩ := h.1
      subst hρ₀
      have hk₁ := hk.right hc
      have hmut : CellIn ρ₁ b :=
        ⟨ℓ, _, by rw [hρ₁]; exact ResU.single_get_self _ _, by simp, le_rfl⟩
      refine ⟨α, hα, ℓ, _, _, hc, ⟨rfl, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, ?_, hunif⟩
      intro x
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mpr hx, hb⟩⟩
  | unk => exact h
  | tvar _ => exact h.elim
  | mu A => exact vC_roll h.1 h.2.1 (h.2.2.2 _ hk)
  | fam L =>
      obtain ⟨ℓ, n, ρ₀, ρ₃, hc, hp, hs⟩ := h
      exact ⟨ℓ, n, ρ₀, ρ₃, hc, hp, sepRange_mono_down (R := fun σ => Ext ls ls' σ)
        (fun _ _ _ hc' hk' => ⟨hk'.left hc', hk'.right hc'⟩) (fun m σ hkσ hm => hm.2 _ hkσ)
        (hk.right hc) hs⟩

/-- The program's relation implies the observable view. -/
theorem vO_obs : ∀ (T : VTy) {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    vC true T ls δ v ρ → vC false T ls δ v ρ := by
  intro T ls δ v ρ h
  refine vC_ind δ (fun _ T ls v ρ => vC false T ls δ v ρ) ?_ true T ls v ρ h
  intro b T ls v ρ h
  cases T with
  | unit => exact h
  | int w => exact h
  | opq k => exact h
  | tensor T₁ T₂ =>
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁.2, h₂.2⟩
  | sum T₁ T₂ =>
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, h₁.2⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, h₂.2⟩
  | zero => exact h
  | thunk _ => trivial
  | box a T =>
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, hb.2, ho⟩
  | ref T =>
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂.2⟩
  | bang T => exact ⟨h.1, h.2.1⟩
  | imm a T =>
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, hpto⟩ := h
      exact ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, ptoImmS_mono (fun _ _ _ h => h.1) hpto⟩
  | «mut» a T => exact h.1
  | unk => exact h
  | tvar _ => exact h.elim
  | mu A => exact vC_roll h.1 h.2.1 h.2.2.2
  | fam L =>
      obtain ⟨ℓ, n, ρ₀, ρ₃, hc, hp, hs⟩ := h
      exact ⟨ℓ, n, ρ₀, ρ₃, hc, hp, sepRange_mono' (fun m σ hm => hm.2) hs⟩

/-- `vC ⊆ vShape`, both modes. -/
theorem vC_vShape : ∀ (b : Bool) (T : VTy) {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    vC b T ls δ v ρ → vShape T δ v ρ := by
  intro b T ls δ v ρ h
  refine vC_ind δ (fun _ T _ v ρ => vShape T δ v ρ) ?_ b T ls v ρ h
  intro b T ls v ρ h
  cases T with
  | unit => exact h
  | int w => exact h
  | opq k => exact h
  | tensor T₁ T₂ =>
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁.2, h₂.2⟩
  | sum T₁ T₂ =>
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, h₁.2⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, h₂.2⟩
  | zero => exact h
  | thunk _ => trivial
  | bang _ => exact ⟨h.1, trivial⟩
  | box a T =>
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, hb.2, ho⟩
  | ref T =>
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂.2⟩
  | imm a T =>
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, -⟩, s, u, σ, hs, _ls₀, hρ, hP, hle, -⟩ := h
      exact ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, s, u, σ, hs, hρ, hP.2, hle⟩
  | «mut» a T =>
      obtain ⟨⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, b, u, σ, hσ, Q, hw, ls₀, hab, hρ, hQ, -, -⟩, hsub⟩ := h
      refine ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, ofS Q, ⟨b, u, σ, hσ, Q, hw, hab, hρ, rfl⟩, ?_⟩
      intro u' σ' h'
      rw [hQ] at h'
      exact (hsub ls₀ u' σ' h').2
  | unk => exact h
  | tvar _ => exact h.elim
  | mu A => exact vShape_roll h.2.1 h.2.2.2
  | fam L =>
      obtain ⟨ℓ, n, ρ₀, ρ₃, hc, hp, hs⟩ := h
      exact ⟨ℓ, n, ρ₀, ρ₃, hc, ⟨hp.1, hp.2.1⟩, sepRange_mono' (fun m σ hm => hm.2) hs⟩

/-- Reading an `imm` cell at the observable view: the payload is observable-valid at
the current list. -/
theorem ptoImmO_read {l : Loc} {α : Life} {ls : List SRec} {S : VTy} {δ : LSub} {ρ : WRes}
    (h : ptoImmS l α ls (fun ls₀ => vC false S ls₀ δ) ρ) :
    ∃ (s : LSet) (u : Val) (σ : WRes) (hs : σ.InStratum s.join),
      ρ = ResU.single l (CellU.immOf s u σ hs) ∧ α ⊑ s.meet ∧ vC false S ls δ u σ := by
  obtain ⟨s, u, σ, hs, ls₀, hρ, hP, hαs, hls₀⟩ := h
  exact ⟨s, u, σ, hs, hρ, hαs,
    vC_local false S (ext_stored_current hs s.meet_le_join hls₀) hP⟩

/-- Making an `imm` cell at the observable view. -/
theorem ptoImmO_make {l : Loc} {α : Life} {ls : List SRec} {S : VTy} {δ : LSub} {s : LSet}
    {u : Val} {σ : WRes} (hs : σ.InStratum s.join) (hαs : α ⊑ s.meet)
    (hv : vC false S ls δ u σ) (hlb : LifeBound ls σ s.meet) :
    ptoImmS l α ls (fun ls₀ => vC false S ls₀ δ) (ResU.single l (CellU.immOf s u σ hs)) := by
  refine ⟨s, u, σ, hs, ls.filter (fun x => decide (x.2 ⊐ s.meet)), rfl, ?_, hαs,
    fun x => by simp⟩
  refine vC_local false S ⟨fun r hr hrel => ?_, fun b' hb' x hx => ?_⟩ hv
  · obtain ⟨t, ht⟩ := mem_rsOf.mp hr
    exact mem_rsOf.mpr ⟨t, by simp [ht, hlb _ ht hrel]⟩
  · have hxb : x.2 ⊐ s.meet :=
      lt_trans (lt_of_le_of_lt s.meet_le_join (hb'.of_stratum hs)) hx
    simp [hxb]

theorem ptoMutX_read {l : Loc} {α : Life} {ls : List SRec} {S : VTy} {δ : LSub} {ρ : WRes}
    (h : ptoMutS l α ls (fun ls₀ => vC true S ls₀ δ) ρ) :
    ∃ (b : Life) (u : Val) (σ : WRes) (hσ : σ.InStratum b) (Q : Val → SPropS Loc Val b)
      (hw : Q u ⟨σ, hσ⟩), ρ = ResU.single l (CellU.mutOf b u σ hσ Q hw) ∧
        vC true S ls δ u σ := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, -, hρ, hQ, hls₀, -⟩ := h
  refine ⟨b, u, σ, hσ, Q, hw, hρ, ?_⟩
  have h₀ : vC true S ls₀ δ u σ := by
    have : ofS Q u σ := ⟨hσ, hw⟩
    rw [hQ] at this; exact this
  exact vC_local true S (ext_stored_current hσ le_rfl hls₀) h₀

theorem ptoMutX_write {l : Loc} {α b : Life} {ls ls₀ : List SRec} {S : VTy} {δ : LSub}
    {Q : Val → SPropS Loc Val b} (hab : α ⊑ b) (hQ : ofS Q = fun v => vC true S ls₀ δ v)
    (hls₀ : ∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ b))
    (hunif : ∀ ls' u' σ', vC true S ls' δ u' σ' → σ'.InStratum b)
    {u : Val} {σ : WRes} (hσ : σ.InStratum b) (hv : vC true S ls δ u σ)
    (hlb : LifeBound ls σ b) :
    ∃ hw : Q u ⟨σ, hσ⟩, ptoMutS l α ls (fun ls₀ => vC true S ls₀ δ)
      (ResU.single l (CellU.mutOf b u σ hσ Q hw)) := by
  have hext : Ext ls ls₀ σ := by
    refine ⟨fun r hr hrel => ?_, fun b' hb' x hx => ?_⟩
    · obtain ⟨t, ht⟩ := mem_rsOf.mp hr
      exact mem_rsOf.mpr ⟨t, (hls₀ _).mpr ⟨ht, hlb _ ht hrel⟩⟩
    · have hxb : x.2 ⊐ b := lt_trans (hb'.of_stratum hσ) hx
      exact ⟨fun h => (hls₀ x).mpr ⟨h, hxb⟩, fun h => ((hls₀ x).mp h).1⟩
  have h₀ : vC true S ls₀ δ u σ := vC_local true S hext hv
  have hw : Q u ⟨σ, hσ⟩ := by
    have : ofS Q u σ := by rw [hQ]; exact h₀
    exact this.2
  exact ⟨hw, b, u, σ, hσ, Q, hw, ls₀, hab, rfl, hQ, hls₀, hunif⟩

theorem ptoMutX_create {l : Loc} {α b : Life} {ls : List SRec} {S : VTy} {δ : LSub}
    {Q : Val → SPropS Loc Val b} (hab : α ⊑ b) (hQ : ofS Q = fun v => vC true S ls δ v)
    (hfresh : ∀ x ∈ ls, x.2 ⊐ b)
    (hunif : ∀ ls' u' σ', vC true S ls' δ u' σ' → σ'.InStratum b)
    {u : Val} {σ : WRes} (hσ : σ.InStratum b) (hv : vC true S ls δ u σ) :
    ∃ hw : Q u ⟨σ, hσ⟩, ptoMutS l α ls (fun ls₀ => vC true S ls₀ δ)
      (ResU.single l (CellU.mutOf b u σ hσ Q hw)) := by
  have hw : Q u ⟨σ, hσ⟩ := by
    have : ofS Q u σ := by rw [hQ]; exact hv
    exact this.2
  exact ⟨hw, b, u, σ, hσ, Q, hw, ls, hab, rfl, hQ, strat_fresh hfresh, hunif⟩

/-- `[TR]` 6.60 at `vC`, both modes: `vDen_outlives`'s induction.  The `Imm` case reads the
cell's bound only; the payload is not consulted.  The box case takes the stratum's
monotonicity at `α ⊑ β`, the non-strict box rule.  `[spec §23]` -/
theorem vC_outlives {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) {T : VTy}
    (hT : VOutlives Δ a T) (b : Bool) :
    ∀ (ls : List SRec) (v : Val) (ρ : WRes), vC b T ls δ v ρ → BoLo.Outlives ρ α := by
  intro ls v ρ h
  refine vC_ind δ (fun _ T _ _ ρ => VOutlives Δ a T → BoLo.Outlives ρ α) ?_ b T ls v ρ h hT
  intro b T ls v ρ h hT
  cases T with
  | unit =>
      obtain ⟨rfl, -⟩ := h
      exact ResU.inStratum_empty α
  | int w =>
      obtain ⟨rfl, -⟩ := h
      exact ResU.inStratum_empty α
  | opq k =>
      obtain ⟨rfl, -⟩ := h
      exact ResU.inStratum_empty α
  | zero => exact False.elim h
  | tensor T₁ T₂ =>
      cases hT with
      | tensor h₁ h₂ =>
          obtain ⟨v₁, v₂, hs⟩ := h
          obtain ⟨-, ρ₁, ρ₂, hc, g₁, g₂⟩ := pure_sep_iff.mp hs
          exact (outlives_comp hc α).mpr ⟨g₁.2 h₁, g₂.2 h₂⟩
  | sum T₁ T₂ =>
      cases hT with
      | sum h₁ h₂ =>
          rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
          · exact (pure_sep_iff.mp hs).2.2 h₁
          · exact (pure_sep_iff.mp hs).2.2 h₂
  | ref T =>
      cases hT with
      | ref h₁ =>
          obtain ⟨ℓ, w, hs⟩ := h
          obtain ⟨-, ρ₁, ρ₂, hc, rfl, g₂⟩ := pure_sep_iff.mp hs
          exact (outlives_comp hc α).mpr ⟨ResU.inStratum_single_own α ℓ w, g₂.2 h₁⟩
  | bang T =>
      obtain ⟨rfl, -⟩ := h
      exact ResU.inStratum_empty α
  | box c T =>
      cases hT with
      | box hle =>
          obtain ⟨β, hb, -, ho⟩ := h
          obtain ⟨α', β', ha', hb', hle'⟩ := hle δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hb] at hb'; cases Option.some.inj hb'
          exact ho.mono (show (α : Life) ≤ β from hle')
  | imm c T =>
      cases hT with
      | imm hlt =>
          obtain ⟨β, hbi, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, s, w, σ, hσ, _ls₀, hρ₁, -, hle, -⟩ := h
          subst hρ₀
          have e := eq_of_compS_empty_left hc
          subst e; subst hρ₁
          obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hbi] at hb'; cases Option.some.inj hb'
          exact ResU.inStratum_single ℓ (lt_of_lt_of_le (show (α : Life) < β from hlt') hle)
  | «mut» c T =>
      cases hT with
      | «mut» hlt =>
          obtain ⟨β, hbi, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, b, w, σ, hσ, Q, hw, _ls₀, hle, hρ₁, -⟩ := h.1
          subst hρ₀
          have e := eq_of_compS_empty_left hc
          subst e; subst hρ₁
          obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hbi] at hb'; cases Option.some.inj hb'
          exact ResU.inStratum_single ℓ
            (show (CellU.mutOf b w σ hσ Q hw).InStratum α from
              lt_of_lt_of_le (show (α : Life) < β from hlt') hle)
  | thunk _ => cases hT
  | unk => cases hT
  | tvar _ => exact h.elim
  | mu A => exact h.2.2.2 hT.unroll
  | fam L =>
      cases hT with
      | fam hL =>
          obtain ⟨ℓ, n, hs⟩ := h
          obtain ⟨-, hs⟩ := pure_sep_iff.mp hs
          exact sepRange_closed (R := fun σ => BoLo.Outlives σ α) (ResU.inStratum_empty α)
            (fun _ _ _ hc o₁ o₂ => (outlives_comp hc α).mpr ⟨o₁, o₂⟩) (fun m σ hm => hm.2 hL) hs

/-- `@ρ ⊒ α`, read as membership in every stratum strictly below `α` (`StratumLe`'s shape, at a
resource).  `[spec §23]` -/
def OutlivesLe (ρ : WRes) (α : Life) : Prop := ∀ α', α' < α → BoLo.Outlives ρ α'

theorem outlivesLe_comp {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {α : Life}
    (h₁ : OutlivesLe ρ₁ α) (h₂ : OutlivesLe ρ₂ α) : OutlivesLe ρ α :=
  fun α' h => (outlives_comp hc α').mpr ⟨h₁ α' h, h₂ α' h⟩

theorem outlivesLe_of_outlives {ρ : WRes} {α : Life} (h : BoLo.Outlives ρ α) : OutlivesLe ρ α :=
  fun _ h' => h.mono (le_of_lt h')

/-- `[TR]` 6.60 at `Δ ⊢ T ⊒ @a`: every stratum strictly below `α`. `vC_outlives`'s induction,
with each lifetime premise read at `α ⊑ β`.  `[spec §23]` -/
theorem vC_outlivesLe {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) {T : VTy}
    (hT : VOutlivesLe Δ a T) (b : Bool) :
    ∀ (ls : List SRec) (v : Val) (ρ : WRes), vC b T ls δ v ρ → OutlivesLe ρ α := by
  intro ls v ρ h
  refine vC_ind δ (fun _ T _ _ ρ => VOutlivesLe Δ a T → OutlivesLe ρ α) ?_ b T ls v ρ h hT
  intro b T ls v ρ h hT
  cases T with
  | unit =>
      obtain ⟨rfl, -⟩ := h
      exact outlivesLe_of_outlives (ResU.inStratum_empty α)
  | int w =>
      obtain ⟨rfl, -⟩ := h
      exact outlivesLe_of_outlives (ResU.inStratum_empty α)
  | opq k =>
      obtain ⟨rfl, -⟩ := h
      exact outlivesLe_of_outlives (ResU.inStratum_empty α)
  | zero => exact False.elim h
  | tensor T₁ T₂ =>
      cases hT with
      | tensor h₁ h₂ =>
          obtain ⟨v₁, v₂, hs⟩ := h
          obtain ⟨-, ρ₁, ρ₂, hc, g₁, g₂⟩ := pure_sep_iff.mp hs
          exact outlivesLe_comp hc (g₁.2 h₁) (g₂.2 h₂)
  | sum T₁ T₂ =>
      cases hT with
      | sum h₁ h₂ =>
          rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
          · exact (pure_sep_iff.mp hs).2.2 h₁
          · exact (pure_sep_iff.mp hs).2.2 h₂
  | ref T =>
      cases hT with
      | ref h₁ =>
          obtain ⟨ℓ, w, hs⟩ := h
          obtain ⟨-, ρ₁, ρ₂, hc, rfl, g₂⟩ := pure_sep_iff.mp hs
          exact outlivesLe_comp hc
            (outlivesLe_of_outlives (ResU.inStratum_single_own α ℓ w)) (g₂.2 h₁)
  | bang T =>
      obtain ⟨rfl, -⟩ := h
      exact outlivesLe_of_outlives (ResU.inStratum_empty α)
  | box c T =>
      cases hT with
      | box hle =>
          obtain ⟨β, hb, -, ho⟩ := h
          obtain ⟨α', β', ha', hb', hle'⟩ := hle δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hb] at hb'; cases Option.some.inj hb'
          exact outlivesLe_of_outlives (ho.mono (show (α : Life) ≤ β from hle'))
  | imm c T =>
      cases hT with
      | imm hle₀ =>
          obtain ⟨β, hbi, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, s, w, σ, hσ, _ls₀, hρ₁, -, hle, -⟩ := h
          subst hρ₀
          have e := eq_of_compS_empty_left hc
          subst e; subst hρ₁
          obtain ⟨α', β', ha', hb', hle'⟩ := hle₀ δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hbi] at hb'; cases Option.some.inj hb'
          intro γ hγ
          exact ResU.inStratum_single ℓ
            (lt_of_lt_of_le hγ (le_trans (show (α : Life) ≤ β from hle') hle))
  | «mut» c T =>
      cases hT with
      | «mut» hle₀ =>
          obtain ⟨β, hbi, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, b, w, σ, hσ, Q, hw, _ls₀, hle, hρ₁, -⟩ := h.1
          subst hρ₀
          have e := eq_of_compS_empty_left hc
          subst e; subst hρ₁
          obtain ⟨α', β', ha', hb', hle'⟩ := hle₀ δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hbi] at hb'; cases Option.some.inj hb'
          intro γ hγ
          exact ResU.inStratum_single ℓ
            (show (CellU.mutOf b w σ hσ Q hw).InStratum γ from
              lt_of_lt_of_le hγ (le_trans (show (α : Life) ≤ β from hle') hle))
  | thunk _ => cases hT
  | unk => cases hT
  | tvar _ => exact h.elim
  | mu A => exact h.2.2.2 hT.unroll
  | fam L =>
      cases hT with
      | fam hL =>
          obtain ⟨ℓ, n, hs⟩ := h
          obtain ⟨-, hs⟩ := pure_sep_iff.mp hs
          intro γ hγ
          exact sepRange_closed (R := fun σ => BoLo.Outlives σ γ) (ResU.inStratum_empty γ)
            (fun _ _ _ hc o₁ o₂ => (outlives_comp hc γ).mpr ⟨o₁, o₂⟩)
            (fun m σ hm => hm.2 hL γ hγ) hs

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem coh_congr {rs : List FrameRec} {m : Loc} {S : VTy} {δ₁ δ₂ : LSub}
    (h : ∀ y, VFree y S → δ₁.find? y = δ₂.find? y) : Coh rs m S δ₁ ↔ Coh rs m S δ₂ := by
  unfold Coh AgreeOn
  constructor
  · rintro (⟨r, hr, hm, hS, hag⟩ | ⟨r, hr, p, u, hch, hag⟩)
    · subst hS; exact Or.inl ⟨r, hr, hm, rfl, fun y hy => (h y hy).symm.trans (hag y hy)⟩
    · exact Or.inr ⟨r, hr, p, u, hch, fun y hy => (h y hy).symm.trans (hag y hy)⟩
  · rintro (⟨r, hr, hm, hS, hag⟩ | ⟨r, hr, p, u, hch, hag⟩)
    · subst hS; exact Or.inl ⟨r, hr, hm, rfl, fun y hy => (h y hy).trans (hag y hy)⟩
    · exact Or.inr ⟨r, hr, p, u, hch, fun y hy => (h y hy).trans (hag y hy)⟩

theorem atLife_congr' {δ₁ δ₂ : LSub} {a : Lifetime.Life} {F : Life → WProp}
    (h : a.interp δ₁ = a.interp δ₂) : atLife δ₁ a F = atLife δ₂ a F := by
  unfold atLife; rw [h]

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `δ₁` and `δ₂` agree on the free lifetime variables of every type the environment holds. -/
def EnvAgree (η : Option (Nat → TEnt)) (δ₁ δ₂ : LSub) : Prop :=
  ∀ n y, VFree y (tEnv η n).ty → δ₁.find? y = δ₂.find? y

theorem envAgree_none (δ₁ δ₂ : LSub) : EnvAgree none δ₁ δ₂ := fun _ _ hy => hy.elim

theorem envAgree_tClose {η : Option (Nat → TEnt)} {δ₁ δ₂ : LSub} (hη : EnvAgree η δ₁ δ₂)
    {A : VTy} (h : ∀ y, VFree y A → δ₁.find? y = δ₂.find? y) :
    ∀ y, VFree y (tClose η A) → δ₁.find? y = δ₂.find? y := by
  intro y hy
  rw [tClose_eq] at hy
  rcases vFree_subst A _ hy with hy | ⟨n, hn⟩
  · exact h y hy
  · exact hη n y hn

mutual
/-- `𝒱⟦A⟧δ` depends on `δ` only at the variables free in `A` and in the environment's types. -/
theorem vCE_congr : ∀ (A : VTy) (η : Option (Nat → TEnt)) {δ₁ δ₂ : LSub},
    (∀ y, VFree y A → δ₁.find? y = δ₂.find? y) → EnvAgree η δ₁ δ₂ →
    ∀ (b : Bool) (ls : List SRec), vCE η b A ls δ₁ = vCE η b A ls δ₂
  | .unit, _, _, _, _, _, b, _ => by cases b <;> rfl
  | .int w, _, _, _, _, _, b, _ => by cases b <;> rfl
  | .opq k, _, _, _, _, _, b, _ => by cases b <;> rfl
  | .zero, _, _, _, _, _, b, _ => by cases b <;> rfl
  | .unk, _, _, _, _, _, b, _ => by cases b <;> rfl
  | .tvar _, _, _, _, _, _, _, _ => rfl
  | .tensor A B, η, _, _, h, hη, b, ls => by
      have h₁ := vCE_congr A η (fun y hy => h y (Or.inl hy)) hη
      have h₂ := vCE_congr B η (fun y hy => h y (Or.inr hy)) hη
      funext v; cases b <;> simp only [vCE, h₁, h₂]
  | .sum A B, η, _, _, h, hη, b, ls => by
      have h₁ := vCE_congr A η (fun y hy => h y (Or.inl hy)) hη
      have h₂ := vCE_congr B η (fun y hy => h y (Or.inr hy)) hη
      funext v; cases b <;> simp only [vCE, h₁, h₂]
  | .thunk C, _, _, _, h, _, b, ls => by
      have hC := cC_congr C h
      funext v; cases b
      · rfl
      · simp only [vCE, hC]
  | .ref A, η, _, _, h, hη, b, ls => by
      have ih := vCE_congr A η h hη
      funext v; cases b <;> simp only [vCE, ih]
  | .bang A, η, _, _, h, hη, b, ls => by
      have ih := vCE_congr A η h hη
      funext v; cases b <;> simp only [vCE, ih]
  | .fam A, η, _, _, h, hη, b, ls => by
      have ih := vCE_congr A η h hη
      funext v; cases b <;> simp only [vCE, ih]
  | .box a A, η, δ₁, δ₂, h, hη, b, ls => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vCE_congr A η (fun y hy => h y (Or.inr hy)) hη
      funext v; cases b <;> simp only [vCE, ih, atLife_congr' ha]
  | .imm a A, η, δ₁, δ₂, h, hη, b, ls => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vCE_congr A η (fun y hy => h y (Or.inr hy)) hη
      have hA := envAgree_tClose hη (A := A) (fun y hy => h y (Or.inr hy))
      have hcoh : ∀ rs m, CohE rs m (tClose η A) δ₁ = CohE rs m (tClose η A) δ₂ := fun rs m =>
        propext ⟨fun hc => hc.tyEq (TyEq.of_agree _ (fun y hy => (hA y hy).symm)),
          fun hc => hc.tyEq (TyEq.of_agree _ (fun y hy => hA y hy))⟩
      funext v; cases b <;> simp only [vCE, ih, hcoh, atLife_congr' ha]
  | .mut a A, η, δ₁, δ₂, h, hη, b, ls => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vCE_congr A η (fun y hy => h y (Or.inr hy)) hη
      funext v; cases b <;> simp only [vCE, ih, atLife_congr' ha]
  | .mu A, η, δ₁, δ₂, h, hη, b, ls => by
      funext v ρ
      simp only [vCE]
      congr 2
      apply propext
      refine forall_congr' fun P => imp_congr ?_ Iff.rfl
      have := vCE_congr A (some (VTy.scons ⟨tClose η (.mu A), P⟩ (tEnv η))) h (fun n y hy => by
        cases n with
        | zero => exact envAgree_tClose hη (A := .mu A) h y hy
        | succ n => exact hη n y hy)
      simp only [this]
/-- `𝒞⟦C⟧δ` depends on `δ` only at the variables free in `C`. -/
theorem cC_congr : ∀ (C : CTy) {δ₁ δ₂ : LSub}, (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) →
    ∀ (ls : List SRec), cC C ls δ₁ = cC C ls δ₂
  | .ret A, _, _, h, ls => by
      have ih := vCE_congr A none h (envAgree_none _ _) true
      funext e; simp only [cC, ih]
  | .arr A C, _, _, h, ls => by
      have h₁ := vCE_congr A none (fun y hy => h y (Or.inl hy)) (envAgree_none _ _) true ls
      have h₂ := cC_congr C (fun y hy => h y (Or.inr hy)) ls
      funext e; simp only [cC, h₁, h₂]
  | .amp C D, _, _, h, ls => by
      have h₁ := cC_congr C (fun y hy => h y (Or.inl hy)) ls
      have h₂ := cC_congr D (fun y hy => h y (Or.inr hy)) ls
      funext e; simp only [cC, h₁, h₂]
  | .top, _, _, _, _ => rfl
  | .nu C, δ₁, δ₂, h, ls => by
      have hB : ∀ (R : CPred) (ls' : List SRec),
          cB (some (nuEnv C R)) C ls' δ₁ = cB (some (nuEnv C R)) C ls' δ₂ :=
        fun R ls' => cB_congr C (some (nuEnv C R)) h (fun n y hy => by
          cases n with
          | zero => exact h y hy
          | succ n => exact hy.elim) ls'
      funext e ρ; simp only [cC, hB]
  | .all x c C, δ₁, δ₂, h, ls => by
      have hc : c.interp δ₁ = c.interp δ₂ := interp_congr c (fun y hy => h y (Or.inl hy))
      have hC : ∀ α : Life, cC C ls (δ₁.extend x α) = cC C ls (δ₂.extend x α) := by
        intro α
        refine cC_congr C (fun y hy => ?_) ls
        by_cases hxy : x = y
        · subst hxy; rw [find?_extend_self, find?_extend_self]
        · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
          exact h y (Or.inr ⟨Ne.symm hxy, hy⟩)
      have hL : ∀ α : Life, LtLife δ₁ c α = LtLife δ₂ c α := by intro α; unfold LtLife; rw [hc]
      funext e; simp only [cC, hC, hL]
  | .eff n i q _ A B fin C, δ₁, δ₂, h, ls => by
      have hA := vCE_congr A none (fun y hy => h y (Or.inl hy)) (envAgree_none _ _) true
      have hB := vCE_congr B none (fun y hy => h y (Or.inr (Or.inl hy))) (envAgree_none _ _) true
      have hF := finObl_congr fin (fun y hy => h y (Or.inr (Or.inr (Or.inl hy))))
      have hT := effTab_congr C (fun y hy => h y (Or.inr (Or.inr (Or.inr hy))))
      have hR := effRet_congr C (fun y hy => h y (Or.inr (Or.inr (Or.inr hy))))
      funext e; simp only [cC, hA, hB, hF, hT, hR]
/-- The operation table of a row depends on `δ` only at its free variables. -/
theorem effTab_congr : ∀ (C : CTy) {δ₁ δ₂ : LSub}, (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) →
    effTab C δ₁ = effTab C δ₂
  | .eff n i q _ A B fin C, δ₁, δ₂, h => by
      have hA := vCE_congr A none (fun y hy => h y (Or.inl hy)) (envAgree_none _ _) true
      have hB := vCE_congr B none (fun y hy => h y (Or.inr (Or.inl hy))) (envAgree_none _ _) true
      have hF := finObl_congr fin (fun y hy => h y (Or.inr (Or.inr (Or.inl hy))))
      have hT := effTab_congr C (fun y hy => h y (Or.inr (Or.inr (Or.inr hy))))
      simp only [effTab, hA, hB, hF, hT]
  | .ret _, _, _, _ | .arr _ _, _, _, _ | .amp _ _, _, _, _ | .top, _, _, _
  | .all _ _ _, _, _, _ | .nu _, _, _, _ => by simp only [effTab]
/-- A cancel row's obligation depends on `δ` only at its free variables. -/
theorem finObl_congr : ∀ (C : CTy) {δ₁ δ₂ : LSub}, (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) →
    finObl C δ₁ = finObl C δ₂
  | .eff n i q _ A B fin C, δ₁, δ₂, h => by
      have hA := vCE_congr A none (fun y hy => h y (Or.inl hy)) (envAgree_none _ _) true
      have hB := vCE_congr B none (fun y hy => h y (Or.inr (Or.inl hy))) (envAgree_none _ _) true
      have hF := finObl_congr fin (fun y hy => h y (Or.inr (Or.inr (Or.inl hy))))
      have hT := effTab_congr C (fun y hy => h y (Or.inr (Or.inr (Or.inr hy))))
      simp only [finObl, hA, hB, hF, hT]
  | .ret _, _, _, _ | .arr _ _, _, _, _ | .amp _ _, _, _, _ | .top, _, _, _
  | .all _ _ _, _, _, _ | .nu _, _, _, _ => by simp only [finObl]
/-- The answer relation of a row depends on `δ` only at its free variables. -/
theorem effRet_congr : ∀ (C : CTy) {δ₁ δ₂ : LSub}, (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) →
    effRet C δ₁ = effRet C δ₂
  | .ret A, δ₁, δ₂, h => by
      have hA := vCE_congr A none h (envAgree_none _ _) true
      simp only [effRet, hA]
  | .eff _ _ _ _ _ _ _ C, δ₁, δ₂, h => by
      simp only [effRet]
      exact effRet_congr C (fun y hy => h y (Or.inr (Or.inr (Or.inr hy))))
  | .arr _ _, _, _, _ | .amp _ _, _, _, _ | .top, _, _, _
  | .all _ _ _, _, _, _ | .nu _, _, _, _ => by simp only [effRet]
/-- The answer relation of a row under an environment depends on `δ` only at the free variables
of the row and of the environment's types. -/
theorem effRetE_congr : ∀ (C : CTy) (η : Option (Nat → TEnt)) {δ₁ δ₂ : LSub},
    (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) → EnvAgree η δ₁ δ₂ →
    effRetE η C δ₁ = effRetE η C δ₂
  | .ret A, η, δ₁, δ₂, h, hη => by
      have hA := vCE_congr A η h hη true
      simp only [effRetE, hA]
  | .eff _ _ _ _ _ _ _ C, η, δ₁, δ₂, h, hη => by
      simp only [effRetE]
      exact effRetE_congr C η (fun y hy => h y (Or.inr (Or.inr (Or.inr hy)))) hη
  | .arr _ _, _, _, _, _, _ | .amp _ _, _, _, _, _, _ | .top, _, _, _, _, _
  | .all _ _ _, _, _, _, _, _ | .nu _, _, _, _, _, _ => by simp only [effRetE]
/-- One unfolding of an observation tree depends on `δ` only at the free variables of the tree
and of the environment's types. -/
theorem cB_congr : ∀ (C : CTy) (η : Option (Nat → TEnt)) {δ₁ δ₂ : LSub},
    (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) → EnvAgree η δ₁ δ₂ →
    ∀ (ls : List SRec), cB η C ls δ₁ = cB η C ls δ₂
  | .ret A, η, _, _, h, hη, ls => by
      have ih := vCE_congr A η h hη true
      funext e; simp only [cB, ih]
  | .amp C D, η, _, _, h, hη, ls => by
      have h₁ := cB_congr C η (fun y hy => h y (Or.inl hy)) hη ls
      have h₂ := cB_congr D η (fun y hy => h y (Or.inr hy)) hη ls
      funext e; simp only [cB, h₁, h₂]
  | .eff n i q _ A B fin C, η, δ₁, δ₂, h, hη, ls => by
      have hA := vCE_congr A none (fun y hy => h y (Or.inl hy)) (envAgree_none _ _) true
      have hB := vCE_congr B none (fun y hy => h y (Or.inr (Or.inl hy))) (envAgree_none _ _) true
      have hF := finObl_congr fin (fun y hy => h y (Or.inr (Or.inr (Or.inl hy))))
      have hT := effTab_congr C (fun y hy => h y (Or.inr (Or.inr (Or.inr hy))))
      have hR := effRetE_congr C η (fun y hy => h y (Or.inr (Or.inr (Or.inr hy)))) hη
      funext e; simp only [cB, hA, hB, hF, hT, hR]
  | .arr A D, η, _, _, h, hη, ls => by
      have hA := vCE_congr A none (fun y hy => h y (Or.inl hy)) (envAgree_none _ _) true ls
      have hD := cB_congr D η (fun y hy => h y (Or.inr hy)) hη ls
      funext e; simp only [cB, hA, hD]
  | .top, _, _, _, _, _, _ | .all _ _ _, _, _, _, _, _, _
  | .nu _, _, _, _, _, _, _ => rfl
end

/-- `𝒱⟦A⟧δ` depends on `δ` only at the variables free in `A`. -/
theorem vC_congr (A : VTy) {δ₁ δ₂ : LSub} (h : ∀ y, VFree y A → δ₁.find? y = δ₂.find? y)
    (b : Bool) (ls : List SRec) : vC b A ls δ₁ = vC b A ls δ₂ :=
  vCE_congr A none h (envAgree_none _ _) b ls

/-- One computation type at two substitutions is forced the same way. -/
theorem forceE_of_cTyEq {C C' : CTy} {δ δ' : LSub} (h : CTyEq C δ C' δ') :
    forceE C = forceE C' := by
  cases C <;> cases C' <;> first | rfl | simp_all [CTyEq]

/-- Two environments hold equal candidates at `TyEq` types. -/
def EnvEq (η η' : Option (Nat → TEnt)) (δ δ' : LSub) : Prop :=
  ∀ n, (tEnv η n).P = (tEnv η' n).P ∧ TyEq (tEnv η n).ty δ (tEnv η' n).ty δ'

theorem envEq_none (δ δ' : LSub) : EnvEq none none δ δ' := fun n => ⟨rfl, show n = n from rfl⟩

theorem envEq_tClose {η η' : Option (Nat → TEnt)} {δ δ' : LSub} (hη : EnvEq η η' δ δ')
    {A A' : VTy} (h : TyEq A δ A' δ') : TyEq (tClose η A) δ (tClose η' A') δ' := by
  rw [tClose_eq, tClose_eq]
  exact TyEq.subst A _ _ h (fun n => (hη n).2)

/-- `0` is `0` at every `TyEq` type. -/
theorem TyEq.isZero_eq (A : VTy) {A' : VTy} {δ δ' : LSub} (h : TyEq A δ A' δ') :
    A.isZero = A'.isZero := by
  cases A <;> cases A' <;> simp_all [TyEq, VTy.isZero]

/-- Polynomiality in `X` is invariant under `TyEq`. -/
theorem TyEq.poly_iff : ∀ (A : VTy) {A' : VTy} {δ δ' : LSub}, TyEq A δ A' δ' → (A.Poly ↔ A'.Poly)
  | .tensor A B, A', _, _, h | .sum A B, A', _, _, h => by
      cases A' <;> simp only [TyEq] at h
      exact and_congr (TyEq.poly_iff A h.1) (TyEq.poly_iff B h.2)
  | .box _ A, A', _, _, h => by
      cases A' <;> simp only [TyEq] at h
      simp only [VTy.Poly]
      exact TyEq.poly_iff A h.2
  | .tvar _, A', _, _, h => by cases A' <;> simp only [TyEq] at h; subst h; exact Iff.rfl
  | .unit, A', _, _, h | .zero, A', _, _, h | .thunk _, A', _, _, h | .unk, A', _, _, h
  | .int _, A', _, _, h | .opq _, A', _, _, h | .ref _, A', _, _, h | .imm _ _, A', _, _, h | .mut _ _, A', _, _, h
  | .bang _, A', _, _, h | .mu _, A', _, _, h | .fam _, A', _, _, h => by
      have ho := TyEq.occ_iff _ 0 h
      cases A' <;> simp only [TyEq] at h
      simp only [VTy.Poly, ho]

theorem CTyEq.effLeaf_iff : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    (C.EffLeaf ↔ C'.EffLeaf)
  | .ret A, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      exact TyEq.poly_iff A h
  | .eff n i q _ A B fin C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      cases_type* World
      obtain ⟨rfl, rfl, rfl, -, hA, hB, -, hC⟩ := h
      exact and_congr (TyEq.Cl_iff A 0 hA) (and_congr (TyEq.Cl_iff B 0 hB)
        (CTyEq.effLeaf_iff C hC))
  | .arr _ _, C', _, _, h | .top, C', _, _, h | .all _ _ _, C', _, _, h | .nu _, C', _, _, h
  | .amp _ _, C', _, _, h => by
      cases C' <;> simp_all [CTyEq, CTy.EffLeaf]

theorem CTyEq.nuLeaf_iff : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    (C.NuLeaf ↔ C'.NuLeaf)
  | .ret A, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      exact TyEq.poly_iff A h
  | .amp C D, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      exact and_congr (CTyEq.nuLeaf_iff C h.1) (CTyEq.nuLeaf_iff D h.2)
  | .eff n i q wq A B fin C, C', _, _, h => by
      cases C'
      case eff => exact CTyEq.effLeaf_iff (.eff n i q wq A B fin C) h
      all_goals simp only [CTyEq] at h
  | .arr A D, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      exact and_congr (TyEq.Cl_iff A 0 h.1) (CTyEq.nuLeaf_iff D h.2)
  | .top, C', _, _, h | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp_all [CTyEq, CTy.NuLeaf]

theorem TyEq.isUnitB_eq (A : VTy) {A' : VTy} {δ δ' : LSub} (h : TyEq A δ A' δ') :
    A.isUnitB = A'.isUnitB := by
  cases A <;> cases A' <;> simp_all [TyEq, VTy.isUnitB]

theorem TyEq.isNextB_eq (A : VTy) {A' : VTy} {δ δ' : LSub} (h : TyEq A δ A' δ') :
    A.isNextB = A'.isNextB := by
  cases A <;> cases A' <;> simp only [TyEq] at h <;> simp only [VTy.isNextB]
  rw [TyEq.isUnitB_eq _ h.1, TyEq.isUnitB_eq _ h.2]

/-- Holding `Div` is invariant under `CTyEq`. -/
theorem CTyEq.divAt_eq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    C.divAt = C'.divAt
  | .eff n i q _ A B fin C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      cases_type* World
      obtain ⟨rfl, rfl, rfl, -, hA, hB, -, hC⟩ := h
      simp only [CTy.divAt, tickB, TyEq.isUnitB_eq A hA, TyEq.isNextB_eq B hB,
        CTyEq.divAt_eq C hC]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h <;> rfl

/-- Positivity is invariant under `CTyEq`. -/
theorem CTyEq.nuOk_iff {C C' : CTy} {δ δ' : LSub} (h : CTyEq C δ C' δ') : C.NuOk ↔ C'.NuOk := by
  cases C <;> cases C' <;> simp only [CTyEq] at h <;> simp only [CTy.NuOk]
  exact and_congr (CTyEq.nuLeaf_iff _ h.1) (CTyEq.nuLeaf_iff _ h.2)

mutual
theorem vCE_tyEq : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub} (η η' : Option (Nat → TEnt)),
    TyEq S δ S' δ' → EnvEq η η' δ δ' →
    ∀ (b : Bool) (ls : List SRec), vCE η b S ls δ = vCE η' b S' ls δ'
  | .unit, S', _, _, _, _, h, _ => by
      cases S' <;> simp only [TyEq] at h
      intro b ls; cases b <;> rfl
  | .int w, S', _, _, _, _, h, _ => by
      cases S' <;> simp only [TyEq] at h
      subst h; intro b ls; cases b <;> rfl
  | .opq k, S', _, _, _, _, h, _ => by
      cases S' <;> simp only [TyEq] at h
      subst h; intro b ls; cases b <;> rfl
  | .zero, S', _, _, _, _, h, _ => by
      cases S' <;> simp only [TyEq] at h
      intro b ls; cases b <;> rfl
  | .unk, S', _, _, _, _, h, _ => by
      cases S' <;> simp only [TyEq] at h
      intro b ls; cases b <;> rfl
  | .tvar n, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      subst h
      intro b ls; funext v
      simp only [vCE, tEnvP_eq, (hη _).1]
  | .tensor A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vCE_tyEq A η η' h.1 hη
      have ihB := vCE_tyEq B η η' h.2 hη
      intro b ls; funext v; cases b <;> simp only [vCE, ihA, ihB]
  | .sum A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vCE_tyEq A η η' h.1 hη
      have ihB := vCE_tyEq B η η' h.2 hη
      intro b ls; funext v; cases b <;> simp only [vCE, ihA, ihB]
  | .thunk C, S', _, _, _, _, h, _ => by
      cases S' <;> simp only [TyEq] at h
      have ih := cC_tyEq_aux C h
      have hf := forceE_of_cTyEq h
      intro b ls; funext v; cases b
      · rfl
      · simp only [vCE, ih, hf]
  | .ref A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vCE_tyEq A η η' h hη
      intro b ls; funext v; cases b <;> simp only [vCE, ih]
  | .bang A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vCE_tyEq A η η' h hη
      intro b ls; funext v; cases b <;> simp only [vCE, ih]
  | .fam A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vCE_tyEq A η η' h hη
      intro b ls; funext v; cases b <;> simp only [vCE, ih]
  | .box a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vCE_tyEq A η η' h.2 hη
      intro b ls; funext v
      cases b <;> (simp only [vCE, ih]; exact atLife_congr h.1 rfl)
  | .imm a A, S', δ, δ', η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      rename_i a' A'
      have ih := vCE_tyEq A η η' h.2 hη
      have hA := envEq_tClose hη h.2
      have hcoh : ∀ rs m, CohE rs m (tClose η A) δ = CohE rs m (tClose η' A') δ' := fun rs m =>
        propext ⟨fun hc => hc.tyEq hA.symm, fun hc => hc.tyEq hA⟩
      intro b ls; funext v
      cases b <;> (simp only [vCE, ih, hcoh]; exact atLife_congr h.1 rfl)
  | .mut a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vCE_tyEq A η η' h.2 hη
      intro b ls; funext v
      cases b <;> (simp only [vCE, ih]; exact atLife_congr h.1 rfl)
  | .mu A, S', δ, δ', η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      rename_i A'
      have hM : TyEq (tClose η (.mu A)) δ (tClose η' (.mu A')) δ' := envEq_tClose hη h
      intro b ls; funext v ρ
      simp only [vCE]
      rw [TyEq.noMut_iff A 0 h, TyEq.Cl_iff _ 0 hM]
      congr 2
      apply propext
      refine forall_congr' fun P => imp_congr ?_ Iff.rfl
      have := vCE_tyEq A (some (VTy.scons ⟨tClose η (.mu A), P⟩ (tEnv η)))
        (some (VTy.scons ⟨tClose η' (.mu A'), P⟩ (tEnv η'))) h (fun n => by
          cases n with
          | zero => exact ⟨rfl, hM⟩
          | succ n => exact hη n)
      simp only [this]
theorem cC_tyEq_aux : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    ∀ (ls : List SRec), cC C ls δ = cC C' ls δ'
  | .ret A, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ih := vCE_tyEq A none none h (envEq_none _ _) true
      intro ls; funext e; simp only [cC, ih]
  | .arr A C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vCE_tyEq A none none h.1 (envEq_none _ _) true
      have ihC := cC_tyEq_aux C h.2
      intro ls; funext e; simp only [cC, ihA, ihC]
  | .amp C D, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihC := cC_tyEq_aux C h.1
      have ihD := cC_tyEq_aux D h.2
      intro ls; funext e; simp only [cC, ihC, ihD]
  | .top, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      intro ls; rfl
  | .nu C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      rename_i C'
      have hB : ∀ (R : CPred) (ls' : List SRec),
          cB (some (nuEnv C R)) C ls' δ = cB (some (nuEnv C' R)) C' ls' δ' :=
        fun R => cB_tyEq C h (some (nuEnv C R)) (some (nuEnv C' R)) (fun n => by
          cases n with
          | zero => exact ⟨rfl, h⟩
          | succ n => exact ⟨rfl, rfl⟩)
      have hO : C.NuOk ↔ C'.NuOk := CTyEq.nuOk_iff h
      intro ls; funext e ρ; simp only [cC, hB, hO]
  | .all x c C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      rename_i x' c' C'
      have hT : ∀ (α : Life) (ls : List SRec),
          cC C ls (δ.extend x α) = cC C' ls (δ'.extend x' α) :=
        fun α => cC_tyEq_aux C (h.2 α)
      have hL : ∀ α : Life, LtLife δ c α = LtLife δ' c' α := by
        intro α; unfold LtLife; rw [h.1]
      intro ls; funext e; simp only [cC, hT, hL]
  | .eff n i q wq A B fin C, C', δ, δ', h => by
      have hd := CTyEq.divAt_eq (.eff n i q wq A B fin C) h
      cases C' <;> simp only [CTyEq] at h
      cases_type* World
      obtain ⟨rfl, rfl, rfl, -, hA, hB, hF, hC⟩ := h
      have ihA := vCE_tyEq A none none hA (envEq_none _ _) true
      have ihB := vCE_tyEq B none none hB (envEq_none _ _) true
      have ihF := finObl_tyEq fin hF
      have hT := effTab_tyEq C hC
      have hR := effRet_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      intro ls; funext e; simp only [cC, ihA, ihB, ihF, hT, hR, hz, hd]
theorem effTab_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    effTab C δ = effTab C' δ'
  | .eff n i q _ A B fin C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      cases_type* World
      obtain ⟨rfl, rfl, rfl, -, hA, hB, hF, hC⟩ := h
      have ihA := vCE_tyEq A none none hA (envEq_none _ _) true
      have ihB := vCE_tyEq B none none hB (envEq_none _ _) true
      have ihF := finObl_tyEq fin hF
      have hT := effTab_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      simp only [effTab, ihA, ihB, ihF, hT, hz]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h <;> simp only [effTab]
theorem finObl_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    finObl C δ = finObl C' δ'
  | .eff n i q _ A B fin C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      cases_type* World
      obtain ⟨rfl, rfl, rfl, -, hA, hB, hF, hC⟩ := h
      have ihA := vCE_tyEq A none none hA (envEq_none _ _) true
      have ihB := vCE_tyEq B none none hB (envEq_none _ _) true
      have ihF := finObl_tyEq fin hF
      have hT := effTab_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      simp only [finObl, ihA, ihB, ihF, hT, hz]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h <;> simp only [finObl]
theorem effRet_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    effRet C δ = effRet C' δ'
  | .ret A, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vCE_tyEq A none none h (envEq_none _ _) true
      simp only [effRet, ihA]
  | .eff _ _ _ _ _ _ _ C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      simp only [effRet]
      exact effRet_tyEq C h.2.2.2.2.2.2.2
  | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h <;> simp only [effRet]
theorem effRetE_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    ∀ (η η' : Option (Nat → TEnt)), EnvEq η η' δ δ' → effRetE η C δ = effRetE η' C' δ'
  | .ret A, C', δ, δ', h, η, η', hη => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vCE_tyEq A η η' h hη true
      simp only [effRetE, ihA]
  | .eff _ _ _ _ _ _ _ C, C', δ, δ', h, η, η', hη => by
      cases C' <;> simp only [CTyEq] at h
      simp only [effRetE]
      exact effRetE_tyEq C h.2.2.2.2.2.2.2 η η' hη
  | .arr _ _, C', _, _, h, _, _, _ | .amp _ _, C', _, _, h, _, _, _ | .top, C', _, _, h, _, _, _
  | .all _ _ _, C', _, _, h, _, _, _ | .nu _, C', _, _, h, _, _, _ => by
      cases C' <;> simp_all [CTyEq, effRetE]
theorem cB_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    ∀ (η η' : Option (Nat → TEnt)), EnvEq η η' δ δ' →
    ∀ (ls : List SRec), cB η C ls δ = cB η' C' ls δ'
  | .ret A, C', _, _, h, η, η', hη, ls => by
      cases C' <;> simp only [CTyEq] at h
      have ih := vCE_tyEq A η η' h hη true
      funext e; simp only [cB, ih]
  | .amp C D, C', _, _, h, η, η', hη, ls => by
      cases C' <;> simp only [CTyEq] at h
      have ihC := cB_tyEq C h.1 η η' hη ls
      have ihD := cB_tyEq D h.2 η η' hη ls
      funext e; simp only [cB, ihC, ihD]
  | .eff n i q wq A B fin C, C', δ, δ', h, η, η', hη, ls => by
      have hd := CTyEq.divAt_eq (.eff n i q wq A B fin C) h
      cases C' <;> simp only [CTyEq] at h
      cases_type* World
      obtain ⟨rfl, rfl, rfl, -, hA, hB, hF, hC⟩ := h
      have ihA := vCE_tyEq A none none hA (envEq_none _ _) true
      have ihB := vCE_tyEq B none none hB (envEq_none _ _) true
      have ihF := finObl_tyEq fin hF
      have hT := effTab_tyEq C hC
      have hR := effRetE_tyEq C hC η η' hη
      have hz := TyEq.isZero_eq B hB
      funext e; simp only [cB, ihA, ihB, ihF, hT, hR, hz, hd]
  | .arr A D, C', _, _, h, η, η', hη, ls => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vCE_tyEq A none none h.1 (envEq_none _ _) true ls
      have ihD := cB_tyEq D h.2 η η' hη ls
      funext e; simp only [cB, ihA, ihD]
  | .top, C', _, _, h, _, _, _, _
  | .all _ _ _, C', _, _, h, _, _, _, _ | .nu _, C', _, _, h, _, _, _, _ => by
      cases C' <;> simp only [CTyEq] at h
      rfl
end

/-- `𝒱⟦A⟧` reads a type only up to `TyEq` — `Δ-subst` (`TyEq.applyLSub`) at the relation:
`CohE` is closed under `TyEq`, and every other clause reads its lifetimes through `@aδ`. -/
theorem vC_tyEq {S S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') :
    ∀ (b : Bool) (ls : List SRec), vC b S ls δ = vC b S' ls δ' :=
  vCE_tyEq S none none h (envEq_none _ _)

/-- `𝒞⟦C⟧` reads a type only up to `CTyEq`. -/
theorem cC_tyEq {C C' : CTy} {δ δ' : LSub} (h : CTyEq C δ C' δ') :
    ∀ (ls : List SRec), cC C ls δ = cC C' ls δ' :=
  cC_tyEq_aux C h

theorem vC_extend_of_not_free {x : LifeVar} {T : VTy} (h : ¬ VFree x T) (b : Bool)
    (ls : List SRec) (δ : LSub) (α : Life) : vC b T ls (δ.extend x α) = vC b T ls δ :=
  vC_congr T (fun y hy => find?_extend_ne δ α (fun e => by subst e; exact h hy)) b ls

/-- At `Imm` the two modes are one clause. -/
theorem vC_imm_mode (a : Lifetime.Life) (S : VTy) (b b' : Bool) :
    vC b (.imm a S) = vC b' (.imm a S) := by
  cases b <;> cases b' <;> rfl

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `B`'s cells are `R`'s: same kind, witness and value, and a non-`imm` cell equal
(an `imm` cell may carry fewer lifetimes).  `[about ours]` -/
def CellMatch (R B : WRes) : Prop :=
  ∀ m ψ, B.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ζ.kind = ψ.kind ∧ ζ.wit = ψ.wit ∧
    ζ.erase = ψ.erase ∧ (ψ.kind ≠ Kind.imm → ζ = ψ)

theorem CellMatch.left {R B₁ B₂ B : WRes} (hc : ResU.CompS B₁ B₂ B) (h : CellMatch R B) :
    CellMatch R B₁ := by
  intro m ψ e
  obtain ⟨ψ', e', k', w', r'⟩ := compS_get_left' hc e
  obtain ⟨ζ, eζ, kζ, wζ, rζ, hζ⟩ := h m ψ' e'
  refine ⟨ζ, eζ, kζ.trans k', wζ.trans w', rζ.trans r', fun hk => ?_⟩
  have e'' := compS_get_left_nonImm hc e hk
  rw [e'] at e''; cases Option.some.inj e''
  exact hζ hk

theorem CellMatch.right {R B₁ B₂ B : WRes} (hc : ResU.CompS B₁ B₂ B) (h : CellMatch R B) :
    CellMatch R B₂ := CellMatch.left (ResU.CompS.comm hc) h

theorem CellMatch.of_le {R B : WRes} (h : ResU.Le B R) : CellMatch R B := by
  obtain ⟨τ, hτ⟩ := h
  intro m ψ e
  obtain ⟨ζ, eζ, kζ, wζ, rζ⟩ := compS_get_left' hτ e
  exact ⟨ζ, eζ, kζ, wζ, rζ, fun hk => by
    have e' := compS_get_left_nonImm hτ e hk
    rw [eζ] at e'; exact Option.some.inj e'⟩

theorem CellMatch.del {R B : WRes} (h : CellMatch R B) (l : Loc) : CellMatch R (B.del l) := by
  intro m ψ e
  by_cases hm : m = l
  · subst hm; rw [ResU.del_get_self] at e; cases e
  · rw [ResU.del_get_ne _ hm] at e; exact h m ψ e

/-- Every witness of an `imm` cell of `R` is relevant only to records tagged longer-lived
than any lifetime it lies in.  `[about ours: `lifeBound_of_tagged` at the witnesses
of an escrow's `imm` cells; the input the transfer consumes]` -/
def WitLB (ls : List SRec) (R : WRes) : Prop :=
  ∀ m ζ, R.get m = some ζ → ζ.kind = Kind.imm → ∀ b, ζ.wit.InStratum b → LifeBound ls ζ.wit b

theorem LifeBound.mono {ls : List SRec} {σ : WRes} {b b' : Life} (h : LifeBound ls σ b)
    (hb : b' ⊑ b) : LifeBound ls σ b' :=
  fun x hx hr => lt_of_le_of_lt hb (h x hx hr)

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The observable view transfers between two pieces of one escrow: `A` observable at
`T`, `B` shaped at `T`, both cell-matching `R`, gives `B` observable at `T`.  At a `U`
position both sides are `True`; at an `Imm` or `Mut` position the clause is read off `R`'s
cell. -/
theorem obs_transfer {R : WRes} {ls : List SRec} (hLB : WitLB ls R) :
    ∀ (T : VTy) {δ : LSub} {v : Val} {A B : WRes}, CellMatch R A → CellMatch R B →
      vC false T ls δ v A → vShape T δ v B → vC false T ls δ v B := by
  intro T δ v A B hA hB' h hs
  refine vC_ind δ (fun b T ls' v A => b = false → ls' = ls → ∀ B, CellMatch R A →
      CellMatch R B → vShape T δ v B → vC false T ls δ v B) ?_ false T ls v A h rfl rfl B hA hB' hs
  intro b T ls₁ v A h hb hls B hA hB' hs
  subst hb; subst ls₁
  cases T with
  | unit => exact hs
  | int w => exact hs
  | opq k => exact hs
  | unk => exact hs
  | zero => exact h
  | thunk _ => trivial
  | tvar _ => exact h.elim
  | tensor T₁ T₂ =>
      obtain ⟨v₁, v₂, hk⟩ := h
      obtain ⟨he, A₁, A₂, hcA, h₁, h₂⟩ := pure_sep_iff.mp hk
      obtain ⟨w₁, w₂, hk'⟩ := hs
      obtain ⟨he', B₁, B₂, hcB, g₁, g₂⟩ := pure_sep_iff.mp hk'
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' (he.symm.trans he')
      exact ⟨v₁, v₂, pure_sep_mk he ⟨B₁, B₂, hcB,
        h₁.2 rfl rfl _ (hA.left hcA) (hB'.left hcB) g₁,
        h₂.2 rfl rfl _ (hA.right hcA) (hB'.right hcB) g₂⟩⟩
  | sum T₁ T₂ =>
      rcases h with ⟨a, hk₁⟩ | ⟨a, hk₁⟩ <;> rcases hs with ⟨b, hk₂⟩ | ⟨b, hk₂⟩
      · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₁'⟩ := pure_sep_iff.mp hk₂
        cases Val.inj₁_inj' (he.symm.trans he')
        exact Or.inl ⟨a, pure_sep_mk he (h₁.2 rfl rfl _ hA hB' h₁')⟩
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk₂
        exact (Val.inj₁_ne_inj₂ (he.symm.trans he')).elim
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk₂
        exact (Val.inj₁_ne_inj₂ (he'.symm.trans he)).elim
      · obtain ⟨he, h₂⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₂'⟩ := pure_sep_iff.mp hk₂
        cases Val.inj₂_inj' (he.symm.trans he')
        exact Or.inr ⟨a, pure_sep_mk he (h₂.2 rfl rfl _ hA hB' h₂')⟩
  | box a T =>
      obtain ⟨α, hα, hb, -⟩ := h
      obtain ⟨α', hα', hb', ho'⟩ := hs
      exact ⟨α', hα', hb.2 rfl rfl _ hA hB' hb', ho'⟩
  | ref S =>
      obtain ⟨ℓ, u, hk⟩ := h
      obtain ⟨hl, ρa, ρb, hab, hown, hRb⟩ := pure_sep_iff.mp hk
      obtain ⟨ℓ', u', hk'⟩ := hs
      obtain ⟨hl', σa, σb, hab', hown', hSb⟩ := pure_sep_iff.mp hk'
      have e₀ : ℓ' = ℓ := by
        have := congrArg Subtype.val (hl'.symm.trans hl); simpa using this
      subst e₀
      have hown₁ : ρa = ResU.single ℓ' (CellU.ownOf u) := hown
      have hown₂ : σa = ResU.single ℓ' (CellU.ownOf u') := hown'
      subst hown₁; subst hown₂
      have eA := compS_get_left_nonImm hab (ResU.single_get_self _ _) (by simp)
      have eB := compS_get_left_nonImm hab' (ResU.single_get_self _ _) (by simp)
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hA ℓ' _ eA
      obtain ⟨ζ', eζ', -, -, -, hζ'⟩ := hB' ℓ' _ eB
      rw [eζ] at eζ'; cases Option.some.inj eζ'
      have huu : u = u' := by
        have := (hζ (by simp)).symm.trans (hζ' (by simp))
        have := congrArg CellU.erase this
        simpa using this
      subst huu
      exact ⟨ℓ', u, pure_sep_mk hl' ⟨_, σb, hab', rfl,
        hRb.2 rfl rfl _ (hA.right hab) (hB'.right hab') hSb⟩⟩
  | bang S =>
    obtain ⟨hA, hc⟩ := h
    obtain ⟨hB, -⟩ := hs
    subst hA; subst hB
    exact ⟨rfl, hc.1⟩
  | imm a S =>
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, hcoh⟩, hpto⟩ := h
      subst hρ₀
      have e₁ := eq_of_compS_empty_left hc
      subst e₁
      obtain ⟨s, u, σ, hσ, hρ₁, hαs, hP⟩ := ptoImmO_read (ptoImmS_mono (fun _ _ _ h => h.1) hpto)
      subst hρ₁
      obtain ⟨α', hα', ℓ', σ₀, σ₁, hc', ⟨hσ₀, hv'⟩, t, u', σ', ht, hσ₁, -, hαt⟩ := hs
      subst hσ₀
      have e₂ := eq_of_compS_empty_left hc'
      subst e₂
      subst hσ₁
      have e₀ : ℓ' = ℓ := by
        have := congrArg Subtype.val (hv'.symm.trans hv); simpa using this
      subst e₀
      rw [hα] at hα'; cases Option.some.inj hα'
      obtain ⟨ζ, eζ, kζ, wζ, rζ, -⟩ := hA ℓ' _ (ResU.single_get_self _ _)
      obtain ⟨ζ', eζ', -, wζ', rζ', -⟩ := hB' ℓ' _ (ResU.single_get_self _ _)
      rw [eζ] at eζ'; cases Option.some.inj eζ'
      simp only [CellU.wit_immOf, CellU.erase_immOf] at wζ rζ wζ' rζ'
      have hσσ : σ' = σ := wζ'.symm.trans wζ
      have huu : u' = u := rζ'.symm.trans rζ
      subst hσσ; subst huu
      have hlb : LifeBound ls σ' t.meet := by
        have := hLB ℓ' ζ eζ (by rw [kζ]; simp) t.join (by rw [wζ]; exact ht)
        rw [wζ] at this
        exact this.mono t.meet_le_join
      exact ⟨α, hα, ℓ', PMap.empty, _, hc', ⟨rfl, hv', hcoh⟩, ptoImmO_make ht hαt hP hlb⟩
  | «mut» a S =>
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, hmut⟩ := h.1
      subst hρ₀
      have e₁ := eq_of_compS_empty_left hc
      subst e₁
      obtain ⟨α', hα', ℓ', σ₀, σ₁, hc', ⟨hσ₀, hv'⟩, P, hpto, -⟩ := hs
      subst hσ₀
      have e₂ := eq_of_compS_empty_left hc'
      subst e₂
      have e₀ : ℓ' = ℓ := by
        have := congrArg Subtype.val (hv'.symm.trans hv); simpa using this
      subst e₀
      rw [hα] at hα'; cases Option.some.inj hα'
      obtain ⟨b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, hls₀, hunif⟩ := hmut
      obtain ⟨b', u', σ', hσ', Q', hw', -, hσ₁, -⟩ := hpto
      subst hρ₁; subst hσ₁
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hA ℓ' _ (ResU.single_get_self _ _)
      obtain ⟨ζ', eζ', -, -, -, hζ'⟩ := hB' ℓ' _ (ResU.single_get_self _ _)
      rw [eζ] at eζ'; cases Option.some.inj eζ'
      have hcell := (hζ (by simp)).symm.trans (hζ' (by simp))
      refine ⟨α, hα, ℓ', PMap.empty, _, hc', ⟨rfl, hv'⟩, ?_⟩
      rw [← hcell]
      exact ⟨b, u, σ, hσ, Q, hw, ls₀, hab, rfl, hQ, hls₀, hunif⟩
  | mu M =>
      obtain ⟨hnm, hcl, hG⟩ := h
      exact vC_roll hnm hcl (hG.2 rfl rfl _ hA hB' (vShape_unfold hs).2)
  | fam L =>
      obtain ⟨ℓ, n, hk⟩ := h
      obtain ⟨he, hsA⟩ := pure_sep_iff.mp hk
      obtain ⟨ℓ', n', hk'⟩ := hs
      obtain ⟨he', hsB⟩ := pure_sep_iff.mp hk'
      obtain ⟨rfl, rfl⟩ := Val.arr_inj (he.1.symm.trans he')
      exact ⟨ℓ, n, pure_sep_mk he (sepRange_zip (RA := CellMatch R) (RB := CellMatch R) (f := id)
        (fun _ _ _ hc h => ⟨h.left hc, h.right hc⟩) (fun _ _ _ hc h => ⟨h.left hc, h.right hc⟩)
        (fun _ _ _ hc => hc) rfl
        (fun m _ _ a b ha hb hPa hQb => hPa.2 rfl rfl _ ha hb hQb) hA hB' hsA hsB)⟩

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A cell of `c ∈ reb_β(σ)` against `σ`'s cell: same value; a `mut`/`imm` cell keeps
its witness; an `own` cell's witness is a piece of `σ` (`[TR]` p. 5's three clauses). -/
theorem reb_cell_match {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c) {m : Loc}
    {ψ : CellU Loc Val} (e : c.get m = some ψ) :
    ∃ ζ, σ.get m = some ζ ∧ ψ.erase = ζ.erase ∧ (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧
      (ζ.kind = Kind.own → CellMatch σ ψ.wit) := by
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
  simp only at hpl
  subst hpl
  have hq := hbody l₀ q hpm
  have hmem : q ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hpm, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigComp.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigComp.singleton_iff ResU.compLawsS).mp hb'] at hle'
  have hqσ : ResU.Le q σ := hle'.trans hle
  obtain ⟨ζq, hζq⟩ := hq.1
  obtain ⟨τ, hτ⟩ := hqσ
  obtain ⟨ζ, hζ⟩ := comp_some hτ hζq
  rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b₀, v, χ, hb₀, P, hw, rfl⟩
  · obtain ⟨hh, he⟩ := hq.2.1 u hζ
    rw [e] at he; cases Option.some.inj he
    refine ⟨_, hζ, by simp, fun h => (h (by simp)).elim, fun _ => ?_⟩
    rw [CellU.wit_immOf]
    exact (CellMatch.of_le ⟨τ, hτ⟩).del l₀
  · obtain ⟨⟨t, ht, -, he⟩, -⟩ := hq.2.2.2 s v χ hs hζ
    rw [e] at he; cases Option.some.inj he
    exact ⟨_, hζ, by simp, fun _ => by simp, fun h => absurd h (by simp)⟩
  · obtain ⟨⟨hh, he⟩, -⟩ := hq.2.2.1 b₀ v χ hb₀ P hw hζ
    rw [e] at he; cases Option.some.inj he
    exact ⟨_, hζ, by simp, fun _ => by simp, fun h => absurd h (by simp)⟩

/-- The `reb`-match hypothesis passes to a part. -/
theorem rebMatch_left {R c₁ c₂ c : WRes} (hcc : ResU.CompS c₁ c₂ c)
    (h : ∀ m ψ, c.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
      (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit)) :
    ∀ m ψ, c₁.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
      (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit) := by
  intro m ψ e
  obtain ⟨ψ', e', -, w', r'⟩ := compS_get_left' hcc e
  obtain ⟨ζ, eζ, h₁, h₂, h₃⟩ := h m ψ' e'
  exact ⟨ζ, eζ, r'.symm.trans h₁, fun k => w'.symm.trans (h₂ k),
    fun k => by rw [← w']; exact h₃ k⟩

theorem strat_left {R c₁ c₂ c : WRes} {β : Life} (hcc : ResU.CompS c₁ c₂ c)
    (hs : ∀ m ψ, c.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
      ψ.wit.InStratum (LSet.singleton β).join) :
    ∀ m ψ, c₁.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
      ψ.wit.InStratum (LSet.singleton β).join := by
  intro m ψ e hz
  obtain ⟨ψ', e', -, w', -⟩ := compS_get_left' hcc e
  rw [← w']; exact hs m ψ' e' hz

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- 6.131's image re-taken at `β`, at the program's relation: `relRes` (`relabel_reb`)
typed at `vC true⟦Imm̲ 'x T⟧`.  The inputs: the old image's shape (the
world's `JointAt`), the escrow's observable validity (the payload the program holds),
and coherence at the `Ref` and `Mut` positions.  At a `Ref`/`Mut` position the new cell's
payload is observable because the old image's witness is a piece of the escrow
(`obs_transfer`) or the `mut` cell's content (its stored predicate); at an `Imm` position
the kept cell is the escrow's (`obs_transfer` at the cell). -/
theorem relabel_obs {R : WRes} {ls : List SRec} {β β₀ : Life} {δ : LSub} {x x₀ : LifeVar}
    (hLB : WitLB ls R) (hβls : ∀ y ∈ ls, y.2 ⊐ β) :
    ∀ (T : VTy), ¬ VFree x T → ¬ VFree x₀ T → ∀ {v : Val} {c Rl : WRes},
      vShape (T.immReborrow (.var x₀)) (δ.extend x₀ β₀) v c →
      vC false T ls δ v Rl → CellMatch R Rl →
      (∀ m ψ, c.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
          (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit)) →
      (∀ m ψ, c.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
        ψ.wit.InStratum (LSet.singleton β).join) →
      (∀ m S u, RefPos T v m S → R.get m = some (CellU.ownOf u) →
        Coh (rsOf ls) m S (δ.extend x β)) →
      (∀ m S, MutPos T v m S → Coh (rsOf ls) m S (δ.extend x β)) →
      vC true (T.immReborrow (.var x)) ls (δ.extend x β) v (relRes R β c) := by
  intro T hx hx₀ v c Rl hc hR hRl hcR hs hcr hcm
  refine vC_ind δ (fun b T ls₁ v Rl => b = false → ls₁ = ls → ¬ VFree x T → ¬ VFree x₀ T →
      ∀ c, vShape (T.immReborrow (.var x₀)) (δ.extend x₀ β₀) v c → CellMatch R Rl →
      (∀ m ψ, c.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
          (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit)) →
      (∀ m ψ, c.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
        ψ.wit.InStratum (LSet.singleton β).join) →
      (∀ m S u, RefPos T v m S → R.get m = some (CellU.ownOf u) →
        Coh (rsOf ls) m S (δ.extend x β)) →
      (∀ m S, MutPos T v m S → Coh (rsOf ls) m S (δ.extend x β)) →
      vC true (T.immReborrow (.var x)) ls (δ.extend x β) v (relRes R β c)) ?_
    false T ls v Rl hR rfl rfl hx hx₀ c hc hRl hcR hs hcr hcm
  intro b T ls₁ v Rl hR hb hls hx hx₀ c hc hRl hcR hs hcr hcm
  subst hb; subst ls₁
  have hRv : vC false T ls δ v Rl :=
    (vF_vC δ false T ls v Rl).mpr (vF_mono (fun _ _ _ _ _ h => h.1) δ false T ls v Rl hR)
  cases T with
  | unit =>
      obtain ⟨hce, hv⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, hv⟩
  | int w =>
      obtain ⟨hce, hv⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, hv⟩
  | opq k =>
      obtain ⟨hce, hv⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, hv⟩
  | thunk _ =>
      obtain ⟨hce, -⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, trivial⟩
  | zero => exact False.elim hc
  | unk =>
      obtain ⟨hce, -⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, trivial⟩
  | tvar _ => exact hR.elim
  | sum T₁ T₂ =>
      rcases hc with ⟨a, hk₁⟩ | ⟨a, hk₁⟩ <;> rcases hR with ⟨b, hk₂⟩ | ⟨b, hk₂⟩
      · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₁'⟩ := pure_sep_iff.mp hk₂
        subst he; cases Val.inj₁_inj' he'
        exact Or.inl ⟨a, pure_sep_mk rfl (h₁'.2 rfl rfl (fun h => hx (Or.inl h))
          (fun h => hx₀ (Or.inl h)) _ h₁ hRl hcR hs (fun m S u h => hcr m S u (RefPos.sumL h))
          (fun m S h => hcm m S (MutPos.sumL h)))⟩
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk₂
        subst he; exact (Val.inj₁_ne_inj₂ he').elim
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk₂
        subst he; exact (Val.inj₁_ne_inj₂ he'.symm).elim
      · obtain ⟨he, h₂⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₂'⟩ := pure_sep_iff.mp hk₂
        subst he; cases Val.inj₂_inj' he'
        exact Or.inr ⟨a, pure_sep_mk rfl (h₂'.2 rfl rfl (fun h => hx (Or.inr h))
          (fun h => hx₀ (Or.inr h)) _ h₂ hRl hcR hs (fun m S u h => hcr m S u (RefPos.sumR h))
          (fun m S h => hcm m S (MutPos.sumR h)))⟩
  | tensor T₁ T₂ =>
      obtain ⟨a, b, hk₁⟩ := hc
      obtain ⟨he, c₁, c₂, hcc, h₁, h₂⟩ := pure_sep_iff.mp hk₁
      obtain ⟨a', b', hk₂⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, h₁', h₂'⟩ := pure_sep_iff.mp hk₂
      subst he
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      exact ⟨a, b, pure_sep_mk rfl ⟨_, _, relRes_compS hcc,
        h₁'.2 rfl rfl (fun h => hx (Or.inl h)) (fun h => hx₀ (Or.inl h)) _ h₁ (hRl.left hRR)
          (rebMatch_left hcc hcR) (strat_left hcc hs)
          (fun m S u h => hcr m S u (RefPos.tensorL h)) (fun m S h => hcm m S (MutPos.tensorL h)),
        h₂'.2 rfl rfl (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h)) _ h₂ (hRl.right hRR)
          (rebMatch_left hcc.comm hcR) (strat_left hcc.comm hs)
          (fun m S u h => hcr m S u (RefPos.tensorR h)) (fun m S h => hcm m S (MutPos.tensorR h))⟩⟩
  | box a T =>
      obtain ⟨α, -, hb, -⟩ := hR
      exact hb.2 rfl rfl (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h)) _ hc hRl hcR hs
        (fun m S u h => hcr m S u (RefPos.box h)) (fun m S h => hcm m S (MutPos.box h))
  | ref S =>
      obtain ⟨α, -, l', hk₁⟩ := hc
      obtain ⟨hl, s', w, W, hW, rfl, hWd, -⟩ := pure_sep_iff.mp hk₁
      obtain ⟨l'', u, hk₂⟩ := hR
      obtain ⟨hl', ρa, ρb, hab, hown, hRb⟩ := pure_sep_iff.mp hk₂
      have e₀ : l' = l'' := by
        have := congrArg Subtype.val (hl.symm.trans hl'); simpa using this
      subst e₀
      subst hl
      rw [show ρa = ResU.single l' (CellU.ownOf u) from hown] at hab
      have eRl := compS_get_left_nonImm hab (ResU.single_get_self _ _) (by simp)
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hRl l' _ eRl
      have hζ' : ζ = CellU.ownOf u := hζ (by simp)
      subst hζ'
      obtain ⟨ζ₂, eζ₂, her, -, hcw⟩ := hcR l' _ (ResU.single_get_self _ _)
      rw [eζ] at eζ₂; cases Option.some.inj eζ₂
      simp only [CellU.erase_immOf, CellU.erase_ownOf] at her
      subst her
      have hWm : CellMatch R W := by
        have := hcw (by simp); rwa [CellU.wit_immOf] at this
      have kne : (CellU.ownOf (Loc := Loc) w).kind ≠ Kind.imm := by simp
      have hβ := hs l' _ (ResU.single_get_self _ _) ⟨_, eζ, kne⟩
      rw [CellU.wit_immOf] at hβ
      rw [relRes_single, relCell_fire eζ kne hβ]
      rw [vShape_extend_of_not_free (T := S) hx₀] at hWd
      have hobs : vC false S ls δ w W := obs_transfer hLB S (hRl.right hab) hWm hRb.1 hWd
      have hobs' : vC false S ls (δ.extend x β) w W := by
        rw [vC_extend_of_not_free (T := S) hx]; exact hobs
      exact ⟨β, interp_ext_self δ x β, l', pure_sep_mk ⟨rfl, cohE_of_coh (hcr l' S w (RefPos.ref S l') eζ)⟩
        (ptoImmO_make hβ le_rfl hobs' (fun y hy _ => hβls y hy))⟩
  | bang S =>
    obtain ⟨hce, -⟩ := hc
    subst hce; rw [relRes_empty]
    show vC true (.bang S) ls (δ.extend x β) v PMap.empty
    rw [vC_extend_of_not_free hx true ls δ β]
    obtain ⟨h0, hS⟩ := hRv
    subst h0
    exact ⟨rfl, hS⟩
  | imm a S =>
      have hc' : vShape (.imm a S) (δ.extend x₀ β₀) v c := hc
      have hc'' := hc'
      obtain ⟨α, -, l', hk₁⟩ := hc''
      obtain ⟨hl, s', w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk₁
      have hR' := hRv
      obtain ⟨α', -, l'', ρ₀, ρ₁, hc₀, ⟨hρ₀, hv, -⟩, s₁, u₁, σ₁, hs₁, ls₁, hρ₁, -⟩ := hR'
      subst hρ₀
      have e₁ := eq_of_compS_empty_left hc₀
      subst e₁; subst hρ₁
      have e₀ : l'' = l' := by
        have := congrArg Subtype.val (hv.symm.trans hl); simpa using this
      subst e₀
      obtain ⟨ζ, eζ, kζ, -, -, -⟩ := hRl l'' _ (ResU.single_get_self _ _)
      have kζ' : ζ.kind = Kind.imm := by rw [kζ]; simp
      rw [relRes_single, relCell_keep eζ kζ']
      show vC true (.imm a S) ls (δ.extend x β) v _
      rw [vC_extend_of_not_free hx, vC_imm_mode a S true false]
      rw [vShape_extend_of_not_free hx₀] at hc'
      refine obs_transfer hLB (.imm a S) hRl ?_ hRv hc'
      intro m ψ e
      obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
      obtain ⟨ζ₂, eζ₂, her, hwit, -⟩ := hcR m _ (ResU.single_get_self _ _)
      rw [eζ] at eζ₂; cases Option.some.inj eζ₂
      exact ⟨ζ, eζ, by rw [kζ']; simp, (hwit (by rw [kζ']; simp)).symm, her.symm,
        fun hk => absurd (by simp) hk⟩
  | «mut» a S =>
      obtain ⟨α, -, l', hk₁⟩ := hc
      obtain ⟨hl, s', w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk₁
      obtain ⟨α', -, l'', ρ₀, ρ₁, hc₀, ⟨hρ₀, hv⟩, hmut⟩ := hRv
      subst hρ₀
      have e₁ := eq_of_compS_empty_left hc₀
      subst e₁
      obtain ⟨b, u, σ, hσ, Q, hw, hρ₁, hvS⟩ := ptoMutX_read hmut
      subst hρ₁
      have e₀ : l'' = l' := by
        have := congrArg Subtype.val (hv.symm.trans hl); simpa using this
      subst e₀
      subst hl
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hRl l'' _ (ResU.single_get_self _ _)
      have hζ' := hζ (by simp)
      subst hζ'
      obtain ⟨ζ₂, eζ₂, her, hwit, -⟩ := hcR l'' _ (ResU.single_get_self _ _)
      rw [eζ] at eζ₂; cases Option.some.inj eζ₂
      have hw' := hwit (by simp)
      simp only [CellU.erase_immOf, CellU.erase_mutOf, CellU.wit_immOf,
        CellU.wit_mutOf] at her hw'
      subst her; subst hw'
      have kne : (CellU.mutOf b w W hσ Q hw).kind ≠ Kind.imm := by simp
      have hβ := hs l'' _ (ResU.single_get_self _ _) ⟨_, eζ, kne⟩
      rw [CellU.wit_immOf] at hβ
      rw [relRes_single, relCell_fire eζ kne hβ]
      have hS : ¬ VFree x S := fun h => hx (Or.inr h)
      have hobs' : vC false S ls (δ.extend x β) w W := by
        rw [vC_extend_of_not_free hS]; exact vO_obs S hvS
      exact ⟨β, interp_ext_self δ x β, l'', pure_sep_mk ⟨rfl, cohE_of_coh (hcm l'' S (MutPos.mut a S l''))⟩
        (ptoImmO_make hβ le_rfl hobs' (fun y hy _ => hβls y hy))⟩
  | mu M =>
      obtain ⟨-, hcl, hG⟩ := hR
      have hM : M.Cl 1 := hcl
      refine (vC_immReborrow_mu_iff hM _ true ls _ v _).mpr ?_
      exact hG.2 rfl rfl (fun h => (vFree_inst h).elim hx hx) (fun h => (vFree_inst h).elim hx₀ hx₀)
        _ ((vShape_immReborrow_mu_iff hM _ _ v c).mp hc) hRl hcR hs
        (fun m S u h => hcr m S u (RefPos.mu hcl h)) (fun m S h => hcm m S (MutPos.mu hcl h))
  | fam L =>
      obtain ⟨ℓ, n, hk₁⟩ := hc
      obtain ⟨he, hs₁⟩ := pure_sep_iff.mp hk₁
      obtain ⟨ℓ', n', hk₂⟩ := hR
      obtain ⟨he', hs₂⟩ := pure_sep_iff.mp hk₂
      subst he
      obtain ⟨he', hn⟩ := he'
      obtain ⟨rfl, rfl⟩ := Val.arr_inj he'
      refine ⟨ℓ, n, pure_sep_mk ⟨rfl, hn⟩ ?_⟩
      exact sepRange_zip (RA := CellMatch R)
        (RB := fun c => (∀ m ψ, c.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
          (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit)) ∧
          (∀ m ψ, c.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
            ψ.wit.InStratum (LSet.singleton β).join))
        (f := relRes R β)
        (fun _ _ _ hc h => ⟨h.left hc, h.right hc⟩)
        (fun _ _ _ hc h => ⟨⟨rebMatch_left hc h.1, strat_left hc h.2⟩,
          ⟨rebMatch_left hc.comm h.1, strat_left hc.comm h.2⟩⟩)
        (fun _ _ _ hc => relRes_compS hc) (relRes_empty R β)
        (fun m hm hm' a b ha hb hPa hQb => hPa.2 rfl rfl hx hx₀ b hQb ha hb.1 hb.2
          (fun m' S u h => hcr m' S u (RefPos.fam_at hm hm' h))
          (fun m' S h => hcm m' S (MutPos.fam_at hm hm' h)))
        hRl ⟨hcR, hs⟩ hs₂ hs₁

/-- The chooser at a record's cell, at the program's relation, from the payload the
program holds at the cell (`hRobs`, the observable view of the escrow, read by `ptoImmO_read`), `WitLB` at the escrow, and `β` below every tag.  If no root of the escrow
carries a view, the handed image; otherwise the joint image re-taken at `β`, typed by
`relabel_obs`.  Types and the program's payload only. -/
theorem rebChooseO_top {W F χ₀ : WRes} {ps : List FrameRec} {ls : List SRec} {r : FrameRec}
    {le : Loc} {s : LSet} {hs : r.R.InStratum s.join} {x : LifeVar} {β : Life} {δ' : LSub}
    (hTW : TW W ps (rsOf ls)) (hr : r ∈ rsOf ls) (hag : AgreeOn r.T δ' r.δ)
    (hW : ResU.CompS (ResU.single le (CellU.immOf s r.v r.R hs)) F W)
    (hx : ¬ VFree x r.T) (hr₀ : ResU.Reb β r.R χ₀)
    (hP₀ : vC true (r.T.immReborrow (.var x)) ls (δ'.extend x β) r.v χ₀)
    (hRobs : vC false r.T ls δ' r.v r.R)
    (hLB : WitLB ls r.R) (hβls : ∀ y ∈ ls, y.2 ⊐ β) :
    ∃ χ : WRes, ResU.Reb β r.R χ ∧
      vC true (r.T.immReborrow (.var x)) ls (δ'.extend x β) r.v χ ∧
      (∃ A, AgW χ A) ∧ (∀ a, AgW F a → EscrowAgree r.R χ a) ∧
      (∀ a, AgW (ResU.single le (CellU.immOf s r.v r.R hs)) a → EscrowAgree r.R χ a) := by
  have hTI := hTW.inv.1
  obtain ⟨-, -, -, h4, h5, -⟩ := hTI
  obtain ⟨hRden, -⟩ := h4 r hr
  obtain ⟨-, e, aW, -, haW, -⟩ := hTW.valid
  obtain ⟨σ₁, σ₂, h₁, h₂, hc⟩ := (AgW.split hW).mp haW
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hW
  have liftG : ∀ G, (G = F ∨ G = ResU.single le (CellU.immOf s r.v r.R hs)) →
      ∀ a, AgW G a → ∀ l (ψf : CellU Loc Val), a.get l = some ψf → ψf.kind ≠ Kind.own →
      ∃ ψ, aW.get l = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψf.wit := by
    rintro G (rfl | rfl) a ha l ψf e hk
    · rw [AgW.functional ha h₂] at e; exact lift_view hc.comm e hk
    · rw [AgW.functional ha h₁] at e; exact lift_view hc e hk
  have hP₀s : vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v χ₀ := by
    rw [← vShape_immReb_agree hag]; exact vC_vShape true _ hP₀
  have agreeCoh : ∀ {S : VTy}, (∀ y, VFree y S → VFree y r.T) → ∀ m,
      Coh (rsOf ls) m S (r.δ.extend x β) → Coh (rsOf ls) m S (δ'.extend x β) := by
    intro S hfree m h
    refine (coh_congr (fun y hy => ?_)).mp h
    by_cases hxy : x = y
    · subst hxy; rw [find?_extend_self, find?_extend_self]
    · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
      exact (hag y (hfree y hy)).symm
  by_cases hv : ∃ S l u, Root r S l u ∧ ∃ a, AgW W a ∧ ∃ ψ, a.get l = some ψ ∧ ψ.kind ≠ Kind.own
  · obtain ⟨β₀, x₀, c₀, hx₀, hreb₀, hden₀, ⟨A₀, hA₀⟩, hj⟩ := h5 r hr hv
    have hRβ := hr₀.1
    have agree : ∀ G, (G = F ∨ G = ResU.single le (CellU.immOf s r.v r.R hs)) →
        ∀ a, AgW G a → EscrowAgree r.R (relRes r.R β c₀) a := by
      intro G hG a ha l v ψ ψf hown hψ hψf _ hk
      rw [relRes_get] at hψ
      obtain ⟨ψ₀, e₀, rfl⟩ := Option.map_eq_some_iff.mp hψ
      obtain ⟨ζ, eζ, hpos⟩ := image_dom r.T hden₀ hRden e₀
      rw [hown] at eζ; cases Option.some.inj eζ
      obtain ⟨S, hS⟩ := hpos rfl
      obtain ⟨ψ', e', k', w'⟩ := liftG G hG a ha l ψf hψf hk
      obtain ⟨ζ₀, eζ₀, wζ₀⟩ := hj S l v ⟨hS, hown⟩ aW haW ψ' e' k'
      rw [e₀] at eζ₀; cases Option.some.inj eζ₀
      rw [(relCell_props r.R β l ψ₀).2.1, ← wζ₀, w']
    have hden₀' : vShape (r.T.immReborrow (.var x₀)) (δ'.extend x₀ β₀) r.v c₀ := by
      rw [vShape_immReb_agree hag]; exact hden₀
    refine ⟨relRes r.R β c₀, relabel_reb hRβ hreb₀, ?_,
      agW_relRes (fun m ψ e => (reb_cell hreb₀ e).1) hA₀,
      agree F (Or.inl rfl), agree _ (Or.inr rfl)⟩
    refine relabel_obs hLB hβls r.T hx hx₀ hden₀' hRobs (CellMatch.of_le ⟨_, ResU.comp_empty_right _⟩)
      (fun m ψ e => reb_cell_match hreb₀ e) (reb_wit_stratum hRβ hreb₀)
      (fun m S u hpos hown => agreeCoh (fun y => hpos.free) m (coh_root hr hx hpos hown))
      (fun m S hpos => agreeCoh (fun y => hpos.free) m (coh_mut hTW hr hx hpos))
  · have agree : ∀ G, (G = F ∨ G = ResU.single le (CellU.immOf s r.v r.R hs)) →
        ∀ a, AgW G a → EscrowAgree r.R χ₀ a := by
      intro G hG a ha l v ψ ψf hown hψ hψf _ hk
      obtain ⟨ζ, eζ, hpos⟩ := image_dom r.T hP₀s hRden hψ
      rw [hown] at eζ; cases Option.some.inj eζ
      obtain ⟨S, hS⟩ := hpos rfl
      obtain ⟨ψ', e', k', -⟩ := liftG G hG a ha l ψf hψf hk
      exact (hv ⟨S, l, v, ⟨hS, hown⟩, aW, haW, ψ', e', k'⟩).elim
    have hag₀ : ∃ A, AgW χ₀ A := by
      refine agW_image_noview haW hle hr₀ (fun y ψ u hψ hu ζ hζ => ?_)
      obtain ⟨ζ', eζ', hpos⟩ := image_dom r.T hP₀s hRden hψ
      rw [hu] at eζ'; cases Option.some.inj eζ'
      obtain ⟨S, hS⟩ := hpos rfl
      by_contra hk
      exact hv ⟨S, y, u, ⟨hS, hu⟩, aW, haW, ζ, hζ, hk⟩
    exact ⟨χ₀, hr₀, hP₀, hag₀, agree F (Or.inl rfl), agree _ (Or.inr rfl)⟩

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- Re-taking an image at its own lifetime changes nothing: `relRes R β c = c` for
`c ∈ reb_β(R)`. -/
theorem relRes_self {β : Life} {R c : WRes} (hr : ResU.Reb β R c) : relRes R β c = c := by
  refine PMap.ext fun m => ?_
  rw [relRes_get]
  cases e : c.get m with
  | none => rfl
  | some ψ =>
    simp only [Option.map_some]
    congr 1
    unfold relCell
    split
    · rename_i h
      obtain ⟨hk, ⟨ζ, eζ, kζ⟩, hβ⟩ := h
      obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
      obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
      simp only at hpl
      subst hpl
      have hq := hbody l₀ q hpm
      rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b₀, v, χ, hb₀, P, hw, rfl⟩
      · obtain ⟨hh, he⟩ := hq.2.1 u eζ
        rw [e] at he; cases Option.some.inj he
        exact CellU.immOf_congr rfl (by simp) (by simp) _ _
      · exact absurd (CellU.kind_immOf _ _ _ _) kζ
      · obtain ⟨⟨hh, he⟩, -⟩ := hq.2.2.1 b₀ v χ hb₀ P hw eζ
        rw [e] at he; cases Option.some.inj he
        exact CellU.immOf_congr rfl (by simp) (by simp) _ _
    · rfl

/-- Every tag is longer-lived than 6.150's `β` (H11: `W ∈ Res_β`): a tag is the lifetime
of a record proper's cell (`Tagged`, `FrameLife`), and that cell is in `ag(W)`. -/
theorem tags_above {W : WRes} {ps : List FrameRec} {ls : List SRec} {β : Life}
    (hTW : TW W ps (rsOf ls)) (htag : Tagged W ps ls) (hβ : W.InStratum β) :
    ∀ y ∈ ls, y.2 ⊐ β := by
  intro y hy
  obtain ⟨p, hp, -, hFL⟩ := htag y hy
  obtain ⟨aW, haW⟩ := agW_of_valid hTW.valid
  obtain ⟨ψ, e, k, -, -⟩ := hTW.inv.2.1 p hp aW haW
  obtain ⟨t, ht⟩ := lsOf_of_imm k
  have h₁ : t.meet ⊐ β := CellU.sqsupset_of_lsOf ht (AgW.inStratum haW β hβ _ ψ e)
  rw [hFL.1 aW haW ψ t e ht t.meet t.meet_mem] at h₁
  exact h₁

/-- `WitLB` at a record's escrow: the witness of an `imm` cell of the escrow held at
`W(ℓₑ)` has its `imm` cells in `ag(W)` (`escrow_icp` twice), so `lifeBound_of_tagged`'s
argument applies to it. -/
theorem witLB_of {W : WRes} {ps : List FrameRec} {ls : List SRec} {le : Loc} {s : LSet}
    {v : Val} {R : WRes} {hs : R.InStratum s.join} (hvW : ResU.Valid W)
    (htag : Tagged W ps ls) (hle : W.get le = some (CellU.immOf s v R hs)) : WitLB ls R := by
  intro m ζ eζ kζ b hb x hx hrel
  obtain ⟨p, -, hpx, hFL⟩ := htag x hx
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨-, a₀, -, ha₀, hI₀⟩ := escrow_icp haW hle
  obtain ⟨s', hs', eta⟩ := CellU.imm_eta kζ
  rw [eta] at eζ
  obtain ⟨-, a₁, -, ha₁, hI₁⟩ := escrow_icp ha₀ eζ
  obtain ⟨m', ψ, e, k, hm⟩ := hrel
  obtain ⟨t, ht⟩ := lsOf_of_imm k
  have hlow : t.meet ⊐ b := CellU.sqsupset_of_lsOf ht (hb m' ψ e)
  have hicp : ICp aW m' ψ := icp_trans (icp_trans (icpAt_agW ha₁ m' ψ e) (hI₁ m')) (hI₀ m')
  obtain ⟨ζ', t', eζ', ht', hmt⟩ := hicp.ls ht t.meet_mem
  rcases linLoc_of_rel hpx hm with ⟨-, rfl⟩ | hL
  · have := hFL.1 aW haW ζ' t' eζ' ht' t.meet hmt
    rw [this] at hlow; exact hlow
  · exact lt_of_lt_of_le hlow (hFL.2 aW haW m' hL ζ' t' eζ' ht' t.meet hmt)

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The chooser at a record's cell, at the program's relation, from the tagged world:
`rebChooseO_top` with `WitLB` and the tag bound discharged by the world (`witLB_of`,
`tags_above`, H11).  The one input not read off the world is the payload the program holds
at the cell (`hRobs`). -/
theorem rebChooseO_top_tw {W F χ₀ : WRes} {ps : List FrameRec} {ls : List SRec} {r : FrameRec}
    {le : Loc} {s : LSet} {hs : r.R.InStratum s.join} {x : LifeVar} {β : Life} {δ' : LSub}
    (hTW : TW W ps (rsOf ls)) (htag : Tagged W ps ls) (hβ : W.InStratum β)
    (hr : r ∈ rsOf ls) (hag : AgreeOn r.T δ' r.δ)
    (hW : ResU.CompS (ResU.single le (CellU.immOf s r.v r.R hs)) F W)
    (hx : ¬ VFree x r.T) (hr₀ : ResU.Reb β r.R χ₀)
    (hP₀ : vC true (r.T.immReborrow (.var x)) ls (δ'.extend x β) r.v χ₀)
    (hRobs : vC false r.T ls δ' r.v r.R) :
    ∃ χ : WRes, ResU.Reb β r.R χ ∧
      vC true (r.T.immReborrow (.var x)) ls (δ'.extend x β) r.v χ ∧
      (∃ A, AgW χ A) ∧ (∀ a, AgW F a → EscrowAgree r.R χ a) ∧
      (∀ a, AgW (ResU.single le (CellU.immOf s r.v r.R hs)) a → EscrowAgree r.R χ a) := by
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hW
  exact rebChooseO_top hTW hr hag hW hx hr₀ hP₀ hRobs (witLB_of hTW.valid htag hle)
    (tags_above hTW htag hβ)

/-- …and at a chain view, from the tagged world, at the program's relation.  The payload
the program holds at the view is `hRobs`. -/
theorem rebChooseO_deep_tw {W F χ₀ : WRes} {ps : List FrameRec} {ls : List SRec}
    {r : FrameRec} {p₀ : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes}
    {hs : w₀.InStratum s.join} {x : LifeVar} {β : Life} {δ' : LSub}
    (hTW : TW W ps (rsOf ls)) (htag : Tagged W ps ls) (hβ : W.InStratum β)
    (hr : r ∈ rsOf ls) (hch : Chain r.R r.T r.v p₀ l₀ S₀ u₀) (hag : AgreeOn S₀ δ' r.δ)
    (hW : ResU.CompS (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) F W)
    (hx : ¬ VFree x S₀) (hr₀ : ResU.Reb β w₀ χ₀)
    (hP₀ : vC true (S₀.immReborrow (.var x)) ls (δ'.extend x β) u₀ χ₀)
    (hRobs : vC false S₀ ls δ' u₀ w₀) :
    ∃ χ : WRes, ResU.Reb β w₀ χ ∧
      vC true (S₀.immReborrow (.var x)) ls (δ'.extend x β) u₀ χ ∧
      (∃ A, AgW χ A) ∧ (∀ a, AgW F a → EscrowAgree w₀ χ a) ∧
      (∀ a, AgW (ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) a → EscrowAgree w₀ χ a) := by
  have hTI := hTW.inv.1
  obtain ⟨h1, -, -, -, -, h6⟩ := hTI
  obtain ⟨-, e, aW, -, haW, -⟩ := hTW.valid
  obtain ⟨σ₁, σ₂, h₁, h₂, hc⟩ := (AgW.split hW).mp haW
  obtain ⟨s', hs', hle⟩ := cell_of_compS_single hW
  obtain ⟨χl, eχl, kχl, -, wχl⟩ := AgW.get_imm h₁ (ResU.single_get_self _ _)
    (CellU.kind_immOf _ _ _ _)
  rw [CellU.wit_immOf] at wχl
  obtain ⟨χ₀', eχ₀', kχ₀', wχ₀'⟩ := lift_view hc eχl (by rw [kχl]; simp)
  have hχ₀w : χ₀'.wit = w₀ := wχ₀'.trans wχl
  obtain ⟨-, hw₀den, hw₀own, -, -⟩ := h1 r hr p₀ l₀ S₀ u₀ hch aW haW χ₀' eχ₀' kχ₀'
  rw [hχ₀w] at hw₀den hw₀own
  have liftG : ∀ G, (G = F ∨ G = ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) →
      ∀ a, AgW G a → ∀ l (ψf : CellU Loc Val), a.get l = some ψf → ψf.kind ≠ Kind.own →
      ∃ ψ, aW.get l = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψf.wit := by
    rintro G (rfl | rfl) a ha l ψf e hk
    · rw [AgW.functional ha h₂] at e; exact lift_view hc.comm e hk
    · rw [AgW.functional ha h₁] at e; exact lift_view hc e hk
  have hP₀s : vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ χ₀ := by
    rw [← vShape_immReb_agree hag]; exact vC_vShape true _ hP₀
  have child : ∀ (c₀ : WRes) (β₀ : Life) (x₀ : LifeVar),
      vShape (S₀.immReborrow (.var x₀)) (r.δ.extend x₀ β₀) u₀ c₀ →
      ∀ l (v : Val) (ψ : CellU Loc Val), w₀.get l = some (CellU.ownOf v) → c₀.get l = some ψ →
      ∃ S, Chain r.R r.T r.v (some l₀) l S v := by
    intro c₀ β₀ x₀ hden₀ l v ψ hown hψ
    obtain ⟨ζ, eζ, hpos⟩ := image_dom S₀ hden₀ hw₀den hψ
    rw [hown] at eζ; cases Option.some.inj eζ
    obtain ⟨S, hS⟩ := hpos rfl
    exact ⟨S, hch.snoc hS (hw₀own l v hown)⟩
  by_cases hv : ∃ l S u, Chain r.R r.T r.v (some l₀) l S u ∧ ∃ a, AgW W a ∧
      ∃ ψ : CellU Loc Val, a.get l = some ψ ∧ ψ.kind ≠ Kind.own
  · obtain ⟨w₁, hw₁, β₀, x₀, c₀, hx₀, hreb₀, hden₀, ⟨A₀, hA₀⟩, hj⟩ :=
      h6 r hr p₀ l₀ S₀ u₀ hch hv
    have hw₁₀ : w₁ = w₀ := by
      obtain ⟨ψ₁, e₁, -, w₁'⟩ := hw₁ aW haW
      rw [eχ₀'] at e₁; cases Option.some.inj e₁
      exact w₁'.symm.trans hχ₀w
    subst hw₁₀
    have hRβ := hr₀.1
    have agree : ∀ G, (G = F ∨ G = ResU.single l₀ (CellU.immOf s u₀ w₁ hs)) →
        ∀ a, AgW G a → EscrowAgree w₁ (relRes w₁ β c₀) a := by
      intro G hG a ha l v ψ ψf hown hψ hψf _ hk
      rw [relRes_get] at hψ
      obtain ⟨ψ₀, e₀, rfl⟩ := Option.map_eq_some_iff.mp hψ
      obtain ⟨S, hS⟩ := child c₀ β₀ x₀ hden₀ l v ψ₀ hown e₀
      obtain ⟨ψ', e', k', w'⟩ := liftG G hG a ha l ψf hψf hk
      obtain ⟨ζ₀, eζ₀, wζ₀⟩ := hj l S v hS aW haW ψ' e' k'
      rw [e₀] at eζ₀; cases Option.some.inj eζ₀
      rw [(relCell_props w₁ β l ψ₀).2.1, ← wζ₀, w']
    have hden₀' : vShape (S₀.immReborrow (.var x₀)) (δ'.extend x₀ β₀) u₀ c₀ := by
      rw [vShape_immReb_agree hag]; exact hden₀
    refine ⟨relRes w₁ β c₀, relabel_reb hRβ hreb₀, ?_,
      agW_relRes (fun m ψ e => (reb_cell hreb₀ e).1) hA₀,
      agree F (Or.inl rfl), agree _ (Or.inr rfl)⟩
    exact relabel_obs (witLB_of hTW.valid htag hle) (tags_above hTW htag hβ) S₀ hx hx₀ hden₀'
      hRobs (CellMatch.of_le ⟨_, ResU.comp_empty_right _⟩)
      (fun m ψ e => reb_cell_match hreb₀ e) (reb_wit_stratum hRβ hreb₀)
      (fun m S u hpos hown => coh_child hr hch hag hx hpos (hw₀own m u hown))
      (fun m S hpos => coh_mut_child hTW hr hch hag hx hpos)
  · have agree : ∀ G, (G = F ∨ G = ResU.single l₀ (CellU.immOf s u₀ w₀ hs)) →
        ∀ a, AgW G a → EscrowAgree w₀ χ₀ a := by
      intro G hG a ha l v ψ ψf hown hψ hψf _ hk
      obtain ⟨S, hS⟩ := child χ₀ β x hP₀s l v ψ hown hψ
      obtain ⟨ψ', e', k', -⟩ := liftG G hG a ha l ψf hψf hk
      exact (hv ⟨l, S, v, hS, aW, haW, ψ', e', k'⟩).elim
    have hag₀ : ∃ A, AgW χ₀ A := by
      refine agW_image_noview haW hle hr₀ (fun y ψ u hψ hu ζ hζ => ?_)
      obtain ⟨S, hS⟩ := child χ₀ β x hP₀s y u ψ hu hψ
      by_contra hk
      exact hv ⟨y, S, u, hS, aW, haW, ζ, hζ, hk⟩
    exact ⟨χ₀, hr₀, hP₀, hag₀, agree F (Or.inl rfl), agree _ (Or.inr rfl)⟩

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Lemma 6.131 (↺V₁) at the typed world; record in `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` -/
/-- 6.131's conclusion at the program's relation, from a shaped image: an image
`c ∈ reb_β(R)` shaped at `Imm̲ 'x T`, over an escrow observable at `T`, is `vC true`-typed at
`Imm̲ 'x T` — `relabel_obs` at `β₀ = β`, with `relRes_self`.  So `[TR]` 6.131 at `vC` is
6.131 at the shape relation plus coherence at the roots and `Mut` positions. -/
theorem image_vC_of_shape {R c : WRes} {ls : List SRec} {β : Life} {δ : LSub} {x : LifeVar}
    (hLB : WitLB ls R) (hβls : ∀ y ∈ ls, y.2 ⊐ β) (T : VTy) (hx : ¬ VFree x T) {v : Val}
    (hr : ResU.Reb β R c) (hc : vShape (T.immReborrow (.var x)) (δ.extend x β) v c)
    (hR : vC false T ls δ v R)
    (hcr : ∀ m S u, RefPos T v m S → R.get m = some (CellU.ownOf u) →
      Coh (rsOf ls) m S (δ.extend x β))
    (hcm : ∀ m S, MutPos T v m S → Coh (rsOf ls) m S (δ.extend x β)) :
    vC true (T.immReborrow (.var x)) ls (δ.extend x β) v c := by
  have := relabel_obs hLB hβls T hx hx hc hR
    (CellMatch.of_le ⟨_, ResU.comp_empty_right _⟩) (fun m ψ e => reb_cell_match hr e)
    (reb_wit_stratum hr.1 hr) hcr hcm
  rwa [relRes_self hr] at this

end BoCa.Fig16.LogRel.Core

end
