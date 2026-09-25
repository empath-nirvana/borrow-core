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
import CBPVWorld.Images
import CBPVWorld.Invariant
import CBPVWorld.Records
import CBPVWorld.Relation
import CBPVWorld.World
import CBPVWorld.Wp

/-!
# CBPVWorld — RelationFacts

`Support/TypedWorld`'s layer `RelationFacts`, with records typed at `VTy`.  The repaired relation `vC` read at substitutions: monotonicity, the `imm` cell at the observable view, reading, writing and making a `mut` cell, 6.60 at `vC`, congruence in `δ`, and the choosers' inputs.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVWorld
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

mutual
theorem tyEq_symm : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub}, TyEq S δ S' δ' → TyEq S' δ' S δ
  | .unit, S', _, _, h => by cases S' <;> simp_all [TyEq]
  | .zero, S', _, _, h => by cases S' <;> simp_all [TyEq]
  | .unk, S', _, _, h => by cases S' <;> simp_all [TyEq]
  | .tensor A B, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact ⟨tyEq_symm A h.1, tyEq_symm B h.2⟩
  | .sum A B, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact ⟨tyEq_symm A h.1, tyEq_symm B h.2⟩
  | .thunk C, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact cTyEq_symm C h
  | .ref A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact tyEq_symm A h
  | .bang A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact tyEq_symm A h
  | .box a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact ⟨h.1.symm, tyEq_symm A h.2⟩
  | .imm a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact ⟨h.1.symm, tyEq_symm A h.2⟩
  | .mut a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h ⊢
      exact ⟨h.1.symm, tyEq_symm A h.2⟩
theorem cTyEq_symm : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' → CTyEq C' δ' C δ
  | .ret A, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h ⊢
      exact tyEq_symm A h
  | .arr A C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h ⊢
      exact ⟨tyEq_symm A h.1, cTyEq_symm C h.2⟩
  | .amp C D, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h ⊢
      exact ⟨cTyEq_symm C h.1, cTyEq_symm D h.2⟩
  | .top, C', _, _, h => by cases C' <;> simp_all [CTyEq]
  | .all x b C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h ⊢
      exact ⟨h.1.symm, fun α => cTyEq_symm C (h.2 α)⟩
end

theorem TyEq.symm {S S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') : TyEq S' δ' S δ :=
  tyEq_symm S h

theorem CTyEq.symm {C C' : CTy} {δ δ' : LSub} (h : CTyEq C δ C' δ') : CTyEq C' δ' C δ :=
  cTyEq_symm C h

mutual
theorem tyEq_trans : ∀ (S : VTy) {S' S'' : VTy} {δ δ' δ'' : LSub}, TyEq S δ S' δ' →
    TyEq S' δ' S'' δ'' → TyEq S δ S'' δ''
  | .unit, S', S'', _, _, _, h, h' => by cases S' <;> cases S'' <;> simp_all [TyEq]
  | .zero, S', S'', _, _, _, h, h' => by cases S' <;> cases S'' <;> simp_all [TyEq]
  | .unk, S', S'', _, _, _, h, h' => by cases S' <;> cases S'' <;> simp_all [TyEq]
  | .tensor A B, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨tyEq_trans A h.1 h'.1, tyEq_trans B h.2 h'.2⟩
  | .sum A B, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨tyEq_trans A h.1 h'.1, tyEq_trans B h.2 h'.2⟩
  | .thunk C, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact cTyEq_trans C h h'
  | .ref A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact tyEq_trans A h h'
  | .bang A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact tyEq_trans A h h'
  | .box a A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, tyEq_trans A h.2 h'.2⟩
  | .imm a A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, tyEq_trans A h.2 h'.2⟩
  | .mut a A, S', S'', _, _, _, h, h' => by
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, tyEq_trans A h.2 h'.2⟩
theorem cTyEq_trans : ∀ (C : CTy) {C' C'' : CTy} {δ δ' δ'' : LSub}, CTyEq C δ C' δ' →
    CTyEq C' δ' C'' δ'' → CTyEq C δ C'' δ''
  | .ret A, C', C'', _, _, _, h, h' => by
      cases C' <;> simp only [CTyEq] at h
      cases C'' <;> simp only [CTyEq] at h' ⊢
      exact tyEq_trans A h h'
  | .arr A C, C', C'', _, _, _, h, h' => by
      cases C' <;> simp only [CTyEq] at h
      cases C'' <;> simp only [CTyEq] at h' ⊢
      exact ⟨tyEq_trans A h.1 h'.1, cTyEq_trans C h.2 h'.2⟩
  | .amp C D, C', C'', _, _, _, h, h' => by
      cases C' <;> simp only [CTyEq] at h
      cases C'' <;> simp only [CTyEq] at h' ⊢
      exact ⟨cTyEq_trans C h.1 h'.1, cTyEq_trans D h.2 h'.2⟩
  | .top, C', C'', _, _, _, h, h' => by cases C' <;> cases C'' <;> simp_all [CTyEq]
  | .all x b C, C', C'', _, _, _, h, h' => by
      cases C' <;> simp only [CTyEq] at h
      cases C'' <;> simp only [CTyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, fun α => cTyEq_trans C (h.2 α) (h'.2 α)⟩
end

theorem TyEq.trans {S S' S'' : VTy} {δ δ' δ'' : LSub} (h : TyEq S δ S' δ')
    (h' : TyEq S' δ' S'' δ'') : TyEq S δ S'' δ'' := tyEq_trans S h h'

theorem CTyEq.trans {C C' C'' : CTy} {δ δ' δ'' : LSub} (h : CTyEq C δ C' δ')
    (h' : CTyEq C' δ' C'' δ'') : CTyEq C δ C'' δ'' := cTyEq_trans C h h'

mutual
theorem TyEq.of_agree : ∀ (T : VTy) {δ₁ δ₂ : LSub},
    (∀ y, VFree y T → δ₁.find? y = δ₂.find? y) → TyEq T δ₁ T δ₂
  | .unit, _, _, _ => trivial
  | .zero, _, _, _ => trivial
  | .unk, _, _, _ => trivial
  | .tensor A B, _, _, h => ⟨TyEq.of_agree A (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree B (fun y hy => h y (Or.inr hy))⟩
  | .sum A B, _, _, h => ⟨TyEq.of_agree A (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree B (fun y hy => h y (Or.inr hy))⟩
  | .thunk C, _, _, h => CTyEq.of_agree C h
  | .ref A, _, _, h => TyEq.of_agree A h
  | .bang A, _, _, h => TyEq.of_agree A h
  | .box a A, _, _, h => ⟨interp_congr a (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree A (fun y hy => h y (Or.inr hy))⟩
  | .imm a A, _, _, h => ⟨interp_congr a (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree A (fun y hy => h y (Or.inr hy))⟩
  | .mut a A, _, _, h => ⟨interp_congr a (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree A (fun y hy => h y (Or.inr hy))⟩
theorem CTyEq.of_agree : ∀ (C : CTy) {δ₁ δ₂ : LSub},
    (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) → CTyEq C δ₁ C δ₂
  | .ret A, _, _, h => TyEq.of_agree A h
  | .arr A C, _, _, h => ⟨TyEq.of_agree A (fun y hy => h y (Or.inl hy)),
      CTyEq.of_agree C (fun y hy => h y (Or.inr hy))⟩
  | .amp C D, _, _, h => ⟨CTyEq.of_agree C (fun y hy => h y (Or.inl hy)),
      CTyEq.of_agree D (fun y hy => h y (Or.inr hy))⟩
  | .top, _, _, _ => trivial
  | .all x b C, δ₁, δ₂, h => by
      refine ⟨interp_congr b (fun y hy => h y (Or.inl hy)), fun α => ?_⟩
      refine CTyEq.of_agree C (fun y hy => ?_)
      by_cases hxy : x = y
      · subst hxy; rw [find?_extend_self, find?_extend_self]
      · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
        exact h y (Or.inr ⟨Ne.symm hxy, hy⟩)
end

theorem TyEq.refl (T : VTy) (δ : LSub) : TyEq T δ T δ := TyEq.of_agree T (fun _ _ => rfl)

theorem CTyEq.refl (C : CTy) (δ : LSub) : CTyEq C δ C δ := CTyEq.of_agree C (fun _ _ => rfl)

/-- A fresh extension on the left is invisible. -/
theorem TyEq.extend_left {S S' : VTy} {δ δ' : LSub} {x : LifeVar} (hx : ¬ VFree x S) (β : Life)
    (h : TyEq S δ S' δ') : TyEq S (δ.extend x β) S' δ' :=
  (TyEq.of_agree S (fun y hy => find?_extend_ne δ β (fun e => hx (by rw [e]; exact hy)))).trans h

theorem TyEq.immReborrow {S S' : VTy} {δ δ' : LSub} {c c' : Lifetime.Life}
    (hc : c.interp δ = c'.interp δ') (h : TyEq S δ S' δ') :
    TyEq (S.immReborrow c) δ (S'.immReborrow c') δ' := by
  induction S using VTy.recV generalizing S' with
  | unit => cases S' <;> simp_all [TyEq, VTy.immReborrow]
  | zero => cases S' <;> simp_all [TyEq, VTy.immReborrow]
  | unk => cases S' <;> simp_all [TyEq, VTy.immReborrow]
  | thunk C => cases S' <;> simp_all [TyEq, VTy.immReborrow]
  | tensor A B ihA ihB =>
      cases S' <;> simp only [TyEq] at h
      exact ⟨ihA h.1, ihB h.2⟩
  | sum A B ihA ihB =>
      cases S' <;> simp only [TyEq] at h
      exact ⟨ihA h.1, ihB h.2⟩
  | ref A _ =>
      cases S' <;> simp only [TyEq] at h
      exact ⟨hc, h⟩
  | bang A _ => cases S' <;> simp_all [TyEq, VTy.immReborrow]
  | imm a A _ =>
      cases S' <;> simp only [TyEq] at h
      exact h
  | «mut» a A _ =>
      cases S' <;> simp only [TyEq] at h
      exact ⟨hc, h.2⟩
  | box a A ih =>
      cases S' <;> simp only [TyEq] at h
      simp only [VTy.immReborrow]
      exact ih h.2

mutual
/-- `Δ-subst` at `TyEq`: `vDen_applyLSub`'s induction, the `∀` case, now at `CTy`, with its
two branches. -/
theorem TyEq.applyLSub : ∀ (T : VTy) (σ : Lifetime.LSubst) (δ δ' : LSub),
    (∀ y, VFree y T → ((Lifetime.Life.var y).applySub σ).interp δ = δ'.find? y) →
      TyEq (T.applyLSub σ) δ T δ'
  | .unit, _, _, _, _ => trivial
  | .zero, _, _, _, _ => trivial
  | .unk, _, _, _, _ => trivial
  | .ref T, σ, δ, δ', h => TyEq.applyLSub T σ δ δ' h
  | .bang T, σ, δ, δ', h => TyEq.applyLSub T σ δ δ' h
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

/-- `vShape` reads a type only up to `TyEq`. -/
theorem vShape_tyEq {S S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') : vShape S δ = vShape S' δ' := by
  induction S using VTy.recV generalizing S' with
  | unit => cases S' <;> first | rfl | simp_all [TyEq]
  | zero => cases S' <;> first | rfl | simp_all [TyEq]
  | unk => cases S' <;> first | rfl | simp_all [TyEq]
  | thunk C =>
      cases S' <;> simp only [TyEq] at h
      rfl
  | tensor A B ihA ihB =>
      cases S' <;> simp only [TyEq] at h
      funext v
      simp only [vShape, ihA h.1, ihB h.2]
  | sum A B ihA ihB =>
      cases S' <;> simp only [TyEq] at h
      funext v
      simp only [vShape, ihA h.1, ihB h.2]
  | ref A ih =>
      cases S' <;> simp only [TyEq] at h
      funext v
      simp only [vShape, ih h]
  | bang A ih =>
      cases S' <;> simp only [TyEq] at h
      funext v
      simp only [vShape, ih h]
  | box a A ih =>
      cases S' <;> simp only [TyEq] at h
      funext v
      simp only [vShape, ih h.2]
      exact atLife_congr h.1 rfl
  | imm a A ih =>
      cases S' <;> simp only [TyEq] at h
      funext v
      simp only [vShape, ih h.2]
      exact atLife_congr h.1 rfl
  | «mut» a A ih =>
      cases S' <;> simp only [TyEq] at h
      funext v
      simp only [vShape, ih h.2]
      exact atLife_congr h.1 rfl

theorem cohE_of_coh {rs : List FrameRec} {m : Loc} {S : VTy} {δ : LSub} (h : Coh rs m S δ) :
    CohE rs m S δ := ⟨S, δ, TyEq.refl S δ, h⟩

theorem CohE.tyEq {rs : List FrameRec} {m : Loc} {S S' : VTy} {δ δ' : LSub}
    (he : TyEq S δ S' δ') (h : CohE rs m S' δ') : CohE rs m S δ := by
  obtain ⟨S₀, δ₀, he₀, hc⟩ := h
  exact ⟨S₀, δ₀, he.trans he₀, hc⟩

theorem cohE_keeps {rs rs' : List FrameRec} {l : Loc} {S : VTy} {δ : LSub} {ψ : CellU Loc Val}
    (hk : Keeps rs rs' (ResU.single l ψ)) (hψ : ψ.kind = Kind.imm) (h : CohE rs l S δ) :
    CohE rs' l S δ := by
  obtain ⟨S₀, δ₀, he, hc⟩ := h
  exact ⟨S₀, δ₀, he, coh_keeps hk hψ hc⟩

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `vC` is stable along `Ext`, in both modes: at a `mut` cell the stored list is kept, so
the predicate stays equal; the `U` clause is Kripke in the list, and that of the
observable view is `True`. -/
theorem vC_local : ∀ (b : Bool) (T : VTy) {ls ls' : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    Ext ls ls' ρ → vC b T ls δ v ρ → vC b T ls' δ v ρ
  | _, .unit, _, _, _, _, _, _, h => h
  | b, .tensor T₁ T₂, _, _, _, _, _, hk, h => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      have hk' := hk.right hc
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
        vC_local b T₁ (hk'.left hc') h₁, vC_local b T₂ (hk'.right hc') h₂⟩
  | b, .sum T₁ T₂, _, _, _, _, _, hk, h => by
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, vC_local b T₁ (hk.right hc) h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, vC_local b T₂ (hk.right hc) h₂⟩
  | _, .zero, _, _, _, _, _, _, h => h
  | true, .thunk _, _, _, _, _, _, hk, h => fun ls'' hk' => h ls'' (hk.trans hk')
  | false, .thunk _, _, _, _, _, _, _, h => h
  | _, .bang T, _, _, _, _, _, hk, h => ⟨h.1, vC_local true T hk h.2⟩
  | b, .box a T, _, _, _, _, _, hk, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, vC_local b T hk hb, ho⟩
  | b, .ref T, _, _, _, _, _, hk, h => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho,
        vC_local b T ((hk.right hc).right hc') h₂⟩
  | _, .imm a T, ls, ls', _, _, _, hk, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, hcoh⟩, s, u, σ, hs, ls₀, hρ₁, hP, hαs, hls₀⟩ := h
      subst hρ₀
      have hρ₁' := eq_of_compS_empty_left hc
      subst hρ₁'
      subst hρ₁
      have hk₁ : Keeps (rsOf _) (rsOf _) _ := hk.1
      have hcell : CellIn (ResU.single ℓ (CellU.immOf s u σ hs)) s.meet :=
        CellIn.single (by simp)
      refine ⟨α, hα, ℓ, _, _, hc, ⟨rfl, hv, cohE_keeps hk₁ (CellU.kind_immOf _ _ _ _) hcoh⟩,
        s, u, σ, hs, ls₀, rfl, hP, hαs, fun x => ?_⟩
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mpr hx, hb⟩⟩
  | _, .mut a T, ls, ls', _, _, _, hk, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, hls₀,
        hunif⟩ := h
      subst hρ₀
      have hk₁ := hk.right hc
      have hmut : CellIn ρ₁ b :=
        ⟨ℓ, _, by rw [hρ₁]; exact ResU.single_get_self _ _, by simp, le_rfl⟩
      refine ⟨α, hα, ℓ, _, _, hc, ⟨rfl, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, ?_, hunif⟩
      intro x
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mpr hx, hb⟩⟩
  | _, .unk, _, _, _, _, _, _, h => h

/-- The program's relation implies the observable view. -/
theorem vO_obs : ∀ (T : VTy) {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    vC true T ls δ v ρ → vC false T ls δ v ρ
  | .unit, _, _, _, _, h => h
  | .tensor T₁ T₂, _, _, _, _, h => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', vO_obs T₁ h₁, vO_obs T₂ h₂⟩
  | .sum T₁ T₂, _, _, _, _, h => by
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, vO_obs T₁ h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, vO_obs T₂ h₂⟩
  | .zero, _, _, _, _, h => h
  | .thunk _, _, _, _, _, _ => trivial
  | .box a T, _, _, _, _, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, vO_obs T hb, ho⟩
  | .ref T, _, _, _, _, h => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, vO_obs T h₂⟩
  | .bang T, _, _, _, _, h => h
  | .imm _ _, _, _, _, _, h => h
  | .mut _ _, _, _, _, _, h => h
  | .unk, _, _, _, _, h => h

/-- `vC ⊆ vShape`, both modes. -/
theorem vC_vShape : ∀ (b : Bool) (T : VTy) {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    vC b T ls δ v ρ → vShape T δ v ρ
  | _, .unit, _, _, _, _, h => h
  | b, .tensor T₁ T₂, _, _, _, _, h => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', vC_vShape b T₁ h₁, vC_vShape b T₂ h₂⟩
  | b, .sum T₁ T₂, _, _, _, _, h => by
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, vC_vShape b T₁ h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, vC_vShape b T₂ h₂⟩
  | _, .zero, _, _, _, _, h => h
  | true, .thunk _, _, _, _, _, _ => trivial
  | false, .thunk _, _, _, _, _, _ => trivial
  | _, .bang _, _, _, _, _, h => ⟨h.1, trivial⟩
  | b, .box a T, _, _, _, _, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, vC_vShape b T hb, ho⟩
  | b, .ref T, _, _, _, _, h => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, vC_vShape b T h₂⟩
  | _, .imm a T, _, _, _, _, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, -⟩, s, u, σ, hs, _ls₀, hρ, hP, hle, -⟩ := h
      exact ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, s, u, σ, hs, hρ, vC_vShape false T hP, hle⟩
  | _, .mut a T, _, _, _, _, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, b, u, σ, hσ, Q, hw, ls₀, hab, hρ, hQ, -, -⟩ := h
      refine ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, ofS Q, ⟨b, u, σ, hσ, Q, hw, hab, hρ, rfl⟩, ?_⟩
      intro u' σ' h'
      rw [hQ] at h'
      exact vC_vShape true T h'
  | _, .unk, _, _, _, _, h => h

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
cell's bound only; the payload is not consulted. -/
theorem vC_outlives {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) {T : VTy}
    (hT : VOutlives Δ a T) (b : Bool) :
    ∀ (ls : List SRec) (v : Val) (ρ : WRes), vC b T ls δ v ρ → BoLo.Outlives ρ α := by
  induction hT with
  | unit =>
      rintro ls v ρ ⟨rfl, -⟩
      exact ResU.inStratum_empty α
  | zero =>
      rintro ls v ρ h
      cases b <;> exact False.elim h
  | tensor _ _ ih₁ ih₂ =>
      rintro ls v ρ ⟨v₁, v₂, hs⟩
      obtain ⟨-, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      exact (outlives_comp hc α).mpr ⟨ih₁ ls v₁ ρ₁ h₁, ih₂ ls v₂ ρ₂ h₂⟩
  | sum _ _ ih₁ ih₂ =>
      rintro ls v ρ (⟨v₁, hs⟩ | ⟨v₂, hs⟩)
      · exact ih₁ ls v₁ ρ (pure_sep_iff.mp hs).2
      · exact ih₂ ls v₂ ρ (pure_sep_iff.mp hs).2
  | ref _ ih =>
      rintro ls v ρ ⟨ℓ, w, hs⟩
      obtain ⟨-, ρ₁, ρ₂, hc, rfl, h₂⟩ := pure_sep_iff.mp hs
      exact (outlives_comp hc α).mpr
        ⟨ResU.inStratum_single_own α ℓ w, ih ls w ρ₂ h₂⟩
  | bang =>
    rintro ls v ρ ⟨rfl, -⟩
    exact ResU.inStratum_empty α
  | box hlt =>
      rintro ls v ρ ⟨β, hb, -, ho⟩
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ho.mono (le_of_lt (show (α : Life) < β from hlt'))
  | imm hlt =>
      rintro ls v ρ ⟨β, hbi, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, s, w, σ, hσ, _ls₀, hρ₁, -, hle, -⟩
      subst hρ₀
      have e := eq_of_compS_empty_left hc
      subst e; subst hρ₁
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hbi] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single ℓ (lt_of_lt_of_le (show (α : Life) < β from hlt') hle)
  | «mut» hlt =>
      rintro ls v ρ ⟨β, hbi, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, b, w, σ, hσ, Q, hw, _ls₀, hle, hρ₁, -⟩
      subst hρ₀
      have e := eq_of_compS_empty_left hc
      subst e; subst hρ₁
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hbi] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single ℓ
        (show (CellU.mutOf b w σ hσ Q hw).InStratum α from
          lt_of_lt_of_le (show (α : Life) < β from hlt') hle)

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
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

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

mutual
/-- `𝒱⟦A⟧δ` depends on `δ` only at the variables free in `A`. -/
theorem vC_congr : ∀ (A : VTy) {δ₁ δ₂ : LSub}, (∀ y, VFree y A → δ₁.find? y = δ₂.find? y) →
    ∀ (b : Bool) (ls : List SRec), vC b A ls δ₁ = vC b A ls δ₂
  | .unit, _, _, _, b, _ => by cases b <;> rfl
  | .zero, _, _, _, b, _ => by cases b <;> rfl
  | .unk, _, _, _, b, _ => by cases b <;> rfl
  | .tensor A B, _, _, h, b, ls => by
      have h₁ := vC_congr A (fun y hy => h y (Or.inl hy))
      have h₂ := vC_congr B (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vC, h₁, h₂]
  | .sum A B, _, _, h, b, ls => by
      have h₁ := vC_congr A (fun y hy => h y (Or.inl hy))
      have h₂ := vC_congr B (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vC, h₁, h₂]
  | .thunk C, _, _, h, b, ls => by
      have hC := cC_congr C h
      funext v; cases b
      · rfl
      · simp only [vC, hC]
  | .ref A, _, _, h, b, ls => by
      have ih := vC_congr A h
      funext v; cases b <;> simp only [vC, ih]
  | .bang A, _, _, h, b, ls => by
      have ih := vC_congr A h
      funext v; cases b <;> simp only [vC, ih]
  | .box a A, δ₁, δ₂, h, b, ls => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vC_congr A (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vC, ih, atLife_congr' ha]
  | .imm a A, δ₁, δ₂, h, b, ls => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vC_congr A (fun y hy => h y (Or.inr hy))
      have hcoh : ∀ rs m, CohE rs m A δ₁ = CohE rs m A δ₂ := fun rs m => propext
        ⟨fun hc => hc.tyEq (TyEq.of_agree A (fun y hy => (h y (Or.inr hy)).symm)),
         fun hc => hc.tyEq (TyEq.of_agree A (fun y hy => h y (Or.inr hy)))⟩
      funext v; cases b <;> simp only [vC, ih, hcoh, atLife_congr' ha]
  | .mut a A, δ₁, δ₂, h, b, ls => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vC_congr A (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vC, ih, atLife_congr' ha]
/-- `𝒞⟦C⟧δ` depends on `δ` only at the variables free in `C`. -/
theorem cC_congr : ∀ (C : CTy) {δ₁ δ₂ : LSub}, (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) →
    ∀ (ls : List SRec), cC C ls δ₁ = cC C ls δ₂
  | .ret A, _, _, h, ls => by
      have ih := vC_congr A h true
      funext e; simp only [cC, ih]
  | .arr A C, _, _, h, ls => by
      have h₁ := vC_congr A (fun y hy => h y (Or.inl hy)) true ls
      have h₂ := cC_congr C (fun y hy => h y (Or.inr hy)) ls
      funext e; simp only [cC, h₁, h₂]
  | .amp C D, _, _, h, ls => by
      have h₁ := cC_congr C (fun y hy => h y (Or.inl hy)) ls
      have h₂ := cC_congr D (fun y hy => h y (Or.inr hy)) ls
      funext e; simp only [cC, h₁, h₂]
  | .top, _, _, _, _ => rfl
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
end

/-- One computation type at two substitutions is forced the same way. -/
theorem forceE_of_cTyEq {C C' : CTy} {δ δ' : LSub} (h : CTyEq C δ C' δ') :
    forceE C = forceE C' := by
  cases C <;> cases C' <;> first | rfl | simp_all [CTyEq]

mutual
theorem vC_tyEq_aux : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub}, TyEq S δ S' δ' →
    ∀ (b : Bool) (ls : List SRec), vC b S ls δ = vC b S' ls δ'
  | .unit, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      intro b ls; cases b <;> rfl
  | .zero, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      intro b ls; cases b <;> rfl
  | .unk, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      intro b ls; cases b <;> rfl
  | .tensor A B, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vC_tyEq_aux A h.1
      have ihB := vC_tyEq_aux B h.2
      intro b ls; funext v; cases b <;> simp only [vC, ihA, ihB]
  | .sum A B, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vC_tyEq_aux A h.1
      have ihB := vC_tyEq_aux B h.2
      intro b ls; funext v; cases b <;> simp only [vC, ihA, ihB]
  | .thunk C, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := cC_tyEq_aux C h
      have hf := forceE_of_cTyEq h
      intro b ls; funext v; cases b
      · rfl
      · simp only [vC, ih, hf]
  | .ref A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vC_tyEq_aux A h
      intro b ls; funext v; cases b <;> simp only [vC, ih]
  | .bang A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vC_tyEq_aux A h
      intro b ls; funext v; cases b <;> simp only [vC, ih]
  | .box a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vC_tyEq_aux A h.2
      intro b ls; funext v
      cases b <;> (simp only [vC, ih]; exact atLife_congr h.1 rfl)
  | .imm a A, S', δ, δ', h => by
      cases S' <;> simp only [TyEq] at h
      rename_i a' A'
      have ih := vC_tyEq_aux A h.2
      have hcoh : ∀ rs m, CohE rs m A δ = CohE rs m A' δ' := fun rs m =>
        propext ⟨fun hc => hc.tyEq h.2.symm, fun hc => hc.tyEq h.2⟩
      intro b ls; funext v
      cases b <;> (simp only [vC, ih, hcoh]; exact atLife_congr h.1 rfl)
  | .mut a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vC_tyEq_aux A h.2
      intro b ls; funext v
      cases b <;> (simp only [vC, ih]; exact atLife_congr h.1 rfl)
theorem cC_tyEq_aux : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    ∀ (ls : List SRec), cC C ls δ = cC C' ls δ'
  | .ret A, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ih := vC_tyEq_aux A h true
      intro ls; funext e; simp only [cC, ih]
  | .arr A C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vC_tyEq_aux A h.1 true
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
  | .all x c C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      rename_i x' c' C'
      have hT : ∀ (α : Life) (ls : List SRec),
          cC C ls (δ.extend x α) = cC C' ls (δ'.extend x' α) :=
        fun α => cC_tyEq_aux C (h.2 α)
      have hL : ∀ α : Life, LtLife δ c α = LtLife δ' c' α := by
        intro α; unfold LtLife; rw [h.1]
      intro ls; funext e; simp only [cC, hT, hL]
end

/-- `𝒱⟦A⟧` reads a type only up to `TyEq` — `Δ-subst` (`TyEq.applyLSub`) at the relation:
`CohE` is closed under `TyEq`, and every other clause reads its lifetimes through `@aδ`. -/
theorem vC_tyEq {S S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') :
    ∀ (b : Bool) (ls : List SRec), vC b S ls δ = vC b S' ls δ' :=
  vC_tyEq_aux S h

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

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
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

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
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
      vC false T ls δ v A → vShape T δ v B → vC false T ls δ v B
  | .unit, _, _, _, _, _, _, _, hB => hB
  | .unk, _, _, _, _, _, _, _, hB => hB
  | .zero, _, _, _, _, _, _, h, _ => h
  | .thunk _, _, _, _, _, _, _, _, _ => trivial
  | .tensor T₁ T₂, _, _, _, _, hA, hB', h, hs => by
      obtain ⟨v₁, v₂, hk⟩ := h
      obtain ⟨he, A₁, A₂, hcA, h₁, h₂⟩ := pure_sep_iff.mp hk
      obtain ⟨w₁, w₂, hk'⟩ := hs
      obtain ⟨he', B₁, B₂, hcB, g₁, g₂⟩ := pure_sep_iff.mp hk'
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' (he.symm.trans he')
      exact ⟨v₁, v₂, pure_sep_mk he ⟨B₁, B₂, hcB,
        obs_transfer hLB T₁ (hA.left hcA) (hB'.left hcB) h₁ g₁,
        obs_transfer hLB T₂ (hA.right hcA) (hB'.right hcB) h₂ g₂⟩⟩
  | .sum T₁ T₂, _, _, _, _, hA, hB', h, hs => by
      rcases h with ⟨a, hk₁⟩ | ⟨a, hk₁⟩ <;> rcases hs with ⟨b, hk₂⟩ | ⟨b, hk₂⟩
      · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₁'⟩ := pure_sep_iff.mp hk₂
        cases Val.inj₁_inj' (he.symm.trans he')
        exact Or.inl ⟨a, pure_sep_mk he (obs_transfer hLB T₁ hA hB' h₁ h₁')⟩
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk₂
        exact (Val.inj₁_ne_inj₂ (he.symm.trans he')).elim
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk₂
        exact (Val.inj₁_ne_inj₂ (he'.symm.trans he)).elim
      · obtain ⟨he, h₂⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₂'⟩ := pure_sep_iff.mp hk₂
        cases Val.inj₂_inj' (he.symm.trans he')
        exact Or.inr ⟨a, pure_sep_mk he (obs_transfer hLB T₂ hA hB' h₂ h₂')⟩
  | .box a T, _, _, _, _, hA, hB', h, hs => by
      obtain ⟨α, hα, hb, -⟩ := h
      obtain ⟨α', hα', hb', ho'⟩ := hs
      exact ⟨α', hα', obs_transfer hLB T hA hB' hb hb', ho'⟩
  | .ref S, _, _, _, _, hA, hB', h, hs => by
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
        obs_transfer hLB S (hA.right hab) (hB'.right hab') hRb hSb⟩⟩
  | .bang S, _, _, _, _, _, _, h, hs => by
    obtain ⟨hA, hc⟩ := h
    obtain ⟨hB, -⟩ := hs
    subst hA; subst hB
    exact ⟨rfl, hc⟩
  | .imm a S, δ, v, A, B, hA, hB', h, hs => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, hcoh⟩, hpto⟩ := h
      subst hρ₀
      have e₁ := eq_of_compS_empty_left hc
      subst e₁
      obtain ⟨s, u, σ, hσ, hρ₁, hαs, hP⟩ := ptoImmO_read hpto
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
  | .mut a S, δ, v, A, B, hA, hB', h, hs => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, hmut⟩ := h
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

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
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

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
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
  intro T
  induction T using VTy.recV with
  | unit =>
      intro _ _ v c Rl hc _ _ _ _ _ _
      obtain ⟨hce, hv⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, hv⟩
  | thunk _ =>
      intro _ _ v c Rl hc _ _ _ _ _ _
      obtain ⟨hce, -⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, trivial⟩
  | zero =>
      intro _ _ v c Rl hc _ _ _ _ _ _
      exact False.elim hc
  | unk =>
      intro _ _ v c Rl hc _ _ _ _ _ _
      obtain ⟨hce, -⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, trivial⟩
  | sum T₁ T₂ ih₁ ih₂ =>
      intro hx hx₀ v c Rl hc hR hRl hcR hs hcr hcm
      rcases hc with ⟨a, hk₁⟩ | ⟨a, hk₁⟩ <;> rcases hR with ⟨b, hk₂⟩ | ⟨b, hk₂⟩
      · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₁'⟩ := pure_sep_iff.mp hk₂
        subst he; cases Val.inj₁_inj' he'
        exact Or.inl ⟨a, pure_sep_mk rfl (ih₁ (fun h => hx (Or.inl h)) (fun h => hx₀ (Or.inl h))
          h₁ h₁' hRl hcR hs (fun m S u h => hcr m S u (RefPos.sumL h))
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
        exact Or.inr ⟨a, pure_sep_mk rfl (ih₂ (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h))
          h₂ h₂' hRl hcR hs (fun m S u h => hcr m S u (RefPos.sumR h))
          (fun m S h => hcm m S (MutPos.sumR h)))⟩
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro hx hx₀ v c Rl hc hR hRl hcR hs hcr hcm
      obtain ⟨a, b, hk₁⟩ := hc
      obtain ⟨he, c₁, c₂, hcc, h₁, h₂⟩ := pure_sep_iff.mp hk₁
      obtain ⟨a', b', hk₂⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, h₁', h₂'⟩ := pure_sep_iff.mp hk₂
      subst he
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      exact ⟨a, b, pure_sep_mk rfl ⟨_, _, relRes_compS hcc,
        ih₁ (fun h => hx (Or.inl h)) (fun h => hx₀ (Or.inl h)) h₁ h₁' (hRl.left hRR)
          (rebMatch_left hcc hcR) (strat_left hcc hs)
          (fun m S u h => hcr m S u (RefPos.tensorL h)) (fun m S h => hcm m S (MutPos.tensorL h)),
        ih₂ (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h)) h₂ h₂' (hRl.right hRR)
          (rebMatch_left hcc.comm hcR) (strat_left hcc.comm hs)
          (fun m S u h => hcr m S u (RefPos.tensorR h)) (fun m S h => hcm m S (MutPos.tensorR h))⟩⟩
  | box a T ih =>
      intro hx hx₀ v c Rl hc hR hRl hcR hs hcr hcm
      obtain ⟨α, -, hb, -⟩ := hR
      exact ih (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h)) hc hb hRl hcR hs
        (fun m S u h => hcr m S u (RefPos.box h)) (fun m S h => hcm m S (MutPos.box h))
  | ref S _ =>
      intro hx hx₀ v c Rl hc hR hRl hcR hs hcr _
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
      have hobs : vC false S ls δ w W := obs_transfer hLB S (hRl.right hab) hWm hRb hWd
      have hobs' : vC false S ls (δ.extend x β) w W := by
        rw [vC_extend_of_not_free (T := S) hx]; exact hobs
      exact ⟨β, interp_ext_self δ x β, l', pure_sep_mk ⟨rfl, cohE_of_coh (hcr l' S w (RefPos.ref S l') eζ)⟩
        (ptoImmO_make hβ le_rfl hobs' (fun y hy _ => hβls y hy))⟩
  | bang S _ =>
    intro hfx _ v c Rl hc hRl _ _ _ _ _
    obtain ⟨hce, -⟩ := hc
    subst hce; rw [relRes_empty]
    show vC true (.bang S) ls (δ.extend x β) v PMap.empty
    rw [vC_extend_of_not_free hfx true ls δ β]
    obtain ⟨h0, hS⟩ := hRl
    subst h0
    exact ⟨rfl, hS⟩
  | imm a S _ =>
      intro hx hx₀ v c Rl hc hR hRl hcR _ _ _
      have hc' : vShape (.imm a S) (δ.extend x₀ β₀) v c := hc
      have hc'' := hc'
      obtain ⟨α, -, l', hk₁⟩ := hc''
      obtain ⟨hl, s', w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk₁
      have hR' := hR
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
      refine obs_transfer hLB (.imm a S) hRl ?_ hR hc'
      intro m ψ e
      obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
      obtain ⟨ζ₂, eζ₂, her, hwit, -⟩ := hcR m _ (ResU.single_get_self _ _)
      rw [eζ] at eζ₂; cases Option.some.inj eζ₂
      exact ⟨ζ, eζ, by rw [kζ']; simp, (hwit (by rw [kζ']; simp)).symm, her.symm,
        fun hk => absurd (by simp) hk⟩
  | «mut» a S _ =>
      intro hx hx₀ v c Rl hc hR hRl hcR hs _ hcm
      obtain ⟨α, -, l', hk₁⟩ := hc
      obtain ⟨hl, s', w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk₁
      obtain ⟨α', -, l'', ρ₀, ρ₁, hc₀, ⟨hρ₀, hv⟩, hmut⟩ := hR
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

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
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
  · exact lt_trans hlow (hFL.2 aW haW m' hL ζ' t' eζ' ht' t.meet hmt)

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
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

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Lemma 6.113 (I-mono) at the typed world; record in `Paper/S6_5_NonStandardEntailments/Lemmas.lean` -/
/-- `ptoImmS` is monotone in its payload.  6.172 (`withbor1`) frames a payload at the
program's relation (6.64 at `vC true`); the relation's `Imm` clause asks it at the
observable view. -/
theorem ptoImmS_mono {l : Loc} {α : Life} {ls : List SRec} {P P' : List SRec → Val → WProp}
    (h : ∀ ls₀ u σ, P ls₀ u σ → P' ls₀ u σ) {ρ : WRes} (hp : ptoImmS l α ls P ρ) :
    ptoImmS l α ls P' ρ := by
  obtain ⟨s, u, σ, hs, ls₀, hρ, hP, hα, hls₀⟩ := hp
  exact ⟨s, u, σ, hs, ls₀, hρ, h _ _ _ hP, hα, hls₀⟩

end BoCa.Fig16.LogRel.CBPVWorld

namespace BoCa.Fig16.LogRel.CBPVWorld
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

end BoCa.Fig16.LogRel.CBPVWorld

end
