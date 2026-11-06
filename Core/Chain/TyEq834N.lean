import Core.Chain.Iface834N
import Core.RelMu
import Core.ShapeMu

/-!
# The relation reads a type only up to `TyEq`  `[spec §62]`

`docs/new-core/scope-831-interface.md` §2, unit L2 (V1): Core's `vC_tyEq`/`cC_tyEq`
(`Core/RelationFacts.lean`, `vCE_tyEq`/`cC_tyEq_aux`) at the chain, by the same induction on the
type, under type-variable environments related by Core's `EnvEq` (`EnvEqN`). `Imm`'s witness
is closed under `TyEq` by Core's `CohE.tyEq`; `⊸`, `U` read `forceE` alike (`forceE_of_cTyEq`); an
effect row's entries read `B.isZero` alike (`TyEq.isZero_eq`, `capB_congr`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `ImmWitW` is closed under `TyEq` (Core's `CohE.tyEq` at the witness). -/
theorem immWitW_tyEq {A A' : VTy} {δ δ' : LSub} (h : TyEq A δ A' δ') (I : List SRec) (l : Loc)
    (s : LSet) : ImmWitW I l s A δ = ImmWitW I l s A' δ' := by
  unfold ImmWitW
  apply propext
  constructor
  · rintro ⟨x, hx, hs, d, hd, hc⟩; exact ⟨x, hx, hs, d, hd, hc.tyEq h.symm⟩
  · rintro ⟨x, hx, hs, d, hd, hc⟩; exact ⟨x, hx, hs, d, hd, hc.tyEq h⟩

/-- Two environments hold the same candidates at types `TyEq` at `δ` and `δ'` (Core's `EnvEq`). -/
def EnvEqN (η η' : Option (Nat → TEntN)) (δ δ' : LSub) : Prop :=
  ∀ n, (tEnvN η n).P = (tEnvN η' n).P ∧ TyEq (tEnvN η n).ty δ (tEnvN η' n).ty δ'

theorem envEqN_none (δ δ' : LSub) : EnvEqN none none δ δ' := fun n => ⟨rfl, show n = n from rfl⟩

theorem envEqN_tClose {η η' : Option (Nat → TEntN)} {δ δ' : LSub} (hη : EnvEqN η η' δ δ')
    {A A' : VTy} (h : TyEq A δ A' δ') : TyEq (tCloseN η A) δ (tCloseN η' A') δ' := by
  rw [tCloseN_eq, tCloseN_eq]
  exact TyEq.subst A _ _ h (fun n => (hη n).2)

mutual
/-- **`𝒱⟦A⟧` reads a type only up to `TyEq`** (Core's `vC_tyEq`, `vCE_tyEq`). -/
theorem vNE_tyEq : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub} (η η' : Option (Nat → TEntN)),
    TyEq S δ S' δ' → EnvEqN η η' δ δ' → vNE (ℍ := ℍ) η S δ = vNE (ℍ := ℍ) η' S' δ'
  | .unit, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .int w, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .opq k, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .zero, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .unk, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .tvar n, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      subst h
      funext Θ k v ρ
      simp only [vNE, tEnvPN_eq, (hη _).1]
  | .mu A, S', δ, δ', η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      rename_i A'
      have hM : TyEq (tCloseN η (.mu A)) δ (tCloseN η' (.mu A')) δ' := envEqN_tClose hη h
      have hb : ∀ P b', vBN (ℍ := ℍ) (muEnvN η A P) b' A δ = vBN (ℍ := ℍ) (muEnvN η' A' P) b' A' δ' := by
        intro P b'
        have hη' : EnvEqN (muEnvN η A P) (muEnvN η' A' P) δ δ' := fun n => by
          cases n with
          | zero => exact ⟨rfl, hM⟩
          | succ n => exact hη n
        cases b'
        · exact vOE_tyEq A _ _ h hη'
        · exact vNE_tyEq A _ _ h hη'
      funext Θ n v ρ
      exact propext ((vBN_mu (b := true)).trans (Iff.trans (and_congr (TyEq.noMut_iff A 0 h)
        (and_congr (TyEq.Cl_iff _ 0 hM) (forall_congr' fun P => imp_congr
          (by unfold MuClosedN; simp only [hb]) Iff.rfl))) (vBN_mu (b := true)).symm))
  | .fam A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vNE, ih]
  | .tensor A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vNE_tyEq A η η' h.1 hη
      have ihB := vNE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vNE, ihA, ihB]
  | .sum A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vNE_tyEq A η η' h.1 hη
      have ihB := vNE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vNE, ihA, ihB]
  | .thunk C, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := cN_tyEq C h
      have hf := forceE_of_cTyEq h
      funext Θ n v ρ; simp only [vNE, ih, hf]
  | .ref A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vNE, ih]
  | .bang A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vNE, ih]
  | .box a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vNE, ih, h.1]
  | .imm a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h.2 hη
      have hw := immWitW_tyEq (envEqN_tClose hη h.2)
      funext Θ n v ρ; simp only [vNE, ih, hw, h.1]
  | .mut a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vNE, ih, h.1]
/-- The observable view reads a type only up to `TyEq`. -/
theorem vOE_tyEq : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub} (η η' : Option (Nat → TEntN)),
    TyEq S δ S' δ' → EnvEqN η η' δ δ' → vOE (ℍ := ℍ) η S δ = vOE (ℍ := ℍ) η' S' δ'
  | .unit, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .int w, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .opq k, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .zero, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .unk, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .tvar n, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      subst h
      funext Θ k v ρ
      simp only [vOE, tEnvPN_eq, (hη _).1]
  | .mu A, S', δ, δ', η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      rename_i A'
      have hM : TyEq (tCloseN η (.mu A)) δ (tCloseN η' (.mu A')) δ' := envEqN_tClose hη h
      have hb : ∀ P b', vBN (ℍ := ℍ) (muEnvN η A P) b' A δ = vBN (ℍ := ℍ) (muEnvN η' A' P) b' A' δ' := by
        intro P b'
        have hη' : EnvEqN (muEnvN η A P) (muEnvN η' A' P) δ δ' := fun n => by
          cases n with
          | zero => exact ⟨rfl, hM⟩
          | succ n => exact hη n
        cases b'
        · exact vOE_tyEq A _ _ h hη'
        · exact vNE_tyEq A _ _ h hη'
      funext Θ n v ρ
      exact propext ((vBN_mu (b := false)).trans (Iff.trans (and_congr (TyEq.noMut_iff A 0 h)
        (and_congr (TyEq.Cl_iff _ 0 hM) (forall_congr' fun P => imp_congr
          (by unfold MuClosedN; simp only [hb]) Iff.rfl))) (vBN_mu (b := false)).symm))
  | .fam A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vOE, ih]
  | .tensor A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vOE_tyEq A η η' h.1 hη
      have ihB := vOE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vOE, ihA, ihB]
  | .sum A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vOE_tyEq A η η' h.1 hη
      have ihB := vOE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vOE, ihA, ihB]
  | .thunk C, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .ref A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vOE, ih]
  | .bang A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vOE, ih]
  | .box a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vOE, ih, h.1]
  | .imm a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h.2 hη
      have hw := immWitW_tyEq (envEqN_tClose hη h.2)
      funext Θ n v ρ; simp only [vOE, ih, hw, h.1]
  | .mut a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vOE, ih, h.1]
/-- **`𝒞⟦C⟧` reads a type only up to `CTyEq`** (Core's `cC_tyEq`, `cC_tyEq_aux`). -/
theorem cN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    cN (ℍ := ℍ) C δ = cN (ℍ := ℍ) C' δ'
  | .ret A, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ih := vNE_tyEq A none none h (envEqN_none _ _)
      funext Θ c n ls e ρ; simp only [cN, ih]
  | .arr A C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNE_tyEq A none none h.1 (envEqN_none _ _)
      have ihC := cN_tyEq C h.2
      funext Θ c n ls e ρ; simp only [cN, ihA, ihC]
  | .amp C D, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihC := cN_tyEq C h.1
      have ihD := cN_tyEq D h.2
      funext Θ c n ls e ρ; simp only [cN, ihC, ihD]
  | .top, C', _, _, h => by cases C' <;> simp only [CTyEq] at h; rfl
  | .nu C, C', _, _, h => by cases C' <;> simp only [CTyEq] at h; rfl
  | .all x b C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      rename_i x' b' C'
      have hT : ∀ α : Life, cN (ℍ := ℍ) C (δ.extend x α) = cN (ℍ := ℍ) C' (δ'.extend x' α) :=
        fun α => cN_tyEq C (h.2 α)
      have hL : ∀ α : Life, LtLife δ b α = LtLife δ' b' α := by
        intro α; unfold LtLife; rw [h.1]
      funext Θ c n ls e ρ; simp only [cN, hT, hL]
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hR := retN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c k ls e ρ; simp only [cN, entN, ihA, ihB, ihF, hT, hR, hz]; rw [capB_congr hz]
/-- The table of a row's layers reads a type only up to `CTyEq`. -/
theorem tabN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    tabN (ℍ := ℍ) C δ = tabN (ℍ := ℍ) C' δ'
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c; simp only [tabN, entN, ihA, ihB, ihF, hT, hz]; rw [capB_congr hz]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
/-- The cancel obligation reads a type only up to `CTyEq`. -/
theorem finN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    finN (ℍ := ℍ) C δ = finN (ℍ := ℍ) C' δ'
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c; simp only [finN, entN, ihA, ihB, ihF, hT, hz]; rw [capB_congr hz]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
/-- The answer of a row's layers reads a type only up to `CTyEq`. -/
theorem retN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    retN (ℍ := ℍ) C δ = retN (ℍ := ℍ) C' δ'
  | .ret A, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNE_tyEq A none none h (envEqN_none _ _)
      funext Θ n v ρ; simp only [retN, ihA]
  | .eff _ _ _ _ _ _ _ C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      have ih := retN_tyEq C h.2.2.2.2.2.2
      funext Θ n v ρ; simp only [retN, ih]
  | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
end

/-- **`𝒱⟦A⟧` reads a type only up to `TyEq`** (Core's `vC_tyEq`). -/
theorem vN_tyEq (S : VTy) {S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') :
    vN (ℍ := ℍ) S δ = vN (ℍ := ℍ) S' δ' :=
  vNE_tyEq S none none h (envEqN_none _ _)

/-- The observable view reads a type only up to `TyEq`. -/
theorem vO_tyEq (S : VTy) {S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') :
    vO (ℍ := ℍ) S δ = vO (ℍ := ℍ) S' δ' :=
  vOE_tyEq S none none h (envEqN_none _ _)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
