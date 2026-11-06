import Core.Chain.Iface834N
import Core.RelMu
import Core.ShapeMu

/-!
# The relation reads a type only up to `TyEq`  `[spec §62]`

`docs/new-core/scope-831-interface.md` §2, unit L2 (V1): Core's `vC_tyEq`/`cC_tyEq`
(`Core/RelationFacts.lean`, `vCE_tyEq`/`cC_tyEq_aux`) at the chain, by the same induction on the
type. The chain's relation has no type-variable environment (type variables and `μ` are outside
the fragment and read as empty), so Core's `EnvEq` argument has no counterpart. `Imm`'s witness
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

mutual
/-- **`𝒱⟦A⟧` reads a type only up to `TyEq`** (Core's `vC_tyEq`, `vCE_tyEq`). -/
theorem vN_tyEq : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub}, TyEq S δ S' δ' →
    vN (ℍ := ℍ) S δ = vN (ℍ := ℍ) S' δ'
  | .unit, S', _, _, h => by cases S' <;> simp only [TyEq] at h; rfl
  | .int w, S', _, _, h => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .opq k, S', _, _, h => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .zero, S', _, _, h => by cases S' <;> simp only [TyEq] at h; rfl
  | .unk, S', _, _, h => by cases S' <;> simp only [TyEq] at h; rfl
  | .tvar n, S', _, _, h => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .mu A, S', _, _, h => by cases S' <;> simp only [TyEq] at h; rfl
  | .fam A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vN_tyEq A h
      funext Θ n v ρ; simp only [vN, ih]
  | .tensor A B, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vN_tyEq A h.1
      have ihB := vN_tyEq B h.2
      funext Θ n v ρ; simp only [vN, ihA, ihB]
  | .sum A B, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vN_tyEq A h.1
      have ihB := vN_tyEq B h.2
      funext Θ n v ρ; simp only [vN, ihA, ihB]
  | .thunk C, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := cN_tyEq C h
      have hf := forceE_of_cTyEq h
      funext Θ n v ρ; simp only [vN, ih, hf]
  | .ref A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vN_tyEq A h
      funext Θ n v ρ; simp only [vN, ih]
  | .bang A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vN_tyEq A h
      funext Θ n v ρ; simp only [vN, ih]
  | .box a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vN_tyEq A h.2
      funext Θ n v ρ; simp only [vN, ih, h.1]
  | .imm a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vO_tyEq A h.2
      have hw := immWitW_tyEq h.2
      funext Θ n v ρ; simp only [vN, ih, hw, h.1]
  | .mut a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vN_tyEq A h.2
      funext Θ n v ρ; simp only [vN, ih, h.1]
  termination_by structural x => x
/-- The observable view reads a type only up to `TyEq`. -/
theorem vO_tyEq : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub}, TyEq S δ S' δ' →
    vO (ℍ := ℍ) S δ = vO (ℍ := ℍ) S' δ'
  | .unit, S', _, _, h => by cases S' <;> simp only [TyEq] at h; rfl
  | .int w, S', _, _, h => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .opq k, S', _, _, h => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .zero, S', _, _, h => by cases S' <;> simp only [TyEq] at h; rfl
  | .unk, S', _, _, h => by cases S' <;> simp only [TyEq] at h; rfl
  | .tvar n, S', _, _, h => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .mu A, S', _, _, h => by cases S' <;> simp only [TyEq] at h; rfl
  | .fam A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vO_tyEq A h
      funext Θ n v ρ; simp only [vO, ih]
  | .tensor A B, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vO_tyEq A h.1
      have ihB := vO_tyEq B h.2
      funext Θ n v ρ; simp only [vO, ihA, ihB]
  | .sum A B, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vO_tyEq A h.1
      have ihB := vO_tyEq B h.2
      funext Θ n v ρ; simp only [vO, ihA, ihB]
  | .thunk C, S', _, _, h => by cases S' <;> simp only [TyEq] at h; rfl
  | .ref A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vO_tyEq A h
      funext Θ n v ρ; simp only [vO, ih]
  | .bang A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vN_tyEq A h
      funext Θ n v ρ; simp only [vO, ih]
  | .box a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vO_tyEq A h.2
      funext Θ n v ρ; simp only [vO, ih, h.1]
  | .imm a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vO_tyEq A h.2
      have hw := immWitW_tyEq h.2
      funext Θ n v ρ; simp only [vO, ih, hw, h.1]
  | .mut a A, S', _, _, h => by
      cases S' <;> simp only [TyEq] at h
      have ih := vN_tyEq A h.2
      funext Θ n v ρ; simp only [vO, ih, h.1]
  termination_by structural x => x
/-- **`vNX` reads a type only up to `TyEq`**, at closed types for `X` related by `TyEq`. -/
theorem vNX_tyEq (T T' : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (S : VTy) {S' : VTy}
    {δ δ' : LSub}, TyEq S δ S' δ' → TyEq T δ T' δ' →
    vNX (ℍ := ℍ) T P S δ = vNX (ℍ := ℍ) T' P S' δ'
  | .unit, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; rfl
  | .int w, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .opq k, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .zero, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; rfl
  | .unk, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; rfl
  | .tvar n, S', _, _, h, _ => by cases S' <;> simp only [TyEq] at h; subst h; cases n <;> rfl
  | .mu A, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; rfl
  | .fam A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNX_tyEq T T' P A h hT
      funext Θ n v ρ; simp only [vNX, ih]
  | .tensor A B, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vNX_tyEq T T' P A h.1 hT
      have ihB := vNX_tyEq T T' P B h.2 hT
      funext Θ n v ρ; simp only [vNX, ihA, ihB]
  | .sum A B, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vNX_tyEq T T' P A h.1 hT
      have ihB := vNX_tyEq T T' P B h.2 hT
      funext Θ n v ρ; simp only [vNX, ihA, ihB]
  | .thunk C, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := cN_tyEq C h
      have hf := forceE_of_cTyEq h
      funext Θ n v ρ; simp only [vNX, ih, hf]
  | .ref A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNX_tyEq T T' P A h hT
      funext Θ n v ρ; simp only [vNX, ih]
  | .bang A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNX_tyEq T T' P A h hT
      funext Θ n v ρ; simp only [vNX, ih]
  | .box a A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNX_tyEq T T' P A h.2 hT
      funext Θ n v ρ; simp only [vNX, ih, h.1]
  | .imm a A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOX_tyEq T T' P A h.2 hT
      have hw := immWitW_tyEq (TyEq.inst h.2 hT)
      funext Θ n v ρ; simp only [vNX, ih, hw, h.1]
  | .mut a A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNX_tyEq T T' P A h.2 hT
      funext Θ n v ρ; simp only [vNX, ih, h.1]
  termination_by structural x => x
/-- `vOX` reads a type only up to `TyEq`. -/
theorem vOX_tyEq (T T' : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (S : VTy) {S' : VTy}
    {δ δ' : LSub}, TyEq S δ S' δ' → TyEq T δ T' δ' →
    vOX (ℍ := ℍ) T P S δ = vOX (ℍ := ℍ) T' P S' δ'
  | .unit, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; rfl
  | .int w, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .opq k, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .zero, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; rfl
  | .unk, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; rfl
  | .tvar n, S', _, _, h, _ => by cases S' <;> simp only [TyEq] at h; subst h; cases n <;> rfl
  | .mu A, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; rfl
  | .fam A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOX_tyEq T T' P A h hT
      funext Θ n v ρ; simp only [vOX, ih]
  | .tensor A B, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vOX_tyEq T T' P A h.1 hT
      have ihB := vOX_tyEq T T' P B h.2 hT
      funext Θ n v ρ; simp only [vOX, ihA, ihB]
  | .sum A B, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vOX_tyEq T T' P A h.1 hT
      have ihB := vOX_tyEq T T' P B h.2 hT
      funext Θ n v ρ; simp only [vOX, ihA, ihB]
  | .thunk C, S', _, _, h, hT => by cases S' <;> simp only [TyEq] at h; rfl
  | .ref A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOX_tyEq T T' P A h hT
      funext Θ n v ρ; simp only [vOX, ih]
  | .bang A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNX_tyEq T T' P A h hT
      funext Θ n v ρ; simp only [vOX, ih]
  | .box a A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOX_tyEq T T' P A h.2 hT
      funext Θ n v ρ; simp only [vOX, ih, h.1]
  | .imm a A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOX_tyEq T T' P A h.2 hT
      have hw := immWitW_tyEq (TyEq.inst h.2 hT)
      funext Θ n v ρ; simp only [vOX, ih, hw, h.1]
  | .mut a A, S', _, _, h, hT => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNX_tyEq T T' P A h.2 hT
      funext Θ n v ρ; simp only [vOX, ih, h.1]
  termination_by structural x => x
/-- **One unfolding reads a type only up to `CTyEq`** (Core's `cB_tyEq`), at closed types for
`X` related at every pair of substitutions. -/
theorem cBN_tyEq (T T' : VTy) (R : CandN) : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub},
    CTyEq C δ C' δ' → (∀ δ₁ δ₂, TyEq T δ₁ T' δ₂) →
    cBN (ℍ := ℍ) T R C δ = cBN (ℍ := ℍ) T' R C' δ'
  | .ret A, C', _, _, h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ih := vNX_tyEq T T' (thunkRN R) A h (hT _ _)
      funext Θ c n ls e ρ; simp only [cBN, ih]
  | .arr A C, C', _, _, h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vN_tyEq A h.1
      have ihC := cBN_tyEq T T' R C h.2 hT
      funext Θ c n ls e ρ; simp only [cBN, ihA, ihC]
  | .amp C D, C', _, _, h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ihC := cBN_tyEq T T' R C h.1 hT
      have ihD := cBN_tyEq T T' R D h.2 hT
      funext Θ c n ls e ρ; simp only [cBN, ihC, ihD]
  | .top, C', _, _, h, _ => by cases C' <;> simp only [CTyEq] at h; rfl
  | .nu C, C', _, _, h, _ => by cases C' <;> simp only [CTyEq] at h; rfl
  | .all x b C, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      rename_i x' b' C'
      have hC : ∀ α : Life, cBN (ℍ := ℍ) T R C (δ.extend x α) = cBN (ℍ := ℍ) T' R C' (δ'.extend x' α) :=
        fun α => cBN_tyEq T T' R C (h.2 α) hT
      have hL : ∀ α : Life, LtLife δ b α = LtLife δ' b' α := by
        intro α; unfold LtLife; rw [h.1]
      funext Θ c n ls e ρ; simp only [cBN, hC, hL]
  | .eff n i q A B fin rc C, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vN_tyEq A hA
      have ihB := vN_tyEq B hB
      have ihF := finN_tyEq fin hF
      have hTb := tabN_tyEq C hC
      have hR := retNX_tyEq T T' (thunkRN R) C hC (hT _ _)
      have hz := TyEq.isZero_eq B hB
      funext Θ c k ls e ρ; simp only [cBN, entN, ihA, ihB, ihF, hTb, hR, hz]; rw [capB_congr hz]
  termination_by structural x => x
/-- The answer of a row's layers with one type variable reads a type only up to `CTyEq`. -/
theorem retNX_tyEq (T T' : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (C : CTy) {C' : CTy}
    {δ δ' : LSub}, CTyEq C δ C' δ' → TyEq T δ T' δ' →
    retNX (ℍ := ℍ) T P C δ = retNX (ℍ := ℍ) T' P C' δ'
  | .ret A, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNX_tyEq T T' P A h hT
      funext Θ n v ρ; simp only [retNX, ihA]
  | .eff _ _ _ _ _ _ _ C, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ih := retNX_tyEq T T' P C h.2.2.2.2.2.2 hT
      funext Θ n v ρ; simp only [retNX, ih]
  | .arr _ _, C', _, _, h, _ | .amp _ _, C', _, _, h, _ | .top, C', _, _, h, _
  | .all _ _ _, C', _, _, h, _ | .nu _, C', _, _, h, _ => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
/-- **`𝒞⟦C⟧` reads a type only up to `CTyEq`** (Core's `cC_tyEq`, `cC_tyEq_aux`). -/
theorem cN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    cN (ℍ := ℍ) C δ = cN (ℍ := ℍ) C' δ'
  | .ret A, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ih := vN_tyEq A h
      funext Θ c n ls e ρ; simp only [cN, ih]
  | .arr A C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vN_tyEq A h.1
      have ihC := cN_tyEq C h.2
      funext Θ c n ls e ρ; simp only [cN, ihA, ihC]
  | .amp C D, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihC := cN_tyEq C h.1
      have ihD := cN_tyEq D h.2
      funext Θ c n ls e ρ; simp only [cN, ihC, ihD]
  | .top, C', _, _, h => by cases C' <;> simp only [CTyEq] at h; rfl
  | .nu C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      rename_i C'
      have hO : C.NuShape ↔ C'.NuShape := CTyEq.nuShape_iff h
      have hB : C.NuShape → ∀ R : CandN, cBN (ℍ := ℍ) (.thunk (.nu C)) R C δ =
          cBN (ℍ := ℍ) (.thunk (.nu C')) R C' δ' := fun hC R => by
        rw [cBN_poly_ty _ .unit R hC.nuLeaf, cBN_poly_ty _ .unit R (hO.mp hC).nuLeaf]
        exact cBN_tyEq .unit .unit R C h (fun _ _ => trivial)
      funext Θ c n ls e ρ
      simp only [cN]
      exact propext ⟨fun k hC' => by
          obtain ⟨R, hR, hr⟩ := k (hO.mpr hC')
          exact ⟨R, by rwa [← hB (hO.mpr hC') R], hr⟩,
        fun k hC => by
          obtain ⟨R, hR, hr⟩ := k (hO.mp hC)
          exact ⟨R, by rwa [hB hC R], hr⟩⟩
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
      have ihA := vN_tyEq A hA
      have ihB := vN_tyEq B hB
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hR := retN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c k ls e ρ; simp only [cN, entN, ihA, ihB, ihF, hT, hR, hz]; rw [capB_congr hz]
  termination_by structural x => x
/-- The table of a row's layers reads a type only up to `CTyEq`. -/
theorem tabN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    tabN (ℍ := ℍ) C δ = tabN (ℍ := ℍ) C' δ'
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vN_tyEq A hA
      have ihB := vN_tyEq B hB
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c; simp only [tabN, entN, ihA, ihB, ihF, hT, hz]; rw [capB_congr hz]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
/-- The cancel obligation reads a type only up to `CTyEq`. -/
theorem finN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    finN (ℍ := ℍ) C δ = finN (ℍ := ℍ) C' δ'
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vN_tyEq A hA
      have ihB := vN_tyEq B hB
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c; simp only [finN, entN, ihA, ihB, ihF, hT, hz]; rw [capB_congr hz]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
/-- The answer of a row's layers reads a type only up to `CTyEq`. -/
theorem retN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    retN (ℍ := ℍ) C δ = retN (ℍ := ℍ) C' δ'
  | .ret A, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vN_tyEq A h
      funext Θ n v ρ; simp only [retN, ihA]
  | .eff _ _ _ _ _ _ _ C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      have ih := retN_tyEq C h.2.2.2.2.2.2
      funext Θ n v ρ; simp only [retN, ih]
  | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
end

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
