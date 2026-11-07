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


/-- `ν`'s one-entry environments at `TyEq` closed types are related. -/
theorem envEqN_nu {T T' : VTy} {P : LocTy → Nat → Val → WRes → Prop} {δ δ' : LSub}
    (hT : TyEq T δ T' δ') : EnvEqN (nuEnvN T P) (nuEnvN T' P) δ δ' := fun n => by
  cases n with
  | zero => exact ⟨rfl, hT⟩
  | succ n => exact ⟨rfl, show n = n from rfl⟩

mutual
/-- **`𝒱⟦A⟧` reads a type only up to `TyEq`** (Core's `vC_tyEq`, `vCE_tyEq`). -/
theorem vNE_tyEq : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub} (η η' : Option (Nat → TEntN)),
    TyEq S δ S' δ' → EnvEqN η η' δ δ' → vNE₀ (ℍ := ℍ) η S δ = vNE₀ (ℍ := ℍ) η' S' δ'
  | .unit, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .int w, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .opq k, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .zero, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .unk, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .tvar n, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      subst h
      funext Θ k v ρ
      simp only [vNE₀, tEnvPN_eq, (hη _).1]
  | .mu A, S', δ, δ', η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      rename_i A'
      have hM : TyEq (tCloseN η (.mu A)) δ (tCloseN η' (.mu A')) δ' := envEqN_tClose hη h
      have hb : ∀ P b', vBN₀ (ℍ := ℍ) (muEnvN η A P) b' A δ = vBN₀ (ℍ := ℍ) (muEnvN η' A' P) b' A' δ' := by
        intro P b'
        have hη' : EnvEqN (muEnvN η A P) (muEnvN η' A' P) δ δ' := fun n => by
          cases n with
          | zero => exact ⟨rfl, hM⟩
          | succ n => exact hη n
        cases b'
        · exact vOE_tyEq A _ _ h hη'
        · exact vNE_tyEq A _ _ h hη'
      funext Θ n v ρ
      exact propext ((vBN_mu₀ (b := true)).trans (Iff.trans (and_congr (TyEq.noMut_iff A 0 h)
        (and_congr (TyEq.Cl_iff _ 0 hM) (forall_congr' fun P => imp_congr
          (by unfold MuClosedN₀; simp only [hb]) Iff.rfl))) (vBN_mu₀ (b := true)).symm))
  | .fam A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vNE₀, ih]
  | .tensor A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vNE_tyEq A η η' h.1 hη
      have ihB := vNE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vNE₀, ihA, ihB]
  | .sum A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vNE_tyEq A η η' h.1 hη
      have ihB := vNE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vNE₀, ihA, ihB]
  | .thunk C, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := cN_tyEq C h
      have hf := forceE_of_cTyEq h
      funext Θ n v ρ; simp only [vNE₀, ih, hf]
  | .ref A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vNE₀, ih]
  | .bang A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vNE₀, ih]
  | .box a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vNE₀, ih, h.1]
  | .imm a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h.2 hη
      have hw := immWitW_tyEq (envEqN_tClose hη h.2)
      funext Θ n v ρ; simp only [vNE₀, ih, hw, h.1]
  | .mut a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vNE₀, ih, h.1]
  termination_by structural x => x
/-- The observable view reads a type only up to `TyEq`. -/
theorem vOE_tyEq : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub} (η η' : Option (Nat → TEntN)),
    TyEq S δ S' δ' → EnvEqN η η' δ δ' → vOE₀ (ℍ := ℍ) η S δ = vOE₀ (ℍ := ℍ) η' S' δ'
  | .unit, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .int w, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .opq k, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .zero, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .unk, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .tvar n, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      subst h
      funext Θ k v ρ
      simp only [vOE₀, tEnvPN_eq, (hη _).1]
  | .mu A, S', δ, δ', η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      rename_i A'
      have hM : TyEq (tCloseN η (.mu A)) δ (tCloseN η' (.mu A')) δ' := envEqN_tClose hη h
      have hb : ∀ P b', vBN₀ (ℍ := ℍ) (muEnvN η A P) b' A δ = vBN₀ (ℍ := ℍ) (muEnvN η' A' P) b' A' δ' := by
        intro P b'
        have hη' : EnvEqN (muEnvN η A P) (muEnvN η' A' P) δ δ' := fun n => by
          cases n with
          | zero => exact ⟨rfl, hM⟩
          | succ n => exact hη n
        cases b'
        · exact vOE_tyEq A _ _ h hη'
        · exact vNE_tyEq A _ _ h hη'
      funext Θ n v ρ
      exact propext ((vBN_mu₀ (b := false)).trans (Iff.trans (and_congr (TyEq.noMut_iff A 0 h)
        (and_congr (TyEq.Cl_iff _ 0 hM) (forall_congr' fun P => imp_congr
          (by unfold MuClosedN₀; simp only [hb]) Iff.rfl))) (vBN_mu₀ (b := false)).symm))
  | .fam A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vOE₀, ih]
  | .tensor A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vOE_tyEq A η η' h.1 hη
      have ihB := vOE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vOE₀, ihA, ihB]
  | .sum A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vOE_tyEq A η η' h.1 hη
      have ihB := vOE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vOE₀, ihA, ihB]
  | .thunk C, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .ref A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vOE₀, ih]
  | .bang A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vOE₀, ih]
  | .box a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vOE₀, ih, h.1]
  | .imm a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h.2 hη
      have hw := immWitW_tyEq (envEqN_tClose hη h.2)
      funext Θ n v ρ; simp only [vOE₀, ih, hw, h.1]
  | .mut a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vOE₀, ih, h.1]
  termination_by structural x => x
/-- **One unfolding reads a type only up to `CTyEq`** (Core's `cB_tyEq`), at closed types for
`X` related at every pair of substitutions. -/
theorem cBN_tyEq (T T' : VTy) (R : CandN) : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub},
    CTyEq C δ C' δ' → (∀ δ₁ δ₂, TyEq T δ₁ T' δ₂) →
    cBN₀ (ℍ := ℍ) T R C δ = cBN₀ (ℍ := ℍ) T' R C' δ'
  | .ret A, C', _, _, h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ih := vNE_tyEq A _ _ h (envEqN_nu (P := thunkRN R) (hT _ _))
      funext Θ c n ls e ρ; simp only [cBN₀, ih]
  | .arr A C, C', _, _, h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNE_tyEq A none none h.1 (envEqN_none _ _)
      have ihC := cBN_tyEq T T' R C h.2 hT
      funext Θ c n ls e ρ; simp only [cBN₀, ihA, ihC]
  | .amp C D, C', _, _, h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ihC := cBN_tyEq T T' R C h.1 hT
      have ihD := cBN_tyEq T T' R D h.2 hT
      funext Θ c n ls e ρ; simp only [cBN₀, ihC, ihD]
  | .top, C', _, _, h, _ => by cases C' <;> simp only [CTyEq] at h; rfl
  | .nu C, C', _, _, h, _ => by cases C' <;> simp only [CTyEq] at h; rfl
  | .all x b C, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      rename_i x' b' C'
      have hC : ∀ α : Life, cBN₀ (ℍ := ℍ) T R C (δ.extend x α) = cBN₀ (ℍ := ℍ) T' R C' (δ'.extend x' α) :=
        fun α => cBN_tyEq T T' R C (h.2 α) hT
      have hL : ∀ α : Life, LtLife δ b α = LtLife δ' b' α := by
        intro α; unfold LtLife; rw [h.1]
      funext Θ c n ls e ρ; simp only [cBN₀, hC, hL]
  | .eff n i q A B fin rc C, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hTb := tabN_tyEq C hC
      have hR := retNX_tyEq T T' (thunkRN R) C hC (hT _ _)
      have hz := TyEq.isZero_eq B hB
      funext Θ c k ls e ρ; simp only [cBN₀, entN, ihA, ihB, ihF, hTb, hR, hz]; rw [capB_congr hz]
  termination_by structural x => x
/-- The answer of a row's layers with one type variable reads a type only up to `CTyEq`. -/
theorem retNX_tyEq (T T' : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (C : CTy) {C' : CTy}
    {δ δ' : LSub}, CTyEq C δ C' δ' → TyEq T δ T' δ' →
    retNX₀ (ℍ := ℍ) T P C δ = retNX₀ (ℍ := ℍ) T' P C' δ'
  | .ret A, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNE_tyEq A _ _ h (envEqN_nu (P := P) hT)
      funext Θ n v ρ; simp only [retNX₀, ihA]
  | .eff _ _ _ _ _ _ _ C, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ih := retNX_tyEq T T' P C h.2.2.2.2.2.2 hT
      funext Θ n v ρ; simp only [retNX₀, ih]
  | .arr _ _, C', _, _, h, _ | .amp _ _, C', _, _, h, _ | .top, C', _, _, h, _
  | .all _ _ _, C', _, _, h, _ | .nu _, C', _, _, h, _ => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
/-- **`𝒞⟦C⟧` reads a type only up to `CTyEq`** (Core's `cC_tyEq`, `cC_tyEq_aux`). -/
theorem cN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    cN₀ (ℍ := ℍ) C δ = cN₀ (ℍ := ℍ) C' δ'
  | .ret A, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ih := vNE_tyEq A none none h (envEqN_none _ _)
      funext Θ c n ls e ρ; simp only [cN₀, ih]
  | .arr A C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNE_tyEq A none none h.1 (envEqN_none _ _)
      have ihC := cN_tyEq C h.2
      funext Θ c n ls e ρ; simp only [cN₀, ihA, ihC]
  | .amp C D, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihC := cN_tyEq C h.1
      have ihD := cN_tyEq D h.2
      funext Θ c n ls e ρ; simp only [cN₀, ihC, ihD]
  | .top, C', _, _, h => by cases C' <;> simp only [CTyEq] at h; rfl
  | .nu C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      rename_i C'
      have hO : C.NuShape ↔ C'.NuShape := CTyEq.nuShape_iff h
      have hB : C.NuShape → ∀ R : CandN, cBN₀ (ℍ := ℍ) (.thunk (.nu C)) R C δ =
          cBN₀ (ℍ := ℍ) (.thunk (.nu C')) R C' δ' := fun hC R => by
        rw [cBN_poly_ty₀ _ .unit R hC.nuLeaf, cBN_poly_ty₀ _ .unit R (hO.mp hC).nuLeaf]
        exact cBN_tyEq .unit .unit R C h (fun _ _ => trivial)
      funext Θ c n ls e ρ
      simp only [cN₀]
      exact propext ⟨fun k hC' => by
          obtain ⟨R, hR, hr⟩ := k (hO.mpr hC')
          exact ⟨R, by rwa [← hB (hO.mpr hC') R], hr⟩,
        fun k hC => by
          obtain ⟨R, hR, hr⟩ := k (hO.mp hC)
          exact ⟨R, by rwa [hB hC R], hr⟩⟩
  | .all x b C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      rename_i x' b' C'
      have hT : ∀ α : Life, cN₀ (ℍ := ℍ) C (δ.extend x α) = cN₀ (ℍ := ℍ) C' (δ'.extend x' α) :=
        fun α => cN_tyEq C (h.2 α)
      have hL : ∀ α : Life, LtLife δ b α = LtLife δ' b' α := by
        intro α; unfold LtLife; rw [h.1]
      funext Θ c n ls e ρ; simp only [cN₀, hT, hL]
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hR := retN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c k ls e ρ; simp only [cN₀, entN, ihA, ihB, ihF, hT, hR, hz]; rw [capB_congr hz]
  termination_by structural x => x
/-- The table of a row's layers reads a type only up to `CTyEq`. -/
theorem tabN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    tabN₀ (ℍ := ℍ) C δ = tabN₀ (ℍ := ℍ) C' δ'
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c; simp only [tabN₀, entN, ihA, ihB, ihF, hT, hz]; rw [capB_congr hz]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
/-- The cancel obligation reads a type only up to `CTyEq`. -/
theorem finN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    finN₀ (ℍ := ℍ) C δ = finN₀ (ℍ := ℍ) C' δ'
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c; simp only [finN₀, entN, ihA, ihB, ihF, hT, hz]; rw [capB_congr hz]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
/-- The answer of a row's layers reads a type only up to `CTyEq`. -/
theorem retN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    retN₀ (ℍ := ℍ) C δ = retN₀ (ℍ := ℍ) C' δ'
  | .ret A, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNE_tyEq A none none h (envEqN_none _ _)
      funext Θ n v ρ; simp only [retN₀, ihA]
  | .eff _ _ _ _ _ _ _ C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      have ih := retN_tyEq C h.2.2.2.2.2.2
      funext Θ n v ρ; simp only [retN₀, ih]
  | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
end

/-- **`𝒱⟦A⟧` reads a type only up to `TyEq`** (Core's `vC_tyEq`). -/
theorem vN_tyEq (S : VTy) {S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') :
    vN₀ (ℍ := ℍ) S δ = vN₀ (ℍ := ℍ) S' δ' :=
  vNE_tyEq S none none h (envEqN_none _ _)

/-- The observable view reads a type only up to `TyEq`. -/
theorem vO_tyEq (S : VTy) {S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') :
    vO₀ (ℍ := ℍ) S δ = vO₀ (ℍ := ℍ) S' δ' :=
  vOE_tyEq S none none h (envEqN_none _ _)

/-- **`vNX₀` reads a type only up to `TyEq`**, at closed types for `X` related by `TyEq`. -/
theorem vNX_tyEq (T T' : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (S : VTy) {S' : VTy}
    {δ δ' : LSub}, TyEq S δ S' δ' → TyEq T δ T' δ' →
    vNX₀ (ℍ := ℍ) T P S δ = vNX₀ (ℍ := ℍ) T' P S' δ' :=
  fun S _ _ _ h hT => vNE_tyEq S _ _ h (envEqN_nu hT)

/-- `vOX₀` reads a type only up to `TyEq`. -/
theorem vOX_tyEq (T T' : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (S : VTy) {S' : VTy}
    {δ δ' : LSub}, TyEq S δ S' δ' → TyEq T δ T' δ' →
    vOX₀ (ℍ := ℍ) T P S δ = vOX₀ (ℍ := ℍ) T' P S' δ' :=
  fun S _ _ _ h hT => vOE_tyEq S _ _ h (envEqN_nu hT)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
