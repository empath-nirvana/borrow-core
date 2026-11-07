import Core.CapNorm
import Core.Nu

/-!
# Core — the code predicate and `unfold`'s codata at its own code  `[spec §68]`

`𝒱⟦Code⟨N; E⟩ C⟧`, stated over existing definitions: the value is the code `N` closed by a list
of captured values whose tuple is in `𝒱⟦E⟧` at the value's whole resource (`codeP`), and it is
in `𝒱⟦U C⟧` (`codeRelC`).

`unfold step s` is `etaN C g s`, the code `etaCode C` closed by `[g, s]` (`etaN_code`), at the
environment type `!G ⊗ (S ⊗ 1)` (`etaEnv`). `nuOutK`'s step:

* `etaN_codeRel`: `etaN C g s` with `g ∈ 𝒱⟦!G⟧`, `s ∈ 𝒱⟦S⟧` is in the code predicate;
* `codeRel_etaN`: conversely, a value in the code predicate is `etaN C g s` with such `g`, `s`;
* `nuOutK_step`: such a value is in one unfolding of `νX. C` with every rest read in the code
  predicate at the same code (`codeCand`): `candN_post`, then `nuF_mono` along `candN ⊆ codeCand`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The code predicate -/

/-- A capture list as one value: right-nested pairs ending in `()`.  `[spec §68]` -/
def tupleV : List Val → Val
  | []      => .unit
  | u :: us => .pair u (tupleV us)

/-- **The code conjunct** of `𝒱⟦Code⟨N; E⟩ C⟧`: `v` is `N` closed by captured values `us` whose
tuple is in `𝒱⟦E⟧` at the whole resource.  `[spec §68]` -/
def codeP (N : Expr) (E : VTy) (ls : List SRec) (δ : LSub) (v : Val) : WProp := fun ρ =>
  ∃ us : List Val, v.1 = Expr.psub 0 us N ∧ vC true E ls δ (tupleV us) ρ

/-- **`𝒱⟦Code⟨N; E⟩ C⟧`** in the program's mode: the code conjunct and `𝒱⟦U C⟧`.
`[spec §68]` -/
def codeRelC (N : Expr) (E : VTy) (C : CTy) (ls : List SRec) (δ : LSub) (v : Val) : WProp :=
  fun ρ => codeP N E ls δ v ρ ∧ vC true (.thunk C) ls δ v ρ

/-- The code predicate is below `𝒱⟦U C⟧` (`erase`'s semantic content). -/
theorem codeRelC_thunk {N : Expr} {E : VTy} {C : CTy} {ls : List SRec} {δ : LSub} {v : Val}
    {ρ : WRes} (h : codeRelC N E C ls δ v ρ) : vC true (.thunk C) ls δ v ρ := h.2

/-! ### `unfold`'s codata as a code -/

/-- A term closed at `k` has no free variable under `k` binders. -/
theorem occs_eq_nil_of_closedAt : ∀ (e : Expr) (k : Nat), closedAt k e = true → Expr.occs k e = []
  | .var i, k, h => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp [Expr.occs, h]
  | .unit, _, _ => rfl
  | .pair a b, k, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp [Expr.occs, occs_eq_nil_of_closedAt a k h.1, occs_eq_nil_of_closedAt b k h.2]
  | .inj₁ a, k, h => occs_eq_nil_of_closedAt a k h
  | .inj₂ a, k, h => occs_eq_nil_of_closedAt a k h
  | .lam b, k, h => occs_eq_nil_of_closedAt b (k + 1) h
  | .loc _, _, _ => rfl
  | .prim _, _, _ => rfl
  | .seq a b, k, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp [Expr.occs, occs_eq_nil_of_closedAt a k h.1, occs_eq_nil_of_closedAt b k h.2]
  | .letpair a b, k, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp [Expr.occs, occs_eq_nil_of_closedAt a k h.1, occs_eq_nil_of_closedAt b (k + 2) h.2]
  | .case a b₁ b₂, k, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp [Expr.occs, occs_eq_nil_of_closedAt a k h.1.1,
        occs_eq_nil_of_closedAt b₁ (k + 1) h.1.2, occs_eq_nil_of_closedAt b₂ (k + 1) h.2]
  | .app f a, k, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp [Expr.occs, occs_eq_nil_of_closedAt f k h.1, occs_eq_nil_of_closedAt a k h.2]

/-- **A term closed at `m` has its free variables below `m`**, the hypothesis of
`Expr.psub_capNorm` at a typed term (`closedAt_of_derives`).  `[spec §68]` -/
theorem occs_lt_of_closedAt :
    ∀ (e : Expr) (m k : Nat), closedAt (m + k) e = true → ∀ i ∈ Expr.occs k e, i < m
  | .var i, m, k, h, j, hj => by
      simp only [closedAt, decide_eq_true_eq] at h
      by_cases hi : i < k
      · simp [Expr.occs, hi] at hj
      · simp only [Expr.occs, if_neg hi, List.mem_singleton] at hj
        omega
  | .unit, _, _, _, _, hj => by simp [Expr.occs] at hj
  | .loc _, _, _, _, _, hj => by simp [Expr.occs] at hj
  | .prim _, _, _, _, _, hj => by simp [Expr.occs] at hj
  | .inj₁ a, m, k, h, j, hj => occs_lt_of_closedAt a m k h j hj
  | .inj₂ a, m, k, h, j, hj => occs_lt_of_closedAt a m k h j hj
  | .lam b, m, k, h, j, hj => occs_lt_of_closedAt b m (k + 1) h j hj
  | .pair a b, m, k, h, j, hj | .seq a b, m, k, h, j, hj | .app a b, m, k, h, j, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.occs, List.mem_append] at hj
      rcases hj with hj | hj
      · exact occs_lt_of_closedAt a m k h.1 j hj
      · exact occs_lt_of_closedAt b m k h.2 j hj
  | .letpair a b, m, k, h, j, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.occs, List.mem_append] at hj
      rcases hj with hj | hj
      · exact occs_lt_of_closedAt a m k h.1 j hj
      · exact occs_lt_of_closedAt b m (k + 2) h.2 j hj
  | .case a b₁ b₂, m, k, h, j, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.occs, List.mem_append] at hj
      rcases hj with (hj | hj) | hj
      · exact occs_lt_of_closedAt a m k h.1.1 j hj
      · exact occs_lt_of_closedAt b₁ m (k + 1) h.1.2 j hj
      · exact occs_lt_of_closedAt b₂ m (k + 1) h.2 j hj

/-- **The code of `unfold step s`**: `λo. self x₀ x₁ o`, the step `x₀` and the state `x₁`
captured.  `[spec §68]` -/
def etaCode (C : CTy) : Expr :=
  .lam (.app (.app (.app (.val (selfNu C)) (.var 1)) (.var 2)) (.var 0))

/-- The environment type of `etaCode`: the step at `!G`, then the state.  `[spec §68]` -/
abbrev etaEnv (G S : VTy) : VTy := .tensor (.bang G) (.tensor S .unit)

theorem etaCode_occs (C : CTy) : Expr.occs 0 (etaCode C) = [0, 1] := by
  simp [etaCode, Expr.occs, occs_eq_nil_of_closedAt _ 1
    (closedAt_mono _ (selfNu_closed C) (Nat.zero_le 1))]

/-- `etaCode C` is its own code: its captures are `0, 1` in order.  `[spec §68]` -/
theorem etaCode_capNorm (C : CTy) : Expr.capNorm (etaCode C) = etaCode C := by
  refine Expr.ren_eq_self _ _ 0 (fun i hi => ?_)
  rw [etaCode_occs] at hi
  simp only [Expr.capIdx, Expr.capVars, etaCode_occs]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

/-- **`unfold step s` is its code closed by `[g, s]`.**  `[spec §68]` -/
theorem etaN_code (C : CTy) (g s : Val) :
    (etaN C g s).1 = Expr.psub 0 [g, s] (etaCode C) := by
  simp [etaN, etaCode, Expr.psub, Val.lam,
    psub_closedAt _ _ (selfNu_closed C) (Nat.zero_le 1)]

/-- `!G` at the step, at every list. -/
theorem bang_step_of {G S : VTy} {C : CTy} {δ : LSub} {g : Val}
    (hG : ∀ ls v ρ, vC true G ls δ v ρ → vC true (.thunk (.arr S (C.instT S))) ls δ v ρ)
    (hg : ∀ ls, vC true (.bang G) ls δ g PMap.empty) :
    ∀ ls, vC true (.bang (.thunk (.arr S (C.instT S)))) ls δ g PMap.empty :=
  fun ls => ⟨rfl, hG ls g _ (hg ls).2⟩

/-- **`unfold step s` is in the code predicate** at `etaCode C` and `!G ⊗ (S ⊗ 1)`, for a step
in `𝒱⟦!G⟧` at every list whose `G` erases to `U(S ⊸ C[S/X])`, and a state in `𝒱⟦S⟧`.
`[spec §68]` -/
theorem etaN_codeRel {C : CTy} (hC : C.NuOk) {G S : VTy}
    (hS : ∀ x, C.LeafBinds x → ¬ VFree x S) {δ : LSub} {g : Val}
    (hG : ∀ ls v ρ, vC true G ls δ v ρ → vC true (.thunk (.arr S (C.instT S))) ls δ v ρ)
    (hg : ∀ ls, vC true (.bang G) ls δ g PMap.empty)
    {ls : List SRec} {s : Val} {ρ : WRes} (hs : vC true S ls δ s ρ) :
    codeRelC (etaCode C) (etaEnv G S) (.nu C) ls δ (etaN C g s) ρ := by
  refine ⟨⟨[g, s], etaN_code C g s, ?_⟩, ?_⟩
  · refine ⟨g, tupleV [s], PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, rfl⟩,
      PMap.empty, ρ, compS_empty_left ρ, hg ls, ?_⟩
    exact ⟨s, .unit, PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, rfl⟩,
      ρ, PMap.empty, ResU.comp_empty_right ρ, hs, ⟨rfl, rfl⟩⟩
  · intro ls' hext _
    exact nuRel_coind (candN_post hC hS (bang_step_of hG hg)) ls' _ ρ
      ⟨s, rfl, vC_local true S hext hs⟩

theorem val_pair_inj {a b c d : Val} (h : Val.pair a b = Val.pair c d) : a = c ∧ b = d := by
  have h' := congrArg Subtype.val h
  simp only [Val.pair, Expr.pair.injEq] at h'
  exact ⟨Val.ext h'.1, Val.ext h'.2⟩

theorem val_pair_ne_unit {a b : Val} : Val.pair a b ≠ Val.unit := fun h => by
  have h' := congrArg Subtype.val h
  simp [Val.pair, Val.unit] at h'

/-- A capture list whose tuple is `(g, (s, ()))` is `[g, s]`. -/
theorem tupleV_two {us : List Val} {g s : Val}
    (h : tupleV us = Val.pair g (Val.pair s Val.unit)) : us = [g, s] := by
  match us, h with
  | [], h => exact absurd h.symm val_pair_ne_unit
  | [a], h =>
      exact absurd (val_pair_inj h).2.symm val_pair_ne_unit
  | [a, b], h =>
      obtain ⟨rfl, h₂⟩ := val_pair_inj h
      obtain ⟨rfl, -⟩ := val_pair_inj h₂
      rfl
  | a :: b :: c :: rest, h =>
      obtain ⟨-, h₂⟩ := val_pair_inj h
      exact absurd (val_pair_inj h₂).2 val_pair_ne_unit

/-- `ρ ● ∅ = ρ'` is `ρ' = ρ`. -/
theorem eq_of_compS_empty_right' {ρ₁ ρ : WRes} (h : ResU.CompS ρ₁ PMap.empty ρ) : ρ = ρ₁ :=
  eq_of_compS_empty_left (ResU.CompS.comm h)

/-- **A value in the code predicate at `etaCode C` is `unfold step s`**, its step in `𝒱⟦!G⟧` at
every list and its state in `𝒱⟦S⟧` at the whole resource.  `[spec §68]` -/
theorem codeRel_etaN {C : CTy} {G S : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : codeRelC (etaCode C) (etaEnv G S) (.nu C) ls δ v ρ) :
    ∃ g s, v = etaN C g s ∧ (∀ ls', vC true (.bang G) ls' δ g PMap.empty) ∧
      vC true S ls δ s ρ := by
  obtain ⟨⟨us, hv, hE⟩, -⟩ := h
  obtain ⟨g, w, ρ₀, ρ₁, hc, ⟨rfl, hw⟩, ρg, ρw, hc', hg, hrest⟩ := hE
  obtain ⟨s, u, ρ₂, ρ₃, hc₂, ⟨rfl, hsu⟩, ρs, ρu, hc₃, hs, hu⟩ := hrest
  obtain ⟨rfl, hu⟩ := hu
  have hρ₁ : ρ = ρ₁ := eq_of_compS_empty_left hc
  have hρg : ρg = PMap.empty := hg.1
  subst hρg
  have hρw : ρ₁ = ρw := eq_of_compS_empty_left hc'
  have hρ₃ : ρw = ρ₃ := eq_of_compS_empty_left hc₂
  have hρs : ρ₃ = ρs := eq_of_compS_empty_right' hc₃
  subst hρ₁ hρw hρ₃ hρs
  subst hsu hu
  obtain rfl := tupleV_two hw
  exact ⟨g, s, Val.ext (by rw [hv, ← etaN_code]),
    fun ls' => vC_local true _ (ext_empty ls ls') hg, hs⟩

/-! ### `nuOutK`'s step -/

/-- The codata of the code `etaCode C` at `!G ⊗ (S ⊗ 1)`, as a candidate for `νX. C`: the rest
type `Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)` of `nuOutK`.  `[spec §68]` -/
def codeCand (C : CTy) (G S : VTy) (δ : LSub) : CPred := fun ls e ρ =>
  ∃ v, e = .val v ∧ codeRelC (etaCode C) (etaEnv G S) (.nu C) ls δ v ρ

/-- `unfold`'s candidate at a step in `𝒱⟦!G⟧` is inside the code's. -/
theorem candN_le_codeCand {C : CTy} (hC : C.NuOk) {G S : VTy}
    (hS : ∀ x, C.LeafBinds x → ¬ VFree x S) {δ : LSub} {g : Val}
    (hG : ∀ ls v ρ, vC true G ls δ v ρ → vC true (.thunk (.arr S (C.instT S))) ls δ v ρ)
    (hg : ∀ ls, vC true (.bang G) ls δ g PMap.empty) :
    (candN C g S δ).Le (codeCand C G S δ) := by
  rintro ls e ρ ⟨s, rfl, hs⟩
  exact ⟨etaN C g s, rfl, etaN_codeRel hC hS hG hg hs⟩

/-- **`nuOutK`'s step**: a value of `Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)` is in one unfolding of
`νX. C` with every rest at the same code type, when `G` erases to `U(S ⊸ C[S/X])`: the value is
`unfold step s` (`codeRel_etaN`), in `unfold`'s candidate, which is post-fixed (`candN_post`) and
inside the code's (`candN_le_codeCand`).  `[spec §68]` -/
theorem nuOutK_step {C : CTy} (hC : C.NuOk) {G S : VTy}
    (hS : ∀ x, C.LeafBinds x → ¬ VFree x S) {δ : LSub}
    (hG : ∀ ls v ρ, vC true G ls δ v ρ → vC true (.thunk (.arr S (C.instT S))) ls δ v ρ) :
    (codeCand C G S δ).Le (nuF C δ (codeCand C G S δ)) := by
  rintro ls e ρ ⟨v, rfl, hv⟩
  obtain ⟨g, s, rfl, hg, hs⟩ := codeRel_etaN hv
  exact nuF_mono hC.shape δ (candN_le_codeCand hC hS hG hg) ls _ ρ
    (candN_post hC hS (bang_step_of hG hg) ls _ ρ ⟨s, rfl, hs⟩)

end BoCa.Fig16.LogRel.Core

end
