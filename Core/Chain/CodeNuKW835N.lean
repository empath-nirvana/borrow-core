import Core.Chain.NuKW835N
import Core.CodeNu

/-!
# The code predicate at the chain's relation, and `nuOutK`'s step  `[spec §68]`

`Core/CodeNu.lean` at `vN`/`cN`, the relation `goal791N` reads. `𝒱⟦Code⟨N; E⟩ C⟧` is the code
conjunct (`codePN`: `v` is `N` closed by captured values whose tuple is in `𝒱⟦E⟧` at the same
world, index and resource) and `𝒱⟦U C⟧` (`codeRelN`); `vNE`'s clause at `VTy.code` is this
predicate (`vNE_code`).

* `etaN_codeRelN`, `codeRelN_etaN`: `unfold step s` is in the code predicate at `etaCode C` and
  `!G ⊗ (S ⊗ 1)`, and every value there is such a codata.
* `nuOutK_stepN`: the code's candidate (`codeCandN`) is below one unfolding of `νX. C` at itself:
  `candNN_post` at the value's index, then `cBN_mono` along `candNN ⊆ codeCandN`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The code conjunct** at the chain's relation.  `[spec §68]` -/
def codePN (N : Expr) (E : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes) : Prop :=
  ∃ us : List Val, v.1 = Expr.psub 0 us N ∧ vN (ℍ := ℍ) E δ Θ n (tupleV us) ρ

/-- **`𝒱⟦Code⟨N; E⟩ C⟧`** at the chain's relation: the code conjunct and `𝒱⟦U C⟧`.
`[spec §68]` -/
def codeRelN (N : Expr) (E : VTy) (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val)
    (ρ : WRes) : Prop :=
  codePN (ℍ := ℍ) N E δ Θ n v ρ ∧ vN (ℍ := ℍ) (.thunk C) δ Θ n v ρ

/-- **`vNE`'s clause at `Code⟨N; E⟩ C` is the code predicate** at the chain's relation, under
every environment.  `[spec §68]` -/
theorem vNE_code {η : Option (Nat → TEntN)} {N : Expr} {E : VTy} {C : CTy} {δ : LSub} {Θ : LocTy}
    {n : Nat} {v : Val} {ρ : WRes} :
    vNE (ℍ := ℍ) η (.code N E C) δ Θ n v ρ ↔ codeRelN (ℍ := ℍ) N E C δ Θ n v ρ := Iff.rfl

/-- `vOE` at `Code⟨N; E⟩ C` is `True`, as at `U C`.  `[spec §68]` -/
theorem vOE_code {η : Option (Nat → TEntN)} {N : Expr} {E : VTy} {C : CTy} {δ : LSub} {Θ : LocTy}
    {n : Nat} {v : Val} {ρ : WRes} : vOE (ℍ := ℍ) η (.code N E C) δ Θ n v ρ := trivial

/-- `!G` at the step, at every world. -/
theorem bang_step_ofN {G S : VTy} {C : CTy} {δ : LSub} {g : Val} {k : Nat}
    (hG : ∀ Θ k v ρ, vN (ℍ := ℍ) G δ Θ k v ρ →
      vN (ℍ := ℍ) (.thunk (.arr S (C.instT S))) δ Θ k v ρ)
    (hg : ∀ Θ : LocTy, vN (ℍ := ℍ) (.bang G) δ Θ k g PMap.empty) :
    ∀ Θ : LocTy, vN (ℍ := ℍ) (.bang (.thunk (.arr S (C.instT S)))) δ Θ k g PMap.empty :=
  fun Θ => ⟨rfl, hG Θ k g _ (hg Θ).2⟩

/-- **`unfold step s` is in the code predicate** at `etaCode C` and `!G ⊗ (S ⊗ 1)`, at the step's
index.  `[spec §68]` -/
theorem etaN_codeRelN {C : CTy} (hC : C.NuOk) {G S : VTy}
    (hS : ∀ x, C.LeafBinds x → ¬ VFree x S) {δ : LSub} {g : Val} {k : Nat}
    (hG : ∀ Θ k v ρ, vN (ℍ := ℍ) G δ Θ k v ρ →
      vN (ℍ := ℍ) (.thunk (.arr S (C.instT S))) δ Θ k v ρ)
    (hg : ∀ Θ : LocTy, vN (ℍ := ℍ) (.bang G) δ Θ k g PMap.empty)
    {Θ : LocTy} {s : Val} {ρ : WRes} (hs : vN (ℍ := ℍ) S δ Θ k s ρ) :
    codeRelN (ℍ := ℍ) (etaCode C) (etaEnv G S) (.nu C) δ Θ k (etaN C g s) ρ := by
  refine ⟨⟨[g, s], etaN_code C g s, g, tupleV [s], PMap.empty, ρ, rfl, compS_empty_left ρ,
    hg Θ, s, .unit, ρ, PMap.empty, rfl, ResU.comp_empty_right ρ, hs, rfl, rfl⟩, ?_⟩
  intro Θ' hE hΘ' c hc ls
  exact cN_nu_coind (candNN_post hC hS (bang_step_ofN hG hg)) Θ' c k ls _ ρ
    ⟨le_rfl, hΘ', hc, s, rfl, vN_extR S δ k s ρ hE hs⟩

/-- **A value in the code predicate at `etaCode C` is `unfold step s`.**  `[spec §68]` -/
theorem codeRelN_etaN {C : CTy} {G S : VTy} {δ : LSub} {Θ : LocTy} {k : Nat} {v : Val}
    {ρ : WRes} (h : codeRelN (ℍ := ℍ) (etaCode C) (etaEnv G S) (.nu C) δ Θ k v ρ) :
    ∃ g s, v = etaN C g s ∧ (∀ Θ' : LocTy, vN (ℍ := ℍ) (.bang G) δ Θ' k g PMap.empty) ∧
      vN (ℍ := ℍ) S δ Θ k s ρ := by
  obtain ⟨⟨us, hv, hE⟩, -⟩ := h
  obtain ⟨g, w, ρg, ρw, hw, hc, hg, s, u, ρs, ρu, hsu, hc', hs, hu, hρu⟩ := hE
  subst hsu hu hρu
  have hρg : ρg = PMap.empty := hg.1
  subst hρg
  obtain rfl := eq_of_compS_empty_left hc
  obtain rfl := eq_of_compS_empty_right' hc'
  obtain rfl := tupleV_two hw
  exact ⟨g, s, Val.ext (by rw [hv, ← etaN_code]),
    fun Θ' => vN_extR _ δ k g _ (LocTy.extR_empty Θ Θ') hg, hs⟩

/-- The codata of the code `etaCode C` at `!G ⊗ (S ⊗ 1)`, as a candidate for `νX. C` at the
chain's signature: the rest type of `nuOutK`, at the worlds `thunkRN` reads it at.
`[spec §68]` -/
def codeCandN (C : CTy) (G S : VTy) (δ : LSub) : CandN := fun Θ c n _ e ρ =>
  Θ.OK ∧ ConsistentX c ρ ∧
    ∃ v : Val, e = v.1 ∧ codeRelN (ℍ := ℍ) (etaCode C) (etaEnv G S) (.nu C) δ Θ n v ρ

/-- `unfold`'s candidate at a step in `𝒱⟦!G⟧` is inside the code's. -/
theorem candNN_le_codeCandN {C : CTy} (hC : C.NuOk) {G S : VTy}
    (hS : ∀ x, C.LeafBinds x → ¬ VFree x S) {δ : LSub} {g : Val} {kg : Nat}
    (hG : ∀ Θ k v ρ, vN (ℍ := ℍ) G δ Θ k v ρ →
      vN (ℍ := ℍ) (.thunk (.arr S (C.instT S))) δ Θ k v ρ)
    (hg : ∀ Θ : LocTy, vN (ℍ := ℍ) (.bang G) δ Θ kg g PMap.empty) :
    (candNN (ℍ := ℍ) C g S δ kg).LeOK (codeCandN (ℍ := ℍ) C G S δ) := by
  rintro Θ - c j ls e ρ ⟨hj, hΘ, hc, s, rfl, hs⟩
  exact ⟨hΘ, hc, etaN C g s, rfl,
    etaN_codeRelN hC hS hG (fun Θ' => vN_le hj (hg Θ')) hs⟩

/-- **`nuOutK`'s step at the chain's relation**: the code's candidate is below one unfolding of
`νX. C` at itself, so each rest of a value of `Code⟨etaCode C; !G ⊗ (S ⊗ 1)⟩ (νX. C)` is again
one.  `[spec §68]` -/
theorem nuOutK_stepN {C : CTy} (hC : C.NuOk) {G S : VTy}
    (hS : ∀ x, C.LeafBinds x → ¬ VFree x S) {δ : LSub}
    (hG : ∀ Θ k v ρ, vN (ℍ := ℍ) G δ Θ k v ρ →
      vN (ℍ := ℍ) (.thunk (.arr S (C.instT S))) δ Θ k v ρ) :
    (codeCandN (ℍ := ℍ) C G S δ).Le
      (cBN (ℍ := ℍ) (.thunk (.nu C)) (codeCandN (ℍ := ℍ) C G S δ) C δ) := by
  rintro Θ c n ls e ρ ⟨hΘ, hc, v, rfl, hv⟩
  obtain ⟨g, s, rfl, hg, hs⟩ := codeRelN_etaN hv
  exact cBN_mono (candNN_le_codeCandN hC hS hG hg) hC.shape.nuLeaf δ Θ c n ls _ ρ
    (candNN_post hC hS (bang_step_ofN hG hg) Θ c n ls _ ρ ⟨le_rfl, hΘ, hc, s, rfl, hs⟩)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
