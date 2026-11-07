import Core.Chain.SI.CaptureGen
import Core.Chain.SI.LoopN

/-!
# A scheduler at `cerwp`: bind, frame, divergence, adequacy

At the empty table nothing stops, so a scheduler's own code composes by `crwpG_bind` and
`crwpG_frame` without reinstalling continuations. `cerwp_frameBindE` is the shape the scheduler
uses for every task it runs: the task in the middle, the stored continuations and cells the
scheduler keeps as the frame (their records owned by the frame), the frame condition the task
asks met by the scheduler's frame and the resources it keeps, the rest of the scheduler after.

`cerwp_adequacy`: a closed program at the empty table, the empty frame (`ρ_f = ∅`), the empty
list and no records, whose result owns no records and holds only `imm` cells, is safe or
diverges, a value only at the empty memory, every `free` finding its cell. The result's `imm`
cells are gone by the typed world's coverage: with no records proper, `ag` of the world holds no
view.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Steps Head Kont freeE)

/-- Nothing stops at the empty table. -/
theorem opTableC_emptyC_false {F : WRes → Prop} {k : Nat} {ls : List SRec} {O : List FrameRec}
    {t : Expr} {Ψ : ContC} {ρ : WRes} (h : opTableC OpTabC.emptyC F k ls O t Ψ ρ) : False := by
  obtain ⟨_, _, _, _, _, h⟩ := h
  exact absurd (pure_sep_iff.mp h).1.2.2.1 (by simp [OpTabC.emptyC])

/-- **Bind at the empty table.** -/
theorem cerwp_bindE {Q Q₁ : PostCV} {F : WRes → Prop} (K : Kont) {n : Nat} {ls : List SRec}
    {O : List FrameRec} {e : Expr} {ρ : WRes}
    (h : cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q₁ F n ls O e ρ)
    (hK : ∀ k ls' O' (v : Val) ρ', k ≤ n → Q₁ k ls' O' v ρ' →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q F k ls' O' (K.plug v.1) ρ') :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q F n ls O (K.plug e) ρ := by
  have hL := opTableC_local OpTabC.emptyC
  rw [cerwp_eq] at h ⊢
  refine crwpG_bind K (crwpG_mono_le (fun k hk ls' O' t ρ' ht => ?_) h)
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · exact cerwp_unfold_at hL hk (hK k ls' O' v ρ' hk hv)
  · exact (opTableC_emptyC_false ht).elim

/-- **The frame at the empty table**: `ρ₂` and the records `O₂` kept beside the run, the run's
frame condition met by the outer frame with `ρ₂`. -/
theorem cerwp_frameE {Q₁ : PostCV} {F F₁ : WRes → Prop} (R : WRes → Prop) {n : Nat}
    {ls : List SRec} {O₁ O₂ : List FrameRec} (hO : ∀ p ∈ O₁, p ∉ O₂) {e : Expr}
    {ρ₁ ρ₂ ρ : WRes} (hcρ : ResU.CompS ρ₁ ρ₂ ρ)
    (hF : ∀ ρf y, F ρf → ResU.Hash ρf ρ → ResU.CompS ρf ρ₂ y → F₁ y)
    (h : cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q₁ F₁ n ls O₁ e ρ₁) (hR : R ρ₂) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (fun k ls' O' v ρ' => ∃ O₁', O' = O₁' ++ O₂ ∧
      (Q₁ k ls' O₁' v ⋆ R) ρ') F n ls (O₁ ++ O₂) e ρ := by
  have hL := opTableC_local OpTabC.emptyC
  rw [cerwp_eq] at h ⊢
  refine crwpG_mono_le (fun k hk ls' O' t ρ' ht => ?_)
    (crwpG_frame (fun _ => R) (fun _ _ _ h => h) hO hcρ hF h hR)
  obtain ⟨O₁', rfl, ρa, ρb, hc, ht, hRb⟩ := ht
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · exact Or.inl ⟨v, rfl, O₁', rfl, ρa, ρb, hc, hv, hRb⟩
  · exact (opTableC_emptyC_false ht).elim

/-- **A task run by a scheduler**: framed, then the rest of the scheduler. -/
theorem cerwp_frameBindE {Q Q₁ : PostCV} {F F₁ : WRes → Prop} (R : WRes → Prop) (K : Kont)
    {n : Nat} {ls : List SRec} {O₁ O₂ : List FrameRec} (hO : ∀ p ∈ O₁, p ∉ O₂) {e : Expr}
    {ρ₁ ρ₂ ρ : WRes} (hcρ : ResU.CompS ρ₁ ρ₂ ρ)
    (hF : ∀ ρf y, F ρf → ResU.Hash ρf ρ → ResU.CompS ρf ρ₂ y → F₁ y)
    (h : cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q₁ F₁ n ls O₁ e ρ₁) (hR : R ρ₂)
    (hK : ∀ k ls' O₁' (v : Val) ρa ρb ρ', k ≤ n → Q₁ k ls' O₁' v ρa → R ρb →
      ResU.CompS ρa ρb ρ' →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q F k ls' (O₁' ++ O₂) (K.plug v.1) ρ') :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q F n ls (O₁ ++ O₂) (K.plug e) ρ :=
  cerwp_bindE K (cerwp_frameE R hO hcρ hF h hR) (fun k ls' _ v ρ' hk ⟨O₁', hO', ρa, ρb, hc, hq, hr⟩ =>
    hO' ▸ hK k ls' O₁' v ρa ρb ρ' hk hq hr hc)

/-! ### Divergence -/

/-- `(λx. x x) (λx. x x)`. -/
def omegaV : Val := Val.lam (.app (.var 0) (.var 0))

def omegaE : Expr := .app (.val omegaV) (.val omegaV)

theorem omega_step (μ : Heap) : Step1Only (ℍ := ℍ) μ omegaE μ omegaE := by
  have h := step1Only_plug (ℍ := ℍ) (Head.beta μ (.app (.var 0) (.var 0)) omegaV) rfl .hole
  have e : Expr.subst 0 omegaV (.app (.var 0) (.var 0)) = omegaE := by
    simp [Expr.subst, omegaE, omegaV, Val.lam, Expr.val]
  rw [e] at h
  exact h

/-- **A term that runs forever is in every relation.** -/
theorem cerwp_omega {Tb : TableC} (hL : Tb.Local) {Q : PostCV} {F : WRes → Prop} :
    ∀ n ls O ρ, cerwp (ℍ := ℍ) Tb Q F n ls O omegaE ρ := by
  intro n
  induction n with
  | zero => exact fun _ _ _ => cerwp_zero
  | succ n ih => exact fun ls O ρ => cerwp_step hL (fun μ => omega_step μ) (ih ls O ρ)

/-! ### Adequacy -/

/-- Every cell is `imm`. -/
def AllImm (ρ : WRes) : Prop := ∀ m (ψ : CellU Loc Val), ρ.get m = some ψ → ψ.kind = Kind.imm

/-- **With no records proper, a typed world of `imm` cells is empty** (coverage). -/
theorem empty_of_allImm {W : WRes} {ps : List FrameRec} {ls : List SRec}
    (hT : TWNC W ps (rsOf ls)) (hps : ∀ p, p ∉ ps) (h : AllImm W) : W = PMap.empty := by
  have hTI := hT.inv
  have hv : ResU.Valid W := hT.valid
  obtain ⟨a, ha⟩ := agW_of_valid hv
  refine PMap.ext fun m => ?_
  rw [PMap.empty_get]
  cases e : W.get m with
  | none => rfl
  | some ψ =>
      exfalso
      obtain ⟨s, hs⟩ := lsOf_of_imm (h m ψ e)
      obtain ⟨ζ, t, eζ, ht, -⟩ := ag_ls_of_le ⟨PMap.empty, ResU.comp_empty_right W⟩ ha e hs
        s.join_mem
      have hcl : Class (rsOf ls) m ζ := hTI.2.2.2.2.2.2.2 a ha m ζ eζ (CellU.kind_of_lsOf ht)
      have hr : ∃ r, r ∈ rsOf ls := by
        rcases hcl with ⟨r, hr, -⟩ | ⟨r, hr, -⟩
        · exact ⟨r, hr⟩
        · exact ⟨r, hr⟩
      obtain ⟨r, hr⟩ := hr
      obtain ⟨p, hp, -⟩ := (hTI.2.2.2.2.2.2.1 r).mp hr
      exact hps p hp

/-- **Adequacy at `cerwp`.** -/
theorem cerwp_adequacy {Q : PostCV} {P₀ : Expr}
    (hQ : ∀ k ls O v ρ, Q k ls O v ρ → O = [] ∧ AllImm ρ)
    (hall : ∀ n, cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q (fun ρf => ρf = PMap.empty) n [] []
      P₀ (PMap.empty : WRes)) :
    OrDiverges (ℍ := ℍ) P₀ := by
  intro μ e hs
  obtain ⟨j, hrun⟩ := stepsN_of_steps hs
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  have hS : Split [] [] [] := ⟨fun p => by simp, fun p hp => by simp at hp⟩
  have hend : Final (ℍ := ℍ) μ e → ∃ v : Val, e = v.1 ∧ μ = fun _ => none := by
    intro hfin
    have h := hall (j + 1)
    rw [cerwp_eq] at h
    obtain ⟨ρ', fρ', ps', O', ls', -, h2, h3, h4, h5, -, h7⟩ :=
      h PMap.empty PMap.empty [] [] (fun _ => none) rfl Fig16.LogRel.hash_empty
        (ResU.comp_empty_right _) hS TWNC.empty htg Fig16.BoLo.lower_empty fd_empty j μ e
        (by omega) hrun hfin
    rcases h7 with ⟨v, rfl, hq⟩ | ht
    · obtain ⟨rfl, hall'⟩ := hQ _ _ _ _ _ hq
      obtain rfl : ρ' = fρ' := ResU.eq_of_comp_empty_left h2
      have hps : ∀ p, p ∉ ps' := fun p hp => by
        rcases (h4.1 p).mp hp with h | h <;> simp at h
      obtain rfl := empty_of_allImm h5 hps hall'
      exact ⟨v, rfl, ResU.Lower.functional h3 Fig16.BoLo.lower_empty⟩
    · exact (opTableC_emptyC_false ht).elim
  have hp : IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e' := by
    by_cases hst : ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e'
    · exact .inr hst
    · have hfin : Final (ℍ := ℍ) μ e := fun μ' e' h => hst ⟨μ', e', h⟩
      obtain ⟨v, rfl, -⟩ := hend hfin
      exact .inl v.2
  refine ⟨hp, fun hv => ?_, fun K ℓ he => ?_⟩
  · have hfin : Final (ℍ := ℍ) μ e := fun μ' e' h => BoLo.no_step_val (w := ⟨e, hv⟩) h
    obtain ⟨-, -, hμ⟩ := hend hfin
    exact hμ
  · subst he
    rcases hp with hv | ⟨μ', e', hst⟩
    · have := K.isVal_of_plug hv
      simp [freeE, Expr.val, Val.prim] at this
    · obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).1 hst
      exact ⟨u, hu⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
