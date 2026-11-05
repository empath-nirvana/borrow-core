import Core.Chain.SI.StopFrameN
import Core.Chain.SI.Loop
import Core.Chain.SI.Adequacy

/-!
# The unbounded loop and adequacy at `erwp`

`erwp_iterate` is `ewp_iterate` (`SI/Loop.lean`) over Core's worlds: each turn ends in a tick, a
stop, so the next turn is owed only below the index the tick is at, and the loop is in `erwp` at
every index by induction on the index. Here the tick's answer is always *next*: a loop the
runtime never closes.

`erwp_adequacy` is stage 1's `adequacy` (LinearActris Theorem 5.4's shape) for `erwp`: a closed
program at the empty table, the empty world and the empty list, at every index, at a
postcondition that owns nothing, is `OrDiverges`: every configuration a run reaches is a value or
steps, a value is reached only at the empty memory (`reclaimN`, `Fundamental.reclaim` at the
index), and every `free` finds its cell.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload freeE)

/-! ### Bind up to an index, and a step the index pays for -/

/-- `erwp_bind` with the continuation known only up to the index `N`. -/
theorem erwp_bind_le {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} {Q Q' : PostN} (K : Kont)
    (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false) (hK : T.CtxClosed K)
    (N : Nat) (hcont : ∀ k ls (v : Val) ρ, k ≤ N → Q' k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (K.plug v.1) ρ) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q' n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug e) ρ := by
  have hL := opTableN_local T
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN ls e ρ h
  rw [erwp_eq]
  refine rwpG_bind hΦ K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ht | ht
  · exact erwp_unfold_at hL hk (hcont k ls' v σ (by omega) hv)
  · obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont'⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).HasHnd m = false := by simp [hasHnd_comp, hH, hK₁]
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' P hP => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      have hc := (hcont' ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) (by omega) _ _ _ hc
    · exact hK m i en P hT hP _ _ _ _ _ ((hcont' ls'' he).2 hq' P hP)
  · obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, hrest⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).Catches m = false := by simp [catches_comp, hC, hK₁]
    have ht' : K.plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE true (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ hrest⟩))

/-- **A step the index pays for**: a configuration's only step, keeping the memory. -/
theorem erwp_step {Φ : LocFam} {Tb : TableN} (hL : Tb.Local) {Q : PostN} {n : Nat}
    {ls : List SRec} {e e' : Expr} {ρ : WRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : erwp (ℍ := ℍ) Φ Tb Q n ls e' ρ) : erwp (ℍ := ℍ) Φ Tb Q (n + 1) ls e ρ :=
  erwp_fold_at hL le_rfl (rwpG_step hdet (erwp_unfold_at hL (Nat.le_succ n) h))

/-! ### The loop -/

/-- The turn's postcondition at the index: done at `inl x`, in `Q_L`, or going on at `inr s′`,
in the invariant. -/
def turnPostN (I : Val → WProp) (QL : PostN) : PostN := fun k ls v ρ =>
  (∃ x, v = Val.inj₁ x ∧ QL k ls (Val.inj₁ x) ρ) ∨ (∃ s', v = Val.inj₂ s' ∧ I s' ρ)

/-- A table with no cancel obligation is closed under every context. -/
theorem OpTabN.ctxClosed_of_fin {T : OpTabN} (h : ∀ m i en, T m i = some en → en.fin = none)
    (K : Kont) : T.CtxClosed K := by
  intro m i en P hT hP
  rw [h m i en hT] at hP
  cases hP

/-- **The loop rule at `erwp`**, for a tick the runtime always answers *next*. -/
theorem erwp_iterate {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down)
    {f : Val} (hK : T.CtxClosed (iterK f)) {QL : PostN} (hQL : QL.Down)
    (hf : closedAt 0 f.1 = true) {I : Val → WProp} {en : OpEntN}
    (htick : T divEff 0 = some en) (hab : en.abort = false) (hq : en.q = .lin)
    (hta : ∀ k ls, en.PA k ls Val.unit PMap.empty)
    (htb : ∀ k ls w (ρ : WRes), en.PB k ls w ρ → w = nextV ∧ ρ = PMap.empty)
    (hIc : ∀ s ρ, I s ρ → closedAt 0 s.1 = true)
    (hturn : ∀ k s ls ρ, I s ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) (turnPostN I QL) k ls
        (.app (.app (.val f) (.val s)) (.val nextV)) ρ) :
    ∀ n s ls ρ, I s ρ → erwp (ℍ := ℍ) Φ (opTableN T) QL n ls (iterateE f s) ρ := by
  have hD := opTableN_down hTD
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s ls ρ hI
  refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.iterate μ f s) rfl .hole) ?_
  simp only [Kont.plug_hole]
  rw [iterNext_eq]
  refine erwp_bind_le hΦ (iterK f) (fun m => by simp [iterK, Kont.HasHnd])
    (fun m => by simp [iterK, Kont.Catches]) hK n ?_ n le_rfl
    ls _ ρ (hturn n s ls ρ hI)
  rintro k ls' v σ hk (⟨x, rfl, hx⟩ | ⟨s', rfl, hs'⟩)
  · refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.case₁ μ x _ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₁ x) hx
  · refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.case₂ μ s' _ _) rfl .hole) ?_
    simp only [Kont.plug_hole]
    rw [iterK_case₂]
    refine erwp_perform _ (by simp [Kont.HasHnd]) htick hab hq (compS_empty_left σ) (hta k ls')
      (fun ls'' _ k' hk' w σB XB hB hXB => ?_)
    obtain ⟨rfl, rfl⟩ := htb k' ls'' w σB hB
    obtain rfl : XB = σ := ResU.CompS.functional hXB (ResU.comp_empty_right σ)
    refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
    simp only [Kont.plug_hole]
    rw [iterTurn_subst hf (hIc s' XB hs')]
    refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
    simp only [Kont.plug_hole, Expr.subst, subst_closedAt _ _ hf (Nat.zero_le _),
      subst_closedAt _ _ (hIc s' XB hs') (Nat.zero_le _)]
    exact ih k' (by omega) s' ls'' XB hs'

/-! ### Adequacy -/

/-- `∅ ↭ₖ ρ⁺` and `ρ⁺|own = ∅` force `ρ⁺ = ∅` (`Fundamental.reclaim` at the index). -/
theorem reclaimN {Φ : LocFam} {k : Nat} (ρ : WRes) (hupd : UpdVN Φ k PMap.empty ρ)
    (hno : NoOwn ρ) : ρ = PMap.empty := by
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  cases hg : ρ.get l with
  | none => rfl
  | some ψ =>
      exfalso
      obtain ⟨σ, hσ⟩ := hupd.2.2
      obtain ⟨χ, hχ, hk, -, -⟩ := ResU.Flat.get hσ hg
      have hfa : ρ.FlatAt l χ := (ResU.flatAt_iff hσ l χ).mpr hχ
      rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
      · have hko : ψ.kind = Kind.own := by rw [← hk]; exact CellU.kind_ownOf w
        have hr : (ρ.restrict Kind.own).get l = some ψ :=
          ResU.restrict_eq_some.mpr ⟨hg, hko⟩
        rw [hno, PMap.empty_get] at hr
        simp at hr
      · have hemp := (hupd.1.1 l s w ξ hξ).mpr hfa
        rw [ResU.flatAt_iff Fig16.BoLo.flat_empty, PMap.empty_get] at hemp
        simp at hemp
      · obtain ⟨ψ₀, hfa₀, -⟩ := hupd.1.2.2 l _ hfa (CellU.kind_mutOf _ _ _ _ _ _)
        rw [ResU.flatAt_iff Fig16.BoLo.flat_empty, PMap.empty_get] at hfa₀
        simp at hfa₀

/-- A run counted. -/
theorem stepsN_of_steps {μ μ' : Heap} {e e' : Expr} (h : BoCa.BoLo.Steps (ℍ := ℍ) μ e μ' e') :
    ∃ j, StepsN (ℍ := ℍ) j μ e μ' e' := by
  induction h with
  | refl => exact ⟨0, .refl _ _⟩
  | more h₁ _ ih =>
      obtain ⟨j, hj⟩ := ih
      exact ⟨j + 1, .more h₁ hj⟩

/-- **Adequacy at `erwp`**: safe or divergent, with every value at the empty memory and every
`free` finding its cell. -/
theorem erwp_adequacy {Φ : LocFam} {Q : PostN} {P₀ : Expr}
    (hQ : ∀ k ls v (ρ : WRes), Q k ls v ρ → ρ = PMap.empty)
    (hall : ∀ n, erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n [] P₀ (PMap.empty : WRes)) :
    OrDiverges (ℍ := ℍ) P₀ := by
  intro μ e hs
  obtain ⟨j, hrun⟩ := stepsN_of_steps hs
  have hp := erwp_safe (Φ := Φ) hall hrun
  refine ⟨hp, fun hv => ?_, fun K ℓ he => ?_⟩
  · have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
    have h := erwp_unfold_at (opTableN_local _) le_rfl (hall (j + 1))
    have hE := h PMap.empty PMap.empty [] (fun _ => none) Fig16.LogRel.hash_empty
        (ResU.comp_empty_right _) TWNC.empty htg Fig16.BoLo.lower_empty fd_empty j μ e
        (by omega) hrun (final_val μ ⟨e, hv⟩)
    obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h1, h2, h3, h6, h7, h9, h10, h11, hT', htg', hps,
      hls, hq⟩ := hE
    rcases hq with ⟨v, -, hqv⟩ | ⟨_, _, _, _, _, h'⟩ | ⟨_, _, _, _, _, h'⟩
    · obtain rfl := hQ _ _ _ _ hqv
      obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
      obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
      obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
      obtain rfl : ρp = PMap.empty := reclaimN ρp h10 h11
      exact ResU.Lower.functional h7 Fig16.BoLo.lower_empty
    · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])
    · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])
  · subst he
    rcases hp with hv | ⟨μ', e', hst⟩
    · have := K.isVal_of_plug hv
      simp [freeE, Expr.val, Val.prim] at this
    · obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).1 hst
      exact ⟨u, hu⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
