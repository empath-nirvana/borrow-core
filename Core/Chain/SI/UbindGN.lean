import Core.Chain.SI.LendCancelProg

/-!
# The finaliser frame at `erwp`: `[then]`, `[finalise]`, `[finalise-cancel]`, `[cfin-ret]`

`ewp_ubind` (`SI/Fin.lean`) over Core's worlds: `ubind (N, D) M` owning `M`'s resource and the
finaliser's `ρ_D`. The frame's resource rides along every run of `M` (`rwpG_frame` with the
frame `· = ρ_D`), into the continuation's share at a stop. At a return `[then]` runs `N`; at an
ordinary `raise` `[finalise]` runs `D (); raise p`; on a cancel `[finalise-cancel]` runs
`cfin s (D ())`, and `[cfin-ret]` re-raises. A stop passes the frame, which is put back into its
continuation; its cancel obligation is read through the frame (`cancelOblN_ubind`: the cancel run
of `ubind (N, D) K†` owning `ρ_D` more is the cancel run of `K†` followed by `D`).

Narrowings: the finaliser neither stops nor raises (`rwp`), as `[let-closeFin]`'s `¬ Σ_D.Cancels`;
finalisers that perform operations (stage 1's `close`) are not covered here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE cfinE)

/-- The finaliser's run: `D ()` releases `ρ_D`, returning `()` and owning nothing. -/
def FinOK (Φ : LocFam) (D : Val) (ρD : WRes) : Prop :=
  ∀ k ls, rwp (ℍ := ℍ) Φ (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
    (.app (.val D) (.val .unit)) ρD

theorem OpTabN.Down.pa_le {T : OpTabN} (hT : T.Down) {n i : UInt32} {en : OpEntN}
    (h : T n i = some en) {m k : Nat} (hmk : m ≤ k) {ls : List SRec} {v : Val} {ρ : WRes}
    (hk : en.PA k ls v ρ) : en.PA m ls v ρ := by
  induction hmk with
  | refl => exact hk
  | step _ ih => exact ih (hT.pa _ _ _ h _ _ _ _ hk)

/-- **A cancel run under a finaliser frame owning `ρ_D`**: still a cancel run (`cancelObl_ubind`
at `erwp`). -/
theorem cancelOblN_ubind {Φ : LocFam} (hΦ : Φ.Down) {T₁ : OpTabN} (hT₁ : T₁.Down)
    (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin) (N D : Val) {ρD : WRes}
    (hD : FinOK (ℍ := ℍ) Φ D ρD) :
    ∀ n ls x ρ X, ResU.CompS ρ ρD X → cancelOblN (ℍ := ℍ) Φ T₁ n ls x ρ →
      cancelOblN (ℍ := ℍ) Φ T₁ n ls ((ubK N D).plug x) X := by
  have hL := cancelTabN_local T₁
  have hPD := erwpPost_down (cancelTabN_down hT₁) falsePost_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls x ρ X hX h
  show erwp (ℍ := ℍ) Φ _ _ _ _ _ _
  rw [erwp_eq]
  refine rwpG_bind hΦ (ubK N D) ?_
  have hfr := rwpG_frame (fun _ τ => τ = ρD) (fun _ _ _ _ h => h) hX
    (erwp_unfold_at hL le_rfl h) rfl
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hσ, ht, hσ₂⟩ => ?_) hfr
  rw [hσ₂] at hσ
  rcases ht with ⟨_, _, hf⟩ | ⟨K', err, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact hf.elim
  · obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, herr, hnb⟩ := pure_sep_iff.mp hp
    cases err with
    | some E =>
        obtain ⟨m, j, w, en, he⟩ := herr
        obtain ⟨⟨-, hTe, ha⟩, -⟩ := pure_sep_iff.mp he
        exact absurd ha (by rw [(hT₁e _ _ en hTe).1]; simp)
    | none =>
    obtain rfl : τa = PMap.empty := herr.1
    obtain rfl := eq_of_compS_empty_left hcab
    refine rwpG_det hΦ (hPD _)
      (fun μ => step1Only_plug (Head.ufinC μ N D none K' hK') rfl .hole) ?_
    rw [Kont.plug_hole, ← cfK_plug]
    refine rwpG_bind hΦ (cfK _) ?_
    have hDr := rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) (ResU.CompS.comm hσ)
      (rwp_iff_rwpG.mp (hD k ls')) hnb
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ, ⟨w, rfl, -, rfl⟩, hnσb⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ
    refine rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.cfret μ none w) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (cancelVal none))) :=
      final_opPlug (payloadName_cancelVal none) (by simp [OpFree, Kont.Catches])
    exact rwpG_here hfin (Or.inr (Or.inl ⟨.hole, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, σ₂, compS_empty_left _, emp_empty, hnσb⟩⟩))
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hq := (hT₁e _ _ en hT).2
    obtain ⟨ρkD, hkD, haX⟩ := (ResU.CompS.assoc ρa ρk ρD σ).mpr ⟨σ₁, hcak, hσ⟩
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρkD, haX, hA, fun hu' => absurd (hq.symm.trans hu') (by simp),
          fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
            fun hq' => absurd hq hq'⟩⟩⟩))
    have he' : en.wc ls' ls'' ρk := hT₁.wcl _ _ _ hT _ _ _ _ _ hkD he
    obtain ⟨y, hy, hyτ⟩ := compS_exch hkD hcτ
    have hc := (hcont ls'' he').1 k' hk' w τ₁ y hB hy
    simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
    rw [Kont.plug_comp]
    exact ih k' (by omega) _ _ _ _ hyτ hc

/-- **The finaliser frame at `erwp`.** -/
theorem erwp_ubind {Φ : LocFam} (hΦ : Φ.Down) {Tin Tout : OpTabN} (hToutD : Tout.Down)
    (hTinD : Tin.Down) {Qin Qout : PostN} (hQout : Qout.Down) (N D : Val) {ρD : WRes}
    (hD : FinOK (ℍ := ℍ) Φ D ρD)
    (hN : ∀ k ls (v : Val) ρ X, ResU.CompS ρ ρD X → Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val N) (.val v)) X)
    (hperf : ∀ m i en, Tin m i = some en → en.abort = false → ∃ en', Tout m i = some en' ∧
      en'.q = en.q ∧ en'.abort = false ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      ∀ k ls K ρk X, ResU.CompS ρk ρD X → cancelOKN en k ls K ρk →
        cancelOKN en' k ls ((ubK N D).comp K) X)
    (hunr : ∀ m i en, Tin m i = some en → en.q ≠ .unr)
    (hrais : ∀ m i en, Tin m i = some en → en.abort = true → m ≠ 0 ∧ ∃ en', Tout m i = some en' ∧
      en'.abort = true ∧ (∀ k ls v ρ, en.PA k ls v ρ → en'.PA k ls v ρ) ∧
      ∀ k ls ls' v ρ, (∀ x, x ∈ ls' ↔ x ∈ ls) → en'.PA k ls v ρ → en'.PA k ls' v ρ) :
    ∀ n ls M ρ X, ResU.CompS ρ ρD X → erwp (ℍ := ℍ) Φ (opTableN Tin) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (ubindE (.pair N D) M) X := by
  have hL := opTableN_local Tin
  have hPD := erwpPost_down (opTableN_down hToutD) hQout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls M ρ X hX h
  rw [← ubK_plug, erwp_eq]
  refine rwpG_bind hΦ (ubK N D) ?_
  have hfr := rwpG_frame (fun _ τ => τ = ρD) (fun _ _ _ _ h => h) hX
    (erwp_unfold_at hL le_rfl h) rfl
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hσ, ht, hσ₂⟩ => ?_) hfr
  rw [hσ₂] at hσ
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[then]`
    have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det hΦ (hPD _) hstep
      (erwp_unfold_at (opTableN_local Tout) hk (hN k ls' v σ₁ σ hσ hv))
  · -- a stop passes the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hT', hq', ha', hPA', hPB', hwc', hcan⟩ := hperf m i en hT ha
    obtain ⟨ρkD, hkD, haX⟩ := (ResU.CompS.assoc ρa ρk ρD σ).mpr ⟨σ₁, hcak, hσ⟩
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT', ha'⟩
        ⟨ρa, ρkD, haX, hPA' ▸ hA,
          fun hu' => absurd (hq'.symm.trans hu') (hunr m i en hT),
          fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq'' => ?_⟩⟩⟩))
    · have he' : en.wc ls' ls'' ρk := by
        rw [hwc'] at he; exact hTinD.wcl _ _ _ hT _ _ _ _ _ hkD he
      rw [hPB'] at hB
      obtain ⟨y, hy, hyτ⟩ := compS_exch hkD hcτ
      have hc := (hcont ls'' he').1 k' hk' w τ₁ y hB hy
      simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) _ _ _ _ hyτ hc
    · have he' : en.wc ls' ls'' ρk := by
        rw [hwc'] at he; exact hTinD.wcl _ _ _ hT _ _ _ _ _ hkD he
      exact hcan k ls'' K₁ ρk ρkD hkD ((hcont ls'' he').2 (hq' ▸ hq''))
  · -- `[finalise]`: `D (); raise p`
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨hm0, en', hT', ha', hPA', hPAls⟩ := hrais m i en hT ha
    refine rwpG_det hΦ (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    refine rwpG_bind hΦ _ ?_
    have hDr := rwpG_frame
      (fun ls₀ τ => (∀ x, x ∈ ls₀ ↔ x ∈ ls') ∧
        ((fun ρ => en.PA k ls' v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ)
      (fun _ _ hs _ ⟨h₁, h₂⟩ => ⟨fun x => (hs x).trans (h₁ x), h₂⟩) (ResU.CompS.comm hσ)
      (rwp_iff_rwpG.mp (hD k ls')) ⟨fun _ => Iff.rfl, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ, ⟨w, rfl, rfl, rfl⟩, hls₂, ⟨τa, τn, hcτ, ⟨hPAτ, hnτ⟩, hnn'⟩⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ
    refine rwpG_det hΦ (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).2.2) ?_
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload m i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, m, i, v, en',
        pure_sep_mk ⟨rfl, rfl, hT', ha'⟩ ⟨τa, τn, hcτ, ⟨hToutD.pa_le hT' hk₂
          (hPAls _ _ _ _ _ hls₂ (hPA' _ _ _ _ hPAτ)), hnτ⟩, hnn'⟩⟩))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
