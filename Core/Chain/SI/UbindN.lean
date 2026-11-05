import Core.Chain.SI.StopCancelN
import Core.Chain.SI.Fin

/-!
# A finaliser frame at `erwp` that takes the lend's claim on a cancel

`ubind (N, D) M` at `erwp` (`ewp_ubind`, `SI/Fin.lean`, over Core's worlds), for a body whose
stops are at a twin table (`claimT`) whose cancel runs end carrying a claim `R`: `D` consumes the
claim. The frame turns the body's cancel runs back into ordinary ones:

* `erwp_ubind_cancelRun`: under `ubind (N, D)`, a cancel run ending at `raise cancel` carrying
  `R` (`cancelTabR`) is a cancel run ending owning nothing (`cancelTabN`): at the `raise`,
  `[finalise-cancel]` runs `cfin cancel (D ())`, `D` consumes `R`, and `[cfin-ret]` re-raises.
  A finaliser's stop passes the frame, which is put back into its continuation.
* `erwp_ubindClaim`: the frame around a body at `claimT`: `[then]` at a return, and at a stop the
  frame passes outward, its cancel obligation the body's under `erwp_ubind_cancelRun`.

The narrowings are those of the frames across stops: the body's table has no abortive entries
(no `[finalise]` for an ordinary raise here), and `D` neither stops nor raises (`rwp`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE cfinE)

theorem cancelTabN_down {T : OpTabN} (hT : T.Down) : (cancelTabN T).Down := by
  intro k ls t Ψ ρ h
  rcases h with ⟨K, err, hp⟩ | ⟨K, n, i, v, en, h⟩
  · obtain ⟨hc, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hp
    refine Or.inl ⟨K, err, pure_sep_mk hc ⟨τa, τb, hcab, ?_, hnb⟩⟩
    cases err with
    | none => exact he
    | some E =>
        obtain ⟨m, j, w, en, he⟩ := he
        obtain ⟨hh, hPA, hn⟩ := pure_sep_iff.mp he
        exact ⟨m, j, w, en, pure_sep_mk hh ⟨hT.pa _ _ _ hh.2.1 _ _ _ _ hPA, hn⟩⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩ ⟨ρa, ρk, hc,
      hT.pa _ _ _ h₃ _ _ _ _ hA, hu, fun ls' he =>
      ⟨fun k' hk => (hcont ls' he).1 k' (by omega), fun hq P hP =>
        hT.fin _ _ _ _ h₃ hP _ _ _ _ ((hcont ls' he).2 hq P hP)⟩⟩⟩

theorem falsePost_down : PostN.Down (fun _ _ _ _ => False) := fun _ _ _ _ h => h

/-- **A cancel run carrying `R`, under a frame whose finaliser consumes `R`.** -/
theorem erwp_ubind_cancelRun {Φ : LocFam} (hΦ : Φ.Down) {T₁ : OpTabN} (hT₁ : T₁.Down)
    (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin) {R : Nat → WProp}
    (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) Φ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ) :
    ∀ n ls x ρ, erwp (ℍ := ℍ) Φ (cancelTabR T₁ R) (fun _ _ _ _ => False) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls ((ubK N D).plug x) ρ := by
  have hL := cancelTabR_local T₁ R
  have hPD := erwpPost_down (cancelTabN_down hT₁) falsePost_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls x ρ h
  rw [erwp_eq]
  refine rwpG_bind hΦ (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hL le_rfl h)
  rcases ht with ⟨_, _, hf⟩ | ⟨K', err, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact hf.elim
  · -- the cancel's `raise`: `[finalise-cancel]`, `D` consumes the claim, `[cfin-ret]`
    obtain ⟨⟨rfl, hK'⟩, y1, y2, hy, ⟨τa, τb, hcab, herr, hnb⟩, hR⟩ := pure_sep_iff.mp hp
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
    have hDr := rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) (ResU.CompS.comm hy)
      (rwp_iff_rwpG.mp (hD k ls' y2 hR)) hnb
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ, ⟨w, rfl, rfl⟩, hnσb⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ
    refine rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.cfret μ none w) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (cancelVal none))) :=
      final_opPlug (payloadName_cancelVal none) (by simp [OpFree, Kont.Catches])
    exact rwpG_here hfin (Or.inr (Or.inl ⟨.hole, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, σ₂, compS_empty_left _, emp_empty, hnσb⟩⟩))
  · -- a finaliser's stop passes the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' => absurd (hT₁e _ _ en hT).2 hq'⟩⟩⟩))
    rw [Kont.plug_comp]
    have hc := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) _ _ _ hc

theorem claimT_some {Φ : LocFam} {T T₁ : OpTabN} {R : Nat → WProp} {m i : UInt32} {en' : OpEntN}
    (h : @OpTabN.claimT ℍ _ T Φ T₁ R m i = some en') :
    ∃ en, T m i = some en ∧ en' = if en.q = .cancel then
      OpEntN.mk en.q en.abort en.PA en.PB (some (@cancelOblRN ℍ _ Φ T₁ R)) en.wc else en := by
  unfold OpTabN.claimT at h
  cases hT : T m i with
  | none => rw [hT] at h; cases h
  | some en =>
      rw [hT] at h
      exact ⟨en, rfl, (Option.some.inj h).symm⟩

/-- **The finaliser frame around a body at `claimT`.** -/
theorem erwp_ubindClaim {Φ : LocFam} (hΦ : Φ.Down) {T T₁ : OpTabN} (hTD : T.Down)
    (hT₁ : T₁.Down) (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin)
    (hTe : ∀ m i en, T m i = some en → en.abort = false ∧ en.q ≠ .unr)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁))
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) Φ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout k ls (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) Φ (opTableN (@OpTabN.claimT ℍ _ T Φ T₁ R)) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout n ls (ubindE (.pair N D) M) ρ := by
  have hL := opTableN_local (@OpTabN.claimT ℍ _ T Φ T₁ R)
  have hPD := erwpPost_down (opTableN_down hTD) hQout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls M ρ h
  rw [← ubK_plug, erwp_eq]
  refine rwpG_bind hΦ (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en', hp⟩ | ⟨K₁, m, i, v, en', hp⟩
  · -- `[then]`
    have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det hΦ (hPD _) hstep
      (erwp_unfold_at (opTableN_local T) hk (hN k ls' v σ hv))
  · obtain ⟨⟨rfl, hK₁, hT', ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en, hT, rfl⟩ := claimT_some hT'
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    by_cases hqc : en.q = .cancel
    · rw [if_pos hqc] at ha hA hu hcont
      refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
        ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
            fun _ P hP => ?_⟩⟩⟩))
      · rw [Kont.plug_comp]
        have hc := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
        simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
        exact ih k' (by omega) _ _ _ hc
      · rw [hfin m i en hT hqc] at hP
        cases hP
        have hql : en.q ≠ .lin := by rw [hqc]; simp
        have hin := (hcont ls'' he).2 hql _ rfl
        show erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) k ls''
          (((ubK N D).comp K₁).dead.plug _) ρk
        rw [dead_comp, ubK_dead, Kont.plug_comp]
        exact erwp_ubind_cancelRun hΦ hT₁ hT₁e N D hD k ls'' _ ρk hin
    · rw [if_neg hqc] at ha hA hu hcont
      refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
        ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
            fun hql => ?_⟩⟩⟩))
      · rw [Kont.plug_comp]
        have hc := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
        simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
        exact ih k' (by omega) _ _ _ hc
      · exfalso
        have := (hTe m i en hT).2
        cases h : en.q <;> simp_all
  · obtain ⟨⟨-, -, hT', ha⟩, -⟩ := pure_sep_iff.mp hp
    obtain ⟨en, hT, rfl⟩ := claimT_some hT'
    have := (hTe m i en hT).1
    by_cases hqc : en.q = .cancel <;> simp_all

end BoCa.Fig16.LogRel.Core.Chain.SI

end
