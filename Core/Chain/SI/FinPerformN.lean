import Core.Chain.SI.StopRaiseN

/-!
# Finalisers that perform

`erwp_ubind` and `erwp_ubindRaise` read the finaliser's run at `rwp`: `D ()` neither stops nor
raises (`FinOK`). The finaliser of `SI/Programs.lean` closes a file through a capability, `close`, an operation
of the row (`Σ_D ≤ Σ`): its run stops. Here `D ()` is read at `erwp` at the body's table, whose
non-abortive entries are must-resume; at `[finalise]` the `raise`'s resource rides along the
finaliser's run, into its continuations' shares (`erwp_frameL`), and the `raise` goes on when
`D ()` answers.

* `erwp_frameL`: `[TR]` 6.146 at `erwp` across must-resume stops: the frame is put into each
  stop's continuation share and taken back at the resume; at a `raise` it is garbage, so the frame
  owns nothing there (`hRno`).
* `erwp_ubindRaiseF`: `erwp_ubindRaise` with `D ()` at `erwp`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE)

/-- **The frame at `erwp`, across must-resume stops.** `R` holds of the frame at the list the run
starts at, at every list with the same members, and at every list a resume's world condition
allows; at a `raise` it owns nothing. -/
theorem erwp_frameL {Φ : LocFam} {T : OpTabN} (hTD : T.Down)
    (hq : ∀ m i en, T m i = some en → en.abort = false → en.q = .lin)
    {Q : PostN} (R : List SRec → WProp)
    (hR : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, R ls ρ → R ls' ρ)
    (hRwc : ∀ m i en, T m i = some en → en.abort = false → ∀ ls ls' (ρk ρ₂ ρ : WRes),
      ResU.CompS ρk ρ₂ ρ → en.wc ls ls' ρ → R ls ρ₂ → R ls' ρ₂)
    (hRno : ∀ ls ρ, R ls ρ → NoOwn ρ) :
    ∀ n ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → R ls ρ₂ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ₁ →
      erwp (ℍ := ℍ) Φ (opTableN T) (fun k ls' v => Q k ls' v ⋆ R ls') n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hσ, ht, hσ₂⟩ => ?_)
    (rwpG_frame R hR hc h hR₂)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, rfl, σ₁, σ₂, hσ, hv, hσ₂⟩
  · obtain ⟨⟨rfl, hK, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hql := hq m i en hT ha
    obtain ⟨ρk₂, hk₂, haσ⟩ := (ResU.CompS.assoc ρa ρk σ₂ σ).mpr ⟨σ₁, hcak, hσ⟩
    refine Or.inr (Or.inl ⟨K, m, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩ ⟨ρa, ρk₂, haσ, hA,
      fun hu' => absurd (hql.symm.trans hu') (by simp), fun ls'' he =>
        ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq' => absurd hql hq'⟩⟩⟩)
    have he' : en.wc ls' ls'' ρk := hTD.wcl _ _ _ hT _ _ _ _ _ hk₂ he
    obtain ⟨y, hy, hyτ⟩ := compS_exch hk₂ hcτ
    have hc' := (hcont ls'' he').1 k' hk' w τ₁ y hB hy
    simp only [erwpC, show k' < n by omega, if_true] at hc' ⊢
    exact ih k' (by omega) ls'' _ y σ₂ τ₂ hyτ (hRwc m i en hT ha ls' ls'' ρk σ₂ ρk₂ hk₂ he hσ₂) hc'
  · obtain ⟨hpur, τa, τn, hcan, hPA, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨τn₂, hn₂, haσ⟩ := (ResU.CompS.assoc τa τn σ₂ σ).mpr ⟨σ₁, hcan, hσ⟩
    exact Or.inr (Or.inr ⟨K, m, i, v, en, pure_sep_mk hpur
      ⟨τa, τn₂, haσ, hPA, noOwn_compS hn₂ hnn (hRno _ _ hσ₂)⟩⟩)

/-- **The finaliser frame around a body whose raises carry `R`, the finaliser performing.**
`erwp_ubindRaise` with `D ()` at `erwp` at the body's table: at `[finalise]` the `raise`'s
resource rides along `D ()` (`erwp_frameL`), and the `raise` goes on when `D ()` answers `()`
owning nothing. -/
theorem erwp_ubindRaiseF {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down)
    (hTe : ∀ m i en, T m i = some en → en.abort = false → en.q = .lin ∧ en.wc = extF)
    (hfinN : ∀ m i en, T m i = some en → en.fin = none)
    (hTr : ∀ m i en, T m i = some en → en.abort = true → m ≠ 0)
    (hPAls : ∀ m i en, T m i = some en → ∀ k ls ls' v ρ, extF ls ls' ρ →
      en.PA k ls v ρ → en.PA k ls' v ρ)
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ → erwp (ℍ := ℍ) Φ (opTableN T)
      (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout k ls (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) Φ (opTableR T R) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout n ls (ubindE (.pair N D) M) ρ := by
  have hL := opTableR_local T R
  have hPD := erwpPost_down (opTableN_down hTD) hQout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls M ρ h
  rw [← ubK_plug, erwp_eq]
  refine rwpG_bind hΦ (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[then]`
    have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det hΦ (hPD _) hstep
      (erwp_unfold_at (opTableN_local T) hk (hN k ls' v σ hv))
  · -- a stop passes the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hql => absurd (hTe m i en hT ha).1 hql⟩⟩⟩))
    rw [Kont.plug_comp]
    have hc := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) _ _ _ hc
  · -- `[finalise]`: `D (); raise p`, `D` consuming the claim, its stops passing the `raise`
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, σ₁, ρR, hcσ, ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩, hR⟩ :=
      pure_sep_iff.mp hp
    have hm0 := hTr m i en hT ha
    refine rwpG_det hΦ (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    refine erwp_unfold_at (opTableN_local T) hk ?_
    set Fr : List SRec → WProp := fun ls₀ τ =>
      ((fun ρ => en.PA k ls₀ v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ with hFr
    have hDr := erwp_frameL hTD (fun m i en h ha => (hTe m i en h ha).1) Fr
      (fun _ _ hs _ ⟨τa, τn, hcτ, ⟨hPAτ, hn⟩, hnn⟩ =>
        ⟨τa, τn, hcτ, ⟨hPAls _ _ _ hT _ _ _ _ _ (extF_of_same hs τa) hPAτ, hn⟩, hnn⟩)
      (fun m' i' en' h ha' ls₁ ls₂ ρk ρ₂ ρ₃ hc₃ he ⟨τa, τn, hcτ, ⟨hPAτ, hn⟩, hnn⟩ => by
        rw [(hTe m' i' en' h ha').2] at he
        exact ⟨τa, τn, hcτ, ⟨hPAls _ _ _ hT _ _ _ _ _
          (extF_left _ _ _ _ _ hcτ (extF_right hc₃ he)) hPAτ, hn⟩, hnn⟩)
      (fun _ _ ⟨τa, τn, hcτ, ⟨_, hnA'⟩, hnn'⟩ => noOwn_compS hcτ hnA' hnn')
      k ls' _ ρR σ₁ σ (ResU.CompS.comm hcσ) ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩
      (hD k ls' ρR hR)
    refine erwp_bind_le hΦ _ (fun m => by simp [Kont.HasHnd])
      (then_fin (ℍ := ℍ) (μ := fun _ => none) (i := i) N D v hm0 hK₁ .hole).2.1
      (OpTabN.ctxClosed_of_fin hfinN _) k ?_ k le_rfl ls' _ σ hDr
    rintro k₂ ls₂ w σ₂ hk₂ ⟨σa, σb, hcσ', ⟨rfl, rfl⟩, τa, τn, hcτ, ⟨hPAτ, hnτ⟩, hnn'⟩
    obtain rfl := eq_of_compS_empty_left hcσ'
    refine erwp_det hΦ (opTableN_down hTD) hQout
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).2.2) ?_
    rw [Kont.plug_hole, erwp_eq]
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload m i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, m, i, v, en,
        pure_sep_mk ⟨rfl, rfl, hT, ha⟩ ⟨τa, τn, hcτ, ⟨hTD.pa_le hT hk₂
          hPAτ, hnτ⟩, hnn'⟩⟩))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
