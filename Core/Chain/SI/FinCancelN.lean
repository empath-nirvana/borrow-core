import Core.Chain.SI.UbindN
import Core.Chain.SI.FinPerformN

/-!
# A finaliser that performs, on the cancel path

`erwp_ubind_cancelRun` and `erwp_ubindClaim` (`SI/UbindN.lean`) read the finaliser at `rwp`:
`D ()` neither stops nor raises. Here `D ()` is read at `erwp` at the cancel run's table `T₁`,
whose entries are must-resume and non-abortive. At `[finalise-cancel]` the cancel run is
`cfin cancel (D ())`; the `raise`'s resource, which owns nothing, rides along `D ()`'s run into
each of its stops' continuation shares, as `erwp_frameL` carries it on the raise path; `D ()`'s
stops are the cancel run's stops at `T₁` (`cancelTabN T₁`'s perform clause), under the context
`cfin cancel [·]`; when `D ()` answers `()` owning nothing, `[cfin-ret]` re-raises
(`erwp_cfin_run`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE cfinE)

/-- **`cfin cancel (D ())` as a cancel run.** A computation at `erwp` at `T₁` answering `()`
owning nothing, with a part `g` owning nothing beside it, under `cfin cancel [·]`, is a cancel
run at `T₁`. -/
theorem erwp_cfin_run {Φ : LocFam} (hΦ : Φ.Down) {T₁ : OpTabN} (hT₁ : T₁.Down)
    (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin) :
    ∀ n ls x (ρ g σ : WRes), ResU.CompS ρ g σ → NoOwn g →
      erwp (ℍ := ℍ) Φ (opTableN T₁) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls
        ((cfK (cancelVal none)).plug x) σ := by
  have hPD := erwpPost_down (cancelTabN_down hT₁) falsePost_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls x ρ g σ hc hg h
  rw [erwp_eq] at h ⊢
  refine rwpG_bind hΦ (cfK _) ?_
  refine rwpG_mono_le (fun k hk ls' t τ ⟨τ₁, τ₂, hτ, ht, hτ₂⟩ => ?_)
    (rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) hc h hg)
  rcases ht with ⟨w, rfl, rfl, rfl⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `D ()` answered: `[cfin-ret]`
    obtain rfl := eq_of_compS_empty_left hτ
    refine rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.cfret μ none Val.unit) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (cancelVal none))) :=
      final_opPlug (payloadName_cancelVal none) (by simp [OpFree, Kont.Catches])
    exact rwpG_here hfin (Or.inr (Or.inl ⟨.hole, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, _, compS_empty_left _, emp_empty, hτ₂⟩⟩))
  · -- a stop of `D ()`: a stop of the cancel run, the part riding in its share
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hql := (hT₁e m i en hT).2
    have hKo : ((cfK (cancelVal none)).comp K₁).HasHnd m = false := by
      simp [hasHnd_comp, hK₁, cfK, Kont.HasHnd]
    have ht' : (cfK (cancelVal none)).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((cfK (cancelVal none)).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    obtain ⟨ρk₂, hk₂, haσ⟩ := (ResU.CompS.assoc ρa ρk τ₂ τ).mpr ⟨τ₁, hcak, hτ⟩
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨(cfK (cancelVal none)).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk₂, haσ, hA, fun hu' => absurd (hql.symm.trans hu') (by simp), fun ls'' he =>
          ⟨fun k' hk' w σ₁ σ₂ hB hcσ => ?_, fun hq' => absurd hql hq'⟩⟩⟩))
    have he' : en.wc ls' ls'' ρk := hT₁.wcl _ _ _ hT _ _ _ _ _ hk₂ he
    obtain ⟨y, hy, hyσ⟩ := compS_exch hk₂ hcσ
    have hc' := (hcont ls'' he').1 k' hk' w σ₁ y hB hy
    rw [Kont.plug_comp]
    simp only [erwpC, show k' < n by omega, if_true] at hc' ⊢
    exact ih k' (by omega) ls'' _ y τ₂ σ₂ hyσ hτ₂ hc'
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT₁e m i en hT).1]; simp)

/-- **`erwp_ubind_cancelRun` with a finaliser that performs**: `D ()` at `erwp` at the cancel
run's table, its stops must-resume; the `raise`'s resource rides along its run
(`erwp_cfin_run`). -/
theorem erwp_ubind_cancelRunF {Φ : LocFam} (hΦ : Φ.Down) {T₁ : OpTabN} (hT₁ : T₁.Down)
    (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin) {R : Nat → WProp}
    (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      erwp (ℍ := ℍ) Φ (opTableN T₁) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
        (.app (.val D) (.val .unit)) ρ) :
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
    exact erwp_unfold_at (cancelTabN_local T₁) hk
      (erwp_cfin_run hΦ hT₁ hT₁e k ls' _ y2 y1 σ (ResU.CompS.comm hy) hnb (hD k ls' y2 hR))
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

/-- **`erwp_ubindClaim` with a finaliser that performs on the cancel path.** -/
theorem erwp_ubindClaimF {Φ : LocFam} (hΦ : Φ.Down) {T T₁ : OpTabN} (hTD : T.Down)
    (hT₁ : T₁.Down) (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin)
    (hTe : ∀ m i en, T m i = some en → en.abort = false ∧ en.q ≠ .unr)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁))
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      erwp (ℍ := ℍ) Φ (opTableN T₁) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
        (.app (.val D) (.val .unit)) ρ)
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
        exact erwp_ubind_cancelRunF hΦ hT₁ hT₁e N D hD k ls'' _ ρk hin
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
