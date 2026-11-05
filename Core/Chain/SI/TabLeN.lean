import Core.Chain.SI.AntiStopN

/-!
# Tables widened: `OpTab.Le` and `FinLeS` at the index

`erwp_handle` and `erwp_ccatch` (`SI/HandleN.lean`) take the cancel run's table included in the
handler's (`OpTabN.Sub`, the same entries). Core's `[handle]` takes it below (`OpTab.Le`):
the same operations, and at a capturable one a weaker cancel obligation (`FinLeS`). These are
the definitions at the index (`FinLeSN`, `OpEntN.Le`, `OpTabN.Le`), `erwp` monotone in the table
along them (`erwp_tabLe`), and `erwp_ccatchLe`, `erwp_handleLe` with `Le` where the originals
have `Sub`. `OpTabN.Sub` is a special case (`OpTabN.Sub.le`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE)

/-- `FinLeS` at the index: a cancel obligation at least as weak. -/
def FinLeSN : Option (Nat → List SRec → Expr → WProp) → Option (Nat → List SRec → Expr → WProp) →
    Prop
  | _, none => True
  | none, some _ => False
  | some P, some P' => ∀ k ls e ρ, P k ls e ρ → P' k ls e ρ

/-- What a weaker obligation gives: the obligation `cancelOKN` reads, carried along. -/
theorem finLeSN_apply {F F' : Option (Nat → List SRec → Expr → WProp)} (h : FinLeSN F F')
    {P' : Nat → List SRec → Expr → WProp} (hP' : F' = some P') {k : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (hF : ∀ P, F = some P → P k ls e ρ) : P' k ls e ρ := by
  subst hP'
  cases F with
  | none => exact h.elim
  | some P => exact h k ls e ρ (hF P rfl)

/-- `OpEnt.Le` at the index. -/
def OpEntN.Le (en en' : OpEntN) : Prop :=
  en.q = en'.q ∧ en.abort = en'.abort ∧ en.PA = en'.PA ∧ en.PB = en'.PB ∧ en.wc = en'.wc ∧
    (en.abort = false → en.q ≠ .lin → FinLeSN en.fin en'.fin)

/-- `OpTab.Le` at the index. -/
def OpTabN.Le (T T' : OpTabN) : Prop :=
  ∀ n i en, T n i = some en → ∃ en', T' n i = some en' ∧ en.Le en'

theorem FinLeSN.refl : ∀ F : Option (Nat → List SRec → Expr → WProp), FinLeSN F F
  | none => trivial
  | some _ => fun _ _ _ _ h => h

theorem OpTabN.Sub.le {T T' : OpTabN} (h : T.Sub T') : T.Le T' := fun n i en hT =>
  ⟨en, h n i en hT, rfl, rfl, rfl, rfl, rfl, fun _ _ => FinLeSN.refl _⟩

/-- A stop of `opTableN T` is one of `opTableN T′` when `T ≤ T′`. -/
theorem opTableN_le {T T' : OpTabN} (hT : T.Le T') :
    ∀ k ls t (Ψ Ψ' : ContN) ρ, (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
      opTableN T k ls t Ψ ρ → opTableN T' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases opTableN_local T k ls t Ψ Ψ' ρ hΨ h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', h₃', hq, hab, hPA, hPB, hwc, hfl⟩ := hT n i en h₃
    refine Or.inl ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩ ⟨ρa, ρk, hc, hPA ▸ hA,
      fun hu' => hu (hq.trans hu'), fun ls' he => ?_⟩⟩
    rw [← hwc] at he
    refine ⟨fun k' hk' w => hPB ▸ (hcont ls' he).1 k' hk' w, fun hq' P hP => ?_⟩
    exact finLeSN_apply (hfl h₄ (hq ▸ hq')) hP (fun P₀ hP₀ => (hcont ls' he).2 (hq ▸ hq') P₀ hP₀)
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρn, hc, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨en', h₃', -, hab, hPA', -⟩ := hT n i en h₃
    exact Or.inr ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩
      ⟨ρa, ρn, hc, ⟨hPA' ▸ hPA, hnA⟩, hnn⟩⟩

/-- **`erwp` widened along `OpTabN.Le`.** -/
theorem erwp_tabLe {Φ : LocFam} {T T' : OpTabN} (hT : T.Le T') {Q : PostN} :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ → erwp (ℍ := ℍ) Φ (opTableN T') Q n ls e ρ :=
  erwp_mono (fun _ _ _ _ h => h) (opTableN_le hT)

/-- **`erwp_ccatch` with the cancel run's table below the handler's.** -/
theorem erwp_ccatchLe {Φ : LocFam} (hΦ : Φ.Down) {T Tout : OpTabN} (hT : T.Le Tout)
    (hToutD : Tout.Down) :
    ∀ n ls e ρ, cancelOblN (ℍ := ℍ) Φ T n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) unitPost n ls (ccatchE e) ρ := by
  have hLin := cancelTabN_local T
  have hPD := erwpPost_down (opTableN_down hToutD) unitPost_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h
  rw [erwp_eq]
  show rwpG (ℍ := ℍ) Φ _ n ls (ccatchK.plug e) ρ
  refine rwpG_bind hΦ ccatchK ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hLin le_rfl h)
  rcases ht with ⟨_, _, hv⟩ | ht
  · exact hv.elim
  rcases ht with ⟨K', err, hs'⟩ | ⟨K₁, m, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    cases err with
    | none =>
        refine rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.cancel μ K' hK') rfl .hole) ?_
        have hτa : τa = PMap.empty := he.1
        subst hτa
        rw [← eq_of_compS_empty_left hcab] at hnb
        refine rwpG_garbage (rwpG_here (fun μ => final_val μ Val.unit)
          ⟨PMap.empty, σ, compS_empty_left σ, hnb, Or.inl ⟨Val.unit, rfl, rfl, rfl⟩⟩)
    | some E =>
        refine rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.creraise μ E K' hK') rfl .hole) ?_
        obtain ⟨m, j, w, en, he⟩ := he
        obtain ⟨⟨rfl, hTe, ha⟩, hPA, hnA⟩ := pure_sep_iff.mp he
        obtain ⟨en', hTe', hle⟩ := hT _ _ _ hTe
        have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (opPayload m j w))) :=
          final_opPlug (payloadName_opPayload m j w) (by simp [OpFree, Kont.Catches])
        exact rwpG_here hfin (Or.inr (Or.inr ⟨.hole, m, j, w, en',
          pure_sep_mk ⟨rfl, rfl, hTe', hle.2.1 ▸ ha⟩ ⟨τa, τb, hcab, ⟨hle.2.2.1 ▸ hPA, hnA⟩, hnb⟩⟩))
  · -- an operation of a finaliser passes `ccatch`
    obtain ⟨⟨rfl, hK₁, hT₁, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hKo : (ccatchK.comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val]
    have ht' : ccatchK.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (ccatchK.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    obtain ⟨en', hT₁', hle⟩ := hT _ _ _ hT₁
    obtain ⟨hq, hab, hPA, hPB, hwc, hfl⟩ := hle
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨ccatchK.comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT₁', hab ▸ ha⟩
        ⟨ρa, ρk, hcak, hPA ▸ hA, fun hu' => hu (hq.trans hu'), fun ls'' he =>
          ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq' => ?_⟩⟩⟩))
    · rw [← hwc] at he
      rw [Kont.plug_comp]
      have hc := (hcont ls'' he).1 k' hk' w τ₁ τ₂ (hPB ▸ hB) hcτ
      simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) _ _ _ hc
    · rw [← hwc] at he
      intro P hP
      show P k ls'' ((ccatchK.comp K₁).dead.plug _) ρk
      rw [dead_comp, dead_ccatchK]
      exact finLeSN_apply (hfl ha (hq ▸ hq')) hP
        (fun P₀ hP₀ => (hcont ls'' he).2 (hq ▸ hq') P₀ hP₀)

/-- **`erwp_handle` with each cancel row's table below the cancel table** (`OpTab.Le`, Core's
`[handle]` premise). -/
theorem erwp_handleLe {Φ : LocFam} (hΦ : Φ.Down) (Tin Tout : OpTabN) (hTinD : Tin.Down)
    (hTout : Tout.Down) (n₀ : UInt32) (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : PostN) (hQout : Qout.Down)
    (hq : ∀ i en, Tin n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (Tc : UInt32 → Option OpTabN)
    (hTc : ∀ i en, Tin n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁) ∧ T₁.Le Tk ∧ Tk.Down)
    (hret : ∀ k ls v ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val hr) (.val v)) ρ)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelN (ℍ := ℍ) Φ (opTableN Tout) Qout en (Tc i) k ls κ) ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k ls v ρ, en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.val v)) ρ)) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN Tin) Qin n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) ρ := by
  have hLin := opTableN_local Tin
  have hLout := opTableN_local Tout
  have hDout := opTableN_down hTout
  have hPD := erwpPost_down hDout hQout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h
  set H := hndVal n₀ qs hr hs with hH
  rw [erwp_eq]
  show rwpG (ℍ := ℍ) Φ _ n ls ((hndK H).plug e) ρ
  refine rwpG_bind hΦ (hndK H) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hLin le_rfl h)
  -- what the continuations of the handled run are owed, read through the induction hypothesis
  have hcontIH : ∀ k', k' < k → ∀ ls'' e'' τ,
      erwpC (ℍ := ℍ) Φ (opTableN Tin) Qin n k' ls'' e'' τ →
      erwpC (ℍ := ℍ) Φ (opTableN Tout) Qout n k' ls'' (hndE H e'') τ := by
    intro k' hk' ls'' e'' τ hc
    simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) ls'' e'' τ hc
  rcases ht with ⟨v, rfl, hv⟩ | ht | ht
  · -- `[ret]`
    exact rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole)
      (erwp_unfold_at hLout hk (hret k ls' v σ hv))
  · -- a stop at a non-abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n₀
    · -- `[op]` at the handler's name: the clause, with `κ`
      subst hm
      obtain ⟨c, hc, hna, -⟩ := hop i en hT
      refine rwpG_det hΦ (hPD _)
        (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
      -- the cancel run of the continuation, at the cancel row's table, at every `k″ ≤ k`
      have hcan : ∀ ls'', en.wc ls' ls'' ρk → en.q ≠ .lin → ∀ Tk, Tc i = some Tk → ∀ k'', k'' ≤ k →
          erwp (ℍ := ℍ) Φ (opTableN Tk) unitPost k'' ls''
            (ccatchE (K₁.dead.plug (raiseE (.val (cancelVal none))))) ρk := by
        intro ls'' he hq' Tk hTk k'' hk''
        obtain ⟨T₁, hf, hsub, hTkD⟩ := hTc i en hT ha hq' Tk hTk
        have hP := (hcont ls'' he).2 hq' _ hf
        exact erwp_ccatchLe hΦ hsub hTkD k'' ls'' _ ρk (hTinD.fin_le hT hf hk'' hP)
      have hDk : ∀ Tk : OpTabN, Tc i = some Tk → en.q ≠ .lin → (opTableN Tk).Down := by
        intro Tk hTk hq'
        obtain ⟨-, -, -, hTkD⟩ := hTc i en hT ha hq' Tk hTk
        exact opTableN_down hTkD
      rw [hq i en hT ha, kappaAt_tag]
      cases hqq : en.q with
      | unr =>
          refine erwp_unfold_at hLout hk (hna ha k ls' v
            ⟨kappa H K₁, by unfold kappa; exact .lam⟩ σ ⟨ρa, ρk, hcak, hA, hu, ?_⟩)
          intro ls'' he k' hk'
          refine ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' Tk hTk => ?_⟩
          · have h₁ := hcontIH k' hk' _ _ _ ((hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ)
            simp only [erwpC, show k' < n by omega, if_true] at h₁
            exact erwp_kappa_resume hΦ hDout hQout H K₁ w h₁
          · exact erwp_kappa_cancel hΦ (hDk Tk hTk hq') unitPost_down H K₁
              (hcan ls'' he hq' Tk hTk k' (by omega))
      | lin | cancel =>
          -- the cell is allocated, one step; `κ` is `kappaC` at it, owning the cell and the share
          refine erwp_unfold_at hLout hk (erwp_kappaCell hΦ hLout hDout hQout _ H K₁
            (.appR (.val c) (.pairR v .hole)) (fun ℓ σ₁ σ₂ hcell hc₂ => ?_))
          obtain ⟨y, hy₁, hy₂⟩ := compS_reassoc hcak hc₂
          have hA' : en.PA (k - 1) ls' v ρa := by
            cases k with
            | zero => exact hA
            | succ k₀ => exact hTinD.pa _ _ _ hT _ _ _ _ hA
          refine hna ha (k - 1) ls' v ⟨_, isVal_kappaC _ ℓ H K₁⟩ σ₂
            ⟨ρa, y, hy₂, hA', fun hq' => absurd (hqq.symm.trans hq') (by simp), ?_⟩
          intro ls'' he k' hk'
          refine ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' Tk hTk => ?_⟩
          · obtain ⟨z, hz, hzτ⟩ := compS_exch hy₁ hcτ
            have h₁ := hcontIH k' (by omega) _ _ _
              ((hcont ls'' (hTinD.wcl _ _ _ hT _ _ _ _ _ hy₁ he)).1 k' (by omega) w τ₁ z hB hz)
            simp only [erwpC, show k' < n by omega, if_true] at h₁
            exact erwp_kappaC_resume hΦ hLout hDout hQout _ ℓ H K₁ w
              ⟨σ₁, z, ResU.CompS.comm hzτ, hcell,
                erwp_le hΦ hLout hDout hQout (Nat.sub_le k' 1) h₁⟩
          · first
              | exact absurd hqq hq'
              | exact erwp_kappaC_cancel hΦ (opTableN_local Tk) (hDk Tk hTk hq') unitPost_down
                  ℓ H K₁ ⟨σ₁, ρk, ResU.CompS.comm hy₁, hcell,
                    hcan ls'' (hTinD.wcl _ _ _ hT _ _ _ _ _ hy₁ he) hq' Tk hTk (k' - 1) (by omega)⟩
    · -- an operation of another name passes outward
      have hKo : ((hndK H).comp K₁).HasHnd m = false := by
        rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
      have ht' : (hndK H).plug (K₁.plug (performE (.val (opPayload m i v)))) =
          ((hndK H).comp K₁).plug (opE false (opPayload m i v)) := by
        rw [Kont.plug_comp]; rfl
      rw [ht']
      refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
        ⟨(hndK H).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
            fun hq' => ?_⟩⟩⟩))
      · rw [Kont.plug_comp]
        exact hcontIH k' hk' _ _ _ ((hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ)
      · intro P hP
        show P k ls'' (((hndK H).comp K₁).dead.plug _) ρk
        rw [dead_comp, dead_hndK]
        exact (hcont ls'' he).2 hq' P hP
  · -- a stop at an abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n₀
    · -- `[unwind]` at the handler's name: the clause; the continuation is discarded
      subst hm
      obtain ⟨c, hc, -, hab⟩ := hop i en hT
      refine rwpG_det hΦ (hPD _)
        (fun μ => step1Only_plug (Head.hunwind μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
      refine rwpG_garbage (rwpG_mono (fun _ _ _ _ ⟨τ₁, τ₂, hcτ, hq', hnτ⟩ =>
        ⟨τ₁, τ₂, hcτ, hnτ, hq'⟩) (rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) hcan
          (erwp_unfold_at hLout hk (hab ha k ls' v ρa hPA)) hnn))
    · -- an abortive operation of another name passes outward
      have hKo : ((hndK H).comp K₁).Catches m = false := by
        rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm
      have ht' : (hndK H).plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
          ((hndK H).comp K₁).plug (opE true (opPayload m i v)) := by
        rw [Kont.plug_comp]; rfl
      rw [ht']
      exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
        ⟨(hndK H).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
