import Core.Chain.Loop835N

/-!
# `[handle]` at the stratified table  `[spec §28]`

Core's `ewp_handleS` (`Core/EffBoxed.lean`) at `erwp`: `erwp_handle` with the handled computation
at `opTableNS α Tin` (E12's table, `Core/Chain/Stop835N.lean`), so the clause of a capturing
operation receives `κ` with its resource in `Res_α`. The proof is `erwp_handle_le`'s
(`SI/HandleN.lean`), case for case; at a must-resume or cancellable operation `κ`'s resource is
the share and its cell, an `own` cell, which is in every stratum.

This is the step from `stop_semN` to BOXED-κ's handler. `effHandleVB`'s compatibility lemma also
needs the clauses read at `vN` (interface entry E10), which is not built here: a clause's `κ` is at
`kTy Σ R q B F`, a thunk type, and `vN` of a thunk asks the computation at every world `Θ′` along
`ExtR` from `κ`'s resource and every view consistent with it, while the handled run's stop owes
its continuation (`KapRelN`) only at the run's own view and along `extF` on the record list.
Not derived; obstruction not verified.
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

/-- **A handler at the stratified table, its clauses asked at the stops up to `N`** (Core's
`ewp_handleS`): `erwp_handle_le` with the handled run at `opTableNS α Tin`; a capturing clause
receives `κ` in `Res_α`. -/
theorem erwp_handleS_le {Φ : LocFam} (hΦ : Φ.Down) (α : Life) (N : Nat) (Tin Tout : OpTabN)
    (hTinD : Tin.Down)
    (hTout : Tout.Down) (n₀ : UInt32) (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : PostN) (hQout : Qout.Down)
    (hq : ∀ i en, Tin n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (Tc : UInt32 → Option OpTabN)
    (hTc : ∀ i en, Tin n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁) ∧ T₁.Sub Tk ∧ Tk.Down)
    (hret : ∀ k, k ≤ N → ∀ ls v ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val hr) (.val v)) ρ)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ fun ρ => KapRelN (ℍ := ℍ) Φ (opTableN Tout) Qout en (Tc i) k ls κ ρ ∧
          ρ.InStratum α) ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k, k ≤ N → ∀ ls v ρ, en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.val v)) ρ)) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ (opTableNS α Tin) Qin n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) ρ := by
  have hLin := opTableNS_local α Tin
  have hLout := opTableN_local Tout
  have hDout := opTableN_down hTout
  have hPD := erwpPost_down hDout hQout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN ls e ρ h
  set H := hndVal n₀ qs hr hs with hH
  rw [erwp_eq]
  show rwpG (ℍ := ℍ) Φ _ n ls ((hndK H).plug e) ρ
  refine rwpG_bind hΦ (hndK H) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hLin le_rfl h)
  -- what the continuations of the handled run are owed, read through the induction hypothesis
  have hcontIH : ∀ k', k' < k → ∀ ls'' e'' τ,
      erwpC (ℍ := ℍ) Φ (opTableNS α Tin) Qin n k' ls'' e'' τ →
      erwpC (ℍ := ℍ) Φ (opTableN Tout) Qout n k' ls'' (hndE H e'') τ := by
    intro k' hk' ls'' e'' τ hc
    simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) (by omega) ls'' e'' τ hc
  rcases ht with ⟨v, rfl, hv⟩ | ht | ht
  · -- `[ret]`
    exact rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole)
      (erwp_unfold_at hLout hk (hret k (by omega) ls' v σ hv))
  · -- a stop at a non-abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, ⟨hu, hcont⟩, hstr⟩ := pure_sep_iff.mp hp
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
        exact erwp_ccatch hΦ hsub hTkD k'' ls'' _ ρk (hTinD.fin_le hT hf hk'' hP)
      have hDk : ∀ Tk : OpTabN, Tc i = some Tk → en.q ≠ .lin → (opTableN Tk).Down := by
        intro Tk hTk hq'
        obtain ⟨-, -, -, hTkD⟩ := hTc i en hT ha hq' Tk hTk
        exact opTableN_down hTkD
      rw [hq i en hT ha, kappaAt_tag]
      cases hqq : en.q with
      | unr =>
          refine erwp_unfold_at hLout hk (hna ha k (by omega) ls' v
            ⟨kappa H K₁, by unfold kappa; exact .lam⟩ σ ⟨ρa, ρk, hcak, hA, ⟨hu, ?_⟩, hstr⟩)
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
          have hy : y.InStratum α := by
            refine inStratum_compS hy₁ hstr ?_
            rw [hcell]
            exact ResU.inStratum_single_own α ℓ Val.unit
          have hA' : en.PA (k - 1) ls' v ρa := by
            cases k with
            | zero => exact hA
            | succ k₀ => exact hTinD.pa _ _ _ hT _ _ _ _ hA
          refine hna ha (k - 1) (by omega) ls' v ⟨_, isVal_kappaC _ ℓ H K₁⟩ σ₂
            ⟨ρa, y, hy₂, hA', ⟨fun hq' => absurd (hqq.symm.trans hq') (by simp), ?_⟩, hy⟩
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
          (erwp_unfold_at hLout hk (hab ha k (by omega) ls' v ρa hPA)) hnn))
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

/-- **A handler at the stratified table** (Core's `ewp_handleS`): `erwp_handleS_le` at `N = n`. -/
theorem erwp_handleS {Φ : LocFam} (hΦ : Φ.Down) (α : Life) (Tin Tout : OpTabN)
    (hTinD : Tin.Down) (hTout : Tout.Down) (n₀ : UInt32)
    (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : PostN) (hQout : Qout.Down)
    (hq : ∀ i en, Tin n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (Tc : UInt32 → Option OpTabN)
    (hTc : ∀ i en, Tin n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁) ∧ T₁.Sub Tk ∧ Tk.Down)
    (hret : ∀ k ls v ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val hr) (.val v)) ρ)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ fun ρ => KapRelN (ℍ := ℍ) Φ (opTableN Tout) Qout en (Tc i) k ls κ ρ ∧
          ρ.InStratum α) ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k ls v ρ, en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.val v)) ρ)) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableNS α Tin) Qin n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) ρ :=
  fun n => erwp_handleS_le hΦ α n Tin Tout hTinD hTout n₀ hTin qs hr hs Qin Qout hQout hq Tc hTc
    (fun k _ => hret k)
    (fun i en hT => by
      obtain ⟨c, hc, h₁, h₂⟩ := hop i en hT
      exact ⟨c, hc, fun ha k _ => h₁ ha k, fun ha k _ => h₂ ha k⟩) n le_rfl

end BoCa.Fig16.LogRel.Core.Chain.SI

end
