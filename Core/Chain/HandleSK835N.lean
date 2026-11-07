import Core.Chain.HandleK835N
import Core.Chain.HandleS835N
import Core.Chain.MechK835N3

/-!
# `[handle]` at the stratified table, at `erwpK`  `[spec §28]`

`erwp_handleS_le` (`HandleS835N.lean`) restated over a world index: `erwpK_handleLe_le`'s proof with
the handled run at the stratified table `opTableKS α Tin` (`erwpK_stratify`'s), so a capturing
clause receives the Kripke stop with its resource in `Res_α`; at a must-resume or cancellable
operation `κ`'s resource is the share and its cell, an `own` cell, in every stratum. Each `erwp`
statement is proved again at one world (`*_of_K`); its text is the original's.
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

variable {ι : Type}

/-- `opTableNS` at the floor bound `lo` reads what is owed only below the index. -/
theorem opTableKS_local (lo α : Life) (T : OpTabK ι) : (opTableKS lo α T).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, ρa, ρk, hc, hA, ⟨hu, f, hf, hcont⟩, hs⟩ := pure_sep_iff.mp h
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, ⟨hu, f, hf, fun y hy ls' he =>
      ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ y k' hk _ _ _ ((hcont y hy ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
        (hcont y hy ls' he).2⟩⟩, hs⟩⟩
  · exact Or.inr h

/-- **A handler at the stratified table at `erwpK`, its clauses asked at the stops up to `N`**
(`erwp_handleS_le`): `erwpK_handleLe_le` with the handled run at `opTableKS α Tin`; a capturing
clause receives the Kripke stop with its resource in `Res_α`. -/
theorem erwpK_handleS_le {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    (α : Life) (N : Nat) (Tin Tout : ι → OpTabK ι) (hTinD : ∀ x, (Tin x).Down)
    (hTout : ∀ x, (Tout x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (Tout y)).Le (opTableK (fl x) (Tout x)))
    (n₀ : UInt32) (hTin : ∀ x m i, m ≠ n₀ → Tin x m i = Tout x m i) (qs hr hs : Val)
    (Qin Qout : ι → PostN) (hQout : ∀ x, (Qout x).Down)
    (hq : ∀ x i en, Tin x n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hwcl : ∀ x m i en, Tin x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x i en, Tin x n₀ i = some en → en.abort = false → ∀ f y (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (Tc : UInt32 → Option (ι → OpTabK ι))
    (hTc : ∀ x i en, Tin x n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk,
      Tc i = some Tk → ∃ T₁ : ι → OpTabK ι,
        en.fin = some (fun y k ls e => erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z))
          (fun _ _ _ _ _ => False) y k ls e) ∧ (∀ z, (T₁ z).Sub (Tk z)) ∧ ∀ z, (Tk z).Down)
    (hVr : ∀ y, V y y)
    (hInvW : ∀ x m i en, Tin x m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y)
    (hInvC : ∀ i Tk, Tc i = some Tk → ∀ z m j en, Tk z m j = some en → en.abort = false →
      ∀ f y ρ, en.wk f y ρ → Inv y)
    (hret : ∀ x k, k ≤ N → ∀ ls v ρ, Qin x k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
        (.app (.val hr) (.val v)) ρ)
    (hop : ∀ x i en, Tin x n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ fun ρ => KapRelK (ℍ := ℍ) V Φ fl (fun z => opTableK (fl z) (Tout z)) Qout
          en (fl x) (Tc i) k ls κ ρ ∧ ρ.InStratum α) ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k, k ≤ N → ∀ ls v ρ, en.PA k ls v ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.val v)) ρ)) :
    ∀ n, n ≤ N → ∀ x, Inv x → ∀ ls e ρ,
      erwpK (ℍ := ℍ) V Φ (fun z => opTableKS (fl z) α (Tin z)) Qin x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x n ls
        (hndE (hndVal n₀ qs hr hs) e) ρ := by
  have hLin : ∀ z, (opTableKS (fl z) α (Tin z)).Local := fun z => opTableKS_local _ _ _
  have hLout : ∀ z, (opTableK (fl z) (Tout z)).Local := fun z => opTableK_local _ _
  have hDout : ∀ z, (opTableK (fl z) (Tout z)).Down := fun z => opTableK_down (hTout z)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN x hx ls e ρ h
  have hPD := erwpPostK_down (V := V x) (hDout x) hQout
  set H := hndVal n₀ qs hr hs with hH
  rw [erwpK_eq]
  show rwpG (ℍ := ℍ) (Φ x) _ n ls ((hndK H).plug e) ρ
  refine rwpG_bind (hΦ x hx) (hndK H) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨ht, hvσ⟩ => ?_)
    (rwpG_validK (erwpK_unfold_at hLin le_rfl h))
  -- what the continuations of the handled run are owed, read through the induction hypothesis
  have hcontIH : ∀ y, Inv y → ∀ k', k' < k → ∀ ls'' e'' τ,
      erwpCK (ℍ := ℍ) V Φ (fun z => opTableKS (fl z) α (Tin z)) Qin n y k' ls'' e'' τ →
      erwpCK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout n y k' ls'' (hndE H e'') τ := by
    intro y hyI k' hk' ls'' e'' τ hc
    simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) (by omega) y hyI ls'' e'' τ hc
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ht | ht
  · -- `[ret]`, at the world the handled run's value is posted at
    exact rwpG_det (hΦ x hx) (hPD _)
      (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole)
      (erwpK_shift hVt hΦV hTV hLout hy hk (hret y k (by omega) ls' v σ hv))
  · -- a stop at a non-abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, ⟨hu, f, hf, hcont⟩, hstr⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n₀
    · -- `[op]` at the handler's name: the clause, with the Kripke stop
      subst hm
      obtain ⟨c, hc, hna, -⟩ := hop x i en hT
      refine rwpG_det (hΦ x hx) (hPD _)
        (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
      -- the cancel run of the continuation at a world, at the cancel row's table
      have hcan : ∀ y, Inv y → ∀ (ρ' : WRes), ∀ ls'', en.wc ls' ls'' ρ' →
          (en.q ≠ .lin → cancelOKK en y k ls'' K₁ ρ') → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
          ∀ k'', k'' ≤ k →
          erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tk z)) (fun _ => unitPost) y k'' ls''
            (ccatchE (K₁.dead.plug (raiseE (.val (cancelVal none))))) ρ' := by
        intro y hyI ρ' ls'' _ hco hq' Tk hTk k'' hk''
        obtain ⟨T₁, hfn, hsub, hTkD⟩ := hTc x i en hT ha hq' Tk hTk
        have hP := hco hq' _ hfn
        exact erwpK_ccatch hVr hΦ hsub hTkD (hInvC i Tk hTk) k'' y hyI ls'' _ ρ'
          ((hTinD x).fin_le hT hfn hk'' hP)
      have hDk : ∀ Tk : ι → OpTabK ι, Tc i = some Tk → en.q ≠ .lin → ∀ z,
          (opTableK (fl z) (Tk z)).Down := by
        intro Tk hTk hq' z
        obtain ⟨-, -, -, hTkD⟩ := hTc x i en hT ha hq' Tk hTk
        exact opTableK_down (hTkD z)
      rw [hq x i en hT ha, kappaAt_tag]
      cases hqq : en.q with
      | unr =>
          refine erwpK_unfold_at hLout hk (hna ha k (by omega) ls' v
            ⟨kappa H K₁, by unfold kappa; exact .lam⟩ σ ⟨ρa, ρk, hcak, hA, ⟨hu, f, hf, ?_⟩, hstr⟩)
          intro y hy ls'' he k' hk'
          have hyI := hInvW x _ i en hT ha f y ρk hy
          refine ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' Tk hTk => ?_⟩
          · have h₁ := hcontIH y hyI k' hk' _ _ _
              ((hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ)
            simp only [erwpCK, show k' < n by omega, if_true] at h₁
            exact erwpK_kappa_resume (hΦ y hyI) (hDout y) hQout H K₁ w h₁
          · exact erwpK_kappa_cancel (hΦ y hyI) (hDk Tk hTk hq' y) (fun _ => unitPost_down) H K₁
              (hcan y hyI ρk ls'' he (hcont y hy ls'' he).2 hq' Tk hTk k' (by omega))
      | lin | cancel =>
          -- the cell is allocated, one step; `κ` is `kappaC` at it, owning the cell and the share
          refine erwpK_unfold_at hLout hk (erwpK_kappaCellV hLout (hΦ x hx) (hDout x) hQout _ H K₁
            (.appR (.val c) (.pairR v .hole)) (fun ℓ σ₁ σ₂ hcell hc₂ hv₂ => ?_))
          obtain ⟨y₀, hy₁, hy₂⟩ := compS_reassoc hcak hc₂
          have hvy : ResU.Valid y₀ := (ResU.Valid.split hy₂ hv₂).2
          have hy₀ : y₀.InStratum α := by
            refine inStratum_compS hy₁ hstr ?_
            rw [hcell]
            exact ResU.inStratum_single_own α ℓ Val.unit
          have hA' : en.PA (k - 1) ls' v ρa := by
            cases k with
            | zero => exact hA
            | succ k₀ => exact (hTinD x).pa _ _ _ hT _ _ _ _ hA
          refine hna ha (k - 1) (by omega) ls' v ⟨_, isVal_kappaC _ ℓ H K₁⟩ σ₂
            ⟨ρa, y₀, hy₂, hA', ⟨fun hq' => absurd (hqq.symm.trans hq') (by simp), f, hf, ?_⟩, hy₀⟩
          intro y hy ls'' he k' hk'
          have hyk : en.wk f y ρk := hwk x i en hT ha f y ρk σ₁ y₀ hy₁ hvy hy
          have hek : en.wc ls' ls'' ρk := hwcl x _ _ _ hT _ _ _ _ _ hy₁ he
          have hyI := hInvW x _ i en hT ha f y ρk hyk
          refine ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' Tk hTk => ?_⟩
          · obtain ⟨z, hz, hzτ⟩ := compS_exch hy₁ hcτ
            have h₁ := hcontIH y hyI k' (by omega) _ _ _
              ((hcont y hyk ls'' hek).1 k' (by omega) w τ₁ z hB hz)
            simp only [erwpCK, show k' < n by omega, if_true] at h₁
            exact erwpK_kappaC_resume hLout (hΦ y hyI) (hDout y) hQout _ ℓ H K₁ w
              ⟨σ₁, z, ResU.CompS.comm hzτ, hcell,
                erwpK_le (hΦ y hyI) hLout (hDout y) hQout (Nat.sub_le k' 1) h₁⟩
          · first
              | exact absurd hqq hq'
              | exact erwpK_kappaC_cancel (fun z => opTableK_local _ _) (hΦ y hyI)
                  (hDk Tk hTk hq' y)
                  (fun _ => unitPost_down) ℓ H K₁ ⟨σ₁, ρk, ResU.CompS.comm hy₁, hcell,
                    hcan y hyI ρk ls'' hek (hcont y hyk ls'' hek).2 hq' Tk hTk (k' - 1)
                      (by omega)⟩
    · -- an operation of another name passes outward, at the same entry and floor
      have hKo : ((hndK H).comp K₁).HasHnd m = false := by
        rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
      have ht' : (hndK H).plug (K₁.plug (performE (.val (opPayload m i v)))) =
          ((hndK H).comp K₁).plug (opE false (opPayload m i v)) := by
        rw [Kont.plug_comp]; rfl
      rw [ht']
      refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
        ⟨(hndK H).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, (hTin x m i hm) ▸ hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
            fun hq' => ?_⟩⟩⟩))
      · rw [Kont.plug_comp]
        exact hcontIH y (hInvW x m i en hT ha f y ρk hy) k' hk' _ _ _
          ((hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ)
      · intro P hP
        show P y k ls'' (((hndK H).comp K₁).dead.plug _) ρk
        rw [dead_comp, dead_hndK]
        exact (hcont y hy ls'' he).2 hq' P hP
  · -- a stop at an abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n₀
    · -- `[unwind]` at the handler's name: the clause; the continuation is discarded
      subst hm
      obtain ⟨c, hc, -, hab⟩ := hop x i en hT
      refine rwpG_det (hΦ x hx) (hPD _)
        (fun μ => step1Only_plug (Head.hunwind μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
      refine rwpG_garbage (rwpG_mono (fun _ _ _ _ ⟨τ₁, τ₂, hcτ, hq', hnτ⟩ =>
        ⟨τ₁, τ₂, hcτ, hnτ, hq'⟩) (rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) hcan
          (erwpK_unfold_at hLout hk (hab ha k (by omega) ls' v ρa hPA)) hnn))
    · -- an abortive operation of another name passes outward
      have hKo : ((hndK H).comp K₁).Catches m = false := by
        rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm
      have ht' : (hndK H).plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
          ((hndK H).comp K₁).plug (opE true (opPayload m i v)) := by
        rw [Kont.plug_comp]; rfl
      rw [ht']
      exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
        ⟨(hndK H).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, (hTin x m i hm) ▸ hT, ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))


/-- **A handler at the stratified table at `erwpK`** (`erwp_handleS`): `erwpK_handleS_le` at
`N = n`. -/
theorem erwpK_handleS {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    (α : Life) (Tin Tout : ι → OpTabK ι) (hTinD : ∀ x, (Tin x).Down)
    (hTout : ∀ x, (Tout x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (Tout y)).Le (opTableK (fl x) (Tout x)))
    (n₀ : UInt32) (hTin : ∀ x m i, m ≠ n₀ → Tin x m i = Tout x m i) (qs hr hs : Val)
    (Qin Qout : ι → PostN) (hQout : ∀ x, (Qout x).Down)
    (hq : ∀ x i en, Tin x n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hwcl : ∀ x m i en, Tin x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x i en, Tin x n₀ i = some en → en.abort = false → ∀ f y (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (Tc : UInt32 → Option (ι → OpTabK ι))
    (hTc : ∀ x i en, Tin x n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk,
      Tc i = some Tk → ∃ T₁ : ι → OpTabK ι,
        en.fin = some (fun y k ls e => erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z))
          (fun _ _ _ _ _ => False) y k ls e) ∧ (∀ z, (T₁ z).Sub (Tk z)) ∧ ∀ z, (Tk z).Down)
    (hVr : ∀ y, V y y)
    (hInvW : ∀ x m i en, Tin x m i = some en → en.abort = false → ∀ f y ρ, en.wk f y ρ → Inv y)
    (hInvC : ∀ i Tk, Tc i = some Tk → ∀ z m j en, Tk z m j = some en → en.abort = false →
      ∀ f y ρ, en.wk f y ρ → Inv y)
    (hret : ∀ x k ls v ρ, Qin x k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
        (.app (.val hr) (.val v)) ρ)
    (hop : ∀ x i en, Tin x n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ fun ρ => KapRelK (ℍ := ℍ) V Φ fl (fun z => opTableK (fl z) (Tout z)) Qout
          en (fl x) (Tc i) k ls κ ρ ∧ ρ.InStratum α) ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k ls v ρ, en.PA k ls v ρ →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x k ls
          (.app (.val c) (.val v)) ρ)) :
    ∀ n x, Inv x → ∀ ls e ρ,
      erwpK (ℍ := ℍ) V Φ (fun z => opTableKS (fl z) α (Tin z)) Qin x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x n ls
        (hndE (hndVal n₀ qs hr hs) e) ρ :=
  fun n => erwpK_handleS_le hVt hΦ hΦV α n Tin Tout hTinD hTout hTV n₀ hTin qs hr hs Qin Qout
    hQout hq hwcl hwk Tc hTc hVr hInvW hInvC (fun x k _ => hret x k)
    (fun x i en hT => by
      obtain ⟨c, hc, h₁, h₂⟩ := hop x i en hT
      exact ⟨c, hc, fun ha k _ => h₁ ha k, fun ha k _ => h₂ ha k⟩) n le_rfl

/-! ### At one world -/

/-- `erwp_handleS_le` from `erwpK_handleS_le`. -/
theorem erwp_handleS_le_of_K {Φ : LocFam} (hΦ : Φ.Down) (α : Life) (N : Nat) (Tin Tout : OpTabN)
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
  intro n hnN ls e ρ h
  rw [erwp_eq_erwpK_of (opTableKS_lift 0 α Tin) Φ _] at h
  rw [erwp_opTableN_eq_erwpK 0]
  refine erwpK_handleS_le (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (Inv := fun _ => True) (fun _ _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => 0)
    α N (fun _ => liftTabK Tin) (fun _ => liftTabK Tout) (fun _ => hTinD.liftK)
    (fun _ => hTout.liftK) (fun _ _ _ _ _ _ _ _ h => h) n₀ ?_ qs hr hs (fun _ => Qin)
    (fun _ => Qout) (fun _ => hQout) ?_ ?_ ?_ (fun i => (Tc i).map (fun T _ => liftTabK T)) ?_
    (fun _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_ ?_ n hnN () trivial ls e ρ h
  · intro _ m i hm
    simp only [liftTabK, hTin m i hm]
  · intro _ i en h₁ ha
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hq i en₀ h₀ ha
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hTinD.wcl m i en₀ h₀
  · intro _ i en h₁ _ _ _ _ _ _ _ _ _
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    trivial
  · intro _ i en h₁ ha hq' Tk hTk
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    cases hTc' : Tc i with
    | none => rw [hTc'] at hTk; cases hTk
    | some T₀ =>
        rw [hTc'] at hTk
        cases Option.some.inj hTk
        obtain ⟨T₁, hf, hsub, hTkD⟩ := hTc i en₀ h₀ ha hq' T₀ hTc'
        refine ⟨fun _ => liftTabK T₁, ?_, fun _ m j e he => ?_, fun _ => hTkD.liftK⟩
        · simp only [liftEntK, hf, Option.map_some]
          rw [cancelOblN_eq_K 0 Φ T₁]
        · obtain ⟨e₀, he₀, rfl⟩ := liftTabK_some he
          exact liftTabK_of_some (hsub m j e₀ he₀)
  · intro _ k hk ls' v ρ' hv
    have h' := hret k hk ls' v ρ' hv
    rw [erwp_opTableN_eq_erwpK 0] at h'
    exact h'
  · intro _ i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    obtain ⟨c, hc, h₁, h₂⟩ := hop i en₀ h₀
    refine ⟨c, hc, fun ha k hk ls' v κ ρ' hp => ?_, fun ha k hk ls' v ρ' hp => ?_⟩
    · obtain ⟨ρa, ρk, hcak, hA, hK, hs⟩ := hp
      have := h₁ ha k hk ls' v κ ρ' ⟨ρa, ρk, hcak, hA,
        (kapRelK_liftT_iff 0 Φ Tout Qout en₀ (Tc i) k ls' κ ρk).mp hK, hs⟩
      rw [erwp_opTableN_eq_erwpK 0] at this; exact this
    · have := h₂ ha k hk ls' v ρ' hp
      rw [erwp_opTableN_eq_erwpK 0] at this; exact this

/-- `erwp_handleS` from `erwp_handleS_le_of_K`. -/
theorem erwp_handleS_of_K {Φ : LocFam} (hΦ : Φ.Down) (α : Life) (Tin Tout : OpTabN)
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
  fun n => erwp_handleS_le_of_K hΦ α n Tin Tout hTinD hTout n₀ hTin qs hr hs Qin Qout hQout hq Tc
    hTc (fun k _ => hret k)
    (fun i en hT => by
      obtain ⟨c, hc, h₁, h₂⟩ := hop i en hT
      exact ⟨c, hc, fun ha k _ => h₁ ha k, fun ha k _ => h₂ ha k⟩) n le_rfl

end BoCa.Fig16.LogRel.Core.Chain.SI

end
