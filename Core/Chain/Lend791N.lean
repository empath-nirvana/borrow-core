import Core.Chain.Goal791N

/-!
# The suspending `mut` lend over the chain relation  `[spec §62]`

The frames a `mut` lend needs when its callback's row is `Row.Suspend`: every operation named,
none unrestricted, abortive ones (raises), must-resume ones and cancellable ones all allowed. The
chain relation has the Mut Frame across stops for raises with must-resume stops
(`erwp_M_frameR`, `SI/StopRaiseN.lean`) and for cancellable stops without raises
(`erwp_M_frameT`, `SI/StopCancelN.lean`); here they are one lemma, by the same strong induction
on the index, each case the existing one:

* `erwp_M_frameCR`: the Mut Frame across stops whose table may have abortive, must-resume and
  cancellable entries. At a return, 6.65; at a stop, the borrow folded into the continuation's
  share and lent again at the resume (`erwp_M_frame`'s case); at a cancellable stop the cancel
  obligation is the lender's (`hcan`, `erwp_M_frameT`'s case); at a `raise`, the borrow folded and
  the cell the claim the `raise` carries (`erwp_M_frameR`'s case). The lender's stops are at a
  twin table `T′`, its raises carrying the claim (`opTableR`).
* `claimT_canX`: the lender's cancel obligations, at a twin whose cancellable entries' obligation
  is the cancel run ending at the claim (`claimT_canS` with the twin given).
* `erwp_ubindClaimR`: the finaliser frame around a body at `opTableR (claimT T …) R`: `[then]` at
  a return; at a stop the frame passes outward (`erwp_ubindClaim`'s case, the cancel run through
  `erwp_ubind_cancelRun`); at a `raise`, `[finalise]` runs `D ()`, which consumes the claim
  (`erwp_ubindRaise`'s case).

Then the compatibility of `withbor (2)` at a suspending row (`withbor2S_compat`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE)

/-- **A table whose stops may be taken under a live `mut` lend at `A`, raises and cancellable
stops included**: every non-abortive entry not unrestricted and resumed under `extF`; what passes
out outlives `A`, what passes in holds nothing shorter. -/
structure OpTabN.LendOKCR (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum (↓A)

/-- **Mut Frame at `erwp` across stops: raises, must-resume and cancellable stops.** -/
theorem erwp_M_frameCR {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKCR A) (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL)
    {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableR T' (claimR l A F)) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq]
  refine rwpG_M_frameG hF hjn houtP houtb hPF hwit hclP hcρ ?_ (fun BM hBM => by
    have h := hA BM hBM
    rw [erwp_eq] at h
    exact h)
  intro k hk ls' t ρ' ρp X hQin hnoρp h9 hdX v'' χ hχ P'' hw'' hPk hsplit W'' hW'' Y hY
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hw'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hXl : X.get l = some (CellU.mutOf A v'' χ hχ P'' hw'') :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hsplit) (ResU.single_get_self _ _) hkm'').2
  rcases hQin with ⟨w, rfl, houtρ', hwand⟩ | ⟨K, m, i, v₀, en, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · -- a return: 6.65's end
    rcases ResU.CompS.get_split_of_ne_imm h9 hXl hkm'' with ⟨hg, -⟩ | ⟨-, hgp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hpd := ResU.del_compS hgp
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨ρp, hpd, h9⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨Z1, hZ1, hρ'Z1⟩ := (ResU.CompS.assoc ρ' (ρp.del l) W'' Y).mpr ⟨_, hD, hY⟩
    obtain ⟨R, hR, hRY⟩ :=
      (ResU.CompS.assoc ρ' W'' (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, hwand v'' y hy₁ χ (hPk v'' χ ⟨hχ, hw''⟩) R hy₂⟩⟩
  · -- a stop: the borrow folded into the continuation's share, lent again at the resume
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hq, hwc⟩ := hT.entry m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc'⟩ := hTT' m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc ρa ρk ρp X).mpr ⟨ρ', hcak, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨ρkL, hkL, haY⟩ := (ResU.CompS.assoc ρa (Z.del l) W'' Y).mpr ⟨_, hD, hY⟩
    have hdZd : (Z.del l).InStratum (↓A) :=
      ResU.CompS.inStratum_left hZd (ResU.CompS.inStratum_right haZ hdX)
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, ρkL, haY,
        hPA' ▸ hPA, fun hu' => absurd (hq'.symm.trans hu') hq, fun ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩)⟩
    · simp only [erwpC, show k' < n by omega, if_true]
      rw [hPB'] at hB
      obtain ⟨ρbB, hρbB, hWXB⟩ :=
        (ResU.CompS.assoc W'' (Z.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
      have hdB : ρbB.InStratum (↓A) :=
        inStratum_compS hρbB hdZd (hT.pb m i en hTe _ _ _ _ hB)
      refine ih k' (by omega) k (le_of_lt hk') ls'' _ v'' χ W'' ρbB XB hχ hdB P'' hPk hw''
        (ResU.CompS.comm hW'') hWXB (fun BM' hBM' => ?_)
      have he' : en.wc ls' ls'' ρk := by
        rw [hwc', hwc] at he; rw [hwc]
        exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW''
          hkL he
      obtain ⟨s1, hs1, hZds1⟩ := (ResU.CompS.assoc (Z.del l) σB
        (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) BM').mpr ⟨ρbB, hρbB, hBM'⟩
      obtain ⟨Z', hZ', hZ'σ⟩ := (ResU.CompS.assoc (Z.del l)
        (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) σB BM').mp
          ⟨s1, ResU.CompS.comm hs1, hZds1⟩
      obtain rfl : Z = Z' := ResU.CompS.functional hZd hZ'
      obtain ⟨s2, hs2, hks2⟩ := (ResU.CompS.assoc ρk ρp σB BM').mpr ⟨Z, hZ, hZ'σ⟩
      obtain ⟨Xk, hXk, hXkp⟩ :=
        (ResU.CompS.assoc ρk σB ρp BM').mp ⟨s2, ResU.CompS.comm hs2, hks2⟩
      have hc := (hcont ls'' he').1 k' hk' w σB Xk hB hXk
      simp only [erwpC, show k' < n by omega, if_true] at hc
      exact erwp_garbage hXkp hnoρp hc
    · have he' : en.wc ls' ls'' ρk := by
        rw [hwc', hwc] at he; rw [hwc]
        exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW''
          hkL he
      have hql' : en.q ≠ .lin := hq' ▸ hql
      exact hcan m i en en' hTe hTe' ha hql' k ls'' K ρk ρp Z ρkL W'' v'' χ hχ P'' hw'' hnoρp hZ
        hZd hdZd hPk hW'' hkL ((hcont ls'' he').2 hql')
  · -- a `raise`: the borrow folded, the cell the claim the `raise` carries
    obtain ⟨⟨rfl, hK, hTe, ha⟩, τa, τn, hcan', ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hTe', -, hab', hPA', -, -⟩ := hTT' m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc τa τn ρp X).mpr ⟨ρ', hcan', h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc τa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    have hnoZ : NoOwn Z := noOwn_compS hZ hnn hnoρp
    obtain ⟨hs, hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨X.del l, W'', hY,
        ⟨τa, Z.del l, hD, ⟨hPA' ▸ hPA, hnA⟩, noOwn_del hnoZ l⟩,
        v'', χ, hs, hFk, ResU.CompS.comm hW''⟩⟩)⟩

/-- **The lender's cancel obligations at a twin whose cancellable entries end at the claim**
(`claimT_canS` with the twin `T′` given): the borrowed run's cancel run at its own location
typing `Φ[ℓ ↦ (A, F)]`, framed by `erwp_M_frame_cancelRun`. -/
theorem claimT_canX {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T T' T₁ : OpTabN} (hT₁ : T₁.LendOK A) (hTT' : T.Twin T')
    (hfin : ∀ m i en, T m i = some en → en.abort = false → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) (Φ.set l A F) T₁))
    (hq : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr)
    (hT' : ∀ m i en', T' m i = some en' → en'.q = .cancel →
      en'.fin = some (@cancelOblRN ℍ _ Φ T₁ (claimR l A F))) :
    ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false → en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL := by
  intro m i en en' hT hT'' ha hql k ls K ρk ρp Z ρkL W'' v'' χ hχ P'' hw'' hno hZ hZd hdZd hPk
    hW'' hkL hc
  have hqc : en.q = .cancel := by
    have := hq m i en hT ha
    cases h : en.q <;> simp_all
  obtain ⟨en₂, hT₂, hq₂, -⟩ := hTT' m i en hT
  rw [hT''] at hT₂
  cases Option.some.inj hT₂
  intro P' hP'
  rw [hT' m i en' hT'' (hq₂.trans hqc)] at hP'
  cases hP'
  have hin := hc _ (hfin m i en hT ha hqc)
  refine erwp_M_frame_cancelRun hF hT₁ k k le_rfl ls _ v'' χ W'' (Z.del l) ρkL hχ hdZd P'' hPk
    hw'' (ResU.CompS.comm hW'') (ResU.CompS.comm hkL) (fun BM hBM => ?_)
  obtain rfl := ResU.CompS.functional hBM hZd
  exact erwp_garbage hZ hno hin

/-- **The finaliser frame around a body at `opTableR (claimT T …) R`**: the body's cancel runs
and its raises both end carrying `R`, which `D` consumes. -/
theorem erwp_ubindClaimR {Φ : LocFam} (hΦ : Φ.Down) {T T₁ : OpTabN} (hTD : T.Down)
    (hT₁ : T₁.Down) (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin)
    (hTe : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr)
    (hTr : ∀ m i en, T m i = some en → en.abort = true → m ≠ 0)
    (hPAls : ∀ m i en, T m i = some en → ∀ k ls ls' v ρ, (∀ x, x ∈ ls' ↔ x ∈ ls) →
      en.PA k ls v ρ → en.PA k ls' v ρ)
    (hfin : ∀ m i en, T m i = some en → en.abort = false → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁))
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ → rwp (ℍ := ℍ) Φ (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout k ls (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) Φ (opTableR (@OpTabN.claimT ℍ _ T Φ T₁ R) R) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout n ls (ubindE (.pair N D) M) ρ := by
  have hL := opTableR_local (@OpTabN.claimT ℍ _ T Φ T₁ R) R
  have hPD := erwpPost_down (opTableN_down hTD) hQout
  have hD' : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) Φ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ :=
    fun k ls ρ h => rwp_mono (fun _ _ _ _ h => h.2) (hD k ls ρ h)
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
  · -- a stop passes the frame; a cancellable one's cancel run through the frame
    obtain ⟨⟨rfl, hK₁, hT', ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
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
      · rw [hfin m i en hT ha hqc] at hP
        cases hP
        have hql : en.q ≠ .lin := by rw [hqc]; simp
        have hin := (hcont ls'' he).2 hql _ rfl
        show erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) k ls''
          (((ubK N D).comp K₁).dead.plug _) ρk
        rw [dead_comp, ubK_dead, Kont.plug_comp]
        exact erwp_ubind_cancelRun hΦ hT₁ hT₁e N D hD' k ls'' _ ρk hin
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
        have := hTe m i en hT ha
        cases h : en.q <;> simp_all
  · -- `[finalise]`: `D (); raise p`, `D` consuming the claim
    obtain ⟨⟨rfl, hK₁, hT', ha⟩, σ₁, ρR, hcσ, ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩, hR⟩ :=
      pure_sep_iff.mp hp
    obtain ⟨en, hT, rfl⟩ := claimT_some hT'
    have hab : en.abort = true := by
      by_cases hqc : en.q = .cancel
      · rw [if_pos hqc] at ha; exact ha
      · rw [if_neg hqc] at ha; exact ha
    have hPAe : en.PA k ls' v ρa := by
      by_cases hqc : en.q = .cancel
      · rw [if_pos hqc] at hPA; exact hPA
      · rw [if_neg hqc] at hPA; exact hPA
    have hm0 := hTr m i en hT hab
    refine rwpG_det hΦ (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    refine rwpG_bind hΦ _ ?_
    have hDr := rwpG_frame
      (fun ls₀ τ => (∀ x, x ∈ ls₀ ↔ x ∈ ls') ∧
        ((fun ρ => en.PA k ls' v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ)
      (fun _ _ hs _ ⟨h₁, h₂⟩ => ⟨fun x => (hs x).trans (h₁ x), h₂⟩) (ResU.CompS.comm hcσ)
      (rwp_iff_rwpG.mp (hD k ls' ρR hR)) ⟨fun _ => Iff.rfl, ρa, ρn, hcan, ⟨hPAe, hnA⟩, hnn⟩
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ', ⟨w, rfl, rfl, rfl⟩, hls₂, ⟨τa, τn, hcτ, ⟨hPAτ, hnτ⟩, hnn'⟩⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ'
    refine rwpG_det hΦ (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).2.2) ?_
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload m i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, m, i, v, en,
        pure_sep_mk ⟨rfl, rfl, hT, hab⟩ ⟨τa, τn, hcτ, ⟨hTD.pa_le hT hk₂
          (hPAls _ _ _ hT _ _ _ _ _ hls₂ hPAτ), hnτ⟩, hnn'⟩⟩))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
