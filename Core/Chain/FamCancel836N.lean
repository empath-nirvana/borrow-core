import Core.Chain.FamStop836N
import Core.Chain.Unwind833N

/-!
# The `n`-cell Mut Frame across stops and layered cancel runs, and `slice_borrow_mut` at a
suspending row  `[spec §9, §19, §62]`

Core's `sliceBorrowMU_compatX` (`Core/EffBorrow.lean`) nests one Mut Frame per cell of the source
array (`wpG_M_frameFam`, `wpG_M_frameList`, `Core/SliceFrames.lean`) around a callback whose row
may stop. On the chain the one-cell frame across stops, raises and layered cancel runs is
`erwp_M_frameCR` with `erwp_M_frame_cancelRunCR` (`Core/Chain/Lend791N.lean`,
`Core/Chain/Cancel791N.lean`): the callback's table `tabN₀`, the lender's its twin `tabR` at the
lend's claim. Nested, the callback of frame `j` is the run of frames `j+1 … n`, already at a
`tabR` whose raises and cancel runs end at the inner frames' claims. So the one-cell frame is
restated at an incoming claim `R`:

* `erwp_M_frameCRR`, `erwp_M_frame_cancelRunCRR`: `erwp_M_frameCR` and
  `erwp_M_frame_cancelRunCR` with the callback's raises and cancel runs at `opTableR T R`,
  `cancelTabR T R`; at a raise the lent cell's claim joins `R` (`erwp_M_frameRR`'s case).
* `tabR_tabR_twinW`, `tabR_lendOKCR_C`, `tabR_canR`: `tabN_tabR_twin`, `tabN_lendOKCR_C` and
  `tabR_can` with the callback's table `tabR R` at the lend's world.
* `tabR_le`, `tabN_tabR_le`: `tabR` monotone in the claim, and the callback's own `tabN₀` below
  `tabR` at an empty claim (`OpTabN.Le`); `erwp_opTableR_le` and `erwp_opTableN_R` carry runs
  along them.
* `erwp_M_frameListCRN`: Core's `wpG_M_frameList` across stops, raises and layered cancel runs,
  the list induction over `erwp_M_frameCRR`; the composite claim is the cells owned again
  (`claimL₀`), the `Array A` the finaliser `d` takes.
* `sliceBorrowMS_compat₀`, `constN_sm₀`, `sliceBorrowMS_inst₀`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE)

/-! ### Tables along `OpTabN.Le`, with raises carrying a claim -/

/-- A stop of `performStopN T` is one of `performStopN T′` when `T ≤ T′`. -/
theorem performStopN_le {T T' : OpTabN} (hT : T.Le T') :
    ∀ k ls t (Ψ Ψ' : ContN) ρ, (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
      performStopN T k ls t Ψ ρ → performStopN T' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ ⟨K, n, i, v, en, hp⟩
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨en', h₃', hq, hab, hPA, hPB, hwc, hfl⟩ := hT n i en h₃
  refine ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩ ⟨ρa, ρk, hc, hPA ▸ hA,
    fun hu' => hu (hq.trans hu'), fun ls' he => ?_⟩⟩
  rw [← hwc] at he
  refine ⟨fun k' hk' w σ₁ σ₂ hB hcσ => ?_, fun hq' P hP => ?_⟩
  · rw [← hPB] at hB
    exact hΨ k' hk' _ _ _ ((hcont ls' he).1 k' hk' w σ₁ σ₂ hB hcσ)
  · exact finLeSN_apply (hfl h₄ (hq ▸ hq')) hP (fun P₀ hP₀ => (hcont ls' he).2 (hq ▸ hq') P₀ hP₀)

/-- An error payload at a table above. -/
theorem errOkN_le {T T' : OpTabN} (hT : T.Le T') :
    ∀ {k : Nat} {ls : List SRec} {err : Option Val} {ρ : WRes}, errOkN T k ls err ρ →
      errOkN T' k ls err ρ
  | _, _, none, _, h => h
  | _, _, some _, _, h => by
      obtain ⟨m, j, w, en, he⟩ := h
      obtain ⟨⟨hE, hTe, ha⟩, hPA, hn⟩ := pure_sep_iff.mp he
      obtain ⟨en', hTe', -, hab', hPA', -⟩ := hT m j en hTe
      exact ⟨m, j, w, en', pure_sep_mk ⟨hE, hTe', hab' ▸ ha⟩ ⟨hPA' ▸ hPA, hn⟩⟩

/-- **`erwp` at `opTableR` widened along `OpTabN.Le` and a weaker claim.** -/
theorem erwp_opTableR_le {Φ : LocFam} {T T' : OpTabN} (hT : T.Le T') {R R' : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → R' k ρ) {Q : PostN} :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableR T R) Q n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableR T' R') Q n ls e ρ := by
  refine erwp_mono (fun _ _ _ _ h => h) fun k ls t Ψ Ψ' ρ hΨ h => ?_
  rcases h with h | ⟨K, n, i, v, en, hp⟩
  · exact Or.inl (performStopN_le hT k ls t Ψ Ψ' ρ hΨ h)
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρ₁, ρ₂, hc, ⟨ρa, ρn, hcn, ⟨hPA, hnA⟩, hnn⟩, hRk⟩ :=
      pure_sep_iff.mp hp
    obtain ⟨en', h₃', -, hab, hPA', -⟩ := hT n i en h₃
    exact Or.inr ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩
      ⟨ρ₁, ρ₂, hc, ⟨ρa, ρn, hcn, ⟨hPA' ▸ hPA, hnA⟩, hnn⟩, hR _ _ hRk⟩⟩

/-- **A cancel run at `cancelTabR` widened along `OpTabN.Le` and a weaker claim.** -/
theorem erwp_cancelTabR_le {Φ : LocFam} {T T' : OpTabN} (hT : T.Le T') {R R' : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → R' k ρ) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (cancelTabR T R) (fun _ _ _ _ => False) n ls e ρ →
      erwp (ℍ := ℍ) Φ (cancelTabR T' R') (fun _ _ _ _ => False) n ls e ρ := by
  refine erwp_mono (fun _ _ _ _ h => h) fun k ls t Ψ Ψ' ρ hΨ h => ?_
  rcases h with ⟨K, err, hp⟩ | h
  · obtain ⟨hc, y1, y2, hy, ⟨τa, τb, hcab, herr, hnb⟩, hRk⟩ := pure_sep_iff.mp hp
    exact Or.inl ⟨K, err, pure_sep_mk hc ⟨y1, y2, hy, ⟨τa, τb, hcab, errOkN_le hT herr, hnb⟩,
      hR _ _ hRk⟩⟩
  · exact Or.inr (performStopN_le hT k ls t Ψ Ψ' ρ hΨ h)

/-- **`erwp` at `opTableN T` is one at `opTableR T′ R₀`** when `T ≤ T′` and `R₀` holds of `∅`:
the raises carry the empty claim. -/
theorem erwp_opTableN_R {Φ : LocFam} {T T' : OpTabN} (hT : T.Le T') {R₀ : Nat → WProp}
    (hR₀ : ∀ k, R₀ k PMap.empty) {Q : PostN} :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableR T' R₀) Q n ls e ρ := by
  refine erwp_mono (fun _ _ _ _ h => h) fun k ls t Ψ Ψ' ρ hΨ h => ?_
  rcases h with h | ⟨K, n, i, v, en, hp⟩
  · exact Or.inl (performStopN_le hT k ls t Ψ Ψ' ρ hΨ h)
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρn, hcn, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨en', h₃', -, hab, hPA', -⟩ := hT n i en h₃
    exact Or.inr ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩
      ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨ρa, ρn, hcn, ⟨hPA' ▸ hPA, hnA⟩, hnn⟩, hR₀ k⟩⟩

/-- **A cancel run at `cancelTabN T` is one at `cancelTabR T′ R₀`** when `T ≤ T′` and `R₀` holds
of `∅`. -/
theorem erwp_cancelTabN_R {Φ : LocFam} {T T' : OpTabN} (hT : T.Le T') {R₀ : Nat → WProp}
    (hR₀ : ∀ k, R₀ k PMap.empty) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (cancelTabN T) (fun _ _ _ _ => False) n ls e ρ →
      erwp (ℍ := ℍ) Φ (cancelTabR T' R₀) (fun _ _ _ _ => False) n ls e ρ := by
  refine erwp_mono (fun _ _ _ _ h => h) fun k ls t Ψ Ψ' ρ hΨ h => ?_
  rcases h with ⟨K, err, hp⟩ | h
  · obtain ⟨hc, τa, τb, hcab, herr, hnb⟩ := pure_sep_iff.mp hp
    exact Or.inl ⟨K, err, pure_sep_mk hc ⟨ρ, PMap.empty, ResU.comp_empty_right ρ,
      ⟨τa, τb, hcab, errOkN_le hT herr, hnb⟩, hR₀ k⟩⟩
  · exact Or.inr (performStopN_le hT k ls t Ψ Ψ' ρ hΨ h)

/-! ### The one-cell frame at an incoming claim -/

/-- **`erwp_M_frameCR` at an incoming claim**: the callback's raises at `opTableR T R`, the
claims of the frames inside it. At a `raise` the borrow is folded and the lent cell's claim joins
`R` (`erwp_M_frameRR`'s case); `R` lies in the lend's stratum (`hR`), so the lent cell is not in
it. Its returns and stops are `erwp_M_frameCR`'s cases. -/
theorem erwp_M_frameCRR {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
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
    {R : Nat → WProp} (hR : ∀ k ρ, R k ρ → ρ.InStratum A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableR T R) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableR T' (fun k => claimR l A F k ⋆ R k)) Q n ls e ρ := by
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
  · -- a `raise`: the borrow folded, the cell's claim joining the one the `raise` carries
    obtain ⟨⟨rfl, hK, hTe, ha⟩, τ0, τR, hc0R, ⟨τa, τn, hcan', ⟨hPA, hnA⟩, hnn⟩, hRk⟩ :=
      pure_sep_iff.mp hp
    obtain ⟨en', hTe', -, hab', hPA', -, -⟩ := hTT' m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨t1, ht1, hρ't1⟩ := compS_exch hcan' hc0R
    have hρa' : t1.InStratum A := inStratum_compS ht1 hρa (hR _ _ hRk)
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc t1 τn ρp X).mpr ⟨ρ', hρ't1, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc t1 (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    have hnoZ : NoOwn Z := noOwn_compS hZ hnn hnoρp
    obtain ⟨hs, hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
    obtain ⟨s0, hs0, hXd⟩ := compS_exch ht1 hD
    obtain ⟨s1, hs1, hYs⟩ := compS_reassoc hXd hY
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨s0, s1, hYs,
        ⟨τa, Z.del l, hs0, ⟨hPA' ▸ hPA, hnA⟩, noOwn_del hnoZ l⟩,
        ⟨W'', τR, ResU.CompS.comm hs1, ⟨v'', χ, hs, hFk, ResU.CompS.comm hW''⟩, hRk⟩⟩⟩)⟩

/-- **`erwp_M_frame_cancelRunCR` at an incoming claim**: the callback's cancel run at
`cancelTabR T R`; at the cancel's `raise` the lent cell's claim joins `R`. -/
theorem erwp_M_frame_cancelRunCRR {Φ : LocFam} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKCR A)
    (hTT' : T.Twin T')
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
    {R : Nat → WProp} (hR : ∀ k ρ, R k ρ → ρ.InStratum A) :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (cancelTabR T R) (fun _ _ _ _ => False) n ls e BM) →
      erwp (ℍ := ℍ) Φ (cancelTabR T' (fun k => claimR l A F k ⋆ R k)) (fun _ _ _ _ => False) n ls e ρ := by
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
  rcases hQin with ⟨w, -, hf⟩ | ⟨K, err, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · exact hf.elim
  · -- the cancel's `raise`: the borrow folded, the cell's claim joining the one it carries
    obtain ⟨⟨rfl, hK⟩, τ0, τR, hc0R, ⟨τa, τn, hcan', herr, hnn⟩, hRk⟩ := pure_sep_iff.mp hp
    have hρa := errOkN_inStratum hT.pa herr
    obtain ⟨t1, ht1, hρ't1⟩ := compS_exch hcan' hc0R
    have hρa' : t1.InStratum A := inStratum_compS ht1 hρa (hR _ _ hRk)
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc t1 τn ρp X).mpr ⟨ρ', hρ't1, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc t1 (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    have hnoZ : NoOwn Z := noOwn_compS hZ hnn hnoρp
    obtain ⟨hs, hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
    obtain ⟨s0, hs0, hXd⟩ := compS_exch ht1 hD
    obtain ⟨s1, hs1, hYs⟩ := compS_reassoc hXd hY
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, err, pure_sep_mk ⟨rfl, hK⟩ ⟨s0, s1, hYs,
        ⟨τa, Z.del l, hs0, errOkN_twin hTT' herr, noOwn_del hnoZ l⟩,
        ⟨W'', τR, ResU.CompS.comm hs1, ⟨v'', χ, hs, hFk, ResU.CompS.comm hW''⟩, hRk⟩⟩⟩)⟩
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
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
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

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC interp_top_of_defines_empty
  defines_meetOfDom_empty)
open BoCa.BoLo (Heap Kont ubindE Head performE raiseE cancelVal opPayload)

/-! ### The lender's twin at an incoming claim -/

/-! ### The `n`-cell Mut Frame across stops and layered cancel runs -/

/-! ### `slice_borrow_mut` at a suspending row -/

/-- `withborU`'s `then` at the source `a`: `λb. (a, b)`. -/
def NFa (a : Val) : Val := Val.lam (.pair (.val a) (.var 0))

/-- `withborU`'s `unwind` at the source `a`: `λ_. d a`. -/
def DFa (d : Expr) (a : Val) : Val := Val.lam (.app d (.val a))

/-! ### `slice_borrow_mut` at an unwinding row -/

/-! ### `slice_borrow_mut` at the hardest case's row -/

/-- `λu. ()`. -/
def dropU : Val := Val.lam (.val .unit)

/-- `λa. drop (λu. (), a)`: the source array's cells freed. -/
def dArrFree : Expr := .val (Val.lam (.app (.val (.prim .drop)) (.pair (.val dropU) (.var 0))))

theorem dArrFree_closed : closedAt 0 dArrFree = true := by decide

/-! ### Every constant -/

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
