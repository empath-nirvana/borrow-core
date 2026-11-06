import Core.Chain.FamStop836N

/-!
# The `n`-cell Mut Frame across stops and layered cancel runs, and `slice_borrow_mut` at a
suspending row  `[spec §9, §19, §62]`

Core's `sliceBorrowMU_compatX` (`Core/EffBorrow.lean`) nests one Mut Frame per cell of the source
array (`wpG_M_frameFam`, `wpG_M_frameList`, `Core/SliceFrames.lean`) around a callback whose row
may stop. On the chain the one-cell frame across stops, raises and layered cancel runs is
`erwp_M_frameCR` with `erwp_M_frame_cancelRunCR` (`Core/Chain/Lend791N.lean`,
`Core/Chain/Cancel791N.lean`): the callback's table `tabN`, the lender's its twin `tabR` at the
lend's claim. Nested, the callback of frame `j` is the run of frames `j+1 … n`, already at a
`tabR` whose raises and cancel runs end at the inner frames' claims. So the one-cell frame is
restated at an incoming claim `R`:

* `erwp_M_frameCRR`, `erwp_M_frame_cancelRunCRR`: `erwp_M_frameCR` and
  `erwp_M_frame_cancelRunCR` with the callback's raises and cancel runs at `opTableR T R`,
  `cancelTabR T R`; at a raise the lent cell's claim joins `R` (`erwp_M_frameRR`'s case).
* `tabR_tabR_twinW`, `tabR_lendOKCR_C`, `tabR_canR`: `tabN_tabR_twin`, `tabN_lendOKCR_C` and
  `tabR_can` with the callback's table `tabR R` at the lend's world.
* `tabR_le`, `tabN_tabR_le`: `tabR` monotone in the claim, and the callback's own `tabN` below
  `tabR` at an empty claim (`OpTabN.Le`); `erwp_opTableR_le` and `erwp_opTableN_R` carry runs
  along them.
* `erwp_M_frameListCRN`: Core's `wpG_M_frameList` across stops, raises and layered cancel runs,
  the list induction over `erwp_M_frameCRR`; the composite claim is the cells owned again
  (`claimL`), the `Array A` the finaliser `d` takes.
* `sliceBorrowMS_compat`, `constN_sm`, `sliceBorrowMS_inst`.
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
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC interp_top_of_defines_empty)
open BoCa.BoLo (Heap Kont ubindE Head performE raiseE cancelVal opPayload)

/-! ### The lender's twin at an incoming claim -/

/-- **An entry of `tabR` is a layer's, and every `tabR`, at every claim and world, has the
layer's entry at the same key.** -/
theorem tab_lookupRW (R : Nat → WProp) : ∀ (F : CTy) {δ₂ : LSub} {Θ₂ : LocTy}
    {c₂ : Loc → Option Life} {m j : UInt32} {en : OpEntN},
    tabR (ℍ := ℍ) R F δ₂ Θ₂ c₂ m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₂ Θ₂ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) B δ₂ Θ₂ k v ρ) (finR (ℍ := ℍ) R fin δ₂ Θ₂ c₂) ∧
      ∀ (R' : Nat → WProp) (δ₃ : LSub) (Θ₃ : LocTy) (c₃ : Loc → Option Life),
        tabR (ℍ := ℍ) R' F δ₃ Θ₃ c₃ m j =
          some (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₃ Θ₃ k v ρ)
            (fun k v ρ => vN (ℍ := ℍ) B δ₃ Θ₃ k v ρ) (finR (ℍ := ℍ) R' fin δ₃ Θ₃ c₃))
  | .eff m₀ i₀ q A B fin rc C, δ₂, Θ₂, c₂, m, j, en, h => by
      simp only [tabR] at h
      unfold extTabN at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R' δ₃ Θ₃ c₃ => by
          simp only [tabR, extTabN, if_pos hmj]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR'⟩ := tab_lookupRW R C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R' δ₃ Θ₃ c₃ => by
          simp only [tabR, extTabN, if_neg hmj]; exact hR' R' δ₃ Θ₃ c₃⟩
  | .ret _, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .arr _ _, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .amp _ _, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .top, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .all _ _ _, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .nu _, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h

/-- **The lender's twins at two worlds and claims agree but for the cancel obligations**: the
layers' types, outliving the bound, read alike at the two worlds (`hΘ`). `tabN_tabR_twin` with
the callback's table a `tabR`. -/
theorem tabR_tabR_twinW {x : LifeVar} {bnd : Lifetime.Life} {F : CTy}
    (hF : F.SuspendC x bnd) (R R' : Nat → WProp) (δ : LSub) (Θ₁ Θ₂ : LocTy)
    (c₁ c₂ : Loc → Option Life)
    (hΘ : ∀ A : VTy, VOutlives LifeCtx.empty bnd A → vN (ℍ := ℍ) A δ Θ₁ = vN (ℍ := ℍ) A δ Θ₂) :
    (tabR (ℍ := ℍ) R F δ Θ₁ c₁).Twin (tabR (ℍ := ℍ) R' F δ Θ₂ c₂) := by
  intro m i en h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupRW R F h
  obtain ⟨-, -, -, hOA, hOB, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR R' δ Θ₂ c₂, rfl, rfl, ?_, ?_, rfl⟩
  · simp only [entN, hΘ A hOA]
  · simp only [entN, hΘ B hOB]

/-- **The lender's twin of a row meeting `CTy.SuspendC` may be stopped at under a lend at
`α ⊏ @bnd`** (`tabN_lendOKCR_C` at `tabR`). -/
theorem tabR_lendOKCR_C {x : LifeVar} {bnd : Lifetime.Life} {α : Life} {F : CTy}
    (hF : F.SuspendC x bnd) (R : Nat → WProp) (δ : LSub) (hLt : LtLife δ bnd α)
    (Θ : LocTy) (c : Loc → Option Life) : (tabR (ℍ := ℍ) R F δ Θ c).LendOKCR α where
  entry := fun m i en h _ => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupRW R F h
    exact ⟨(layer_suspend F hF hL).1, rfl⟩
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupRW R F h
    obtain ⟨-, -, -, hOA, -⟩ := layer_suspend F hF hL
    exact vN_inStratum_bnd hOA hLt hp
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupRW R F h
    obtain ⟨-, -, -, -, hOB, -⟩ := layer_suspend F hF hL
    exact (vN_inStratum_bnd hOB hLt hp).mono (Life.down_sqsubset α).le

/-- **`tabR` is monotone in its claim**: at a weaker claim every cancel run, at every depth,
ends at the weaker claim. -/
theorem tabR_le {R R' : Nat → WProp} (hR : ∀ k ρ, R k ρ → R' k ρ) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → (tabR (ℍ := ℍ) R F δ Θ c).Le (tabR (ℍ := ℍ) R' F δ Θ c) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro F hd m i en h
  obtain ⟨q, A, B, fin, hL, rfl, hR'⟩ := tab_lookupRW R F h
  refine ⟨_, hR' R' δ Θ c, rfl, rfl, rfl, rfl, rfl, fun _ _ => ?_⟩
  simp only [entN]
  by_cases hcap : capB q B = true
  · rw [if_pos hcap, if_pos hcap]
    by_cases htop : fin = .top
    · subst htop; simp [finR, FinLeSN]
    rw [finR_eq _ htop, finR_eq _ htop]
    intro k ls e ρ h'
    have hfd := layer_cdepth F hL
    exact erwp_cancelTabR_le (ih fin.cdepth (by omega) fin le_rfl) hR k ls e ρ h'
  · rw [if_neg hcap, if_neg hcap]; trivial

/-- **The callback's table lies below the lender's twin at the same world and an empty claim**:
the callback's `'x` is read by no layer's types, and every cancel run at the callback's
`cancelTabN` is one at `cancelTabR` ending at a claim holding of `∅`. -/
theorem tabN_tabR_le {x : LifeVar} {bnd : Lifetime.Life} {α : Life} {R₀ : Nat → WProp}
    (hR₀ : ∀ k, R₀ k PMap.empty) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC x bnd →
      (tabN (ℍ := ℍ) F (δ.extend x α) Θ c).Le (tabR (ℍ := ℍ) R₀ F δ Θ c) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro F hd hF m i en h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupN F h
  obtain ⟨-, hA, hB, -, -, hfinS⟩ := layer_suspend F hF hL
  refine ⟨_, hR R₀ δ Θ c, rfl, rfl, ?_, ?_, rfl, fun _ _ => ?_⟩
  · simp only [entN, vN_extend_of_not_free (ℍ := ℍ) hA δ α]
  · simp only [entN, vN_extend_of_not_free (ℍ := ℍ) hB δ α]
  · simp only [entN]
    by_cases hcap : capB q B = true
    · rw [if_pos hcap, if_pos hcap]
      have hfS := hfinS hcap
      by_cases htop : fin = .top
      · subst htop; simp [finR, finN, FinLeSN]
      rw [finR_eq _ htop, finN_eq htop]
      intro k ls e ρ h'
      have hfd := layer_cdepth F hL
      exact erwp_cancelTabN_R (ih fin.cdepth (by omega) fin le_rfl hfS) hR₀ k ls e ρ h'
    · rw [if_neg hcap, if_neg hcap]; trivial

/-- **The lender's cancel obligations from the callback's, at an incoming claim** (`tabR_can`
with the callback's table `tabR R` at the lend's world): at a capturable entry the callback's
cancel run at its cancel row's `tabR R`, framed by `erwp_M_frame_cancelRunCRR`, its own nested
cancel obligations by the induction on how deep cancel rows nest. -/
theorem tabR_canR {x : LifeVar} {bnd : Lifetime.Life} {α : Life} {δ : LSub} {Θ : LocTy}
    (hf : Θ.Fresh α) (hLt : LtLife δ bnd α) {c : Loc → Option Life} {l : Loc}
    {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam) {R : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → ρ.InStratum α) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC x bnd →
    ∀ m i en en', tabR (ℍ := ℍ) R F δ (Θ.add l α Fam) (setLife c l α) m i = some en →
      tabR (ℍ := ℍ) (fun k => claimR l α Fam k ⋆ R k) F δ Θ c m i = some en' →
      en.abort = false → en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum α)
        (P'' : Val → SPropS Loc Val α) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf α v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓α) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (Fam k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL := by
  intro d
  induction d with
  | zero =>
      intro F hd hF m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupRW R F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF m i en en' h h' ha hql k ls K ρk ρp Z ρkL W'' v'' χ hχ P'' hw'' hno hZ hZd hdZd
    hPk hW'' hkL hc
  obtain ⟨q, A, B, fin, hL, rfl, hR'⟩ := tab_lookupRW R F h
  rw [hR'] at h'
  cases Option.some.inj h'
  have hcap := entN_capB ha hql
  have hfin := (layer_suspend F hF hL).2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  intro P' hP'
  simp only [entN, hcap, if_true] at hP' hc
  by_cases htop : fin = .top
  · subst htop; simp [finR] at hP'
  rw [finR_eq _ htop] at hP'
  cases Option.some.inj hP'
  have hin := hc _ (finR_eq _ htop _ _ _)
  refine erwp_M_frame_cancelRunCRR (Φ := Θ.view c) hFam
    (tabR_lendOKCR_C hfin R δ hLt (Θ.add l α Fam) (setLife c l α))
    (tabR_tabR_twinW hfin R _ δ (Θ.add l α Fam) Θ (setLife c l α) c
      (fun A' hO => vN_add_eq_bnd hO δ hLt hf l Fam))
    (ih fin hfd hfin) hR k k le_rfl ls _ v'' χ W'' (Z.del l) ρkL hχ hdZd P'' hPk hw''
    (ResU.CompS.comm hW'') (ResU.CompS.comm hkL) (fun BM hBM => ?_)
  obtain rfl := ResU.CompS.functional hBM hZd
  rw [← LocTy.view_add]
  exact erwp_garbage hZ hno hin

/-! ### The `n`-cell Mut Frame across stops and layered cancel runs -/

/-- **The composite claim of a family's frames**: the cells owned again, each holding a member of
`A` at the world `Θ`. It is the source array's range, which the finaliser `d : Array A ⊸ 1`
takes. -/
def claimL (A : VTy) (δ : LSub) (Θ : LocTy) (I : List Loc) : Nat → WProp :=
  fun k => sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I

/-- **One Mut Frame per place, around one expression, across stops, raises and layered cancel
runs** (Core's `wpG_M_frameList`, the frames of `sliceBorrowMU_compatX`), at the chain: the list
induction over `erwp_M_frameCRR`, each frame its own key in the world, as `rwp_M_frameListN`.

Frame `j` lends its leaf at `αⱼ` fresh for the world the frames before it reached and below the
bound, so the row's types read alike at the two worlds (`vN_add_eq_bnd`). The callback of
frame `j` is the run of frames `j+1 … n`, at the lender's twin `tabR` of the row at the world with
`αⱼ`, its raises and cancel runs ending at the inner frames' composite claim (`claimL`, at that
world); frame `j`'s claim joins it (`erwp_M_frameCRR`, `tabR_canR`), and the cells it claims are
moved to the world without `αⱼ` by `vN_local`, their contents in `αⱼ`'s stratum (`tabR_le`). The
innermost callback runs at the lender's twin at the empty claim, `claimL … []`. -/
theorem erwp_M_frameListCRN {A : VTy} {δ : LSub} {β β' : Life}
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    {x : LifeVar} {bnd : Lifetime.Life} {mb : Life} (hmb : bnd.interp δ = some mb)
    {F : CTy} (hF : F.SuspendC x bnd)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) :
    ∀ (I : List Loc) (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      Θ.OK → ConsistentX c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (Θ' : LocTy) (c' : Loc → Option Life), Θ.ExtA Θ' →
        Θ'.OK → ∀ ρm ρ', sepList (mutLeafN (ℍ := ℍ) A δ α Θ' n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c' ρ' →
          erwp (ℍ := ℍ) (Θ'.view c')
            (opTableR (tabR (ℍ := ℍ) (claimL (ℍ := ℍ) A δ Θ' []) F δ Θ' c')
              (claimL (ℍ := ℍ) A δ Θ' [])) (Ψ Θ') n ls e ρ') →
      erwp (ℍ := ℍ) (Θ.view c)
        (opTableR (tabR (ℍ := ℍ) (claimL (ℍ := ℍ) A δ Θ I) F δ Θ c) (claimL (ℍ := ℍ) A δ Θ I))
        (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n ls e ρ
  | [], Θ, c, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨rfl, -⟩ := ho
      rw [eq_of_compS_empty_left hcρ] at hc ⊢
      have h := (hH (↓γ) (Life.down_sqsubset γ)).2 Θ c (LocTy.extA_refl Θ) hΘ PMap.empty ρH
        ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH) hc
      exact erwp_mono (fun k ls' v σ h' =>
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h'⟩) (opTableR_local _ _) n ls e ρH h
  | ℓ :: I, Θ, c, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨ρ0, ρr, hc0, hleaf, hrest⟩ := ho
      obtain ⟨l, u, σ, hl, hcl, hu⟩ := hleaf
      obtain rfl : ℓ = l := loc_inj hl
      -- `ρ = ρ0 ● F`, `F = ρr ● ρH`
      obtain ⟨Fr, hFr, hρ⟩ := compS_reassoc hc0 hcρ
      refine erwp_of_valid fun hv => ?_
      have hvρ0 : ResU.Valid ρ0 := (ResU.Valid.split hρ hv).1
      have hko : (CellU.ownOf (Loc := Loc) u).kind ≠ Kind.imm := by simp
      have hown : ρ0.get ℓ = some (CellU.ownOf u) :=
        (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
      have hcF : ConsistentX c Fr := consistentX_right hρ hc hv
      have hcσ : ConsistentX c σ := consistentX_right hcl (consistentX_left hρ hc hv) hvρ0
      -- the outer frame's lifetime: fresh, below the frame's rest, `β`, `β′` and the bound
      obtain ⟨βF, hβF⟩ := ResU.exists_stratum Fr
      obtain ⟨α₁, hα₁le, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(βF ⊓ β ⊓ β' ⊓ mb))
      have hα₁lt : α₁ < βF ⊓ β ⊓ β' ⊓ mb := lt_of_le_of_lt hα₁le (Life.down_sqsubset _)
      have hα₁F : α₁ ≤ βF := hα₁lt.le.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
      have hα₁β : α₁ ≤ β := hα₁lt.le.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
      have hα₁β' : α₁ ≤ β' := hα₁lt.le.trans (inf_le_left.trans inf_le_right)
      have hLt : LtLife δ bnd α₁ := ⟨mb, hmb, lt_of_lt_of_le hα₁lt inf_le_right⟩
      set P : CPredL := fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r with hP
      set Fm : Nat → Val → SPropS Loc Val α₁ := famL α₁ P Θ with hFm
      have hFmD : DownFam α₁ Fm := vN_fam_down A δ α₁ Θ
      have houtP : σ.InStratum α₁ := (hunif Θ n u σ hu).mono hα₁β
      have houtb : Fr.InStratum (↓α₁) := hβF.mono ((Life.down_sqsubset α₁).le.trans hα₁F)
      have hwit : Fm n u ⟨σ, houtP⟩ := (vN_above A δ Θ houtP).mpr hu
      set Θ₁ := Θ.add ℓ α₁ Fm with hΘ₁
      set c₁ := setLife c ℓ α₁ with hc₁
      have hOK₁ : Θ₁.OK := by
        obtain ⟨N, hN⟩ := hΘ.2
        exact ⟨LocTy.down_add hΘ.1 ℓ hFmD, ⟨min N (↓α₁), LocTy.fresh_add hN (min_le_left _ _)
          (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α₁)) ℓ Fm⟩⟩
      have hE₁ : Θ.ExtA Θ₁ := LocTy.extA_add hfr ℓ Fm
      have hview : Θ₁.view c₁ = (Θ.view c).set ℓ α₁ Fm := LocTy.view_add Θ c ℓ α₁ Fm
      have hcF₁ : ConsistentX c₁ Fr :=
        consistentX_setLife hcF (exS_none_of_part hρ hv hown hko) α₁
      have hcσ₁ : ConsistentX c₁ σ :=
        consistentX_setLife hcσ (exS_none_of_part hcl hvρ0 (ResU.single_get_self _ _) hko) α₁
      -- the inner frames' claim lies in the lend's stratum
      have hRs : ∀ k ρ', claimL (ℍ := ℍ) A δ Θ₁ I k ρ' → ρ'.InStratum α₁ := fun k ρ' h =>
        sepList_closed (ResU.inStratum_empty α₁) (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) h
      -- the frame's claim joined to the inner ones' is the cells owned again at `Θ`
      have hcl' : ∀ k ρ', (claimR ℓ α₁ Fm k ⋆ claimL (ℍ := ℍ) A δ Θ₁ I k) ρ' →
          claimL (ℍ := ℍ) A δ Θ (ℓ :: I) k ρ' := by
        rintro k ρ' ⟨ρ₁, ρ₂, hc12, ⟨w, σ', hσ', hFσ, hcw⟩, hr⟩
        refine ⟨ρ₁, ρ₂, hc12, ⟨ℓ, w, σ', rfl, hcw, (vN_above A δ Θ hσ').mp hFσ⟩, ?_⟩
        exact sepList_mono_down (R := fun τ => τ.InStratum α₁)
          (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
            ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
          (fun m τ hτ hm => vN_local (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) (hRs k ρ₂ hr) hr
      have hM := erwp_M_frameCRR (Φ := Θ.view c) (l := ℓ) (A := α₁) (F := Fm) hFmD
        (tabR_lendOKCR_C hF (claimL (ℍ := ℍ) A δ Θ₁ I) δ hLt Θ₁ c₁)
        (tabR_tabR_twinW hF (claimL (ℍ := ℍ) A δ Θ₁ I) (fun k => claimR ℓ α₁ Fm k ⋆
          claimL (ℍ := ℍ) A δ Θ₁ I k) δ Θ₁ Θ c₁ c
          (fun A' hO => vN_add_eq_bnd hO δ hLt hfr ℓ Fm))
        (tabR_canR hfr hLt hFmD hRs F.cdepth F le_rfl hF) hRs
        (Q := fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) (ℓ :: I) ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n n le_rfl ls e u σ ρ0 Fr ρ houtP houtb (Fm n) (fun _ _ h => h) hwit hcl hρ
        (fun BM hBM => ?_)
      · exact erwp_opTableR_le (tabR_le hcl' δ Θ c F.cdepth F le_rfl) hcl' n ls e ρ hM
      rw [← hview]
      -- `BM = ρr ● R`, `R = ρH ● cell`
      obtain ⟨R, hR, hBMR⟩ := compS_reassoc hFr hBM
      have hcBM : ConsistentX c₁ BM := consistentX_compS hBM hcF₁
        (consistentX_single_mut hcσ₁ (by simp [hc₁, setLife]))
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ₁ n (Val.loc m)) I ρr :=
        sepList_mono' (fun m τ h => vN_extA (.ref A) δ hE₁ n _ τ h) hrest
      refine erwp_mono (fun k ls' v ρ' h => ?_) (opTableR_local _ _) n ls e BM
        (erwp_M_frameListCRN hunif hmb hF Ψ hΨs hΨl e ls I Θ₁ c₁ n ρr R BM (βR ⊓ α₁ ⊓ γ) hOK₁
          hcBM hBMR hrest₁ (fun α₂ hα₂ => ⟨hβR.mono (le_of_lt (lt_of_lt_of_le hα₂
            (inf_le_left.trans inf_le_left))), ?_⟩))
      · -- the outer frame's postcondition from the inner ones'
        obtain ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ := h
        have hs1 : ρ₁.InStratum α₁ := sepList_closed (ResU.inStratum_empty α₁)
          (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨inStratum_compS hc12 hs1 hs2, fun w Y hY σ' ⟨hσ', hFσ⟩ Z hZ => ?_⟩
        have ho1' : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ :=
          sepList_mono_down (R := fun τ => τ.InStratum α₁)
            (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
              ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
            (fun m τ hτ hm => vN_local (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) hs1 ho1
        have hψ' := hΨl Θ ℓ α₁ Fm k ls' v ρ₂ hs2 hψ
        have hwA : vN (ℍ := ℍ) A δ Θ k w σ' := (vN_above A δ Θ hσ').mp hFσ
        obtain ⟨cp, hcp, hZ'⟩ := compS_reassoc hY hZ
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨cp, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, w, σ', rfl, hcp, hwA⟩, ho1'⟩, hψ'⟩
      · -- the inner frames' callback: the outer leaf, at `α₂ ⊑ α₁`, heads the family
        intro Θ' c' hE hOK' ρm₂ ρ' hm₂ hcomp hc'
        have hα₂γ : α₂ < γ := lt_of_lt_of_le hα₂ inf_le_right
        have hα₂α₁ : α₂ ≤ α₁ := le_of_lt (lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_right))
        obtain ⟨X, hX, hρ'X⟩ := compS_reassoc hR hcomp
        have hlead : mutLeafN (ℍ := ℍ) A δ α₂ Θ' n ℓ
            (ResU.single ℓ (CellU.mutOf α₁ u σ houtP (Fm n) hwit)) :=
          ⟨α₁, hα₂α₁, mutL_extR (hE.extR _) (lend_mutL Θ ℓ α₁ P le_rfl houtP hwit),
            fun Θ'' j w r h => (hunif Θ'' j w r h).mono hα₁β⟩
        exact (hH α₂ hα₂γ).2 Θ' c' (LocTy.extA_trans hE₁ hE) hOK' X ρ' ⟨_, ρm₂, hX, hlead, hm₂⟩
          hρ'X hc'

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
