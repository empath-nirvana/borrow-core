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
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC interp_top_of_defines_empty
  defines_meetOfDom_empty)
open BoCa.BoLo (Heap Kont ubindE Head performE raiseE cancelVal opPayload)

/-! ### The lender's twin at an incoming claim -/

/-- **An entry of `tabR` is a layer's, and every `tabR`, at every claim and world, has the
layer's entry at the same key.** -/
theorem tab_lookupRW (R : Nat → WProp) : ∀ (F : CTy) {δ₂ : LSub} {Θ₂ : LocTy}
    {c₂ : Loc → Option Life} {m j : UInt32} {en : OpEntN},
    tabR (ℍ := ℍ) R F δ₂ Θ₂ c₂ m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entN q B (fun k v ρ => vN₀ (ℍ := ℍ) A δ₂ Θ₂ k v ρ)
        (fun k v ρ => vN₀ (ℍ := ℍ) B δ₂ Θ₂ k v ρ ∧ ConsistentX c₂ ρ) (finR (ℍ := ℍ) R fin δ₂ Θ₂ c₂) ∧
      ∀ (R' : Nat → WProp) (δ₃ : LSub) (Θ₃ : LocTy) (c₃ : Loc → Option Life),
        tabR (ℍ := ℍ) R' F δ₃ Θ₃ c₃ m j =
          some (entN q B (fun k v ρ => vN₀ (ℍ := ℍ) A δ₃ Θ₃ k v ρ)
            (fun k v ρ => vN₀ (ℍ := ℍ) B δ₃ Θ₃ k v ρ ∧ ConsistentX c₃ ρ)
            (finR (ℍ := ℍ) R' fin δ₃ Θ₃ c₃))
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
layers' types, outliving the bound, read alike at the two worlds (`hΘ`), and the answers,
outliving the closed bound, are alike consistent with the two views
(`consistentX_of_outlives`). `tabN_tabR_twin` with the callback's table a `tabR`. -/
theorem tabR_tabR_twinW {x : LifeVar} {bnd : Lifetime.Life} {F : CTy}
    (hbnd : LifeCtx.empty.Defines bnd) (hF : F.SuspendC x bnd) (R R' : Nat → WProp) (δ : LSub) (Θ₁ Θ₂ : LocTy)
    (c₁ c₂ : Loc → Option Life)
    (hΘ : ∀ A : VTy, VOutlives LifeCtx.empty bnd A → vN₀ (ℍ := ℍ) A δ Θ₁ = vN₀ (ℍ := ℍ) A δ Θ₂) :
    (tabR (ℍ := ℍ) R F δ Θ₁ c₁).Twin (tabR (ℍ := ℍ) R' F δ Θ₂ c₂) := by
  intro m i en h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupRW R F h
  obtain ⟨-, -, -, hOA, hOB, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR R' δ Θ₂ c₂, rfl, rfl, ?_, ?_, rfl⟩
  · simp only [entN, hΘ A hOA]
  · simp only [entN, hΘ B hOB]
    funext k _ v ρ
    exact propext ⟨fun h => ⟨h.1, consistentX_of_outlives hbnd hOB h.1 c₁⟩,
      fun h => ⟨h.1, consistentX_of_outlives hbnd hOB h.1 c₂⟩⟩

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
    exact vN_inStratum_bnd₀ hOA hLt hp
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupRW R F h
    obtain ⟨-, -, -, -, hOB, -⟩ := layer_suspend F hF hL
    exact (vN_inStratum_bnd₀ hOB hLt hp.1).mono (Life.down_sqsubset α).le

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
      (tabN₀ (ℍ := ℍ) F (δ.extend x α) Θ c).Le (tabR (ℍ := ℍ) R₀ F δ Θ c) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro F hd hF m i en h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupN F h
  obtain ⟨-, hA, hB, -, -, hfinS⟩ := layer_suspend F hF hL
  refine ⟨_, hR R₀ δ Θ c, rfl, rfl, ?_, ?_, rfl, fun _ _ => ?_⟩
  · simp only [entN, vN_extend_of_not_free₀ (ℍ := ℍ) hA δ α]
  · simp only [entN, vN_extend_of_not_free₀ (ℍ := ℍ) hB δ α]
  · simp only [entN]
    by_cases hcap : capB q B = true
    · rw [if_pos hcap, if_pos hcap]
      have hfS := hfinS hcap
      by_cases htop : fin = .top
      · subst htop; simp [finR, finN₀, FinLeSN]
      rw [finR_eq _ htop, finN_eq₀ htop]
      intro k ls e ρ h'
      have hfd := layer_cdepth F hL
      exact erwp_cancelTabN_R (ih fin.cdepth (by omega) fin le_rfl hfS) hR₀ k ls e ρ h'
    · rw [if_neg hcap, if_neg hcap]; trivial

/-- **The lender's cancel obligations from the callback's, at an incoming claim** (`tabR_can`
with the callback's table `tabR R` at the lend's world): at a capturable entry the callback's
cancel run at its cancel row's `tabR R`, framed by `erwp_M_frame_cancelRunCRR`, its own nested
cancel obligations by the induction on how deep cancel rows nest. -/
theorem tabR_canR {x : LifeVar} {bnd : Lifetime.Life} {α : Life} {δ : LSub} {Θ : LocTy}
    (hbnd : LifeCtx.empty.Defines bnd) (hf : Θ.Fresh α) (hLt : LtLife δ bnd α) {c : Loc → Option Life} {l : Loc}
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
    (tabR_tabR_twinW hbnd hfin R _ δ (Θ.add l α Fam) Θ (setLife c l α) c
      (fun A' hO => vN_add_eq_bnd₀ hO δ hLt hf l Fam))
    (ih fin hfd hfin) hR k k le_rfl ls _ v'' χ W'' (Z.del l) ρkL hχ hdZd P'' hPk hw''
    (ResU.CompS.comm hW'') (ResU.CompS.comm hkL) (fun BM hBM => ?_)
  obtain rfl := ResU.CompS.functional hBM hZd
  rw [← LocTy.view_add]
  exact erwp_garbage hZ hno hin

/-! ### The `n`-cell Mut Frame across stops and layered cancel runs -/

/-- **The composite claim of a family's frames**: the cells owned again, each holding a member of
`A` at the world `Θ`. It is the source array's range, which the finaliser `d : Array A ⊸ 1`
takes. -/
def claimL₀ (A : VTy) (δ : LSub) (Θ : LocTy) (I : List Loc) : Nat → WProp :=
  fun k => sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I

/-- **One Mut Frame per place, around one expression, across stops, raises and layered cancel
runs** (Core's `wpG_M_frameList`, the frames of `sliceBorrowMU_compatX`), at the chain: the list
induction over `erwp_M_frameCRR`, each frame its own key in the world, as `rwp_M_frameListN`.

Frame `j` lends its leaf at `αⱼ` fresh for the world the frames before it reached and below the
bound, so the row's types read alike at the two worlds (`vN_add_eq_bnd₀`). The callback of
frame `j` is the run of frames `j+1 … n`, at the lender's twin `tabR` of the row at the world with
`αⱼ`, its raises and cancel runs ending at the inner frames' composite claim (`claimL₀`, at that
world); frame `j`'s claim joins it (`erwp_M_frameCRR`, `tabR_canR`), and the cells it claims are
moved to the world without `αⱼ` by `vN_local₀`, their contents in `αⱼ`'s stratum (`tabR_le`). The
innermost callback runs at the lender's twin at the empty claim, `claimL₀ … []`. -/
theorem erwp_M_frameListCRN {A : VTy} {δ : LSub} {β β' : Life}
    (hunif : ∀ Θ j u r, vN₀ (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    {x : LifeVar} {bnd : Lifetime.Life} (hbnd : LifeCtx.empty.Defines bnd) {mb : Life}
    (hmb : bnd.interp δ = some mb) {F : CTy} (hF : F.SuspendC x bnd)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) :
    ∀ (I : List Loc) (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      Θ.OK → ConsistentX c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (Θ' : LocTy) (c' : Loc → Option Life), Θ.ExtA Θ' →
        Θ'.OK → ∀ ρm ρ', sepList (mutLeafN₀ (ℍ := ℍ) A δ α Θ' n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c' ρ' →
          erwp (ℍ := ℍ) (Θ'.view c')
            (opTableR (tabR (ℍ := ℍ) (claimL₀ (ℍ := ℍ) A δ Θ' []) F δ Θ' c')
              (claimL₀ (ℍ := ℍ) A δ Θ' [])) (Ψ Θ') n ls e ρ') →
      erwp (ℍ := ℍ) (Θ.view c)
        (opTableR (tabR (ℍ := ℍ) (claimL₀ (ℍ := ℍ) A δ Θ I) F δ Θ c) (claimL₀ (ℍ := ℍ) A δ Θ I))
        (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
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
      set P : CPredL := fun Θ' j w r => vN₀ (ℍ := ℍ) A δ Θ' j w r with hP
      set Fm : Nat → Val → SPropS Loc Val α₁ := famL α₁ P Θ with hFm
      have hFmD : DownFam α₁ Fm := vN_fam_down₀ A δ α₁ Θ
      have houtP : σ.InStratum α₁ := (hunif Θ n u σ hu).mono hα₁β
      have houtb : Fr.InStratum (↓α₁) := hβF.mono ((Life.down_sqsubset α₁).le.trans hα₁F)
      have hwit : Fm n u ⟨σ, houtP⟩ := (vN_above₀ A δ Θ houtP).mpr hu
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
      have hRs : ∀ k ρ', claimL₀ (ℍ := ℍ) A δ Θ₁ I k ρ' → ρ'.InStratum α₁ := fun k ρ' h =>
        sepList_closed (ResU.inStratum_empty α₁) (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum₀ hα₁β hunif hm) h
      -- the frame's claim joined to the inner ones' is the cells owned again at `Θ`
      have hcl' : ∀ k ρ', (claimR ℓ α₁ Fm k ⋆ claimL₀ (ℍ := ℍ) A δ Θ₁ I k) ρ' →
          claimL₀ (ℍ := ℍ) A δ Θ (ℓ :: I) k ρ' := by
        rintro k ρ' ⟨ρ₁, ρ₂, hc12, ⟨w, σ', hσ', hFσ, hcw⟩, hr⟩
        refine ⟨ρ₁, ρ₂, hc12, ⟨ℓ, w, σ', rfl, hcw, (vN_above₀ A δ Θ hσ').mp hFσ⟩, ?_⟩
        exact sepList_mono_down (R := fun τ => τ.InStratum α₁)
          (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
            ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
          (fun m τ hτ hm => vN_local₀ (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) (hRs k ρ₂ hr) hr
      have hM := erwp_M_frameCRR (Φ := Θ.view c) (l := ℓ) (A := α₁) (F := Fm) hFmD
        (tabR_lendOKCR_C hF (claimL₀ (ℍ := ℍ) A δ Θ₁ I) δ hLt Θ₁ c₁)
        (tabR_tabR_twinW hbnd hF (claimL₀ (ℍ := ℍ) A δ Θ₁ I) (fun k => claimR ℓ α₁ Fm k ⋆
          claimL₀ (ℍ := ℍ) A δ Θ₁ I k) δ Θ₁ Θ c₁ c
          (fun A' hO => vN_add_eq_bnd₀ hO δ hLt hfr ℓ Fm))
        (tabR_canR hbnd hfr hLt hFmD hRs F.cdepth F le_rfl hF) hRs
        (Q := fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) (ℓ :: I) ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n n le_rfl ls e u σ ρ0 Fr ρ houtP houtb (Fm n) (fun _ _ h => h) hwit hcl hρ
        (fun BM hBM => ?_)
      · exact erwp_opTableR_le (tabR_le hcl' δ Θ c F.cdepth F le_rfl) hcl' n ls e ρ hM
      rw [← hview]
      -- `BM = ρr ● R`, `R = ρH ● cell`
      obtain ⟨R, hR, hBMR⟩ := compS_reassoc hFr hBM
      have hcBM : ConsistentX c₁ BM := consistentX_compS hBM hcF₁
        (consistentX_single_mut hcσ₁ (by simp [hc₁, setLife]))
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ₁ n (Val.loc m)) I ρr :=
        sepList_mono' (fun m τ h => vN_extA₀ (.ref A) δ hE₁ n _ τ h) hrest
      refine erwp_mono (fun k ls' v ρ' h => ?_) (opTableR_local _ _) n ls e BM
        (erwp_M_frameListCRN hunif hbnd hmb hF Ψ hΨs hΨl e ls I Θ₁ c₁ n ρr R BM (βR ⊓ α₁ ⊓ γ) hOK₁
          hcBM hBMR hrest₁ (fun α₂ hα₂ => ⟨hβR.mono (le_of_lt (lt_of_lt_of_le hα₂
            (inf_le_left.trans inf_le_left))), ?_⟩))
      · -- the outer frame's postcondition from the inner ones'
        obtain ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ := h
        have hs1 : ρ₁.InStratum α₁ := sepList_closed (ResU.inStratum_empty α₁)
          (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum₀ hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨inStratum_compS hc12 hs1 hs2, fun w Y hY σ' ⟨hσ', hFσ⟩ Z hZ => ?_⟩
        have ho1' : sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ :=
          sepList_mono_down (R := fun τ => τ.InStratum α₁)
            (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
              ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
            (fun m τ hτ hm => vN_local₀ (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) hs1 ho1
        have hψ' := hΨl Θ ℓ α₁ Fm k ls' v ρ₂ hs2 hψ
        have hwA : vN₀ (ℍ := ℍ) A δ Θ k w σ' := (vN_above₀ A δ Θ hσ').mp hFσ
        obtain ⟨cp, hcp, hZ'⟩ := compS_reassoc hY hZ
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨cp, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, w, σ', rfl, hcp, hwA⟩, ho1'⟩, hψ'⟩
      · -- the inner frames' callback: the outer leaf, at `α₂ ⊑ α₁`, heads the family
        intro Θ' c' hE hOK' ρm₂ ρ' hm₂ hcomp hc'
        have hα₂γ : α₂ < γ := lt_of_lt_of_le hα₂ inf_le_right
        have hα₂α₁ : α₂ ≤ α₁ := le_of_lt (lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_right))
        obtain ⟨X, hX, hρ'X⟩ := compS_reassoc hR hcomp
        have hlead : mutLeafN₀ (ℍ := ℍ) A δ α₂ Θ' n ℓ
            (ResU.single ℓ (CellU.mutOf α₁ u σ houtP (Fm n) hwit)) :=
          ⟨α₁, hα₂α₁, mutL_extR (hE.extR _) (lend_mutL Θ ℓ α₁ P le_rfl houtP hwit),
            fun Θ'' j w r h => (hunif Θ'' j w r h).mono hα₁β⟩
        exact (hH α₂ hα₂γ).2 Θ' c' (LocTy.extA_trans hE₁ hE) hOK' X ρ' ⟨_, ρm₂, hX, hlead, hm₂⟩
          hρ'X hc'

/-! ### `slice_borrow_mut` at a suspending row -/

/-- `withborU`'s `then` at the source `a`: `λb. (a, b)`. -/
def NFa (a : Val) : Val := Val.lam (.pair (.val a) (.var 0))

/-- `withborU`'s `unwind` at the source `a`: `λ_. d a`. -/
def DFa (d : Expr) (a : Val) : Val := Val.lam (.app d (.val a))

/-- **The finaliser consumes the source array** (`fin_claim` at `Array A`): `d`'s judgment at
`Array A ⊸ 1`, applied to the array owned again. -/
theorem fin_claimArr {A : VTy} {d : Expr} (hdc : closedAt 0 d = true)
    (hd : SemJN₀ (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.array A) .unit))) {δ : LSub}
    {Θ : LocTy} (hΘ : Θ.OK) {c : Loc → Option Life} {a : Val} {k : Nat} {ls : List SRec}
    {ρ : WRes} (h : vN₀ (ℍ := ℍ) (.array A) δ Θ k a ρ) (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) (Θ.view c) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (DFa d a)) (.val .unit)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  obtain ⟨l, cn, rfl, -, -⟩ := id h
  refine Hardest791.rwp_det'' (Q := fun _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) hΦ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app d (.val (Val.arr l cn)))) =
      (Kont.appL .hole (Val.arr l cn)).plug d := by
    simp [Kont.plug, Expr.subst, subst_closedAt d (s := _) hdc (Nat.zero_le _), subst_arr]
  rw [e]
  refine rwp_bind hΦ _ ?_
  have hd0 := hd δ [] Θ c k ls PMap.empty (models_empty_any _) hΘ (consistentX_empty c) trivial rfl
  rw [show substAll [] d = d from psub_closedAt d [] hdc (Nat.zero_le 0)] at hd0
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty hd0) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'
    c k' le_rfl (Val.arr l cn) τ₂ τ hcτ (vN_le₀ hk' h) hcτ'
  exact rwp_of_erwp_empty this

/-- **`slice_borrow_mut` at a suspending row is a value of `!` its type** (Core's
`sliceBorrowMU_compatX` at `Row.Suspend`): `withborU d` at
`Array A ⊸ (∀'x ⊏ @bnd. [Mut 'x A] ⊸ F_Σ(['x] B)) ⊸ F_Σ(Array A ⊗ B)`, `Σ` a
`Row.Suspend x bnd` row, cleanup that performs included.

`withbor2S_compat`'s structure, with the one-cell frame replaced by the `n`-cell frame across
stops, raises and layered cancel runs (`erwp_M_frameListCRN`, Core's `wpG_M_frameFam` at the
array's range): the payloads' stratum and the result's from the side conditions by 6.60 at
`↓@bδ` (`vN_outlivesLe₀`), the frames' lifetimes below the bound; the callback, at the innermost
lifetime `α`, receives the family `[Mut 'x A]` (`vN_mutLeaf` at each leaf) and runs at its row's
`tabN₀`, below the lender's twin at the empty claim (`tabN_tabR_le`); the composite claim, the
cells owned again at `Θ` (`claimL₀`), is the array; it is consistent with the view
(`erwp_claimX`), and the finaliser frame `then b. (a, b) unwind d a` consumes it with `d`
(`erwp_ubindClaimRT`, `fin_claimArr`).

Premises, and the rule that supplies each: `hbnd` is the bound's definedness (`Const791.OK`);
`hOA`, `hOB`, `hA`, `hB`, `hS`, `hdc` are `sliceBorrowMU`'s with `Row.Suspend` for `Row.Unwind`
(`Const791.OK`); `hd` is the fundamental property at `d`'s derivation. -/
theorem sliceBorrowMS_compat {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy} {S : Row}
    {d : Expr} (hbnd : LifeCtx.empty.Defines bnd)
    (hOA : ∃ b, LifeCtx.empty.Defines b ∧ VOutlivesLe LifeCtx.empty b A)
    (hOB : ∃ b, LifeCtx.empty.Defines b ∧ VOutlivesLe LifeCtx.empty b B)
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hS : S.Suspend x bnd) (hdc : closedAt 0 d = true)
    (hd : SemJN₀ (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.array A) .unit))) (δ : LSub)
    (Θ₀ : LocTy) (n : Nat) :
    vN₀ (ℍ := ℍ) (.bang (sliceBorrowMUTy x bnd A B S)) δ Θ₀ n (withborUV d) PMap.empty := by
  refine ⟨rfl, fun Θ _ hΘ c₁ _ ls => ?_⟩
  intro c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  have hu' := vN_le₀ hk' hu
  obtain ⟨l, cn, rfl, hn, hs⟩ := hu'
  rw [cN_effOf₀]
  refine erwp_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set Fo := CTy.effOf S (.tensor (.array A) B) with hFo
  set T := tabN₀ (ℍ := ℍ) Fo δ Θ c with hTdef
  have hTd : T.Down := tabN_down _ δ Θ hΘ.1 c
  have hQo : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (.array A) B) δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h
  refine erwp_det hΦ (opTableN_down hTd) hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l cn)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ (opTableN_down hTd) hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.arr l cn))
        (thenE ((Expr.var 2).pair (Expr.var 0)) (d.app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFa (Val.arr l cn)) (DFa d (Val.arr l cn)))
        (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) := by
    simp [Kont.plug, Expr.subst, thenE, ubindE, NFa, DFa, Val.pair,
      Val.lam, Expr.val, Val.prim, shift_arr, subst_arr,
      subst_closedAt d (s := _) hdc (Nat.zero_le _)]
  rw [e₃]
  -- the side conditions: the payloads' and the result's strata (6.60 at `↓@bδ`)
  obtain ⟨a, hdefa, hOa⟩ := hOA
  obtain ⟨βP, hβP⟩ := hdefa δ (models_empty_any _)
  have hunif : ∀ Θ j w r, vN₀ (ℍ := ℍ) A δ Θ j w r → r.InStratum (↓βP) :=
    vN_outlivesLe₀ (models_empty_any _) hβP (Life.down_sqsubset βP) hOa
  obtain ⟨b, hdefb, hOb⟩ := hOB
  obtain ⟨βB, hβB⟩ := hdefb δ (models_empty_any _)
  have hBs : ∀ Θ j w r, vN₀ (ℍ := ℍ) B δ Θ j w r → r.InStratum (↓βB) :=
    vN_outlivesLe₀ (models_empty_any _) hβB (Life.down_sqsubset βB) hOb
  obtain ⟨mb, hmb⟩ := hbnd δ (models_empty_any _)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  have hAδ : ∀ α, vN₀ (ℍ := ℍ) A (δ.extend x α) = vN₀ (ℍ := ℍ) A δ :=
    fun α => vN_extend_of_not_free₀ hA δ α
  have hBδ : ∀ α, vN₀ (ℍ := ℍ) B (δ.extend x α) = vN₀ (ℍ := ℍ) B δ :=
    fun α => vN_extend_of_not_free₀ hB δ α
  have hFS : Fo.SuspendC x bnd := suspendC_effOf hS _
  set I := rangeLocs l cn.toNat with hI
  -- the frames, the composite claim the array
  let Ψ : LocTy → PostN := fun Θ k _ v ρ => vN₀ (ℍ := ℍ) B δ Θ k v ρ
  have hM := erwp_M_frameListCRN hunif hbnd hmb hFS Ψ (fun Θ k _ v ρ hw => hBs Θ k v ρ hw)
    (fun Θ l₀ α F k _ v ρ hρ hw => vN_local₀ B δ Θ l₀ α F k v ρ hρ hw)
    (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) ls I Θ c k' ρu ρf ρ'' (mb ⊓ βf)
    hΘ hcon hc' (by rw [← sepRange_eq_sepList]; exact hs)
    (fun α hα => ⟨hβf.mono (le_of_lt (lt_of_lt_of_le hα inf_le_right)), ?_⟩)
  · have hM' := erwp_claimX (c := c) hbnd hFS k' ls _ ρ'' hcon hM
    refine erwp_ubindClaimRT hΘ.1 (F := Fo) (δ := δ) (c := c)
      (fun m i en h _ => by obtain ⟨o, ho, rfl, -⟩ := tabN_effOf_some h; exact (hS o ho).2.1)
      (NFa (Val.arr l cn)) (DFa d (Val.arr l cn)) (fun k ls ρ hR => ?_) hQo
      (fun k ls b ρ hq => ?_) k' ls _ ρ'' hM'
    · obtain ⟨hR, hcR⟩ := hR
      exact fin_claimArr hdc hd hΘ ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact hR⟩ hcR
    · obtain ⟨ρ₁, ρ₂, hc12, ho, hb⟩ := hq
      refine erwp_det hΦ (opTableN_down hTd) hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwp_val (v := Val.pair (Val.arr l cn) b)
        ⟨Val.arr l cn, b, ρ₁, ρ₂, rfl, hc12,
          ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact ho⟩, hb⟩
  -- the callback, at the frames' world and view, from the leaves at `α`
  intro Θ'' c'' hE hOK'' ρm ρ₃ hml hcomp hc''
  refine erwp_of_valid fun hv₃ => ?_
  have hLt : LtLife δ bnd α := ⟨mb, hmb, lt_of_lt_of_le hα inf_le_left⟩
  have hcf : ConsistentX c'' ρf := consistentX_left hcomp hc'' hv₃
  have hfam : vN₀ (ℍ := ℍ) (.sliceMut (.var x) A) (δ.extend x α) Θ'' k' (Val.arr l cn) ρm :=
    ⟨l, cn, rfl, hn, by
      rw [sepRange_eq_sepList]; exact sepList_mono' (fun _ _ h => vN_mutLeaf hA h) hml⟩
  have h1 := (hf Θ'' (hE.extR ρf) hOK'' c'' hcf ls) α hLt
  have h2 := h1 c'' k' le_rfl (Val.arr l cn) _ ρ₃ hcomp hfam hc''
  rw [cN_effOf₀, tabN_effOf_base S (.box (.var x) B) (.tensor (.array A) B)] at h2
  refine erwp_opTableN_R (tabN_tabR_le (R₀ := claimL₀ (ℍ := ℍ) A δ Θ'' []) (fun _ => ⟨rfl, trivial⟩)
    δ Θ'' c'' Fo.cdepth Fo le_rfl hFS) (fun _ => ⟨rfl, trivial⟩) k' ls _ ρ₃
    (erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ ρ₃ h2)
  obtain ⟨β, hβ, hbB, -⟩ := hb
  rw [interp_ext_self] at hβ
  cases Option.some.inj hβ
  show vN₀ (ℍ := ℍ) B δ Θ'' k b ρ'
  rw [← hBδ α]; exact hbB

/-- **`ConstN` for `slice_borrow_mut` at a suspending row**, from the fundamental property at the
finaliser's derivation. -/
theorem constN_sm (hF : FundamentalN (ℍ := ℍ)) {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {d : Expr} (hfr : (Const791.sm x bnd A B S d).InFrag) :
    ConstN (ℍ := ℍ) (.sm x bnd A B S d) := by
  rintro ⟨hbnd, hOA, hOB, hA, hB, hS, hdc, hder⟩ δ Θ n _
  have hL : (VTy.array A).inFrag = true := by
    simp_all [Const791.InFrag, Const791.ty, sliceBorrowMUTy, withborUTy, VTy.inFrag, CTy.inFrag]
  exact sliceBorrowMS_compat hbnd hOA hOB hA hB hS hdc (hF _ _ _ _ hder (jdgInFrag_lolli hL)) δ Θ n

/-! ### `slice_borrow_mut` at an unwinding row -/

/-- **An unwinding row's table does not read a fresh key of the world.** -/
theorem tabN_unwind_add {S : Row} {x : LifeVar} (hS : S.Unwind x) (R : VTy) (δ : LSub)
    {Θ : LocTy} {α : Life} (hfr : Θ.Fresh α) (l : Loc) (F : Nat → Val → SPropS Loc Val α)
    (c₁ c₂ : Loc → Option Life) :
    tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ (Θ.add l α F) c₁ = tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c₂ := by
  induction S with
  | nil => rfl
  | cons o S ih =>
      have ho : o ∈ o :: S := List.mem_cons_self ..
      have hS' : Row.Unwind S x := fun o' ho' => hS o' (List.mem_cons_of_mem _ ho')
      have hA : vN₀ (ℍ := ℍ) o.A δ (Θ.add l α F) = vN₀ (ℍ := ℍ) o.A δ Θ := by
        funext n v ρ
        have hρ := vN_unwind_inStratum hS ho δ α
        exact propext ⟨fun h => vN_local₀ _ δ Θ l α F n v ρ (hρ _ n v ρ h) h,
          fun h => vN_extA₀ _ δ (LocTy.extA_add hfr l F) n v ρ h⟩
      have hB := unwind_B hS ho
      simp only [CTy.effOf, tabN₀]
      rw [ih hS', hA, hB,
        entN_fin_congr (f := finN₀ (ℍ := ℍ) o.fin δ (Θ.add l α F) c₁)
          (f' := finN₀ (ℍ := ℍ) o.fin δ Θ c₂) (fun hcap => by simp [capB, VTy.isZero] at hcap),
        ansN_zero, ansN_zero]

/-- **One Mut Frame per place, around one expression, across raises** (Core's
`wpG_M_frameList`, the frames of `sliceBorrowMU_compatX` at an unwinding row): the list
induction over `erwp_M_frameRR`. The table `τ Θ c` does not read a fresh key (`hτ`), so every
frame's callback runs at the lender's table; frame `j`'s claim joins the inner frames' at a
raise, and the cells it claims are moved to the world without its key (`vN_local₀`), as in
`erwp_M_frameListCRN`. -/
theorem erwp_M_frameListRN {A : VTy} {δ : LSub} {β β' : Life}
    (hunif : ∀ Θ j u r, vN₀ (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    (τ : LocTy → (Loc → Option Life) → OpTabN)
    (hτ : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) c,
      Θ.Fresh α → τ (Θ.add l α F) (setLife c l α) = τ Θ c)
    (hτok : ∀ Θ c α, (τ Θ c).LendOKR α)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) :
    ∀ (I : List Loc) (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      Θ.OK → ConsistentX c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (Θ' : LocTy) (c' : Loc → Option Life), Θ.ExtA Θ' →
        Θ'.OK → ∀ ρm ρ', sepList (mutLeafN₀ (ℍ := ℍ) A δ α Θ' n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c' ρ' →
          erwp (ℍ := ℍ) (Θ'.view c') (opTableR (τ Θ' c') (claimL₀ (ℍ := ℍ) A δ Θ' []))
            (Ψ Θ') n ls e ρ') →
      erwp (ℍ := ℍ) (Θ.view c) (opTableR (τ Θ c) (claimL₀ (ℍ := ℍ) A δ Θ I))
        (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
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
      obtain ⟨Fr, hFr, hρ⟩ := compS_reassoc hc0 hcρ
      refine erwp_of_valid fun hv => ?_
      have hvρ0 : ResU.Valid ρ0 := (ResU.Valid.split hρ hv).1
      have hko : (CellU.ownOf (Loc := Loc) u).kind ≠ Kind.imm := by simp
      have hown : ρ0.get ℓ = some (CellU.ownOf u) :=
        (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
      have hcF : ConsistentX c Fr := consistentX_right hρ hc hv
      have hcσ : ConsistentX c σ := consistentX_right hcl (consistentX_left hρ hc hv) hvρ0
      -- the outer frame's lifetime: fresh, below the frame's rest, `β` and `β′`
      obtain ⟨βF, hβF⟩ := ResU.exists_stratum Fr
      obtain ⟨α₁, hα₁le, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(βF ⊓ β ⊓ β'))
      have hα₁lt : α₁ < βF ⊓ β ⊓ β' := lt_of_le_of_lt hα₁le (Life.down_sqsubset _)
      have hα₁F : α₁ ≤ βF := hα₁lt.le.trans (inf_le_left.trans inf_le_left)
      have hα₁β : α₁ ≤ β := hα₁lt.le.trans (inf_le_left.trans inf_le_right)
      have hα₁β' : α₁ ≤ β' := hα₁lt.le.trans inf_le_right
      set P : CPredL := fun Θ' j w r => vN₀ (ℍ := ℍ) A δ Θ' j w r with hP
      set Fm : Nat → Val → SPropS Loc Val α₁ := famL α₁ P Θ with hFm
      have hFmD : DownFam α₁ Fm := vN_fam_down₀ A δ α₁ Θ
      have houtP : σ.InStratum α₁ := (hunif Θ n u σ hu).mono hα₁β
      have houtb : Fr.InStratum (↓α₁) := hβF.mono ((Life.down_sqsubset α₁).le.trans hα₁F)
      have hwit : Fm n u ⟨σ, houtP⟩ := (vN_above₀ A δ Θ houtP).mpr hu
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
      have hRs : ∀ k ρ', claimL₀ (ℍ := ℍ) A δ Θ₁ I k ρ' → ρ'.InStratum α₁ := fun k ρ' h =>
        sepList_closed (ResU.inStratum_empty α₁) (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum₀ hα₁β hunif hm) h
      have hcl' : ∀ k ρ', (claimR ℓ α₁ Fm k ⋆ claimL₀ (ℍ := ℍ) A δ Θ₁ I k) ρ' →
          claimL₀ (ℍ := ℍ) A δ Θ (ℓ :: I) k ρ' := by
        rintro k ρ' ⟨ρ₁, ρ₂, hc12, ⟨w, σ', hσ', hFσ, hcw⟩, hr⟩
        refine ⟨ρ₁, ρ₂, hc12, ⟨ℓ, w, σ', rfl, hcw, (vN_above₀ A δ Θ hσ').mp hFσ⟩, ?_⟩
        exact sepList_mono_down (R := fun τ => τ.InStratum α₁)
          (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
            ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
          (fun m τ hτ hm => vN_local₀ (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) (hRs k ρ₂ hr) hr
      have hM := erwp_M_frameRR (Φ := Θ.view c) (l := ℓ) (A := α₁) (F := Fm) hFmD
        (hτok Θ c α₁) hRs
        (Q := fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) (ℓ :: I) ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n n le_rfl ls e u σ ρ0 Fr ρ houtP houtb (Fm n) (fun _ _ h => h) hwit hcl hρ
        (fun BM hBM => ?_)
      · exact erwp_opTableR_le (OpTabN.Sub.le fun _ _ _ h => h) hcl' n ls e ρ hM
      rw [← hview, ← hτ Θ ℓ α₁ Fm c hfr]
      obtain ⟨R, hR, hBMR⟩ := compS_reassoc hFr hBM
      have hcBM : ConsistentX c₁ BM := consistentX_compS hBM hcF₁
        (consistentX_single_mut hcσ₁ (by simp [hc₁, setLife]))
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ₁ n (Val.loc m)) I ρr :=
        sepList_mono' (fun m τ h => vN_extA₀ (.ref A) δ hE₁ n _ τ h) hrest
      refine erwp_mono (fun k ls' v ρ' h => ?_) (opTableR_local _ _) n ls e BM
        (erwp_M_frameListRN hunif τ hτ hτok Ψ hΨs hΨl e ls I Θ₁ c₁ n ρr R BM (βR ⊓ α₁ ⊓ γ) hOK₁
          hcBM hBMR hrest₁ (fun α₂ hα₂ => ⟨hβR.mono (le_of_lt (lt_of_lt_of_le hα₂
            (inf_le_left.trans inf_le_left))), ?_⟩))
      · obtain ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ := h
        have hs1 : ρ₁.InStratum α₁ := sepList_closed (ResU.inStratum_empty α₁)
          (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum₀ hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨inStratum_compS hc12 hs1 hs2, fun w Y hY σ' ⟨hσ', hFσ⟩ Z hZ => ?_⟩
        have ho1' : sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ :=
          sepList_mono_down (R := fun τ => τ.InStratum α₁)
            (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
              ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
            (fun m τ hτ hm => vN_local₀ (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) hs1 ho1
        have hψ' := hΨl Θ ℓ α₁ Fm k ls' v ρ₂ hs2 hψ
        have hwA : vN₀ (ℍ := ℍ) A δ Θ k w σ' := (vN_above₀ A δ Θ hσ').mp hFσ
        obtain ⟨cp, hcp, hZ'⟩ := compS_reassoc hY hZ
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨cp, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, w, σ', rfl, hcp, hwA⟩, ho1'⟩, hψ'⟩
      · intro Θ' c' hE hOK' ρm₂ ρ' hm₂ hcomp hc'
        have hα₂γ : α₂ < γ := lt_of_lt_of_le hα₂ inf_le_right
        have hα₂α₁ : α₂ ≤ α₁ := le_of_lt (lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_right))
        obtain ⟨X, hX, hρ'X⟩ := compS_reassoc hR hcomp
        have hlead : mutLeafN₀ (ℍ := ℍ) A δ α₂ Θ' n ℓ
            (ResU.single ℓ (CellU.mutOf α₁ u σ houtP (Fm n) hwit)) :=
          ⟨α₁, hα₂α₁, mutL_extR (hE.extR _) (lend_mutL Θ ℓ α₁ P le_rfl houtP hwit),
            fun Θ'' j w r h => (hunif Θ'' j w r h).mono hα₁β⟩
        exact (hH α₂ hα₂γ).2 Θ' c' (LocTy.extA_trans hE₁ hE) hOK' X ρ' ⟨_, ρm₂, hX, hlead, hm₂⟩
          hρ'X hc'

/-- **The finaliser consumes the source array, its judgment read at the index** (`fin_claimI`
at `Array A`). -/
theorem fin_claimArrI {A : VTy} {d : Expr} (hdc : closedAt 0 d = true) {δ : LSub} {Θ : LocTy}
    (hΘ : Θ.OK) {c : Loc → Option Life} {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls, cN₀ (ℍ := ℍ) (.ret (.lolli (.array A) .unit)) δ Θ c k ls d PMap.empty)
    {a : Val} {k : Nat} (hk : k ≤ N) {ls : List SRec} {ρ : WRes}
    (h : vN₀ (ℍ := ℍ) (.array A) δ Θ k a ρ) (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) (Θ.view c) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (DFa d a)) (.val .unit)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  obtain ⟨l, cn, rfl, -, -⟩ := id h
  refine Hardest791.rwp_det'' (Q := fun _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) hΦ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app d (.val (Val.arr l cn)))) =
      (Kont.appL .hole (Val.arr l cn)).plug d := by
    simp [Kont.plug, Expr.subst, subst_closedAt d (s := _) hdc (Nat.zero_le _), subst_arr]
  rw [e]
  refine rwp_bind hΦ _ ?_
  have hd0 := hd k hk ls
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty hd0) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'
    c k' le_rfl (Val.arr l cn) τ₂ τ hcτ (vN_le₀ hk' h) hcτ'
  exact rwp_of_erwp_empty this

/-- **`slice_borrow_mut` at an unwinding row is a value of its type** (Core's
`sliceBorrowMU_compatX`): `withborU d` at
`Array A ⊸ (∀'x ⊏ @Δ. [Mut 'x A] ⊸ F_Σ(['x] B)) ⊸ F_Σ(Array A ⊗ B)`, `Σ` a `Row.Unwind x`
row. `withbor2U_sem`'s steps with the one-cell frame replaced by the `n`-cell frame across the
row's raises (`erwp_M_frameListRN`, Core's `wpG_M_frameFam`), the row's table reading no fresh
key (`tabN_unwind_add`); the payloads' and the result's strata from the side conditions by 6.60
at `↓@bδ`; the callback receives the family `[Mut 'x A]` at the innermost lifetime; the
composite claim, the array owned again, consistent with the view (`erwp_claimX_abort`), is
consumed by the finaliser at a raise (`erwp_ubindRaise`, `fin_claimArrI`). -/
theorem sliceBorrowMU_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {S : Row} {d : Expr}
    {δ : LSub} (hδ : Δ.Models δ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Unwind x) (hdc : closedAt 0 d = true) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN₀ (ℍ := ℍ) (.ret (.lolli (.array A) .unit)) δ Θ c k ls d PMap.empty) :
    vN₀ (ℍ := ℍ) (sliceBorrowMUTy x Δ.meetOfDom A B S) δ Θ₀ n (withborUV d) PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l, cn, rfl, hn, hs⟩ := vN_le₀ hk' hu
  rw [cN_effOf₀]
  refine erwp_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set Fo := CTy.effOf S (.tensor (.array A) B) with hFo
  set T := tabN₀ (ℍ := ℍ) Fo δ Θ c with hTdef
  have hTd : T.Down := tabN_down _ δ Θ hΘ.1 c
  have hQo : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (.array A) B) δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h
  refine erwp_det hΦ (opTableN_down hTd) hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l cn)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ (opTableN_down hTd) hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.arr l cn))
        (thenE ((Expr.var 2).pair (Expr.var 0)) (d.app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFa (Val.arr l cn)) (DFa d (Val.arr l cn)))
        (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) := by
    simp [Kont.plug, Expr.subst, thenE, ubindE, NFa, DFa, Val.pair,
      Val.lam, Expr.val, Val.prim, shift_arr, subst_arr,
      subst_closedAt d (s := _) hdc (Nat.zero_le _)]
  rw [e₃]
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βP, hβP⟩ := hdefa δ hδ
  have hunif : ∀ Θ j w r, vN₀ (ℍ := ℍ) A δ Θ j w r → r.InStratum (↓βP) :=
    vN_outlivesLe₀ hδ hβP (Life.down_sqsubset βP) hOa
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  have hBs : ∀ Θ j w r, vN₀ (ℍ := ℍ) B δ Θ j w r → r.InStratum (↓βB) :=
    vN_outlivesLe₀ hδ hβB (Life.down_sqsubset βB) hOb
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  have hBδ : ∀ α, vN₀ (ℍ := ℍ) B (δ.extend x α) = vN₀ (ℍ := ℍ) B δ :=
    fun α => vN_extend_of_not_free₀ hB δ α
  set I := rangeLocs l cn.toNat with hI
  let Ψ : LocTy → PostN := fun Θ k _ v ρ => vN₀ (ℍ := ℍ) B δ Θ k v ρ
  have hM := erwp_M_frameListRN hunif (fun Θ c => tabN₀ (ℍ := ℍ) Fo δ Θ c)
    (fun Θ l₀ α F c₀ hf₀ => tabN_unwind_add hS _ δ hf₀ l₀ F _ c₀)
    (fun Θ c₀ α => tabN_unwind_lendOKR hS _ δ Θ c₀ α) Ψ
    (fun Θ k _ v ρ hw => hBs Θ k v ρ hw)
    (fun Θ l₀ α F k _ v ρ hρ hw => vN_local₀ B δ Θ l₀ α F k v ρ hρ hw)
    (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) ls I Θ c k' ρu ρf ρ'' (m ⊓ βf)
    hΘ hcon hc' (by rw [← sepRange_eq_sepList]; exact hs)
    (fun α hα => ⟨hβf.mono (le_of_lt (lt_of_lt_of_le hα inf_le_right)), ?_⟩)
  · have hM' := erwp_claimX_abort (tabN_unwind_abort hS _ δ Θ c) hcon hM
    have hM'' := erwp_mono_le
      (Tb' := opTableR T (fun j ρ => claimX (claimL₀ (ℍ := ℍ) A δ Θ I) c j ρ ∧ j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [tabN_unwind_abort hS _ δ Θ c m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hM'
    refine erwp_ubindRaise hΦ hTd
      (fun m i en h ha => by rw [tabN_unwind_abort hS _ δ Θ c m i en h] at ha; cases ha)
      (tabN_unwind_named hS _ δ Θ c)
      (fun m i en h k ls ls' v ρ _ hp => by
        obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
        exact hp)
      (NFa (Val.arr l cn)) (DFa d (Val.arr l cn)) (fun j ls' ρ hR => ?_) hQo
      (fun j ls' b ρ hq => ?_) k' ls _ ρ'' hM''
    · obtain ⟨⟨hR, hcR⟩, hj⟩ := hR
      exact fin_claimArrI hdc hΘ (fun j' hj' ls => hd Θ hΘ c j' (hj'.trans (hk'.trans hk)) ls)
        (hj.trans le_rfl) ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact hR⟩ hcR
    · obtain ⟨ρ₁, ρ₂, hc12, ho, hb⟩ := hq
      refine erwp_det hΦ (opTableN_down hTd) hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwp_val (v := Val.pair (Val.arr l cn) b)
        ⟨Val.arr l cn, b, ρ₁, ρ₂, rfl, hc12,
          ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact ho⟩, hb⟩
  -- the callback, at the frames' world and view, from the leaves at `α`
  intro Θ'' c'' hE hOK'' ρm ρ₃ hml hcomp hc''
  refine erwp_of_valid fun hv₃ => ?_
  have hLt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_left⟩
  have hcf : ConsistentX c'' ρf := consistentX_left hcomp hc'' hv₃
  have hfam : vN₀ (ℍ := ℍ) (.sliceMut (.var x) A) (δ.extend x α) Θ'' k' (Val.arr l cn) ρm :=
    ⟨l, cn, rfl, hn, by
      rw [sepRange_eq_sepList]; exact sepList_mono' (fun _ _ h => vN_mutLeaf hA h) hml⟩
  have h1 := (hf Θ'' (hE.extR ρf) hOK'' c'' hcf ls) α hLt
  have h2 := h1 c'' k' le_rfl (Val.arr l cn) _ ρ₃ hcomp hfam hc''
  rw [cN_effOf₀, tabN_unwind_extend hS (.box (.var x) B) (.tensor (.array A) B) δ Θ'' α c''] at h2
  refine erwp_opTableN_R (OpTabN.Sub.le fun _ _ _ h => h) (R₀ := claimL₀ (ℍ := ℍ) A δ Θ'' [])
    (fun _ => ⟨rfl, trivial⟩) k' ls _ ρ₃
    (erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ ρ₃ h2)
  obtain ⟨β, hβ, hbB, -⟩ := hb
  rw [interp_ext_self] at hβ
  cases Option.some.inj hβ
  show vN₀ (ℍ := ℍ) B δ Θ'' k b ρ'
  rw [← hBδ α]; exact hbB

/-- **`sliceBorrowMU` at `SemJN₀`** (Core's `sliceBorrowMU_compatX`), at an unwinding row and any
`Δ`. -/
theorem sliceBorrowMU_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) (hS : S.Unwind x) (hdc : closedAt 0 d = true)
    (hd : SemJN₀ (ℍ := ℍ) Δ Γ d (.val (.lolli (.array A) .unit))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (withborUE d) (.val (sliceBorrowMUTy x Δ.meetOfDom A B S)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (withborUE d)) _
  rw [show substAll γ (withborUE d) = withborUE d from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine erwp_val (v := withborUV d) (sliceBorrowMU_sem hδ hsideA hsideB hfree₁ hfree₂ hS hdc Θ n
    (fun Θ' hΘ' c' k hk ls' => ?_))
  have h := hd δ γ Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') hlw
    (gN_dead_any hΓ hg Θ' k hk)
  rwa [show substAll γ d = d from psub_closedAt d γ hdc (Nat.zero_le 0)] at h

/-! ### `slice_borrow_mut` at the hardest case's row -/

/-- `λu. ()`. -/
def dropU : Val := Val.lam (.val .unit)

/-- `λa. drop (λu. (), a)`: the source array's cells freed. -/
def dArrFree : Expr := .val (Val.lam (.app (.val (.prim .drop)) (.pair (.val dropU) (.var 0))))

theorem dArrFree_closed : closedAt 0 dArrFree = true := by decide

/-- `λu. ()` is a value of `!(1 ⊸ 1)`. -/
theorem dropU_sem (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN₀ (ℍ := ℍ) (.bang (.lolli .unit .unit)) δ Θ n dropU PMap.empty := by
  refine ⟨rfl, ?_⟩
  intro Θ'' _ hOK c' _ ls' c'' k _ v ρv ρ' hc hv _
  obtain ⟨rfl, rfl⟩ := hv
  obtain rfl := eq_of_compS_empty_left hc
  have hΦ := LocTy.view_down hOK.1 c''
  show erwp (ℍ := ℍ) (Θ''.view c'') (opTableN OpTabN.empty) _ k ls'
    (.app (Val.lam (.val .unit)).1 (.val Val.unit)) _
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ _ _ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  simp only [Kont.plug, Expr.subst, Val.unit, Expr.val]
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

/-- **`λa. drop (λu. (), a)` is a finaliser of an `Array 1` source**: the cells are freed in
order by `dropFill` (`dropFill_wpN₀`). -/
theorem dArrFree_sem :
    SemJN₀ (ℍ := ℍ) LifeCtx.empty [] dArrFree (.val (.lolli (.array .unit) .unit)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl : ρ = PMap.empty := hg
  rw [show substAll γ dArrFree = dArrFree from psub_closedAt dArrFree γ dArrFree_closed le_rfl]
  refine erwp_val (v := Val.lam (.app (.val (.prim .drop)) (.pair (.val dropU) (.var 0)))) ?_
  intro Θ'' _ hOK c' _ ls' c'' k _ v ρv ρ' hc hv hcon
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, cn, rfl, -, hs⟩ := hv
  have hΦ := LocTy.view_down hOK.1 c''
  have hQd : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) .unit δ Θ'' k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ _ _ k v ρ h
  show erwp (ℍ := ℍ) (Θ''.view c'') (opTableN OpTabN.empty) _ k ls'
    (.app (Val.lam (.app (.val (.prim .drop)) (.pair (.val dropU) (.var 0)))).1
      (.val (Val.arr l cn))) _
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQd
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l cn)) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 (Val.arr l cn)
      (.app (.val (.prim .drop)) (.pair (.val dropU) (.var 0)))) =
      Kont.hole.plug (.app (.val (.prim .drop)) (.val (Val.pair dropU (Val.arr l cn)))) := by
    simp [Kont.plug, Expr.subst, dropU, Val.pair, Val.lam, Val.unit, Expr.val, Val.prim]
  rw [e]
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQd
    (fun μ => step1Only_plug (Head.drop μ dropU l cn) rfl .hole) ?_
  exact dropFill_wpN₀ hOK dropU l (dropU_sem δ Θ'' k) cn.toNat 0 k ls' ρ' c'' le_rfl hcon
    (by simpa using hs)

/-- **`slice_borrow_mut` at the hardest case's row**, every hypothesis of `sliceBorrowMS_compat`
discharged: an `Array 1` lent cell by cell at the bound `LifeCtx.empty.meetOfDom`, finalised by
`dArrFree`. -/
theorem sliceBorrowMS_inst (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) :
    vN₀ (ℍ := ℍ) (.bang (sliceBorrowMUTy x LifeCtx.empty.meetOfDom .unit .unit hardestRow)) δ Θ n
      (withborUV dArrFree) PMap.empty :=
  sliceBorrowMS_compat defines_meetOfDom_empty ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩
    ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩ id id (hardestRow_suspend x _) dArrFree_closed
    dArrFree_sem δ Θ n

/-! ### Every constant -/

/-- **`ConstsN` from the fundamental property**: each of the five constants inside the fragment,
the finalisers' judgments read by the fundamental property (`constN_w2`, `constN_w3`,
`constN_wF`, `constN_wl`, `constN_sm`). -/
theorem constsN_of (hF : FundamentalN (ℍ := ℍ)) : ConstsN (ℍ := ℍ)
  | .w2 .., hfr => constN_w2 hF hfr
  | .w3 .., hfr => constN_w3 hF hfr
  | .wF .., hfr => constN_wF hF hfr
  | .wl .., _ => constN_wl
  | .sm .., hfr => constN_sm hF hfr

/-- **`Goal791SchedN` from the fundamental property alone**: `goal791Sched_of` at `constsN_of`. -/
theorem goal791Sched_of_fundamental (hF : FundamentalN (ℍ := ℍ)) : Goal791SchedN (ℍ := ℍ) :=
  goal791Sched_of hF (constsN_of hF)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
