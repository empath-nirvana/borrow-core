import Core.Chain.Cancel791N

/-!
# The suspending reborrow `withbor (3)`  `[spec §62]`

Core's `withbor3U_compatX` (`Core/EffBorrow.lean`), whose proof is 6.174's (`withbor3_compatX`,
`Core/Compatibility.lean:1109`): the finaliser frame outermost, the Mut Anti-Frame at the source
`Mut @a A` inside it with the borrow handed back at every end, then the Mut Frame of the opened
cell at a fresh lifetime, its premise read off the borrow in hand. At `Row.Suspend` the callback
stops under the reborrow, raises, and its cancel rows have layers whose cleanup performs, so the
anti-frame runs across stops, raises and layered cancel runs.

* `opTableGR`/`cancelTabGR`: `opTableR`/`cancelTabR` with the stops guarded (`opTableG`).
* `erwp_M_frameCRG`, `erwp_M_frame_cancelRunCRG`: `erwp_M_frameCR` and
  `erwp_M_frame_cancelRunCR` with the borrow's fold recorded at every stop (`CellFold`), as
  `erwp_M_frameTF` records it for `erwp_M_frameT`.
* `erwp_M_antiFrameCR`, `erwp_M_antiFrame_cancelRunCR`: `erwp_M_antiFrameC` extended to raises
  and to cancel runs that stop: at a raise the claim is sealed again into the source's entry and
  carried out (`Rout`, the `Mut @a A` value the finaliser consumes); a cancellable stop's cancel
  obligation is transferred by a premise (`hcan`), as the Mut Frame's is.
* `tabG`/`finG`: the lender's twin of the callback's table with every cancel run at its cancel
  row's own guarded table, ending at the claim; `tabG_can`, `tabR_canA`: the two transfers, by
  induction on how deep cancel rows nest.
* `withbor3S_compat₀`, `constN_w3₀`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE)

/-! ### Guarded tables with raises -/

/-- `opTableR T R` with its stops guarded by `G`. -/
def opTableGR (T : OpTabN) (G : ShareG) (R : Nat → WProp) : TableN := fun k ls t Ψ =>
  BoLo.or (opTableG T G k ls t Ψ) (raiseStopR T R k ls t Ψ)

/-- `cancelTabR T R` with its stops guarded by `G`. -/
def cancelTabGR (T : OpTabN) (G : ShareG) (R : Nat → WProp) : TableN := fun k ls t Ψ =>
  BoLo.or
    (ex fun (K : Kont) => ex fun (err : Option Val) =>
      ⌜t = K.plug (raiseE (.val (cancelVal err))) ∧ K.Catches 0 = false⌝ ⋆
        ((errOkN T k ls err ⋆ fun ρ => NoOwn ρ) ⋆ R k))
    (opTableG T G k ls t Ψ)

/-! ### The Mut Frame with the fold recorded at every stop -/

/-- **`erwp_M_frameCR` with its stops guarded by the fold**: at a stop the borrow is folded back
into `ℓ ↦ own(w) ● χ` with `χ` in `F k`, the guard an anti-frame around the lend reads. -/
theorem erwp_M_frameCRG {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
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
      erwp (ℍ := ℍ) Φ (opTableGR T' (CellFold l A F) (claimR l A F)) Q n ls e ρ := by
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
    have hfold : CellFold l A F k ls' ρkL := by
      obtain ⟨hχ', hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
      obtain ⟨ac, hac, hacl⟩ := compS_exch hW'' (ResU.CompS.comm hkL)
      exact ⟨v'', χ, hχ', hFk, Z.del l, ac, ResU.CompS.comm hacl, hac⟩
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, ρkL, haY,
        hPA' ▸ hPA, hfold, fun hu' => absurd (hq'.symm.trans hu') hq, fun ls'' he =>
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

/-- **`erwp_M_frame_cancelRunCR` with its stops guarded by the fold.** -/
theorem erwp_M_frame_cancelRunCRG {Φ : LocFam} {l : Loc} {A : Life}
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
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL) :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (cancelTabN T) (fun _ _ _ _ => False) n ls e BM) →
      erwp (ℍ := ℍ) Φ (cancelTabGR T' (CellFold l A F) (claimR l A F)) (fun _ _ _ _ => False) n ls e ρ := by
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
  · -- the cancel's `raise`: the borrow folded, the cell is the claim
    obtain ⟨⟨rfl, hK⟩, τa, τb, hcab, herr, hnb⟩ := pure_sep_iff.mp hp
    have hρa := errOkN_inStratum hT.pa herr
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc τa τb ρp X).mpr ⟨ρ', hcab, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc τa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    have hnoZ : NoOwn Z := noOwn_compS hZ hnb hnoρp
    obtain ⟨hs, hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, err, pure_sep_mk ⟨rfl, hK⟩ ⟨X.del l, W'', hY,
        ⟨τa, Z.del l, hD, errOkN_twin hTT' herr, noOwn_del hnoZ l⟩,
        v'', χ, hs, hFk, ResU.CompS.comm hW''⟩⟩)⟩
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
    have hfold : CellFold l A F k ls' ρkL := by
      obtain ⟨hχ', hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
      obtain ⟨ac, hac, hacl⟩ := compS_exch hW'' (ResU.CompS.comm hkL)
      exact ⟨v'', χ, hχ', hFk, Z.del l, ac, ResU.CompS.comm hacl, hac⟩
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, ρkL, haY,
        hPA' ▸ hPA, hfold, fun hu' => absurd (hq'.symm.trans hu') hq, fun ls'' he =>
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

/-! ### The Mut Anti-Frame across raises and layered cancel runs -/

/-- **The Mut Anti-Frame over a cancel run that stops.** From the opened cell the callback's
cancel run, at the guarded table `cancelTabGR T G Rin`, ends at the cancel's `raise` carrying the
claim `ℓ ↦ own(w) ● σ` with `σ` in `F k` (`hRin`); from the sealed cell the run ends at the
`raise` carrying the claim sealed again, `ℓ ↦ mut(β, w, σ, F k)` (`hRout`). At a stop the guard
gives the fold (`hG`) and the cell is sealed in the continuation's share; a resume opens it again,
and a cancellable stop's cancel obligation is the lender's by `hcan`. -/
theorem erwp_M_antiFrame_cancelRunCR {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T T' : OpTabN}
    (hTT' : T.Twin T')
    (hT : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    {G : ShareG} (hG : ∀ k ls ρ, G k ls ρ → CellFold l β F k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw)))
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ k ls (K : Kont) (w : Val) (σ : WRes) (h : σ.InStratum β)
        (hw : F k w ⟨σ, h⟩) (R ρk' : WRes),
        ResU.CompS (ResU.single l (CellU.mutOf β w σ h (F k) hw)) R ρk' →
        (∀ W X, ResU.CompS σ (ResU.single l (CellU.ownOf w)) W → ResU.CompS R W X →
          cancelOKN en k ls K X) →
        cancelOKN en' k ls K ρk') :
    ∀ n ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat) (hwit : F j v ⟨σP, hstr⟩)
      (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwp (ℍ := ℍ) Φ (cancelTabGR T G Rin) (fun _ _ _ _ => False) n ls e X) →
      erwp (ℍ := ℍ) Φ (cancelTabR T' Rout) (fun _ _ _ _ => False) n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e v σP hstr j hwit ρa ρ hsplit hA
  rw [erwp_eq]
  refine rwpG_M_antiFrameG hΦ hF hsplit fun W X hW hX => ?_
  have h := hA W X hW hX
  rw [erwp_eq] at h
  refine rwpG_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ⟨_, _, hf⟩ | ⟨K, err, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · exact hf.elim
  · -- the cancel's `raise`: the claim sealed again
    obtain ⟨hpur, y1, y2, hy, ⟨τa, τb, hcab, herr, hnb⟩, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨w, σ, hσ, hFk, hclm⟩ := hRin _ _ hR
    obtain ⟨rest, hrest, hρ'⟩ := compS_reassoc hclm (ResU.CompS.comm hy)
    refine ⟨w, σ, hσ, hFk, y1, rest, hρ', hrest, fun X hX => ?_⟩
    exact Or.inr (Or.inl ⟨K, err, pure_sep_mk hpur ⟨y1, _, hX,
      ⟨τa, τb, hcab, errOkN_twin hTT' herr, hnb⟩, hRout k w σ hσ hFk⟩⟩)
  · -- a stop: seal the cell in the continuation's share
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa', ρk, hcak, hPA, hGk, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨w, σ', h', hw', R, rest, hk1, hk2⟩ := hG _ _ _ hGk
    obtain ⟨hqu, hwc⟩ := hT m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc'⟩ := hTT' m i en hTe
    obtain ⟨y, hy1, hy2⟩ := compS_lcomm hk1 hcak
    obtain ⟨R', hR', hσR'⟩ := compS_lcomm hk2 hy1
    refine ⟨w, σ', h', hw', R', y, hy2, hσR', fun X hX => ?_⟩
    obtain ⟨ρk', hRk, hX'⟩ := compS_reassoc hR' hX
    have hback : ∀ (σB ac X₀ W : WRes), ResU.CompS R σB ac →
        ResU.CompS σ' (ResU.single l (CellU.ownOf w)) W → ResU.CompS ac W X₀ →
        ResU.CompS ρk σB X₀ := by
      intro σB ac X₀ W hac hW hX₀
      obtain ⟨t, ht1, ht2⟩ := compS_reassoc hac hX₀
      obtain ⟨ac3, hac3, hW3⟩ := compS_lcomm (ResU.CompS.comm ht1) ht2
      obtain ⟨WR, hWR, hX₀'⟩ := compS_reassoc' hac3 hW3
      obtain ⟨ac2, hac2, hac2W⟩ := compS_exch hW hWR
      obtain rfl : ac2 = rest := ResU.CompS.functional hac2 hk2
      obtain rfl : WR = ρk := ResU.CompS.functional (ResU.CompS.comm hac2W) hk1
      exact hX₀'
    have hwe : ∀ ls'', en'.wc ls' ls'' ρk' → en.wc ls' ls'' ρk := by
      intro ls'' he
      rw [hwc', hwc] at he; rw [hwc]
      exact extF_seal hk1 hk2 hRk (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) he
    refine Or.inr (Or.inr ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩
      ⟨ρa', ρk', hX', hPA' ▸ hPA, fun hu' => absurd (hq'.symm.trans hu') hqu, fun ls'' he =>
        ⟨fun k' hk' w' σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩)
    · simp only [erwpC, show k' < n by omega, if_true]
      obtain ⟨ac, hac, hacX⟩ := compS_exch hRk hXB
      refine ih k' (by omega) ls'' _ w σ' h' k hw' ac XB (ResU.CompS.comm hacX)
        fun W X₀ hW hX₀ => ?_
      have hc := (hcont ls'' (hwe ls'' he)).1 k' (by omega) w' σB X₀ (hPB' ▸ hB)
        (hback σB ac X₀ W hac hW hX₀)
      simp only [erwpC, show k' < n by omega, if_true] at hc
      exact hc
    · have hql' : en.q ≠ .lin := hq' ▸ hql
      refine hcan m i en en' hTe hTe' ha hql' k ls'' K w σ' h' hw' R ρk'
        (ResU.CompS.comm hRk) fun W X₀ hW hX₀ => ?_
      obtain rfl : X₀ = ρk := by
        have h0 := hback PMap.empty R X₀ W (ResU.comp_empty_right R) hW hX₀
        exact ResU.CompS.functional h0 (ResU.comp_empty_right ρk)
      exact (hcont ls'' (hwe ls'' he)).2 hql'

/-- **Mut Anti-Frame at `erwp` across stops, raises and layered cancel runs** (`erwp_M_antiFrameC`
extended as `erwp_M_frame_cancelRunCR` extends the Mut Frame). The callback's table is the
guarded `opTableGR T G Rin`: its stops carry the fold (`hG`), its raises the claim (`hRin`). The
anti-frame's stops are at the twin `T′`, the cell sealed in the share; its raises carry the claim
sealed into the source's entry (`hRout`); a cancellable stop's cancel obligation is transferred by
`hcan`. -/
theorem erwp_M_antiFrameCR {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T T' : OpTabN}
    (hTT' : T.Twin T')
    (hT : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    {G : ShareG} (hG : ∀ k ls ρ, G k ls ρ → CellFold l β F k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw)))
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ k ls (K : Kont) (w : Val) (σ : WRes) (h : σ.InStratum β)
        (hw : F k w ⟨σ, h⟩) (R ρk' : WRes),
        ResU.CompS (ResU.single l (CellU.mutOf β w σ h (F k) hw)) R ρk' →
        (∀ W X, ResU.CompS σ (ResU.single l (CellU.ownOf w)) W → ResU.CompS R W X →
          cancelOKN en k ls K X) →
        cancelOKN en' k ls K ρk')
    {Q : PostN} :
    ∀ n ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat) (hwit : F j v ⟨σP, hstr⟩)
      (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwp (ℍ := ℍ) Φ (opTableGR T G Rin) (AFPost l β F Q) n ls e X) →
      erwp (ℍ := ℍ) Φ (opTableR T' Rout) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e v σP hstr j hwit ρa ρ hsplit hA
  rw [erwp_eq]
  refine rwpG_M_antiFrameG hΦ hF hsplit fun W X hW hX => ?_
  have h := hA W X hW hX
  rw [erwp_eq] at h
  refine rwpG_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ⟨v', rfl, w, σ', h', hw', R, rest, h1, h2, hQ⟩ | ⟨K, m, i, v₀, en, hp⟩ |
      ⟨K, m, i, v₀, en, hp⟩
  · exact ⟨w, σ', h', hw', R, rest, h1, h2, fun X hX => Or.inl ⟨v', rfl, hQ X hX⟩⟩
  · -- a stop: seal the cell in the continuation's share
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa', ρk, hcak, hPA, hGk, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨w, σ', h', hw', R, rest, hk1, hk2⟩ := hG _ _ _ hGk
    obtain ⟨hqu, hwc⟩ := hT m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc'⟩ := hTT' m i en hTe
    obtain ⟨y, hy1, hy2⟩ := compS_lcomm hk1 hcak
    obtain ⟨R', hR', hσR'⟩ := compS_lcomm hk2 hy1
    refine ⟨w, σ', h', hw', R', y, hy2, hσR', fun X hX => ?_⟩
    obtain ⟨ρk', hRk, hX'⟩ := compS_reassoc hR' hX
    have hback : ∀ (σB ac X₀ W : WRes), ResU.CompS R σB ac →
        ResU.CompS σ' (ResU.single l (CellU.ownOf w)) W → ResU.CompS ac W X₀ →
        ResU.CompS ρk σB X₀ := by
      intro σB ac X₀ W hac hW hX₀
      obtain ⟨t, ht1, ht2⟩ := compS_reassoc hac hX₀
      obtain ⟨ac3, hac3, hW3⟩ := compS_lcomm (ResU.CompS.comm ht1) ht2
      obtain ⟨WR, hWR, hX₀'⟩ := compS_reassoc' hac3 hW3
      obtain ⟨ac2, hac2, hac2W⟩ := compS_exch hW hWR
      obtain rfl : ac2 = rest := ResU.CompS.functional hac2 hk2
      obtain rfl : WR = ρk := ResU.CompS.functional (ResU.CompS.comm hac2W) hk1
      exact hX₀'
    have hwe : ∀ ls'', en'.wc ls' ls'' ρk' → en.wc ls' ls'' ρk := by
      intro ls'' he
      rw [hwc', hwc] at he; rw [hwc]
      exact extF_seal hk1 hk2 hRk (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) he
    refine Or.inr (Or.inl ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩
      ⟨ρa', ρk', hX', hPA' ▸ hPA, fun hu' => absurd (hq'.symm.trans hu') hqu, fun ls'' he =>
        ⟨fun k' hk' w' σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩)
    · simp only [erwpC, show k' < n by omega, if_true]
      obtain ⟨ac, hac, hacX⟩ := compS_exch hRk hXB
      refine ih k' (by omega) ls'' _ w σ' h' k hw' ac XB (ResU.CompS.comm hacX)
        fun W X₀ hW hX₀ => ?_
      have hc := (hcont ls'' (hwe ls'' he)).1 k' (by omega) w' σB X₀ (hPB' ▸ hB)
        (hback σB ac X₀ W hac hW hX₀)
      simp only [erwpC, show k' < n by omega, if_true] at hc
      exact hc
    · have hql' : en.q ≠ .lin := hq' ▸ hql
      refine hcan m i en en' hTe hTe' ha hql' k ls'' K w σ' h' hw' R ρk'
        (ResU.CompS.comm hRk) fun W X₀ hW hX₀ => ?_
      obtain rfl : X₀ = ρk := by
        have h0 := hback PMap.empty R X₀ W (ResU.comp_empty_right R) hW hX₀
        exact ResU.CompS.functional h0 (ResU.comp_empty_right ρk)
      exact (hcont ls'' (hwe ls'' he)).2 hql'
  · -- a `raise`: the claim sealed again, carried out
    obtain ⟨⟨rfl, hK, hTe, hab⟩, σ₁, ρR, hcσR, hpa, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨w, σ, hσ, hFk, hclm⟩ := hRin _ _ hR
    obtain ⟨en', hTe', -, hab', hPA', -, -⟩ := hTT' m i en hTe
    obtain ⟨rest, hrest, hρ'⟩ := compS_reassoc hclm (ResU.CompS.comm hcσR)
    refine ⟨w, σ, hσ, hFk, σ₁, rest, hρ', hrest, fun X hX => ?_⟩
    exact Or.inr (Or.inr ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans hab⟩
      ⟨σ₁, _, hX, hPA' ▸ hpa, hRout k w σ hσ hFk⟩⟩)

/-! ### A `mut` cell's witness -/

/-- **A `mut` cell's witness is consistent with a view the cell is consistent with**: the cell's
exclusive walk is the cell beside its witness's (`ExW.single_mut_inv`). -/
theorem consistentX_mut_wit {c : Loc → Option Life} {l : Loc} {b : Life} {w : Val} {χ : WRes}
    {hχ : χ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P w ⟨χ, hχ⟩}
    (hc : ConsistentX c (ResU.single l (CellU.mutOf b w χ hχ P hw)))
    (hv : ResU.Valid (ResU.single l (CellU.mutOf b w χ hχ P hw))) : ConsistentX c χ := by
  intro e₀ he₀ x ψ hg hk
  obtain ⟨σ, e, a, he, -, -⟩ := hv
  obtain ⟨e₀', he₀', hcomp⟩ := ExW.single_mut_inv he
  obtain rfl := ExS.functional he₀ he₀'
  exact hc e he x ψ (compS_get_left_nonimm (ResU.CompS.comm hcomp) hg (by rw [hk]; decide)).2 hk

/-- **A `mut` cell's witness's exclusive walk misses the cell's location.** -/
theorem exS_wit_none {l : Loc} {b : Life} {w : Val} {χ : WRes} {hχ : χ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P w ⟨χ, hχ⟩}
    (hv : ResU.Valid (ResU.single l (CellU.mutOf b w χ hχ P hw))) :
    ∀ e, ExS χ e → e.get l = none := by
  intro e₀ he₀
  obtain ⟨σ, e, a, he, -, -⟩ := hv
  obtain ⟨e₀', he₀', hcomp⟩ := ExW.single_mut_inv he
  obtain rfl := ExS.functional he₀ he₀'
  exact (compS_get_left_nonimm hcomp (ResU.single_get_self _ _)
    (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c)).1

/-- The cancel run at a guarded table, ending at the claim. -/
def cancelOblGN (Φ : LocFam) (T₁ : OpTabN) (G : ShareG) (R : Nat → WProp) :
    Nat → List SRec → Expr → WProp :=
  fun k ls e => erwp (ℍ := ℍ) Φ (cancelTabGR T₁ G R) (fun _ _ _ _ => False) k ls e

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC)
open BoCa.Fig16.LogRel.Core.Chain.SI.Hardest791 (rwp_det'')
open BoCa.BoLo (Heap Kont ubindE Head performE raiseE cancelVal opPayload)

/-! ### The lender's guarded twin -/

/-! ### The suspending reborrow -/

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
