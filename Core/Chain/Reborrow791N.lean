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
* `withbor3S_compat`, `constN_w3`.
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

mutual
/-- **The lender's guarded table of a row's layers**: `tabR`'s entries, every capturable one's
cancel obligation the cancel run at its cancel row's own guarded table, its stops guarded by `G`,
ending at `R`. The Mut Frame inside an anti-frame produces it (`erwp_M_frame_cancelRunCRG`). -/
def tabG (R : Nat → WProp) (G : ShareG) : CTy → LSub → LocTy → (Loc → Option Life) → OpTabN
  | .eff m i q A B fin _ C, δ, Θ, c => extTabN m i
      (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) (fun k v ρ => vN (ℍ := ℍ) B δ Θ k v ρ)
        (finG R G fin δ Θ c))
      (tabG R G C δ Θ c)
  | _, _, _, _ => OpTabN.empty
/-- The guarded cancel obligation of a cancel row: `none` at `⊤`. -/
def finG (R : Nat → WProp) (G : ShareG) : CTy → LSub → LocTy → (Loc → Option Life) →
    Option (Nat → List SRec → Expr → WProp)
  | .top, _, _, _ => none
  | .eff m i q A B fin _ C, δ, Θ, c => some (cancelOblGN (ℍ := ℍ) (Θ.view c) (extTabN m i
      (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) (fun k v ρ => vN (ℍ := ℍ) B δ Θ k v ρ)
        (finG R G fin δ Θ c))
      (tabG R G C δ Θ c)) G R)
  | .ret _, _, Θ, c => some (cancelOblGN (ℍ := ℍ) (Θ.view c) OpTabN.empty G R)
  | .arr _ _, _, Θ, c => some (cancelOblGN (ℍ := ℍ) (Θ.view c) OpTabN.empty G R)
  | .amp _ _, _, Θ, c => some (cancelOblGN (ℍ := ℍ) (Θ.view c) OpTabN.empty G R)
  | .all _ _ _, _, Θ, c => some (cancelOblGN (ℍ := ℍ) (Θ.view c) OpTabN.empty G R)
  | .nu _, _, Θ, c => some (cancelOblGN (ℍ := ℍ) (Θ.view c) OpTabN.empty G R)
end

theorem finG_eq (R : Nat → WProp) (G : ShareG) {F : CTy} (hF : F ≠ .top) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) :
    finG (ℍ := ℍ) R G F δ Θ c =
      some (cancelOblGN (ℍ := ℍ) (Θ.view c) (tabG (ℍ := ℍ) R G F δ Θ c) G R) := by
  cases F <;> simp_all [finG, tabG]

/-- **An entry of `tabN` is a layer's, and every `tabG` has the layer's entry at the same key.** -/
theorem tab_lookupNG (R : Nat → WProp) (G : ShareG) : ∀ (F : CTy) {δ₁ : LSub} {Θ₁ : LocTy}
    {c₁ : Loc → Option Life} {m j : UInt32} {en : OpEntN},
    tabN (ℍ := ℍ) F δ₁ Θ₁ c₁ m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₁ Θ₁ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) B δ₁ Θ₁ k v ρ) (finN (ℍ := ℍ) fin δ₁ Θ₁ c₁) ∧
      ∀ (δ₂ : LSub) (Θ₂ : LocTy) (c₂ : Loc → Option Life),
        tabG (ℍ := ℍ) R G F δ₂ Θ₂ c₂ m j =
          some (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₂ Θ₂ k v ρ)
            (fun k v ρ => vN (ℍ := ℍ) B δ₂ Θ₂ k v ρ) (finG (ℍ := ℍ) R G fin δ₂ Θ₂ c₂))
  | .eff m₀ i₀ q A B fin rc C, δ₁, Θ₁, c₁, m, j, en, h => by
      simp only [tabN] at h
      unfold extTabN at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun δ₂ Θ₂ c₂ => by
          simp only [tabG, extTabN, if_pos hmj]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupNG R G C h
        exact ⟨q', A', B', fin', .inr hL, he, fun δ₂ Θ₂ c₂ => by
          simp only [tabG, extTabN, if_neg hmj]; exact hR δ₂ Θ₂ c₂⟩
  | .ret _, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .arr _ _, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .amp _ _, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .top, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .all _ _ _, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .nu _, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h

/-- **An entry of `tabG` is a layer's, and every `tabR` has the layer's entry at the same key.** -/
theorem tab_lookupG (R : Nat → WProp) (G : ShareG) : ∀ (F : CTy) {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {m j : UInt32} {en : OpEntN},
    tabG (ℍ := ℍ) R G F δ Θ c m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entN q B (fun k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) (finG (ℍ := ℍ) R G fin δ Θ c) ∧
      ∀ R' : Nat → WProp, tabR (ℍ := ℍ) R' F δ Θ c m j =
        some (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
          (fun k v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) (finR (ℍ := ℍ) R' fin δ Θ c))
  | .eff m₀ i₀ q A B fin rc C, δ, Θ, c, m, j, en, h => by
      simp only [tabG] at h
      unfold extTabN at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R' => by
          simp only [tabR, extTabN, if_pos hmj]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupG R G C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R' => by
          simp only [tabR, extTabN, if_neg hmj]; exact hR R'⟩
  | .ret _, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h
  | .arr _ _, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h
  | .amp _ _, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h
  | .top, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h
  | .all _ _ _, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h
  | .nu _, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h

/-- **The callback's table and the lender's guarded twin agree but for the cancel obligations**
(`tabN_tabR_twin`'s argument). -/
theorem tabN_tabG_twin {x : LifeVar} {bnd : Lifetime.Life} {α : Life} {F : CTy}
    (hF : F.SuspendC x bnd) (R : Nat → WProp)
    (G : ShareG) (δ : LSub) (Θ₁ Θ₂ : LocTy) (c₁ c₂ : Loc → Option Life)
    (hΘ : ∀ A : VTy, VOutlives LifeCtx.empty bnd A → vN (ℍ := ℍ) A δ Θ₁ = vN (ℍ := ℍ) A δ Θ₂) :
    (tabN (ℍ := ℍ) F (δ.extend x α) Θ₁ c₁).Twin (tabG (ℍ := ℍ) R G F δ Θ₂ c₂) := by
  intro m i en h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNG R G F h
  obtain ⟨-, hA, hB, hOA, hOB, -, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR δ Θ₂ c₂, rfl, rfl, ?_, ?_, rfl⟩
  · simp only [entN, vN_extend_of_not_free (ℍ := ℍ) hA δ α, hΘ A hOA]
  · simp only [entN, vN_extend_of_not_free (ℍ := ℍ) hB δ α, hΘ B hOB]

/-- The guarded twin and the lender's twin at the same world and view agree but for the cancel
obligations. -/
theorem tabG_tabR_twin (R : Nat → WProp) (G : ShareG) (R' : Nat → WProp) (F : CTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) :
    (tabG (ℍ := ℍ) R G F δ Θ c).Twin (tabR (ℍ := ℍ) R' F δ Θ c) := by
  intro m i en h
  obtain ⟨q, A, B, fin, -, rfl, hR⟩ := tab_lookupG R G F h
  exact ⟨_, hR R', rfl, rfl, rfl, rfl, rfl⟩

/-- A row meeting `CTy.SuspendC` may be stopped at under an anti-frame. -/
theorem tabG_afok {x : LifeVar} {bnd : Lifetime.Life} {F : CTy} (hF : F.SuspendC x bnd) (R : Nat → WProp) (G : ShareG)
    (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) :
    ∀ m i en, tabG (ℍ := ℍ) R G F δ Θ c m i = some en → en.abort = false →
      en.q ≠ .unr ∧ en.wc = extF := by
  intro m i en h _
  obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupG R G F h
  exact ⟨(layer_suspend F hF hL).1, rfl⟩

/-- **The lender's guarded cancel obligations, from the callback's** (`tabR_can` with the folds
recorded), by induction on how deep cancel rows nest. The callback's table is at the world with the lend at a fresh `α` and the view moved
there; the lender's at the world and view without it. At a capturable entry, the callback's
cancel run at its cancel row's table, framed by `erwp_M_frame_cancelRunCRG` at that table (the
callback's view is the relation's `Φ.set`, `LocTy.view_add`), its own nested cancel obligations by
the induction. -/
theorem tabG_can {x : LifeVar} {bnd : Lifetime.Life} {α : Life} {δ : LSub} {Θ : LocTy}
    (hf : Θ.Fresh α) (hLt : LtLife δ bnd α) {c : Loc → Option Life} {l : Loc}
    {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC x bnd →
    ∀ m i en en', tabN (ℍ := ℍ) F (δ.extend x α) (Θ.add l α Fam) (setLife c l α) m i = some en →
      tabG (ℍ := ℍ) (claimR l α Fam) (CellFold l α Fam) F δ Θ c m i = some en' → en.abort = false →
      en.q ≠ .lin →
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
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupN F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF m i en en' h h' ha hql k ls K ρk ρp Z ρkL W'' v'' χ hχ P'' hw'' hno hZ hZd hdZd
    hPk hW'' hkL hc
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNG (claimR l α Fam) (CellFold l α Fam) F h
  rw [hR δ Θ c] at h'
  cases Option.some.inj h'
  have hcap := entN_capB ha hql
  have hfin := (layer_suspend F hF hL).2.2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  intro P' hP'
  simp only [entN, hcap, if_true] at hP' hc
  by_cases htop : fin = .top
  · subst htop; simp [finG] at hP'
  rw [finG_eq _ _ htop] at hP'
  cases Option.some.inj hP'
  have hin := hc _ (finN_eq htop _ _ _)
  refine erwp_M_frame_cancelRunCRG (Φ := Θ.view c) hFam
    (tabN_lendOKCR_C hfin δ hLt (Θ.add l α Fam) (setLife c l α))
    (tabN_tabG_twin hfin _ _ δ (Θ.add l α Fam) Θ (setLife c l α) c
      (fun A' hO => vN_add_eq_bnd hO δ hLt hf l Fam))
    (ih fin hfd hfin) k k le_rfl ls _ v'' χ W'' (Z.del l) ρkL hχ hdZd P'' hPk hw''
    (ResU.CompS.comm hW'') (ResU.CompS.comm hkL) (fun BM hBM => ?_)
  obtain rfl := ResU.CompS.functional hBM hZd
  rw [← LocTy.view_add]
  exact erwp_garbage hZ hno hin

/-- **The anti-frame's cancel obligations, from the guarded twin's**, by induction on how deep
cancel rows nest. At a capturable entry the inner cancel run, from the opened cell at its cancel
row's guarded table, is the anti-frame's cancel run from the sealed cell at that row's `tabR`
(`erwp_M_antiFrame_cancelRunCR`), its own nested cancel obligations by the induction. -/
theorem tabR_canA {x : LifeVar} {bnd : Lifetime.Life} {δ : LSub} {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life}
    {l : Loc} {β : Life} {Fo : Nat → Val → SPropS Loc Val β}
    (hF : (Θ.view c) l = some ⟨β, Fo⟩) {G : ShareG}
    (hG : ∀ k ls ρ, G k ls ρ → CellFold l β Fo k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β Fo k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : Fo k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (Fo k) hw))) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC x bnd →
    ∀ m i en en', tabG (ℍ := ℍ) Rin G F δ Θ c m i = some en →
      tabR (ℍ := ℍ) Rout F δ Θ c m i = some en' → en.abort = false → en.q ≠ .lin →
      ∀ k ls (K : Kont) (w : Val) (σ : WRes) (h : σ.InStratum β)
        (hw : Fo k w ⟨σ, h⟩) (R ρk' : WRes),
        ResU.CompS (ResU.single l (CellU.mutOf β w σ h (Fo k) hw)) R ρk' →
        (∀ W X, ResU.CompS σ (ResU.single l (CellU.ownOf w)) W → ResU.CompS R W X →
          cancelOKN en k ls K X) →
        cancelOKN en' k ls K ρk' := by
  intro d
  induction d with
  | zero =>
      intro F hd hF m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupG Rin G F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hFs m i en en' h h' ha hql k ls K w σ hσ hw R ρk' hsplit hc
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupG Rin G F h
  rw [hR Rout] at h'
  cases Option.some.inj h'
  have hcap := entN_capB ha hql
  have hfin := (layer_suspend F hFs hL).2.2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  intro P' hP'
  simp only [entN, hcap, if_true] at hP'
  by_cases htop : fin = .top
  · subst htop; simp [finR] at hP'
  rw [finR_eq _ htop] at hP'
  cases Option.some.inj hP'
  refine erwp_M_antiFrame_cancelRunCR (Φ := Θ.view c) (LocTy.view_down hΘ c) hF
    (tabG_tabR_twin Rin G Rout fin δ Θ c) (tabG_afok hfin Rin G δ Θ c) hG hRin hRout
    (ih fin hfd hfin) k ls _ w σ hσ k hw R ρk' hsplit fun W X hW hX => ?_
  exact hc W X hW hX _ (by simp only [entN, hcap, if_true]; exact finG_eq Rin G htop δ Θ c)

/-- **The finaliser consumes the source**: `λ_. d ℓ` from a `Mut @a A` value at `ℓ`, by `d`'s
judgment at `Mut @a A ⊸ 1` (`fin_claim` at the reborrow's source). -/
theorem fin_claimM {a : Lifetime.Life} {A : VTy} {d : Expr} (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.mut a A) .unit))) {δ : LSub}
    {Θ : LocTy} (hΘ : Θ.OK) {c : Loc → Option Life} {l : Loc} {k : Nat} {ls : List SRec}
    {ρ : WRes} (h : vN (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l) ρ) (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) (Θ.view c) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (Val.lam (.app d (.val (Val.loc l))))) (.val .unit)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  refine rwp_det'' (Q := fun _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) hΦ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app d (.val (Val.loc l)))) =
      (Kont.appL .hole (Val.loc l)).plug d := by
    simp [Kont.plug, Expr.subst, subst_closedAt d (s := _) hdc (Nat.zero_le _), Val.loc]
  rw [e]
  refine rwp_bind hΦ _ ?_
  have hd0 := hd δ [] Θ c k ls PMap.empty (models_empty_any _) hΘ (consistentX_empty c) trivial rfl
  rw [show substAll [] d = d from psub_closedAt d [] hdc (Nat.zero_le 0)] at hd0
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty hd0) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls' Θ (LocTy.extR_refl Θ _)
    hΘ c k' le_rfl (Val.loc l) τ₂ τ hcτ (vN_le hk' h) hcτ'
  exact rwp_of_erwp_empty this

/-! ### The suspending reborrow -/

/-- **`withbor (3)` at a suspending row is a value of `!` its type**: `withborU d`, at
`Mut @a A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Mut @a A ⊗ B)` with `Σ` a
`Row.Suspend x bnd` row. Core's `withbor3U_compatX`, step by step (`scope-791-rule.md` §7.1):

1. the context owns nothing: the constant at `PMap.empty`;
2. the source is `loc ℓ` with its cell `ℓ ↦ mut(β, w₀, σ₀, F_o j₀)`, `F_o = famL β 𝒱⟦A⟧ Θ` and
   `Θ (ℓ, β) = F_o` (`vN`'s `Mut` clause);
3. the callback, at the world along `ExtR`;
4. both arrive at the world `Θ` the run is at (`vN_extR`, Core's `vC_local`);
5. the cell unpacked (`mutL`);
6. `MutFrame`'s premise read off the borrow: every value of `A` is in `Res_β` (`hunif`, the
   `Mut` clause's last conjunct);
7. the anti-frame at the source's own entry: the start is consistent with the view, so
   `c ℓ = β` (`consistentX_get`), and the view types `ℓ` with `F_o` (`reseal_at_entry`), which
   `erwp_M_antiFrameCR` reseals into;
8. the opened cell lent at a fresh `α` below `β`, the bound and the callback's stratum
   (`erwp_M_frameCRG`), the anti-frame across the callback's stops, raises and layered cancel
   runs (`erwp_M_antiFrameCR`, `tabR_canA`), the Mut Frame's cancel runs at their rows' guarded
   tables (`tabG_can`);
9. the fresh lifetime from `LocTy.exists_fresh`;
10. the borrow `Mut @α A` at `δ[x ↦ α]` (`vN_extend_of_not_free`, `lend_mutL`);
11. the callback at the world `Θ + (ℓ, α) ↦ famL α 𝒱⟦A⟧ Θ` and the view `setLife c ℓ α`, the
    relation's `Φ[ℓ ↦ (α, …)]` (`LocTy.view_add`), its table the guarded twin at `Θ`
    (`tabN_tabG_twin`, `vN_add_eq_bnd`);
12. its result `['x] B` back at `Θ` (`vN_local`);
13. the content handed back in `F_i k` is in `F_o k` (`hunif`, `vN_above`), and the resealed cell
    is a `Mut @a A` value again, beside the result and in every raise's claim; the claim is
    consistent (`erwp_claimX`) and the finaliser frame consumes it with `d`
    (`erwp_ubindClaimRT`, `fin_claimM`).

Premises, and the rule that supplies each: `hbnd` is the bound's definedness, which Core's rule
gets from its bound `Δ.meetOfDom` (`Const791.OK`); `hA`, `hB`, `hS`, `hdc` are `withbor3U`'s with
`Row.Suspend` for `Row.Unwind` (`Const791.OK`); `hd` is the fundamental property at `d`'s
derivation, the premise `CDerives Δ Γ d (Mut @a A ⊸ 1)` read semantically. -/
theorem withbor3S_compat {a : Lifetime.Life} {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {d : Expr} (hbnd : LifeCtx.empty.Defines bnd) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Suspend x bnd)
    (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.mut a A) .unit))) (δ : LSub)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withbor3UTy a x bnd A B S)) δ Θ₀ n (withborUV d) PMap.empty := by
  -- step 1
  refine ⟨rfl, fun Θ₁ _ _ c₁ _ ls => ?_⟩
  intro Θ₂ _ _ c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  -- steps 2–4
  intro Θ hE₃ hΘ c k' hk' f ρf ρ'' hc' hf hcon
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ Θ' j u r with hP
  obtain ⟨α₀, hα₀, (β : Life), hα₀β, hm, hunif⟩ := vN_le hk' (vN_extR _ δ k u ρu hE₃ hu)
  -- step 5
  obtain ⟨l, w₀, σ₀, hσ₀, j₀, hw₀, hkj, rfl, hl, rfl⟩ := id hm
  rw [cN_effOf]
  refine erwp_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set Fo := CTy.effOf S (.tensor (.mut a A) B) with hFo
  set T := tabN (ℍ := ℍ) Fo δ Θ c with hTdef
  have hTd : T.Down := tabN_down _ δ Θ hΘ.1 c
  have hQo : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.mut a A) B) δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ k v ρ h
  set Qin : PostN := fun k _ b ρ =>
    vN (ℍ := ℍ) (.tensor (.mut a A) B) δ Θ k (Val.pair (Val.loc l) b) ρ with hQin
  refine erwp_det hΦ (opTableN_down hTd) hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ (opTableN_down hTd) hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (thenE ((Expr.var 2).pair (Expr.var 0)) (d.app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFv l) (DFv d l)) (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NFv, DFv, Val.shift, Val.pair,
      Val.loc, Val.lam, Expr.val, Val.prim, subst_closedAt d (s := _) hdc (Nat.zero_le _)]
  rw [e₃]
  -- the source's cell
  set cellβ := ResU.single l (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀) with hcellβ
  have hvu : ResU.Valid cellβ := (ResU.Valid.split hc' hv'').1
  have hkm : (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hget : ρ''.get l = some (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀) :=
    (ResU.CompS.get_left_of_ne_imm hc' (ResU.single_get_self _ _) hkm).2
  -- step 7: the source's cell is at its view lifetime, and the view types it with `F_o`
  have hcl : c l = some β := by
    have h := consistentX_get hcon hv'' hget (CellU.kind_mutOf _ _ _ _ _ _)
    rwa [CellU.at_mutOf] at h
  obtain ⟨-, -, -, -, -, -, -, hFv, -⟩ :=
    reseal_at_entry (Θ' := Θ) (fun _ _ _ h => h) hcl (vN_fam_down A δ β Θ) hm
  -- the parts of the start are consistent with the view
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_mut_wit (consistentX_left hc' hcon hv'') hvu
  -- steps 6 and 9: the lend's lifetime, fresh, below `β`, the bound and the callback's stratum
  obtain ⟨γ, hγ⟩ := hbnd δ (models_empty_any _)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(β ⊓ βf ⊓ γ))
  have hαlt : α < β ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαβ : α ≤ β := hαlt.le.trans (inf_le_left.trans inf_le_left)
  have houtP : σ₀.InStratum α := hσ₀.mono hαβ
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ bnd α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  -- step 10
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P' : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ' Θ' j u r with hP'
  set Fam : Nat → Val → SPropS Loc Val α := famL α P' Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ
  have hwit : Fam j₀ w₀ ⟨σ₀, houtP⟩ :=
    (vN_above A δ' Θ houtP).mpr (by rw [hAδ]; exact (vN_above A δ Θ hσ₀).mp hw₀)
  -- step 13's inclusion: the content handed back in `F_i k` is in `F_o k`
  have hoi : ∀ k w σ (h : σ.InStratum α), Fam k w ⟨σ, h⟩ →
      ∃ h' : σ.InStratum β, famL β P Θ k w ⟨σ, h'⟩ := by
    intro k w σ h hw
    have hv : vN (ℍ := ℍ) A δ Θ k w σ := by rw [← hAδ]; exact (vN_above A δ' Θ h).mp hw
    exact ⟨hunif Θ k w σ hv, (vN_above A δ Θ (hunif Θ k w σ hv)).mpr hv⟩
  have hG : ∀ k ls ρ, CellFold l α Fam k ls ρ → CellFold l β (famL β P Θ) k ls ρ := by
    rintro k ls ρ ⟨w, χ, h, hw, R, rest, h1, h2⟩
    obtain ⟨h', hw'⟩ := hoi k w χ h hw
    exact ⟨w, χ, h', hw', R, rest, h1, h2⟩
  have hRin : ∀ k ρ, claimR l α Fam k ρ → claimR l β (famL β P Θ) k ρ := by
    rintro k ρ ⟨w, σ, h, hw, hcl'⟩
    obtain ⟨h', hw'⟩ := hoi k w σ h hw
    exact ⟨w, σ, h', hw', hcl'⟩
  set Rout : Nat → WProp := fun k ρ => vN (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l) ρ with hRoutd
  have hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : famL β P Θ k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (famL β P Θ k) hw)) :=
    fun k w σ h hw => ⟨α₀, hα₀, β, hα₀β, ⟨l, w, σ, h, k, hw, le_rfl, rfl, hl, rfl⟩, hunif⟩
  -- step 11: the callback's world and view
  set Θ' := Θ.add l α Fam with hΘ'
  set c' := setLife c l α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ.2
    exact ⟨LocTy.down_add hΘ.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hview : Θ'.view c' = (Θ.view c).set l α Fam := LocTy.view_add Θ c l α Fam
  have hcf' : ConsistentX c' ρf :=
    consistentX_setLife hcf (exS_none_of_part hc' hv'' (ResU.single_get_self _ _) hkm) α
  have hcσ' : ConsistentX c' σ₀ := consistentX_setLife hcσ (exS_wit_none hvu) α
  set Rc := claimR l α Fam with hRc
  set Gc := CellFold l α Fam with hGc
  have hFS : Fo.SuspendC x bnd := suspendC_effOf hS _
  have hbase : tabN (ℍ := ℍ) (CTy.effOf S (.box (.var x) B)) δ' Θ' c' =
      tabN (ℍ := ℍ) Fo δ' Θ' c' := tabN_effOf_base S _ _ δ' Θ' c'
  have hTw : (tabN (ℍ := ℍ) (CTy.effOf S (.box (.var x) B)) δ' Θ' c').Twin
      (tabG (ℍ := ℍ) Rc Gc Fo δ Θ c) := by
    rw [hbase]
    exact tabN_tabG_twin hFS Rc Gc δ Θ' Θ c' c (fun A' hO => vN_add_eq_bnd hO δ hLt hfr l Fam)
  have hcanM := tabG_can (ℍ := ℍ) (δ := δ) hfr hLt (c := c) (l := l) hFamD Fo.cdepth Fo le_rfl hFS
  rw [← hbase] at hcanM
  have hcanA := tabR_canA (ℍ := ℍ) (x := x) (δ := δ) hΘ.1 hFv hG hRin hRout Fo.cdepth Fo le_rfl
    hFS
  -- step 8: the anti-frame at the source, across stops, raises and layered cancel runs
  have hAF := erwp_M_antiFrameCR (Φ := Θ.view c) hΦ hFv (tabG_tabR_twin Rc Gc Rout Fo δ Θ c)
    (tabG_afok hFS Rc Gc δ Θ c) hG hRin hRout hcanA (Q := Qin) k' ls
    (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) w₀ σ₀ hσ₀ j₀ hw₀ ρf ρ'' hc'
    (fun W X hW hX => ?_)
  · -- step 13: the claim consistent, the finaliser frame consuming it
    have hM' := erwp_claimX (c := c) hFS k' ls _ ρ'' hcon hAF
    refine erwp_ubindClaimRT hΘ.1 (F := Fo) (δ := δ) (c := c)
      (fun m i en h _ => by obtain ⟨o, ho, rfl, -⟩ := tabN_effOf_some h; exact (hS o ho).2.1)
      (NFv l) (DFv d l) (fun k ls ρ hR => fin_claimM hdc hd hΘ hR.1 hR.2) hQo
      (fun k ls b ρ hq => ?_) k' ls _ ρ'' hM'
    refine erwp_det hΦ (opTableN_down hTd) hQo
      (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, NFv]
    exact erwp_val (v := Val.pair (Val.loc l) b) hq
  -- step 8: the opened cell lent at `α`
  refine erwp_M_frameCRG (Φ := Θ.view c) (l := l) (A := α) (F := Fam) hFamD
    (tabN_lendOKCR hS _ δ hLt Θ' c') hTw hcanM (Q := AFPost l β (famL β P Θ) Qin)
    k' j₀ hkj ls _ w₀ σ₀ W ρf X houtP houtf (Fam j₀) (fun _ _ h => h) hwit
    (ResU.CompS.comm hW) (ResU.CompS.comm hX) (fun BM hBM => ?_)
  -- step 11: the callback, at the lend's world and view, from the borrow
  rw [← hview]
  have h1 := (hf Θ' ((LocTy.extA_add hfr l Fam).extR ρf) hOK' c' hcf' ls) α hLt
  have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ' k' (Val.loc l)
      (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam j₀) hwit)) :=
    ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l α P' hkj houtP hwit,
      fun Θ'' j u r h => (hunif Θ'' j u r (by rw [← hAδ]; exact h)).mono hαβ⟩
  have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
    (consistentX_single_mut hcσ' (by simp [hc'def, setLife]))
  have h2 := h1 Θ' (LocTy.extR_refl _ _) hOK' c' k' le_rfl (Val.loc l) _ BM hBM hcell hcBM
  rw [cN_effOf] at h2
  refine erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ BM h2
  obtain ⟨β', hβ', hbB, hst⟩ := hb
  rw [interp_ext_self] at hβ'
  cases Option.some.inj hβ'
  refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
  -- step 12: the result back at `Θ`; step 13: the content in `F_o k`, the cell resealed
  obtain ⟨h', hw'⟩ := hoi k w σ hσ hFσ
  obtain ⟨ac, hac, hacZ⟩ := compS_exch hY hZ
  have hbB' : vN (ℍ := ℍ) B δ Θ k b ρ' :=
    vN_local B δ Θ l α Fam k b ρ' hst (by rw [← hBδ]; exact hbB)
  exact ⟨w, σ, h', hw', ρ', ac, ResU.CompS.comm hacZ, ResU.CompS.comm hac, fun X' hX' =>
    ⟨Val.loc l, b, _, ρ', rfl, ResU.CompS.comm hX', hRout k w σ h' hw', hbB'⟩⟩

/-- **`ConstN` for `withbor (3)` at a suspending row**, from the fundamental property at the
finaliser's derivation. -/
theorem constN_w3 (hF : FundamentalN (ℍ := ℍ)) {a : Lifetime.Life} {x : LifeVar}
    {bnd : Lifetime.Life} {A B : VTy} {S : Row} {d : Expr} :
    ConstN (ℍ := ℍ) (.w3 a x bnd A B S d) := by
  rintro ⟨hbnd, hA, hB, hS, hdc, hder⟩ δ Θ n _
  exact withbor3S_compat hbnd hA hB hS hdc (hF _ _ _ _ hder) δ Θ n

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
