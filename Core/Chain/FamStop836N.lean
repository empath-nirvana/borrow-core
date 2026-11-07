import Core.Chain.FamFrame836N

/-!
# The `n`-cell Mut Frame across raises  `[spec §9, §19, §62]`

Core's `wpG_M_frameFam` (`Core/SliceFrames.lean`) nests one Mut Frame per cell around a run
that may stop. On the chain the one-cell frame across raises is `erwp_M_frameR`: the callback's
raises at `opTableN T`, the lender's at `opTableR T (claimR ℓ A F)`, the `raise` carrying the
lend's claim. Nested, the inner frames' raises already carry their claims, so the frame one level
out is `erwp_M_frameR` with the callback's raises at `opTableR T R`: `erwp_M_frameRR`, the cell's
claim joining `R`. Its stops and returns are `erwp_M_frameR`'s cases.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE)

/-- **Mut Frame at `erwp` across stops, the inner raises already carrying a claim `R`.**
`erwp_M_frameR` with the callback's raises at `opTableR T R` (the claims of the frames inside
it): at a `raise` the borrow is folded and the cell's claim joins `R`. `R` lies in the lend's
stratum (`hR`), so the lent cell is not in it. -/
theorem erwp_M_frameRR {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T : OpTabN} (hT : T.LendOKR A) {R : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → ρ.InStratum A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableR T R) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableR T (fun k => claimR l A F k ⋆ R k)) Q n ls e ρ := by
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
  · -- a stop: as in `erwp_M_frame`
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hq, hwc⟩ := hT.entry m i en hTe ha
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
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, ρkL, haY, hPA,
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)⟩
    simp only [erwpC, show k' < n by omega, if_true]
    obtain ⟨ρbB, hρbB, hWXB⟩ :=
      (ResU.CompS.assoc W'' (Z.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
    have hdB : ρbB.InStratum (↓A) :=
      inStratum_compS hρbB hdZd (hT.pb m i en hTe _ _ _ _ hB)
    refine ih k' (by omega) k (le_of_lt hk') ls'' _ v'' χ W'' ρbB XB hχ hdB P'' hPk hw''
      (ResU.CompS.comm hW'') hWXB (fun BM' hBM' => ?_)
    have he' : en.wc ls' ls'' ρk := by rw [hwc] at he ⊢; exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW'' hkL he
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
  · -- a `raise`: the borrow folded, the cell's claim joining the one the `raise` carries
    obtain ⟨⟨rfl, hK, hTe, ha⟩, τ0, τR, hc0R, ⟨τa, τn, hcan, ⟨hPA, hnA⟩, hnn⟩, hRk⟩ :=
      pure_sep_iff.mp hp
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    -- `ρ′ = (τa ● τR) ● τn`, the first part in the lend's stratum
    obtain ⟨t1, ht1, hρ't1⟩ := compS_exch hcan hc0R
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
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨s0, s1, hYs,
        ⟨τa, Z.del l, hs0, ⟨hPA, hnA⟩, noOwn_del hnoZ l⟩,
        ⟨W'', τR, ResU.CompS.comm hs1, ⟨v'', χ, hs, hFk, ResU.CompS.comm hW''⟩, hRk⟩⟩⟩)⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
