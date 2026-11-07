import Core.Chain.FamNew836N
import Core.Chain.FamCancel836N

/-!
# The `n`-cell Imm Frame and `slice_borrow` at `SemJN₀`  `[spec §9, §19, §23]`

Core's `wpTS_I_frameFam`/`wpG_I_frameFam` (`Core/SliceFrames.lean`) nest one Imm Frame per cell
of an owned array around the callback, by induction on the list (`wpG_I_frameList`). On the
chain:

* `erwp_I_frameRR` is the one-cell frame `erwp_I_frameR` with the callback's raises already
  carrying the inner frames' claims (as `erwp_M_frameRR` is for the Mut Frame);
* `erwp_I_frameListRN₀` is the list induction over it. Frame `j` lends its leaf `imm` at a
  lifetime `αⱼ` below the frame's rest, the payloads' and the result's strata and the callback's
  bound, its record `(pⱼ, αⱼ)` in the inner frames' world (`LocTy.addImm`); the run of the inner
  frames is read at the lender's view by `erwp_tieEntryR` (the table is abortive), as in
  `withbor1U_sem₀`. The callback receives every leaf at the innermost lifetime (`immCell` reads
  `α ⊑ ⊓s`), at the world holding every record (`LocTy.addImms`). Frame `j`'s output moves what the
  inner frames returned to the world without its record (`LocTy.extR_of_addImm`), and its claim
  joins theirs, the cells owned again (`claimL₀`);
* `sliceBorrowI_compatN₀` and `sliceBorrowIU_compatN₀` are Core's `sliceBorrowI_compatX` and
  `sliceBorrowIU_compatX` against it, with `withbor1_sem₀`'s and `withbor1U_sem₀`'s steps around
  the callback.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **A run at an abortive table, its raises carrying `R`, reads its tie only at its entry**
(`erwp_tieEntry` at `opTableR`). -/
theorem erwp_tieEntryR {Φ Φ' : LocFam} (hfam : Φ'.fam = Φ.fam) {T : OpTabN}
    (hab : ∀ m i en, T m i = some en → en.abort = true) {R : Nat → WProp} {Q : PostN} {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes} (hI : ∀ x ∈ Φ'.imm, x ∈ Φ.imm ∨ x ∈ ls)
    (h : erwp (ℍ := ℍ) Φ' (opTableR T R) Q n ls e ρ) :
    erwp (ℍ := ℍ) Φ (opTableR T R) Q n ls e ρ := by
  rw [erwp_eq] at h ⊢
  refine Goal791N.rwpG_tieEntry hfam hI (rwpG_mono (fun k ls' t σ ht => ?_) h)
  rcases ht with ht | ⟨K, m, i, v, en, hp⟩ | ht
  · exact Or.inl ht
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd (hab m i en hTe) (by rw [ha]; decide)
  · exact Or.inr (Or.inr ht)

/-! ### Records added to a world -/

/-- The world `Θ` with the records `xs` in front of its own. -/
def LocTy.addImms (Θ : LocTy) (xs : List SRec) : LocTy := ⟨Θ.fam, xs ++ Θ.imm⟩

theorem LocTy.addImms_nil (Θ : LocTy) : Θ.addImms [] = Θ := rfl

theorem LocTy.addImms_cons (Θ : LocTy) (x : SRec) (xs : List SRec) :
    Θ.addImms (x :: xs) = (Θ.addImms xs).addImm x := rfl

theorem LocTy.addImm_addImms (Θ : LocTy) (x : SRec) (xs : List SRec) :
    (Θ.addImm x).addImms xs = Θ.addImms (xs ++ [x]) := by
  simp [LocTy.addImms, LocTy.addImm]

/-- **Records lent at lifetimes whose strata hold `ρ` extend the world at `ρ`** (`n` of
`LocTy.extR_addImm`). -/
theorem LocTy.extR_addImms (Θ : LocTy) {ρ : WRes} :
    ∀ xs : List SRec, (∀ x ∈ xs, ρ.InStratum x.2) → Θ.ExtR (Θ.addImms xs) ρ
  | [], _ => LocTy.extR_refl Θ ρ
  | x :: xs, h =>
      (LocTy.extR_addImms Θ xs fun y hy => h y (List.mem_cons_of_mem _ hy)).trans
        (LocTy.extR_addImm (Θ.addImms xs) x.1 (h x (List.mem_cons_self ..)))

theorem LocTy.addImms_ok {Θ : LocTy} (hΘ : Θ.OK) (xs : List SRec) : (Θ.addImms xs).OK :=
  ⟨fun l' b F h => hΘ.1 l' b F h, let ⟨N, hN⟩ := hΘ.2; ⟨N, fun l' b h => hN l' b h⟩⟩

/-- **Imm Frame at `erwp` across stops, the inner raises already carrying a claim `R`.**
`erwp_I_frameR` with the callback's raises at `opTableR Tb R` (the claims of the frames inside
it): at a `raise` the borrow is garbage and the lend's claim `ρ_ℓ ● ρ_P̂(v)` joins `R`. `R` lies in
the lend's stratum (`hR`), so the lent cell is not in it. Its stops and returns are
`erwp_I_frameR`'s cases. -/
theorem erwp_I_frameRR {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    (P : List SRec → Val → WProp) (hPshape : ∀ ls ρ, P ls v ρ → vShape T δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {Tb : OpTabN} (hT : Tb.ILendOKR A) {R : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → ρ.InStratum A) {Q : PostN}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ n ls e (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A), ρb.InStratum A →
      P ls v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      ∀ ds, (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (opTableR Tb R) (IFPost l v P A Q) n
          (frameList ⟨l, v, ρP, T, δ⟩ ds A ls) e BI) →
      erwp (ℍ := ℍ) Φ (opTableR Tb (fun k => claimI l v ρP k ⋆ R k)) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρP ρlP ρb ρ houtP houtb hPv hclP hcρ ds hds hA
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  have houtlP : ρlP.InStratum A := inStratum_ownP hclP houtP
  rw [erwp_eq]
  refine rwpG_I_frameG l T δ hadm v houtP houtb hclP hcρ (hPshape ls ρP hPv) hds ?_
    (fun BI hBI => by
      have h := hA BI hBI
      rw [erwp_eq] at h
      exact h)
  intro k hk ls'' t ρ' ρp π Y hQin hnoρp h9 hls'' hGc hπdA hY hext hNX
  have hπl : π.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    ResU.compS_single_get_self (ResU.CompS.comm hGc) (ResU.del_get_self _ _)
  have hls''add : AddAt ls ls'' A :=
    ⟨fun x hx => (hls'' x).mpr ((addAt_frameList _ ds A ls).1 x hx),
     fun x hx hn => (addAt_frameList _ ds A ls).2 x ((hls'' x).mp hx) hn⟩
  rcases hQin with ⟨w, rfl, hwand', houtρ'⟩ | ⟨K, m, i, v₀, en, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · -- a return: 6.64's end, as printed (6.38's `ρ′(ℓ) = ∅` at the box)
    have hρ'l : ρ'.get l = none := ResU.six38_no_borrow_in_frame houtρ' h9 hπl
    have hppl : ρp.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
      (ResU.Comp.get_of_left_none h9 hρ'l).symm.trans hπl
    have hpd : ResU.CompS (ρp.del l) ρi ρp := ResU.del_compS hppl
    obtain ⟨G, hG, hGi⟩ := (ResU.CompS.assoc ρ' (ρp.del l) ρi π).mp ⟨ρp, hpd, h9⟩
    have hGl : G.get l = none :=
      (ResU.Comp.eq_none_iff hG l).mpr ⟨hρ'l, ResU.del_get_self _ _⟩
    obtain rfl : G = π.del l := eq_del_of_compS_single hGi hGl
    obtain ⟨Z1, hZ1, hρ'Z1⟩ := (ResU.CompS.assoc ρ' (ρp.del l) ρlP Y).mpr ⟨_, hG, hY⟩
    obtain ⟨R, hR, hRY⟩ :=
      (ResU.CompS.assoc ρ' ρlP (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨X, hX, hXR⟩ :=
      (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v)) ρP R).mp ⟨ρlP, hclP, hR⟩
    have hPv'' : P ls'' v ρP := hPloc ls ls'' ρP (extF_of_addAt hls''add ρP) hPv
    have hQ'' : Q k ls'' w R := (hwand' _ X rfl hX) ρP R hPv'' hXR
    have hRα : R.InStratum A := inStratum_compS hR houtρ' houtlP
    have hRl : ∀ ψ : CellU Loc Val, R.get l = some ψ → ψ.kind ≠ Kind.imm := by
      intro ψ eψ
      obtain ⟨ψ₁, eψ₁, kψ₁, -⟩ := compS_get_right' hR
        ((ResU.CompS.get_left_of_ne_imm hclP (ResU.single_get_self _ _) (by simp)).2)
      rw [eψ] at eψ₁; cases Option.some.inj eψ₁
      rw [kψ₁]; simp
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, hQ k ls'' ls w R (hext R _ hRY hRα hRl) hQ''⟩⟩
  · -- a stop: the borrow folded into the continuation's share
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hq, hwc⟩ := hT.entry m i en hTe ha
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨X, hX, haX⟩ := (ResU.CompS.assoc ρa ρk ρp π).mpr ⟨ρ', hcak, h9⟩
    have hρal : ρa.get l = none := ResU.six38_no_borrow_in_frame hρa haX hπl
    -- 6.116: `π ● ρᵢ = π`, so `X ● ρᵢ` is defined
    obtain ⟨π₂, hπ₂, hπ₂i⟩ := (ResU.CompS.assoc (π.del l) ρi ρi π).mp
      ⟨ρi, compS_imm_dup l _ v ρP houtP, hGc⟩
    obtain rfl : π = π₂ := ResU.CompS.functional hGc hπ₂
    obtain ⟨Xi, hXi, haXi⟩ := (ResU.CompS.assoc ρa X ρi π).mpr ⟨π, haX, hπ₂i⟩
    have hXil : Xi.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
      (ResU.Comp.get_of_left_none haXi hρal).symm.trans hπl
    have hXid : ResU.CompS (Xi.del l) ρi Xi := ResU.del_compS hXil
    obtain ⟨G, hG, hGi⟩ := (ResU.CompS.assoc ρa (Xi.del l) ρi π).mp ⟨Xi, hXid, haXi⟩
    have hGl : G.get l = none :=
      (ResU.Comp.eq_none_iff hG l).mpr ⟨hρal, ResU.del_get_self _ _⟩
    obtain rfl : G = π.del l := eq_del_of_compS_single hGi hGl
    have hXdA : (Xi.del l).InStratum A := ResU.CompS.inStratum_right hG hπdA
    obtain ⟨ρkL, hkL, haY⟩ := (ResU.CompS.assoc ρa (Xi.del l) ρlP Y).mpr ⟨_, hG, hY⟩
    have hPA' : en.PA k ls v₀ ρa := hT.paExt m i en hTe k ls'' ls v₀ ρa
      (hext ρa ρkL haY hρa (fun ψ h => by rw [hρal] at h; cases h)) hPA
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, ρkL, haY, hPA',
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun lsO he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)⟩
    simp only [erwpC, show k' < n by omega, if_true]
    have he' : extF ls lsO ρkL := by rw [hwc] at he; exact he
    -- the frame of the next segment: `(X ● ρᵢ)/ℓ ● σ_B`
    obtain ⟨ρbB, hρbB, hWXB⟩ :=
      (ResU.CompS.assoc ρlP (Xi.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
    have hσBA : σB.InStratum A := hT.pb m i en hTe _ _ _ _ hB
    have hdB : ρbB.InStratum A := inStratum_compS hρbB hXdA hσBA
    refine ih k' (by omega) lsO _ ρP ρlP ρbB XB houtP hdB
      (hPloc ls lsO ρP (extF_right hclP (extF_right hkL he')) hPv) hclP hWXB
      ds hds (fun BI' hBI' => ?_)
    -- the borrowed continuation, at the list it stopped at, with the garbage `ρ⁺ ● ρᵢ`
    have he'' : en.wc ls'' (frameList ⟨l, v, ρP, T, δ⟩ ds A lsO) ρk := by
      rw [hwc]
      exact extF_ifold hX hXi hXil hkL hclP hNX hls'' he'
    have hB' : en.PB k' (frameList ⟨l, v, ρP, T, δ⟩ ds A lsO) w σB :=
      hT.pbExt m i en hTe k' lsO _ w σB (ext_add (addAt_frameList _ ds A lsO) hσBA) hB
    obtain ⟨s1, hs1, h1'⟩ := (ResU.CompS.assoc (Xi.del l) σB ρi BI').mpr ⟨ρbB, hρbB, hBI'⟩
    obtain ⟨Xi', hXi', hXi'σ⟩ :=
      (ResU.CompS.assoc (Xi.del l) ρi σB BI').mp ⟨s1, ResU.CompS.comm hs1, h1'⟩
    obtain rfl : Xi = Xi' := ResU.CompS.functional hXid hXi'
    obtain ⟨s2, hs2, hXs2⟩ := (ResU.CompS.assoc X ρi σB BI').mpr ⟨Xi, hXi, hXi'σ⟩
    obtain ⟨Xσ, hXσ, hXσi⟩ :=
      (ResU.CompS.assoc X σB ρi BI').mp ⟨s2, ResU.CompS.comm hs2, hXs2⟩
    obtain ⟨s3, hs3, hks3⟩ := (ResU.CompS.assoc ρk ρp σB Xσ).mpr ⟨X, hX, hXσ⟩
    obtain ⟨Xk, hXk, hXkp⟩ :=
      (ResU.CompS.assoc ρk σB ρp Xσ).mp ⟨s3, ResU.CompS.comm hs3, hks3⟩
    have hc := (hcont _ he'').1 k' hk' w σB Xk hB' hXk
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact erwp_garbage hXσi (noOwn_single_imm l _ _ _ _) (erwp_garbage hXkp hnoρp hc)
  · -- a `raise`: the borrow garbage, the cell and payload the claim joining the one the `raise`
    -- carries
    obtain ⟨⟨rfl, hK, hTe, ha⟩, τ0, τR, hc0R, ⟨τa, τn, hcan, ⟨hPA, hnA⟩, hnn⟩, hRk⟩ :=
      pure_sep_iff.mp hp
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    -- `ρ′ = (τa ● τR) ● τn`, the first part in the lend's stratum
    obtain ⟨t1, ht1, hρ't1⟩ := compS_exch hcan hc0R
    have hρa' : t1.InStratum A := inStratum_compS ht1 hρa (hR _ _ hRk)
    obtain ⟨X, Xi, ρkL, hρal, haY, hkL, -, hX, hXi, -, -⟩ :=
      iFold hρa' hρ't1 h9 hnoρp hGc hπdA hY
    have hnoXi : NoOwn Xi :=
      noOwn_compS hXi (noOwn_compS hX hnn hnoρp) (noOwn_single_imm l _ _ _ _)
    -- `Y = τa ● (τR ● ρkL)`
    obtain ⟨bc, hbc, hτaY⟩ := compS_reassoc ht1 haY
    have hτal : τa.get l = none := ((ResU.Comp.eq_none_iff ht1 l).mp hρal).1
    have hPA' : en.PA k ls v₀ τa := hT.paExt m i en hTe k ls'' ls v₀ τa
      (hext τa bc hτaY hρa (fun ψ h => by rw [hτal] at h; cases h)) hPA
    -- `Y = (τa ● Xi/ℓ) ● (τR ● ρ_lP)`
    obtain ⟨ac, hac, hbc'⟩ := compS_lcomm hkL hbc
    obtain ⟨D, hD, hDY⟩ := compS_reassoc' hbc' hτaY
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨D, ac, hDY,
        ⟨τa, Xi.del l, hD, ⟨hPA', hnA⟩, noOwn_del hnoXi l⟩,
        ⟨ρlP, τR, ResU.CompS.comm hac, hclP, hRk⟩⟩⟩)⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head ubindE)

/-! ### `slice_borrow` at the pure row -/

/-! ### `slice_borrow` at an unwinding row -/

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
