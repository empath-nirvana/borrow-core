import Core.Chain.FamNew836N
import Core.Chain.FamCancel836N

/-!
# The `n`-cell Imm Frame and `slice_borrow` at `SemJN`  `[spec §9, §19, §23]`

Core's `wpTS_I_frameFam`/`wpG_I_frameFam` (`Core/SliceFrames.lean`) nest one Imm Frame per cell
of an owned array around the callback, by induction on the list (`wpG_I_frameList`). On the
chain:

* `erwp_I_frameRR` is the one-cell frame `erwp_I_frameR` with the callback's raises already
  carrying the inner frames' claims (as `erwp_M_frameRR` is for the Mut Frame);
* `erwp_I_frameListRN` is the list induction over it. Frame `j` lends its leaf `imm` at a
  lifetime `αⱼ` below the frame's rest, the payloads' and the result's strata and the callback's
  bound, its record `(pⱼ, αⱼ)` in the inner frames' world (`LocTy.addImm`); the run of the inner
  frames is read at the lender's view by `erwp_tieEntryR` (the table is abortive), as in
  `withbor1U_sem`. The callback receives every leaf at the innermost lifetime (`immCell` reads
  `α ⊑ ⊓s`), at the world holding every record (`LocTy.addImms`). Frame `j`'s output moves what the
  inner frames returned to the world without its record (`LocTy.extR_of_addImm`), and its claim
  joins theirs, the cells owned again (`claimL`);
* `sliceBorrowI_compatN` and `sliceBorrowIU_compatN` are Core's `sliceBorrowI_compatX` and
  `sliceBorrowIU_compatX` against it, with `withbor1_sem`'s and `withbor1U_sem`'s steps around
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
open BoCa.BoLo (Heap Kont Head)

/-- **An `imm` leaf at `α`** at the world `Θ`: `Imm`'s clause read at `α` (Core's `immLeaf`), one
`imm` cell longer-lived than `α` with its payload in the observable view, witnessed in the world's
records. -/
def immLeafN (A : VTy) (δ : LSub) (α : Life) (Θ : LocTy) (n : Nat) (m : Loc) : WProp := fun ρ =>
  immCell α (fun u σ => vO (ℍ := ℍ) A δ Θ n u σ) (Val.loc m) ρ ∧
    ∀ l s u σ h, ρ = ResU.single l (CellU.immOf s u σ h) → ImmWitW Θ.imm l s A δ

/-- An `imm` leaf at `α` is a value of `Imm 'x A` at `δ['x ↦ α]` (Core's `immLeaf_to_vP`). -/
theorem vN_immLeaf {x : LifeVar} {A : VTy} (hx : ¬ VFree x A) {δ : LSub} {α : Life} {Θ : LocTy}
    {n : Nat} {m : Loc} {ρ : WRes} (h : immLeafN (ℍ := ℍ) A δ α Θ n m ρ) :
    vN (ℍ := ℍ) (.imm (.var x) A) (δ.extend x α) Θ n (Val.loc m) ρ := by
  have hag : ∀ y, VFree y A → δ.find? y = (δ.extend x α).find? y := fun y hy =>
    (BoCa.Fig16.LogRel.find?_extend_ne δ α (fun e => by subst e; exact hx hy)).symm
  refine ⟨α, interp_ext_self δ x α, ?_, fun l s u σ hs e => ?_⟩
  · rw [vO_extend_of_not_free hx]; exact h.1
  · exact (immWitW_congr hag Θ.imm l s) ▸ h.2 l s u σ hs e

/-- **One Imm Frame per place, around one expression, across raises** (Core's
`wpG_I_frameList`, the frames of `sliceBorrowI_compatX` and `sliceBorrowIU_compatX`): the list
induction over `erwp_I_frameRR`, at an abortive table `Tb`.

Frame `j` lends its leaf `imm` at `αⱼ`, below the frame's rest, the payloads' stratum `β`, the
result's `β′` and the bound `γ` (Core's `aF ⊓ β′ ⊓ β`), its record `(pⱼ, αⱼ)` in the world of the
frames inside it; their run is read at the lender's view (`erwp_tieEntryR`). The inner frames'
bound is `@R ⊓ αⱼ ⊓ γ` as printed. The callback runs at the world holding every record, each lent
below the bound and on the callback's list, and receives every leaf at the innermost lifetime.
`Ψ` is the callback's postcondition: in the stratum `β′`, read at the world without a record at
a resource in the record's stratum, and not reading the list. The claim a `raise` carries is the
cells owned again (`claimL`, at the frames' index). -/
theorem erwp_I_frameListRN {A : VTy} {δ : LSub} {β β' : Life} (hadm : AdmWf A δ)
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    (Tb : OpTabN) (hab : ∀ m i en, Tb m i = some en → en.abort = true)
    (hTok : ∀ α, Tb.ILendOKR α)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (r : FrameRec) (α : Life) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.addImm (r, α)) k ls v ρ → Ψ Θ k ls v ρ)
    (hΨls : ∀ Θ k ls₁ ls₂ v ρ, Ψ Θ k ls₁ v ρ → Ψ Θ k ls₂ v ρ) (e : Expr) (c : Loc → Option Life) :
    ∀ (I : List Loc) (Θ : LocTy) (n : Nat) (ls : List SRec) (ρo ρH ρ : WRes) (γ : Life),
      ConsistentX c ρH → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (xs ls' : List SRec), (∀ x ∈ xs, x.2 < γ ∧ x ∈ ls') →
        (∀ y ∈ ls, y ∈ ls') → ∀ ρm ρ',
          sepList (immLeafN (ℍ := ℍ) A δ α (Θ.addImms xs) n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c ρ' →
          erwp (ℍ := ℍ) ((Θ.addImms xs).view c) (opTableR Tb (fun _ => claimL (ℍ := ℍ) A δ Θ [] n))
            (Ψ (Θ.addImms xs)) n ls' e ρ') →
      erwp (ℍ := ℍ) (Θ.view c) (opTableR Tb (fun _ => claimL (ℍ := ℍ) A δ Θ I n))
        (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n ls e ρ
  | [], Θ, n, ls, ρo, ρH, ρ, γ, hcH, hcρ, ho, hH => by
      obtain ⟨rfl, -⟩ := ho
      rw [eq_of_compS_empty_left hcρ]
      have h := (hH (↓γ) (Life.down_sqsubset γ)).2 [] ls (fun _ h => absurd h List.not_mem_nil)
        (fun _ h => h) PMap.empty ρH ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH) hcH
      exact erwp_mono (fun k ls' v σ h' =>
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h'⟩) (opTableR_local _ _) n ls e ρH h
  | ℓ :: I, Θ, n, ls, ρo, ρH, ρ, γ, hcH, hcρ, ho, hH => by
      obtain ⟨ρ0, ρr, hc0, hleaf, hrest⟩ := ho
      obtain ⟨l, u, σ, hl, hcl, hu⟩ := hleaf
      obtain rfl : ℓ = l := loc_inj hl
      -- `ρ = ρ0 ● Fr`, `Fr = ρr ● ρH`
      obtain ⟨Fr, hFr, hρ⟩ := compS_reassoc hc0 hcρ
      refine erwp_of_valid fun hv => ?_
      have hvρ0 : ResU.Valid ρ0 := (ResU.Valid.split hρ hv).1
      have hvσ : ResU.Valid σ := (ResU.Valid.split hcl hvρ0).2
      -- the outer frame's lifetime: below the frame's rest, `β`, `β′` and the bound
      obtain ⟨βF, hβF⟩ := ResU.exists_stratum Fr
      set α₁ : Life := ↓(βF ⊓ β ⊓ β' ⊓ γ) with hα₁def
      have hα₁lt : α₁ < βF ⊓ β ⊓ β' ⊓ γ := Life.down_sqsubset _
      have hα₁F : α₁ ≤ βF := hα₁lt.le.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
      have hα₁β : α₁ ≤ β := hα₁lt.le.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
      have hα₁β' : α₁ ≤ β' := hα₁lt.le.trans (inf_le_left.trans inf_le_right)
      have hα₁γ : α₁ < γ := lt_of_lt_of_le hα₁lt inf_le_right
      have houtP : σ.InStratum α₁ := (hunif Θ n u σ hu).mono hα₁β
      have houtb : Fr.InStratum α₁ := hβF.mono hα₁F
      -- the record and its lineage
      set p : FrameRec := ⟨ℓ, u, σ, A, δ⟩ with hpdef
      obtain ⟨-, eR, -, heR, -, -⟩ := hvσ
      obtain ⟨ds, hds⟩ := lineage_list (r := p) (vN_vShape A δ Θ n u σ hu) hadm heR
      set Θ₁ := Θ.addImm (p, α₁) with hΘ₁
      set ls₁ := frameList p ds α₁ ls with hls₁
      set ρi : WRes := ResU.single ℓ (CellU.immOf (LSet.singleton α₁) u σ houtP) with hρi
      have hci : ConsistentX c ρi := consistentX_allImm (fun m ψ e => by
        obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
        exact CellU.kind_immOf _ _ _ _) c
      have hRs : ∀ k ρ', (fun _ : Nat => claimL (ℍ := ℍ) A δ Θ₁ I n) k ρ' → ρ'.InStratum α₁ :=
        fun k ρ' h =>
          sepList_closed (ResU.inStratum_empty α₁) (fun _ _ _ hc a b => inStratum_compS hc a b)
            (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) h
      -- the cells of `I` at the world without the record
      have hdrop : ∀ k ρ', ρ'.InStratum α₁ →
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ₁ k (Val.loc m)) I ρ' →
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ' := fun k ρ' hs h =>
        sepList_mono_down (R := fun τ => τ.InStratum α₁)
          (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
            ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
          (fun m τ hτ hm => vN_extR (.ref A) δ k _ τ (LocTy.extR_of_addImm Θ p hτ) hm) hs h
      have hcl' : ∀ k ρ', (claimI ℓ u σ k ⋆ (fun _ : Nat => claimL (ℍ := ℍ) A δ Θ₁ I n) k) ρ' →
          claimL (ℍ := ℍ) A δ Θ (ℓ :: I) n ρ' := by
        rintro k ρ' ⟨ρ₁, ρ₂, hc12, hcw, hr⟩
        exact ⟨ρ₁, ρ₂, hc12, ⟨ℓ, u, σ, rfl, hcw, hu⟩, hdrop n ρ₂ (hRs k ρ₂ hr) hr⟩
      set Q : PostN := fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
        sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) (ℓ :: I) ρ₁ ∧
          Ψ Θ k ls' v ρ₂ with hQ
      have hIF := erwp_I_frameRR (Φ := Θ.view c) ℓ A δ hadm u
        (fun _ v ρ => vN (ℍ := ℍ) A δ Θ n v ρ) (fun _ ρ h => vN_vShape A δ Θ n u ρ h)
        (fun _ _ _ _ h => h) (hTok α₁) hRs (Q := Q)
        (fun k _ _ w ρ _ ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ => ⟨ρ₁, ρ₂, hc12, ho1, hΨls _ _ _ _ _ _ hψ⟩)
        n ls e σ ρ0 Fr ρ houtP houtb hu hcl hρ ds hds (fun BI hBI => ?_)
      · exact erwp_opTableR_le (OpTabN.Sub.le fun _ _ _ h => h) hcl' n ls e ρ hIF
      -- `BI = ρr ● R`, `R = ρH ● ρi`
      obtain ⟨R, hR, hBIR⟩ := compS_reassoc hFr hBI
      have hcR : ConsistentX c R := consistentX_compS hR hcH hci
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ₁ n (Val.loc m)) I ρr :=
        sepList_mono_down (R := fun τ => τ.InStratum α₁)
          (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
            ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
          (fun m τ hτ hm => vN_extR (.ref A) δ n _ τ (LocTy.extR_addImm Θ p hτ) hm)
          (ResU.CompS.inStratum_left hFr houtb) hrest
      -- the inner frames' run, read at the lender's view
      refine erwp_tieEntryR (Φ := Θ.view c) (Φ' := Θ₁.view c) rfl hab (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact .inr (List.mem_cons_self ..)
        · exact .inl hy) ?_
      refine erwp_mono_le n (fun k hk ls' v ρ' h => ?_)
        (fun j _ ls' t Ψ' Ψ'' ρ hΨ h => opTableR_local _ _ j ls' t Ψ' Ψ'' ρ hΨ h) n le_rfl _ _ BI
        (erwp_I_frameListRN hadm hunif Tb hab hTok Ψ hΨs hΨl hΨls e c I Θ₁ n ls₁ ρr R BI
          (βR ⊓ α₁ ⊓ γ) hcR hBIR hrest₁ (fun α₂ hα₂ => ⟨hβR.mono (le_of_lt (lt_of_lt_of_le hα₂
            (inf_le_left.trans inf_le_left))), ?_⟩))
      · -- the outer frame's postcondition from the inner ones'
        obtain ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ := h
        have hs1 : ρ₁.InStratum α₁ := sepList_closed (ResU.inStratum_empty α₁)
          (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨fun Y X hY hX σ' Z hσ' hZ => ?_, inStratum_compS hc12 hs1 hs2⟩
        subst hY
        obtain ⟨Wc, hWc, hZ'⟩ :=
          (ResU.CompS.assoc ρ' (ResU.single ℓ (CellU.ownOf u)) σ' Z).mpr ⟨X, hX, hZ⟩
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨Wc, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, u, σ', rfl, hWc, vN_le hk hσ'⟩,
          hdrop k ρ₁ hs1 ho1⟩, hΨl Θ p α₁ k ls' v ρ₂ hs2 hψ⟩
      · -- the inner frames' callback: the outer leaf, at `α₂ ⊑ α₁`, heads the family
        intro xs ls' hxs hls' ρm₂ ρ' hm₂ hcomp hc'
        have hα₂γ : α₂ < γ := lt_of_lt_of_le hα₂ inf_le_right
        have hα₂α₁ : α₂ < α₁ := lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_right)
        have hγ₁α₁ : βR ⊓ α₁ ⊓ γ ≤ α₁ := inf_le_left.trans inf_le_right
        have hγ₁γ : βR ⊓ α₁ ⊓ γ ≤ γ := inf_le_right
        obtain ⟨X, hX, hρ'X⟩ := compS_reassoc hR hcomp
        rw [LocTy.addImm_addImms] at hm₂ ⊢
        have hlead : immLeafN (ℍ := ℍ) A δ α₂ (Θ.addImms (xs ++ [(p, α₁)])) n ℓ ρi := by
          refine ⟨⟨ℓ, LSet.singleton α₁, u, σ, houtP, rfl, rfl, hα₂α₁.le, ?_⟩,
            fun l₀ s₀ u₀ σ₀ h₀ e => ?_⟩
          · refine vO_extR A δ n u σ (LocTy.extR_addImms Θ _ fun x hx => ?_)
              (vN_vO A δ Θ n u σ hu)
            rcases List.mem_append.mp hx with hx | hx
            · exact houtP.mono ((hxs x hx).1.le.trans hγ₁α₁)
            · rw [List.mem_singleton.mp hx]; exact houtP
          · obtain ⟨rfl, e'⟩ := single_immOf_inj e
            obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
            exact ⟨(p, α₁), List.mem_append_left _ (List.mem_append_right _
              (List.mem_singleton_self _)), le_refl _, p, DescR.refl _, A, δ, TyEq.refl _ _,
              Or.inl ⟨p, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩
        refine (hH α₂ hα₂γ).2 (xs ++ [(p, α₁)]) ls' (fun x hx => ?_)
          (fun y hy => hls' y ((addAt_frameList p ds α₁ ls).1 y hy)) X ρ'
          ⟨_, ρm₂, hX, hlead, hm₂⟩ hρ'X hc'
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨lt_of_lt_of_le (hxs x hx).1 hγ₁γ, (hxs x hx).2⟩
        · rw [List.mem_singleton.mp hx]
          exact ⟨hα₁γ, hls' _ (List.mem_cons_self ..)⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
