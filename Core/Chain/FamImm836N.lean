import Core.Chain.FamNew836N
import Core.Chain.FamCancel836N

/-!
# The `n`-cell Imm Frame and `slice_borrow` at `SemJN₀`  `[spec §9, §19, §23]`

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
  joins theirs, the cells owned again (`claimL₀`);
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
open BoCa.BoLo (Heap Kont Head ubindE)

/-- **An `imm` leaf at `α`** at the world `Θ`: `Imm`'s clause read at `α` (Core's `immLeaf`), one
`imm` cell longer-lived than `α` with its payload in the observable view, witnessed in the world's
records. -/
def immLeafN (A : VTy) (δ : LSub) (α : Life) (Θ : LocTy) (n : Nat) (m : Loc) : WProp := fun ρ =>
  immCell α (fun u σ => vO₀ (ℍ := ℍ) A δ Θ n u σ) (Val.loc m) ρ ∧
    ∀ l s u σ h, ρ = ResU.single l (CellU.immOf s u σ h) → ImmWitW Θ.imm l s A δ

/-- An `imm` leaf at `α` is a value of `Imm 'x A` at `δ['x ↦ α]` (Core's `immLeaf_to_vP`). -/
theorem vN_immLeaf {x : LifeVar} {A : VTy} (hx : ¬ VFree x A) {δ : LSub} {α : Life} {Θ : LocTy}
    {n : Nat} {m : Loc} {ρ : WRes} (h : immLeafN (ℍ := ℍ) A δ α Θ n m ρ) :
    vN₀ (ℍ := ℍ) (.imm (.var x) A) (δ.extend x α) Θ n (Val.loc m) ρ := by
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
cells owned again (`claimL₀`, at the frames' index). -/
theorem erwp_I_frameListRN {A : VTy} {δ : LSub} {β β' : Life} (hadm : AdmWf A δ)
    (hunif : ∀ Θ j u r, vN₀ (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    (Tb : OpTabN) (hab : ∀ m i en, Tb m i = some en → en.abort = true)
    (hTok : ∀ α, Tb.ILendOKR α)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (r : FrameRec) (α : Life) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.addImm (r, α)) k ls v ρ → Ψ Θ k ls v ρ)
    (hΨls : ∀ Θ k ls₁ ls₂ v ρ, Ψ Θ k ls₁ v ρ → Ψ Θ k ls₂ v ρ) (e : Expr) (c : Loc → Option Life) :
    ∀ (I : List Loc) (Θ : LocTy) (n : Nat) (ls : List SRec) (ρo ρH ρ : WRes) (γ : Life),
      ConsistentX c ρH → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (xs ls' : List SRec), (∀ x ∈ xs, x.2 < γ ∧ x ∈ ls') →
        (∀ y ∈ ls, y ∈ ls') → ∀ ρm ρ',
          sepList (immLeafN (ℍ := ℍ) A δ α (Θ.addImms xs) n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c ρ' →
          erwp (ℍ := ℍ) ((Θ.addImms xs).view c) (opTableR Tb (fun _ => claimL₀ (ℍ := ℍ) A δ Θ [] n))
            (Ψ (Θ.addImms xs)) n ls' e ρ') →
      erwp (ℍ := ℍ) (Θ.view c) (opTableR Tb (fun _ => claimL₀ (ℍ := ℍ) A δ Θ I n))
        (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
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
      have hRs : ∀ k ρ', (fun _ : Nat => claimL₀ (ℍ := ℍ) A δ Θ₁ I n) k ρ' → ρ'.InStratum α₁ :=
        fun k ρ' h =>
          sepList_closed (ResU.inStratum_empty α₁) (fun _ _ _ hc a b => inStratum_compS hc a b)
            (fun m τ hm => ownLeafN_inStratum₀ hα₁β hunif hm) h
      -- the cells of `I` at the world without the record
      have hdrop : ∀ k ρ', ρ'.InStratum α₁ →
          sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ₁ k (Val.loc m)) I ρ' →
          sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ' := fun k ρ' hs h =>
        sepList_mono_down (R := fun τ => τ.InStratum α₁)
          (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
            ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
          (fun m τ hτ hm => vN_extR₀ (.ref A) δ k _ τ (LocTy.extR_of_addImm Θ p hτ) hm) hs h
      have hcl' : ∀ k ρ', (claimI ℓ u σ k ⋆ (fun _ : Nat => claimL₀ (ℍ := ℍ) A δ Θ₁ I n) k) ρ' →
          claimL₀ (ℍ := ℍ) A δ Θ (ℓ :: I) n ρ' := by
        rintro k ρ' ⟨ρ₁, ρ₂, hc12, hcw, hr⟩
        exact ⟨ρ₁, ρ₂, hc12, ⟨ℓ, u, σ, rfl, hcw, hu⟩, hdrop n ρ₂ (hRs k ρ₂ hr) hr⟩
      set Q : PostN := fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
        sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) (ℓ :: I) ρ₁ ∧
          Ψ Θ k ls' v ρ₂ with hQ
      have hIF := erwp_I_frameRR (Φ := Θ.view c) ℓ A δ hadm u
        (fun _ v ρ => vN₀ (ℍ := ℍ) A δ Θ n v ρ) (fun _ ρ h => vN_vShape A δ Θ n u ρ h)
        (fun _ _ _ _ h => h) (hTok α₁) hRs (Q := Q)
        (fun k _ _ w ρ _ ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ => ⟨ρ₁, ρ₂, hc12, ho1, hΨls _ _ _ _ _ _ hψ⟩)
        n ls e σ ρ0 Fr ρ houtP houtb hu hcl hρ ds hds (fun BI hBI => ?_)
      · exact erwp_opTableR_le (OpTabN.Sub.le fun _ _ _ h => h) hcl' n ls e ρ hIF
      -- `BI = ρr ● R`, `R = ρH ● ρi`
      obtain ⟨R, hR, hBIR⟩ := compS_reassoc hFr hBI
      have hcR : ConsistentX c R := consistentX_compS hR hcH hci
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ₁ n (Val.loc m)) I ρr :=
        sepList_mono_down (R := fun τ => τ.InStratum α₁)
          (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
            ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
          (fun m τ hτ hm => vN_extR₀ (.ref A) δ n _ τ (LocTy.extR_addImm Θ p hτ) hm)
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
          (fun m τ hm => ownLeafN_inStratum₀ hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨fun Y X hY hX σ' Z hσ' hZ => ?_, inStratum_compS hc12 hs1 hs2⟩
        subst hY
        obtain ⟨Wc, hWc, hZ'⟩ :=
          (ResU.CompS.assoc ρ' (ResU.single ℓ (CellU.ownOf u)) σ' Z).mpr ⟨X, hX, hZ⟩
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨Wc, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, u, σ', rfl, hWc, vN_le₀ hk hσ'⟩,
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
          · refine vO_extR₀ A δ n u σ (LocTy.extR_addImms Θ _ fun x hx => ?_)
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

/-! ### `slice_borrow` at the pure row -/

/-- **`slice_borrow` is a value of its type** (Core's `sliceBorrowI_compatX`):
`withbor` at `Array A ⊸ (∀'x ⊏ @Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`. `sliceBorrowM_sem₀`'s
steps with the `n` Imm Frames around the callback (`erwp_I_frameListRN` at the family's range,
the pure row's table): the payloads' and the result's strata from the side conditions by 6.60 at
`↓@bδ` (`vN_outlivesLe₀`), the frames' lifetimes below the bound and the callback's stratum; the
callback at the world holding the records (`LocTy.extR_addImms` at its resource), the family
`[Imm 'x A]` at the innermost lifetime (`vN_immLeaf`), `withbor1_sem`'s steps inside. -/
theorem sliceBorrowI_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {δ : LSub} (hδ : Δ.Models δ)
    (hadm : AdmWf A δ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (Θ₀ : LocTy) (n : Nat) :
    vN₀ (ℍ := ℍ) (sliceBorrowITy x Δ.meetOfDom A B) δ Θ₀ n withborVal PMap.empty := by
  intro Θ₂ _ hΘ₂ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, cn, rfl, hn, hs⟩ := hu
  have hΦ₂ : (Θ₂.view c₂).Down := LocTy.view_down hΘ₂.1 c₂
  refine erwp_det hΦ₂ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l cn)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.arr l cn)
      (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))).1) =
      (withborAtV (Val.arr l cn)).1 := by
    simp [Kont.plug, Expr.subst, withborAtV, BoCa.v0, BoCa.v1, unit', Val.lam,
      Expr.val, Val.unit, shift_arr]
  rw [e₁]
  refine erwp_val (v := withborAtV (Val.arr l cn)) ?_
  intro Θ' hE₃ hΘ' c _ ls' c' k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l₁, cn₁, he, hn', hs'⟩ := vN_le₀ hk'
    (vN_extR₀ (.array A) δ k _ ρu hE₃ ⟨l, cn, rfl, hn, hs⟩)
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  have hΦ : (Θ'.view c').Down := LocTy.view_down hΘ'.1 c'
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f
      (.pair (.val (Val.arr l cn)) (.app (.app BoCa.v0 unit') (.val (Val.arr l cn))))) =
      (Kont.pairR (Val.arr l cn) (Kont.appL Kont.hole (Val.arr l cn))).plug
        (.app (.val f) (.val Val.unit)) := by
    simp [Kont.plug, Expr.subst, BoCa.v0, unit', Expr.val, Val.unit, subst_arr]
  rw [e₂]
  refine erwp_of_valid fun hv'' => ?_
  have hcf : ConsistentX c' ρf := consistentX_right hc' hcon hv''
  -- the side conditions: the payloads' and the result's strata (6.60 at `↓@bδ`)
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
  -- the frames' postcondition: the handle beside a result of `B`
  let Ψ : LocTy → PostN := fun Θ k _ v ρ => ∃ w, v = Val.pair (Val.arr l cn) w ∧
    vN₀ (ℍ := ℍ) B δ Θ k w ρ
  have hI := erwp_I_frameListRN hadm hunif OpTabN.empty
    (fun _ _ _ h => by simp [OpTabN.empty] at h) empty_iLendOKR Ψ
    (fun Θ k _ v ρ ⟨w, _, hw⟩ => hBs Θ k w ρ hw)
    (fun Θ r α k _ v ρ hρ ⟨w, hvw, hw⟩ =>
      ⟨w, hvw, vN_extR₀ B δ k w ρ (LocTy.extR_of_addImm Θ r hρ) hw⟩)
    (fun _ _ _ _ _ _ h => h)
    ((Kont.pairR (Val.arr l cn) (Kont.appL Kont.hole (Val.arr l cn))).plug
      (.app (.val f) (.val Val.unit))) c' (rangeLocs l cn.toNat) Θ' k' ls' ρu ρf ρ'' (m ⊓ βf) hcf hc'
    (by rw [← sepRange_eq_sepList]; exact hs')
    (fun α hα => ⟨hβf.mono (le_of_lt (lt_of_lt_of_le hα inf_le_right)), ?_⟩)
  · refine erwp_mono (fun k ls₁ v ρ' h => ?_) (fun j ls₁ t Ψ₁ Ψ₂ ρ _ h => ?_) k' ls' _ ρ'' hI
    · -- the returned leaves are the array again, beside the callback's result
      obtain ⟨ρ₁, ρ₂, hc12, ho, w, rfl, hw⟩ := h
      exact ⟨Val.arr l cn, w, ρ₁, ρ₂, rfl, hc12,
        ⟨l, cn, rfl, hn', by rw [sepRange_eq_sepList]; exact ho⟩, hw⟩
    · -- the pure row stops nowhere
      rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
      · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
      · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
  -- the callback, at the world holding the records, from the leaves at `α`
  intro xs ls₂ hxs _ ρm ρ₃ hml hcomp hc''
  set W := Θ'.addImms xs with hW
  have hOKW : W.OK := LocTy.addImms_ok hΘ' xs
  have hEW : Θ'.ExtR W ρf := LocTy.extR_addImms Θ' xs fun x hx =>
    hβf.mono (le_of_lt (lt_of_lt_of_le (hxs x hx).1 inf_le_right))
  refine erwp_of_valid fun hv₃ => erwp_of_rwp ?_
  have hLt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_left⟩
  have hΦi : (W.view c').Down := LocTy.view_down hOKW.1 c'
  have hcm : ConsistentX c' ρm := consistentX_right hcomp hc'' hv₃
  have hfam : vN₀ (ℍ := ℍ) (.arrayImm (.var x) A) (δ.extend x α) W k' (Val.arr l cn) ρm :=
    ⟨l, cn, rfl, hn', by
      rw [sepRange_eq_sepList]; exact sepList_mono' (fun _ _ h => vN_immLeaf hA h) hml⟩
  refine rwp_bind hΦi _ ?_
  have hcb := (hf W hEW hOKW c' hcf ls₂) α hLt
  have hfr' := rwp_frame (fun _ τ => τ = ρm) (fun _ _ _ _ h => h) hcomp (rwp_of_erwp_empty hcb) rfl
  refine rwp_mono_le (fun j hj ls₃ g τ hg => ?_) (rwp_consistentXV hfr' hc'')
  obtain ⟨⟨τg, τm, hcτ, hgv, rfl⟩, hcτ', hvτ⟩ := hg
  have happ := hgv W (LocTy.extR_refl _ _) hOKW c' (consistentX_left hcτ hcτ' hvτ) ls₃
    c' j le_rfl (Val.arr l cn) _ τ hcτ (vN_le₀ hj hfam) hcτ'
  show rwp (ℍ := ℍ) _ _ j ls₃ ((Kont.pairR (Val.arr l cn) Kont.hole).plug
    (.app (.val g) (.val (Val.arr l cn)))) τ
  refine rwp_bind hΦi _ ?_
  refine rwp_mono_le (fun j' hj' ls₄ w ρw hw => ?_) (rwp_of_erwp_empty happ)
  refine rwp_val (v := Val.pair (Val.arr l cn) w) ?_
  obtain ⟨β, hβ, hwB, -⟩ := hw
  exact ⟨w, rfl, by rw [← hBδ α]; exact hwB⟩

/-- **`slice_borrow` at `SemJN₀`** (Core's `sliceBorrowI_compatX`). -/
theorem sliceBorrowI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) :
    SemJN₀ (ℍ := ℍ) Δ Γ withbor (.val (sliceBorrowITy x Δ.meetOfDom A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withbor) _
  rw [show substAll γ withbor = withbor from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  exact erwp_val (v := withborVal)
    (sliceBorrowI_sem hδ (admWf_of_vScoped hsc hδ) hsideA hsideB hfree₁ hfree₂ Θ n)

/-! ### `slice_borrow` at an unwinding row -/

/-- **An unwinding row's table does not read an `imm` record of the world**: its payloads lie in
every stratum, the record's among them. -/
theorem tabN_unwind_addImm {S : Row} {x : LifeVar} (hS : S.Unwind x) (R : VTy) (δ : LSub)
    (Θ : LocTy) (y : SRec) (c : Loc → Option Life) :
    tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ (Θ.addImm y) c = tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c := by
  induction S with
  | nil => rfl
  | cons o S ih =>
      have ho : o ∈ o :: S := List.mem_cons_self ..
      have hS' : Row.Unwind S x := fun o' ho' => hS o' (List.mem_cons_of_mem _ ho')
      have hA : vN₀ (ℍ := ℍ) o.A δ (Θ.addImm y) = vN₀ (ℍ := ℍ) o.A δ Θ := by
        funext n v ρ
        have hρ := vN_unwind_inStratum hS ho δ y.2
        exact propext ⟨fun h => vN_extR₀ _ δ n v ρ
          (LocTy.extR_of_addImm Θ y.1 (hρ _ n v ρ h)) h,
          fun h => vN_extR₀ _ δ n v ρ (LocTy.extR_addImm Θ y.1 (hρ _ n v ρ h)) h⟩
      have hB := unwind_B hS ho
      simp only [CTy.effOf, tabN₀]
      rw [ih hS', hA, hB,
        entN_fin_congr (f := finN₀ (ℍ := ℍ) o.fin δ (Θ.addImm y) c)
          (f' := finN₀ (ℍ := ℍ) o.fin δ Θ c) (fun hcap => by simp [capB, VTy.isZero] at hcap)]
      rfl

/-- `tabN_unwind_addImm` at every list of records. -/
theorem tabN_unwind_addImms {S : Row} {x : LifeVar} (hS : S.Unwind x) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) :
    ∀ xs : List SRec,
      tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ (Θ.addImms xs) c = tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c
  | [] => rfl
  | y :: xs => by
      rw [LocTy.addImms_cons, tabN_unwind_addImm hS R δ _ y c, tabN_unwind_addImms hS R δ Θ c xs]

/-- **`slice_borrow` at an unwinding row is a value of its type** (Core's
`sliceBorrowIU_compatX`): `withborU d` at
`Array A ⊸ (∀'x ⊏ @Δ. [Imm 'x A] ⊸ F_Σ(['x] B)) ⊸ F_Σ(Array A ⊗ B)`, `Σ` a `Row.Unwind x` row.
`sliceBorrowMU_sem`'s steps with the `n` Imm Frames across the row's raises
(`erwp_I_frameListRN`, Core's `wpG_I_frameFam`) at the lender's table, which reads no record
(`tabN_unwind_addImms`); the payloads' and the result's strata from the side conditions by 6.60
at `↓@bδ`; the callback at the world holding the records receives the family `[Imm 'x A]` at the
innermost lifetime; the composite claim, the array owned again, consistent with the view
(`erwp_claimX_abort`), is consumed by the finaliser at a raise (`erwp_ubindRaise`,
`fin_claimArrI`). -/
theorem sliceBorrowIU_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {S : Row} {d : Expr}
    {δ : LSub} (hδ : Δ.Models δ) (hadm : AdmWf A δ)
    (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Unwind x) (hdc : closedAt 0 d = true) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN₀ (ℍ := ℍ) (.ret (.lolli (.array A) .unit)) δ Θ c k ls d PMap.empty) :
    vN₀ (ℍ := ℍ) (sliceBorrowIUTy x Δ.meetOfDom A B S) δ Θ₀ n (withborUV d) PMap.empty := by
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
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
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
  have hab := tabN_unwind_abort (ℍ := ℍ) hS (.tensor (.array A) B) δ Θ c
  have hM := erwp_I_frameListRN hadm hunif T hab
    (fun α => tabN_unwind_iLendOKR hS _ δ Θ c α) Ψ
    (fun Θ k _ v ρ hw => hBs Θ k v ρ hw)
    (fun Θ r α k _ v ρ hρ hw => vN_extR₀ B δ k v ρ (LocTy.extR_of_addImm Θ r hρ) hw)
    (fun _ _ _ _ _ _ h => h) (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) c
    I Θ k' ls ρu ρf ρ'' (m ⊓ βf) hcf hc' (by rw [← sepRange_eq_sepList]; exact hs)
    (fun α hα => ⟨hβf.mono (le_of_lt (lt_of_lt_of_le hα inf_le_right)), ?_⟩)
  · have hM' := erwp_claimX_abort hab hcon hM
    have hM'' := erwp_mono_le
      (Tb' := opTableR T (fun j ρ => claimX (fun _ => claimL₀ (ℍ := ℍ) A δ Θ I k') c j ρ ∧
        j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [hab m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hM'
    refine erwp_ubindRaise hΦ hTd
      (fun m i en h ha => by rw [hab m i en h] at ha; cases ha)
      (tabN_unwind_named hS _ δ Θ c)
      (fun m i en h k ls ls' v ρ _ hp => by
        obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
        exact hp)
      (NFa (Val.arr l cn)) (DFa d (Val.arr l cn)) (fun j ls' ρ hR => ?_) hQo
      (fun j ls' b ρ hq => ?_) k' ls _ ρ'' hM''
    · obtain ⟨⟨hR, hcR⟩, hj⟩ := hR
      exact fin_claimArrI hdc hΘ (fun j' hj' ls => hd Θ hΘ c j' (hj'.trans (hk'.trans hk)) ls)
        (hj.trans le_rfl) (vN_le₀ hj ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact hR⟩) hcR
    · obtain ⟨ρ₁, ρ₂, hc12, ho, hb⟩ := hq
      refine erwp_det hΦ (opTableN_down hTd) hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwp_val (v := Val.pair (Val.arr l cn) b)
        ⟨Val.arr l cn, b, ρ₁, ρ₂, rfl, hc12,
          ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact ho⟩, hb⟩
  -- the callback, at the world holding the records, from the leaves at `α`
  intro xs ls₂ hxs _ ρm ρ₃ hml hcomp hc''
  set W := Θ.addImms xs with hW
  have hOKW : W.OK := LocTy.addImms_ok hΘ xs
  have hEW : Θ.ExtR W ρf := LocTy.extR_addImms Θ xs fun x hx =>
    hβf.mono (le_of_lt (lt_of_lt_of_le (hxs x hx).1 inf_le_right))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_left⟩
  have hfam : vN₀ (ℍ := ℍ) (.arrayImm (.var x) A) (δ.extend x α) W k' (Val.arr l cn) ρm :=
    ⟨l, cn, rfl, hn, by
      rw [sepRange_eq_sepList]; exact sepList_mono' (fun _ _ h => vN_immLeaf hA h) hml⟩
  have h1 := (hf W hEW hOKW c hcf ls₂) α hLt
  have h2 := h1 c k' le_rfl (Val.arr l cn) _ ρ₃ hcomp hfam hc''
  rw [cN_effOf₀, tabN_unwind_extend hS (.box (.var x) B) (.tensor (.array A) B) δ W α c,
    hW, tabN_unwind_addImms hS _ δ Θ c xs] at h2
  refine erwp_opTableN_R (OpTabN.Sub.le fun _ _ _ h => h)
    (R₀ := fun _ => claimL₀ (ℍ := ℍ) A δ Θ [] k') (fun _ => ⟨rfl, trivial⟩) k' ls₂ _ ρ₃
    (erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls₂ _ ρ₃ h2)
  obtain ⟨β, hβ, hbB, -⟩ := hb
  rw [interp_ext_self] at hβ
  cases Option.some.inj hβ
  show vN₀ (ℍ := ℍ) B δ (Θ.addImms xs) k b ρ'
  rw [← hBδ α]; exact hbB

/-- **`sliceBorrowIU` at `SemJN₀`** (Core's `sliceBorrowIU_compatX`), at an unwinding row and any
`Δ`. -/
theorem sliceBorrowIU_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
    (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) (hS : S.Unwind x) (hdc : closedAt 0 d = true)
    (hd : SemJN₀ (ℍ := ℍ) Δ Γ d (.val (.lolli (.array A) .unit))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (withborUE d) (.val (sliceBorrowIUTy x Δ.meetOfDom A B S)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (withborUE d)) _
  rw [show substAll γ (withborUE d) = withborUE d from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine erwp_val (v := withborUV d) (sliceBorrowIU_sem hδ (admWf_of_vScoped hsc hδ) hsideA hsideB
    hfree₁ hfree₂ hS hdc Θ n (fun Θ' hΘ' c' k hk ls' => ?_))
  have h := hd δ γ Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') hlw
    (gN_dead_any hΓ hg Θ' k hk)
  rwa [show substAll γ d = d from psub_closedAt d γ hdc (Nat.zero_le 0)] at h

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
