import Core.Chain.SI.IStopCancelN
import Core.Chain.SI.StopRaiseN

/-!
# An ordinary `raise` under a live `imm` lend

**Not a transcription.** `SI/StopRaiseN.lean`'s design at the Imm Frame: at a `raise` the borrow
is garbage (an `imm` cell owns nothing), and the lender's `raise` carries the lend's claim
`ρ_ℓ ● ρ_P̂(v)` (`claimI`) beside what owns nothing, at `opTableR T (claimI ℓ v ρ_P̂(v))`; a
finaliser frame consumes it at `[finalise]` (`erwp_ubindRaise`). The fold at the `raise` is
`iFold`'s (6.116), with the continuation's share empty.
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

/-- **A table whose stops may be taken under a live `imm` lend at `A`, raises included.**
`OpTabN.ILendOK` with abortive entries admitted. -/
structure OpTabN.ILendOKR (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false → en.q = .lin ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum A
  paExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ v (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PA k ls₁ v ρ → en.PA k ls₂ v ρ
  pbExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ w (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PB k ls₁ w ρ → en.PB k ls₂ w ρ

/-- **Imm Frame at `erwp` across stops, raises included.** As `erwp_I_frame`; at a `raise` the
lender's resource is the claim beside what owns nothing. -/
theorem erwp_I_frameR {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    (P : List SRec → Val → WProp) (hPshape : ∀ ls ρ, P ls v ρ → vShape T δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {Tb : OpTabN} (hT : Tb.ILendOKR A) {Q : PostN}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ n ls e (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A), ρb.InStratum A →
      P ls v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      ∀ ds, (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (IFPost l v P A Q) n (frameList ⟨l, v, ρP, T, δ⟩ ds A ls)
          e BI) →
      erwp (ℍ := ℍ) Φ (opTableR Tb (claimI l v ρP)) Q n ls e ρ := by
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
  · -- a `raise`: the borrow garbage, the cell and payload the claim the `raise` carries
    obtain ⟨⟨rfl, hK, hTe, ha⟩, τa, τn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨X, Xi, ρkL, hρal, haY, hkL, -, hX, hXi, -, -⟩ :=
      iFold hρa hcan h9 hnoρp hGc hπdA hY
    have hnoXi : NoOwn Xi :=
      noOwn_compS hXi (noOwn_compS hX hnn hnoρp) (noOwn_single_imm l _ _ _ _)
    have hPA' : en.PA k ls v₀ τa := hT.paExt m i en hTe k ls'' ls v₀ τa
      (hext τa ρkL haY hρa (fun ψ h => by rw [hρal] at h; cases h)) hPA
    obtain ⟨D, hD, hDY⟩ := (ResU.CompS.assoc τa (Xi.del l) ρlP Y).mp ⟨ρkL, hkL, haY⟩
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨D, ρlP, hDY,
        ⟨τa, Xi.del l, hD, ⟨hPA', hnA⟩, noOwn_del hnoXi l⟩, hclP⟩⟩)⟩
end BoCa.Fig16.LogRel.Core.Chain.SI

end
