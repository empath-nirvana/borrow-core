import Core.Chain.SI.IStopN
import Core.Chain.SI.StopCancelN

/-!
# An `imm` lend live across a cancellable stop

**Not a transcription.** `SI/StopCancelN.lean`'s design at the Imm Frame. A cancel run inside an
`imm` lend ends at the cancel's `raise` owning nothing; the borrow is an `imm` cell, so it is
garbage there already. The lender's cancel run, from the folded share, ends holding
`ℓ ↦ own(v) ● ρ_P̂(v)` again; a cancel run that owns nothing cannot carry it, so the lender's run
ends at `cancelTabR T (claimI ℓ v ρ_P̂(v))`: the `raise` carrying the lend's claim, which a
finaliser frame around the lend consumes (`erwp_ubindClaim`, generic in the claim).

* `iFold`: the fold at a stop of `erwp_I_frame`, as a resource lemma: 6.116 makes `X ● ρᵢ`
  defined, and a re-entry from `(X ● ρᵢ)/ℓ ● σ_B` gives the continuation `ρ_k ● σ_B` and garbage.
* `erwp_I_frame_cancelRun`: the Imm Frame over a cancel run.
* `erwp_I_frameT`: `erwp_I_frame` at a table with cancellable entries, the lender's stops at a
  twin table whose cancel obligations it meets from the borrowed continuation's (`hcan`).
* `claimIT_can`, `erwp_I_frameC`: the twin `claimT … (claimI …)`, its obligations met by the
  cancel-run frame.

Soundness is `SI/StopCancelN.lean`'s: the lender's cancel run is the borrowed one with the
borrow folded at every stop, and the claim is the resource 6.64 returns to the lender at a
return (`ρ_ℓ ● ρ_P̂(v)`), returned at the cancel's `raise` instead.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont performE raiseE cancelVal opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The fold at a stop -/

/-- **The fold at a stop, and the re-entry, as resources.** `π = ρ_a ● ρ_k ● ρ⁺ = π/ℓ ● ρᵢ`,
`ρ_a` in `Res_A`: the lender's share `ρ_kL = (X ● ρᵢ)/ℓ ● ρ_ℓ ● ρ_P̂(v)` beside `ρ_a`, and a
re-entry from `(X ● ρᵢ)/ℓ ● σ_B` at `ρᵢ` holds `ρ_k ● σ_B` and garbage (6.116). -/
theorem iFold {l : Loc} {A : Life} {v : Val} {ρP ρlP ρa ρk ρp ρ' π Y : WRes}
    {houtP : ρP.InStratum A} (hρa : ρa.InStratum A) (hcak : ResU.CompS ρa ρk ρ')
    (h9 : ResU.CompS ρ' ρp π) (hnoρp : NoOwn ρp)
    (hGc : ResU.CompS (π.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) π)
    (hπdA : (π.del l).InStratum A) (hY : ResU.CompS (π.del l) ρlP Y) :
    ∃ (X Xi ρkL : WRes), ρa.get l = none ∧ ResU.CompS ρa ρkL Y ∧
      ResU.CompS (Xi.del l) ρlP ρkL ∧ (Xi.del l).InStratum A ∧ ResU.CompS ρk ρp X ∧
      ResU.CompS X (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi ∧
      ResU.CompS (Xi.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi ∧
      ∀ σB ρbB BI', ResU.CompS (Xi.del l) σB ρbB →
        ResU.CompS ρbB (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI' →
        ∃ Xk g, ResU.CompS ρk σB Xk ∧ ResU.CompS Xk g BI' ∧ NoOwn g := by
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  have hπl : π.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    ResU.compS_single_get_self (ResU.CompS.comm hGc) (ResU.del_get_self _ _)
  obtain ⟨X, hX, haX⟩ := (ResU.CompS.assoc ρa ρk ρp π).mpr ⟨ρ', hcak, h9⟩
  have hρal : ρa.get l = none := ResU.six38_no_borrow_in_frame hρa haX hπl
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
  refine ⟨X, Xi, ρkL, hρal, haY, hkL, hXdA, hX, hXi, hXid, fun σB ρbB BI' hρbB hBI' => ?_⟩
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
  obtain ⟨g, hg, hXkg⟩ := (ResU.CompS.assoc Xk ρp ρi BI').mpr ⟨Xσ, hXkp, hXσi⟩
  exact ⟨Xk, g, hXk, hXkg, noOwn_compS hg hnoρp (noOwn_single_imm l _ _ _ _)⟩

/-! ### The Imm Frame over a cancel run -/

/-- **The lend's claim** at an Imm Frame: the cell and its payload, owned again. -/
def claimI (l : Loc) (v : Val) (ρP : WRes) : Nat → WProp :=
  fun _ ρ => ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρ

/-- **The Imm Frame over a cancel run.** From `cancelTabN T` inside to
`cancelTabR T (claimI ℓ v ρ_P̂(v))` outside. At the cancel's `raise` the borrow is garbage and
`ρ_ℓ ● ρ_P̂(v)` is the claim; at a finaliser's (must-resume) stop, as in `erwp_I_frame`. -/
theorem erwp_I_frame_cancelRun {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ)
    (v : Val) {A : Life} {Tb : OpTabN} (hT : Tb.ILendOK A) :
    ∀ n ls e (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A), ρb.InStratum A →
      vShape T δ v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP →
      ResU.CompS ρlP ρb ρ → ∀ ds,
      (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (cancelTabN Tb) (fun _ _ _ _ => False) n
          (frameList ⟨l, v, ρP, T, δ⟩ ds A ls) e BI) →
      erwp (ℍ := ℍ) Φ (cancelTabR Tb (claimI l v ρP)) (fun _ _ _ _ => False) n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρP ρlP ρb ρ houtP houtb hshape hclP hcρ ds hds hA
  rw [erwp_eq]
  refine rwpG_I_frameG l T δ hadm v houtP houtb hclP hcρ hshape hds ?_
    (fun BI hBI => by
      have h := hA BI hBI
      rw [erwp_eq] at h
      exact h)
  intro k hk ls'' t ρ' ρp π Y hQin hnoρp h9 hls'' hGc hπdA hY hext hNX
  rcases hQin with ⟨w, -, hf⟩ | ⟨K, err, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · exact hf.elim
  · -- the cancel's `raise`: the borrow garbage, the cell and payload the claim
    obtain ⟨⟨rfl, hK⟩, τa, τb, hcab, herr, hnb⟩ := pure_sep_iff.mp hp
    cases err with
    | some E =>
        obtain ⟨m, j', w', en, he⟩ := herr
        obtain ⟨⟨-, hTe, ha⟩, -⟩ := pure_sep_iff.mp he
        exact absurd ha (by rw [(hT.entry _ _ en hTe).1]; simp)
    | none =>
    obtain rfl : τa = PMap.empty := herr.1
    obtain rfl := eq_of_compS_empty_left hcab
    have hnoπ : NoOwn π := noOwn_compS h9 hnb hnoρp
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, none, pure_sep_mk ⟨rfl, hK⟩ ⟨π.del l, ρlP, hY,
        ⟨PMap.empty, π.del l, compS_empty_left _, emp_empty, noOwn_del hnoπ l⟩, hclP⟩⟩)⟩
  · -- a finaliser's stop: as in `erwp_I_frame`
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨X, Xi, ρkL, hρal, haY, hkL, hXdA, hX, hXi, hXid, hre⟩ :=
      iFold hρa hcak h9 hnoρp hGc hπdA hY
    have hPA' : en.PA k ls v₀ ρa := hT.paExt m i en hTe k ls'' ls v₀ ρa
      (hext ρa ρkL haY hρa (fun ψ h => by rw [hρal] at h; cases h)) hPA
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, ρkL, haY, hPA',
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun lsO he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)⟩
    simp only [erwpC, show k' < n by omega, if_true]
    have he' : extF ls lsO ρkL := by rw [hwc] at he; exact he
    obtain ⟨ρbB, hρbB, hWXB⟩ :=
      (ResU.CompS.assoc ρlP (Xi.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
    have hσBA : σB.InStratum A := hT.pb m i en hTe _ _ _ _ hB
    refine ih k' (by omega) lsO _ ρP ρlP ρbB XB houtP (inStratum_compS hρbB hXdA hσBA) hshape
      hclP hWXB ds hds (fun BI' hBI' => ?_)
    have he'' : en.wc ls'' (frameList ⟨l, v, ρP, T, δ⟩ ds A lsO) ρk := by
      rw [hwc]
      exact extF_ifold hX hXi (ResU.compS_single_get_self (ResU.CompS.comm hXid) (ResU.del_get_self _ _)) hkL hclP hNX hls'' he'
    have hB' : en.PB k' (frameList ⟨l, v, ρP, T, δ⟩ ds A lsO) w σB :=
      hT.pbExt m i en hTe k' lsO _ w σB (ext_add (addAt_frameList _ ds A lsO) hσBA) hB
    obtain ⟨Xk, g, hXk, hXkg, hg⟩ := hre σB ρbB BI' hρbB hBI'
    have hc := (hcont _ he'').1 k' hk' w σB Xk hB' hXk
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact erwp_garbage hXkg hg hc

/-! ### The frame across a cancellable stop -/

/-- **A table whose stops may be taken under a live `imm` lend at `A`, cancellable entries
included.** `OpTabN.ILendOK` with `q ≠ unr` for `q = lin`. -/
structure OpTabN.ILendOKC (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q ≠ .unr ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum A
  paExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ v (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PA k ls₁ v ρ → en.PA k ls₂ v ρ
  pbExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ w (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PB k ls₁ w ρ → en.PB k ls₂ w ρ

/-- What the lender owes at a cancellable stop: from the borrowed continuation's cancel run at
the frame's list, its own at the caller's list, from the folded share. -/
def ICan (T T' : OpTabN) (l : Loc) (Ty : VTy) (δ : LSub) (A : Life) (v : Val) (ρP ρlP : WRes)
    (houtP : ρP.InStratum A) (ds : List FrameRec) : Prop :=
  ∀ m i en en', T m i = some en → T' m i = some en' → en.q ≠ .lin →
    ∀ k lsO (K : Kont) (ρk ρp X Xi ρkL : WRes),
      NoOwn ρp → ResU.CompS ρk ρp X →
      ResU.CompS X (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi →
      ResU.CompS (Xi.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi →
      (Xi.del l).InStratum A → ResU.CompS (Xi.del l) ρlP ρkL →
      cancelOKN en k (frameList ⟨l, v, ρP, Ty, δ⟩ ds A lsO) K ρk → cancelOKN en' k lsO K ρkL

/-- **Imm Frame at `erwp` across stops, cancellable ones included.** The lender's stops are at
the twin table `T′`, whose cancel obligations it meets from the borrowed continuation's, with
the borrow folded (`hcan`). -/
theorem erwp_I_frameT {Φ : LocFam} (l : Loc) (Ty : VTy) (δ : LSub) (hadm : AdmWf Ty δ) (v : Val)
    (P : List SRec → Val → WProp) (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {T T' : OpTabN} (hT : T.ILendOKC A) (hTT' : T.Twin T') {ρP ρlP : WRes}
    (houtP : ρP.InStratum A) (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d)
    (hcan : ICan T T' l Ty δ A v ρP ρlP houtP ds) {Q : PostN}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ n ls e (ρb ρ : WRes), ρb.InStratum A → P ls v ρP → ResU.CompS ρlP ρb ρ →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (opTableN T) (IFPost l v P A Q) n (frameList ⟨l, v, ρP, Ty, δ⟩ ds A ls)
          e BI) →
      erwp (ℍ := ℍ) Φ (opTableN T') Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρb ρ houtb hPv hcρ hA
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  have houtlP : ρlP.InStratum A := inStratum_ownP hclP houtP
  rw [erwp_eq]
  refine rwpG_I_frameG l Ty δ hadm v houtP houtb hclP hcρ (hPshape ls ρP hPv) hds ?_
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
  · -- a return: 6.64's end, as in `erwp_I_frame`
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
  · -- a stop: the borrow folded; the twin's entry
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc'⟩ := hTT' m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨X, Xi, ρkL, hρal, haY, hkL, hXdA, hX, hXi, hXid, hre⟩ :=
      iFold hρa hcak h9 hnoρp hGc hπdA hY
    have hPAo : en.PA k ls v₀ ρa := hT.paExt m i en hTe k ls'' ls v₀ ρa
      (hext ρa ρkL haY hρa (fun ψ h => by rw [hρal] at h; cases h)) hPA
    have hwcl : ∀ lsO, en'.wc ls lsO ρkL → extF ls lsO ρkL := by
      intro lsO he; rw [hwc', hwc] at he; exact he
    have hwcI : ∀ lsO, extF ls lsO ρkL →
        en.wc ls'' (frameList ⟨l, v, ρP, Ty, δ⟩ ds A lsO) ρk := by
      intro lsO he'
      rw [hwc]
      exact extF_ifold hX hXi (ResU.compS_single_get_self (ResU.CompS.comm hXid) (ResU.del_get_self _ _)) hkL hclP hNX hls'' he'
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, ρkL, haY,
        hPA' ▸ hPAo, fun hu' => absurd (hq'.symm.trans hu') hq, fun lsO he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩)⟩
    · simp only [erwpC, show k' < n by omega, if_true]
      rw [hPB'] at hB
      have he' := hwcl lsO he
      obtain ⟨ρbB, hρbB, hWXB⟩ :=
        (ResU.CompS.assoc ρlP (Xi.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
      have hσBA : σB.InStratum A := hT.pb m i en hTe _ _ _ _ hB
      refine ih k' (by omega) lsO _ ρbB XB (inStratum_compS hρbB hXdA hσBA)
        (hPloc ls lsO ρP (extF_right hclP (extF_right hkL he')) hPv) hWXB
        (fun BI' hBI' => ?_)
      have hB' : en.PB k' (frameList ⟨l, v, ρP, Ty, δ⟩ ds A lsO) w σB :=
        hT.pbExt m i en hTe k' lsO _ w σB (ext_add (addAt_frameList _ ds A lsO) hσBA) hB
      obtain ⟨Xk, g, hXk, hXkg, hg⟩ := hre σB ρbB BI' hρbB hBI'
      have hc := (hcont _ (hwcI lsO he')).1 k' hk' w σB Xk hB' hXk
      simp only [erwpC, show k' < n by omega, if_true] at hc
      exact erwp_garbage hXkg hg hc
    · have he' := hwcl lsO he
      have hql' : en.q ≠ .lin := hq' ▸ hql
      exact hcan m i en en' hTe hTe' hql' k lsO K ρk ρp X Xi ρkL
        hnoρp hX hXi hXid hXdA hkL
        ((hcont _ (hwcI lsO he')).2 hql')
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT.entry m i en hTe).1]; simp)

/-- **The lender's cancel obligations at `claimT … (claimI …)`**: the borrowed continuation's
cancel run, at `cancelOblN Φ T₁`, with the garbage added, framed by `erwp_I_frame_cancelRun`. -/
theorem claimIT_can {Φ : LocFam} (l : Loc) (Ty : VTy) (δ : LSub) (hadm : AdmWf Ty δ) (v : Val)
    {A : Life} {T T₁ : OpTabN} (hT₁ : T₁.ILendOK A)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel → en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁))
    (hq : ∀ m i en, T m i = some en → en.q ≠ .unr) {ρP ρlP : WRes} (houtP : ρP.InStratum A)
    (hshape : vShape Ty δ v ρP) (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d) :
    ICan T (@OpTabN.claimT ℍ _ T Φ T₁ (claimI l v ρP)) l Ty δ A v ρP ρlP houtP ds := by
  intro m i en en' hT hT' hql k lsO K ρk ρp X Xi ρkL hno hX hXi hXid hXdA hkL hc
  have hqc : en.q = .cancel := by
    have := hq m i en hT
    cases h : en.q <;> simp_all
  simp only [OpTabN.claimT, hT, Option.map_some, hqc, if_true, Option.some.injEq] at hT'
  subst hT'
  intro P' hP'
  simp only [Option.some.injEq] at hP'
  subst hP'
  have hin := hc _ (hfin m i en hT hqc)
  refine erwp_I_frame_cancelRun l Ty δ hadm v hT₁ k lsO _ ρP ρlP (Xi.del l) ρkL houtP hXdA
    hshape hclP (ResU.CompS.comm hkL) ds hds (fun BI hBI => ?_)
  obtain rfl := ResU.CompS.functional hBI hXid
  obtain ⟨g, hg, hkg⟩ := (ResU.CompS.assoc ρk ρp _ _).mpr ⟨X, hX, hXi⟩
  exact erwp_garbage hkg (noOwn_compS hg hno (noOwn_single_imm l _ _ _ _)) hin

/-- **Imm Frame at `erwp` across stops, cancellable stops included**: the lender's stops are at
`claimT`, whose cancel runs end carrying the lend's claim `ρ_ℓ ● ρ_P̂(v)`. -/
theorem erwp_I_frameC {Φ : LocFam} (l : Loc) (Ty : VTy) (δ : LSub) (hadm : AdmWf Ty δ) (v : Val)
    (P : List SRec → Val → WProp) (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {T T₁ : OpTabN} (hT : T.ILendOKC A) (hT₁ : T₁.ILendOK A)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel → en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁))
    {ρP ρlP : WRes} (houtP : ρP.InStratum A) (hshape : vShape Ty δ v ρP)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d) {Q : PostN}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ n ls e (ρb ρ : WRes), ρb.InStratum A → P ls v ρP → ResU.CompS ρlP ρb ρ →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (opTableN T) (IFPost l v P A Q) n (frameList ⟨l, v, ρP, Ty, δ⟩ ds A ls)
          e BI) →
      erwp (ℍ := ℍ) Φ (opTableN (@OpTabN.claimT ℍ _ T Φ T₁ (claimI l v ρP))) Q n ls e ρ :=
  erwp_I_frameT l Ty δ hadm v P hPshape hPloc hT (claimT_twin T Φ T₁ _) houtP hclP hds
    (claimIT_can l Ty δ hadm v hT₁ hfin (fun m i en h => (hT.entry m i en h).2.1) houtP hshape
      hclP hds) hQ

end BoCa.Fig16.LogRel.Core.Chain.SI

end
