import Core.Chain.SI.IFrameN
import Core.Chain.SI.StopFrameN

/-!
# An `imm` lend live across a stop, at `erwp`

**Not a transcription.** `[TR]` 6.64 is a lemma about a run that returns. `rwpG` asks its
post-configuration, `ρ ↭ₙ π`, at every final configuration; at a stop inside an Imm Frame the
lent cell is `imm({α}, v, ρ_P̂(v))` in `⦇π⦈` and `own(v)` in `⦇ρ⦈`, and `↭`'s `imm` clause fails
from right to left. This file does at a stop what the printed proof does at a return, with the
printed lemmas the proof uses, and carries the borrow across the stop the way `SI/StopFrameN.lean`
carries a `mut` one: folded into the continuation's share at the stop, lent again at the resume.

## What the printed proof already gives at any final configuration

The printed proof's steps after the run do not read the term the run ends at:

* **6.29** (`six29N`): `ρ_b ● ρᵢ ↭ π`, `@ρ_b ⊐ α`, give `π = π/ℓ ● ρᵢ`: the borrow is at the top
  level of `π`, and nowhere below it, since a cell holding it would be shorter than `α`.
  The same proof (`six29_borrows_offN`, then 6.50's second half at a location,
  `ResU.flat_inStratum_inv_at`) gives `@(π/ℓ) ⊐ α`.
* **6.38** (`six38N`) at `ρ′ := π/ℓ`, `ρ⁺ := ρᵢ`: H1–H6 hold (H4 by the line above, H5 since
  `ρᵢ` is one `imm` cell), and G1 is `π/ℓ # ρ_ℓ ● ρ_P̂(v)`.
* **6.39** (`six39N`): `ρ ↭ π/ℓ ● ρ_ℓ ● ρ_P̂(v)`.
* the memory (6.26 under a frame), `TWNC.immEnd`, the tags, and `ext_drop` for any part of the
  lender's resource in `Res_α` with no `imm` cell at `ℓ`.

At a return the printed proof applies 6.38 at `ρ′ :=` the returned resource and `ρ⁺ :=` the
garbage; here 6.38 is applied once for every final configuration at `ρ′ := π/ℓ`, `ρ⁺ := ρᵢ`. The
conclusion G1 is the same resource (`ρ′ ● ρ⁺/ℓ = π/ℓ` at a return), and the return case then
splits it as printed (`erwp_I_frame`, the value case: 6.38's `ρ′(ℓ) = ∅` at the box).

## What is new at a stop

At a stop `π = ρ_a ● ρ_k ● ρ⁺`, with `ρ_a` the payload and `ρ_k` the continuation's share. The
borrow can be at the top of `ρ_k` and of `ρ⁺` and, if the payload is in `Res_α`, not of `ρ_a`.
**6.116** (`I-dup`, `ρᵢ = ρᵢ ● ρᵢ`) makes the arrangement irrelevant: `X ● ρᵢ`, `X = ρ_k ● ρ⁺`, is
defined and is `(X ● ρᵢ)/ℓ ● ρᵢ`, whatever `X` held at `ℓ`. The lender keeps
`(X ● ρᵢ)/ℓ ● ρ_ℓ ● ρ_P̂(v)` as the continuation's share. At the resume, at whatever list the
handler resumes at, it lends the cell again at the **same** `α` and the same record, pushed onto
that list; the body gets `(X ● ρᵢ)/ℓ ● σ_B ● ρᵢ = ρ_k ● σ_B ● (ρ⁺ ● ρᵢ)`, the continuation's
resource and garbage that owns nothing.

## The resume list

The handler resumes at any list `extF` allows at the lender's share (`SI/ExtF.lean`). Two facts
make that enough, and neither reads the list's tags:

* **The borrowed continuation's `extF`** (`extF_ifold`): a location frozen in its share is frozen
  in the lender's share, or is `ℓ` or an exclusive location of `ρ_P̂(v)`. Those the frame's own
  records name, which the re-entry pushes again; no record of the caller's list names them,
  since at the frame's entry they are exclusive in the world (`not_relAt_xex`).
* **The exit's tags**: a record of the caller's list is not in the frame's lineage
  (`notDesc_frame`), so its tag is not the frame's. 6.64's freshness of `α` (6.112's `⋔`, every
  record longer than `α`) is not read: a handler's own frame, at any lifetime, may sit in the list
  the lend is re-entered at.

## The conditions (`OpTabN.ILendOK`)

As `OpTabN.LendOK`, with two changes the Imm Frame forces:

* `PB` in `Res_α` rather than `Res_{↓α}`: the frame of a 6.64 entry is in `Res_α` (H11).
* `PA` and `PB` stable along `Ext`: 6.64 changes the list (`frameList`), so what crosses the
  frame's boundary is read at both lists, as `Q` is in the printed statement (`hQ`).
* The payload predicate `P̂` stable along `extF` (`hPloc`): it is read again at the resume list.

## Soundness

The lender's post-configuration at a stop is the one 6.64's proof builds at a return, at the
resource the run ended at. The only change of resource is the borrow `ρᵢ` replaced by
`ρ_ℓ ● ρ_P̂(v)` — the move 6.64 makes at a return. At the resume the lender re-enters with the
same `α`, `ρ_P̂(v)` and record, which is the entry 6.64 makes, at the list the handler chose.
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

/-! ### Small facts -/

/-- A composite with a singleton, the other factor undefined at the location, is the deletion. -/
theorem eq_del_of_compS_single {G π : WRes} {l : Loc} {ψ : CellU Loc Val}
    (h : ResU.CompS G (ResU.single l ψ) π) (hG : G.get l = none) : G = π.del l := by
  refine PMap.ext fun m => ?_
  by_cases hm : m = l
  · subst hm; rw [hG, ResU.del_get_self]
  · rw [ResU.del_get_ne _ hm, ResU.Comp.get_of_right_none h (ResU.single_get_ne ψ hm)]

/-- `[TR]` 6.116 (`I-dup`) at a cell: `ρᵢ = ρᵢ ● ρᵢ`. -/
theorem compS_imm_dup (l : Loc) (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join) :
    ResU.CompS (ResU.single l (CellU.immOf s v χ h)) (ResU.single l (CellU.immOf s v χ h))
      (ResU.single l (CellU.immOf s v χ h)) := by
  have h₃ : χ.InStratum (s ∪ s).join := ResU.InStratum.sup h h
  have e : CellU.immOf (s ∪ s) v χ h₃ = CellU.immOf s v χ h :=
    CellU.immOf_congr (LSet.union_self s) rfl rfl h₃ h
  have hcomp := ResU.compS_single_imm l s s v χ h h h₃
  rw [e] at hcomp
  exact hcomp

/-- The own cell and a payload in `Res_α` are in `Res_α`. -/
theorem inStratum_ownP {l : Loc} {v : Val} {ρP ρlP : WRes} {α : Life}
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hP : ρP.InStratum α) :
    ρlP.InStratum α :=
  inStratum_compS hclP (ResU.inStratum_single l (by simp [CellU.InStratum, CellU.ownOf])) hP

/-! ### The Imm Frame at any final term -/

/-- **The lender's side of an Imm Frame at any final term**, at a lifetime `α` fixed by the
caller (`[TR]` 6.64's proof from the entry on, at `rwpG`). The entry is the printed one at `α`:
`TWNC.immFrame` and the frame list `frameList p ds α ls` with `ds` the record's lineage. At the
end, at whatever final term: 6.29, 6.38 at `ρ′ := π/ℓ`, `ρ⁺ := ρᵢ`, 6.39, the memory and
`TWNC.immEnd`, as printed; `hpost` splits `π/ℓ ● ρ_ℓ ● ρ_P̂(v)` for the caller's postcondition,
given `ext_drop` for its parts and that no record of the caller's list names an exclusive
location of `ℓ ↦ own(v) ● ρ_P̂(v)` (`not_relAt_xex` at the entry world).

**Forced change at the exit's tags.** The printed proof takes `α` fresh (6.112's `⋔`: every record
longer than `α`), so a record of the caller's list is not tagged by the frame. At a resume the list
is the handler's and `α` the first entry's, so freshness is not available; the exit reads instead
that no record of the caller's list is in the frame's lineage (`notDesc_frame`, from the entry
world). The printed freshness technique is not used here. -/
theorem rwpG_I_frameG {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    {A : Life} {ρP ρlP ρb ρ : WRes} (houtP : ρP.InStratum A) (houtb : ρb.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (hshape : vShape T δ v ρP) {ls : List SRec}
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d)
    {Qin Qout : PostG} {n : Nat} {e : Expr}
    (hpost : ∀ k, k ≤ n → ∀ ls'' t (ρ' ρp π Y : WRes), Qin k ls'' t ρ' → NoOwn ρp →
      ResU.CompS ρ' ρp π → (∀ x, x ∈ ls'' ↔ x ∈ frameList ⟨l, v, ρP, T, δ⟩ ds A ls) →
      ResU.CompS (π.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) π →
      (π.del l).InStratum A → ResU.CompS (π.del l) ρlP Y →
      (∀ R Z, ResU.CompS R Z Y → R.InStratum A →
        (∀ ψ : CellU Loc Val, R.get l = some ψ → ψ.kind ≠ Kind.imm) → Ext ls'' ls R) →
      (∀ r ∈ rsOf ls, ∀ m, XEx ρlP m → ¬ RelAt r m) →
      ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ Qout k ls t ρ'L)
    (hA : ∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
      rwpG (ℍ := ℍ) Φ Qin n (frameList ⟨l, v, ρP, T, δ⟩ ds A ls) e BI) :
    rwpG (ℍ := ℍ) Φ Qout n ls e ρ := by
  classical
  intro ρf sρ ps μ hH3 hsρ hT htg hI hlow hfd jr μ' e' hj hrun hfin
  have hTI := hT.inv
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  have houtlP : ρlP.InStratum A := inStratum_ownP hclP houtP
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP :=
    ResU.CompS.comm hclP
  -- H12-H17: the compatibility block
  have hH12 : ResU.Hash ρb ρlP :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb ρi := ResU.six34 hlPcell hH12
  obtain ⟨hlPf, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf ρi := ResU.six34 hlPcell (ResU.hash_symm hlPf)
  obtain ⟨BI, hBI⟩ := (ResU.compS_defined_iff ρb ρi).mpr hH13.1
  have hH17 : ResU.Hash ρf BI :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBI
  obtain ⟨fρ, h4, hvfρ⟩ := hH17.2
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBi⟩ := (ResU.CompS.assoc ρf ρb ρi fρ).mp ⟨BI, hBI, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  -- the record and the entry
  set p : FrameRec := ⟨l, v, ρP, T, δ⟩ with hpdef
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvsρ
  set ls' : List SRec := frameList p ds A ls with hls'def
  have hadd : AddAt ls ls' A := addAt_frameList p ds A ls
  have hTin : TWNC fρ (p :: ps) (rsOf ls') := by
    rw [hls'def, rsOf_frameList]
    exact TWNC.immFrame T δ houtP hT hadm hclP (ResU.CompS.comm hFBl) hshape
      (ResU.CompS.comm hFBi) hvfρ hds
  obtain ⟨hFLnew, hFLold⟩ :=
    frameLife_frame T δ hvsρ hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBi) hTI
  have htgin : Tagged fρ (p :: ps) ls' := by
    intro x hx
    simp only [hls'def, frameList, List.mem_cons, List.mem_append, List.mem_map] at hx
    rcases hx with rfl | ⟨d, hd, rfl⟩ | hx
    · exact ⟨p, List.mem_cons_self, DescR.refl p, hFLnew⟩
    · obtain ⟨q, hq, hqd⟩ := (hds d).mp hd
      exact ⟨p, List.mem_cons_self, ⟨q, hqd⟩, hFLnew⟩
    · obtain ⟨q, hq, hqd, hfq⟩ := htg x hx
      exact ⟨q, List.mem_cons_of_mem _ hq, hqd, hFLold q hq x.2 hfq⟩
  -- the same memory, by 6.26 under a frame (6.8)
  have hvlP : ResU.Valid ρlP := by
    obtain ⟨-, s, hs, hv⟩ := hH12; exact (ResU.Valid.split hs hv).2
  have hvBI : ResU.Valid BI := by
    obtain ⟨-, s, hs, hv⟩ := hH17; exact (ResU.Valid.split hs hv).2
  have hvi : ResU.Valid ρi := (ResU.Valid.split hBI hvBI).2
  have hFBiH : ResU.Hash FB ρi :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hH15)
      (ResU.hash_symm hbf) (ResU.hash_symm hH13) hFB)
  have hFBlH : ResU.Hash FB ρlP :=
    ResU.hash_symm
      (ResU.hash_of_pairwise hlPf (ResU.hash_symm hbf) (ResU.hash_symm hH12) hFB)
  have hlowin : ResU.Lower fρ μ :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFBi hFBiH hFBl hFBlH).mpr hlow
  -- H18: the run under the frame
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps'', ls'', h1, h2, h3, h6, h7, h9, h10, h11, hT'', htg'',
    hps'', hls'', h12⟩ :=
    hA BI hBI ρf fρ (p :: ps) μ hH17 h4 hTin htgin
      (hI.of_sub fun r hr => by
        rw [hls'def, rsOf_frameList]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hr))
      hlowin hfd jr μ' e' hj hrun hfin
  have hvπ : ResU.Valid π := h10.2.2
  -- 6.29: `π = π/ℓ ● ρᵢ`, and every other cell of `⦇π⦈` outlives `α`
  have hGc : ResU.CompS (π.del l) ρi π := six29N houtb hlPcell hH12 hBI h10
  obtain ⟨σπ, hσπ⟩ := hvπ
  have hoff := (six29_borrows_offN houtb hlPcell hH12 hBI h10 hσπ).2
  have hπdA : (π.del l).InStratum A := by
    intro m ψ hm
    by_cases hml : m = l
    · subst hml; rw [ResU.del_get_self] at hm; exact absurd hm (by simp)
    · rw [ResU.del_get_ne _ hml] at hm
      exact ResU.flat_inStratum_inv_at hσπ (fun φ hφ => hoff m hml φ hφ) hm
  -- 6.38 at `ρ′ := π/ℓ`, `ρ⁺ := ρᵢ`
  have hidel : ρi.del l = PMap.empty := by
    refine PMap.ext fun m => ?_
    by_cases hml : m = l
    · subst hml; rw [ResU.del_get_self]; rfl
    · rw [ResU.del_get_ne _ hml, ResU.single_get_ne _ hml]; rfl
  obtain ⟨G₀, hG₀, hGW⟩ := six38N (ρ' := π.del l) (ρp := ρi) hlPcell hH12
    ⟨hGc.1, π, hGc, ⟨σπ, hσπ⟩⟩ houtb hπdA (noOwn_single_imm l _ _ _ _) hBI hGc h10
  rw [hidel] at hG₀
  obtain rfl : π.del l = G₀ := ResU.CompS.functional (ResU.comp_empty_right _) hG₀
  -- 6.39: `ρ ↭ π/ℓ ● ρ_ℓ ● ρ_P̂(v)`
  obtain ⟨w₁, Y, hw₁, hY, hupdw⟩ := six39N hclP hH12 hGW hBI hGc h10
  obtain rfl : ρ = w₁ := ResU.CompS.functional (ResU.CompS.comm hcρ) hw₁
  -- the worlds at the end: `ρ_f ● π = (ρ_f ● π/ℓ) ● ρᵢ`, and `(ρ_f ● π/ℓ) ● ρ_ℓ ● ρ_P̂(v)`
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  obtain ⟨π₁, hπ₁, hfπ⟩ := (ResU.CompS.assoc ρf ρ' ρp fρ'p).mpr ⟨fρ', h2, h6⟩
  obtain rfl : π = π₁ := ResU.CompS.functional h9 hπ₁
  obtain ⟨FP, hFP, hFPi⟩ := (ResU.CompS.assoc ρf (π.del l) ρi fρ'p).mp ⟨π, hGc, hfπ⟩
  have hfπH : ResU.Hash π ρf := ⟨(ResU.CompS.comm hfπ).1, fρ'p, ResU.CompS.comm hfπ, hvfρ'p⟩
  obtain ⟨hDf, -⟩ := ResU.Hash.split hGc hfπH
  have hflP : ResU.Hash ρf ρlP := ResU.hash_symm hlPf
  have hfY : ResU.Hash ρf Y := ResU.hash_of_pairwise (ResU.hash_symm hDf) hGW hflP hY
  obtain ⟨FY, hFY, hvFY⟩ := hfY.2
  obtain ⟨FP₁, hFP₁, hFPlP⟩ := (ResU.CompS.assoc ρf (π.del l) ρlP FY).mp ⟨Y, hY, hFY⟩
  obtain rfl : FP = FP₁ := ResU.CompS.functional hFP hFP₁
  have hFPiH : ResU.Hash FP ρi := ⟨hFPi.1, fρ'p, hFPi, hvfρ'p⟩
  have hFPlH : ResU.Hash FP ρlP := ⟨hFPlP.1, FY, hFPlP, hvFY⟩
  have hmem₂ : ResU.Lower FY μ' :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFPi hFPiH hFPlP hFPlH).mp h7
  -- the frame's record and its lifetime at the end
  obtain ⟨aF, haF⟩ := agW_of_valid hvfρ'p
  have hρiF : ResU.Le ρi fρ'p := ⟨FP, ResU.CompS.comm hFPi⟩
  obtain ⟨ζl, tl, eζl, htl, hAl⟩ := ag_ls_of_le hρiF haF (ResU.single_get_self _ _)
    (CellU.lsOf_immOf _ _ _ _) (show (LSet.singleton A).mem A from rfl)
  have hpps : p ∉ ps := by
    intro hp
    obtain ⟨ψ, eψ, -⟩ := hTI.2.1 p hp aW haW
    have Wl : sρ.get l = some (CellU.ownOf v) :=
      (ResU.CompS.get_right_of_ne_imm hFBl (ResU.CompS.get_left_of_ne_imm hclP
        (ResU.single_get_self _ _) (by simp)).2 (by simp)).2
    exact ex_ag_disjoint hvsρ heW haW (ExS.get_of_ne_imm heW Wl (by simp)) eψ
  have hp'' : p ∈ ps'' := (hps'' p).mpr List.mem_cons_self
  obtain ⟨α', hα'⟩ := hT''.linLife p hp''
  have hαA : A = α' := frameLife_eq hα' haF eζl htl hAl
  subst hαA
  have hls''add : AddAt ls ls'' A :=
    ⟨fun x hx => (hls'' x).mpr (hadd.1 x hx),
     fun x hx hn => hadd.2 x ((hls'' x).mp hx) hn⟩
  -- the parts of `π/ℓ ● ρ_ℓ ● ρ_P̂(v)` hold no view of the frame's lineage (`ext_drop`)
  have hicpY : ∀ m, ICpAt aF Y m := by
    intro m
    have hD : ICpAt aF (π.del l) m :=
      icpAt_trans (icpAt_right (ResU.CompS.toCompR hFP) m)
        (icpAt_trans (icpAt_left (ResU.CompS.toCompR hFPi) m) (icpAt_agW haF m))
    obtain ⟨ψl, eψl, kψl, wψl, rψl⟩ := compS_get_right' hFPi (ResU.single_get_self _ _)
    obtain ⟨sl, hsl, hψl⟩ := CellU.imm_eta (kψl.trans (CellU.kind_immOf _ _ _ _))
    rw [hψl] at eψl
    obtain ⟨e₀, a₀, -, ha₀, icp₀⟩ := escrow_icp haF eψl
    have hwl : ψl.wit = ρP := wψl.trans (CellU.wit_immOf _ _ _ _)
    rw [hwl] at ha₀
    have hρP : ICpAt aF ρP m := icpAt_trans (icpAt_agW ha₀ m) (icp₀ m)
    exact icpAt_comp (ResU.CompS.toCompR hY) hD
      (icpAt_comp (ResU.CompS.toCompR hclP)
        (icpAt_of_immFree (fun x ψ e => by
          obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; simp) m) hρP)
  have hext : ∀ R Z, ResU.CompS R Z Y → R.InStratum A →
      (∀ ψ : CellU Loc Val, R.get l = some ψ → ψ.kind ≠ Kind.imm) → Ext ls'' ls R := by
    intro R Z hRZ hRα hRl
    have hicpR : ∀ m, ICpAt aF R m := fun m =>
      icpAt_trans (icpAt_left (ResU.CompS.toCompR hRZ) m) (hicpY m)
    refine ext_drop hls''add hRα fun r hr hrel => ?_
    obtain ⟨t, ht⟩ := mem_rsOf.mp hr
    have ht' := (hls'' _).mp ht
    simp only [hls'def, frameList, List.mem_cons, List.mem_append, List.mem_map] at ht'
    rcases ht' with h | ⟨d, hd, h⟩ | h
    · cases h
      exact (not_rel_lineage hα' haF hicpR hRα hRl (DescR.refl p) hrel).elim
    · cases h
      obtain ⟨q, hq, hqd⟩ := (hds _).mp hd
      exact (not_rel_lineage hα' haF hicpR hRα hRl ⟨q, hqd⟩ hrel).elim
    · exact mem_rsOf.mpr ⟨t, h⟩
  -- exit: `TWNC.immEnd` at `p`, back to the caller's records
  have hTout : TWNC FY ps (rsOf ls) :=
    TWNC.immEnd p hT'' hp'' (ResU.CompS.comm hFPi) hclP (ResU.CompS.comm hFPlP) hvFY
      (fun r' => ⟨fun h => ⟨(hps'' r').mpr (List.mem_cons_of_mem _ h),
        fun e => hpps (e ▸ h)⟩, fun ⟨h, hne⟩ => by
          rcases List.mem_cons.mp ((hps'' r').mp h) with e | h'
          · exact absurd e hne
          · exact h'⟩)
      hTI.2.2.2.2.2.2.1
  have backOut : ∀ a', AgW FY a' → ∀ m, ICpAt aF a' m := by
    intro a' ha' m
    obtain ⟨aσ, aY, eR', aR, pR, heR', -, hpR, hcp, hσY, hRY⟩ :=
      end_walks (ResU.CompS.comm hFPi) hclP (ResU.CompS.comm hFPlP) haF ha'
    exact icpAt_comp hRY (icpAt_trans (icpAt_right hpR m)
      (icpAt_trans (icpAt_right hcp m) (icpAt_left hσY m))) (icpAt_right hσY m)
  have htgout : Tagged FY ps ls := by
    intro x hx
    obtain ⟨q, hq, hqd, hfq⟩ := htg'' x ((hls'' x).mpr (hadd.1 x hx))
    have hqp : q ≠ p := by
      rintro rfl
      exact notDesc_frame hvsρ hTI hclP ⟨FB, ResU.CompS.comm hFBl⟩ (mem_rsOf.mpr ⟨_, hx⟩) hqd
    have hq' : q ∈ ps := by
      rcases List.mem_cons.mp ((hps'' q).mp hq) with e | h
      · exact absurd e hqp
      · exact h
    exact ⟨q, hq', hqd, frameLife_back hfq (fun a' ha' =>
      ⟨aF, haF, backOut a' ha' _, fun m _ => backOut a' ha' m⟩)⟩
  -- the lender's post-configuration
  obtain ⟨ρ'L, ρpL, hLY, hnoL, hQ⟩ :=
    hpost (n - jr) (by omega) ls'' e' ρ' ρp π Y h12 h11 h9 hls'' hGc hπdA hY hext
      (fun r hr m hx => not_relAt_xex hvsρ hTI ⟨FB, ResU.CompS.comm hFBl⟩ hr hx)
  obtain ⟨fL, hf1, hf2⟩ := (ResU.CompS.assoc ρf ρ'L ρpL FY).mp ⟨Y, hLY, hFY⟩
  have hvfL : ResU.Valid fL := (ResU.Valid.split hf2 hvFY).1
  exact ⟨ρ'L, ρpL, fL, FY, Y, ps, ls,
    ⟨(ResU.CompS.comm hf1).1, fL, ResU.CompS.comm hf1, hvfL⟩, hf1,
    ⟨(ResU.CompS.comm hf2).1, FY, ResU.CompS.comm hf2, hvFY⟩, hf2, hmem₂, hLY, hupdw, hnoL,
    hTout, htgout, fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩

/-! ### The Imm Frame across stops -/

/-- **`extF` across the Imm Frame's fold.** The continuation's share `ρ_k` is a part of `X`, and
`X ● ρᵢ = Xᵢ` holds `ℓ ↦ imm(s, v, ρ_P)`; the lender's share is `Xᵢ/ℓ ● ℓ ↦ own(v) ● ρ_P`. A
location frozen in `ρ_k` is frozen in `Xᵢ/ℓ`, is `ℓ`, or lies in `ρ_P`, where it is frozen or
exclusive. Exclusive locations of `ℓ ↦ own(v) ● ρ_P` are named by no record of the caller's list
(`not_relAt_xex` at the frame's entry); the frame's own records are taken again at the resume. -/
theorem extF_ifold {ls lsO ls'' : List SRec} {p : FrameRec} {ds : List FrameRec} {A : Life}
    {ρk ρp X ρi Xi ρkL ρlP ρP : WRes} {l : Loc} {v : Val} {s : LSet} {hs : ρP.InStratum s.join}
    (hX : ResU.CompS ρk ρp X) (hXi : ResU.CompS X ρi Xi)
    (hXil : Xi.get l = some (CellU.immOf s v ρP hs))
    (hkL : ResU.CompS (Xi.del l) ρlP ρkL)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    (hNX : ∀ r ∈ rsOf ls, ∀ m, XEx ρlP m → ¬ RelAt r m)
    (hls'' : ∀ x, x ∈ ls'' ↔ x ∈ frameList p ds A ls)
    (h : extF ls lsO ρkL) : extF ls'' (frameList p ds A lsO) ρk := by
  intro r hr ⟨m, hf, hm⟩
  obtain ⟨t, ht⟩ := mem_rsOf.mp hr
  have ht' := (hls'' _).mp ht
  rw [rsOf_frameList]
  have hr' : r = p ∨ r ∈ ds ∨ r ∈ rsOf ls := by
    simp only [frameList, List.mem_cons, List.mem_append, List.mem_map] at ht'
    rcases ht' with h1 | ⟨d, hd, h2⟩ | h3
    · exact Or.inl (Prod.mk.inj h1).1
    · exact Or.inr (Or.inl ((Prod.mk.inj h2).1 ▸ hd))
    · exact Or.inr (Or.inr (mem_rsOf.mpr ⟨t, h3⟩))
  rcases hr' with rfl | hd | hro
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ hd)
  · refine List.mem_cons_of_mem _ (List.mem_append_right _ (h r hro ⟨m, ?_, hm⟩))
    have hlP : XEx ρlP l := ⟨[], ρlP, _, XPath.nil _,
      (ResU.CompS.get_left_of_ne_imm hclP (ResU.single_get_self _ _) (by simp)).2, by simp⟩
    rcases ((hf.of_compS_left hX).of_compS_left hXi).del_or (l := l) with hd | ⟨φ, eφ, hφ⟩
    · exact hd.of_compS_left hkL
    · rw [hXil] at eφ; cases Option.some.inj eφ
      rcases hφ with ⟨-, hml | hin⟩ | ⟨k, -⟩
      · subst hml; exact absurd hm (hNX r hro _ hlP)
      · rw [CellU.wit_immOf] at hin
        rcases hin.frz_or_xex with hfz | hxx
        · exact (hfz.of_compS_right hclP).of_compS_right hkL
        · exact absurd hm (hNX r hro m (hxx.of_compS_right hclP))
      · simp at k

/-- **A table whose stops may be taken under a live `imm` lend at `A`.** As `OpTabN.LendOK`, with
`PB` in `Res_A` (6.64's H11: the frame outlives the lend) and both payload predicates stable
along `Ext` (6.64 changes the list; the printed statement asks the same of `Q`, `hQ`). -/
structure OpTabN.ILendOK (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q = .lin ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum A
  paExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ v (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PA k ls₁ v ρ → en.PA k ls₂ v ρ
  pbExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ w (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PB k ls₁ w ρ → en.PB k ls₂ w ρ

/-- The lender's postcondition for the borrowed run, `[α] (ℓ ↦ v ─⋆ P̂(v) ─⋆ Q̂)` as printed. -/
def IFPost (l : Loc) (v : Val) (P : List SRec → Val → WProp) (A : Life) (Q : PostN) : PostN :=
  fun k ls'' w => box A (ptoOwn l v ─⋆ (P ls'' v ─⋆ Q k ls'' w))

/-- **Imm Frame at `erwp`, across stops**, at a lifetime `A` the first entry chose. `ℓ ↦ v ⋆
P̂(ls)(v) ⋆ ρ_b`, `ρ_b` in `Res_A`, the caller's records longer than `A`, lent `imm` at `A` to a
computation in `erwp` from `ρ_b ● ρᵢ` at `frameList p ds A ls`, that may stop at an `ILendOK`
table with the lend live: the computation is in `erwp`. At a return, 6.64; at a stop, the
borrow folded into the continuation's share (6.116); at the resume, lent again at `A`, by
induction on the index. -/
theorem erwp_I_frame {Φ : LocFam} (l : Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    (P : List SRec → Val → WProp) (hPshape : ∀ ls ρ, P ls v ρ → vShape T δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {Tb : OpTabN} (hT : Tb.ILendOK A) {Q : PostN}
    (hQ : ∀ k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q k ls₁ w ρ → Q k ls₂ w ρ) :
    ∀ n ls e (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A), ρb.InStratum A →
      P ls v ρP → ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      ∀ ds, (∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, T, δ⟩ d) →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwp (ℍ := ℍ) Φ (opTableN Tb) (IFPost l v P A Q) n (frameList ⟨l, v, ρP, T, δ⟩ ds A ls)
          e BI) →
      erwp (ℍ := ℍ) Φ (opTableN Tb) Q n ls e ρ := by
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
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
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
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT.entry m i en hTe).1]; simp)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
