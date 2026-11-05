import Core.Chain.SI.CaptureScope
import Core.Chain.SI.StopFrameN

/-!
# A `mut` lend to one other task: the Mut Frame left open at stops, ended after a join

**Not a transcription.** `[TR]` 6.65 across stops without folding, for a borrow that leaves the
lender: entered as 6.65 enters it (`TWNC.mutFold`, `capture_worldM`), left open at every stop of
the body, ended after `join(ℓ)` (`TWNC.mutUnfold`, `uncapture_worldM`).

What differs from the `imm` scope (`SI/CaptureScope.lean`):

* **No record, no frame condition.** A `mut` lend adds no frame record, and a `mut` cell composes
  with nothing: whoever holds the borrow holds it alone. At the join's resume the borrow is back in
  the joiner's resource (`joinPBvM`), so no other computation can hold a cell at `ℓ` at the top,
  and 6.24 (`ResU.six24`) makes the world compatible with the cell's unfolding, at any depth.
* **The borrow comes back through the join's answer**, not through the body's run: 6.27 and 6.28,
  which 6.65 reads off the body's `↭` at its end, do not apply; what the lender learns about the
  cell (its predicate `P̂`, its lifetime) is the answer's (`joinPBvM` names them: the join of a
  `mut` scope is the scope's own operation). The predicate is read from the cell itself, as
  `rwpG_M_frameG` reads `P̂″` at its end; here it is `P̂` because the answer says so.
* **The body is any `cerwp` computation** whose operations are must-resume (`cerwp_bindK`): it
  stops at the lender's table, with the lend open.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-! ### Bind across stops -/

/-- **Bind across stops, at a table of must-resume operations**: the stops of `e` are stops of
`K[e]`, their continuations wrapped in `K`, by induction on the index; the continuation `K[v]` at
every frame condition a resume may have strengthened. -/
theorem cerwp_bindK {T : OpTabC} {Q Q' : PostCV} (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hlin : ∀ m i en, T m i = some en → en.q = .lin)
    (hcont : ∀ (F : WRes → Prop) k ls O (v : Val) ρ, Q' k ls O v ρ →
      cerwp (ℍ := ℍ) (opTableC T) Q F k ls O (K.plug v.1) ρ) :
    ∀ n (F : WRes → Prop) ls O e ρ, cerwp (ℍ := ℍ) (opTableC T) Q' F n ls O e ρ →
      cerwp (ℍ := ℍ) (opTableC T) Q F n ls O (K.plug e) ρ := by
  have hL := opTableC_local T
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F ls O e ρ h
  rw [cerwp_eq]
  refine crwpG_bind K (crwpG_mono_le (fun k hk ls' O' t ρ' ht => ?_) (cerwp_unfold_at hL le_rfl h))
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, w, en, hp⟩
  · exact cerwp_unfold_at hL hk (hcont F k ls' O' v ρ' hv)
  · obtain ⟨⟨rfl, hK₁, hT, ha, hoc⟩, ρa, ρk, hcak, hA, hu, hcont'⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).HasHnd m = false := by rw [hasHnd_comp, hH m, hK₁]; rfl
    rw [← Kont.plug_comp]
    refine crwpG_here (final_opPlug (r := false) (payloadName_opPayload m i w) hKo) (Or.inr
      ⟨K.comp K₁, m, i, w, en, pure_sep_mk ⟨rfl, hKo, hT, ha, hoc⟩ ⟨ρa, ρk, hcak, hA, hu,
        fun ls'' he => ⟨fun k' hk' w' τ₁ τ₂ hB hcτ => ?_,
          fun hq => absurd (hlin m i en hT) hq⟩⟩⟩)
    have h₁ := (hcont' ls'' he).1 k' hk' w' τ₁ τ₂ hB hcτ
    simp only [cerwpC, show k' < n by omega, if_true] at h₁ ⊢
    rw [Kont.plug_comp]
    exact ih k' (by omega) _ _ _ _ _ h₁

/-! ### The world at a `mut` lend's entry and end -/

/-- **A `mut` lend's entry** (`rwpG_M_frameG`'s entry, verbatim): `TWNC.mutFold`, the memory by
6.25 under a frame, the tags unchanged. -/
theorem capture_worldM {l : Loc} {A : Life} {v : Val} {ρP ρlP ρb ρ : WRes}
    (houtP : ρP.InStratum A) {P : Val → SPropS Loc Val A} (hwit : P v ⟨ρP, houtP⟩)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    {ρf sρ : WRes} {ps : List FrameRec} {ls : List SRec} {μ : Heap}
    (hH3 : ResU.Hash ρf ρ) (hsρ : ResU.CompS ρf ρ sρ) (hT : TWNC sρ ps (rsOf ls))
    (htg : Tagged sρ ps ls) (hlow : ResU.Lower sρ μ) :
    ∃ BM fρ, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM ∧
      ResU.Hash ρf BM ∧ ResU.CompS ρf BM fρ ∧ TWNC fρ ps (rsOf ls) ∧ Tagged fρ ps ls ∧
      ResU.Lower fρ μ := by
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  set ρm : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.mutOf A v ρP houtP P hwit) with hρm
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP :=
    ResU.CompS.comm hclP
  have hH12 : ResU.Hash ρb ρlP :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb ρm := (ResU.six24 hlPcell).mpr hH12
  obtain ⟨hlPf, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf ρm :=
    (ResU.six24 hlPcell).mpr (ResU.hash_symm hlPf)
  obtain ⟨BM, hBM⟩ := (ResU.compS_defined_iff ρb ρm).mpr hH13.1
  have hH17 : ResU.Hash ρf BM :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBM
  obtain ⟨fρ, h4, hvfρ⟩ := hH17.2
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBm⟩ := (ResU.CompS.assoc ρf ρb ρm fρ).mp ⟨BM, hBM, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  have hTin : TWNC fρ ps (rsOf ls) :=
    TWNC.mutFold hT hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) a).mpr ha) htg
  have hvlP : ResU.Valid ρlP := by
    obtain ⟨-, s, hs, hv⟩ := hH12; exact (ResU.Valid.split hs hv).2
  have hvBM : ResU.Valid BM := by
    obtain ⟨-, s, hs, hv⟩ := hH17; exact (ResU.Valid.split hs hv).2
  have hvmm : ResU.Valid ρm := (ResU.Valid.split hBM hvBM).2
  have hFBmH : ResU.Hash FB ρm :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hH15)
      (ResU.hash_symm hbf) (ResU.hash_symm hH13) hFB)
  have hFBlH : ResU.Hash FB ρlP :=
    ResU.hash_symm (ResU.hash_of_pairwise hlPf (ResU.hash_symm hbf) (ResU.hash_symm hH12) hFB)
  have hlowin : ResU.Lower fρ μ :=
    (ResU.lower_swap_mut_own hlPcell hvmm hvlP hFBm hFBmH hFBl hFBlH).mpr hlow
  exact ⟨BM, fρ, hBM, hH17, h4, hTin, htgin, hlowin⟩

/-- **A `mut` lend's end in a resumed segment**: the borrow `ℓ ↦ mut(A, u, χ, P̂)` back in the
resource `ρ₀ ● ℓ ↦ mut(…)`. 6.24 makes the frame and `ρ₀` compatible with `χ ● ℓ ↦ own(u)`;
`TWNC.mutUnfold`, the memory by 6.25 under a frame, the tags unchanged. -/
theorem uncapture_worldM {l : Loc} {A : Life} {u : Val} {χ : WRes} {hχ : χ.InStratum A}
    {P : Val → SPropS Loc Val A} {hu : P u ⟨χ, hχ⟩} {ρ₀ X ρf W W'' : WRes}
    {ps : List FrameRec} {ls : List SRec} {μ : Heap}
    (hX : ResU.CompS ρ₀ (ResU.single l (CellU.mutOf A u χ hχ P hu)) X)
    (hW : ResU.CompS ρf X W) (hT : TWNC W ps (rsOf ls)) (htg : Tagged W ps ls)
    (hlow : ResU.Lower W μ) (hW'' : ResU.CompS χ (ResU.single l (CellU.ownOf u)) W'') :
    ∃ ρout W', ResU.CompS ρ₀ W'' ρout ∧ ResU.Hash ρf ρout ∧ ResU.CompS ρf ρout W' ∧
      TWNC W' ps (rsOf ls) ∧ Tagged W' ps ls ∧ ResU.Lower W' μ := by
  set ρm : WRes := ResU.single l (CellU.mutOf A u χ hχ P hu) with hρm
  have hvW : ResU.Valid W := by obtain ⟨σ, hσ, -⟩ := hlow; exact ⟨σ, hσ⟩
  obtain ⟨Z, hZ, hZW⟩ := (ResU.CompS.assoc ρf ρ₀ ρm W).mp ⟨X, hX, hW⟩
  have hZm : ResU.Hash Z ρm := ⟨hZW.1, W, hZW, hvW⟩
  have hZW'' : ResU.Hash Z W'' := (ResU.six24 hW'').mp hZm
  obtain ⟨W', hW', hvW'⟩ := hZW''.2
  have hvm : ResU.Valid ρm := (ResU.Valid.split hZW hvW).2
  have hvW'' : ResU.Valid W'' := (ResU.Valid.split hW' hvW').2
  have hlow' : ResU.Lower W' μ :=
    (ResU.lower_swap_mut_own hW'' hvm hvW'' hZW hZm hW' hZW'').mp hlow
  have hT' : TWNC W' ps (rsOf ls) :=
    TWNC.mutUnfold hT (ResU.CompS.comm hZW) (ResU.CompS.comm hW'') (ResU.CompS.comm hW') hvW'
  have htg' : Tagged W' ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW'') (ResU.CompS.comm hW') (ResU.CompS.comm hZW) a).mp ha) htg
  obtain ⟨ρout, hρout, hfW'⟩ := (ResU.CompS.assoc ρf ρ₀ W'' W').mpr ⟨Z, hZ, hW'⟩
  exact ⟨ρout, W', hρout, ⟨hfW'.1, W', hfW', hvW'⟩, hfW', hT', htg', hlow'⟩

/-! ### The scope -/

/-- **The join of a `mut` scope**: must-resume, the lent location as payload, answered with the
borrow of that location back, at the scope's lifetime and predicate. -/
def joinEntM (l : Loc) (A : Life) (P : Val → SPropS Loc Val A) : OpEntC :=
  { q := .lin, abort := false, PA := fun _ _ v ρ => v = Val.loc l ∧ ρ = PMap.empty,
    PB := fun _ _ _ _ => False, fin := none, wc := fun _ _ _ => True, fd := fun _ _ => True,
    PBv := fun v _ _ w σ => ∃ m, v = Val.loc m ∧ w = Val.unit ∧
      ∃ (u : Val) (χ : WRes) (hχ : χ.InStratum A) (hu : P u ⟨χ, hχ⟩),
        σ = ResU.single m (CellU.mutOf A u χ hχ P hu),
    oc := fun _ => True }

/-- **The `mut` lend scope** (`[TR]` 6.65 across stops, ended after a join). `ℓ ↦ own(v) ⋆ ρ_P ⋆
ρ_b`, lent `mut` at `A` with predicate `P̂` to a body in `cerwp` from `ρ_b ● ℓ ↦ mut(A, v, ρ_P,
P̂)`, at a table of must-resume operations with the scope's join: the scope `e; join(ℓ)` is in
`cerwp`. The lender gets the cell back with whatever the borrow last held, in `P̂`. -/
theorem cerwp_scopeM (l : Loc) (v : Val) (A : Life) (P : Val → SPropS Loc Val A) {ρP : WRes}
    (houtP : ρP.InStratum A) (hwit : P v ⟨ρP, houtP⟩) (nJ iJ : UInt32) {Tout : OpTabC}
    (hToutD : Tout.Down) (hlin : ∀ m i en, Tout m i = some en → en.q = .lin)
    (hJ : Tout nJ iJ = some (joinEntM l A P))
    {Q₀ Qout : PostCV} (hQout : Qout.Down)
    (hQ₀u : ∀ k ls O (w : Val) ρ, Q₀ k ls O w ρ → w = Val.unit)
    (hpost : ∀ k k₀ ls₀ ls' O (w₀ : Val) ρ₀ (u : Val) (χ : WRes) (hχ : χ.InStratum A),
      P u ⟨χ, hχ⟩ → ∀ W'' ρout, k ≤ k₀ → Q₀ k₀ ls₀ O w₀ ρ₀ →
      ResU.CompS χ (ResU.single l (CellU.ownOf u)) W'' → ResU.CompS ρ₀ W'' ρout →
      Qout k ls' O Val.unit ρout)
    (n : Nat) (F : WRes → Prop) (ls : List SRec) (O : List FrameRec) (e : Expr)
    {ρlP ρb ρ : WRes} (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    (hcρ : ResU.CompS ρlP ρb ρ) (hvρ : ResU.Valid ρ)
    (h : ∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
      cerwp (ℍ := ℍ) (opTableC Tout) Q₀ F n ls O e BM) :
    cerwp (ℍ := ℍ) (opTableC Tout) Qout F n ls O ((seqK nJ iJ l).plug e) ρ := by
  have hL := opTableC_local Tout
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP := ResU.CompS.comm hclP
  have hH12 : ResU.Hash ρb ρlP := ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  obtain ⟨BM, hBM⟩ := (ResU.compS_defined_iff ρb _).mpr ((ResU.six24 (P := P) (hw := hwit)
    (b := A) hlPcell).mpr hH12).1
  rw [cerwp_eq]
  refine crwpG_update (ρ₁ := BM) (O₁ := O) (ls₁ := ls)
    (fun ρf fρ ps psF μ _ hf hc hS hT htg hlow => ?_) ?_
  · obtain ⟨BM', fρ', hBM', hfB, hcB, hT', htg', hlow'⟩ :=
      capture_worldM houtP hwit hclP hcρ hf hc hT htg hlow
    have e : BM' = BM := ResU.CompS.functional hBM' hBM
    subst e
    exact ⟨fρ', ps, hfB, hcB, hS, hT', htg', hlow'⟩
  rw [← cerwp_eq]
  refine cerwp_bindK (seqK nJ iJ l) (fun m => by simp [seqK, Kont.HasHnd]) hlin
    (fun F' k ls' O' w₀ ρ₀ hq => ?_) n F ls O e BM (h BM hBM)
  obtain rfl := hQ₀u _ _ _ _ _ hq
  refine cerwp_det (opTableC_down hToutD) hQout
    (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine cerwp_perform (T := Tout) (F := F') .hole (m := nJ) (i := iJ) (v := Val.loc l)
    (en := joinEntM l A P) (by simp [Kont.HasHnd]) hJ rfl trivial (compS_empty_left ρ₀)
    ⟨rfl, rfl⟩ (fun h => by simp [joinEntM] at h)
    (fun ls_r _ k' hk' w σB X hB hX => ?_) (fun _ _ hq => absurd rfl hq)
  obtain ⟨m', hm', rfl, u, χ, hχ, hu, rfl⟩ := hB
  obtain rfl : l = m' := by
    have := congrArg Subtype.val hm'
    simpa [Val.loc, Expr.val, Val.prim] using this
  -- the join's resume: the borrow is back; the lend ends
  rw [cerwp_eq]
  intro ρf fρ ps psF μ _ hf hcf hS hT htg hlow _ j μ' e' hj hrun _
  cases hrun with
  | more hs _ => exact absurd hs BoLo.no_step_val
  | refl =>
  have hvW : ResU.Valid fρ := by obtain ⟨σ, hσ, -⟩ := hlow; exact ⟨σ, hσ⟩
  have hvX : ResU.Valid X := (ResU.Valid.split hcf hvW).2
  obtain ⟨W'', hW''⟩ := ResU.compS_own_of_valid_mut (ResU.Valid.split hX hvX).2
  obtain ⟨ρout, W', hρout, hfo, hcW', hT', htg', hlow'⟩ :=
    uncapture_worldM hX hcf hT htg hlow hW''
  exact ⟨ρout, W', ps, O', ls_r, ResU.hash_symm hfo, hcW', hlow', hS, hT', htg',
    Or.inl ⟨Val.unit, rfl, hpost _ k ls' ls_r O' Val.unit ρ₀ u χ hχ hu W'' ρout (by omega) hq
      hW'' hρout⟩⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
