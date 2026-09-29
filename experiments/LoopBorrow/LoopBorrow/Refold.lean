import LoopBorrow.Obstruction

/-!
# LoopBorrow — a saved lend re-pushed for one observation

The Mut Frame (6.65, `wpTS_M_frameX`) folds the lender `ℓ ↦ own(v) ⋆ P̂(v)` into a fresh
`ℓ ↦ mut(α, v, ρ_P̂, P̂)`, runs the callee, finds the cell again (6.27) and unfolds it, all in one
run. A lend held by codata across observations would have to be saved between them and pushed
again at each resume, at whatever depth the consumer has reached by then.

`wpTS_M_refold` is that resume, as a theorem of the typed world. The saved state is the lend
unfolded, `ρr ● ℓ ↦ own(w) ● χ`, with its lifetime `α`, predicate `P̂` and the rest `ρr` at
least `α` (`Res_{↓α}`). The run pushes the same cell `ℓ ↦ mut(α, w, χ, P̂)` back at the current
world (`TW.mutFold`, at any record list), runs the observation at `ρr ● ℓ ↦ mut(…)`, finds the
cell at the top level of what the observation leaves (`six27_down`, 6.27 with `Res_{↓α}`), and
unfolds it again (`TW.mutUnfold`); `↭` holds between the two unfolded states (6.28). What the
observation returned and dropped is kept, together with the cell (`Refolded`).

So the frame itself survives being re-pushed at a new depth: nothing in `TW`, `Tagged`, the
memory or `↭` depends on where the consumer's frames sit. What does not survive is the Kripke
order of the unfolded state, which cannot see `α` (`Obstruction.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.LoopBorrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `[TR]` 6.27 with the rest in `Res_{↓α}` rather than `Res_α`: the rest may hold cells at `α`
itself. The printed proof uses the hypothesis only to put `ρ ● ℓ ↦ mut(α, …)` in `Res_{↓α}`,
which this hypothesis gives directly. -/
theorem six27_down {l : BoCa.Loc} {α : Life} {v : BoCa.Val}
    {ρ ρv M ρ' : ResU BoCa.Loc BoCa.Val}
    {h : ResU.InStratum α ρv} {P : BoCa.Val → SPropS BoCa.Loc BoCa.Val α}
    {hw : P v ⟨ρv, h⟩}
    (hout : ResU.InStratum (↓α) ρ)
    (hM : ResU.CompS ρ (ResU.single l (CellU.mutOf α v ρv h P hw)) M)
    (hu : ResU.UpdV M ρ') :
    ∃ (v' : BoCa.Val) (χ : ResU BoCa.Loc BoCa.Val) (h' : ResU.InStratum α χ)
      (hw' : P v' ⟨χ, h'⟩),
      ResU.CompS (ρ'.del l) (ResU.single l (CellU.mutOf α v' χ h' P hw')) ρ' := by
  classical
  have hkm : (CellU.mutOf α v ρv h P hw).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hMl : M.get l = some (CellU.mutOf α v ρv h P hw) :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hM)
      (ResU.single_get_self _ _) hkm).2
  have hσl : σ.get l = some (CellU.mutOf α v ρv h P hw) :=
    ResU.flat_get_of_ne_imm hσ hMl hkm
  obtain ⟨v', χ, h', hw', hflat⟩ := (hu.1.2 l α P).mp ⟨v, ρv, h, hw, ⟨σ, hσ, hσl⟩⟩
  rw [ResU.flatAt_iff hσ'] at hflat
  have hdM : M.InStratum (↓α) :=
    BoLo.inStratum_comp (BoLo.compS_hC (↓α)) hM hout
      (ResU.inStratum_single l ((CellU.inStratum_mutOf (↓α) α v ρv h P hw).mpr
        (Life.down_sqsubset α)))
  have hd' : ρ'.InStratum (↓α) := ResU.updV_inStratum hdM hu
  have hρ'l : ρ'.get l ≠ none := by
    intro hnone
    have hcon := ResU.flat_inStratum_at hσ' hd'
      (fun φ e => absurd (hnone ▸ e) (by simp)) hflat
    rw [CellU.inStratum_mutOf] at hcon
    exact absurd hcon (lt_irrefl _)
  obtain ⟨φ, hφ⟩ : ∃ φ, ρ'.get l = some φ := by
    cases hg : ρ'.get l with
    | none => exact absurd hg hρ'l
    | some φ => exact ⟨φ, rfl⟩
  obtain ⟨χ₀, hχ₀, hk₀, -, -⟩ := ResU.Flat.get hσ' hφ
  rw [hflat] at hχ₀
  obtain rfl : χ₀ = CellU.mutOf α v' χ h' P hw' := (Option.some.inj hχ₀).symm
  have hkφ : φ.kind ≠ Kind.imm := by
    rw [← hk₀, CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hgg : σ'.get l = some φ := ResU.flat_get_of_ne_imm hσ' hφ hkφ
  rw [hflat] at hgg
  obtain rfl : φ = CellU.mutOf α v' χ h' P hw' := (Option.some.inj hgg).symm
  exact ⟨v', χ, h', hw', ResU.del_compS hφ⟩

/-- What an observation leaves, with the lend unfolded again: the state is
`R ● ℓ ↦ own(w′) ● χ′` with `R ∈ Res_{↓α}`, and `R ● ℓ ↦ mut(α, w′, χ′, P̂)` is the
observation's result resource `π₁` (where `P` holds) with its dropped part `π₂`. -/
def Refolded (l : BoCa.Loc) (A : Life) (Qs : BoCa.Val → SPropS BoCa.Loc BoCa.Val A)
    (P : WProp) : WProp := fun ρ' =>
  ∃ (R W' π π₁ π₂ : WRes) (w' : BoCa.Val) (χ' : WRes) (hχ' : χ'.InStratum A)
    (hw' : Qs w' ⟨χ', hχ'⟩),
    R.InStratum (↓A) ∧ ResU.CompS χ' (ResU.single l (CellU.ownOf w')) W' ∧
    ResU.CompS R W' ρ' ∧
    ResU.CompS R (ResU.single l (CellU.mutOf A w' χ' hχ' Qs hw')) π ∧
    ResU.CompS π₁ π₂ π ∧ P π₁

/-- **A saved lend re-pushed for one observation.** From the unfolded state
`ρ = ρr ● (χ ● ℓ ↦ own(w))`, a run of `e` whose `wp` holds at the folded state
`ρr ● ℓ ↦ mut(α, w, χ, P̂)` is a run of `e` from `ρ`, which leaves the lend unfolded again
(`Refolded`). `α` is the lend's lifetime, fixed when it was made; the record list is any. -/
theorem wpTS_M_refold (l : BoCa.Loc) (A : Life) (w : BoCa.Val) (χ : WRes) (hχ : χ.InStratum A)
    (Qs : BoCa.Val → SPropS BoCa.Loc BoCa.Val A) (hw : Qs w ⟨χ, hχ⟩)
    (e : Expr) (ls : List SRec) (Q : List SRec → BoCa.Val → WProp) {ρr W ρ M : WRes}
    (hr : ρr.InStratum (↓A))
    (hW : ResU.CompS χ (ResU.single l (CellU.ownOf w)) W) (hO : ResU.CompS ρr W ρ)
    (hM : ResU.CompS ρr (ResU.single l (CellU.mutOf A w χ hχ Qs hw)) M)
    (hwp : wpTS ls e Q M) :
    wpTS ls e (fun ls' v => Refolded l A Qs (Q ls' v)) ρ := by
  classical
  intro ρf sρ ps hH3 hsρ hT htg alc kc
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  set ρm : WRes := ResU.single l (CellU.mutOf A w χ hχ Qs hw) with hρm
  -- the compatibility block, as 6.65's H12–H17 with `ρb = ρr`
  have hrW : ResU.Hash ρr W := ⟨hO.1, ρ, hO, hvρ⟩
  have hrm : ResU.Hash ρr ρm := (ResU.six24 hW).mpr hrW
  obtain ⟨hrf, hWf⟩ := ResU.Hash.split hO (ResU.hash_symm hH3)
  have hfm : ResU.Hash ρf ρm := (ResU.six24 hW).mpr (ResU.hash_symm hWf)
  have hfM : ResU.Hash ρf M := ResU.hash_of_pairwise (ResU.hash_symm hrf) hrm hfm hM
  obtain ⟨fρ, h4, hvfρ⟩ := hfM.2
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρr).mpr (ResU.hash_symm hrf).1
  obtain ⟨FB₁, hFB₁, hFBm⟩ := (ResU.CompS.assoc ρf ρr ρm fρ).mp ⟨M, hM, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBW⟩ := (ResU.CompS.assoc ρf ρr W sρ).mp ⟨ρ, hO, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  -- entry: `TW.mutFold` of the saved cell, at the current world and list
  have hTin : TW fρ ps (rsOf ls) :=
    TW.mutFold hT (ResU.CompS.comm hW) (ResU.CompS.comm hFBW) (ResU.CompS.comm hFBm) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW) (ResU.CompS.comm hFBW) (ResU.CompS.comm hFBm) a).mpr ha)
    htg
  -- the observation, at the folded state
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v', μ, μ', ps'', ls'',
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, hT'', htg'', hps'', hls'', h12⟩ :=
    hwp ρf fρ ps hfM h4 hTin htgin alc kc
  -- 6.27: the cell is at the top level of `ρ′ ● ρ⁺`
  obtain ⟨v'', χ', hχ', hw'', hsplit⟩ := six27_down hr hM h10
  set R : WRes := π.del l with hRdef
  set ρm'' : WRes := ResU.single l (CellU.mutOf A v'' χ' hχ' Qs hw'') with hρm''
  have hvπ : ResU.Valid π := h10.2.2
  have hvm'' : ResU.Valid ρm'' := (ResU.Valid.split hsplit hvπ).2
  have hvR : ResU.Valid R := (ResU.Valid.split hsplit hvπ).1
  obtain ⟨W'', hW''⟩ := ResU.compS_own_of_valid_mut hvm''
  have hvW'' : ResU.Valid W'' := by
    have hRm : ResU.Hash R ρm'' := ⟨hsplit.1, π, hsplit, hvπ⟩
    obtain ⟨-, s, hs, hv⟩ := (ResU.six24 hW'').mp hRm
    exact (ResU.Valid.split hs hv).2
  have hRW : ResU.Hash R W'' := (ResU.six24 hW'').mp ⟨hsplit.1, π, hsplit, hvπ⟩
  obtain ⟨RW, hRWc⟩ := (ResU.compS_defined_iff R W'').mpr hRW.1
  have hvRW : ResU.Valid RW := by obtain ⟨-, s, hs, hv⟩ := hRW; exact ResU.CompS.functional hs hRWc ▸ hv
  -- the world after the observation is `ρf ● π`
  obtain ⟨FP, hFP, hfFP⟩ := (ResU.CompS.assoc ρf ρ' ρp fρ'p).mpr ⟨fρ', h2, h6⟩
  obtain rfl : π = FP := ResU.CompS.functional h9 hFP
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hfπ : ResU.Hash ρf π := ⟨hfFP.1, fρ'p, hfFP, hvfρ'p⟩
  obtain ⟨hfR, hfm''⟩ := ResU.Hash.split hsplit (ResU.hash_symm hfπ)
  have hfW'' : ResU.Hash ρf W'' := (ResU.six24 hW'').mp (ResU.hash_symm hfm'')
  have hfRW : ResU.Hash ρf RW := ResU.hash_of_pairwise (ResU.hash_symm hfR) hRW hfW'' hRWc
  obtain ⟨F, hF⟩ := (ResU.compS_defined_iff ρf RW).mpr hfRW.1
  have hvF : ResU.Valid F := by obtain ⟨-, s, hs, hv⟩ := hfRW; exact ResU.CompS.functional hs hF ▸ hv
  obtain ⟨FR, hFR⟩ := (ResU.compS_defined_iff ρf R).mpr (ResU.hash_symm hfR).1
  obtain ⟨FR₁, hFR₁, hFRm⟩ := (ResU.CompS.assoc ρf R ρm'' fρ'p).mp ⟨π, hsplit, hfFP⟩
  obtain rfl : FR = FR₁ := ResU.CompS.functional hFR hFR₁
  obtain ⟨FR₂, hFR₂, hFRW⟩ := (ResU.CompS.assoc ρf R W'' F).mp ⟨RW, hRWc, hF⟩
  obtain rfl : FR = FR₂ := ResU.CompS.functional hFR hFR₂
  -- the two memories, by 6.25 under a frame (6.8)
  have hvm : ResU.Valid ρm := (ResU.Valid.split hM (hash_valid hfM).2).2
  have hvW : ResU.Valid W := (ResU.Valid.split hO hvρ).2
  have hFBmH : ResU.Hash FB ρm := ⟨hFBm.1, fρ, hFBm, hvfρ⟩
  have hFBWH : ResU.Hash FB W := ⟨hFBW.1, sρ, hFBW, hvsρ⟩
  have hmem₁ : ResU.Lower sρ μ :=
    (ResU.lower_swap_mut_own hW hvm hvW hFBm hFBmH hFBW hFBWH).mp h5
  have hFRmH : ResU.Hash FR ρm'' := ⟨hFRm.1, fρ'p, hFRm, hvfρ'p⟩
  have hFRWH : ResU.Hash FR W'' := ⟨hFRW.1, F, hFRW, hvF⟩
  have hmem₂ : ResU.Lower F μ' :=
    (ResU.lower_swap_mut_own hW'' hvm'' hvW'' hFRm hFRmH hFRW hFRWH).mp h7
  -- 6.28: `ρ ↭ R ● χ′ ● ℓ ↦ own(v″)`
  have hupd : ResU.Upd ρ RW :=
    (ResU.six28 hW hW'' hM hsplit hO hRWc (hash_valid hfM).2 hvπ hvρ hvRW).mp h10.1
  -- exit: `TW.mutUnfold`
  have hTout : TW F ps'' (rsOf ls'') :=
    TW.mutUnfold hT'' (ResU.CompS.comm hFRm) (ResU.CompS.comm hW'') (ResU.CompS.comm hFRW) hvF
  have htgout : Tagged F ps'' ls'' := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW'') (ResU.CompS.comm hFRW) (ResU.CompS.comm hFRm) a).mp
      ha) htg''
  -- `R ∈ Res_{↓α}`, by 6.27's stratification of `ρ′ ● ρ⁺`
  have hdM : M.InStratum (↓A) :=
    BoLo.inStratum_comp (BoLo.compS_hC (↓A)) hM hr
      (ResU.inStratum_single l ((CellU.inStratum_mutOf (↓A) A w χ hχ Qs hw).mpr
        (Life.down_sqsubset A)))
  have hRd : R.InStratum (↓A) :=
    ResU.CompS.inStratum_left hsplit (ResU.updV_inStratum hdM h10)
  refine ⟨RW, PMap.empty, F, F, RW, v', μ, μ', ps'', ls'',
    ResU.hash_symm hfRW, hF, ⟨(ResU.comp_empty_left F : ResU.CompS PMap.empty F F).1, F,
      ResU.comp_empty_left F, hvF⟩, hmem₁, ResU.comp_empty_right F, hmem₂, h8,
    ResU.comp_empty_right RW, ⟨hupd, hvρ, hvRW⟩, noOwn_empty, hTout, htgout, hps'', hls'', ?_⟩
  exact ⟨R, W'', π, ρ', ρp, v'', χ', hχ', hw'', hRd, hW'', hRWc, hsplit, h9, h12⟩

end BoCa.Fig16.LogRel.Core.LoopBorrow

end
