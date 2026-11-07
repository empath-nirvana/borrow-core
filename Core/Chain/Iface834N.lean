import Core.Chain.ImmLend833N
import Core.Integers

/-!
# The lemma interface for `FundamentalN`: the context and bind layer  `[spec §62]`

`docs/new-core/scope-831-interface.md` §2, unit L1. The relation-level lemmas Core's
compatibility proofs (`Core/Compat.lean`, `Core/Compatibility.lean`, `Core/Computation.lean`)
reach for, at the chain (`vN`/`cN`/`gN`/`erwp`), under Core's names with `N` for `C`. The entries
that read the relation are in `RulesKW835N.lean` and `Goal791N.lean`; this file holds K5, W4, W7
and the first-order types F4 reads:

* **G1/G12** `gN_split`, `gN_splitC`: Core's `gDenC_split`, the parts consistent with the view at
  a valid resource; `cN_of_valid`: a computation may assume its resource valid, at every type, so
  a split's consistency holds at a conclusion that is not `F`/`F_Σ`.
* **G2** `gN_soloP`, **G4** `gN_persistent`, **G6** `gN_extR`, **G7** `gN_outlives`, **G8**
  `gN_congr`, **G9** `gN_noOwn`, **G11** `gN_le`.
* **K5** `LocTy.extR_empty`: every two worlds are related at `∅` (Core's `ext_empty'`).
* **W4** `erwp_bind_frame`: Core's `wpTS_bind_frame`, the frame carried through the run and read
  at the index the run leaves, the view kept consistent.
* **C2** `cN_bind`: Core's `cC_bind`, by induction on `C`.
* **W7** `erwp_box`: Core's `wpTS_box`.
* **V8** `vN_noOwn_of_ownFree`; **F2** `bang_app`; **F4** `host_call_sound` at `vN`, over the
  first-order value types (`VTy.isFO`, `hostArg_isFO`, `hostRes_isFO`).

Core's `⊸` is a plain wand (`cC .arr`), and so is the chain's (`cN .arr`): the argument is read at
the function's own world, at every later index and every view consistent with the composite. The
index is the chain's step index (Core has none); the view is the chain's `ConsistentX` (Core has
none).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head)

/-! ### K5: the order at the empty resource -/

/-- **Every two worlds are related at `∅`** (Core's `ext_empty'`): `∅` holds no borrow cell, so
neither conjunct of `ExtR` reads anything. -/
theorem _root_.BoCa.Fig16.LogRel.Core.Chain.SI.LocTy.extR_empty (Θ Θ' : LocTy) :
    Θ.ExtR Θ' PMap.empty :=
  ⟨fun _ _ _ _ hc => absurd hc (fun ⟨m, ψ, e, _⟩ => by simp at e),
    fun _ _ hc => absurd hc (fun ⟨m, ψ, e, _⟩ => by simp at e)⟩

/-! ### W4: bind with a frame -/

/-- **Bind on the sub-expression, frame the rest through the run, then continue** (Core's
`wpTS_bind_frame`, 6.135 with 6.146). The sub-expression runs at the empty table, so its run never
stops (`rwp_of_erwp_empty`) and binds into any table (`erwp_bindR`); the frame goes through it
(`rwp_frame`); the returned resource stays consistent with the view and is valid
(`rwp_consistentXV`). The continuation is read at the index the run leaves, `k ≤ n`. -/
theorem erwp_bind_frame {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) (K : Kont)
    {e : Expr} {P Q : PostN} (R : WProp) {n : Nat} {ls : List SRec} {ρ₁ ρ₂ ρ : WRes}
    {c : Loc → Option Life} (hcρ : ResU.CompS ρ₁ ρ₂ ρ) (hc : ConsistentX c ρ)
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) P n ls e ρ₁) (hR : R ρ₂)
    (h : ∀ k, k ≤ n → ∀ ls' (v : Val) (σ₁ σ₂ σ : WRes), ResU.CompS σ₁ σ₂ σ → P k ls' v σ₁ →
      R σ₂ → ConsistentX c σ → ResU.Valid σ → erwp (ℍ := ℍ) Φ Tb Q k ls' (K.plug v.1) σ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls (K.plug e) ρ := by
  refine erwp_bindR hΦ hL K ?_
  refine rwp_mono_le (fun k hk ls' v σ hv => ?_)
    (rwp_consistentXV (rwp_frame (fun _ => R) (fun _ _ _ _ h => h) hcρ (rwp_of_erwp_empty hw) hR)
      hc)
  obtain ⟨⟨σ₁, σ₂, hcσ, hP, hRσ⟩, hcσ', hvσ⟩ := hv
  exact h k hk ls' v σ₁ σ₂ σ hcσ hP hRσ hcσ' hvσ

/-! ### W7: a run from `Res_α` ends in `Res_α` -/

/-- **`[TR]` 6.147 (`wp-box`) at `rwp`** (Core's `wpTS_box`): `↭` keeps the strata
(`updVN_inStratum`), and the returned resource is a part of its right side. -/
theorem rwp_box {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    {α : Life} (h : rwp (ℍ := ℍ) Φ Q n ls e ρ) (hρ : ρ.InStratum α) :
    rwp (ℍ := ℍ) Φ (fun k ls v ρ' => Q k ls v ρ' ∧ ρ'.InStratum α) n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun
  obtain ⟨hval, hprog⟩ := h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun
  refine ⟨fun v hv => ?_, hprog⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := hval v hv
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃, ResU.CompS.inStratum_left h₆ (updVN_inStratum hρ h₇)⟩

/-- **`wp-box` at `erwp` at the empty table**: a run that never stops is an `rwp` run. -/
theorem erwp_box {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    {α : Life} (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls e ρ) (hρ : ρ.InStratum α) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (fun k ls v ρ' => Q k ls v ρ' ∧ ρ'.InStratum α)
      n ls e ρ :=
  erwp_of_rwp (rwp_box (rwp_of_erwp_empty h) hρ)

/-! ### F4: the first-order value types -/

/-- **The first-order value types**: `1`, `0`, the integer widths, `⊗`, `⊕`. The host operations'
signatures (`hostArg`, `hostRes`) are among them. -/
def _root_.BoCa.Fig16.LogRel.Core.VTy.isFO : VTy → Bool
  | .unit | .zero | .int _ => true
  | .tensor A B | .sum A B => A.isFO && B.isFO
  | _ => false

theorem isFO_intOnly {w : Width} {A : VTy} (h : A.isFO = true) : (intOnly w A).isFO = true := by
  cases w <;> first | exact h | rfl

theorem hostArg_isFO (op : HostOp) : (hostArg op).isFO = true := by
  cases op <;> simp only [hostArg] <;> first | rfl | exact isFO_intOnly rfl

theorem hostRes_isFO (op : HostOp) : (hostRes op).isFO = true := by
  cases op <;> rfl

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
