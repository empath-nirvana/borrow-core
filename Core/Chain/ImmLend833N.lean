import Core.Chain.Withload791N
import Core.Chain.ExtRLit791
import Core.Chain.ImmRec791N
import Core.Chain.SI.IStopRaiseN

/-!
# The `imm` lend at `SemJN₀`  `[spec §62]`

Core's `withbor1U_compatX` (`Core/EffBorrow.lean`) and `withbor1_compatX`
(`Core/Compatibility.lean`), step by step, at the per-lend world:

* the context owns nothing (`gN_deadP₀`) and the finaliser's judgment holds at every world and
  lower index (`gN_dead_any₀`, Core's `semV_dead_closed`);
* the lend's record goes into the callback's world (`LocTy.addImm`), an extension at the
  callback's resource in the lend's stratum (`LocTy.extR_addImm`, Core's `ext_add`); the
  callback's `Imm` argument is witnessed there by the record;
* the callback's run, at that world's view, is a run at the lender's view: an unwinding row's
  table never resumes, so the relation reads the tie only at the run's entry, whose list is the
  frame's and holds the record (`erwp_tieEntry`);
* the Imm Frame across the row's raises (`erwp_I_frameR`, Core's `ewpTS_I_frameU`);
* the callback's result `['x] B` returns to the world without the record (`LocTy.extR_of_addImm`,
  Core's `ext_drop`);
* the finaliser frame consumes the lend's claim at a raise (`erwp_ubindRaise`, `fin_claimI₀`).

The same steps give the `mut` lend `withbor (2)` at the pure row and at an unwinding row, at any
`Δ` (`withbor2_compatN₀`, `withbor2U_compatN₀`): the Mut Frame across raises (`erwp_M_frameR`), the
claim consistent with the view (`erwp_claimX_abort`).
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
open BoCa.BoLo (Heap Kont Head ubindE)

/-! ### A dead context -/

/-! ### A run whose table never resumes reads its tie only at its entry -/

/-- **The tie is read only at the entry**: a run at a location typing with more `imm` records,
the same families, from a list holding the extra records, is a run at the one with fewer. -/
theorem rwpG_tieEntry {Φ Φ' : LocFam} (hfam : Φ'.fam = Φ.fam) {ls : List SRec}
    (hI : ∀ x ∈ Φ'.imm, x ∈ Φ.imm ∨ x ∈ ls) {Q : PostG} {n : Nat} {e : Expr} {ρ : WRes}
    (h : rwpG (ℍ := ℍ) Φ' Q n ls e ρ) : rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  obtain ⟨f', I'⟩ := Φ'
  obtain ⟨f, I⟩ := Φ
  simp only at hfam hI
  subst hfam
  intro ρf fρ ps μ hf hc hT htg hIt hl hfd j μ' e' hj hrun hfin
  have hIt' : ImmTieL I' ls := fun x hx => (hI x hx).elim (hIt x) id
  exact h ρf fρ ps μ hf hc hT htg hIt' hl hfd j μ' e' hj hrun hfin

/-- **A run at an abortive table reads its tie only at its entry**: the table never resumes, so
what the run owes at a stop does not mention the location typing. -/
theorem erwp_tieEntry {Φ Φ' : LocFam} (hfam : Φ'.fam = Φ.fam) {T : OpTabN}
    (hab : ∀ m i en, T m i = some en → en.abort = true) {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (hI : ∀ x ∈ Φ'.imm, x ∈ Φ.imm ∨ x ∈ ls)
    (h : erwp (ℍ := ℍ) Φ' (opTableN T) Q n ls e ρ) : erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  rw [erwp_eq] at h ⊢
  refine rwpG_tieEntry hfam hI (rwpG_mono (fun k ls' t σ ht => ?_) h)
  rcases ht with ht | ⟨K, m, i, v, en, hp⟩ | ht
  · exact Or.inl ht
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd (hab m i en hTe) (by rw [ha]; decide)
  · exact Or.inr (Or.inr ht)

/-! ### An unwinding row's table -/

/-- An unwinding row's answer types are empty. -/
theorem unwind_B {S : Row} {x : LifeVar} (hS : S.Unwind x) {o : OpSig} (ho : o ∈ S) :
    o.B = .zero := OpSig.B_zero (hS o ho).1

/-! ### The finaliser at the lend's claim -/

/-! ### `withbor (1)` at an unwinding row -/

/-! ### `withbor (1)` at the pure row -/

/-- The pure row's table may be stopped at under any lend: it has no entry. -/
theorem empty_iLendOKR (α : Life) : OpTabN.empty.ILendOKR α where
  entry := fun _ _ _ h => by simp [OpTabN.empty] at h
  pa := fun _ _ _ h => by simp [OpTabN.empty] at h
  pb := fun _ _ _ h => by simp [OpTabN.empty] at h
  paExt := fun _ _ _ h => by simp [OpTabN.empty] at h
  pbExt := fun _ _ _ h => by simp [OpTabN.empty] at h

/-- `withbor`'s inner abstraction at the source `ℓ`: `λf. (ℓ, f () ℓ)`. -/
def withborAt (l : Loc) : Val :=
  Val.lam (.pair (.val (Val.loc l)) (.app (.app BoCa.v0 unit') (.val (Val.loc l))))

/-- `withbor` as a value. -/
def withborVal : Val := Val.lam (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))).1

theorem withborVal_eq : withborVal.1 = withbor := rfl

/-! ### `withbor (2)` at an unwinding row -/

/-- **A body at an abortive table carries the view's consistency to its claim** (`erwp_claimX`'s
`raise` case): a run from a resource consistent with `c` returns consistent resources, and the
claim a `raise` carries is part of one. -/
theorem erwp_claimX_abort {Θ : LocTy} {c : Loc → Option Life} {T : OpTabN}
    (hab : ∀ m i en, T m i = some en → en.abort = true) {R : Nat → WProp} {Q : PostN} {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes} (hc : ConsistentX c ρ)
    (h : erwp (ℍ := ℍ) (Θ.view c) (opTableR T R) Q n ls e ρ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableR T (claimX R c)) Q n ls e ρ := by
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (rwpG_consistentXV h hc)
  obtain ⟨ht, hcσ, hvσ⟩ := ht
  rcases ht with hv | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact Or.inl hv
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [hab m i en hTe]; decide)
  · obtain ⟨hpt, σ₁, ρR, hcσR, hpa, hR⟩ := pure_sep_iff.mp hp
    exact Or.inr (Or.inr ⟨K₁, m, i, v, en, pure_sep_mk hpt
      ⟨σ₁, ρR, hcσR, hpa, hR, consistentX_right hcσR hcσ hvσ⟩⟩)

/-! ### `withbor (2)` at the pure row -/

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
