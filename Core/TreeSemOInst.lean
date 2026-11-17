import Core.TreeSemO
import Core.TreePoolSpawnProgs

/-!
# E3's first configuration: an `imm` island owned by a continuation

Research branch `rq1-tree`; no SPEC entry states this file yet.

The loan task `L` (`Core/TreePoolSpawnProgs.lean`) opens a lend of its cell `ℓ` at `α` in its own
branch and parks holding the lend cell (a view of `ℓ`) with the lend's record open. Its
continuation `κ` (the `ubind (λ_. free ℓ, λ_. free ℓ)` context) owns the island
`O = [lendRec ℓ]`.

* **E3.1** (`loan_kontO`): `κ` is a value of `STy.kontO 1 (F 1)` owning `[lendRec ℓ]`, holding
  `viewRes α ℓ`: the park's share (`loan_share`) through `STy.kontO_of_share`.
* **E3.2** (`loan_carried_resumed`): carried to any extension `w′` of the stop's world, at any
  list keeping the records the view reads (a sibling may meanwhile have opened and ended a lend at
  `β` of its own: the extension and `KeepRel` are what `cactusT_step` gives the stored branch),
  `κ` is still of its type owning `[lendRec ℓ]` (the record re-reads to itself), and resuming it
  at `()` is a run owning the island.
* **E3.3** (`loan_resume_exit`): the resumed run reads through `ubind`'s normal branch, ends `α`
  by `STy.kontO_exit` (the record leaves the run's records, the cell returns to `ℓ ↦ own(())`),
  frees `ℓ` and answers `()` owning nothing.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack
open BoCa.Fig16.Tree.Wp.SchedProgs.Spawn
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload freeE)

open Classical in
/-- **E3.3 on the loan task**: the continuation resumed at `()`, owning `[lendRec ℓ]` and holding
the lend cell, at the resumer's guarantee: two steps of `ubind`'s normal branch, the lend ended by
`STy.kontO_exit`, `ℓ` freed, `()` owning nothing. -/
theorem loan_resume_exit {T : OpTabT}
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    {Fb : TFrame} {k : Nat} {w : TWd} {ls : List (SRecT w.K)} {l : BoCa.Loc} {α : Life} :
    cerwpT (ℍ := ℍ) (opTableT T) QS Fb (fdAt enPark Val.unit Fb [lendRec (K := w.K) l]) k w ls
      [lendRec l] ((ubK (Nf l) (Nf l)).plug (.val Val.unit)) (viewRes α l) := by
  have hD := post_down hTd (Ψ := cerwpTC (ℍ := ℍ) (opTableT T) QS Fb k)
    (Ψc := cerwpTK (ℍ := ℍ) k) (F := Fb)
  rw [cerwpT_eq]
  refine twp_det hD (fun μ => step1Only_plug (Head.uthen μ (Nf l) (Nf l) Val.unit) rfl .hole) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  rw [← cerwpT_eq]
  refine STy.kontO_exit (Ls := [l]) (O₁ := []) (Z := PMap.empty)
    (ls₁ := ls.filter fun x => x.1 ≠ lendRec l) (α := α) rfl (List.mem_singleton.mpr rfl)
    (ResUT.CompS.comm (ResUT.compS_empty_right _)) (ResUT.CompS.comm (ResUT.compS_empty_right _))
    ⟨_, flat_empty⟩ (noneAt_empty _) (fun x => by simp) (by simp)
    (fun x hx => by
      by_cases h : x.1 = lendRec l
      · exact Or.inl h
      · exact Or.inr (List.mem_filter.mpr ⟨hx, by simpa using h⟩))
    (fun x hx => (List.mem_filter.mp hx).1)
    (fun x hx => by simpa using (List.mem_filter.mp hx).2) ?_
  rw [cerwpT_eq]
  exact twp_free hD .hole l Val.unit (ResUT.compS_empty_right _) twp_unitEnd

/-- **The park's share, owning the island**: the loan task's continuation at a park, holding the
lend cell and owning `[lendRec ℓ]`, resumes (E3.3) and cancels (`twp_cancelTail`). -/
theorem loan_share {T : OpTabT}
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    {Fb : TFrame} {k : Nat} {w : TWd} {ls : List (SRecT w.K)} {l : BoCa.Loc} {α : Life} :
    contShareT T enPark Fb k w ls [lendRec l] (ubK (Nf l) (Nf l)) Val.unit
      (cerwpTC (ℍ := ℍ) (opTableT T) QS Fb k) (cerwpTK (ℍ := ℍ) k) (viewRes α l) := by
  have hO₀ : ∀ {K K' : WCactus} {Θ : CodeTy} {O'' : List (FrameRecT K')},
      RecsRR Θ [lendRec (K := K) l] O'' → O'' = [lendRec l] := by
    intro K K' Θ O'' h
    cases h with
    | cons h₁ t => cases t; rw [RecRR.func h₁ (lendRec_rr l)]
  unfold contShareT
  refine ⟨fun h => by simp [enPark] at h, fun w' ρ' ls' O' _ hr' _ hO' => ?_⟩
  obtain rfl := hO₀ hO'
  obtain rfl := rr_view_eq hr'
  refine ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun _ _ k' hk' => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := compS_empty_right_eq hcσ
    simp only [cerwpTC, hk', if_true]
    exact loan_resume_exit hTd
  · simp only [cerwpTK, hk', if_true]
    refine cerwpT_QV ?_
    rw [cerwpT_eq]
    exact twp_cancelTail (post_down (PADown.restrict hTd _)) fdAt_lend (Nf l) twp_unitEnd

/-- The run type of the loan task's continuation: `F 1` at `T`, answering `QS`, at the resumer's
guarantee read at the run's records. -/
abbrev loanC {T : OpTabT}
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    (Fb : TFrame) : SCmpO :=
  SCmpO.ret (ℍ := ℍ) (opTableT T) (opTableT_local T) (opTableT_down hTd) QS QB_down Fb
    (fun w' O' => fdAt enPark Val.unit Fb (w' := w') O')

/-- **E3.1 on the loan task**: a `κ` whose application is the park's context is a value of
`U (1 ⊸ F 1)` owning the island `[lendRec ℓ]`, over the lend cell. -/
theorem loan_kontO {T : OpTabT}
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    {Fb : TFrame} {k : Nat} {w : TWd} {ls : List (SRecT w.K)} {l : BoCa.Loc} {α : Life}
    {κ : Val}
    (hκ : ∀ (a : Val) μ, Step1Only (ℍ := ℍ) μ (.app (.val κ) (.val a)) μ
      ((ubK (Nf l) (Nf l)).plug (.val a)))
    {n : Nat} (hn : n < k) :
    (STy.kontO STy.unit (loanC (ℍ := ℍ) hTd Fb)).PO n w ls [lendRec l] κ (viewRes α l) :=
  STy.kontO_of_share (opTableT_local T) (opTableT_down hTd) QB_down hκ
    (fun _ _ _ _ _ h => h) (loan_share hTd) hn

/-- **E3.2 on the loan task**: carried to any extension `w′` (another branch, say a sibling with
its own lend at `β`, having opened and ended it), at any list keeping the records the view reads,
`κ` is still of its type owning `[lendRec ℓ]`, and resuming it at `()` is a run owning the island
there. -/
theorem loan_carried_resumed {T : OpTabT}
    (hTd : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ)
    {Fb : TFrame} {k : Nat} {w w' : TWd} {ls : List (SRecT w.K)} {ls' : List (SRecT w'.K)}
    {l : BoCa.Loc} {α : Life} {κ : Val}
    (hκ : ∀ (a : Val) μ, Step1Only (ℍ := ℍ) μ (.app (.val κ) (.val a)) μ
      ((ubK (Nf l) (Nf l)).plug (.val a)))
    (hE : w.Ext w' (viewRes α l)) (hk : KeepRel w'.Θ ls ls' (viewRes α l))
    (hls : ∀ x ∈ ls', CovR (sem w'.Θ) w'.K x.1.R) {n : Nat} (hn : n < k) :
    (STy.kontO STy.unit (loanC (ℍ := ℍ) hTd Fb)).PO n w' ls' [lendRec l] κ (viewRes α l) ∧
      cerwpT (ℍ := ℍ) (opTableT T) QS Fb (fdAt enPark Val.unit Fb [lendRec (K := w'.K) l]) n w'
        ls' [lendRec l] (.app (.val κ) (.val Val.unit)) (viewRes α l) := by
  have h₁ := loan_kontO (ℍ := ℍ) hTd (Fb := Fb) (w := w) (ls := ls) (α := α) hκ hn
  have h₂ := STy.kontO_mono (O' := [lendRec (K := w'.K) l]) hE rr_view hk (lendRecs_rr [l])
    (view_cov w.Θ α l) h₁
  exact ⟨h₂, STy.kontO_resume h₂ (TWd.Ext.refl w' _) rr_view (KeepRel.refl hls _)
    (lendRecs_rr [l]) le_rfl (ResUT.compS_empty_right _) ⟨rfl, rfl⟩⟩

end BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs

end
