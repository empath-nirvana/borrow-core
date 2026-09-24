import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Model.Composition
import Support.Model.Prelude

/-!
# Support — Model — Singletons

`[about ours]`.  Restriction `ρ∣ι`, singleton resources `ℓ ↦ ψ`, the order `ρ ≤ ρ′`, and the walks and restrictions of singletons.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem ResU.restrictOn_eq_some {ρ : ResU Loc Val} {p : Kind → Bool} {l : Loc}
    {ψ : CellU Loc Val} :
    (ρ.restrictOn p).get l = some ψ ↔ (ρ.get l = some ψ ∧ p ψ.kind = true) := by
  have hdef : (ρ.restrictOn p).get l
      = (ρ.get l).bind (fun ψ => if p ψ.kind then some ψ else none) := rfl
  rw [hdef]
  cases hf : ρ.get l with
  | none => simp
  | some ψ' =>
      simp only [Option.bind_some]
      by_cases hk : p ψ'.kind = true
      · rw [if_pos hk]
        exact ⟨fun he => by cases Option.some.inj he; exact ⟨rfl, hk⟩, fun he => he.1⟩
      · rw [if_neg hk]
        refine ⟨fun he => absurd he (by simp), fun he => ?_⟩
        cases Option.some.inj he.1
        exact absurd he.2 hk

open Classical in
theorem ResU.single_get_ne {l l' : Loc} (ψ : CellU Loc Val) (h : l' ≠ l) :
    (ResU.single l ψ).get l' = none := if_neg h

/-- `∅ ∈ Res_α` at every `α`. -/
theorem ResU.inStratum_empty (α : Life) :
    ResU.InStratum α (PMap.empty : ResU Loc Val) :=
  fun l _ e => absurd (e.symm.trans (PMap.empty_get l)) (by simp)

/-- `ℓ ↦ ψ ∈ Res_α` exactly when its one cell is. -/
theorem ResU.inStratum_single {α : Life} (l : Loc) {ψ : CellU Loc Val}
    (h : ψ.InStratum α) : (ResU.single l ψ).InStratum α := by
  intro k χ e
  by_cases hk : k = l
  · subst hk; rw [ResU.single_get_self] at e; cases Option.some.inj e; exact h
  · rw [ResU.single_get_ne _ hk] at e; exact absurd e (by simp)

/-- An owned cell lies in every stratum. -/
theorem ResU.inStratum_single_own (α : Life) (l : Loc) (v : Val) :
    (ResU.single l (CellU.ownOf v)).InStratum α :=
  ResU.inStratum_single l trivial

theorem ResU.single_get_eq_some {l l' : Loc} {ψ χ : CellU Loc Val}
    (h : (ResU.single l ψ).get l' = some χ) : l' = l ∧ χ = ψ := by
  classical
  by_cases e : l' = l
  · exact ⟨e, (Option.some.inj (by rw [← h, e, ResU.single_get_self])).symm⟩
  · exact absurd (h.symm.trans (ResU.single_get_ne ψ e)) (by simp)

/-- `ρ ≼ ρ′`: "is a `○`-factor of".
`[variant: `[CONF]` p. 415:24 footnote 1's `≤` at `○`; the print defines it at
`●` only]` -/
def ResU.LeR (ρ σ : ResU Loc Val) : Prop := ∃ τ, ResU.CompR ρ τ σ

theorem ResU.comp_empty_left {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (ρ : ResU Loc Val) :
    ResU.Comp R C PMap.empty ρ ρ := by
  refine ⟨ResU.Compat.of_disjoint (fun _ => Or.inl rfl), fun l => ?_⟩
  show OptComp C none (ρ.get l) (ρ.get l)
  cases e : ρ.get l with
  | none => rfl
  | some ψ => rfl

theorem ResU.restrict_single_self {l : Loc} {ψ : CellU Loc Val} {k : Kind}
    (h : ψ.kind = k) : (ResU.single l ψ).restrict k = ResU.single l ψ := by
  classical
  refine PMap.ext fun l' => ?_
  by_cases e : l' = l
  · subst e
    rw [ResU.single_get_self]
    exact ResU.restrict_eq_some.mpr ⟨ResU.single_get_self _ _, h⟩
  · rw [ResU.single_get_ne _ e]
    cases f : ((ResU.single l ψ).restrict k).get l' with
    | none => rfl
    | some χ =>
        obtain ⟨hg, -⟩ := ResU.restrict_eq_some.mp f
        exact absurd (hg.symm.trans (ResU.single_get_ne _ e)) (by simp)

theorem ResU.restrict_single_other {l : Loc} {ψ : CellU Loc Val} {k : Kind}
    (h : ψ.kind ≠ k) : (ResU.single l ψ).restrict k = PMap.empty := by
  refine PMap.ext fun l' => ?_
  cases f : ((ResU.single l ψ).restrict k).get l' with
  | none => rfl
  | some χ =>
      obtain ⟨hg, hk⟩ := ResU.restrict_eq_some.mp f
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
      exact absurd hk h

theorem ResU.sites_single_self {l : Loc} {ψ : CellU Loc Val} {k : Kind}
    (h : ψ.kind = k) : ResU.Sites (ResU.single l ψ) k [l] := by
  classical
  refine ⟨by simp, fun l' => ⟨fun hm => ?_, fun ⟨χ, hg, hk⟩ => ?_⟩⟩
  · cases List.mem_singleton.mp hm
    exact ⟨ψ, ResU.single_get_self _ _, h⟩
  · exact List.mem_singleton.mpr (ResU.single_get_eq_some hg).1

theorem ResU.sites_single_other {l : Loc} {ψ : CellU Loc Val} {k : Kind}
    (h : ψ.kind ≠ k) : ResU.Sites (ResU.single l ψ) k [] := by
  refine ⟨by simp, fun l' => ⟨fun hm => absurd hm (by simp), fun ⟨χ, hg, hk⟩ => ?_⟩⟩
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
  exact absurd hk h

/-- `ex(ℓ ↦ own(v))_◐ = ℓ ↦ own(v)`, at either operator. -/
theorem ExW.single_own {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (l : Loc) (v : Val) :
    ExW R C (ResU.single l (CellU.ownOf v)) (ResU.single l (CellU.ownOf v)) := by
  refine ExW.mk (w := []) (b := PMap.empty) (nm := ResU.single l (CellU.ownOf v))
    (ResU.sites_single_other (fun e => Kind.noConfusion e))
    ExWits.nil BigComp.nil ?_ (ResU.comp_empty_right _)
  rw [ResU.restrict_single_self (k := Kind.own) rfl,
    ResU.restrict_single_other (k := Kind.mut) (fun e => Kind.noConfusion e)]
  exact ResU.comp_empty_right _

/-- `ag(ℓ↦own(v)) = ∅`. -/
theorem AgW.single_own (l : Loc) (v : Val) :
    AgW (ResU.single l (CellU.ownOf v)) (PMap.empty : ResU Loc Val) := by
  refine AgW.mk (wm := []) (wi := []) (a := PMap.empty) (bm := PMap.empty)
    (bi := PMap.empty)
    (ResU.sites_single_other (fun e => Kind.noConfusion e))
    (ResU.sites_single_other (fun e => Kind.noConfusion e))
    AgWitsM.nil AgWitsI.nil BigComp.nil BigComp.nil ?_ (ResU.comp_empty_right _)
  rw [ResU.restrict_single_other (k := Kind.imm) (fun e => Kind.noConfusion e)]
  exact ResU.comp_empty_right _

/-- `⦇ℓ ↦ own(v)⦈ = ℓ ↦ own(v)`, hence `✓(ℓ ↦ own(v))`. -/
theorem ResU.flat_single_own (l : Loc) (v : Val) :
    ResU.Flat (ResU.single l (CellU.ownOf v)) (ResU.single l (CellU.ownOf v)) :=
  ⟨_, _, ExW.single_own l v, AgW.single_own l v, ResU.comp_empty_right _⟩

theorem ResU.valid_single_own (l : Loc) (v : Val) :
    ResU.Valid (ResU.single l (CellU.ownOf (Val := Val) v)) :=
  ⟨_, ResU.flat_single_own l v⟩

end BoCa.Fig16

end
