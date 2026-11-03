import Support.Model.Tree.Port.WalkSplitting

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Support/Model/Singletons.lean`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

/-!
# Support — Model — Singletons

`[about ours]`.  Restriction `ρ∣ι`, singleton resources `ℓ ↦ ψ`, the order `ρ ≤ ρ′`, and the walks and restrictions of singletons.
-/



namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
theorem ResUT.restrictOn_eq_some {ρ : ResUT Loc Val K} {p : Kind → Bool} {l : Loc}
    {ψ : CellUT Loc Val K} :
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
theorem ResUT.single_get_ne {l l' : Loc} (ψ : CellUT Loc Val K) (h : l' ≠ l) :
    (ResUT.single l ψ).get l' = none := if_neg h

/-- `∅ ∈ Res_α` at every `α`. -/
theorem ResUT.inStratum_empty (α : TSet) :
    ResUT.InStratum α (PMap.empty : ResUT Loc Val K) :=
  fun l _ e => absurd (e.symm.trans (PMap.empty_get l)) (by simp)

/-- `ℓ ↦ ψ ∈ Res_α` exactly when its one cell is. -/
theorem ResUT.inStratum_single {α : TSet} (l : Loc) {ψ : CellUT Loc Val K}
    (h : ψ.InStratum α) : (ResUT.single l ψ).InStratum α := by
  intro k χ e
  by_cases hk : k = l
  · subst hk; rw [ResUT.single_get_self] at e; cases Option.some.inj e; exact h
  · rw [ResUT.single_get_ne _ hk] at e; exact absurd e (by simp)

/-- An owned cell lies in every stratum. -/
theorem ResUT.inStratum_single_own (α : TSet) (l : Loc) (v : Val) :
    (ResUT.single l (CellUT.ownOf (K := K) (Loc := Loc) v)).InStratum α :=
  ResUT.inStratum_single l trivial

theorem ResUT.single_get_eq_some {l l' : Loc} {ψ χ : CellUT Loc Val K}
    (h : (ResUT.single l ψ).get l' = some χ) : l' = l ∧ χ = ψ := by
  classical
  by_cases e : l' = l
  · exact ⟨e, (Option.some.inj (by rw [← h, e, ResUT.single_get_self])).symm⟩
  · exact absurd (h.symm.trans (ResUT.single_get_ne ψ e)) (by simp)

/-- `ρ ≼ ρ′`: "is a `○`-factor of".
`[variant: `[CONF]` p. 415:24 footnote 1's `≤` at `○`; the print defines it at
`●` only]` -/
def ResUT.LeR (ρ σ : ResUT Loc Val K) : Prop := ∃ τ, ResUT.CompR ρ τ σ

theorem ResUT.comp_empty_left {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop} (ρ : ResUT Loc Val K) :
    ResUT.Comp R C PMap.empty ρ ρ := by
  refine ⟨ResUT.Compat.of_disjoint (fun _ => Or.inl rfl), fun l => ?_⟩
  show OptCompT C none (ρ.get l) (ρ.get l)
  cases e : ρ.get l with
  | none => rfl
  | some ψ => rfl

theorem ResUT.restrict_single_self {l : Loc} {ψ : CellUT Loc Val K} {k : Kind}
    (h : ψ.kind = k) : (G.restrict CellUT.kind (ResUT.single l ψ) k) = ResUT.single l ψ := by
  classical
  refine PMap.ext fun l' => ?_
  by_cases e : l' = l
  · subst e
    rw [ResUT.single_get_self]
    exact ResUT.restrict_eq_some.mpr ⟨ResUT.single_get_self _ _, h⟩
  · rw [ResUT.single_get_ne _ e]
    cases f : (G.restrict CellUT.kind (ResUT.single l ψ) k).get l' with
    | none => rfl
    | some χ =>
        obtain ⟨hg, -⟩ := ResUT.restrict_eq_some.mp f
        exact absurd (hg.symm.trans (ResUT.single_get_ne _ e)) (by simp)

theorem ResUT.restrict_single_other {l : Loc} {ψ : CellUT Loc Val K} {k : Kind}
    (h : ψ.kind ≠ k) : (G.restrict CellUT.kind (ResUT.single l ψ) k) = PMap.empty := by
  refine PMap.ext fun l' => ?_
  cases f : (G.restrict CellUT.kind (ResUT.single l ψ) k).get l' with
  | none => rfl
  | some χ =>
      obtain ⟨hg, hk⟩ := ResUT.restrict_eq_some.mp f
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some hg
      exact absurd hk h

theorem ResUT.sites_single_self {l : Loc} {ψ : CellUT Loc Val K} {k : Kind}
    (h : ψ.kind = k) : ResUT.Sites (ResUT.single l ψ) k [l] := by
  classical
  refine ⟨by simp, fun l' => ⟨fun hm => ?_, fun ⟨χ, hg, hk⟩ => ?_⟩⟩
  · cases List.mem_singleton.mp hm
    exact ⟨ψ, ResUT.single_get_self _ _, h⟩
  · exact List.mem_singleton.mpr (ResUT.single_get_eq_some hg).1

theorem ResUT.sites_single_other {l : Loc} {ψ : CellUT Loc Val K} {k : Kind}
    (h : ψ.kind ≠ k) : ResUT.Sites (ResUT.single l ψ) k [] := by
  refine ⟨by simp, fun l' => ⟨fun hm => absurd hm (by simp), fun ⟨χ, hg, hk⟩ => ?_⟩⟩
  obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some hg
  exact absurd hk h

/-- `ex(ℓ ↦ own(v))_◐ = ℓ ↦ own(v)`, at either operator. -/
theorem ExWT.single_own {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop} (l : Loc) (v : Val) :
    ExWT R C (ResUT.single l (CellUT.ownOf v)) (ResUT.single l (CellUT.ownOf v)) := by
  refine G.ExW.mk (w := []) (b := PMap.empty) (nm := ResUT.single l (CellUT.ownOf v))
    (ResUT.sites_single_other (fun e => Kind.noConfusion e))
    G.ExWits.nil G.BigComp.nil ?_ (ResUT.comp_empty_right _)
  rw [ResUT.restrict_single_self (k := Kind.own) rfl,
    ResUT.restrict_single_other (k := Kind.mut) (fun e => Kind.noConfusion e)]
  exact ResUT.comp_empty_right _

/-- `ag(ℓ↦own(v)) = ∅`. -/
theorem AgWT.single_own (l : Loc) (v : Val) :
    AgWT (ResUT.single l (CellUT.ownOf (K := K) v)) (PMap.empty : ResUT Loc Val K) := by
  refine G.AgW.mk (wm := []) (wi := []) (a := PMap.empty) (bm := PMap.empty)
    (bi := PMap.empty)
    (ResUT.sites_single_other (fun e => Kind.noConfusion e))
    (ResUT.sites_single_other (fun e => Kind.noConfusion e))
    G.AgWitsM.nil G.AgWitsI.nil G.BigComp.nil G.BigComp.nil ?_ (ResUT.comp_empty_right _)
  rw [ResUT.restrict_single_other (k := Kind.imm) (fun e => Kind.noConfusion e)]
  exact ResUT.comp_empty_right _

/-- `⦇ℓ ↦ own(v)⦈ = ℓ ↦ own(v)`, hence `✓(ℓ ↦ own(v))`. -/
theorem ResUT.flat_single_own (l : Loc) (v : Val) :
    ResUT.Flat (ResUT.single l (CellUT.ownOf (K := K) v)) (ResUT.single l (CellUT.ownOf v)) :=
  ⟨_, _, ExWT.single_own l v, AgWT.single_own l v, ResUT.comp_empty_right _⟩

theorem ResUT.valid_single_own (l : Loc) (v : Val) :
    ResUT.Valid (ResUT.single l (CellUT.ownOf (K := K) (Val := Val) v)) :=
  ⟨_, ResUT.flat_single_own l v⟩

end BoCa.Fig16.Tree

end
