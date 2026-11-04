import Core.TreeLend
import Core.TreeSchedPool

/-!
# Ending a lend whose copies came back composed  `[spec §62]`

A lend's cell `ℓ ↦ imm({α}, (), ∅)` splits into copies that tasks hold apart. When they come back
they compose (`compS_single_imm`) to `ℓ ↦ imm(S, (), ∅)`, `S` the union of the copies' lifetime
sets. `twp_lendEnd` asks for the lend cell itself. This file proves that the two are the same
cell, so `twp_lendEnd`'s statement is unchanged:

* **A tagged record proper's frame is at its tag** (`frameLife_of_tagged`): `TaggedT` puts every
  tagged record in the lineage of a record proper framed at its tag. A record proper is no proper
  descendant of a record (`not_desc_proper`), so that record proper is itself.
* **A cell at its location carries its frame lifetime and nothing else** (`proper_view_single`):
  `view_at_lender` at that frame lifetime. Every cell any part of the world holds at `ℓ`, while
  `lendRec ℓ` is a record proper tagged `α`, has lifetime set `{α}`.
* **End at the composed copies** (`twp_lendEnd_imm`): the run holds `ℓ ↦ imm(S, (), ∅)` and the
  list carries `lendRec ℓ` at a tag `α`; at every start world `S = {α}`, and `twp_lendEnd` applies
  there.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont)

/-- **A tagged record proper's frame is at its tag.** -/
theorem frameLife_of_tagged {w : TWd} {fρ : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} (hR : RecInv w fρ ps ls) {p : FrameRecT w.K} {α : Life}
    (hp : p ∈ ps) (hx : (p, α) ∈ ls) : FrameLifeT w.K fρ p α := by
  obtain ⟨q, hq, ⟨path, hpath⟩, hFL⟩ := hR.2 (p, α) hx
  have hqrs : q ∈ rsOfT ls := (hR.1.inv.2.2.2.2.2.2.1 q).mpr ⟨q, hq, [], .nil q⟩
  cases path with
  | nil =>
      cases hpath
      exact hFL
  | cons x path =>
      exact (not_desc_proper hR.1 hp hqrs ⟨x :: path, List.cons_ne_nil _ _, hpath⟩).elim

/-- **A cell at a tagged record proper's location carries the tag and nothing else**: any part of
the world, any cell there with a lifetime set. -/
theorem proper_view_single {w : TWd} {fρ ρ o : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} (hR : RecInv w fρ ps ls) {p : FrameRecT w.K} {α : Life}
    (hp : p ∈ ps) (hx : (p, α) ∈ ls) (hW : ResUT.CompS ρ o fρ) {ψ : TCell w.K} {s : TSet}
    (hl : ρ.get p.le = some ψ) (hs : ψ.lsOf = some s) : s = TSet.single α := by
  have h := view_at_lender hR.1 hp hW (frameLife_of_tagged hR hp hx) hl hs
  refine TSet.ext (Finset.ext fun y => ?_)
  simp only [TSet.single_set, Finset.mem_singleton]
  refine ⟨h y, fun e => ?_⟩
  subst e
  obtain ⟨z, hz⟩ := s.ne
  exact h z hz ▸ hz

/-- The copy `ℓ ↦ imm(S, (), ∅)`. -/
def viewResS {K : WCactus} (S : TSet) (l : BoCa.Loc) : TRes K :=
  ResUT.single l (CellUT.immOf S BoCa.Val.unit PMap.empty (emptyT_inStratum _))

theorem viewResS_single {K : WCactus} (α : Life) (l : BoCa.Loc) :
    viewResS (K := K) (TSet.single α) l = viewRes α l := rfl

/-- Copies compose: their lifetime sets join. -/
theorem viewResS_compS {K : WCactus} (S T : TSet) (l : BoCa.Loc) :
    ResUT.CompS (viewResS (K := K) S l) (viewResS T l) (viewResS (S ∪ T) l) :=
  ResUT.compS_single_imm (K := K) l S T BoCa.Val.unit PMap.empty (emptyT_inStratum _)
    (emptyT_inStratum _) (emptyT_inStratum _)

/-- **End a lend at its copies composed.** `twp_lendEnd` with the run holding
`ℓ ↦ imm(S, (), ∅)` for the lend cell, the list carrying `lendRec ℓ` at some tag. -/
theorem twp_lendEnd_imm {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls ls₁ : List (SRecT w.K)}
    {O O₁ : List (FrameRecT w.K)} {e : Expr} {Z ρ ρ₁ : TRes w.K} {l : BoCa.Loc}
    {S : TSet} (hρ : ResUT.CompS Z (viewResS S l) ρ) (hα : lendRec l ∈ rsOfT ls)
    (hρ₁ : ResUT.CompS Z (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ₁)
    (hvZ : ResUT.Valid Z) (hZ : NoneAt (· = l) Z)
    (hF : ∀ w' ρf, F w' ρf → NoneAt (· = l) ρf)
    (hO : ∀ x, x ∈ O ↔ x = lendRec l ∨ x ∈ O₁) (hO₁ : lendRec l ∉ O₁)
    (hls : ∀ x ∈ ls, x.1 = lendRec l ∨ x ∈ ls₁) (hls₁in : ∀ x ∈ ls₁, x ∈ ls)
    (hls₁ : ∀ x ∈ ls₁, x.1 ≠ lendRec l)
    (h : twp (ℍ := ℍ) F Q n w ls₁ O₁ e ρ₁) :
    twp (ℍ := ℍ) F Q n w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hOr hFρ hf hc hS hR hI
  obtain ⟨⟨r, α⟩, hα', hrα⟩ := List.mem_map.mp hα
  simp only at hrα
  subst hrα
  -- at the start world, the copy's lifetime set is the lend's tag
  have hS1 : S = TSet.single α := by
    obtain ⟨σZ, hσZ⟩ := hvZ
    have hZl : Z.get l = none := get_eq_none_of_flatT hσZ (hZ σZ hσZ l rfl)
    have hρl : ρ.get l = some (CellUT.immOf S BoCa.Val.unit PMap.empty (emptyT_inStratum _)) := by
      rw [ResUT.Comp.get_of_left_none hρ hZl, viewResS, ResUT.single_get_self]
    obtain ⟨ψ', e', hrc⟩ := hr.get_some hρl
    obtain ⟨χ', h', rfl, -⟩ := RC.immOf_inv hrc
    have hp₀ : lendRec l ∈ O₀ := by
      obtain ⟨y, hy, hry⟩ := forall₂_mem_left hOr ((hO _).mpr (Or.inl rfl))
      rwa [RecRR.func hry (lendRec_rr l)] at hy
    have hpps : lendRec l ∈ ps := (hS.1 _).mpr (Or.inl hp₀)
    have hx₀ : (lendRec l, α) ∈ ls₀ := by
      obtain ⟨y, hy, hry, hyt⟩ := forall₂_mem_left hl hα'
      have : y = (lendRec l, α) := Prod.ext (RecRR.func hry (lendRec_rr l)) hyt
      exact this ▸ hy
    exact proper_view_single hR hpps hx₀ (ResUT.CompS.comm hc) e' (CellUT.lsOf_immOf _ _ _ _)
  subst hS1
  exact twp_lendEnd hρ hρ₁ hvZ hZ hF hO hO₁ hls hls₁in hls₁ h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE
    hr hl hOr hFρ hf hc hS hR hI

end BoCa.Fig16.Tree.Wp

end
