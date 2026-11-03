import Core.TreeStepKeep

/-!
# The step-indexed relation over the tree world: headline results at one branch  `[spec §62]`

The statements of `docs/new-core/scope-781.md` §4 that slice (b) proves, each stated as a `Prop`
and proved below it:

* **Top-level adequacy** (`TopAdequacyT`, `topAdequacyT`): a closed program verified at
  `cerwpT` at the empty table, from the empty world at any tree, under the empty frame, whose
  result holds nothing, is safe or diverges, reaches a value only at the empty memory, and every
  `free` finds its cell. It is `cerwpT_adequacy`, derived through `CactusInvT`'s `cactusT_step`
  (`Core/TreeCactus.lean`).
* **R1, a step keeps every other branch's open lend** (`R1_StepKeepsFdEsc`,
  `r1_stepKeepsFdEsc`): a branch that holds nothing of a frame record's lend before its run holds
  nothing of it after, in every post-configuration `twp` admits. Beside it,
  `not_stepKeepsFdEscNoUpd` (`Core/TreeStepKeep.lean`): without `EndT`'s `↭` and frame clause the
  same statement fails, a branch ending with a copy of another's lent cell.
* **R2, a lend is not ended while a stored branch still holds part of it**
  (`R2_EndBlockedByHolder`, `r2_endBlockedByHolder`): in a configuration of the cactus invariant,
  a branch that holds part of a record's lend (its flattening meets the lent location or the
  escrow's exclusive part) blocks the end: the lender's piece `ℓ ↦ own(v) ● R` composes with no
  rest of the world containing that branch to a valid world. So no branch is resumed after a lend
  it still borrows from ended.
* **R3, a join ends a shared lend only when the other branches hold nothing of it**
  (`R3_JoinEndNeedsFdEsc`, `r3_joinEndNeedsFdEsc`): if the joiner's end of a record it owns is
  valid, the other branches' composite meets `FdEsc`. With `fdEsc_at_join` (`JoinPtT` ⇒ `FdEsc`)
  and `immEnd_valid_of_fdEsc` (`FdEsc` ⇒ the end is valid), the end is valid exactly when no
  other branch holds part of the lend.

R2 and R3 both rest on one fact about the carrier (`fdEsc_of_end_valid`): a valid world in which
`ℓ ↦ own(v) ● R` is a part leaves nothing of `ℓ` or of `ex(R)` to the rest. `ex` of the lender's
piece holds both, and an exclusive cell composes with no other cell under `●`, so the rest's
exclusive walk misses them, and the world's aliasable walk, which contains the rest's, misses the
world's exclusive walk. Neither proof reads the invariant: its premises place the statement at a
configuration the scheduler reaches, and `config_end_refused` shows the configuration of
`cactusT_config` meets them.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)

/-- The empty world at the tree `P`. -/
def w₀ (P : ParentFn) : TWd := ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩

/-! ### Top-level adequacy (the `OrDiverges` shape) -/

/-- **Top-level adequacy, one branch.** -/
def TopAdequacyT : Prop :=
  ∀ (P : ParentFn) (Q : TPostV) (P₀ : Expr),
    (∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty) →
    (∀ n, cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Q (fun _ ρf => ρf = PMap.empty) n (w₀ P) [] []
      P₀ (PMap.empty : TRes (WCactus.ofParent P))) →
    OrDiverges (ℍ := ℍ) P₀

theorem topAdequacyT : TopAdequacyT (ℍ := ℍ) :=
  fun P _ _ hQ hall => cerwpT_adequacy (ℍ := ℍ) P hQ hall

/-! ### R1. A step keeps every other branch's open lend -/

abbrev R1_StepKeepsFdEsc : Prop := StepKeepsFdEsc (ℍ := ℍ)

theorem r1_stepKeepsFdEsc : R1_StepKeepsFdEsc (ℍ := ℍ) := stepKeepsFdEsc

/-! ### The end of a lend, read off validity -/

/-- **A valid world with the lender's piece in it leaves nothing of the lend to the rest.** With
`X′ = ℓ ↦ own(v) ● R` and `X′ ● Y` valid, `Y`'s flattening holds nothing at `ℓ` nor at any
location of `ex(R)`. The converse of `immEnd_valid_of_fdEsc` at the end world. -/
theorem fdEsc_of_end_valid {K : WCactus} {l : BoCa.Loc} {v : BoCa.Val} {R Y X' W' : TRes K}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X') (hW' : ResUT.CompS X' Y W')
    (hv : ResUT.Valid W') : FdEsc l R Y := by
  obtain ⟨σW, hσW⟩ := hv
  obtain ⟨eX, eY, eW, aX, aY, aW, heX, heY, heW, -, haY, haW, hσWc⟩ :=
    (ResUT.Flat.split hW').mp hσW
  have heW' : ExST W' eW := (ExST.split hW').mpr ⟨eX, eY, heX, heY, heW⟩
  obtain ⟨o₁, eR, ho₁, heR, heXc⟩ := (ExST.split hX).mp heX
  obtain rfl : o₁ = ResUT.single l (CellUT.ownOf v) := ExST.functional ho₁ (ExWT.single_own l v)
  -- `ex(ℓ ↦ own(v) ● R)` holds `ℓ` and every location of `ex(R)`
  have hl : (eX.get l).isSome := by
    cases h : eX.get l with
    | some _ => rfl
    | none =>
        have := none_of_comp_none_left heXc h
        rw [ResUT.single_get_self] at this; cases this
  have hR : ∀ x, (eR.get x).isSome → (eX.get x).isSome := by
    intro x hx
    cases h : eX.get x with
    | some _ => rfl
    | none =>
        have := none_of_comp_none_right heXc h
        rw [this] at hx; cases hx
  -- the rest's flattening misses every location of `ex(ℓ ↦ own(v) ● R)`
  have key : ∀ τ, ResUT.Flat Y τ → ∀ x, (eX.get x).isSome → τ.get x = none := by
    intro τ hτ x hx
    obtain ⟨eY', aY', heY', haY', hτc⟩ := hτ
    obtain rfl := ExST.functional heY heY'
    obtain rfl := AgWT.functional haY haY'
    have h₁ : eY.get x = none :=
      (ResUT.CompatS.disjoint_of_immFree (ExST.immFree heX) heW.1 x).resolve_left
        (fun h => by rw [h] at hx; cases hx)
    have h₂ : eW.get x ≠ none := fun hn => by
      rw [none_of_comp_none_left heW hn] at hx; cases hx
    have h₃ : aW.get x = none :=
      (ResUT.CompatS.disjoint_of_immFree (ExST.immFree heW') hσWc.1 x).resolve_left h₂
    exact (ResUT.Comp.eq_none_iff hτc x).mpr ⟨h₁, none_of_comp_none_right haW h₃⟩
  intro τ hτ
  refine ⟨key τ hτ l hl, fun eR' heR' x hx => key τ hτ x (hR x ?_)⟩
  rwa [ExST.functional heR' heR] at hx

/-! ### R2. A lend a stored branch still borrows is not ended -/

/-- **R2.** In a configuration of the cactus invariant, a branch `b` that holds part of a record
proper `p`'s lend (its flattening meets `p`'s location or the escrow's exclusive part, `¬ FdEsc`)
blocks the end of `p`: with `b` a part of the rest `Y` of the world, `ℓ ↦ own(v) ● R` does not
compose with `Y` to a valid world. So no branch resumes after `p` ended while it still borrowed. -/
def R2_EndBlockedByHolder : Prop :=
  ∀ (w : TWd) (bs : List (TBranch w.K)) (ns : List Life) (W : TRes w.K)
    (ps : List (FrameRecT w.K)) (ls : List (SRecT w.K)) (μ : Heap),
    CactusInvT w bs ns W ps ls μ →
    ∀ b ∈ bs, ∀ p ∈ ps, ¬ FdEsc p.le p.R b.1 →
    ∀ (s : TSet) (hs : p.R.InStratum s) (Y Yr X' : TRes w.K),
      ResUT.CompS (ResUT.single p.le (CellUT.immOf s p.v p.R hs)) Y W →
      ResUT.CompS b.1 Yr Y →
      ResUT.CompS (ResUT.single p.le (CellUT.ownOf p.v)) p.R X' →
      ¬ ∃ W', ResUT.CompS X' Y W' ∧ ResUT.Valid W'

/-- **R2 holds.** The end world, if valid, leaves the rest nothing of the lend
(`fdEsc_of_end_valid`), and the holder is a part of the rest (`NoneAt.of_compS_left`). -/
theorem r2_endBlockedByHolder : R2_EndBlockedByHolder := by
  intro w bs ns W ps ls μ _ b _ p _ hb s hs Y Yr X' _ hbY hX ⟨W', hW', hv⟩
  have hY : FdEsc p.le p.R Y := fdEsc_of_end_valid hX hW' hv
  have hvY : ResUT.Valid Y := (ResUT.Valid.split hW' hv).2
  exact hb (fdEsc_iff_noneAt.mpr ((fdEsc_iff_noneAt.mp hY).of_compS_left hbY hvY))

/-! ### R3. A join ends a shared lend only when no other branch holds part of it -/

/-- **R3.** At a join, the joiner (the head branch) owns `p` and ends it: if the end world is valid,
the other branches' composite holds nothing of `p`'s lend (`FdEsc`). With `fdEsc_at_join`
(`JoinPtT` ⇒ `FdEsc`) and `immEnd_valid_of_fdEsc` (`FdEsc` ⇒ the end is valid), the end is valid
exactly when no other branch holds part of the lend. -/
def R3_JoinEndNeedsFdEsc : Prop :=
  ∀ (w : TWd) (ρ : TRes w.K) (O : List (FrameRecT w.K)) (others : List (TBranch w.K))
    (n₀ : Life) (ns : List Life) (W : TRes w.K) (ps : List (FrameRecT w.K))
    (ls : List (SRecT w.K)) (μ : Heap),
    CactusInvT w ((ρ, O) :: others) (n₀ :: ns) W ps ls μ →
    ∀ p ∈ O, ∀ (ρf : TRes w.K), CompAllT (others.map Prod.fst) ρf →
    ∀ (s : TSet) (hs : p.R.InStratum s) (Y X' W' : TRes w.K),
      ResUT.CompS (ResUT.single p.le (CellUT.immOf s p.v p.R hs)) Y W →
      ResUT.Le ρf Y →
      ResUT.CompS (ResUT.single p.le (CellUT.ownOf p.v)) p.R X' →
      ResUT.CompS X' Y W' → ResUT.Valid W' →
      FdEsc p.le p.R ρf

/-- **R3 holds**, by `fdEsc_of_end_valid` at the rest and `NoneAt.of_compS_left` at its part. -/
theorem r3_joinEndNeedsFdEsc : R3_JoinEndNeedsFdEsc := by
  intro w ρ O others n₀ ns W ps ls μ _ p _ ρf _ s hs Y X' W' _ hle hX hW' hv
  obtain ⟨z, hz⟩ := hle
  have hY : FdEsc p.le p.R Y := fdEsc_of_end_valid hX hW' hv
  have hvY : ResUT.Valid Y := (ResUT.Valid.split hW' hv).2
  exact fdEsc_iff_noneAt.mpr ((fdEsc_iff_noneAt.mp hY).of_compS_left hz hvY)

/-! ### At the configuration without points -/

/-- **The configuration meets R2's and R3's premises, and the end is refused there.** At
`cactusT_config` the parent's world is `ℓ ↦ imm({α}, loc m, R) ● childRes`, the child holds the
record's image at `m ∈ ex(R)`, and no lender's piece `ℓ ↦ own(loc m) ● R` composes with the child
to a valid world. R2 gives it from the child's failure of `FdEsc` (`config_not_fdEsc`); R3 gives
it at the join of the parent with the child as the only other branch. -/
theorem config_end_refused :
    ∃ (W : TRes wC.K) (μ : BoCa.Loc → Option BoCa.Val),
      CactusInvT wC bsC nsC W [recE ℓC mC] lsC μ ∧
      ResUT.CompS (ResUT.single (recE (K := KC) ℓC mC).le (lendCell αC mC)) childRes W ∧
      ∀ X' : TRes wC.K,
        ResUT.CompS (ResUT.single (recE (K := KC) ℓC mC).le
          (CellUT.ownOf (recE (K := KC) ℓC mC).v)) (recE (K := KC) ℓC mC).R X' →
        ¬ ∃ W', ResUT.CompS X' childRes W' ∧ ResUT.Valid W' := by
  obtain ⟨W, μ, hW, hI⟩ := cactusT_config
  refine ⟨W, μ, hI, hW, fun X' hX => ?_⟩
  exact r2_endBlockedByHolder wC bsC nsC W [recE ℓC mC] lsC μ hI (childRes, [])
    (by simp [bsC]) (recE ℓC mC) (List.mem_singleton_self _) config_not_fdEsc
    (TSet.single αC) (own_inStratum _ _ _) childRes PMap.empty X' hW
    (ResUT.compS_empty_right _) hX

end BoCa.Fig16.Tree.Wp

end
