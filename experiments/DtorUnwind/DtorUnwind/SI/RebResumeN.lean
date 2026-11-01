import DtorUnwind.SI.RebStopN

/-!
# 6.150 across a stop: what bounds the resume frame

`RebReentryN` (`SI/RebStopN.lean`) is `TW.reb` without its premise `StratumLe W β`, the step a
reborrow live across a stop needs at the resume: the continuation holds the reborrow `χ` at the
`β` its first entry chose, and the resume's world is `ρ_f′ ● ρ` for a frame `ρ_f′` that `rwpG`
quantifies over.

## `sameW` does not bound `ρ_f′`

`OpEntN.wc = sameW` fixes the list of tagged records the continuation is resumed at. It reads
nothing of the frame. `resume_frame_short` builds, from any typed world at any list, a typed world
at the same records and the same list (so `sameW` holds) whose frame holds one more cell
`ℓ ↦ mut(A′, v, ∅, ⊤)`, at any `A′`: a handler that lends a cell of its own at a fresh
`A′ ⊏ β` and resumes `κ` inside the lend. A `mut` lend adds no record (`TW.mutFold`), so no
condition on the list can see it. At that world both stratum premises of the reborrow fail:
`TW.reb`'s `StratumLe W β` at the re-entry, and `TW.rebEnd`'s `W′.InStratum β` at the return
of the resumed segment (`resume_frame_not_stratumLe`, `resume_frame_not_inStratum`). The second
is the one that also defeats the alternative of keeping `χ` live in the world across the stop
instead of folding it: the reborrow still ends inside the handler's lend.

## What the premises are read for

`TW.reb`'s premise is read once, in `frameLife_reb_like`, as `β ⊑ α` at a record proper `p`
whose lineage meets an exclusive location of the reborrowed escrow (the branch where a new view
at `β` lands in `p`'s lineage). `frameLife_reb_rec` is that lemma with the premise at that
record only; `RebRecLe` collects it over the records proper, and `rebRecLe_of_stratumLe` shows
it is implied by `StratumLe`. `TW.rebEnd`'s premise is read in `ti_endReb` for `NestLife`, at
chain positions of records. Both are conditions on records; the handler's `mut` cell above is
not in any record's lineage.

`RebReentryRecN` is `TW.reb` with `RebRecLe` in place of `StratumLe`. `TW` is
`Core/World.lean`'s, a library definition: neither `RebReentryN` nor `RebReentryRecN` can be
added from an experiment, and the repository's rule is a spec entry before a library change.

I have not derived `RebReentryRecN`, nor that `RebRecLe` holds at every resume under `sameW`,
and have not verified that any obstruction is real.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeVar)

/-- The stored predicate of the handler's cell: anything. -/
def predTop (A : Life) : Val → SPropS Loc Val A := fun _ _ => True

/-- The handler's `mut` cell at `A`, holding `v` and nothing else. -/
def shortCell (A : Life) (v : Val) : CellU Loc Val :=
  CellU.mutOf A v PMap.empty (ResU.inStratum_empty A) (predTop A) trivial

/-- **A resume frame may hold a cell at any lifetime.** From a typed, tagged world `W` at the
records `ps`, `rs` and the list `ls`, with a location its memory misses: `W ● ℓ ↦ mut(A, v, ∅, ⊤)`
is a typed, tagged world at the same records and list, over the memory with `ℓ ↦ v` (6.141 then
6.66's fold). The extra cell is outside every resource `W` holds, so it is a frame extension:
`rwpG` quantifies over it at every resource it quantifies over at `W`. -/
theorem resume_frame_short {W : WRes} {ps rs : List FrameRec} {ls : List SRec} {μ : Heap}
    {l : Loc} (hT : TW W ps rs) (htg : Tagged W ps ls) (hL : ResU.Lower W μ) (hμ : μ l = none)
    (v : Val) (A : Life) :
    ∃ W', ResU.CompS W (ResU.single l (shortCell A v)) W' ∧ TW W' ps rs ∧ Tagged W' ps ls ∧
      ResU.Lower W' (BoCa.BoLo.Heap.upd μ l v) ∧ ¬ W'.InStratum A := by
  obtain ⟨τ, hτ, hval⟩ := id hL
  have hWl : W.get l = none := get_eq_none_of_flat hτ ((lower_eq_none_iff hval).mp hμ)
  obtain ⟨W1, hc⟩ := (ResU.compS_defined_iff W (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hWl)
  obtain ⟨σ', hσ', hH, hLσ'⟩ := hash_compS_own (ρf := PMap.empty) (ResU.comp_empty_left W) hL hμ hc
  obtain rfl : W1 = σ' := ResU.CompS.functional (ResU.comp_empty_left W1) hσ'
  have hv1 : ResU.Valid W1 := hash_valid_comp hH hσ'
  -- 6.141: the allocation
  have hT1 : TW W1 ps rs := TW.alloc hT hL hμ hc hv1
  have htg1 : Tagged W1 ps ls := tagged_of_ag (fun a ha => alloc_ag hc ha) htg
  -- 6.66's fold: `ℓ ↦ own(v) ● ∅` to `ℓ ↦ mut(A, v, ∅, ⊤)`
  have hown : ResU.CompS (PMap.empty : WRes) (ResU.single l (CellU.ownOf v))
      (ResU.single l (CellU.ownOf v)) := ResU.comp_empty_left _
  have hHown : ResU.Hash W (ResU.single l (CellU.ownOf v)) := ⟨hc.1, W1, hc, hv1⟩
  have hHmut : ResU.Hash W (ResU.single l (shortCell A v)) := (ResU.six24 hown).mpr hHown
  obtain ⟨W', hW', hvW'⟩ := hHmut.2
  have hvm : ResU.Valid (ResU.single l (shortCell A v)) := (ResU.Valid.split hW' hvW').2
  have hvo : ResU.Valid (ResU.single l (CellU.ownOf v)) := (ResU.Valid.split hc hv1).2
  have hT' : TW W' ps rs :=
    TW.mutFold hT1 (ResU.comp_empty_right _) (ResU.CompS.comm hc) (ResU.CompS.comm hW') hvW'
  have htg' : Tagged W' ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.comp_empty_right _) (ResU.CompS.comm hc) (ResU.CompS.comm hW') a).mpr ha)
    htg1
  have hL' : ResU.Lower W' (BoCa.BoLo.Heap.upd μ l v) :=
    (ResU.lower_swap_mut_own hown hvm hvo hW' hHmut hc hHown).mpr hLσ'
  refine ⟨W', hW', hT', htg', hL', fun hA => ?_⟩
  have hk : (shortCell A v).kind ≠ Kind.imm := by
    simp only [shortCell]; exact fun c => Kind.noConfusion c
  have hW'l : W'.get l = some (shortCell A v) :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hW') (ResU.single_get_self _ _) hk).2
  have hcon := hA l _ hW'l
  simp only [shortCell] at hcon
  exact lt_irrefl _ hcon

/-- At that world `TW.reb`'s premise fails for every `β` longer than the handler's cell. -/
theorem resume_frame_not_stratumLe {W : WRes} {A β : Life} (hA : A ⊏ β)
    (h : ¬ W.InStratum A) : ¬ StratumLe W β :=
  fun hs => h (hs A hA)

/-- …and `TW.rebEnd`'s, at every such `β`. -/
theorem resume_frame_not_inStratum {W : WRes} {A β : Life} (hA : A ⊏ β)
    (h : ¬ W.InStratum A) : ¬ W.InStratum β :=
  fun hs => h (fun m ψ e => CellU.InStratum.mono hA.le (hs m ψ e))

/-! ### What `TW.reb`'s premise is read for -/

/-- A reborrow keeps `FrameLife` at a record whose frame is no shorter than `β`:
`frameLife_reb_like` with its premise read where it is used. -/
theorem frameLife_reb_rec {W W' c w₀ : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} {β : Life} (hvW : ResU.Valid W)
    (hle : W.get le = some (CellU.immOf s v w₀ hs)) (hreb : ResU.Reb β w₀ c)
    (hW : ResU.CompS W c W') {p : FrameRec} {α : Life}
    (hex : ∀ ζ : CellU Loc Val, w₀.get p.le = some ζ → ζ.kind = Kind.imm)
    (hβα : (∃ m, LinLoc p m ∧ ∃ ζ : CellU Loc Val, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
      β ⊑ α)
    (h : FrameLife W p α) : FrameLife W' p α := by
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have newls : ∀ a', AgW W' a' → ∀ m (ψ : CellU Loc Val) s' x, a'.get m = some ψ →
      ψ.lsOf = some s' → s'.mem x →
      (∃ (ζ : CellU Loc Val) (t : LSet), aW.get m = some ζ ∧ ζ.lsOf = some t ∧ t.mem x) ∨
      (x = β ∧ ∃ ζ : CellU Loc Val, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) := by
    intro a' ha' m ψ s' x e hs' hx
    obtain ⟨aW', ac, haW', hac, hcomp⟩ := (AgW.split hW).mp ha'
    rw [AgW.functional haW' haW] at hcomp
    rcases ResU.CompR.lsOf_inv hcomp e hs' hx with h₁ | ⟨ξ, t₁, e₁, ht₁, hx₁⟩
    · exact Or.inl h₁
    · rcases img_ls haW hle hreb (fun _ _ e => e) hac e₁ ht₁ hx₁ with h₂ | ⟨rfl, -, h₃⟩
      · exact Or.inl h₂
      · exact Or.inr ⟨rfl, h₃⟩
  refine ⟨fun a' ha' ζ t e ht y hy => ?_, fun a' ha' m hm ψ s' e hs' x hx => ?_⟩
  · rcases newls a' ha' p.le ζ t y e ht hy with ⟨ζ', t', e', ht', hy'⟩ | ⟨-, ζ', e', k'⟩
    · exact h.1 aW haW ζ' t' e' ht' y hy'
    · exact absurd (hex ζ' e') k'
  · rcases newls a' ha' m ψ s' x e hs' hx with ⟨ζ', t', e', ht', hx'⟩ | ⟨rfl, ζ', e', k'⟩
    · exact h.2 aW haW m hm ζ' t' e' ht' x hx'
    · exact hβα ⟨m, hm, ζ', e', k'⟩

/-- **The records-only premise.** Every record proper whose lineage meets an exclusive location
of the reborrowed escrow `w₀` has its frame no shorter than `β`. -/
def RebRecLe (W : WRes) (ps : List FrameRec) (w₀ : WRes) (β : Life) : Prop :=
  ∀ p ∈ ps, ∀ α, FrameLife W p α →
    (∃ m, LinLoc p m ∧ ∃ ζ : CellU Loc Val, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) → β ⊑ α

/-- `StratumLe` gives the records-only premise: `frameLife_reb_like`'s derivation of `β ⊑ α`. -/
theorem rebRecLe_of_stratumLe {W : WRes} {ps rs : List FrameRec} (hT : TW W ps rs) (w₀ : WRes)
    {β : Life} (hβ : StratumLe W β) : RebRecLe W ps w₀ β := by
  intro p hp α h _
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨ζ, e, k, -⟩ := hT.inv.2.1 p hp aW haW
  obtain ⟨t, ht⟩ := lsOf_of_imm k
  refine le_of_not_gt fun hlt => ?_
  have h₁ : t.meet ⊐ α := CellU.sqsupset_of_lsOf ht (AgW.inStratum haW α (hβ α hlt) _ ζ e)
  rw [h.1 aW haW ζ t e ht t.meet t.meet_mem] at h₁
  exact lt_irrefl _ h₁

/-- `TW.reb` with `RebRecLe` in place of `StratumLe W β`: the re-entry the across-stops 6.150
needs, at a premise the handler's `mut` cell does not touch. A library change to `TW`. -/
def RebReentryRecN : Prop :=
  ∀ (W W' c : WRes) (ps rs : List FrameRec) (r : FrameRec) (le : Loc) (s : LSet) (β : Life)
    (hs : r.R.InStratum s.join) (x : LifeVar),
    TW W ps rs → r ∈ rs → W.get le = some (CellU.immOf s r.v r.R hs) → ¬ VFree x r.T →
    ResU.Reb β r.R c → vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v c →
    RebRecLe W ps r.R β → ResU.CompS W c W' → ResU.Valid W' → TW W' ps rs

/-- `RebReentryRecN` is weaker than `RebReentryN`. -/
theorem rebReentryRecN_of (h : RebReentryN) : RebReentryRecN :=
  fun W W' c ps rs r le s β hs x hT hr hle hx hreb hsh _ hc hv =>
    h W W' c ps rs r le s β hs x hT hr hle hx hreb hsh hc hv

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI

end
