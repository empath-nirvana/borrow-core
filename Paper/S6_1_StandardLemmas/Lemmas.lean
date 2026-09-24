import Paper.S5_Model.Definitions
import Support.Model.Algebra
import Support.Model.Cells
import Support.Model.Compatibility
import Support.Model.Composition
import Support.Model.Flattening
import Support.Model.Prelude
import Support.Model.WalkSplitting
import Support.Model.Walks

/-!
# [TR] §6.1 Standard Lemmas (pp. 6–8), Lemmas 6.1–6.15

*"There's no strict definition, but lemmas feel 'standard' when their statement
doesn't unfold resources or definitions, and don't include any particularly
unusual/custom operations."*

`[TR]` writes `▸◁` and `◐` for "either of `▸◂`/`▷◁`" and "either of `●`/`○`"; such a
lemma is stated once over a schema and instantiated at both.  §6.2's Lemmas 6.18,
6.20, 6.30, 6.31 and 6.36, and the row theorems `BigComp.perm` (row 5.56) and two of
row 5.67's, are declared here because the proofs of 6.7, 6.10 and 6.15 use them.

**Records.**  Each numbered result of `[TR]` §6 opens with a record: number, page
and status (`proved`, `proved*`, `variant`; legend in `Paper/INDEX.md`); the printed
statement, quoted; the printed proof, transcribed compactly in its own order; the
Lean declaration, its alias `TR.lemma_6_N` and its tag; and, where the Lean
statement reads the printed one in a way the tag does not say, a note.  A result
declared in an earlier subsection's file, because a printed proof there needs it,
keeps its record in its own subsection.  Declarations the paper does not print are
marked `[about ours]`.  `§N` citations are to `docs/adjudications.md`.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.1 · `[TR]` p. 6 · `proved`

> ρ₁ ▸◁ ρ₂ = ρ₂ ▸◁ ρ₁

**Printed proof, transcribed.** By definition, and the fact that `▸◁` is commutative on cells: at `▸◂` commutativity is immediate; at `▷◁` the first case is the previous one, and the second is immediate since sets are unordered.

**Lean.** `BoCa.Fig16.ResU.compat_comm_iff`, alias `TR.lemma_6_1`, tag `[as printed]`.

**Note.** `hC` is discharged at `▶◀` (`Fig16.ResU.compatS_comm_iff`) and at `⋈` (`Fig16.ResU.compatR_comm_iff`), `⋈` read as in §12.35.
-/
/-- `[TR]` Lemma 6.1 (p. 6).  `hC` is the print's "`▶◁` is commutative on cells".
`[as printed]` -/
theorem ResU.compat_comm_iff (C : CellU Loc Val → CellU Loc Val → Prop)
    (hC : ∀ ψ₁ ψ₂, C ψ₁ ψ₂ → C ψ₂ ψ₁) (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.Compat C ρ₁ ρ₂ ↔ ResU.Compat C ρ₂ ρ₁ :=
  ⟨ResU.Compat.comm hC, ResU.Compat.comm hC⟩

/-- `[TR]` Lemma 6.1 at `▶◀`.  `[as printed]` -/
theorem ResU.compatS_comm_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.CompatS ρ₁ ρ₂ ↔ ResU.CompatS ρ₂ ρ₁ :=
  ResU.compat_comm_iff _ (fun _ _ a => a.symm) ρ₁ ρ₂

/-- `[TR]` Lemma 6.1 at `⋈`.  `[as printed]` -/
theorem ResU.compatR_comm_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.CompatR ρ₁ ρ₂ ↔ ResU.CompatR ρ₂ ρ₁ :=
  ResU.compat_comm_iff _ (fun _ _ a => a.symm) ρ₁ ρ₂

end BoCa.Fig16

alias TR.lemma_6_1 := BoCa.Fig16.ResU.compat_comm_iff

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.2 · `[TR]` p. 6 · `proved`

> ρ₁ ◐ ρ₂ = ρ₂ ◐ ρ₁

**Printed proof, transcribed.** Composability follows from Lemma 6.1.  The rest follows from commutativity of composition on cells: at `●` it is immediate because `∪` is commutative; at `○` the first two cases are immediate, and the other two follow from noting that `ψᵢ` is invariant under changing the order of the cells.

**Lean.** `BoCa.Fig16.ResU.Comp.comm`, alias `TR.lemma_6_2`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.2 (p. 6), as an equality of graphs: definedness and value
together.  `[as printed]` -/
theorem ResU.Comp.comm {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R ψ₂ ψ₁)
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C ψ₂ ψ₁ ψ)
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) :
    ResU.Comp R C ρ₂ ρ₁ ρ := by
  refine ⟨ResU.Compat.comm hR h.1, fun l => ?_⟩
  rcases h.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC'⟩ <;> rw [e₁, e₂]
  · exact e
  · exact e
  · exact e
  · exact ⟨ψ, e, hC _ _ _ hC'⟩

end BoCa.Fig16

alias TR.lemma_6_2 := BoCa.Fig16.ResU.Comp.comm

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.3 · `[TR]` p. 6 · `proved`

> ρ₁ ◐ (ρ₂ ◐ ρ₃) = ρ₁ ◐ ρ₂ ◐ ρ₃

**Printed proof, transcribed.** Unfolding `◐`, the only interesting case is `ℓ ∈ dom(ρ₁) ∩ dom(ρ₂) ∩ dom(ρ₃)`.  At `●`, associativity of `∪`.  At `○`, split on `ρ₂ ○ ρ₃`: the first case is immediate; the second follows from `imm` always being preserved by `○`; in the third, if `ρ₁(ℓ)` is owned the `mut` is the result, if it is `mut` use associativity of `⊓` and `∧`, and if it is `imm` the result is `imm` either way; in the fourth, owned gives the `mut`, `mut` is immediate, `imm` gives `imm` either way; in the fifth, owned gives the `imm`, `mut` gives the `imm`, and `imm` combines the `imm`s.

**Lean.** `BoCa.Fig16.ResU.Comp.assoc`, alias `TR.lemma_6_3`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.3 (pp. 6–7), as the Kleene equality of the two partial
expressions.  `hR` and `hC` are the cell-level facts about `◐` the print uses.
`[as printed]` -/
theorem ResU.Comp.assoc {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) ↔ (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    (ρ₁ ρ₂ ρ₃ w : ResU Loc Val) :
    (∃ x, ResU.Comp R C ρ₂ ρ₃ x ∧ ResU.Comp R C ρ₁ x w) ↔
    (∃ y, ResU.Comp R C ρ₁ ρ₂ y ∧ ResU.Comp R C y ρ₃ w) := by
  constructor
  · rintro ⟨x, h₂₃, h₁x⟩
    exact ResU.Comp.assoc_left hR (fun a b c d => (hC a b c d).mp) h₂₃ h₁x
  · rintro ⟨y, h₁₂, hy₃⟩
    obtain ⟨x, hx, hw⟩ :=
      ResU.Comp.assoc_left (R := fun a b => R b a) (C := fun a b c => C b a c)
        (fun ψ₁ ψ₂ ψ h => hR ψ₂ ψ₁ ψ h)
        (fun ψ₁ ψ₂ ψ₃ ω h => (hC ψ₃ ψ₂ ψ₁ ω).mpr h)
        ((ResU.Comp.swap _ _ _).mpr h₁₂) ((ResU.Comp.swap _ _ _).mpr hy₃)
    exact ⟨x, (ResU.Comp.swap _ _ _).mp hx, (ResU.Comp.swap _ _ _).mp hw⟩

end BoCa.Fig16

alias TR.lemma_6_3 := BoCa.Fig16.ResU.Comp.assoc

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.4 · `[TR]` p. 7 · `proved`

> ρ ◐ ∅ = ρ

**Printed proof, transcribed.** By definition `dom(ρ) ∩ ∅ = ∅`, so `▸◁` holds immediately, and the result is trivially `ρ`.

**Lean.** `BoCa.Fig16.ResU.comp_empty_right`, alias `TR.lemma_6_4`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.4 (p. 7).  `[as printed]` -/
theorem ResU.comp_empty_right {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (ρ : ResU Loc Val) :
    ResU.Comp R C ρ PMap.empty ρ := by
  refine ⟨ResU.Compat.of_disjoint (fun _ => Or.inr rfl), fun l => ?_⟩
  show OptComp C (ρ.get l) none (ρ.get l)
  cases e : ρ.get l with
  | none => rfl
  | some ψ => rfl

end BoCa.Fig16

alias TR.lemma_6_4 := BoCa.Fig16.ResU.comp_empty_right

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.5 · `[TR]` p. 7 · `proved`

> If ✓ρ then ρ # ∅

**Printed proof, transcribed.** Immediate by definition.

**Lean.** `BoCa.Fig16.ResU.hash_empty_right`, alias `TR.lemma_6_5`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.5 (p. 7).  `[as printed]` -/
theorem ResU.hash_empty_right {ρ : ResU Loc Val} (h : ResU.Valid ρ) :
    ResU.Hash ρ PMap.empty :=
  ⟨ResU.Compat.of_disjoint (fun _ => Or.inr rfl), ρ, ResU.comp_empty_right ρ, h⟩

end BoCa.Fig16

alias TR.lemma_6_5 := BoCa.Fig16.ResU.hash_empty_right

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]`, for Lemma 6.6. -/
/-- `[TR]` Lemma 6.2 at `●`.  `[as printed]` -/
theorem ResU.CompS.comm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ) :
    ResU.CompS ρ₂ ρ₁ ρ :=
  ResU.Comp.comm (fun _ _ a => a.symm) (fun _ _ _ a => a.comm) h

/-- `[TR]` Lemma 6.6 (p. 7), one direction.  `[as printed]` -/
theorem ResU.hash_symm {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.Hash ρ₁ ρ₂) :
    ResU.Hash ρ₂ ρ₁ := by
  obtain ⟨hc, ρ, hcomp, hv⟩ := h
  exact ⟨hc.symm, ρ, hcomp.comm, hv⟩

/-!
## Lemma 6.6 · `[TR]` p. 7 · `proved`

> ρ₁ # ρ₂ if and only if ρ₂ # ρ₁

**Printed proof, transcribed.** From Lemma 6.2, and unfolding `⦇−⦈` with Lemmas 6.20 and 6.18.

**Lean.** `BoCa.Fig16.ResU.hash_symm_iff`, alias `TR.lemma_6_6`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.6 (p. 7).  `[as printed]` -/
theorem ResU.hash_symm_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.Hash ρ₁ ρ₂ ↔ ResU.Hash ρ₂ ρ₁ := ⟨ResU.hash_symm, ResU.hash_symm⟩

end BoCa.Fig16

alias TR.lemma_6_6 := BoCa.Fig16.ResU.hash_symm_iff

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.9 · `[TR]` p. 7 · `proved`

> ρ₁ ▸◂ ρ₂ iff ρ₁ ● ρ₂ is defined.

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.ResU.compS_defined_iff`, alias `TR.lemma_6_9`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.9 (p. 7).  The forward direction is `ResU.Comp`'s first
conjunct; the converse builds the composite (`ResU.compS_spec`).  Stated on the
carrier with `Res`'s `fin` mark (§12.33).  `[as printed]` -/
theorem ResU.compS_defined_iff (ρ₁ ρ₂ : ResU Loc Val) :
    (∃ ρ, ResU.CompS ρ₁ ρ₂ ρ) ↔ ResU.CompatS ρ₁ ρ₂ :=
  ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨_, ResU.compS_spec ρ₁ ρ₂ h⟩⟩

end BoCa.Fig16

alias TR.lemma_6_9 := BoCa.Fig16.ResU.compS_defined_iff

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### Lemma 6.36, ahead of its subsection

Printed in §6.2 (p. 12); its record and alias are in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`.
-/
/-- `[TR]` Lemma 6.36 (p. 12).  `hC` is the print's schematic operator,
discharged at both values by `CellU.compS_ne_imm` and `CellU.compR_ne_imm`; the
conclusion `ImmFree` is `ρ|imm = ∅` pointwise (`ResU.restrict_imm_empty_iff`).
`[as printed]` -/
theorem ExW.immFree {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.kind ≠ Kind.imm → ψ₂.kind ≠ Kind.imm →
        ψ.kind ≠ Kind.imm)
    {ρ σ : ResU Loc Val} (h : ExW R C ρ σ) : σ.ImmFree := by
  induction h using ExW.rec
    (motive_2 := fun _ w _ => ∀ p ∈ w, ResU.ImmFree p.2)
  case mk ρ' σ' nm b w hs hw hb hnm hσ ih =>
      refine ResU.ImmFree.comp hC hσ
        (ResU.ImmFree.comp hC hnm (ResU.immFree_restrict (fun e => Kind.noConfusion e))
          (ResU.immFree_restrict (fun e => Kind.noConfusion e)))
        (ResU.ImmFree.bigComp hC hb ?_)
      intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      exact ih p hp
  case nil ρ' p hp =>
      exact absurd hp (by simp)
  case cons ρ' e l w ψ hψ hk he hw ihe ihw p hp =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ihe
      · exact ihw p hp

/-! `[about ours]`, for Lemma 6.7. -/
/-- `[TR]` Lemma 6.36 at `●` (`[CONF]` Fig. 18a's `E⦇ρ′⦈_•`).  `[as printed]` -/
theorem ExS.immFree {ρ σ : ResU Loc Val} (h : ExS ρ σ) : σ.ImmFree :=
  ExW.immFree (fun ψ₁ ψ₂ ψ hc h₁ _ => CellU.compS_ne_imm ψ₁ ψ₂ ψ hc h₁) h

/-!
### Lemma 6.31, ahead of its subsection

Printed in §6.2 (p. 11); its record and alias are in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`.
-/
/-- `[TR]` Lemma 6.31 (p. 11), as an equality of graphs.  `[as printed]` -/
theorem ResU.compR_iff_compS {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.CompatS ρ₁ ρ₂)
    (σ : ResU Loc Val) : ResU.CompR ρ₁ ρ₂ σ ↔ ResU.CompS ρ₁ ρ₂ σ := by
  constructor
  · intro hr
    refine ⟨h, fun l => ?_⟩
    rcases hr.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩ <;> rw [e₁, e₂]
    · exact e
    · exact e
    · exact e
    · have hk := h l _ _ e₁ e₂
      have hψ : ψ = CellU.compS _ _ hk :=
        CellU.CompR.functional hC (CellU.CompR.strict hk)
      exact ⟨ψ, e, hψ ▸ CellU.compS_spec _ _ hk⟩
  · intro hs
    refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => CellU.CompatR.of_compatS (h l ψ₁ ψ₂ e₁ e₂), fun l => ?_⟩
    rcases hs.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩ <;> rw [e₁, e₂]
    · exact e
    · exact e
    · exact e
    · have hk := h l _ _ e₁ e₂
      have hψ : ψ = CellU.compS _ _ hk :=
        CellU.CompS.functional hC (CellU.compS_spec _ _ hk)
      exact ⟨ψ, e, hψ ▸ CellU.CompR.strict hk⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-! `[about ours]`, for Lemma 6.7. -/
/-- Exchanging the first two entries of the fold: Lemma 6.3, then 6.2 on the head
pair, then 6.3 again.
`[about ours: `[TR]` Lemmas 6.2 and 6.3 read at one step of the fold]` -/
theorem BigComp.swap (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {σ₁ σ₂ : ResU Loc Val} {l : List (ResU Loc Val)} {b : ResU Loc Val}
    (h : BigComp R C (σ₁ :: σ₂ :: l) b) : BigComp R C (σ₂ :: σ₁ :: l) b := by
  cases h with
  | cons h₁ hc₁ =>
      cases h₁ with
      | cons h₂ hc₂ =>
          obtain ⟨y, h₁₂, hy⟩ :=
            (ResU.Comp.assoc hR hC.assoc _ _ _ b).mp ⟨_, hc₂, hc₁⟩
          obtain ⟨x, hx, hb⟩ :=
            (ResU.Comp.assoc hR hC.assoc _ _ _ b).mpr
              ⟨y, ResU.Comp.comm_of_laws hR hC h₁₂, hy⟩
          exact BigComp.cons (BigComp.cons h₂ hx) hb

/-- Reordering the folded list preserves the result.
`[about ours: the order-independence of the fold, in transport form]` -/
theorem BigComp.of_perm (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {l l' : List (ResU Loc Val)} (hp : l.Perm l') :
    ∀ {b : ResU Loc Val}, BigComp R C l b → BigComp R C l' b := by
  induction hp with
  | nil => exact fun h => h
  | cons σ _ ih =>
      intro b h
      cases h with
      | cons hτ hc => exact BigComp.cons (ih hτ) hc
  | swap σ₁ σ₂ l => exact fun h => BigComp.swap hR hC h
  | trans _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)

/-!
### Row 5.56's theorem `BoCa.Fig16.BigComp.perm`, ahead of its file

Recorded in `Paper/S5_Model/Remarks.lean`.
-/
/-- The value of the fold does not depend on the order of the list: `[TR]` Lemmas
6.1–6.3, through `ResU.Comp.comm_of_laws` and `BigComp.swap`.
`[about ours: `BigComp` is the fold shape; the printed `⨀` is the order-free
operator this makes it]` -/
theorem BigComp.perm (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {l l' : List (ResU Loc Val)} (hp : l.Perm l') {b b' : ResU Loc Val}
    (h : BigComp R C l b) (h' : BigComp R C l' b') : b = b' :=
  BigComp.functional hC (BigComp.of_perm hR hC hp h) h'

/-! `[about ours]`, for Lemma 6.7. -/
/-- `BigComp.perm` in the form the walks use: two families indexed by the same
`ResU.Sites` set, agreeing location by location, fold to one value.
`[about ours: `ResU.Sites` is convention G6's index set]` -/
theorem BigComp.sites (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {ρ : ResU Loc Val} {k : Kind} {w w' : List (Loc × ResU Loc Val)}
    (hs : ResU.Sites ρ k (w.map Prod.fst)) (hs' : ResU.Sites ρ k (w'.map Prod.fst))
    (hval : ∀ p ∈ w, ∀ q ∈ w', p.1 = q.1 → p.2 = q.2)
    {b b' : ResU Loc Val}
    (h : BigComp R C (w.map Prod.snd) b) (h' : BigComp R C (w'.map Prod.snd) b') :
    b = b' :=
  BigComp.perm hR hC ((List.perm_of_keys hs.1 (hs.perm hs') hval).map Prod.snd) h h'

/-- `ex(ρ)_◐` is single-valued, so the graph `ExW` names `[TR]` p. 5's term
`ex(ρ)_◐` (`[CONF]` Fig. 18a's `E⦇ρ⦈_◐`).  Two derivations may enumerate `ρ`'s `mut`
locations in different orders, so the motive is pointwise and `BigComp.sites`
matches the lists up to permutation.
`[about ours: the print's `ex(ρ)_◐` is a term and `ExW` is its graph (G4)]` -/
theorem ExW.functional (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {ρ σ σ' : ResU Loc Val} (h : ExW R C ρ σ) (h' : ExW R C ρ σ') : σ = σ' := by
  refine ExW.rec (motive_1 := fun ρ σ _ => ∀ τ, ExW R C ρ τ → σ = τ)
    (motive_2 := fun ρ w _ => ∀ p ∈ w,
      ∃ ψ, ρ.get p.1 = some ψ ∧ ∀ e, ExW R C ψ.wit e → p.2 = e)
    ?mk ?nil ?cons h σ' h'
  -- The walk itself; `ih` is the family hypothesis of the same induction.
  case mk =>
    intro ρ₀ σ₀ nm b w hs _ hb hnm hσ ih τ hτ
    cases hτ with
    | mk hs' hw' hb' hnm' hσ' =>
        have hnn : nm = _ := ResU.Comp.functional hC.functional hnm hnm'
        have hbb : b = _ :=
          BigComp.sites hR hC hs hs'
            (fun p hp q hq hpq => by
              obtain ⟨ψ, hψ, hfun⟩ := ih p hp
              obtain ⟨ψ', hψ', he'⟩ := ExWits.mem hw' q hq
              rw [hpq, hψ'] at hψ
              cases Option.some.inj hψ
              exact hfun q.2 he') hb hb'
        exact ResU.Comp.functional hC.functional hσ (hnn ▸ hbb ▸ hσ')
  -- The empty family has no entry to disagree at.
  case nil => intro _ p hp; exact absurd hp (by simp)
  -- With a head, either the entry asked about is it — and the walk induction
  -- hypothesis fixes its value — or it is in the tail.
  case cons =>
    intro _ _ _ _ ψ hψ _ _ _ ihe ihw p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨ψ, hψ, fun e' he' => ihe e' he'⟩
    · exact ihw p hp

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `ex(ρ)_●` is a term.
`[about ours: `ExS` is the graph of `[TR]` p. 5's `ex(ρ)_●`]` -/
theorem ExS.functional {ρ σ σ' : ResU Loc Val} (h : ExS ρ σ) (h' : ExS ρ σ') :
    σ = σ' :=
  ExW.functional (fun _ _ _ hc => CellU.CompS.compat hc) ResU.compLawsS h h'

/-- `ex(ρ)_○` is a term.
`[about ours: `ExR` is the graph of `[TR]` p. 5's `ex(ρ)_○`]` -/
theorem ExR.functional {ρ σ σ' : ResU Loc Val} (h : ExR ρ σ) (h' : ExR ρ σ') :
    σ = σ' :=
  ExW.functional (fun _ _ ψ hc => ⟨ψ, hc⟩) ResU.compLawsR h h'

/-- `ag(ρ)` is single-valued, so the graph `AgW` names `[TR]` p. 5's term `ag(ρ)`
(`[CONF]` Fig. 18a's `A⦇ρ⦈`).
`[about ours: the print's `ag(ρ)` is a term and `AgW` is its graph (G4)]` -/
theorem AgW.functional {ρ σ σ' : ResU Loc Val} (h : AgW ρ σ) (h' : AgW ρ σ') :
    σ = σ' := by
  refine AgW.rec (motive_1 := fun ρ σ _ => ∀ τ, AgW ρ τ → σ = τ)
    (motive_2 := fun ρ w _ => ∀ p ∈ w,
      ∃ ψ, ρ.get p.1 = some ψ ∧ ∀ e, AgW ψ.wit e → p.2 = e)
    (motive_3 := fun ρ w _ => ∀ p ∈ w,
      ∃ ψ, ρ.get p.1 = some ψ ∧ ∀ e a q, ExR ψ.wit e → AgW ψ.wit a →
        ResU.CompR e a q → p.2 = q)
    ?mk ?nilM ?consM ?nilI ?consI h σ' h'
  case mk =>
    intro ρ₀ σ₀ a bm bi wm wi hsm hsi _ _ hbm hbi ha hσ ihm ihi τ hτ
    cases hτ with
    | mk hsm' hsi' hwm' hwi' hbm' hbi' ha' hσ' =>
        have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
          fun _ _ ψ hc => ⟨ψ, hc⟩
        have hbm₀ : bm = _ :=
          BigComp.sites hR ResU.compLawsR hsm hsm'
            (fun p hp q hq hpq => by
              obtain ⟨ψ, hψ, hfun⟩ := ihm p hp
              obtain ⟨ψ', hψ', hag'⟩ := AgWitsM.mem hwm' q hq
              rw [hpq, hψ'] at hψ
              cases Option.some.inj hψ
              exact hfun q.2 hag') hbm hbm'
        have hbi₀ : bi = _ :=
          BigComp.sites hR ResU.compLawsR hsi hsi'
            (fun p hp q hq hpq => by
              obtain ⟨ψ, hψ, hfun⟩ := ihi p hp
              obtain ⟨ψ', e', a', hψ', hex', hag', hc'⟩ := AgWitsI.mem hwi' q hq
              rw [hpq, hψ'] at hψ
              cases Option.some.inj hψ
              exact hfun e' a' q.2 hex' hag' hc') hbi hbi'
        have haa : a = _ := ResU.CompR.functional ha (hbm₀ ▸ ha')
        exact ResU.CompR.functional hσ (haa ▸ hbi₀ ▸ hσ')
  case nilM => intro _ p hp; exact absurd hp (by simp)
  case consM =>
    intro _ _ _ _ ψ hψ _ _ _ ihe ihw p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨ψ, hψ, fun e' hag => ihe e' hag⟩
    · exact ihw p hp
  case nilI => intro _ p hp; exact absurd hp (by simp)
  -- The `imm` entry is `ex(ρ′)_○ ○ ag(ρ′)`: the first factor is pinned by
  -- `ExR.functional`, the second by the induction hypothesis.
  case consI =>
    intro _ _ _ _ ψ hψ _ e a hex _ hc _ iha ihw p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨ψ, hψ, fun e' a' q hex' hag' hc' => ?_⟩
      have hee : e = e' := ExR.functional hex hex'
      have haa : a = a' := iha a' hag'
      exact ResU.CompR.functional hc (hee ▸ haa ▸ hc')
    · exact ihw p hp

/-- `⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)` (`[TR]` p. 5) is a term.
`[about ours: `ResU.Flat` is the graph of the printed `⦇ρ⦈` (G4)]` -/
theorem ResU.Flat.functional {ρ σ σ' : ResU Loc Val}
    (h : ρ.Flat σ) (h' : ρ.Flat σ') : σ = σ' := by
  obtain ⟨e, a, hex, hag, hc⟩ := h
  obtain ⟨e', a', hex', hag', hc'⟩ := h'
  have he : e = e' := ExS.functional hex hex'
  have ha : a = a' := AgW.functional hag hag'
  subst he; subst ha
  exact ResU.CompS.functional hc hc'

/-- `⟦ρ⟧ ≜ [ℓ ↦ v | ⟦⦇ρ⦈(ℓ)⟧ = v]` (`[TR]` p. 5) is a term.
`[about ours: `ResU.Lower` is the graph of the printed `⟦ρ⟧` (G4)]` -/
theorem ResU.Lower.functional {ρ : ResU Loc Val} {m m' : Loc → Option Val}
    (h : ρ.Lower m) (h' : ρ.Lower m') : m = m' := by
  obtain ⟨σ, hf, hm⟩ := h
  obtain ⟨σ', hf', hm'⟩ := h'
  cases ResU.Flat.functional hf hf'
  exact funext fun l => (hm l).trans (hm' l).symm

/-- The mirror of `ResU.CompS.get_left`. -/
theorem ResU.CompS.get_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ₂ : CellU Loc Val} (e₂ : ρ₂.get l = some ψ₂) :
    ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = ψ₂.kind ∧ ψ.wit = ψ₂.wit :=
  ResU.CompS.get_left (ResU.CompS.comm h) e₂

/-- The mirror of `ResU.CompS.get_left_of_ne_imm`. -/
theorem ResU.CompS.get_right_of_ne_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellU Loc Val} (e₂ : ρ₂.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ρ₁.get l = none ∧ ρ.get l = some ψ :=
  ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm h) e₂ hk

/-- `●` is an instance of `○` — `[TR]` Lemma 6.31 read left to right.
`[restricted: the `●`-implies-`○` half of the printed Kleene equality; the
other half is `ResU.compR_iff_compS`'s forward direction]` -/
theorem ResU.CompS.toCompR {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ) :
    ResU.CompR ρ₁ ρ₂ ρ :=
  (ResU.compR_iff_compS h.1 ρ).mpr h

/-- `(ρ₁ ● ρ₂)|ι = ρ₁|ι ○ ρ₂|ι`, the form 6.20 uses.
`[about ours: the printed `ρ|ι` and `●`, composed at `○` by 6.31]` -/
theorem ResU.CompS.restrictR {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (k : Kind) :
    ResU.CompR (ρ₁.restrict k) (ρ₂.restrict k) (ρ.restrict k) :=
  ResU.CompS.toCompR (ResU.CompS.restrict h k)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-- `⨀[σ]` is `σ` and nothing else, by [TR] Lemma 6.4.
`[about ours: `BigComp` is the fold shape for the printed `⨀`]` -/
theorem BigComp.singleton_iff (hC : ResU.CompLaws C) {σ τ : ResU Loc Val} :
    BigComp R C [σ] τ ↔ τ = σ := by
  constructor
  · intro h
    cases h with
    | cons ht hc =>
        cases ht
        exact ResU.Comp.functional hC.functional hc (ResU.comp_empty_right _)
  · rintro rfl
    exact BigComp.cons BigComp.nil (ResU.comp_empty_right _)

/-- `⨀[σ₁, σ₂] = σ₁ ◐ σ₂` — the two-element fold is the binary composition.
`[about ours: `BigComp` is the fold shape for the printed `⨀`]` -/
theorem BigComp.pair (hC : ResU.CompLaws C) {σ₁ σ₂ τ : ResU Loc Val} :
    BigComp R C [σ₁, σ₂] τ ↔ ResU.Comp R C σ₁ σ₂ τ := by
  constructor
  · intro h
    cases h with
    | cons ht hc =>
        obtain rfl := BigComp.singleton_iff hC |>.mp ht
        exact hc
  · intro h
    exact BigComp.cons (BigComp.singleton_iff hC |>.mpr rfl) h

/-- `⨀(l₁ ++ l₂) = ⨀l₁ ◐ ⨀l₂`, as a Kleene equality.
`[about ours: `BigComp` is the fold shape; the rebracketing is the printed
6.3 and the base case the printed 6.4]` -/
theorem BigComp.append (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {l₁ l₂ : List (ResU Loc Val)} {b : ResU Loc Val} :
    BigComp R C (l₁ ++ l₂) b ↔
      ∃ b₁ b₂, BigComp R C l₁ b₁ ∧ BigComp R C l₂ b₂ ∧ ResU.Comp R C b₁ b₂ b := by
  induction l₁ generalizing b with
  | nil =>
      refine ⟨fun h => ⟨PMap.empty, b, BigComp.nil, h, ResU.Comp.comm_of_laws hR hC (ResU.comp_empty_right b)⟩, ?_⟩
      rintro ⟨b₁, b₂, h₁, h₂, hc⟩
      cases h₁
      exact ResU.Comp.functional hC.functional
        (ResU.Comp.comm_of_laws hR hC (ResU.comp_empty_right b₂)) hc ▸ h₂
  | cons σ l ih =>
      constructor
      · intro h
        cases h with
        | cons hτ hcσ =>
            obtain ⟨b₁, b₂, k₁, k₂, kc⟩ := ih.mp hτ
            obtain ⟨y, hy₁, hy₂⟩ :=
              (ResU.Comp.assoc hR hC.assoc σ b₁ b₂ b).mp ⟨_, kc, hcσ⟩
            exact ⟨y, b₂, BigComp.cons k₁ hy₁, k₂, hy₂⟩
      · rintro ⟨b₁, b₂, h₁, h₂, hc⟩
        cases h₁ with
        | cons hτ hcσ =>
            obtain ⟨x, hx₁, hx₂⟩ :=
              (ResU.Comp.assoc hR hC.assoc σ _ b₂ b).mpr ⟨b₁, hcσ, hc⟩
            exact BigComp.cons (ih.mpr ⟨_, b₂, hτ, h₂, hx₁⟩) hx₂

/-- The exchange of the middle two factors, as a Kleene equality:

    (a₁ ◐ a₂) ◐ (b₁ ◐ b₂)  =  (a₁ ◐ b₁) ◐ (a₂ ◐ b₂).

`[about ours: the rearrangement [TR] 6.18's and 6.20's proofs perform on a
four-fold composite; the printed rows behind it are 6.2 and 6.3]` -/
theorem ResU.Comp.exchange₄ (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    (a₁ a₂ b₁ b₂ x : ResU Loc Val) :
    (∃ A B, ResU.Comp R C a₁ a₂ A ∧ ResU.Comp R C b₁ b₂ B ∧ ResU.Comp R C A B x) ↔
      (∃ S₁ S₂, ResU.Comp R C a₁ b₁ S₁ ∧ ResU.Comp R C a₂ b₂ S₂ ∧
        ResU.Comp R C S₁ S₂ x) := by
  -- Both sides are the fold of a four-element list; the two lists differ by the
  -- transposition of their middle entries.
  have hleft : (∃ A B, ResU.Comp R C a₁ a₂ A ∧ ResU.Comp R C b₁ b₂ B ∧
      ResU.Comp R C A B x) ↔ BigComp R C [a₁, a₂, b₁, b₂] x := by
    rw [show ([a₁, a₂, b₁, b₂] : List (ResU Loc Val)) = [a₁, a₂] ++ [b₁, b₂] from rfl,
      BigComp.append hR hC]
    exact ⟨fun ⟨A, B, hA, hB, hx⟩ =>
        ⟨A, B, BigComp.pair hC |>.mpr hA, BigComp.pair hC |>.mpr hB, hx⟩,
      fun ⟨A, B, hA, hB, hx⟩ =>
        ⟨A, B, BigComp.pair hC |>.mp hA, BigComp.pair hC |>.mp hB, hx⟩⟩
  have hright : (∃ S₁ S₂, ResU.Comp R C a₁ b₁ S₁ ∧ ResU.Comp R C a₂ b₂ S₂ ∧
      ResU.Comp R C S₁ S₂ x) ↔ BigComp R C [a₁, b₁, a₂, b₂] x := by
    rw [show ([a₁, b₁, a₂, b₂] : List (ResU Loc Val)) = [a₁, b₁] ++ [a₂, b₂] from rfl,
      BigComp.append hR hC]
    exact ⟨fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair hC |>.mpr h₁, BigComp.pair hC |>.mpr h₂, hx⟩,
      fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair hC |>.mp h₁, BigComp.pair hC |>.mp h₂, hx⟩⟩
  have hp : ([a₁, a₂, b₁, b₂] : List (ResU Loc Val)).Perm [a₁, b₁, a₂, b₂] :=
    List.Perm.cons a₁ (List.Perm.swap b₁ a₂ [b₂])
  rw [hleft, hright]
  exact ⟨BigComp.of_perm hR hC hp, BigComp.of_perm hR hC hp.symm⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The exchange at `●`, which [TR] 6.18 uses.
`[about ours: `ResU.Comp.exchange₄` instantiated at `●`]` -/
theorem ResU.CompS.exchange₄ (a₁ a₂ b₁ b₂ x : ResU Loc Val) :
    (∃ A B, ResU.CompS a₁ a₂ A ∧ ResU.CompS b₁ b₂ B ∧ ResU.CompS A B x) ↔
      (∃ S₁ S₂, ResU.CompS a₁ b₁ S₁ ∧ ResU.CompS a₂ b₂ S₂ ∧ ResU.CompS S₁ S₂ x) :=
  ResU.Comp.exchange₄ (fun _ _ _ hc => CellU.CompS.compat hc) ResU.compLawsS
    a₁ a₂ b₁ b₂ x

/-- The `own` and `mut` sites of `ρ₁ ● ρ₂` are those of `ρ₁` then those of `ρ₂`. -/
theorem ResU.Sites.append_of_compS {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {k : Kind} (hk : k ≠ Kind.imm) {d₁ d₂ : List Loc}
    (h₁ : ρ₁.Sites k d₁) (h₂ : ρ₂.Sites k d₂) : ρ.Sites k (d₁ ++ d₂) := by
  refine ⟨List.nodup_append.mpr ⟨h₁.1, h₂.1, ?_⟩, fun l => ?_⟩
  · rintro a ha b hb rfl
    obtain ⟨ψ₁, g₁, gk₁⟩ := (h₁.2 a).mp ha
    obtain ⟨ψ₂, g₂, -⟩ := (h₂.2 a).mp hb
    rw [ResU.CompatS.right_eq_none h.1 g₁ (fun e => hk (gk₁.symm.trans e))] at g₂
    exact absurd g₂ (by simp)
  · refine ⟨fun hm => ?_, fun hm => ?_⟩
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨ψ, g, gk⟩ := (h₁.2 l).mp hm
        exact ⟨ψ, (ResU.CompS.get_left_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2, gk⟩
      · obtain ⟨ψ, g, gk⟩ := (h₂.2 l).mp hm
        exact ⟨ψ, (ResU.CompS.get_right_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2, gk⟩
    · obtain ⟨ψ, g, gk⟩ := hm
      rcases ResU.CompS.get_split_of_ne_imm h g (fun e => hk (gk.symm.trans e)) with
        ⟨g₁, -⟩ | ⟨-, g₂⟩
      · exact List.mem_append.mpr (Or.inl ((h₁.2 l).mpr ⟨ψ, g₁, gk⟩))
      · exact List.mem_append.mpr (Or.inr ((h₂.2 l).mpr ⟨ψ, g₂, gk⟩))

/-- A family over the `own` or `mut` sites of `ρ₁ ● ρ₂` splits, up to order, into
one over `ρ₁`'s sites and one over `ρ₂`'s.
`[about ours: `ResU.Sites` is convention G6's index set]` -/
theorem ResU.Sites.split_pairs {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {k : Kind} (hk : k ≠ Kind.imm) {A : Type} {w : List (Loc × A)}
    (hs : ρ.Sites k (w.map Prod.fst)) :
    ∃ w₁ w₂ : List (Loc × A), w.Perm (w₁ ++ w₂) ∧
      ρ₁.Sites k (w₁.map Prod.fst) ∧ ρ₂.Sites k (w₂.map Prod.fst) ∧
      (∀ p ∈ w₁, p ∈ w) ∧ (∀ p ∈ w₂, p ∈ w) := by
  obtain ⟨w₁, w₂, hp, hm₁, hm₂⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = k) w
  -- The key lists inherit duplicate-freeness from `hs` along `hp`.
  have hnd : ((w₁.map Prod.fst) ++ (w₂.map Prod.fst)).Nodup := by
    rw [← List.map_append]
    exact (hp.map Prod.fst).nodup hs.1
  obtain ⟨nd₁, nd₂, -⟩ := List.nodup_append.mp hnd
  refine ⟨w₁, w₂, hp, ⟨nd₁, fun l => ⟨?_, ?_⟩⟩, ⟨nd₂, fun l => ⟨?_, ?_⟩⟩,
    fun p hp' => ((hm₁ p).mp hp').1, fun p hp' => ((hm₂ p).mp hp').1⟩
  · intro hl
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hl
    exact ((hm₁ p).mp hp').2
  · intro hl
    obtain ⟨ψ, g, gk⟩ := hl
    have hρ : ρ.get l = some ψ :=
      (ResU.CompS.get_left_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2
    obtain ⟨p, hp', hp1⟩ := List.mem_map.mp ((hs.2 l).mpr ⟨ψ, hρ, gk⟩)
    exact List.mem_map.mpr ⟨p, (hm₁ p).mpr ⟨hp', hp1 ▸ ⟨ψ, g, gk⟩⟩, hp1⟩
  · intro hl
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hl
    obtain ⟨hpw, hq⟩ := (hm₂ p).mp hp'
    obtain ⟨ψ, g, gk⟩ := (hs.2 p.1).mp (List.mem_map.mpr ⟨p, hpw, rfl⟩)
    rcases ResU.CompS.get_split_of_ne_imm h g (fun e => hk (gk.symm.trans e)) with
      ⟨g₁, -⟩ | ⟨-, g₂⟩
    · exact absurd ⟨ψ, g₁, gk⟩ hq
    · exact ⟨ψ, g₂, gk⟩
  · intro hl
    obtain ⟨ψ, g, gk⟩ := hl
    have hρ : ρ.get l = some ψ :=
      (ResU.CompS.get_right_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2
    have hnone : ρ₁.get l = none :=
      (ResU.CompS.get_right_of_ne_imm h g (fun e => hk (gk.symm.trans e))).1
    obtain ⟨p, hp', hp1⟩ := List.mem_map.mp ((hs.2 l).mpr ⟨ψ, hρ, gk⟩)
    refine List.mem_map.mpr ⟨p, (hm₂ p).mpr ⟨hp', ?_⟩, hp1⟩
    rintro ⟨χ, gχ, -⟩
    rw [hp1, hnone] at gχ
    exact absurd gχ (by simp)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-- The mirror of `ExWits.of_compS_left`. -/
theorem ExWits.of_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : ExWits R C ρ₂ w) : ExWits R C ρ w :=
  ExWits.of_compS_left (ResU.CompS.comm h) hw

/-- The mirror of `ExWits.to_compS_left`. -/
theorem ExWits.to_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₂ : List (Loc × ResU Loc Val)} (hw : ExWits R C ρ w)
    (hsub : ∀ p ∈ w₂, p ∈ w) (hs₂ : ρ₂.Sites Kind.mut (w₂.map Prod.fst)) :
    ExWits R C ρ₂ w₂ :=
  ExWits.to_compS_left (ResU.CompS.comm h) hw hsub hs₂

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### Lemma 6.18, ahead of its subsection

Printed in §6.2 (p. 8); its record and alias are in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`.
-/
/-- `[TR]` Lemma 6.18 (p. 8), as a Kleene equality of graphs (G4).  `[as printed]` -/
theorem ExS.split {ρ₁ ρ₂ ρ₁₂ w : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    ExS ρ₁₂ w ↔ ∃ σ₁ σ₂, ExS ρ₁ σ₁ ∧ ExS ρ₂ σ₂ ∧ ResU.CompS σ₁ σ₂ w := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompS ψ₁ ψ₂ ψ → CellU.CompatS ψ₁ ψ₂ :=
    fun _ _ _ hc => CellU.CompS.compat hc
  -- The printed second line, at `own` and at `mut`.
  have hown : ResU.CompS (ρ₁.restrict Kind.own) (ρ₂.restrict Kind.own)
      (ρ₁₂.restrict Kind.own) := ResU.CompS.restrict h₁₂ Kind.own
  have hmut : ResU.CompS (ρ₁.restrict Kind.mut) (ρ₂.restrict Kind.mut)
      (ρ₁₂.restrict Kind.mut) := ResU.CompS.restrict h₁₂ Kind.mut
  constructor
  · -- `ex(ρ₁₂)_●` is defined: cut its index set, its family and its fold in two,
    -- then exchange twice.
    intro h
    cases h with
    | mk hs hw hb hnm hσ =>
        rename_i u
        obtain ⟨u₁, u₂, hperm, hs₁, hs₂, hsub₁, hsub₂⟩ :=
          ResU.Sites.split_pairs h₁₂ Kind.mut_ne_imm hs
        have hperm' : (u.map Prod.snd).Perm (u₁.map Prod.snd ++ u₂.map Prod.snd) := by
          rw [← List.map_append]
          exact hperm.map Prod.snd
        obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ :=
          (BigComp.append hR ResU.compLawsS).mp
            (BigComp.of_perm hR ResU.compLawsS hperm' hb)
        -- The printed third line.
        obtain ⟨nm₁, nm₂, hnm₁, hnm₂, hnmc⟩ :=
          (ResU.CompS.exchange₄ _ _ _ _ _).mp ⟨_, _, hown, hmut, hnm⟩
        -- The printed fourth line.
        obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hσc⟩ :=
          (ResU.CompS.exchange₄ nm₁ nm₂ b₁ b₂ w).mp ⟨_, _, hnmc, hbc, hσ⟩
        exact ⟨σ₁, σ₂,
          ExW.mk hs₁ (ExWits.to_compS_left h₁₂ hw hsub₁ hs₁) hb₁ hnm₁ hσ₁,
          ExW.mk hs₂ (ExWits.to_compS_right h₁₂ hw hsub₂ hs₂) hb₂ hnm₂ hσ₂,
          hσc⟩
  · -- Both operands' walks are defined and compose: assemble the composite's
    -- index set, family and fold, then run the same two exchanges backwards.
    rintro ⟨σ₁, σ₂, h₁, h₂, hc⟩
    cases h₁ with
    | mk hs₁ hw₁ hb₁ hnm₁ hσ₁ =>
        rename_i u₁
        cases h₂ with
        | mk hs₂ hw₂ hb₂ hnm₂ hσ₂ =>
            rename_i u₂
            -- The printed fourth line, read right to left.
            obtain ⟨nm, b, hnmc, hbc, hσ⟩ :=
              (ResU.CompS.exchange₄ _ _ _ _ w).mpr ⟨σ₁, σ₂, hσ₁, hσ₂, hc⟩
            -- The printed third line, read right to left; the two composites it
            -- produces are `ρ₁₂|own` and `ρ₁₂|mut` by single-valuedness of `●`.
            obtain ⟨O, M, hO, hM, hOM⟩ :=
              (ResU.CompS.exchange₄ _ _ _ _ nm).mpr ⟨_, _, hnm₁, hnm₂, hnmc⟩
            obtain rfl : O = ρ₁₂.restrict Kind.own := ResU.CompS.functional hO hown
            obtain rfl : M = ρ₁₂.restrict Kind.mut := ResU.CompS.functional hM hmut
            refine ExW.mk (w := u₁ ++ u₂) ?_
              (ExWits.append (ExWits.of_compS_left h₁₂ hw₁)
                (ExWits.of_compS_right h₁₂ hw₂)) ?_ hOM hσ
            · rw [List.map_append]
              exact ResU.Sites.append_of_compS h₁₂ Kind.mut_ne_imm hs₁ hs₂
            · rw [List.map_append]
              exact (BigComp.append hR ResU.compLawsS).mpr ⟨_, _, hb₁, hb₂, hbc⟩

/-! `[about ours]`, for Lemma 6.7. -/
/-- The mirror of `AgWitsM.of_compS_left`. -/
theorem AgWitsM.of_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : AgWitsM ρ₂ w) : AgWitsM ρ w :=
  AgWitsM.of_compS_left (ResU.CompS.comm h) hw

/-- The mirror of `AgWitsI.of_compS_left`. -/
theorem AgWitsI.of_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : AgWitsI ρ₂ w) : AgWitsI ρ w :=
  AgWitsI.of_compS_left (ResU.CompS.comm h) hw

/-- The mirror of `AgWitsM.to_compS_left`. -/
theorem AgWitsM.to_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₂ : List (Loc × ResU Loc Val)} (hw : AgWitsM ρ w)
    (hsub : ∀ p ∈ w₂, p ∈ w) (hs₂ : ρ₂.Sites Kind.mut (w₂.map Prod.fst)) :
    AgWitsM ρ₂ w₂ :=
  AgWitsM.to_compS_left (ResU.CompS.comm h) hw hsub hs₂

/-- The mirror of `AgWitsI.to_compS_left`. -/
theorem AgWitsI.to_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₂ : List (Loc × ResU Loc Val)} (hw : AgWitsI ρ w)
    (hsub : ∀ p ∈ w₂, p ∈ w) (hs₂ : ρ₂.Sites Kind.imm (w₂.map Prod.fst)) :
    AgWitsI ρ₂ w₂ :=
  AgWitsI.to_compS_left (ResU.CompS.comm h) hw hsub hs₂

/-- The value the `imm` half pairs with a location depends only on the cell's
witness, so [TR] 6.20's `ρ₁ ∩ ρ₂` entry is one term.
`[about ours: `AgWitsI` is the family relation; the printed 6.19 is
`ResU.flatR_idem`]` -/
theorem AgWitsI.value_functional {ρ ρ' : ResU Loc Val}
    {w w' : List (Loc × ResU Loc Val)} (h : AgWitsI ρ w) (h' : AgWitsI ρ' w')
    {p q : Loc × ResU Loc Val} (hp : p ∈ w) (hq : q ∈ w')
    {ψ χ : CellU Loc Val} (hψ : ρ.get p.1 = some ψ) (hχ : ρ'.get q.1 = some χ)
    (hwit : ψ.wit = χ.wit) : p.2 = q.2 := by
  obtain ⟨ψ₀, g, -, e, a, hex, hag, hc⟩ := AgWitsI.iff_mem.mp h p hp
  obtain ⟨χ₀, g', -, e', a', hex', hag', hc'⟩ := AgWitsI.iff_mem.mp h' q hq
  rw [hψ] at g; obtain rfl := Option.some.inj g
  rw [hχ] at g'; obtain rfl := Option.some.inj g'
  have hee : e = e' := ExR.functional hex (by rw [← hwit] at hex'; exact hex')
  have haa : a = a' := AgW.functional hag (by rw [← hwit] at hag'; exact hag')
  exact ResU.CompR.functional hc (hee ▸ haa ▸ hc')

/-- The `imm` locations of `ρ₁ ● ρ₂` are the union, not the disjoint union, of
those of `ρ₁` and `ρ₂`.
`[about ours: the printed `▶◀` and `●` read at the `imm` tag]` -/
theorem ResU.CompS.imm_site_iff {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (l : Loc) :
    (∃ ψ, ρ.get l = some ψ ∧ ψ.kind = Kind.imm) ↔
      ((∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm) ∨
        (∃ ψ, ρ₂.get l = some ψ ∧ ψ.kind = Kind.imm)) := by
  constructor
  · rintro ⟨ψ, g, gk⟩
    rcases ResU.Comp.get h l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
        ⟨χ₁, χ₂, χ, f₁, -, -, hC⟩
    · rw [g] at f; exact absurd f (by simp)
    · obtain rfl : ψ = χ := Option.some.inj (g.symm.trans f)
      exact Or.inl ⟨ψ, f₁, gk⟩
    · obtain rfl : ψ = χ := Option.some.inj (g.symm.trans f)
      exact Or.inr ⟨ψ, f₂, gk⟩
    · exact Or.inl ⟨χ₁, f₁, (CellU.CompatS.kinds (CellU.CompS.compat hC)).1⟩
  · rintro (⟨ψ, g, gk⟩ | ⟨ψ, g, gk⟩)
    · obtain ⟨χ, f, fk, -⟩ := ResU.CompS.get_left h g
      exact ⟨χ, f, fk.trans gk⟩
    · obtain ⟨χ, f, fk, -⟩ := ResU.CompS.get_right h g
      exact ⟨χ, f, fk.trans gk⟩

/-- A family over the `imm` sites of `ρ₁ ● ρ₂` splits into blocks over `ρ₁`
alone, `ρ₂` alone, and both: [TR] 6.20's inclusion-exclusion at the index sets.
`[about ours: `ResU.Sites` is convention G6's index set]` -/
theorem ResU.Sites.split_pairs_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {A : Type} {w : List (Loc × A)} (hs : ρ.Sites Kind.imm (w.map Prod.fst)) :
    ∃ wa wb wc : List (Loc × A), w.Perm (wa ++ (wb ++ wc)) ∧
      ρ₁.Sites Kind.imm ((wa ++ wc).map Prod.fst) ∧
      ρ₂.Sites Kind.imm ((wb ++ wc).map Prod.fst) ∧
      (∀ p ∈ wa, p ∈ w) ∧ (∀ p ∈ wb, p ∈ w) ∧ (∀ p ∈ wc, p ∈ w) := by
  classical
  -- `u` is the part of `w` lying over `ρ₁` and `wb` the rest; `u` then splits by
  -- whether the location lies over `ρ₂` as well.
  obtain ⟨u, wb, hpu, hmu, hmb⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm) w
  obtain ⟨wc, wa, hpc, hmc, hma⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₂.get l = some ψ ∧ ψ.kind = Kind.imm) u
  have hperm : w.Perm (wa ++ (wb ++ wc)) := by
    refine hpu.trans ((hpc.append_right wb).trans ?_)
    rw [List.append_assoc, ← List.append_assoc wa wb wc]
    exact List.perm_append_comm
  have hsubw : ∀ p ∈ u, p ∈ w := fun p hp => ((hmu p).mp hp).1
  have hsuba : ∀ p ∈ wa, p ∈ w := fun p hp => hsubw p ((hma p).mp hp).1
  have hsubb : ∀ p ∈ wb, p ∈ w := fun p hp => ((hmb p).mp hp).1
  have hsubc : ∀ p ∈ wc, p ∈ w := fun p hp => hsubw p ((hmc p).mp hp).1
  -- Duplicate-freeness of the three key blocks, and their pairwise
  -- disjointness, travel from `hs` along the permutation.
  have hkeys : (w.map Prod.fst).Perm
      ((wa.map Prod.fst) ++ ((wb.map Prod.fst) ++ (wc.map Prod.fst))) := by
    have hm := hperm.map Prod.fst
    rwa [List.map_append, List.map_append] at hm
  obtain ⟨nda, ndbc, hdis⟩ := List.nodup_append.mp (hkeys.nodup hs.1)
  obtain ⟨ndb, ndc, hdbc⟩ := List.nodup_append.mp ndbc
  have hcov : ∀ p ∈ w, (∃ ψ, ρ₁.get p.1 = some ψ ∧ ψ.kind = Kind.imm) ∨
      (∃ ψ, ρ₂.get p.1 = some ψ ∧ ψ.kind = Kind.imm) := fun p hp =>
    (ResU.CompS.imm_site_iff h p.1).mp ((hs.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩))
  refine ⟨wa, wb, wc, hperm, ⟨?_, fun l => ⟨?_, ?_⟩⟩, ⟨?_, fun l => ⟨?_, ?_⟩⟩,
    hsuba, hsubb, hsubc⟩
  · rw [List.map_append]
    exact List.nodup_append.mpr ⟨nda, ndc, fun a ha b hb =>
      hdis a ha b (List.mem_append.mpr (Or.inr hb))⟩
  · intro hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_append.mp hp with hp | hp
    · exact ((hmu p).mp ((hma p).mp hp).1).2
    · exact ((hmu p).mp ((hmc p).mp hp).1).2
  · intro hl
    obtain ⟨p, hp, hp1⟩ :=
      List.mem_map.mp ((hs.2 l).mpr ((ResU.CompS.imm_site_iff h l).mpr (Or.inl hl)))
    have hpu' : p ∈ u := (hmu p).mpr ⟨hp, hp1 ▸ hl⟩
    refine List.mem_map.mpr ⟨p, ?_, hp1⟩
    by_cases hq : ∃ ψ, ρ₂.get p.1 = some ψ ∧ ψ.kind = Kind.imm
    · exact List.mem_append.mpr (Or.inr ((hmc p).mpr ⟨hpu', hq⟩))
    · exact List.mem_append.mpr (Or.inl ((hma p).mpr ⟨hpu', hq⟩))
  · rw [List.map_append]
    exact List.nodup_append.mpr ⟨ndb, ndc, hdbc⟩
  · intro hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨hpw, hnq⟩ := (hmb p).mp hp
      exact (hcov p hpw).resolve_left hnq
    · exact ((hmc p).mp hp).2
  · intro hl
    obtain ⟨p, hp, hp1⟩ :=
      List.mem_map.mp ((hs.2 l).mpr ((ResU.CompS.imm_site_iff h l).mpr (Or.inr hl)))
    refine List.mem_map.mpr ⟨p, ?_, hp1⟩
    by_cases hq : ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm
    · exact List.mem_append.mpr (Or.inr ((hmc p).mpr ⟨(hmu p).mpr ⟨hp, hp1 ▸ hq⟩, hp1 ▸ hl⟩))
    · exact List.mem_append.mpr (Or.inl ((hmb p).mpr ⟨hp, hp1 ▸ hq⟩))

/-- `⨀(l ++ (m ++ m)) = ⨀(l ++ m)` at `○`, from `ResU.compR_self`
(`ρ ○ ρ = ρ`; [TR] Lemma 6.19 is its instance at `⦇ρ⦈_○`).
`[about ours: `BigComp` is the fold shape]` -/
theorem BigComp.dupR {l m : List (ResU Loc Val)} {x : ResU Loc Val} :
    BigComp CellU.CompatR CellU.CompR (l ++ (m ++ m)) x ↔
      BigComp CellU.CompatR CellU.CompR (l ++ m) x := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  rw [BigComp.append hR ResU.compLawsR, BigComp.append hR ResU.compLawsR]
  refine ⟨fun ⟨L, Y, hL, hY, hx⟩ => ?_, fun ⟨L, M, hL, hM, hx⟩ => ?_⟩
  · obtain ⟨M₁, M₂, hM₁, hM₂, hMc⟩ := (BigComp.append hR ResU.compLawsR).mp hY
    obtain rfl : M₁ = M₂ := BigComp.functional ResU.compLawsR hM₁ hM₂
    obtain rfl : Y = M₁ := ResU.CompR.functional hMc (ResU.compR_self M₁)
    exact ⟨L, Y, hL, hM₁, hx⟩
  · exact ⟨L, M, hL,
      (BigComp.append hR ResU.compLawsR).mpr ⟨M, M, hM, hM, ResU.compR_self M⟩, hx⟩

/-- At `○`, a block already present in `l` up to order may be appended again:
`⨀(l ++ d) = ⨀l`.
`[about ours: `BigComp` is the fold shape; the printed 6.19 is
`ResU.flatR_idem`]` -/
theorem BigComp.dup_of_perm {l m d : List (ResU Loc Val)} (hp : l.Perm (m ++ d))
    {x : ResU Loc Val} :
    BigComp CellU.CompatR CellU.CompR (l ++ d) x ↔
      BigComp CellU.CompatR CellU.CompR l x := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have h₁ : (l ++ d).Perm (m ++ (d ++ d)) := by
    rw [← List.append_assoc]
    exact hp.append_right d
  constructor
  · intro h
    exact BigComp.of_perm hR ResU.compLawsR hp.symm
      (BigComp.dupR.mp (BigComp.of_perm hR ResU.compLawsR h₁ h))
  · intro h
    exact BigComp.of_perm hR ResU.compLawsR h₁.symm
      (BigComp.dupR.mpr (BigComp.of_perm hR ResU.compLawsR hp h))

/-- The exchange of the middle two factors at `○`, which [TR] 6.20 uses.
`[about ours: `ResU.Comp.exchange₄` instantiated at `○`]` -/
theorem ResU.CompR.exchange₄ (a₁ a₂ b₁ b₂ x : ResU Loc Val) :
    (∃ A B, ResU.CompR a₁ a₂ A ∧ ResU.CompR b₁ b₂ B ∧ ResU.CompR A B x) ↔
      (∃ S₁ S₂, ResU.CompR a₁ b₁ S₁ ∧ ResU.CompR a₂ b₂ S₂ ∧ ResU.CompR S₁ S₂ x) :=
  ResU.Comp.exchange₄ (fun _ _ ψ hc => ⟨ψ, hc⟩) ResU.compLawsR a₁ a₂ b₁ b₂ x

/-- The composite's `imm` family, assembled from the operands': `w₂a` is `ρ₂`'s
family off `ρ₁`, `w₂c` its family on `ρ₁`, and `w₁c` the block of `ρ₁`'s family
over the same locations, a permutation of `w₂c`.
`[about ours: `ResU.Sites` is convention G6's index set and `AgWitsI` the family;
6.20's inclusion-exclusion in the assembling direction]` -/
theorem AgWitsI.assemble {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w₁ w₂ : List (Loc × ResU Loc Val)}
    (hs₁ : ρ₁.Sites Kind.imm (w₁.map Prod.fst)) (hw₁ : AgWitsI ρ₁ w₁)
    (hs₂ : ρ₂.Sites Kind.imm (w₂.map Prod.fst)) (hw₂ : AgWitsI ρ₂ w₂) :
    ∃ w₂a w₂c w₁r w₁c : List (Loc × ResU Loc Val),
      w₂.Perm (w₂a ++ w₂c) ∧ w₁.Perm (w₁r ++ w₁c) ∧ w₁c.Perm w₂c ∧
      ρ.Sites Kind.imm ((w₁ ++ w₂a).map Prod.fst) ∧
      AgWitsI ρ (w₁ ++ w₂a) := by
  classical
  -- `w₂c` is the shared block of `ρ₂`'s family, `w₁c` the matching block of
  -- `ρ₁`'s.  Each is cut by asking whether the *other* operand is `imm` there.
  obtain ⟨w₂c, w₂a, hp2, hm2c, hm2a⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm) w₂
  obtain ⟨w₁c, w₁r, hp1, hm1c, -⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₂.get l = some ψ ∧ ψ.kind = Kind.imm) w₁
  have hperm2 : w₂.Perm (w₂a ++ w₂c) := hp2.trans List.perm_append_comm
  have hperm1 : w₁.Perm (w₁r ++ w₁c) := hp1.trans List.perm_append_comm
  have hsub2a : ∀ p ∈ w₂a, p ∈ w₂ := fun p hp => ((hm2a p).mp hp).1
  -- Key lists inherit duplicate-freeness from the two `ResU.Sites`.
  have hk2 : ((w₂a.map Prod.fst) ++ (w₂c.map Prod.fst)).Nodup := by
    rw [← List.map_append]
    exact ((hperm2.map Prod.fst)).nodup hs₂.1
  obtain ⟨nd2a, nd2c, -⟩ := List.nodup_append.mp hk2
  have hk1 : ((w₁r.map Prod.fst) ++ (w₁c.map Prod.fst)).Nodup := by
    rw [← List.map_append]
    exact ((hperm1.map Prod.fst)).nodup hs₁.1
  obtain ⟨-, nd1c, -⟩ := List.nodup_append.mp hk1
  -- Both shared blocks are indexed by the locations `imm` in *both* operands.
  have hkey : ∀ l, l ∈ w₁c.map Prod.fst ↔ l ∈ w₂c.map Prod.fst := by
    intro l
    constructor
    · intro hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      obtain ⟨hp1, hq2⟩ := (hm1c p).mp hp
      obtain ⟨q, hq, hq1⟩ := List.mem_map.mp ((hs₂.2 p.1).mpr hq2)
      exact List.mem_map.mpr ⟨q, (hm2c q).mpr ⟨hq, hq1 ▸
        (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp1, rfl⟩)⟩, hq1⟩
    · intro hl
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      obtain ⟨hq2, hp1⟩ := (hm2c q).mp hq
      obtain ⟨p, hp, hp1'⟩ := List.mem_map.mp ((hs₁.2 q.1).mpr hp1)
      exact List.mem_map.mpr ⟨p, (hm1c p).mpr ⟨hp, hp1' ▸
        (hs₂.2 q.1).mp (List.mem_map.mpr ⟨q, hq2, rfl⟩)⟩, hp1'⟩
  -- At a shared location the two cells have one witness, so the two families
  -- pair the same value with it.
  have hval : ∀ p ∈ w₁c, ∀ q ∈ w₂c, p.1 = q.1 → p.2 = q.2 := by
    intro p hp q hq hpq
    obtain ⟨hp1, -⟩ := (hm1c p).mp hp
    obtain ⟨hq2, -⟩ := (hm2c q).mp hq
    obtain ⟨ψ₁, g₁, -⟩ := (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp1, rfl⟩)
    obtain ⟨ψ₂, g₂, -⟩ := (hs₂.2 q.1).mp (List.mem_map.mpr ⟨q, hq2, rfl⟩)
    exact AgWitsI.value_functional hw₁ hw₂ hp1 hq2 g₁ g₂
      (ResU.CompatS.wit_of_overlap h.1 g₁ (hpq ▸ g₂))
  refine ⟨w₂a, w₂c, w₁r, w₁c, hperm2, hperm1,
    List.perm_of_keys_mem nd1c nd2c hkey hval, ⟨?_, fun l => ⟨?_, ?_⟩⟩, ?_⟩
  · -- `w₁`'s keys and `w₂a`'s are disjoint: every `w₁` key is `imm` in `ρ₁`,
    -- and no `w₂a` key is.
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hs₁.1, nd2a, fun a ha b hb hab => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact ((hm2a q).mp hq).2 (hab ▸ (hs₁.2 a).mp ha)
  · intro hl
    rw [List.map_append] at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact (ResU.CompS.imm_site_iff h l).mpr (Or.inl ((hs₁.2 l).mp hl))
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      exact (ResU.CompS.imm_site_iff h q.1).mpr
        (Or.inr ((hs₂.2 q.1).mp (List.mem_map.mpr ⟨q, hsub2a q hq, rfl⟩)))
  · intro hl
    rw [List.map_append]
    rcases (ResU.CompS.imm_site_iff h l).mp hl with hq | hq
    · exact List.mem_append.mpr (Or.inl ((hs₁.2 l).mpr hq))
    · by_cases hq₁ : ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm
      · exact List.mem_append.mpr (Or.inl ((hs₁.2 l).mpr hq₁))
      · obtain ⟨q, hq', hq1⟩ := List.mem_map.mp ((hs₂.2 l).mpr hq)
        exact List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨q, (hm2a q).mpr ⟨hq', hq1 ▸ hq₁⟩, hq1⟩))
  · exact AgWitsI.append (AgWitsI.of_compS_left h hw₁)
      (AgWitsI.of_compS_right h (AgWitsI.subset hw₂ hsub2a))

/-- The exchange when one factor is shared, at `○`, as a Kleene equality:

    A ◐ (B ◐ C)  =  (A ◐ C) ◐ (B ◐ C).

The repeated `C` folds to one copy (`BigComp.dup_of_perm`).
`[about ours: the rearrangement 6.20's proof performs on the `imm` families;
the printed rows behind it are 6.2, 6.3 and 6.19]` -/
theorem ResU.CompR.exchange₃dup (A B C x : ResU Loc Val) :
    (∃ Y, ResU.CompR B C Y ∧ ResU.CompR A Y x) ↔
      (∃ S₁ S₂, ResU.CompR A C S₁ ∧ ResU.CompR B C S₂ ∧ ResU.CompR S₁ S₂ x) := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have hleft : (∃ Y, ResU.CompR B C Y ∧ ResU.CompR A Y x) ↔
      BigComp CellU.CompatR CellU.CompR [A, B, C] x := by
    constructor
    · rintro ⟨Y, hY, hx⟩
      exact BigComp.cons (BigComp.pair ResU.compLawsR |>.mpr hY) hx
    · intro h
      cases h with
      | cons ht hx => exact ⟨_, BigComp.pair ResU.compLawsR |>.mp ht, hx⟩
  have hright : (∃ S₁ S₂, ResU.CompR A C S₁ ∧ ResU.CompR B C S₂ ∧ ResU.CompR S₁ S₂ x) ↔
      BigComp CellU.CompatR CellU.CompR [A, C, B, C] x := by
    rw [show ([A, C, B, C] : List (ResU Loc Val)) = [A, C] ++ [B, C] from rfl,
      BigComp.append hR ResU.compLawsR]
    exact ⟨fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair ResU.compLawsR |>.mpr h₁,
          BigComp.pair ResU.compLawsR |>.mpr h₂, hx⟩,
      fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair ResU.compLawsR |>.mp h₁,
          BigComp.pair ResU.compLawsR |>.mp h₂, hx⟩⟩
  -- `[A, C, B, C]` is `[A, B, C]` with its own last entry appended again.
  have hp : ([A, C, B, C] : List (ResU Loc Val)).Perm ([A, B, C] ++ [C]) :=
    List.Perm.cons A (List.Perm.swap B C [C])
  have hd : BigComp CellU.CompatR CellU.CompR ([A, B, C] ++ [C]) x ↔
      BigComp CellU.CompatR CellU.CompR [A, B, C] x :=
    BigComp.dup_of_perm (m := [A, B]) (List.Perm.refl _)
  rw [hleft, hright]
  exact ⟨fun h => BigComp.of_perm hR ResU.compLawsR hp.symm (hd.mpr h),
    fun h => hd.mp (BigComp.of_perm hR ResU.compLawsR hp h)⟩

/-!
### Lemma 6.20, ahead of its subsection

Printed in §6.2 (p. 9); its record and alias are in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`.
-/
/-- `[TR]` Lemma 6.20 (p. 9), as a Kleene equality of graphs (G4); the hypothesis
is at `●` and the conclusion at `○`.  `[as printed]` -/
theorem AgW.split {ρ₁ ρ₂ ρ₁₂ w : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    AgW ρ₁₂ w ↔ ∃ σ₁ σ₂, AgW ρ₁ σ₁ ∧ AgW ρ₂ σ₂ ∧ ResU.CompR σ₁ σ₂ w := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have himm : ResU.CompR (ρ₁.restrict Kind.imm) (ρ₂.restrict Kind.imm)
      (ρ₁₂.restrict Kind.imm) := ResU.CompS.restrictR h₁₂ Kind.imm
  constructor
  · intro h
    cases h with
    | mk hsm hsi hwm hwi hbm hbi ha hσ =>
        rename_i wm wi
        -- The `mut` index set is cut in two, as in 6.18.
        obtain ⟨wm₁, wm₂, hpm, hsm₁, hsm₂, hsubm₁, hsubm₂⟩ :=
          ResU.Sites.split_pairs h₁₂ Kind.mut_ne_imm hsm
        have hpm' : (wm.map Prod.snd).Perm (wm₁.map Prod.snd ++ wm₂.map Prod.snd) := by
          rw [← List.map_append]
          exact hpm.map Prod.snd
        obtain ⟨bm₁, bm₂, hbm₁, hbm₂, hbmc⟩ :=
          (BigComp.append hR ResU.compLawsR).mp
            (BigComp.of_perm hR ResU.compLawsR hpm' hbm)
        -- The `imm` index set is cut in three: `ρ₁` alone, `ρ₂` alone, shared.
        obtain ⟨wa, wb, wc, hpi, hsi₁, hsi₂, hsuba, hsubb, hsubc⟩ :=
          ResU.Sites.split_pairs_imm h₁₂ hsi
        have hpi' : (wi.map Prod.snd).Perm
            (wa.map Prod.snd ++ (wb.map Prod.snd ++ wc.map Prod.snd)) := by
          rw [← List.map_append, ← List.map_append]
          exact hpi.map Prod.snd
        obtain ⟨A, X, hA, hX, hAX⟩ :=
          (BigComp.append hR ResU.compLawsR).mp
            (BigComp.of_perm hR ResU.compLawsR hpi' hbi)
        obtain ⟨B, Cc, hB, hCc, hBC⟩ := (BigComp.append hR ResU.compLawsR).mp hX
        -- The shared block is handed to both sides; this is 6.19's step.
        obtain ⟨bi₁, bi₂, hS₁, hS₂, hbic⟩ :=
          (ResU.CompR.exchange₃dup A B Cc _).mp ⟨X, hBC, hAX⟩
        have hbi₁ : BigComp CellU.CompatR CellU.CompR ((wa ++ wc).map Prod.snd) bi₁ := by
          rw [List.map_append]
          exact (BigComp.append hR ResU.compLawsR).mpr ⟨A, Cc, hA, hCc, hS₁⟩
        have hbi₂ : BigComp CellU.CompatR CellU.CompR ((wb ++ wc).map Prod.snd) bi₂ := by
          rw [List.map_append]
          exact (BigComp.append hR ResU.compLawsR).mpr ⟨B, Cc, hB, hCc, hS₂⟩
        -- The two exchanges of the print's final regrouping.
        obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ :=
          (ResU.CompR.exchange₄ _ _ _ _ _).mp ⟨_, _, himm, hbmc, ha⟩
        obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hσc⟩ :=
          (ResU.CompR.exchange₄ a₁ a₂ bi₁ bi₂ w).mp ⟨_, _, hac, hbic, hσ⟩
        refine ⟨σ₁, σ₂,
          AgW.mk hsm₁ hsi₁ (AgWitsM.to_compS_left h₁₂ hwm hsubm₁ hsm₁)
            (AgWitsI.to_compS_left h₁₂ hwi ?_ hsi₁) hbm₁ hbi₁ ha₁ hσ₁,
          AgW.mk hsm₂ hsi₂ (AgWitsM.to_compS_right h₁₂ hwm hsubm₂ hsm₂)
            (AgWitsI.to_compS_right h₁₂ hwi ?_ hsi₂) hbm₂ hbi₂ ha₂ hσ₂,
          hσc⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hsuba p hp
          · exact hsubc p hp
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hsubb p hp
          · exact hsubc p hp
  · rintro ⟨σ₁, σ₂, h₁, h₂, hc⟩
    cases h₁ with
    | mk hsm₁ hsi₁ hwm₁ hwi₁ hbm₁ hbi₁ ha₁ hσ₁ =>
        rename_i wm₁ wi₁
        cases h₂ with
        | mk hsm₂ hsi₂ hwm₂ hwi₂ hbm₂ hbi₂ ha₂ hσ₂ =>
            rename_i wm₂ wi₂
            -- The two exchanges, read right to left.
            obtain ⟨a, bi, hac, hbic, hσ⟩ :=
              (ResU.CompR.exchange₄ _ _ _ _ w).mpr ⟨σ₁, σ₂, hσ₁, hσ₂, hc⟩
            obtain ⟨I, bm, hI, hbmc, ha⟩ :=
              (ResU.CompR.exchange₄ _ _ _ _ a).mpr ⟨_, _, ha₁, ha₂, hac⟩
            obtain rfl : I = ρ₁₂.restrict Kind.imm := ResU.CompR.functional hI himm
            -- The composite's `imm` family, assembled with its shared block named.
            obtain ⟨w₂a, w₂c, w₁r, w₁c, hperm2, hperm1, hcperm, hsi, hwi⟩ :=
              AgWitsI.assemble h₁₂ hsi₁ hwi₁ hsi₂ hwi₂
            refine AgW.mk (wm := wm₁ ++ wm₂) (wi := wi₁ ++ w₂a) ?_ hsi
              (AgWitsM.append (AgWitsM.of_compS_left h₁₂ hwm₁)
                (AgWitsM.of_compS_right h₁₂ hwm₂)) hwi ?_ ?_ ha hσ
            · rw [List.map_append]
              exact ResU.Sites.append_of_compS h₁₂ Kind.mut_ne_imm hsm₁ hsm₂
            · rw [List.map_append]
              exact (BigComp.append hR ResU.compLawsR).mpr ⟨_, _, hbm₁, hbm₂, hbmc⟩
            · -- `wi₁ ++ w₂a` folds to `bi` because the block `w₂c` that `ρ₂`'s
              -- family adds is, entry for entry, the block `w₁c` of `ρ₁`'s.
              have hsplit : (wi₁ ++ w₂a).Perm ((w₁r ++ w₂a) ++ w₂c) := by
                refine (hperm1.append_right w₂a).trans ?_
                refine ((hcperm.append_left w₁r).append_right w₂a).trans ?_
                rw [List.append_assoc, List.append_assoc]
                exact List.Perm.append_left w₁r List.perm_append_comm
              have hdup : ((wi₁ ++ w₂a).map Prod.snd).Perm
                  (((w₁r ++ w₂a).map Prod.snd) ++ (w₂c.map Prod.snd)) := by
                rw [← List.map_append]
                exact hsplit.map Prod.snd
              refine BigComp.dup_of_perm hdup |>.mp ?_
              rw [List.map_append, List.append_assoc, ← List.map_append]
              exact (BigComp.append hR ResU.compLawsR).mpr ⟨_, _, hbi₁,
                BigComp.of_perm hR ResU.compLawsR (hperm2.map Prod.snd) hbi₂, hbic⟩

/-! `[about ours]`, for Lemma 6.7. -/
/-- `⦇ρ₁ ● ρ₂⦈ = ex(ρ₁)_● ● ex(ρ₂)_● ● (ag(ρ₁) ○ ag(ρ₂))`, as a Kleene equality:
the expansion [TR] 6.15's proof (p. 8) obtains from 6.18 and 6.20.
`[about ours: the equation [TR] 6.15's proof obtains from 6.18 and 6.20; it
carries no numbered row of its own]` -/
theorem ResU.Flat.split {ρ₁ ρ₂ ρ₁₂ σ : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    ResU.Flat ρ₁₂ σ ↔ ∃ e₁ e₂ e a₁ a₂ a,
      ExS ρ₁ e₁ ∧ ExS ρ₂ e₂ ∧ ResU.CompS e₁ e₂ e ∧
      AgW ρ₁ a₁ ∧ AgW ρ₂ a₂ ∧ ResU.CompR a₁ a₂ a ∧ ResU.CompS e a σ := by
  constructor
  · rintro ⟨e, a, he, ha, hc⟩
    obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split h₁₂).mp he
    obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ := (AgW.split h₁₂).mp ha
    exact ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩
  · rintro ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩
    exact ⟨e, a, (ExS.split h₁₂).mpr ⟨e₁, e₂, he₁, he₂, hec⟩,
      (AgW.split h₁₂).mpr ⟨a₁, a₂, ha₁, ha₂, hac⟩, hc⟩

/-!
### Row 5.67's theorem `BoCa.Fig16.ResU.CompatS.disjoint_of_immFree`, ahead of its file

Recorded in `Paper/S5_Model/Remarks.lean`.
-/
/-- `▸◂` with an `imm`-free resource is disjointness.
`[about ours: the step "Since ρ|imm = ∅, ρ ▸◂ ρ′ implies dom(ρ) ∩ dom(ρ′) = ∅"
of `[TR]` Lemma 6.30's proof, with `dom` written pointwise]` -/
theorem ResU.CompatS.disjoint_of_immFree {ρ ρ' : ResU Loc Val}
    (himm : ρ.ImmFree) (h : ResU.CompatS ρ ρ') (l : Loc) :
    ρ.get l = none ∨ ρ'.get l = none := by
  cases e : ρ.get l with
  | none => exact Or.inl rfl
  | some ψ =>
      cases e' : ρ'.get l with
      | none => exact Or.inr rfl
      | some ψ' => exact absurd (CellU.CompatS.kinds (h l ψ ψ' e e')).1 (himm l ψ e)

/-!
### Lemma 6.30, ahead of its subsection

Printed in §6.2 (p. 11); its record and alias are in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`.
-/
/-- `[TR]` Lemma 6.30 (p. 11).  `ρ|imm = ∅` is carried literally, as
`ResU.restrict` against `PMap.empty`.
`[as printed]` (the printed `ρ₁ ○ ρ₂` appears as its graph — G4) -/
theorem ResU.CompatS.of_compR_left {ρ ρ₁ ρ₂ r : ResU Loc Val}
    (himm : ρ.restrict Kind.imm = PMap.empty)
    (hr : ResU.CompR ρ₁ ρ₂ r) (h : ResU.CompatS ρ r) :
    ResU.CompatS ρ ρ₁ ∧ ResU.CompatS ρ ρ₂ := by
  have hfree : ρ.ImmFree := (ResU.restrict_imm_empty_iff ρ).mp himm
  have hdisj := ResU.CompatS.disjoint_of_immFree hfree h
  refine ⟨ResU.Compat.of_disjoint fun l => ?_, ResU.Compat.of_disjoint fun l => ?_⟩ <;>
    rcases hdisj l with e | e
  · exact Or.inl e
  · exact Or.inr ((ResU.Comp.eq_none_iff hr l).mp e).1
  · exact Or.inl e
  · exact Or.inr ((ResU.Comp.eq_none_iff hr l).mp e).2

/-! `[about ours]`, for Lemma 6.7. -/
/-- 6.35's "by the previous constraint": if an `imm`-free composite is `▸◂`
something, so is each of its factors.
`[about ours: the second of the composability constraints `[TR]` Lemma 6.35's
proof lists, with `dom` written pointwise]` -/
theorem ResU.CompatS.of_compS_left_immFree {ρ₁ ρ₂ ρ σ : ResU Loc Val}
    (himm : ρ.ImmFree) (h : ResU.CompS ρ₁ ρ₂ ρ) (hc : ResU.CompatS ρ σ) :
    ResU.CompatS ρ₁ σ ∧ ResU.CompatS ρ₂ σ := by
  have hdisj := ResU.CompatS.disjoint_of_immFree himm hc
  refine ⟨ResU.Compat.of_disjoint fun l => ?_, ResU.Compat.of_disjoint fun l => ?_⟩ <;>
    rcases hdisj l with e | e
  · exact Or.inl ((ResU.Comp.eq_none_iff h l).mp e).1
  · exact Or.inr e
  · exact Or.inl ((ResU.Comp.eq_none_iff h l).mp e).2
  · exact Or.inr e

/-- The display and the composability constraints of `[TR]` Lemma 6.35's proof
(p. 12): from `⦇ρ₁ ● ρ₂⦈ = σ`, the factorisation
`ex(ρ₁)_● ● ex(ρ₂)_● ● (ag(ρ₁) ○ ag(ρ₂))` and the composites
`⦇ρᵢ⦈ = ex(ρᵢ)_● ● ag(ρᵢ)`.
`[about ours: the body of `[TR]` Lemma 6.35's proof, stated with the walks and
the compositions as graphs (G4) so that its intermediate values survive]` -/
theorem ResU.Flat.split_factors {ρ₁ ρ₂ ρ₁₂ σ : ResU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hσ : ResU.Flat ρ₁₂ σ) :
    ∃ e₁ e₂ e a₁ a₂ a σ₁ σ₂,
      ExS ρ₁ e₁ ∧ ExS ρ₂ e₂ ∧ ResU.CompS e₁ e₂ e ∧
      AgW ρ₁ a₁ ∧ AgW ρ₂ a₂ ∧ ResU.CompR a₁ a₂ a ∧ ResU.CompS e a σ ∧
      ResU.CompS e₁ a₁ σ₁ ∧ ResU.CompS e₂ a₂ σ₂ := by
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩ :=
    (ResU.Flat.split h).mp hσ
  -- `(ex(ρ₁)_● ● ex(ρ₂)_●)|imm = ∅`, by 6.36 at each factor.
  have himm : e.ImmFree := ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)
  -- `ex(ρ₁)_● ● ex(ρ₂)_● ▸◂ ag(ρᵢ)`, by 6.30 on `ag(ρ₁) ○ ag(ρ₂)`.
  obtain ⟨hca₁, hca₂⟩ :=
    ResU.CompatS.of_compR_left ((ResU.restrict_imm_empty_iff e).mpr himm) hac hc.1
  -- `ex(ρᵢ)_● ▸◂ ag(ρᵢ)`, "by the previous constraint".
  obtain ⟨hd₁, -⟩ := ResU.CompatS.of_compS_left_immFree himm hec hca₁
  obtain ⟨-, hd₂⟩ := ResU.CompatS.of_compS_left_immFree himm hec hca₂
  -- …"which implies `⦇ρᵢ⦈` is defined", by 6.9.
  obtain ⟨σ₁, hσ₁⟩ := (ResU.compS_defined_iff e₁ a₁).mpr hd₁
  obtain ⟨σ₂, hσ₂⟩ := (ResU.compS_defined_iff e₂ a₂).mpr hd₂
  exact ⟨e₁, e₂, e, a₁, a₂, a, σ₁, σ₂, he₁, he₂, hec, ha₁, ha₂, hac, hc, hσ₁, hσ₂⟩

/-- One half of `[TR]` Lemma 6.7 (p. 7): if `⟦ρ₁ ● ρ₂⟧` is defined then so are
`⟦ρ₁⟧` and `⟦ρ₂⟧`, and it is their union.  The proof is the print's case analysis,
through `ResU.Flat.split_factors`.
`[restricted: the definedness-and-value half of the printed 6.7's Kleene
equality, with the printed `ρ₁ # ρ₂` weakened to `⟦ρ₁ ● ρ₂⟧` being defined]` -/
theorem ResU.Lower.split_left {ρ₁ ρ₂ ρ₁₂ : ResU Loc Val} {m : Loc → Option Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hm : ResU.Lower ρ₁₂ m) :
    ∃ m₁ m₂, ResU.Lower ρ₁ m₁ ∧ ResU.Lower ρ₂ m₂ ∧ MemUnion m₁ m₂ m := by
  obtain ⟨σ, hσ, hval⟩ := hm
  obtain ⟨e₁, e₂, e, a₁, a₂, a, σ₁, σ₂, he₁, he₂, hec, ha₁, ha₂, hac, hc, hσ₁, hσ₂⟩ :=
    ResU.Flat.split_factors h hσ
  have himm : e.ImmFree := ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)
  -- The exclusive part and the aliasable part never meet.
  have hdisj := ResU.CompatS.disjoint_of_immFree himm hc.1
  refine ⟨fun l => (σ₁.get l).map CellU.erase, fun l => (σ₂.get l).map CellU.erase,
    ⟨σ₁, ⟨e₁, a₁, he₁, ha₁, hσ₁⟩, fun _ => rfl⟩,
    ⟨σ₂, ⟨e₂, a₂, he₂, ha₂, hσ₂⟩, fun _ => rfl⟩, ?_⟩
  intro l
  show OptUnion ((σ₁.get l).map CellU.erase) ((σ₂.get l).map CellU.erase) (m l)
  rcases hdisj l with hnoE | hnoA
  · obtain ⟨he₁l, he₂l⟩ := (ResU.Comp.eq_none_iff hec l).mp hnoE
    rw [hval l, ResU.Comp.get_of_left_none hc hnoE,
      ResU.Comp.get_of_left_none hσ₁ he₁l, ResU.Comp.get_of_left_none hσ₂ he₂l]
    exact optUnion_map_erase (fun _ _ _ hr => CellU.CompR.erase hr) (hac.2 l)
  · obtain ⟨ha₁l, ha₂l⟩ := (ResU.Comp.eq_none_iff hac l).mp hnoA
    rw [hval l, ResU.Comp.get_of_right_none hc hnoA,
      ResU.Comp.get_of_right_none hσ₁ ha₁l, ResU.Comp.get_of_right_none hσ₂ ha₂l]
    refine optUnion_map_erase (fun _ _ _ hs => ⟨?_, (CellU.CompS.erase hs).1⟩) (hec.2 l)
    exact (CellU.CompS.erase hs).1.symm.trans (CellU.CompS.erase hs).2

/-!
## Lemma 6.7 · `[TR]` p. 7 · `proved`

> If ρ₁ # ρ₂ then ⟦ρ₁ ● ρ₂⟧ = ⟦ρ₁⟧ ∪ ⟦ρ₂⟧.

**Printed proof, transcribed.** By Lemmas 6.20 and 6.18 with Lemma 6.36, every `ℓ ∈ dom(⟦ρ₁ ● ρ₂⟧)` is in `dom(ex(ρ₁)_●)`, in `dom(ex(ρ₂)_●)`, or in `dom(ag(ρ₁) ○ ag(ρ₂))`.  In the first two cases we are done; in the third we are done unless `ℓ ∈ dom(ag(ρ₁)) ∩ dom(ag(ρ₂))`, and then the definition of `○` gives `⟦ag(ρ₁)(ℓ)⟧ = ⟦ag(ρ₂)(ℓ)⟧`.

**Lean.** `BoCa.Fig16.ResU.Lower.split`, alias `TR.lemma_6_7`, tag `[as printed]`.

**Note.** The printed `=` between partial terms is the `↔` of the two graphs at a common result (G4); `∪` is `Fig16.MemUnion`, whose overlap clause asserts the agreement the proof's last sentence establishes.
-/
/-- `[TR]` Lemma 6.7 (p. 7).  The forward half is `ResU.Lower.split_left`.
`[as printed]` (as a Kleene equality between graphs — G4; the printed
`ρ₁ ● ρ₂` is `ResU.CompS ρ₁ ρ₂ ρ₁₂`, whose own first conjunct is `#`'s `▸◂`) -/
theorem ResU.Lower.split {ρ₁ ρ₂ ρ₁₂ : ResU Loc Val} {m : Loc → Option Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hh : ResU.Hash ρ₁ ρ₂) :
    ResU.Lower ρ₁₂ m ↔
      ∃ m₁ m₂, ResU.Lower ρ₁ m₁ ∧ ResU.Lower ρ₂ m₂ ∧ MemUnion m₁ m₂ m := by
  refine ⟨ResU.Lower.split_left h, ?_⟩
  rintro ⟨m₁, m₂, k₁, k₂, ku⟩
  obtain ⟨-, ρ, hρ, σ, hσ⟩ := hh
  cases ResU.CompS.functional hρ h
  have hlow : ResU.Lower ρ₁₂ (fun l => (σ.get l).map CellU.erase) :=
    ⟨σ, hσ, fun _ => rfl⟩
  obtain ⟨n₁, n₂, j₁, j₂, ju⟩ := ResU.Lower.split_left h hlow
  cases ResU.Lower.functional j₁ k₁
  cases ResU.Lower.functional j₂ k₂
  cases MemUnion.functional ju ku
  exact hlow

end BoCa.Fig16

alias TR.lemma_6_7 := BoCa.Fig16.ResU.Lower.split

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.8 · `[TR]` p. 7 · `proved`

> If ⟦ρ₂⟧ = ⟦ρ₃⟧ and ρ₁ # ρ₂ and ρ₁ # ρ₃ then ⟦ρ₁ ● ρ₂⟧ = ⟦ρ₁ ● ρ₃⟧

**Printed proof, transcribed.** Immediate by Lemma 6.7, rewriting with `⟦ρ₂⟧ = ⟦ρ₃⟧`.

**Lean.** `BoCa.Fig16.ResU.Lower.congr`, alias `TR.lemma_6_8`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.8 (p. 7).  The hypothesis `⟦ρ₂⟧ = ⟦ρ₃⟧` relates both
lowerings to one memory `m`.
`[as printed]` (as Kleene equalities between graphs — G4) -/
theorem ResU.Lower.congr {ρ₁ ρ₂ ρ₃ ρ₁₂ ρ₁₃ : ResU Loc Val} {m w : Loc → Option Val}
    (hm₂ : ResU.Lower ρ₂ m) (hm₃ : ResU.Lower ρ₃ m)
    (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hh₂ : ResU.Hash ρ₁ ρ₂)
    (h₁₃ : ResU.CompS ρ₁ ρ₃ ρ₁₃) (hh₃ : ResU.Hash ρ₁ ρ₃) :
    ResU.Lower ρ₁₂ w ↔ ResU.Lower ρ₁₃ w := by
  refine Iff.trans (ResU.Lower.split h₁₂ hh₂)
    (Iff.trans ?_ (ResU.Lower.split h₁₃ hh₃).symm)
  constructor
  · rintro ⟨n₁, n₂, k₁, k₂, ku⟩
    cases ResU.Lower.functional k₂ hm₂
    exact ⟨n₁, m, k₁, hm₃, ku⟩
  · rintro ⟨n₁, n₂, k₁, k₂, ku⟩
    cases ResU.Lower.functional k₂ hm₃
    exact ⟨n₁, m, k₁, hm₂, ku⟩

end BoCa.Fig16

alias TR.lemma_6_8 := BoCa.Fig16.ResU.Lower.congr

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.10 · `[TR]` p. 7 · `proved`

> If ✓(ρ₁ ● ρ₂) then ✓ρ₁ and ✓ρ₂

**Printed proof, transcribed.** By unfolding and applying Lemmas 6.18 and 6.20.

**Lean.** `BoCa.Fig16.ResU.Valid.split`, alias `TR.lemma_6_10`, tag `[as printed]`.

**Note.** p. 5's `✓ρ ≜ ⦇ρ⦈ defined` makes 6.10 and 6.35 one proposition, so one declaration is both; its proof is 6.35's.
-/
/-- `[TR]` Lemma 6.10 (p. 7), which is also `[TR]` Lemma 6.35 (p. 12).
`[as printed]` (both of them; the printed `ρ₁ ● ρ₂` appears as its graph — G4) -/
theorem ResU.Valid.split {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (hv : ρ.Valid) : ρ₁.Valid ∧ ρ₂.Valid := by
  obtain ⟨σ, hσ⟩ := hv
  obtain ⟨e₁, e₂, e, a₁, a₂, a, σ₁, σ₂, he₁, he₂, -, ha₁, ha₂, -, -, hσ₁, hσ₂⟩ :=
    ResU.Flat.split_factors h hσ
  exact ⟨⟨σ₁, e₁, a₁, he₁, ha₁, hσ₁⟩, ⟨σ₂, e₂, a₂, he₂, ha₂, hσ₂⟩⟩

end BoCa.Fig16

alias TR.lemma_6_10 := BoCa.Fig16.ResU.Valid.split

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]`, for Lemma 6.11. -/
/-- `[TR]` Lemma 6.3 at `●`.  `[as printed]` -/
theorem ResU.CompS.assoc (ρ₁ ρ₂ ρ₃ w : ResU Loc Val) :
    (∃ x, ResU.CompS ρ₂ ρ₃ x ∧ ResU.CompS ρ₁ x w) ↔
    (∃ y, ResU.CompS ρ₁ ρ₂ y ∧ ResU.CompS y ρ₃ w) :=
  ResU.Comp.assoc (fun _ _ _ h => CellU.CompS.compat h)
    (fun ψ₁ ψ₂ ψ₃ ω => CellU.compS_assoc ψ₁ ψ₂ ψ₃ ω) ρ₁ ρ₂ ρ₃ w

/-!
## Lemma 6.11 · `[TR]` p. 7 · `proved`

> If ρ₁ ● ρ₂ # ρ₃ then ρ₁ # ρ₃ and ρ₂ # ρ₃

**Printed proof, transcribed.** Definedness of `ρ₁ ● ρ₃` and `ρ₂ ● ρ₃` follows from unfolding definitions; `✓(ρ₁ ● ρ₃)` and `✓(ρ₂ ● ρ₃)` follow from Lemma 6.10 applied to `✓(ρ₁ ● ρ₂ ● ρ₃)`.

**Lean.** `BoCa.Fig16.ResU.Hash.split`, alias `TR.lemma_6_11`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.11 (p. 7).
`[as printed]` (the printed `ρ₁ ● ρ₂` appears as its graph — G4) -/
theorem ResU.Hash.split {ρ₁ ρ₂ ρ₁₂ ρ₃ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ₁₂)
    (hh : ResU.Hash ρ₁₂ ρ₃) : ResU.Hash ρ₁ ρ₃ ∧ ResU.Hash ρ₂ ρ₃ := by
  obtain ⟨-, ρ, hρ, hv⟩ := hh
  obtain ⟨x, hx, hρx⟩ := (ResU.CompS.assoc ρ₁ ρ₂ ρ₃ ρ).mpr ⟨ρ₁₂, h, hρ⟩
  obtain ⟨y, hy, hρy⟩ := (ResU.CompS.assoc ρ₂ ρ₁ ρ₃ ρ).mpr ⟨ρ₁₂, ResU.CompS.comm h, hρ⟩
  exact ⟨⟨hy.1, y, hy, (ResU.Valid.split hρy hv).2⟩,
    ⟨hx.1, x, hx, (ResU.Valid.split hρx hv).2⟩⟩

end BoCa.Fig16

alias TR.lemma_6_11 := BoCa.Fig16.ResU.Hash.split

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.12 · `[TR]` p. 7 · `proved`

> If ρ₁ ● ρ₂ and ρ₁ ● ρ₃ and ρ₂ ○ ρ₃ are all defined, then so is ρ₁ ● (ρ₂ ○ ρ₃).

**Printed proof, transcribed.** The own-or-mut cells of `ρ₁` are disjoint from those of `ρ₂` and `ρ₃`, hence from those of `ρ₂ ○ ρ₃`, because `○` introduces no new own-or-mut cells.  At a location where `(ρ₂ ○ ρ₃)(ℓ)` is an `imm` cell, either (1) both operands are `imm` cells over one value and one witness, `imm(α₁, v, ρ)` and `imm(α₂, v, ρ)`, so the composite is `imm(α₁ ∪ α₂, v, ρ)` and is composable with `ρ₁(ℓ)` by `ρ₁ ▸◂ ρ₂`; or (2) one operand is `imm` and the other own-or-mut (without loss of generality `ρ₂`'s), so `ℓ ∉ dom(ρ₁)` and `ℓ` is not in the overlap.  So the `imm` cells of `ρ₁` agree on overlap with those of `ρ₂ ○ ρ₃` up to lifetimes.

**Lean.** `BoCa.Fig16.ResU.compatS_of_compR`, alias `TR.lemma_6_12`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.12 (p. 7), with "defined" stated as `▸◂`, which is
definedness by Lemma 6.9 (`ResU.compS_defined_iff`).
`[as printed]` (the printed `ρ₂ ○ ρ₃` appears as its graph — G4) -/
theorem ResU.compatS_of_compR {ρ₁ ρ₂ ρ₃ r : ResU Loc Val}
    (h₁₂ : ResU.CompatS ρ₁ ρ₂) (h₁₃ : ResU.CompatS ρ₁ ρ₃)
    (h₂₃ : ResU.CompR ρ₂ ρ₃ r) : ResU.CompatS ρ₁ r := by
  intro l ψ₁ χ e₁ e
  rcases h₂₃.get l with ⟨-, -, e₀⟩ | ⟨ψ, f₁, -, e₀⟩ | ⟨ψ, -, f₂, e₀⟩ |
      ⟨ψ₂, ψ₃, ψ, f₁, f₂, e₀, hC⟩
  · rw [e₀] at e; exact absurd e (by simp)
  · rw [e₀] at e; cases Option.some.inj e; exact h₁₂ l _ _ e₁ f₁
  · rw [e₀] at e; cases Option.some.inj e; exact h₁₃ l _ _ e₁ f₂
  · rw [e₀] at e
    cases Option.some.inj e
    exact CellU.CompatS.of_compR_left (h₁₂ l _ _ e₁ f₁) hC

end BoCa.Fig16

alias TR.lemma_6_12 := BoCa.Fig16.ResU.compatS_of_compR

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.13 · `[TR]` p. 7 · `proved`

> If ρ₁ ● ρ₂ and ρ₁ ● ρ₃ and ρ₂ ● ρ₃ are all defined, then so is ρ₁ ● ρ₂ ● ρ₃.

**Printed proof, transcribed.** The own-or-mut cells of `ρ₁, ρ₂, ρ₃` are pairwise disjoint, hence mutually disjoint, and the `imm` cells pairwise agree up to lifetimes, hence mutually agree up to lifetimes.

**Lean.** `BoCa.Fig16.ResU.compatS_of_pairwise`, alias `TR.lemma_6_13`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.13 (p. 7), with the conclusion stated as `(ρ₁ ● ρ₂) ▸◂ ρ₃`,
which is definedness by Lemma 6.9.  `[as printed]` -/
theorem ResU.compatS_of_pairwise {ρ₁ ρ₂ ρ₃ σ : ResU Loc Val}
    (h₁₂ : ResU.CompS ρ₁ ρ₂ σ) (h₁₃ : ResU.CompatS ρ₁ ρ₃)
    (h₂₃ : ResU.CompatS ρ₂ ρ₃) : ResU.CompatS σ ρ₃ := by
  intro l χ ψ₃ hχ h₃
  rcases h₁₂.get l with ⟨-, -, e⟩ | ⟨ψ, e₁, -, e⟩ | ⟨ψ, -, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩
  · rw [e] at hχ; exact absurd hχ (by simp)
  · rw [e] at hχ; cases Option.some.inj hχ; exact h₁₃ l _ _ e₁ h₃
  · rw [e] at hχ; cases Option.some.inj hχ; exact h₂₃ l _ _ e₂ h₃
  · rw [e] at hχ
    cases Option.some.inj hχ
    obtain ⟨s₁, s₂, v, τ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := hC
    obtain ⟨t₁, t₃, w, τ', m₁, m₃, g₁, g₃⟩ := h₁₃ l _ _ e₁ h₃
    obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj (f₁.symm.trans g₁)
    subst hv; subst hρ
    exact ⟨s₁ ∪ s₂, t₃, _, _, k₃, m₃, f₃, g₃⟩

end BoCa.Fig16

alias TR.lemma_6_13 := BoCa.Fig16.ResU.compatS_of_pairwise

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### Row 5.67's theorem `BoCa.Fig16.CellU.compatR_iff`, ahead of its file

Recorded in `Paper/S5_Model/Remarks.lean`.
-/
/-- `⋈` holds exactly when the two cells share a value, and a witness wherever
both have one.  The right-to-left direction is the "only when the given own-or-mut
cell has the same value and subresource inside of it" that `[TR]` Lemma 6.14's
proof spends.
`[about ours: the `⋈` of `[TR]` p. 5's second disjunct on §12.35's reading, in the
projections `CellU.rep` and `CellU.erase`]` -/
theorem CellU.compatR_iff {ψ₁ ψ₂ : CellU Loc Val} :
    CellU.CompatR ψ₁ ψ₂ ↔
      (ψ₁.erase = ψ₂.erase ∧
        (ψ₁.kind ≠ Kind.own → ψ₂.kind ≠ Kind.own → ψ₁.wit = ψ₂.wit)) := by
  constructor
  · rintro ⟨ψ, h⟩
    exact ⟨(CellU.CompR.erase h).1, fun k₁ k₂ => CellU.CompR.wit h k₁ k₂⟩
  · rintro ⟨hv, hw⟩
    rcases CellU.rep ψ₁ with ⟨v₁, rfl⟩ | ⟨s₁, v₁, τ₁, m₁, rfl⟩ |
        ⟨b₁, v₁, τ₁, m₁, P₁, w₁, rfl⟩ <;>
      rcases CellU.rep ψ₂ with ⟨v₂, rfl⟩ | ⟨s₂, v₂, τ₂, m₂, rfl⟩ |
        ⟨b₂, v₂, τ₂, m₂, P₂, w₂, rfl⟩ <;>
      simp only [CellU.erase_ownOf, CellU.erase_immOf, CellU.erase_mutOf] at hv <;>
      subst hv
    -- `own` on the left: clauses (1), (5) and (4), which ask only for the value.
    · exact ⟨_, CellU.CompR.same _⟩
    · exact ⟨_, CellU.CompR.ownImm s₂ _ τ₂ m₂⟩
    · exact ⟨_, CellU.CompR.ownMut b₂ _ τ₂ m₂ P₂ w₂⟩
    -- `imm` on the left: clause (5) against `own`, then (2) and (5), which ask
    -- for the witness as well.
    · exact ⟨_, CellU.CompR.immOwn s₁ _ τ₁ m₁⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellU.wit_immOf, CellU.wit_immOf] at hww
      subst hτ
      exact ⟨_, CellU.CompR.strict ⟨s₁, s₂, _, τ₁, m₁, m₂, rfl, rfl⟩⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellU.wit_immOf, CellU.wit_mutOf] at hww
      subst hτ
      exact ⟨_, CellU.CompR.immMut s₁ _ τ₁ m₁ b₂ m₂ P₂ w₂⟩
    -- `mut` on the left: clause (4) against `own`, then (5) and (3).
    · exact ⟨_, CellU.CompR.mutOwn b₁ _ τ₁ m₁ P₁ w₁⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellU.wit_mutOf, CellU.wit_immOf] at hww
      subst hτ
      exact ⟨_, CellU.CompR.mutImm s₂ _ τ₁ m₂ b₁ m₁ P₁ w₁⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellU.wit_mutOf, CellU.wit_mutOf] at hww
      subst hτ
      exact ⟨_, CellU.CompR.mutMut b₁ b₂ _ τ₁ m₁ m₂ P₁ P₂ w₁ w₂⟩

/-! `[about ours]`, for Lemma 6.14. -/
/-- The cell level of `[TR]` Lemma 6.14: the value of a `○` is `⋈` a third cell
whenever both operands are.
`[about ours: the cell-level step `[TR]` Lemma 6.14's proof takes at a location
where both `ρ₁` and `ρ₂` are defined]` -/
theorem CellU.CompatR.of_compR {ψ₁ ψ₂ ψ ψ₃ : CellU Loc Val}
    (h : CellU.CompR ψ₁ ψ₂ ψ) (k₁ : ψ₁.CompatR ψ₃) (k₂ : ψ₂.CompatR ψ₃) :
    ψ.CompatR ψ₃ := by
  rw [CellU.compatR_iff] at k₁ k₂ ⊢
  refine ⟨(CellU.CompR.erase h).2.trans k₁.1, fun hψ h₃ => ?_⟩
  rcases h.wit_of_ne_own hψ with ⟨hn, he⟩ | ⟨hn, he⟩
  · exact he.trans (k₁.2 hn h₃)
  · exact he.trans (k₂.2 hn h₃)

/-!
## Lemma 6.14 · `[TR]` p. 8 · `proved`

> If ρ₁ ○ ρ₂ and ρ₁ ○ ρ₃ and ρ₂ ○ ρ₃ are all defined, then so is ρ₁ ○ ρ₂ ○ ρ₃.

**Printed proof, transcribed.** Analogous to Lemma 6.13.  The only wrinkle is that `○`, unlike `●`, merges `imm` cells with `own` and `mut` cells; but it does so only when the own-or-mut cell has the same value and subresource inside it, so the composites still agree on overlapping `imm` cells up to lifetimes.

**Lean.** `BoCa.Fig16.ResU.compatR_of_pairwise`, alias `TR.lemma_6_14`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.14 (p. 8), with the conclusion stated as `⋈`, which is
definedness by `ResU.compR_defined_iff`.  The printed wrinkle is
`CellU.CompatR.of_compR`.
`[as printed]` (the printed `ρ₁ ○ ρ₂` appears as its graph — G4) -/
theorem ResU.compatR_of_pairwise {ρ₁ ρ₂ ρ₃ σ : ResU Loc Val}
    (h₁₂ : ResU.CompR ρ₁ ρ₂ σ) (h₁₃ : ResU.CompatR ρ₁ ρ₃)
    (h₂₃ : ResU.CompatR ρ₂ ρ₃) : ResU.CompatR σ ρ₃ := by
  intro l χ ψ₃ hχ h₃
  rcases h₁₂.get l with ⟨-, -, e⟩ | ⟨ψ, e₁, -, e⟩ | ⟨ψ, -, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩
  · rw [e] at hχ; exact absurd hχ (by simp)
  · rw [e] at hχ; cases Option.some.inj hχ; exact h₁₃ l _ _ e₁ h₃
  · rw [e] at hχ; cases Option.some.inj hχ; exact h₂₃ l _ _ e₂ h₃
  · rw [e] at hχ
    cases Option.some.inj hχ
    exact CellU.CompatR.of_compR hC (h₁₃ l _ _ e₁ h₃) (h₂₃ l _ _ e₂ h₃)

end BoCa.Fig16

alias TR.lemma_6_14 := BoCa.Fig16.ResU.compatR_of_pairwise

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]`, for Lemma 6.15. -/
/-- The composability constraints one `#` puts on its operands' walks, read off
`ResU.Flat.split` (Lemmas 6.18 and 6.20) as `[TR]` Lemma 6.15's proof reads them.
`[about ours: the constraints `[TR]` Lemmas 6.15 and 6.35 read off the display,
collected at named walks]` -/
theorem ResU.Hash.walks {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.Hash ρ₁ ρ₂)
    {e₁ e₂ a₁ a₂ : ResU Loc Val}
    (he₁ : ExS ρ₁ e₁) (he₂ : ExS ρ₂ e₂) (ha₁ : AgW ρ₁ a₁) (ha₂ : AgW ρ₂ a₂) :
    ResU.CompatS e₁ e₂ ∧ ResU.CompatR a₁ a₂ ∧
      ResU.CompatS e₁ a₁ ∧ ResU.CompatS e₁ a₂ ∧
      ResU.CompatS e₂ a₁ ∧ ResU.CompatS e₂ a₂ := by
  obtain ⟨-, ρ, hρ, σ, hσ⟩ := h
  obtain ⟨f₁, f₂, e, b₁, b₂, a, hf₁, hf₂, hec, hb₁, hb₂, hac, hc⟩ :=
    (ResU.Flat.split hρ).mp hσ
  cases ExS.functional hf₁ he₁
  cases ExS.functional hf₂ he₂
  cases AgW.functional hb₁ ha₁
  cases AgW.functional hb₂ ha₂
  have himm : e.ImmFree := ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)
  obtain ⟨hca₁, hca₂⟩ :=
    ResU.CompatS.of_compR_left ((ResU.restrict_imm_empty_iff e).mpr himm) hac hc.1
  obtain ⟨d₁₁, d₂₁⟩ := ResU.CompatS.of_compS_left_immFree himm hec hca₁
  obtain ⟨d₁₂, d₂₂⟩ := ResU.CompatS.of_compS_left_immFree himm hec hca₂
  exact ⟨hec.1, hac.1, d₁₁, d₁₂, d₂₁, d₂₂⟩

/-!
## Lemma 6.15 · `[TR]` p. 8 · `proved`

> If ρ₁ # ρ₂ and ρ₂ # ρ₃ and ρ₁ # ρ₃ then ρ₁ # ρ₂ ● ρ₃.

**Printed proof, transcribed.** The composite `ρ₁ ● ρ₂ ● ρ₃` is defined by Lemma 6.13, so it remains to show `✓(ρ₁ ● ρ₂ ● ρ₃)`, which by Lemmas 6.18 and 6.20 is definedness of `ex(ρ₁)_● ● ex(ρ₂)_● ● ex(ρ₃)_● ● (ag(ρ₁) ○ ag(ρ₂) ○ ag(ρ₃))`.  By assumption the three flattenings `⦇ρᵢ ● ρⱼ⦈ = ex(ρᵢ)_● ● ex(ρⱼ)_● ● (ag(ρᵢ) ○ ag(ρⱼ))` are defined, so the `ex(ρᵢ)_●` are pairwise `●`-composable and the `ag(ρᵢ)` pairwise `○`-composable, and Lemmas 6.13 and 6.14 give the two triple composites.  By two applications of Lemma 6.12 it remains that `ex(ρ₁)_● ● ex(ρ₂)_● ● ex(ρ₃)_● ● ag(ρᵢ)` is defined for each `i`; for `i = 1`, `ex(ρ₁)_●`, `ex(ρ₂)_● ● ex(ρ₃)_●` and `ag(ρ₁)` are pairwise composable by assumption, so Lemma 6.13 applies, and the other two are analogous.

**Lean.** `BoCa.Fig16.ResU.hash_of_pairwise`, alias `TR.lemma_6_15`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.15 (p. 8).
`[as printed]` (the printed `ρ₂ ● ρ₃` appears as its graph — G4) -/
theorem ResU.hash_of_pairwise {ρ₁ ρ₂ ρ₃ ρ₂₃ : ResU Loc Val}
    (h₁₂ : ResU.Hash ρ₁ ρ₂) (h₂₃ : ResU.Hash ρ₂ ρ₃) (h₁₃ : ResU.Hash ρ₁ ρ₃)
    (h : ResU.CompS ρ₂ ρ₃ ρ₂₃) : ResU.Hash ρ₁ ρ₂₃ := by
  -- `ρ₁ ▸◂ ρ₂ ● ρ₃`, by 6.13, and the composite 6.9 then names.
  have hcompat : ResU.CompatS ρ₁ ρ₂₃ :=
    (ResU.compatS_of_pairwise h h₁₂.1.symm h₁₃.1.symm).symm
  obtain ⟨ρ, hρ⟩ := (ResU.compS_defined_iff ρ₁ ρ₂₃).mpr hcompat
  refine ⟨hcompat, ρ, hρ, ?_⟩
  -- One pair of walks per operand: `✓ρᵢ` is 6.10, and the walks are functions.
  obtain ⟨x₁₂, hx₁₂, hv₁₂⟩ := h₁₂.2
  obtain ⟨x₂₃, hx₂₃, hv₂₃⟩ := h₂₃.2
  obtain ⟨hV₁, hV₂⟩ := ResU.Valid.split hx₁₂ hv₁₂
  obtain ⟨-, hV₃⟩ := ResU.Valid.split hx₂₃ hv₂₃
  obtain ⟨-, e₁, a₁, he₁, ha₁, -⟩ := hV₁
  obtain ⟨-, e₂, a₂, he₂, ha₂, -⟩ := hV₂
  obtain ⟨-, e₃, a₃, he₃, ha₃, -⟩ := hV₃
  -- The constraints the print takes "by assumption", at the three printed pairs.
  obtain ⟨g₁₂, r₁₂, c₁₁, c₁₂, c₂₁, c₂₂⟩ := h₁₂.walks he₁ he₂ ha₁ ha₂
  obtain ⟨g₂₃, r₂₃, -, c₂₃, c₃₂, c₃₃⟩ := h₂₃.walks he₂ he₃ ha₂ ha₃
  obtain ⟨g₁₃, r₁₃, -, c₁₃, c₃₁, -⟩ := h₁₃.walks he₁ he₃ ha₁ ha₃
  -- The walks of `ρ₂ ● ρ₃`, by 6.18 and 6.20.
  obtain ⟨e₂₃, hE₂₃⟩ := (ResU.compS_defined_iff e₂ e₃).mpr g₂₃
  obtain ⟨a₂₃, hA₂₃⟩ := (ResU.compR_defined_iff a₂ a₃).mpr r₂₃
  have hex : ExS ρ₂₃ e₂₃ := (ExS.split h).mpr ⟨e₂, e₃, he₂, he₃, hE₂₃⟩
  have hag : AgW ρ₂₃ a₂₃ := (AgW.split h).mpr ⟨a₂, a₃, ha₂, ha₃, hA₂₃⟩
  -- The triple exclusive composite, by 6.13; the triple aliasable one, by 6.14.
  obtain ⟨E, hE⟩ := (ResU.compS_defined_iff e₁ e₂₃).mpr
    (ResU.compatS_of_pairwise hE₂₃ g₁₂.symm g₁₃.symm).symm
  obtain ⟨A, hA⟩ := (ResU.compR_defined_iff a₁ a₂₃).mpr
    (ResU.compatR_of_pairwise hA₂₃ r₁₂.symm r₁₃.symm).symm
  -- The print's three displayed composites `E ▸◂ ag(ρⱼ)`, each 6.13 twice.
  have hEa₁ : ResU.CompatS E a₁ :=
    ResU.compatS_of_pairwise hE c₁₁ (ResU.compatS_of_pairwise hE₂₃ c₂₁ c₃₁)
  have hEa₂ : ResU.CompatS E a₂ :=
    ResU.compatS_of_pairwise hE c₁₂ (ResU.compatS_of_pairwise hE₂₃ c₂₂ c₃₂)
  have hEa₃ : ResU.CompatS E a₃ :=
    ResU.compatS_of_pairwise hE c₁₃ (ResU.compatS_of_pairwise hE₂₃ c₂₃ c₃₃)
  -- "By two applications of theorem 6.12", `E ▸◂ ag(ρ₁) ○ ag(ρ₂) ○ ag(ρ₃)`.
  obtain ⟨σ, hσ⟩ := (ResU.compS_defined_iff E A).mpr
    (ResU.compatS_of_compR hEa₁ (ResU.compatS_of_compR hEa₂ hEa₃ hA₂₃) hA)
  exact ⟨σ, (ResU.Flat.split hρ).mpr
    ⟨e₁, e₂₃, E, a₁, a₂₃, A, he₁, hex, hE, ha₁, hag, hA, hσ⟩⟩

end BoCa.Fig16

alias TR.lemma_6_15 := BoCa.Fig16.ResU.hash_of_pairwise

end
