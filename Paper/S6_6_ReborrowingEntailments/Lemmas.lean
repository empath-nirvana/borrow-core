import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Support.Model.Unr
import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.S6_4_StandardEntailments.Lemmas
import Paper.S6_5_NonStandardEntailments.Lemmas
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts
import Support.Model.Algebra
import Support.Model.CellFacts
import Support.Model.Entailments
import Support.Model.FlatteningCells
import Support.Model.Notation
import Support.Model.Propositions
import Support.Model.Singletons
import Support.Model.Update

/-!
# [TR] §6.6 Reborrowing Entailments  (physical pp. 32–35), Lemmas 6.120–6.134

The rules of the reborrowing modality `↺_α` (6.120–6.130), and the three lemmas that
carry the logical relation through it: `↺V₁` (6.131, by induction on the type),
`↺V₂` (6.132) and `↺V₃` (6.133), and 6.134, which 6.175 applies.  Records as in
§6.1's file; *Typed-world version* names the statement proved at the typed world, in
`Support/TypedWorld/`.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.120 (↺-mono) · `[TR]` p. 32 · `proved`

> P ⊨ Q
> ──────────────
> ↺_α P ⊨ ↺_α Q

**Printed proof, transcribed.** Suppose `P ⊨ Q`, and let `P(ρ′)` for some `ρ′ ∈ reb_α(ρ)`.  Choose `ρ′`; by `P ⊨ Q` at `ρ′`, `Q(ρ′)`.

**Lean.** `BoCa.Fig16.BoLo.reborrow_mono`, aliases `TR.lemma_6_120`, `TR.«↺-mono»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.120 (`↻-mono`, p. 32).  `[as printed]` -/
theorem reborrow_mono {α : Life} {P Q : SPropU Loc Val} (h : P ⊨ Q) :
    reborrow α P ⊨ reborrow α Q := by
  rintro ρ ⟨ρ', hr, hP⟩
  exact ⟨ρ', hr, h ρ' hP⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_120 := BoCa.Fig16.BoLo.reborrow_mono
alias TR.«↺-mono» := BoCa.Fig16.BoLo.reborrow_mono

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.121 (↺↦) · `[TR]` p. 32 · `proved`

> ℓ ↦ v ⋆ [α]P̂(v) ⊨ ↺_α ℓ ↦I_α P̂

**Printed proof, transcribed.** Let `ρ = ρ₁ ● ρ₂` with `ρ₁ = ℓ ↦ own(v)`, `P̂(v)(ρ₂)` and `@ρ₂ ⊐ α`.  Choose `ρ′ ∈ reb_α(ρ)` to be `ℓ ↦ imm({α}, v, ρ₂)`, and `β̃, v, ρ′` to be `{α}, v, ρ₂`.  What remains is `ℓ ↦ imm({α}, v, ρ₂) ∈ reb_α(ρ)`; choose `π` to be `ℓ ↦ ρ`.  It suffices that: `@ρ ⊐ α` — since `ρ = ℓ ↦ own(v) ● ρ₂`, it suffices that `@(ℓ ↦ own(v)) ⊐ α`, which holds by definition, and `@ρ₂ ⊐ α`, which is given; `ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ)` — since `dom(π) = {ℓ}` and `π(ℓ) = ρ`, this is `ρ ≥ ρ`; and the clause for each `ℓ ∈ dom(π)` — since `ρ(ℓ) = own(v)`, it is `(ℓ ↦ imm({α}, v, ρ₂))(ℓ) = imm({α}, v, π(ℓ) ∖ ℓ)`, by inspection.

**Lean.** `BoCa.Fig16.BoLo.reborrow_ptoOwn`, aliases `TR.lemma_6_121`, `TR.«↺↦»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.121 (`↻↦`, p. 32).  The partition is `π ≜ [(ℓ, ρ)]`, so the
printed `ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ)` holds at `ρ ≥ ρ`.  `[as printed]` -/
theorem reborrow_ptoOwn {α : Life} (l : Loc) (v : Val) (P : Val → SPropU Loc Val) :
    (ptoOwn l v ⋆ box α (P v)) ⊨ reborrow α (ptoImm l α P) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, rfl, hP, ho₂⟩
  have hnone : ρ₂.get l = none := ResU.compatS_single_own hc.1
  have hdel : ρ₂ = ρ.del l := by
    refine (PMap.ext fun k => ?_).symm
    by_cases hk : k = l
    · subst hk; rw [ResU.del_get_self, hnone]
    · rw [ResU.del_get_ne ρ hk]
      have hk2 := hc.2 k
      rw [ResU.single_get_ne _ hk] at hk2
      cases e2 : ρ₂.get k with
      | none => rw [e2] at hk2; exact hk2
      | some ψ => rw [e2] at hk2; exact hk2
  subst hdel
  have hstr : (ρ.del l).InStratum α := ho₂
  have ho₁ : Outlives (ResU.single l (CellU.ownOf v)) α :=
    (box_ptoOwn α l v _ rfl).2
  have hρl : ρ.get l = some (CellU.ownOf v) := by
    have hk2 := hc.2 l
    rw [ResU.single_get_self, hnone] at hk2
    exact hk2
  refine ⟨ResU.single l (CellU.immOf (LSet.singleton α) v (ρ.del l) hstr),
    ⟨(outlives_comp hc α).mpr ⟨ho₁, ho₂⟩, [(l, ρ)], ρ,
      ResU.dom_single _ _, BigComp.single _, ResU.Le.refl _, ?_⟩,
    LSet.singleton α, v, ρ.del l, hstr, rfl, hP, Nat.le_refl α⟩
  intro k p hm
  obtain ⟨rfl, rfl⟩ := memSingle hm
  refine ⟨⟨_, hρl⟩, ?_, ?_, ?_⟩
  · intro x e
    have hx : CellU.ownOf v = CellU.ownOf x := Option.some.inj (hρl.symm.trans e)
    injection hx with hx'
    subst hx'
    exact ⟨hstr, ResU.single_get_self _ _⟩
  · intro b x χ hb Q hw e
    have hx : CellU.ownOf v = CellU.mutOf b x χ hb Q hw :=
      Option.some.inj (hρl.symm.trans e)
    exact absurd hx CellU.ownOf_ne_mutOf
  · intro s x χ hs e
    have hx : CellU.ownOf v = CellU.immOf s x χ hs :=
      Option.some.inj (hρl.symm.trans e)
    exact absurd hx CellU.ownOf_ne_immOf

end BoCa.Fig16.BoLo

alias TR.lemma_6_121 := BoCa.Fig16.BoLo.reborrow_ptoOwn
alias TR.«↺↦» := BoCa.Fig16.BoLo.reborrow_ptoOwn

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.122 (↺m) · `[TR]` p. 32 · `proved`

> [α](ℓ ↦M_β P̂) ⊨ ↺_α(ℓ ↦I_α P̂)

**Printed proof, transcribed.** Let `ρ = ℓ ↦ mut(β, v, ρ′, P̂)` (which implies `P̂(v)`) with `@ρ ⊐ α`, for some `β ⊒ α`, `v`, `ρ′`.  Choose `ℓ ↦ imm({α}, v, ρ′)` for the reborrow and `{α}, v, ρ′` for `β̃, v, ρ′`; it remains that `ℓ ↦ imm({α}, v, ρ′) ∈ reb_α(ρ)`.  Choose `π` to be `ℓ ↦ ρ`: `@ρ ⊐ α` is given; `ρ ≥ ⨀ π(ℓ)` is `ρ ≥ ρ`; and since `ρ(ℓ) = mut(β, v, ρ′, P̂)` the clause is `(ℓ ↦ imm({α}, v, ρ′))(ℓ) = imm({α}, v, ρ′) ∧ dom(π(ℓ)) = {ℓ}`, by inspection.

**Lean.** `BoCa.Fig16.BoLo.reborrow_ptoMut`, aliases `TR.lemma_6_122`, `TR.«↺m»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.122 (`↻m`, p. 32).  `[as printed]` -/
theorem reborrow_ptoMut {α β : Life} (l : Loc) (P : Val → SPropU Loc Val) :
    box α (ptoMut l β P) ⊨ reborrow α (ptoImm l α P) := by
  rintro ρ ⟨⟨b, v, σ, hs, Q, hw, hβ, rfl, rfl⟩, ho⟩
  have hb : b ⊐ α := ho l _ (ResU.single_get_self _ _)
  have hstr : σ.InStratum (LSet.singleton α).join := by
    intro k ψ e
    cases ψ with
    | own w => exact trivial
    | imm i => exact lt_trans hb (hs k _ e)
    | «mut» m => exact lt_trans hb (hs k _ e)
  have hρl : (ResU.single l (CellU.mutOf b v σ hs Q hw)).get l
      = some (CellU.mutOf b v σ hs Q hw) := ResU.single_get_self _ _
  refine ⟨ResU.single l (CellU.immOf (LSet.singleton α) v σ hstr),
    ⟨ho, [(l, ResU.single l (CellU.mutOf b v σ hs Q hw))], _,
      ResU.dom_single _ _, BigComp.single _, ResU.Le.refl _, ?_⟩,
    LSet.singleton α, v, σ, hstr, rfl, ⟨hs, hw⟩, Nat.le_refl α⟩
  intro k p hm
  obtain ⟨rfl, rfl⟩ := memSingle hm
  refine ⟨⟨_, hρl⟩, ?_, ?_, ?_⟩
  · intro x e
    have hx : CellU.mutOf b v σ hs Q hw = CellU.ownOf x := Option.some.inj (hρl.symm.trans e)
    exact absurd hx.symm CellU.ownOf_ne_mutOf
  · intro b' x χ hb' Q' hw' e
    have hx : CellU.mutOf b v σ hs Q hw = CellU.mutOf b' x χ hb' Q' hw' :=
      Option.some.inj (hρl.symm.trans e)
    have hbb : b = b' := CellU.mutOf_at hx
    subst hbb
    obtain ⟨rfl, rfl, -⟩ := CellU.mutOf_inj hx
    exact ⟨⟨hstr, ResU.single_get_self _ _⟩, ResU.dom_single _ _⟩
  · intro s x χ hsx e
    have hx : CellU.mutOf b v σ hs Q hw = CellU.immOf s x χ hsx :=
      Option.some.inj (hρl.symm.trans e)
    exact absurd hx.symm CellU.immOf_ne_mutOf

end BoCa.Fig16.BoLo

alias TR.lemma_6_122 := BoCa.Fig16.BoLo.reborrow_ptoMut
alias TR.«↺m» := BoCa.Fig16.BoLo.reborrow_ptoMut

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.123 (↺i) · `[TR]` p. 32 · `proved`

> [α](ℓ ↦I_β P̂) ⊨ ↺_α(ℓ ↦I_β P̂)

**Printed proof, transcribed.** Let `ρ = ℓ ↦ imm(β̃, v, ρ′)` with `P̂(v)(ρ′)`, `β ⊑ ⊔β̃` and `@ρ ⊐ α`.  Choose `ℓ ↦ imm(β̃, v, ρ′)` for the reborrow and `β̃, v, ρ′` for the cell; it remains that `ℓ ↦ imm(β̃, v, ρ′) ∈ reb_α(ρ)`.  Choose `π` to be `ℓ ↦ ρ`: `@ρ ⊐ α` is given; `ρ ≥ ⨀ π(ℓ)` is `ρ ≥ ρ`; and since `ρ(ℓ) = imm(β̃, v, ρ′)` the clause is `(ℓ ↦ imm(β̃, v, ρ′))(ℓ) = ρ(ℓ) ∧ dom(π(ℓ)) = {ℓ}`, by inspection.

**Lean.** `BoCa.Fig16.BoLo.reborrow_ptoImm`, aliases `TR.lemma_6_123`, `TR.«↺i»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.123 (`↻i`, p. 32).  `[as printed]` -/
theorem reborrow_ptoImm {α β : Life} (l : Loc) (P : Val → SPropU Loc Val) :
    box α (ptoImm l β P) ⊨ reborrow α (ptoImm l β P) := by
  rintro ρ ⟨⟨s, v, σ, hs, rfl, hP, hβ⟩, ho⟩
  have hρl : (ResU.single l (CellU.immOf s v σ hs)).get l
      = some (CellU.immOf s v σ hs) := ResU.single_get_self _ _
  refine ⟨ResU.single l (CellU.immOf s v σ hs),
    ⟨ho, [(l, ResU.single l (CellU.immOf s v σ hs))], _,
      ResU.dom_single _ _, BigComp.single _, ResU.Le.refl _, ?_⟩,
    s, v, σ, hs, rfl, hP, hβ⟩
  intro k p hm
  obtain ⟨rfl, rfl⟩ := memSingle hm
  refine ⟨⟨_, hρl⟩, ?_, ?_,
    fun s' _ _ h' e' => ⟨⟨s', h', fun _ y => y, e'⟩, ResU.dom_single _ _⟩⟩
  · intro x e
    have hx : CellU.immOf s v σ hs = CellU.ownOf x := Option.some.inj (hρl.symm.trans e)
    exact absurd hx.symm CellU.ownOf_ne_immOf
  · intro b' x χ hb' Q' hw' e
    have hx : CellU.immOf s v σ hs = CellU.mutOf b' x χ hb' Q' hw' :=
      Option.some.inj (hρl.symm.trans e)
    exact absurd hx CellU.immOf_ne_mutOf

end BoCa.Fig16.BoLo

alias TR.lemma_6_123 := BoCa.Fig16.BoLo.reborrow_ptoImm
alias TR.«↺i» := BoCa.Fig16.BoLo.reborrow_ptoImm

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.124 (↺⌜⌝) · `[TR]` p. 33 · `proved`

> ⌜P⌝ ⊨ ↺_α ⌜P⌝

**Printed proof, transcribed.** Let `ρ = ∅` and `P`.  Choose `ρ′ ∈ reb_α(ρ)` to be `∅`; it remains that `∅ ∈ reb_α(ρ)`.  Choose `π` to be `∅`; since `dom(∅) = ∅` this is `@∅ ⊐ α` and `∅ ≥ ⨀_{ℓ∈dom(π)} π(ℓ)`, which hold by definition.

**Lean.** `BoCa.Fig16.BoLo.reborrow_pure`, aliases `TR.lemma_6_124`, `TR.«↺⌜⌝»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.124 (`↻⌜⌝`, p. 33).  `[as printed]` -/
theorem reborrow_pure (α : Life) (p : Prop) :
    (⌜p⌝ : SPropU Loc Val) ⊨ reborrow α ⌜p⌝ := by
  rintro ρ ⟨rfl, hp⟩
  exact ⟨PMap.empty, reb_empty α, rfl, hp⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_124 := BoCa.Fig16.BoLo.reborrow_pure
alias TR.«↺⌜⌝» := BoCa.Fig16.BoLo.reborrow_pure

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}
variable {Loc Val : Type}

/-!
## Lemma 6.125 (↺⋆) · `[TR]` p. 33 · `proved`

> ↺_α P ⋆ ↺_α Q ⊨ ↺_α(P ⋆ Q)

**Printed proof, transcribed.** Let `ρ = ρ₁ ● ρ₂` with `P(ρ′₁)` and `Q(ρ′₂)` for `ρ′₁ ∈ reb_α(ρ₁)` and `ρ′₂ ∈ reb_α(ρ₂)`.  By Lemma 6.61, `ρ′₁ ● ρ′₂ ∈ reb_α(ρ₁ ● ρ₂)`; choose it.  The remaining obligations are immediate.

**Lean.** `BoCa.Fig16.BoLo.reborrow_star`, aliases `TR.lemma_6_125`, `TR.«↺⋆»`, tag `[as printed]`.

**Note.** At the subset clause of `reb_α` (definition row 5.28, `docs/adjudications.md` §12.67(b)) the row carries no added hypothesis.
-/
/-- `[TR]` Lemma 6.125 (`↺⋆`, p. 33).  `[as printed]` -/
theorem reborrow_star (α : Life) (P Q : SPropU Loc Val) :
    (reborrow α P ⋆ reborrow α Q) ⊨ reborrow α (P ⋆ Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, ⟨ρ'₁, hreb₁, hP⟩, ⟨ρ'₂, hreb₂, hQ⟩⟩
  obtain ⟨ρ', hcomp, hreb⟩ := ResU.six61 hreb₁ hreb₂ hc
  exact ⟨ρ', hreb, ρ'₁, ρ'₂, hcomp, hP, hQ⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_125 := BoCa.Fig16.BoLo.reborrow_star
alias TR.«↺⋆» := BoCa.Fig16.BoLo.reborrow_star

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.126 (↺∨) · `[TR]` p. 33 · `proved`

> ↺_α P ∨ ↺_α Q ⫤⊨ ↺_α(P ∨ Q)

**Printed proof, transcribed.** Case `⊨`: let `(∃ρ′ ∈ reb_α(ρ). P(ρ′)) ∨ (∃ρ′ ∈ reb_α(ρ). Q(ρ′))`; in either case choose that `ρ′` and discharge the disjunction on the same side.  Case `⫤`: let `P(ρ′) ∨ Q(ρ′)` for some `ρ′ ∈ reb_α(ρ)`; in either case take the matching side of the disjunction and choose `ρ′`.

**Lean.** `BoCa.Fig16.BoLo.reborrow_or`, aliases `TR.lemma_6_126`, `TR.«↺∨»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.126 (`↻∨`, p. 33).  `[as printed]` -/
theorem reborrow_or (α : Life) (P Q : SPropU Loc Val) :
    or (reborrow α P) (reborrow α Q) ⫤⊨ reborrow α (or P Q) := by
  constructor
  · rintro ρ (⟨ρ', hr, hP⟩ | ⟨ρ', hr, hQ⟩)
    · exact ⟨ρ', hr, Or.inl hP⟩
    · exact ⟨ρ', hr, Or.inr hQ⟩
  · rintro ρ ⟨ρ', hr, (hP | hQ)⟩
    · exact Or.inl ⟨ρ', hr, hP⟩
    · exact Or.inr ⟨ρ', hr, hQ⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_126 := BoCa.Fig16.BoLo.reborrow_or
alias TR.«↺∨» := BoCa.Fig16.BoLo.reborrow_or

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.127 (↺-weak) · `[TR]` p. 33 · `proved`

> ↺_α(P ⋆ Q) ⊨ ↺_α P

**Printed proof, transcribed.** Let `ρ′ = ρ′₁ ● ρ′₂` with `P(ρ′₁)` and `Q(ρ′₂)`, for some `ρ′ ∈ reb_α(ρ)`.  Choose `ρ′₁`; `P(ρ′₁)` is immediate and it remains that `ρ′₁ ∈ reb_α(ρ)`.  Unfolding `ρ′ ∈ reb_α(ρ)`: `@ρ ⊐ α` (H1), `ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ)` (H2), and `∀ℓ ∈ dom(π), v, ρ″. F(ℓ, v, ρ, ρ′, ρ″, π)` (H3) for some `π : dom(ρ′) → Res`, where `F(ℓ, v, ρ, ρ′, ρ″, π) = ℓ ∈ dom(π(ℓ)) ∧ (ρ(ℓ) = own(v) ⇒ ρ′(ℓ) = imm({α}, v, π(ℓ) ∖ ℓ)) ∧ (ρ(ℓ) = mut(−, v, ρ″, −) ⇒ ρ′(ℓ) = imm({α}, v, ρ″) ∧ dom(π(ℓ)) = {ℓ}) ∧ (ρ(ℓ) = imm(−, −, −) ⇒ ρ′(ℓ) = ρ(ℓ) ∧ dom(π(ℓ)) = {ℓ})`.  Let `π′` be `π` restricted to `dom(ρ′₁)`, and choose it.  `@ρ ⊐ α` is H1.  `ρ ≥ ⨀_{ℓ∈dom(π′)} π′(ℓ)`: since `π′ ⊆ π`, `ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ) ≥ ⨀_{ℓ∈dom(π′)} π′(ℓ)`.  For `ℓ ∈ dom(π′)`, `v`, `ρ″`: `ℓ ∈ dom(π)`, so H3 gives `F(ℓ, v, ρ, ρ′, ρ″, π)`; *"by inspection of `F`, we observe that all usages of `π` are of the form `π(ℓ)`.  Since `π(ℓ) = π′(ℓ)`, we obtain `F(ℓ, v, ρ, ρ′₁, ρ″, π′)`."*

**Lean.** `BoCa.Fig16.BoLo.reborrow_weak`, aliases `TR.lemma_6_127`, `TR.«↺-weak»`, tag `[as printed]`.

**Note.** At the subset clause of `reb_α` (definition row 5.28, `docs/adjudications.md` §12.67(b)) the row carries no added hypothesis; the closing sentence's `ρ′ → ρ′₁` half is `Fig16.ResU.RebAt.factor`.
-/
/-- `[TR]` Lemma 6.127 (`↻-weak`, p. 33).  `[as printed]` -/
theorem reborrow_weak {α : Life} {P Q : SPropU Loc Val} :
    reborrow α (P ⋆ Q) ⊨ reborrow α P := by
  rintro ρ ⟨ρ', ⟨h1, π, b, hdom, hbig, hle, hbody⟩, ρ₁, ρ₂, hc, hP, hQ⟩
  have hdef : ∀ l ψ, ρ₁.get l = some ψ → ∃ φ, ρ'.get l = some φ := by
    intro l ψ hψ
    rcases ResU.Comp.get hc l with ⟨f₁, -, -⟩ | ⟨φ, -, -, f⟩ | ⟨φ, f₁, -, -⟩ |
        ⟨φa, φb, φ, -, -, f, -⟩
    · rw [hψ] at f₁; exact absurd f₁ (by simp)
    · exact ⟨φ, f⟩
    · rw [hψ] at f₁; exact absurd f₁ (by simp)
    · exact ⟨φ, f⟩
  -- `π′` is `π` with its domain restricted to `dom(ρ′₁)`.
  have hsub : List.Sublist (π.filter (fun q => (ρ₁.get q.1).isSome)) π :=
    List.filter_sublist
  obtain ⟨b', hb', hle'⟩ := BigComp.leS_of_sublist (hsub.map Prod.snd) hbig
  refine ⟨ρ₁, ⟨h1, _, b', ⟨List.Nodup.sublist (hsub.map Prod.fst) hdom.1, fun l => ?_⟩,
    hb', hle'.trans hle, fun l p hm => ?_⟩, hP⟩
  · constructor
    · intro hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      have hs : (ρ₁.get q.1).isSome = true := by simpa using (List.mem_filter.mp hq).2
      exact Option.isSome_iff_exists.mp hs
    · rintro ⟨ψ, hψ⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((hdom.2 l).mpr (hdef l ψ hψ))
      exact List.mem_map.mpr ⟨q, List.mem_filter.mpr ⟨hq, by simp [hψ]⟩, rfl⟩
  · have hf := List.mem_filter.mp hm
    have hs : (ρ₁.get l).isSome = true := by simpa using hf.2
    obtain ⟨ψ, hψ⟩ := Option.isSome_iff_exists.mp hs
    exact ResU.RebAt.factor (hbody l p hf.1) hc hψ

end BoCa.Fig16.BoLo

alias TR.lemma_6_127 := BoCa.Fig16.BoLo.reborrow_weak
alias TR.«↺-weak» := BoCa.Fig16.BoLo.reborrow_weak

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.128 (↺∃) · `[TR]` p. 34 · `proved`

> ∃x. ↺_α P(x) ⫤⊨ ↺_α ∃x. P(x)

**Printed proof, transcribed.** Case `⊨`: let `P̂(x)(ρ′)` for some `x` and `ρ′ ∈ reb_α(ρ)`; choose `x` and `ρ′`.  Case `⫤`: let `P̂(x)(ρ′)` for some `ρ′ ∈ reb_α(ρ)` and `x`; choose `ρ′` and `x`.  In both, `P̂(x)(ρ′)` is immediate.

**Lean.** `BoCa.Fig16.BoLo.reborrow_ex`, aliases `TR.lemma_6_128`, `TR.«↺∃»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.128 (`↻∃`, p. 34).  `[as printed]` -/
theorem reborrow_ex {A : Type} (α : Life) (Φ : A → SPropU Loc Val) :
    ex (fun x => reborrow α (Φ x)) ⫤⊨ reborrow α (ex Φ) := by
  constructor
  · rintro ρ ⟨x, ρ', hr, hP⟩
    exact ⟨ρ', hr, x, hP⟩
  · rintro ρ ⟨ρ', hr, x, hP⟩
    exact ⟨x, ρ', hr, hP⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_128 := BoCa.Fig16.BoLo.reborrow_ex
alias TR.«↺∃» := BoCa.Fig16.BoLo.reborrow_ex

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.129 (↺∀) · `[TR]` p. 34 · `variant`

> ∀x. ↺_α P(x) ⫤⊨ ↺_α ∀x. P(x)

**Printed proof, transcribed.** Let `∀x. P̂(x)(ρ′)` for some `ρ′ ∈ reb_α(ρ)`.  Let `x` be arbitrary and choose `ρ′`.  Instantiate `∀x. P̂(x)(ρ′)` at `x` to obtain `P̂(x)(ρ′)`.

**Lean.** `BoCa.Fig16.BoLo.reborrow_all`, aliases `TR.lemma_6_129`, `TR.«↺∀»`, tag `[variant: one direction of a printed `⫤⊨` — the direction the printed
paragraph runs]`.

**Note.** `[variant: one direction of a printed `⫤⊨`]`.  The printed paragraph opens on the right-hand proposition, one `ρ′ ∈ reb_α(ρ)` with `∀x. P̂(x)(ρ′)`, and closes on the left, so it runs `⫤`; unlike 6.126's and 6.128's, it does not split into `Case ⊨` and `Case ⫤`.
-/
/-- `[TR]` Lemma 6.129 (`↻∀`, p. 34).  `[variant: the `⫤` direction]` -/
theorem reborrow_all {A : Type} (α : Life) (Φ : A → SPropU Loc Val) :
    reborrow α (all Φ) ⊨ all (fun x => reborrow α (Φ x)) := by
  rintro ρ ⟨ρ', hr, h⟩ x
  exact ⟨ρ', hr, h x⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_129 := BoCa.Fig16.BoLo.reborrow_all
alias TR.«↺∀» := BoCa.Fig16.BoLo.reborrow_all

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-! A declaration the record of Lemma 6.130 cites. -/
/-- `∅ ∈ reb_α(ρ) ⟺ @ρ ⊐ α`: `reb_α` at its empty family.
`[about ours: the printed `reb_α` at `ρ′ = ∅`]` -/
theorem reb_emp_iff (α : Life) (ρ : ResU Loc Val) :
    ResU.Reb α ρ (PMap.empty : ResU Loc Val) ↔ Outlives ρ α := by
  constructor
  · rintro ⟨h, -⟩
    exact h
  · intro h
    exact ⟨h, [], PMap.empty,
      ⟨List.nodup_nil, fun _ => ⟨fun hm => absurd hm (by simp),
        fun ⟨_, hg⟩ => absurd hg (by simp)⟩⟩,
      BigComp.nil, ResU.Le.empty ρ, fun _ _ hp => absurd hp (by simp)⟩

/-! A declaration the record of Lemma 6.130 cites. -/
/-- `↻_α emp` is `Res_α`.  `[about ours: the extension of the printed `↻_α emp`]` -/
theorem reborrow_emp_iff (α : Life) (ρ : ResU Loc Val) :
    reborrow α (emp : SPropU Loc Val) ρ ↔ Outlives ρ α := by
  constructor
  · exact fun h => reborrow_outlives α emp ρ h
  · exact fun h => ⟨PMap.empty, (reb_emp_iff α ρ).mpr h, emp_empty⟩

/-!
## Lemma 6.130 · `[TR]` p. 34 · `proved*`

> P ⊨ ↺_α emp

**Printed proof, transcribed.** Suppose `ρ ∈ P`.  Then `∅` vacuously satisfies the conditions needed to be a reborrowed version of `ρ`, so `ρ ∈ ↺_α emp`.

**Lean.** `BoCa.Fig16.BoLo.reborrow_emp`, alias `TR.lemma_6_130`, tag `[restricted: to `∀ρ. P(ρ) ⇒ ρ ∈ Res_α` — that `P` is one of `[TR]`.

**Also here.** `BoCa.Fig16.BoLo.reb_emp_iff`; `BoCa.Fig16.BoLo.reborrow_emp_iff`; `BoCa.Fig16.BoLo.reborrow_emp_box`; `BoCa.Fig16.BoLo.reborrow_emp_ptoOwn`.

**Literal reading.** `BoCa.Fig16.BoLo.reborrow_emp_outside_stratum`, in `Paper/LiteralReadings/S6_6_ReborrowingEntailments.lean`.

**Note.** `[restricted: to `∀ρ. P(ρ) ⇒ ρ ∈ Res_α`]` (`docs/adjudications.md` §12.62).  The printed proof supplies `∅` for `ρ′`; `Fig16.BoLo.reb_emp_iff` is its "vacuously", and what remains is `reb_α`'s leading conjunct `@ρ ⊐ α`, a condition on `ρ`.  Both of [TR]'s uses of 6.130, inside 6.131, supply the hypothesis: `reborrow_emp_box` and `reborrow_emp_ptoOwn`.
-/
/-- `[TR]` Lemma 6.130 (p. 34).  `[restricted: to `∀ρ. P(ρ) ⇒ ρ ∈ Res_α`]` -/
theorem reborrow_emp {α : Life} {P : SPropU Loc Val}
    (h : ∀ ρ, P ρ → Outlives ρ α) : P ⊨ reborrow α (emp : SPropU Loc Val) :=
  fun ρ hp => (reborrow_emp_iff α ρ).mpr (h ρ hp)

end BoCa.Fig16.BoLo

alias TR.lemma_6_130 := BoCa.Fig16.BoLo.reborrow_emp

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-! A declaration the record of Lemma 6.130 cites. -/
/-- 6.130 at 6.131's `T₁ ⊸ T₂` case (p. 34), where `[α]`'s second conjunct is
`@ρ ⊐ α`.  `[about ours: the scope of 6.130's added hypothesis]` -/
theorem reborrow_emp_box (α : Life) (P : SPropU Loc Val) :
    box α P ⊨ reborrow α (emp : SPropU Loc Val) :=
  reborrow_emp (fun _ h => h.2)

/-! A declaration the record of Lemma 6.130 cites. -/
/-- 6.130 at 6.131's `Ref T′` case (p. 34): an `own` cell carries no borrow, so it
lies in every stratum.  `[about ours: the scope of 6.130's added hypothesis]` -/
theorem reborrow_emp_ptoOwn (α : Life) (l : Loc) (v : Val) :
    ptoOwn l v ⊨ reborrow α (emp : SPropU Loc Val) := by
  refine reborrow_emp (fun ρ h => ?_)
  rw [show ρ = ResU.single l (CellU.ownOf v) from h]
  exact ResU.inStratum_single_own α l v

/-! A declaration the record of Lemma 6.131 (↺V₁) cites. -/
/-- 6.124 and 6.125 at the shape 6.131 applies them in, a pure left factor:
`⌜p⌝ ⋆ ↻_α R ⊨ ↻_α (⌜p⌝ ⋆ R)`.  `[about ours]` -/
theorem reborrow_star_pure (α : Life) (p : Prop) (R : SPropU Loc Val) :
    (⌜p⌝ ⋆ reborrow α R) ⊨ reborrow α (⌜p⌝ ⋆ R) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, ⟨rfl, hp⟩, ρ', hreb, hR⟩
  rw [eq_of_compS_empty_left hc]
  exact ⟨ρ', hreb, PMap.empty, ρ', compS_empty_left ρ', ⟨rfl, hp⟩, hR⟩

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-! A declaration the record of Lemma 6.131 (↺V₁) cites. -/
/-- `[TR]` Lemma 6.131 (`↺V₁`, pp. 34–35) at every `T`, including `Unk`.
`[as printed]` -/
theorem reborrow_vDen {α : Life} {x : LifeVar} {δ : LSub}
    (hδ : (Lifetime.Life.var x).interp δ = some α) :
    ∀ (T : Ty) (v : Val),
      box α (vDen T δ v) ⊨ reborrow α (vDen (T.immReborrow (.var x)) δ v) := by
  intro T
  induction T with
  | unit =>
      -- Unfold: `[α] ⌜v = ()⌝ ⊨ ↺_α ⌜v = ()⌝`.  Apply `[]L` and `↺⌜⌝`.
      intro v
      rw [vDen_immReborrow_unit, vDen_unit]
      exact Entails.trans (box_L α _) (reborrow_pure α _)
  | sum T₁ T₂ ih₁ ih₂ =>
      -- Analogous to `⊗`, using `↺∨` in place of `↺⋆`.
      intro v ρ hρ
      rw [vDen_sum] at hρ
      rw [vDen_immReborrow_sum]
      -- Apply `[]∨`.
      rcases (box_or α _ _).1 ρ hρ with h | h
      · -- Apply `[]∃`, `∃L`, `[]⋆`, `[]L`.
        obtain ⟨v₁, h⟩ := (box_ex α _).2 ρ h
        obtain ⟨σ₀, σ, hc, hp, hA⟩ := (box_sep α _ _).1 ρ h
        -- Apply IH, then `↺⌜⌝`, `↺⋆`, `↺∃`, `∃R`, and `↺∨`.
        exact (reborrow_or α _ _).1 ρ (or_R₁ _ _ ρ ((reborrow_ex α _).1 ρ
          (ex_R v₁ (Entails.refl _) ρ (reborrow_star_pure α _ _ ρ
            ⟨σ₀, σ, hc, box_L α _ σ₀ hp, ih₁ v₁ σ hA⟩))))
      · obtain ⟨v₂, h⟩ := (box_ex α _).2 ρ h
        obtain ⟨σ₀, σ, hc, hp, hA⟩ := (box_sep α _ _).1 ρ h
        exact (reborrow_or α _ _).1 ρ (or_R₂ _ _ ρ ((reborrow_ex α _).1 ρ
          (ex_R v₂ (Entails.refl _) ρ (reborrow_star_pure α _ _ ρ
            ⟨σ₀, σ, hc, box_L α _ σ₀ hp, ih₂ v₂ σ hA⟩))))
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro v ρ hρ
      rw [vDen_tensor] at hρ
      rw [vDen_immReborrow_tensor]
      -- Apply `[]∃`, `∃L`.
      obtain ⟨v₁, hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨v₂, hρ⟩ := (box_ex α _).2 ρ hρ
      -- Apply `[]⋆`, `[]L`.
      obtain ⟨σ₀, σ, hc, hp, hrest⟩ := (box_sep α _ _).1 ρ hρ
      obtain ⟨σ₁, σ₂, hc', h₁, h₂⟩ := (box_sep α _ _).1 σ hrest
      -- Apply IH, then `↺⋆` — the printed 6.125 — then `↺⌜⌝`, `↺∃`, `∃R`.
      exact (reborrow_ex α _).1 ρ (ex_R v₁ (Entails.refl _) ρ
        ((reborrow_ex α _).1 ρ (ex_R v₂ (Entails.refl _) ρ
          (reborrow_star_pure α _ _ ρ ⟨σ₀, σ, hc, box_L α _ σ₀ hp,
            BoLo.reborrow_star α _ _ σ
              ⟨σ₁, σ₂, hc', ih₁ v₁ σ₁ h₁, ih₂ v₂ σ₂ h₂⟩⟩))))
  | lolli T₁ T₂ _ _ =>
      -- Unfold: `[α] 𝒱⟦T₁ ⊸ T₂⟧δ(v) ⊨ ↺_α emp`.  Apply theorem 6.130.
      intro v
      rw [vDen_immReborrow_lolli]
      exact reborrow_emp_box α _
  | all y c T _ =>
      -- Analogous to the `T₁ ⊸ T₂` case.
      intro v
      rw [vDen_immReborrow_all]
      exact reborrow_emp_box α _
  | box a T ih =>
      -- Unfold: `[α] [@aδ] 𝒱⟦T⟧δ(v) ⊨ ↺_α 𝒱⟦Imm̲ 'a T⟧δ(v)`.
      -- Apply `[]L` (under `[]-mono`), then the IH.
      intro v
      rw [vDen_immReborrow_box]
      refine Entails.trans (box_mono ?_) (ih v)
      intro ρ hρ
      rw [vDen_box] at hρ
      obtain ⟨β, -, hb⟩ := hρ
      exact box_L β _ ρ hb
  | ref T _ =>
      intro v ρ hρ
      rw [vDen_ref] at hρ
      rw [vDen_immReborrow_ref_at _ _ _ hδ]
      -- Apply `[]∃`, `∃L`, `[]⋆`, `[]L`.
      obtain ⟨ℓ, hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨v', hρ⟩ := (box_ex α _).2 ρ hρ
      obtain ⟨σ₀, σ, hc, hp, hrest⟩ := (box_sep α _ _).1 ρ hρ
      obtain ⟨σ₁, σ₂, hc', hown, hpay⟩ := (box_sep α _ _).1 σ hrest
      -- Apply `↺↦` (6.121), then `↺⌜⌝`, `↺⋆`, `↺∃`.
      exact (reborrow_ex α _).1 ρ (ex_R ℓ (Entails.refl _) ρ
        (reborrow_star_pure α _ _ ρ
          ⟨σ₀, σ, hc, box_L α _ σ₀ hp,
            reborrow_ptoOwn ℓ v' (vDen T δ) σ
              ⟨σ₁, σ₂, hc', box_L α _ σ₁ hown, hpay⟩⟩))
  | bang T _ =>
    -- `[α] 𝒱⟦!T⟧δ(v) ⊨ ↺_α 𝒱⟦!T⟧δ(v)`: its resource `∅` is its own reborrow.
    intro v
    show box α (vDen (.bang T) δ v) ⊨ reborrow α (vDen (.bang T) δ v)
    exact reborrow_self_of_imm α _ (fun _ h => h.1.1 ▸ ⟨free_empty _, free_empty _⟩)
  | imm a T _ =>
      -- Unfold: `[α] ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦I_{@bδ} 𝒱⟦T′⟧δ ⊨ ↺_α 𝒱⟦Imm @b T′⟧δ(v)`.
      intro v ρ hρ
      rw [vDen_imm] at hρ
      obtain ⟨⟨γ, hγ, hb⟩, ho⟩ := hρ
      rw [vDen_immReborrow_imm_at _ _ _ a hγ]
      -- Apply `[]∃`, `[]⋆`, `[]L`.
      obtain ⟨ℓ, hbox⟩ := (box_ex α _).2 ρ (show box α _ ρ from ⟨hb, ho⟩)
      obtain ⟨σ₀, σ, hc, hp, hcell⟩ := (box_sep α _ _).1 ρ hbox
      -- Apply `↺I` (6.123), then `↺⌜⌝`, `↺⋆`, `↺∃`, and fold `𝒱⟦Imm @b T′⟧`.
      exact (reborrow_ex α _).1 ρ (ex_R ℓ (Entails.refl _) ρ
        (reborrow_star_pure α _ _ ρ
          ⟨σ₀, σ, hc, box_L α _ σ₀ hp, reborrow_ptoImm ℓ (vDen T δ) σ hcell⟩))
  | «mut» a T _ =>
      -- Unfold: `[α] ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦M_{@bδ} 𝒱⟦T′⟧δ ⊨ ↺_α 𝒱⟦Imm α T′⟧δ(v)`.
      intro v ρ hρ
      rw [vDen_mut] at hρ
      obtain ⟨⟨γ, hγ, hb⟩, ho⟩ := hρ
      rw [vDen_immReborrow_mut_at _ _ _ hδ]
      -- Apply `[]∃`, `[]⋆`, `[]L`.
      obtain ⟨ℓ, hbox⟩ := (box_ex α _).2 ρ (show box α _ ρ from ⟨hb, ho⟩)
      obtain ⟨σ₀, σ, hc, hp, hcell⟩ := (box_sep α _ _).1 ρ hbox
      -- Apply `↺M` (6.122), then `↺⌜⌝`, `↺⋆`, `↺∃`, and fold `𝒱⟦Imm α T′⟧`.
      exact (reborrow_ex α _).1 ρ (ex_R ℓ (Entails.refl _) ρ
        (reborrow_star_pure α _ _ ρ
          ⟨σ₀, σ, hc, box_L α _ σ₀ hp, reborrow_ptoMut ℓ (vDen T δ) σ hcell⟩))
  | unk =>
      -- The print says "impossible"; §12.11's clause makes it the `⊸` step.
      intro v
      rw [vDen_immReborrow_unk]
      exact reborrow_emp_box α _

/-!
## Lemma 6.131 (↺V₁) · `[TR]` p. 34 · `proved`

> [δ('a)] 𝒱⟦T⟧δ(v) ⊨ ↺_δ('a) 𝒱⟦Imm̲ 'a T⟧δ(v) for all T ≠ Unk.

**Printed proof, transcribed.** By induction on `T`, with `δ('a) = α`.  `T = 1`: unfold to `[α]⌜v = ()⌝ ⊨ ↺_α ⌜v = ()⌝`; apply `[]L` and `↺⌜⌝`.  `T = T₁ ⊗ T₂`: unfold; apply `[]∃`, `∃L`, `[]⋆`, `[]L` to reach `⌜v = (v₁, v₂)⌝ ⋆ [α]𝒱⟦T₁⟧δ(v₁) ⋆ [α]𝒱⟦T₂⟧δ(v₂)` on the left; apply `↺∃`, `∃R`, `↺⋆`, `↺⌜⌝` to reach `⌜v = (v₁, v₂)⌝ ⋆ ↺_α 𝒱⟦Imm̲ 'a T₁⟧δ(v₁) ⋆ ↺_α 𝒱⟦Imm̲ 'a T₂⟧δ(v₂)` on the right; apply IH.  `T = T₁ ⊕ T₂`: analogous, with `↺∨` for `↺⋆`.  `T = T₁ ⊸ T₂`: the goal unfolds to `[α]𝒱⟦T₁ ⊸ T₂⟧δ(v) ⊨ ↺_α emp`; apply Lemma 6.130.  `T = ∀'a ⊏ @b. T′`: analogous to `⊸`.  `T = [@a]T′`: unfold to `[α][@aδ]𝒱⟦T′⟧δ(v)`; apply `[]L`; apply IH.  `T = Ref T′`: unfold to `[α]∃ℓ, v′. ⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ 𝒱⟦T′⟧δ(v′)`; apply `[]∃`, `∃L`, `[]⋆`, `[]L`; apply IH, giving `⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ ↺_α 𝒱⟦Imm̲ 'a T′⟧δ(v′)`; apply Lemma 6.130, giving `↺_α emp ⋆ ↺_α 𝒱⟦Imm̲ 'a T′⟧δ(v′)`; apply `↺⋆`; done because `emp` is a unit for `⋆`.  `T = Imm @b T′`: unfold to `[α]∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦I_{@bδ} 𝒱⟦T′⟧δ`; apply `[]∃`, `[]⋆`, `[]L`; apply `↺i`; apply `↺⌜⌝`, `↺⋆`, `↺∃`; fold `𝒱⟦Imm @b T′⟧`.  `T = Mut @b T′`: the goal's right side is `↺_α 𝒱⟦Imm α T′⟧δ(v)`; unfold, apply `[]∃`, `[]⋆`, `[]L`; apply `↺m`, giving `↺_α(ℓ ↦I_α 𝒱⟦T′⟧δ)`; apply `↺⌜⌝`, `↺⋆`, `↺∃`; fold `𝒱⟦Imm α T′⟧`.  `T = Unk`: impossible.

**Lean.** `BoCa.Fig16.LogRel.reborrow_vDen_ne_unk`, aliases `TR.lemma_6_131`, `TR.«↺V₁»`, tag `[as printed]`.

**Also here.** `BoCa.Fig16.LogRel.reborrow_vDen`; `BoCa.Fig16.BoLo.reborrow_star_pure`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.reborrow_vShape`, in `Support/TypedWorld/ReborrowShapes.lean`; `BoCa.Fig16.LogRel.Typed.image_vX_of_shape`, in `Support/TypedWorld/RelationFacts.lean`.

**Literal reading.** `BoCa.Fig16.LogRel.RefPrintedChainResidual`, in `Paper/LiteralReadings/S6_6_ReborrowingEntailments.lean`.

**Note.** `Imm` in `𝒱⟦Imm 'a T⟧` is underlined (400 dpi): the metafunction `Ty.immReborrow`.  The `Unk` bullet, printed "impossible", is the `⊸` bullet's step under §12.11's clause `Imm̲ 'b Unk ≜ Unk`, so `Fig16.LogRel.reborrow_vDen` holds at every `T`; `reborrow_vDen_ne_unk` carries the printed `T ≠ Unk`.  The `Ref` bullet applies 6.121 (`↺↦`) where the printed chain applies 6.130, `↺⋆` and `emp`'s unit: clause (5) sends `Ref T′` to the constructor `Imm 'a T′`, and `Fig16.LogRel.RefPrintedChainResidual` is what the printed chain leaves against it — not derived, and no obstruction verified.
-/
/-- `[TR]` Lemma 6.131 (`↺V₁`, pp. 34–35), with its printed side condition `T ≠ Unk`
carried and not spent.  `[as printed]` -/
theorem reborrow_vDen_ne_unk {α : Life} {x : LifeVar} {δ : LSub}
    (hδ : (Lifetime.Life.var x).interp δ = some α)
    (T : Ty) (_hT : T ≠ .unk) (v : Val) :
    box α (vDen T δ v) ⊨ reborrow α (vDen (T.immReborrow (.var x)) δ v) :=
  reborrow_vDen hδ T v

end BoCa.Fig16.LogRel

alias TR.lemma_6_131 := BoCa.Fig16.LogRel.reborrow_vDen_ne_unk
alias TR.«↺V₁» := BoCa.Fig16.LogRel.reborrow_vDen_ne_unk

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.132 (↺V₂) · `[TR]` p. 35 · `proved`

> If 'a not free in T then 𝒱⟦T⟧δ(v) ⊨ Иα. ↺_α 𝒱⟦Imm̲ 'a T⟧δ['a↦α](v)

**Printed proof, transcribed.** A table of steps.  Apply `ИR`, `Иmono` and fix `α ⊏ ⨅δ` arbitrary: `[α]𝒱⟦T⟧δ(v) ⊨ [α]↺_α 𝒱⟦Imm̲ 'a T⟧δ['a↦α](v)`.  Apply `[]R`: `[α]𝒱⟦T⟧δ(v) ⊨ ↺_α 𝒱⟦Imm̲ 'a T⟧δ['a↦α](v)`.  Have `𝒱⟦T⟧δ = 𝒱⟦T⟧δ['a↦α]` because `'a` is not free in `T`: `[α]𝒱⟦T⟧δ['a↦α](v) ⊨ ↺_α 𝒱⟦Imm̲ 'a T⟧δ['a↦α](v)`.  Apply `↺V₁`.

**Lean.** `BoCa.Fig16.LogRel.reborrow_vDen_fresh`, aliases `TR.lemma_6_132`, `TR.«↺V₂»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.six132_shape`, in `Support/TypedWorld/ReborrowShapes.lean`; `BoCa.Fig16.LogRel.Typed.six132_shape_fresh`, in `Support/TypedWorld/ReborrowShapes.lean`.

**Note.** `Imm` is underlined, as in 6.131.  `Иα` carries `[TR]`'s `[α]`, which `[]R` in the second row acts on; the bound `⨅δ` is `Fig16.LogRel.meetOfCod`.
-/
/-- `[TR]` Lemma 6.132 (`↺V₂`, p. 35).  `[as printed]` -/
theorem reborrow_vDen_fresh {x : LifeVar} {δ : LSub}
    (T : Ty) (hT : ¬ LFree x T) (v : Val) :
    vDen T δ v ⊨
      fresh fun α => reborrow α (vDen (T.immReborrow (.var x)) (δ.extend x α) v) := by
  -- Apply `ИR`, `Иmono`, and fix `α ⊏ ⨅δ` arbitrary.
  refine Entails.trans (fresh_R (vDen T δ v)) (fresh_mono (β' := meetOfCod δ) ?_)
  intro α _hα
  -- Apply `[]R`.
  refine box_R ?_
  -- Have `𝒱⟦T⟧δ = 𝒱⟦T⟧δ['a↦α]`, because `'a` is not free in `T`.
  rw [← vDen_extend_of_not_free hT δ α]
  -- Apply `↺V₁`.
  exact reborrow_vDen (find?_extend_self δ x α) T v

end BoCa.Fig16.LogRel

alias TR.lemma_6_132 := BoCa.Fig16.LogRel.reborrow_vDen_fresh
alias TR.«↺V₂» := BoCa.Fig16.LogRel.reborrow_vDen_fresh

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.133 (↺V₃) · `[TR]` p. 35 · `proved`

> If 'b not free in T then ℓ ↦I_α 𝒱⟦T⟧δ ⊨ ℓ ↦I_α Иβ. ↺_β 𝒱⟦Imm̲ 'b T⟧δ['b↦β]

**Printed proof, transcribed.** Apply `↺V₂` and `I-mono`.

**Lean.** `BoCa.Fig16.LogRel.ptoImm_reborrow_vDen_fresh`, aliases `TR.lemma_6_133`, `TR.«↺V₃»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.133 (`↺V₃`, p. 35).  `[as printed]` -/
theorem ptoImm_reborrow_vDen_fresh {l : BoCa.Loc} {α : Life} {x : LifeVar} {δ : LSub}
    (T : Ty) (hT : ¬ LFree x T) :
    ptoImm l α (vDen T δ) ⊨
      ptoImm l α fun v =>
        fresh fun β => reborrow β (vDen (T.immReborrow (.var x)) (δ.extend x β) v) :=
  ptoImm_mono (reborrow_vDen_fresh T hT)

end BoCa.Fig16.LogRel

alias TR.lemma_6_133 := BoCa.Fig16.LogRel.ptoImm_reborrow_vDen_fresh
alias TR.«↺V₃» := BoCa.Fig16.LogRel.ptoImm_reborrow_vDen_fresh

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.134 · `[TR]` p. 35 · `proved`

> ⌜x = y⌝ ⋆ Иα. ↺_α 𝒱⟦Imm̲ 'a T⟧δ['a↦α] ⊨ Иα. ↺_α(⌜x = y⌝ ⋆ 𝒱⟦Imm̲ 'a T⟧δ['a↦α])

**Printed proof, transcribed.** By unfolding and substituting for `x = y`.

**Lean.** `BoCa.Fig16.LogRel.pure_sep_reborrow_vDen_fresh`, alias `TR.lemma_6_134`, tag `[as printed]`.

**Note.** The value argument the printed row leaves off `𝒱⟦Imm̲ 'a T⟧δ['a↦α]` is supplied, the same on both sides; 6.175 applies the row at `v ≔ v_ℓ` (p. 48).
-/
/-- `[TR]` Lemma 6.134 (p. 35).  `[as printed]` -/
theorem pure_sep_reborrow_vDen_fresh {x y : Val} {a : LifeVar} {δ : LSub}
    (T : Ty) (v : Val) :
    (⌜x = y⌝ ⋆ fresh fun α =>
        reborrow α (vDen (T.immReborrow (.var a)) (δ.extend a α) v)) ⊨
      fresh fun α =>
        reborrow α (⌜x = y⌝ ⋆ vDen (T.immReborrow (.var a)) (δ.extend a α) v) := by
  intro ρ hpre
  -- "By unfolding…"
  obtain ⟨hxy, β, hβ⟩ := pure_sep_iff.mp hpre
  refine ⟨β, fun α hα => ?_⟩
  obtain ⟨⟨χ, hreb, hV⟩, hout⟩ := hβ α hα
  -- "…and substituting for `x = y`."
  exact ⟨⟨χ, hreb, pure_sep_mk hxy hV⟩, hout⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_134 := BoCa.Fig16.LogRel.pure_sep_reborrow_vDen_fresh

end
