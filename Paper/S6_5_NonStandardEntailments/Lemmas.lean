import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.S6_3_FrameAndAntiFrame.Lemmas
import Paper.S6_4_StandardEntailments.Lemmas
import Support.Model.Composition
import Support.Model.Entailments
import Support.Model.Lifetimes
import Support.Model.Notation
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.Singletons

/-!
# [TR] §6.5 Non-standard Entailments  (physical pp. 29–32), Lemmas 6.96–6.119

The rules of the lifetime modality `[α]` (6.96–6.107), of the freshness quantifier
`Иα` (6.108–6.112), of immutable points-to `ℓ ↦I_α P̂` (6.113–6.116) and of mutable
points-to `ℓ ↦M_α P̂` (6.117–6.119).  Lemma 6.112 is declared in §6.3's file; its
record and aliases are here.  Records as in §6.1's file; *Typed-world version*
names the statement proved at the typed world, in `Support/TypedWorld/`.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.96 ([]-mono) · `[TR]` p. 29 · `proved`

> P ⊨ Q
> ──────────────
> [α]P ⊨ [α]Q

**Printed proof, transcribed.** Suppose `P ⊨ Q`, and let `P(ρ)` and `@ρ ⊐ α`.  By `P ⊨ Q` and `P(ρ)`, `Q(ρ)`.

**Lean.** `BoCa.Fig16.BoLo.box_mono`, aliases `TR.lemma_6_96`, `TR.«[]-mono»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.96 (`[]-mono`, p. 29).  `[as printed]` -/
theorem box_mono {α : Life} {P Q : SPropU Loc Val} (h : P ⊨ Q) : box α P ⊨ box α Q :=
  fun ρ k => ⟨h ρ k.1, k.2⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_96 := BoCa.Fig16.BoLo.box_mono
alias TR.«[]-mono» := BoCa.Fig16.BoLo.box_mono

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.97 ([]l) · `[TR]` p. 29 · `proved`

> [α]P ⊨ P

**Printed proof, transcribed.** By inspection.

**Lean.** `BoCa.Fig16.BoLo.box_L`, aliases `TR.lemma_6_97`, `TR.«[]l»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.97 (`[]l`, p. 29).  `[as printed]` -/
theorem box_L (α : Life) (P : SPropU Loc Val) : box α P ⊨ P := fun _ h => h.1

end BoCa.Fig16.BoLo

alias TR.lemma_6_97 := BoCa.Fig16.BoLo.box_L
alias TR.«[]l» := BoCa.Fig16.BoLo.box_L

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.98 ([]r) · `[TR]` p. 29 · `proved`

> [α]P ⊨ Q
> ──────────────
> [α]P ⊨ [α]Q

**Printed proof, transcribed.** By inspection.

**Lean.** `BoCa.Fig16.BoLo.box_R`, aliases `TR.lemma_6_98`, `TR.«[]r»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.98 (`[]r`, p. 29).  `[as printed]` -/
theorem box_R {α : Life} {P Q : SPropU Loc Val} (h : box α P ⊨ Q) : box α P ⊨ box α Q :=
  fun ρ k => ⟨h ρ k, k.2⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_98 := BoCa.Fig16.BoLo.box_R
alias TR.«[]r» := BoCa.Fig16.BoLo.box_R

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.99 ([]4) · `[TR]` p. 29 · `proved`

> [α][β]P ⊨ [α ⊔ β]P

**Printed proof, transcribed.** Case `⊨`: let `P(ρ)`, `@ρ ⊐ α` and `@ρ ⊐ β`; by lattice laws, `@ρ ⊐ α ⊔ β`.  Case `⫤`: let `P(ρ)` and `@ρ ⊐ α ⊔ β`; by lattice laws, `@ρ ⊐ α` and `@ρ ⊐ β`.

**Lean.** `BoCa.Fig16.BoLo.box_4`, aliases `TR.lemma_6_99`, `TR.«[]4»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.99 (`[]4`, p. 29).  `[as printed]` -/
theorem box_4 (α β : Life) (P : SPropU Loc Val) : box α (box β P) ⊨ box (α ⊔ β) P := by
  rintro ρ ⟨⟨hP, h₂⟩, h₁⟩
  exact ⟨hP, ResU.InStratum.sup h₁ h₂⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_99 := BoCa.Fig16.BoLo.box_4
alias TR.«[]4» := BoCa.Fig16.BoLo.box_4

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.100 ([]⊒) · `[TR]` p. 29 · `proved`

> α ⊒ β
> ──────────────
> [α]P ⊨ [β]P

**Printed proof, transcribed.** Suppose `α ⊒ β`, and let `P(ρ)` and `@ρ ⊐ α`.  By transitivity, `@ρ ⊐ α ⊒ β`; thus `@ρ ⊐ β`.

**Lean.** `BoCa.Fig16.BoLo.box_antitone`, aliases `TR.lemma_6_100`, `TR.«[]⊒»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.100 (`[] ⊒`, p. 29).  `[as printed]` -/
theorem box_antitone {α β : Life} (h : β ⊑ α) (P : SPropU Loc Val) :
    box α P ⊨ box β P := fun _ k => ⟨k.1, k.2.mono h⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_100 := BoCa.Fig16.BoLo.box_antitone
alias TR.«[]⊒» := BoCa.Fig16.BoLo.box_antitone

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.101 ([]∃r) · `[TR]` p. 30 · `proved`

> P ⊨ ∃α. [α]P

**Printed proof, transcribed.** Let `P(ρ)`.  Choose `α` to be `↓@ρ`.  By Lemma 6.63, `@ρ ⊐ ↓@ρ`.

**Lean.** `BoCa.Fig16.BoLo.box_ex_R`, aliases `TR.lemma_6_101`, `TR.«[]∃r»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.101 (`[]∃r`, p. 30).  `[as printed]` -/
theorem box_ex_R (P : SPropU Loc Val) : P ⊨ ex (fun α => box α P) := by
  intro ρ hP
  obtain ⟨a, ha⟩ := ρ.exists_atLife
  exact ⟨↓a, hP, outlives_of_atLife ha (Nat.lt_succ_self a)⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_101 := BoCa.Fig16.BoLo.box_ex_R
alias TR.«[]∃r» := BoCa.Fig16.BoLo.box_ex_R

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.102 ([]∀) · `[TR]` p. 30 · `proved*`

> ∀x. [α]P(x) ⫤⊨ [α]∀x. P(x)

**Printed proof, transcribed.** Case `⊨`: suppose `X ≠ ∅`, and let `∀x ∈ X. P̂(x)(ρ) ∧ @ρ ⊐ α`; since `X ≠ ∅`, `@ρ ⊐ α` and `∀x ∈ X. P̂(x)(ρ)`.  Case `⫤`: similar, without the domain restriction on `x`.

**Lean.** `BoCa.Fig16.BoLo.box_all`, aliases `TR.lemma_6_102`, `TR.«[]∀»`.

**Literal reading.** `BoCa.Fig16.BoLo.box_all_needs_nonempty`, in `Paper/LiteralReadings/S6_5_NonStandardEntailments.lean`.

**Note.** `[restricted: to a nonempty index type]` — as 6.88; [TR]'s proof of the `⊨` direction opens "Suppose X ≠ ∅".
-/
/-- `[TR]` Lemma 6.102 (`[]∀`, p. 30).  `[restricted: to a nonempty index type]` -/
theorem box_all {A : Type} (hA : Nonempty A) (α : Life) (Φ : A → SPropU Loc Val) :
    all (fun x => box α (Φ x)) ⫤⊨ box α (all Φ) := by
  constructor
  · intro ρ h
    obtain ⟨x₀⟩ := hA
    exact ⟨fun x => (h x).1, (h x₀).2⟩
  · exact fun ρ h x => ⟨h.1 x, h.2⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_102 := BoCa.Fig16.BoLo.box_all
alias TR.«[]∀» := BoCa.Fig16.BoLo.box_all

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.103 ([]∃) · `[TR]` p. 30 · `proved`

> ∃x. [α]P(x) ⫤⊨ [α]∃x. P(x)

**Printed proof, transcribed.** Case `⊨`: let `P̂(x)(ρ)` for some `x` and `@ρ ⊐ α`; choose `x`.  Immediate.  Case `⫤`: similar.

**Lean.** `BoCa.Fig16.BoLo.box_ex`, aliases `TR.lemma_6_103`, `TR.«[]∃»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.103 (`[]∃`, p. 30).  `[as printed]` -/
theorem box_ex {A : Type} (α : Life) (Φ : A → SPropU Loc Val) :
    ex (fun x => box α (Φ x)) ⫤⊨ box α (ex Φ) :=
  ⟨fun _ h => h.elim fun x hx => ⟨⟨x, hx.1⟩, hx.2⟩,
   fun _ h => h.1.elim fun x hx => ⟨x, hx, h.2⟩⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_103 := BoCa.Fig16.BoLo.box_ex
alias TR.«[]∃» := BoCa.Fig16.BoLo.box_ex

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.104 ([]⋆) · `[TR]` p. 30 · `proved`

> [α](P ⋆ Q) ⫤⊨ [α]P ⋆ [α]Q

**Printed proof, transcribed.** Case `⊨`: let `ρ = ρ₁ ● ρ₂` with `P(ρ₁)`, `Q(ρ₂)` and `@(ρ₁ ● ρ₂) ⊐ α`; choose `ρ₁, ρ₂`.  It suffices that `@ρ₁ ⊐ α` and `@ρ₂ ⊐ α`, which follows by Lemma 6.45.  Case `⫤`: similar.

**Lean.** `BoCa.Fig16.BoLo.box_sep`, aliases `TR.lemma_6_104`, `TR.«[]⋆»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.104 (`[]⋆`, p. 30).  `[as printed]` -/
theorem box_sep (α : Life) (P Q : SPropU Loc Val) :
    box α (P ⋆ Q) ⫤⊨ box α P ⋆ box α Q := by
  constructor
  · rintro ρ ⟨⟨ρ₁, ρ₂, hc, hP, hQ⟩, ho⟩
    obtain ⟨o₁, o₂⟩ := (outlives_comp hc α).mp ho
    exact ⟨ρ₁, ρ₂, hc, ⟨hP, o₁⟩, ⟨hQ, o₂⟩⟩
  · rintro ρ ⟨ρ₁, ρ₂, hc, ⟨hP, o₁⟩, ⟨hQ, o₂⟩⟩
    exact ⟨⟨ρ₁, ρ₂, hc, hP, hQ⟩, (outlives_comp hc α).mpr ⟨o₁, o₂⟩⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_104 := BoCa.Fig16.BoLo.box_sep
alias TR.«[]⋆» := BoCa.Fig16.BoLo.box_sep

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.105 ([]∨) · `[TR]` p. 30 · `proved`

> [α](P ∨ Q) ⫤⊨ [α]P ∨ [α]Q

**Printed proof, transcribed.** Case `⊨`: let `(P(ρ) ∨ Q(ρ)) ∧ @ρ ⊐ α`; it suffices that `(P(ρ) ∧ @ρ ⊐ α) ∨ (Q(ρ) ∧ @ρ ⊐ α)`, which follows by De Morgan's laws.  Case `⫤`: similar.

**Lean.** `BoCa.Fig16.BoLo.box_or`, aliases `TR.lemma_6_105`, `TR.«[]∨»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.105 (`[]∨`, p. 30).  `[as printed]` -/
theorem box_or (α : Life) (P Q : SPropU Loc Val) :
    box α (or P Q) ⫤⊨ or (box α P) (box α Q) :=
  ⟨fun _ h => h.1.elim (fun k => Or.inl ⟨k, h.2⟩) (fun k => Or.inr ⟨k, h.2⟩),
   fun _ h => h.elim (fun k => ⟨Or.inl k.1, k.2⟩) (fun k => ⟨Or.inr k.1, k.2⟩)⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_105 := BoCa.Fig16.BoLo.box_or
alias TR.«[]∨» := BoCa.Fig16.BoLo.box_or

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.106 ([]!) · `[TR]` p. 30 · `proved`

> [α]!P ⫤⊨ ![α]P

**Printed proof, transcribed.** By inspection.

**Lean.** `BoCa.Fig16.BoLo.box_bang`, aliases `TR.lemma_6_106`, `TR.«[]!»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.106 (`[]!`, p. 30).  `[as printed]` -/
theorem box_bang (α : Life) (P : SPropU Loc Val) :
    box α (!ₛP) ⫤⊨ !ₛ(box α P) :=
  ⟨fun _ h => ⟨h.1.1, h.1.2, h.2⟩, fun _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_106 := BoCa.Fig16.BoLo.box_bang
alias TR.«[]!» := BoCa.Fig16.BoLo.box_bang

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.107 ([]↦) · `[TR]` p. 30 · `proved`

> ℓ ↦ v ⊨ [α]ℓ ↦ v

**Printed proof, transcribed.** By inspection.

**Lean.** `BoCa.Fig16.BoLo.box_ptoOwn`, aliases `TR.lemma_6_107`, `TR.«[]↦»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.107 (`[]↦`, p. 30).  `[as printed]` -/
theorem box_ptoOwn (α : Life) (l : Loc) (v : Val) :
    ptoOwn l v ⊨ box α (ptoOwn l v) := by
  rintro ρ rfl
  refine ⟨rfl, fun k ψ e => ?_⟩
  by_cases hk : k = l
  · subst hk; rw [ResU.single_get_self] at e
    cases Option.some.inj e; exact trivial
  · rw [ResU.single_get_ne _ hk] at e; exact absurd e (by simp)

end BoCa.Fig16.BoLo

alias TR.lemma_6_107 := BoCa.Fig16.BoLo.box_ptoOwn
alias TR.«[]↦» := BoCa.Fig16.BoLo.box_ptoOwn

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.108 (И-mono) · `[TR]` p. 30 · `proved`

> ∀α ⊏ β′. ([α]P(α) ⊨ [α]Q(α))
> ─────────────────────────────
> Иα. P(α) ⊨ Иα. Q(α)

**Printed proof, transcribed.** A table of steps.  Unfold `И`: `∃β. ∀α ⊏ β. [α]P(α) ⊨ ∃β. ∀α ⊏ β. [α]Q(α)`.  Apply `∃L`; choose `β ≔ β ⊓ β′` on the right; fix `α ⊏ β ⊓ β′`: `(∀α ⊏ β. [α]P(α)) ⊨ [α]Q(α)`.  Choose `α ≔ α` on the left: `[α]P(α) ⊨ [α]Q(α)`.  Follows by assumption because `α ⊏ β′`.

**Lean.** `BoCa.Fig16.BoLo.fresh_mono`, aliases `TR.lemma_6_108`, `TR.«И-mono»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.108 (`⋔-mono`, p. 30).  `[as printed]` -/
theorem fresh_mono {β' : Life} {P Q : Life → SPropU Loc Val}
    (h : ∀ α, α ⊏ β' → (box α (P α) ⊨ box α (Q α))) : fresh P ⊨ fresh Q := by
  rintro ρ ⟨β, hβ⟩
  refine ⟨β ⊓ β', fun α hα => ?_⟩
  have k₁ : α ⊏ β := Nat.lt_of_le_of_lt (leMaxL β β') hα
  have k₂ : α ⊏ β' := Nat.lt_of_le_of_lt (leMaxR β β') hα
  exact h α k₂ ρ (hβ α k₁)

end BoCa.Fig16.BoLo

alias TR.lemma_6_108 := BoCa.Fig16.BoLo.fresh_mono
alias TR.«И-mono» := BoCa.Fig16.BoLo.fresh_mono

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.109 (Иl) · `[TR]` p. 30 · `proved`

> ∀α ⊏ β′. ([α]P(α) ⊨ Q)
> ───────────────────────
> Иα. P(α) ⊨ Q

**Printed proof, transcribed.** A table of steps.  Unfold `И`: `∃β. ∀α ⊏ β. [α]P(α) ⊨ Q`.  Fix `β` arbitrary: `∀α ⊏ β. [α]P(α) ⊨ Q`.  Choose arbitrary `α ⊏ β ⊓ β′`, always possible since `⊏` is infinitely decreasing: `[α]P(α) ⊨ Q`.  Follows by assumption because `α ⊏ β′`.

**Lean.** `BoCa.Fig16.BoLo.fresh_L`, aliases `TR.lemma_6_109`, `TR.«Иl»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.109 (`⋔l`, p. 30).  `[as printed]` -/
theorem fresh_L {β' : Life} {P : Life → SPropU Loc Val} {Q : SPropU Loc Val}
    (h : ∀ α, α ⊏ β' → (box α (P α) ⊨ Q)) : fresh P ⊨ Q := by
  rintro ρ ⟨β, hβ⟩
  have k₁ : (↓(β ⊓ β')) ⊏ β := Nat.lt_succ_of_le (leMaxL β β')
  have k₂ : (↓(β ⊓ β')) ⊏ β' := Nat.lt_succ_of_le (leMaxR β β')
  exact h _ k₂ ρ (hβ _ k₁)

end BoCa.Fig16.BoLo

alias TR.lemma_6_109 := BoCa.Fig16.BoLo.fresh_L
alias TR.«Иl» := BoCa.Fig16.BoLo.fresh_L

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.110 (Иr) · `[TR]` p. 30 · `proved`

> P ⊨ Иα. P

**Printed proof, transcribed.** A table of steps.  Unfold `И`: `P ⊨ ∃β. ∀α ⊏ β. [α]P`.  Apply `[]∃R` on the left: `∃β. [β]P ⊨ ∃β. ∀α ⊏ β. [α]P`.  Fix `β`; choose `β ≔ β`: `[β]P ⊨ ∀α ⊏ β. [α]P`.  Fix `α ⊏ β`: `[β]P ⊨ [α]P`.  Apply `[]⊒`.

**Lean.** `BoCa.Fig16.BoLo.fresh_R`, aliases `TR.lemma_6_110`, `TR.«Иr»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.110 (`⋔r`, p. 30).  `[as printed]` -/
theorem fresh_R (P : SPropU Loc Val) : P ⊨ fresh (fun _ => P) := by
  intro ρ hP
  obtain ⟨a, ha⟩ := ρ.exists_atLife
  exact ⟨a, fun α hα => ⟨hP, outlives_of_atLife ha hα⟩⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_110 := BoCa.Fig16.BoLo.fresh_R
alias TR.«Иr» := BoCa.Fig16.BoLo.fresh_R

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.111 (И⋆) · `[TR]` p. 31 · `proved`

> Иα. P(α) ⋆ Иα. Q(α) ⊨ Иα. (P(α) ⋆ Q(α))

**Printed proof, transcribed.** A table of steps.  Unfold `И`: `(∃β_P. ∀α_P ⊏ β_P. P(α_P)) ⋆ (∃β_Q. ∀α_Q ⊏ β_Q. Q(α_Q)) ⊨ ∃β. ∀α ⊏ β. (P(α) ⋆ Q(α))`.  Fix `β_P, β_Q`; choose `β ≔ β_P ⊓ β_Q`; fix `α ⊏ β_P ⊓ β_Q`; choose `α_P ≔ α`, `α_Q ≔ α`: `P(α) ⋆ Q(α) ⊨ P(α) ⋆ Q(α)`.

**Lean.** `BoCa.Fig16.BoLo.fresh_sep`, aliases `TR.lemma_6_111`, `TR.«И⋆»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.111 (`⋔⋆`, p. 31).  `[as printed]` -/
theorem fresh_sep (P Q : Life → SPropU Loc Val) :
    (fresh P ⋆ fresh Q) ⊨ fresh (fun α => P α ⋆ Q α) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, ⟨β₁, h₁⟩, ⟨β₂, h₂⟩⟩
  refine ⟨β₁ ⊓ β₂, fun α hα => ?_⟩
  obtain ⟨hP, o₁⟩ := h₁ α (lt_of_lt_of_le hα inf_le_left)
  obtain ⟨hQ, o₂⟩ := h₂ α (lt_of_lt_of_le hα inf_le_right)
  exact ⟨⟨ρ₁, ρ₂, hc, hP, hQ⟩, (outlives_comp hc α).mpr ⟨o₁, o₂⟩⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_111 := BoCa.Fig16.BoLo.fresh_sep
alias TR.«И⋆» := BoCa.Fig16.BoLo.fresh_sep

/-!
## Lemma 6.112 (Иf) · `[TR]` p. 31 · `proved`

> P ⋆ Иα. Q(α) ⊨ Иα. ([α]P ⋆ Q(α))

**Printed proof, transcribed.** A chain: `P ⋆ Иα. Q(α) ⊨ ∃β. [β]P ⋆ Иα. Q(α)` by `[]∃r`; `⊨ ∃β. [β][β]P ⋆ Иα. Q(α)` by `[]4`; `⊨ (∃β. ∀α ⊏ β. [α][α]P) ⋆ Иα. Q(α)` by `[]⊒` and monotonicity; `⊨ Иα. [α]P ⋆ Иα. Q(α)` by the definition of `И`; `⊨ Иα. ([α]P ⋆ Q(α))` by `И⋆`.

**Lean.** `BoCa.Fig16.BoLo.fresh_frame`, aliases `TR.lemma_6_112`, `TR.«Иf»`, tag `[as printed]` — declared in `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean`, ahead of this subsection: the Lean of Lemmas 6.64 and 6.65 there needs it.
-/
alias TR.lemma_6_112 := BoCa.Fig16.BoLo.fresh_frame
alias TR.«Иf» := BoCa.Fig16.BoLo.fresh_frame

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.113 (I-mono) · `[TR]` p. 31 · `proved`

> ∀v. P̂(v) ⊨ Q̂(v)
> ──────────────────────
> ℓ ↦I_α P̂ ⊨ ℓ ↦I_α Q̂

**Printed proof, transcribed.** Suppose `∀v. P̂(v) ⊨ Q̂(v)`, and let `ρ = ℓ ↦ imm(β̃, v, ρ′)` with `P̂(v)(ρ′)` and `α ⊑ ⊔β̃`.  Choose `β̃, v, ρ′`; it suffices that `Q̂(v)(ρ′)`, which follows from the premise and `P̂(v)(ρ′)`.

**Lean.** `BoCa.Fig16.BoLo.ptoImm_mono`, aliases `TR.lemma_6_113`, `TR.«I-mono»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.ptoImmS_mono`, in `Support/TypedWorld/RelationFacts.lean`.
-/
/-- `[TR]` Lemma 6.113 (`I-mono`, p. 31).  `[as printed]` -/
theorem ptoImm_mono {l : Loc} {α : Life} {P Q : Val → SPropU Loc Val}
    (h : ∀ v, P v ⊨ Q v) : ptoImm l α P ⊨ ptoImm l α Q := by
  rintro ρ ⟨s, v, σ, hs, rfl, hP, hα⟩
  exact ⟨s, v, σ, hs, rfl, h v σ hP, hα⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_113 := BoCa.Fig16.BoLo.ptoImm_mono
alias TR.«I-mono» := BoCa.Fig16.BoLo.ptoImm_mono

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.114 (I⊒) · `[TR]` p. 31 · `proved`

> α ⊒ β
> ──────────────────────
> ℓ ↦I_α P̂ ⊨ ℓ ↦I_β P̂

**Printed proof, transcribed.** Suppose `α ⊒ β`, and let `ρ = ℓ ↦ imm(β̃, v, ρ′)` with `P̂(v)(ρ′)` and `α ⊑ ⊔β̃`.  Choose `β̃, v, ρ′`; it suffices that `β ⊑ ⊔β̃`, which follows by transitivity, `β ⊑ α ⊑ ⊔β̃`.

**Lean.** `BoCa.Fig16.BoLo.ptoImm_antitone`, aliases `TR.lemma_6_114`, `TR.«I⊒»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.114 (`I ⊒`, p. 31).  `[as printed]` -/
theorem ptoImm_antitone {l : Loc} {α β : Life} (h : β ⊑ α) (P : Val → SPropU Loc Val) :
    ptoImm l α P ⊨ ptoImm l β P := by
  rintro ρ ⟨s, v, σ, hs, rfl, hP, hα⟩
  exact ⟨s, v, σ, hs, rfl, hP, Nat.le_trans hα h⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_114 := BoCa.Fig16.BoLo.ptoImm_antitone
alias TR.«I⊒» := BoCa.Fig16.BoLo.ptoImm_antitone

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.115 (I-ag) · `[TR]` p. 31 · `variant`

> ℓ ↦I_α P̂ ⋆ ℓ ↦I_β Q̂ ⊨ ℓ ↦I_{α⊔β} (P̂ ∧ Q̂)

**Printed proof, transcribed.** Let `ρ = ρ₁ ● ρ₂` with `ρ₁ = ℓ ↦ imm(β̃₁, v₁, ρ′₁)`, `P̂(v₁)(ρ′₁)`, `α ⊑ ⊔β̃₁`, `ρ₂ = ℓ ↦ imm(β̃₂, v₂, ρ′₂)`, `Q̂(v₂)(ρ′₂)` and `β ⊑ ⊔β̃₂`; the goal is `∃β̃, v, ρ′. ρ = ℓ ↦ imm(β̃, v, ρ′) ∧ P̂(v)(ρ′) ∧ Q̂(v)(ρ′) ∧ α ⊔ β ⊑ ⊔β̃`.  By definition, `ρ = ℓ ↦ imm(β̃₁ ∪ β̃₂, v₁, ρ′₁)`, `v₁ = v₂` and `ρ′₁ = ρ′₂`.  Choose `β̃₁ ∪ β̃₂, v₁, ρ′₁`; everything is immediate except `α ⊔ β ⊑ ⊔(β̃₁ ∪ β̃₂)`, which follows from the lattice laws given `α ⊑ ⊔β̃₁` and `β ⊑ ⊔β̃₂`.

**Lean.** `BoCa.Fig16.BoLo.ptoImm_agree`, aliases `TR.lemma_6_115`, `TR.«I-ag»`, tag `[variant: the conclusion's index is `α ⊓ β` where the print has `α ⊔ β`; with
`ptoImm` at `⊓β̄` (`docs/adjudications.md` §12.67) the union's meet is bounded by
`α ⊓ β` and not by `α ⊔ β` — `not_iAgreeAtJoin`.  `ptoImm_agree_eq` is the
equal-index case, `[CONF]`.

**Also here.** `BoCa.Fig16.BoLo.ptoImm_agree_eq`.

**Literal reading.** `BoCa.Fig16.BoLo.not_iAgreeAtJoin`, in `Paper/LiteralReadings/S6_5_NonStandardEntailments.lean`.

**Note.** `[variant: conclusion at `α ⊓ β` where the print has `α ⊔ β`]`, at `ℓ ↦ Imm α P̂` bounded by `⊓β̄` (definition row 5.30, `docs/adjudications.md` §12.67(a)): `●` unions the lifetime sets, and `⊓(β̄₁ ∪ β̄₂) = ⊓β̄₁ ⊓ ⊓β̄₂`.  `ptoImm_agree_eq` is the equal-index case, where the printed conclusion is reached — [CONF] 415:13 describes `I Agree` as aliases that "all agree on the lifetime".
-/
/-- `[TR]` Lemma 6.115 (`I-ag`, p. 31).  `[variant: conclusion at `α ⊓ β`]` -/
theorem ptoImm_agree (l : Loc) (α β : Life) (P Q : Val → SPropU Loc Val) :
    (ptoImm l α P ⋆ ptoImm l β Q) ⊨ ptoImm l (α ⊓ β) (fun v => and (P v) (Q v)) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, ⟨s, v₁, σ₁, h₁, rfl, hP, hα⟩, ⟨t, v₂, σ₂, h₂, rfl, hQ, hβ⟩⟩
  obtain ⟨rfl, rfl⟩ := ResU.compatS_single_imm_inv hc.1
  have h₃ : σ₁.InStratum (s ∪ t).join := by
    intro k ψ e
    cases ψ with
    | own w => exact trivial
    | imm i => exact sup_lt_iff.mpr ⟨h₁ k _ e, h₂ k _ e⟩
    | «mut» m => exact sup_lt_iff.mpr ⟨h₁ k _ e, h₂ k _ e⟩
  refine ⟨s ∪ t, v₁, σ₁, h₃,
    ResU.CompS.functional hc (ResU.compS_single_imm l s t v₁ σ₁ h₁ h₂ h₃),
    ⟨hP, hQ⟩, ?_⟩
  exact inf_le_inf hα hβ

end BoCa.Fig16.BoLo

alias TR.lemma_6_115 := BoCa.Fig16.BoLo.ptoImm_agree
alias TR.«I-ag» := BoCa.Fig16.BoLo.ptoImm_agree

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-! A declaration the record of Lemma 6.115 (I-ag) cites. -/
/-- `[TR]` Lemma 6.115 at equal indices, where the printed conclusion is reached.
`[restricted: to `α = β`]` -/
theorem ptoImm_agree_eq (l : Loc) (α : Life) (P Q : Val → SPropU Loc Val) :
    (ptoImm l α P ⋆ ptoImm l α Q) ⊨ ptoImm l α (fun v => and (P v) (Q v)) := by
  intro ρ h
  have := ptoImm_agree l α α P Q ρ h
  rwa [inf_idem] at this

/-!
## Lemma 6.116 (I-dup) · `[TR]` p. 31 · `proved`

> ℓ ↦I_α P̂ ⊨ ℓ ↦I_α P̂ ⋆ ℓ ↦I_α P̂

**Printed proof, transcribed.** Let `ρ = ℓ ↦ imm(β̃, v, ρ′)` with `P̂(v)(ρ′)` and `α ⊑ ⊔β̃`.  Choose `ρ₁, ρ₂` to be `ρ, ρ`; it suffices that `ρ = ρ ● ρ`, which follows from Lemma 6.43.

**Lean.** `BoCa.Fig16.BoLo.ptoImm_dup`, aliases `TR.lemma_6_116`, `TR.«I-dup»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.116 (`I-dup`, p. 31).  `[as printed]` -/
theorem ptoImm_dup (l : Loc) (α : Life) (P : Val → SPropU Loc Val) :
    ptoImm l α P ⊨ ptoImm l α P ⋆ ptoImm l α P := by
  rintro ρ ⟨s, v, σ, hs, rfl, hP, hα⟩
  have h₃ : σ.InStratum (s ∪ s).join := ResU.InStratum.sup hs hs
  have e : CellU.immOf (s ∪ s) v σ h₃ = CellU.immOf s v σ hs :=
    CellU.immOf_congr (LSet.union_self s) rfl rfl h₃ hs
  have hcomp := ResU.compS_single_imm l s s v σ hs hs h₃
  rw [e] at hcomp
  exact ⟨_, _, hcomp, ⟨s, v, σ, hs, rfl, hP, hα⟩, ⟨s, v, σ, hs, rfl, hP, hα⟩⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_116 := BoCa.Fig16.BoLo.ptoImm_dup
alias TR.«I-dup» := BoCa.Fig16.BoLo.ptoImm_dup

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.117 (M-inv) · `[TR]` p. 32 · `proved`

> ∀v. P̂(v) ⫤⊨ Q̂(v)
> ─────────────────────────
> ℓ ↦M_α P̂ ⫤⊨ ℓ ↦M_α Q̂

**Printed proof, transcribed.** By inspection, using functional extensionality.

**Lean.** `BoCa.Fig16.BoLo.ptoMut_inv`, aliases `TR.lemma_6_117`, `TR.«M-inv»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.117 (`M-inv`, p. 32).  `[as printed]` -/
theorem ptoMut_inv {l : Loc} {α : Life} {P Q : Val → SPropU Loc Val}
    (h : ∀ v, P v ⫤⊨ Q v) : ptoMut l α P ⫤⊨ ptoMut l α Q := by
  have e : P = Q := funext fun v => eq_of_biEntails (h v)
  subst e
  exact BiEntails.refl _

end BoCa.Fig16.BoLo

alias TR.lemma_6_117 := BoCa.Fig16.BoLo.ptoMut_inv
alias TR.«M-inv» := BoCa.Fig16.BoLo.ptoMut_inv

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.118 (M⊒) · `[TR]` p. 32 · `proved`

> α ⊒ β
> ──────────────────────
> ℓ ↦M_α P̂ ⊨ ℓ ↦M_β P̂

**Printed proof, transcribed.** Suppose `α ⊒ β`, and let `ρ = ℓ ↦ mut(β₀, v, ρ′, P̂)` for some `β₀ ⊒ α`, `v`, `ρ′`.  Choose `β₀, v, ρ′`; it suffices that `β₀ ⊒ β`, by transitivity `β₀ ⊒ α ⊒ β`.

**Lean.** `BoCa.Fig16.BoLo.ptoMut_antitone`, aliases `TR.lemma_6_118`, `TR.«M⊒»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.118 (`M ⊒`, p. 32).  `[as printed]` -/
theorem ptoMut_antitone {l : Loc} {α β : Life} (h : β ⊑ α) (P : Val → SPropU Loc Val) :
    ptoMut l α P ⊨ ptoMut l β P := by
  rintro ρ ⟨b, v, σ, hs, Q, hw, hb, rfl, hd⟩
  exact ⟨b, v, σ, hs, Q, hw, Nat.le_trans hb h, rfl, hd⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_118 := BoCa.Fig16.BoLo.ptoMut_antitone
alias TR.«M⊒» := BoCa.Fig16.BoLo.ptoMut_antitone

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-! A declaration the record of Lemma 6.119 (M-ex) cites. -/
/-- `ℓ ↦M_α P̂ ⋆ ℓ ↦ _ ⊨ ⊥` with `_` read as a cell of any kind.
`[variant: of [TR] Lemma 6.119, whose `_` is an elided value]` -/
theorem ptoMut_excl (l : Loc) (α : Life) (P : Val → SPropU Loc Val) :
    (ptoMut l α P ⋆ ptoAny l) ⊨ bot := by
  rintro ρ ⟨ρ₁, ρ₂, ⟨hc, -⟩, ⟨b, v, σ, hs, Q, hw, -, rfl, -⟩, ψ, rfl⟩
  have h := ResU.compatS_single_mut hc
  rw [ResU.single_get_self] at h
  exact absurd h (by simp)

/-!
## Lemma 6.119 (M-ex) · `[TR]` p. 32 · `proved`

> ℓ ↦M_α P̂ ⋆ ℓ ↦ _ ⊨ ⊥

**Printed proof, transcribed.** By inspection, using Lemma 6.42.

**Lean.** `BoCa.Fig16.BoLo.ptoMut_excl_own`, aliases `TR.lemma_6_119`, `TR.«M-ex»`, tag `[as printed]`.

**Also here.** `BoCa.Fig16.BoLo.ptoMut_excl`.

**Note.** The elided value is bound at the theorem, as in 6.95.  `ptoMut_excl` reads `_` as a cell of any kind, `[variant]`.
-/
/-- `[TR]` Lemma 6.119 (`M-ex`, p. 32).  `[as printed]` -/
theorem ptoMut_excl_own (l : Loc) (α : Life) (P : Val → SPropU Loc Val) (v : Val) :
    (ptoMut l α P ⋆ ptoOwn l v) ⊨ bot :=
  Entails.trans (sep_mono (Entails.refl _) (ptoAny_of_own l v)) (ptoMut_excl l α P)

end BoCa.Fig16.BoLo

alias TR.lemma_6_119 := BoCa.Fig16.BoLo.ptoMut_excl_own
alias TR.«M-ex» := BoCa.Fig16.BoLo.ptoMut_excl_own

end
