import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Notation
import Support.Model.Propositions

/-!
# [TR] §6.4 Standard Entailments  (physical pp. 27–29), Lemmas 6.67–6.95

The sequent rules of the propositions of `[TR]` p. 6 that do not unfold the
carrier: `⊨` reflexive and transitive (6.67, 6.68), the connectives `⊤ ⊥ ∧ ∨ ⇒ ∀ ∃`
(6.69–6.80), `⌜−⌝` (6.81, 6.82), `!` (6.83–6.89), `⋆` and `–⋆` (6.90–6.94), and
exclusivity of `ℓ ↦ v` (6.95).  Each is printed with its name, which is the second
alias `TR.«name»`; a rule the print states schematically in `i ∈ {1, 2}` (6.72, 6.73)
is two declarations with aliases `TR.lemma_6_N_i`.  Records as in §6.1's file.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.67 (refl) · `[TR]` p. 27 · `proved`

> P ⊨ P

**Printed proof, transcribed.** By inspection.

**Lean.** `BoCa.Fig16.BoLo.Entails.refl`, aliases `TR.lemma_6_67`, `TR.refl`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.67 (`refl`, p. 27).  `[as printed]` -/
theorem Entails.refl (P : SPropU Loc Val) : P ⊨ P := fun _ h => h

end BoCa.Fig16.BoLo

alias TR.lemma_6_67 := BoCa.Fig16.BoLo.Entails.refl
alias TR.refl := BoCa.Fig16.BoLo.Entails.refl

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.68 (trans) · `[TR]` p. 27 · `proved`

> P ⊨ Q    Q ⊨ R
> ─────────────
> P ⊨ R

**Printed proof, transcribed.** Suppose `P ⊨ Q` and `Q ⊨ R`, and let `P(ρ)`.  By `P ⊨ Q`, `Q(ρ)`; by `Q ⊨ R`, `R(ρ)`.

**Lean.** `BoCa.Fig16.BoLo.Entails.trans`, aliases `TR.lemma_6_68`, `TR.trans`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.68 (`trans`, p. 27).  `[as printed]` -/
theorem Entails.trans {P Q R : SPropU Loc Val} (h₁ : P ⊨ Q) (h₂ : Q ⊨ R) : P ⊨ R :=
  fun ρ h => h₂ ρ (h₁ ρ h)

end BoCa.Fig16.BoLo

alias TR.lemma_6_68 := BoCa.Fig16.BoLo.Entails.trans
alias TR.trans := BoCa.Fig16.BoLo.Entails.trans

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.69 (⊤r) · `[TR]` p. 27 · `proved`

> P ⊨ ⊤

**Printed proof, transcribed.** By inspection.

**Lean.** `BoCa.Fig16.BoLo.top_R`, aliases `TR.lemma_6_69`, `TR.«⊤r»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.69 (`⊤r`, p. 27).  `[as printed]` -/
theorem top_R (P : SPropU Loc Val) : P ⊨ top := fun _ _ => trivial

end BoCa.Fig16.BoLo

alias TR.lemma_6_69 := BoCa.Fig16.BoLo.top_R
alias TR.«⊤r» := BoCa.Fig16.BoLo.top_R

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.70 (⊥l) · `[TR]` p. 27 · `proved`

> ⊥ ⊨ P

**Printed proof, transcribed.** By inspection.

**Lean.** `BoCa.Fig16.BoLo.bot_L`, aliases `TR.lemma_6_70`, `TR.«⊥l»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.70 (`⊥l`, p. 27).  `[as printed]` -/
theorem bot_L (P : SPropU Loc Val) : bot ⊨ P := fun _ h => h.elim

end BoCa.Fig16.BoLo

alias TR.lemma_6_70 := BoCa.Fig16.BoLo.bot_L
alias TR.«⊥l» := BoCa.Fig16.BoLo.bot_L

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.71 (∧r) · `[TR]` p. 27 · `proved`

> P ⊨ Q₁    P ⊨ Q₂
> ───────────────
> P ⊨ Q₁ ∧ Q₂

**Printed proof, transcribed.** Suppose `P ⊨ Q₁` and `P ⊨ Q₂`, and let `P(ρ)`.  By the first, `Q₁(ρ)`; by the second, `Q₂(ρ)`.

**Lean.** `BoCa.Fig16.BoLo.and_R`, aliases `TR.lemma_6_71`, `TR.«∧r»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.71 (`∧r`, p. 27).  `[as printed]` -/
theorem and_R {P Q₁ Q₂ : SPropU Loc Val} (h₁ : P ⊨ Q₁) (h₂ : P ⊨ Q₂) : P ⊨ and Q₁ Q₂ :=
  fun ρ h => ⟨h₁ ρ h, h₂ ρ h⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_71 := BoCa.Fig16.BoLo.and_R
alias TR.«∧r» := BoCa.Fig16.BoLo.and_R

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.72 (∧l) · `[TR]` p. 27 · `proved`

> P₁ ∧ P₂ ⊨ Pᵢ

**Printed proof, transcribed.** By inspection.

The print states one rule schematic in `i ∈ {1, 2}`; Lean states it once per `i`, and the two aliases carry the index.

**Lean.** `BoCa.Fig16.BoLo.and_L₁`, aliases `TR.lemma_6_72_1`, `TR.«∧l₁»`, tag `[as printed]`; `BoCa.Fig16.BoLo.and_L₂`, aliases `TR.lemma_6_72_2`, `TR.«∧l₂»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.72 (`∧l`, p. 27) at `i = 1`.  `[as printed]` -/
theorem and_L₁ (P₁ P₂ : SPropU Loc Val) : and P₁ P₂ ⊨ P₁ := fun _ h => h.1

end BoCa.Fig16.BoLo

alias TR.lemma_6_72_1 := BoCa.Fig16.BoLo.and_L₁
alias TR.«∧l₁» := BoCa.Fig16.BoLo.and_L₁

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-! Lemma 6.72 (∧l), continued. -/
/-- `[TR]` Lemma 6.72 (`∧l`, p. 27) at `i = 2`.  `[as printed]` -/
theorem and_L₂ (P₁ P₂ : SPropU Loc Val) : and P₁ P₂ ⊨ P₂ := fun _ h => h.2

end BoCa.Fig16.BoLo

alias TR.lemma_6_72_2 := BoCa.Fig16.BoLo.and_L₂
alias TR.«∧l₂» := BoCa.Fig16.BoLo.and_L₂

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.73 (∨r) · `[TR]` p. 27 · `proved`

> Pᵢ ⊨ P₁ ∨ P₂

**Printed proof, transcribed.** Let `Pᵢ(ρ)`.  Since `i ∈ {1, 2}`, `P₁(ρ) ∨ P₂(ρ)`.

Schematic in `i`, as Lemma 6.72.

**Lean.** `BoCa.Fig16.BoLo.or_R₁`, aliases `TR.lemma_6_73_1`, `TR.«∨r₁»`, tag `[as printed]`; `BoCa.Fig16.BoLo.or_R₂`, aliases `TR.lemma_6_73_2`, `TR.«∨r₂»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.73 (`∨r`, p. 27) at `i = 1`.  `[as printed]` -/
theorem or_R₁ (P₁ P₂ : SPropU Loc Val) : P₁ ⊨ or P₁ P₂ := fun _ h => Or.inl h

end BoCa.Fig16.BoLo

alias TR.lemma_6_73_1 := BoCa.Fig16.BoLo.or_R₁
alias TR.«∨r₁» := BoCa.Fig16.BoLo.or_R₁

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-! Lemma 6.73 (∨r), continued. -/
/-- `[TR]` Lemma 6.73 (`∨r`, p. 27) at `i = 2`.  `[as printed]` -/
theorem or_R₂ (P₁ P₂ : SPropU Loc Val) : P₂ ⊨ or P₁ P₂ := fun _ h => Or.inr h

end BoCa.Fig16.BoLo

alias TR.lemma_6_73_2 := BoCa.Fig16.BoLo.or_R₂
alias TR.«∨r₂» := BoCa.Fig16.BoLo.or_R₂

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.74 (∨l) · `[TR]` p. 27 · `proved`

> P₁ ⊨ Q    P₂ ⊨ Q
> ───────────────
> P₁ ∨ P₂ ⊨ Q

**Printed proof, transcribed.** Suppose `P₁ ⊨ Q` and `P₂ ⊨ Q`, and let `P₁(ρ) ∨ P₂(ρ)`.  By cases on the disjunction.

**Lean.** `BoCa.Fig16.BoLo.or_L`, aliases `TR.lemma_6_74`, `TR.«∨l»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.74 (`∨l`, p. 27).  `[as printed]` -/
theorem or_L {P₁ P₂ Q : SPropU Loc Val} (h₁ : P₁ ⊨ Q) (h₂ : P₂ ⊨ Q) : or P₁ P₂ ⊨ Q :=
  fun ρ h => h.elim (h₁ ρ) (h₂ ρ)

end BoCa.Fig16.BoLo

alias TR.lemma_6_74 := BoCa.Fig16.BoLo.or_L
alias TR.«∨l» := BoCa.Fig16.BoLo.or_L

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.75 (⇒r) · `[TR]` p. 27 · `proved`

> P ∧ Q ⊨ R
> ──────────
> P ⊨ Q ⇒ R

**Printed proof, transcribed.** Suppose `P ∧ Q ⊨ R`, let `P(ρ)` and suppose `Q(ρ)`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.imp_R`, aliases `TR.lemma_6_75`, `TR.«⇒r»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.75 (`⇒r`, p. 27).  `[as printed]` -/
theorem imp_R {P Q R : SPropU Loc Val} (h : and P Q ⊨ R) : P ⊨ imp Q R :=
  fun ρ hP hQ => h ρ ⟨hP, hQ⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_75 := BoCa.Fig16.BoLo.imp_R
alias TR.«⇒r» := BoCa.Fig16.BoLo.imp_R

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.76 (⇒l) · `[TR]` p. 28 · `proved`

> P ∧ (P ⇒ Q) ⊨ Q

**Printed proof, transcribed.** By inspection.

**Lean.** `BoCa.Fig16.BoLo.imp_L`, aliases `TR.lemma_6_76`, `TR.«⇒l»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.76 (`⇒l`, p. 28).  `[as printed]` -/
theorem imp_L (P Q : SPropU Loc Val) : and P (imp P Q) ⊨ Q := fun _ h => h.2 h.1

end BoCa.Fig16.BoLo

alias TR.lemma_6_76 := BoCa.Fig16.BoLo.imp_L
alias TR.«⇒l» := BoCa.Fig16.BoLo.imp_L

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.77 (∀r) · `[TR]` p. 28 · `proved`

> ∀x. (P ⊨ Q(x))
> ──────────────
> P ⊨ ∀x. Q(x)

**Printed proof, transcribed.** Suppose `∀x. P ⊨ Q̂(x)`, let `P(ρ)` and let `x` be arbitrary.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.all_R`, aliases `TR.lemma_6_77`, `TR.«∀r»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.77 (`∀r`, p. 28).  `[as printed]` -/
theorem all_R {A : Type} {P : SPropU Loc Val} {Φ : A → SPropU Loc Val}
    (h : ∀ x, P ⊨ Φ x) : P ⊨ all Φ := fun ρ hP x => h x ρ hP

end BoCa.Fig16.BoLo

alias TR.lemma_6_77 := BoCa.Fig16.BoLo.all_R
alias TR.«∀r» := BoCa.Fig16.BoLo.all_R

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.78 (∀l) · `[TR]` p. 28 · `proved`

> P(x) ⊨ Q
> ──────────────────
> (∀x. P(x)) ⊨ Q

**Printed proof, transcribed.** Suppose `P̂(x) ⊨ Q`, and let `ρ`, `x` be such that `P̂(x)(ρ)`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.all_L`, aliases `TR.lemma_6_78`, `TR.«∀l»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.78 (`∀l`, p. 28).  `[as printed]` -/
theorem all_L {A : Type} {Φ : A → SPropU Loc Val} {Q : SPropU Loc Val} (x : A)
    (h : Φ x ⊨ Q) : all Φ ⊨ Q := fun ρ hP => h ρ (hP x)

end BoCa.Fig16.BoLo

alias TR.lemma_6_78 := BoCa.Fig16.BoLo.all_L
alias TR.«∀l» := BoCa.Fig16.BoLo.all_L

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.79 (∃r) · `[TR]` p. 28 · `proved`

> P ⊨ Q(x)
> ──────────────
> P ⊨ ∃x. Q(x)

**Printed proof, transcribed.** Suppose `P ⊨ Q̂(x)` and let `P(ρ)`.  Choose `x`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.ex_R`, aliases `TR.lemma_6_79`, `TR.«∃r»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.79 (`∃r`, p. 28).  `[as printed]` -/
theorem ex_R {A : Type} {P : SPropU Loc Val} {Φ : A → SPropU Loc Val} (x : A)
    (h : P ⊨ Φ x) : P ⊨ ex Φ := fun ρ hP => ⟨x, h ρ hP⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_79 := BoCa.Fig16.BoLo.ex_R
alias TR.«∃r» := BoCa.Fig16.BoLo.ex_R

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.80 (∃l) · `[TR]` p. 28 · `proved`

> ∀x. (P(x) ⊨ Q)
> ──────────────────
> (∃x. P(x)) ⊨ Q

**Printed proof, transcribed.** Suppose `P̂(x) ⊨ Q`, and let `x`, `ρ` be such that `P̂(x)(ρ)`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.ex_L`, aliases `TR.lemma_6_80`, `TR.«∃l»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.80 (`∃l`, p. 28).  `[as printed]` -/
theorem ex_L {A : Type} {Φ : A → SPropU Loc Val} {Q : SPropU Loc Val}
    (h : ∀ x, Φ x ⊨ Q) : ex Φ ⊨ Q := fun ρ hP => hP.elim fun x hx => h x ρ hx

end BoCa.Fig16.BoLo

alias TR.lemma_6_80 := BoCa.Fig16.BoLo.ex_L
alias TR.«∃l» := BoCa.Fig16.BoLo.ex_L

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.81 (⌜⌝r) · `[TR]` p. 28 · `proved`

> Q_meta
> ──────────────────
> P ⊨ P ⋆ ⌜Q_meta⌝

**Printed proof, transcribed.** Suppose `Q_meta` and let `P(ρ)`.  Choose `ρ₁, ρ₂` to be `ρ, ∅`; then by Lemma 6.4 and inspection.

**Lean.** `BoCa.Fig16.BoLo.pure_R`, aliases `TR.lemma_6_81`, `TR.«⌜⌝r»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.81 (`⌜⌝r`, p. 28).  `[as printed]` -/
theorem pure_R {q : Prop} (hq : q) (P : SPropU Loc Val) : P ⊨ P ⋆ ⌜q⌝ :=
  fun ρ hP => ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, hP, rfl, hq⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_81 := BoCa.Fig16.BoLo.pure_R
alias TR.«⌜⌝r» := BoCa.Fig16.BoLo.pure_R

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.82 (⌜⌝l) · `[TR]` p. 28 · `proved`

> P_meta ⇒ (Q ⊨ R)
> ──────────────────
> ⌜P_meta⌝ ⋆ Q ⊨ R

**Printed proof, transcribed.** Suppose `P_meta ⇒ (Q ⊨ R)`, and let `ρ = ∅ ● ρ₂` with `P_meta` and `Q(ρ₂)`.  By Lemmas 6.2 and 6.4, `ρ = ρ₂`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.pure_L`, aliases `TR.lemma_6_82`, `TR.«⌜⌝l»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.82 (`⌜⌝l`, p. 28).  `[as printed]` -/
theorem pure_L {p : Prop} {Q R : SPropU Loc Val} (h : p → (Q ⊨ R)) : (⌜p⌝ ⋆ Q) ⊨ R := by
  rintro ρ ⟨ρ₁, ρ₂, hc, ⟨rfl, hp⟩, hQ⟩
  rw [eq_of_compS_empty_left hc]
  exact h hp ρ₂ hQ

end BoCa.Fig16.BoLo

alias TR.lemma_6_82 := BoCa.Fig16.BoLo.pure_L
alias TR.«⌜⌝l» := BoCa.Fig16.BoLo.pure_L

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.83 (!mono) · `[TR]` p. 28 · `proved`

> P ⊨ Q
> ──────────
> !P ⊨ !Q

**Printed proof, transcribed.** Suppose `P ⊨ Q` and let `(!P)(ρ)`.  Unfolding, `ρ = ∅` and `P(∅)`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.bang_mono`, aliases `TR.lemma_6_83`, `TR.«!mono»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.83 (`!mono`, p. 28).  `[as printed]` -/
theorem bang_mono {P Q : SPropU Loc Val} (h : P ⊨ Q) : !ₛP ⊨ !ₛQ :=
  fun ρ hP => ⟨hP.1, h ρ hP.2⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_83 := BoCa.Fig16.BoLo.bang_mono
alias TR.«!mono» := BoCa.Fig16.BoLo.bang_mono

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.84 (!l) · `[TR]` p. 28 · `proved*`

> !P ⊨ Q

**Printed proof, transcribed.** By inspection.

**Lean.** `BoCa.Fig16.BoLo.bang_L`, aliases `TR.lemma_6_84`, `TR.«!l»`.

**Also here.** `BoCa.Fig16.BoLo.bang_L_dereliction`.

**Literal reading.** `BoCa.Fig16.BoLo.bang_L_needs_premise`, in `Paper/LiteralReadings/S6_4_StandardEntailments.lean`.

**Note.** `[restricted: to the premise `P ⊨ Q`]`.  The display (p. 28, 1200 dpi) leaves `Q` free with nothing above the bar; `P ⊨ Q` is the premise 6.78, 6.80 and 6.82 print at this shape, and with it the printed proof is an inspection: `!P ≜ emp ∧ P` gives `P`, and the premise gives `Q`.  `bang_L_dereliction` is the row at `Q ≜ P`, where the premise is 6.67.
-/
/-- `[TR]` Lemma 6.84 (`!l`, p. 28).  `[restricted: to the premise `P ⊨ Q`]` -/
theorem bang_L {P Q : SPropU Loc Val} (h : P ⊨ Q) : !ₛP ⊨ Q :=
  fun ρ hP => h ρ hP.2

end BoCa.Fig16.BoLo

alias TR.lemma_6_84 := BoCa.Fig16.BoLo.bang_L
alias TR.«!l» := BoCa.Fig16.BoLo.bang_L

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-! A declaration the record of Lemma 6.84 (!l) cites. -/
/-- 6.84 at `Q ≜ P`, its premise discharged by 6.67.
`[about ours: the scope of 6.84's added hypothesis]` -/
theorem bang_L_dereliction (P : SPropU Loc Val) : !ₛP ⊨ P :=
  bang_L (Entails.refl P)

/-!
## Lemma 6.85 (!unr) · `[TR]` p. 28 · `proved`

> !P ⫤⊨ !P ⋆ !P

**Printed proof, transcribed.** Case `⊨`: let `ρ = ∅` and `P(∅)`; choose `ρ₁, ρ₂` to be `∅, ∅`.  Case `⫤`: let `ρ = ∅ ● ∅`, `P(∅)` and `P(∅)`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.bang_unr`, aliases `TR.lemma_6_85`, `TR.«!unr»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.85 (`!unr`, p. 28).  `[as printed]` -/
theorem bang_unr (P : SPropU Loc Val) : !ₛP ⫤⊨ !ₛP ⋆ !ₛP := by
  constructor
  · rintro ρ ⟨⟨rfl, -⟩, hP⟩
    exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _,
      ⟨emp_empty, hP⟩, ⟨emp_empty, hP⟩⟩
  · rintro ρ ⟨ρ₁, ρ₂, hc, ⟨⟨rfl, -⟩, hP⟩, ⟨⟨rfl, -⟩, -⟩⟩
    rw [eq_of_compS_empty_left hc]
    exact ⟨emp_empty, hP⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_85 := BoCa.Fig16.BoLo.bang_unr
alias TR.«!unr» := BoCa.Fig16.BoLo.bang_unr

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.86 (!∧) · `[TR]` p. 28 · `proved`

> (!P) ∧ Q ⊨ (!P) ⋆ Q

**Printed proof, transcribed.** Let `ρ = ∅`, `P(∅)` and `Q(∅)`.  Choosing `ρ₁, ρ₂` to be `∅, ∅`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.bang_and`, aliases `TR.lemma_6_86`, `TR.«!∧»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.86 (`!∧`, p. 28).  `[as printed]` -/
theorem bang_and (P Q : SPropU Loc Val) : and (!ₛP) Q ⊨ (!ₛP) ⋆ Q := by
  rintro ρ ⟨⟨⟨rfl, -⟩, hP⟩, hQ⟩
  exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨emp_empty, hP⟩, hQ⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_86 := BoCa.Fig16.BoLo.bang_and
alias TR.«!∧» := BoCa.Fig16.BoLo.bang_and

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.87 (!4) · `[TR]` p. 28 · `proved`

> !P ⊨ !!P

**Printed proof, transcribed.** By inspection.

**Lean.** `BoCa.Fig16.BoLo.bang_4`, aliases `TR.lemma_6_87`, `TR.«!4»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.87 (`!4`, p. 28).  `[as printed]` -/
theorem bang_4 (P : SPropU Loc Val) : !ₛP ⊨ !ₛ!ₛP := fun _ h => ⟨h.1, h⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_87 := BoCa.Fig16.BoLo.bang_4
alias TR.«!4» := BoCa.Fig16.BoLo.bang_4

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.88 (!∀) · `[TR]` p. 28 · `proved*`

> ∀x. !P(x) ⊨ !∀x. P(x)

**Printed proof, transcribed.** Suppose `X ≠ ∅`.  Let `ρ` be such that `∀x ∈ X. ρ = ∅ ∧ P̂(x)(ρ)`.  From `X ≠ ∅`, `ρ = ∅` and `∀x. P̂(x)(ρ)`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.bang_all`, aliases `TR.lemma_6_88`, `TR.«!∀»`.

**Literal reading.** `BoCa.Fig16.BoLo.bang_all_needs_nonempty`, in `Paper/LiteralReadings/S6_4_StandardEntailments.lean`.

**Note.** `[restricted: to a nonempty index type]` — [TR]'s own proof (p. 29) opens "Suppose X ≠ ∅".
-/
/-- `[TR]` Lemma 6.88 (`!∀`, p. 28).  `[restricted: to a nonempty index type]` -/
theorem bang_all {A : Type} (hA : Nonempty A) (Φ : A → SPropU Loc Val) :
    all (fun x => !ₛ(Φ x)) ⊨ !ₛ(all Φ) := by
  intro ρ h
  obtain ⟨x₀⟩ := hA
  exact ⟨(h x₀).1, fun x => (h x).2⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_88 := BoCa.Fig16.BoLo.bang_all
alias TR.«!∀» := BoCa.Fig16.BoLo.bang_all

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.89 (!∃) · `[TR]` p. 29 · `proved`

> ∃x. !P(x) ⊨ !∃x. P(x)

**Printed proof, transcribed.** Let `ρ = ∅` and `P̂(x)(∅)` for some `x`.  Choose `x`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.bang_ex`, aliases `TR.lemma_6_89`, `TR.«!∃»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.89 (`!∃`, p. 29).  `[as printed]` -/
theorem bang_ex {A : Type} (Φ : A → SPropU Loc Val) :
    ex (fun x => !ₛ(Φ x)) ⊨ !ₛ(ex Φ) := by
  rintro ρ ⟨x, he, hP⟩
  exact ⟨he, x, hP⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_89 := BoCa.Fig16.BoLo.bang_ex
alias TR.«!∃» := BoCa.Fig16.BoLo.bang_ex

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.90 (⋆com) · `[TR]` p. 29 · `proved`

> P ⋆ Q ⊨ Q ⋆ P

**Printed proof, transcribed.** By inspection, using Lemma 6.2.

**Lean.** `BoCa.Fig16.BoLo.sep_comm`, aliases `TR.lemma_6_90`, `TR.«⋆com»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.90 (`⋆com`, p. 29).  `[as printed]` -/
theorem sep_comm (P Q : SPropU Loc Val) : (P ⋆ Q) ⊨ Q ⋆ P := by
  rintro ρ ⟨ρ₁, ρ₂, hc, h₁, h₂⟩
  exact ⟨ρ₂, ρ₁, hc.comm, h₂, h₁⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_90 := BoCa.Fig16.BoLo.sep_comm
alias TR.«⋆com» := BoCa.Fig16.BoLo.sep_comm

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.91 (⋆asc) · `[TR]` p. 29 · `proved`

> (P ⋆ Q) ⋆ R ⊨ P ⋆ (Q ⋆ R)

**Printed proof, transcribed.** By inspection, using Lemma 6.3.

**Lean.** `BoCa.Fig16.BoLo.sep_assoc`, aliases `TR.lemma_6_91`, `TR.«⋆asc»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.91 (`⋆asc`, p. 29).  `[as printed]` -/
theorem sep_assoc (P Q R : SPropU Loc Val) : ((P ⋆ Q) ⋆ R) ⊨ P ⋆ (Q ⋆ R) := by
  rintro ρ ⟨ρ₁₂, ρ₃, hc, ⟨ρ₁, ρ₂, hc', hP, hQ⟩, hR⟩
  obtain ⟨ρ₂₃, h₂₃, h₁⟩ := (ResU.CompS.assoc ρ₁ ρ₂ ρ₃ ρ).mpr ⟨ρ₁₂, hc', hc⟩
  exact ⟨ρ₁, ρ₂₃, h₁, hP, ρ₂, ρ₃, h₂₃, hQ, hR⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_91 := BoCa.Fig16.BoLo.sep_assoc
alias TR.«⋆asc» := BoCa.Fig16.BoLo.sep_assoc

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.92 (⋆mono) · `[TR]` p. 29 · `proved`

> P₁ ⊨ Q₁    P₂ ⊨ Q₂
> ──────────────────
> P₁ ⋆ P₂ ⊨ Q₁ ⋆ Q₂

**Printed proof, transcribed.** Suppose `P₁ ⊨ Q₁` and `P₂ ⊨ Q₂`, and let `ρ = ρ₁ ● ρ₂` with `P₁(ρ₁)` and `P₂(ρ₂)`.  Then `Q₁(ρ₁)` and `Q₂(ρ₂)`; choose `ρ₁, ρ₂`.  Immediate.

**Lean.** `BoCa.Fig16.BoLo.sep_mono`, aliases `TR.lemma_6_92`, `TR.«⋆mono»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.92 (`⋆mono`, p. 29).  `[as printed]` -/
theorem sep_mono {P₁ P₂ Q₁ Q₂ : SPropU Loc Val} (h₁ : P₁ ⊨ Q₁) (h₂ : P₂ ⊨ Q₂) :
    (P₁ ⋆ P₂) ⊨ Q₁ ⋆ Q₂ := by
  rintro ρ ⟨ρ₁, ρ₂, hc, k₁, k₂⟩
  exact ⟨ρ₁, ρ₂, hc, h₁ ρ₁ k₁, h₂ ρ₂ k₂⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_92 := BoCa.Fig16.BoLo.sep_mono
alias TR.«⋆mono» := BoCa.Fig16.BoLo.sep_mono

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.93 (–⋆r) · `[TR]` p. 29 · `proved`

> P ⋆ Q ⊨ R
> ──────────────
> P ⊨ Q –⋆ R

**Printed proof, transcribed.** Suppose `P ⋆ Q ⊨ R` and let `P(ρ)`.  Let `ρ₁, ρ₂` be such that `Q(ρ₁)` and `ρ ● ρ₁ = ρ₂`.  By `P ⋆ Q ⊨ R` at `ρ ● ρ₁`, `R(ρ ● ρ₁)`.

**Lean.** `BoCa.Fig16.BoLo.wand_R`, aliases `TR.lemma_6_93`, `TR.«–⋆r»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.93 (`─⋆r`, p. 29).  `[as printed]` -/
theorem wand_R {P Q R : SPropU Loc Val} (h : (P ⋆ Q) ⊨ R) : P ⊨ Q ─⋆ R :=
  fun ρ hP ρ₁ ρ₂ hQ hc => h ρ₂ ⟨ρ, ρ₁, hc, hP, hQ⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_93 := BoCa.Fig16.BoLo.wand_R
alias TR.«–⋆r» := BoCa.Fig16.BoLo.wand_R

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
## Lemma 6.94 (–⋆l) · `[TR]` p. 29 · `proved`

> P ⋆ (P –⋆ Q) ⊨ Q

**Printed proof, transcribed.** Let `ρ = ρ₁ ● ρ₂` with `P(ρ₁)` and `(P –⋆ Q)(ρ₂)`.  By the wand at `ρ₁`, `Q(ρ₂ ● ρ₁)`; by Lemma 6.2, `Q(ρ₁ ● ρ₂)`.

**Lean.** `BoCa.Fig16.BoLo.wand_L`, aliases `TR.lemma_6_94`, `TR.«–⋆l»`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.94 (`─⋆l`, p. 29).  `[as printed]` -/
theorem wand_L (P Q : SPropU Loc Val) : (P ⋆ (P ─⋆ Q)) ⊨ Q := by
  rintro ρ ⟨ρ₁, ρ₂, hc, hP, hw⟩
  exact hw ρ₁ ρ hP hc.comm

end BoCa.Fig16.BoLo

alias TR.lemma_6_94 := BoCa.Fig16.BoLo.wand_L
alias TR.«–⋆l» := BoCa.Fig16.BoLo.wand_L

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-! A declaration the record of Lemma 6.95 (↦ex) cites. -/
/-- `ℓ ↦ v ⋆ ℓ ↦ _ ⊨ ⊥` with `_` read as a cell of any kind.
`[variant: of [TR] Lemma 6.95, whose `_` is an elided value]` -/
theorem ptoOwn_excl (l : Loc) (v : Val) : (ptoOwn l v ⋆ ptoAny l) ⊨ bot := by
  rintro ρ ⟨ρ₁, ρ₂, ⟨hc, -⟩, rfl, ψ, rfl⟩
  have h := ResU.compatS_single_own hc
  rw [ResU.single_get_self] at h
  exact absurd h (by simp)

/-!
## Lemma 6.95 (↦ex) · `[TR]` p. 29 · `proved`

> ℓ ↦ v₁ ⋆ ℓ ↦ _ ⊨ ⊥

**Printed proof, transcribed.** By contradiction, using Lemma 6.41.

**Lean.** `BoCa.Fig16.BoLo.ptoOwn_excl_own`, aliases `TR.lemma_6_95`, `TR.«↦ex»`, tag `[as printed]`.

**Also here.** `BoCa.Fig16.BoLo.ptoOwn_excl`.

**Note.** `↦` in a proposition is the owned form ([TR] p. 6), and 6.41, which the proof cites, elides `ℓ ↦ own(−)` the same way, so the print's `_` is an elided value, bound at the theorem.  `ptoOwn_excl` reads `_` as a cell of any kind, `[variant]`.
-/
/-- `[TR]` Lemma 6.95 (`↦ex`, p. 29).  `[as printed]` -/
theorem ptoOwn_excl_own (l : Loc) (v₁ v₂ : Val) : (ptoOwn l v₁ ⋆ ptoOwn l v₂) ⊨ bot :=
  Entails.trans (sep_mono (Entails.refl _) (ptoAny_of_own l v₂)) (ptoOwn_excl l v₁)

end BoCa.Fig16.BoLo

alias TR.lemma_6_95 := BoCa.Fig16.BoLo.ptoOwn_excl_own
alias TR.«↦ex» := BoCa.Fig16.BoLo.ptoOwn_excl_own

end
