import PartialLife.Interleave
import Frontend.Check.Decide

/-!
# PartialLife — the statics' entailment is read on a chain

`Δ ⊨ @a ⊏ @b` (`LifeCtx.EntailsLt`, `Paper/S2_Statics/Definitions.lean`) quantifies over `ℕ`-valued
lifetime substitutions: it is entailment **on a chain**. The relation over a partial order reads
its typing premises at `L`-valued readings (`EntailsLtP`), and an entailment that holds on every
chain need not hold on a partial order. The checker's search `ordB` (`Frontend/Check/Decide.lean`)
has two strict rules that hold on chains only:

* `@a ⊏ @b₁ ⊓ @b₂` from `@a ⊏ @b₁` and `@a ⊏ @b₂` (`a < b ∧ a < c → a < b ⊓ c`, `lt_inf`);
* `@a₁ ⊔ @a₂ ⊏ @b` from `@a₁ ⊏ @b` and `@a₂ ⊏ @b` (`a < c ∧ b < c → a ⊔ b < c`, `sup_lt`).

At `Δ₂ = 'x ⊏ 'a, 'y ⊏ 'b, 'a ⊏ ⊤, 'b ⊏ ⊤` the checker accepts `'x ⊓ 'y ⊏ 'a ⊓ 'b` and
`'x ⊔ 'y ⊏ ⊤` (`ltB … = true`, so Core's `EntailsLt` holds by `ltB_sound`), and both fail at a
reading of `Δ₂` in `TwoBranches` (`checker_meet_not_partial`, `checker_join_not_partial`). Every
other rule of `ordB` holds in every partial order with its bounds (`≤`, `⊤`, `x ⊏ Δ(x)`, the
non-strict `⊓`/`⊔` rules, and the strict rules that take strictness from one side: `@a₁ ⊓ @a₂ ⊏ @b`
from one `@aᵢ ⊏ @b`, `@a ⊏ @b₁ ⊔ @b₂` from one `@a ⊏ @bᵢ`).

So over a partial order the typing premises are to be read at `L`-valued readings and the two
strict rules dropped from the checker (or kept non-strict). That changes the statics, not the
relation's clauses. Whether any corpus program needs the two rules is not checked here.

`OrderFacts.lean` has the order facts behind the census's classes.
-/

noncomputable section

namespace PartialLife
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check (ltB ltB_sound)
open DenseCarrier (LSubD)

/-! ### Two entailments the checker accepts, false on a partial order -/

/-- `'x ⊓ 'y`. -/
abbrev xMy : Lifetime.Life := .meet (.var xx) (.var xy)
/-- `'a ⊓ 'b`. -/
abbrev aMb : Lifetime.Life := .meet (.var xa) (.var xb)
/-- `'x ⊔ 'y`. -/
abbrev xJy : Lifetime.Life := .join (.var xx) (.var xy)

/-- The checker accepts `'x ⊓ 'y ⊏ 'a ⊓ 'b` at `Δ₂`. -/
theorem checker_meet : ltB Δ₂ xMy aMb = true := by decide

/-- The checker accepts `'x ⊔ 'y ⊏ ⊤` at `Δ₂`. -/
theorem checker_join : ltB Δ₂ xJy .top = true := by decide

/-- Both hold on the chain (Core's `EntailsLt`). -/
theorem entailsLt_meet : Δ₂.EntailsLt xMy aMb := ltB_sound checker_meet
theorem entailsLt_join : Δ₂.EntailsLt xJy .top := ltB_sound checker_join

/-- `(1, 1)`: beneath both branches' first lifetimes, their meet. -/
def bot₁₁ : TwoBranches := (OrderDual.toDual 1, OrderDual.toDual 1)

/-- A reading of `Δ₂` with both borrows at the meet of the two tasks' lifetimes. -/
def δmeet : LSubD TwoBranches :=
  ⟨[(xa, br₁ 1), (xb, br₂ 1), (xx, bot₁₁), (xy, bot₁₁)]⟩

theorem bot₁₁_lt_br₁ : bot₁₁ < br₁ 1 := by
  rw [Prod.lt_iff]; exact Or.inr ⟨le_rfl, by decide⟩

theorem bot₁₁_lt_br₂ : bot₁₁ < br₂ 1 := by
  rw [Prod.lt_iff]; exact Or.inl ⟨by decide, le_rfl⟩

theorem modelsP_δmeet : ModelsP Δ₂ δmeet := by
  intro x u hx
  simp only [Δ₂, LifeCtx.find?, Lifetime.assocFind] at hx
  split_ifs at hx with h₁ h₂ h₃ h₄ <;> cases hx
  · subst h₁; exact ⟨bot₁₁, br₁ 1, rfl, rfl, bot₁₁_lt_br₁⟩
  · subst h₂; exact ⟨bot₁₁, br₂ 1, rfl, rfl, bot₁₁_lt_br₂⟩
  · subst h₃; exact ⟨br₁ 1, ⊤, rfl, rfl, br₁_lt_top (by decide)⟩
  · subst h₄; exact ⟨br₂ 1, ⊤, rfl, rfl, br₂_lt_top (by decide)⟩

theorem br₁_inf_br₂ : br₁ 1 ⊓ br₂ 1 = bot₁₁ := rfl

/-- **The checker's strict `⊓` rule does not hold on a partial order**: `'x ⊓ 'y ⊏ 'a ⊓ 'b` is
accepted at `Δ₂` and fails at the reading `δmeet ∈ ⟦Δ₂⟧` in `TwoBranches`. -/
theorem checker_meet_not_partial :
    ltB Δ₂ xMy aMb = true ∧ Δ₂.EntailsLt xMy aMb ∧ ¬ EntailsLtP TwoBranches Δ₂ xMy aMb := by
  refine ⟨checker_meet, entailsLt_meet, fun h => ?_⟩
  obtain ⟨m, n, hm, hn, hlt⟩ := h δmeet modelsP_δmeet
  have e₁ : interpP δmeet xMy = glbOpt bot₁₁ bot₁₁ := rfl
  have e₂ : interpP δmeet aMb = glbOpt (br₁ 1) (br₂ 1) := rfl
  rw [e₁, glbOpt_eq, inf_idem, Option.some.injEq] at hm
  rw [e₂, glbOpt_eq, br₁_inf_br₂, Option.some.injEq] at hn
  rw [← hm, ← hn] at hlt
  exact lt_irrefl _ hlt

/-- **The checker's strict `⊔` rule does not hold on a partial order**: `'x ⊔ 'y ⊏ ⊤` is accepted at
`Δ₂` and fails at the reading `δ₂ ∈ ⟦Δ₂⟧` in `TwoBranches`, where `br₁ 2 ⊔ br₂ 2 = ⊤`. -/
theorem checker_join_not_partial :
    ltB Δ₂ xJy .top = true ∧ Δ₂.EntailsLt xJy .top ∧ ¬ EntailsLtP TwoBranches Δ₂ xJy .top := by
  refine ⟨checker_join, entailsLt_join, fun h => ?_⟩
  obtain ⟨m, n, hm, hn, hlt⟩ := h δ₂ modelsP_Δ₂
  have e₁ : interpP δ₂ xJy = lubOpt (br₁ 2) (br₂ 2) := rfl
  have e₂ : interpP δ₂ (.top : Lifetime.Life) = some ⊤ := rfl
  have hsup : br₁ 2 ⊔ br₂ 2 = ⊤ := rfl
  rw [e₁, lubOpt_eq, hsup, Option.some.injEq] at hm
  rw [e₂, Option.some.injEq] at hn
  rw [← hm, ← hn] at hlt
  exact lt_irrefl _ hlt

end PartialLife

end
