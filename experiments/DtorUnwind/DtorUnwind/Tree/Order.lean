import Paper.S6_2_NonStandardLemmas.Lemmas

/-!
# The lifetime order as a tree

Row 5.9 orders `Life` as a single chain (`ℕᵒᵈ`): every two lifetimes are comparable. Lends
nested across stored continuations do not form a chain. A task stored in `κ` keeps the
lifetimes it opened; the resumer opens new ones beside them. Those are siblings: neither is
inside the other.

`Cactus` is the order this file puts in its place. `le a b` reads "`a` is `b` or nested inside
it" (`b` outlives `a`, row 5.9's `⊑`). The order is a tree: the lifetimes above any one
lifetime form a chain (`up_chain`), and `⊤` is above all. Lifetimes are still named by `Life`,
and the printed chain is kept as the *allocation order*: a lifetime nested inside another was
opened after it (`sub`). So the printed carrier (row 5.58's well-founded recursion on the chain)
is unchanged, and `Cactus` is the order the model reads when it asks whether one lifetime
outlives another.

Contents:
* `Cactus`, its strict part `lt`, the printed chain as an instance (`chainC`), and `star`, where
  every lifetime other than `⊤` is a child of `⊤` (the configuration of
  `not_fdFromLifetimeTypes`: `a = ⊤`, `α = 1`, `β = 2`).
* What becomes of the operations that compare two lifetimes:
  - a common lower bound exists only for comparable lifetimes (`comparable_of_lower`,
    `star_no_lower`): `α ⊓ β`, `↓(γ ⊓ β)` and `И` combined with `И` have no tree counterpart
    for siblings;
  - a least common upper bound (`⊔`, the nearest common ancestor) always exists
    (`exists_sup`), but `x ⊐ a ⊔ b ↔ x ⊐ a ∧ x ⊐ b` (`sup_lt_iff`) fails for siblings
    (`star_sup_lt_fails`);
  - `↓α` is replaced by a child covering `α` (`Covers`); the fact the printed proofs read of
    `↓α`, that nothing lies strictly between, holds for every covering child
    (`Covers.le_of_lt`), and `↓α` covers `α` in the chain (`chainC_covers_down`);
  - on one branch (every lifetime above a common `n`) every two are comparable
    (`onBranch_comparable`), so every printed comparison among lifetimes of one branch holds.
* The meet of a lifetime set as it is read: `α ⊑ ⊓ᾱ ↔ ∀ x ∈ ᾱ. α ⊑ x` and
  `⊓ᾱ ⊏ x ↔ ∃ y ∈ ᾱ. y ⊏ x` in the chain (`LSet.le_meet_iff`, `LSet.meet_lt_iff`); the tree
  reading takes the right-hand sides.
* Strata in the tree order: `CellU.InStratumT`/`ResU.InStratumT`, inside the printed
  stratum when the order sits inside the chain (`ResU.InStratumT.toChain`) and equal to it in the chain (`ResU.inStratumT_chainC`);
  `Res_{⊔ᾱ}` read as `⋂_{x ∈ ᾱ} Res_x` (`ResU.InStratumAll`), equal to the printed one in the
  chain (`ResU.inStratumAll_chainC`).
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-- **A lifetime order that is a tree.** `le a b`: `a` is `b` or nested inside it. The
lifetimes above any one form a chain (`up_chain`), and `⊤` is above every lifetime. -/
structure Cactus where
  le : Life → Life → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  antisymm : ∀ {a b}, le a b → le b a → a = b
  top : ∀ a, le a ⊤
  up_chain : ∀ {a b c}, le a b → le a c → le b c ∨ le c b

namespace Cactus

/-- Strictly nested inside. -/
def lt (C : Cactus) (a b : Life) : Prop := C.le a b ∧ a ≠ b

theorem lt.le {C : Cactus} {a b : Life} (h : C.lt a b) : C.le a b := h.1

/-- **The order sits inside the printed chain**: a lifetime nested inside another was opened
after it. -/
def InChain (C : Cactus) : Prop := ∀ {a b : Life}, C.le a b → a ≤ b

theorem lt.sub {C : Cactus} (hC : C.InChain) {a b : Life} (h : C.lt a b) : a < b :=
  lt_of_le_of_ne (hC h.1) h.2

theorem lt_irrefl (C : Cactus) (a : Life) : ¬ C.lt a a := fun h => h.2 rfl

theorem lt_of_lt_of_le {C : Cactus} {a b c : Life} (h₁ : C.lt a b) (h₂ : C.le b c) :
    C.lt a c :=
  ⟨C.trans h₁.1 h₂, fun e => by subst e; exact h₁.2 (C.antisymm h₁.1 h₂)⟩

theorem lt_of_le_of_lt {C : Cactus} {a b c : Life} (h₁ : C.le a b) (h₂ : C.lt b c) :
    C.lt a c :=
  ⟨C.trans h₁ h₂.1, fun e => by subst e; exact h₂.2 (C.antisymm h₂.1 h₁)⟩

/-- The printed chain is a cactus. -/
def chainC : Cactus where
  le a b := a ≤ b
  refl a := le_refl a
  trans h₁ h₂ := le_trans h₁ h₂
  antisymm h₁ h₂ := le_antisymm h₁ h₂
  top _ := le_top
  up_chain {_ b c} _ _ := le_total b c

@[simp] theorem chainC_le (a b : Life) : chainC.le a b ↔ a ≤ b := Iff.rfl

theorem chainC_inChain : chainC.InChain := fun h => h

theorem chainC_lt (a b : Life) : chainC.lt a b ↔ a < b :=
  ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨h.le, ne_of_lt h⟩⟩

/-- Every lifetime other than `⊤` is a child of `⊤`: any two of them are siblings. -/
def star : Cactus where
  le a b := a = b ∨ b = ⊤
  refl a := Or.inl rfl
  trans {a b c} h₁ h₂ := by
    rcases h₂ with rfl | rfl
    · exact h₁
    · exact Or.inr rfl
  antisymm {a b} h₁ h₂ := by
    rcases h₁ with h | rfl
    · exact h
    · rcases h₂ with h | h
      · exact h.symm
      · exact h
  top a := Or.inr rfl
  up_chain {a b c} h₁ h₂ := by
    rcases h₁ with rfl | rfl
    · exact Or.inl h₂
    · rcases h₂ with rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl (Or.inl rfl)

theorem star_inChain : star.InChain := by
  intro a b h
  rcases h with rfl | rfl
  · exact le_refl _
  · exact le_top

/-- `n ≠ 0` is a child of `⊤` in `star`. -/
theorem star_lt_top {n : Nat} (hn : n ≠ 0) : star.lt (OrderDual.toDual n) ⊤ :=
  ⟨Or.inr rfl, fun h => hn (by
    have : OrderDual.ofDual (OrderDual.toDual n : Life) = OrderDual.ofDual (⊤ : Life) :=
      congrArg OrderDual.ofDual h
    simpa using this)⟩

/-- Two distinct children of `⊤` are incomparable in `star`. -/
theorem star_not_le {m n : Nat} (hmn : m ≠ n) (hn : n ≠ 0) :
    ¬ star.le (OrderDual.toDual m) (OrderDual.toDual n) := by
  rintro (h | h)
  · exact hmn (OrderDual.toDual.injective h)
  · exact hn (by
      have : OrderDual.ofDual (OrderDual.toDual n : Life) = OrderDual.ofDual (⊤ : Life) :=
        congrArg OrderDual.ofDual h
      simpa using this)

/-! ### Comparisons the printed proofs make, read in a tree -/

/-- **A common lower bound exists only for comparable lifetimes.** So `α ⊓ β`, a lifetime
strictly below two given ones (`↓(γ ⊓ β)`, `[TR]` 6.65 H4, 6.150 H11), and the bound 6.112
computes (`@ρ_P ⊓ β_Q`) exist in a tree only when the two are on one branch. -/
theorem comparable_of_lower (C : Cactus) {a b c : Life} (ha : C.le c a) (hb : C.le c b) :
    C.le a b ∨ C.le b a :=
  C.up_chain ha hb

/-- In `star`, two siblings have no common lower bound. -/
theorem star_no_lower {m n : Nat} (hmn : m ≠ n) (hm : m ≠ 0) (hn : n ≠ 0) :
    ¬ ∃ c, star.le c (OrderDual.toDual m) ∧ star.le c (OrderDual.toDual n) := by
  rintro ⟨c, h₁, h₂⟩
  rcases comparable_of_lower star h₁ h₂ with h | h
  · exact star_not_le hmn hn h
  · exact star_not_le (Ne.symm hmn) hm h

/-- `n` is above every lifetime of `s`, all on one branch below `n`. -/
def OnBranch (C : Cactus) (n : Life) (a : Life) : Prop := C.le n a

/-- **On one branch every two lifetimes are comparable.** -/
theorem onBranch_comparable (C : Cactus) {n a b : Life} (ha : C.OnBranch n a)
    (hb : C.OnBranch n b) : C.le a b ∨ C.le b a :=
  C.up_chain ha hb

/-- `j` is the nearest common ancestor of `a` and `b`. -/
def IsSup (C : Cactus) (a b j : Life) : Prop :=
  C.le a j ∧ C.le b j ∧ ∀ x, C.le a x → C.le b x → C.le j x

/-- **`⊔` exists in a tree inside the chain**: the nearest common ancestor. The common
ancestors of `a` are among the finitely many lifetimes opened before it; the one opened last is
below every other, because they are all above `a` and so form a chain. -/
theorem exists_sup (C : Cactus) (hC : C.InChain) (a b : Life) : ∃ j, C.IsSup a b j := by
  classical
  let P : Nat → Prop := fun k => C.le a (OrderDual.toDual k) ∧ C.le b (OrderDual.toDual k)
  have hP0 : P 0 := ⟨C.top a, C.top b⟩
  let k := Nat.findGreatest P (OrderDual.ofDual a)
  have hk : P k := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  refine ⟨OrderDual.toDual k, hk.1, hk.2, fun x hax hbx => ?_⟩
  rcases C.up_chain hk.1 hax with h | h
  · exact h
  · have hx : OrderDual.ofDual x ≤ OrderDual.ofDual a := hC hax
    have hle : OrderDual.ofDual x ≤ k :=
      Nat.le_findGreatest (P := P) hx ⟨hax, hbx⟩
    have hge : k ≤ OrderDual.ofDual x := hC h
    have : x = OrderDual.toDual k := by
      apply OrderDual.ofDual.injective; simp only [OrderDual.ofDual_toDual]; omega
    subst this
    exact C.refl _

/-- **`x ⊐ a ⊔ b ↔ x ⊐ a ∧ x ⊐ b` fails in a tree.** In `star`, `⊤` is strictly above the
siblings `1` and `2`, and is their nearest common ancestor. -/
theorem star_sup_lt_fails :
    star.IsSup (OrderDual.toDual 1) (OrderDual.toDual 2) ⊤ ∧
      star.lt (OrderDual.toDual 1) ⊤ ∧ star.lt (OrderDual.toDual 2) ⊤ ∧ ¬ star.lt ⊤ ⊤ := by
  refine ⟨⟨Or.inr rfl, Or.inr rfl, fun x h₁ h₂ => ?_⟩, star_lt_top (by decide),
    star_lt_top (by decide), lt_irrefl _ _⟩
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) (fun h => by
        have := congrArg OrderDual.ofDual h; simp at this)
    · exact Or.inl h₂.symm
  · exact Or.inl h₁.symm

/-- **`c` covers `a`**: a child of `a`, with nothing strictly between. The tree's reading of
`↓α` (row 5.12), of which there may be many. -/
def Covers (C : Cactus) (c a : Life) : Prop := C.lt c a ∧ ∀ x, C.lt c x → C.le a x

/-- What the printed proofs read of `↓α` (`Life.not_lt_of_down_lt`, `Life.le_of_down_lt`):
anything strictly above a covering child is above its parent. -/
theorem Covers.le_of_lt {C : Cactus} {c a b : Life} (h : C.Covers c a) (hb : C.lt c b) :
    C.le a b :=
  h.2 b hb

/-- `↓α` covers `α` in the chain. -/
theorem chainC_covers_down (a : Life) : chainC.Covers (Life.down a) a := by
  refine ⟨(chainC_lt _ _).mpr (Life.down_sqsubset a), fun x hx => ?_⟩
  have h1 : OrderDual.ofDual x < OrderDual.ofDual a + 1 := ((chainC_lt _ _).mp hx)
  show OrderDual.ofDual x ≤ OrderDual.ofDual a
  omega

/-- In `star`, every `n ≠ 0` covers `⊤`: `⊤` has infinitely many covering children. -/
theorem star_covers_top {n : Nat} (hn : n ≠ 0) : star.Covers (OrderDual.toDual n) ⊤ := by
  refine ⟨star_lt_top hn, fun x hx => ?_⟩
  rcases hx.1 with h | h
  · exact absurd h hx.2
  · subst h; exact star.refl _

end Cactus

/-! ### The meet of a lifetime set, as it is read -/

/-- `α ⊑ ⊓ᾱ` is `α ⊑ x` at every member. -/
theorem LSet.le_meet_iff (s : LSet) (a : Life) : a ≤ s.meet ↔ ∀ x, s.mem x → a ≤ x :=
  ⟨fun h x hx => le_trans h (s.meet_least x hx), fun h => h _ s.meet_mem⟩

/-- `⊓ᾱ ⊏ x` is `y ⊏ x` at some member. -/
theorem LSet.meet_lt_iff (s : LSet) (x : Life) : s.meet < x ↔ ∃ y, s.mem y ∧ y < x :=
  ⟨fun h => ⟨_, s.meet_mem, h⟩, fun ⟨y, hy, h⟩ => lt_of_le_of_lt (s.meet_least y hy) h⟩

/-! ### Strata in the tree order -/

variable {Loc Val : Type}

/-- `ψ ∈ Cell_α` in the tree order: every lifetime of a borrow cell is strictly above `α`. -/
def CellU.InStratumT (C : Cactus) (α : Life) : CellU Loc Val → Prop
  | .own _ => True
  | .imm i => ∀ x, i.ls.mem x → C.lt α x
  | .mut m => C.lt α m.β

/-- `ρ ∈ Res_α` in the tree order. -/
def ResU.InStratumT (C : Cactus) (α : Life) (ρ : ResU Loc Val) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → CellU.InStratumT C α ψ

theorem CellU.InStratumT.toChain {C : Cactus} (hC : C.InChain) {α : Life} {ψ : CellU Loc Val}
    (h : CellU.InStratumT C α ψ) : ψ.InStratum α := by
  cases ψ with
  | own _ => trivial
  | imm i => exact (h _ i.ls.meet_mem).sub hC
  | «mut» m => exact Cactus.lt.sub hC h

/-- The tree stratum is inside the printed one, when the order sits inside the chain. -/
theorem ResU.InStratumT.toChain {C : Cactus} (hC : C.InChain) {α : Life} {ρ : ResU Loc Val}
    (h : ResU.InStratumT C α ρ) : ρ.InStratum α :=
  fun l ψ e => CellU.InStratumT.toChain hC (h l ψ e)

theorem CellU.inStratumT_chainC (α : Life) (ψ : CellU Loc Val) :
    CellU.InStratumT Cactus.chainC α ψ ↔ ψ.InStratum α := by
  cases ψ with
  | own _ => exact ⟨fun _ => trivial, fun _ => trivial⟩
  | imm i =>
      show (∀ x, i.ls.mem x → Cactus.chainC.lt α x) ↔ α < i.ls.meet
      simp only [Cactus.chainC_lt]
      exact ⟨fun h => h _ i.ls.meet_mem, fun h x hx => lt_of_lt_of_le h (i.ls.meet_least x hx)⟩
  | «mut» m => exact Cactus.chainC_lt _ _

/-- At the printed chain the tree stratum is the printed one. -/
theorem ResU.inStratumT_chainC (α : Life) (ρ : ResU Loc Val) :
    ResU.InStratumT Cactus.chainC α ρ ↔ ρ.InStratum α :=
  ⟨fun h l ψ e => (CellU.inStratumT_chainC α ψ).mp (h l ψ e),
    fun h l ψ e => (CellU.inStratumT_chainC α ψ).mpr (h l ψ e)⟩

/-- `Res_{⊔ᾱ}` read without `⊔`: in the stratum of every member. -/
def ResU.InStratumAll (C : Cactus) (s : LSet) (ρ : ResU Loc Val) : Prop :=
  ∀ x, s.mem x → ResU.InStratumT C x ρ

/-- At the printed chain, `⋂_{x ∈ ᾱ} Res_x = Res_{⊔ᾱ}`. -/
theorem ResU.inStratumAll_chainC (s : LSet) (ρ : ResU Loc Val) :
    ResU.InStratumAll Cactus.chainC s ρ ↔ ρ.InStratum s.join := by
  simp only [ResU.InStratumAll, ResU.inStratumT_chainC]
  exact ⟨fun h => h _ s.join_mem, fun h x hx => h.mono (s.join_greatest x hx)⟩

end BoCa.Fig16.Tree

end
