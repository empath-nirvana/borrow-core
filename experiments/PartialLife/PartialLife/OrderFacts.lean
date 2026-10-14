import PartialLife.Cell

/-!
# PartialLife — the order facts behind the census

The census (`scripts/Census.lean`, `scripts/classify.py`) sorts the library's uses of the lifetime
order. This file states the order fact behind each class and checks it on `TwoBranches`
(`ℕᵒᵈ × ℕᵒᵈ`, `Cell.lean`).

**Class (iii)**, a comparison of two lifetimes no relation is known between. Each of the three
facts it uses is, in a lattice, *equivalent* to every two lifetimes being comparable:

* `sup_lt_iff_chain`: `a < c → b < c → a ⊔ b < c` for all `a, b, c` (`sup_lt_iff.mpr`,
  `Nat.le_total` on joins): the witness of a union of borrower sets lies in `Res_{⊔(ᾱ ∪ β̄)}`
  (`CellU.InStratum.sup`, `ResU.InStratum.sup`, `CellU.compS_assoc`, `CellU.compR_assoc_forward`,
  `ptoImm_agree`, `LSet.union`);
* `lt_inf_iff_chain`: `γ < a → γ < b → γ < a ⊓ b` for all `γ, a, b` (`lt_inf_iff.mpr`,
  `Nat.max_lt`): a composite `imm` cell at `⊓(ᾱ ∪ β̄)`, and `○`'s `mut(α ⊓ β, …)`, stays in every
  stratum both parts are in (`CellU.CompS.inStratum`, `cellCompS_inStratum`, `cellCompR_inStratum`,
  `ResU.atLife_comp_sqsupset`);
* `le_of_not_lt_iff_chain`: `¬ a < b → b ≤ a` for all `a, b`, in any partial order
  (`le_of_not_gt`: `frameLife_reb_like`).

At `TwoBranches` each fails (`sup_lt_fails`, `lt_inf_fails`, `not_lt_not_ge`).

**Class (ii)**, `⊓`, `⊔`, a lifetime beneath finitely many. `TwoBranches` is a lattice and has a
lifetime strictly beneath any finitely many (`exists_lt_all`); the three-point order `Vee` has none
beneath its two branches (`vee_no_lower_bound`, `Cell.lean`).

**Class (iv)**, `ρ ∈ Res_{↓α}` read as "every cell is `⊒ α`": it needs a `c ⊏ α` such that every
lifetime strictly above `c` is `⊒ α` (`Life.le_of_down_lt`, with `c = ↓α`). On each branch of
`TwoBranches` there is one (`down_on_branch`); at the meet of the two branches' first lifetimes there
is none (`no_down_at_meet`): `(1, 1)` has two lifetimes just above every lifetime below it.
-/

noncomputable section

namespace PartialLife

section Chain
variable {L : Type}

/-- **`γ < a → γ < b → γ < a ⊓ b` for all triples holds exactly in a chain.** -/
theorem lt_inf_iff_chain [Lattice L] :
    (∀ γ a b : L, γ < a → γ < b → γ < a ⊓ b) ↔ ∀ a b : L, a ≤ b ∨ b ≤ a := by
  constructor
  · intro h a b
    by_contra hab
    simp only [not_or] at hab
    have h₁ : a ⊓ b < a := lt_of_le_of_ne inf_le_left fun e => hab.1 (inf_eq_left.mp e)
    have h₂ : a ⊓ b < b := lt_of_le_of_ne inf_le_right fun e => hab.2 (inf_eq_right.mp e)
    exact lt_irrefl _ (h _ _ _ h₁ h₂)
  · intro htot γ a b ha hb
    rcases htot a b with h | h
    · rwa [inf_eq_left.mpr h]
    · rwa [inf_eq_right.mpr h]

/-- **`a < c → b < c → a ⊔ b < c` for all triples holds exactly in a chain.** -/
theorem sup_lt_iff_chain [Lattice L] :
    (∀ a b c : L, a < c → b < c → a ⊔ b < c) ↔ ∀ a b : L, a ≤ b ∨ b ≤ a := by
  constructor
  · intro h a b
    by_contra hab
    simp only [not_or] at hab
    have h₁ : a < a ⊔ b := lt_of_le_of_ne le_sup_left fun e => hab.2 (sup_eq_left.mp e.symm)
    have h₂ : b < a ⊔ b := lt_of_le_of_ne le_sup_right fun e => hab.1 (sup_eq_right.mp e.symm)
    exact lt_irrefl _ (h _ _ _ h₁ h₂)
  · intro htot a b c ha hb
    rcases htot a b with h | h
    · rwa [sup_eq_right.mpr h]
    · rwa [sup_eq_left.mpr h]

/-- **`¬ a < b → b ≤ a` for all pairs holds exactly in a chain.** -/
theorem le_of_not_lt_iff_chain [PartialOrder L] :
    (∀ a b : L, ¬ a < b → b ≤ a) ↔ ∀ a b : L, a ≤ b ∨ b ≤ a := by
  constructor
  · intro h a b
    by_cases hab : a < b
    · exact Or.inl hab.le
    · exact Or.inr (h a b hab)
  · intro htot a b hab
    rcases htot a b with h | h
    · rcases eq_or_lt_of_le h with rfl | h
      · exact le_rfl
      · exact absurd h hab
    · exact h

end Chain

/-! ### At `TwoBranches` -/

theorem br₁_lt_top' {n : ℕ} (h : n ≠ 0) : br₁ n < ⊤ :=
  lt_of_le_of_ne le_top fun e => h (by
    have := congrArg (fun p : TwoBranches => OrderDual.ofDual p.1) e
    simpa [br₁] using this)

theorem br₂_lt_top' {m : ℕ} (h : m ≠ 0) : br₂ m < ⊤ :=
  lt_of_le_of_ne le_top fun e => h (by
    have := congrArg (fun p : TwoBranches => OrderDual.ofDual p.2) e
    simpa [br₂] using this)

/-- `(1, 1)`, the meet of the two branches' first lifetimes. -/
def meet₁₁ : TwoBranches := (OrderDual.toDual 1, OrderDual.toDual 1)

theorem meet₁₁_eq : br₁ 1 ⊓ br₂ 1 = meet₁₁ := rfl

theorem meet₁₁_lt_br₁ : meet₁₁ < br₁ 1 := by
  rw [Prod.lt_iff]; exact Or.inr ⟨le_rfl, by decide⟩

theorem meet₁₁_lt_br₂ : meet₁₁ < br₂ 1 := by
  rw [Prod.lt_iff]; exact Or.inl ⟨by decide, le_rfl⟩

/-- `a < c` and `b < c`, and not `a ⊔ b < c`. -/
theorem sup_lt_fails : br₁ 1 < ⊤ ∧ br₂ 1 < ⊤ ∧ ¬ br₁ 1 ⊔ br₂ 1 < ⊤ :=
  ⟨br₁_lt_top' (by decide), br₂_lt_top' (by decide), fun h => lt_irrefl _ (by
    rwa [show br₁ 1 ⊔ br₂ 1 = ⊤ from rfl] at h)⟩

/-- `γ < a` and `γ < b`, and not `γ < a ⊓ b`. -/
theorem lt_inf_fails : meet₁₁ < br₁ 1 ∧ meet₁₁ < br₂ 1 ∧ ¬ meet₁₁ < br₁ 1 ⊓ br₂ 1 :=
  ⟨meet₁₁_lt_br₁, meet₁₁_lt_br₂, fun h => lt_irrefl _ (by rwa [meet₁₁_eq] at h)⟩

/-- Neither `a < b` nor `b ≤ a`. -/
theorem not_lt_not_ge : ¬ br₁ 1 < br₂ 1 ∧ ¬ br₂ 1 ≤ br₁ 1 :=
  ⟨fun h => (br_incomparable (n := 1) (m := 1) (by decide) (by decide)).1 h.le,
    (br_incomparable (n := 1) (m := 1) (by decide) (by decide)).2⟩

/-- `TwoBranches` is not a chain. -/
theorem twoBranches_not_chain : ¬ ∀ a b : TwoBranches, a ≤ b ∨ b ≤ a := fun h =>
  (h (br₁ 1) (br₂ 1)).elim (br_incomparable (n := 1) (m := 1) (by decide) (by decide)).1
    (br_incomparable (n := 1) (m := 1) (by decide) (by decide)).2

/-- `≤` on `TwoBranches`, coordinatewise in `ℕ`, reversed. -/
theorem tb_le_iff (p q : TwoBranches) :
    p ≤ q ↔ OrderDual.ofDual q.1 ≤ OrderDual.ofDual p.1 ∧ OrderDual.ofDual q.2 ≤ OrderDual.ofDual p.2 :=
  Iff.rfl

theorem tb_lt_iff (p q : TwoBranches) :
    p < q ↔ (OrderDual.ofDual q.1 ≤ OrderDual.ofDual p.1 ∧ OrderDual.ofDual q.2 ≤ OrderDual.ofDual p.2) ∧
      p ≠ q := by
  rw [lt_iff_le_and_ne, tb_le_iff]

/-- **A lifetime strictly beneath any finitely many** (class (ii) at `TwoBranches`). -/
theorem exists_lt_all (S : List TwoBranches) : ∃ c : TwoBranches, ∀ p ∈ S, c < p := by
  set k : ℕ := (S.map fun p => OrderDual.ofDual p.1 + OrderDual.ofDual p.2).sum + 1 with hk
  refine ⟨(OrderDual.toDual k, OrderDual.toDual k), fun p hp => ?_⟩
  have hle : OrderDual.ofDual p.1 + OrderDual.ofDual p.2 ≤
      (S.map fun p => OrderDual.ofDual p.1 + OrderDual.ofDual p.2).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hp)
  rw [tb_lt_iff]
  refine ⟨⟨?_, ?_⟩, fun e => ?_⟩
  · show OrderDual.ofDual p.1 ≤ k
    omega
  · show OrderDual.ofDual p.2 ≤ k
    omega
  · have := congrArg (fun q : TwoBranches => OrderDual.ofDual q.1) e
    simp only [OrderDual.ofDual_toDual] at this
    omega

/-- **On a branch, `↓α` exists**: a lifetime beneath `br₁ n` every lifetime strictly above which is
`⊒ br₁ n`. -/
theorem down_on_branch (n : ℕ) :
    ∃ c : TwoBranches, c < br₁ n ∧ ∀ b, c < b → br₁ n ≤ b := by
  refine ⟨br₁ (n + 1), ?_, fun ⟨b₁, b₂⟩ hb => ?_⟩
  · rw [tb_lt_iff]
    refine ⟨⟨?_, le_rfl⟩, fun e => ?_⟩
    · show n ≤ n + 1; omega
    · have := congrArg (fun q : TwoBranches => OrderDual.ofDual q.1) e
      simp [br₁] at this
  · rw [tb_lt_iff] at hb
    obtain ⟨⟨h₁, h₂⟩, hne⟩ := hb
    change OrderDual.ofDual b₁ ≤ n + 1 at h₁
    change OrderDual.ofDual b₂ ≤ 0 at h₂
    rw [tb_le_iff]
    refine ⟨?_, ?_⟩
    · show OrderDual.ofDual b₁ ≤ n
      rcases Nat.lt_or_ge (OrderDual.ofDual b₁) (n + 1) with h | h
      · omega
      · exfalso
        apply hne
        have e₁ : OrderDual.ofDual b₁ = n + 1 := by omega
        have e₂ : OrderDual.ofDual b₂ = 0 := by omega
        simp only [br₁, Prod.mk.injEq]
        exact ⟨congrArg OrderDual.toDual e₁.symm, congrArg OrderDual.toDual e₂.symm⟩
    · show OrderDual.ofDual b₂ ≤ 0
      exact h₂

/-- **At the meet of the two branches' first lifetimes there is no `↓α`**: every lifetime `c`
beneath `meet₁₁` has a lifetime strictly above it that is not `⊒ meet₁₁`. -/
theorem no_down_at_meet : ¬ ∃ c : TwoBranches, c < meet₁₁ ∧ ∀ b, c < b → meet₁₁ ≤ b := by
  rintro ⟨⟨c₁, c₂⟩, hc, hup⟩
  rw [tb_lt_iff] at hc
  obtain ⟨⟨h₁, h₂⟩, hne⟩ := hc
  change 1 ≤ OrderDual.ofDual c₁ at h₁
  change 1 ≤ OrderDual.ofDual c₂ at h₂
  rcases Nat.lt_or_ge 1 (OrderDual.ofDual c₁) with hc₁ | hc₁
  · -- `c₁ ≥ 2`: `(c₁, 0)` is above `c` and not above `meet₁₁`
    have hb := hup (c₁, OrderDual.toDual 0) (by
      rw [tb_lt_iff]
      refine ⟨⟨le_rfl, ?_⟩, fun e => ?_⟩
      · show 0 ≤ OrderDual.ofDual c₂; omega
      · have := congrArg (fun q : TwoBranches => OrderDual.ofDual q.2) e
        simp only [OrderDual.ofDual_toDual] at this
        omega)
    rw [tb_le_iff] at hb
    change OrderDual.ofDual c₁ ≤ 1 ∧ _ at hb
    omega
  · -- `c₁ = 1`, so `c₂ ≥ 2`: `(0, c₂)` is above `c` and not above `meet₁₁`
    have hc₂ : 1 < OrderDual.ofDual c₂ := by
      by_contra h
      apply hne
      have e₁ : OrderDual.ofDual c₁ = 1 := by omega
      have e₂ : OrderDual.ofDual c₂ = 1 := by omega
      simp only [meet₁₁, Prod.mk.injEq]
      exact ⟨congrArg OrderDual.toDual e₁, congrArg OrderDual.toDual e₂⟩
    have hb := hup (OrderDual.toDual 0, c₂) (by
      rw [tb_lt_iff]
      refine ⟨⟨?_, le_rfl⟩, fun e => ?_⟩
      · show 0 ≤ OrderDual.ofDual c₁; omega
      · have := congrArg (fun q : TwoBranches => OrderDual.ofDual q.1) e
        simp only [OrderDual.ofDual_toDual] at this
        omega)
    rw [tb_le_iff] at hb
    change _ ∧ OrderDual.ofDual c₂ ≤ 1 at hb
    omega

end PartialLife

end
