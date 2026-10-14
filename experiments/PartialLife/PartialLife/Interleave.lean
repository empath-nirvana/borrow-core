import PartialLife.Cell
import PartialLife.Symmetry
import GhostEnd.RLCompat

/-!
# PartialLife — two interleaved suspended borrows

Two tasks each borrow their own local across a suspension: task 1 lends `ℓ₁` at `'x`, task 2 lends
`ℓ₂` at `'y`, and neither borrow outlives the other. On a chain one of `'x`, `'y` is beneath the
other. Here the lifetimes the relation reads are `TwoBranches = ℕᵒᵈ × ℕᵒᵈ` (`Cell.lean`): task 1's
lifetimes on the first branch (`br₁ n`), task 2's on the second (`br₂ m`), incomparable across.

**The reading** `ι₂`: Core's slot `s` is read at `Nat.unpair s` (`ι₂`). It is a bijection from the
slots onto `TwoBranches` (`ι₂_slotOf`, `slotOf_ι₂`), and the slot order extends it (`ι₂_extends`):
the cells stay on Core's chain of slots, which is a schedule, a linear extension, of the lifetimes
they are read at. Two cells at slots `6` and `4` are read at `br₁ 2` and `br₂ 2`.

**The configuration** (`Δ₂`, `δ₂`, `cfg`): the lifetime context `'a ⊏ ⊤, 'b ⊏ ⊤, 'x ⊏ 'a, 'y ⊏ 'b`
read at `'a ↦ br₁ 1`, `'b ↦ br₂ 1`, `'x ↦ br₁ 2`, `'y ↦ br₂ 2` (`modelsP_Δ₂`); each borrow beneath its
own task's lifetime and neither beneath the other or the other task's (`δ₂_shape`); the resource
`ℓ₁ ↦ mut(s₁, (), ∅, 𝒱⟦1⟧) ● ℓ₂ ↦ mut(s₂, (), ∅, 𝒱⟦1⟧)` with `s₁`, `s₂` read at `br₁ 2`, `br₂ 2`.

* `interleaved_world`: it is a typed world (`TW`), hence a valid resource (`ResU.Valid`).
* `interleaved_related`: it is related at `Mut 'x 1 ⊗ Mut 'y 1`, and `return (ℓ₁, ℓ₂)` at
  `F (Mut 'x 1 ⊗ Mut 'y 1)`; `suspended_related`: the two tasks suspended, each a thunk
  `λ_. return ℓᵢ` holding its borrow, are related at `U (F (Mut 'x 1)) ⊗ U (F (Mut 'y 1))`.
* `interleaved_swap`: the automorphism swapping the branches preserves the relation, at both types
  (`vP_map`, `cP_map`); after it the cell at `s₁` is read on the second branch, at `δ₂.map π`'s
  `'x` (`swapped_reading`).

**A fresh lifetime beneath the resumer's** (`fresh_on_branch`): given any finitely many slots (the
cells and records in play) and any lifetime of task 1's branch, there is a slot below every one of
them, which is what Core's proofs pick (`exists_fresh`), read on task 1's branch beneath the given
lifetime and incomparable with every lifetime of task 2 below `⊤`. The schedule puts the new slot
below everything; the reading puts it beneath the resumer's branch only.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace PartialLife
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)
open DenseCarrier (LSubD)
open GhostEnd (innerView unitQ unitQ_holds)

/-! ### The reading of the slots in two branches -/

/-- Slot `s` read at `Nat.unpair s`. -/
def ι₂ : Reading TwoBranches :=
  ⟨fun s => (OrderDual.toDual (Nat.unpair (OrderDual.ofDual s)).1,
      OrderDual.toDual (Nat.unpair (OrderDual.ofDual s)).2), by
    show (OrderDual.toDual (Nat.unpair 0).1, OrderDual.toDual (Nat.unpair 0).2) = ⊤
    rw [Nat.unpair_zero]; rfl⟩

/-- The slot a lifetime of `TwoBranches` is read from. -/
def slotOf (p : TwoBranches) : Life :=
  OrderDual.toDual (Nat.pair (OrderDual.ofDual p.1) (OrderDual.ofDual p.2))

theorem ι₂_slotOf (p : TwoBranches) : ι₂ (slotOf p) = p := by
  obtain ⟨a, b⟩ := p
  show (OrderDual.toDual (Nat.unpair (Nat.pair (OrderDual.ofDual a) (OrderDual.ofDual b))).1,
      OrderDual.toDual (Nat.unpair (Nat.pair (OrderDual.ofDual a) (OrderDual.ofDual b))).2) = (a, b)
  rw [Nat.unpair_pair]; rfl

theorem slotOf_ι₂ (s : Life) : slotOf (ι₂ s) = s := by
  show OrderDual.toDual (Nat.pair (Nat.unpair (OrderDual.ofDual s)).1
    (Nat.unpair (OrderDual.ofDual s)).2) = s
  rw [Nat.pair_unpair]; rfl

theorem pair_le_pair {a b c d : ℕ} (h₁ : a ≤ c) (h₂ : b ≤ d) : Nat.pair a b ≤ Nat.pair c d := by
  rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
  · rcases Nat.eq_or_lt_of_le h₂ with rfl | h₂
    · exact le_rfl
    · exact (Nat.pair_lt_pair_right a h₂).le
  · refine le_trans (Nat.pair_lt_pair_left b h₁).le ?_
    rcases Nat.eq_or_lt_of_le h₂ with rfl | h₂
    · exact le_rfl
    · exact (Nat.pair_lt_pair_right c h₂).le

/-- **The slot order extends the reading**: the slots are a linear extension of `TwoBranches`. -/
theorem ι₂_extends : ι₂.Extends := by
  intro s t hst
  rw [← slotOf_ι₂ s, ← slotOf_ι₂ t]
  generalize ι₂ s = p at hst
  generalize ι₂ t = q at hst
  obtain ⟨⟨p₁, p₂⟩, hp⟩ : ∃ r : ℕ × ℕ, p = (OrderDual.toDual r.1, OrderDual.toDual r.2) :=
    ⟨(OrderDual.ofDual p.1, OrderDual.ofDual p.2), rfl⟩
  obtain ⟨⟨q₁, q₂⟩, hq⟩ : ∃ r : ℕ × ℕ, q = (OrderDual.toDual r.1, OrderDual.toDual r.2) :=
    ⟨(OrderDual.ofDual q.1, OrderDual.ofDual q.2), rfl⟩
  subst hp hq
  show Nat.pair q₁ q₂ < Nat.pair p₁ p₂
  rw [Prod.lt_iff] at hst
  simp only [OrderDual.toDual_le_toDual, OrderDual.toDual_lt_toDual] at hst
  rcases hst with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact lt_of_lt_of_le (Nat.pair_lt_pair_left q₂ h₁) (pair_le_pair le_rfl h₂)
  · exact lt_of_lt_of_le (Nat.pair_lt_pair_right q₁ h₂) (pair_le_pair h₁ le_rfl)

/-! ### The configuration -/

/-- `'a`, `'b`: the two tasks' lifetimes; `'x`, `'y`: their borrows. -/
abbrev xa : LifeVar := 0
abbrev xb : LifeVar := 1
abbrev xx : LifeVar := 2
abbrev xy : LifeVar := 3

/-- `'x ⊏ 'a, 'y ⊏ 'b, 'a ⊏ ⊤, 'b ⊏ ⊤`. -/
def Δ₂ : LifeCtx :=
  ⟨[(xx, .var xa), (xy, .var xb), (xa, .top), (xb, .top)]⟩

/-- `'a ↦ br₁ 1`, `'b ↦ br₂ 1`, `'x ↦ br₁ 2`, `'y ↦ br₂ 2`. -/
def δ₂ : LSubD TwoBranches :=
  ⟨[(xa, br₁ 1), (xb, br₂ 1), (xx, br₁ 2), (xy, br₂ 2)]⟩

theorem br₁_lt_br₁ {n m : ℕ} (h : m < n) : br₁ n < br₁ m := by
  rw [Prod.lt_iff]
  exact Or.inl ⟨OrderDual.toDual_lt_toDual.mpr h, le_rfl⟩

theorem br₂_lt_br₂ {n m : ℕ} (h : m < n) : br₂ n < br₂ m := by
  rw [Prod.lt_iff]
  exact Or.inr ⟨le_rfl, OrderDual.toDual_lt_toDual.mpr h⟩

theorem br₁_lt_top {n : ℕ} (h : n ≠ 0) : br₁ n < ⊤ :=
  lt_of_le_of_ne le_top fun e => h (by
    have := congrArg (fun p : TwoBranches => OrderDual.ofDual p.1) e
    simpa [br₁] using this)

theorem br₂_lt_top {m : ℕ} (h : m ≠ 0) : br₂ m < ⊤ :=
  lt_of_le_of_ne le_top fun e => h (by
    have := congrArg (fun p : TwoBranches => OrderDual.ofDual p.2) e
    simpa [br₂] using this)

/-- **`δ₂ ∈ ⟦Δ₂⟧`** over `TwoBranches`. -/
theorem modelsP_Δ₂ : ModelsP Δ₂ δ₂ := by
  intro x u hx
  simp only [Δ₂, LifeCtx.find?, Lifetime.assocFind] at hx
  split_ifs at hx with h₁ h₂ h₃ h₄ <;> cases hx
  · subst h₁; exact ⟨br₁ 2, br₁ 1, rfl, rfl, br₁_lt_br₁ (by decide)⟩
  · subst h₂; exact ⟨br₂ 2, br₂ 1, rfl, rfl, br₂_lt_br₂ (by decide)⟩
  · subst h₃; exact ⟨br₁ 1, ⊤, rfl, rfl, br₁_lt_top (by decide)⟩
  · subst h₄; exact ⟨br₂ 1, ⊤, rfl, rfl, br₂_lt_top (by decide)⟩

/-- **Each borrow is beneath its own task's lifetime, and neither is beneath the other or beneath
the other task's lifetime.** -/
theorem δ₂_shape :
    br₁ 2 < br₁ 1 ∧ br₂ 2 < br₂ 1 ∧
      ¬ br₁ 2 ≤ br₂ 2 ∧ ¬ br₂ 2 ≤ br₁ 2 ∧ ¬ br₁ 2 ≤ br₂ 1 ∧ ¬ br₂ 2 ≤ br₁ 1 :=
  ⟨br₁_lt_br₁ (by decide), br₂_lt_br₂ (by decide),
    (br_incomparable (by decide) (by decide)).1, (br_incomparable (by decide) (by decide)).2,
    (br_incomparable (by decide) (by decide)).1, (br_incomparable (by decide) (by decide)).2⟩

/-- The slots of the two borrows: read at `br₁ 2` and `br₂ 2`. -/
def s₁ : Life := slotOf (br₁ 2)
def s₂ : Life := slotOf (br₂ 2)

theorem ι₂_s₁ : ι₂ s₁ = br₁ 2 := ι₂_slotOf _
theorem ι₂_s₂ : ι₂ s₂ = br₂ 2 := ι₂_slotOf _

/-- On Core's chain the two slots are comparable: the schedule orders what the reading does not. -/
theorem s₁_lt_s₂ : s₁ < s₂ := by decide

/-- The type of the two borrows, `Mut 'x 1 ⊗ Mut 'y 1`. -/
abbrev twoMut : VTy := .tensor (.mut (.var xx) .unit) (.mut (.var xy) .unit)

/-- **The inner view stores `𝒱⟦1⟧` for every lifetime of `L` read at or below its slot.** -/
theorem ptoMutP_innerView_le {L : Type} [PartialOrder L] [OrderTop L] (ι : Reading L) {k : Loc}
    {b : Life} {α : L} (h : α ≤ ι b) (ls : List SRec) (δ' : LSubD L) :
    ptoMutP ι k α ls (fun ls₀ => vP (ℍ := ℍ) ι .unit ls₀ δ') (innerView k b) := by
  refine ⟨b, Val.unit, PMap.empty, ResU.inStratum_empty b, unitQ b, unitQ_holds b,
    ls.filter (fun r => decide (r.2 ⊐ b)), h, rfl, ?_, ?_, ?_⟩
  · funext v ρ
    apply propext
    constructor
    · rintro ⟨_, h'⟩; exact h'
    · intro h'
      exact ⟨by obtain ⟨rfl, -⟩ := h'; exact ResU.inStratum_empty b, h'⟩
  · intro r; simp [List.mem_filter]
  · rintro ls' u' σ' ⟨rfl, -⟩; exact ResU.inStratum_empty b

/-- `ℓ ↦ mut(s, (), ∅, 𝒱⟦1⟧)` is related at `Mut 'z 1` when `'z` is read at or below its slot. -/
theorem innerView_mut {L : Type} [PartialOrder L] [OrderTop L] (ι : Reading L) (δ : LSubD L)
    (z : LifeVar) {α : L} (hz : δ.find? z = some α) (k : Loc) (s : Life) (h : α ≤ ι s)
    (ls : List SRec) :
    vP (ℍ := ℍ) ι (.mut (.var z) .unit) ls δ (.loc k) (innerView k s) :=
  ⟨α, hz, k, pure_sep_mk rfl (ptoMutP_innerView_le ι h ls δ)⟩

/-- The two cells at distinct locations are compatible and their composite is valid. -/
theorem hash_two :
    ResU.Hash (innerView 0 s₁) (innerView 1 s₂) := by
  classical
  have hc₀ : ResU.CompS PMap.empty (ResU.single (0 : Loc) (CellU.ownOf Val.unit))
      (ResU.single 0 (CellU.ownOf Val.unit)) := ResU.comp_empty_left _
  have hl₀ := lower_compS_own hc₀ lower_empty rfl
  obtain ⟨-, -, hown, -⟩ := hash_compS_own (ρ := PMap.empty) (ResU.comp_empty_right _) hl₀
    (show BoCa.BoLo.Heap.upd (fun _ => none) 0 Val.unit 1 = none from rfl)
    (ResU.comp_empty_left (ResU.single (1 : Loc) (CellU.ownOf Val.unit)))
  have h₁ : ResU.Hash (ResU.single (0 : Loc) (CellU.ownOf Val.unit)) (innerView 1 s₂) :=
    ResU.six23 (ResU.comp_empty_left _) hown
  have h₂ : ResU.Hash (innerView 1 s₂) (innerView 0 s₁) :=
    ResU.six23 (ResU.comp_empty_left _) (ResU.hash_symm h₁)
  exact ResU.hash_symm h₂

/-- **The two interleaved borrows form a typed world**, built by allocating the two places and
lending each: `TW.alloc` twice, `TW.mutFold` twice. -/
theorem interleaved_world :
    ∃ ρ : WRes, ResU.CompS (innerView 0 s₁) (innerView 1 s₂) ρ ∧ ResU.Valid ρ ∧ TW ρ [] [] := by
  classical
  have hc₀ : ResU.CompS PMap.empty (ResU.single (0 : Loc) (CellU.ownOf Val.unit))
      (ResU.single 0 (CellU.ownOf Val.unit)) := ResU.comp_empty_left _
  have hl₀ := lower_compS_own hc₀ lower_empty rfl
  have hT₁ : TW (ResU.single (0 : Loc) (CellU.ownOf Val.unit)) [] [] :=
    TW.alloc TW.empty lower_empty rfl hc₀ (ResU.valid_single_own _ _)
  obtain ⟨W₂, hW₂, hown, -⟩ := hash_compS_own (ρ := PMap.empty) (ResU.comp_empty_right _) hl₀
    (show BoCa.BoLo.Heap.upd (fun _ => none) 0 Val.unit 1 = none from rfl)
    (ResU.comp_empty_left (ResU.single (1 : Loc) (CellU.ownOf Val.unit)))
  have hT₂ : TW W₂ [] [] :=
    TW.alloc hT₁ hl₀ (show BoCa.BoLo.Heap.upd (fun _ => none) 0 Val.unit 1 = none from rfl) hW₂
      (hash_valid_comp hown hW₂)
  -- lend `ℓ₁`
  have h₃ : ResU.Hash (ResU.single (1 : Loc) (CellU.ownOf Val.unit)) (innerView 0 s₁) :=
    ResU.six23 (ResU.comp_empty_left _) (ResU.hash_symm hown)
  obtain ⟨-, W₃, hW₃, hv₃⟩ := h₃
  have hT₃ : TW W₃ [] [] :=
    TW.mutFold (ρ := PMap.empty) (Z := ResU.single 1 (CellU.ownOf Val.unit))
      (hw := unitQ_holds s₁) hT₂ (ResU.comp_empty_right _) hW₂ (ResU.CompS.comm hW₃) hv₃
  -- lend `ℓ₂`
  have h₄ : ResU.Hash (innerView 0 s₁) (innerView 1 s₂) := hash_two
  obtain ⟨-, W₄, hW₄, hv₄⟩ := h₄
  have hT₄ : TW W₄ [] [] :=
    TW.mutFold (ρ := PMap.empty) (Z := innerView 0 s₁) (hw := unitQ_holds s₂) hT₃
      (ResU.comp_empty_right _) hW₃ (ResU.CompS.comm hW₄) hv₄
  exact ⟨W₄, hW₄, hv₄, hT₄⟩

/-- **The two interleaved borrows are related** at `Mut 'x 1 ⊗ Mut 'y 1`, and `return (ℓ₁, ℓ₂)` at
`F (Mut 'x 1 ⊗ Mut 'y 1)`, at the reading `δ₂ ∈ ⟦Δ₂⟧` in `TwoBranches`. -/
theorem interleaved_related {ρ : WRes} (hρ : ResU.CompS (innerView 0 s₁) (innerView 1 s₂) ρ) :
    vP (ℍ := ℍ) ι₂ twoMut [] δ₂ (.pair (.loc 0) (.loc 1)) ρ ∧
      cP (ℍ := ℍ) ι₂ (.ret twoMut) [] δ₂ (.val (.pair (.loc 0) (.loc 1))) ρ := by
  have hv : vP (ℍ := ℍ) ι₂ twoMut [] δ₂ (.pair (.loc 0) (.loc 1)) ρ :=
    ⟨Val.loc 0, Val.loc 1, pure_sep_mk rfl ⟨_, _, hρ,
      innerView_mut ι₂ δ₂ xx rfl 0 s₁ (le_of_eq ι₂_s₁.symm) [],
      innerView_mut ι₂ δ₂ xy rfl 1 s₂ (le_of_eq ι₂_s₂.symm) []⟩⟩
  exact ⟨hv, wpTS_val [] _ _ _ hv⟩

/-! ### The two tasks suspended -/

/-- A suspended task holding its borrow: `λ_. return ℓ`, forced by applying it to `()`. -/
def resumeK (k : Loc) : Val := .lam (.val (.loc k))

/-- The type of the two suspended tasks, `U (F (Mut 'x 1)) ⊗ U (F (Mut 'y 1))`. -/
abbrev twoTasks : VTy :=
  .tensor (.thunk (.ret (.mut (.var xx) .unit))) (.thunk (.ret (.mut (.var xy) .unit)))

/-- **A suspended task holding its borrow is related at `U (F (Mut 'z 1))`**, at every record list
its resumer extends the list to. -/
theorem resumeK_related {L : Type} [PartialOrder L] [OrderTop L] (ι : Reading L) (δ : LSubD L)
    (z : LifeVar) {α : L} (hz : δ.find? z = some α) (k : Loc) (s : Life) (h : α ≤ ι s)
    (ls : List SRec) :
    vP (ℍ := ℍ) ι (.thunk (.ret (.mut (.var z) .unit))) ls δ (resumeK k) (innerView k s) := by
  intro ls' _
  show wpTS ls' (.app (.val (resumeK k)) (.val .unit))
    (fun ls'' => vP (ℍ := ℍ) ι (.mut (.var z) .unit) ls'' δ) (innerView k s)
  refine wpTS_lolli ls' (.val (.loc k)) .unit _ _ ?_
  rw [show Expr.subst 0 Val.unit (.val (Val.loc k) : Expr) = .val (Val.loc k) by
    simp [Expr.subst]]
  exact wpTS_val ls' (.loc k) _ _ (innerView_mut ι δ z hz k s h ls')

/-- **The two suspended tasks are related** at `U (F (Mut 'x 1)) ⊗ U (F (Mut 'y 1))`. -/
theorem suspended_related {ρ : WRes} (hρ : ResU.CompS (innerView 0 s₁) (innerView 1 s₂) ρ) :
    vP (ℍ := ℍ) ι₂ twoTasks [] δ₂ (.pair (resumeK 0) (resumeK 1)) ρ :=
  ⟨resumeK 0, resumeK 1, pure_sep_mk rfl ⟨_, _, hρ,
    resumeK_related ι₂ δ₂ xx rfl 0 s₁ (le_of_eq ι₂_s₁.symm) [],
    resumeK_related ι₂ δ₂ xy rfl 1 s₂ (le_of_eq ι₂_s₂.symm) []⟩⟩

/-! ### The automorphism swapping the two branches -/

theorem swapped_reading :
    (ι₂.map swapBranches) s₁ = br₂ 2 ∧ (ι₂.map swapBranches) s₂ = br₁ 2 ∧
      (δ₂.map swapBranches).find? xx = some (br₂ 2) ∧
      (δ₂.map swapBranches).find? xy = some (br₁ 2) := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · rw [Reading.map_apply, ι₂_s₁]; rfl
  · rw [Reading.map_apply, ι₂_s₂]; rfl

/-- **The automorphism swapping the two branches preserves the relation** at the configuration: it
is related at the swapped reading, at both types, exactly when at the reading. -/
theorem interleaved_swap (ρ : WRes) (v : Val) (e : Expr) :
    (vP (ℍ := ℍ) (ι₂.map swapBranches) twoMut [] (δ₂.map swapBranches) v ρ ↔
      vP (ℍ := ℍ) ι₂ twoMut [] δ₂ v ρ) ∧
    (cP (ℍ := ℍ) (ι₂.map swapBranches) (.ret twoMut) [] (δ₂.map swapBranches) e ρ ↔
      cP (ℍ := ℍ) ι₂ (.ret twoMut) [] δ₂ e ρ) ∧
    ModelsP Δ₂ (δ₂.map swapBranches) ∧ (ι₂.map swapBranches).Extends := by
  refine ⟨by rw [vP_map], by rw [cP_map], (modelsP_map _ _ _).mpr modelsP_Δ₂,
    ι₂_extends.map _⟩

/-- **The configuration, assembled**: a typed world, valid, related at the borrows' types and at
the suspended tasks' type at the reading, and at the swapped reading. -/
theorem interleaved :
    ∃ ρ : WRes, ResU.CompS (innerView 0 s₁) (innerView 1 s₂) ρ ∧ ResU.Valid ρ ∧ TW ρ [] [] ∧
      vP (ℍ := ℍ) ι₂ twoMut [] δ₂ (.pair (.loc 0) (.loc 1)) ρ ∧
      cP (ℍ := ℍ) ι₂ (.ret twoMut) [] δ₂ (.val (.pair (.loc 0) (.loc 1))) ρ ∧
      vP (ℍ := ℍ) ι₂ twoTasks [] δ₂ (.pair (resumeK 0) (resumeK 1)) ρ ∧
      vP (ℍ := ℍ) (ι₂.map swapBranches) twoMut [] (δ₂.map swapBranches)
        (.pair (.loc 0) (.loc 1)) ρ ∧
      cP (ℍ := ℍ) (ι₂.map swapBranches) (.ret twoMut) [] (δ₂.map swapBranches)
        (.val (.pair (.loc 0) (.loc 1))) ρ ∧
      vP (ℍ := ℍ) (ι₂.map swapBranches) twoTasks [] (δ₂.map swapBranches)
        (.pair (resumeK 0) (resumeK 1)) ρ := by
  obtain ⟨ρ, hρ, hv, hT⟩ := interleaved_world
  obtain ⟨h₁, h₂⟩ := interleaved_related (ℍ := ℍ) hρ
  have h₃ := suspended_related (ℍ := ℍ) hρ
  obtain ⟨e₁, e₂, -, -⟩ := interleaved_swap (ℍ := ℍ) ρ (.pair (.loc 0) (.loc 1))
    (.val (.pair (.loc 0) (.loc 1)))
  have e₃ := vP_map (ℍ := ℍ) ι₂ swapBranches twoTasks [] δ₂
  exact ⟨ρ, hρ, hv, hT, h₁, h₂, h₃, e₁.mpr h₁, e₂.mpr h₂, by rw [e₃]; exact h₃⟩

/-! ### A fresh lifetime beneath the resumer's -/

/-- **A fresh slot read beneath the resumer's branch only**: below every given slot (the cells and
records in play), read on task 1's branch beneath `br₁ n`, incomparable with every lifetime of
task 2 below `⊤`. -/
theorem fresh_on_branch (S : List Life) (n : ℕ) :
    ∃ s : Life, (∀ t ∈ S, s < t) ∧ ι₂ s < br₁ n ∧
      ∀ m, m ≠ 0 → ¬ ι₂ s ≤ br₂ m ∧ ¬ br₂ m ≤ ι₂ s := by
  set k : ℕ := (S.map OrderDual.ofDual).sum + n + 1 with hk
  refine ⟨slotOf (br₁ k), fun t ht => ?_, ?_, fun m hm => ?_⟩
  · show OrderDual.ofDual t < Nat.pair k 0
    have h₁ : OrderDual.ofDual t ≤ (S.map OrderDual.ofDual).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem ht)
    have h₂ : k ≤ Nat.pair k 0 := by
      have := Nat.left_le_pair k 0
      exact this
    omega
  · rw [ι₂_slotOf]; exact br₁_lt_br₁ (by omega)
  · rw [ι₂_slotOf]; exact br_incomparable (by omega) hm

end PartialLife

end
