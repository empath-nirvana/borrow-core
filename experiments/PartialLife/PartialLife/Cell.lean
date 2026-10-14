import DenseCarrier.Cantor

/-!
# PartialLife — the layer equation over a partial order

`Paper/S5_Model/Definitions.lean` builds `Cell_α ≜ own(Val) + imm(Imm_α) + mut(Mut_α)` by
well-founded recursion on `Life = ℕᵒᵈ`, a chain. `DenseCarrier/Cantor.lean` wrote the same layer
equation over any chain `L` and proved that it has a solution exactly when `L` has no infinite
ascending sequence (`carrier_iff`), and that a chain carrying it has only the identity automorphism
(`carrier_rigid`). Here the order is a partial order: some lifetimes may be incomparable.

Two readings of the `imm` layer `Imm_α ≜ {(ᾱ, v, ρ : Res_⊔ᾱ) ∣ ⊓ᾱ ⊐ α}`:

* `CellFP`, over any partial order: `ᾱ` is Core's `LSet` (`ᾱ` with a greatest and a least member,
  `Paper/S5_Model/Definitions.lean` row 5.4's encoding), field for field;
* `CellFL`, over a lattice: `ᾱ` a nonempty finite set, `⊓ᾱ` and `⊔ᾱ` its infimum and supremum, the
  row as printed with the lattice's operations.

Results:

* `carrierP_iff`, `carrierL_iff`: **a solution exists exactly when the order has no infinite
  ascending sequence** (`WellFoundedGT`), for every partial order (resp. lattice). The proof is
  `Cantor.lean`'s: recursion down `⊐` builds a solution; along `a₀ < a₁ < ⋯` a `mut` cell at `aₙ`
  stores any predicate on the cells at `aₙ₊₁` (`predInjP`), so the cardinals would descend forever.
  Neither direction compares two lifetimes that are not already compared by `⊐`.
* `two_branches_carrier`, `two_branches_nonrigid`: `ℕᵒᵈ × ℕᵒᵈ` (two branches of lifetimes under a
  common `⊤`, `(n, 0)` and `(0, m)` incomparable for `n, m ≥ 1`, their meet `(n, m)` beneath both)
  carries the model, and the swap of the two coordinates is an order automorphism other than the
  identity. `vee_carrier`, `vee_nonrigid`, `vee_no_lower_bound`: the three-point order `⊤` over two
  incomparable points carries the model, has the swap, and its two branches have no common lower
  bound.

So rigidity (`carrier_rigid`) comes from the chain, not from the layer equation: the layer equation
needs a well-founded measure and nothing else.
-/

noncomputable section

namespace PartialLife
open BoCa.Fig16 (PMap)
open DenseCarrier (pmapSingle pmapSingle_ne_empty pmapSingle_injective encodeP)

/-! ### The layer over a partial order, with Core's encoding of `ᾱ` -/

/-- Core's `LSet` over a partial order: a borrower set with a greatest member `⊔ᾱ` and a least
member `⊓ᾱ` (`BoCa.Fig16.LSet` with `L` for `Life`). -/
structure LSetP (L : Type) [PartialOrder L] where
  mem : L → Prop
  join : L
  meet : L
  join_mem : mem join
  meet_mem : mem meet
  join_greatest : ∀ x, mem x → x ≤ join
  meet_least : ∀ x, mem x → meet ≤ x

theorem LSetP.meet_le_join {L : Type} [PartialOrder L] (s : LSetP L) : s.meet ≤ s.join :=
  s.join_greatest _ s.meet_mem

section LayerP
variable {L : Type} [PartialOrder L] (Loc Val : Type)

/-- `Imm_α`, one layer (`BoCa.Fig16.ImmF` with a partial order `L` for `Life`). -/
structure ImmFP (α : L) (below : ∀ β, α < β → Type) : Type where
  ls : LSetP L
  hls : α < ls.meet
  v : Val
  ρ : PMap Loc (below ls.join (lt_of_lt_of_le hls ls.meet_le_join))

/-- `Mut_α`, one layer (`BoCa.Fig16.MutF` with a partial order `L` for `Life`). -/
structure MutFP (α : L) (below : ∀ β, α < β → Type) : Type where
  β : L
  hβ : α < β
  v : Val
  ρ : PMap Loc (below β hβ)
  P : Val → PMap Loc (below β hβ) → Prop
  hw : P v ρ

/-- `Cell_α`, one layer (`BoCa.Fig16.CellF` with a partial order `L` for `Life`). -/
inductive CellFP (α : L) (below : ∀ β, α < β → Type) : Type where
  | own (v : Val)
  | imm (i : ImmFP Loc Val α below)
  | mut (m : MutFP Loc Val α below)

/-- A solution of Fig. 16 row 3 over the partial order `L`. -/
def IsCarrierP (Cell : L → Type) : Prop :=
  Nonempty (∀ α, Cell α ≃ CellFP Loc Val α (fun β _ => Cell β))

end LayerP

/-! ### The layer over a lattice, with `⊓ᾱ`, `⊔ᾱ` the lattice's -/

section LayerL
variable {L : Type} [Lattice L] (Loc Val : Type)

theorem inf'_le_sup' {s : Finset L} (ne : s.Nonempty) : s.inf' ne id ≤ s.sup' ne id := by
  obtain ⟨b, hb⟩ := ne
  exact le_trans (Finset.inf'_le id hb) (Finset.le_sup' id hb)

/-- `Imm_α ≜ {(ᾱ, v, ρ : Res_⊔ᾱ) ∣ ⊓ᾱ ⊐ α}`, one layer, with `ᾱ` a nonempty finite set and
`⊓ᾱ`, `⊔ᾱ` the lattice's infimum and supremum. -/
structure ImmFL (α : L) (below : ∀ β, α < β → Type) : Type where
  ls : Finset L
  ne : ls.Nonempty
  hls : α < ls.inf' ne id
  v : Val
  ρ : PMap Loc (below (ls.sup' ne id) (lt_of_lt_of_le hls (inf'_le_sup' ne)))

/-- `Cell_α`, one layer, over a lattice. -/
inductive CellFL (α : L) (below : ∀ β, α < β → Type) : Type where
  | own (v : Val)
  | imm (i : ImmFL Loc Val α below)
  | mut (m : MutFP Loc Val α below)

/-- A solution of Fig. 16 row 3 over the lattice `L`. -/
def IsCarrierL (Cell : L → Type) : Prop :=
  Nonempty (∀ α, Cell α ≃ CellFL Loc Val α (fun β _ => Cell β))

end LayerL

/-! ### A reverse-well-founded order: the paper's recursion -/

section Exists
variable {L : Type} (Loc Val : Type)

/-- The paper's construction over a reverse-well-founded partial order. -/
def CellGP [PartialOrder L] [WellFoundedGT L] : L → Type :=
  WellFounded.fix wellFounded_gt (CellFP Loc Val)

theorem CellGP_eq [PartialOrder L] [WellFoundedGT L] (α : L) :
    CellGP (L := L) Loc Val α = CellFP Loc Val α (fun β _ => CellGP Loc Val β) :=
  WellFounded.fix_eq wellFounded_gt (CellFP Loc Val) α

theorem carrierP_of_wellFoundedGT [PartialOrder L] [WellFoundedGT L] :
    IsCarrierP Loc Val (CellGP (L := L) Loc Val) :=
  ⟨fun α => Equiv.cast (CellGP_eq Loc Val α)⟩

/-- The paper's construction over a reverse-well-founded lattice. -/
def CellGL [Lattice L] [WellFoundedGT L] : L → Type :=
  WellFounded.fix wellFounded_gt (CellFL Loc Val)

theorem CellGL_eq [Lattice L] [WellFoundedGT L] (α : L) :
    CellGL (L := L) Loc Val α = CellFL Loc Val α (fun β _ => CellGL Loc Val β) :=
  WellFounded.fix_eq wellFounded_gt (CellFL Loc Val) α

theorem carrierL_of_wellFoundedGT [Lattice L] [WellFoundedGT L] :
    IsCarrierL Loc Val (CellGL (L := L) Loc Val) :=
  ⟨fun α => Equiv.cast (CellGL_eq Loc Val α)⟩

end Exists

/-! ### An ascending sequence: no solution -/

section NoCarrier
variable {L : Type} [PartialOrder L] {Loc Val : Type}

/-- **A `mut` cell at `α` stores any predicate on the cells at a `β ⊐ α`**, injectively. -/
theorem predInjP (Cell : L → Type) {α β : L} (h : α < β) (l₀ : Loc) (v₀ : Val) :
    Function.Injective (fun S : Set (Cell β) =>
      (⟨β, h, v₀, PMap.empty, encodeP l₀ S, Or.inl rfl⟩ : MutFP Loc Val α (fun β _ => Cell β))) := by
  intro S T hST
  obtain ⟨-, -, -, hP⟩ := MutFP.mk.inj hST
  have hP' : encodeP (Val := Val) l₀ S = encodeP l₀ T := eq_of_heq hP
  ext c
  have hc := congrFun (congrFun hP' v₀) (pmapSingle l₀ c)
  simp only [encodeP, eq_iff_iff] at hc
  constructor
  · intro hS
    rcases hc.mp (Or.inr ⟨c, hS, rfl⟩) with he | ⟨c', hT, he⟩
    · exact absurd he (pmapSingle_ne_empty _ _)
    · rwa [pmapSingle_injective _ he]
  · intro hT
    rcases hc.mpr (Or.inr ⟨c, hT, rfl⟩) with he | ⟨c', hS, he⟩
    · exact absurd he (pmapSingle_ne_empty _ _)
    · rwa [pmapSingle_injective _ he]

omit [PartialOrder L] in
/-- The cardinals along an ascending sequence descend, given an injection of the predicates on the
cells one step up into the cells one step down. -/
theorem no_descent_of_inj (Cell : L → Type) (a : ℕ → L)
    (inj : ∀ n, ∃ f : Set (Cell (a (n + 1))) → Cell (a n), Function.Injective f) : False := by
  have key : ∀ n, Cardinal.mk (Cell (a (n + 1))) < Cardinal.mk (Cell (a n)) := by
    intro n
    obtain ⟨f, hf⟩ := inj n
    calc Cardinal.mk (Cell (a (n + 1))) < 2 ^ Cardinal.mk (Cell (a (n + 1))) := Cardinal.cantor _
      _ = Cardinal.mk (Set (Cell (a (n + 1)))) := Cardinal.mk_set.symm
      _ ≤ Cardinal.mk (Cell (a n)) := Cardinal.mk_le_of_injective hf
  exact not_strictAnti_of_wellFoundedLT (fun n => Cardinal.mk (Cell (a n)))
    (strictAnti_nat_of_succ_lt key)

/-- **No solution over a partial order with an infinite ascending sequence.** -/
theorem no_carrierP_of_strictMono [Nonempty Loc] [Nonempty Val] (Cell : L → Type)
    (hC : IsCarrierP Loc Val Cell) (a : ℕ → L) (ha : StrictMono a) : False := by
  obtain ⟨e⟩ := hC
  obtain ⟨l₀⟩ := (inferInstance : Nonempty Loc)
  obtain ⟨v₀⟩ := (inferInstance : Nonempty Val)
  refine no_descent_of_inj Cell a fun n => ?_
  have hlt : a n < a (n + 1) := ha (Nat.lt_succ_self n)
  exact ⟨fun S => (e (a n)).symm (CellFP.mut ⟨a (n + 1), hlt, v₀, PMap.empty, encodeP l₀ S,
      Or.inl rfl⟩),
    (e (a n)).symm.injective.comp fun S T h =>
      predInjP (Loc := Loc) (Val := Val) Cell hlt l₀ v₀ (CellFP.mut.inj h)⟩

/-- The same over a lattice. -/
theorem no_carrierL_of_strictMono {L : Type} [Lattice L] [Nonempty Loc] [Nonempty Val]
    (Cell : L → Type) (hC : IsCarrierL Loc Val Cell) (a : ℕ → L) (ha : StrictMono a) : False := by
  obtain ⟨e⟩ := hC
  obtain ⟨l₀⟩ := (inferInstance : Nonempty Loc)
  obtain ⟨v₀⟩ := (inferInstance : Nonempty Val)
  refine no_descent_of_inj Cell a fun n => ?_
  have hlt : a n < a (n + 1) := ha (Nat.lt_succ_self n)
  exact ⟨fun S => (e (a n)).symm (CellFL.mut ⟨a (n + 1), hlt, v₀, PMap.empty, encodeP l₀ S,
      Or.inl rfl⟩),
    (e (a n)).symm.injective.comp fun S T h =>
      predInjP (Loc := Loc) (Val := Val) Cell hlt l₀ v₀ (CellFL.mut.inj h)⟩

/-- A partial order with no infinite strictly ascending sequence is reverse-well-founded. -/
theorem wellFoundedGT_of_no_seq {L : Type} [PartialOrder L] (h : ∀ a : ℕ → L, ¬ StrictMono a) :
    WellFoundedGT L := by
  refine ⟨?_⟩
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => h f fun m n hmn => ?_⟩
  exact f.map_rel_iff.mpr hmn

/-- **Over a partial order, a solution exists exactly when the order is reverse-well-founded.** -/
theorem carrierP_iff [Nonempty Loc] [Nonempty Val] :
    (∃ Cell : L → Type, IsCarrierP Loc Val Cell) ↔ WellFoundedGT L := by
  constructor
  · rintro ⟨Cell, hC⟩
    exact wellFoundedGT_of_no_seq fun a ha => no_carrierP_of_strictMono Cell hC a ha
  · intro _
    exact ⟨CellGP Loc Val, carrierP_of_wellFoundedGT Loc Val⟩

/-- **Over a lattice, with the lattice's `⊓ᾱ` and `⊔ᾱ`, a solution exists exactly when the order is
reverse-well-founded.** -/
theorem carrierL_iff {L : Type} [Lattice L] [Nonempty Loc] [Nonempty Val] :
    (∃ Cell : L → Type, IsCarrierL Loc Val Cell) ↔ WellFoundedGT L := by
  constructor
  · rintro ⟨Cell, hC⟩
    exact wellFoundedGT_of_no_seq fun a ha => no_carrierL_of_strictMono Cell hC a ha
  · intro _
    exact ⟨CellGL Loc Val, carrierL_of_wellFoundedGT Loc Val⟩

end NoCarrier

/-! ### Solvable orders with automorphisms other than the identity -/

/-- Two branches of lifetimes under a common `⊤`: `(n, 0)` is task 1's `n`-th lifetime, `(0, m)`
task 2's, and `(n, m)` their meet. -/
abbrev TwoBranches : Type := ℕᵒᵈ × ℕᵒᵈ

/-- `(n, 0)`, the `n`-th lifetime of the first branch. -/
def br₁ (n : ℕ) : TwoBranches := (OrderDual.toDual n, OrderDual.toDual 0)

/-- `(0, m)`, the `m`-th lifetime of the second branch. -/
def br₂ (m : ℕ) : TwoBranches := (OrderDual.toDual 0, OrderDual.toDual m)

theorem br₁_le_br₂_iff {n m : ℕ} : br₁ n ≤ br₂ m ↔ m = 0 := by
  simp only [br₁, br₂, Prod.mk_le_mk, OrderDual.toDual_le_toDual]
  omega

theorem br₂_le_br₁_iff {n m : ℕ} : br₂ m ≤ br₁ n ↔ n = 0 := by
  simp only [br₁, br₂, Prod.mk_le_mk, OrderDual.toDual_le_toDual]
  omega

/-- **Lifetimes of the two branches below `⊤` are incomparable.** -/
theorem br_incomparable {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    ¬ br₁ n ≤ br₂ m ∧ ¬ br₂ m ≤ br₁ n :=
  ⟨fun h => hm (br₁_le_br₂_iff.mp h), fun h => hn (br₂_le_br₁_iff.mp h)⟩

/-- The swap of the two branches. -/
def swapBranches : TwoBranches ≃o TwoBranches := OrderIso.prodComm

@[simp] theorem swapBranches_br₁ (n : ℕ) : swapBranches (br₁ n) = br₂ n := rfl
@[simp] theorem swapBranches_br₂ (m : ℕ) : swapBranches (br₂ m) = br₁ m := rfl

/-- **The swap is not the identity.** -/
theorem swapBranches_ne_refl : swapBranches ≠ OrderIso.refl TwoBranches := by
  intro h
  have h1 : swapBranches (br₁ 1) = br₁ 1 := by rw [h]; rfl
  rw [swapBranches_br₁] at h1
  have := congrArg (fun p : TwoBranches => OrderDual.ofDual p.1) h1
  simp [br₁, br₂] at this

/-- **The two branches carry the model** (with Core's encoding of `ᾱ`, and with the lattice's). -/
theorem two_branches_carrier (Loc Val : Type) :
    (∃ Cell : TwoBranches → Type, IsCarrierP Loc Val Cell) ∧
      (∃ Cell : TwoBranches → Type, IsCarrierL Loc Val Cell) :=
  ⟨⟨_, carrierP_of_wellFoundedGT Loc Val⟩, ⟨_, carrierL_of_wellFoundedGT Loc Val⟩⟩

/-- **A partial order carrying the model with an automorphism other than the identity**, against
`DenseCarrier.carrier_rigid` for chains. -/
theorem two_branches_nonrigid (Loc Val : Type) :
    (∃ Cell : TwoBranches → Type, IsCarrierP Loc Val Cell) ∧
      ∃ e : TwoBranches ≃o TwoBranches, e ≠ OrderIso.refl _ :=
  ⟨(two_branches_carrier Loc Val).1, swapBranches, swapBranches_ne_refl⟩

/-! ### Two branches with no meet -/

/-- `⊤` over two incomparable points. -/
abbrev Vee : Type := WithTop (Unit ⊕ Unit)

/-- The first branch's point. -/
def veeL : Vee := (Sum.inl () : Unit ⊕ Unit)

/-- The second branch's point. -/
def veeR : Vee := (Sum.inr () : Unit ⊕ Unit)

instance : WellFoundedGT Vee := Finite.to_wellFoundedGT

/-- The swap of the two points. -/
def swapVee : Vee ≃o Vee := (OrderIso.sumComm Unit Unit).withTopCongr

theorem swapVee_ne_refl : swapVee ≠ OrderIso.refl Vee := by
  intro h
  have := congrArg (fun e : Vee ≃o Vee => e veeL) h
  simp [swapVee, veeL, OrderIso.withTopCongr] at this

/-- **The two points have no common lower bound**: a lifetime beneath both does not exist. -/
theorem vee_no_lower_bound : ¬ ∃ c : Vee, c ≤ veeL ∧ c ≤ veeR := by
  rintro ⟨c, h₁, h₂⟩
  induction c using WithTop.recTopCoe with
  | top => exact absurd h₁ (by simp [veeL])
  | coe c =>
      simp only [veeL, veeR, WithTop.coe_le_coe] at h₁ h₂
      rcases c with c | c
      · exact absurd h₂ (by simp)
      · exact absurd h₁ (by simp)

theorem vee_nonrigid (Loc Val : Type) :
    (∃ Cell : Vee → Type, IsCarrierP Loc Val Cell) ∧ ∃ e : Vee ≃o Vee, e ≠ OrderIso.refl _ :=
  ⟨⟨_, carrierP_of_wellFoundedGT Loc Val⟩, swapVee, swapVee_ne_refl⟩

end PartialLife

end
