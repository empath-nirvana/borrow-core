import Paper.S5_Model.Definitions

/-!
# DenseCarrier — the stratification index must be reverse-well-ordered

`Paper/S5_Model/Definitions.lean` builds `Cell_α ≜ own(Val) + imm(Imm_α) + mut(Mut_α)` by
well-founded recursion on `Life = ℕᵒᵈ`: a `mut` cell of stratum `α` stores a predicate
`P̂ : Val → SProp_β` on the resources of a stratum `β ⊐ α`. Here the same layer equation is
written over an arbitrary linear order `L` (`CellFG`: the paper's `CellF` with `Life` replaced by
`L`, field for field), and the question is for which `L` a family of types solves it.

* `carrier_of_wellFoundedGT`: when `L` has no infinite strictly ascending chain
  (`WellFoundedGT L`, which `ℕᵒᵈ` and every finite order satisfy), the paper's recursion builds a
  solution.
* `no_carrier_of_strictMono`: when `L` has an infinite strictly ascending chain
  `a₀ < a₁ < ⋯`, no family solves it. A `mut` cell of stratum `aₙ` can store any predicate on
  the cells of stratum `aₙ₊₁` (`predInj`), so `#Cell_{aₙ} ≥ 2^#Cell_{aₙ₊₁} > #Cell_{aₙ₊₁}`
  (Cantor), and the cardinals would descend forever.
* `carrier_iff`: a solution exists exactly when `L` is reverse-well-founded.
* `no_carrier_of_dense`: a densely ordered `L` with two points has such a chain, so no solution;
  `no_carrier_withTopRat` at `WithTop ℚ`.

So a dense lifetime order cannot also be the stratification index of the paper's carrier: the
index of the strata must stay reverse-well-ordered (the lifetimes in play, finitely many or
`ℕᵒᵈ`), and a dense order can only be where those lifetimes are read.
-/

noncomputable section

namespace DenseCarrier
open BoCa.Fig16 (PMap)

/-- `℘⁺(L)` at the sets where `⊓ᾱ` and `⊔ᾱ` exist: `LSet` over a general linear order. -/
structure LSetG (L : Type) [LinearOrder L] where
  mem : L → Prop
  join : L
  meet : L
  join_mem : mem join
  meet_mem : mem meet
  join_greatest : ∀ x, mem x → x ≤ join
  meet_least : ∀ x, mem x → meet ≤ x

theorem LSetG.meet_le_join {L : Type} [LinearOrder L] (s : LSetG L) : s.meet ≤ s.join :=
  s.join_greatest _ s.meet_mem

section Layer
variable {L : Type} [LinearOrder L] (Loc Val : Type)

/-- `Imm_α`, one layer, over `L` (`BoCa.Fig16.ImmF` with `Life` replaced by `L`). -/
structure ImmFG (α : L) (below : ∀ β, α < β → Type) : Type where
  ls : LSetG L
  hls : α < ls.meet
  v : Val
  ρ : PMap Loc (below ls.join (lt_of_lt_of_le hls ls.meet_le_join))

/-- `Mut_α`, one layer, over `L` (`BoCa.Fig16.MutF` with `Life` replaced by `L`). -/
structure MutFG (α : L) (below : ∀ β, α < β → Type) : Type where
  β : L
  hβ : α < β
  v : Val
  ρ : PMap Loc (below β hβ)
  P : Val → PMap Loc (below β hβ) → Prop
  hw : P v ρ

/-- `Cell_α`, one layer, over `L` (`BoCa.Fig16.CellF` with `Life` replaced by `L`). -/
inductive CellFG (α : L) (below : ∀ β, α < β → Type) : Type where
  | own (v : Val)
  | imm (i : ImmFG Loc Val α below)
  | mut (m : MutFG Loc Val α below)

/-- A solution of Fig. 16 row 3 over `L`: a family of types, each the layer over the others. -/
def IsCarrier (Cell : L → Type) : Prop :=
  Nonempty (∀ α, Cell α ≃ CellFG Loc Val α (fun β _ => Cell β))

end Layer

/-! ### A reverse-well-founded index: the paper's recursion -/

section Exists
variable {L : Type} [LinearOrder L] [WellFoundedGT L] (Loc Val : Type)

/-- The paper's construction (`BoCa.Fig16.Cell`) over a reverse-well-founded `L`. -/
def CellG : L → Type := WellFounded.fix wellFounded_gt (CellFG Loc Val)

theorem CellG_eq (α : L) : CellG Loc Val α = CellFG Loc Val α (fun β _ => CellG Loc Val β) :=
  WellFounded.fix_eq wellFounded_gt (CellFG Loc Val) α

theorem carrier_of_wellFoundedGT : IsCarrier Loc Val (CellG (L := L) Loc Val) :=
  ⟨fun α => Equiv.cast (CellG_eq Loc Val α)⟩

end Exists

/-! ### An ascending chain: no solution -/

section NoCarrier
variable {L : Type} [LinearOrder L] {Loc Val : Type}

/-- The one-location map `ℓ ↦ a`. -/
def pmapSingle {A : Type} (l : Loc) (a : A) : PMap Loc A := by
  classical
  exact
    { get := fun l' => if l' = l then some a else none
      finite := ⟨[l], fun l' h => by
        by_cases e : l' = l
        · exact e ▸ List.mem_singleton.mpr rfl
        · exact absurd (if_neg e) h⟩ }

theorem pmapSingle_ne_empty {A : Type} (l : Loc) (a : A) : pmapSingle l a ≠ PMap.empty := by
  classical
  intro h
  have := congrArg (fun p => PMap.get p l) h
  simp [pmapSingle, PMap.empty] at this

theorem pmapSingle_injective {A : Type} (l : Loc) : Function.Injective (pmapSingle (A := A) l) := by
  classical
  intro a b h
  have := congrArg (fun p => PMap.get p l) h
  simpa [pmapSingle] using this

/-- The stored predicate that encodes `S`: `∅`, or a single cell of `S` at `ℓ₀`. -/
def encodeP {A : Type} (l₀ : Loc) (S : A → Prop) : Val → PMap Loc A → Prop :=
  fun _ ρ => ρ = PMap.empty ∨ ∃ c, S c ∧ ρ = pmapSingle l₀ c

/-- **A `mut` cell of stratum `α` stores any predicate on the cells of a stratum `β ⊐ α`**,
injectively. -/
theorem predInj (Cell : L → Type) {α β : L} (h : α < β) (l₀ : Loc) (v₀ : Val) :
    Function.Injective (fun S : Set (Cell β) =>
      (CellFG.mut ⟨β, h, v₀, PMap.empty, encodeP l₀ S, Or.inl rfl⟩ :
        CellFG Loc Val α (fun β _ => Cell β))) := by
  intro S T hST
  have hm := CellFG.mut.inj hST
  obtain ⟨-, -, -, hP⟩ := MutFG.mk.inj hm
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

/-- **No solution over an order with an infinite strictly ascending chain.** -/
theorem no_carrier_of_strictMono [Nonempty Loc] [Nonempty Val] (Cell : L → Type)
    (hC : IsCarrier Loc Val Cell) (a : ℕ → L) (ha : StrictMono a) : False := by
  obtain ⟨e⟩ := hC
  obtain ⟨l₀⟩ := (inferInstance : Nonempty Loc)
  obtain ⟨v₀⟩ := (inferInstance : Nonempty Val)
  have key : ∀ n, Cardinal.mk (Cell (a (n + 1))) < Cardinal.mk (Cell (a n)) := by
    intro n
    have hlt : a n < a (n + 1) := ha (Nat.lt_succ_self n)
    have hinj : Function.Injective (fun S : Set (Cell (a (n + 1))) =>
        (e (a n)).symm (CellFG.mut ⟨a (n + 1), hlt, v₀, PMap.empty, encodeP l₀ S, Or.inl rfl⟩)) :=
      (e (a n)).symm.injective.comp (predInj (Loc := Loc) (Val := Val) Cell hlt l₀ v₀)
    calc Cardinal.mk (Cell (a (n + 1))) < 2 ^ Cardinal.mk (Cell (a (n + 1))) := Cardinal.cantor _
      _ = Cardinal.mk (Set (Cell (a (n + 1)))) := Cardinal.mk_set.symm
      _ ≤ Cardinal.mk (Cell (a n)) := Cardinal.mk_le_of_injective hinj
  exact not_strictAnti_of_wellFoundedLT (fun n => Cardinal.mk (Cell (a n)))
    (strictAnti_nat_of_succ_lt key)

/-- An order with no infinite strictly ascending chain is reverse-well-founded. -/
theorem wellFoundedGT_of_no_chain (h : ∀ a : ℕ → L, ¬ StrictMono a) : WellFoundedGT L := by
  refine ⟨?_⟩
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => h f fun m n hmn => ?_⟩
  exact f.map_rel_iff.mpr hmn

/-- **A solution exists exactly when `L` is reverse-well-founded.** -/
theorem carrier_iff [Nonempty Loc] [Nonempty Val] :
    (∃ Cell : L → Type, IsCarrier Loc Val Cell) ↔ WellFoundedGT L := by
  constructor
  · rintro ⟨Cell, hC⟩
    exact wellFoundedGT_of_no_chain fun a ha => no_carrier_of_strictMono Cell hC a ha
  · intro _
    exact ⟨CellG Loc Val, carrier_of_wellFoundedGT Loc Val⟩

/-- A dense order has an infinite strictly ascending chain below any point above another. -/
theorem exists_strictMono_of_dense [DenselyOrdered L] {x y : L} (h : x < y) :
    ∃ a : ℕ → L, StrictMono a ∧ ∀ n, a n < y := by
  let step : {z : L // z < y} → {z : L // z < y} := fun z =>
    ⟨Classical.choose (exists_between z.2), (Classical.choose_spec (exists_between z.2)).2⟩
  let b : ℕ → {z : L // z < y} := fun n => Nat.rec ⟨x, h⟩ (fun _ z => step z) n
  refine ⟨fun n => (b n).1, strictMono_nat_of_lt_succ fun n => ?_, fun n => (b n).2⟩
  exact (Classical.choose_spec (exists_between (b n).2)).1

/-- **No solution over a dense order with two points.** -/
theorem no_carrier_of_dense [DenselyOrdered L] [Nonempty Loc] [Nonempty Val] {x y : L}
    (h : x < y) (Cell : L → Type) : ¬ IsCarrier Loc Val Cell := by
  intro hC
  obtain ⟨a, ha, -⟩ := exists_strictMono_of_dense h
  exact no_carrier_of_strictMono Cell hC a ha

/-- At `WithTop ℚ`. -/
theorem no_carrier_withTopRat [Nonempty Loc] [Nonempty Val] (Cell : WithTop ℚ → Type) :
    ¬ IsCarrier Loc Val Cell :=
  no_carrier_of_dense (show ((0 : ℚ) : WithTop ℚ) < ⊤ from WithTop.coe_lt_top 0) Cell

/-- At the `Loc` and `Val` of `[TR]` §3. -/
theorem no_carrier_withTopRat_BoCa (Cell : WithTop ℚ → Type) :
    ¬ IsCarrier BoCa.Loc BoCa.Val Cell :=
  haveI : Nonempty BoCa.Loc := ⟨(0 : ℕ)⟩
  haveI : Nonempty BoCa.Val := ⟨BoCa.Val.unit⟩
  no_carrier_withTopRat Cell

end NoCarrier

end DenseCarrier

end
