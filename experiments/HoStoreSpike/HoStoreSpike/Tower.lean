import Support.Model.Tree.World.UpdXInv

/-!
# Higher-order store typing over the tree carrier: the approximation tower (spike, #790)

A store typing that may give a location **any** semantic type, including one that reads the
store typing itself, is circular: a type reads the world, and the world holds types. The circle is
cut by the step index (Ahmed's approximations; the "later" of Iris): a type at index `n` reads the
store typing only through its types' approximations at `n`, which are their meanings at indices
`< n`.

* `ATy n`: a type known at the indices `< n`. `ATy (n+1)` is `ATy n` beside the predicate at index
  `n`, which reads a store typing of `ATy n`s. The recursion is structural in `n`.
* `HTy`: a semantic type, a predicate at each index `n` over the tree `K`, a store typing of `ATy n`s,
  a value and a resource. `HTy.ap τ n : ATy n` is its approximation at `n`.
* `HStore`: a store typing, a `HTy` per location. `HTy.P τ n K Ψ` reads `τ` at index `n` at `Ψ`'s
  approximation at `n`. So no type can see the store typing beyond the index it is read at
  (`HTy.P_congr`), and that is the whole of the circularity's resolution.

No `sorry`, `axiom`, `native_decide`, `opaque`, `partial` or `unsafe`.
-/

noncomputable section

namespace BoCa.Fig16.Tree.HoStore
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp

/-! ### The tower -/

/-- **A type known at the indices `< n`.** -/
def ATy : Nat → Type
  | 0 => PUnit
  | n + 1 => ATy n × ((K : WCactus) → (BoCa.Loc → Option (ATy n)) → BoCa.Val → TRes K → Prop)

/-- **A semantic type**: its predicate at each index reads the store typing approximated there. -/
structure HTy where
  Q : (n : Nat) → (K : WCactus) → (BoCa.Loc → Option (ATy n)) → BoCa.Val → TRes K → Prop

/-- The approximation of `τ` at `n`: its predicates at the indices `< n`. -/
def HTy.ap (τ : HTy) : (n : Nat) → ATy n
  | 0 => PUnit.unit
  | n + 1 => (τ.ap n, τ.Q n)

theorem HTy.ap_succ_fst (τ : HTy) (n : Nat) : (τ.ap (n + 1)).1 = τ.ap n := rfl

theorem HTy.ap_succ_snd (τ : HTy) (n : Nat) : (τ.ap (n + 1)).2 = τ.Q n := rfl

/-- Two types agreeing at `n` agree at every `k ≤ n`. -/
theorem HTy.ap_le {τ σ : HTy} : ∀ {n k : Nat}, τ.ap n = σ.ap n → k ≤ n → τ.ap k = σ.ap k
  | 0, k, _, hk => by
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      rfl
  | n + 1, k, h, hk => by
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · have h' : τ.ap n = σ.ap n := by
          rw [← HTy.ap_succ_fst τ n, ← HTy.ap_succ_fst σ n, h]
        exact HTy.ap_le h' (Nat.lt_succ_iff.mp hlt)
      · obtain rfl : k = n + 1 := Nat.le_antisymm hk hge
        exact h

/-- Two types agreeing at `n` have one predicate at every `k < n`. -/
theorem HTy.Q_eq_of_ap {τ σ : HTy} {n k : Nat} (h : τ.ap n = σ.ap n) (hk : k < n) :
    τ.Q k = σ.Q k := by
  have := HTy.ap_le h hk
  rw [← HTy.ap_succ_snd τ k, ← HTy.ap_succ_snd σ k, this]

/-- **A store typing**: a semantic type per location. -/
abbrev HStore : Type := BoCa.Loc → Option HTy

/-- The store typing approximated at `n`. -/
def HStore.ap (Ψ : HStore) (n : Nat) : BoCa.Loc → Option (ATy n) :=
  fun l => (Ψ l).map (fun τ => τ.ap n)

/-- **`τ` read at index `n` at the store typing `Ψ`.** -/
def HTy.P (τ : HTy) (n : Nat) (K : WCactus) (Ψ : HStore) (v : BoCa.Val) (ρ : TRes K) : Prop :=
  τ.Q n K (Ψ.ap n) v ρ

/-- **The circularity's resolution**: at index `n` a type reads only the store typing's
approximation at `n`. -/
theorem HTy.P_congr (τ : HTy) {n : Nat} {K : WCactus} {Ψ Ψ' : HStore} (h : Ψ.ap n = Ψ'.ap n)
    (v : BoCa.Val) (ρ : TRes K) : τ.P n K Ψ v ρ ↔ τ.P n K Ψ' v ρ := by
  unfold HTy.P; rw [h]

/-! ### Cell invariants, read one step later -/

/-- **A cell's invariant at index `n`** for a location of type `τ`: `τ` read at `n - 1` (one step
later), and nothing at `0`. -/
def cellInv (Ψ : HStore) (τ : HTy) : Nat → KSem
  | 0 => ⟨fun _ _ _ => True⟩
  | k + 1 => ⟨fun K v ρ => τ.P k K Ψ v ρ⟩

/-- **The location typing at index `n`**: `Reread.lean`'s `LocTy`, so `Cov`, `RC` and `RR` read it
unchanged. -/
def semH (Ψ : HStore) (n : Nat) : LocTy := fun l => (Ψ l).map (cellInv Ψ · n)

theorem semH_of {Ψ : HStore} {n : Nat} {l : BoCa.Loc} {τ : HTy} (h : Ψ l = some τ) :
    semH Ψ n l = some (cellInv Ψ τ n) := by simp [semH, h]

theorem semH_some {Ψ : HStore} {n : Nat} {l : BoCa.Loc} {κ : KSem} (h : semH Ψ n l = some κ) :
    ∃ τ, Ψ l = some τ ∧ κ = cellInv Ψ τ n := by
  unfold semH at h
  cases e : Ψ l with
  | none => rw [e] at h; cases h
  | some τ => rw [e] at h; exact ⟨τ, rfl, (Option.some.inj h).symm⟩

/-! ### The laws -/

/-- `Ψ′` keeps `Ψ`'s type wherever `ρ` holds a `mut` cell, at any depth. -/
def AgreeH {K : WCactus} (Ψ Ψ' : HStore) (ρ : TRes K) : Prop := ∀ l, HoldsMut ρ l → Ψ' l = Ψ l

theorem AgreeH.wit {K : WCactus} {Ψ Ψ' : HStore} {ρ : TRes K} (h : AgreeH Ψ Ψ' ρ) {k : BoCa.Loc}
    {ψ : TCell K} (e : ρ.get k = some ψ) : AgreeH Ψ Ψ' ψ.wit :=
  fun l hl => h l (.deep e hl)

theorem AgreeH.refl {K : WCactus} (Ψ : HStore) (ρ : TRes K) : AgreeH Ψ Ψ ρ := fun _ _ => rfl

theorem AgreeH.trans {Θ : LocTy} {K K' : WCactus} {Ψ₁ Ψ₂ Ψ₃ : HStore} {ρ : TRes K}
    {ρ' : TRes K'} (h₁ : AgreeH Ψ₁ Ψ₂ ρ) (hr : RR Θ ρ ρ') (h₂ : AgreeH Ψ₂ Ψ₃ ρ') :
    AgreeH Ψ₁ Ψ₃ ρ :=
  fun l hl => (h₂ l (hl.rr hr)).trans (h₁ l hl)

/-- Downward closed in the index. -/
def HTy.Down (τ : HTy) : Prop :=
  ∀ n K Ψ v (ρ : TRes K), τ.P (n + 1) K Ψ v ρ → τ.P n K Ψ v ρ

/-- **Monotone along the tree**: at every extension of the tree, every store typing keeping the
types where `ρ` holds a `mut` cell, and every re-reading of `ρ` at that store typing at any index. -/
def HTy.Mono (τ : HTy) : Prop :=
  ∀ n (K K' : WCactus) (Ψ Ψ' : HStore) (j : Nat) v (ρ : TRes K) (ρ' : TRes K'),
    K.Ext K' → AgreeH Ψ Ψ' ρ → RR (semH Ψ' j) ρ ρ' → τ.P n K Ψ v ρ → τ.P n K' Ψ' v ρ'

/-- A lawful semantic type. -/
structure HTy.Lawful (τ : HTy) : Prop where
  down : τ.Down
  mono : τ.Mono

theorem HTy.down_le {τ : HTy} (hd : τ.Down) {m n : Nat} (h : m ≤ n) {K : WCactus} {Ψ : HStore}
    {v : BoCa.Val} {ρ : TRes K} : τ.P n K Ψ v ρ → τ.P m K Ψ v ρ := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun x => ih (hd _ K Ψ v ρ x)

/-- Every type the store typing gives is lawful. -/
def HStore.Lawful (Ψ : HStore) : Prop := ∀ l τ, Ψ l = some τ → τ.Lawful

/-- Lawfulness is a property of the predicates. -/
theorem HTy.Lawful.of_Q_eq {τ σ : HTy} (h : τ.Q = σ.Q) (hτ : τ.Lawful) : σ.Lawful := by
  obtain ⟨Q⟩ := τ; obtain ⟨Q'⟩ := σ
  simp only at h; subst h; exact hτ

end BoCa.Fig16.Tree.HoStore

end
