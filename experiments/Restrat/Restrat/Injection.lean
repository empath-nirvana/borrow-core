import Paper.S5_Model.Definitions
import Paper.S2_Statics.Definitions
import Support.Lifetimes.Terms
import Support.Model.Notation
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.S4_LogicalRelation.Definitions

/-!
# Restrat — re-stratifications of `Life`

A **re-stratification at the cut `c`** is a strictly monotone map `f : Life → Life` that is the
identity at and above `c` (`Emb c`).  `Life` is `ℕᵒᵈ`, which has no non-trivial order
automorphism, so `f` is an order embedding and not a symmetry: it moves the lifetimes below the
cut to shorter ones (`Emb.le_self`) and keeps them below the cut (`Emb.lt_cut`).

* `Emb.shift c k` moves every lifetime strictly below `c` down by `k`.  It commutes with `↓`
  strictly inside the moved interval (`shift_down`), and not at the cut (`shift_down_cut`): the
  identity `f(↓o) = ↓f(o)` fails at the outer lifetime `o = c` for every `k > 0`, so no added
  hypothesis "`f` preserves `↓` at the cut" is satisfiable by a non-trivial shift.
* `Emb.shift_fresh`: a shift places the moved interval below any given lifetime.
* The lifetime level: the action on `LSub` (`LSub.mapN`), and its naturality for `@aδ`
  (`interp_mapN`), `⟦Δ⟧` (`models_mapN_iff`) and `α ⊏ @bδ` (`ltLife_mapN_iff`).
-/

noncomputable section

namespace Restrat
open BoCa.Fig16

/-- A re-stratification at the cut `c`: strictly monotone, the identity at and above `c`. -/
structure Emb (c : Life) where
  /-- The map. -/
  f : Life → Life
  /-- An order embedding. -/
  strictMono : StrictMono f
  /-- The identity at and above the cut. -/
  fix : ∀ x, c ≤ x → f x = x

namespace Emb
variable {c : Life} (e : Emb c)

instance : CoeFun (Emb c) (fun _ => Life → Life) := ⟨Emb.f⟩

theorem lt_iff {a b : Life} : e a < e b ↔ a < b := e.strictMono.lt_iff_lt
theorem le_iff {a b : Life} : e a ≤ e b ↔ a ≤ b := e.strictMono.le_iff_le
theorem injective : Function.Injective e.f := e.strictMono.injective
theorem monotone : Monotone e.f := e.strictMono.monotone

@[simp] theorem map_top : e ⊤ = ⊤ := e.fix ⊤ le_top

theorem map_inf (a b : Life) : e (a ⊓ b) = e a ⊓ e b := e.monotone.map_min
theorem map_sup (a b : Life) : e (a ⊔ b) = e a ⊔ e b := e.monotone.map_max

/-- The map on the underlying naturals. -/
def toNat (n : ℕ) : ℕ := OrderDual.ofDual (e (OrderDual.toDual n))

theorem toNat_strictMono : StrictMono e.toNat := by
  intro a b h
  exact e.strictMono (a := OrderDual.toDual b) (b := OrderDual.toDual a) h

/-- `f` moves lifetimes only shorter. -/
theorem le_self (x : Life) : e x ≤ x := by
  have := e.toNat_strictMono.id_le (OrderDual.ofDual x)
  exact this

/-- Below the cut stays below the cut. -/
theorem lt_cut {x : Life} (h : x < c) : e x < c := lt_of_le_of_lt (e.le_self x) h

@[simp] theorem toNat_zero : e.toNat 0 = 0 := congrArg OrderDual.ofDual e.map_top

theorem toNat_min (m n : ℕ) : e.toNat (min m n) = min (e.toNat m) (e.toNat n) :=
  e.toNat_strictMono.monotone.map_min

theorem toNat_max (m n : ℕ) : e.toNat (max m n) = max (e.toNat m) (e.toNat n) :=
  e.toNat_strictMono.monotone.map_max

/-- The identity. -/
def id (c : Life) : Emb c where
  f x := x
  strictMono := strictMono_id
  fix _ _ := rfl

/-! ### Shifts -/

/-- `n ↦ n` at and above the cut, `n ↦ n + k` below it, on the naturals. -/
def shiftN (c k n : ℕ) : ℕ := if n ≤ c then n else n + k

theorem shiftN_strictMono (c k : ℕ) : StrictMono (shiftN c k) := by
  intro a b h
  unfold shiftN
  split_ifs <;> omega

/-- The shift by `k` of every lifetime strictly below `c`. -/
def shift (c : Life) (k : ℕ) : Emb c where
  f x := OrderDual.toDual (shiftN (OrderDual.ofDual c) k (OrderDual.ofDual x))
  strictMono := by
    intro a b h
    exact shiftN_strictMono (OrderDual.ofDual c) k (a := OrderDual.ofDual b)
      (b := OrderDual.ofDual a) h
  fix x hx := by
    show OrderDual.toDual (shiftN _ k _) = x
    unfold shiftN
    rw [if_pos (show OrderDual.ofDual x ≤ OrderDual.ofDual c from hx)]; rfl

theorem shift_apply_lt {c x : Life} {k : ℕ} (h : x < c) :
    OrderDual.ofDual (shift c k x) = OrderDual.ofDual x + k := by
  show shiftN _ _ _ = _
  unfold shiftN
  rw [if_neg]
  exact not_le.mpr h

/-- Strictly inside the moved interval, a shift commutes with `↓`. -/
theorem shift_down {c x : Life} {k : ℕ} (h : x < c) : shift c k (↓x) = ↓(shift c k x) := by
  have h' : (↓x) < c := lt_trans (Life.down_sqsubset x) h
  apply OrderDual.ofDual.injective
  rw [shift_apply_lt h']
  show OrderDual.ofDual x + 1 + k = OrderDual.ofDual (shift c k x) + 1
  rw [shift_apply_lt h]; omega

/-- At the cut, it does not: `f(↓c) = ↓c` moves to `↓c` shifted, while `↓f(c) = ↓c`. -/
theorem shift_down_cut (c : Life) {k : ℕ} (hk : 0 < k) : shift c k (↓c) ≠ ↓(shift c k c) := by
  intro h
  have h1 := congrArg OrderDual.ofDual h
  rw [shift_apply_lt (Life.down_sqsubset c), (shift c k).fix c le_rfl] at h1
  change OrderDual.ofDual c + 1 + k = OrderDual.ofDual c + 1 at h1
  omega

/-- No re-stratification other than the identity on `↓c` commutes with `↓` at the cut. -/
theorem down_cut_iff (e : Emb c) : e (↓c) = (↓(e c)) ↔ e (↓c) = (↓c) := by
  rw [e.fix c le_rfl]

/-- A shift by at least `p` puts every moved lifetime strictly below `p`. -/
theorem shift_fresh {c x : Life} (p : Life) {k : ℕ} (hk : OrderDual.ofDual p ≤ k) (h : x < c) :
    shift c k x < p := by
  show OrderDual.ofDual p < OrderDual.ofDual (shift c k x)
  rw [shift_apply_lt h]
  have : OrderDual.ofDual c < OrderDual.ofDual x := h
  omega

end Emb

/-! ### The lifetime level: `δ`, `@aδ`, `⟦Δ⟧` -/

open BoCa.Lifetime

/-- `f ∘ δ`, on the `LSub` carrier (whose codomain is `Life` carried as `ℕ`). -/
def LSub.mapN (g : ℕ → ℕ) (δ : LSub) : LSub := ⟨δ.entries.map fun p => (p.1, g p.2)⟩

theorem assocFind_map (g : ℕ → ℕ) (x : LifeVar) :
    ∀ l : List (LifeVar × ℕ),
      assocFind x (l.map fun p => (p.1, g p.2)) = (assocFind x l).map g
  | [] => rfl
  | (y, v) :: t => by
      simp only [List.map_cons, assocFind]
      split_ifs
      · rfl
      · exact assocFind_map g x t

theorem LSub.find?_mapN (g : ℕ → ℕ) (δ : LSub) (x : LifeVar) :
    (LSub.mapN g δ).find? x = (δ.find? x).map g :=
  assocFind_map g x δ.entries

theorem LSub.mapN_extend (g : ℕ → ℕ) (δ : LSub) (x : LifeVar) (n : ℕ) :
    LSub.mapN g (δ.extend x n) = (LSub.mapN g δ).extend x (g n) := rfl

namespace Emb
variable {c : BoCa.Fig16.Life} (e : Emb c)

/-- `@a(f ∘ δ) = f(@aδ)`: the interpretation of lifetime terms is natural. -/
theorem interp_mapN (δ : LSub) : ∀ a : BoCa.Lifetime.Life,
    a.interp (LSub.mapN e.toNat δ) = (a.interp δ).map e.toNat
  | .var x => LSub.find?_mapN _ δ x
  | .top => by simp [BoCa.Lifetime.Life.interp, SLife.top]
  | .join a b => by
      simp only [BoCa.Lifetime.Life.interp, interp_mapN δ a, interp_mapN δ b]
      cases a.interp δ <;> cases b.interp δ <;> simp only [Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, SLife.join]
      exact congrArg some (e.toNat_min _ _).symm
  | .meet a b => by
      simp only [BoCa.Lifetime.Life.interp, interp_mapN δ a, interp_mapN δ b]
      cases a.interp δ <;> cases b.interp δ <;> simp only [Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, SLife.meet]
      exact congrArg some (e.toNat_max _ _).symm

theorem interp_mapN_some {δ : LSub} {a : BoCa.Lifetime.Life} {n : ℕ} :
    a.interp (LSub.mapN e.toNat δ) = some n ↔ ∃ m, a.interp δ = some m ∧ e.toNat m = n := by
  rw [e.interp_mapN]
  cases a.interp δ <;> simp

/-- `⟦Δ⟧` is invariant: `δ ∈ ⟦Δ⟧ ↔ f ∘ δ ∈ ⟦Δ⟧`. -/
theorem models_mapN_iff (Δ : LifeCtx) (δ : LSub) :
    Δ.Models (LSub.mapN e.toNat δ) ↔ Δ.Models δ := by
  constructor
  · intro h x u hu
    obtain ⟨m', n', hm, hn, hlt⟩ := h x u hu
    rw [LSub.find?_mapN] at hm
    obtain ⟨m, hm0, rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨n, hn0, rfl⟩ := (e.interp_mapN_some).mp hn
    exact ⟨m, n, hm0, hn0, e.toNat_strictMono.lt_iff_lt.mp hlt⟩
  · intro h x u hu
    obtain ⟨m, n, hm, hn, hlt⟩ := h x u hu
    refine ⟨e.toNat m, e.toNat n, ?_, ?_, e.toNat_strictMono hlt⟩
    · rw [LSub.find?_mapN, hm]; rfl
    · rw [e.interp_mapN, hn]; rfl

theorem toNat_toDual (n : ℕ) : OrderDual.toDual (e.toNat n) = e (OrderDual.toDual n) := rfl

/-- `f(α) ⊏ @b(f ∘ δ) ↔ α ⊏ @bδ`. -/
theorem ltLife_mapN_iff (δ : LSub) (b : BoCa.Lifetime.Life) (α : BoCa.Fig16.Life) :
    BoCa.Fig16.LogRel.LtLife (LSub.mapN e.toNat δ) b (e α) ↔ BoCa.Fig16.LogRel.LtLife δ b α := by
  constructor
  · rintro ⟨β', hb, hlt⟩
    obtain ⟨β, hb0, rfl⟩ := (e.interp_mapN_some).mp hb
    exact ⟨β, hb0, e.lt_iff.mp hlt⟩
  · rintro ⟨β, hb, hlt⟩
    exact ⟨e.toNat β, by rw [e.interp_mapN, hb]; rfl, e.lt_iff.mpr hlt⟩

end Emb

end Restrat
