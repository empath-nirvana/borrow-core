import Core.Chain.SI.UpdMask

/-!
# The ghost resource of the one relation  `[spec §62]`

`docs/new-core/scope-821-loans.md`, stage 1. `GRes` has three parts, each with the standard
composition and validity:

* **lifetime tokens** `[α]_q`, `Life → ℚ≥0`, composed by adding fractions, valid when every sum
  is at most `1` (Boyland; RustBelt's `[α]_q`);
* **`mut` authorities** `xm`, keyed by `Loc`, exclusive;
* **the task registry**, Iris's `Auth(Loc ⇀ Agree(Ret))`: at most one authoritative map, and at
  each slot at most one `tok r` fragment (the joiner's) and one `wr r` fragment (the child's),
  each agreeing with the authoritative entry.

Every part is a counting map, so composition is pointwise addition: commutative, associative,
with unit `0`. Validity is downward closed (`GRes.Valid.left`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16

/-- A loan a task returns at its join: a fraction of a lifetime, or a `mut` cell's authority. -/
inductive Loan where
  | imm (α : Life) (q : ℚ≥0)
  | mut (l : Loc) (b : Life) (P : Val → SPropS Loc Val b)

/-- What a task returns at its join. -/
abbrev Ret := List Loan

/-- **The ghost resource.** -/
@[ext]
structure GRes where
  /-- Lifetime tokens `[α]_q`. -/
  tok : Life → ℚ≥0
  /-- `mut` authorities. -/
  xm : Loc → ℕ
  /-- The registry's authoritative piece `●m`, counted. -/
  auth : (Loc → Option Ret) → ℕ
  /-- The joiner's fragments `tok r` at each slot, counted. -/
  tokF : Loc → Ret → ℕ
  /-- The child's fragments `wr r` at each slot, counted. -/
  wrF : Loc → Ret → ℕ

namespace GRes

instance : Zero GRes := ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩⟩

instance : Add GRes :=
  ⟨fun g h => ⟨fun α => g.tok α + h.tok α, fun l => g.xm l + h.xm l,
    fun m => g.auth m + h.auth m, fun a r => g.tokF a r + h.tokF a r,
    fun a r => g.wrF a r + h.wrF a r⟩⟩

@[simp] theorem tok_add (g h : GRes) (α : Life) : (g + h).tok α = g.tok α + h.tok α := rfl
@[simp] theorem xm_add (g h : GRes) (l : Loc) : (g + h).xm l = g.xm l + h.xm l := rfl
@[simp] theorem auth_add (g h : GRes) m : (g + h).auth m = g.auth m + h.auth m := rfl
@[simp] theorem tokF_add (g h : GRes) a r : (g + h).tokF a r = g.tokF a r + h.tokF a r := rfl
@[simp] theorem wrF_add (g h : GRes) a r : (g + h).wrF a r = g.wrF a r + h.wrF a r := rfl
@[simp] theorem tok_zero (α : Life) : (0 : GRes).tok α = 0 := rfl
@[simp] theorem xm_zero (l : Loc) : (0 : GRes).xm l = 0 := rfl
@[simp] theorem auth_zero m : (0 : GRes).auth m = 0 := rfl
@[simp] theorem tokF_zero a r : (0 : GRes).tokF a r = 0 := rfl
@[simp] theorem wrF_zero a r : (0 : GRes).wrF a r = 0 := rfl

theorem add_comm (g h : GRes) : g + h = h + g := by
  ext <;> simp [_root_.add_comm]

theorem add_assoc (g h k : GRes) : g + h + k = g + (h + k) := by
  ext <;> simp [_root_.add_assoc]

@[simp] theorem add_zero (g : GRes) : g + 0 = g := by ext <;> simp

@[simp] theorem zero_add (g : GRes) : 0 + g = g := by ext <;> simp

theorem add_left_comm (g h k : GRes) : g + (h + k) = h + (g + k) := by
  rw [← add_assoc, add_comm g h, add_assoc]

theorem add_right_comm (g h k : GRes) : g + h + k = g + k + h := by
  rw [add_assoc, add_comm h k, ← add_assoc]

/-- **Validity.** Each fraction is at most `1`; each authority and fragment exclusive; one
authoritative map; every fragment agrees with it. -/
structure Valid (g : GRes) : Prop where
  tok : ∀ α, g.tok α ≤ 1
  xm : ∀ l, g.xm l ≤ 1
  auth_le : ∀ m, g.auth m ≤ 1
  auth_one : ∀ m m', 0 < g.auth m → 0 < g.auth m' → m = m'
  tokF_le : ∀ a r, g.tokF a r ≤ 1
  tokF_one : ∀ a r r', 0 < g.tokF a r → 0 < g.tokF a r' → r = r'
  wrF_le : ∀ a r, g.wrF a r ≤ 1
  wrF_one : ∀ a r r', 0 < g.wrF a r → 0 < g.wrF a r' → r = r'
  tokF_agree : ∀ m a r, 0 < g.auth m → 0 < g.tokF a r → m a = some r
  wrF_agree : ∀ m a r, 0 < g.auth m → 0 < g.wrF a r → m a = some r
  /-- Finitely many lifetimes have a token, so a fresh one can be minted. -/
  fin : {α | 0 < g.tok α}.Finite

theorem valid_zero : (0 : GRes).Valid :=
  ⟨fun _ => by simp, fun _ => by simp, fun _ => by simp, fun _ _ h => by simp at h,
    fun _ _ => by simp, fun _ _ _ h => by simp at h, fun _ _ => by simp,
    fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h,
    Set.finite_empty.subset (fun α h => by simp at h)⟩

/-- **Validity is downward closed.** -/
theorem Valid.left {g h : GRes} (hv : (g + h).Valid) : g.Valid := by
  obtain ⟨t, x, al, ao, tl, tz, wl, wo, ta, wa, fi⟩ := hv
  refine ⟨fun α => le_trans le_self_add (t α), fun l => le_trans (Nat.le_add_right _ _) (x l),
    fun m => le_trans (Nat.le_add_right _ _) (al m), fun m m' h₁ h₂ => ao m m' (by simp; omega)
      (by simp; omega), fun a r => le_trans (Nat.le_add_right _ _) (tl a r),
    fun a r r' h₁ h₂ => tz a r r' (by simp; omega) (by simp; omega),
    fun a r => le_trans (Nat.le_add_right _ _) (wl a r),
    fun a r r' h₁ h₂ => wo a r r' (by simp; omega) (by simp; omega),
    fun m a r h₁ h₂ => ta m a r (by simp; omega) (by simp; omega),
    fun m a r h₁ h₂ => wa m a r (by simp; omega) (by simp; omega),
    fi.subset (fun α hα => lt_of_lt_of_le hα (show g.tok α ≤ g.tok α + h.tok α from le_self_add))⟩

theorem Valid.right {g h : GRes} (hv : (g + h).Valid) : h.Valid :=
  Valid.left (by rwa [add_comm] at hv)

/-- The lifetimes with a token: `C`. -/
def counted (g : GRes) : Set Life := {α | 0 < g.tok α}

theorem mem_counted_add {g h : GRes} {α : Life} :
    α ∈ counted (g + h) ↔ α ∈ counted g ∨ α ∈ counted h := by
  show 0 < g.tok α + h.tok α ↔ 0 < g.tok α ∨ 0 < h.tok α
  simp only [pos_iff_ne_zero, ne_eq, add_eq_zero, not_and_or]

/-- A token held whole by a part of a valid sum is the sum's whole token. -/
theorem tok_one_of_add {g h : GRes} (hv : (g + h).Valid) {α : Life} (h1 : g.tok α = 1) :
    (g + h).tok α = 1 :=
  le_antisymm (hv.tok α) (by rw [tok_add, h1]; exact le_self_add)

theorem xm_one_of_add {g h : GRes} (hv : (g + h).Valid) {l : Loc} (h1 : g.xm l = 1) :
    (g + h).xm l = 1 :=
  le_antisymm (hv.xm l) (by rw [xm_add, h1]; exact Nat.le_add_right _ _)

/-- `[α]_1`. -/
def life (α : Life) : GRes :=
  ⟨fun β => if β = α then 1 else 0, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩

@[simp] theorem tok_life (α β : Life) : (life α).tok β = if β = α then 1 else 0 := rfl
@[simp] theorem xm_life (α : Life) (l : Loc) : (life α).xm l = 0 := rfl
@[simp] theorem auth_life (α : Life) m : (life α).auth m = 0 := rfl
@[simp] theorem tokF_life (α : Life) a r : (life α).tokF a r = 0 := rfl
@[simp] theorem wrF_life (α : Life) a r : (life α).wrF a r = 0 := rfl

/-- `[α]_1` composes with anything holding no fraction of `α`. -/
theorem valid_add_life {g : GRes} (hv : g.Valid) {α : Life} (h0 : g.tok α = 0) :
    (g + life α).Valid := by
  obtain ⟨t, x, al, ao, tl, tz, wl, wo, ta, wa, fi⟩ := hv
  have ht : ∀ β, (g + life α).tok β ≤ 1 := by
    intro β
    by_cases hβ : β = α
    · subst hβ; simp [h0]
    · simpa [hβ] using t β
  have hfi : {β | 0 < (g + life α).tok β}.Finite := by
    refine (fi.union (Set.finite_singleton α)).subset (fun β hβ => ?_)
    by_cases hβα : β = α
    · exact Or.inr hβα
    · exact Or.inl (by simpa [hβα] using hβ)
  exact ⟨ht, fun l => by simpa using x l, fun m => by simpa using al m,
    fun m m' h₁ h₂ => ao m m' (by simpa using h₁) (by simpa using h₂),
    fun a r => by simpa using tl a r,
    fun a r r' h₁ h₂ => tz a r r' (by simpa using h₁) (by simpa using h₂),
    fun a r => by simpa using wl a r,
    fun a r r' h₁ h₂ => wo a r r' (by simpa using h₁) (by simpa using h₂),
    fun m a r h₁ h₂ => ta m a r (by simpa using h₁) (by simpa using h₂),
    fun m a r h₁ h₂ => wa m a r (by simpa using h₁) (by simpa using h₂), hfi⟩

/-- **A fresh lifetime**: below any given one and with no token in a valid `g`. -/
theorem exists_fresh_life {g : GRes} (hv : g.Valid) (a : Life) :
    ∃ A : Life, A < a ∧ g.tok A = 0 := by
  obtain ⟨N, hN⟩ := (hv.fin.image OrderDual.ofDual).bddAbove
  refine ⟨OrderDual.toDual (max N (OrderDual.ofDual a) + 1), ?_, ?_⟩
  · show OrderDual.ofDual a < max N (OrderDual.ofDual a) + 1
    omega
  · by_contra hne
    have hmem : OrderDual.ofDual (OrderDual.toDual (max N (OrderDual.ofDual a) + 1)) ∈
        OrderDual.ofDual '' {α | 0 < g.tok α} :=
      ⟨_, pos_iff_ne_zero.mpr hne, rfl⟩
    have := hN hmem
    simp only [OrderDual.ofDual_toDual] at this
    omega

end GRes

end BoCa.Fig16.LogRel.Core.Chain.SI

end
