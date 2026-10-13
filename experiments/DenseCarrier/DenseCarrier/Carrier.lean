import Core.Relation
import Support.LogicalRelation.Facts

/-!
# DenseCarrier — the lifetimes the relation reads, and where the cells sit in them

Core's model keeps its carrier: cells, resources, `↭`, `wpTS` and the typed world `TW` are
`Paper/S5_Model` and `Core/World.lean` unchanged, stratified over `Life = ℕᵒᵈ` (`Cantor.lean`: the
index of the strata has to be reverse-well-ordered). Here a cell's lifetime is read as a **slot**:
which of the lifetimes in play it is.

The relation reads its lifetimes in a second linear order `L` with a top, the **lifetime order**:
`δ` sends lifetime variables into `L`, the `∀` ranges over `L`, and a cell's lifetime is compared
with an `L`-lifetime through `Slots`, a strictly monotone map from slots into `L` keeping `⊤`. At
`L = Life` and the identity it is Core (`Faithful.lean`); at a dense `L` the relation's `∀` reads
no adjacency (`Gap.lean`).

This file: `Slots`, `LSubD` (`δ : LifeVar ⇀ L`), `@aδ` over `L` (`interpD`), `atLifeD`,
`LtLifeD`, `⟦Δ⟧` over `L` (`ModelsD`), `Δ ⊨ @a ⊏ @b` over `L` (`EntailsLtD`), and the action of a
map `L → L` on `δ`.
-/

noncomputable section

namespace DenseCarrier
open BoCa BoCa.Fig16
open BoCa.Lifetime (LifeVar LifeCtx)

/-- Where the slots sit in the lifetime order `L`: strictly monotone, `⊤` to `⊤`. -/
structure Slots (L : Type) [LinearOrder L] [OrderTop L] where
  f : Life → L
  strictMono : StrictMono f
  map_top : f ⊤ = ⊤

namespace Slots
variable {L : Type} [LinearOrder L] [OrderTop L]

instance : CoeFun (Slots L) (fun _ => Life → L) := ⟨Slots.f⟩

theorem lt_iff (ι : Slots L) {a b : Life} : ι a < ι b ↔ a < b := ι.strictMono.lt_iff_lt
theorem le_iff (ι : Slots L) {a b : Life} : ι a ≤ ι b ↔ a ≤ b := ι.strictMono.le_iff_le

/-- The slots read in `Life` itself. -/
def id : Slots Life := ⟨fun x => x, strictMono_id, rfl⟩

/-- Moved by a strictly monotone map of `L` keeping `⊤`. -/
def comp (ι : Slots L) (φ : L → L) (hφ : StrictMono φ) (hφt : φ ⊤ = ⊤) : Slots L :=
  ⟨fun x => φ (ι x), hφ.comp ι.strictMono, by simp [ι.map_top, hφt]⟩

@[simp] theorem comp_apply (ι : Slots L) (φ : L → L) (hφ : StrictMono φ) (hφt : φ ⊤ = ⊤)
    (x : Life) : ι.comp φ hφ hφt x = φ (ι x) := rfl

/-- Moved by an order automorphism of `L`. -/
def map (ι : Slots L) (π : L ≃o L) : Slots L := ι.comp π π.strictMono (OrderIso.map_top π)

@[simp] theorem map_apply (ι : Slots L) (π : L ≃o L) (x : Life) : ι.map π x = π (ι x) := rfl

theorem ext {ι ι' : Slots L} (h : ∀ x, ι x = ι' x) : ι = ι' := by
  cases ι; cases ι'
  congr
  exact funext h

end Slots

/-- `δ : LifeVar ⇀ L`, an association list (`LSub` with `L` for `ℕ`). -/
structure LSubD (L : Type) where
  entries : List (LifeVar × L)

namespace LSubD
variable {L L' L'' : Type}

def find? (δ : LSubD L) (x : LifeVar) : Option L := Lifetime.assocFind x δ.entries

def extend (δ : LSubD L) (x : LifeVar) (α : L) : LSubD L := ⟨(x, α) :: δ.entries⟩

/-- `δ` moved by a map of lifetimes. -/
def map (φ : L → L') (δ : LSubD L) : LSubD L' := ⟨δ.entries.map fun p => (p.1, φ p.2)⟩

theorem find?_extend (δ : LSubD L) (x : LifeVar) (α : L) (y : LifeVar) :
    (δ.extend x α).find? y = if x = y then some α else δ.find? y := by
  simp only [find?, extend, Lifetime.assocFind]

theorem find?_extend_self (δ : LSubD L) (x : LifeVar) (α : L) :
    (δ.extend x α).find? x = some α := by
  rw [find?_extend, if_pos rfl]

theorem find?_extend_ne (δ : LSubD L) {x y : LifeVar} (α : L) (h : x ≠ y) :
    (δ.extend x α).find? y = δ.find? y := by
  rw [find?_extend, if_neg h]

theorem assocFind_map (φ : L → L') (x : LifeVar) :
    ∀ es : List (LifeVar × L),
      Lifetime.assocFind x (es.map fun p => (p.1, φ p.2)) = (Lifetime.assocFind x es).map φ
  | [] => rfl
  | (y, v) :: t => by
      simp only [List.map_cons, Lifetime.assocFind]
      split_ifs
      · rfl
      · exact assocFind_map φ x t

theorem find?_map (φ : L → L') (δ : LSubD L) (x : LifeVar) :
    (δ.map φ).find? x = (δ.find? x).map φ :=
  assocFind_map φ x δ.entries

theorem map_extend (φ : L → L') (δ : LSubD L) (x : LifeVar) (α : L) :
    (δ.extend x α).map φ = (δ.map φ).extend x (φ α) := rfl

theorem map_map (φ : L → L') (ψ : L' → L'') (δ : LSubD L) :
    (δ.map φ).map ψ = δ.map (ψ ∘ φ) := by
  simp [map, Function.comp_def]

theorem map_congr {φ ψ : L → L'} {δ : LSubD L} (h : ∀ p ∈ δ.entries, φ p.2 = ψ p.2) :
    δ.map φ = δ.map ψ := by
  simp only [map, LSubD.mk.injEq]
  exact List.map_congr_left fun p hp => by rw [h p hp]

theorem map_id (δ : LSubD L) : δ.map (fun x => x) = δ := by
  cases δ; simp [map]

end LSubD

section Interp
variable {L : Type} [LinearOrder L] [OrderTop L]

/-- `@aδ` over `L`: `δ('a)`, `⊤`, `⊔`, `⊓` (`Life.interp` with `L` for `ℕ`). -/
def interpD (δ : LSubD L) : Lifetime.Life → Option L
  | .var x => δ.find? x
  | .top => some ⊤
  | .join a b => (interpD δ a).bind fun m => (interpD δ b).bind fun n => some (m ⊔ n)
  | .meet a b => (interpD δ a).bind fun m => (interpD δ b).bind fun n => some (m ⊓ n)

theorem interpD_congr {δ₁ δ₂ : LSubD L} : ∀ (a : Lifetime.Life),
    (∀ x, a.mentions x = true → δ₁.find? x = δ₂.find? x) → interpD δ₁ a = interpD δ₂ a := by
  intro a
  induction a with
  | var y => intro h; exact h y (by simp [Lifetime.Life.mentions])
  | top => intro _; rfl
  | join p q ihp ihq =>
      intro h
      simp only [interpD,
        ihp (fun x hx => h x (by simp [Lifetime.Life.mentions, hx])),
        ihq (fun x hx => h x (by simp [Lifetime.Life.mentions, hx]))]
  | meet p q ihp ihq =>
      intro h
      simp only [interpD,
        ihp (fun x hx => h x (by simp [Lifetime.Life.mentions, hx])),
        ihq (fun x hx => h x (by simp [Lifetime.Life.mentions, hx]))]

theorem interpD_extend_of_not_mentions {δ : LSubD L} {z : LifeVar} {α : L}
    {c : Lifetime.Life} (h : c.mentions z = false) :
    interpD (δ.extend z α) c = interpD δ c := by
  refine interpD_congr c (fun w hw => ?_)
  by_cases hzw : z = w
  · subst hzw; simp [h] at hw
  · exact LSubD.find?_extend_ne δ α hzw

/-- `@(a[σ])δ = @a δ′` whenever `δ′` reads each variable of `@a` the way `δ` reads what `σ` sends
it to. -/
theorem interpD_applySub {σ : Lifetime.LSubst} {δ δ' : LSubD L} : ∀ (c : Lifetime.Life),
    (∀ y, c.mentions y = true → interpD δ ((Lifetime.Life.var y).applySub σ) = δ'.find? y) →
      interpD δ (c.applySub σ) = interpD δ' c := by
  intro c
  induction c with
  | var y => intro h; exact h y (by simp [Lifetime.Life.mentions])
  | top => intro _; rfl
  | join p q ihp ihq =>
      intro h
      simp only [Lifetime.Life.applySub, interpD,
        ihp (fun y hy => h y (by simp [Lifetime.Life.mentions, hy])),
        ihq (fun y hy => h y (by simp [Lifetime.Life.mentions, hy]))]
  | meet p q ihp ihq =>
      intro h
      simp only [Lifetime.Life.applySub, interpD,
        ihp (fun y hy => h y (by simp [Lifetime.Life.mentions, hy])),
        ihq (fun y hy => h y (by simp [Lifetime.Life.mentions, hy]))]

/-- A monotone map keeping `⊤` commutes with `@aδ`. -/
theorem interpD_map {L' : Type} [LinearOrder L'] [OrderTop L'] {φ : L → L'} (hφ : Monotone φ)
    (hφt : φ ⊤ = ⊤) (δ : LSubD L) :
    ∀ a : Lifetime.Life, interpD (δ.map φ) a = (interpD δ a).map φ := by
  intro a
  induction a with
  | var y => exact LSubD.find?_map φ δ y
  | top => simp [interpD, hφt]
  | join p q ihp ihq =>
      simp only [interpD, ihp, ihq]
      cases interpD δ p <;> cases interpD δ q <;> simp [hφ.map_max]
  | meet p q ihp ihq =>
      simp only [interpD, ihp, ihq]
      cases interpD δ p <;> cases interpD δ q <;> simp [hφ.map_min]

/-- `@aδ` as a connective's argument (`atLife` over `L`). -/
def atLifeD (δ : LSubD L) (a : Lifetime.Life) (F : L → BoLo.WProp) : BoLo.WProp :=
  fun ρ => ∃ α, interpD δ a = some α ∧ F α ρ

/-- `α ⊏ @bδ` (`LtLife` over `L`). -/
def LtLifeD (δ : LSubD L) (b : Lifetime.Life) (α : L) : Prop :=
  ∃ β, interpD δ b = some β ∧ α < β

/-- `δ ∈ ⟦Δ⟧` over `L` (`LifeCtx.Models` over `L`). -/
def ModelsD (Δ : LifeCtx) (δ : LSubD L) : Prop :=
  ∀ x u, Δ.find? x = some u → ∃ m n, δ.find? x = some m ∧ interpD δ u = some n ∧ m < n

/-- `Δ ⊨ @a ⊏ @b` over `L` (`LifeCtx.EntailsLt` over `L`). -/
def EntailsLtD (L : Type) [LinearOrder L] [OrderTop L] (Δ : LifeCtx) (a b : Lifetime.Life) :
    Prop :=
  ∀ δ : LSubD L, ModelsD Δ δ → ∃ m n, interpD δ a = some m ∧ interpD δ b = some n ∧ m < n

end Interp

end DenseCarrier

end
