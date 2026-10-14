import DenseCarrier.Carrier

/-!
# PartialLife — the lifetimes the relation reads, in a partial order

Core's model keeps its carrier: cells, resources, `↭`, `wpTS` and the typed world `TW` are
`Paper/S5_Model` and `Core/World.lean` unchanged, stratified over `Life = ℕᵒᵈ`. As in
`DenseCarrier/Carrier.lean` a cell's lifetime is read as a **slot**, and the relation reads its
lifetimes in a second order `L`; here `L` is a **partial order** with a top, so two lifetimes the
relation reads may be incomparable.

* `Reading L`: where each slot is read in `L`, any map keeping `⊤`. `DenseCarrier.Slots` asked a
  strictly monotone map; into a partial order a strictly monotone image of the slots is a chain, so
  two cells could never be read at incomparable lifetimes. `Reading.Extends` says the slot order
  extends the reading (a slot read strictly below another is strictly below it): the slots are then
  a linear extension, a schedule, of the lifetimes they are read at.
* `lubOpt`, `glbOpt`: `a ⊔ b`, `a ⊓ b` where the least upper (greatest lower) bound exists. A
  partial order need not have them; the lifetime terms `@a ⊔ @b`, `@a ⊓ @b` are read through them,
  and are undefined where the bound does not exist (`interpP`). In a lattice they are `⊔`, `⊓`
  (`lubOpt_eq`, `glbOpt_eq`).
* `interpP`, `atLifeP`, `LtLifeP`, `ModelsP`, `EntailsLtP`, `EntailsLeP`: `DenseCarrier`'s
  `interpD`, … over a partial order.
* `interpP_map`: an order automorphism commutes with `interpP`, because it preserves least upper
  and greatest lower bounds.
-/

noncomputable section

namespace PartialLife
open BoCa BoCa.Fig16
open BoCa.Lifetime (LifeVar LifeCtx)
open DenseCarrier (LSubD)

/-- Where the slots are read in the lifetime order `L`: any map keeping `⊤`. -/
structure Reading (L : Type) [PartialOrder L] [OrderTop L] where
  f : Life → L
  map_top : f ⊤ = ⊤

namespace Reading
variable {L : Type} [PartialOrder L] [OrderTop L]

instance : CoeFun (Reading L) (fun _ => Life → L) := ⟨Reading.f⟩

/-- The slots read in `Life` itself. -/
def id : Reading Life := ⟨fun x => x, rfl⟩

@[simp] theorem id_apply (x : Life) : Reading.id x = x := rfl

/-- Moved by an order automorphism of `L`. -/
def map (ι : Reading L) (π : L ≃o L) : Reading L :=
  ⟨fun x => π (ι x), by rw [ι.map_top]; exact OrderIso.map_top π⟩

@[simp] theorem map_apply (ι : Reading L) (π : L ≃o L) (x : Life) : ι.map π x = π (ι x) := rfl

/-- **The slot order extends the reading**: a slot read strictly below another is strictly below
it. The slots are then a linear extension of the lifetimes they are read at. -/
def Extends (ι : Reading L) : Prop := ∀ s t : Life, ι s < ι t → s < t

theorem extends_id : Extends Reading.id := fun _ _ h => h

theorem Extends.map {ι : Reading L} (h : ι.Extends) (π : L ≃o L) : (ι.map π).Extends :=
  fun s t hst => h s t (π.lt_iff_lt.mp hst)

end Reading

/-! ### Least upper and greatest lower bounds where they exist -/

section Bounds
variable {L : Type} [PartialOrder L]

open Classical in
/-- `a ⊔ b`, where the least upper bound of `{a, b}` exists. -/
def lubOpt (a b : L) : Option L :=
  if h : ∃ c, IsLUB ({a, b} : Set L) c then some (Classical.choose h) else none

open Classical in
/-- `a ⊓ b`, where the greatest lower bound of `{a, b}` exists. -/
def glbOpt (a b : L) : Option L :=
  if h : ∃ c, IsGLB ({a, b} : Set L) c then some (Classical.choose h) else none

theorem lubOpt_eq_some {a b c : L} : lubOpt a b = some c ↔ IsLUB ({a, b} : Set L) c := by
  unfold lubOpt
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun e => e ▸ Classical.choose_spec h, fun hc => (Classical.choose_spec h).unique hc⟩
  · simp only [false_iff]
    exact fun hc => h ⟨c, hc⟩

theorem lubOpt_eq_none {a b : L} : lubOpt a b = none ↔ ¬ ∃ c, IsLUB ({a, b} : Set L) c := by
  unfold lubOpt
  split_ifs with h <;> simp [h]

theorem glbOpt_eq_some {a b c : L} : glbOpt a b = some c ↔ IsGLB ({a, b} : Set L) c := by
  unfold glbOpt
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun e => e ▸ Classical.choose_spec h, fun hc => (Classical.choose_spec h).unique hc⟩
  · simp only [false_iff]
    exact fun hc => h ⟨c, hc⟩

theorem glbOpt_eq_none {a b : L} : glbOpt a b = none ↔ ¬ ∃ c, IsGLB ({a, b} : Set L) c := by
  unfold glbOpt
  split_ifs with h <;> simp [h]

/-- An order automorphism carries least upper bounds of pairs. -/
theorem isLUB_pair_map (π : L ≃o L) {a b c : L} :
    IsLUB ({π a, π b} : Set L) (π c) ↔ IsLUB ({a, b} : Set L) c := by
  have h := π.isLUB_image (s := ({a, b} : Set L)) (x := π c)
  rwa [Set.image_pair, OrderIso.symm_apply_apply] at h

theorem isGLB_pair_map (π : L ≃o L) {a b c : L} :
    IsGLB ({π a, π b} : Set L) (π c) ↔ IsGLB ({a, b} : Set L) c := by
  have h := π.isGLB_image (s := ({a, b} : Set L)) (x := π c)
  rwa [Set.image_pair, OrderIso.symm_apply_apply] at h

theorem lubOpt_map (π : L ≃o L) (a b : L) : lubOpt (π a) (π b) = (lubOpt a b).map π := by
  cases h : lubOpt a b with
  | some c =>
      exact lubOpt_eq_some.mpr ((isLUB_pair_map π).mpr (lubOpt_eq_some.mp h))
  | none =>
      refine lubOpt_eq_none.mpr ?_
      rintro ⟨c', hc'⟩
      rw [← π.apply_symm_apply c', isLUB_pair_map] at hc'
      exact lubOpt_eq_none.mp h ⟨_, hc'⟩

theorem glbOpt_map (π : L ≃o L) (a b : L) : glbOpt (π a) (π b) = (glbOpt a b).map π := by
  cases h : glbOpt a b with
  | some c =>
      exact glbOpt_eq_some.mpr ((isGLB_pair_map π).mpr (glbOpt_eq_some.mp h))
  | none =>
      refine glbOpt_eq_none.mpr ?_
      rintro ⟨c', hc'⟩
      rw [← π.apply_symm_apply c', isGLB_pair_map] at hc'
      exact glbOpt_eq_none.mp h ⟨_, hc'⟩

/-- In a lattice the bound is `⊔`. -/
theorem lubOpt_eq {L : Type} [Lattice L] (a b : L) : lubOpt a b = some (a ⊔ b) :=
  lubOpt_eq_some.mpr isLUB_pair

/-- In a lattice the bound is `⊓`. -/
theorem glbOpt_eq {L : Type} [Lattice L] (a b : L) : glbOpt a b = some (a ⊓ b) :=
  glbOpt_eq_some.mpr isGLB_pair

end Bounds

/-! ### The reading of lifetime terms and contexts -/

section Interp
variable {L : Type} [PartialOrder L] [OrderTop L]

/-- `@aδ` over a partial order: `δ('a)`, `⊤`, and `⊔`, `⊓` where they exist. -/
def interpP (δ : LSubD L) : Lifetime.Life → Option L
  | .var x => δ.find? x
  | .top => some ⊤
  | .join a b => (interpP δ a).bind fun m => (interpP δ b).bind fun n => lubOpt m n
  | .meet a b => (interpP δ a).bind fun m => (interpP δ b).bind fun n => glbOpt m n

/-- **An order automorphism commutes with `@aδ`.** -/
theorem interpP_map (π : L ≃o L) (δ : LSubD L) :
    ∀ a : Lifetime.Life, interpP (δ.map π) a = (interpP δ a).map π := by
  intro a
  induction a with
  | var y => exact LSubD.find?_map π δ y
  | top => simp [interpP]
  | join p q ihp ihq =>
      simp only [interpP, ihp, ihq]
      cases interpP δ p <;> cases interpP δ q <;> simp [lubOpt_map]
  | meet p q ihp ihq =>
      simp only [interpP, ihp, ihq]
      cases interpP δ p <;> cases interpP δ q <;> simp [glbOpt_map]

/-- `@aδ` as a connective's argument (`atLife` over `L`). -/
def atLifeP (δ : LSubD L) (a : Lifetime.Life) (F : L → BoLo.WProp) : BoLo.WProp :=
  fun ρ => ∃ α, interpP δ a = some α ∧ F α ρ

/-- `α ⊏ @bδ` (`LtLife` over `L`). -/
def LtLifeP (δ : LSubD L) (b : Lifetime.Life) (α : L) : Prop :=
  ∃ β, interpP δ b = some β ∧ α < β

/-- `δ ∈ ⟦Δ⟧` over `L` (`LifeCtx.Models` over `L`). -/
def ModelsP (Δ : LifeCtx) (δ : LSubD L) : Prop :=
  ∀ x u, Δ.find? x = some u → ∃ m n, δ.find? x = some m ∧ interpP δ u = some n ∧ m < n

/-- `Δ ⊨ @a ⊏ @b` over `L` (`LifeCtx.EntailsLt` over `L`). -/
def EntailsLtP (L : Type) [PartialOrder L] [OrderTop L] (Δ : LifeCtx) (a b : Lifetime.Life) :
    Prop :=
  ∀ δ : LSubD L, ModelsP Δ δ → ∃ m n, interpP δ a = some m ∧ interpP δ b = some n ∧ m < n

/-- `Δ ⊨ @a ⊑ @b` over `L` (`LifeCtx.EntailsLe` over `L`). -/
def EntailsLeP (L : Type) [PartialOrder L] [OrderTop L] (Δ : LifeCtx) (a b : Lifetime.Life) :
    Prop :=
  ∀ δ : LSubD L, ModelsP Δ δ → ∃ m n, interpP δ a = some m ∧ interpP δ b = some n ∧ m ≤ n

theorem atLifeP_map (π : L ≃o L) (δ : LSubD L) (a : Lifetime.Life) (F : L → BoLo.WProp) :
    atLifeP (δ.map π) a F = atLifeP δ a (fun α => F (π α)) := by
  funext ρ
  simp only [atLifeP, interpP_map]
  apply propext
  constructor
  · rintro ⟨α', hα', hF⟩
    obtain ⟨α, hα, rfl⟩ := Option.map_eq_some_iff.mp hα'
    exact ⟨α, hα, hF⟩
  · rintro ⟨α, hα, hF⟩
    exact ⟨π α, by rw [hα]; rfl, hF⟩

theorem ltLifeP_map (π : L ≃o L) (δ : LSubD L) (b : Lifetime.Life) (α : L) :
    LtLifeP (δ.map π) b (π α) ↔ LtLifeP δ b α := by
  simp only [LtLifeP, interpP_map]
  constructor
  · rintro ⟨β', hβ', hlt⟩
    obtain ⟨β, hβ, rfl⟩ := Option.map_eq_some_iff.mp hβ'
    exact ⟨β, hβ, π.lt_iff_lt.mp hlt⟩
  · rintro ⟨β, hβ, hlt⟩
    exact ⟨π β, by rw [hβ]; rfl, π.lt_iff_lt.mpr hlt⟩

theorem modelsP_map (π : L ≃o L) (Δ : LifeCtx) (δ : LSubD L) :
    ModelsP Δ (δ.map π) ↔ ModelsP Δ δ := by
  simp only [ModelsP, LSubD.find?_map, interpP_map]
  refine forall_congr' fun x => forall_congr' fun u => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨m', n', hm', hn', hlt⟩
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hm'
    obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp hn'
    exact ⟨m, n, hm, hn, π.lt_iff_lt.mp hlt⟩
  · rintro ⟨m, n, hm, hn, hlt⟩
    exact ⟨π m, π n, by rw [hm]; rfl, by rw [hn]; rfl, π.lt_iff_lt.mpr hlt⟩

end Interp

end PartialLife

end
