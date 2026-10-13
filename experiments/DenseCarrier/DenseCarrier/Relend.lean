import DenseCarrier.Reslot

/-!
# DenseCarrier — re-lending a region: the region's cells re-made, at every depth

Law 2 re-lends a suspended region at fresh lifetimes beneath the resumer's list. On the two-order
design a re-lending is a re-slotting `θ : Restrat.Emb c` of the region's slots (those below the
cut `c`) together with a move `ψ` of the reading that agrees with it on the slots
(`ψ (ι s) = ι (θ s)`) and keeps the order (`StrictMono ψ`): `Relend ι`. Every such `θ` may put the
region below any given lifetimes (`Restrat.Emb.shift_fresh`), so "beneath the resumer's list" is
one choice of it.

The region's cells are **re-made**, not moved: a re-made cell has the kind, value and location of
the old one, its slot moved by `θ`, its witness re-made cell by cell, and a `mut` cell stores
whatever predicate the relation at the moved reading asks for (`RemakeC`, `RemakeR`). Moving a
cell's stored predicate to its image (`θ.relRU`) is what `Reslot.lean` refutes.

* `RelendV ι A`: **re-lending preserves the relation at `A`** — every configuration related at `A`
  has a re-make related at the moved reading. This is the invariant of the stored predicates: a
  `mut` cell storing `𝒱⟦A⟧` can be re-made exactly when `RelendV ι A` holds at its payload.
* `relendV_of_fov`: **it holds at every first-order type** — `1`, `⊗`, `Ref`, `[@a]` and `Mut`,
  nested to any depth — by one induction over the clauses (`relend_fov`). No case split on depth
  or on a witness.
* The `Mut` clause's stratification conjunct (the payload lies in the stratum of the cell) is the
  one step that is not pointwise: it is carried to the moved reading by reading where a payload's
  top-level cells may sit (`lbV`), which only compares lifetimes (`lbV_relend`), and by lowering a
  top-level cell to any slot those comparisons allow (`lower_vD`): `strat_relend`.

`RelendRoom.lean` shows the invariant is not closed under `U`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)

variable {L : Type} [LinearOrder L] [OrderTop L]

/-! ### Re-lendings -/

/-- **A re-lending**: the slots below the cut `c` re-slotted by `θ`, the reading moved by `ψ`, which
keeps the order and agrees with `θ` on the slots' positions. -/
structure Relend (ι : Slots L) where
  c : Life
  θ : Restrat.Emb c
  ψ : L → L
  mono : StrictMono ψ
  agree : ∀ s, ψ (ι s) = ι (θ s)

namespace Relend
variable {ι : Slots L} (R : Relend ι)

theorem map_top : R.ψ ⊤ = ⊤ := by
  have h := R.agree ⊤
  rwa [ι.map_top, R.θ.map_top, ι.map_top] at h

/-- `@a(ψ ∘ δ) = ψ(@aδ)`. -/
theorem interp (δ : LSubD L) (a : Lifetime.Life) :
    interpD (δ.map R.ψ) a = (interpD δ a).map R.ψ :=
  interpD_map R.mono.monotone R.map_top δ a

theorem interp_some {δ : LSubD L} {a : Lifetime.Life} {α : L} (h : interpD δ a = some α) :
    interpD (δ.map R.ψ) a = some (R.ψ α) := by
  rw [R.interp, h]; rfl

theorem interp_some_inv {δ : LSubD L} {a : Lifetime.Life} {α' : L}
    (h : interpD (δ.map R.ψ) a = some α') : ∃ α, interpD δ a = some α ∧ R.ψ α = α' := by
  rw [R.interp] at h
  exact Option.map_eq_some_iff.mp h

end Relend

/-! ### Re-made cells and resources -/

mutual
/-- `ψ'` is `ψ` **re-made** at the re-slotting `θ`: an `own` cell is kept; a `mut` cell keeps its
kind and value, its slot is moved by `θ`, and its witness is re-made cell by cell. The stored
predicate of the re-made `mut` cell is not constrained: the relation at the moved reading says
what it is. -/
inductive RemakeC {c : Life} (θ : Restrat.Emb c) : CellU Loc Val → CellU Loc Val → Prop
  | own (v : Val) : RemakeC θ (.own v) (.own v)
  | mut {ψ ψ' : CellU Loc Val} (hk : ψ.kind = Kind.mut) (hk' : ψ'.kind = Kind.mut)
      (hat : ψ'.at = θ ψ.at) (hv : ψ'.erase = ψ.erase)
      (hw : ∀ l, RemakeO θ (ψ.wit.get l) (ψ'.wit.get l)) : RemakeC θ ψ ψ'

/-- Re-made at one location: both empty, or a cell and its re-make. -/
inductive RemakeO {c : Life} (θ : Restrat.Emb c) :
    Option (CellU Loc Val) → Option (CellU Loc Val) → Prop
  | none : RemakeO θ none none
  | some {a b : CellU Loc Val} : RemakeC θ a b → RemakeO θ (some a) (some b)
end

/-- `ρ'` is `ρ` re-made at `θ`, location by location. -/
def RemakeR {c : Life} (θ : Restrat.Emb c) (ρ ρ' : WRes) : Prop :=
  ∀ l, RemakeO θ (ρ.get l) (ρ'.get l)

section Remake
variable {c : Life} {θ : Restrat.Emb c}

theorem RemakeC.kind {a b : CellU Loc Val} (h : RemakeC θ a b) : b.kind = a.kind := by
  cases h with
  | own v => rfl
  | «mut» hk hk' => rw [hk, hk']

theorem RemakeC.kind_ne_imm {a b : CellU Loc Val} (h : RemakeC θ a b) : a.kind ≠ Kind.imm := by
  cases h with
  | own v => exact fun e => Kind.noConfusion e
  | «mut» hk => rw [hk]; exact fun e => Kind.noConfusion e

theorem RemakeC.erase {a b : CellU Loc Val} (h : RemakeC θ a b) : b.erase = a.erase := by
  cases h with
  | own v => rfl
  | «mut» hk hk' hat hv => exact hv

/-- The witness of a re-made cell is the re-made witness. -/
theorem RemakeC.wit {a b : CellU Loc Val} (h : RemakeC θ a b) : ∀ l, RemakeO θ (a.wit.get l) (b.wit.get l) := by
  cases h with
  | own v => intro l; exact RemakeO.none
  | «mut» hk hk' hat hv hw => exact hw

/-- A `mut` cell lies in the stratum of `α` exactly when its slot is above `α`. -/
theorem inStratum_iff_of_mut {ψ : CellU Loc Val} (hk : ψ.kind = Kind.mut) (α : Life) :
    ψ.InStratum α ↔ α < ψ.at := by
  cases ψ with
  | own v => exact absurd hk (fun e => Kind.noConfusion e)
  | imm i => exact absurd hk (fun e => Kind.noConfusion e)
  | «mut» m => exact Iff.rfl

theorem RemakeC.inStratum {a b : CellU Loc Val} (h : RemakeC θ a b) {α : Life}
    (ha : a.InStratum α) : b.InStratum (θ α) := by
  cases h with
  | own v => exact trivial
  | «mut» hk hk' hat =>
      rw [inStratum_iff_of_mut hk'] 
      rw [inStratum_iff_of_mut hk] at ha
      rw [hat]
      exact θ.strictMono ha

theorem remakeR_empty_iff {ρ' : WRes} : RemakeR θ PMap.empty ρ' ↔ ρ' = PMap.empty := by
  constructor
  · intro h
    refine PMap.ext fun l => ?_
    have hl := h l
    rw [PMap.empty_get] at hl
    cases e : ρ'.get l with
    | none => rfl
    | some b => rw [e] at hl; cases hl
  · rintro rfl l
    exact RemakeO.none

theorem remakeR_empty : RemakeR θ (PMap.empty : WRes) PMap.empty := remakeR_empty_iff.mpr rfl

theorem remakeR_single {l : Loc} {a b : CellU Loc Val} (h : RemakeC θ a b) :
    RemakeR θ (ResU.single l a) (ResU.single l b) := by
  intro k
  by_cases e : k = l
  · subst e
    rw [ResU.single_get_self, ResU.single_get_self]
    exact RemakeO.some h
  · rw [ResU.single_get_ne _ e, ResU.single_get_ne _ e]
    exact RemakeO.none

theorem RemakeR.get_none_iff {ρ ρ' : WRes} (h : RemakeR θ ρ ρ') (l : Loc) :
    ρ'.get l = none ↔ ρ.get l = none := by
  have hl := h l
  cases e : ρ.get l <;> cases e' : ρ'.get l <;> rw [e, e'] at hl <;> simp <;> cases hl

theorem RemakeR.get_some {ρ ρ' : WRes} (h : RemakeR θ ρ ρ') {l : Loc} {b : CellU Loc Val}
    (e' : ρ'.get l = some b) : ∃ a, ρ.get l = some a ∧ RemakeC θ a b := by
  have hl := h l
  rw [e'] at hl
  cases e : ρ.get l with
  | none => rw [e] at hl; cases hl
  | some a =>
      rw [e] at hl
      cases hl with
      | some hab => exact ⟨a, rfl, hab⟩

theorem RemakeR.get_some' {ρ ρ' : WRes} (h : RemakeR θ ρ ρ') {l : Loc} {a : CellU Loc Val}
    (e : ρ.get l = some a) : ∃ b, ρ'.get l = some b ∧ RemakeC θ a b := by
  have hl := h l
  rw [e] at hl
  cases e' : ρ'.get l with
  | none => rw [e'] at hl; cases hl
  | some b =>
      rw [e'] at hl
      cases hl with
      | some hab => exact ⟨b, rfl, hab⟩

/-- A re-made resource lies in the moved stratum. -/
theorem RemakeR.inStratum {ρ ρ' : WRes} (h : RemakeR θ ρ ρ') {α : Life} (hρ : ρ.InStratum α) :
    ρ'.InStratum (θ α) := by
  intro l b e'
  obtain ⟨a, e, hab⟩ := h.get_some e'
  exact hab.inStratum (hρ l a e)

/-- A re-made resource has no `imm` cell. -/
theorem RemakeR.ne_imm {ρ ρ' : WRes} (h : RemakeR θ ρ ρ') {l : Loc} {a : CellU Loc Val}
    (e : ρ.get l = some a) : a.kind ≠ Kind.imm := by
  obtain ⟨b, -, hab⟩ := h.get_some' e
  exact hab.kind_ne_imm

/-- Two resources compose only where both have `imm` cells: one with no `imm` cell is disjoint
from what it composes with. -/
theorem disjoint_of_compS {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : ∀ l a, ρ₁.get l = some a → a.kind ≠ Kind.imm) (l : Loc) :
    ρ₁.get l = none ∨ ρ₂.get l = none := by
  cases e₁ : ρ₁.get l with
  | none => exact Or.inl rfl
  | some a =>
      cases e₂ : ρ₂.get l with
      | none => exact Or.inr rfl
      | some b => exact absurd (CellU.CompatS.kinds (hc.1 l a b e₁ e₂)).1 (h₁ l a e₁)

/-- **Re-making commutes with `●`**: re-makes of the two sides compose, to a re-make of the
composite. -/
theorem remakeR_compS {ρ₁ ρ₂ ρ ρ₁' ρ₂' : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : RemakeR θ ρ₁ ρ₁') (h₂ : RemakeR θ ρ₂ ρ₂') :
    ∃ ρ', ResU.CompS ρ₁' ρ₂' ρ' ∧ RemakeR θ ρ ρ' := by
  have hd : ∀ l, ρ₁.get l = none ∨ ρ₂.get l = none :=
    disjoint_of_compS hc (fun l a e => h₁.ne_imm e)
  have hd' : ∀ l, ρ₁'.get l = none ∨ ρ₂'.get l = none := fun l => by
    rcases hd l with e | e
    · exact Or.inl ((h₁.get_none_iff l).mpr e)
    · exact Or.inr ((h₂.get_none_iff l).mpr e)
  obtain ⟨ρ', hc'⟩ := (ResU.compS_defined_iff ρ₁' ρ₂').mpr (ResU.Compat.of_disjoint hd')
  refine ⟨ρ', hc', fun l => ?_⟩
  rcases hd l with e | e
  · rw [ResU.Comp.get_of_left_none hc e,
      ResU.Comp.get_of_left_none hc' ((h₁.get_none_iff l).mpr e)]
    exact h₂ l
  · rw [ResU.Comp.get_of_right_none hc e,
      ResU.Comp.get_of_right_none hc' ((h₂.get_none_iff l).mpr e)]
    exact h₁ l

/-- **`[α]` is carried to the moved reading**: a re-made cell sits at the moved slot. -/
theorem RemakeR.outlivesD {ι : Slots L} (R : Relend ι) {ρ ρ' : WRes} (h : RemakeR R.θ ρ ρ')
    {α : L} (ho : OutlivesD ι ρ α) : OutlivesD ι ρ' (R.ψ α) := by
  intro l b e'
  obtain ⟨a, e, hab⟩ := h.get_some e'
  have ha := ho l a e
  cases hab with
  | own v => exact trivial
  | «mut» hk hk' hat =>
      cases a with
      | own v => exact absurd hk (fun e => Kind.noConfusion e)
      | imm i => exact absurd hk (fun e => Kind.noConfusion e)
      | «mut» m =>
          cases b with
          | own v => exact absurd hk' (fun e => Kind.noConfusion e)
          | imm i => exact absurd hk' (fun e => Kind.noConfusion e)
          | «mut» m' =>
              show R.ψ α < ι m'.β
              have hat' : m'.β = R.θ m.β := hat
              rw [hat', ← R.agree]
              exact R.mono ha

end Remake

/-! ### The invariant -/

/-- **Re-lendable at `A`**: at every re-lending, every configuration related at `A` has a re-make
related at the moved reading, with the records re-slotted. A `mut` cell storing `𝒱⟦A⟧` can be
re-made exactly when its payload is re-lendable. -/
def RelendV (ι : Slots L) (A : VTy) : Prop :=
  ∀ (R : Relend ι) (ls : List SRec) (δ : LSubD L) (v : Val) (ρ : WRes),
    vD (ℍ := ℍ) ι A ls δ v ρ →
      ∃ ρ', RemakeR R.θ ρ ρ' ∧
        vD (ℍ := ℍ) ι A (ls.map (Targets.srecRestrat R.θ)) (δ.map R.ψ) v ρ'

/-- The first-order types of the fragment: `1`, `⊗`, `Ref`, `[@a]` and `Mut`, nested to any depth. -/
def FOV : VTy → Prop
  | .unit => True
  | .tensor A B => FOV A ∧ FOV B
  | .ref A => FOV A
  | .box _ A => FOV A
  | .mut _ A => FOV A
  | _ => False

theorem fragV_of_fov : ∀ A, FOV A → FragV A
  | .unit, _ => trivial
  | .tensor A B, h => ⟨fragV_of_fov A h.1, fragV_of_fov B h.2⟩
  | .ref A, h => fragV_of_fov A h
  | .box _ A, h => fragV_of_fov A h
  | .mut _ A, h => fragV_of_fov A h
  | .zero, h | .sum _ _, h | .thunk _, h | .imm _ _, h | .bang _, h | .unk, h | .tvar _, h
  | .mu _, h | .int _, h | .fam _, h | .opq _, h => h.elim

/-! ### First-order types do not read the record list -/

/-- `ℓ ↦ M_α P̂` does not read the list when `P̂` does not. -/
theorem ptoMutD_ls (ι : Slots L) {l : Loc} {α : L} {P : List SRec → Val → WProp}
    (hP : ∀ ls₁ ls₂, P ls₁ = P ls₂) (ls ls' : List SRec) :
    ptoMutD ι l α ls P = ptoMutD ι l α ls' P := by
  funext ρ
  apply propext
  constructor
  · rintro ⟨b, u, σ, h, Q, hw, ls₀, hαb, hρ, hQ, -, hstr⟩
    exact ⟨b, u, σ, h, Q, hw, ls'.filter (fun r => decide (r.2 ⊐ b)), hαb, hρ,
      by rw [hQ, hP], fun x => by simp [List.mem_filter], hstr⟩
  · rintro ⟨b, u, σ, h, Q, hw, ls₀, hαb, hρ, hQ, -, hstr⟩
    exact ⟨b, u, σ, h, Q, hw, ls.filter (fun r => decide (r.2 ⊐ b)), hαb, hρ,
      by rw [hQ, hP], fun x => by simp [List.mem_filter], hstr⟩

/-- **The relation at a first-order type does not read the record list.** -/
theorem vD_ls (ι : Slots L) : ∀ A, FOV A → ∀ (ls ls' : List SRec) (δ : LSubD L),
    vD (ℍ := ℍ) ι A ls δ = vD (ℍ := ℍ) ι A ls' δ
  | .unit, _, _, _, _ => rfl
  | .tensor A B, h, ls, ls', δ => by
      funext v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vD (ℍ := ℍ) ι A ls δ v₁ ⋆ vD (ℍ := ℍ) ι B ls δ v₂) =
        (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vD (ℍ := ℍ) ι A ls' δ v₁ ⋆ vD (ℍ := ℍ) ι B ls' δ v₂)
      rw [vD_ls ι A h.1 ls ls' δ, vD_ls ι B h.2 ls ls' δ]
  | .ref A, h, ls, ls', δ => by
      funext v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vD (ℍ := ℍ) ι A ls δ v') =
        (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vD (ℍ := ℍ) ι A ls' δ v')
      rw [vD_ls ι A h ls ls' δ]
  | .box a A, h, ls, ls', δ => by
      funext v
      show atLifeD δ a (fun α => boxD ι α (vD (ℍ := ℍ) ι A ls δ v)) =
        atLifeD δ a (fun α => boxD ι α (vD (ℍ := ℍ) ι A ls' δ v))
      rw [vD_ls ι A h ls ls' δ]
  | .mut a A, h, ls, ls', δ => by
      funext v
      show atLifeD δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutD ι ℓ α ls (fun ls₀ => vD (ℍ := ℍ) ι A ls₀ δ)) =
        atLifeD δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutD ι ℓ α ls' (fun ls₀ => vD (ℍ := ℍ) ι A ls₀ δ))
      simp only [ptoMutD_ls ι (fun ls₁ ls₂ => vD_ls ι A h ls₁ ls₂ δ) ls ls']
  | .zero, h, _, _, _ | .sum _ _, h, _, _, _ | .thunk _, h, _, _, _ | .imm _ _, h, _, _, _
  | .bang _, h, _, _, _ | .unk, h, _, _, _ | .tvar _, h, _, _, _ | .mu _, h, _, _, _
  | .int _, h, _, _, _ | .fam _, h, _, _, _ | .opq _, h, _, _, _ => h.elim

/-! ### Where a first-order value's top-level `mut` cells may sit -/

/-- `lbV ι A δ s`: the slot `s` meets every bound some top-level `mut` cell of a value of `A` has
from below at the reading `δ`: its own `Mut 'a` (`@aδ ⊑ ι s`) and every `[@b]` around it
(`@bδ ⊏ ι s`). It compares lifetimes and nothing else. -/
def lbV (ι : Slots L) : VTy → LSubD L → Life → Prop
  | .unit, _, _ => False
  | .tensor A B, δ, s => lbV ι A δ s ∨ lbV ι B δ s
  | .ref A, δ, s => lbV ι A δ s
  | .box a A, δ, s => (∃ α, interpD δ a = some α ∧ α < ι s) ∧ lbV ι A δ s
  | .mut a _, δ, s => ∃ α, interpD δ a = some α ∧ α ≤ ι s
  | _, _, _ => False

/-- A cell of a composite with no `imm` cell on its left comes from one side. -/
theorem get_side {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : ∀ a, ρ₁.get l = some a → a.kind ≠ Kind.imm) {ψ : CellU Loc Val}
    (e : ρ.get l = some ψ) : ρ₁.get l = some ψ ∨ ρ₂.get l = some ψ := by
  rcases ResU.Comp.get hc l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, -, -⟩
  · rw [e] at f; exact absurd f (by simp)
  · rw [e] at f; obtain rfl := Option.some.inj f; exact Or.inl f₁
  · rw [e] at f; obtain rfl := Option.some.inj f; exact Or.inr f₂
  · exact absurd (CellU.CompatS.kinds (hc.1 l χ₁ χ₂ f₁ f₂)).1 (h₁ χ₁ f₁)

/-- **The top-level cells of a first-order value** are `own` cells and `mut` cells at slots `lbV`
admits. -/
theorem cells_of_vD (ι : Slots L) : ∀ A, FOV A → ∀ (ls : List SRec) (δ : LSubD L) (v : Val)
    (σ : WRes), vD (ℍ := ℍ) ι A ls δ v σ → ∀ l ψ, σ.get l = some ψ →
      ψ.kind = Kind.own ∨ (ψ.kind = Kind.mut ∧ lbV ι A δ ψ.at)
  | .unit, _, _, _, _, σ, h, l, ψ, e => by
      obtain ⟨rfl, -⟩ := h
      exact absurd e (by simp)
  | .tensor A B, hf, ls, δ, v, σ, h, l, ψ, e => by
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      have hne : ∀ a, ρ₁.get l = some a → a.kind ≠ Kind.imm := fun a ea => by
        rcases cells_of_vD ι A hf.1 ls δ v₁ ρ₁ h₁ l a ea with k | ⟨k, -⟩ <;> rw [k] <;>
          exact fun e => Kind.noConfusion e
      rcases get_side hc hne e with e₁ | e₂
      · rcases cells_of_vD ι A hf.1 ls δ v₁ ρ₁ h₁ l ψ e₁ with k | ⟨k, hl⟩
        · exact Or.inl k
        · exact Or.inr ⟨k, Or.inl hl⟩
      · rcases cells_of_vD ι B hf.2 ls δ v₂ ρ₂ h₂ l ψ e₂ with k | ⟨k, hl⟩
        · exact Or.inl k
        · exact Or.inr ⟨k, Or.inr hl⟩
  | .ref A, hf, ls, δ, v, σ, h, l, ψ, e => by
      obtain ⟨ℓ, w, hs⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, rfl, h₂⟩ := pure_sep_iff.mp hs
      have hne : ∀ a, (ResU.single ℓ (CellU.ownOf w)).get l = some a → a.kind ≠ Kind.imm :=
        fun a ea => by
          obtain ⟨-, rfl⟩ := ResU.single_get_eq_some ea
          exact fun e => Kind.noConfusion e
      rcases get_side hc hne e with e₁ | e₂
      · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e₁
        exact Or.inl rfl
      · exact cells_of_vD ι A hf ls δ w ρ₂ h₂ l ψ e₂
  | .box a A, hf, ls, δ, v, σ, h, l, ψ, e => by
      obtain ⟨α, hα, hb, ho⟩ := h
      rcases cells_of_vD ι A hf ls δ v σ hb l ψ e with k | ⟨k, hl⟩
      · exact Or.inl k
      · refine Or.inr ⟨k, ⟨α, hα, ?_⟩, hl⟩
        have hs := ho l ψ e
        cases ψ with
        | own w => exact absurd k (fun e => Kind.noConfusion e)
        | imm i => exact absurd k (fun e => Kind.noConfusion e)
        | «mut» m => exact hs
  | .mut a A, hf, ls, δ, v, σ, h, l, ψ, e => by
      obtain ⟨α, hα, ℓ, hsep⟩ := h
      obtain ⟨-, b, u, w, hw, Q, hQ, ls₀, hαb, rfl, -⟩ := pure_sep_iff.mp hsep
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      exact Or.inr ⟨CellU.kind_mutOf _ _ _ _ _ _, α, hα, hαb⟩
  | .zero, h, _, _, _, _, _, _, _, _ | .sum _ _, h, _, _, _, _, _, _, _, _
  | .thunk _, h, _, _, _, _, _, _, _, _ | .imm _ _, h, _, _, _, _, _, _, _, _
  | .bang _, h, _, _, _, _, _, _, _, _ | .unk, h, _, _, _, _, _, _, _, _
  | .tvar _, h, _, _, _, _, _, _, _, _ | .mu _, h, _, _, _, _, _, _, _, _
  | .int _, h, _, _, _, _, _, _, _, _ | .fam _, h, _, _, _, _, _, _, _, _
  | .opq _, h, _, _, _, _, _, _, _, _ => h.elim

theorem ne_imm_of_vD (ι : Slots L) {A : VTy} (hA : FOV A) {ls : List SRec} {δ : LSubD L}
    {v : Val} {σ : WRes} (h : vD (ℍ := ℍ) ι A ls δ v σ) (l : Loc) (a : CellU Loc Val)
    (e : σ.get l = some a) : a.kind ≠ Kind.imm := by
  rcases cells_of_vD ι A hA ls δ v σ h l a e with k | ⟨k, -⟩ <;> rw [k] <;>
    exact fun e => Kind.noConfusion e

/-- Composing a resource with the same locations as `ρ₁` in place of `ρ₁`. -/
theorem compS_swap {ρ₁ ρ₁' ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (hne : ∀ l a, ρ₁.get l = some a → a.kind ≠ Kind.imm)
    (hdom : ∀ l, ρ₁'.get l = none ↔ ρ₁.get l = none) :
    ∃ ρ', ResU.CompS ρ₁' ρ₂ ρ' ∧ (∀ l, ρ'.get l = none ↔ ρ.get l = none) ∧
      (∀ l, ρ₁.get l = none → ρ'.get l = ρ.get l) ∧ (∀ l, ρ₂.get l = none → ρ'.get l = ρ₁'.get l) := by
  have hd := disjoint_of_compS hc hne
  have hd' : ∀ l, ρ₁'.get l = none ∨ ρ₂.get l = none := fun l => by
    rcases hd l with e | e
    · exact Or.inl ((hdom l).mpr e)
    · exact Or.inr e
  obtain ⟨ρ', hc'⟩ := (ResU.compS_defined_iff ρ₁' ρ₂).mpr (ResU.Compat.of_disjoint hd')
  refine ⟨ρ', hc', fun l => ?_, fun l e => ?_, fun l e => ResU.Comp.get_of_right_none hc' e⟩
  · rcases hd l with e | e
    · rw [ResU.Comp.get_of_left_none hc' ((hdom l).mpr e), ResU.Comp.get_of_left_none hc e]
    · rw [ResU.Comp.get_of_right_none hc' e, ResU.Comp.get_of_right_none hc e]
      exact hdom l
  · rw [ResU.Comp.get_of_left_none hc' ((hdom l).mpr e), ResU.Comp.get_of_left_none hc e]

/-- **A top-level `mut` cell can be lowered to any slot `lbV` admits**: from a value of a
first-order type and a slot `s` that `lbV` admits, a value of the same type whose resource has the
same locations, whose every cell is kept or is a `mut` cell at `s`, and which has a `mut` cell at or
below `s`. -/
theorem lower_vD (ι : Slots L) : ∀ A, FOV A → ∀ (ls : List SRec) (δ : LSubD L) (v : Val)
    (σ : WRes) (s : Life), vD (ℍ := ℍ) ι A ls δ v σ → lbV ι A δ s →
      ∃ σ', vD (ℍ := ℍ) ι A ls δ v σ' ∧ (∀ l, σ'.get l = none ↔ σ.get l = none) ∧
        (∀ l ψ, σ'.get l = some ψ → σ.get l = some ψ ∨ (ψ.kind = Kind.mut ∧ ψ.at = s)) ∧
        ∃ l ψ, σ'.get l = some ψ ∧ ψ.kind = Kind.mut ∧ ψ.at ≤ s
  | .unit, _, _, _, _, _, _, _, hl => hl.elim
  | .tensor A B, hf, ls, δ, v, σ, s, h, hl => by
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨hv, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      have hne₁ := ne_imm_of_vD ι hf.1 h₁
      have hd := disjoint_of_compS hc hne₁
      rcases hl with hl | hl
      · obtain ⟨σ₁, g₁, hdom₁, hcell₁, l₀, ψ₀, e₀, k₀, a₀⟩ := lower_vD ι A hf.1 ls δ v₁ ρ₁ s h₁ hl
        obtain ⟨σ', hc', hdom', hleft, hright⟩ := compS_swap hc hne₁ hdom₁
        refine ⟨σ', ⟨v₁, v₂, pure_sep_mk hv ⟨σ₁, ρ₂, hc', g₁, h₂⟩⟩, hdom', fun l ψ e => ?_,
          l₀, ψ₀, ?_, k₀, a₀⟩
        · rcases hd l with f | f
          · rw [hleft l f] at e; exact Or.inl e
          · rw [hright l f] at e
            rcases hcell₁ l ψ e with e' | e'
            · rw [ResU.Comp.get_of_right_none hc f]; exact Or.inl e'
            · exact Or.inr e'
        · have f : ρ₂.get l₀ = none := by
            rcases hd l₀ with f | f
            · exact absurd ((hdom₁ l₀).mpr f) (by rw [e₀]; simp)
            · exact f
          rw [hright l₀ f]; exact e₀
      · have hne₂ := ne_imm_of_vD ι hf.2 h₂
        obtain ⟨σ₂, g₂, hdom₂, hcell₂, l₀, ψ₀, e₀, k₀, a₀⟩ := lower_vD ι B hf.2 ls δ v₂ ρ₂ s h₂ hl
        obtain ⟨σ', hc', hdom', hleft, hright⟩ := compS_swap (ResU.CompS.comm hc) hne₂ hdom₂
        have hd₂ := disjoint_of_compS (ResU.CompS.comm hc) hne₂
        refine ⟨σ', ⟨v₁, v₂, pure_sep_mk hv ⟨ρ₁, σ₂, ResU.CompS.comm hc', h₁, g₂⟩⟩, hdom',
          fun l ψ e => ?_, l₀, ψ₀, ?_, k₀, a₀⟩
        · rcases hd₂ l with f | f
          · rw [hleft l f] at e; exact Or.inl e
          · rw [hright l f] at e
            rcases hcell₂ l ψ e with e' | e'
            · rw [ResU.Comp.get_of_left_none hc f]; exact Or.inl e'
            · exact Or.inr e'
        · have f : ρ₁.get l₀ = none := by
            rcases hd₂ l₀ with f | f
            · exact absurd ((hdom₂ l₀).mpr f) (by rw [e₀]; simp)
            · exact f
          rw [hright l₀ f]; exact e₀
  | .ref A, hf, ls, δ, v, σ, s, h, hl => by
      obtain ⟨ℓ, w, hs⟩ := h
      obtain ⟨hv, ρ₁, ρ₂, hc, rfl, h₂⟩ := pure_sep_iff.mp hs
      have hne₂ := ne_imm_of_vD ι (A := A) hf h₂
      obtain ⟨σ₂, g₂, hdom₂, hcell₂, l₀, ψ₀, e₀, k₀, a₀⟩ := lower_vD ι A hf ls δ w ρ₂ s h₂ hl
      obtain ⟨σ', hc', hdom', hleft, hright⟩ := compS_swap (ResU.CompS.comm hc) hne₂ hdom₂
      have hd₂ := disjoint_of_compS (ResU.CompS.comm hc) hne₂
      refine ⟨σ', ⟨ℓ, w, pure_sep_mk hv ⟨_, σ₂, ResU.CompS.comm hc', rfl, g₂⟩⟩, hdom',
        fun l ψ e => ?_, l₀, ψ₀, ?_, k₀, a₀⟩
      · rcases hd₂ l with f | f
        · rw [hleft l f] at e; exact Or.inl e
        · rw [hright l f] at e
          rcases hcell₂ l ψ e with e' | e'
          · rw [ResU.Comp.get_of_left_none hc f]; exact Or.inl e'
          · exact Or.inr e'
      · have f : (ResU.single ℓ (CellU.ownOf w)).get l₀ = none := by
          rcases hd₂ l₀ with f | f
          · exact absurd ((hdom₂ l₀).mpr f) (by rw [e₀]; simp)
          · exact f
        rw [hright l₀ f]; exact e₀
  | .box a A, hf, ls, δ, v, σ, s, h, hl => by
      obtain ⟨α, hα, hb, ho⟩ := h
      obtain ⟨⟨α', hα', hlt⟩, hl⟩ := hl
      rw [hα] at hα'
      obtain rfl := Option.some.inj hα'
      obtain ⟨σ', g, hdom, hcell, hlow⟩ := lower_vD ι A hf ls δ v σ s hb hl
      refine ⟨σ', ⟨α, hα, g, fun l ψ e => ?_⟩, hdom, hcell, hlow⟩
      rcases hcell l ψ e with e' | ⟨k, hat⟩
      · exact ho l ψ e'
      · cases ψ with
        | own w => exact absurd k (fun e => Kind.noConfusion e)
        | imm i => exact absurd k (fun e => Kind.noConfusion e)
        | «mut» m =>
            show α < ι m.β
            have hat' : m.β = s := hat
            rw [hat']; exact hlt
  | .mut a A, hf, ls, δ, v, σ, s, h, hl => by
      obtain ⟨α, hα, ℓ, hsep⟩ := h
      obtain ⟨hv, b, u, w, hw, Q, hQw, ls₀, hαb, hσ, hQ, hmem, hstr⟩ := pure_sep_iff.mp hsep
      obtain ⟨α', hα', hle⟩ := hl
      rw [hα] at hα'
      obtain rfl := Option.some.inj hα'
      by_cases hbs : b ≤ s
      · refine ⟨σ, ⟨α, hα, ℓ, pure_sep_mk hv ⟨b, u, w, hw, Q, hQw, ls₀, hαb, hσ, hQ, hmem, hstr⟩⟩,
          fun l => Iff.rfl, fun l ψ e => Or.inl e, ℓ, _, by rw [hσ]; exact ResU.single_get_self _ _,
          CellU.kind_mutOf _ _ _ _ _ _, hbs⟩
      · have hsb : s < b := not_le.mp hbs
        have hw' : w.InStratum s := hw.mono hsb.le
        let Q' : Val → SPropS Loc Val s := fun x r => ofS Q x r.val
        have hQw' : Q' u ⟨w, hw'⟩ := ⟨hw, hQw⟩
        have hP : ∀ ls' u' σ', vD (ℍ := ℍ) ι A ls' δ u' σ' → σ'.InStratum s :=
          fun ls' u' σ' h => (hstr ls' u' σ' h).mono hsb.le
        refine ⟨ResU.single ℓ (CellU.mutOf s u w hw' Q' hQw'),
          ⟨α, hα, ℓ, pure_sep_mk hv ⟨s, u, w, hw', Q', hQw', ls.filter (fun r => decide (r.2 ⊐ s)),
            hle, rfl, ?_, fun x => by simp [List.mem_filter], hP⟩⟩, fun l => ?_,
          fun l ψ e => ?_, ℓ, _, ResU.single_get_self _ _, CellU.kind_mutOf _ _ _ _ _ _, le_rfl⟩
        · funext x r
          apply propext
          show ofS Q' x r ↔ vD (ℍ := ℍ) ι A (ls.filter (fun r => decide (r.2 ⊐ s))) δ x r
          rw [vD_ls ι A hf (ls.filter _) ls₀ δ]
          have hQx : ofS Q x r ↔ vD (ℍ := ℍ) ι A ls₀ δ x r := by rw [hQ]
          constructor
          · rintro ⟨_, h⟩; exact hQx.mp h
          · intro h
            exact ⟨hP _ _ _ h, hQx.mpr h⟩
        · rw [hσ]
          by_cases e : l = ℓ
          · subst e; simp
          · rw [ResU.single_get_ne _ e, ResU.single_get_ne _ e]
        · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
          exact Or.inr ⟨CellU.kind_mutOf _ _ _ _ _ _, rfl⟩
  | .zero, h, _, _, _, _, _, _, _ | .sum _ _, h, _, _, _, _, _, _, _
  | .thunk _, h, _, _, _, _, _, _, _ | .imm _ _, h, _, _, _, _, _, _, _
  | .bang _, h, _, _, _, _, _, _, _ | .unk, h, _, _, _, _, _, _, _
  | .tvar _, h, _, _, _, _, _, _, _ | .mu _, h, _, _, _, _, _, _, _
  | .int _, h, _, _, _, _, _, _, _ | .fam _, h, _, _, _, _, _, _, _
  | .opq _, h, _, _, _, _, _, _, _ => h.elim

/-- **`lbV` reads lifetimes only**: a slot at or below the moved position of `b` that `lbV` admits at
the moved reading makes `lbV` admit `b` at the original one. -/
theorem lbV_relend {ι : Slots L} (R : Relend ι) : ∀ (A : VTy) (δ : LSubD L) {t b : Life},
    lbV ι A (δ.map R.ψ) t → ι t ≤ R.ψ (ι b) → lbV ι A δ b
  | .tensor A B, δ, _, _, h, hle =>
      h.imp (fun h => lbV_relend R A δ h hle) (fun h => lbV_relend R B δ h hle)
  | .ref A, δ, _, _, h, hle => lbV_relend R A δ h hle
  | .box a A, δ, _, _, ⟨⟨α', hα', hlt⟩, h⟩, hle => by
      obtain ⟨α, hα, rfl⟩ := R.interp_some_inv hα'
      exact ⟨⟨α, hα, R.mono.lt_iff_lt.mp (lt_of_lt_of_le hlt hle)⟩, lbV_relend R A δ h hle⟩
  | .mut a A, δ, _, _, ⟨α', hα', hle'⟩, hle => by
      obtain ⟨α, hα, rfl⟩ := R.interp_some_inv hα'
      exact ⟨α, hα, R.mono.le_iff_le.mp (le_trans hle' hle)⟩
  | .unit, _, _, _, h, _ | .zero, _, _, _, h, _ | .sum _ _, _, _, _, h, _
  | .thunk _, _, _, _, h, _ | .imm _ _, _, _, _, h, _ | .bang _, _, _, _, h, _
  | .unk, _, _, _, h, _ | .tvar _, _, _, _, h, _ | .mu _, _, _, _, h, _
  | .int _, _, _, _, h, _ | .fam _, _, _, _, h, _ | .opq _, _, _, _, h, _ => h.elim

/-- **The `Mut` clause's stratification, carried to the moved reading**: if every value of the
payload `A` at `δ` lies in the stratum of `b`, and the payload has a value, then every value of `A`
at the moved reading lies in the stratum of `θ b`. -/
theorem strat_relend {ι : Slots L} (R : Relend ι) {A : VTy} (hA : FOV A) {δ : LSubD L} {b : Life}
    (hC : ∀ ls u σ, vD (ℍ := ℍ) ι A ls δ u σ → σ.InStratum b)
    (hI : ∃ ls u σ, vD (ℍ := ℍ) ι A ls δ u σ) :
    ∀ ls u σ', vD (ℍ := ℍ) ι A ls (δ.map R.ψ) u σ' → σ'.InStratum (R.θ b) := by
  intro ls u σ' h' l χ e
  rcases cells_of_vD ι A hA ls _ u σ' h' l χ e with hk | ⟨hk, hlb⟩
  · cases χ with
    | own w => exact trivial
    | imm i => exact absurd hk (fun e => Kind.noConfusion e)
    | «mut» m => exact absurd hk (fun e => Kind.noConfusion e)
  · rw [inStratum_iff_of_mut hk]
    by_contra hnot
    have hle : χ.at ≤ R.θ b := not_lt.mp hnot
    have hlb' : lbV ι A δ b :=
      lbV_relend R A δ hlb (by rw [R.agree]; exact ι.le_iff.mpr hle)
    obtain ⟨ls₁, u₁, σ₁, h₁⟩ := hI
    obtain ⟨σ₂, h₂, -, -, l₂, ψ₂, e₂, hk₂, hat₂⟩ := lower_vD ι A hA ls₁ δ u₁ σ₁ b h₁ hlb'
    have hin := hC ls₁ u₁ σ₂ h₂ l₂ ψ₂ e₂
    rw [inStratum_iff_of_mut hk₂] at hin
    exact absurd hat₂ (not_le.mpr hin)

/-! ### Re-making one lent cell, at any payload -/

/-- **Re-making a lent cell, at any payload type**: a configuration related at `Mut 'a A` has a
re-make related at the moved reading when its payload's values re-lend (`hwit`) and the payload's
stratification is carried to the moved reading (`hstrat`). These are the two obligations a stored
predicate `𝒱⟦A⟧` meets for its cell to be re-made, at every depth and every payload; at first-order
payloads `relend_fov` discharges both. -/
theorem relend_mut {ι : Slots L} (R : Relend ι) {a : Lifetime.Life} {A : VTy}
    {ls : List SRec} {δ : LSubD L} {v : Val} {ρ : WRes}
    (hwit : ∀ ls₀ u σ, vD (ℍ := ℍ) ι A ls₀ δ u σ → ∀ ls₁ : List SRec,
      ∃ σ', RemakeR R.θ σ σ' ∧ vD (ℍ := ℍ) ι A ls₁ (δ.map R.ψ) u σ')
    (hstrat : ∀ b : Life, (∀ ls u σ, vD (ℍ := ℍ) ι A ls δ u σ → σ.InStratum b) →
      (∃ ls u σ, vD (ℍ := ℍ) ι A ls δ u σ) →
      ∀ ls u σ', vD (ℍ := ℍ) ι A ls (δ.map R.ψ) u σ' → σ'.InStratum (R.θ b))
    (h : vD (ℍ := ℍ) ι (.mut a A) ls δ v ρ) (ls' : List SRec) :
    ∃ ρ', RemakeR R.θ ρ ρ' ∧ vD (ℍ := ℍ) ι (.mut a A) ls' (δ.map R.ψ) v ρ' := by
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨hv, b, u, σ, hσ, Q, hw, ls₀, hαb, rfl, hQ, -, hstr⟩ := pure_sep_iff.mp hsep
  have hP : vD (ℍ := ℍ) ι A ls₀ δ u σ := by
    have h0 : ofS Q u σ := ⟨hσ, hw⟩
    rwa [hQ] at h0
  obtain ⟨σ', hRσ, hσ'⟩ := hwit ls₀ u σ hP (ls'.filter (fun r => decide (r.2 ⊐ R.θ b)))
  have hσs : σ'.InStratum (R.θ b) := hRσ.inStratum hσ
  have hstr' := hstrat b hstr ⟨ls₀, u, σ, hP⟩
  let Q' : Val → SPropS Loc Val (R.θ b) := fun x r =>
    vD (ℍ := ℍ) ι A (ls'.filter (fun r => decide (r.2 ⊐ R.θ b))) (δ.map R.ψ) x r.val
  have hw' : Q' u ⟨σ', hσs⟩ := hσ'
  refine ⟨ResU.single ℓ (CellU.mutOf (R.θ b) u σ' hσs Q' hw'), remakeR_single ?_, R.ψ α,
    R.interp_some hα, ℓ, pure_sep_mk hv ⟨R.θ b, u, σ', hσs, Q', hw',
      ls'.filter (fun r => decide (r.2 ⊐ R.θ b)), ?_, rfl, ?_,
      fun x => by simp [List.mem_filter], hstr'⟩⟩
  · refine RemakeC.mut (CellU.kind_mutOf _ _ _ _ _ _) (CellU.kind_mutOf _ _ _ _ _ _) rfl rfl ?_
    rw [CellU.wit_mutOf, CellU.wit_mutOf]
    exact hRσ
  · rw [← R.agree]; exact R.mono.monotone hαb
  · funext x r
    exact propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨hstr' _ _ _ h, h⟩⟩

/-! ### Re-lending at the first-order types -/

/-- **Re-lending preserves the relation at every first-order type, at any depth**: one induction
over the clauses `1`, `⊗`, `Ref`, `[@a]`, `Mut`. A configuration related at `A` has a re-make —
each `mut` cell re-made at its moved slot, storing `𝒱⟦−⟧` at the moved reading — related at the
moved reading, at every target list. -/
theorem relend_fov {ι : Slots L} (R : Relend ι) : ∀ A, FOV A → ∀ (ls : List SRec) (δ : LSubD L)
    (v : Val) (ρ : WRes), vD (ℍ := ℍ) ι A ls δ v ρ → ∀ ls' : List SRec,
      ∃ ρ', RemakeR R.θ ρ ρ' ∧ vD (ℍ := ℍ) ι A ls' (δ.map R.ψ) v ρ'
  | .unit, _, _, _, _, _, h, _ => by
      obtain ⟨rfl, hv⟩ := h
      exact ⟨PMap.empty, remakeR_empty, rfl, hv⟩
  | .tensor A B, hf, ls, δ, v, ρ, h, ls' => by
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨hv, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      obtain ⟨ρ₁', hR₁, h₁'⟩ := relend_fov R A hf.1 ls δ v₁ ρ₁ h₁ ls'
      obtain ⟨ρ₂', hR₂, h₂'⟩ := relend_fov R B hf.2 ls δ v₂ ρ₂ h₂ ls'
      obtain ⟨ρ', hc', hR⟩ := remakeR_compS hc hR₁ hR₂
      exact ⟨ρ', hR, v₁, v₂, pure_sep_mk hv ⟨ρ₁', ρ₂', hc', h₁', h₂'⟩⟩
  | .ref A, hf, ls, δ, v, ρ, h, ls' => by
      obtain ⟨ℓ, w, hs⟩ := h
      obtain ⟨hv, ρ₁, ρ₂, hc, rfl, h₂⟩ := pure_sep_iff.mp hs
      obtain ⟨ρ₂', hR₂, h₂'⟩ := relend_fov R A hf ls δ w ρ₂ h₂ ls'
      obtain ⟨ρ', hc', hR⟩ := remakeR_compS hc (remakeR_single (RemakeC.own w)) hR₂
      exact ⟨ρ', hR, ℓ, w, pure_sep_mk hv ⟨_, ρ₂', hc', rfl, h₂'⟩⟩
  | .box a A, hf, ls, δ, v, ρ, h, ls' => by
      obtain ⟨α, hα, hb, ho⟩ := h
      obtain ⟨ρ', hR, hb'⟩ := relend_fov R A hf ls δ v ρ hb ls'
      exact ⟨ρ', hR, R.ψ α, R.interp_some hα, hb', hR.outlivesD R ho⟩
  | .mut a A, hf, ls, δ, v, ρ, h, ls' =>
      relend_mut R (fun ls₀ u σ hP ls₁ => relend_fov R A hf ls₀ δ u σ hP ls₁)
        (fun _ hC hI => strat_relend R (A := A) hf hC hI) h ls'
  | .zero, h, _, _, _, _, _, _ | .sum _ _, h, _, _, _, _, _, _
  | .thunk _, h, _, _, _, _, _, _ | .imm _ _, h, _, _, _, _, _, _
  | .bang _, h, _, _, _, _, _, _ | .unk, h, _, _, _, _, _, _
  | .tvar _, h, _, _, _, _, _, _ | .mu _, h, _, _, _, _, _, _
  | .int _, h, _, _, _, _, _, _ | .fam _, h, _, _, _, _, _, _
  | .opq _, h, _, _, _, _, _, _ => h.elim

/-- **The invariant holds at every first-order type.** -/
theorem relendV_of_fov (ι : Slots L) {A : VTy} (hA : FOV A) : RelendV (ℍ := ℍ) ι A :=
  fun R ls δ v ρ h => relend_fov R A hA ls δ v ρ h _

end DenseCarrier

end
