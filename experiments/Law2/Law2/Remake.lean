import Core.Fundamental
import Restrat.Injection

/-!
# Law2 — re-making a region's cells, at Core's relation

Law 2 ends a suspended region's lends at the stop and makes them afresh at resume, at lifetimes
beneath the resumer's list. A re-making of the region below the cut `c` is a re-stratification
`θ : Restrat.Emb c` of the lifetimes (strictly monotone, the identity at and above `c`) together
with the reading moved by it (`Restrat.LSub.mapN θ.toNat δ`).

The region's cells are **re-made**, not moved: a re-made cell has the kind, value and location of
the old one, its lifetime moved by `θ`, its witness re-made cell by cell, and a `mut` cell stores
whatever predicate it is folded with (`RemakeC`, `RemakeR`). Cells at and above the cut are
re-made at their own lifetime, so outside the region a re-make is free only in the predicates it
stores.

* `relend_fov`: **Core's relation re-lends at every first-order type at any depth** — `1`, `⊗`,
  `Ref`, `[@a]`, `Mut`, nested — by one induction over the clauses: a configuration related at
  `A` has a re-make related at the moved reading, each `mut` cell storing `𝒱⟦−⟧` at the moved
  reading. The `Mut` clause's stratification is carried by `strat_relend`, which reads where a
  payload's top-level cells may sit (`lbV`) by lifetime comparisons only.
* `relend_gSepC`, `relend_derivable`: a first-order captured context re-lends slot by slot, and
  every term Core's typing derives over it re-lends at every computation type (`fundamentalC` at
  the moved reading, which `⟦Δ⟧` admits).

These are DenseCarrier's `relend_fov` and `core_relend_derivable` (`DenseCarrier/Relend.lean`,
`RelendFL.lean`) read at `L = Life` directly on `vC`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx LSub)

/-! ### Re-made cells and resources -/

mutual
/-- `ψ'` is `ψ` **re-made** at `θ`: an `own` cell is kept; a `mut` cell keeps its kind and value,
its lifetime is moved by `θ`, and its witness is re-made cell by cell. The stored predicate of the
re-made cell is not constrained. -/
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

theorem RemakeC.wit {a b : CellU Loc Val} (h : RemakeC θ a b) :
    ∀ l, RemakeO θ (a.wit.get l) (b.wit.get l) := by
  cases h with
  | own v => intro l; exact RemakeO.none
  | «mut» hk hk' hat hv hw => exact hw

theorem RemakeC.at {a b : CellU Loc Val} (h : RemakeC θ a b) : b.at = θ a.at := by
  cases h with
  | own v => exact (θ.map_top).symm
  | «mut» hk hk' hat => exact hat

/-- A `mut` cell lies in the stratum of `α` exactly when its lifetime is above `α`. -/
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

theorem RemakeR.ne_imm' {ρ ρ' : WRes} (h : RemakeR θ ρ ρ') {l : Loc} {b : CellU Loc Val}
    (e : ρ'.get l = some b) : b.kind ≠ Kind.imm := by
  obtain ⟨a, -, hab⟩ := h.get_some e
  rw [hab.kind]; exact hab.kind_ne_imm

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

/-- **`[α]` is carried to the moved lifetime**: a re-made cell sits at the moved lifetime. -/
theorem RemakeR.outlives {ρ ρ' : WRes} (h : RemakeR θ ρ ρ') {α : Life} (ho : Outlives ρ α) :
    Outlives ρ' (θ α) :=
  h.inStratum ho

end Remake

/-! ### The first-order types -/

/-- The first-order types: `1`, `⊗`, `Ref`, `[@a]` and `Mut`, nested to any depth. -/
def FOV : VTy → Prop
  | .unit => True
  | .tensor A B => FOV A ∧ FOV B
  | .ref A => FOV A
  | .box _ A => FOV A
  | .mut _ A => FOV A
  | _ => False

/-- `ℓ ↦ M_α P̂` does not read the list when `P̂` does not. -/
theorem ptoMutS_ls {l : Loc} {α : Life} {P : List SRec → Val → WProp}
    (hP : ∀ ls₁ ls₂, P ls₁ = P ls₂) (ls ls' : List SRec) :
    ptoMutS l α ls P = ptoMutS l α ls' P := by
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
theorem vC_ls : ∀ A, FOV A → ∀ (ls ls' : List SRec) (δ : LSub),
    vCE (ℍ := ℍ) none true A ls δ = vCE (ℍ := ℍ) none true A ls' δ
  | .unit, _, _, _, _ => rfl
  | .tensor A B, h, ls, ls', δ => by
      funext v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vCE (ℍ := ℍ) none true A ls δ v₁ ⋆ vCE (ℍ := ℍ) none true B ls δ v₂) =
        (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vCE (ℍ := ℍ) none true A ls' δ v₁ ⋆ vCE (ℍ := ℍ) none true B ls' δ v₂)
      rw [vC_ls A h.1 ls ls' δ, vC_ls B h.2 ls ls' δ]
  | .ref A, h, ls, ls', δ => by
      funext v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vCE (ℍ := ℍ) none true A ls δ v') =
        (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vCE (ℍ := ℍ) none true A ls' δ v')
      rw [vC_ls A h ls ls' δ]
  | .box a A, h, ls, ls', δ => by
      funext v
      show atLife δ a (fun α => box α (vCE (ℍ := ℍ) none true A ls δ v)) =
        atLife δ a (fun α => box α (vCE (ℍ := ℍ) none true A ls' δ v))
      rw [vC_ls A h ls ls' δ]
  | .mut a A, h, ls, ls', δ => by
      funext v
      show atLife δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutS ℓ α ls (fun ls₀ => vCE (ℍ := ℍ) none true A ls₀ δ)) =
        atLife δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutS ℓ α ls' (fun ls₀ => vCE (ℍ := ℍ) none true A ls₀ δ))
      simp only [ptoMutS_ls (fun ls₁ ls₂ => vC_ls A h ls₁ ls₂ δ) ls ls']
  | .zero, h, _, _, _ | .sum _ _, h, _, _, _ | .thunk _, h, _, _, _ | .imm _ _, h, _, _, _
  | .bang _, h, _, _, _ | .unk, h, _, _, _ | .tvar _, h, _, _, _ | .mu _, h, _, _, _
  | .int _, h, _, _, _ | .fam _, h, _, _, _ | .opq _, h, _, _, _ => h.elim

/-! ### Where a first-order value's top-level `mut` cells may sit -/

/-- `lbV A δ s`: the lifetime `s` meets every bound some top-level `mut` cell of a value of `A` has
from below at the reading `δ`: its own `Mut 'a` (`@aδ ⊑ s`) and every `[@b]` around it
(`@bδ ⊏ s`). It compares lifetimes and nothing else. -/
def lbV : VTy → LSub → Life → Prop
  | .tensor A B, δ, s => lbV A δ s ∨ lbV B δ s
  | .ref A, δ, s => lbV A δ s
  | .box a A, δ, s => (∃ α : Life, a.interp δ = some α ∧ α < s) ∧ lbV A δ s
  | .mut a _, δ, s => ∃ α : Life, a.interp δ = some α ∧ α ≤ s
  | _, _, _ => False

/-- A cell of a composite with no `imm` cell on its left comes from one side. -/
theorem get_side {ρ₁ ρ₂ ρ : WRes} {l : Loc} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : ∀ a, ρ₁.get l = some a → a.kind ≠ Kind.imm) {ψ : CellU Loc Val}
    (e : ρ.get l = some ψ) : ρ₁.get l = some ψ ∨ ρ₂.get l = some ψ := by
  rcases ResU.Comp.get hc l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, -, -⟩
  · rw [e] at f; exact absurd f (by simp)
  · rw [e] at f; obtain rfl := Option.some.inj f; exact Or.inl f₁
  · rw [e] at f; obtain rfl := Option.some.inj f; exact Or.inr f₂
  · exact absurd (CellU.CompatS.kinds (hc.1 l χ₁ χ₂ f₁ f₂)).1 (h₁ χ₁ f₁)

/-- **The top-level cells of a first-order value** are `own` cells and `mut` cells at lifetimes
`lbV` admits. -/
theorem cells_of_vC : ∀ A, FOV A → ∀ (ls : List SRec) (δ : LSub) (v : Val)
    (σ : WRes), vCE (ℍ := ℍ) none true A ls δ v σ → ∀ l ψ, σ.get l = some ψ →
      ψ.kind = Kind.own ∨ (ψ.kind = Kind.mut ∧ lbV A δ ψ.at)
  | .unit, _, _, _, _, σ, h, l, ψ, e => by
      obtain ⟨rfl, -⟩ := h
      exact absurd e (by simp)
  | .tensor A B, hf, ls, δ, v, σ, h, l, ψ, e => by
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      have hne : ∀ a, ρ₁.get l = some a → a.kind ≠ Kind.imm := fun a ea => by
        rcases cells_of_vC A hf.1 ls δ v₁ ρ₁ h₁ l a ea with k | ⟨k, -⟩ <;> rw [k] <;>
          exact fun e => Kind.noConfusion e
      rcases get_side hc hne e with e₁ | e₂
      · rcases cells_of_vC A hf.1 ls δ v₁ ρ₁ h₁ l ψ e₁ with k | ⟨k, hl⟩
        · exact Or.inl k
        · exact Or.inr ⟨k, Or.inl hl⟩
      · rcases cells_of_vC B hf.2 ls δ v₂ ρ₂ h₂ l ψ e₂ with k | ⟨k, hl⟩
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
      · exact cells_of_vC A hf ls δ w ρ₂ h₂ l ψ e₂
  | .box a A, hf, ls, δ, v, σ, h, l, ψ, e => by
      obtain ⟨α, hα, hb, ho⟩ := h
      rcases cells_of_vC A hf ls δ v σ hb l ψ e with k | ⟨k, hl⟩
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

theorem ne_imm_of_vC {A : VTy} (hA : FOV A) {ls : List SRec} {δ : LSub}
    {v : Val} {σ : WRes} (h : vCE (ℍ := ℍ) none true A ls δ v σ) (l : Loc) (a : CellU Loc Val)
    (e : σ.get l = some a) : a.kind ≠ Kind.imm := by
  rcases cells_of_vC A hA ls δ v σ h l a e with k | ⟨k, -⟩ <;> rw [k] <;>
    exact fun e => Kind.noConfusion e

/-- Composing a resource with the same locations as `ρ₁` in place of `ρ₁`. -/
theorem compS_swap {ρ₁ ρ₁' ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (hne : ∀ l a, ρ₁.get l = some a → a.kind ≠ Kind.imm)
    (hdom : ∀ l, ρ₁'.get l = none ↔ ρ₁.get l = none) :
    ∃ ρ', ResU.CompS ρ₁' ρ₂ ρ' ∧ (∀ l, ρ'.get l = none ↔ ρ.get l = none) ∧
      (∀ l, ρ₁.get l = none → ρ'.get l = ρ.get l) ∧
      (∀ l, ρ₂.get l = none → ρ'.get l = ρ₁'.get l) := by
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

/-- **A top-level `mut` cell can be lowered to any lifetime `lbV` admits**: from a value of a
first-order type and a lifetime `s` that `lbV` admits, a value of the same type whose resource has
the same locations, whose every cell is kept or is a `mut` cell at `s`, and which has a `mut` cell
at or below `s`. -/
theorem lower_vC : ∀ A, FOV A → ∀ (ls : List SRec) (δ : LSub) (v : Val)
    (σ : WRes) (s : Life), vCE (ℍ := ℍ) none true A ls δ v σ → lbV A δ s →
      ∃ σ', vCE (ℍ := ℍ) none true A ls δ v σ' ∧ (∀ l, σ'.get l = none ↔ σ.get l = none) ∧
        (∀ l ψ, σ'.get l = some ψ → σ.get l = some ψ ∨ (ψ.kind = Kind.mut ∧ ψ.at = s)) ∧
        ∃ l ψ, σ'.get l = some ψ ∧ ψ.kind = Kind.mut ∧ ψ.at ≤ s
  | .unit, _, _, _, _, _, _, _, hl => hl.elim
  | .tensor A B, hf, ls, δ, v, σ, s, h, hl => by
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨hv, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      have hne₁ := ne_imm_of_vC hf.1 h₁
      have hd := disjoint_of_compS hc hne₁
      rcases hl with hl | hl
      · obtain ⟨σ₁, g₁, hdom₁, hcell₁, l₀, ψ₀, e₀, k₀, a₀⟩ := lower_vC A hf.1 ls δ v₁ ρ₁ s h₁ hl
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
      · have hne₂ := ne_imm_of_vC hf.2 h₂
        obtain ⟨σ₂, g₂, hdom₂, hcell₂, l₀, ψ₀, e₀, k₀, a₀⟩ := lower_vC B hf.2 ls δ v₂ ρ₂ s h₂ hl
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
      have hne₂ := ne_imm_of_vC (A := A) hf h₂
      obtain ⟨σ₂, g₂, hdom₂, hcell₂, l₀, ψ₀, e₀, k₀, a₀⟩ := lower_vC A hf ls δ w ρ₂ s h₂ hl
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
      obtain ⟨σ', g, hdom, hcell, hlow⟩ := lower_vC A hf ls δ v σ s hb hl
      refine ⟨σ', ⟨α, hα, g, fun l ψ e => ?_⟩, hdom, hcell, hlow⟩
      rcases hcell l ψ e with e' | ⟨k, hat⟩
      · exact ho l ψ e'
      · cases ψ with
        | own w => exact absurd k (fun e => Kind.noConfusion e)
        | imm i => exact absurd k (fun e => Kind.noConfusion e)
        | «mut» m =>
            exact (inStratum_iff_of_mut (ψ := CellU.mut m) rfl α).mpr (by rw [hat]; exact hlt)
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
        have hP : ∀ ls' u' σ', vCE (ℍ := ℍ) none true A ls' δ u' σ' → σ'.InStratum s :=
          fun ls' u' σ' h => (hstr ls' u' σ' h).mono hsb.le
        refine ⟨ResU.single ℓ (CellU.mutOf s u w hw' Q' hQw'),
          ⟨α, hα, ℓ, pure_sep_mk hv ⟨s, u, w, hw', Q', hQw', ls.filter (fun r => decide (r.2 ⊐ s)),
            hle, rfl, ?_, fun x => by simp [List.mem_filter], hP⟩⟩, fun l => ?_,
          fun l ψ e => ?_, ℓ, _, ResU.single_get_self _ _, CellU.kind_mutOf _ _ _ _ _ _, le_rfl⟩
        · funext x r
          apply propext
          show ofS Q' x r ↔ vCE (ℍ := ℍ) none true A (ls.filter (fun r => decide (r.2 ⊐ s))) δ x r
          rw [vC_ls A hf (ls.filter _) ls₀ δ]
          have hQx : ofS Q x r ↔ vCE (ℍ := ℍ) none true A ls₀ δ x r := by rw [hQ]
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

/-! ### Re-lending at the first-order types -/

section Relend
variable {c : Life} (θ : Restrat.Emb c)

/-- The moved reading `θ ∘ δ`. -/
abbrev mv (δ : LSub) : LSub := Restrat.LSub.mapN θ.toNat δ

theorem interp_mv_some {δ : LSub} {a : Lifetime.Life} {α : Life} (h : a.interp δ = some α) :
    a.interp (mv θ δ) = some (θ α) := by
  rw [θ.interp_mapN, h]; rfl

theorem interp_mv_inv {δ : LSub} {a : Lifetime.Life} {α' : Life}
    (h : a.interp (mv θ δ) = some α') : ∃ α : Life, a.interp δ = some α ∧ θ α = α' := by
  obtain ⟨m, hm, e⟩ := θ.interp_mapN_some.mp h
  exact ⟨m, hm, e⟩

/-- **`lbV` reads lifetimes only**: a lifetime at or below `θ b` that `lbV` admits at the moved
reading makes `lbV` admit `b` at the original one. -/
theorem lbV_relend : ∀ (A : VTy) (δ : LSub) {t b : Life},
    lbV A (mv θ δ) t → t ≤ θ b → lbV A δ b
  | .tensor A B, δ, _, _, h, hle =>
      h.imp (fun h => lbV_relend A δ h hle) (fun h => lbV_relend B δ h hle)
  | .ref A, δ, _, _, h, hle => lbV_relend A δ h hle
  | .box a A, δ, _, _, ⟨⟨α', hα', hlt⟩, h⟩, hle => by
      obtain ⟨α, hα, rfl⟩ := interp_mv_inv θ hα'
      exact ⟨⟨α, hα, θ.lt_iff.mp (lt_of_lt_of_le hlt hle)⟩, lbV_relend A δ h hle⟩
  | .mut a A, δ, _, _, ⟨α', hα', hle'⟩, hle => by
      obtain ⟨α, hα, rfl⟩ := interp_mv_inv θ hα'
      exact ⟨α, hα, θ.le_iff.mp (le_trans hle' hle)⟩
  | .unit, _, _, _, h, _ | .zero, _, _, _, h, _ | .sum _ _, _, _, _, h, _
  | .thunk _, _, _, _, h, _ | .imm _ _, _, _, _, h, _ | .bang _, _, _, _, h, _
  | .unk, _, _, _, h, _ | .tvar _, _, _, _, h, _ | .mu _, _, _, _, h, _
  | .int _, _, _, _, h, _ | .fam _, _, _, _, h, _ | .opq _, _, _, _, h, _ => h.elim

/-- **The `Mut` clause's stratification, carried to the moved reading**: if every value of the
payload `A` at `δ` lies in the stratum of `b`, and the payload has a value, then every value of `A`
at the moved reading lies in the stratum of `θ b`. -/
theorem strat_relend {A : VTy} (hA : FOV A) {δ : LSub} {b : Life}
    (hC : ∀ ls u σ, vCE (ℍ := ℍ) none true A ls δ u σ → σ.InStratum b)
    (hI : ∃ ls u σ, vCE (ℍ := ℍ) none true A ls δ u σ) :
    ∀ ls u σ', vCE (ℍ := ℍ) none true A ls (mv θ δ) u σ' → σ'.InStratum (θ b) := by
  intro ls u σ' h' l χ e
  rcases cells_of_vC A hA ls _ u σ' h' l χ e with hk | ⟨hk, hlb⟩
  · cases χ with
    | own w => exact trivial
    | imm i => exact absurd hk (fun e => Kind.noConfusion e)
    | «mut» m => exact absurd hk (fun e => Kind.noConfusion e)
  · rw [inStratum_iff_of_mut hk]
    by_contra hnot
    have hle : χ.at ≤ θ b := not_lt.mp hnot
    have hlb' : lbV A δ b := lbV_relend θ A δ hlb hle
    obtain ⟨ls₁, u₁, σ₁, h₁⟩ := hI
    obtain ⟨σ₂, h₂, -, -, l₂, ψ₂, e₂, hk₂, hat₂⟩ := lower_vC A hA ls₁ δ u₁ σ₁ b h₁ hlb'
    have hin := hC ls₁ u₁ σ₂ h₂ l₂ ψ₂ e₂
    rw [inStratum_iff_of_mut hk₂] at hin
    exact absurd hat₂ (not_le.mpr hin)

/-- **Re-making a lent cell, at any payload type**: a configuration related at `Mut 'a A` has a
re-make related at the moved reading when its payload's values re-lend (`hwit`) and the payload's
stratification is carried to the moved reading (`hstrat`). -/
theorem relend_mut {a : Lifetime.Life} {A : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (hwit : ∀ ls₀ u σ, vCE (ℍ := ℍ) none true A ls₀ δ u σ → ∀ ls₁ : List SRec,
      ∃ σ', RemakeR θ σ σ' ∧ vCE (ℍ := ℍ) none true A ls₁ (mv θ δ) u σ')
    (hstrat : ∀ b : Life, (∀ ls u σ, vCE (ℍ := ℍ) none true A ls δ u σ → σ.InStratum b) →
      (∃ ls u σ, vCE (ℍ := ℍ) none true A ls δ u σ) →
      ∀ ls u σ', vCE (ℍ := ℍ) none true A ls (mv θ δ) u σ' → σ'.InStratum (θ b))
    (h : vCE (ℍ := ℍ) none true (.mut a A) ls δ v ρ) (ls' : List SRec) :
    ∃ ρ', RemakeR θ ρ ρ' ∧ vCE (ℍ := ℍ) none true (.mut a A) ls' (mv θ δ) v ρ' := by
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨hv, b, u, σ, hσ, Q, hw, ls₀, hαb, rfl, hQ, -, hstr⟩ := pure_sep_iff.mp hsep
  have hP : vCE (ℍ := ℍ) none true A ls₀ δ u σ := by
    have h0 : ofS Q u σ := ⟨hσ, hw⟩
    rwa [hQ] at h0
  obtain ⟨σ', hRσ, hσ'⟩ := hwit ls₀ u σ hP (ls'.filter (fun r => decide (r.2 ⊐ θ b)))
  have hσs : σ'.InStratum (θ b) := hRσ.inStratum hσ
  have hstr' := hstrat b hstr ⟨ls₀, u, σ, hP⟩
  let Q' : Val → SPropS Loc Val (θ b) := fun x r =>
    vCE (ℍ := ℍ) none true A (ls'.filter (fun r => decide (r.2 ⊐ θ b))) (mv θ δ) x r.val
  have hw' : Q' u ⟨σ', hσs⟩ := hσ'
  refine ⟨ResU.single ℓ (CellU.mutOf (θ b) u σ' hσs Q' hw'), remakeR_single ?_, θ α,
    interp_mv_some θ hα, ℓ, pure_sep_mk hv ⟨θ b, u, σ', hσs, Q', hw',
      ls'.filter (fun r => decide (r.2 ⊐ θ b)), θ.monotone hαb, rfl, ?_,
      fun x => by simp [List.mem_filter], hstr'⟩⟩
  · refine RemakeC.mut (CellU.kind_mutOf _ _ _ _ _ _) (CellU.kind_mutOf _ _ _ _ _ _) rfl rfl ?_
    rw [CellU.wit_mutOf, CellU.wit_mutOf]
    exact hRσ
  · funext x r
    exact propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨hstr' _ _ _ h, h⟩⟩

/-- **Re-lending preserves Core's relation at every first-order type, at any depth**: one
induction over the clauses `1`, `⊗`, `Ref`, `[@a]`, `Mut`. A configuration related at `A` has a
re-make — each `mut` cell re-made at its moved lifetime, storing `𝒱⟦−⟧` at the moved reading —
related at the moved reading, at every target list. -/
theorem relend_fov : ∀ A, FOV A → ∀ (ls : List SRec) (δ : LSub)
    (v : Val) (ρ : WRes), vCE (ℍ := ℍ) none true A ls δ v ρ → ∀ ls' : List SRec,
      ∃ ρ', RemakeR θ ρ ρ' ∧ vCE (ℍ := ℍ) none true A ls' (mv θ δ) v ρ'
  | .unit, _, _, _, _, _, h, _ => by
      obtain ⟨rfl, hv⟩ := h
      exact ⟨PMap.empty, remakeR_empty, rfl, hv⟩
  | .tensor A B, hf, ls, δ, v, ρ, h, ls' => by
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨hv, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      obtain ⟨ρ₁', hR₁, h₁'⟩ := relend_fov A hf.1 ls δ v₁ ρ₁ h₁ ls'
      obtain ⟨ρ₂', hR₂, h₂'⟩ := relend_fov B hf.2 ls δ v₂ ρ₂ h₂ ls'
      obtain ⟨ρ', hc', hR⟩ := remakeR_compS hc hR₁ hR₂
      exact ⟨ρ', hR, v₁, v₂, pure_sep_mk hv ⟨ρ₁', ρ₂', hc', h₁', h₂'⟩⟩
  | .ref A, hf, ls, δ, v, ρ, h, ls' => by
      obtain ⟨ℓ, w, hs⟩ := h
      obtain ⟨hv, ρ₁, ρ₂, hc, rfl, h₂⟩ := pure_sep_iff.mp hs
      obtain ⟨ρ₂', hR₂, h₂'⟩ := relend_fov A hf ls δ w ρ₂ h₂ ls'
      obtain ⟨ρ', hc', hR⟩ := remakeR_compS hc (remakeR_single (RemakeC.own w)) hR₂
      exact ⟨ρ', hR, ℓ, w, pure_sep_mk hv ⟨_, ρ₂', hc', rfl, h₂'⟩⟩
  | .box a A, hf, ls, δ, v, ρ, h, ls' => by
      obtain ⟨α, hα, hb, ho⟩ := h
      obtain ⟨ρ', hR, hb'⟩ := relend_fov A hf ls δ v ρ hb ls'
      exact ⟨ρ', hR, θ α, interp_mv_some θ hα, hb', hR.outlives ho⟩
  | .mut a A, hf, ls, δ, v, ρ, h, ls' =>
      relend_mut θ (fun ls₀ u σ hP ls₁ => relend_fov A hf ls₀ δ u σ hP ls₁)
        (fun _ hC hI => strat_relend θ (A := A) hf hC hI) h ls'
  | .zero, h, _, _, _, _, _, _ | .sum _ _, h, _, _, _, _, _, _
  | .thunk _, h, _, _, _, _, _, _ | .imm _ _, h, _, _, _, _, _, _
  | .bang _, h, _, _, _, _, _, _ | .unk, h, _, _, _, _, _, _
  | .tvar _, h, _, _, _, _, _, _ | .mu _, h, _, _, _, _, _, _
  | .int _, h, _, _, _, _, _, _ | .fam _, h, _, _, _, _, _, _
  | .opq _, h, _, _, _, _, _, _ => h.elim

/-! ### Captured contexts and the terms Core's typing derives -/

/-- Every live slot of the context is at a first-order type. -/
def FOCtx (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → FOV s.ty

theorem emp_eq {ρ : WRes} (h : (emp : WProp) ρ) : ρ = PMap.empty := h.1

/-- **A first-order captured context re-lends**, slot by slot. -/
theorem relend_gSepC {ls : List SRec} {δ : LSub} :
    ∀ (Γ : Ctx VTy), FOCtx Γ → ∀ (γ : List Val) (ρ : WRes), gSepC (ℍ := ℍ) ls δ Γ γ ρ →
      ∀ ls' : List SRec, ∃ ρ', RemakeR θ ρ ρ' ∧ gSepC (ℍ := ℍ) ls' (mv θ δ) Γ γ ρ'
  | [], _, γ, ρ, h, ls' => by
      obtain rfl := emp_eq h
      exact ⟨PMap.empty, remakeR_empty, by cases γ <;> exact ⟨rfl, trivial⟩⟩
  | s :: Γ, hΓ, [], ρ, h, ls' => by
      obtain rfl := emp_eq h
      exact ⟨PMap.empty, remakeR_empty, ⟨rfl, trivial⟩⟩
  | s :: Γ, hΓ, v :: γ, ρ, h, ls' => by
      have hΓ' : FOCtx Γ := fun t ht hl => hΓ t (List.mem_cons_of_mem _ ht) hl
      by_cases hl : s.live = true
      · have hs : FOV s.ty := hΓ s (List.mem_cons_self) hl
        have h' : (vCE (ℍ := ℍ) none true s.ty ls δ v ⋆ gSepC (ℍ := ℍ) ls δ Γ γ) ρ := by
          simpa [gSepC, hl] using h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h'
        obtain ⟨ρ₁', hR₁, h₁'⟩ := relend_fov θ s.ty hs ls δ v ρ₁ h₁ ls'
        obtain ⟨ρ₂', hR₂, h₂'⟩ := relend_gSepC Γ hΓ' γ ρ₂ h₂ ls'
        obtain ⟨ρ', hc', hR⟩ := remakeR_compS hc hR₁ hR₂
        refine ⟨ρ', hR, ?_⟩
        unfold gSepC
        rw [if_pos hl]
        exact ⟨ρ₁', ρ₂', hc', h₁', h₂'⟩
      · have h' : gSepC (ℍ := ℍ) ls δ Γ γ ρ := by simpa [gSepC, hl] using h
        obtain ⟨ρ', hR, h''⟩ := relend_gSepC Γ hΓ' γ ρ h' ls'
        exact ⟨ρ', hR, by simpa [gSepC, hl] using h''⟩

theorem relend_gDenC {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} (hΓ : FOCtx Γ) {γ : List Val}
    {ρ : WRes} (h : gDenC (ℍ := ℍ) ls δ Γ γ ρ) (ls' : List SRec) :
    ∃ ρ', RemakeR θ ρ ρ' ∧ gDenC (ℍ := ℍ) ls' (mv θ δ) Γ γ ρ' := by
  obtain ⟨hlive, hs⟩ := pure_sep_iff.mp h
  obtain ⟨ρ', hR, hs'⟩ := relend_gSepC θ Γ hΓ γ ρ hs ls'
  exact ⟨ρ', hR, pure_sep_mk hlive hs'⟩

/-- **A term Core's semantic judgment relates re-lends wherever its captured context does**, at
every computation type: the judgment holds at the moved reading, which `⟦Δ⟧` admits. -/
theorem semC_relend {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy}
    (hS : SemC (ℍ := ℍ) Δ Γ e C) {δ : LSub} {γ : List Val} {ls' : List SRec}
    {ρ ρ' : WRes} (hδ : Δ.Models δ) (hR : RemakeR θ ρ ρ')
    (hg : gDenC (ℍ := ℍ) ls' (mv θ δ) Γ γ ρ') :
    ∃ ρ'', RemakeR θ ρ ρ'' ∧ cC (ℍ := ℍ) C ls' (mv θ δ) (substAll γ e) ρ'' :=
  ⟨ρ', hR, hS _ γ ls' ρ' ((θ.models_mapN_iff Δ δ).mpr hδ) hg⟩

/-- **Every term Core's typing derives re-lends**, closed by a first-order context, at every
computation type and every re-making of the region. -/
theorem relend_derivable {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy}
    (hd : CDerives Δ Γ e (.comp C)) (hΓ : FOCtx Γ) {δ : LSub} {γ : List Val} {ls : List SRec}
    {ρ : WRes} (hδ : Δ.Models δ) (hg : gDenC (ℍ := ℍ) ls δ Γ γ ρ) (ls' : List SRec) :
    ∃ ρ', RemakeR θ ρ ρ' ∧ cC (ℍ := ℍ) C ls' (mv θ δ) (substAll γ e) ρ' := by
  obtain ⟨ρ', hR, hg'⟩ := relend_gDenC θ hΓ hg ls'
  exact semC_relend θ (fundamentalC (ℍ := ℍ) hd : SemC Δ Γ e C) hδ hR hg'

end Relend

end Law2

end
