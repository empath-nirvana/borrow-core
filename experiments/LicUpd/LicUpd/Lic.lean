import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Algebra
import Support.Model.Ancestors
import Support.Model.CellFacts
import Support.Model.Composition
import Support.Model.Empty
import Support.Model.FlatteningCells
import Support.Model.Propositions
import Support.Model.Reborrow
import Support.Model.ReborrowFrame
import Support.Model.Singletons
import Support.Model.Surgery
import Support.Model.SubtractionKeep
import Support.Model.WalkSplitting

/-!
# LicUpd — Lic

G1 (#1007): `↭` with its `imm` clause's end-to-start direction exempted for views
*derivable* from the start's `imm` views.

- `Derivable σ l ψ`: the least relation that contains the `imm` cells of `σ` and is closed
  under one projection step. The step goes from a derivable `imm(s, u, χ)` to an image
  `imm(t, v, w)` at a location `l` where `χ` owns `v`. Every lifetime of `t` is no longer than
  some lifetime of `s`, and `w ≤ χ`. This is the shape of `RebAt`'s `own` clause, read one
  level at a time.
- `UpdImmLic ρ₁ ρ₂`: every `imm` cell of `⦇ρ₁⦈` is in `⦇ρ₂⦈`, as in `UpdImm`. Every `imm` cell
  of `⦇ρ₂⦈` is in `⦇ρ₁⦈` or is derivable from `⦇ρ₁⦈`.
- `UpdLic`: `UpdImmLic` with `↭`'s `mut` clause (`UpdMut`) unchanged. G1 exempts no `mut` cell.
- `UpdVLic`: `UpdLic` guarded by `✓ρ₁ ∧ ✓ρ₂`, as `UpdV` guards `Upd`.

Proved here, in general:
- conservativity: `↭` implies `UpdLic`;
- transitivity (`UpdImmLic.trans`, `UpdVLic.trans`): derivability is a closure, so a view
  derived from a middle view is derived from the start (`Derivable.trans`);
- `UpdLic.updMut`: the `mut` clause is `↭`'s.
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-- `ψ` at `l` is derivable from the flattening `σ`: an `imm` cell of `σ`, or an image of an
owned cell of a derivable view's witness. Each image lifetime is no longer than some lifetime
of the view it is taken from. -/
inductive Derivable (σ : WRes) : Loc → CellU Loc Val → Prop
  | base {m : Loc} {ψ : CellU Loc Val} :
      σ.get m = some ψ → ψ.kind = Kind.imm → Derivable σ m ψ
  | proj {m l : Loc} {s : LSet} {u : Val} {χ : WRes} {hχ : χ.InStratum s.join}
      {t : LSet} {v : Val} {w : WRes} {hw : w.InStratum t.join} :
      Derivable σ m (CellU.immOf s u χ hχ) → χ.get l = some (CellU.ownOf v) →
      (∀ x, t.mem x → ∃ y, s.mem y ∧ x ≤ y) → ResU.Le w χ →
      Derivable σ l (CellU.immOf t v w hw)

/-- Every derivation starts at an `imm` cell of `σ`. -/
theorem Derivable.root {σ : WRes} {l : Loc} {ψ : CellU Loc Val} (h : Derivable σ l ψ) :
    ∃ m ψ₀, σ.get m = some ψ₀ ∧ ψ₀.kind = Kind.imm := by
  induction h with
  | base e k => exact ⟨_, _, e, k⟩
  | proj _ _ _ _ ih => exact ih

/-- **Derivability is a closure.** If every `imm` cell of `σ₁` is derivable from `σ₀`, so is
everything derivable from `σ₁`. -/
theorem Derivable.trans {σ₀ σ₁ : WRes}
    (H : ∀ m ψ, σ₁.get m = some ψ → ψ.kind = Kind.imm → Derivable σ₀ m ψ)
    {l : Loc} {ψ : CellU Loc Val} (h : Derivable σ₁ l ψ) : Derivable σ₀ l ψ := by
  induction h with
  | base e k => exact H _ _ e k
  | proj _ hl ht hle ih => exact Derivable.proj ih hl ht hle

/-- G1's `imm` clause: `UpdImm` with the end-to-start direction relaxed to derivable views. -/
def UpdImmLic (ρ₁ ρ₂ : WRes) : Prop :=
  (∀ (l : Loc) (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join),
    ρ₁.FlatAt l (CellU.immOf s v χ h) → ρ₂.FlatAt l (CellU.immOf s v χ h)) ∧
  (∀ (l : Loc) (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join),
    ρ₂.FlatAt l (CellU.immOf s v χ h) →
      ρ₁.FlatAt l (CellU.immOf s v χ h) ∨
      ∃ σ, ResU.Flat ρ₁ σ ∧ Derivable σ l (CellU.immOf s v χ h))

/-- G1's `↭`: the `imm` clause relaxed, the `mut` clause unchanged. -/
def UpdLic (ρ₁ ρ₂ : WRes) : Prop := UpdImmLic ρ₁ ρ₂ ∧ ResU.UpdMut ρ₁ ρ₂

/-- `UpdLic` guarded by `✓ρ₁ ∧ ✓ρ₂`. -/
def UpdVLic (ρ₁ ρ₂ : WRes) : Prop := UpdLic ρ₁ ρ₂ ∧ ρ₁.Valid ∧ ρ₂.Valid

/-! ### Conservativity -/

theorem UpdImmLic.of_updImm {ρ₁ ρ₂ : WRes} (h : ResU.UpdImm ρ₁ ρ₂) : UpdImmLic ρ₁ ρ₂ :=
  ⟨fun l s v χ hs h₁ => (h l s v χ hs).mp h₁,
    fun l s v χ hs h₂ => Or.inl ((h l s v χ hs).mpr h₂)⟩

theorem UpdLic.of_upd {ρ₁ ρ₂ : WRes} (h : ResU.Upd ρ₁ ρ₂) : UpdLic ρ₁ ρ₂ :=
  ⟨UpdImmLic.of_updImm h.1, h.2⟩

theorem UpdVLic.of_updV {ρ₁ ρ₂ : WRes} (h : ResU.UpdV ρ₁ ρ₂) : UpdVLic ρ₁ ρ₂ :=
  ⟨UpdLic.of_upd h.1, h.2⟩

/-- **G1 exempts no `mut` cell.** -/
theorem UpdLic.updMut {ρ₁ ρ₂ : WRes} (h : UpdLic ρ₁ ρ₂) : ResU.UpdMut ρ₁ ρ₂ := h.2

/-! ### Transitivity -/

/-- **G1 composes.** A view the second run derives from the middle is derivable from the
start, because every `imm` view of the middle is in the start or derivable from it. -/
theorem UpdImmLic.trans {ρ₀ ρ₁ ρ₂ : WRes} (h₁ : UpdImmLic ρ₀ ρ₁) (h₂ : UpdImmLic ρ₁ ρ₂) :
    UpdImmLic ρ₀ ρ₂ := by
  refine ⟨fun l s v χ hs hf => h₂.1 l s v χ hs (h₁.1 l s v χ hs hf), fun l s v χ hs hf => ?_⟩
  rcases h₂.2 l s v χ hs hf with hf' | ⟨σ₁, hσ₁, hd⟩
  · exact h₁.2 l s v χ hs hf'
  · -- the start has a flattening: the derivation's root is a view of the middle
    obtain ⟨m₀, ψ₀, e₀, k₀⟩ := hd.root
    obtain ⟨t₀, ht₀, hψ₀⟩ := CellU.imm_eta k₀
    have hf₀ : ρ₁.FlatAt m₀ (CellU.immOf t₀ ψ₀.erase ψ₀.wit ht₀) :=
      ⟨σ₁, hσ₁, by rw [← hψ₀]; exact e₀⟩
    have hex : ∃ σ₀, ResU.Flat ρ₀ σ₀ := by
      rcases h₁.2 m₀ t₀ ψ₀.erase ψ₀.wit ht₀ hf₀ with ⟨σ₀, hσ₀, -⟩ | ⟨σ₀, hσ₀, -⟩
      · exact ⟨σ₀, hσ₀⟩
      · exact ⟨σ₀, hσ₀⟩
    obtain ⟨σ₀, hσ₀⟩ := hex
    refine Or.inr ⟨σ₀, hσ₀, Derivable.trans (fun m ψ e k => ?_) hd⟩
    obtain ⟨t, ht, hψ⟩ := CellU.imm_eta k
    have hf₁ : ρ₁.FlatAt m (CellU.immOf t ψ.erase ψ.wit ht) :=
      ⟨σ₁, hσ₁, by rw [← hψ]; exact e⟩
    rw [hψ]
    rcases h₁.2 m t ψ.erase ψ.wit ht hf₁ with ⟨σ', hσ', e'⟩ | ⟨σ', hσ', hd'⟩
    · rw [ResU.Flat.functional hσ' hσ₀] at e'
      exact Derivable.base e' (CellU.kind_immOf _ _ _ _)
    · rw [ResU.Flat.functional hσ' hσ₀] at hd'
      exact hd'

theorem UpdLic.trans {ρ₀ ρ₁ ρ₂ : WRes} (h₁ : UpdLic ρ₀ ρ₁) (h₂ : UpdLic ρ₁ ρ₂) :
    UpdLic ρ₀ ρ₂ :=
  ⟨h₁.1.trans h₂.1, fun l b P => (h₁.2 l b P).trans (h₂.2 l b P)⟩

theorem UpdVLic.trans {ρ₀ ρ₁ ρ₂ : WRes} (h₁ : UpdVLic ρ₀ ρ₁) (h₂ : UpdVLic ρ₁ ρ₂) :
    UpdVLic ρ₀ ρ₂ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1, h₂.2.2⟩

/-! ### Small facts used by the configurations -/

theorem comp_get_left {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ₁ ρ₂ ρ : WRes}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ : CellU Loc Val}
    (e₁ : ρ₁.get l = some ψ) (e₂ : ρ₂.get l = none) : ρ.get l = some ψ := by
  have hp := h.2 l
  rw [e₁, e₂] at hp
  exact hp

theorem comp_get_right {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ₁ ρ₂ ρ : WRes}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ : CellU Loc Val}
    (e₁ : ρ₁.get l = none) (e₂ : ρ₂.get l = some ψ) : ρ.get l = some ψ := by
  have hp := h.2 l
  rw [e₁, e₂] at hp
  exact hp

theorem comp_get_none {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ₁ ρ₂ ρ : WRes}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc}
    (e₁ : ρ₁.get l = none) (e₂ : ρ₂.get l = none) : ρ.get l = none := by
  have hp := h.2 l
  rw [e₁, e₂] at hp
  exact hp

theorem comp_get_both {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ₁ ρ₂ ρ : WRes}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ₁ ψ₂ : CellU Loc Val}
    (e₁ : ρ₁.get l = some ψ₁) (e₂ : ρ₂.get l = some ψ₂) :
    ∃ ψ, ρ.get l = some ψ ∧ C ψ₁ ψ₂ ψ := by
  have hp := h.2 l
  rw [e₁, e₂] at hp
  exact hp

/-- `∅ ∈ Res_a`, at `WRes`. -/
theorem inStratum_emptyW (a : Life) : ResU.InStratum a (PMap.empty : WRes) :=
  ResU.inStratum_empty a

/-- `⦇∅⦈ = ∅`. -/
theorem flat_empty_eq {τ : WRes} (hτ : ResU.Flat (PMap.empty : WRes) τ) : τ = PMap.empty := by
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  obtain rfl : e = PMap.empty := ExS.functional he exW_empty
  obtain rfl : a = PMap.empty := AgW.functional ha agW_empty
  exact eq_of_compS_empty_left hc

/-- Nothing is derivable from the empty flattening. -/
theorem not_derivable_empty {l : Loc} {ψ : CellU Loc Val} :
    ¬ Derivable (PMap.empty : WRes) l ψ := by
  intro h
  obtain ⟨m, ψ₀, e, -⟩ := h.root
  rw [PMap.empty_get] at e
  cases e

/-- A non-`imm` cell of a one-cell resource is its flattening's cell. -/
theorem flat_single_get_of_ne_imm {l : Loc} {ψ : CellU Loc Val} (hk : ψ.kind ≠ Kind.imm)
    {σ : WRes} (h : ResU.Flat (ResU.single l ψ) σ) : σ.get l = some ψ := by
  obtain ⟨ex, a, hex, -, hc⟩ := h
  exact (ResU.CompS.get_left_of_ne_imm hc
    (ExS.get_of_ne_imm hex (ResU.single_get_self _ _) hk) hk).2

end BoCa.Fig16.LicUpd

end
