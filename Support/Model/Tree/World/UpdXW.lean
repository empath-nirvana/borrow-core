import Support.Model.Tree.World.UpdX

/-!
# `↭` with a given-up `imm` copy absorbed by the end world  `[spec §62]`

Departure D4, design (b) (`docs/new-core/scope-806.md`). `UpdXW` is `UpdX` read beside the end
world `fρ′`: an unmasked `imm` cell of the start's flattening is a cell of the end's (`XCell`), or
the end world's flattening absorbs it (`CellAbs`: same value, witness re-read, lifetime set at
least the cell's); an unmasked `imm` cell of the end's flattening is a cell of the start's, or a
start cell absorbs it (`CellSub`). `mut` cells read `XCell` exactly (`CellAbs` and `CellSub` force
`imm`).

**The frame.** A frame step for `UpdXW` one location at a time does not go through where a run
gives up an `imm` cell at `ℓ` whose framed neighbour's flattening holds a `mut` cell at `ℓ` (the
clause `imm ○ mut = imm` of `○`): no relation between the two cells at `ℓ` alone accepts it.
`EndT` reads `UpdA` (`World/UpdA.lean`), which accounts for that `mut` cell by its `imm` ancestor
(`UpdA.frame`); `UpdA` admits the configuration (`updA_admits_frameAt`, `Core/TreeConsume.lean`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-! ### The clause -/

/-- `χ` (at the end) absorbs the `imm` cell `ψ` (at the start), across the re-reading: same
value, witness re-read, lifetime set at least `ψ`'s. -/
def CellAbs (Θ : LocTy) (ψ : TCell K) (χ : TCell K') : Prop :=
  ψ.kind = Kind.imm ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ RR Θ ψ.wit χ.wit ∧
    ∃ s t, ψ.lsOf = some s ∧ χ.lsOf = some t ∧ s.set ⊆ t.set

/-- `ψ'` (at the end) is absorbed by `ψ` (at the start): same value, witness re-read, lifetime
set at most `ψ`'s. -/
def CellSub (Θ : LocTy) (ψ : TCell K) (ψ' : TCell K') : Prop :=
  ψ.kind = Kind.imm ∧ ψ'.kind = Kind.imm ∧ ψ'.erase = ψ.erase ∧ RR Θ ψ.wit ψ'.wit ∧
    ∃ s t, ψ.lsOf = some s ∧ ψ'.lsOf = some t ∧ t.set ⊆ s.set

/-- **`XOpt` with the `imm` clauses relaxed.** `ow` is the end world's flattening at the
location. -/
def XOptW (Θ : LocTy) (E E' : Prop) (o : Option (TCell K)) (o' ow : Option (TCell K')) : Prop :=
  (∀ ψ, o = some ψ → ψ.kind ≠ Kind.own → ¬ E → ¬ E' ∧
    ((∃ ψ', o' = some ψ' ∧ XCell Θ ψ ψ') ∨ ∃ χ, ow = some χ ∧ CellAbs Θ ψ χ)) ∧
  (∀ ψ', o' = some ψ' → ψ'.kind ≠ Kind.own → ¬ E' → ¬ E ∧
    ∃ ψ, o = some ψ ∧ (XCell Θ ψ ψ' ∨ CellSub Θ ψ ψ'))

/-- **`UpdX` relaxed at the end world `fρ′`.** -/
def UpdXW (Θ : LocTy) (E E' : BoCa.Loc → Prop) (ρ : TRes K) (ρ' fρ' : TRes K') : Prop :=
  ∃ σ σ' τw, ResUT.Flat ρ σ ∧ ResUT.Flat ρ' σ' ∧ ResUT.Flat fρ' τw ∧
    ∀ l, XOptW Θ (E l) (E' l) (σ.get l) (σ'.get l) (τw.get l)

/-- `UpdX` implies `UpdXW` at any valid end world. -/
theorem UpdX.toW {Θ : LocTy} {E E' : BoCa.Loc → Prop} {ρ : TRes K} {ρ' fρ' : TRes K'}
    (h : UpdX Θ E E' ρ ρ') (hv : ResUT.Valid fρ') : UpdXW Θ E E' ρ ρ' fρ' := by
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := h
  obtain ⟨τw, hτw⟩ := hv
  refine ⟨σ, σ', τw, hσ, hσ', hτw, fun l => ⟨fun ψ e hk hE => ?_, fun ψ' e hk hE => ?_⟩⟩
  · obtain ⟨h₁, h₂⟩ := (hx l).1 ψ e hk hE
    exact ⟨h₁, Or.inl h₂⟩
  · obtain ⟨h₁, ψ, e₀, hc⟩ := (hx l).2 ψ' e hk hE
    exact ⟨h₁, ψ, e₀, Or.inl hc⟩

/-! ### Composing the relaxed clauses -/

theorem rlsOf_imm (K' : WCactus) (o : Option TSet) : rlsOf K' Kind.imm o = o := rfl

/-- An `imm` cell `XCell`-related to its successor keeps its lifetime set. -/
theorem XCell.lsOf_imm {Θ : LocTy} {ψ : TCell K} {ψ' : TCell K'} (h : XCell Θ ψ ψ')
    (hk : ψ.kind = Kind.imm) : ψ'.lsOf = ψ.lsOf := by
  rw [h.2.1, hk, rlsOf_imm]

variable {K'' : WCactus}

theorem XCell.abs {Θ₁ Θ₂ : LocTy} (hE : K'.Ext K'') {ψ : TCell K} {ψ' : TCell K'}
    {χ : TCell K''} (h : XCell Θ₁ ψ ψ') (h' : CellAbs Θ₂ ψ' χ) : CellAbs Θ₂ ψ χ := by
  obtain ⟨k₁, k₂, e, r, s, t, hs, ht, hst⟩ := h'
  have hk : ψ.kind = Kind.imm := h.1.symm.trans k₁
  obtain ⟨e₀, r₀⟩ := h.2.2 hk
  exact ⟨hk, k₂, e.trans e₀, RR.trans_retype hE r₀ r, s, t, (h.lsOf_imm hk).symm.trans hs, ht,
    hst⟩

theorem CellAbs.trans {Θ₁ Θ₂ : LocTy} (hE : K'.Ext K'') {ψ : TCell K} {χ : TCell K'}
    {χ' : TCell K''} (h : CellAbs Θ₁ ψ χ) (h' : CellAbs Θ₂ χ χ') : CellAbs Θ₂ ψ χ' := by
  obtain ⟨k₁, k₂, e, r, s, t, hs, ht, hst⟩ := h
  obtain ⟨-, k₃, e', r', t', u, ht', hu, htu⟩ := h'
  rw [ht] at ht'; cases ht'
  exact ⟨k₁, k₃, e'.trans e, RR.trans_retype hE r r', s, u, hs, hu, hst.trans htu⟩

/-- The end side's relation composes. -/
theorem xsub_trans {Θ₁ Θ₂ : LocTy} (hE : K'.Ext K'') {ψ : TCell K} {ψ' : TCell K'}
    {ψ'' : TCell K''} (h : XCell Θ₁ ψ ψ' ∨ CellSub Θ₁ ψ ψ')
    (h' : XCell Θ₂ ψ' ψ'' ∨ CellSub Θ₂ ψ' ψ'') : XCell Θ₂ ψ ψ'' ∨ CellSub Θ₂ ψ ψ'' := by
  rcases h with h | ⟨k₁, k₂, e, r, s, t, hs, ht, hst⟩ <;>
    rcases h' with h' | ⟨k₃, k₄, e', r', t', u, ht', hu, htu⟩
  · exact Or.inl (h.trans hE h')
  · have hk : ψ.kind = Kind.imm := h.1.symm.trans k₃
    obtain ⟨e₀, r₀⟩ := h.2.2 hk
    exact Or.inr ⟨hk, k₄, e'.trans e₀, RR.trans_retype hE r₀ r', t', u,
      (h.lsOf_imm hk).symm.trans ht', hu, htu⟩
  · obtain ⟨e₀, r₀⟩ := h'.2.2 k₂
    refine Or.inr ⟨k₁, h'.1.trans k₂, e₀.trans e, RR.trans_retype hE r r₀, s, t, hs,
      (h'.lsOf_imm k₂).trans ht, hst⟩
  · rw [ht] at ht'; cases ht'
    exact Or.inr ⟨k₁, k₄, e'.trans e, RR.trans_retype hE r r', s, u, hs, hu, htu.trans hst⟩

/-- **The relaxed clause composes at one location**, given that the end world absorbs every
`imm` cell the middle world absorbed, the end unmasked there (`hw`, read where the middle is
unmasked). The mask part of `hw` is what an absorbed cell needs that an `XCell`-carried cell gets
from the next segment's clause: where the middle holds no cell, the next segment says nothing of
the end's mask. -/
theorem XOptW.trans {Θ₁ Θ₂ : LocTy} (hE : K'.Ext K'') {E E' E'' : Prop} {o : Option (TCell K)}
    {o' ow' : Option (TCell K')} {o'' ow'' : Option (TCell K'')}
    (h : XOptW Θ₁ E E' o o' ow') (h' : XOptW Θ₂ E' E'' o' o'' ow'')
    (hw : ¬ E' → ∀ χ, ow' = some χ → χ.kind = Kind.imm →
      ¬ E'' ∧ ∃ χ'', ow'' = some χ'' ∧ CellAbs Θ₂ χ χ'') :
    XOptW Θ₂ E E'' o o'' ow'' := by
  refine ⟨fun ψ e hk hE₀ => ?_, fun ψ'' e hk hE₀ => ?_⟩
  · obtain ⟨hE₁, h₁⟩ := h.1 ψ e hk hE₀
    rcases h₁ with ⟨ψ', e', hx⟩ | ⟨χ, eχ, ha⟩
    · obtain ⟨hE₂, h₂⟩ := h'.1 ψ' e' (hx.1 ▸ hk) hE₁
      rcases h₂ with ⟨ψ'', e'', hx'⟩ | ⟨χ'', eχ'', ha'⟩
      · exact ⟨hE₂, Or.inl ⟨ψ'', e'', hx.trans hE hx'⟩⟩
      · exact ⟨hE₂, Or.inr ⟨χ'', eχ'', hx.abs hE ha'⟩⟩
    · obtain ⟨hE₂, χ'', eχ'', ha'⟩ := hw hE₁ χ eχ ha.2.1
      exact ⟨hE₂, Or.inr ⟨χ'', eχ'', ha.trans hE ha'⟩⟩
  · obtain ⟨hE₁, ψ', e', hx'⟩ := h'.2 ψ'' e hk hE₀
    have hk' : ψ'.kind ≠ Kind.own := by
      rcases hx' with hx' | hx'
      · exact fun c => hk (hx'.1.trans c)
      · rw [hx'.1]; exact fun c => Kind.noConfusion c
    obtain ⟨hE₂, ψ, e₀, hx⟩ := h.2 ψ' e' hk' hE₁
    exact ⟨hE₂, ψ, e₀, xsub_trans hE hx hx'⟩

end BoCa.Fig16.Tree.Wp

end
