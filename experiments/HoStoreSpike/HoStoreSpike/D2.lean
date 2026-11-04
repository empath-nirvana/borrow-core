import HoStoreSpike.Formers

/-!
# D2 at the higher-order store (spike, #790)

`World/UpdXInv.lean`'s D2 reads row 5.27's "same `P̂`" as "the same code at `ℓ` on both sides"
(`InvKept`, `UpdX.inv`). `UpdX`, `MutCov` and `flat_mut_inv` are generic in the location typing, so
at `semH` they apply unchanged. Here D2 is restated with the store typing's types in place of
codes (`InvKeptH`) and `UpdX.inv`'s proof is replayed (`UpdX.invH`): at an unmasked `mut` cell of
both flattenings, the two invariants are one type `τ`, kept from `Ψ` to `Ψ′`, read at each side's
tree **and index**. At one tree and one index they are one predicate (`updXH_refl_mut`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.HoStore
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp

variable {K K' : WCactus}

/-- **`Ψ′` keeps `Ψ`'s type at every `mut` cell of `⦇ρ⦈` outside `E`** (`InvKept` at types). -/
def InvKeptH (Ψ Ψ' : HStore) (E : BoCa.Loc → Prop) (ρ : TRes K) : Prop :=
  ∀ σ, ResUT.Flat ρ σ → ∀ l (m : TMut K), σ.get l = some (.mut m) → ¬ E l → Ψ' l = Ψ l

/-- A store typing keeping the types where `ρ` holds a `mut` cell keeps those `⦇ρ⦈` reads
(`InvKept.of_agree`). -/
theorem InvKeptH.of_agree {Ψ Ψ' : HStore} {E : BoCa.Loc → Prop} {ρ W : TRes K} (hW : MutOne W)
    (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) (hag : AgreeH Ψ Ψ' ρ) :
    InvKeptH Ψ Ψ' E ρ :=
  fun _ hσ l _ e _ => hag l ((flat_mut_cellAt hW hsub hσ l _ e rfl).holdsMut.1 rfl)

/-- `ψ`, `ψ′` at `l`, if both `mut`, store one type `τ`, kept from `Ψ` to `Ψ′`, read at `(Ψ, K, n)`
and at `(Ψ′, K′, n′)` (`XInv` at types). -/
def XInvH (Ψ Ψ' : HStore) (n n' : Nat) (l : BoCa.Loc) (ψ : TCell K) (ψ' : TCell K') : Prop :=
  ∀ m m', ψ = .mut m → ψ' = .mut m' →
    ∃ τ, Ψ l = some τ ∧ Ψ' l = some τ ∧ (∀ w r, m.P w r ↔ (cellInv Ψ τ n).P K w r.toU) ∧
      (∀ w r, m'.P w r ↔ (cellInv Ψ' τ n').P K' w r.toU)

/-- **Row 5.27's `P̂` across a re-reading at the higher-order store** (`UpdX.inv`'s proof). -/
theorem UpdX.invH {Θx : LocTy} {Ψ Ψ' : HStore} {n n' : Nat} {E E' : BoCa.Loc → Prop}
    {ρ : TRes K} {ρ' : TRes K'} (h : UpdX Θx E E' ρ ρ') (hm : MutCov (semH Ψ n) K ρ)
    (hm' : MutCov (semH Ψ' n') K' ρ') (hk : InvKeptH Ψ Ψ' E ρ) :
    ∃ σ σ', ResUT.Flat ρ σ ∧ ResUT.Flat ρ' σ' ∧ (∀ l, XOpt Θx (E l) (E' l) (σ.get l) (σ'.get l)) ∧
      ∀ l ψ ψ', σ.get l = some ψ → σ'.get l = some ψ' → ¬ E l → XInvH Ψ Ψ' n n' l ψ ψ' := by
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := h
  obtain ⟨hc, W, hW, hsub⟩ := hm
  obtain ⟨hc', W', hW', hsub'⟩ := hm'
  refine ⟨σ, σ', hσ, hσ', hx, fun l ψ ψ' e e' hE m m' hψ hψ' => ?_⟩
  subst hψ hψ'
  obtain ⟨κ, hΘ, hP⟩ := flat_mut_inv hW hsub hc hσ e
  obtain ⟨κ', hΘ', hP'⟩ := flat_mut_inv hW' hsub' hc' hσ' e'
  obtain ⟨τ, hτ, rfl⟩ := semH_some hΘ
  obtain ⟨τ', hτ', rfl⟩ := semH_some hΘ'
  have hl := hk σ hσ l m e hE
  rw [hl, hτ] at hτ'
  cases Option.some.inj hτ'
  exact ⟨τ, hτ, hl.trans hτ, hP, hP'⟩

/-- **At one tree and one index the clause is row 5.27's**: one `P̂`. -/
theorem updXH_refl_mut {Ψ : HStore} {n : Nat} {l : BoCa.Loc} {m m' : TMut K}
    (h : XInvH (K' := K) Ψ Ψ n n l (.mut m) (.mut m')) :
    ∀ w (r : ResT BoCa.Loc BoCa.Val K m.ls) (r' : ResT BoCa.Loc BoCa.Val K m'.ls),
      r.toU = r'.toU → (m.P w r ↔ m'.P w r') := by
  intro w r r' er
  obtain ⟨τ, -, -, hP, hP'⟩ := h m m' rfl rfl
  rw [hP, hP', er]

/-- **Lowering the index, or growing the tree, is an update.** A valid world covered at
`semH Ψ n` has a re-reading at every later tree and index `m ≤ n`, covered there, and the
re-reading is a `↭`-update at any mask (`UpdX.of_rr`, generic in the location typing), so the run
conditions R1 reads (`UpdX` chains, `UpdX.trans`) accept a step that drops the index. -/
theorem reread_is_update {Ψ Ψ' : HStore} (hL : Ψ.Lawful) (hE : K.Ext K') {n m : Nat}
    (hmn : m ≤ n) (E : BoCa.Loc → Prop) {ρ : TRes K} (hv : ResUT.Valid ρ)
    (hc : CovR (semH Ψ n) K ρ) (hag : AgreeH Ψ Ψ' ρ) :
    ∃ ρ' : TRes K', RR (semH Ψ' m) ρ ρ' ∧ CovR (semH Ψ' m) K' ρ' ∧ UpdX (semH Ψ' m) E E ρ ρ' := by
  obtain ⟨ρ', hr, hc'⟩ := RR.exists_H hL hE hmn hc hag
  exact ⟨ρ', hr, hc', UpdX.of_rr hE E hv hr⟩

end BoCa.Fig16.Tree.HoStore

end
