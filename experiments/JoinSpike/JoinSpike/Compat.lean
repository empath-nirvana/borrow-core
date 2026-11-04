import JoinSpike.Keep

/-!
# Join spike: where a task's borrowed cells may sit

`HoldsIn A O ρ`: every `imm` cell of `ρ`'s flattening is at a location masked by `ρ`'s
own records `O` or in `A`. For a task run by the scheduler, `A` is the locations its nearest
joiner shares; so a task holds no borrowed cell from outside the pool, and the views it holds of
the pool's lends are at shared locations. This is the invariant over the running task that
`PoolAns` lacks.

It is kept by every run (`twp_holdsIn`): a cell of the end's flattening outside the end's masks is
one of the start's, outside the start's masks (`UpdX`, its converse clause). It is carried by
re-reading (`HoldsIn.rr`), by taking a part (`HoldsIn.of_compS_left`) and by composing
(`HoldsIn.compS`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont)

variable {K K' : WCactus}

/-- **Borrowed cells only at own masks or at `A`.** -/
def HoldsIn (A : BoCa.Loc → Prop) (O : List (FrameRecT K)) (ρ : TRes K) : Prop :=
  ∀ τ, ResUT.Flat ρ τ → ∀ x (ψ : TCell K), τ.get x = some ψ → ψ.kind = Kind.imm →
    recMask O x ∨ A x

theorem kcomb_imm_left {k₂ : Kind} : kcomb Kind.imm k₂ = Kind.imm := by
  cases k₂ <;> rfl

theorem kcomb_imm {k₁ k₂ : Kind} (h : kcomb k₁ k₂ = Kind.imm) : k₁ = Kind.imm ∨ k₂ = Kind.imm := by
  cases k₁ <;> cases k₂ <;> simp_all [kcomb]

theorem HoldsIn.mono {A A' : BoCa.Loc → Prop} {O : List (FrameRecT K)} {ρ : TRes K}
    (h : HoldsIn A O ρ) (hA : ∀ x, A x → A' x) : HoldsIn A' O ρ :=
  fun τ hτ x ψ e k => (h τ hτ x ψ e k).imp id (hA x)

theorem HoldsIn.empty (A : BoCa.Loc → Prop) (O : List (FrameRecT K)) :
    HoldsIn A O (PMap.empty : TRes K) := by
  intro τ hτ x ψ e _
  obtain rfl := ResUT.Flat.functional hτ flat_empty
  simp at e

theorem HoldsIn.of_compS_left {A : BoCa.Loc → Prop} {O : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (hv : ResUT.Valid c) (h : HoldsIn A O c) : HoldsIn A O a := by
  intro τa hτa x ψ e k
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨σ₁, σ₂, h₁, -, hσ⟩ := BoLo.flat_compR hc hτ
  obtain rfl := ResUT.Flat.functional h₁ hτa
  have hp := hσ.2 x
  rw [e] at hp
  revert hp
  cases e₂ : σ₂.get x with
  | none => intro hp; exact h τ hτ x ψ hp k
  | some ψ₂ =>
      rintro ⟨χ, hχ, hC⟩
      exact h τ hτ x χ hχ (by rw [CellUT.CompR.kind_eq hC, k]; exact kcomb_imm_left)

theorem HoldsIn.of_compS_right {A : BoCa.Loc → Prop} {O : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (hv : ResUT.Valid c) (h : HoldsIn A O c) : HoldsIn A O b :=
  HoldsIn.of_compS_left (ResUT.CompS.comm hc) hv h

theorem HoldsIn.compS {A : BoCa.Loc → Prop} {O : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (ha : HoldsIn A O a) (hb : HoldsIn A O b) : HoldsIn A O c := by
  intro τ hτ x ψ e k
  obtain ⟨σ₁, σ₂, h₁, h₂, hσ⟩ := BoLo.flat_compR hc hτ
  have hp := hσ.2 x
  rw [e] at hp
  revert hp
  cases e₁ : σ₁.get x with
  | none =>
      cases e₂ : σ₂.get x with
      | none => intro hp; cases hp
      | some ψ₂ => intro hp; cases hp; exact hb σ₂ h₂ x _ e₂ k
  | some ψ₁ =>
      cases e₂ : σ₂.get x with
      | none => intro hp; cases hp; exact ha σ₁ h₁ x _ e₁ k
      | some ψ₂ =>
          rintro ⟨χ, hχ, hC⟩
          cases hχ
          rcases kcomb_imm ((CellUT.CompR.kind_eq hC).symm.trans k) with k₁ | k₂
          · exact ha σ₁ h₁ x ψ₁ e₁ k₁
          · exact hb σ₂ h₂ x ψ₂ e₂ k₂

/-- **Carried by re-reading**: the flattening's cells are re-read with their tags. -/
theorem HoldsIn.rr {Θ : LocTy} (hE : K.Ext K') {A : BoCa.Loc → Prop} {O : List (FrameRecT K)}
    {O' : List (FrameRecT K')} (hO : ∀ x, recMask O x ↔ recMask O' x) {ρ : TRes K}
    {ρ' : TRes K'} (hv : ResUT.Valid ρ) (hr : RR Θ ρ ρ') (h : HoldsIn A O ρ) :
    HoldsIn A O' ρ' := by
  intro τ' hτ' x ψ' e k
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨σ', hσ', hs⟩ := ResUT.Flat.rrLs hE hτ hr
  obtain rfl := ResUT.Flat.functional hσ' hτ'
  have hl := hs x
  rw [e] at hl
  revert hl
  cases eψ : τ.get x with
  | none => intro hl; cases hl
  | some ψ =>
      intro hl
      cases hl with
      | some hl => exact (h τ hτ x ψ eψ (hl.1.symm.trans k)).imp (hO x).mp id

/-- **Kept by every run.** -/
theorem twp_holdsIn {A : BoCa.Loc → Prop} {F : TFrame} {P : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (hv : ResUT.Valid ρ) (hA : HoldsIn A O ρ) (h : twp (ℍ := ℍ) F P n w ls O e ρ) :
    twp (ℍ := ℍ) F (fun k w' ls' O' t ρ' => P k w' ls' O' t ρ' ∧ HoldsIn A O' ρ') n w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' hj hrun hfin
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ := h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' hj hrun hfin
  have hA₀ : HoldsIn A O₀ ρ₀ := hA.rr hE.1 (recMask_rr hO) hv hr
  refine ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, ⟨g₈, ?_⟩, g₉,
    g₁₀, g₁₁⟩
  intro τ' hτ' x ψ' eψ k
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := g₉
  obtain rfl := ResUT.Flat.functional hσ' hτ'
  by_cases hm : recMask O' x
  · exact Or.inl hm
  · obtain ⟨hm₀, ψ, eψ₀, hX⟩ := (hx x).2 ψ' eψ (by rw [k]; decide) hm
    exact (hA₀ σ hσ x ψ eψ₀ (hX.1.symm.trans k)).resolve_left hm₀ |> Or.inr

end BoCa.Fig16.Tree.Wp

end
