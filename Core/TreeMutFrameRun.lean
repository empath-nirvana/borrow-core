import Core.TreeMutFrame

/-!
# The Mut Frame's fold: `↭`, `P̂` and the memory across `ℓ ↦ mut ⇄ ℓ ↦ own ● ρ_v`  `[spec §62]`

`docs/new-core/scope-791.md` O8, step 1. The lender of a Mut Frame folds the borrow back at the
end of the borrowed run: `ℓ ↦ mut(β̄, v, ρ_v, P̂)` replaced by `ℓ ↦ own(v) ● ρ_v`, at the start and at
the end. `[TR]` 6.28's printed proof reads the two flattenings as agreeing off `ℓ` by exclusivity
of `ℓ` (`ResUT.flat_mut_own_agree_off`). Read along the walks (`UpdA`), the same agreement carries
every clause: an ancestor of a `Beneath` clause is an `imm` cell, so it is not at `ℓ`, where the
`mut` side has the `mut` cell.

* `UpdA.of_mut_own`: `↭` along the walks from the `mut` sides to the `own` sides (6.28, `⇒`).
* `InvKeptA.of_mut_own`: the codes `↭`'s `P̂` reads, from the `mut` side to the `own` side.
* `lower_mut_own_iff`: the two sides lower to the same memory (6.25 under a frame).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa BoCa.Fig16 BoCa.Fig16.Tree

variable {K K' : WCactus}

/-- **`[TR]` 6.28 along the walks, `⇒`.** The start `M = ρ ● ℓ ↦ mut(b, v, ρ_v, P̂)` and its
fold `O = ρ ● ℓ ↦ own(v) ● ρ_v`; the end `M′`, `O′` likewise; the end world `fM`, `fO` likewise.
`↭` from `M` to `M′` beside `fM` gives `↭` from `O` to `O′` beside `fO`. -/
theorem UpdA.of_mut_own {Θ : LocTy} {E E' : BoCa.Loc → Prop} {l : BoCa.Loc}
    {b : TSet} [Fact (K.Anti b)] {b' : TSet} [Fact (K'.Anti b')] {v : BoCa.Val} {v' : BoCa.Val}
    {ρ ρv W M O : TRes K} {hs : ρv.InStratum b} {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K b}
    {hw : P v ⟨ρv, hs⟩}
    {ρ' ρv' W' M' O' φ fM fO : TRes K'} {hs' : ρv'.InStratum b'}
    {P' : BoCa.Val → SPropST BoCa.Loc BoCa.Val K' b'} {hw' : P' v' ⟨ρv', hs'⟩}
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W)
    (hM : ResUT.CompS ρ (ResUT.single l (CellUT.mutOf b v ρv hs P hw)) M)
    (hO : ResUT.CompS ρ W O)
    (hW' : ResUT.CompS ρv' (ResUT.single l (CellUT.ownOf v')) W')
    (hM' : ResUT.CompS ρ' (ResUT.single l (CellUT.mutOf b' v' ρv' hs' P' hw')) M')
    (hO' : ResUT.CompS ρ' W' O')
    (hfM : ResUT.CompS φ (ResUT.single l (CellUT.mutOf b' v' ρv' hs' P' hw')) fM)
    (hfO : ResUT.CompS φ W' fO)
    (hvO : ResUT.Valid O) (hvO' : ResUT.Valid O') (hvfO : ResUT.Valid fO)
    (h : UpdA Θ E E' M M' fM) : UpdA Θ E E' O O' fO := by
  obtain ⟨σ, σ', τw, hσ, hσ', hτw, hx⟩ := h
  obtain ⟨G, hG⟩ := hvO
  obtain ⟨G', hG'⟩ := hvO'
  obtain ⟨Gw, hGw⟩ := hvfO
  obtain ⟨hoff, hFl, hGl⟩ := ResUT.flat_mut_own_agree_off hW hM hO hσ hG
  obtain ⟨hoff', -, hGl'⟩ := ResUT.flat_mut_own_agree_off hW' hM' hO' hσ' hG'
  obtain ⟨hoffw, -, -⟩ := ResUT.flat_mut_own_agree_off hW' hfM hfO hτw hGw
  have hne : ∀ m (ζ : TCell K), σ.get m = some ζ → ζ.kind = Kind.imm → m ≠ l := by
    rintro m ζ e hk rfl
    rw [hFl] at e; cases Option.some.inj e
    simp [CellUT.kind, CellUT.mutOf] at hk
  refine ⟨G, G', Gw, hG, hG', hGw, fun x => ⟨fun ψ e hk hE => ?_, fun ψ' e hk hE' => ?_⟩⟩
  · by_cases hxl : x = l
    · subst hxl; rw [hGl] at e; cases Option.some.inj e; exact absurd rfl hk
    rw [hoff x hxl] at e
    obtain ⟨h₁, h₂⟩ := (hx x).1 ψ e hk hE
    refine ⟨h₁, ?_⟩
    rcases h₂ with ⟨ψ'', e', hc⟩ | ⟨χ, e', hc⟩ | ⟨hkm, m, ζ, χ, hEm, hb, e', hc⟩
    · exact Or.inl ⟨ψ'', by rw [hoff' x hxl]; exact e', hc⟩
    · exact Or.inr (Or.inl ⟨χ, by rw [hoffw x hxl]; exact e', hc⟩)
    · have hm := hne m ζ hb.1 hb.2.1
      exact Or.inr (Or.inr ⟨hkm, m, ζ, χ, hEm, ⟨by rw [hoff m hm]; exact hb.1, hb.2⟩,
        by rw [hoffw m hm]; exact e', hc⟩)
  · by_cases hxl : x = l
    · subst hxl; rw [hGl'] at e; cases Option.some.inj e; exact absurd rfl hk
    rw [hoff' x hxl] at e
    obtain ⟨h₁, h₂⟩ := (hx x).2 ψ' e hk hE'
    refine ⟨h₁, ?_⟩
    rcases h₂ with ⟨ψ, e₀, hc⟩ | ⟨hkm, m, ζ, ξ, hb, hc⟩
    · exact Or.inl ⟨ψ, by rw [hoff x hxl]; exact e₀, hc⟩
    · have hm := hne m ζ hb.1 hb.2.1
      exact Or.inr ⟨hkm, m, ζ, ξ, ⟨by rw [hoff m hm]; exact hb.1, hb.2⟩, hc⟩

/-- **The codes `↭`'s `P̂` reads, from the `mut` side to its fold.** -/
theorem InvKeptA.of_mut_own {Θ Θ' : CodeTy} {E : BoCa.Loc → Prop} {l : BoCa.Loc}
    {b : TSet} [Fact (K.Anti b)] {v : BoCa.Val} {ρ ρv W M O : TRes K} {hs : ρv.InStratum b}
    {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K b} {hw : P v ⟨ρv, hs⟩}
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W)
    (hM : ResUT.CompS ρ (ResUT.single l (CellUT.mutOf b v ρv hs P hw)) M)
    (hO : ResUT.CompS ρ W O) (hvM : ResUT.Valid M) (h : InvKeptA Θ Θ' E M) :
    InvKeptA Θ Θ' E O := by
  obtain ⟨F, hF⟩ := hvM
  refine ⟨fun σ hσ x m e hE => ?_, fun σ hσ m ζ x ξ hb hk hEm hEx => ?_⟩
  · obtain ⟨hoff, -, hGl⟩ := ResUT.flat_mut_own_agree_off hW hM hO hF hσ
    have hxl : x ≠ l := by rintro rfl; rw [hGl] at e; cases e
    exact h.1 F hF x m (by rw [← hoff x hxl]; exact e) hE
  · obtain ⟨hoff, -, hGl⟩ := ResUT.flat_mut_own_agree_off hW hM hO hF hσ
    have hm : m ≠ l := by
      rintro rfl
      have e := hb.1
      rw [hGl] at e
      have := hb.2.1
      rw [← Option.some.inj e] at this
      cases this
    exact h.2 F hF m ζ x ξ ⟨by rw [← hoff m hm]; exact hb.1, hb.2⟩ hk hEm hEx

/-- **`[TR]` 6.25 under a frame**: a resource and its fold lower to the same memory. -/
theorem lower_mut_own_iff {l : BoCa.Loc} {b : TSet} [Fact (K.Anti b)] {v : BoCa.Val}
    {ρ ρv W M O : TRes K} {hs : ρv.InStratum b} {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K b}
    {hw : P v ⟨ρv, hs⟩} (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W)
    (hM : ResUT.CompS ρ (ResUT.single l (CellUT.mutOf b v ρv hs P hw)) M)
    (hO : ResUT.CompS ρ W O) (hvM : ResUT.Valid M) (hvO : ResUT.Valid O)
    (μ : BoCa.Loc → Option BoCa.Val) : ResUT.Lower M μ ↔ ResUT.Lower O μ := by
  obtain ⟨F, hF⟩ := hvM
  obtain ⟨G, hG⟩ := hvO
  obtain ⟨hoff, hFl, hGl⟩ := ResUT.flat_mut_own_agree_off hW hM hO hF hG
  have key : ∀ x, (F.get x).map CellUT.erase = (G.get x).map CellUT.erase := fun x => by
    by_cases hx : x = l
    · subst hx; rw [hFl, hGl]; rfl
    · rw [hoff x hx]
  constructor
  · rintro ⟨F₁, hF₁, hμ⟩
    obtain rfl := ResUT.Flat.functional hF₁ hF
    exact ⟨G, hG, fun x => (hμ x).trans (key x)⟩
  · rintro ⟨G₁, hG₁, hμ⟩
    obtain rfl := ResUT.Flat.functional hG₁ hG
    exact ⟨F, hF, fun x => (hμ x).trans (key x).symm⟩

end BoCa.Fig16.Tree.Wp
