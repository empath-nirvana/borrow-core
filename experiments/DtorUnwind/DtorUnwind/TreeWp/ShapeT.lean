import DtorUnwind.TreeWp.Templ

/-!
# The shape lemmas of `Core/Images.lean` at the codes

`Core/Images.lean`'s lemmas about a typed escrow's roots and images (`image_dom`, `own_split`,
`refPos_blocks`, `chain_own`), read at the codes (`1`, `+`, `Imm`, `Mut`, `[a]`, `ref`) with
`T.interp Θ` for `vShape T δ`. Each is the printed induction, on `T` or on the position, at the
codes' clauses. The codes have no `⊗`, so two positions of one value are one position
(`RefPosT.unique`): `refPos_blocks`'s second disjunct does not arise.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-- `ρ₁ ● ℓ ↦ ψ` is `ρ₁` with `ℓ ↦ ψ` inserted, when `ℓ ∉ dom ρ₁`. -/
theorem compS_single_ins {ρ₁ : TRes K} {l : BoCa.Loc} (hl : ρ₁.get l = none) (ψ : TCell K) :
    ResUT.CompS (ResUT.single l ψ) ρ₁ (PMap.ins ρ₁ l ψ) := by
  obtain ⟨X, hX⟩ := (ResUT.compS_defined_iff (ResUT.single l ψ) ρ₁).mpr
    (ResUT.Compat.of_disjoint fun x => by
      by_cases hx : x = l
      · subst hx; exact Or.inr hl
      · exact Or.inl (ResUT.single_get_ne _ hx))
  have e : X = PMap.ins ρ₁ l ψ := PMap.ext fun x => by
    rw [PMap.ins_get]
    by_cases hx : x = l
    · subst hx; rw [if_pos rfl]
      exact (ResUT.Comp.get_of_right_none hX hl).trans (ResUT.single_get_self _ _)
    · rw [if_neg hx]
      exact ResUT.Comp.get_of_left_none hX (ResUT.single_get_ne _ hx)
  rw [← e]; exact hX

/-- An `own` cell of a piece is one of the whole. -/
theorem own_of_le {B R : TRes K} (h : ResUT.Le B R) {l : BoCa.Loc} {u : BoCa.Val}
    (e : B.get l = some (CellUT.ownOf u)) : R.get l = some (CellUT.ownOf u) := by
  obtain ⟨τ, hτ⟩ := h
  exact (ResUT.CompS.get_left_of_ne_imm hτ e (by simp)).2

theorem le_of_compS_right {a b c : TRes K} (h : ResUT.CompS a b c) : ResUT.Le b c :=
  ⟨a, ResUT.CompS.comm h⟩

/-- **Two positions of one value at a code are one position.** -/
theorem RefPosT.unique {T : KTy} {v : BoCa.Val} {l₁ l₂ : BoCa.Loc} {S₁ S₂ : KTy}
    (h₁ : RefPosT T v l₁ S₁) (h₂ : RefPosT T v l₂ S₂) : l₁ = l₂ ∧ S₁ = S₂ := by
  induction h₁ generalizing l₂ S₂ with
  | ref S l => cases h₂; exact ⟨rfl, rfl⟩
  | @sumL T₁ T₂ v₁ l S _ ih =>
      generalize hv : BoCa.Val.inj₁ v₁ = w at h₂
      cases h₂ with
      | sumL h => cases Val.inj₁_inj' hv; exact ih h
      | sumR _ => exact (Val.inj₁_ne_inj₂ hv).elim
  | @sumR T₁ T₂ v₂ l S _ ih =>
      generalize hv : BoCa.Val.inj₂ v₂ = w at h₂
      cases h₂ with
      | sumL _ => exact (Val.inj₁_ne_inj₂ hv.symm).elim
      | sumR h => cases Val.inj₂_inj' hv; exact ih h
  | box _ ih => cases h₂ with
      | box h => exact ih h

/-- **`own_split` at the codes**: at a root, a typed escrow holds `ℓ ↦ own(u) ● P` with `P` of the
pointee's code at `u`, through the `+` and `[a]` clauses to the `ref` clause. -/
theorem own_splitT (Θ : CodeTy) {T : KTy} {v : BoCa.Val} {l : BoCa.Loc} {S : KTy}
    (hp : RefPosT T v l S) :
    ∀ {R : TRes K}, (T.interp Θ).P K v R →
      ∃ u P B, ResUT.CompS (ResUT.single l (CellUT.ownOf u)) P B ∧ (S.interp Θ).P K u P ∧
        ResUT.Le B R := by
  induction hp with
  | ref S l =>
      rintro R ⟨l', w, ρ₁, hv, hl, rfl, hP⟩
      cases hv
      exact ⟨w, ρ₁, _, compS_single_ins hl _, hP, ResUT.Le.refl _⟩
  | sumL _ ih =>
      rintro R (⟨v₁, hv, h⟩ | ⟨v₂, hv, -⟩)
      · cases Val.inj₁_inj' hv; exact ih h
      · exact (Val.inj₁_ne_inj₂ hv).elim
  | sumR _ ih =>
      rintro R (⟨v₁, hv, -⟩ | ⟨v₂, hv, h⟩)
      · exact (Val.inj₁_ne_inj₂ hv.symm).elim
      · cases Val.inj₂_inj' hv; exact ih h
  | box _ ih =>
      rintro R ⟨h, -⟩
      exact ih h

/-- **`chain_own` at the codes**: a chain stays inside every typed piece of its source whose
`own` cells are the escrow's. -/
theorem chain_ownT (Θ : CodeTy) {R : TRes K} {T : KTy} {v : BoCa.Val} {p : Option BoCa.Loc}
    {l : BoCa.Loc} {S : KTy} {u : BoCa.Val} (h : ChainT R T v p l S u) :
    ∀ {P : TRes K}, (T.interp Θ).P K v P →
      (∀ m w, P.get m = some (CellUT.ownOf w) → R.get m = some (CellUT.ownOf w)) →
      P.get l = some (CellUT.ownOf u) := by
  induction h with
  | one hp e =>
      intro P hP hag
      obtain ⟨u', P₀, B, hB, -, hle⟩ := own_splitT Θ hp hP
      have eB := (ResUT.CompS.get_left_of_ne_imm hB (ResUT.single_get_self _ _) (by simp)).2
      have eP := own_of_le hle eB
      rw [hag _ u' eP] at e
      cases Option.some.inj e
      exact eP
  | step hp e₁ _ ih =>
      intro P hP hag
      obtain ⟨u', P₁, B, hB, hP₁, hle⟩ := own_splitT Θ hp hP
      have eB := (ResUT.CompS.get_left_of_ne_imm hB (ResUT.single_get_self _ _) (by simp)).2
      have eP := own_of_le hle eB
      rw [hag _ u' eP] at e₁
      cases Option.some.inj e₁
      have hle₁ : ResUT.Le P₁ P := (le_of_compS_right hB).trans hle
      exact own_of_le hle₁ (ih hP₁ (fun m w e => hag m w (own_of_le hle₁ e)))

/-- **`image_dom` at the codes**: every cell of a typed reborrow image sits over a cell of the
typed escrow, and over an `own` cell only at a root. By induction on the code: `1` gives `∅`;
`+` and `[a]` pass to the component; `ref S` a single cell over `ℓ ↦ own(u)`; `Imm @a S` a single
cell over the `imm` cell; `Mut @a S` a single cell over the `mut` cell. -/
theorem image_domT (Θ : CodeTy) (b : Life) :
    ∀ (T : KTy) {v : BoCa.Val} {c R : TRes K}, ((T.immReborrow b).interp Θ).P K v c →
      (T.interp Θ).P K v R → ∀ {m : BoCa.Loc} {ψ : TCell K}, c.get m = some ψ →
      ∃ ζ, R.get m = some ζ ∧ (ζ.kind = Kind.own → ∃ S, RefPosT T v m S) := by
  intro T
  induction T with
  | unit =>
      rintro v c R ⟨-, rfl⟩ - m ψ e
      simp at e
  | sum A B ihA ihB =>
      rintro v c R (⟨v₁, hv, hc⟩ | ⟨v₂, hv, hc⟩) hR m ψ e
      · subst hv
        rcases hR with ⟨v₁', hv', hR⟩ | ⟨v₂', hv', -⟩
        · cases Val.inj₁_inj' hv'
          obtain ⟨ζ, eζ, hζ⟩ := ihA hc hR e
          exact ⟨ζ, eζ, fun k => let ⟨S, hS⟩ := hζ k; ⟨S, RefPosT.sumL hS⟩⟩
        · exact (Val.inj₁_ne_inj₂ hv').elim
      · subst hv
        rcases hR with ⟨v₁', hv', -⟩ | ⟨v₂', hv', hR⟩
        · exact (Val.inj₁_ne_inj₂ hv'.symm).elim
        · cases Val.inj₂_inj' hv'
          obtain ⟨ζ, eζ, hζ⟩ := ihB hc hR e
          exact ⟨ζ, eζ, fun k => let ⟨S, hS⟩ := hζ k; ⟨S, RefPosT.sumR hS⟩⟩
  | imm a A _ =>
      rintro v c R ⟨l, i, rfl, rfl, -⟩ ⟨l', i', hv, rfl, -⟩ m ψ e
      cases hv
      rw [PMap.sng_get] at e
      split_ifs at e with hm
      subst hm
      exact ⟨CellUT.imm i', by simp [PMap.sng_get], fun k => by simp [CellUT.kind] at k⟩
  | «mut» a A _ =>
      rintro v c R ⟨l, i, rfl, rfl, -⟩ ⟨l', m', hv, rfl, -⟩ m ψ e
      cases hv
      rw [PMap.sng_get] at e
      split_ifs at e with hm
      subst hm
      exact ⟨CellUT.mut m', by simp [PMap.sng_get], fun k => by simp [CellUT.kind] at k⟩
  | box a A ih =>
      rintro v c R hc ⟨hR, -⟩ m ψ e
      obtain ⟨ζ, eζ, hζ⟩ := ih hc hR e
      exact ⟨ζ, eζ, fun k => let ⟨S, hS⟩ := hζ k; ⟨S, RefPosT.box hS⟩⟩
  | ref A _ =>
      rintro v c R ⟨l, i, rfl, rfl, -⟩ ⟨l', w, ρ₁, hv, hl, rfl, -⟩ m ψ e
      cases hv
      rw [PMap.sng_get] at e
      split_ifs at e with hm
      subst hm
      exact ⟨CellUT.own w, by simp [PMap.ins_get], fun _ => ⟨A, RefPosT.ref A m⟩⟩

end BoCa.Fig16.Tree.Wp

end
