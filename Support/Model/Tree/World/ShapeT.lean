import Support.Model.Tree.World.Templ

/-!
# The shape lemmas of `Core/Images.lean` at the codes

`[spec §62]`. `Core/Images.lean`'s lemmas about a typed escrow's roots and images (`image_dom`, `own_split`,
`refPos_blocks`, `chain_own`), read at the codes (`1`, `+`, `Imm`, `Mut`, `[a]`, `ref`) with
`T.interp Θ` for `vShape T δ`. Each is the printed induction, on `T` or on the position, at the
codes' clauses. The codes have no `⊗`, so two positions of one value are one position
(`RefPosT.unique`): `refPos_blocks`'s second disjunct does not arise, and `chain_uniqueT` is
`chain_unique`'s induction with that disjunct's cases absent. `ChainT.own`, `ChainT.snoc` and
`chain_lastT` are the printed ones at `ChainT`.
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

theorem ChainT.own {R : TRes K} {T : KTy} {v : BoCa.Val} {p : Option BoCa.Loc} {l : BoCa.Loc}
    {S : KTy} {u : BoCa.Val} (h : ChainT R T v p l S u) : R.get l = some (CellUT.ownOf u) := by
  induction h with
  | one _ e => exact e
  | step _ _ _ ih => exact ih

/-- Extending a chain by one `RefPosT` step of its last pointee. -/
theorem ChainT.snoc {R : TRes K} {T : KTy} {v : BoCa.Val} {p : Option BoCa.Loc} {l₀ : BoCa.Loc}
    {S₀ : KTy} {u₀ : BoCa.Val} (h : ChainT R T v p l₀ S₀ u₀) {l : BoCa.Loc} {S : KTy}
    {u : BoCa.Val} (hp : RefPosT S₀ u₀ l S) (e : R.get l = some (CellUT.ownOf u)) :
    ChainT R T v (some l₀) l S u := by
  induction h with
  | one h₁ e₁ => exact ChainT.step h₁ e₁ (ChainT.one hp e)
  | step h₁ e₁ _ ih => exact ChainT.step h₁ e₁ (ih hp)

/-- **`chain_unique` at the codes**: a location is reached by at most one chain, one parent and
one pointee code. The printed proof's case split on two first steps (`refPos_blocks`) has one
case at the codes, the steps being one position (`RefPosT.unique`); a chain through a first step
stays inside that step's piece (`chain_ownT`). -/
theorem chain_uniqueT (Θ : CodeTy) {R : TRes K} {T : KTy} {v : BoCa.Val} {p₁ : Option BoCa.Loc}
    {l : BoCa.Loc} {S₁ : KTy} {u₁ : BoCa.Val} (h₁ : ChainT R T v p₁ l S₁ u₁) :
    ∀ {P : TRes K}, (T.interp Θ).P K v P →
      (∀ m w, P.get m = some (CellUT.ownOf w) → R.get m = some (CellUT.ownOf w)) →
      ∀ {p₂ : Option BoCa.Loc} {S₂ : KTy} {u₂ : BoCa.Val}, ChainT R T v p₂ l S₂ u₂ →
        p₁ = p₂ ∧ S₁ = S₂ := by
  induction h₁ with
  | @one T v l S₁ u₁ hp₁ e₁ =>
      intro P hP hag p₂ S₂ u₂ h₂
      cases h₂ with
      | one hp₂ e₂ => exact ⟨rfl, (RefPosT.unique hp₁ hp₂).2⟩
      | @step _ _ l₁' S₁' u₁' p' _ _ _ hp₂ e₂ t₂ =>
          obtain ⟨rfl, rfl⟩ := RefPosT.unique hp₁ hp₂
          obtain ⟨w, Q, B, hB, hQ, hle⟩ := own_splitT Θ hp₁ hP
          have eP := own_of_le hle
            (ResUT.CompS.get_left_of_ne_imm hB (ResUT.single_get_self _ _) (by simp)).2
          rw [hag _ w eP] at e₂; cases Option.some.inj e₂
          have hleQ : ResUT.Le Q P := (le_of_compS_right hB).trans hle
          have eQ := chain_ownT Θ t₂ hQ (fun m w e => hag m w (own_of_le hleQ e))
          have := ResUT.CompatS.right_eq_none hB.1 (ResUT.single_get_self _ _) (by simp)
          rw [eQ] at this; cases this
  | @step T v l₁ S₁ u₁ p l S u hp₁ e₁ t₁ ih =>
      intro P hP hag p₂ S₂ u₂ h₂
      cases h₂ with
      | one hp₂ e₂ =>
          obtain ⟨rfl, rfl⟩ := RefPosT.unique hp₂ hp₁
          obtain ⟨w, Q, B, hB, hQ, hle⟩ := own_splitT Θ hp₂ hP
          have eP := own_of_le hle
            (ResUT.CompS.get_left_of_ne_imm hB (ResUT.single_get_self _ _) (by simp)).2
          rw [hag _ w eP] at e₁; cases Option.some.inj e₁
          have hleQ : ResUT.Le Q P := (le_of_compS_right hB).trans hle
          have eQ := chain_ownT Θ t₁ hQ (fun m w e => hag m w (own_of_le hleQ e))
          have := ResUT.CompatS.right_eq_none hB.1 (ResUT.single_get_self _ _) (by simp)
          rw [eQ] at this; cases this
      | @step _ _ l₁' S₁' u₁' p' _ _ _ hp₂ e₂ t₂ =>
          obtain ⟨rfl, rfl⟩ := RefPosT.unique hp₁ hp₂
          rw [e₁] at e₂; cases Option.some.inj e₂
          obtain ⟨w, Q, B, hB, hQ, hle⟩ := own_splitT Θ hp₁ hP
          have eP := own_of_le hle
            (ResUT.CompS.get_left_of_ne_imm hB (ResUT.single_get_self _ _) (by simp)).2
          rw [hag _ w eP] at e₁; cases Option.some.inj e₁
          have hleQ : ResUT.Le Q P := (le_of_compS_right hB).trans hle
          obtain ⟨hp, hS⟩ := ih hQ (fun m w e => hag m w (own_of_le hleQ e)) t₂
          subst hp; exact ⟨rfl, hS⟩

/-- The last step of a chain with a parent. -/
theorem chain_lastT {R : TRes K} {T : KTy} {v : BoCa.Val} {p : Option BoCa.Loc} {l : BoCa.Loc}
    {S : KTy} {u : BoCa.Val} (h : ChainT R T v p l S u) :
    ∀ l₀, p = some l₀ → ∃ p₀ S₀ u₀, ChainT R T v p₀ l₀ S₀ u₀ ∧ RefPosT S₀ u₀ l S := by
  induction h with
  | one _ _ => intro l₀ e; cases e
  | @step T v l₁ S₁ u₁ p l S u hp e₁ t ih =>
      intro l₀ e
      cases p with
      | none =>
          simp only [Option.getD_none, Option.some.injEq] at e
          subst e
          cases t with
          | one hp' _ => exact ⟨none, S₁, u₁, ChainT.one hp e₁, hp'⟩
      | some l₀' =>
          simp only [Option.getD_some, Option.some.injEq] at e
          subst e
          obtain ⟨p₀, S₀, u₀, hc, hr⟩ := ih l₀' rfl
          exact ⟨_, S₀, u₀, ChainT.step hp e₁ hc, hr⟩

end BoCa.Fig16.Tree.Wp

end
