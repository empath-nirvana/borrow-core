import DtorUnwind.TreeWp.InvMid

/-!
# The image and `Mut`-position lemmas of `Core/Images.lean` and `Core/Invariant.lean` at the codes

`image_at_pos`, `typed_image_pos` (`Core/Images.lean`), `image_dom_mut`, `mut_split_den`,
`GPos.of_chain`, `gpos_mut_cell` (`Core/Invariant.lean`), read at the codes (`1`, `+`, `Imm`,
`Mut`, `[a]`, `ref`) with `T.interp Θ` for `vShape T δ` and `T.immReborrow β` for
`vShape (T.immReborrow (.var x)) (δ.extend x β)`. Each is the printed induction, on the position
or on the code, at the codes' clauses; a code names its lifetimes, so the printed `¬ VFree x T`
side conditions do not arise.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-- **`image_at_pos` at the codes**: at a root, a typed reborrow image has an `imm` cell whose
witness is typed at the pointee's code. -/
theorem image_at_posT (Θ : CodeTy) {T : KTy} {v : BoCa.Val} {l : BoCa.Loc} {S : KTy}
    (hp : RefPosT T v l S) {β : Life} :
    ∀ {c : TRes K}, ((T.immReborrow β).interp Θ).P K v c →
      ∃ ψ, c.get l = some ψ ∧ ψ.kind = Kind.imm ∧ (S.interp Θ).P K ψ.erase ψ.wit := by
  induction hp with
  | ref S l =>
      rintro c ⟨l', i, hv, rfl, -, hP⟩
      cases hv
      exact ⟨.imm i, by simp [PMap.sng_get], rfl, hP⟩
  | sumL _ ih =>
      rintro c (⟨v₁, hv, h⟩ | ⟨v₂, hv, -⟩)
      · cases Val.inj₁_inj' hv; exact ih h
      · exact (Val.inj₁_ne_inj₂ hv).elim
  | sumR _ ih =>
      rintro c (⟨v₁, hv, -⟩ | ⟨v₂, hv, h⟩)
      · exact (Val.inj₁_ne_inj₂ hv.symm).elim
      · cases Val.inj₂_inj' hv; exact ih h
  | box _ ih => intro c hc; exact ih hc

/-- **`typed_image_pos` at the codes**: at a root `ℓ ↦ own(u)` of `σ`, a typed
`c ∈ reb_β(σ)` has `c(ℓ) = imm({β}, u, q/ℓ)` for a piece `q ≤ σ` holding `ℓ`, and `q/ℓ` is
typed at the pointee's code. -/
theorem typed_image_posT (Θ : CodeTy) {T S : KTy} {σ c : TRes K} {v : BoCa.Val} {l : BoCa.Loc}
    {u : BoCa.Val} {β : Life} (hp : RefPosT T v l S)
    (hown : σ.get l = some (CellUT.ownOf u)) (hr : ResUT.Reb β σ c)
    (ht : ((T.immReborrow β).interp Θ).P K v c) :
    ∃ (q : TRes K) (h : (q.del l).InStratum (TSet.single β)),
      c.get l = some (CellUT.immOf (TSet.single β) u (q.del l) h) ∧
      ResUT.Le q σ ∧ (∃ ψ, q.get l = some ψ) ∧ (S.interp Θ).P K u (q.del l) := by
  obtain ⟨ψ, eψ, -, hd⟩ := image_at_posT Θ hp ht
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨_, eψ⟩)
  simp only at hpl
  subst hpl
  have hq := hbody l₀ q hpm
  obtain ⟨hh, he⟩ := hq.2.1 u hown
  rw [eψ] at he
  cases Option.some.inj he
  refine ⟨q, hh, eψ, ResUT.Le.trans (bigCompS_le hbig (List.mem_map.mpr ⟨_, hpm, rfl⟩)) hle,
    hq.1, ?_⟩
  simpa using hd

/-- **`image_dom_mut` at the codes**: a typed reborrow's cell over a `mut` cell of the escrow
sits at a `Mut` position. -/
theorem image_dom_mutT (Θ : CodeTy) (b : Life) :
    ∀ (T : KTy) {v : BoCa.Val} {c R : TRes K}, ((T.immReborrow b).interp Θ).P K v c →
      (T.interp Θ).P K v R → ∀ {m : BoCa.Loc} {ψ : TCell K}, c.get m = some ψ →
      ∀ {ζ : TCell K}, R.get m = some ζ → ζ.kind = Kind.mut → ∃ S, MutPosT T v m S := by
  intro T
  induction T with
  | unit =>
      rintro v c R ⟨-, rfl⟩ - m ψ e
      simp at e
  | sum A B ihA ihB =>
      rintro v c R (⟨v₁, hv, hc⟩ | ⟨v₂, hv, hc⟩) hR m ψ e ζ eζ kζ
      · subst hv
        rcases hR with ⟨v₁', hv', hR⟩ | ⟨v₂', hv', -⟩
        · cases Val.inj₁_inj' hv'
          obtain ⟨S, hS⟩ := ihA hc hR e eζ kζ
          exact ⟨S, .sumL hS⟩
        · exact (Val.inj₁_ne_inj₂ hv').elim
      · subst hv
        rcases hR with ⟨v₁', hv', -⟩ | ⟨v₂', hv', hR⟩
        · exact (Val.inj₁_ne_inj₂ hv'.symm).elim
        · cases Val.inj₂_inj' hv'
          obtain ⟨S, hS⟩ := ihB hc hR e eζ kζ
          exact ⟨S, .sumR hS⟩
  | imm a A _ =>
      rintro v c R - ⟨l, i, rfl, rfl, -, -⟩ m ψ - ζ eζ kζ
      rw [PMap.sng_get] at eζ
      split_ifs at eζ
      cases eζ; cases kζ
  | «mut» a A _ =>
      rintro v c R ⟨l', i, hv, rfl, -, -⟩ ⟨l, m', rfl, rfl, -, -, -⟩ m ψ e ζ eζ kζ
      cases hv
      rw [PMap.sng_get] at e
      split_ifs at e with hm
      subst hm
      exact ⟨A, .mut a A _⟩
  | box a A ih =>
      rintro v c R hc ⟨hR, -⟩ m ψ e ζ eζ kζ
      obtain ⟨S, hS⟩ := ih hc hR e eζ kζ
      exact ⟨S, .box hS⟩
  | ref A _ =>
      classical
      rintro v c R ⟨l', i, hv, rfl, -, -⟩ ⟨l, w, ρ₁, rfl, -, rfl, -⟩ m ψ e ζ eζ kζ
      cases hv
      rw [PMap.sng_get] at e
      split_ifs at e with hm
      subst hm
      rw [PMap.ins_get, if_pos rfl] at eζ
      cases eζ; cases kζ

/-- **`mut_split_den` at the codes**: at a `Mut` position a typed escrow holds a `mut` cell whose
witness is typed at the pointee's code. -/
theorem mut_split_denT (Θ : CodeTy) {T : KTy} {v : BoCa.Val} {m : BoCa.Loc} {S : KTy}
    (hp : MutPosT T v m S) :
    ∀ {R : TRes K}, (T.interp Θ).P K v R →
      ∃ ζ : TCell K, R.get m = some ζ ∧ ζ.kind = Kind.mut ∧ (S.interp Θ).P K ζ.erase ζ.wit := by
  induction hp with
  | «mut» a S l =>
      rintro R ⟨l', m', hv, rfl, -, -, hP⟩
      cases hv
      exact ⟨.mut m', by simp [PMap.sng_get], rfl, (hP m'.v m'.ρ).mp m'.hw⟩
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

theorem GPosT.of_chain {R : TRes K} {T : KTy} {v : BoCa.Val} {p : Option BoCa.Loc}
    {l₀ : BoCa.Loc} {S₀ : KTy} {u₀ : BoCa.Val} (h : ChainT R T v p l₀ S₀ u₀) {m : BoCa.Loc}
    {S : KTy} (hm : MutPosT S₀ u₀ m S) : GPosT R T v m S := by
  induction h with
  | one hp e => exact GPosT.step hp e (GPosT.here hm)
  | step hp e _ ih => exact GPosT.step hp e (ih hm)

/-- **`gpos_mut_cell` at the codes**: at a `GPos` a typed piece holds the `mut` cell, its witness
typed at the pointee's code. -/
theorem gpos_mut_cellT (Θ : CodeTy) {R : TRes K} {T : KTy} {v : BoCa.Val} {m : BoCa.Loc}
    {S : KTy} (h : GPosT R T v m S) :
    ∀ {P : TRes K}, (T.interp Θ).P K v P →
      (∀ x w, P.get x = some (CellUT.ownOf w) → R.get x = some (CellUT.ownOf w)) →
      ∃ ζ : TCell K, P.get m = some ζ ∧ ζ.kind = Kind.mut ∧ (S.interp Θ).P K ζ.erase ζ.wit := by
  induction h with
  | here hp => intro P hP _; exact mut_split_denT Θ hp hP
  | @step T v l S₀ u₀ m S hp e _ ih =>
      intro P hP hag
      obtain ⟨u', Q, B, hB, hQ, hle⟩ := own_splitT Θ hp hP
      have eB := (ResUT.CompS.get_left_of_ne_imm hB (ResUT.single_get_self _ _) (by simp)).2
      have eP := own_of_le hle eB
      rw [hag l u' eP] at e
      cases Option.some.inj e
      have hleQ : ResUT.Le Q P := ResUT.Le.trans (le_of_compS_right hB) hle
      obtain ⟨ζ, eζ, kζ, dζ⟩ := ih hQ (fun x w e' => hag x w (own_of_le hleQ e'))
      obtain ⟨τ, hτ⟩ := hleQ
      exact ⟨ζ, (ResUT.CompS.get_left_of_ne_imm hτ eζ (by rw [kζ]; simp)).2, kζ, dζ⟩

end BoCa.Fig16.Tree.Wp

end
