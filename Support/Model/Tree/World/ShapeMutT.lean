import Support.Model.Tree.World.InvMid

/-!
# The image and `Mut`-position lemmas of `Core/Images.lean` and `Core/Invariant.lean` at the codes

`[spec §62]`. `image_at_pos`, `typed_image_pos` (`Core/Images.lean`), `image_dom_mut`, `mut_split_den`,
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

/-! ### Sub-records -/

/-- A `Mut` position is one position: the codes have no `⊗`. -/
theorem MutPosT.unique {T : KTy} {v : BoCa.Val} {l₁ l₂ : BoCa.Loc} {S₁ S₂ : KTy}
    (h₁ : MutPosT T v l₁ S₁) (h₂ : MutPosT T v l₂ S₂) : l₁ = l₂ ∧ S₁ = S₂ := by
  induction h₁ generalizing l₂ S₂ with
  | «mut» a S l => cases h₂; exact ⟨rfl, rfl⟩
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

/-- A `Mut` position and a `ref` position of one value are not both: at the codes a value's
positions follow one path through `+` and `[a]`. -/
theorem MutPosT.not_refPos {T : KTy} {v : BoCa.Val} {m l : BoCa.Loc} {S S' : KTy}
    (h₁ : MutPosT T v m S) (h₂ : RefPosT T v l S') : False := by
  induction h₁ generalizing l S' with
  | «mut» a S l => cases h₂
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

/-- **`gpos_unique` at the codes.** The printed proof's two crossing cases (`gpos_cross`) and
`refPos_blocks`'s second disjunct do not arise: a value's `Mut` and `ref` positions are one path
(`MutPosT.not_refPos`, `RefPosT.unique`). -/
theorem gpos_uniqueT (Θ : CodeTy) {R : TRes K} {T : KTy} {v : BoCa.Val} {m : BoCa.Loc}
    {S₁ : KTy} (h₁ : GPosT R T v m S₁) :
    ∀ {P : TRes K}, (T.interp Θ).P K v P →
      (∀ x w, P.get x = some (CellUT.ownOf w) → R.get x = some (CellUT.ownOf w)) →
      ∀ {S₂ : KTy}, GPosT R T v m S₂ → S₁ = S₂ := by
  induction h₁ with
  | @here T v m S₁ hp₁ =>
      intro P hP hag S₂ h₂
      cases h₂ with
      | here hp₂ => exact (MutPosT.unique hp₁ hp₂).2
      | step hr _ _ => exact (MutPosT.not_refPos hp₁ hr).elim
  | @step T v l₁ S₀ u₀ m S₁ hp₁ e₁ t₁ ih =>
      intro P hP hag S₂ h₂
      cases h₂ with
      | here hp₂ => exact (MutPosT.not_refPos hp₂ hp₁).elim
      | @step _ _ l₂ S₀' u₀' _ _ hp₂ e₂ t₂ =>
          obtain ⟨rfl, rfl⟩ := RefPosT.unique hp₁ hp₂
          rw [e₁] at e₂; cases Option.some.inj e₂
          obtain ⟨w, Q, B, hB, hQ, hle⟩ := own_splitT Θ hp₁ hP
          have eP := own_of_le hle
            (ResUT.CompS.get_left_of_ne_imm hB (ResUT.single_get_self _ _) (by simp)).2
          rw [hag l₁ w eP] at e₁; cases Option.some.inj e₁
          have hleQ : ResUT.Le Q P := ResUT.Le.trans (le_of_compS_right hB) hle
          exact ih hQ (fun x w e' => hag x w (own_of_le hleQ e')) t₂

/-- A sub-record of a typed record is typed: the `mut` cell's witness at the pointee's code. -/
theorem SubRecT.typed {Θ : CodeTy} {r d : FrameRecT K} (h : SubRecT r d)
    (hR : (r.T.interp Θ).P K r.v r.R) : (d.T.interp Θ).P K d.v d.R := by
  obtain ⟨hg, ζ, eζ, -, rζ, wζ⟩ := h
  obtain ⟨ζ', eζ', -, dζ'⟩ := gpos_mut_cellT Θ hg hR (fun _ _ e => e)
  rw [eζ] at eζ'; cases Option.some.inj eζ'
  rw [← rζ, ← wζ]; exact dζ'

theorem LinPathT.typed {Θ : CodeTy} {r d : FrameRecT K} {p : List BoCa.Loc} (h : LinPathT r p d)
    (hR : (r.T.interp Θ).P K r.v r.R) : (d.T.interp Θ).P K d.v d.R := by
  induction h with
  | nil r => exact hR
  | cons hs _ ih => exact ih (hs.typed hR)

theorem FrameRecT.ext' {a b : FrameRecT K} (h₁ : a.le = b.le) (h₂ : a.v = b.v) (h₃ : a.R = b.R)
    (h₄ : a.T = b.T) : a = b := by
  cases a; cases b; simp_all

/-- Two sub-records of a typed record at one location are one. -/
theorem SubRecT.functional {Θ : CodeTy} {r d₁ d₂ : FrameRecT K}
    (hR : (r.T.interp Θ).P K r.v r.R) (h₁ : SubRecT r d₁) (h₂ : SubRecT r d₂)
    (he : d₁.le = d₂.le) : d₁ = d₂ := by
  obtain ⟨hg₁, ζ₁, e₁, -, r₁, w₁⟩ := h₁
  obtain ⟨hg₂, ζ₂, e₂, -, r₂, w₂⟩ := h₂
  rw [he, e₂] at e₁; cases Option.some.inj e₁
  rw [he] at hg₁
  exact FrameRecT.ext' he (r₁.symm.trans r₂) (w₁.symm.trans w₂)
    (gpos_uniqueT Θ hg₁ hR (fun _ _ e => e) hg₂)

/-- A lineage path names one record. -/
theorem LinPathT.functional {Θ : CodeTy} {r d₁ : FrameRecT K} {p : List BoCa.Loc}
    (h₁ : LinPathT r p d₁) :
    (r.T.interp Θ).P K r.v r.R → ∀ {d₂ : FrameRecT K}, LinPathT r p d₂ → d₁ = d₂ := by
  induction h₁ with
  | nil r => intro _ d₂ h₂; exact (h₂.inv_nil).symm
  | @cons r d e p hs _ ih =>
      intro hR d₂ h₂
      obtain ⟨d', hs', hle, t'⟩ := h₂.inv_cons
      have hdd : d = d' := SubRecT.functional hR hs hs' hle.symm
      subst hdd
      exact ih (hs.typed hR) t'

end BoCa.Fig16.Tree.Wp

end
