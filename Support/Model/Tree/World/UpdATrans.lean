import Support.Model.Tree.World.RecMask

/-!
# `UpdA` across two segments: the ancestor's walk re-read  `[spec §62]`

The pieces `UpdA.trans` reads at an ancestor (`docs/new-core/scope-806.md`, appendix):

* **An ancestor's walk re-reads with its witness** (`walk_rr`): when `RR ζ.wit χ.wit`, the
  `⦇−⦈_○` of `χ.wit` is the cell-by-cell re-reading of `ζ.wit`'s (`ExW.lsSim`, `AgW.lsSim`,
  `lsRSim_comp`, and the walks' functionality). So a `Beneath` at the middle pulls back to the
  start's ancestor over a re-read cell (`Beneath.rr_back`).
* **An `imm` cell of a flattening carries its walk** (`flat_beneath_nonown`): every non-`own` cell
  of the walk at `n` gives the flattening a non-`own` cell at `n` (`ResUT.flat_imm_wit_factor`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-! ### The walk of a re-read witness -/

/-- **`⦇−⦈_○` re-reads with the resource.** -/
theorem walk_rr {Θ : LocTy} (hE : K.Ext K') {ω : TRes K} {ω' : TRes K'} (hr : RR Θ ω ω')
    {ev av p : TRes K} (hev : ExRT ω ev) (hav : AgWT ω av) (hp : ResUT.CompR ev av p)
    {ev' av' p' : TRes K'} (hev' : ExRT ω' ev') (hav' : AgWT ω' av')
    (hp' : ResUT.CompR ev' av' p') : LsRSim Θ p' p := by
  have hR' : ∀ ψ₁ ψ₂ ψ, CellUT.CompR (K := K') (Loc := BoCa.Loc) (Val := BoCa.Val) ψ₁ ψ₂ ψ →
      CellUT.CompatR ψ₁ ψ₂ := fun _ _ ψ hc => ⟨ψ, hc⟩
  have hC : ∀ {ψ₁ ψ₂ ψ : TCell K} {ψ₁' ψ₂' : TCell K'},
      LsSim Θ ψ₁' ψ₁ → LsSim Θ ψ₂' ψ₂ → CellUT.CompR ψ₁ ψ₂ ψ →
      ∃ ψ', CellUT.CompR ψ₁' ψ₂' ψ' ∧ LsSim Θ ψ' ψ := fun a b c => lsSim_compR hE a b c
  obtain ⟨ev₁, hev₁, hs₁⟩ := ExW.lsSim hR' hC hev ω' hr.lsRSim
  obtain rfl := ExRT.functional hev₁ hev'
  obtain ⟨av₁, hav₁, hs₂⟩ := AgW.lsSim hE hav ω' hr.lsRSim
  obtain rfl := AgWT.functional hav₁ hav'
  obtain ⟨p₁, hp₁, hs₃⟩ := lsRSim_comp hR' hC hs₁ hs₂ hp
  obtain rfl := ResUT.CompR.functional hp₁ hp'
  exact hs₃

/-- **A `Beneath` at the end of a re-reading pulls back** to a start ancestor whose witness
re-reads to the end ancestor's, over a cell the end cell re-reads. -/
theorem Beneath.rr_back {Θ : LocTy} (hE : K.Ext K') {σ : TRes K} {σ' : TRes K'} {m n : BoCa.Loc}
    {ζ : TCell K} {ζ' ξ' : TCell K'} (h : Beneath σ' m ζ' n ξ') (e : σ.get m = some ζ)
    (hk : ζ.kind = Kind.imm) (hr : RR Θ ζ.wit ζ'.wit)
    (hw : ∃ ev av p, ExRT ζ.wit ev ∧ AgWT ζ.wit av ∧ ResUT.CompR ev av p) :
    ∃ ξ, Beneath σ m ζ n ξ ∧ LsSim Θ ξ' ξ := by
  obtain ⟨-, -, ev', av', p', hev', hav', hp', hn⟩ := h
  obtain ⟨ev, av, p, hev, hav, hp⟩ := hw
  have hs := walk_rr hE hr hev hav hp hev' hav' hp' n
  rw [hn] at hs
  cases hq : p.get n with
  | none => rw [hq] at hs; cases hs
  | some ξ =>
      rw [hq] at hs
      cases hs with
      | some h' => exact ⟨ξ, ⟨e, hk, ev, av, p, hev, hav, hp, hq⟩, h'⟩

/-! ### An `imm` cell of a flattening carries its walk -/

/-- **The walk of an `imm` cell of a flattening exists, as a `○`-factor of the aliasable walk.** -/
theorem flat_imm_walk {ρ τ : TRes K} (hτ : ResUT.Flat ρ τ) {m : BoCa.Loc} {χ : TCell K}
    (e : τ.get m = some χ) (hk : χ.kind = Kind.imm) :
    ∃ a ev av p z, AgWT ρ a ∧ ExRT χ.wit ev ∧ AgWT χ.wit av ∧ ResUT.CompR ev av p ∧
      ResUT.CompR p z a := by
  obtain ⟨eρ, a, he, ha, hc⟩ := hτ
  obtain ⟨s, hs, heta⟩ := CellUT.imm_eta hk
  rw [heta] at e
  obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := ResUT.flat_imm_wit_factor he ha hc e
  exact ⟨a, ev, av, p, z, ha, hev, hav, hp, hz⟩

/-- **A non-`own` cell of an `imm` cell's walk gives the flattening a non-`own` cell there.** -/
theorem flat_beneath_nonown {ρ τ : TRes K} (hτ : ResUT.Flat ρ τ) {m n : BoCa.Loc} {χ ξ : TCell K}
    (e : τ.get m = some χ) (hk : χ.kind = Kind.imm) {ev av p : TRes K} (hev : ExRT χ.wit ev)
    (hav : AgWT χ.wit av) (hp : ResUT.CompR ev av p) (hn : p.get n = some ξ)
    (hkn : ξ.kind ≠ Kind.own) : ∃ ψ, τ.get n = some ψ ∧ ψ.kind ≠ Kind.own := by
  obtain ⟨a, ev₀, av₀, p₀, z, ha, hev₀, hav₀, hp₀, hz⟩ := flat_imm_walk hτ e hk
  obtain rfl := ExRT.functional hev hev₀
  obtain rfl := AgWT.functional hav hav₀
  obtain rfl := ResUT.CompR.functional hp hp₀
  obtain ⟨eρ, a', he, ha', hc⟩ := hτ
  obtain rfl := AgWT.functional ha ha'
  have hna : ∃ φ, a.get n = some φ ∧ φ.kind ≠ Kind.own := by
    rcases G.Comp.get hz n with ⟨f, -, -⟩ | ⟨φ, f₁, -, f⟩ | ⟨φ, f₁, -, -⟩ |
        ⟨φ₁, φ₂, φ, f₁, -, f, hC⟩
    · rw [hn] at f; cases f
    · rw [hn] at f₁; cases f₁; exact ⟨_, f, hkn⟩
    · rw [hn] at f₁; cases f₁
    · rw [hn] at f₁; cases f₁
      refine ⟨φ, f, ?_⟩
      rw [CellUT.CompR.kind_eq hC]
      cases h₁ : ξ.kind <;> cases h₂ : φ₂.kind <;> simp_all [kcomb]
  obtain ⟨φ, eφ, kφ⟩ := hna
  rcases G.Comp.get hc n with ⟨-, f, -⟩ | ⟨ψ, -, f, -⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, -, f₂, f, hC⟩
  · rw [eφ] at f; cases f
  · rw [eφ] at f; cases f
  · rw [eφ] at f₂; cases f₂; exact ⟨_, f, kφ⟩
  · refine ⟨ψ, f, ?_⟩
    rw [CellUT.CompS.kind hC]; exact fun c => Kind.noConfusion c

/-! ### A view of the aliasable walk is a view at depth -/

/-- An `imm` cell of `○` comes from an `imm` operand over the same witness. -/
theorem back_imm {a₁ a₂ a : TRes K} (h : ResUT.CompR a₁ a₂ a) {l : BoCa.Loc} {ψ : TCell K}
    (e : a.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    (∃ ψ₁, a₁.get l = some ψ₁ ∧ ψ₁.kind = Kind.imm ∧ ψ₁.wit = ψ.wit) ∨
    (∃ ψ₂, a₂.get l = some ψ₂ ∧ ψ₂.kind = Kind.imm ∧ ψ₂.wit = ψ.wit) := by
  rcases G.Comp.get h l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hc⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, hk, rfl⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, hk, rfl⟩
  · rw [e'] at e; cases e
    rcases CellUT.CompR.imm_operand hc hk with k | k
    · exact Or.inl ⟨_, e₁, k, (CellUT.CompR.immLe_left hc k).2.2.2.1.symm⟩
    · exact Or.inr ⟨_, e₂, k, (CellUT.CompR.immLe_right hc k).2.2.2.1.symm⟩

/-- The same along `⨀`. -/
theorem bigComp_back_imm {xs : List (TRes K)} {b : TRes K}
    (h : BigCompT CellUT.CompatR CellUT.CompR xs b) {l : BoCa.Loc} {ψ : TCell K}
    (e : b.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ x ∈ xs, ∃ ψ', x.get l = some ψ' ∧ ψ'.kind = Kind.imm ∧ ψ'.wit = ψ.wit := by
  induction h generalizing ψ with
  | nil => rw [PMap.empty_get] at e; cases e
  | @cons σ τ ρ σs _ hc ih =>
      rcases back_imm hc e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
      · exact ⟨σ, List.mem_cons_self .., ψ₁, e₁, k₁, w₁⟩
      · obtain ⟨x, hx, ψ', e', k', w'⟩ := ih e₁ k₁
        exact ⟨x, List.mem_cons_of_mem _ hx, ψ', e', k', w'.trans w₁⟩

/-- **An `imm` cell of `ag(ρ)` is over the witness of an `imm` cell at depth of `ρ`.** -/
theorem agW_imm_cellAt {ρ σ : TRes K} (h : AgWT ρ σ) :
    ∀ x (ψ : TCell K), σ.get x = some ψ → ψ.kind = Kind.imm →
      ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.kind = Kind.imm ∧ ψ₀.wit = ψ.wit := by
  refine G.AgW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : TCell K), σ.get x = some ψ →
      ψ.kind = Kind.imm → ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.kind = Kind.imm ∧ ψ₀.wit = ψ.wit)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ x (ψ : TCell K), q.2.get x = some ψ →
      ψ.kind = Kind.imm → ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.kind = Kind.imm ∧ ψ₀.wit = ψ.wit)
    (motive_3 := fun ρ w _ => ∀ q ∈ w, ∀ x (ψ : TCell K), q.2.get x = some ψ →
      ψ.kind = Kind.imm → ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.kind = Kind.imm ∧ ψ₀.wit = ψ.wit)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi x ψ e hk
    rcases back_imm hσ e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
    · rcases back_imm ha e₁ k₁ with ⟨ψ₂, e₂, k₂, w₂⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
      · exact ⟨ψ₂, .top (ResUT.restrict_eq_some.mp e₂).1, k₂, w₂.trans w₁⟩
      · obtain ⟨τ, hτ, ψ', e', k', w'⟩ := bigComp_back_imm hbm e₂ k₂
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
        obtain ⟨ψ₀, c₀, k₀, w₀⟩ := ihm q hq x ψ' e' k'
        exact ⟨ψ₀, c₀, k₀, w₀.trans (w'.trans (w₂.trans w₁))⟩
    · obtain ⟨τ, hτ, ψ', e', k', w'⟩ := bigComp_back_imm hbi e₁ k₁
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
      obtain ⟨ψ₀, c₀, k₀, w₀⟩ := ihi q hq x ψ' e' k'
      exact ⟨ψ₀, c₀, k₀, w₀.trans (w'.trans w₁)⟩
  case nilM => intro ρ' q hq; exact absurd hq (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro x φ ex kx
      obtain ⟨ψ₀, c₀, k₀, w₀⟩ := ihe x φ ex kx
      exact ⟨ψ₀, .nest hψ c₀, k₀, w₀⟩
    · exact ihw q hq'
  case nilI => intro ρ' q hq; exact absurd hq (by simp)
  case consI =>
    intro ρ' pe l w ψ hψ hk e a hex hag hc hw iha ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro x φ ex kx
      rcases back_imm hc ex kx with ⟨φ₁, e₁, k₁, -⟩ | ⟨φ₁, e₁, k₁, w₁⟩
      · exact absurd k₁ (ExRT.immFree hex x φ₁ e₁)
      · obtain ⟨ψ₀, c₀, k₀, w₀⟩ := iha x φ₁ e₁ k₁
        exact ⟨ψ₀, .nest hψ c₀, k₀, w₀.trans w₁⟩
    · exact ihw q hq'

/-- **An `imm` cell of a flattening is over the witness of an `imm` cell at depth.** -/
theorem flat_imm_cellAt {ρ σ : TRes K} (h : ResUT.Flat ρ σ) {x : BoCa.Loc} {ψ : TCell K}
    (e : σ.get x = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.kind = Kind.imm ∧ ψ₀.wit = ψ.wit := by
  obtain ⟨eρ, a, he, ha, hc⟩ := h
  rcases G.Comp.get hc x with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
      ⟨ζ₁, ζ₂, ζ, -, f₂, f, hC⟩
  · rw [f] at e; cases e
  · rw [f] at e; cases e; exact absurd hk (ExST.immFree he x _ f₁)
  · rw [f] at e; cases e; exact agW_imm_cellAt ha x _ f₂ hk
  · rw [f] at e; cases e
    obtain ⟨ψ₀, c₀, k₀, w₀⟩ := agW_imm_cellAt ha x ζ₂ f₂ (by
      obtain ⟨_, _, _, _, _, _, _, _, h₂, _⟩ := hC
      rw [h₂]; rfl)
    exact ⟨ψ₀, c₀, k₀, w₀.trans (CellUT.CompS.wit hC).2.symm⟩

/-! ### An unmasked ancestor of a flattening -/

/-- The cells at depth of a cell at depth's witness are at depth. -/
theorem CellAt.trans {ρ : TRes K} {m : BoCa.Loc} {χ : TCell K} (h : CellAt ρ m χ) {y : BoCa.Loc}
    {φ : TCell K} (h' : CellAt χ.wit y φ) : CellAt ρ y φ := by
  induction h with
  | top e => exact .nest e h'
  | nest e _ ih => exact .nest e (ih h')

/-- **A `mut` cell beneath an ancestor of a flattening sits beneath an unmasked one**, under a
mask closed under masked views' exclusive walks. At a masked ancestor the closure keeps the cell
out of the ancestor's exclusive walk, so it is in its witness's aliasable walk, where
`AgW.mut_beneath_unmasked` gives an unmasked ancestor; that ancestor's walk is a `○`-factor of
the flattening's (`flat_imm_walk`), so it lifts (`Beneath.lift`). -/
theorem Beneath.unmasked {W : TRes K} (hW : MutOne W) {E : BoCa.Loc → Prop} {ρ σ : TRes K}
    (hσ : ResUT.Flat ρ σ) (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ)
    (hcl : ImmMaskClosed E ρ) {m n : BoCa.Loc} {ζ ξ : TCell K} (h : Beneath σ m ζ n ξ)
    (hk : ξ.kind = Kind.mut) (hEn : ¬ E n) : ∃ m₂ ζ₂, ¬ E m₂ ∧ Beneath σ m₂ ζ₂ n ξ := by
  by_cases hEm : E m
  swap
  · exact ⟨m, ζ, hEm, h⟩
  obtain ⟨eζ, kζ, ev, av, p, hev, hav, hp, hn⟩ := h
  obtain ⟨ζ₀, cζ₀, kζ₀, wζ₀⟩ := flat_imm_cellAt hσ eζ kζ
  have hen : ev.get n = none := by
    cases f : ev.get n with
    | none => rfl
    | some ξ' => exact absurd (hcl m ζ₀ cζ₀ kζ₀ hEm ev (wζ₀ ▸ hev) n ξ' f) hEn
  have ean : av.get n = some ξ := by
    rcases G.Comp.get hp n with ⟨-, -, f⟩ | ⟨χ, f₁, -, -⟩ | ⟨χ, -, f₂, f⟩ |
        ⟨χ₁, χ₂, χ, f₁, -, -, -⟩
    · rw [f] at hn; cases hn
    · rw [hen] at f₁; cases f₁
    · rw [f] at hn; cases hn; exact f₂
    · rw [hen] at f₁; cases f₁
  have hsub' : ∀ y φ, CellAt ζ.wit y φ → φ.kind = Kind.mut → CellAt W y φ :=
    fun y φ c k => hsub y φ (cζ₀.trans (wζ₀ ▸ c)) k
  have hcl' : ImmMaskClosed E ζ.wit := fun y ζ' c => hcl y ζ' (cζ₀.trans (wζ₀ ▸ c))
  obtain ⟨m₂, ζ₂, hEm₂, hb⟩ := AgW.mut_beneath_unmasked hW hav hsub' hcl' n ξ ean hk hEn
  obtain ⟨ζ₃, -, -, -, -, hb₃⟩ := hb.lift_right hp
  obtain ⟨a, ev₀, av₀, p₀, z, ha, hev₀, hav₀, hp₀, hz⟩ := flat_imm_walk hσ eζ kζ
  obtain rfl := ExRT.functional hev hev₀
  obtain rfl := AgWT.functional hav hav₀
  obtain rfl := ResUT.CompR.functional hp hp₀
  obtain ⟨ζ₄, -, -, -, -, hb₄⟩ := hb₃.lift hz
  obtain ⟨eρ, a', he, ha', hc⟩ := hσ
  obtain rfl := AgWT.functional ha ha'
  obtain ⟨ζ₅, e₅, k₅, w₅, -⟩ := compS_get_right' hc hb₄.1
  exact ⟨m₂, ζ₅, hEm₂, e₅, k₅.trans hb₄.2.1, by rw [w₅]; exact hb₄.2.2⟩

end BoCa.Fig16.Tree.Wp

end
