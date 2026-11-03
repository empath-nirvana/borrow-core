import Support.Model.Tree.World.SimL
import Support.Model.Tree.World.Coherent
import Support.Model.Tree.World.ShapeT

/-!
# A reborrow carried along a re-reading

`c ∈ reb_β(R)` at `K`, `R` covered at `Θ` and `Θ'` agreeing with `Θ` on `R`'s `mut` cells: then
`c` is covered, `Θ'` agrees on it, and its re-reading `c'` is in `reb_β(R')` at `K'`, for `R'`
the re-reading of `R` (`reb_rr`). Each piece `p` of the reborrow's decomposition is a part of
`R`, so it has a re-reading `p'`; the composite of the `p'` is the re-reading of the composite
(`RR.bigComp`) and a part of `R'`; and at each location `reb_β`'s clause reads the cell of `R`
and of `c` there, both kept by the re-reading up to their witnesses, which are re-read.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-! ### Parts -/

theorem le_cov {Θ : LocTy} {q ρ : TRes K} (h : ResUT.Le q ρ) (hc : CovR Θ K ρ) : CovR Θ K q := by
  obtain ⟨τ, hτ⟩ := h; exact hc.of_compS_left hτ

theorem le_agree {Θ Θ' : CodeTy} {q ρ : TRes K} (h : ResUT.Le q ρ) (hc : AgreeOn Θ Θ' ρ) :
    AgreeOn Θ Θ' q := by
  obtain ⟨τ, hτ⟩ := h; exact hc.of_compS_left hτ

theorem le_holdsMut {q ρ : TRes K} (h : ResUT.Le q ρ) {x : BoCa.Loc} (hm : HoldsMut q x) :
    HoldsMut ρ x := by
  obtain ⟨τ, hτ⟩ := h; exact hm.of_compS_left hτ

/-- A member of a `●`-composite is a part of it. -/
theorem bigCompS_le {xs : List (TRes K)} {b : TRes K}
    (h : BigCompT CellUT.CompatS CellUT.CompS xs b) {x : TRes K} (hx : x ∈ xs) :
    ResUT.Le x b := by
  induction h with
  | nil => cases hx
  | @cons σ τ ρ σs _ hc ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨τ, hc⟩
      · exact ResUT.Le.trans (ih hx) (le_of_compS_right hc)

/-- **A `●`-composite carried along re-readings of its members.** -/
theorem RR.bigComp {Θ : LocTy} {xs : List (TRes K)} {b : TRes K}
    (h : BigCompT CellUT.CompatS CellUT.CompS xs b) :
    ∀ {xs' : List (TRes K')}, List.Forall₂ (RR Θ) xs xs' →
      ∃ b', BigCompT CellUT.CompatS CellUT.CompS xs' b' ∧ RR Θ b b' := by
  induction h with
  | nil =>
      intro xs' hx; cases hx
      exact ⟨_, G.BigComp.nil, RR.empty⟩
  | cons _ hc ih =>
      intro xs' hx
      cases hx with
      | cons hσ hrest =>
          obtain ⟨τ', hτ', rτ⟩ := ih hrest
          obtain ⟨ρ', hρ', rρ⟩ := RR.compS hσ rτ hc
          exact ⟨ρ', G.BigComp.cons hτ' hρ', rρ⟩

/-- A part of a re-read resource: the re-reading of the part is a part of the re-reading. -/
theorem RR.le {Θ Θ' : CodeTy} (hE : K.Ext K') {q ρ : TRes K} {q' ρ' : TRes K'}
    (h : ResUT.Le q ρ) (hc : CovR (sem Θ) K ρ) (hag : AgreeOn Θ Θ' ρ) (hr : RR (sem Θ') ρ ρ')
    (hq : RR (sem Θ') q q') : ResUT.Le q' ρ' := by
  obtain ⟨τ, hτ⟩ := h
  obtain ⟨a', b', ha, hb, hc'⟩ := RR.split_retype hE hτ hc hag hr
  obtain rfl := RR.func hq ha
  exact ⟨b', hc'⟩

/-- `del` commutes with re-reading. -/
theorem RR.del {Θ : LocTy} {q : TRes K} {q' : TRes K'} (h : RR Θ q q') (l : BoCa.Loc) :
    RR Θ (q.del l) (q'.del l) := by
  refine ⟨fun m => ?_, fun m ψ ψ' e e' => ?_⟩
  · by_cases hm : m = l
    · subst hm; simp
    · rw [ResUT.del_get_ne _ hm, ResUT.del_get_ne _ hm]; exact h.1 m
  · by_cases hm : m = l
    · subst hm; simp at e
    · rw [ResUT.del_get_ne _ hm] at e e'; exact h.2 m ψ ψ' e e'

/-- Every member of a list of parts of a covered, agreeing resource has a re-reading. -/
theorem exists_forall₂_rr {Θ Θ' : CodeTy} (hE : K.Ext K') {ρ : TRes K}
    (hc : CovR (sem Θ) K ρ) (hag : AgreeOn Θ Θ' ρ) :
    ∀ (π : List (BoCa.Loc × TRes K)), (∀ x ∈ π.map Prod.snd, ResUT.Le x ρ) →
      ∃ π' : List (BoCa.Loc × TRes K'), π'.map Prod.fst = π.map Prod.fst ∧
        List.Forall₂ (RR (sem Θ')) (π.map Prod.snd) (π'.map Prod.snd) ∧
        List.Forall₂ (fun (a : BoCa.Loc × TRes K) (b : BoCa.Loc × TRes K') =>
          a.1 = b.1 ∧ RR (sem Θ') a.2 b.2) π π'
  | [], _ => ⟨[], rfl, .nil, .nil⟩
  | (l, p) :: π, hle => by
      obtain ⟨p', hp, -⟩ := RR.exists_retype hE (le_cov (hle p (by simp)) hc)
        (le_agree (hle p (by simp)) hag)
      obtain ⟨π', h₁, h₂, h₃⟩ := exists_forall₂_rr hE hc hag π
        (fun x hx => hle x (List.mem_cons_of_mem _ hx))
      exact ⟨(l, p') :: π', by simp [h₁], .cons hp h₂, .cons ⟨rfl, hp⟩ h₃⟩

theorem forall₂_mem_left' {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => cases hy
  | cons hxy _ ih =>
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨_, List.mem_cons_self, hxy⟩
      · obtain ⟨x, hx, hr⟩ := ih hy
        exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-! ### The cells of a reborrow -/

/-- Every cell of `reb_β(R)` is `imm`, over a part of `R` or the witness of `R`'s cell. -/
theorem reb_cell_src {β : Life} {R c : TRes K} (hreb : ResUT.Reb β R c) {l : BoCa.Loc}
    {ψ : TCell K} (e : c.get l = some ψ) :
    ψ.kind = Kind.imm ∧
      ((∃ q, ResUT.Le q R ∧ ψ.wit = q) ∨ (∃ χ : TCell K, R.get l = some χ ∧ ψ.wit = χ.wit)) := by
  obtain ⟨-, π, b, hdom, hb, hle, hat⟩ := hreb
  obtain ⟨p, hp⟩ : ∃ p, (l, p) ∈ π := by
    obtain ⟨x, hx⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨ψ, e⟩)
    exact ⟨x.2, by rw [← hx.2]; exact hx.1⟩
  have hpR : ResUT.Le p R :=
    ResUT.Le.trans (bigCompS_le hb (List.mem_map.mpr ⟨_, hp, rfl⟩)) hle
  obtain ⟨⟨ψp, ep⟩, hown, hmut, himm⟩ := hat l p hp
  have hRl : ∃ χ, R.get l = some χ := by
    obtain ⟨τ, hτ⟩ := hpR
    exact comp_some hτ ep
  obtain ⟨χ, eχ⟩ := hRl
  rcases CellUT.rep' χ with ⟨u, rfl⟩ | ⟨s, v, ρ, hs, rfl⟩ | ⟨b', _, v, ρ, hb', P, hP, rfl⟩
  · obtain ⟨h, e'⟩ := hown u eχ
    rw [e] at e'; cases Option.some.inj e'
    refine ⟨by simp, .inl ⟨p.del l, ?_, by simp⟩⟩
    exact ResUT.Le.trans ⟨_, ResUT.del_compS ep⟩ hpR
  · obtain ⟨⟨t, ht, -, e'⟩, -⟩ := himm s v ρ hs eχ
    rw [e] at e'; cases Option.some.inj e'
    exact ⟨by simp, .inr ⟨_, eχ, by simp⟩⟩
  · obtain ⟨⟨h, e'⟩, -⟩ := hmut b' v ρ hb' P hP eχ
    rw [e] at e'; cases Option.some.inj e'
    exact ⟨by simp, .inr ⟨_, eχ, by simp⟩⟩

/-- The witnesses of a covered cell are covered. -/
theorem Cov.wit {Θ : LocTy} {l : BoCa.Loc} {ψ : TCell K} (h : Cov Θ K l ψ) : CovR Θ K ψ.wit := by
  cases h with
  | own => intro m χ e; simp [CellUT.wit] at e
  | imm _ _ hw => exact hw
  | «mut» _ _ _ _ _ hw => exact hw

/-- An `imm` cell over a covered witness is covered. -/
theorem cov_of_imm_wit {Θ : LocTy} {l : BoCa.Loc} {ψ : TCell K} (hk : ψ.kind = Kind.imm)
    (hw : CovR Θ K ψ.wit) : Cov Θ K l ψ := by
  rcases CellUT.rep' ψ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b, _, v, χ, hb, P, hP, rfl⟩
  · simp at hk
  · simp only [CellUT.wit_immOf] at hw; exact Cov.immOf_iff.mpr hw
  · simp at hk

/-- **A reborrow of a covered, agreeing resource is covered and agreeing.** -/
theorem reb_cov_agree {Θ Θ' : CodeTy} {β : Life} {R c : TRes K} (hreb : ResUT.Reb β R c)
    (hc : CovR (sem Θ) K R) (hag : AgreeOn Θ Θ' R) :
    CovR (sem Θ) K c ∧ AgreeOn Θ Θ' c := by
  refine ⟨fun l ψ e => ?_, fun x hx => ?_⟩
  · obtain ⟨hk, h | h⟩ := reb_cell_src hreb e
    · obtain ⟨q, hq, hw⟩ := h
      exact cov_of_imm_wit hk (hw ▸ le_cov hq hc)
    · obtain ⟨χ, eχ, hw⟩ := h
      exact cov_of_imm_wit hk (hw ▸ Cov.wit (hc l χ eχ))
  · cases hx with
    | top e =>
        have := (reb_cell_src hreb e).1
        simp [CellUT.kind] at this
    | deep e hm =>
        rcases (reb_cell_src hreb e).2 with ⟨q, hq, hw⟩ | ⟨χ, eχ, hw⟩
        · rw [hw] at hm; exact hag x (le_holdsMut hq hm)
        · rw [hw] at hm; exact hag x (.deep eχ hm)

/-- `Dom` carried by a re-reading. -/
theorem RR.dom {Θ : LocTy} {q : TRes K} {q' : TRes K'} (h : RR Θ q q') {d : List BoCa.Loc}
    (hd : q.Dom d) : q'.Dom d := by
  refine ⟨hd.1, fun l => (hd.2 l).trans ?_⟩
  constructor
  · rintro ⟨ψ, e⟩; obtain ⟨ψ', e', -⟩ := h.get_some e; exact ⟨ψ', e'⟩
  · rintro ⟨ψ', e'⟩; obtain ⟨ψ, e, -⟩ := h.get_some' e'; exact ⟨ψ, e⟩

/-- The re-read cell of `c` at `l`, when `c(l) = imm(t, v, χ)` and `χ` re-reads to `χ'`. -/
theorem rr_imm_at {Θ : LocTy} {c : TRes K} {c' : TRes K'} (hc : RR Θ c c') {l : BoCa.Loc}
    {t : TSet} {v : BoCa.Val} {χ : TRes K} {h : χ.InStratum t} {χ' : TRes K'}
    (e : c.get l = some (CellUT.immOf t v χ h)) (hχ : RR Θ χ χ') :
    ∃ h' : χ'.InStratum t, c'.get l = some (CellUT.immOf t v χ' h') := by
  obtain ⟨ψ', e', hr⟩ := hc.get_some e
  obtain ⟨χ'', h'', rfl, hr'⟩ := RC.immOf_inv hr
  obtain rfl := RR.func hr' hχ
  exact ⟨h'', e'⟩

/-- **A reborrow carried along a re-reading.** -/
theorem reb_rr {Θ Θ' : CodeTy} (hE : K.Ext K') {β : Life} {R c : TRes K} {R' c' : TRes K'}
    (hreb : ResUT.Reb β R c) (hcR : CovR (sem Θ) K R) (hag : AgreeOn Θ Θ' R)
    (hR : RR (sem Θ') R R') (hc : RR (sem Θ') c c') : ResUT.Reb β R' c' := by
  obtain ⟨hst, π, b, hdom, hb, hle, hat⟩ := hreb
  have hpR : ∀ x ∈ π.map Prod.snd, ResUT.Le x R :=
    fun x hx => ResUT.Le.trans (bigCompS_le hb hx) hle
  obtain ⟨π', h₁, h₂, h₃⟩ := exists_forall₂_rr hE hcR hag π hpR
  obtain ⟨b', hb', hbb⟩ := RR.bigComp hb h₂
  refine ⟨hR.inStratum hE hst, π', b', h₁ ▸ RR.dom hc hdom, hb',
    RR.le hE hle hcR hag hR hbb, fun l p' hlp => ?_⟩
  obtain ⟨⟨l₀, p⟩, hlp₀, rfl, hp⟩ := forall₂_mem_left' h₃ hlp
  obtain ⟨⟨ψp, ep⟩, hown, hmut, himm⟩ := hat l₀ p hlp₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨ψ', e', -⟩ := hp.get_some ep; exact ⟨ψ', e'⟩
  · intro v e
    obtain ⟨h, e₀⟩ := hown v (RR.own_back hR e)
    exact rr_imm_at hc e₀ (RR.del hp l₀)
  · intro b₁ _ v χ₁ hb₁ P hw e
    obtain ⟨ψ, eψ, hr⟩ := hR.get_some' e
    have hk : ψ.kind = Kind.mut := by rw [← hr.kind]; simp
    rcases CellUT.rep' ψ with ⟨u, rfl⟩ | ⟨s, v₀, χ₀, hs, rfl⟩ | ⟨b₀, _, v₀, χ₀, hb₀, P₀, hP₀, rfl⟩
    · simp at hk
    · simp at hk
    · have hv : v₀ = v := by have := hr.erase; simp at this; exact this.symm
      have hχ : RR (sem Θ') χ₀ χ₁ := by have := hr.wit; simpa using this
      subst hv
      obtain ⟨⟨h, e₀⟩, hd⟩ := hmut b₀ v₀ χ₀ hb₀ P₀ hP₀ eψ
      exact ⟨rr_imm_at hc e₀ hχ, RR.dom hp hd⟩
  · intro s v χ₁ h e
    obtain ⟨ψ, eψ, hr⟩ := hR.get_some' e
    have hk : ψ.kind = Kind.imm := by rw [← hr.kind]; simp
    rcases CellUT.rep' ψ with ⟨u, rfl⟩ | ⟨s₀, v₀, χ₀, hs₀, rfl⟩ | ⟨b₀, _, v₀, χ₀, hb₀, P₀, hP₀, rfl⟩
    · simp at hk
    · obtain ⟨χ', h', e', hχ⟩ := RC.immOf_inv hr
      obtain ⟨e1, e2, e3⟩ := CellUT.immOf_inj e'
      subst e1 e2 e3
      obtain ⟨⟨t, ht, hts, e₀⟩, hd⟩ := himm _ _ χ₀ hs₀ eψ
      obtain ⟨ht', e₁⟩ := rr_imm_at hc e₀ hχ
      exact ⟨⟨t, ht', hts, e₁⟩, RR.dom hp hd⟩
    · simp at hk

/-- **A reborrow's re-reading exists and is a reborrow of the re-reading.** -/
theorem reb_rr_exists {Θ Θ' : CodeTy} (hE : K.Ext K') {β : Life} {R c : TRes K} {R' : TRes K'}
    (hreb : ResUT.Reb β R c) (hcR : CovR (sem Θ) K R) (hag : AgreeOn Θ Θ' R)
    (hR : RR (sem Θ') R R') : ∃ c' : TRes K', RR (sem Θ') c c' ∧ ResUT.Reb β R' c' := by
  obtain ⟨hcc, hcag⟩ := reb_cov_agree hreb hcR hag
  obtain ⟨c', hc', -⟩ := RR.exists_retype hE hcc hcag
  exact ⟨c', hc', reb_rr hE hreb hcR hag hR hc'⟩

end BoCa.Fig16.Tree.Wp

end
