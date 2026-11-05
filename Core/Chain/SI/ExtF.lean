import Core.Wp

/-!
# The world condition of a resumed continuation: the records its frozen locations name

**New design, not a transcription.** A continuation stopped under a live lend is resumed by a
handler that sees only the continuation's share as the lender left it: the lent cell folded back
(`SI/StopFrameN.lean`, `SI/IStopN.lean`), sealed (`SI/AntiStopN.lean`), or the reborrow's image
discarded (`SI/RebAcrossC.lean`). `Core`'s `Ext` reads the share pointwise: its second clause keeps
the records longer-lived than a borrow cell of the share. A fold removes the cell at the lend's
lifetime from the share, so `Ext` at the lender's share does not keep what `Ext` at the borrowed
continuation's share keeps (`not_ext_fold`, below).

`extF` reads instead the records the share's views name, at every depth: a location is *frozen*
in `ρ` (`Frz`) when an `imm` cell of `ρ` sits there, or it lies anywhere inside the witness of an
`imm` cell, the cells reached from the top through `mut` witnesses included. A record is relevant
(`RelF`) when a frozen location is its cell or one of its chain positions, the two places `Coh`
looks (`Rel`, at the top only). `extF ls ls′ ρ`: every record of `ls` relevant to `ρ` is in
`ls′`. It is `Keeps` read at every depth, with no lifetime clause.

## Why it survives the folds

Every fold moves a cell between the top and a witness, and never changes which locations sit
inside an `imm` view:

* the Mut Frame's fold replaces `ℓ ↦ mut(A, v, χ)` by `ℓ ↦ own(v) ● χ`: `χ`'s frozen locations
  are frozen at the top (`frz_fold`);
* the anti-frame's seal replaces `ℓ ↦ own(w) ● σ` by `ℓ ↦ mut(β, w, σ)`: the same, read backwards;
* the Imm Frame's fold replaces `ℓ ↦ imm(α, v, ρ_P)` by `ℓ ↦ own(v) ● ρ_P`: `ρ_P`'s `imm` cells
  and their witnesses stay frozen, and its exclusive locations, which the fold unfreezes, belong to
  no record of the caller's list (`not_relAt_excl`, read off the world at the frame's entry);
* the reborrow's fold discards the image `canon r β`, whose cells lie inside `r`'s escrow, which the
  lender's `imm` cell at `r.le` keeps frozen.

## Soundness

`extF` is a Kripke condition on the record list only; the relation's facts about records are
read where `Coh` reads them, at the records an `imm` view names. A `mut` cell's stored predicate in
this development does not read the list (`SI/MutSemN.lean`), so no lifetime-stratified clause is
needed to keep it stable: the records its content's views name are kept because those views are
frozen locations of the share.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-! ### Locations at any depth, and frozen locations -/

/-- `m` lies at any depth inside `σ`: a location of `σ`, or inside the witness of one of its
non-`own` cells. -/
inductive InDom : WRes → Loc → Prop
  | top {σ : WRes} {m : Loc} {ψ : CellU Loc Val} : σ.get m = some ψ → InDom σ m
  | wit {σ : WRes} {m m' : Loc} {ψ : CellU Loc Val} :
      σ.get m' = some ψ → ψ.kind ≠ Kind.own → InDom ψ.wit m → InDom σ m

/-- **`m` is frozen in `ρ`**: an `imm` cell of `ρ` sits at `m`, or `m` lies inside the witness
of an `imm` cell; cells reached from the top through `mut` witnesses count. -/
inductive Frz : WRes → Loc → Prop
  | imm {ρ : WRes} {m : Loc} {ψ : CellU Loc Val} :
      ρ.get m = some ψ → ψ.kind = Kind.imm → Frz ρ m
  | inImm {ρ : WRes} {m m' : Loc} {ψ : CellU Loc Val} :
      ρ.get m' = some ψ → ψ.kind = Kind.imm → InDom ψ.wit m → Frz ρ m
  | inMut {ρ : WRes} {m m' : Loc} {ψ : CellU Loc Val} :
      ρ.get m' = some ψ → ψ.kind = Kind.mut → Frz ψ.wit m → Frz ρ m

/-- `m` is a place `Coh` looks for `r`: its cell, or one of its chain positions. -/
def RelAt (r : FrameRec) (m : Loc) : Prop :=
  m = r.le ∨ ∃ p S u, Chain r.R r.T r.v p m S u

/-- **`r` is relevant to `ρ`**: a frozen location of `ρ` is a place `Coh` looks for `r`. -/
def RelF (r : FrameRec) (ρ : WRes) : Prop := ∃ m, Frz ρ m ∧ RelAt r m

/-- **The world condition of a resumed continuation**: the records of `ls` relevant to the
share `ρ` are in `ls′`. -/
def extF (ls ls' : List SRec) (ρ : WRes) : Prop := ∀ r ∈ rsOf ls, RelF r ρ → r ∈ rsOf ls'

theorem extF_refl (ls : List SRec) (ρ : WRes) : extF ls ls ρ := fun _ h _ => h

/-- A record `Rel` names is relevant. -/
theorem RelF.of_rel {r : FrameRec} {ρ : WRes} (h : Rel r ρ) : RelF r ρ := by
  obtain ⟨m, ψ, e, k, hm⟩ := h
  exact ⟨m, Frz.imm e k, hm⟩

/-- `extF` keeps what `Keeps` keeps. -/
theorem extF.keeps {ls ls' : List SRec} {ρ : WRes} (h : extF ls ls' ρ) :
    Keeps (rsOf ls) (rsOf ls') ρ := fun r hr hrel => h r hr (RelF.of_rel hrel)

/-- A record list that keeps every record keeps the relevant ones. -/
theorem extF_of_sub {ls ls' : List SRec} (h : ∀ r ∈ rsOf ls, r ∈ rsOf ls') (ρ : WRes) :
    extF ls ls' ρ := fun r hr _ => h r hr

/-- A list with the same members keeps every record. -/
theorem extF_of_same {ls ls' : List SRec} (h : ∀ x, x ∈ ls' ↔ x ∈ ls) (ρ : WRes) :
    extF ls ls' ρ := extF_of_sub (fun r hr => by
  obtain ⟨t, ht⟩ := mem_rsOf.mp hr; exact mem_rsOf.mpr ⟨t, (h _).mpr ht⟩) ρ

/-- Adding records keeps every record. -/
theorem extF_of_addAt {ls ls' : List SRec} {α : Life} (h : AddAt ls ls' α) (ρ : WRes) :
    extF ls ls' ρ := extF_of_sub (fun r hr => by
  obtain ⟨t, ht⟩ := mem_rsOf.mp hr; exact mem_rsOf.mpr ⟨t, h.1 _ ht⟩) ρ

/-! ### Moving along composition -/

theorem Frz.of_compS_left {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {m : Loc} (h : Frz ρ₁ m) :
    Frz ρ m := by
  cases h with
  | imm e k =>
      obtain ⟨ψ, e', k', -⟩ := compS_get_left' hc e
      exact Frz.imm e' (k'.trans k)
  | inImm e k hd =>
      obtain ⟨ψ, e', k', w', -⟩ := compS_get_left' hc e
      exact Frz.inImm e' (k'.trans k) (w' ▸ hd)
  | inMut e k hf =>
      obtain ⟨ψ, e', k', w', -⟩ := compS_get_left' hc e
      exact Frz.inMut e' (k'.trans k) (w' ▸ hf)

theorem Frz.of_compS_right {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {m : Loc} (h : Frz ρ₂ m) :
    Frz ρ m := Frz.of_compS_left (ResU.CompS.comm hc) h

theorem RelF.of_compS_left {r : FrameRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : RelF r ρ₁) : RelF r ρ := by
  obtain ⟨m, hf, hm⟩ := h
  exact ⟨m, hf.of_compS_left hc, hm⟩

theorem RelF.of_compS_right {r : FrameRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : RelF r ρ₂) : RelF r ρ := RelF.of_compS_left (ResU.CompS.comm hc) h

theorem extF_left : ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
    extF ls ls' ρ → extF ls ls' ρ₁ := fun _ _ _ _ _ hc h r hr hrel => h r hr (hrel.of_compS_left hc)

theorem extF_right {ls ls' : List SRec} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : extF ls ls' ρ) : extF ls ls' ρ₂ :=
  fun r hr hrel => h r hr (hrel.of_compS_right hc)

/-- A frozen location of a composite is a frozen location of a part, or of the other. -/
theorem Frz.split {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {m : Loc} (h : Frz ρ m) :
    Frz ρ₁ m ∨ Frz ρ₂ m := by
  have back : ∀ {m' : Loc} {ψ : CellU Loc Val}, ρ.get m' = some ψ →
      (∃ ψ₁, ρ₁.get m' = some ψ₁ ∧ ψ₁.kind = ψ.kind ∧ ψ₁.wit = ψ.wit) ∨
      (∃ ψ₂, ρ₂.get m' = some ψ₂ ∧ ψ₂.kind = ψ.kind ∧ ψ₂.wit = ψ.wit) := by
    intro m' ψ e
    rcases ResU.Comp.get hc m' with ⟨f₁, f₂, f⟩ | ⟨χ, f₁, f₂, f⟩ | ⟨χ, f₁, f₂, f⟩ |
        ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
    · rw [f] at e; cases e
    · rw [f] at e; cases Option.some.inj e; exact Or.inl ⟨_, f₁, rfl, rfl⟩
    · rw [f] at e; cases Option.some.inj e; exact Or.inr ⟨_, f₂, rfl, rfl⟩
    · rw [f] at e; cases Option.some.inj e
      obtain ⟨s₁, s₂, v, ρw, k₁, k₂, k₃, h₁, h₂, h₃⟩ := hC
      left
      refine ⟨χ₁, f₁, ?_, ?_⟩
      · rw [CellU.CompS.kind ⟨s₁, s₂, v, ρw, k₁, k₂, k₃, h₁, h₂, h₃⟩]
        rw [h₁]; rfl
      · rw [h₁, h₃, CellU.wit_immOf, CellU.wit_immOf]
  cases h with
  | imm e k =>
      rcases back e with ⟨ψ₁, e₁, k₁, -⟩ | ⟨ψ₂, e₂, k₂, -⟩
      · exact Or.inl (Frz.imm e₁ (k₁.trans k))
      · exact Or.inr (Frz.imm e₂ (k₂.trans k))
  | inImm e k hd =>
      rcases back e with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
      · exact Or.inl (Frz.inImm e₁ (k₁.trans k) (w₁ ▸ hd))
      · exact Or.inr (Frz.inImm e₂ (k₂.trans k) (w₂ ▸ hd))
  | inMut e k hf =>
      rcases back e with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
      · exact Or.inl (Frz.inMut e₁ (k₁.trans k) (w₁ ▸ hf))
      · exact Or.inr (Frz.inMut e₂ (k₂.trans k) (w₂ ▸ hf))

/-! ### Singletons and deletion -/

/-- A frozen location of `ρ` that is not read through the cell at `ℓ` is frozen in `ρ/ℓ`. -/
theorem Frz.del_or {ρ : WRes} {l m : Loc} (h : Frz ρ m) :
    Frz (ρ.del l) m ∨ ∃ ψ, ρ.get l = some ψ ∧
      ((ψ.kind = Kind.imm ∧ (m = l ∨ InDom ψ.wit m)) ∨ (ψ.kind = Kind.mut ∧ Frz ψ.wit m)) := by
  cases h with
  | @imm _ _ ψ e k =>
      by_cases hml : m = l
      · subst hml; exact Or.inr ⟨ψ, e, Or.inl ⟨k, Or.inl rfl⟩⟩
      · exact Or.inl (Frz.imm (by rw [ResU.del_get_ne _ hml]; exact e) k)
  | @inImm _ _ m' ψ e k hd =>
      by_cases hml : m' = l
      · subst hml; exact Or.inr ⟨ψ, e, Or.inl ⟨k, Or.inr hd⟩⟩
      · exact Or.inl (Frz.inImm (by rw [ResU.del_get_ne _ hml]; exact e) k hd)
  | @inMut _ _ m' ψ e k hf =>
      by_cases hml : m' = l
      · subst hml; exact Or.inr ⟨ψ, e, Or.inr ⟨k, hf⟩⟩
      · exact Or.inl (Frz.inMut (by rw [ResU.del_get_ne _ hml]; exact e) k hf)

theorem Frz.of_del {ρ : WRes} {l m : Loc} (h : Frz (ρ.del l) m) : Frz ρ m := by
  have lift : ∀ {m' : Loc} {ψ : CellU Loc Val}, (ρ.del l).get m' = some ψ → ρ.get m' = some ψ := by
    intro m' ψ e
    by_cases hml : m' = l
    · subst hml; rw [ResU.del_get_self] at e; cases e
    · rwa [ResU.del_get_ne _ hml] at e
  cases h with
  | imm e k => exact Frz.imm (lift e) k
  | inImm e k hd => exact Frz.inImm (lift e) k hd
  | inMut e k hf => exact Frz.inMut (lift e) k hf

/-- The frozen locations of a `mut` singleton are its witness's. -/
theorem Frz.single_mut {l m : Loc} {ψ : CellU Loc Val} (hk : ψ.kind = Kind.mut)
    (h : Frz (ResU.single l ψ) m) : Frz ψ.wit m := by
  cases h with
  | imm e k =>
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      rw [hk] at k; cases k
  | inImm e k _ =>
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      rw [hk] at k; cases k
  | inMut e _ hf =>
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      exact hf

/-- An `own` singleton freezes nothing. -/
theorem not_frz_single_own {l m : Loc} {v : Val} : ¬ Frz (ResU.single l (CellU.ownOf v)) m := by
  intro h
  cases h with
  | imm e k => obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; cases k
  | inImm e k _ => obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; cases k
  | inMut e k _ => obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; cases k

/-- A restriction keeps frozen locations of the whole. -/
theorem Frz.of_restrictDom {ρ σ : WRes} {m : Loc} (h : Frz (ρ.restrictDom σ) m) : Frz ρ m := by
  cases h with
  | imm e k => exact Frz.imm (ResU.restrictDom_get_inv e) k
  | inImm e k hd => exact Frz.inImm (ResU.restrictDom_get_inv e) k hd
  | inMut e k hf => exact Frz.inMut (ResU.restrictDom_get_inv e) k hf

theorem InDom.of_del {σ : WRes} {l m : Loc} (h : InDom (σ.del l) m) : InDom σ m := by
  have lift : ∀ {m' : Loc} {ψ : CellU Loc Val}, (σ.del l).get m' = some ψ → σ.get m' = some ψ := by
    intro m' ψ e
    by_cases hml : m' = l
    · subst hml; rw [ResU.del_get_self] at e; cases e
    · rwa [ResU.del_get_ne _ hml] at e
  cases h with
  | top e => exact InDom.top (lift e)
  | wit e k hd => exact InDom.wit (lift e) k hd

theorem InDom.of_compS_left {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {m : Loc}
    (h : InDom ρ₁ m) : InDom ρ m := by
  cases h with
  | top e =>
      obtain ⟨ψ, e', -⟩ := compS_get_left' hc e
      exact InDom.top e'
  | wit e k hd =>
      obtain ⟨ψ, e', k', w', -⟩ := compS_get_left' hc e
      exact InDom.wit e' (k' ▸ k) (w' ▸ hd)

/-- **An image's frozen locations lie in the escrow it is an image of.** Every cell of
`c ∈ reb_β(σ)` is at a location of `σ`, and its witness is a piece of `σ` or the witness of
`σ`'s cell there (`reb_cell`). -/
theorem frz_reb_inDom {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c) {m : Loc} (h : Frz c m) :
    InDom σ m := by
  cases h with
  | @imm _ _ ψ e k =>
      obtain ⟨-, hcase⟩ := reb_cell hr e
      rcases hcase with ⟨u, q, hh, eσ, -, -, -⟩ | ⟨ζ, eσ, -⟩ | ⟨ζ, eσ, -⟩
      · exact InDom.top eσ
      · exact InDom.top eσ
      · exact InDom.top eσ
  | @inImm _ _ m' ψ e k hd =>
      obtain ⟨-, hcase⟩ := reb_cell hr e
      rcases hcase with ⟨u, q, hh, eσ, rfl, ⟨τ, hτ⟩, -⟩ | ⟨ζ, eσ, kζ, w⟩ | ⟨ζ, eσ, kζ, w⟩
      · rw [CellU.wit_immOf] at hd
        exact (InDom.of_del hd).of_compS_left hτ
      · exact InDom.wit eσ (by rw [kζ]; simp) (w ▸ hd)
      · exact InDom.wit eσ (by rw [kζ]; simp) (w ▸ hd)
  | inMut e k _ =>
      rw [(reb_cell hr e).1] at k; cases k

/-! ### Exclusive locations -/

/-- `m` holds a non-`imm` cell reached from the top of `σ` through `mut` witnesses: an exclusive
location of `σ`. -/
def XEx (σ : WRes) (m : Loc) : Prop :=
  ∃ p τ ζ, XPath σ p τ ∧ τ.get m = some ζ ∧ ζ.kind ≠ Kind.imm

/-- A location at any depth is frozen or exclusive. -/
theorem InDom.frz_or_xex {σ : WRes} {m : Loc} (h : InDom σ m) : Frz σ m ∨ XEx σ m := by
  induction h with
  | @top σ m ψ e =>
      by_cases k : ψ.kind = Kind.imm
      · exact Or.inl (Frz.imm e k)
      · exact Or.inr ⟨[], σ, ψ, XPath.nil σ, e, k⟩
  | @wit σ m m' ψ e k hd ih =>
      cases hkk : ψ.kind with
      | own => exact absurd hkk k
      | imm => exact Or.inl (Frz.inImm e hkk hd)
      | «mut» =>
          rcases ih with hf | ⟨p, τ, ζ, hp, eτ, kτ⟩
          · exact Or.inl (Frz.inMut e hkk hf)
          · exact Or.inr ⟨m' :: p, τ, ζ, XPath.cons e hkk hp, eτ, kτ⟩

theorem XEx.of_compS_right {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {m : Loc}
    (h : XEx ρ₂ m) : XEx ρ m := by
  obtain ⟨p, τ, ζ, hp, eτ, kτ⟩ := h
  cases hp with
  | nil => exact ⟨[], ρ, ζ, XPath.nil ρ, (ResU.CompS.get_right_of_ne_imm hc eτ kτ).2, kτ⟩
  | @cons _ _ m' ψ q e k hq =>
      exact ⟨m' :: q, τ, ζ,
        XPath.cons (ResU.CompS.get_right_of_ne_imm hc e (by rw [k]; simp)).2 k hq, eτ, kτ⟩

theorem XEx.of_compS_left {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {m : Loc}
    (h : XEx ρ₁ m) : XEx ρ m := XEx.of_compS_right (ResU.CompS.comm hc) h

/-- **No record of a typed world names an exclusive location of a part of it.** A part `A` of a
valid world `W` whose invariant holds: an exclusive location of `A` is a cell of `ex(W)_●`
(`xpath_ex_part`); a record's cell is a view of `ag(W)` (`LeInvW`), and a chain position is an
`own` cell of the record's escrow, which `ExIn` puts in `ag(W)`; `ex(W)_●` and `ag(W)` are
disjoint (`ex_ag_disjoint`). -/
theorem not_relAt_xex {W A : WRes} {ps rs : List FrameRec} (hv : ResU.Valid W) (hTI : TI W ps rs)
    (hA : ResU.Le A W) {r : FrameRec} (hr : r ∈ rs) {m : Loc} (hx : XEx A m) : ¬ RelAt r m := by
  obtain ⟨p, τ, ζ, hp, eτ, kτ⟩ := hx
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hv
  have hexm : eW.get m = some ζ := xpath_ex_part hA heW hp eτ kτ
  rintro (rfl | ⟨q, S, u, hch⟩)
  · obtain ⟨ψ, eψ, -, -⟩ := hTI.leInvW r hr aW haW
    exact ex_ag_disjoint hv heW haW hexm eψ
  · obtain ⟨e, he, hlift⟩ := hTI.exIn hr aW haW
    obtain ⟨ζ₁, e₁, -⟩ := exR_cell he (Chain.own hch) (by simp)
    obtain ⟨ζ₂, e₂, -⟩ := hlift m ζ₁ e₁
    exact ex_ag_disjoint hv heW haW hexm e₂

/-- **No record's escrow holds an exclusive location of a part of the world exclusively.** The
escrow's exclusive cells are lifted into `ag(W)` (`ExIn`); the part's are in `ex(W)_●`. -/
theorem not_escrow_xex {W A : WRes} {ps rs : List FrameRec} (hv : ResU.Valid W) (hTI : TI W ps rs)
    (hA : ResU.Le A W) {d : FrameRec} (hd : d ∈ rs) {m : Loc} {ζ : CellU Loc Val}
    (he : d.R.get m = some ζ) (hk : ζ.kind ≠ Kind.imm) (hx : XEx A m) : False := by
  obtain ⟨p, τ, ζ', hp, eτ, kτ⟩ := hx
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hv
  have hexm : eW.get m = some ζ' := xpath_ex_part hA heW hp eτ kτ
  obtain ⟨e, hex, hlift⟩ := hTI.exIn hd aW haW
  obtain ⟨ζ₁, e₁, -⟩ := exR_cell hex he hk
  obtain ⟨ζ₂, e₂, -⟩ := hlift m ζ₁ e₁
  exact ex_ag_disjoint hv heW haW hexm e₂

/-- **No record of a typed world is in the lineage of a new frame's record.** A frame about to
be taken at `ℓ ↦ own(v) ● R`, a part of the world: the record `⟨ℓ, v, R, T, δ⟩` and its proper
sub-records sit at exclusive locations of that part, which no record of the world names
(`not_relAt_xex`). -/
theorem notDesc_frame {W X R : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {T : VTy}
    {δ : BoCa.Lifetime.LSub} (hv : ResU.Valid W) (hTI : TI W ps rs)
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hXW : ResU.Le X W) {d : FrameRec}
    (hd : d ∈ rs) (hpd : DescR ⟨l, v, R, T, δ⟩ d) : False := by
  rcases hpd.cases with rfl | ⟨q, hq, hpath⟩
  · exact not_relAt_xex hv hTI hXW hd ⟨[], X, _, XPath.nil X,
      (ResU.CompS.get_left_of_ne_imm hX (ResU.single_get_self _ _) (by simp)).2, by simp⟩
      (Or.inl rfl)
  · obtain ⟨d', ⟨q', hq'⟩, hsub⟩ := hpath.last hq
    obtain ⟨-, -, ζ, eζ, kζ, -⟩ := hsub
    have hx : XEx R d.le := ⟨q', d'.R, ζ, hq'.xpath, eζ, by rw [kζ]; simp⟩
    exact not_relAt_xex hv hTI hXW hd (hx.of_compS_right hX) (Or.inl rfl)

/-! ### `Ext` does not survive a fold -/

/-- The configuration of a Mut Frame's fold, at the share level: `Ext` at the lender's share
(the lent cell folded to `own`) gives `Ext` at the borrowed continuation's share (the cell
`mut`). -/
def ExtFoldTransfer : Prop :=
  ∀ (ls ls' : List SRec) (l : Loc) (A : Life) (v : Val),
    Ext ls ls' (ResU.single l (CellU.ownOf v)) →
    Ext ls ls' (ResU.single l (CellU.mutOf A v PMap.empty (ResU.inStratum_empty A)
      (fun _ _ => True) trivial))

/-- **`Ext` is not carried across a fold**: a record longer-lived than the lend, removed by the
handler, is kept by `Ext` at the borrowed continuation's share and not by `Ext` at the lender's.
-/
theorem not_extFoldTransfer : ¬ ExtFoldTransfer := by
  intro h
  let r : FrameRec := ⟨0, Val.unit, PMap.empty, .unit, ⟨[]⟩⟩
  let A : Life := OrderDual.toDual 1
  let x : SRec := (r, OrderDual.toDual 0)
  have hown : Ext [x] [] (ResU.single 0 (CellU.ownOf Val.unit)) := by
    refine ⟨fun r' _ hrel => ?_, fun b hb => ?_⟩
    · obtain ⟨m, ψ, e, k, -⟩ := hrel
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      cases k
    · obtain ⟨m, ψ, e, k, -⟩ := hb
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      exact absurd rfl k
  have hm := (h [x] [] 0 A Val.unit hown).2 A
    ⟨0, _, ResU.single_get_self _ _, by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c,
      le_rfl⟩ x
    (show OrderDual.ofDual (OrderDual.toDual 0 : Life) < OrderDual.ofDual A from by decide)
  simp at hm

end BoCa.Fig16.LogRel.Core.Chain.SI

end
