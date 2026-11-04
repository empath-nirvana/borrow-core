import Support.Model.Tree.World.UpdAGrow

/-!
# `↭`'s `P̂` along the walks  `[spec §62]`

`InvKept` (row 5.27's `P̂`, departure D2) reads the codes at the `mut` cells of `⦇ρ⦈`. Under `UpdA`
a start `mut` cell may leave the run with its `imm` ancestor (`docs/new-core/scope-806.md`, R3),
and then the middle holds no flattened `mut` cell to chain the codes through: the cell is read
beneath the ancestor's absorber in the middle world. When that absorber is the run's own cell, the
middle's flattening may read an `imm` cell at the location (`imm ○ mut`, `○` clause (5)), which
`InvKept` says nothing of. So the codes are also kept beneath the unmasked ancestors of `⦇ρ⦈`
(`InvBeneath`), the same ancestor technique, and `EndT` reads both (`InvKeptA`).

* **Along an update** (`InvKeptA.trans`): an ancestor kept by `UpdX` carries the cell beneath it
  (`Beneath.rr_fwd`, the walk re-read).
* **Along a run** (`InvKeptA.transA`): an ancestor kept by `UpdA` likewise; an ancestor absorbed by
  the middle world is absorbed by an `imm` operand of `⦇ρf⦈ ○ ⦇ρ⦈` with its witness. The run's
  operand carries the cell beneath it into the second segment's `InvBeneath`; the frame's holds
  it at depth, where the world's re-typing agrees (`AgreeOn`).
* **Beside a frame** (`InvKeptA.frame`) and **at a re-typing agreeing on the resource**
  (`InvKeptA.of_agree`): an ancestor of a composite is an `imm` operand's.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-! ### Cells beneath an ancestor -/

/-- **A `mut` cell beneath an ancestor of `⦇ρ⦈` is a cell of `ρ` at depth.** -/
theorem Beneath.cellAt {W : TRes K} (hW : MutOne W) {ρ σ : TRes K} (hσ : ResUT.Flat ρ σ)
    (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) {m n : BoCa.Loc}
    {ζ ξ : TCell K} (h : Beneath σ m ζ n ξ) (hk : ξ.kind = Kind.mut) : CellAt ρ n ξ := by
  obtain ⟨eζ, kζ, ev, av, p, hev, hav, hp, hn⟩ := h
  obtain ⟨ζ₀, cζ₀, -, wζ₀⟩ := flat_imm_cellAt hσ eζ kζ
  have hsub' : ∀ y φ, CellAt ζ.wit y φ → φ.kind = Kind.mut → CellAt W y φ :=
    fun y φ c k => hsub y φ (cζ₀.trans (wζ₀ ▸ c)) k
  have hpm : MutIn (CellAt ζ.wit) p := MutIn.comp mutKeep_compR (MutUniq.of_sub hW hsub') hp
    (ExW.mutIn mutKeep_compR hW hev hsub') (AgW.mutIn hW hav hsub')
  exact cζ₀.trans (wζ₀ ▸ hpm n ξ hn hk)

/-- **A `Beneath` carried forward along a re-read ancestor**: the end ancestor's walk is the
re-reading of the start ancestor's (`walk_rr`). -/
theorem Beneath.rr_fwd {Θ : LocTy} (hE : K.Ext K') {σ : TRes K} {σ' : TRes K'} {m n : BoCa.Loc}
    {ζ ξ : TCell K} {ζ' : TCell K'} (h : Beneath σ m ζ n ξ) (e' : σ'.get m = some ζ')
    (hk' : ζ'.kind = Kind.imm) (hr : RR Θ ζ.wit ζ'.wit)
    (hw : ∃ ev av p, ExRT ζ'.wit ev ∧ AgWT ζ'.wit av ∧ ResUT.CompR ev av p) :
    ∃ ξ', Beneath σ' m ζ' n ξ' ∧ LsSim Θ ξ' ξ := by
  obtain ⟨-, -, ev, av, p, hev, hav, hp, hn⟩ := h
  obtain ⟨ev', av', p', hev', hav', hp'⟩ := hw
  have hs := walk_rr hE hr hev hav hp hev' hav' hp' n
  rw [hn] at hs
  cases hq : p'.get n with
  | none => rw [hq] at hs; cases hs
  | some ξ' =>
      rw [hq] at hs
      cases hs with
      | some h' => exact ⟨ξ', ⟨e', hk', ev', av', p', hev', hav', hp', hq⟩, h'⟩

/-- An `imm` cell of a flattening has its walks. -/
theorem flat_imm_walks {ρ σ : TRes K} (hσ : ResUT.Flat ρ σ) {m : BoCa.Loc} {ζ : TCell K}
    (e : σ.get m = some ζ) (hk : ζ.kind = Kind.imm) :
    ∃ ev av p, ExRT ζ.wit ev ∧ AgWT ζ.wit av ∧ ResUT.CompR ev av p := by
  obtain ⟨-, ev, av, p, -, -, hev, hav, hp, -⟩ := flat_imm_walk hσ e hk
  exact ⟨ev, av, p, hev, hav, hp⟩

/-- A `Beneath` read at an `imm` cell over the same witness. -/
theorem Beneath.of_wit {σ τ : TRes K} {m n : BoCa.Loc} {ζ φ ξ : TCell K}
    (h : Beneath σ m ζ n ξ) (e : τ.get m = some φ) (hk : φ.kind = Kind.imm)
    (hw : φ.wit = ζ.wit) : Beneath τ m φ n ξ :=
  ⟨e, hk, by rw [hw]; exact h.2.2⟩

/-- **An `imm` cell of a `○` of resources is above an `imm` operand's cell.** -/
theorem compR_imm_source {σ₁ σ₂ σ : TRes K} (h : ResUT.CompR σ₁ σ₂ σ) {m : BoCa.Loc}
    {ζ : TCell K} (e : σ.get m = some ζ) (hk : ζ.kind = Kind.imm) :
    ∃ φ, (σ₁.get m = some φ ∨ σ₂.get m = some φ) ∧ ImmLe φ ζ := by
  rcases G.Comp.get h m with ⟨-, -, f⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, f₂, f, hC⟩
  · rw [f] at e; cases e
  · rw [f] at e; cases e; exact ⟨_, Or.inl f₁, ImmLe.refl hk⟩
  · rw [f] at e; cases e; exact ⟨_, Or.inr f₂, ImmLe.refl hk⟩
  · rw [f] at e; cases e
    rcases CellUT.CompR.imm_operand hC hk with k | k
    · exact ⟨_, Or.inl f₁, CellUT.CompR.immLe_left hC k⟩
    · exact ⟨_, Or.inr f₂, CellUT.CompR.immLe_right hC k⟩

/-! ### The codes beneath the ancestors -/

/-- **`Θ′` keeps `Θ`'s code at every `mut` cell beneath an unmasked ancestor of `⦇ρ⦈`**, at an
unmasked location. -/
def InvBeneath (Θ Θ' : CodeTy) (E : BoCa.Loc → Prop) (ρ : TRes K) : Prop :=
  ∀ σ, ResUT.Flat ρ σ → ∀ m ζ l ξ, Beneath σ m ζ l ξ → ξ.kind = Kind.mut → ¬ E m → ¬ E l →
    Θ' l = Θ l

/-- **`↭`'s `P̂` along the walks**: the codes kept at the `mut` cells of `⦇ρ⦈` (`InvKept`) and
beneath its unmasked ancestors (`InvBeneath`). -/
def InvKeptA (Θ Θ' : CodeTy) (E : BoCa.Loc → Prop) (ρ : TRes K) : Prop :=
  InvKept Θ Θ' E ρ ∧ InvBeneath Θ Θ' E ρ

theorem InvKeptA.refl (Θ : CodeTy) (E : BoCa.Loc → Prop) (ρ : TRes K) : InvKeptA Θ Θ E ρ :=
  ⟨InvKept.refl Θ E ρ, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩

theorem InvKeptA.mono {Θ Θ' : CodeTy} {E F : BoCa.Loc → Prop} (hEF : ∀ l, E l → F l)
    {ρ : TRes K} (h : InvKeptA Θ Θ' E ρ) : InvKeptA Θ Θ' F ρ :=
  ⟨h.1.mono hEF, fun σ hσ m ζ l ξ hb hk hFm hFl =>
    h.2 σ hσ m ζ l ξ hb hk (fun c => hFm (hEF m c)) (fun c => hFl (hEF l c))⟩

/-- **At a re-typing agreeing where `ρ` holds a `mut` cell**, every code `InvKeptA` reads is
kept: a cell beneath an ancestor is a cell of `ρ` at depth. -/
theorem InvKeptA.of_agree {Θ Θ' : CodeTy} {E : BoCa.Loc → Prop} {ρ W : TRes K} (hW : MutOne W)
    (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) (hag : AgreeOn Θ Θ' ρ) :
    InvKeptA Θ Θ' E ρ :=
  ⟨InvKept.of_agree hW hsub hag, fun _ hσ _ _ l _ hb hk _ _ =>
    hag l ((hb.cellAt hW hσ hsub hk).holdsMut.1 hk)⟩

/-- **Along an update, `InvKeptA` composes**: an unmasked ancestor is kept by `UpdX`, and the
cell beneath it is carried along its walk. -/
theorem InvKeptA.trans {Θ₀ Θ₁ Θ₂ : CodeTy} {Θx : LocTy} (hK : K.Ext K') {E E' : BoCa.Loc → Prop}
    {ρ₀ : TRes K} {ρ₁ : TRes K'} (h₁ : InvKeptA Θ₀ Θ₁ E ρ₀) (hu : UpdX Θx E E' ρ₀ ρ₁)
    (h₂ : InvKeptA Θ₁ Θ₂ E' ρ₁) : InvKeptA Θ₀ Θ₂ E ρ₀ := by
  refine ⟨h₁.1.trans hu h₂.1, fun σ hσ m ζ l ξ hb hk hEm hEl => ?_⟩
  obtain ⟨σa, σ₁, hσa, hσ₁, hx⟩ := hu
  obtain rfl := ResUT.Flat.functional hσa hσ
  obtain ⟨hE'm, ζ', e', hxc⟩ := (hx m).1 ζ hb.1 (by rw [hb.2.1]; decide) hEm
  have hk' : ζ'.kind = Kind.imm := hxc.1.trans hb.2.1
  obtain ⟨ξ', hb', hs⟩ :=
    hb.rr_fwd hK e' hk' (hxc.2.2 hb.2.1).2 (flat_imm_walks hσ₁ e' hk')
  obtain ⟨eb, kb, ev, av, p, hev, hav, hp, hn⟩ := hb
  obtain ⟨φ, eφ, kφ⟩ := flat_beneath_nonown hσ eb kb hev hav hp hn
    (by rw [hk]; exact fun c => Kind.noConfusion c)
  obtain ⟨hE'l, -⟩ := (hx l).1 φ eφ kφ hEl
  rw [h₂.2 σ₁ hσ₁ m ζ' l ξ' hb' (hs.1.trans hk) hE'm hE'l,
    h₁.2 σa hσa m ζ l ξ ⟨eb, kb, ev, av, p, hev, hav, hp, hn⟩ hk hEm hEl]

/-- **Beside a frame**: the codes kept at the run's part, and the re-typing agreeing at the
frame's `mut` cells, keep the codes at the composite. An ancestor of the composite is an `imm`
operand's, over its witness (`compR_imm_source`). -/
theorem InvKeptA.frame {Θ Θ' : CodeTy} {E : BoCa.Loc → Prop} {ρ₁ ρ₂ ρ W : TRes K}
    (hc : ResUT.CompS ρ₁ ρ₂ ρ) (h₁ : InvKeptA Θ Θ' E ρ₁) (hW : MutOne W)
    (hsub : ∀ y φ, CellAt ρ₂ y φ → φ.kind = Kind.mut → CellAt W y φ) (hag : AgreeOn Θ Θ' ρ₂) :
    InvKeptA Θ Θ' E ρ := by
  refine ⟨h₁.1.frame hc hW hsub hag, fun σ hσ m ζ l ξ hb hk hEm hEl => ?_⟩
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hσc⟩ := BoLo.flat_compR hc hσ
  obtain ⟨φ, eφ | eφ, hle⟩ := compR_imm_source hσc hb.1 hb.2.1
  · exact h₁.2 σ₁ hσ₁ m φ l ξ (hb.of_wit eφ hle.1 hle.2.2.2.1.symm) hk hEm hEl
  · exact hag l (((hb.of_wit eφ hle.1 hle.2.2.2.1.symm).cellAt hW hσ₂ hsub hk).holdsMut.1 hk)

/-- **A cell beneath an ancestor the middle world absorbed keeps its code**, the world being the
frame `ρf` beside the run's middle `ρ₁`: the absorber is above an `imm` operand of
`⦇ρf⦈ ○ ⦇ρ₁⦈` with its witness. The run's operand carries the cell beneath it into the second
segment's `InvBeneath`; the frame's holds it at depth, where the re-typing agrees. -/
theorem InvBeneath.absorbed {Θ₁ Θ₂ : CodeTy} {Θx : LocTy} (hK : K.Ext K')
    {E' : BoCa.Loc → Prop} {σ : TRes K} {ρf ρ₁ fρ₁ : TRes K'} {τw : TRes K'}
    (h₂ : InvBeneath Θ₁ Θ₂ E' ρ₁) (hc : ResUT.CompS ρf ρ₁ fρ₁) (hτw : ResUT.Flat fρ₁ τw)
    {W : TRes K'} (hW : MutOne W)
    (hsub : ∀ y φ, CellAt ρf y φ → φ.kind = Kind.mut → CellAt W y φ) (hag : AgreeOn Θ₁ Θ₂ ρf)
    {m l : BoCa.Loc} {ζ ξ : TCell K} (hb : Beneath σ m ζ l ξ) (hk : ξ.kind = Kind.mut)
    {χ : TCell K'} (eχ : τw.get m = some χ) (ha : CellAbs Θx ζ χ) (hEm : ¬ E' m)
    (hEl : ¬ E' l) : Θ₂ l = Θ₁ l := by
  obtain ⟨σf, σ₁, hσf, hσ₁, hσc⟩ := BoLo.flat_compR hc hτw
  obtain ⟨φ, eφ | eφ, hle⟩ := compR_imm_source hσc eχ ha.2.1
  · obtain ⟨ξ', hb', hs⟩ := hb.rr_fwd hK eφ hle.1 (hle.2.2.2.1 ▸ ha.2.2.2.1)
      (flat_imm_walks hσf eφ hle.1)
    have hk' : ξ'.kind = Kind.mut := hs.1.trans hk
    exact hag l ((hb'.cellAt hW hσf hsub hk').holdsMut.1 hk')
  · obtain ⟨ξ', hb', hs⟩ := hb.rr_fwd hK eφ hle.1 (hle.2.2.2.1 ▸ ha.2.2.2.1)
      (flat_imm_walks hσ₁ eφ hle.1)
    exact h₂ σ₁ hσ₁ m φ l ξ' hb' (hs.1.trans hk) hEm hEl

/-- **Along a run beside a frame, `InvKeptA` composes**: the first segment `UpdA` from `ρ₀` to
`ρ₁` beside the middle world `ρf ● ρ₁`, the second segment's codes kept at `ρ₁`, and the
re-typing of the second segment agreeing at the frame (`TWd.Ext`'s `AgreeOn`). A start `mut`
cell kept into the middle chains as in `InvKept.trans`; one leaving with its ancestor, and a
cell beneath an ancestor the middle world absorbed, by `InvBeneath.absorbed`. -/
theorem InvKeptA.transA {Θ₀ Θ₁ Θ₂ : CodeTy} {Θx : LocTy} (hK : K.Ext K')
    {E E' : BoCa.Loc → Prop} {ρ₀ : TRes K} {ρf ρ₁ fρ₁ : TRes K'}
    (h₁ : InvKeptA Θ₀ Θ₁ E ρ₀) (hu : UpdA Θx E E' ρ₀ ρ₁ fρ₁) (h₂ : InvKeptA Θ₁ Θ₂ E' ρ₁)
    (hc : ResUT.CompS ρf ρ₁ fρ₁) {W : TRes K'} (hW : MutOne W)
    (hsub : ∀ y φ, CellAt ρf y φ → φ.kind = Kind.mut → CellAt W y φ) (hag : AgreeOn Θ₁ Θ₂ ρf) :
    InvKeptA Θ₀ Θ₂ E ρ₀ := by
  obtain ⟨σ, σ₁, τw, hσ, hσ₁, hτw, hx⟩ := hu
  have imm_ne : ∀ {ψ : TCell K}, ψ.kind = Kind.imm → ψ.kind ≠ Kind.own :=
    fun k c => Kind.noConfusion (k.symm.trans c)
  refine ⟨fun σ' hσ' l mc e hEl => ?_, fun σ' hσ' m ζ l ξ hb hk hEm hEl => ?_⟩
  · obtain rfl := ResUT.Flat.functional hσ hσ'
    rw [← h₁.1 σ hσ l mc e hEl]
    obtain ⟨hE'l, hd⟩ := (hx l).1 _ e (by simp [CellUT.kind]) hEl
    rcases hd with ⟨ψ', e', hxc⟩ | ⟨χ, -, ha⟩ | ⟨-, m, ζ, χ, hEm, hb, eχ, ha⟩
    · obtain ⟨m', rfl⟩ := hxc.mut_right
      exact h₂.1 σ₁ hσ₁ l m' e' hE'l
    · cases ha.1
    · obtain ⟨hE'm, -⟩ := (hx m).1 ζ hb.1 (imm_ne hb.2.1) hEm
      exact InvBeneath.absorbed hK h₂.2 hc hτw hW hsub hag hb rfl eχ ha hE'm hE'l
  · obtain rfl := ResUT.Flat.functional hσ hσ'
    rw [← h₁.2 σ hσ m ζ l ξ hb hk hEm hEl]
    have hE'l : ¬ E' l := by
      obtain ⟨eb, kb, ev, av, p, hev, hav, hp, hn⟩ := hb
      obtain ⟨φ, eφ, kφ⟩ := flat_beneath_nonown hσ eb kb hev hav hp hn
        (by rw [hk]; exact fun c => Kind.noConfusion c)
      exact ((hx l).1 φ eφ kφ hEl).1
    obtain ⟨hE'm, hd⟩ := (hx m).1 ζ hb.1 (imm_ne hb.2.1) hEm
    rcases hd with ⟨ζ', e', hxc⟩ | ⟨χ, eχ, ha⟩ | ⟨hkm, -⟩
    · have hk' : ζ'.kind = Kind.imm := hxc.1.trans hb.2.1
      obtain ⟨ξ', hb', hs⟩ :=
        hb.rr_fwd hK e' hk' (hxc.2.2 hb.2.1).2 (flat_imm_walks hσ₁ e' hk')
      exact h₂.2 σ₁ hσ₁ m ζ' l ξ' hb' (hs.1.trans hk) hE'm hE'l
    · exact InvBeneath.absorbed hK h₂.2 hc hτw hW hsub hag hb hk eχ ha hE'm hE'l
    · rw [hb.2.1] at hkm; cases hkm

/-! ### Row 5.27's `P̂` across a run along the walks -/

/-- **`UpdX.inv` at `UpdA`**: where the two flattenings carry a `mut` cell at an unmasked `ℓ`,
the two invariants are one code `A`, kept from `Θ` to `Θ′`, read at each side's world. -/
theorem UpdA.inv {Θx : LocTy} {Θ Θ' : CodeTy} {E E' : BoCa.Loc → Prop} {ρ : TRes K}
    {ρ' fρ' : TRes K'} (h : UpdA Θx E E' ρ ρ' fρ') (hm : MutCov (sem Θ) K ρ)
    (hm' : MutCov (sem Θ') K' ρ') (hk : InvKept Θ Θ' E ρ) :
    ∃ σ σ' τw, ResUT.Flat ρ σ ∧ ResUT.Flat ρ' σ' ∧ ResUT.Flat fρ' τw ∧
      (∀ l, XOptA Θx E E' σ σ' τw l) ∧
      ∀ l ψ ψ', σ.get l = some ψ → σ'.get l = some ψ' → ¬ E l → XInv Θ Θ' K K' l ψ ψ' := by
  obtain ⟨σ, σ', τw, hσ, hσ', hτw, hx⟩ := h
  obtain ⟨hc, W, hW, hsub⟩ := hm
  obtain ⟨hc', W', hW', hsub'⟩ := hm'
  refine ⟨σ, σ', τw, hσ, hσ', hτw, hx, fun l ψ ψ' e e' hE m m' hψ hψ' => ?_⟩
  subst hψ hψ'
  obtain ⟨τ, hΘ, hP⟩ := flat_mut_inv hW hsub hc hσ e
  obtain ⟨τ', hΘ', hP'⟩ := flat_mut_inv hW' hsub' hc' hσ' e'
  obtain ⟨A, hA, rfl⟩ := sem_some hΘ
  obtain ⟨A', hA', rfl⟩ := sem_some hΘ'
  have hl := hk σ hσ l m e hE
  rw [hl, hA] at hA'
  cases Option.some.inj hA'
  exact ⟨A, hA, hl.trans hA, hP, hP'⟩

/-! ### The frame condition along the walks -/

/-- **`FdEsc` along `↭`, read along the walks** (R5). An end non-`own` cell outside the end's
mask comes from the start's cell there, or sat beneath a start ancestor, which puts a non-`own`
cell in `⦇ρ⦈` there (`flat_beneath_nonown`); `FdEsc` at the start refuses both. -/
theorem fdEsc_of_updA {w w' : TWd} (_hE : w.K.Ext w'.K) {ρ : TRes w.K} {O : List (FrameRecT w.K)}
    {p : FrameRecT w.K} (hpv : ResUT.Valid p.R) (h₀ : FdEsc p.le p.R ρ)
    {ρf' ρ' fρ' : TRes w'.K} {ps' O' psF' : List (FrameRecT w'.K)} {rs' : List (FrameRecT w'.K)}
    (hT : TWNT w'.K w'.Θ w'.tc fρ' ps' rs') (hc : ResUT.CompS ρf' ρ' fρ')
    (hS : SplitT ps' O' psF') {p' : FrameRecT w'.K} (hp' : p' ∈ psF') (hpp : RecRR w'.Θ p p')
    (hu : UpdA (sem w'.Θ) (recMask O) (recMask O') ρ ρ' fρ') : FdEsc p'.le p'.R ρ' := by
  obtain ⟨σ, σ', τw, hσ, hσ', -, hx⟩ := hu
  refine fdEsc_of_end hpv h₀ hT hc hS hp' hpp ⟨σ, σ', hσ, hσ', fun x hx' ψ e hk => ?_⟩
  obtain ⟨-, hd⟩ := (hx x).2 ψ e hk hx'
  rcases hd with ⟨ψ₀, e₀, -⟩ | ⟨hkm, m, ζ, ξ, hb, hxc⟩
  · exact ⟨ψ₀, e₀⟩
  · obtain ⟨eb, kb, ev, av, q, hev, hav, hq, hn⟩ := hb
    obtain ⟨φ, eφ, -⟩ := flat_beneath_nonown hσ eb kb hev hav hq hn
      (by rw [← hxc.1, hkm]; exact fun c => Kind.noConfusion c)
    exact ⟨φ, eφ⟩

end BoCa.Fig16.Tree.Wp

end
