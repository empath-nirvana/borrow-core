import Core.Chain.SI.LinDisj

/-!
# `Ext` implies `extF` at typed worlds

**New design, not a transcription.** `Core`'s continuation share is resumed at every list `ls′`
with `Ext ls ls′ ρ`; the frame rules across stops resume at `extF ls ls′ ρ` (`SI/ExtF.lean`). At a
share `ρ` contained in a tagged `TWNC` world at `ls`, with `TWNC` holding at `ls′`, the first
implies the second (`ext_extF`): `extF` refuses no resumption `Core` allows.

## The proof

A frozen location `m` of `ρ` is an `imm` cell of `ρ`, which `Keeps` handles, or it lies inside
the witness of a top cell `ψ₀` of `ρ`, `imm` or `mut`. Inside that witness, `m` has a deepest
`imm` ancestor, or none (`inDom_imm_or_xex`):

* **A nested `imm` cell `ψ₁` at `m₁`, with `m = m₁` or `m` exclusive in `ψ₁`'s witness.** `ψ₁`
  lies in `ψ₀`'s witness, so it outlives `@ψ₀` strictly (`NCell.inStratum`). It is a view of
  `ag(W)` (`NCell.icp`). Every record relevant at `m` is tagged no shorter than `ψ₁`
  (`tag_ge_nested`): at `m = m₁` by `FrameLife`, as `lifeBound_of_tagged` reads it; otherwise the
  record is in the lineage of the record `ψ₁`'s view is classified by (`desc_of_xex`), whose
  root's frame bounds `ψ₁`. So the record is tagged strictly longer than `@ψ₀`, and `Ext`'s
  lifetime clause at `@ψ₀` keeps it.
* **No `imm` ancestor: `m` exclusive in `ψ₀`'s witness.** If `ψ₀` is `mut`, `m` is an exclusive
  location of `ρ` and no record names it (`not_relAt_xex`). If `ψ₀` is `imm`, its view is
  classified by a record `q` relevant to `ρ` at the top, which `Keeps` keeps; the record at `m`
  is in `q`'s lineage (`desc_of_xex`), and `TI`'s closure at `ls′` keeps it with `q`.

`desc_of_xex` reads two facts of the records proper, both fixed when the frame is taken and kept
by every step: no two records proper share a location their lineages hold exclusively at any
depth, or a frame cell (`DLinDisj`, `LinDisj` read through `mut` witnesses); and a record
proper's escrow is exclusively walkable, without the frame's cell (`EscEx`). In one escrow an
exclusive location is reached along one path (`xpath_unique`), and a lineage path names one
record (`LinPath.functional`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-! ### Paths -/

theorem XPath.append {ρ σ τ : WRes} {p p' : List Loc} (h : XPath ρ p σ) (h' : XPath σ p' τ) :
    XPath ρ (p ++ p') τ := by
  induction h with
  | nil => exact h'
  | cons e k _ ih => exact XPath.cons e k (ih h')

theorem LinPath.append {r d e : FrameRec} {a b : List Loc} (h : LinPath r a d)
    (h' : LinPath d b e) : LinPath r (a ++ b) e := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact LinPath.cons hs (ih h')

theorem LinPath.split {e : FrameRec} {b : List Loc} :
    ∀ {a : List Loc} {r : FrameRec}, LinPath r (a ++ b) e → ∃ d, LinPath r a d ∧ LinPath d b e
  | [], r, h => ⟨r, LinPath.nil r, h⟩
  | x :: a, r, h => by
      obtain ⟨d', hs, rfl, t⟩ := LinPath.inv_cons h
      obtain ⟨d, h₁, h₂⟩ := LinPath.split t
      exact ⟨d, LinPath.cons hs h₁, h₂⟩

theorem DescR.trans {r d e : FrameRec} (h : DescR r d) (h' : DescR d e) : DescR r e := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  exact ⟨_, LinPath.append ha hb⟩

/-- `ex(σ)_○` in `ag(W)` puts `ex(τ)_○` there, for `τ` reached through `mut` witnesses. -/
theorem exIn_xpath {W σ τ : WRes} {p : List Loc} (h : ExIn W σ) (hp : XPath σ p τ) :
    ExIn W τ := by
  induction hp with
  | nil => exact h
  | cons e k _ ih => exact ih (exIn_mut h e k).1

/-! ### Locations held exclusively by a lineage, at any depth -/

/-- `m` is `p`'s frame cell, or an exclusive location, at any depth, of the escrow of a member of
`p`'s lineage. -/
def DLin (p : FrameRec) (m : Loc) : Prop :=
  m = p.le ∨ ∃ d, DescR p d ∧ XEx d.R m

/-- **Records proper hold disjoint locations**: `LinDisj` read through `mut` witnesses, with the
frame cells. -/
def DLinDisj (ps : List FrameRec) : Prop :=
  ∀ p₁ ∈ ps, ∀ p₂ ∈ ps, ∀ m, DLin p₁ m → DLin p₂ m → p₁ = p₂

/-- **A record proper's escrow is exclusively walkable, without the frame's cell.** -/
def EscEx (ps : List FrameRec) : Prop :=
  ∀ p ∈ ps, ∃ e, ExS p.R e ∧ e.get p.le = none

/-- A location a record is relevant at is held by every root of its lineage. -/
theorem dLin_of_relAt {p r : FrameRec} (h : DescR p r) {m : Loc} (hm : RelAt r m) : DLin p m := by
  rcases hm with rfl | ⟨q, S, u, hch⟩
  · rcases h.cases with rfl | ⟨q, hq, hqq⟩
    · exact Or.inl rfl
    · obtain ⟨f, hf, -, -, ζ, eζ, kζ, -⟩ := hqq.last hq
      exact Or.inr ⟨f, hf, [], f.R, ζ, XPath.nil _, eζ, by rw [kζ]; simp⟩
  · exact Or.inr ⟨r, h, [], r.R, _, XPath.nil _, hch.own, by simp⟩

/-- A new frame's locations are exclusive locations of the part it is taken at. -/
theorem xex_of_dLin_frame {X R : WRes} {l : Loc} {v : Val} {T : VTy}
    {δ : BoCa.Lifetime.LSub} (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) {m : Loc}
    (h : DLin ⟨l, v, R, T, δ⟩ m) : XEx X m := by
  rcases h with rfl | ⟨d, ⟨q, hq⟩, p, τ, ζ, hp, eτ, kτ⟩
  · exact ⟨[], X, _, XPath.nil X,
      (ResU.CompS.get_left_of_ne_imm hX (ResU.single_get_self _ _) (by simp)).2, by simp⟩
  · exact XEx.of_compS_right hX ⟨q ++ p, τ, ζ, XPath.append hq.xpath hp, eτ, kτ⟩

/-- An old record proper's locations carry views of `ag(W)`. -/
theorem ag_of_dLin {W : WRes} {ps rs : List FrameRec} (hTI : TI W ps rs) {p : FrameRec}
    (hp : p ∈ ps) {m : Loc} (h : DLin p m) {a : WRes} (ha : AgW W a) : ∃ ξ, a.get m = some ξ := by
  rcases h with rfl | ⟨d, hd, q, τ, ζ, hq, eτ, kτ⟩
  · obtain ⟨ψ, e, -⟩ := hTI.2.1 p hp a ha
    exact ⟨ψ, e⟩
  · have hdR : d ∈ rs := (hTI.2.2.2.2.2.2.1 d).mpr ⟨p, hp, hd⟩
    exact exIn_support (exIn_xpath (hTI.exIn hdR) hq) eτ kτ a ha

theorem dLinDisj_frame {W X Z R : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val}
    {T : VTy} {δ : BoCa.Lifetime.LSub} (hvW : ResU.Valid W) (hTI : TI W ps rs)
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (h : DLinDisj ps) : DLinDisj (⟨l, v, R, T, δ⟩ :: ps) := by
  have hXW : ResU.Le X W := ⟨Z, hW⟩
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW
  have cross : ∀ p₁ ∈ ps, ∀ m, DLin p₁ m → DLin ⟨l, v, R, T, δ⟩ m → False := by
    intro p₁ hp₁ m h₁ h₂
    obtain ⟨q, τ, ζ, hq, eτ, kτ⟩ := xex_of_dLin_frame hX h₂
    obtain ⟨ξ, eξ⟩ := ag_of_dLin hTI hp₁ h₁ haW
    exact ex_ag_disjoint hvW heW haW (xpath_ex_part hXW heW hq eτ kτ) eξ
  intro p₁ hp₁ p₂ hp₂ m h₁ h₂
  rcases List.mem_cons.mp hp₁ with rfl | hp₁ <;> rcases List.mem_cons.mp hp₂ with rfl | hp₂
  · rfl
  · exact (cross p₂ hp₂ m h₂ h₁).elim
  · exact (cross p₁ hp₁ m h₁ h₂).elim
  · exact h p₁ hp₁ p₂ hp₂ m h₁ h₂

/-- **Every `TWN` world's records proper hold disjoint locations.** -/
theorem TWN.dLinDisj {W : WRes} {ps rs : List FrameRec} (h : TWN W ps rs) : DLinDisj ps := by
  induction h with
  | empty => intro p hp; exact absurd hp (by simp)
  | immFrame T δ _ hW₀ _ hX hW _ _ _ _ ih => exact dLinDisj_frame hW₀.valid hW₀.inv hX hW ih
  | immEnd r _ _ _ _ _ _ hps _ ih =>
      exact fun p hp p' hp' m h₁ h₂ => ih p ((hps p).mp hp).1 p' ((hps p').mp hp').1 m h₁ h₂
  | alloc _ _ _ _ _ ih => exact ih
  | reb _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | rebDeep _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | mutFold _ _ _ _ _ ih => exact ih
  | mutUnfold _ _ _ _ _ ih => exact ih
  | free _ _ _ ih => exact ih
  | store _ _ _ _ ih => exact ih
  | rebEnd _ _ _ _ _ _ _ ih => exact ih
  | rebEndDeep _ _ _ _ _ _ _ _ ih => exact ih

/-- **Every `TWN` world's records proper have exclusively walkable escrows**, without the frame's
cell (`frame_ex`, at the frame's entry). -/
theorem TWN.escEx {W : WRes} {ps rs : List FrameRec} (h : TWN W ps rs) : EscEx ps := by
  induction h with
  | empty => intro p hp; exact absurd hp (by simp)
  | immFrame T δ _ hW₀ _ hX hW _ _ _ _ ih =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · obtain ⟨σ₀, eW, aW, heW, -, -⟩ := id hW₀.valid
        obtain ⟨eR, heR, -, hl⟩ := frame_ex hX hW heW
        exact ⟨eR, heR, hl⟩
      · exact ih p hp
  | immEnd r _ _ _ _ _ _ hps _ ih => exact fun p hp => ih p ((hps p).mp hp).1
  | alloc _ _ _ _ _ ih => exact ih
  | reb _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | rebDeep _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | mutFold _ _ _ _ _ ih => exact ih
  | mutUnfold _ _ _ _ _ ih => exact ih
  | free _ _ _ ih => exact ih
  | store _ _ _ _ ih => exact ih
  | rebEnd _ _ _ _ _ _ _ ih => exact ih
  | rebEndDeep _ _ _ _ _ _ _ _ ih => exact ih

/-! ### Cells at any depth -/

/-- `ψ` sits at `m` in `σ`, or at any depth inside the witness of a non-`own` cell of `σ`. -/
inductive NCell : WRes → Loc → CellU Loc Val → Prop
  | top {σ : WRes} {m : Loc} {ψ : CellU Loc Val} : σ.get m = some ψ → NCell σ m ψ
  | wit {σ : WRes} {m m' : Loc} {ψ ψ' : CellU Loc Val} :
      σ.get m' = some ψ' → ψ'.kind ≠ Kind.own → NCell ψ'.wit m ψ → NCell σ m ψ

/-- **A cell at any depth of `σ` has its `imm` counterpart in every `○`-whole of `ag(σ)`**: `ag`
holds the `imm` cells of `σ`, and `ag` of every witness of a non-`own` cell. -/
theorem NCell.icp {σ : WRes} {m : Loc} {ψ : CellU Loc Val} (h : NCell σ m ψ) :
    ∀ {a b : WRes}, AgW σ a → AllICp b a → ICp b m ψ := by
  induction h with
  | top e => intro a b ha hb; exact icp_trans (icpAt_agW ha _ _ e) (hb _)
  | @wit σ m m' ψ ψ' e k _ ih =>
      intro a b ha hb
      cases hk : ψ'.kind with
      | own => exact absurd hk k
      | imm =>
          obtain ⟨ev, av, p, z, -, hav, hp, hz⟩ := AgW.imm_wit_le ha e hk
          exact ih hav (fun x => icpAt_trans (icpAt_right hp x) (icpAt_trans (icpAt_left hz x) (hb x)))
      | «mut» =>
          obtain ⟨av, z, hav, hz⟩ := AgW.mut_wit_le ha e hk
          exact ih hav (fun x => icpAt_trans (icpAt_left hz x) (hb x))

theorem CellU.lt_at_of_inStratum {ψ : CellU Loc Val} (hk : ψ.kind ≠ Kind.own) {b : Life}
    (h : ψ.InStratum b) : b < ψ.at := by
  cases ψ with
  | own v => exact absurd rfl hk
  | imm i => exact h
  | «mut» m => exact h

/-- **A cell at any depth lies in every stratum its resource does**: a witness lies in the
stratum of its cell's lifetime. -/
theorem NCell.inStratum {σ : WRes} {m : Loc} {ψ : CellU Loc Val} (h : NCell σ m ψ) :
    ∀ {b : Life}, σ.InStratum b → ψ.InStratum b := by
  induction h with
  | top e => intro b hσ; exact hσ _ _ e
  | @wit σ m m' ψ ψ' e k _ ih =>
      intro b hσ
      exact ih (ResU.InStratum.mono (le_of_lt (CellU.lt_at_of_inStratum k (hσ _ _ e)))
        (CellU.wit_inStratum_at ψ'))

theorem Frz.inDom {ρ : WRes} {m : Loc} (h : Frz ρ m) : InDom ρ m := by
  induction h with
  | imm e _ => exact InDom.top e
  | inImm e k hd => exact InDom.wit e (by rw [k]; simp) hd
  | inMut e k _ ih => exact InDom.wit e (by rw [k]; simp) ih

/-- **The deepest `imm` ancestor.** A location at any depth of `σ` is an `imm` cell at any
depth, or exclusive in such a cell's witness; or it is exclusive in `σ`. -/
theorem inDom_imm_or_xex {σ : WRes} {m : Loc} (h : InDom σ m) :
    (∃ m₁ ψ₁, NCell σ m₁ ψ₁ ∧ ψ₁.kind = Kind.imm ∧ (m = m₁ ∨ XEx ψ₁.wit m)) ∨ XEx σ m := by
  induction h with
  | @top σ m ψ e =>
      by_cases k : ψ.kind = Kind.imm
      · exact Or.inl ⟨m, ψ, NCell.top e, k, Or.inl rfl⟩
      · exact Or.inr ⟨[], σ, ψ, XPath.nil σ, e, k⟩
  | @wit σ m m' ψ e k _ ih =>
      rcases ih with ⟨m₁, ψ₁, hN, k₁, hc⟩ | ⟨p, τ, ζ, hp, eτ, kτ⟩
      · exact Or.inl ⟨m₁, ψ₁, NCell.wit e k hN, k₁, hc⟩
      · cases hkk : ψ.kind with
        | own => exact absurd hkk k
        | imm => exact Or.inl ⟨m', ψ, NCell.top e, hkk, Or.inr ⟨p, τ, ζ, hp, eτ, kτ⟩⟩
        | «mut» => exact Or.inr ⟨m' :: p, τ, ζ, XPath.cons e hkk hp, eτ, kτ⟩

/-! ### Chain views -/

/-- `chainWit_excl` with the cell named: a chain view's escrow's exclusive cells are the
record's escrow's, the same cells. -/
theorem chainWit_eq {W : WRes} {ps rs : List FrameRec} (hTI : TI W ps rs) {r : FrameRec}
    (hr : r ∈ rs) {a : WRes} (ha : AgW W a) :
    ∀ {n p l S u}, ChainD r.R r.T r.v n p l S u → ∀ ψ : CellU Loc Val, a.get l = some ψ →
      ψ.kind ≠ Kind.own → ∀ m (ζ : CellU Loc Val), ψ.wit.get m = some ζ → ζ.kind ≠ Kind.imm →
      r.R.get m = some ζ := by
  have hD : DeepInv W r := hTI.1.1 r hr
  intro n p l S u h
  induction h with
  | @one l S u hp e =>
      intro ψ eψ kψ m ζ eζ kζ
      obtain ⟨-, -, -, h4, -⟩ := hD none l S u (Chain.one hp e) a ha ψ eψ kψ
      obtain ⟨q, ⟨τ, hτ⟩, -, hw⟩ := h4 rfl
      rw [hw] at eζ
      exact (ResU.CompS.get_left_of_ne_imm hτ (get_of_del eζ) kζ).2
  | @snoc n p l₀ S₀ u₀ l S u c hp e ih =>
      intro ψ eψ kψ m ζ eζ kζ
      obtain ⟨-, -, -, -, h5⟩ := hD (some l₀) l S u (c.chain.snoc hp e) a ha ψ eψ kψ
      obtain ⟨ψ₀, eψ₀, kψ₀, q, ⟨τ, hτ⟩, -, hw⟩ := h5 l₀ rfl
      rw [hw] at eζ
      exact ih ψ₀ eψ₀ kψ₀ m ζ (ResU.CompS.get_left_of_ne_imm hτ (get_of_del eζ) kζ).2 kζ

/-- An exclusive location of `χ` is one of `R` when `χ`'s exclusive cells are `R`'s. -/
theorem XEx.of_excl_eq {χ R : WRes}
    (E : ∀ m (ζ : CellU Loc Val), χ.get m = some ζ → ζ.kind ≠ Kind.imm → R.get m = some ζ)
    {m : Loc} (h : XEx χ m) : XEx R m := by
  obtain ⟨p, τ, ζ, hp, eτ, kτ⟩ := h
  cases hp with
  | nil => exact ⟨[], R, ζ, XPath.nil R, E m ζ eτ kτ, kτ⟩
  | @cons _ _ m' ψ' q e k hq =>
      exact ⟨m' :: q, τ, ζ, XPath.cons (E m' ψ' e (by rw [k]; simp)) k hq, eτ, kτ⟩

/-! ### Records named inside a view's witness -/

/-- **A record relevant at an exclusive location of an `imm` view's witness is in the lineage of
the record the view is classified by.** The view is at that record's cell, over its escrow, or at
one of its chain positions, over a piece of its escrow (`chainWit_eq`); either way the location is
exclusive in the escrow. The two records' roots hold the location, so they are one (`DLinDisj`);
in the root's escrow the location is reached along one path (`xpath_unique`, `EscEx`), which
passes through the classifying record (`LinPath.functional`). -/
theorem desc_of_xex {W : WRes} {ps rs : List FrameRec} (hT : TWN W ps rs) {a : WRes}
    (ha : AgW W a) {m₁ : Loc} {ζ : CellU Loc Val} (eζ : a.get m₁ = some ζ)
    (kζ : ζ.kind = Kind.imm) {m : Loc} (hx : XEx ζ.wit m) {r : FrameRec} (hr : r ∈ rs)
    (hm : RelAt r m) : ∃ q ∈ rs, RelAt q m₁ ∧ DescR q r := by
  have hTI := hT.inv
  have hcl := hTI.2.2.2.2.2.2.1
  obtain ⟨q, hq, hrelq, hxq⟩ : ∃ q ∈ rs, RelAt q m₁ ∧ XEx q.R m := by
    rcases hTI.2.2.2.2.2.2.2 a ha m₁ ζ eζ kζ with ⟨q, hq, rfl, -, hw⟩ | ⟨q, hq, p, S, u, hch⟩
    · exact ⟨q, hq, Or.inl rfl, hw ▸ hx⟩
    · obtain ⟨n, hn⟩ := Chain.chainD hch
      exact ⟨q, hq, Or.inr ⟨p, S, u, hch⟩,
        XEx.of_excl_eq (chainWit_eq hTI hq ha hn ζ eζ (by rw [kζ]; simp)) hx⟩
  refine ⟨q, hq, hrelq, ?_⟩
  obtain ⟨pq, hpq, hdq⟩ := (hcl q).mp hq
  obtain ⟨pr, hpr, hdr⟩ := (hcl r).mp hr
  obtain rfl : pq = pr :=
    hT.dLinDisj pq hpq pr hpr m (Or.inr ⟨q, hdq, hxq⟩) (dLin_of_relAt hdr hm)
  obtain ⟨e, he, hle⟩ := hT.escEx pq hpq
  have hpR : pq ∈ rs := (hcl pq).mpr ⟨pq, hpq, DescR.refl _⟩
  obtain ⟨hshape, hadm⟩ := hTI.1.2.2.2.1 pq hpR
  obtain ⟨a₀, ha₀⟩ := hdq
  obtain ⟨b, τ, ζm, hb, eτ, kτ⟩ := hxq
  have hpath : XPath pq.R (a₀ ++ b) τ := XPath.append ha₀.xpath hb
  -- a lineage path along `a₀ ++ b` passes through `q`
  have through : ∀ {d : FrameRec}, LinPath pq (a₀ ++ b) d → DescR q d := by
    intro d hd
    obtain ⟨q', h₁, h₂⟩ := LinPath.split hd
    obtain rfl : q' = q := h₁.functional hshape hadm ha₀
    exact ⟨b, h₂⟩
  rcases hm with rfl | ⟨c, S, u, hch⟩
  · rcases hdr.cases with rfl | ⟨pp, hpp, hlin⟩
    · have := xpath_ex he hpath eτ kτ
      rw [hle] at this; cases this
    · obtain ⟨f, ⟨pf, hpf⟩, hsub⟩ := LinPath.last hlin hpp
      obtain ⟨-, -, ζf, eζf, kζf, -⟩ := id hsub
      obtain rfl : a₀ ++ b = pf :=
        xpath_unique he hpath hpf.xpath eτ kτ eζf (by rw [kζf]; simp)
      exact DescR.sub (through hpf) hsub
  · obtain ⟨pr', hpr'⟩ := hdr
    obtain rfl : a₀ ++ b = pr' := xpath_unique he hpath hpr'.xpath eτ kτ hch.own (by simp)
    exact through hpr'

/-- **A record relevant inside a view is tagged no shorter than the view.** At the view's own
location, `FrameLife` as `lifeBound_of_tagged` reads it; inside its witness, the record is in the
lineage of the view's classifying record (`desc_of_xex`), whose root is the record's
(`DLinDisj`), and whose location is that root's. -/
theorem tag_ge_nested {W : WRes} {ps : List FrameRec} {ls : List SRec}
    (hT : TWN W ps (rsOf ls)) (htag : Tagged W ps ls) {a : WRes} (ha : AgW W a) {m₁ : Loc}
    {ψ₁ : CellU Loc Val} (hicp : ICp a m₁ ψ₁) {s₁ : LSet} (hs₁ : ψ₁.lsOf = some s₁) {m : Loc}
    (hm₁ : m = m₁ ∨ XEx ψ₁.wit m) {r : FrameRec} {t : Life} (hrt : (r, t) ∈ ls)
    (hm : RelAt r m) : s₁.meet ⊑ t := by
  obtain ⟨p, hp, hpr, hFL⟩ := htag (r, t) hrt
  obtain ⟨ζ, t', eζ, ht', hmem⟩ := hicp.ls hs₁ s₁.meet_mem
  have hloc : (∃ x, x = p ∧ m₁ = p.le) ∨ LinLoc p m₁ := by
    rcases hm₁ with rfl | hx
    · rcases linLoc_of_rel hpr hm with ⟨-, h⟩ | h
      · exact Or.inl ⟨p, rfl, h⟩
      · exact Or.inr h
    · obtain ⟨ζ', eζ', kζ', -, wζ', -⟩ := hicp (CellU.kind_of_lsOf hs₁)
      have hr : r ∈ rsOf ls := mem_rsOf.mpr ⟨t, hrt⟩
      obtain ⟨q, hq, hrelq, hqr⟩ := desc_of_xex hT ha eζ' kζ' (by rw [wζ']; exact hx) hr hm
      obtain ⟨pq, hpq, hdq⟩ := (hT.inv.2.2.2.2.2.2.1 q).mp hq
      obtain rfl : pq = p := hT.dLinDisj pq hpq p hp m
        (dLin_of_relAt (DescR.trans hdq hqr) hm) (dLin_of_relAt hpr hm)
      rcases linLoc_of_rel hdq hrelq with ⟨-, h⟩ | h
      · exact Or.inl ⟨pq, rfl, h⟩
      · exact Or.inr h
  rcases hloc with ⟨-, -, h⟩ | hL
  · rw [h] at eζ
    rw [hFL.1 a ha ζ t' eζ ht' s₁.meet hmem]
  · exact hFL.2 a ha m₁ hL ζ t' eζ ht' s₁.meet hmem

/-! ### The theorem -/

/-- **`Ext` implies `extF` at typed worlds.** At a share `ρ` contained in a tagged `TWNC` world
at `ls`, every list `ls′` at which `TWNC` holds and which `Ext` allows, `extF` allows. -/
theorem ext_extF {W W' ρ : WRes} {ps ps' : List FrameRec} {ls ls' : List SRec}
    (hT : TWNC W ps (rsOf ls)) (htag : Tagged W ps ls) (hρ : ResU.Le ρ W)
    (hT' : TWNC W' ps' (rsOf ls')) (h : Ext ls ls' ρ) : extF ls ls' ρ := by
  have hN := hT.toN
  have hTI := hT.inv
  have hv := hT.valid
  have hcl' := hT'.inv.2.2.2.2.2.2.1
  obtain ⟨aW, haW⟩ := agW_of_valid hv
  obtain ⟨τ, hτ⟩ := id hρ
  obtain ⟨aρ, aτ, haρ, -, hcρ⟩ := (AgW.split hτ).mp haW
  have hρa : AllICp aW aρ := fun x => icpAt_left hcρ x
  intro r hr ⟨m, hf, hm⟩
  have key : ∀ {m₀ : Loc} {ψ₀ : CellU Loc Val}, ρ.get m₀ = some ψ₀ → ψ₀.kind ≠ Kind.own →
      InDom ψ₀.wit m → r ∈ rsOf ls' := by
    intro m₀ ψ₀ e₀ k₀ hd
    rcases inDom_imm_or_xex hd with ⟨m₁, ψ₁, hN₁, k₁, hc⟩ | hx
    · obtain ⟨s₁, hs₁⟩ := lsOf_of_imm k₁
      have hicp : ICp aW m₁ ψ₁ := (NCell.wit e₀ k₀ hN₁).icp haρ hρa
      have hlow : s₁.meet ⊐ ψ₀.at :=
        CellU.sqsupset_of_lsOf hs₁ (hN₁.inStratum (CellU.wit_inStratum_at ψ₀))
      obtain ⟨t, ht⟩ := mem_rsOf.mp hr
      have hge := tag_ge_nested hN htag haW hicp hs₁ hc ht hm
      exact mem_rsOf.mpr ⟨t, (h.2 ψ₀.at ⟨m₀, ψ₀, e₀, k₀, le_rfl⟩ (r, t)
        (lt_of_lt_of_le hlow hge)).mp ht⟩
    · cases hk : ψ₀.kind with
      | own => exact absurd hk k₀
      | «mut» =>
          obtain ⟨p, τ', ζ, hp, eτ, kτ⟩ := hx
          exact (not_relAt_xex hv hTI hρ hr ⟨m₀ :: p, τ', ζ, XPath.cons e₀ hk hp, eτ, kτ⟩
            hm).elim
      | imm =>
          obtain ⟨ζ₀, eζ₀, kζ₀, -, wζ₀, -⟩ := (icp_trans (icpAt_agW haρ m₀ ψ₀ e₀) (hρa m₀)) hk
          obtain ⟨q, hq, hrelq, hqr⟩ := desc_of_xex hN haW eζ₀ kζ₀ (by rw [wζ₀]; exact hx) hr hm
          have hq' : q ∈ rsOf ls' := h.1 q hq ⟨m₀, ψ₀, e₀, hk, hrelq⟩
          obtain ⟨p', hp', hdq⟩ := (hcl' q).mp hq'
          exact (hcl' r).mpr ⟨p', hp', DescR.trans hdq hqr⟩
  cases hf with
  | imm e k => exact h.1 r hr ⟨m, _, e, k, hm⟩
  | inImm e k hd => exact key e (by rw [k]; simp) hd
  | inMut e k hf => exact key e (by rw [k]; simp) hf.inDom

end BoCa.Fig16.LogRel.Core.Chain.SI

end
