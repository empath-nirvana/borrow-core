import Support.Model.Tree.World.StepKeep

/-!
# `ExtLT` implies `extFT` at typed tree worlds

`[spec §62]`. Core's continuation share is resumed at every list `ls′` with `Ext ls ls′ ρ`
(`Core/FrameRecords.lean`). Over the tree carrier that condition is `ExtLT`: the records
relevant to `ρ` kept (`KeepsT`), and the records whose frames are strictly longer-lived than a
lifetime of a borrow cell of `ρ` exactly the same. A stored continuation resumes at `extFT ls ls′ ρ`
(`World/ExtF.lean`). At a share `ρ` inside a tagged `TWNT` world at `ls`, with `TWNT` holding at
`ls′`, the first implies the second (`ext_extFT`): `extFT` refuses no resumption the tree world's
own extension allows.

## The proof

A frozen location `m` of `ρ` is an `imm` cell of `ρ`, which `KeepsT` handles, or it lies inside
the witness of a top cell `ψ₀` of `ρ`, `imm` or `mut`. Inside that witness, `m` has a deepest
`imm` ancestor, or none (`inDomT_imm_or_xex`):

* **A nested `imm` cell `ψ₁` at `m₁`, with `m = m₁` or `m` exclusive in `ψ₁`'s witness.** `ψ₁`
  lies at depth in `ψ₀`'s witness, so each of its lifetimes is strictly above each lifetime `y`
  of `ψ₀` (`CellAt.inStratum`). Its view in `ag(W)` (`cellAt_imm_icp`) carries those lifetimes,
  and every record relevant at `m` is tagged no shorter than them (`tag_ge_nestedT`). So the
  record's tag is strictly above `y`, and `ExtLT`'s lifetime clause at `y` keeps it.
* **No `imm` ancestor: `m` exclusive in `ψ₀`'s witness.** If `ψ₀` is `mut`, `m` is an exclusive
  location of `ρ` and no record names it (`not_relAt_xexT`). If `ψ₀` is `imm`, its view is
  classified by a record `q` relevant to `ρ` at the top, which `KeepsT` keeps; the record at `m`
  is in `q`'s lineage (`desc_of_xexT`), and `TIT`'s closure at `ls′` keeps it with `q`.

**The lifetime clause on one branch.** `ExtLT`'s lifetime clause constrains only the records
whose tags are strictly above a lifetime of a borrow cell of `ρ`; records on branches
incomparable with that lifetime are left free. The proof never reaches them: the tag it bounds is
reached from `y` by a chain `y ⊏ z ⊑ t` (`z` a lifetime of the nested view, `t` the record's tag,
`z ⊑ t` by `FrameLifeT` of the record proper `TaggedT` names), so the record it asks about is
always comparable with `y`.

**Departure (D10, `docs/new-core/scope-781.md` §8).** The chain proof (`SI/ExtExtF.lean` on the
spike branch) reads `desc_of_xex` off two facts it establishes by induction on the typed world:
`DLinDisj` (no two records proper hold a location of their lineages, or a frame cell, in common)
and `EscEx` (a record proper's escrow is exclusively walkable without its frame cell), with
`xpath_unique` and `LinPath.functional`. Over the tree those facts are not ported. Their role is
taken by results already proved of `TWNT`, its `reread` case included: one owner for every
exclusive cell of the records' escrows (`TWNT.exclUnique`), two ancestors of one record
comparable (`desc_comparable`), a record proper no proper sub-record (`not_desc_proper`), and a
lent location no lineage location (`le_not_linLoc`). So `desc_of_xexT` reads the owner of the
cell at `m` off `ExclUniqueT` directly, rather than through the uniqueness of a path in the
root's escrow. No printed technique is replaced: the chain statements are in-house designs.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-! ### The tree world's own extension -/

/-- `r` is relevant to `ρ` as `Core/FrameRecords.lean`'s `Rel` reads it: an `imm` cell of `ρ` at a
place `Coh` looks for `r`. -/
def RelT (r : FrameRecT K) (ρ : TRes K) : Prop :=
  ∃ (m : BoCa.Loc) (ψ : TCell K), ρ.get m = some ψ ∧ ψ.kind = Kind.imm ∧ RelAtT r m

/-- `Core/FrameRecords.lean`'s `Keeps` over the tree carrier. -/
def KeepsT (rs rs' : List (FrameRecT K)) (ρ : TRes K) : Prop :=
  ∀ r ∈ rs, RelT r ρ → r ∈ rs'

/-- `Core/FrameRecords.lean`'s `CellIn` read in `K`: a borrow cell of `ρ` one of whose lifetimes is
`⊑ b` (`@ψ ⊑ b`, `@ψ` the meet of the cell's set, read at a member). -/
def CellInT (ρ : TRes K) (b : Life) : Prop :=
  ∃ (m : BoCa.Loc) (ψ : TCell K) (s : TSet), ρ.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧
    ψ.lsOf = some s ∧ ∃ y ∈ s.set, K.le y b

/-- **`Core/FrameRecords.lean`'s `Ext` over the tree carrier**: the records relevant to `ρ` kept,
and the records strictly longer-lived than a borrow cell of `ρ` exactly the same.

What each clause rules out. `KeepsT`: resuming at a list that has dropped a record an `imm` cell
of the share reads at its top, which would let the resumed run lose the frame whose lend it
holds a view of. The lifetime clause: resuming at a list that adds or drops a record whose frame
outlives a borrow cell of the share; a record nested strictly inside the cell's witness is tagged
longer than the cell, so dropping it would lose a lend the share holds at depth, and adding one
would claim a frame the share's borrows were not taken under. Records whose frames are not
strictly longer-lived than a borrow of the share (in particular those on branches incomparable
with it) are free: the share holds nothing they lend. -/
def ExtLT (ls ls' : List (SRecT K)) (ρ : TRes K) : Prop :=
  KeepsT (rsOfT ls) (rsOfT ls') ρ ∧
    ∀ b, CellInT ρ b → ∀ x : SRecT K, K.lt b x.2 → (x ∈ ls ↔ x ∈ ls')

/-! ### Exclusive locations, cells at depth -/

/-- `m` holds a non-`imm` cell reached from the top of `σ` through `mut` witnesses: an exclusive
location of `σ`. -/
def XExT (σ : TRes K) (m : BoCa.Loc) : Prop :=
  ∃ (p : List BoCa.Loc) (τ : TRes K) (ζ : TCell K), XPath σ p τ ∧ τ.get m = some ζ ∧
    ζ.kind ≠ Kind.imm

theorem FrzT.inDom {ρ : TRes K} {m : BoCa.Loc} (h : FrzT ρ m) : InDomT ρ m := by
  induction h with
  | imm e _ => exact InDomT.top e
  | inImm e k hd => exact InDomT.wit e (by rw [k]; simp) hd
  | inMut e k _ ih => exact InDomT.wit e (by rw [k]; simp) ih

/-- **The deepest `imm` ancestor.** A location at any depth of `σ` is an `imm` cell at any
depth, or exclusive in such a cell's witness; or it is exclusive in `σ`. -/
theorem inDomT_imm_or_xex {σ : TRes K} {m : BoCa.Loc} (h : InDomT σ m) :
    (∃ (m₁ : BoCa.Loc) (ψ₁ : TCell K), CellAt σ m₁ ψ₁ ∧ ψ₁.kind = Kind.imm ∧
      (m = m₁ ∨ XExT ψ₁.wit m)) ∨ XExT σ m := by
  induction h with
  | @top σ m ψ e =>
      by_cases k : ψ.kind = Kind.imm
      · exact Or.inl ⟨m, ψ, .top e, k, Or.inl rfl⟩
      · exact Or.inr ⟨[], σ, ψ, .nil σ, e, k⟩
  | @wit σ m m' ψ e k _ ih =>
      rcases ih with ⟨m₁, ψ₁, hN, k₁, hc⟩ | ⟨p, τ, ζ, hp, eτ, kτ⟩
      · exact Or.inl ⟨m₁, ψ₁, .nest e hN, k₁, hc⟩
      · cases hkk : ψ.kind with
        | own => exact absurd hkk k
        | imm => exact Or.inl ⟨m', ψ, .top e, hkk, Or.inr ⟨p, τ, ζ, hp, eτ, kτ⟩⟩
        | «mut» => exact Or.inr ⟨m' :: p, τ, ζ, .cons e hkk hp, eτ, kτ⟩

/-- A borrow cell's witness lies in the stratum of the cell's lifetimes. -/
theorem CellUT.wit_inStratum_lsOf {ψ : TCell K} {s : TSet} (h : ψ.lsOf = some s) :
    ψ.wit.InStratum s := by
  cases ψ with
  | own v => simp [CellUT.lsOf] at h
  | imm i =>
      simp only [CellUT.lsOf, Option.some.injEq] at h
      subst h
      exact CellUT.wit_inStratum_imm
  | «mut» m =>
      simp only [CellUT.lsOf, Option.some.injEq] at h
      subst h
      exact CellUT.wit_inStratum_mut

/-- A borrow cell in the stratum `S` has its lifetimes strictly above `S`. -/
theorem CellUT.above_of_inStratum {S s : TSet} {ψ : TCell K} (h : ψ.InStratum S)
    (hs : ψ.lsOf = some s) : K.Above S s := by
  cases ψ with
  | own v => simp [CellUT.lsOf] at hs
  | imm i =>
      simp only [CellUT.lsOf, Option.some.injEq] at hs
      subst hs; exact h
  | «mut» m =>
      simp only [CellUT.lsOf, Option.some.injEq] at hs
      subst hs; exact h

/-- **A cell at any depth lies in every stratum its resource does**: a witness lies in the
stratum of its cell's lifetimes, which are above the resource's. -/
theorem CellAt.inStratum {σ : TRes K} {m : BoCa.Loc} {ψ : TCell K} (h : CellAt σ m ψ) :
    ∀ {S : TSet}, σ.InStratum S → ψ.InStratum S := by
  induction h with
  | top e => intro S hσ; exact hσ _ _ e
  | @nest ρ m₀ y χ ψ e hc ih =>
      intro S hσ
      cases hk : χ.lsOf with
      | none =>
          cases χ with
          | own v => exact (CellAt.not_own_wit rfl hc).elim
          | imm i => simp [CellUT.lsOf] at hk
          | «mut» m => simp [CellUT.lsOf] at hk
      | some t =>
          have hab := CellUT.above_of_inStratum (hσ _ _ e) hk
          refine ih (ResUT.InStratum.mono (fun x hx => ?_) (CellUT.wit_inStratum_lsOf hk))
          obtain ⟨z, hz⟩ := t.ne
          exact ⟨z, hz, (hab x hx z hz).le⟩

/-! ### Records named at a location -/

theorem DescRT.trans {r d e : FrameRecT K} (h : DescRT r d) (h' : DescRT d e) : DescRT r e := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  exact ⟨_, ha.append hb⟩

/-- **A place a record is relevant at carries a view in `ag(W)`**: the record proper's cell
(`LeInvT`), a sub-record's cell, a `mut` cell of its parent's escrow (`ExIn`), or a chain
position, an `own` cell of the escrow (`ChainInvT`). -/
theorem relAt_ag {Θ : CodeTy} {W : TRes K} {ps rs : List (FrameRecT K)} (hTI : TIT K Θ W ps rs)
    {r : FrameRecT K} (hr : r ∈ rs) {m : BoCa.Loc} (hm : RelAtT r m) :
    ∀ a, AgWT W a → ∃ ξ, a.get m = some ξ := by
  intro a ha
  rcases hm with rfl | ⟨pc, S, u, hc⟩
  · obtain ⟨p, hp, hpr⟩ := (hTI.2.2.2.2.2.2.1 r).mp hr
    rcases hpr.cases with rfl | ⟨pp, hpp, hlin⟩
    · obtain ⟨ψ, e, -⟩ := hTI.2.1 r hp a ha
      exact ⟨ψ, e⟩
    · obtain ⟨f, hf, hsub⟩ := hlin.last hpp
      obtain ⟨-, ζ, eζ, kζ, -⟩ := hsub
      have hfrs : f ∈ rs := hTI.desc_closed p ((hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, [], .nil p⟩) f hf
      exact exIn_support (TI.exIn hTI hfrs) eζ (by rw [kζ]; simp) a ha
  · exact hTI.1.2.1 r hr m u hc.own a ha

/-- **No record of a typed world names an exclusive location of a part of it.** The location
is in `ex(W)_●` (`xpath_ex_part`), the record's place in `ag(W)` (`relAt_ag`), and the two are
disjoint (`ex_ag_disjoint`). -/
theorem not_relAt_xexT {Θ : CodeTy} {W A : TRes K} {ps rs : List (FrameRecT K)}
    (hv : ResUT.Valid W) (hTI : TIT K Θ W ps rs) (hA : ResUT.Le A W) {r : FrameRecT K}
    (hr : r ∈ rs) {m : BoCa.Loc} (hx : XExT A m) : ¬ RelAtT r m := by
  intro hm
  obtain ⟨p, τ, ζ, hp, eτ, kτ⟩ := hx
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hv
  obtain ⟨ξ, eξ⟩ := relAt_ag hTI hr hm aW haW
  exact ex_ag_disjoint hv heW haW (xpath_ex_part hA heW hp eτ kτ) eξ

/-- **A place a record of `p`'s lineage is relevant at is `p`'s location or a lineage location of
`p`.** -/
theorem linLoc_of_relAt {p r : FrameRecT K} (h : DescRT p r) {m : BoCa.Loc} (hm : RelAtT r m) :
    m = p.le ∨ LinLocT p m := by
  rcases hm with rfl | ⟨pc, S, u, hc⟩
  · rcases h.cases with rfl | ⟨pp, hpp, hlin⟩
    · exact Or.inl rfl
    · obtain ⟨f, hf, -, ζ, eζ, kζ, -⟩ := hlin.last hpp
      exact Or.inr ⟨f, hf, ζ, eζ, by rw [kζ]; simp⟩
  · exact Or.inr ⟨r, h, _, hc.own, by simp⟩

/-! ### Records named inside a view's witness -/

/-- **A record relevant at an exclusive location of an `imm` view's witness is in the lineage of
the record the view is classified by.** The view is that record's cell, over its escrow, or one
of its chain positions, over a piece of its escrow (`chain_view_le`); either way the location
holds a non-`imm` cell of a lineage member `e` of the record (`xpath_linPath`). The record
relevant at the location owns a non-`imm` cell there too: a chain position is an `own` cell of
its escrow, and a sub-record's location a `mut` cell of its parent's. One owner per exclusive
cell (`TWNT.exclUnique`) makes that owner `e`. A record proper's location is a lineage location
of none (`le_not_linLoc`). -/
theorem desc_of_xexT {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {ps rs : List (FrameRecT K)}
    (hT : TWNT K Θ tc W ps rs) {a : TRes K} (ha : AgWT W a) {m₁ : BoCa.Loc} {ζ : TCell K}
    (eζ : a.get m₁ = some ζ) (kζ : ζ.kind = Kind.imm) {m : BoCa.Loc} (hx : XExT ζ.wit m)
    {r : FrameRecT K} (hr : r ∈ rs) (hm : RelAtT r m) : ∃ q ∈ rs, RelAtT q m₁ ∧ DescRT q r := by
  have hTI := hT.inv
  have hU := hT.exclUnique
  have hcl := hTI.desc_closed
  obtain ⟨b, τ, χ, hb, eτ, kτ⟩ := hx
  -- the view's record, and the cell at `m` along a `mut` path of its escrow
  obtain ⟨q, hq, hrelq, σ, hpath, eσ⟩ : ∃ q ∈ rs, RelAtT q m₁ ∧
      ∃ σ, XPath q.R b σ ∧ σ.get m = some χ := by
    rcases hTI.2.2.2.2.2.2.2 a ha m₁ ζ eζ kζ with ⟨q, hq, hle, -, hw⟩ | ⟨q, hq, pc, S, u, hc⟩
    · exact ⟨q, hq, Or.inl hle, τ, hw ▸ hb, eτ⟩
    · obtain ⟨nc, hcD⟩ := hc.depth
      obtain ⟨qq, hqq, -, hqd⟩ :=
        chain_view_le hTI hq ha nc pc m₁ S u hcD ζ eζ (by rw [kζ]; simp)
      rw [hqd] at hb
      obtain ⟨σ₁, hq₁, eσ₁⟩ := xpath_del hb eτ
      obtain ⟨σ₂, hq₂, eσ₂⟩ := xpath_le hqq hq₁ eσ₁ kτ
      exact ⟨q, hq, Or.inr ⟨pc, S, u, hc⟩, σ₂, hq₂, eσ₂⟩
  obtain ⟨e, he, rfl⟩ := xpath_linPath Θ b (hTI.1.2.2.2.1 q hq) hpath
  have hers : e ∈ rs := hcl q hq e ⟨b, he⟩
  refine ⟨q, hq, hrelq, ?_⟩
  rcases hm with rfl | ⟨pc, S, u, hc⟩
  · obtain ⟨p, hp, hpr⟩ := (hTI.2.2.2.2.2.2.1 r).mp hr
    rcases hpr.cases with rfl | ⟨pp, hpp, hlin⟩
    · obtain ⟨p', hp', hde⟩ := (hTI.2.2.2.2.2.2.1 e).mp hers
      exact (le_not_linLoc hT hp' hp ⟨e, hde, χ, eσ, kτ⟩).elim
    · obtain ⟨f, hf, hsub⟩ := hlin.last hpp
      obtain ⟨-, ζf, eζf, kζf, -⟩ := id hsub
      have hfrs : f ∈ rs := hcl p ((hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, [], .nil p⟩) f hf
      obtain rfl := hU e hers f hfrs _ χ ζf eσ kτ eζf (by rw [kζf]; simp)
      exact DescRT.sub ⟨b, he⟩ hsub
  · obtain rfl := hU e hers r hr m χ _ eσ kτ hc.own (by simp)
    exact ⟨b, he⟩

/-- **The root of a record is the one record proper above it**: two records proper in whose
lineage a record lies are one (`desc_comparable`, `not_desc_proper`). -/
theorem root_unique {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {ps rs : List (FrameRecT K)}
    (hT : TWNT K Θ tc W ps rs) {p₁ p₂ r : FrameRecT K} (h₁ : p₁ ∈ ps) (h₂ : p₂ ∈ ps)
    (d₁ : DescRT p₁ r) (d₂ : DescRT p₂ r) : p₁ = p₂ := by
  have hTI := hT.inv
  have hr₁ : p₁ ∈ rs := (hTI.2.2.2.2.2.2.1 p₁).mpr ⟨p₁, h₁, [], .nil p₁⟩
  have hr₂ : p₂ ∈ rs := (hTI.2.2.2.2.2.2.1 p₂).mpr ⟨p₂, h₂, [], .nil p₂⟩
  obtain ⟨q₁, hq₁⟩ := d₁
  obtain ⟨q₂, hq₂⟩ := d₂
  rcases desc_comparable hT.exclUnique hTI.desc_closed _ p₁ p₂ r q₁ q₂ le_rfl hr₁ hr₂ hq₁ hq₂
    with h | h
  · rcases h.cases with rfl | h
    · rfl
    · exact (not_desc_proper hT h₁ hr₂ h).elim
  · rcases h.cases with rfl | h
    · rfl
    · exact (not_desc_proper hT h₂ hr₁ h).elim

/-- **A record relevant inside a view is tagged no shorter than the view.** At the view's own
location, the record's root's `FrameLifeT` bounds the view (the location is the root's or a
lineage location of it, `linLoc_of_relAt`); inside its witness, the record is in the lineage of
the view's classifying record (`desc_of_xexT`), whose root is the record's (`root_unique`), and
whose place is a lineage location of that root. -/
theorem tag_ge_nestedT {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {ps : List (FrameRecT K)}
    {ls : List (SRecT K)} (hT : TWNT K Θ tc W ps (rsOfT ls)) (htag : TaggedT K W ps ls)
    {a : TRes K} (ha : AgWT W a) {m₁ : BoCa.Loc} {ζ : TCell K} (eζ : a.get m₁ = some ζ)
    (kζ : ζ.kind = Kind.imm) {m : BoCa.Loc} (hm₁ : m = m₁ ∨ XExT ζ.wit m) {r : FrameRecT K}
    {t : Life} (hrt : (r, t) ∈ ls) (hm : RelAtT r m) :
    ∀ s, ζ.lsOfI = some s → ∀ z ∈ s.set, K.le z t := by
  have hTI := hT.inv
  obtain ⟨p, hp, hpr, hFL⟩ := htag (r, t) hrt
  have hr : r ∈ rsOfT ls := List.mem_map.mpr ⟨(r, t), hrt, rfl⟩
  have hloc : m₁ = p.le ∨ LinLocT p m₁ := by
    rcases hm₁ with rfl | hx
    · exact linLoc_of_relAt hpr hm
    · obtain ⟨q, hq, hrelq, hqr⟩ := desc_of_xexT hT ha eζ kζ hx hr hm
      obtain ⟨pq, hpq, hdq⟩ := (hTI.2.2.2.2.2.2.1 q).mp hq
      obtain rfl := root_unique hT hpq hp (hdq.trans hqr) hpr
      exact linLoc_of_relAt hdq hrelq
  intro s hs z hz
  rcases hloc with h | hL
  · rw [h] at eζ
    rw [hFL.1 a ha ζ s eζ hs z hz]
    exact K.refl t
  · exact hFL.2 a ha m₁ hL ζ s eζ hs z hz

/-! ### The theorem -/

/-- **`ExtLT` implies `extFT` at typed tree worlds.** At a share `ρ` contained in a tagged `TWNT`
world at `ls`, every list `ls′` at which `TWNT` holds and which `ExtLT` allows, `extFT` allows. -/
theorem ext_extFT {Θ Θ' : CodeTy} {tc tc' : TChoice K} {W W' ρ : TRes K}
    {ps ps' : List (FrameRecT K)} {ls ls' : List (SRecT K)}
    (hT : TWNT K Θ tc W ps (rsOfT ls)) (htag : TaggedT K W ps ls) (hρ : ResUT.Le ρ W)
    (hT' : TWNT K Θ' tc' W' ps' (rsOfT ls')) (h : ExtLT ls ls' ρ) : extFT ls ls' ρ := by
  have hTI := hT.inv
  have hv := hT.valid
  have hcl' := hT'.inv.2.2.2.2.2.2.1
  obtain ⟨aW, haW⟩ := agW_of_valid hv
  obtain ⟨τ, hτ⟩ := id hρ
  obtain ⟨aρ, aτ, haρ, -, hcρ⟩ := (AgWT.split hτ).mp haW
  intro r hr ⟨m, hf, hm⟩
  have key : ∀ {m₀ : BoCa.Loc} {ψ₀ : TCell K}, ρ.get m₀ = some ψ₀ → ψ₀.kind ≠ Kind.own →
      InDomT ψ₀.wit m → r ∈ rsOfT ls' := by
    intro m₀ ψ₀ e₀ k₀ hd
    rcases inDomT_imm_or_xex hd with ⟨m₁, ψ₁, hN₁, k₁, hc⟩ | hx
    · -- a nested `imm` cell: the lifetime clause
      obtain ⟨s₀, hs₀⟩ : ∃ s₀, ψ₀.lsOf = some s₀ := by
        cases ψ₀ with
        | own v => exact absurd rfl k₀
        | imm i => exact ⟨_, rfl⟩
        | «mut» m => exact ⟨_, rfl⟩
      obtain ⟨y, hy⟩ := s₀.ne
      obtain ⟨ζ, eζ, kζ, -, wζ, lζ⟩ :=
        icp_trans (cellAt_imm_icp (.nest e₀ hN₁) haρ) (icpAt_left hcρ m₁) k₁
      obtain ⟨s₁, hs₁⟩ := lsOf_of_imm k₁
      obtain ⟨t₁, ht₁⟩ := lsOf_of_imm kζ
      obtain ⟨z, hz⟩ := s₁.ne
      have hzt : z ∈ t₁.set := lζ s₁ t₁ hs₁ ht₁ z hz
      have hs₁' : ψ₁.lsOf = some s₁ := by
        cases ψ₁ with
        | own v => simp [CellUT.lsOfI] at hs₁
        | imm i => exact hs₁
        | «mut» m => simp [CellUT.lsOfI] at hs₁
      have hyz : K.lt y z := CellUT.above_of_inStratum
        (hN₁.inStratum (CellUT.wit_inStratum_lsOf hs₀)) hs₁' y hy z hz
      obtain ⟨⟨r', t⟩, ht, rfl⟩ := List.mem_map.mp hr
      have hge := tag_ge_nestedT hT htag haW eζ kζ (by rw [wζ]; exact hc) ht hm t₁ ht₁ z hzt
      have hin := (h.2 y ⟨m₀, ψ₀, s₀, e₀, k₀, hs₀, y, hy, K.refl y⟩ (r', t)
        (Cactus.lt_of_lt_of_le hyz hge)).mp ht
      exact List.mem_map.mpr ⟨_, hin, rfl⟩
    · cases hk : ψ₀.kind with
      | own => exact absurd hk k₀
      | «mut» =>
          obtain ⟨p, τ', ζ, hp, eτ, kτ⟩ := hx
          exact (not_relAt_xexT hv hTI hρ hr ⟨m₀ :: p, τ', ζ, .cons e₀ hk hp, eτ, kτ⟩ hm).elim
      | imm =>
          obtain ⟨ζ₀, eζ₀, kζ₀, -, wζ₀, -⟩ :=
            icp_trans (icpAt_agW haρ m₀ ψ₀ e₀) (icpAt_left hcρ m₀) hk
          obtain ⟨q, hq, hrelq, hqr⟩ :=
            desc_of_xexT hT haW eζ₀ kζ₀ (by rw [wζ₀]; exact hx) hr hm
          have hq' : q ∈ rsOfT ls' := h.1 q hq ⟨m₀, ψ₀, e₀, hk, hrelq⟩
          obtain ⟨p', hp', hdq⟩ := (hcl' q).mp hq'
          exact (hcl' r).mpr ⟨p', hp', hdq.trans hqr⟩
  cases hf with
  | imm e k => exact h.1 r hr ⟨m, _, e, k, hm⟩
  | inImm e k hd => exact key e (by rw [k]; simp) hd
  | inMut e k hf => exact key e (by rw [k]; simp) hf.inDom

/-! ### What `ExtLT` admits and refuses

At the printed chain, the share `0 ↦ imm({α}, (), ∅)`: one view, at lifetime `α`, of the record at
location `0`. `ExtLT` admits dropping a record no borrow of the share reads and no longer-lived
than `α` (`extLT_admits_drop`); it refuses dropping the record the view is of
(`not_extLT_drop_relevant`, the `KeepsT` clause), and dropping a record tagged strictly longer than
`α` though the share names it nowhere (`not_extLT_drop_longer`, the lifetime clause, with `KeepsT`
holding there: `keepsT_drop_longer`). -/

/-- The share of the examples. -/
def exShare (α : Life) : TRes WCactus.chain :=
  ResUT.single 0 (CellUT.immOf (TSet.single α) BoCa.Val.unit PMap.empty (ResUT.inStratum_empty _))

/-- A record at `l` over the empty escrow. -/
def exRec (l : BoCa.Loc) : FrameRecT WCactus.chain := ⟨l, BoCa.Val.unit, PMap.empty, .unit⟩

theorem exShare_get {α : Life} {m : BoCa.Loc} {ψ : TCell WCactus.chain} (e : (exShare α).get m = some ψ) :
    m = 0 ∧ ψ = CellUT.immOf (TSet.single α) BoCa.Val.unit PMap.empty
      (ResUT.inStratum_empty _) := by
  by_cases hm : m = 0
  · subst hm
    simp only [exShare, ResUT.single_get_self, Option.some.injEq] at e
    exact ⟨rfl, e.symm⟩
  · rw [exShare, ResUT.single_get_ne _ hm] at e; cases e

theorem exRec_relAt {l m : BoCa.Loc} (h : RelAtT (exRec l) m) : m = l := by
  rcases h with h | ⟨p, S, u, hc⟩
  · exact h
  · have := hc.own
    simp [exRec] at this

/-- **`ExtLT` admits a strict shrinking** at a share with a live view: the record at `1`, tagged
at `α`, is dropped. -/
theorem extLT_admits_drop (α : Life) :
    ExtLT [(exRec 0, α), (exRec 1, α)] [(exRec 0, α)] (exShare α) := by
  refine ⟨fun r hr ⟨m, ψ, e, _, hm⟩ => ?_, fun b ⟨m, ψ, s, e, _, hs, y, hy, hyb⟩ x hx => ?_⟩
  · obtain ⟨rfl, -⟩ := exShare_get e
    simp only [rsOfT, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl
    · rfl
    · exact absurd (exRec_relAt hm) (by simp)
  · obtain ⟨-, rfl⟩ := exShare_get e
    simp only [CellUT.lsOf_immOf, Option.some.injEq] at hs
    subst hs
    simp only [TSet.single_set, Finset.mem_singleton] at hy
    rw [hy] at hyb
    have hno : x.2 ≠ α := fun e => Cactus.lt_irrefl _ _ (Cactus.lt_of_le_of_lt hyb (e ▸ hx))
    constructor
    · intro hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl <;> exact absurd rfl hno
    · intro hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      subst hx'
      exact absurd rfl hno

/-- **`KeepsT` refuses dropping the record the share's view is of.** -/
theorem not_extLT_drop_relevant (α : Life) : ¬ ExtLT [(exRec 0, α)] [] (exShare α) := by
  intro h
  have := h.1 (exRec 0) (by simp [rsOfT])
    ⟨0, _, ResUT.single_get_self _ _, CellUT.kind_immOf _ _ _ _, Or.inl rfl⟩
  simp [rsOfT] at this

/-- At the record at `1`, `KeepsT` admits dropping it: the share names it nowhere. -/
theorem keepsT_drop_longer (α t : Life) :
    KeepsT (rsOfT [(exRec 1, t)]) (rsOfT []) (exShare α) := by
  intro r hr ⟨m, ψ, e, _, hm⟩
  obtain ⟨rfl, -⟩ := exShare_get e
  simp only [rsOfT, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  subst hr
  exact absurd (exRec_relAt hm) (by simp)

/-- **The lifetime clause refuses dropping a record tagged strictly longer than the share's
view**, where `KeepsT` admits it (`keepsT_drop_longer`). -/
theorem not_extLT_drop_longer {α t : Life} (hαt : α < t) :
    ¬ ExtLT [(exRec 1, t)] [] (exShare α) := by
  intro h
  have := (h.2 α ⟨0, _, TSet.single α, ResUT.single_get_self _ _, by simp, CellUT.lsOf_immOf _ _ _ _,
    α, by simp, WCactus.chain.refl α⟩ (exRec 1, t) ((WCactus.chain_lt _ _).mpr hαt)).mp (by simp)
  simp at this

/-- Two lifetimes of the chain, strictly ordered: the refusal's hypothesis is met. -/
example : (OrderDual.toDual 1 : Life) < OrderDual.toDual 0 := by decide

end BoCa.Fig16.Tree.Wp

end
