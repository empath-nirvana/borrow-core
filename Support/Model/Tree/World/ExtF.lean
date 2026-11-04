import Support.Model.Tree.World.Recs
import Support.Model.Tree.World.TInvReread

/-!
# `extF` over the tree carrier

`[spec §62]`. The world condition of a resumed continuation, read on `TRes K`: a location is
*frozen* in `ρ` (`FrzT`) when an `imm` cell of `ρ` sits there, or it lies anywhere inside the
witness of an `imm` cell, the cells reached from the top through `mut` witnesses included. A
record is relevant (`RelFT`) when a frozen location is its cell or one of its chain positions.
`extFT ls ls′ ρ`: every record of `ls` relevant to `ρ` is in `ls′`.

**Re-reading.** A re-reading keeps every location, tag and witness domain, and every `own` cell
(`RC`), so it carries the locations at depth (`InDomT.rr_fwd`, `InDomT.rr_back`), the frozen
locations (`FrzT.rr_fwd`, `FrzT.rr_back`), a record's places (`RelAtT.rr_iff`, through
`chain_recRR_fwd`/`_back`), and the relevant records (`RelFT.rr_iff`). Re-reading is
single-valued on records (`RecRR.func`), so `extFT` between two lists is carried to their
re-readings (`extFT.rr`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-! ### Locations at any depth, and frozen locations -/

/-- `m` lies at any depth inside `σ`: a location of `σ`, or inside the witness of one of its
non-`own` cells. -/
inductive InDomT : TRes K → BoCa.Loc → Prop
  | top {σ : TRes K} {m : BoCa.Loc} {ψ : TCell K} : σ.get m = some ψ → InDomT σ m
  | wit {σ : TRes K} {m m' : BoCa.Loc} {ψ : TCell K} :
      σ.get m' = some ψ → ψ.kind ≠ Kind.own → InDomT ψ.wit m → InDomT σ m

/-- **`m` is frozen in `ρ`**: an `imm` cell of `ρ` sits at `m`, or `m` lies inside the witness
of an `imm` cell; cells reached from the top through `mut` witnesses count. -/
inductive FrzT : TRes K → BoCa.Loc → Prop
  | imm {ρ : TRes K} {m : BoCa.Loc} {ψ : TCell K} :
      ρ.get m = some ψ → ψ.kind = Kind.imm → FrzT ρ m
  | inImm {ρ : TRes K} {m m' : BoCa.Loc} {ψ : TCell K} :
      ρ.get m' = some ψ → ψ.kind = Kind.imm → InDomT ψ.wit m → FrzT ρ m
  | inMut {ρ : TRes K} {m m' : BoCa.Loc} {ψ : TCell K} :
      ρ.get m' = some ψ → ψ.kind = Kind.mut → FrzT ψ.wit m → FrzT ρ m

/-- `m` is a place `Coh` looks for `r`: its cell, or one of its chain positions. -/
def RelAtT (r : FrameRecT K) (m : BoCa.Loc) : Prop :=
  m = r.le ∨ ∃ p S u, ChainT r.R r.T r.v p m S u

/-- **`r` is relevant to `ρ`**: a frozen location of `ρ` is a place `Coh` looks for `r`. -/
def RelFT (r : FrameRecT K) (ρ : TRes K) : Prop := ∃ m, FrzT ρ m ∧ RelAtT r m

/-- **The world condition of a resumed continuation**: the records of `ls` relevant to the
share `ρ` are in `ls′`.

**Departure (D10, `docs/new-core/scope-781.md` §8).** An in-house design, not a transcription:
a stored continuation may resume at any list `extFT` allows. No printed lemma reads it, so no
printed technique is replaced. -/
def extFT (ls ls' : List (SRecT K)) (ρ : TRes K) : Prop :=
  ∀ r ∈ rsOfT ls, RelFT r ρ → r ∈ rsOfT ls'

theorem extFT_refl (ls : List (SRecT K)) (ρ : TRes K) : extFT ls ls ρ := fun _ h _ => h

/-- A record list that keeps every record keeps the relevant ones. -/
theorem extFT_of_sub {ls ls' : List (SRecT K)} (h : ∀ r ∈ rsOfT ls, r ∈ rsOfT ls')
    (ρ : TRes K) : extFT ls ls' ρ := fun r hr _ => h r hr

/-- `extFT` at one share composes. -/
theorem extFT.trans {ls ls' ls'' : List (SRecT K)} {ρ : TRes K} (h : extFT ls ls' ρ)
    (h' : extFT ls' ls'' ρ) : extFT ls ls'' ρ :=
  fun r hr hrel => h' r (h r hr hrel) hrel

/-! ### Moving along composition -/

theorem FrzT.of_compS_left {ρ₁ ρ₂ ρ : TRes K} (hc : ResUT.CompS ρ₁ ρ₂ ρ) {m : BoCa.Loc}
    (h : FrzT ρ₁ m) : FrzT ρ m := by
  cases h with
  | imm e k =>
      obtain ⟨ψ, e', k', -⟩ := compS_get_left' hc e
      exact FrzT.imm e' (k'.trans k)
  | inImm e k hd =>
      obtain ⟨ψ, e', k', w', -⟩ := compS_get_left' hc e
      exact FrzT.inImm e' (k'.trans k) (w' ▸ hd)
  | inMut e k hf =>
      obtain ⟨ψ, e', k', w', -⟩ := compS_get_left' hc e
      exact FrzT.inMut e' (k'.trans k) (w' ▸ hf)

theorem RelFT.of_compS_left {r : FrameRecT K} {ρ₁ ρ₂ ρ : TRes K} (hc : ResUT.CompS ρ₁ ρ₂ ρ)
    (h : RelFT r ρ₁) : RelFT r ρ := by
  obtain ⟨m, hf, hm⟩ := h
  exact ⟨m, hf.of_compS_left hc, hm⟩

theorem RelFT.of_compS_right {r : FrameRecT K} {ρ₁ ρ₂ ρ : TRes K} (hc : ResUT.CompS ρ₁ ρ₂ ρ)
    (h : RelFT r ρ₂) : RelFT r ρ := RelFT.of_compS_left (ResUT.CompS.comm hc) h

theorem extFT_left {ls ls' : List (SRecT K)} {ρ₁ ρ₂ ρ : TRes K} (hc : ResUT.CompS ρ₁ ρ₂ ρ)
    (h : extFT ls ls' ρ) : extFT ls ls' ρ₁ :=
  fun r hr hrel => h r hr (hrel.of_compS_left hc)

theorem extFT_right {ls ls' : List (SRecT K)} {ρ₁ ρ₂ ρ : TRes K} (hc : ResUT.CompS ρ₁ ρ₂ ρ)
    (h : extFT ls ls' ρ) : extFT ls ls' ρ₂ :=
  fun r hr hrel => h r hr (hrel.of_compS_right hc)

/-- A frozen location of a composite is a frozen location of a part, or of the other. -/
theorem FrzT.split {ρ₁ ρ₂ ρ : TRes K} (hc : ResUT.CompS ρ₁ ρ₂ ρ) {m : BoCa.Loc} (h : FrzT ρ m) :
    FrzT ρ₁ m ∨ FrzT ρ₂ m := by
  cases h with
  | imm e k =>
      rcases compS_back hc e with ⟨ψ₁, e₁, k₁, -⟩ | ⟨ψ₂, e₂, k₂, -⟩
      · exact Or.inl (FrzT.imm e₁ (k₁.trans k))
      · exact Or.inr (FrzT.imm e₂ (k₂.trans k))
  | inImm e k hd =>
      rcases compS_back hc e with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
      · exact Or.inl (FrzT.inImm e₁ (k₁.trans k) (w₁ ▸ hd))
      · exact Or.inr (FrzT.inImm e₂ (k₂.trans k) (w₂ ▸ hd))
  | inMut e k hf =>
      rcases compS_back hc e with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
      · exact Or.inl (FrzT.inMut e₁ (k₁.trans k) (w₁ ▸ hf))
      · exact Or.inr (FrzT.inMut e₂ (k₂.trans k) (w₂ ▸ hf))

/-- **`extFT` at a composite from `extFT` at its parts.** -/
theorem extFT_comp {ls ls' : List (SRecT K)} {ρ₁ ρ₂ ρ : TRes K} (hc : ResUT.CompS ρ₁ ρ₂ ρ)
    (h₁ : extFT ls ls' ρ₁) (h₂ : extFT ls ls' ρ₂) : extFT ls ls' ρ := by
  rintro r hr ⟨m, hf, hm⟩
  rcases hf.split hc with h | h
  · exact h₁ r hr ⟨m, h, hm⟩
  · exact h₂ r hr ⟨m, h, hm⟩

/-! ### Re-reading -/

theorem InDomT.rr_fwd {Θ : LocTy} {ρ : TRes K} {m : BoCa.Loc} (h : InDomT ρ m) :
    ∀ {ρ' : TRes K'}, RR Θ ρ ρ' → InDomT ρ' m := by
  induction h with
  | top e =>
      intro ρ' hr
      obtain ⟨ψ', e', -⟩ := hr.get_some e
      exact .top e'
  | wit e k _ ih =>
      intro ρ' hr
      obtain ⟨ψ', e', hc⟩ := hr.get_some e
      exact .wit e' (hc.kind ▸ k) (ih hc.wit)

theorem InDomT.rr_back {Θ : LocTy} {ρ' : TRes K'} {m : BoCa.Loc} (h : InDomT ρ' m) :
    ∀ {ρ : TRes K}, RR Θ ρ ρ' → InDomT ρ m := by
  induction h with
  | top e =>
      intro ρ hr
      obtain ⟨ψ, e', -⟩ := hr.get_some' e
      exact .top e'
  | wit e k _ ih =>
      intro ρ hr
      obtain ⟨ψ, e', hc⟩ := hr.get_some' e
      exact .wit e' (hc.kind ▸ k) (ih hc.wit)

theorem FrzT.rr_fwd {Θ : LocTy} {ρ : TRes K} {m : BoCa.Loc} (h : FrzT ρ m) :
    ∀ {ρ' : TRes K'}, RR Θ ρ ρ' → FrzT ρ' m := by
  induction h with
  | imm e k =>
      intro ρ' hr
      obtain ⟨ψ', e', hc⟩ := hr.get_some e
      exact .imm e' (hc.kind.trans k)
  | inImm e k hd =>
      intro ρ' hr
      obtain ⟨ψ', e', hc⟩ := hr.get_some e
      exact .inImm e' (hc.kind.trans k) (hd.rr_fwd hc.wit)
  | inMut e k _ ih =>
      intro ρ' hr
      obtain ⟨ψ', e', hc⟩ := hr.get_some e
      exact .inMut e' (hc.kind.trans k) (ih hc.wit)

theorem FrzT.rr_back {Θ : LocTy} {ρ' : TRes K'} {m : BoCa.Loc} (h : FrzT ρ' m) :
    ∀ {ρ : TRes K}, RR Θ ρ ρ' → FrzT ρ m := by
  induction h with
  | imm e k =>
      intro ρ hr
      obtain ⟨ψ, e', hc⟩ := hr.get_some' e
      exact .imm e' (hc.kind.symm.trans k)
  | inImm e k hd =>
      intro ρ hr
      obtain ⟨ψ, e', hc⟩ := hr.get_some' e
      exact .inImm e' (hc.kind.symm.trans k) (hd.rr_back hc.wit)
  | inMut e k _ ih =>
      intro ρ hr
      obtain ⟨ψ, e', hc⟩ := hr.get_some' e
      exact .inMut e' (hc.kind.symm.trans k) (ih hc.wit)

/-- **A record's re-reading has its places.** -/
theorem RelAtT.rr_iff {Θ' : CodeTy} {r : FrameRecT K} {r' : FrameRecT K'} (h : RecRR Θ' r r')
    (m : BoCa.Loc) : RelAtT r m ↔ RelAtT r' m := by
  unfold RelAtT
  rw [h.1]
  constructor
  · rintro (e | ⟨p, S, u, hc⟩)
    · exact Or.inl e
    · exact Or.inr ⟨p, S, u, chain_recRR_fwd h hc⟩
  · rintro (e | ⟨p, S, u, hc⟩)
    · exact Or.inl e
    · exact Or.inr ⟨p, S, u, chain_recRR_back h hc⟩

/-- **Re-reading keeps and reflects relevance.** -/
theorem RelFT.rr_iff {Θ' : CodeTy} {r : FrameRecT K} {r' : FrameRecT K'} (h : RecRR Θ' r r')
    {ρ : TRes K} {ρ' : TRes K'} (hr : RR (sem Θ') ρ ρ') : RelFT r ρ ↔ RelFT r' ρ' := by
  unfold RelFT
  constructor
  · rintro ⟨m, hf, hm⟩; exact ⟨m, hf.rr_fwd hr, (RelAtT.rr_iff h m).mp hm⟩
  · rintro ⟨m, hf, hm⟩; exact ⟨m, hf.rr_back hr, (RelAtT.rr_iff h m).mpr hm⟩

/-- A record of a re-read list is the re-reading of a record of the list. -/
theorem SRecsRR.mem_back {Θ' : CodeTy} {ls : List (SRecT K)} {ls' : List (SRecT K')}
    (h : SRecsRR Θ' ls ls') {r' : FrameRecT K'} (hr : r' ∈ rsOfT ls') :
    ∃ r ∈ rsOfT ls, RecRR Θ' r r' := by
  obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hr
  obtain ⟨x, hx, hxx, -⟩ := forall₂_mem_right h hx'
  exact ⟨x.1, List.mem_map.mpr ⟨x, hx, rfl⟩, hxx⟩

/-- A record of a list has its re-reading in the re-read list. -/
theorem SRecsRR.mem_fwd {Θ' : CodeTy} {ls : List (SRecT K)} {ls' : List (SRecT K')}
    (h : SRecsRR Θ' ls ls') {r : FrameRecT K} (hr : r ∈ rsOfT ls) :
    ∃ r' ∈ rsOfT ls', RecRR Θ' r r' := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  obtain ⟨x', hx', hxx, -⟩ := forall₂_mem_left h hx
  exact ⟨x'.1, List.mem_map.mpr ⟨x', hx', rfl⟩, hxx⟩

/-- **`extFT` is carried to the re-readings**: of the two lists, and of the share. -/
theorem extFT.rr {Θ' : CodeTy} {ls ls₂ : List (SRecT K)} {ls' ls₂' : List (SRecT K')}
    {ρ : TRes K} {ρ' : TRes K'} (hl : SRecsRR Θ' ls ls') (hl₂ : SRecsRR Θ' ls₂ ls₂')
    (hr : RR (sem Θ') ρ ρ') (h : extFT ls ls₂ ρ) : extFT ls' ls₂' ρ' := by
  intro r' hr' hrel
  obtain ⟨r, hr₀, hrr⟩ := hl.mem_back hr'
  have hin := h r hr₀ ((RelFT.rr_iff hrr hr).mpr hrel)
  obtain ⟨r'', hr'', hrr'⟩ := hl₂.mem_fwd hin
  rw [RecRR.func hrr hrr']
  exact hr''

/-! ### The records a share reads, kept -/

/-- **The resume list keeps the records the share reads**: every record of the stop list `ls`
relevant to the share `ρ` (`RelFT`, read at the stop) has its re-reading in `ls′`. Records of `ls`
the share does not read are not asked for: another branch may end them.

**Departure (D13, `docs/new-core/scope-781.md` §8).** In-house, as `extFT` (D10): the resume
condition of a stored continuation depends only on the records its share reads. `extFT` asked
for a re-reading of the whole stop list first, which fails at a resume after another branch ended
a record of its own that was open at the stop. -/
def KeepRel {K K' : WCactus} (Θ' : CodeTy) (ls : List (SRecT K)) (ls' : List (SRecT K'))
    (ρ : TRes K) : Prop :=
  ∀ r ∈ rsOfT ls, RelFT r ρ → ∃ r' ∈ rsOfT ls', RecRR Θ' r r'

/-- At the stop's own list, every record is its own re-reading. -/
theorem KeepRel.refl {Θ : CodeTy} {ls : List (SRecT K)} (hc : ∀ x ∈ ls, CovR (sem Θ) K x.1.R)
    (ρ : TRes K) : KeepRel (K' := K) Θ ls ls ρ := by
  intro r hr _
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact ⟨x.1, hr, RecRR.refl (hc x hx)⟩

/-- **A re-reading of the whole stop list, with `extFT` against it, keeps the records the share
reads**: every resume the whole-list condition admits, `KeepRel` admits. -/
theorem keepRel_of_extFT {Θ' : CodeTy} {ls : List (SRecT K)} {lsR ls' : List (SRecT K')}
    {ρ : TRes K} {ρ' : TRes K'} (hl : SRecsRR Θ' ls lsR) (hr : RR (sem Θ') ρ ρ')
    (hx : extFT lsR ls' ρ') : KeepRel Θ' ls ls' ρ := by
  intro r hr₀ hrel
  obtain ⟨r', hr', hrr⟩ := hl.mem_fwd hr₀
  exact ⟨r', hx r' hr' ((RelFT.rr_iff hrr hr).mp hrel), hrr⟩

/-- **`KeepRel` composes** along an extension, the share re-read in between. -/
theorem KeepRel.trans {K₃ : WCactus} (hE : K'.Ext K₃) {Θ₂ Θ₃ : CodeTy} {ls : List (SRecT K)}
    {ls₂ : List (SRecT K')} {ls₃ : List (SRecT K₃)} {ρ : TRes K} {ρ₂ : TRes K'}
    (hr : RR (sem Θ₂) ρ ρ₂) (h : KeepRel Θ₂ ls ls₂ ρ) (h' : KeepRel Θ₃ ls₂ ls₃ ρ₂) :
    KeepRel Θ₃ ls ls₃ ρ := by
  intro r hr₀ hrel
  obtain ⟨r₂, hr₂, e₂⟩ := h r hr₀ hrel
  obtain ⟨r₃, hr₃, e₃⟩ := h' r₂ hr₂ ((RelFT.rr_iff e₂ hr).mp hrel)
  exact ⟨r₃, hr₃, RecRR.trans hE e₂ e₃⟩

/-- `KeepRel` at a part of a share. -/
theorem KeepRel.of_compS_left {Θ' : CodeTy} {ls : List (SRecT K)} {ls' : List (SRecT K')}
    {ρ₁ ρ₂ ρ : TRes K} (hc : ResUT.CompS ρ₁ ρ₂ ρ) (h : KeepRel Θ' ls ls' ρ) :
    KeepRel Θ' ls ls' ρ₁ :=
  fun r hr hrel => h r hr (hrel.of_compS_left hc)

/-- `KeepRel` at a re-reading of the stop list, read at the stop list. -/
theorem KeepRel.of_srecsRR {Θ' : CodeTy} {ls : List (SRecT K)} {ls' : List (SRecT K')}
    (h : SRecsRR Θ' ls ls') (ρ : TRes K) : KeepRel Θ' ls ls' ρ :=
  fun _ hr _ => h.mem_fwd hr

end BoCa.Fig16.Tree.Wp

end
