import Support.Model.Tree.World.Records
import Support.Model.Tree.World.UpdXInv

/-!
# `crwpG` over the tree world: `twp`

`SI/Capture.lean`'s `crwpG F Q n ls O e ρ`, read at a world `w` of `TreeWp/World.lean`. What
changes, each forced by the world growing:

* **The frame is quantified over the tree world.** A run starts at any extension `w₀` of `w`,
  from the re-reading `ρ₀` of `ρ` there (`RRw`): a stored continuation is resumed after the tree
  grew under it (a graft) and its cells' invariants were re-read (`Tree/KSem.lean`). This makes
  `twp` monotone along world extension by construction (`twp_kripke`), as a Kripke relation is.
* **The world at the end extends the world at the start**, and the frame at the end is the
  frame at the start re-read there (`EndT`). A run that opens a lend adds a child to `K`; a run
  that resumes a stored task inside a newer lend grafts it; neither touches the frame's cells
  other than by re-reading them.
* **Records are carried, re-read.** As in `crwpG`, the run owns records `O` and reads a tagged
  list `ls`; the frame owns `psF`; `Split ps O psF`, `TWNT fρ ps (rsOf ls)` and `Tagged fρ ps ls`
  hold of the world (`RecInv`). At an extension the records are re-read with the world
  (`RecsRR`, `SRecsRR`): location, value and code kept, escrow re-read. The end's frame records
  are the start's re-read there.
* **The world invariant** is `WInv` (covered by `sem Θ`, lowering to the memory) beside
  `RecInv` (`TWNT ∧ Tagged`), in place of `TWNC ∧ Tagged ∧ Lower`.
* **Each extension carries a resource**: the run's start extends `w` carrying the run's resource,
  the end extends the start carrying the frame (`TWd.Ext`). A location only the run holds a
  `mut` cell at, or none does, may be re-typed: the run may free a location and allocate it at
  another code.

What the rules ask in exchange: a frame condition and a resource framed beside a run, with the
records it owns, must be carried along re-reading (`TFrame.Mono`, `TRProp.Mono`); records owned
apart are at different locations (`twp_frame`'s `hO`), which re-reading keeps. At `RR.refl` (no
growth) every re-reading is the identity.
-/

noncomputable section


namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo

/-! ### Records along re-reading -/

/-- A tagged record: a record and the lifetime of its frame. -/
abbrev SRecT (K : WCactus) : Type := FrameRecT K × Life

/-- The records of a tagged list. -/
def rsOfT {K : WCactus} (ls : List (SRecT K)) : List (FrameRecT K) := ls.map Prod.fst

/-- `Tagged` read in `K`: every tagged record is in the lineage of a record proper whose frame is
at its tag. -/
def TaggedT (K : WCactus) (W : TRes K) (ps : List (FrameRecT K)) (ls : List (SRecT K)) : Prop :=
  ∀ x ∈ ls, ∃ p ∈ ps, DescRT p x.1 ∧ FrameLifeT K W p x.2

/-- `Split`: the records proper are those the run owns and those the frame owns, apart. Forced
beside `Split`: apart **by location**, which re-reading keeps (two records re-read to one when
their escrows re-read to one); where records proper have distinct locations (`TIT`'s third
clause) it is `Split`'s `p ∉ psF`. -/
def SplitT {K : WCactus} (ps O psF : List (FrameRecT K)) : Prop :=
  (∀ p, p ∈ ps ↔ p ∈ O ∨ p ∈ psF) ∧ ∀ p ∈ O, ∀ q ∈ psF, p.le ≠ q.le

/-- **The records of the world**: `TWNT` at the records proper and the list's records, tagged,
at the world's template choice `w.tc`. A run that does not grow the tree ends at its start's
choice, so every canonical image it makes is read at that choice; a grown world's choice is the
carried one (`TWNT.reread`). -/
def RecInv (w : TWd) (fρ : TRes w.K) (ps : List (FrameRecT w.K)) (ls : List (SRecT w.K)) :
    Prop :=
  TWNT w.K w.Θ w.tc fρ ps (rsOfT ls) ∧ TaggedT w.K fρ ps ls

/-- Records re-read along an extension. -/
abbrev RecsRR {K K' : WCactus} (Θ' : CodeTy) (rs : List (FrameRecT K))
    (rs' : List (FrameRecT K')) : Prop :=
  List.Forall₂ (RecRR Θ') rs rs'

/-- Tagged records re-read along an extension, tags kept. -/
abbrev SRecsRR {K K' : WCactus} (Θ' : CodeTy) (ls : List (SRecT K)) (ls' : List (SRecT K')) :
    Prop :=
  List.Forall₂ (fun x y => RecRR Θ' x.1 y.1 ∧ y.2 = x.2) ls ls'

theorem RecRR.trans {K₁ K₂ K₃ : WCactus} (hE : K₂.Ext K₃) {Θ₂ Θ₃ : CodeTy} {r₁ : FrameRecT K₁}
    {r₂ : FrameRecT K₂} {r₃ : FrameRecT K₃} (h : RecRR Θ₂ r₁ r₂) (h' : RecRR Θ₃ r₂ r₃) :
    RecRR Θ₃ r₁ r₃ :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    RR.trans_retype hE h.2.2.2 h'.2.2.2⟩

theorem forall₂_trans {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop}
    {T : α → γ → Prop} (hT : ∀ a b c, R a b → S b c → T a c) :
    ∀ {xs : List α} {ys : List β} {zs : List γ}, List.Forall₂ R xs ys →
      List.Forall₂ S ys zs → List.Forall₂ T xs zs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons (hT _ _ _ h₁ h₂) (forall₂_trans hT t₁ t₂)

theorem RecsRR.trans {K₁ K₂ K₃ : WCactus} (hE : K₂.Ext K₃) {Θ₂ Θ₃ : CodeTy}
    {rs₁ : List (FrameRecT K₁)} {rs₂ : List (FrameRecT K₂)} {rs₃ : List (FrameRecT K₃)}
    (h : RecsRR Θ₂ rs₁ rs₂) (h' : RecsRR Θ₃ rs₂ rs₃) : RecsRR Θ₃ rs₁ rs₃ :=
  forall₂_trans (R := RecRR Θ₂) (S := RecRR Θ₃) (T := RecRR Θ₃)
    (fun _ _ _ a b => RecRR.trans hE a b) h h'

theorem SRecsRR.trans {K₁ K₂ K₃ : WCactus} (hE : K₂.Ext K₃) {Θ₂ Θ₃ : CodeTy}
    {ls₁ : List (SRecT K₁)} {ls₂ : List (SRecT K₂)} {ls₃ : List (SRecT K₃)}
    (h : SRecsRR Θ₂ ls₁ ls₂) (h' : SRecsRR Θ₃ ls₂ ls₃) : SRecsRR Θ₃ ls₁ ls₃ :=
  forall₂_trans (R := fun (x : SRecT K₁) (y : SRecT K₂) => RecRR Θ₂ x.1 y.1 ∧ y.2 = x.2)
    (S := fun (x : SRecT K₂) (y : SRecT K₃) => RecRR Θ₃ x.1 y.1 ∧ y.2 = x.2)
    (T := fun (x : SRecT K₁) (y : SRecT K₃) => RecRR Θ₃ x.1 y.1 ∧ y.2 = x.2)
    (fun _ _ _ a b => ⟨RecRR.trans hE a.1 b.1, b.2.trans a.2⟩) h h'

theorem RecsRR.refl {K : WCactus} {Θ : CodeTy} {rs : List (FrameRecT K)}
    (h : ∀ r ∈ rs, CovR (sem Θ) K r.R) : RecsRR (K' := K) Θ rs rs :=
  List.forall₂_same.mpr fun r hr => RecRR.refl (h r hr)

theorem SRecsRR.refl {K : WCactus} {Θ : CodeTy} {ls : List (SRecT K)}
    (h : ∀ x ∈ ls, CovR (sem Θ) K x.1.R) : SRecsRR (K' := K) Θ ls ls :=
  List.forall₂_same.mpr fun x hx => ⟨RecRR.refl (h x hx), rfl⟩

/-- Every record of the world is covered (`TWNT.cov_recs`). -/
theorem RecInv.cov_ps {w : TWd} {fρ : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} (h : RecInv w fρ ps ls) : ∀ r ∈ ps, CovR (sem w.Θ) w.K r.R :=
  h.1.cov_recs.1

theorem RecInv.cov_ls {w : TWd} {fρ : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} (h : RecInv w fρ ps ls) : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R :=
  fun x hx => h.1.cov_recs.2 x.1 (List.mem_map_of_mem hx)

theorem SplitT.left {K : WCactus} {ps O psF : List (FrameRecT K)} (h : SplitT ps O psF) :
    ∀ p ∈ O, p ∈ ps := fun p hp => (h.1 p).mpr (Or.inl hp)

theorem SplitT.right {K : WCactus} {ps O psF : List (FrameRecT K)} (h : SplitT ps O psF) :
    ∀ p ∈ psF, p ∈ ps := fun p hp => (h.1 p).mpr (Or.inr hp)

/-! ### The relation -/

/-! ### Basic facts -/

/-! ### Bind -/

/-! ### Reassociation -/

theorem reassoc_out {K : WCactus} {ρf ρ₀ fρ ρ₁ ρ₂ : TRes K} (hc : ResUT.CompS ρf ρ₀ fρ)
    (h₀ : ResUT.CompS ρ₁ ρ₂ ρ₀) : ∃ y, ResUT.CompS ρf ρ₂ y ∧ ResUT.CompS y ρ₁ fρ :=
  (ResUT.CompS.assoc ρf ρ₂ ρ₁ fρ).mp ⟨ρ₀, ResUT.CompS.comm h₀, hc⟩

theorem reassoc_in {K : WCactus} {ρf ρ₂ y ρ₁ fρ : TRes K} (hy : ResUT.CompS ρf ρ₂ y)
    (hc : ResUT.CompS y ρ₁ fρ) : ∃ ρ', ResUT.CompS ρ₁ ρ₂ ρ' ∧ ResUT.CompS ρf ρ' fρ := by
  obtain ⟨x, hx, hfx⟩ := (ResUT.CompS.assoc ρf ρ₂ ρ₁ fρ).mpr ⟨y, hy, hc⟩
  exact ⟨x, ResUT.CompS.comm hx, hfx⟩

/-! ### The frame -/

/-! ### World changes at the start of a run -/

/-! ### Row 5.27's `mut` clause at `twp`'s ends -/

end BoCa.Fig16.Tree.Wp

end
