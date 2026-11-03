import DtorUnwind.TreeWp.Records
import DtorUnwind.SI.RwpG

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

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa.BoLo (Heap Step1 Head Kont)

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

/-- **The records of the world**: `TWNT` at the records proper and the list's records, tagged.
The template choice is read here under `∃`; a relation step that reborrows must keep the choice
of the world it starts from (it changes only at `TWNT.reread`), which this definition does not yet
record. -/
def RecInv (w : TWd) (fρ : TRes w.K) (ps : List (FrameRecT w.K)) (ls : List (SRecT w.K)) :
    Prop :=
  (∃ tc, TWNT w.K w.Θ tc fρ ps (rsOfT ls)) ∧ TaggedT w.K fρ ps ls

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
  h.1.choose_spec.cov_recs.1

theorem RecInv.cov_ls {w : TWd} {fρ : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} (h : RecInv w fρ ps ls) : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R :=
  fun x hx => h.1.choose_spec.cov_recs.2 x.1 (List.mem_map_of_mem hx)

theorem SplitT.left {K : WCactus} {ps O psF : List (FrameRecT K)} (h : SplitT ps O psF) :
    ∀ p ∈ O, p ∈ ps := fun p hp => (h.1 p).mpr (Or.inl hp)

theorem SplitT.right {K : WCactus} {ps O psF : List (FrameRecT K)} (h : SplitT ps O psF) :
    ∀ p ∈ psF, p ∈ ps := fun p hp => (h.1 p).mpr (Or.inr hp)

/-! ### The relation -/

/-- A frame condition, at every world. -/
abbrev TFrame : Type := (w : TWd) → TRes w.K → Prop

/-- A resource predicate with the records it owns, at every world. -/
abbrev TRProp : Type := (w : TWd) → List (FrameRecT w.K) → TRes w.K → Prop

/-- A postcondition over terms: at a step index, a world, the list, the records owned, a term. -/
abbrev TPost : Type :=
  Nat → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → Expr → TRes w.K → Prop

/-- Carried along re-reading, with the records owned. -/
def TRProp.Mono (R : TRProp) : Prop :=
  ∀ (w w' : TWd) (O : List (FrameRecT w.K)) (O' : List (FrameRecT w'.K)) (ρ : TRes w.K)
    (ρ' : TRes w'.K), w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → RecsRR w'.Θ O O' →
    R w O ρ → R w' O' ρ'

/-- A frame condition carried along re-reading. -/
def TFrame.Mono (F : TFrame) : Prop :=
  ∀ (w w' : TWd) (ρ : TRes w.K) (ρ' : TRes w'.K), w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' →
    F w ρ → F w' ρ'

/-- **The post-configuration**: a world `w′` extending the run's world `w₀`, the frame `ρ_f` and
its records `psF` re-read there, the run's resource beside it, the records split, the world's
invariants. -/
def EndT (Q : TPost) (k : Nat) (w₀ : TWd) (ρf : TRes w₀.K) (psF : List (FrameRecT w₀.K))
    (μ' : Heap) (t : Expr) : Prop :=
  ∃ (w' : TWd) (ρf' ρ' fρ' : TRes w'.K) (psF' ps' O' : List (FrameRecT w'.K))
    (ls' : List (SRecT w'.K)), w₀.Ext w' ρf ∧ RRw (w := w₀) (w' := w') ρf ρf' ∧
    RecsRR w'.Θ psF psF' ∧ ResUT.Hash ρ' ρf' ∧ ResUT.CompS ρf' ρ' fρ' ∧ SplitT ps' O' psF' ∧
    RecInv w' fρ' ps' ls' ∧ WInv w' fρ' μ' ∧ Q k w' ls' O' t ρ'

/-- **`crwpG` over the tree world.** -/
def twp (F : TFrame) (Q : TPost) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K) : Prop :=
  ∀ (w₀ : TWd) (ρ₀ ρf fρ : TRes w₀.K) (ls₀ : List (SRecT w₀.K))
    (O₀ ps psF : List (FrameRecT w₀.K)) (μ : Heap),
    w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ →
    F w₀ ρf → ResUT.Hash ρf ρ₀ → ResUT.CompS ρf ρ₀ fρ → SplitT ps O₀ psF →
    RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → FinDom μ →
    ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' → Final (ℍ := ℍ) μ' e' →
      EndT Q (n - j) w₀ ρf psF μ' e'

/-! ### Basic facts -/

theorem EndT.mono {P Q : TPost} {k k' : Nat} {t : Expr}
    (hPQ : ∀ w ls O ρ, P k w ls O t ρ → Q k' w ls O t ρ) {w₀ : TWd} {ρf : TRes w₀.K}
    {psF : List (FrameRecT w₀.K)} {μ' : Heap} (h : EndT P k w₀ ρf psF μ' t) :
    EndT Q k' w₀ ρf psF μ' t := by
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h
  exact ⟨w', ρf', ρ', fρ', psF', ps', O', ls', h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, hPQ _ _ _ _ h₈⟩

theorem twp_zero {F : TFrame} {Q : TPost} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K} : twp (ℍ := ℍ) F Q 0 w ls O e ρ := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j _ _ hj
  omega

theorem twp_mono_le {F : TFrame} {P Q : TPost} {n : Nat}
    (hPQ : ∀ k, k ≤ n → ∀ w ls O t ρ, P k w ls O t ρ → Q k w ls O t ρ) {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F P n w ls O e ρ) : twp (ℍ := ℍ) F Q n w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' hj hrun hfin
  exact (h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' hj hrun
    hfin).mono (fun _ _ _ _ x => hPQ _ (by omega) _ _ _ _ _ x)

theorem twp_mono {F : TFrame} {P Q : TPost}
    (hPQ : ∀ k w ls O t ρ, P k w ls O t ρ → Q k w ls O t ρ) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F P n w ls O e ρ) : twp (ℍ := ℍ) F Q n w ls O e ρ :=
  twp_mono_le (fun k _ => hPQ k) h

/-- A stronger frame condition. -/
theorem twp_frameCond {F F' : TFrame} (hF : ∀ w ρf, F' w ρf → F w ρf) {Q : TPost} {n : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F Q n w ls O e ρ) : twp (ℍ := ℍ) F' Q n w ls O e ρ :=
  fun w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF' =>
    h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO (hF w₀ ρf hF')

/-- A postcondition downward closed in its index. -/
def TPost.Down (Q : TPost) : Prop := ∀ n w ls O t ρ, Q (n + 1) w ls O t ρ → Q n w ls O t ρ

theorem TPost.Down.le {Q : TPost} (hQ : Q.Down) {m k : Nat} (h : m ≤ k) :
    ∀ w ls O t ρ, Q k w ls O t ρ → Q m w ls O t ρ := by
  induction h with
  | refl => exact fun _ _ _ _ _ x => x
  | step _ ih => exact fun w ls O t ρ x => ih w ls O t ρ (hQ _ _ _ _ _ _ x)

/-- **`twp` is downward closed.** -/
theorem twp_le {F : TFrame} {Q : TPost} (hQ : Q.Down) {m n : Nat} (hmn : m ≤ n) {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F Q n w ls O e ρ) : twp (ℍ := ℍ) F Q m w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' hj hrun hfin
  exact (h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' (by omega)
    hrun hfin).mono (fun _ _ _ _ x => hQ.le (by omega) _ _ _ _ _ x)

/-- **`twp` is monotone along world extension**: by construction, the frame being quantified
over the extensions. -/
theorem twp_kripke {F : TFrame} {Q : TPost} {n : Nat} {w w₁ : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ls₁ : List (SRecT w₁.K)} {O₁ : List (FrameRecT w₁.K)}
    {e : Expr} {ρ : TRes w.K} {ρ₁ : TRes w₁.K} (hE : w.Ext w₁ ρ)
    (hr : RRw (w := w) (w' := w₁) ρ ρ₁) (hl : SRecsRR w₁.Θ ls ls₁) (hO : RecsRR w₁.Θ O O₁)
    (h : twp (ℍ := ℍ) F Q n w ls O e ρ) : twp (ℍ := ℍ) F Q n w₁ ls₁ O₁ e ρ₁ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE₀ hr₀ hl₀ hO₀
  exact h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ (hE.trans hr hE₀) (RRw.trans hE₀.1 hr hr₀)
    (hl.trans hE₀.1 hl₀) (hO.trans hE₀.1 hO₀)

/-- The resource of a run, part of a world in the invariant, is covered. -/
theorem cov_of_comp {w : TWd} {ρf ρ fρ : TRes w.K} {μ : Heap} (hc : ResUT.CompS ρf ρ fρ)
    (hI : WInv w fρ μ) : CovR (sem w.Θ) w.K ρ :=
  CovR.of_compS_right hc hI.1

theorem covf_of_comp {w : TWd} {ρf ρ fρ : TRes w.K} {μ : Heap} (hc : ResUT.CompS ρf ρ fρ)
    (hI : WInv w fρ μ) : CovR (sem w.Θ) w.K ρf :=
  CovR.of_compS_left hc hI.1

/-- **A final term in the postcondition**, at every extension of the world. -/
theorem twp_here {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K} (hfin : ∀ μ, Final (ℍ := ℍ) μ e)
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K) (ls₀ : List (SRecT w₀.K)) (O₀ : List (FrameRecT w₀.K)),
      w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ →
      Q n w₀ ls₀ O₀ e ρ₀) :
    twp (ℍ := ℍ) F Q n w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO _ hf hc hS hR hI _ j μ' e' hj hrun _
  cases hrun with
  | more hs _ => exact absurd hs (hfin _ _ _)
  | refl =>
  exact ⟨w₀, ρf, ρ₀, fρ, psF, ps, O₀, ls₀, TWd.Ext.refl _ _, RR.refl (covf_of_comp hc hI),
    RecsRR.refl fun r hr => hR.cov_ps r (hS.right r hr), ResUT.hash_symm hf, hc, hS, hR, hI,
    by simpa using h w₀ ρ₀ ls₀ O₀ hE hr hl hO⟩

/-- **A step that is its configuration's only one, for free.** -/
theorem twp_det {F : TFrame} {Q : TPost} (hQ : Q.Down) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e e' : Expr} {ρ : TRes w.K}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : twp (ℍ := ℍ) F Q n w ls O e' ρ) :
    twp (ℍ := ℍ) F Q n w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' E hj hrun hfin
  cases hrun with
  | refl => exact absurd (hdet _).1 (hfin _ e')
  | @more j' _ _ _ _ _ _ hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet _).2 _ _ hs
      exact (h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF _ hE hr hl hO hF hf hc hS hR hI hfd j' μ' E
        (by omega) t hfin).mono (fun _ _ _ _ x => hQ.le (by omega) _ _ _ _ _ x)

/-- **A step that is its configuration's only one, paid by the index.** -/
theorem twp_step {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e e' : Expr} {ρ : TRes w.K}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : twp (ℍ := ℍ) F Q n w ls O e' ρ) :
    twp (ℍ := ℍ) F Q (n + 1) w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' E hj hrun hfin
  cases hrun with
  | refl => exact absurd (hdet μ).1 (hfin μ e')
  | @more j' μ μ₁ μ' e e₁ E hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet μ).2 _ _ hs
      have := h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF _ hE hr hl hO hF hf hc hS hR hI hfd j' μ' E
        (by omega) t hfin
      rwa [show n + 1 - (j' + 1) = n - j' by omega]

/-! ### Bind -/

/-- **Bind at any final term**: a run of `e` to a final term `t`, then the continuation from
`K[t]` at the world the run ended at, with the list and records it ended with, under the frame
re-read there. The frame condition is carried along the re-reading (`hFm`). -/
theorem twp_bind {F : TFrame} (hFm : F.Mono) {Q : TPost} (K : Kont) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (hw : twp (ℍ := ℍ) F (fun k w' ls' O' t => twp (ℍ := ℍ) F Q k w' ls' O' (K.plug t)) n w
      ls O e ρ) :
    twp (ℍ := ℍ) F Q n w ls O (K.plug e) ρ := by
  classical
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' E hj hrun hfin
  have go : ∀ j₁ j₂ μ₁ t, j₁ + j₂ = j → StepsN (ℍ := ℍ) j₁ μ e μ₁ t → Final (ℍ := ℍ) μ₁ t →
      StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E → EndT Q (n - j) w₀ ρf psF μ' E := by
    intro j₁ j₂ μ₁ t hjj hrun₁ hfin₁ hrun₂
    obtain ⟨w₁, ρf₁, ρ₁, fρ₁, psF₁, ps₁, O₁, ls₁, g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈⟩ :=
      hw w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j₁ μ₁ t (by omega)
        hrun₁ hfin₁
    have hcov : CovR (sem w₁.Θ) w₁.K ρ₁ := cov_of_comp g₄ g₇
    obtain ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, k₀, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈⟩ :=
      g₈ w₁ ρ₁ ρf₁ fρ₁ ls₁ O₁ ps₁ psF₁ μ₁ (TWd.Ext.refl _ _) (RR.refl hcov)
        (SRecsRR.refl g₆.cov_ls) (RecsRR.refl fun r hr => g₆.cov_ps r (g₅.left r hr))
        (hFm _ _ _ _ g₀ g₁ hF) (ResUT.hash_symm g₃) g₄ g₅ g₆ g₇ (fd_stepsN hrun₁ hfd) j₂ μ' E
        (by omega) hrun₂ hfin
    refine ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, g₀.trans g₁ k₀, RRw.trans k₀.1 g₁ k₁,
      g₂.trans k₀.1 k₂, k₃, k₄, k₅, k₆, k₇, ?_⟩
    rwa [show n - j₁ - j₂ = n - j by omega] at k₈
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · have hfin' : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hfin _ _ (hs.plug K)
    exact go j 0 μ' e' (by omega) hrun' hfin' (.refl _ _)
  · exact go j₁ j₂ μ₁ t hjj hrun₁ hirr hrun₂

/-! ### Reassociation -/

theorem reassoc_out {K : WCactus} {ρf ρ₀ fρ ρ₁ ρ₂ : TRes K} (hc : ResUT.CompS ρf ρ₀ fρ)
    (h₀ : ResUT.CompS ρ₁ ρ₂ ρ₀) : ∃ y, ResUT.CompS ρf ρ₂ y ∧ ResUT.CompS y ρ₁ fρ :=
  (ResUT.CompS.assoc ρf ρ₂ ρ₁ fρ).mp ⟨ρ₀, ResUT.CompS.comm h₀, hc⟩

theorem reassoc_in {K : WCactus} {ρf ρ₂ y ρ₁ fρ : TRes K} (hy : ResUT.CompS ρf ρ₂ y)
    (hc : ResUT.CompS y ρ₁ fρ) : ∃ ρ', ResUT.CompS ρ₁ ρ₂ ρ' ∧ ResUT.CompS ρf ρ' fρ := by
  obtain ⟨x, hx, hfx⟩ := (ResUT.CompS.assoc ρf ρ₂ ρ₁ fρ).mpr ⟨y, hy, hc⟩
  exact ⟨x, ResUT.CompS.comm hx, hfx⟩

/-- A composite of a valid world's parts is `#`. -/
theorem hash_of_inv {w : TWd} {a b y : TRes w.K} {μ : Heap} (hc : ResUT.CompS a b y)
    (hI : WInv w y μ) : ResUT.Hash a b :=
  ResUT.Hash.of_compS hc hI.valid

/-! ### The frame -/

/-- `P ⋆ R` over terms, at a world, the records owned split between the two. -/
def TPost.sep (P : TPost) (R : TRProp) : TPost := fun k w ls O t ρ =>
  ∃ (O₁ O₂ : List (FrameRecT w.K)) (a b : TRes w.K), O = O₁ ++ O₂ ∧ ResUT.CompS a b ρ ∧
    P k w ls O₁ t a ∧ R w O₂ b

theorem forall₂_append_left {α β : Type} {R : α → β → Prop} :
    ∀ {xs₁ xs₂ : List α} {ys : List β}, List.Forall₂ R (xs₁ ++ xs₂) ys →
      ∃ ys₁ ys₂, ys = ys₁ ++ ys₂ ∧ List.Forall₂ R xs₁ ys₁ ∧ List.Forall₂ R xs₂ ys₂
  | [], _, ys, h => ⟨[], ys, rfl, .nil, h⟩
  | _ :: _, _, _ :: _, .cons hxy t =>
      let ⟨ys₁, ys₂, e, h₁, h₂⟩ := forall₂_append_left t
      ⟨_ :: ys₁, ys₂, by rw [e]; rfl, .cons hxy h₁, h₂⟩

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => cases hx
  | cons hxy _ ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, List.mem_cons_self, hxy⟩
      · obtain ⟨y, hy, hr⟩ := ih hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

/-- **The frame**: a resource `ρ₂` in `R`, owning the records `O₂`, kept beside the run, which
owns `O₁`. Forced beside `crwpG_frame`: `R` is carried along re-reading (`hR`), and the framed
resource is covered at its world (`hcov`), so that its parts have re-readings at every extension
carrying it; `O₁` and `O₂` are apart by location (`hO`), which every re-reading keeps. -/
theorem twp_frame {F F₁ : TFrame} {P : TPost} {R : TRProp} (hR : R.Mono) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O₁ O₂ : List (FrameRecT w.K)}
    (hO : ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) {e : Expr} {ρ₁ ρ₂ ρ : TRes w.K}
    (hcρ : ResUT.CompS ρ₁ ρ₂ ρ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hF : ∀ (w₀ : TWd) (ρf ρ₂₀ y : TRes w₀.K), w.Ext w₀ ρ₂ → RRw (w := w) (w' := w₀) ρ₂ ρ₂₀ →
      F w₀ ρf → ResUT.CompS ρf ρ₂₀ y → F₁ w₀ y)
    (hwp : twp (ℍ := ℍ) F₁ P n w ls O₁ e ρ₁) (hR₂ : R w O₂ ρ₂) :
    twp (ℍ := ℍ) F (P.sep R) n w ls (O₁ ++ O₂) e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hOr hFρ hf hc hS hRi hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₁₀, O₂₀, rfl, hO₁, hO₂⟩ := forall₂_append_left hOr
  have hO₀ : ∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le := by
    intro p hp q hq
    obtain ⟨p₁, hp₁, r₁⟩ := forall₂_mem_right hO₁ hp
    obtain ⟨q₂, hq₂, r₂⟩ := forall₂_mem_right hO₂ hq
    rw [r₁.1, r₂.1]
    exact hO p₁ hp₁ q₂ hq₂
  obtain ⟨ρ₁₀, ρ₂₀, h₁₀, h₂₀, hc₀⟩ := RR.split_retype hE.1 hcρ hcov hE.2 hr
  have hE₁ := hE.of_compS_left hcρ
  have hE₂ := hE.of_compS_right hcρ
  obtain ⟨y, hy, hyf⟩ := reassoc_out hc hc₀
  have hS₁ : SplitT ps O₁₀ (O₂₀ ++ psF) := by
    refine ⟨fun p => ?_, fun p hp q hq => ?_⟩
    · rw [hS.1 p, List.mem_append, List.mem_append]; tauto
    · rcases List.mem_append.mp hq with h | h
      · exact hO₀ p hp q h
      · exact hS.2 p (List.mem_append_left _ hp) q h
  obtain ⟨w', y', ρ₁', fρ', psF'', ps', O₁', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈⟩ :=
    hwp w₀ ρ₁₀ y fρ ls₀ O₁₀ ps (O₂₀ ++ psF) μ hE₁ h₁₀ hl hO₁ (hF w₀ ρf ρ₂₀ y hE₂ h₂₀ hFρ hy)
      (hash_of_inv hyf hI) hyf hS₁ hRi hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₂', psF', rfl, hO₂', hpsF'⟩ := forall₂_append_left g₂
  obtain ⟨ρf', ρ₂', hf', h₂', hy'⟩ :=
    RR.split_retype g₀.1 hy (covf_of_comp hyf hI) g₀.2 g₁
  obtain ⟨ρ', hρ', hfρ'⟩ := reassoc_in hy' g₄
  have hR₂₀ : R w₀ O₂₀ ρ₂₀ := hR _ _ _ _ _ _ hE₂ h₂₀ hO₂ hR₂
  refine ⟨w', ρf', ρ', fρ', psF', ps', O₁' ++ O₂', ls', g₀.of_compS_left hy, hf', hpsF',
    ResUT.hash_symm (hash_of_inv hfρ' g₇), hfρ', ⟨fun p => ?_, fun p hp q hq => ?_⟩, g₆, g₇,
    O₁', O₂', ρ₁', ρ₂', rfl, hρ', g₈, hR _ _ _ _ _ _ (g₀.of_compS_right hy) h₂' hO₂' hR₂₀⟩
  · rw [g₅.1 p, List.mem_append, List.mem_append]; tauto
  · rcases List.mem_append.mp hp with h | h
    · exact g₅.2 p h q (List.mem_append_right _ hq)
    · obtain ⟨p₀, hp₀, r₀⟩ := forall₂_mem_right hO₂' h
      obtain ⟨q₀, hq₀, s₀⟩ := forall₂_mem_right hpsF' hq
      rw [r₀.1, s₀.1]
      exact hS.2 p₀ (List.mem_append_right _ hp₀) q₀ hq₀

/-! ### World changes at the start of a run -/

/-- **The world changes at the start of a segment**: at whichever extension the run starts at,
the world may be extended further carrying the whole world (a fresh child, a graft, a location
no `mut` cell is at re-typed), the records re-read with it, and the run continues there from the
re-reading. The frame condition is carried along. What the step asks of the new world (`h`): the
records' re-readings, their invariants there (`RecInv`, `SplitT`). -/
theorem twp_extend {F : TFrame} (hFm : F.Mono) {Q : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ ρf fρ : TRes w₀.K) (ls₀ : List (SRecT w₀.K))
      (O₀ ps psF : List (FrameRecT w₀.K)) (μ : Heap), w.Ext w₀ ρ →
      RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ → F w₀ ρf →
      ResUT.CompS ρf ρ₀ fρ → SplitT ps O₀ psF → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ →
      ∃ (w₁ : TWd), w₀.Ext w₁ fρ ∧ ∀ (fρ₁ : TRes w₁.K), RRw (w := w₀) (w' := w₁) fρ fρ₁ →
        ∃ (ls₁ : List (SRecT w₁.K)) (O₁ ps₁ psF₁ : List (FrameRecT w₁.K)),
          SRecsRR w₁.Θ ls₀ ls₁ ∧ RecsRR w₁.Θ O₀ O₁ ∧ RecsRR w₁.Θ psF psF₁ ∧
          SplitT ps₁ O₁ psF₁ ∧ RecInv w₁ fρ₁ ps₁ ls₁ ∧
          ∀ ρ₁ : TRes w₁.K, RRw (w := w₀) (w' := w₁) ρ₀ ρ₁ →
            twp (ℍ := ℍ) F Q n w₁ ls₁ O₁ e ρ₁) :
    twp (ℍ := ℍ) F Q n w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ hf hc hS hR hI hfd j μ' e' hj hrun hfin
  obtain ⟨w₁, hE₁, hw₁⟩ := h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ hc hS hR hI
  obtain ⟨fρ₁, hfr, hI₁⟩ := hI.reread hE₁
  obtain ⟨ls₁, O₁, ps₁, psF₁, hl₁, hO₁, hF₁, hS₁, hR₁, hw⟩ := hw₁ fρ₁ hfr
  obtain ⟨ρf₁, ρ₀₁, hf₁, h₀₁, hc₁⟩ := RR.split_retype hE₁.1 hc hI.1 hE₁.2 hfr
  have hEf := hE₁.of_compS_left hc
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈⟩ :=
    hw ρ₀₁ h₀₁ w₁ ρ₀₁ ρf₁ fρ₁ ls₁ O₁ ps₁ psF₁ μ (TWd.Ext.refl _ _)
      (RR.refl (cov_of_comp hc₁ hI₁)) (SRecsRR.refl hR₁.cov_ls)
      (RecsRR.refl fun r hr => hR₁.cov_ps r (hS₁.left r hr)) (hFm _ _ _ _ hEf hf₁ hFρ)
      (hash_of_inv hc₁ hI₁) hc₁ hS₁ hR₁ hI₁ hfd j μ' e' hj hrun hfin
  exact ⟨w', ρf', ρ', fρ', psF', ps', O', ls', hEf.trans hf₁ g₀, RRw.trans g₀.1 hf₁ g₁,
    hF₁.trans g₀.1 g₂, g₃, g₄, g₅, g₆, g₇, g₈⟩

/-- **The resource and the records change at the start of a segment**, under every frame
meeting `F`, keeping the world's invariants and the memory: a lend opened (a record made), a
lend ended. -/
theorem twp_update {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls ls₁ : List (SRecT w.K)}
    {O O₁ : List (FrameRecT w.K)} {e : Expr} {ρ ρ₁ : TRes w.K}
    (hup : ∀ (w₀ : TWd) (ρ₀ ρf fρ : TRes w₀.K) (ls₀ : List (SRecT w₀.K))
      (O₀ ps psF : List (FrameRecT w₀.K)) (μ : Heap), w.Ext w₀ ρ →
      RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ → F w₀ ρf →
      ResUT.Hash ρf ρ₀ → ResUT.CompS ρf ρ₀ fρ → SplitT ps O₀ psF → RecInv w₀ fρ ps ls₀ →
      WInv w₀ fρ μ →
      ∃ (ρ₁₀ fρ₁ : TRes w₀.K) (ls₁₀ : List (SRecT w₀.K)) (O₁₀ ps₁ : List (FrameRecT w₀.K)),
        w.Ext w₀ ρ₁ ∧ RRw (w := w) (w' := w₀) ρ₁ ρ₁₀ ∧ SRecsRR w₀.Θ ls₁ ls₁₀ ∧
        RecsRR w₀.Θ O₁ O₁₀ ∧ ResUT.Hash ρf ρ₁₀ ∧ ResUT.CompS ρf ρ₁₀ fρ₁ ∧
        SplitT ps₁ O₁₀ psF ∧ RecInv w₀ fρ₁ ps₁ ls₁₀ ∧ WInv w₀ fρ₁ μ)
    (h : twp (ℍ := ℍ) F Q n w ls₁ O₁ e ρ₁) : twp (ℍ := ℍ) F Q n w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ hf hc hS hR hI hfd j μ' e' hj hrun hfin
  obtain ⟨ρ₁₀, fρ₁, ls₁₀, O₁₀, ps₁, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ :=
    hup w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ hf hc hS hR hI
  exact h w₀ ρ₁₀ ρf fρ₁ ls₁₀ O₁₀ ps₁ psF μ h₀ h₁ h₂ h₃ hFρ h₄ h₅ h₆ h₇ h₈ hfd j μ' e' hj hrun
    hfin

end BoCa.Fig16.Tree.Wp

end
