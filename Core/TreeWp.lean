import Core.StepsN
import Support.Model.Tree.World.Recs

/-!
# The step-indexed relation over the tree world: `twp`  `[spec §62]`

`twp F Q n w ls O e ρ`: a run of `e` from the resource `ρ` at the tree world `w`
(`Support/Model/Tree/World/World.lean`), owning the records `O` and reading the tagged list `ls`,
under every frame meeting `F`, cut at the step index `n`. It is Core's step-indexed `wp` read at a
world that grows. Each change is forced by the world growing:

* **The frame is quantified over the tree world.** A run starts at any extension `w₀` of `w`,
  from the re-reading `ρ₀` of `ρ` there (`RRw`): a stored continuation is resumed after the tree
  grew under it (a graft) and its cells' invariants were re-read. This makes `twp` monotone along
  world extension by construction (`twp_kripke`).
* **The world at the end extends the world at the start**, and the frame at the end is the
  frame at the start re-read there (`EndT`). A run that opens a lend adds a child to the tree; a
  run that resumes a stored task inside a newer lend grafts it; neither touches the frame's cells
  other than by re-reading them.
* **Records are carried, re-read** (`World/Recs.lean`): the run owns records `O` and reads a
  tagged list `ls`; the frame owns `psF`; `SplitT ps O psF` and `RecInv` hold of the world. At an
  extension the records are re-read with the world (`RecsRR`, `SRecsRR`). The end's frame records
  are the start's re-read there.
* **The world invariant** is `WInv` (covered by `sem Θ`, lowering to the memory) beside `RecInv`.
* **Each extension carries a resource**: the run's start extends `w` carrying the run's resource,
  the end extends the start carrying the frame (`TWd.Ext`). A location only the run holds a `mut`
  cell at, or none does, may be re-typed: the run may free a location and allocate it at another
  code.

The post-configuration relates the run's start and end by row 5.27's `↭` read across the
re-reading and masked at the run's own records (`UpdX`, departure D1 of
`docs/new-core/scope-781.md` §8), with `↭`'s `P̂` as codes (`InvKept`, D2). It has no `ρ⁺`: row
5.33's `ρ ↭ ρ′ ● ρ⁺` is read as `ρ₀ ↭ ρ′` (D4).

The rules: downward closure (`twp_le`), monotonicity (`twp_mono`, `twp_frameCond`), the Kripke
rule (`twp_kripke`), a final term (`twp_here`), deterministic steps (`twp_det`, `twp_step`), bind
at any final term (`twp_bind`), the frame (`twp_frame`, and `twp_frame_w`, whose frame obligation
also reads the start world's invariants), world changes at a segment's start (`twp_extend`),
resource and record changes at a segment's start (`twp_update`), and row 5.27's `mut` clause at
every end (`endT_inv`).

What the rules ask in exchange: a frame condition and a resource framed beside a run, with the
records it owns, must be carried along re-reading (`TFrame.Mono`, `TRProp.Mono`); records owned
apart are at different locations (`twp_frame`'s `hO`), which re-reading keeps.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)

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
invariants, and two clauses about the run from `ρ₀` with records `O₀`:

* **`↭`**, as `[TR]` p. 6's `wp` asks it of the run (row 5.33, `ρ ↭ ρ′ ● ρ⁺`) and row 5.27 reads
  it, across the re-reading from `w₀` to `w′` (`UpdX`): every `imm` cell of `⦇ρ₀⦈` is one of
  `⦇ρ′⦈`, with its lifetime set and value and the witness re-read, and conversely; every `mut`
  cell of the one is a `mut` cell of the other, `β̄` re-read. Exempt (`recMask`): the lent
  locations and escrow locations of the run's own records, `O₀` on the start side and `O′` on
  the end side. A lend the run opened and left open at a stop has turned an `own` cell into the
  lend cell and handed out views of the escrow, and a lend it ended has turned them back; both
  change `⦇·⦈` at those locations and nowhere else, and neither is a copy of someone else's cell.
  No other location is exempt (`updX_refl_imm`).
* **The frame holds nothing at a record the run opened or ended** (`MaskDiff`): where only one
  side is masked, the re-read frame's flattening is empty. A frame beside a run (`twp_frame`)
  is carried by `↭` only where both sides of the run read the same cells or both are masked
  (`UpdX.frame`).
* **`↭`'s `P̂`** (`InvKept`): at every unmasked `mut` cell of `⦇ρ₀⦈` the code typing of `w′` keeps
  `w₀`'s code. A flattened `mut` cell's invariant is its location's code read at the world
  (`flat_mut_inv`), so with `UpdX` this is row 5.27's `mut` clause, `P̂` re-read (`endT_inv`). -/
def EndT (Q : TPost) (k : Nat) (w₀ : TWd) (ρ₀ : TRes w₀.K) (O₀ : List (FrameRecT w₀.K))
    (ρf : TRes w₀.K) (psF : List (FrameRecT w₀.K)) (μ' : Heap) (t : Expr) : Prop :=
  ∃ (w' : TWd) (ρf' ρ' fρ' : TRes w'.K) (psF' ps' O' : List (FrameRecT w'.K))
    (ls' : List (SRecT w'.K)), w₀.Ext w' ρf ∧ RRw (w := w₀) (w' := w') ρf ρf' ∧
    RecsRR w'.Θ psF psF' ∧ ResUT.Hash ρ' ρf' ∧ ResUT.CompS ρf' ρ' fρ' ∧ SplitT ps' O' psF' ∧
    RecInv w' fρ' ps' ls' ∧ WInv w' fρ' μ' ∧ Q k w' ls' O' t ρ' ∧
    UpdX (sem w'.Θ) (recMask O₀) (recMask O') ρ₀ ρ' ∧
    NoneAt (MaskDiff (recMask O₀) (recMask O')) ρf' ∧ InvKept w₀.Θ w'.Θ (recMask O₀) ρ₀

/-- **`crwpG` over the tree world.** -/
def twp (F : TFrame) (Q : TPost) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K) : Prop :=
  ∀ (w₀ : TWd) (ρ₀ ρf fρ : TRes w₀.K) (ls₀ : List (SRecT w₀.K))
    (O₀ ps psF : List (FrameRecT w₀.K)) (μ : Heap),
    w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ →
    F w₀ ρf → ResUT.Hash ρf ρ₀ → ResUT.CompS ρf ρ₀ fρ → SplitT ps O₀ psF →
    RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → FinDom μ →
    ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' → Final (ℍ := ℍ) μ' e' →
      EndT Q (n - j) w₀ ρ₀ O₀ ρf psF μ' e'

/-! ### Basic facts -/

theorem EndT.mono {P Q : TPost} {k k' : Nat} {t : Expr}
    (hPQ : ∀ w ls O ρ, P k w ls O t ρ → Q k' w ls O t ρ) {w₀ : TWd} {ρ₀ : TRes w₀.K}
    {O₀ : List (FrameRecT w₀.K)} {ρf : TRes w₀.K}
    {psF : List (FrameRecT w₀.K)} {μ' : Heap} (h : EndT P k w₀ ρ₀ O₀ ρf psF μ' t) :
    EndT Q k' w₀ ρ₀ O₀ ρf psF μ' t := by
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ :=
    h
  exact ⟨w', ρf', ρ', fρ', psF', ps', O', ls', h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, hPQ _ _ _ _ h₈,
    h₉, h₁₀, h₁₁⟩

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

/-- The resource of a run, part of a world in the invariant, is valid. -/
theorem cov_valid {w : TWd} {ρf ρ fρ : TRes w.K} {μ : Heap} (hc : ResUT.CompS ρf ρ fρ)
    (hI : WInv w fρ μ) : ResUT.Valid ρ :=
  (ResUT.Valid.split hc hI.valid).2

theorem covf_valid {w : TWd} {ρf ρ fρ : TRes w.K} {μ : Heap} (hc : ResUT.CompS ρf ρ fρ)
    (hI : WInv w fρ μ) : ResUT.Valid ρf :=
  (ResUT.Valid.split hc hI.valid).1

/-- A part of a world meeting `RecInv` and `WInv` meets `MutCov`. -/
theorem MutCov.of_part {w : TWd} {fρ ρf ρ : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} {μ : Heap} (hR : RecInv w fρ ps ls) (hI : WInv w fρ μ)
    (hc : ResUT.CompS ρf ρ fρ) : MutCov (sem w.Θ) w.K ρ :=
  ⟨cov_of_comp hc hI, fρ, TWNT.mutOne hR.1, fun _ _ h k =>
    h.of_compS_right hc (kind_mut_ne_imm k)⟩

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
    by simpa using h w₀ ρ₀ ls₀ O₀ hE hr hl hO,
    UpdX.of_rr (WCactus.Ext.refl _) _ (cov_valid hc hI)
      (RR.refl (cov_of_comp hc hI)),
    NoneAt.of_false (fun x hx => by unfold MaskDiff at hx; tauto) _, InvKept.refl _ _ _⟩

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
      StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E → EndT Q (n - j) w₀ ρ₀ O₀ ρf psF μ' E := by
    intro j₁ j₂ μ₁ t hjj hrun₁ hfin₁ hrun₂
    obtain ⟨w₁, ρf₁, ρ₁, fρ₁, psF₁, ps₁, O₁, ls₁, g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
        g₁₁⟩ := hw w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j₁ μ₁ t (by omega)
        hrun₁ hfin₁
    have hcov : CovR (sem w₁.Θ) w₁.K ρ₁ := cov_of_comp g₄ g₇
    obtain ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, k₀, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀,
        k₁₁⟩ := g₈ w₁ ρ₁ ρf₁ fρ₁ ls₁ O₁ ps₁ psF₁ μ₁ (TWd.Ext.refl _ _) (RR.refl hcov)
        (SRecsRR.refl g₆.cov_ls) (RecsRR.refl fun r hr => g₆.cov_ps r (g₅.left r hr))
        (hFm _ _ _ _ g₀ g₁ hF) (ResUT.hash_symm g₃) g₄ g₅ g₆ g₇ (fd_stepsN hrun₁ hfd) j₂ μ' E
        (by omega) hrun₂ hfin
    refine ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, g₀.trans g₁ k₀, RRw.trans k₀.1 g₁ k₁,
      g₂.trans k₀.1 k₂, k₃, k₄, k₅, k₆, k₇, ?_, UpdX.trans k₀.1 g₉ k₉, ?_, g₁₁.trans g₉ k₁₁⟩
    · rwa [show n - j₁ - j₂ = n - j by omega] at k₈
    · have hf₂ : NoneAt (MaskDiff (recMask O₀) (recMask O₁)) ρf₂ :=
        g₁₀.rr k₀.1 (covf_valid g₄ g₇) k₁
      exact (hf₂.or k₁₀).mono fun x hx => maskDiff_trans x hx
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · have hfin' : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hfin _ _ (hs.plug K)
    exact go j 0 μ' e' (by omega) hrun' hfin' (.refl _ _)
  · exact go j₁ j₂ μ₁ t hjj hrun₁ hirr hrun₂

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
  obtain ⟨w', y', ρ₁', fρ', psF'', ps', O₁', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    hwp w₀ ρ₁₀ y fρ ls₀ O₁₀ ps (O₂₀ ++ psF) μ hE₁ h₁₀ hl hO₁ (hF w₀ ρf ρ₂₀ y hE₂ h₂₀ hFρ hy)
      (hash_of_inv hyf hI) hyf hS₁ hRi hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₂', psF', rfl, hO₂', hpsF'⟩ := forall₂_append_left g₂
  obtain ⟨ρf', ρ₂', hf', h₂', hy'⟩ :=
    RR.split_retype g₀.1 hy (covf_of_comp hyf hI) g₀.2 g₁
  obtain ⟨ρ', hρ', hfρ'⟩ := reassoc_in hy' g₄
  have hR₂₀ : R w₀ O₂₀ ρ₂₀ := hR _ _ _ _ _ _ hE₂ h₂₀ hO₂ hR₂
  have hvy' : ResUT.Valid y' := (ResUT.Valid.split g₄ g₇.valid).1
  have hu : UpdX (sem w'.Θ) (recMask O₁₀) (recMask O₁') ρ₀ ρ' :=
    UpdX.frame g₀.1 g₉ h₂' hc₀ hρ' (cov_valid hc hI) (cov_valid hfρ' g₇)
      (g₁₀.of_compS_right hy' hvy')
  have hmask : ∀ x, MaskDiff (recMask (O₁₀ ++ O₂₀)) (recMask (O₁' ++ O₂')) x →
      MaskDiff (recMask O₁₀) (recMask O₁') x := fun x hx => by
    unfold MaskDiff at hx ⊢
    rw [recMask_append, recMask_append, ← recMask_rr hO₂' x] at hx
    tauto
  refine ⟨w', ρf', ρ', fρ', psF', ps', O₁' ++ O₂', ls', g₀.of_compS_left hy, hf', hpsF',
    ResUT.hash_symm (hash_of_inv hfρ' g₇), hfρ', ⟨fun p => ?_, fun p hp q hq => ?_⟩, g₆, g₇,
    ⟨O₁', O₂', ρ₁', ρ₂', rfl, hρ', g₈, hR _ _ _ _ _ _ (g₀.of_compS_right hy) h₂' hO₂' hR₂₀⟩,
    (hu.widen (recMask O₂₀)).congr (fun l => recMask_append l)
      (fun l => by rw [recMask_append, recMask_rr hO₂' l]),
    (g₁₀.of_compS_left hy' hvy').mono hmask,
    (g₁₁.mono fun l h => (recMask_append l).mpr (Or.inl h)).frame hc₀ (TWNT.mutOne hRi.1)
      (fun _ _ h k => (h.of_compS_right hc₀ (kind_mut_ne_imm k)).of_compS_right hc
        (kind_mut_ne_imm k))
      (AgreeOn.of_compS_right hy g₀.2)⟩
  · rw [g₅.1 p, List.mem_append, List.mem_append]; tauto
  · rcases List.mem_append.mp hp with h | h
    · exact g₅.2 p h q (List.mem_append_right _ hq)
    · obtain ⟨p₀, hp₀, r₀⟩ := forall₂_mem_right hO₂' h
      obtain ⟨q₀, hq₀, s₀⟩ := forall₂_mem_right hpsF' hq
      rw [r₀.1, s₀.1]
      exact hS.2 p₀ (List.mem_append_right _ hp₀) q₀ hq₀

/-- **`twp_frame`, the frame obligation reading the start world.** As `twp_frame`; the obligation
`hF` is also given the run's re-read records, the composite world `fρ` with its invariants, and
the split of the records proper. -/
theorem twp_frame_w {F F₁ : TFrame} {P : TPost} {R : TRProp} (hR : R.Mono) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O₁ O₂ : List (FrameRecT w.K)}
    (hO : ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) {e : Expr} {ρ₁ ρ₂ ρ : TRes w.K}
    (hcρ : ResUT.CompS ρ₁ ρ₂ ρ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hF : ∀ (w₀ : TWd) (ρf ρ₁₀ ρ₂₀ y fρ : TRes w₀.K) (O₁₀ O₂₀ ps psF : List (FrameRecT w₀.K))
      (ls₀ : List (SRecT w₀.K)) (μ : Heap), w.Ext w₀ ρ₂ → RRw (w := w) (w' := w₀) ρ₂ ρ₂₀ →
      RecsRR w₀.Θ O₁ O₁₀ → RecsRR w₀.Θ O₂ O₂₀ → F w₀ ρf → ResUT.CompS ρf ρ₂₀ y →
      ResUT.CompS y ρ₁₀ fρ → SplitT ps (O₁₀ ++ O₂₀) psF →
      (∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le) → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → F₁ w₀ y)
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
  obtain ⟨w', y', ρ₁', fρ', psF'', ps', O₁', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    hwp w₀ ρ₁₀ y fρ ls₀ O₁₀ ps (O₂₀ ++ psF) μ hE₁ h₁₀ hl hO₁
      (hF w₀ ρf ρ₁₀ ρ₂₀ y fρ O₁₀ O₂₀ ps psF ls₀ μ hE₂ h₂₀ hO₁ hO₂ hFρ hy hyf hS hO₀ hRi hI)
      (hash_of_inv hyf hI) hyf hS₁ hRi hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₂', psF', rfl, hO₂', hpsF'⟩ := forall₂_append_left g₂
  obtain ⟨ρf', ρ₂', hf', h₂', hy'⟩ :=
    RR.split_retype g₀.1 hy (covf_of_comp hyf hI) g₀.2 g₁
  obtain ⟨ρ', hρ', hfρ'⟩ := reassoc_in hy' g₄
  have hR₂₀ : R w₀ O₂₀ ρ₂₀ := hR _ _ _ _ _ _ hE₂ h₂₀ hO₂ hR₂
  have hvy' : ResUT.Valid y' := (ResUT.Valid.split g₄ g₇.valid).1
  have hu : UpdX (sem w'.Θ) (recMask O₁₀) (recMask O₁') ρ₀ ρ' :=
    UpdX.frame g₀.1 g₉ h₂' hc₀ hρ' (cov_valid hc hI) (cov_valid hfρ' g₇)
      (g₁₀.of_compS_right hy' hvy')
  have hmask : ∀ x, MaskDiff (recMask (O₁₀ ++ O₂₀)) (recMask (O₁' ++ O₂')) x →
      MaskDiff (recMask O₁₀) (recMask O₁') x := fun x hx => by
    unfold MaskDiff at hx ⊢
    rw [recMask_append, recMask_append, ← recMask_rr hO₂' x] at hx
    tauto
  refine ⟨w', ρf', ρ', fρ', psF', ps', O₁' ++ O₂', ls', g₀.of_compS_left hy, hf', hpsF',
    ResUT.hash_symm (hash_of_inv hfρ' g₇), hfρ', ⟨fun p => ?_, fun p hp q hq => ?_⟩, g₆, g₇,
    ⟨O₁', O₂', ρ₁', ρ₂', rfl, hρ', g₈, hR _ _ _ _ _ _ (g₀.of_compS_right hy) h₂' hO₂' hR₂₀⟩,
    (hu.widen (recMask O₂₀)).congr (fun l => recMask_append l)
      (fun l => by rw [recMask_append, recMask_rr hO₂' l]),
    (g₁₀.of_compS_left hy' hvy').mono hmask,
    (g₁₁.mono fun l h => (recMask_append l).mpr (Or.inl h)).frame hc₀ (TWNT.mutOne hRi.1)
      (fun _ _ h k => (h.of_compS_right hc₀ (kind_mut_ne_imm k)).of_compS_right hc
        (kind_mut_ne_imm k))
      (AgreeOn.of_compS_right hy g₀.2)⟩
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
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ := hw ρ₀₁ h₀₁ w₁ ρ₀₁ ρf₁ fρ₁ ls₁ O₁ ps₁ psF₁ μ (TWd.Ext.refl _ _)
      (RR.refl (cov_of_comp hc₁ hI₁)) (SRecsRR.refl hR₁.cov_ls)
      (RecsRR.refl fun r hr => hR₁.cov_ps r (hS₁.left r hr)) (hFm _ _ _ _ hEf hf₁ hFρ)
      (hash_of_inv hc₁ hI₁) hc₁ hS₁ hR₁ hI₁ hfd j μ' e' hj hrun hfin
  have hu₀₁ : UpdX (sem w₁.Θ) (recMask O₀) (recMask O₁) ρ₀ ρ₀₁ :=
    (UpdX.of_rr hE₁.1 (recMask O₀) (cov_valid hc hI) h₀₁).congr (fun _ => Iff.rfl)
      (fun l => (recMask_rr hO₁ l).symm)
  have hk₀₁ : InvKept w₀.Θ w₁.Θ (recMask O₀) ρ₀ :=
    InvKept.of_agree (TWNT.mutOne hR.1) (fun _ _ h k => h.of_compS_right hc (kind_mut_ne_imm k))
      (AgreeOn.of_compS_right hc hE₁.2)
  refine ⟨w', ρf', ρ', fρ', psF', ps', O', ls', hEf.trans hf₁ g₀, RRw.trans g₀.1 hf₁ g₁,
    hF₁.trans g₀.1 g₂, g₃, g₄, g₅, g₆, g₇, g₈, hu₀₁.trans g₀.1 g₉, g₁₀.mono fun x hx => ?_,
    hk₀₁.trans hu₀₁ g₁₁⟩
  unfold MaskDiff at hx ⊢
  rw [recMask_rr hO₁ x] at hx
  exact hx

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
        SplitT ps₁ O₁₀ psF ∧ RecInv w₀ fρ₁ ps₁ ls₁₀ ∧ WInv w₀ fρ₁ μ ∧
        UpdX (sem w₀.Θ) (recMask O₀) (recMask O₁₀) ρ₀ ρ₁₀ ∧
        NoneAt (MaskDiff (recMask O₀) (recMask O₁₀)) ρf)
    (h : twp (ℍ := ℍ) F Q n w ls₁ O₁ e ρ₁) : twp (ℍ := ℍ) F Q n w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ hf hc hS hR hI hfd j μ' e' hj hrun hfin
  obtain ⟨ρ₁₀, fρ₁, ls₁₀, O₁₀, ps₁, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ :=
    hup w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ hf hc hS hR hI
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ := h w₀ ρ₁₀ ρf fρ₁ ls₁₀ O₁₀ ps₁ psF μ h₀ h₁ h₂ h₃ hFρ h₄ h₅ h₆ h₇ h₈ hfd j μ' e' hj hrun hfin
  exact ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈,
    UpdX.trans g₀.1 h₉ g₉,
    ((h₁₀.rr g₀.1 (covf_valid hc hI) g₁).or g₁₀).mono fun x hx => maskDiff_trans x hx,
    (InvKept.refl _ _ _).trans h₉ g₁₁⟩

/-! ### Row 5.27's `mut` clause at `twp`'s ends -/

/-- **`↭`'s `mut` clause holds of every `EndT` end, `P̂` re-read.** For a run from `ρ₀` (a part of a
world meeting `RecInv`/`WInv`) to an `EndT` end `ρ′`: the flattenings are related by `UpdX`, and at
every location outside the run's start records where both carry a `mut` cell, the two invariants
are one code `A`, the same at `w₀` and `w′`, read at each world (`XInv`). -/
theorem endT_inv {Q : TPost} {k : Nat} {w₀ : TWd} {ρ₀ ρf fρ : TRes w₀.K}
    {O₀ ps psF : List (FrameRecT w₀.K)} {ls₀ : List (SRecT w₀.K)} {μ μ' : Heap} {t : Expr}
    (hc : ResUT.CompS ρf ρ₀ fρ) (hR : RecInv w₀ fρ ps ls₀) (hI : WInv w₀ fρ μ)
    (h : EndT Q k w₀ ρ₀ O₀ ρf psF μ' t) :
    ∃ (w' : TWd) (ρ' : TRes w'.K) (O' : List (FrameRecT w'.K)) (σ : TRes w₀.K) (σ' : TRes w'.K),
      ResUT.Flat ρ₀ σ ∧ ResUT.Flat ρ' σ' ∧
      (∀ l, XOpt (sem w'.Θ) (recMask O₀ l) (recMask O' l) (σ.get l) (σ'.get l)) ∧
      ∀ l ψ ψ', σ.get l = some ψ → σ'.get l = some ψ' → ¬ recMask O₀ l →
        XInv w₀.Θ w'.Θ w₀.K w'.K l ψ ψ' := by
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', -, -, -, -, g₄, -, g₆, g₇, -, g₉, -, g₁₁⟩ := h
  obtain ⟨σ, σ', hσ, hσ', hx, hinv⟩ :=
    g₉.inv (MutCov.of_part hR hI hc) (MutCov.of_part g₆ g₇ g₄) g₁₁
  exact ⟨w', ρ', O', σ, σ', hσ, hσ', hx, hinv⟩

end BoCa.Fig16.Tree.Wp

end
