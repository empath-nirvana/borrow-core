import Core.TreeWpEff
import Support.Model.Tree.World.Config
import Support.Model.Tree.World.EscBeneath

/-!
# The scheduler-wide invariant over the tree world: `CactusInvT`  `[spec §62]`

The branches (the running computation, the stored continuations, the spawned closures) are
resources at the world's tree, each owning records and each **at a point** of the lifetime tree:
every top cell of its resource carries lifetimes that are the point or enclose it (`OnBranchResT`,
`Support/Model/Tree/World/Branches.lean`; the strata carry it to every cell beneath). The world is
the branches' composition, the records proper are the branches' records, apart by location between
branches (`Apart`), and the world's invariants hold (`RecInv`, `WInv`). The points are departure
D7 of `docs/new-core/scope-781.md` §8: without them the join condition does not follow
(`cactusT_not_fdEsc`).

The operations, each proved to keep the invariant, and what each does to the points:

* **step** (`cactusT_step`): the running branch at `twp` under the frame of the others ends at a
  world extending the start, the others **re-read** there with their records, at their points
  (`AtPoints.rr`: a re-reading keeps an `imm` cell's lifetimes and reads a `mut` cell's antichain
  as its minimal members; the grown tree keeps every nesting). The running branch ends at the
  point its postcondition names (`hpt`): a fresh lend opened and still open moves it to the fresh
  child, a lend ended moves it back.
* **grow** (`cactusT_extend`): a fresh child, a graft or a re-typing of a location no `mut` cell is
  at extends the world, every branch re-read and carried at its point; a grafted task's point is
  unchanged and lies, after the graft, inside the resumer's lend.
* **capture / move** (`cactusT_move`): a part leaves one branch for another (a continuation's
  share stored by the scheduler, a borrow handed to a joiner); the part is on the receiver's point
  (`hσn`); the giver keeps its point.
* **spawn** (`cactusT_spawn`): a part of a branch, with the records it owns, becomes a branch at
  the point it sits on.
* **join** (`cactusT_join`): a finished branch's resource and records become the joiner's, at the
  joiner's point; the resource is on that point. A join that resumes a branch owning a record
  framed at `α` reads `JoinPtT`: no other branch's point is inside `α`. From it the other branches
  hold nothing of the record's lend (`fdEsc_at_join`).
* **unwind** is a step of the cancelled branch's `fin` obligation at `twp`, so it is
  `cactusT_step`.

**Adequacy is derived from the invariant** (`cerwpT_adequacy`): the initial configuration is the
invariant at one empty branch at `⊤`; `cactusT_step` carries it to any final configuration; there
the branch's postcondition gives an empty resource, so the world is empty, so the memory is.

**The configuration without points** (`cactusT_config`, at `World/Config.lean`'s world). Two
branches: the parent, at its lend `α`, holds `ℓ ↦ imm({α}, loc m, m ↦ own(()))` and owns the
record; a child, at `β ⊏ α`, holds the record's canonical image `m ↦ imm({β}, (), ∅)` and owns
nothing. Every clause of `CactusInvT` holds. The child fails `FdEsc` at `m` (`cactusT_not_fdEsc`).
What excludes it at a join is the points: the child's point is inside `α` (`config_not_joinPt`,
`config_branch_inside`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Steps Head Kont freeE)

/-- Records owned by different branches are at different locations. -/
def Apart {K : WCactus} (Os : List (List (FrameRecT K))) : Prop :=
  List.Pairwise (fun O₁ O₂ => ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) Os

/-- Each branch sits at its point: its resource is on the point's branch. -/
abbrev AtPoints {K : WCactus} (bs : List (TBranch K)) (ns : List Life) : Prop :=
  List.Forall₂ (fun (b : TBranch K) n => OnBranchResT K n b.1) bs ns

/-- **The scheduler-wide invariant over the tree world.** The branches, each at its point `ns` in
the lifetime tree, compose to the world; the records proper are theirs, apart by location; the
world's invariants hold. -/
def CactusInvT (w : TWd) (bs : List (TBranch w.K)) (ns : List Life) (W : TRes w.K)
    (ps : List (FrameRecT w.K)) (ls : List (SRecT w.K)) (μ : Heap) : Prop :=
  CompAllT (bs.map Prod.fst) W ∧ (∀ p, p ∈ ps ↔ p ∈ (bs.map Prod.snd).flatten) ∧
    Apart (bs.map Prod.snd) ∧ RecInv w W ps ls ∧ WInv w W μ ∧ AtPoints bs ns


/-- **The re-reading of the world is the branches' re-readings composed**, each branch carried
by the extension. -/
theorem CompAllT.reread {w w' : TWd} {bs : List (TRes w.K)} {W : TRes w.K}
    (h : CompAllT bs W) (hE : w.Ext w' W) (hc : CovR (sem w.Θ) w.K W) {W' : TRes w'.K}
    (hr : RRw (w := w) (w' := w') W W') :
    ∃ bs' : List (TRes w'.K),
      List.Forall₂ (fun a b => w.Ext w' a ∧ RRw (w := w) (w' := w') a b) bs bs' ∧
      CompAllT bs' W' := by
  induction h generalizing W' with
  | nil =>
      refine ⟨[], .nil, ?_⟩
      obtain rfl := RR.of_empty hr
      exact .nil
  | @cons ρ W₀ W₁ ρs hr₁ hc₁ ih =>
      obtain ⟨a', b', ha, hb, hab⟩ := RR.split_retype hE.1 hc₁ hc hE.2 hr
      obtain ⟨bs', h₂, h₃⟩ := ih (hE.of_compS_right hc₁) (CovR.of_compS_right hc₁ hc) hb
      exact ⟨a' :: bs', .cons ⟨hE.of_compS_left hc₁, ha⟩ h₂, .cons h₃ hab⟩

/-! ### Lists of lists along re-reading -/

theorem forall₂_flatten {α β : Type} {R : α → β → Prop} :
    ∀ {Os : List (List α)} {ys : List β}, List.Forall₂ R Os.flatten ys →
      ∃ Os' : List (List β), ys = Os'.flatten ∧ List.Forall₂ (List.Forall₂ R) Os Os'
  | [], ys, h => by cases h; exact ⟨[], rfl, .nil⟩
  | O :: Os, ys, h => by
      obtain ⟨y₁, y₂, rfl, h₁, h₂⟩ := forall₂_append_left (xs₁ := O) (xs₂ := Os.flatten) h
      obtain ⟨Os', rfl, h₃⟩ := forall₂_flatten h₂
      exact ⟨y₁ :: Os', rfl, .cons h₁ h₃⟩

theorem forall₂_zip {α β γ : Type} {P : α → β → Prop} {Q : α → γ → Prop} {R : α → β × γ → Prop}
    (hR : ∀ a b c, P a b → Q a c → R a (b, c)) :
    ∀ {xs : List α} {ys : List β} {zs : List γ}, List.Forall₂ P xs ys →
      List.Forall₂ Q xs zs → List.Forall₂ R xs (ys.zip zs)
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons (hR _ _ _ h₁ h₂) (forall₂_zip hR t₁ t₂)

theorem forall₂_map_left {α β γ : Type} {f : α → β} {R : β → γ → Prop} {xs : List α}
    {ys : List γ} : List.Forall₂ R (xs.map f) ys ↔ List.Forall₂ (fun a c => R (f a) c) xs ys := by
  induction xs generalizing ys with
  | nil => constructor <;> intro h <;> cases h <;> exact .nil
  | cons x xs ih =>
      constructor
      · intro h; cases h with | cons h₁ h₂ => exact .cons h₁ (ih.mp h₂)
      · intro h; cases h with | cons h₁ h₂ => exact .cons h₁ (ih.mpr h₂)

/-- The records re-read keep their locations, so records apart stay apart. -/
theorem Apart.rr {K K' : WCactus} {Θ' : CodeTy} {Os : List (List (FrameRecT K))}
    {Os' : List (List (FrameRecT K'))} (h : List.Forall₂ (RecsRR Θ') Os Os') (hA : Apart Os) :
    Apart Os' := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons O O' Os Os' hO _ ih =>
      obtain ⟨hhd, htl⟩ := List.pairwise_cons.mp hA
      refine List.pairwise_cons.mpr ⟨fun O₂' hO₂' p hp q hq => ?_, ih htl⟩
      obtain ⟨O₂, hO₂, hr₂⟩ := forall₂_mem_right ‹List.Forall₂ (RecsRR Θ') Os Os'› hO₂'
      obtain ⟨p₀, hp₀, rp⟩ := forall₂_mem_right hO hp
      obtain ⟨q₀, hq₀, rq⟩ := forall₂_mem_right hr₂ hq
      rw [rp.1, rq.1]
      exact hhd O₂ hO₂ p₀ hp₀ q₀ hq₀

/-- **The points are kept when the world grows**: every branch re-read stays at its point. -/
theorem AtPoints.rr {w w' : TWd} :
    ∀ {bs : List (TBranch w.K)} {bs' : List (TBranch w'.K)} {ns : List Life},
      List.Forall₂ (fun a b => w.Ext w' a.1 ∧ RRw (w := w) (w' := w') a.1 b.1 ∧
        RecsRR w'.Θ a.2 b.2) bs bs' → AtPoints bs ns → AtPoints bs' ns
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons hn tn => .cons (OnBranchResT.rr h.1.1 h.2.1 hn) (AtPoints.rr t tn)

/-! ### The operations -/

/-- **The running branch and its frame.** -/
theorem cactusT_frame {w : TWd} {ρ : TRes w.K} {O : List (FrameRecT w.K)}
    {rest : List (TBranch w.K)} {W : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} {μ : Heap} {ns : List Life}
    (h : CactusInvT w ((ρ, O) :: rest) ns W ps ls μ) :
    ∃ ρf, CompAllT (rest.map Prod.fst) ρf ∧ ResUT.Hash ρf ρ ∧ ResUT.CompS ρf ρ W ∧
      SplitT ps O (rest.map Prod.snd).flatten := by
  obtain ⟨hC, hps, hA, hR, hI, -⟩ := h
  cases hC with
  | cons hr hc =>
  rename_i ρf
  refine ⟨ρf, hr, hash_of_inv (ResUT.CompS.comm hc) hI, ResUT.CompS.comm hc,
    fun p => by simpa using hps p, fun p hp q hq => ?_⟩
  obtain ⟨hhd, -⟩ := List.pairwise_cons.mp hA
  obtain ⟨O₂, hO₂, hq₂⟩ := List.mem_flatten.mp hq
  exact hhd O₂ hO₂ p hp q hq₂

/-- **A run keeps the invariant**: the running branch at `twp`, under the frame of the others,
ends at a world extending the start where the invariant holds with its new resource and records
and the others re-read, records included. -/
theorem cactusT_step {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {e : Expr} {ρ : TRes w.K}
    {O : List (FrameRecT w.K)} {rest : List (TBranch w.K)} {W : TRes w.K}
    {ps : List (FrameRecT w.K)} {ls : List (SRecT w.K)} {μ : Heap}
    {nb : Life} {ns : List Life}
    (h : twp (ℍ := ℍ) F Q n w ls O e ρ) (hI : CactusInvT w ((ρ, O) :: rest) (nb :: ns) W ps ls μ)
    (hF : ∀ ρf, CompAllT (rest.map Prod.fst) ρf → F w ρf)
    (hpt : ∀ k w' ls' O' t ρ', Q k w' ls' O' t ρ' → ∃ n', OnBranchResT w'.K n' ρ')
    (hfd : FinDom μ)
    {j : Nat} {μ' : Heap} {e' : Expr} (hj : j < n) (hrun : StepsN (ℍ := ℍ) j μ e μ' e')
    (hfin : Final (ℍ := ℍ) μ' e') :
    ∃ (w' : TWd) (ρ' W' : TRes w'.K) (O' ps' : List (FrameRecT w'.K))
      (ls' : List (SRecT w'.K)) (rest' : List (TBranch w'.K)) (nb' : Life), w.K.Ext w'.K ∧
      List.Forall₂ (fun a b => w.Ext w' a.1 ∧ RRw (w := w) (w' := w') a.1 b.1 ∧
        RecsRR w'.Θ a.2 b.2) rest rest' ∧
      CactusInvT w' ((ρ', O') :: rest') (nb' :: ns) W' ps' ls' μ' ∧
      Q (n - j) w' ls' O' e' ρ' := by
  obtain ⟨ρf, hr, hf, hc, hS⟩ := cactusT_frame hI
  obtain ⟨-, -, hA, hR, hI', hpts⟩ := hI
  have hcov : CovR (sem w.Θ) w.K ρ := cov_of_comp hc hI'
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, -, -⟩ :=
    h w ρ ρf W ls O ps _ μ (TWd.Ext.refl _ _) (RR.refl hcov) (SRecsRR.refl hR.cov_ls)
      (RecsRR.refl fun r hr' => hR.cov_ps r (hS.left r hr')) (hF ρf hr) hf hc hS hR hI' hfd j μ'
      e' hj hrun hfin
  obtain ⟨rs', h₁, h₂⟩ := CompAllT.reread hr g₀ (covf_of_comp hc hI') g₁
  obtain ⟨Os', rfl, hOs⟩ := forall₂_flatten g₂
  have hrs := forall₂_map_left.mp h₁
  have hOs' := forall₂_map_left.mp hOs
  have hz := forall₂_zip (R := fun (a : TBranch w.K) (b : TBranch w'.K) =>
      w.Ext w' a.1 ∧ RRw (w := w) (w' := w') a.1 b.1 ∧ RecsRR w'.Θ a.2 b.2)
    (fun a b c hb hc' => ⟨hb.1, hb.2, hc'⟩) hrs hOs'
  have hlen : rs'.length = Os'.length := by
    rw [← h₁.length_eq, ← hOs.length_eq]; simp
  have e₁ : (rs'.zip Os').map Prod.fst = rs' := List.map_fst_zip (le_of_eq hlen)
  have e₂ : (rs'.zip Os').map Prod.snd = Os' := List.map_snd_zip (le_of_eq hlen.symm)
  obtain ⟨-, hAtl⟩ := List.pairwise_cons.mp hA
  obtain ⟨nb', hnb'⟩ := hpt _ _ _ _ _ _ g₈
  cases hpts with
  | cons _ hpts' =>
  refine ⟨w', ρ', fρ', O', ps', ls', rs'.zip Os', nb', g₀.1, hz,
    ⟨?_, fun p => ?_, ?_, g₆, g₇, .cons hnb' (AtPoints.rr hz hpts')⟩, g₈⟩
  · simp only [List.map_cons, e₁]
    exact .cons h₂ (ResUT.CompS.comm g₄)
  · simp only [List.map_cons, e₂, List.flatten_cons, List.mem_append]
    exact g₅.1 p
  · simp only [List.map_cons, e₂]
    refine List.pairwise_cons.mpr ⟨fun O₂ hO₂ p hp q hq => ?_, (Apart.rr hOs hAtl)⟩
    exact g₅.2 p hp q (List.mem_flatten.mpr ⟨O₂, hO₂, hq⟩)

/-- **The world changes under every branch**: a fresh child, a graft, a location no `mut` cell
is at re-typed; the world re-read, every branch re-read; the records re-read and the world's
record invariant at the grown world (`hR'`). -/
theorem cactusT_extend {w w' : TWd} {bs : List (TBranch w.K)} {W : TRes w.K}
    {ps : List (FrameRecT w.K)} {ls : List (SRecT w.K)} (hE : w.Ext w' W) {μ : Heap}
    {ns : List Life} (h : CactusInvT w bs ns W ps ls μ)
    (hR' : ∀ W' : TRes w'.K, RRw (w := w) (w' := w') W W' →
      ∃ (ps' : List (FrameRecT w'.K)) (ls' : List (SRecT w'.K))
        (Os' : List (List (FrameRecT w'.K))),
        List.Forall₂ (RecsRR w'.Θ) (bs.map Prod.snd) Os' ∧
        (∀ p, p ∈ ps' ↔ p ∈ Os'.flatten) ∧ RecInv w' W' ps' ls') :
    ∃ (bs' : List (TBranch w'.K)) (W' : TRes w'.K) (ps' : List (FrameRecT w'.K))
      (ls' : List (SRecT w'.K)),
      List.Forall₂ (fun a b => w.Ext w' a.1 ∧ RRw (w := w) (w' := w') a.1 b.1 ∧
        RecsRR w'.Θ a.2 b.2) bs bs' ∧ CactusInvT w' bs' ns W' ps' ls' μ := by
  obtain ⟨hC, -, hA, -, hI, hpts⟩ := h
  obtain ⟨W', hr, hI'⟩ := hI.reread hE
  obtain ⟨rs', h₁, h₂⟩ := CompAllT.reread hC hE hI.1 hr
  obtain ⟨ps', ls', Os', hOs, hps', hR⟩ := hR' W' hr
  have hrs := forall₂_map_left.mp h₁
  have hOs' := forall₂_map_left.mp hOs
  have hz := forall₂_zip (R := fun (a : TBranch w.K) (b : TBranch w'.K) =>
      w.Ext w' a.1 ∧ RRw (w := w) (w' := w') a.1 b.1 ∧ RecsRR w'.Θ a.2 b.2)
    (fun a b c hb hc' => ⟨hb.1, hb.2, hc'⟩) hrs hOs'
  have hlen : rs'.length = Os'.length := by
    rw [← h₁.length_eq, ← hOs.length_eq]; simp
  have e₁ : (rs'.zip Os').map Prod.fst = rs' := List.map_fst_zip (le_of_eq hlen)
  have e₂ : (rs'.zip Os').map Prod.snd = Os' := List.map_snd_zip (le_of_eq hlen.symm)
  refine ⟨rs'.zip Os', W', ps', ls', hz, by rw [e₁]; exact h₂, by rw [e₂]; exact hps',
    by rw [e₂]; exact Apart.rr hOs hA, hR, hI', AtPoints.rr hz hpts⟩

/-- **The scheduler moves a part between branches**: `σ` leaves the first branch for the second,
with the records `Oσ` it owns, at locations apart from those the first keeps (`hσ`); the world,
the records proper and the memory are unchanged. -/
theorem cactusT_move {w : TWd} {ρ₁ ρ₂ σ ρ₁' ρ₂' : TRes w.K} {O₁ O₂ Oσ : List (FrameRecT w.K)}
    {rest : List (TBranch w.K)} {W : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} {μ : Heap} {n₁ n₂ : Life} {ns : List Life}
    (h₁ : ResUT.CompS ρ₁' σ ρ₁) (h₂ : ResUT.CompS ρ₂ σ ρ₂')
    (hσ : ∀ p ∈ O₁, ∀ q ∈ Oσ, p.le ≠ q.le) (hσn : OnBranchResT w.K n₂ σ)
    (hI : CactusInvT w ((ρ₁, Oσ ++ O₁) :: (ρ₂, O₂) :: rest) (n₁ :: n₂ :: ns) W ps ls μ) :
    CactusInvT w ((ρ₁', O₁) :: (ρ₂', O₂ ++ Oσ) :: rest) (n₁ :: n₂ :: ns) W ps ls μ := by
  obtain ⟨hC, hps, hA, hR, hI', hpts⟩ := hI
  obtain _ | ⟨hp₁, _ | ⟨hp₂, hpr⟩⟩ := hpts
  refine ⟨?_, fun p => ?_, ?_, hR, hI', .cons (hp₁.of_compS_left h₁)
    (.cons (OnBranchResT.compS h₂ hp₂ hσn) hpr)⟩
  · simp only [List.map_cons] at hC ⊢
    cases hC with
    | cons hr hc =>
    cases hr with
    | cons hr' hc' =>
    rename_i W₁ W₂
    obtain ⟨x, hx, hW⟩ := (ResUT.CompS.assoc ρ₁' σ W₁ W).mpr ⟨ρ₁, h₁, hc⟩
    obtain ⟨y, hy, hyx⟩ := (ResUT.CompS.assoc σ ρ₂ W₂ x).mp ⟨W₁, hc', hx⟩
    obtain rfl := ResUT.CompS.functional hy (ResUT.CompS.comm h₂)
    exact .cons (.cons hr' hyx) hW
  · rw [hps p]
    simp only [List.map_cons, List.flatten_cons, List.mem_append]
    tauto
  · simp only [List.map_cons] at hA ⊢
    obtain ⟨h₁₂, h₁r⟩ := List.pairwise_cons.mp hA
    obtain ⟨h₂r, hr⟩ := List.pairwise_cons.mp h₁r
    have h12 := h₁₂ O₂ List.mem_cons_self
    refine List.pairwise_cons.mpr ⟨fun O hO p hp q hq => ?_,
      List.pairwise_cons.mpr ⟨fun O hO p hp q hq => ?_, hr⟩⟩
    · rcases List.mem_cons.mp hO with rfl | hO
      · rcases List.mem_append.mp hq with hq | hq
        · exact h12 p (List.mem_append_right _ hp) q hq
        · exact hσ p hp q hq
      · exact h₁₂ O (List.mem_cons_of_mem _ hO) p (List.mem_append_right _ hp) q hq
    · rcases List.mem_append.mp hp with hp | hp
      · exact h₂r O hO p hp q hq
      · exact h₁₂ O (List.mem_cons_of_mem _ hO) p (List.mem_append_left _ hp) q hq

/-- **A spawn**: a part `ρ₂` of a branch, with the records `O₂` it owns, becomes a new branch at
the point `n₂` it sits on. -/
theorem cactusT_spawn {w : TWd} {ρ ρ₁ ρ₂ : TRes w.K} {O₁ O₂ : List (FrameRecT w.K)}
    {rest : List (TBranch w.K)} {W : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} {μ : Heap} {n n₂ : Life} {ns : List Life}
    (hρ : ResUT.CompS ρ₁ ρ₂ ρ) (hO : ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le)
    (hn₂ : OnBranchResT w.K n₂ ρ₂)
    (hI : CactusInvT w ((ρ, O₁ ++ O₂) :: rest) (n :: ns) W ps ls μ) :
    CactusInvT w ((ρ₁, O₁) :: (ρ₂, O₂) :: rest) (n :: n₂ :: ns) W ps ls μ := by
  obtain ⟨hC, hps, hA, hR, hI', hpts⟩ := hI
  obtain _ | ⟨hpt₀, hpr⟩ := hpts
  refine ⟨?_, fun p => ?_, ?_, hR, hI', .cons (hpt₀.of_compS_left hρ) (.cons hn₂ hpr)⟩
  · simp only [List.map_cons] at hC ⊢
    cases hC with
    | cons hr hc =>
    rename_i W₁
    obtain ⟨y, hy, hyW⟩ := (ResUT.CompS.assoc ρ₁ ρ₂ W₁ W).mpr ⟨ρ, hρ, hc⟩
    exact .cons (.cons hr hy) hyW
  · rw [hps p]
    simp only [List.map_cons, List.flatten_cons, List.mem_append]
    tauto
  · simp only [List.map_cons] at hA ⊢
    obtain ⟨h₁, hr⟩ := List.pairwise_cons.mp hA
    refine List.pairwise_cons.mpr ⟨fun O hO' p hp q hq => ?_,
      List.pairwise_cons.mpr ⟨fun O hO' p hp q hq => ?_, hr⟩⟩
    · rcases List.mem_cons.mp hO' with rfl | hO'
      · exact hO p hp q hq
      · exact h₁ O hO' p (List.mem_append_left _ hp) q hq
    · exact h₁ O hO' p (List.mem_append_right _ hp) q hq

/-- **A join**: the joined branch's resource and records become the joiner's, the joiner's point
kept; the joined resource is on the joiner's branch (`hb`). -/
theorem cactusT_join {w : TWd} {ρa ρb ρab : TRes w.K} {Oa Ob : List (FrameRecT w.K)}
    {rest : List (TBranch w.K)} {W : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} {μ : Heap} {na nb : Life} {ns : List Life}
    (hab : ResUT.CompS ρa ρb ρab) (hb : OnBranchResT w.K na ρb)
    (hI : CactusInvT w ((ρa, Oa) :: (ρb, Ob) :: rest) (na :: nb :: ns) W ps ls μ) :
    CactusInvT w ((ρab, Oa ++ Ob) :: rest) (na :: ns) W ps ls μ := by
  obtain ⟨hC, hps, hA, hR, hI', hpts⟩ := hI
  obtain _ | ⟨hpa, _ | ⟨-, hpr⟩⟩ := hpts
  refine ⟨?_, fun p => ?_, ?_, hR, hI', .cons (OnBranchResT.compS hab hpa hb) hpr⟩
  · simp only [List.map_cons] at hC ⊢
    cases hC with
    | cons hr hc =>
    cases hr with
    | cons hr' hc' =>
    rename_i W₁ W₂
    obtain ⟨y, hy, hyW⟩ := (ResUT.CompS.assoc ρa ρb W₂ W).mp ⟨W₁, hc', hc⟩
    obtain rfl := ResUT.CompS.functional hy hab
    exact .cons hr' hyW
  · rw [hps p]
    simp only [List.map_cons, List.flatten_cons, List.mem_append]
    tauto
  · simp only [List.map_cons] at hA ⊢
    obtain ⟨ha, hr⟩ := List.pairwise_cons.mp hA
    obtain ⟨hb', hr'⟩ := List.pairwise_cons.mp hr
    refine List.pairwise_cons.mpr ⟨fun O hO' p hp q hq => ?_, hr'⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact ha O (List.mem_cons_of_mem _ hO') p hp q hq
    · exact hb' O hO' p hp q hq

/-- **What a join's resume reads of the points**: no other branch sits inside the frame `α` of a
record the resumed branch owns. -/
def JoinPtT {K : WCactus} (others : List Life) (α : Life) : Prop := ∀ n ∈ others, ¬ K.le n α

/-! ### Adequacy -/

/-- `⟦∅⟧` is the empty memory. -/
theorem lower_emptyT {K : WCactus} :
    ResUT.Lower (PMap.empty : TRes K) (fun _ => none) :=
  ⟨PMap.empty, ⟨PMap.empty, PMap.empty, exW_empty, agW_empty, G.comp_empty_right _⟩,
    fun _ => by simp⟩

/-- The empty world at any tree and the empty store typing. -/
theorem winv_empty (P : ParentFn) :
    WInv ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ (PMap.empty : TRes (WCactus.ofParent P)) (fun _ => none) :=
  ⟨fun _ _ e => by simp at e, lower_emptyT⟩

theorem recInv_empty (P : ParentFn) :
    RecInv ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ (PMap.empty : TRes (WCactus.ofParent P)) [] [] :=
  ⟨.empty, fun _ hx => by simp at hx⟩

/-- Nothing stops at the empty table. -/
def OpTabT.empty : OpTabT := fun _ _ => none

theorem opTableT_empty_false {F : TFrame} {k : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {t : Expr} {Ψ : ContT} {ρ : TRes w.K}
    (h : opTableT OpTabT.empty F k w ls O t Ψ ρ) : False := by
  obtain ⟨_, _, _, _, _, _, _, h, _⟩ := h
  simp [OpTabT.empty] at h

/-- **Adequacy at `cerwpT`, from the invariant**: a closed program at the empty table, from the
empty world at a tree `P` with no records, under the frame condition "the frame is empty", whose
result holds nothing, is safe or diverges, a value only at the empty memory, every `free` finding
its cell. -/
theorem cerwpT_adequacy (P : ParentFn) {Q : TPostV} {P₀ : Expr}
    (hQ : ∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty)
    (hall : ∀ n, cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Q (fun _ ρf => ρf = PMap.empty)
      (fun _ ρf => ρf = PMap.empty) n ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ [] [] P₀
      (PMap.empty : TRes (WCactus.ofParent P))) :
    OrDiverges (ℍ := ℍ) P₀ := by
  intro μ e hs
  obtain ⟨j, hrun⟩ := stepsN_of_steps hs
  have hI₀ : CactusInvT ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ [(PMap.empty, [])] [⊤]
      PMap.empty [] [] (fun _ => none) :=
    ⟨.cons .nil (ResUT.compS_empty_right _), fun p => by simp,
      List.pairwise_singleton _ _, recInv_empty P, winv_empty P, .cons (OnBranchResT.empty ⊤) .nil⟩
  have hend : Final (ℍ := ℍ) μ e → ∃ v : Val, e = v.1 ∧ μ = fun _ => none := by
    intro hfin
    have h := hall (j + 1)
    rw [cerwpT_eq] at h
    obtain ⟨w', ρ', W', O', ps', ls', rest', -, -, hrest, ⟨hC, -, -, -, hI', -⟩, hq⟩ :=
      cactusT_step h hI₀ (fun ρf hr => by cases hr; rfl) (fun _ _ _ _ _ _ hq => by
        rcases hq with ⟨v, -, hq⟩ | ht
        · obtain rfl := hQ _ _ _ _ _ _ hq; exact ⟨⊤, OnBranchResT.empty ⊤⟩
        · exact (opTableT_empty_false ht).elim)
        finDom_empty (by omega) hrun hfin
    cases hrest
    rcases hq with ⟨v, rfl, hq⟩ | ht
    · obtain rfl := hQ _ _ _ _ _ _ hq
      simp only [List.map_cons, List.map_nil] at hC
      cases hC with
      | cons hr hc =>
          cases hr
          obtain rfl := ResUT.CompS.functional hc (ResUT.compS_empty_right _)
          exact ⟨v, rfl, ResUT.Lower.functional hI'.2 lower_emptyT⟩
    · exact (opTableT_empty_false ht).elim
  have hp : IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e' := by
    by_cases hst : ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e'
    · exact .inr hst
    · have hfin : Final (ℍ := ℍ) μ e := fun μ' e' h => hst ⟨μ', e', h⟩
      obtain ⟨v, rfl, -⟩ := hend hfin
      exact .inl v.2
  refine ⟨hp, fun hv => ?_, fun K ℓ he => ?_⟩
  · have hfin : Final (ℍ := ℍ) μ e := fun μ' e' h => BoLo.no_step_val (w := ⟨e, hv⟩) h
    obtain ⟨-, -, hμ⟩ := hend hfin
    exact hμ
  · subst he
    rcases hp with hv | ⟨μ', e', hst⟩
    · have := K.isVal_of_plug hv
      simp [freeE, Expr.val, Val.prim] at this
    · obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).1 hst
      exact ⟨u, hu⟩


/-! ### The join condition from the points -/

/-- **`FdEsc` at a join, from the cactus invariant**: the resumed branch owns the record framed at
`α`, and no other branch's point is inside `α` (`JoinPtT`). -/
theorem fdEsc_at_join {w : TWd} {ρ : TRes w.K}
    {O : List (FrameRecT w.K)} {others : List (TBranch w.K)} {n₀ : Life} {ns : List Life}
    {W : TRes w.K} {ps : List (FrameRecT w.K)} {ls : List (SRecT w.K)} {μ : BoCa.BoLo.Heap}
    (hC : CactusInvT w ((ρ, O) :: others) (n₀ :: ns) W ps ls μ) {p : FrameRecT w.K}
    (hp : p ∈ O) {α : Life} (hFL : FrameLifeT w.K W p α) (hJ : JoinPtT (K := w.K) ns α)
    {ρf : TRes w.K} (hf : CompAllT (others.map Prod.fst) ρf) : FdEsc p.le p.R ρf := by
  obtain ⟨hCA, hps, -, hR, -, hpts⟩ := hC
  cases hCA with
  | cons hr hc =>
  obtain rfl := compAllT_functional hf hr
  cases hpts with
  | cons _ hpts' =>
  have hpps : p ∈ ps := (hps p).mpr (by simp [hp])
  exact fdEsc_iff_noneAt.mpr (fdEsc_of_points hR.1 hpps hFL
    (forall₂_map_left.mpr hpts') hJ hf hc)

/-- The other branches hold nothing of a record's lend: every composite of them meets `FdEsc`. -/
def JoinReadyEscT {K : WCactus} (others : List (TBranch K)) (l : BoCa.Loc) (R : TRes K) : Prop :=
  ∀ W, CompAllT (others.map Prod.fst) W → FdEsc l R W

/-! ### The configuration without points -/

/-- The branches: the parent owning the record, the child owning nothing. -/
def bsC : List (TBranch wC.K) := [(parentRes, [recE ℓC mC]), (childRes, [])]

/-- The points: the parent at its lend `α`, the child at `β`. -/
def nsC : List Life := [αC, βC]

/-- The list: the record, tagged at `α`. -/
def lsC : List (SRecT wC.K) := [(recE ℓC mC, αC)]

/-- The record's lineage locations: `m` only (`ref 1` has no `Mut` position). -/
theorem linLoc_config {x : BoCa.Loc} (h : LinLocT (recE (K := KC) ℓC mC) x) : x = mC := by
  obtain ⟨d, ⟨p, hp⟩, ζ, eζ, -⟩ := h
  cases hp with
  | nil => exact (ResUT.single_get_eq_some eζ).1
  | cons hs hp' =>
      rename_i d' p'
      exact absurd ⟨_, List.cons_ne_nil _ _, LinPathT.cons hs (LinPathT.nil d')⟩
        (recE_no_desc ℓC mC d')

/-- The record's frame is at `α`: its view is the lent cell, and the image at its lineage
location is at `β ⊑ α`. -/
theorem frameLife_config {W : TRes KC} (hW : ResUT.CompS parentRes childRes W) :
    FrameLifeT KC W (recE ℓC mC) αC := by
  refine ⟨fun a ha ζ t e ht y hy => ?_, fun a ha x hx ψ s e hs y hy => ?_⟩
  · change a.get ℓC = some ζ at e
    rw [(ag_config hW ha).1] at e
    cases Option.some.inj e
    change some (TSet.single αC) = some t at ht
    cases Option.some.inj ht
    simpa [TSet.single_set] using hy
  · obtain rfl := linLoc_config hx
    rw [(ag_config hW ha).2] at e
    cases Option.some.inj e
    change some (TSet.single βC) = some s at hs
    cases Option.some.inj hs
    simp only [TSet.single_set, Finset.mem_singleton] at hy
    subst hy
    exact βC_lt_αC.1

/-- A covered `imm` cell over a covered witness. -/
theorem cov_imm_of_wit {Θ : LocTy} {K : WCactus} {l : BoCa.Loc} {ψ : TCell K}
    (hk : ψ.kind = Kind.imm) (hw : CovR Θ K ψ.wit) : Cov Θ K l ψ := by
  rcases CellUT.rep' ψ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b, _, v, χ, hb, P, hP, rfl⟩
  · simp [CellUT.kind, CellUT.ownOf] at hk
  · exact .imm _ _ hw
  · simp [CellUT.kind, CellUT.mutOf] at hk

/-- **The configuration meets every clause of `CactusInvT`.** -/
theorem cactusT_config :
    ∃ (W : TRes wC.K) (μ : BoCa.Loc → Option BoCa.Val),
      ResUT.CompS parentRes childRes W ∧
      CactusInvT wC bsC nsC W [recE ℓC mC] lsC μ := by
  obtain ⟨W, hW, hT⟩ := twnt_config (K := KC) (fun _ => none) βC_lt_αC ℓC_ne_mC
  obtain ⟨σ, hσ⟩ := hT.valid
  refine ⟨W, fun x => (σ.get x).map CellUT.erase, hW, ?_, ?_, ?_, ⟨hT, ?_⟩, ⟨?_, ⟨σ, hσ, fun _ => rfl⟩⟩,
    .cons ?_ (.cons ?_ .nil)⟩
  · exact .cons (.cons .nil (ResUT.compS_empty_right _)) hW
  · intro p; simp [bsC]
  · simp [bsC, Apart]
  · intro x hx
    simp only [lsC, List.mem_singleton] at hx
    subst hx
    exact ⟨recE ℓC mC, List.mem_singleton_self _, ⟨[], .nil _⟩, frameLife_config hW⟩
  · intro x ψ e
    have hk : ψ.kind = Kind.imm := by
      rcases compS_back hW e with ⟨ψ₀, e₀, k₀, -⟩ | ⟨ψ₀, e₀, k₀, -⟩
      · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
        exact k₀.symm.trans (CellUT.kind_immOf _ _ _ _)
      · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
        exact k₀.symm.trans (CellUT.kind_immOf _ _ _ _)
    refine cov_imm_of_wit hk fun y χ ey => ?_
    rcases compS_back hW e with ⟨ψ₀, e₀, -, w₀⟩ | ⟨ψ₀, e₀, -, w₀⟩
    · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
      have ew : (lendCell (K := KC) αC mC).wit = escR mC := CellUT.wit_immOf _ _ _ _
      rw [← w₀, ew, escR] at ey
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some ey
      exact .own _ _
    · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
      have ew : (viewCell (K := KC) βC).wit = PMap.empty := CellUT.wit_immOf _ _ _ _
      rw [← w₀, ew] at ey
      simp at ey
  · intro l ψ e t ht x hx
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
    change some (TSet.single αC) = some t at ht
    cases Option.some.inj ht
    simp only [TSet.single_set, Finset.mem_singleton] at hx
    subst hx; exact KC.refl _
  · intro l ψ e t ht x hx
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
    change some (TSet.single βC) = some t at ht
    cases Option.some.inj ht
    simp only [TSet.single_set, Finset.mem_singleton] at hx
    subst hx; exact KC.refl _

/-- **At the configuration the parent's other branch fails the escrow's frame condition**: the
child fails `FdEsc` at the record's location and escrow, so `JoinReadyEscT` fails. -/
theorem cactusT_not_fdEsc :
    ∃ (W : TRes wC.K) (μ : BoCa.Loc → Option BoCa.Val),
      CactusInvT wC bsC nsC W [recE ℓC mC] lsC μ ∧
      ¬ FdEsc (recE (K := KC) ℓC mC).le (recE (K := KC) ℓC mC).R childRes ∧
      ¬ JoinReadyEscT (bsC.drop 1) (recE (K := KC) ℓC mC).le (recE (K := KC) ℓC mC).R := by
  obtain ⟨W, μ, -, hI⟩ := cactusT_config
  refine ⟨W, μ, hI, config_not_fdEsc, fun hJ => config_not_fdEsc (hJ childRes ?_)⟩
  exact .cons .nil (ResUT.compS_empty_right _)

/-- **A join cannot resume the parent here**: the child's point is inside the parent's lend. -/
theorem config_not_joinPt : ¬ JoinPtT (K := KC) (nsC.drop 1) αC :=
  fun h => h βC (by simp [nsC]) βC_lt_αC.1

/-- **The child's branch is inside the lend**: every point the child's resource sits on is
inside `α`. -/
theorem config_branch_inside {n : Life} (hbr : OnBranchResT KC n childRes) : KC.le n αC :=
  KC.trans (hbr mC (viewCell βC) (ResUT.single_get_self _ _) (TSet.single βC) rfl βC
    (by simp [TSet.single_set])) βC_lt_αC.1

end BoCa.Fig16.Tree.Wp

end
