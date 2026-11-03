import DtorUnwind.TreeWp.Eff
import DtorUnwind.SI.CaptureAdequacy
import DtorUnwind.Tree.Port.Split

/-!
# The scheduler-wide invariant over the tree world

`SI/CactusInv.lean`'s `CactusInv`, at a world `w`: the branches (the running computation, the
stored continuations, the spawned closures) are resources at `w`'s tree, each owning records;
the world is their composition, the records proper are the branches' records, apart by location
between branches, and the world's invariants hold (`RecInv`, `WInv`).

The operations, each proved to keep the invariant:

* **step** (`cactusT_step`): the running branch at `twp` under the frame of the others ends at a
  world extending the start, the others **re-read** there with their records (in `SI/` they were
  untouched; the tree grew under them);
* **grow** (`cactusT_extend`): a fresh child, a graft or a re-typing of a location no `mut` cell
  is at extends the world, every branch re-read (`CompAllT.reread`) and carried, the records
  re-read; the world's record invariant at the grown world is the step's premise (carrying
  `Tagged` along a re-reading is not built);
* **capture / move** (`cactusT_move`): a part leaves one branch for another (a continuation's
  share stored by the scheduler, a borrow handed to a joiner); world and memory unchanged;
* **unwind** is a step of the cancelled branch's `fin` obligation at `twp`, so it is
  `cactusT_step`.

**Adequacy is derived from the invariant** (`cerwpT_adequacy`): the initial configuration is the
invariant at one empty branch; `cactusT_step` carries it to any final configuration; there the
branch's postcondition gives an empty resource, so the world is empty, so the memory is.
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
open BoCa.BoLo (Heap Step1 Steps Head Kont freeE)

/-- The composition of a list of resources. -/
inductive CompAllT {K : WCactus} : List (TRes K) → TRes K → Prop
  | nil : CompAllT [] PMap.empty
  | cons {ρ W W' : TRes K} {ρs : List (TRes K)} : CompAllT ρs W' → ResUT.CompS ρ W' W →
      CompAllT (ρ :: ρs) W

/-- A branch: its resource and the records it owns. -/
abbrev TBranch (K : WCactus) : Type := TRes K × List (FrameRecT K)

/-- Records owned by different branches are at different locations. -/
def Apart {K : WCactus} (Os : List (List (FrameRecT K))) : Prop :=
  List.Pairwise (fun O₁ O₂ => ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) Os

/-- **The scheduler-wide invariant over the tree world.** -/
def CactusInvT (w : TWd) (bs : List (TBranch w.K)) (W : TRes w.K) (ps : List (FrameRecT w.K))
    (ls : List (SRecT w.K)) (μ : Heap) : Prop :=
  CompAllT (bs.map Prod.fst) W ∧ (∀ p, p ∈ ps ↔ p ∈ (bs.map Prod.snd).flatten) ∧
    Apart (bs.map Prod.snd) ∧ RecInv w W ps ls ∧ WInv w W μ

theorem compAllT_functional {K : WCactus} {ρs : List (TRes K)} {W W' : TRes K}
    (h : CompAllT ρs W) (h' : CompAllT ρs W') : W = W' := by
  induction h generalizing W' with
  | nil => cases h'; rfl
  | cons hr hc ih =>
      cases h' with
      | cons hr' hc' =>
          cases ih hr'
          exact ResUT.CompS.functional hc hc'

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

theorem forall₂_length_eq' {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : xs.length = ys.length := h.length_eq

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

/-! ### The operations -/

/-- **The running branch and its frame.** -/
theorem cactusT_frame {w : TWd} {ρ : TRes w.K} {O : List (FrameRecT w.K)}
    {rest : List (TBranch w.K)} {W : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} {μ : Heap} (h : CactusInvT w ((ρ, O) :: rest) W ps ls μ) :
    ∃ ρf, CompAllT (rest.map Prod.fst) ρf ∧ ResUT.Hash ρf ρ ∧ ResUT.CompS ρf ρ W ∧
      SplitT ps O (rest.map Prod.snd).flatten := by
  obtain ⟨hC, hps, hA, hR, hI⟩ := h
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
    (h : twp (ℍ := ℍ) F Q n w ls O e ρ) (hI : CactusInvT w ((ρ, O) :: rest) W ps ls μ)
    (hF : ∀ ρf, CompAllT (rest.map Prod.fst) ρf → F w ρf) (hfd : FinDom μ)
    {j : Nat} {μ' : Heap} {e' : Expr} (hj : j < n) (hrun : StepsN (ℍ := ℍ) j μ e μ' e')
    (hfin : Final (ℍ := ℍ) μ' e') :
    ∃ (w' : TWd) (ρ' W' : TRes w'.K) (O' ps' : List (FrameRecT w'.K))
      (ls' : List (SRecT w'.K)) (rest' : List (TBranch w'.K)), w.K.Ext w'.K ∧
      List.Forall₂ (fun a b => w.Ext w' a.1 ∧ RRw (w := w) (w' := w') a.1 b.1 ∧
        RecsRR w'.Θ a.2 b.2) rest rest' ∧
      CactusInvT w' ((ρ', O') :: rest') W' ps' ls' μ' ∧ Q (n - j) w' ls' O' e' ρ' := by
  obtain ⟨ρf, hr, hf, hc, hS⟩ := cactusT_frame hI
  obtain ⟨-, -, hA, hR, hI'⟩ := hI
  have hcov : CovR (sem w.Θ) w.K ρ := cov_of_comp hc hI'
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈⟩ :=
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
  refine ⟨w', ρ', fρ', O', ps', ls', rs'.zip Os', g₀.1, hz, ⟨?_, fun p => ?_, ?_, g₆, g₇⟩, g₈⟩
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
    (h : CactusInvT w bs W ps ls μ)
    (hR' : ∀ W' : TRes w'.K, RRw (w := w) (w' := w') W W' →
      ∃ (ps' : List (FrameRecT w'.K)) (ls' : List (SRecT w'.K))
        (Os' : List (List (FrameRecT w'.K))),
        List.Forall₂ (RecsRR w'.Θ) (bs.map Prod.snd) Os' ∧
        (∀ p, p ∈ ps' ↔ p ∈ Os'.flatten) ∧ RecInv w' W' ps' ls') :
    ∃ (bs' : List (TBranch w'.K)) (W' : TRes w'.K) (ps' : List (FrameRecT w'.K))
      (ls' : List (SRecT w'.K)),
      List.Forall₂ (fun a b => w.Ext w' a.1 ∧ RRw (w := w) (w' := w') a.1 b.1 ∧
        RecsRR w'.Θ a.2 b.2) bs bs' ∧ CactusInvT w' bs' W' ps' ls' μ := by
  obtain ⟨hC, -, hA, -, hI⟩ := h
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
    by rw [e₂]; exact Apart.rr hOs hA, hR, hI'⟩

/-- **The scheduler moves a part between branches**: `σ` leaves the first branch for the second,
with the records `Oσ` it owns, at locations apart from those the first keeps (`hσ`); the world,
the records proper and the memory are unchanged. -/
theorem cactusT_move {w : TWd} {ρ₁ ρ₂ σ ρ₁' ρ₂' : TRes w.K} {O₁ O₂ Oσ : List (FrameRecT w.K)}
    {rest : List (TBranch w.K)} {W : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} {μ : Heap} (h₁ : ResUT.CompS ρ₁' σ ρ₁) (h₂ : ResUT.CompS ρ₂ σ ρ₂')
    (hσ : ∀ p ∈ O₁, ∀ q ∈ Oσ, p.le ≠ q.le)
    (hI : CactusInvT w ((ρ₁, Oσ ++ O₁) :: (ρ₂, O₂) :: rest) W ps ls μ) :
    CactusInvT w ((ρ₁', O₁) :: (ρ₂', O₂ ++ Oσ) :: rest) W ps ls μ := by
  obtain ⟨hC, hps, hA, hR, hI'⟩ := hI
  refine ⟨?_, fun p => ?_, ?_, hR, hI'⟩
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

/-! ### Adequacy -/

/-- `⟦∅⟧` is the empty memory. -/
theorem lower_emptyT {K : WCactus} :
    ResUT.Lower (PMap.empty : TRes K) (fun _ => none) :=
  ⟨PMap.empty, ⟨PMap.empty, PMap.empty, exW_empty, agW_empty, G.comp_empty_right _⟩,
    fun _ => by simp⟩

/-- The empty world at any tree and the empty store typing. -/
theorem winv_empty (P : ParentFn) :
    WInv ⟨P, fun _ => none⟩ (PMap.empty : TRes (WCactus.ofParent P)) (fun _ => none) :=
  ⟨fun _ _ e => by simp at e, lower_emptyT⟩

theorem recInv_empty (P : ParentFn) :
    RecInv ⟨P, fun _ => none⟩ (PMap.empty : TRes (WCactus.ofParent P)) [] [] :=
  ⟨⟨tmplT _ (fun _ => none), .empty⟩, fun _ hx => by simp at hx⟩

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
    (hall : ∀ n, cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Q (fun _ ρf => ρf = PMap.empty) n
      ⟨P, fun _ => none⟩ [] [] P₀ (PMap.empty : TRes (WCactus.ofParent P))) :
    BoCa.Fig16.LogRel.Core.DtorUnwind.LoopAwait.OrDiverges (ℍ := ℍ) P₀ := by
  intro μ e hs
  obtain ⟨j, hrun⟩ := stepsN_of_steps hs
  have hI₀ : CactusInvT ⟨P, fun _ => none⟩ [(PMap.empty, [])] PMap.empty [] []
      (fun _ => none) :=
    ⟨.cons .nil (ResUT.compS_empty_right _), fun p => by simp,
      List.pairwise_singleton _ _, recInv_empty P, winv_empty P⟩
  have hend : Final (ℍ := ℍ) μ e → ∃ v : Val, e = v.1 ∧ μ = fun _ => none := by
    intro hfin
    have h := hall (j + 1)
    rw [cerwpT_eq] at h
    obtain ⟨w', ρ', W', O', ps', ls', rest', -, hrest, ⟨hC, -, -, -, hI'⟩, hq⟩ :=
      cactusT_step h hI₀ (fun ρf hr => by cases hr; rfl) fd_empty (by omega) hrun hfin
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

end BoCa.Fig16.Tree.Wp

end
