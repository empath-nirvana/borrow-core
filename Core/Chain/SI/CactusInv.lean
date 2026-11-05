import Core.Chain.SI.CaptureScope

/-!
# The scheduler-wide invariant, stated once

A scheduler holds a running computation and stored ones (continuations in cells, a spawned
closure not yet run). Each is a **branch**: a resource and the frame records it owns. The
invariant over all of them:

* the world is the composition of the branches' resources (nothing is anybody else's garbage);
* the world is a tagged typed world whose records proper are exactly the branches' owned
  records, each owned by one branch;
* the memory is the world's lowering.

That is `CactusInv`. A borrow of a lent location may sit in any branch; the lend's record is owned
by the branch whose continuation holds the lend's end. One more condition is read at one point:
a branch resumed from a join asks that no *other* branch's flattening hold the joined location
(`JoinReady`); the scheduler establishes it by having finished or cancelled every branch that
held a borrow of it and handed their borrows to the joiner.

`crwpG`'s quantifier is this invariant cut in two: the running branch, and the composition of the
others as its frame (`cactus_frame`). `cactus_step`: a run at `crwpG` keeps the invariant, the
other branches untouched. Capture (a lend left open at a stop, `cerwp_scopeK`'s stops), graft
(resuming a stored branch: `cerwp_resumeStored`, under `cerwp_frameE`) and unwind (cancelling a
stored branch: `cerwp_cancelStored`) are runs at `crwpG`, so they are instances. Moving a
resource or a record between branches (the scheduler storing a continuation it received, handing
a borrow to a joiner) is `cactus_move`.

**Where it is sequential.** The frame of a run is fixed for the run (`EndC`'s `ρ_f`), which is
the single-scheduler reading: no other branch runs during a segment. The invariant itself is per
branch and needs nothing of the order: ownership of resources and records is exclusive, borrows
of a lent location are ordinary duplicable `imm` cells, and the join's condition is about the
other branches' holdings at the moment of the resume. A concurrent reading would keep
`CactusInv` as the shared invariant and replace the fixed frame by its framing in a concurrent
separation logic; the join would be the synchronisation after which the joined branches'
resources are the joiner's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)

/-- A branch of the scheduler's cactus: its resource and the frame records it owns. -/
abbrev Branch : Type := WRes × List FrameRec

/-- The composition of a list of resources. -/
inductive CompAll : List WRes → WRes → Prop
  | nil : CompAll [] PMap.empty
  | cons {ρ W W' : WRes} {ρs : List WRes} : CompAll ρs W' → ResU.CompS ρ W' W →
      CompAll (ρ :: ρs) W

/-- The records the branches own. -/
def ownedBy (bs : List Branch) : List FrameRec := (bs.map Prod.snd).flatten

/-- **The scheduler-wide invariant.** -/
def CactusInv (bs : List Branch) (ls : List SRec) (W : WRes) (ps : List FrameRec) (μ : Heap) :
    Prop :=
  CompAll (bs.map Prod.fst) W ∧ (∀ p, p ∈ ps ↔ p ∈ ownedBy bs) ∧
  (bs.map Prod.snd).Pairwise (fun O O' => ∀ p ∈ O, p ∉ O') ∧
  TWNC W ps (rsOf ls) ∧ Tagged W ps ls ∧ ResU.Lower W μ

/-- **What a join's resume asks**: the other branches' composition holds nothing at the joined
location, at any depth. -/
def JoinReady (others : List Branch) (m : Loc) : Prop :=
  ∀ W τ, CompAll (others.map Prod.fst) W → ResU.Flat W τ → τ.get m = none

theorem compAll_functional {ρs : List WRes} {W W' : WRes} (h : CompAll ρs W)
    (h' : CompAll ρs W') : W = W' := by
  induction h generalizing W' with
  | nil => cases h'; rfl
  | cons hr hc ih =>
      cases h' with
      | cons hr' hc' =>
          cases ih hr'
          exact ResU.CompS.functional hc hc'

/-- **The running branch and its frame**: the invariant at `(ρ, O) :: rest` is `crwpG`'s
quantifier at `ρ`, `O`, with the frame the composition of `rest` and the records `rest` owns. -/
theorem cactus_frame {ρ : WRes} {O : List FrameRec} {rest : List Branch} {ls : List SRec}
    {W : WRes} {ps : List FrameRec} {μ : Heap}
    (h : CactusInv ((ρ, O) :: rest) ls W ps μ) :
    ∃ ρf, CompAll (rest.map Prod.fst) ρf ∧ ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ W ∧
      Split ps O (ownedBy rest) ∧ TWNC W ps (rsOf ls) ∧ Tagged W ps ls ∧ ResU.Lower W μ := by
  obtain ⟨hC, hps, hpw, hT, htg, hl⟩ := h
  cases hC with
  | cons hr hc =>
  rename_i ρf
  have hv : ResU.Valid W := by obtain ⟨σ, hσ, -⟩ := hl; exact ⟨σ, hσ⟩
  refine ⟨ρf, hr, ⟨ResU.CompatS.symm hc.1, W, ResU.CompS.comm hc, hv⟩, ResU.CompS.comm hc,
    ⟨fun p => ?_, fun p hp hpF => ?_⟩, hT, htg, hl⟩
  · rw [hps p]
    simp [ownedBy, List.mem_flatten]
  · obtain ⟨O', hO', hpO'⟩ := List.mem_flatten.mp hpF
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hO'
    exact (List.pairwise_cons.mp hpw).1 _ (List.mem_map.mpr ⟨b, hb, rfl⟩) p hp hpO'

/-- **A run keeps the invariant**: the running branch, at `crwpG` under the frame of the other
branches, ends at a configuration where the invariant holds with its new resource and records and
the others untouched. -/
theorem cactus_step {F : WRes → Prop} {Q : PostC} {n : Nat} {ls : List SRec}
    {O : List FrameRec} {e : Expr} {ρ : WRes} {rest : List Branch} {W : WRes}
    {ps : List FrameRec} {μ : Heap}
    (h : crwpG (ℍ := ℍ) F Q n ls O e ρ) (hI : CactusInv ((ρ, O) :: rest) ls W ps μ)
    (hF : ∀ ρf, CompAll (rest.map Prod.fst) ρf → F ρf) (hfd : FinDom μ)
    {j : Nat} {μ' : Heap} {e' : Expr} (hj : j < n) (hrun : StepsN (ℍ := ℍ) j μ e μ' e')
    (hfin : Final (ℍ := ℍ) μ' e') :
    ∃ ρ' O' ls' W' ps', CactusInv ((ρ', O') :: rest) ls' W' ps' μ' ∧ Q (n - j) ls' O' e' ρ' := by
  obtain ⟨ρf, hr, hf, hc, hS, hT, htg, hl⟩ := cactus_frame hI
  obtain ⟨ρ', fρ', ps', O', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ :=
    h ρf W ps (ownedBy rest) μ (hF ρf hr) hf hc hS hT htg hl hfd j μ' e' hj hrun hfin
  refine ⟨ρ', O', ls', fρ', ps', ⟨CompAll.cons hr (ResU.CompS.comm h₂), fun p => ?_, ?_, h₅, h₆,
    h₃⟩, h₇⟩
  · rw [h₄.1 p]
    simp [ownedBy, List.mem_flatten]
  · refine List.pairwise_cons.mpr ⟨fun O'' hO'' p hp hpO'' => ?_, ?_⟩
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hO''
      exact h₄.2 p hp (List.mem_flatten.mpr ⟨b.2, List.mem_map.mpr ⟨b, hb, rfl⟩, hpO''⟩)
    · exact (List.pairwise_cons.mp hI.2.2.1).2

/-- **The scheduler moves a part between branches**: a resource `σ` and records `O₂` leave one
branch for another; the world, the records proper and their ownership are unchanged. -/
theorem cactus_move {ρ₁ ρ₂ σ ρ₁' ρ₂' : WRes} {O₁ O₂ O₂' : List FrameRec} {rest : List Branch}
    {ls : List SRec} {W : WRes} {ps : List FrameRec} {μ : Heap}
    (h₁ : ResU.CompS ρ₁' σ ρ₁) (h₂ : ResU.CompS ρ₂ σ ρ₂')
    (hO : ∀ p, p ∈ O₂' ↔ p ∈ O₂ ∨ p ∈ O₁)
    (hI : CactusInv ((ρ₁, O₁) :: (ρ₂, O₂) :: rest) ls W ps μ) :
    CactusInv ((ρ₁', []) :: (ρ₂', O₂') :: rest) ls W ps μ := by
  obtain ⟨hC, hps, hpw, hT, htg, hl⟩ := hI
  cases hC with
  | cons hr hc =>
  cases hr with
  | cons hr' hc' =>
  rename_i W₁ W₂
  -- `W = ρ₁ ● (ρ₂ ● W₂) = ρ₁' ● (ρ₂' ● W₂)`
  obtain ⟨x, hx, hW⟩ := compS_reassoc h₁ hc
  obtain ⟨y, hy, hyx⟩ := (ResU.CompS.assoc σ ρ₂ W₂ x).mp ⟨W₁, hc', hx⟩
  obtain rfl := ResU.CompS.functional hy (ResU.CompS.comm h₂)
  have hpw' := List.pairwise_cons.mp hpw
  have hpw'' := List.pairwise_cons.mp hpw'.2
  refine ⟨CompAll.cons (CompAll.cons hr' hyx) hW, fun p => ?_, ?_, hT, htg, hl⟩
  · rw [hps p]
    simp only [ownedBy, List.map_cons, List.flatten_cons, List.mem_append, List.nil_append]
    rw [hO p]; tauto
  · refine List.pairwise_cons.mpr ⟨fun _ _ p hp => by simp at hp,
      List.pairwise_cons.mpr ⟨fun O'' hO'' p hp hpO'' => ?_, hpw''.2⟩⟩
    rcases (hO p).mp hp with h | h
    · exact hpw''.1 O'' hO'' p h hpO''
    · exact hpw'.1 O'' (List.mem_cons_of_mem _ hO'') p h hpO''

/-- **`JoinReady` is the join's frame condition** at the frame the other branches make. -/
theorem joinReady_fd {others : List Branch} {m : Loc} {ρf : WRes}
    (hJ : JoinReady others m) (hr : CompAll (others.map Prod.fst) ρf) :
    joinFd (Val.loc m) ρf :=
  ⟨m, rfl, fun τ hτ => hJ ρf τ hr hτ⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
