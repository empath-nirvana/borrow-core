import DtorUnwind.TreeWp.StepCopy
import DtorUnwind.TreeWp.Ops

/-!
# Spike: a scheduler's resume at `cerwpT`, the join condition from the cactus invariant

The question (#781, scope §5, "riskiest step"): at a resume, `fdAt` asks the resumer's frame for
the entry's `fd` at the resumed run's records. For a join that is `FdEsc` against every other
branch, which `fdEsc_at_join` reads off `CactusInvT`'s points. `twp` knows no points. Can the
scheduler carry the invariant over the branches it stores, so that the resume meets `cerwpT`'s
obligations, with `twp`, `EndT` and `contShareT` as they are?

The shape: the scheduler's run holds a stored share `ρₖ` of branch 1 (owning records `O₁`) and
the state `ρ₂` of branch 2 (owning `O₂`), and resumes branch 1 at an answer `a`, with `ρ₂` framed
beside the resumed run. The outer frame is empty (the top-level scheduler holds no lend).

* **The points cannot cross `twp`'s extension quantifier** (`not_joinPtKeptT`). `twp` starts a run
  at every extension of its world, and a graft is one (`TWd.graft_ext`): it puts a sibling's point
  inside `α`. So the join condition in point form (`JoinPtT`) is not a fact a stored state can
  carry to the world the resumed run starts at.
* **The join condition in location form crosses it** (`fdAt_of_joinReady`). `FdEsc` is about
  locations: the state's flattening holds nothing at the lent location or the escrow's exclusive
  part. Re-reading keeps it: `fdEsc_of_updX` (`TreeWp/StepKeep.lean`) at `UpdX.of_rr`, read at the
  invariants `twp` supplies at the start world.
* **The frame rule reading the start world** (`twp_frame_w`): `twp_frame`, with the frame
  obligation also given the start world's invariants (`RecInv`, `WInv`, the split). It is proved
  from `twp`'s definition as `twp_frame` is.
* **The resume** (`sched_resume`): `contShareT_resume_rr`, `cerwpT_eq`, `twp_frame_w`,
  `fdAt_of_joinReady`.
* **Where `FdEsc` comes from**: at a configuration, from the points (`joinReady_of_cactus`,
  through `fdEsc_at_join`); across another branch's run, opening or ending lends, from `EndT`
  (`stepKeepsFdEsc`; `joinReady_after_run`).
* **Store, run, resume** (`sched_store_run_resume`): the three at one configuration.
* **The stored branch's own frame condition** must admit the state beside it (`hFy`). At
  `emptyFrameT` it admits only an empty state (`hFy_emptyFrame`).

No definition is changed.
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
open BoCa.BoLo (Heap Kont)

/-! ### The points along an extension -/

/-- The join condition in point form, kept along every extension of the world. -/
def JoinPtKeptT : Prop :=
  ∀ (w w' : TWd) (ρ : TRes w.K) (ns : List Life) (α : Life), w.Ext w' ρ →
    JoinPtT (K := w.K) ns α → JoinPtT (K := w'.K) ns α

/-- The world of `Tree/Graft.lean`'s round-7 interleaving: `1` and `2` siblings under `⊤`. -/
def wSib : TWd := ⟨beforeP, fun _ => none, tmplT _ (fun _ => none)⟩

theorem wSib_not_anc : ¬ wSib.P.Anc 2 1 := fun h =>
  beforeEx_siblings.1 h

/-- **A graft puts a sibling's point inside `α`**: at `wSib`, the point `1` is not inside
`α = 2`; at the graft of `1` under `2`, an extension of `wSib` carrying every resource, it is. -/
theorem not_joinPtKeptT : ¬ JoinPtKeptT := by
  intro h
  have hc : wSib.P.Anc 2 (wSib.P.par 1) := wSib.P.anc_zero 2
  have hE := wSib.graft_ext (r := 1) (t := 2) (by decide) wSib_not_anc hc
    (tmplT _ (fun _ => none)) PMap.empty
  have hJ : JoinPtT (K := wSib.K) [OrderDual.toDual 1] (OrderDual.toDual 2) := by
    intro n hn
    rw [List.mem_singleton] at hn
    subst hn
    exact beforeEx_siblings.2
  exact h _ _ _ _ _ hE hJ _ List.mem_cons_self
    (wSib.graft_lt (r := 1) (t := 2) (by decide) wSib_not_anc (by decide) _).1

/-! ### The frame rule, reading the start world -/

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

/-! ### The join's `fd`, and the resumer's frame -/

/-- **The join's guarantee**: the frame holds nothing at the lent location or the escrow's
exclusive part of any record the resumed run owns. -/
def fdJoinT : Val → (w : TWd) → List (FrameRecT w.K) → TRes w.K → Prop :=
  fun _ _ O ρf => ∀ p ∈ O, FdEsc p.le p.R ρf

/-- The frame condition of the top-level scheduler: nothing outside it. -/
def emptyFrameT : TFrame := fun _ ρf => ρf = PMap.empty

/-- **The resumer's frame meets `fdAt` at every world the resumed run may start at.** The state
`ρ₂` framed beside the resumed run holds nothing of the lends of the records `O₁` it owns
(`hJ`, at the resume world `w`), the escrows are valid (`hesc`) and so is `ρ₂` (`hv₂`); the
stored continuation's own frame condition holds of the state re-read (`hFy`). At each start world
`w₀` the state is a re-reading of `ρ₂` and the records the re-readings of `O₁`: `fdEsc_of_updX`
at `UpdX.of_rr` carries `hJ` there, read at `w₀`'s invariants. -/
theorem fdAt_of_joinReady {en : OpEntT} {v : Val} {F : TFrame} {w : TWd}
    {O₁ O₂ : List (FrameRecT w.K)} {ρ₂ : TRes w.K}
    (hen : ∀ v w O ρf, fdJoinT v w O ρf → en.fd v w O ρf)
    (hFy : ∀ (w₀ : TWd) (ρ₂₀ : TRes w₀.K), w.Ext w₀ ρ₂ → RRw (w := w) (w' := w₀) ρ₂ ρ₂₀ →
      F w₀ ρ₂₀)
    (hv₂ : ResUT.Valid ρ₂) (hesc : ∀ p ∈ O₁, ResUT.Valid p.R)
    (hJ : ∀ p ∈ O₁, FdEsc p.le p.R ρ₂) :
    ∀ (w₀ : TWd) (ρf ρ₁₀ ρ₂₀ y fρ : TRes w₀.K) (O₁₀ O₂₀ ps psF : List (FrameRecT w₀.K))
      (ls₀ : List (SRecT w₀.K)) (μ : Heap), w.Ext w₀ ρ₂ → RRw (w := w) (w' := w₀) ρ₂ ρ₂₀ →
      RecsRR w₀.Θ O₁ O₁₀ → RecsRR w₀.Θ O₂ O₂₀ → emptyFrameT w₀ ρf → ResUT.CompS ρf ρ₂₀ y →
      ResUT.CompS y ρ₁₀ fρ → SplitT ps (O₁₀ ++ O₂₀) psF →
      (∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le) → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ →
      fdAt en v F O₁ w₀ y := by
  intro w₀ ρf ρ₁₀ ρ₂₀ y fρ O₁₀ O₂₀ ps psF ls₀ μ hE h₂₀ hO₁ hO₂ hFρ hy hyf hS hapart hR _
  cases hFρ
  obtain rfl : y = ρ₂₀ :=
    ResUT.CompS.functional hy (ResUT.CompS.comm (ResUT.compS_empty_right _))
  refine ⟨hFy w₀ y hE h₂₀, fun O'' hO'' => hen _ _ _ _ fun p'' hp'' => ?_⟩
  obtain rfl := RecsRR.func hO₁ hO''
  obtain ⟨p, hp, hpp⟩ := forall₂_mem_right hO₁ hp''
  have hS' : SplitT ps O₂₀ (O₁₀ ++ psF) := by
    refine ⟨fun q => ?_, fun q hq r hr => ?_⟩
    · rw [hS.1 q, List.mem_append, List.mem_append]; tauto
    · rcases List.mem_append.mp hr with h | h
      · exact fun e => hapart r h q hq e.symm
      · exact hS.2 q (List.mem_append_right _ hq) r h
  have hu : UpdX (sem w₀.Θ) (recMask O₂) (recMask O₂₀) ρ₂ y :=
    (UpdX.of_rr hE.1 (recMask O₂) hv₂ h₂₀).congr (fun _ => Iff.rfl)
      (fun l => (recMask_rr hO₂ l).symm)
  exact fdEsc_of_updX hE.1 (hesc p hp) (hJ p hp) hR.1 (ResUT.CompS.comm hyf) hS'
    (List.mem_append_left _ hp'') hpp hu

/-- **Under the empty frame condition, the stored branch's `F` admits no state.** If the stored
continuation was captured at `F = emptyFrameT` (as `MultiBranchAdequacyT`'s task is), then
`fdAt_of_joinReady`'s `hFy` holds only of an empty state: the scheduler can then resume a branch
only while it holds nothing else beside it. -/
theorem hFy_emptyFrame {w : TWd} {ρ₂ : TRes w.K} (hcov : CovR (sem w.Θ) w.K ρ₂)
    (hFy : ∀ (w₀ : TWd) (ρ₂₀ : TRes w₀.K), w.Ext w₀ ρ₂ → RRw (w := w) (w' := w₀) ρ₂ ρ₂₀ →
      emptyFrameT w₀ ρ₂₀) : ρ₂ = PMap.empty :=
  hFy w ρ₂ (TWd.Ext.refl _ _) (RR.refl hcov)

/-! ### The resume -/

/-- **The scheduler resumes a stored branch beside the state it holds.** A share `ρₛ` stored at
a stop at `wₛ` (a non-abortive operation the table allows: `contShareT` at `cerwpTC`), re-read at
the resume world `w` (any extension: the tree grew while other branches ran), is resumed at an
answer `a` whose resource the entry accepts; the state `ρ₂` of the other stored branch, owning
`O₂` and in `R`, is framed beside it. Under the empty outer frame the whole is a `twp` run whose
end is the resumed branch's `cerwpT` end beside `R`. The join condition `hJ` is the state's, in
location form, at `w`. -/
theorem sched_resume {T : OpTabT} {Q : TPostV} {en : OpEntT} {F : TFrame} {k k' : Nat}
    {wₛ w : TWd} {lsₛ : List (SRecT wₛ.K)} {Oₛ : List (FrameRecT wₛ.K)} {ρₛ : TRes wₛ.K}
    {ls : List (SRecT w.K)} {O₁ O₂ : List (FrameRecT w.K)} {K : Kont} {v a : Val}
    {ρk σ σ' ρ₂ ρ : TRes w.K} {R : TRProp}
    (hsh : contShareT en F k wₛ lsₛ Oₛ K v (cerwpTC (ℍ := ℍ) (opTableT T) Q k) ρₛ)
    (hE : wₛ.Ext w ρₛ) (hr : RRw (w := wₛ) (w' := w) ρₛ ρk) (hl : SRecsRR w.Θ lsₛ ls)
    (hO : RecsRR w.Θ Oₛ O₁) (hk : k' < k) (hB : en.PBv v k' w ls a σ)
    (hcσ : ResUT.CompS ρk σ σ') (hcρ : ResUT.CompS σ' ρ₂ ρ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hapart : ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) (hRm : R.Mono) (hR₂ : R w O₂ ρ₂)
    (hen : ∀ v w O ρf, fdJoinT v w O ρf → en.fd v w O ρf)
    (hFy : ∀ (w₀ : TWd) (ρ₂₀ : TRes w₀.K), w.Ext w₀ ρ₂ → RRw (w := w) (w' := w₀) ρ₂ ρ₂₀ →
      F w₀ ρ₂₀)
    (hv₂ : ResUT.Valid ρ₂) (hesc : ∀ p ∈ O₁, ResUT.Valid p.R)
    (hJ : ∀ p ∈ O₁, FdEsc p.le p.R ρ₂) :
    twp (ℍ := ℍ) emptyFrameT
      ((cerwpPostT (opTableT T) Q (cerwpTC (ℍ := ℍ) (opTableT T) Q k') (fdAt en v F O₁)).sep R)
      k' w ls (O₁ ++ O₂) (K.plug (.val a)) ρ := by
  have h := contShareT_resume_rr hsh hE hr hl hO hk hB hcσ
  simp only [cerwpTC, hk, if_true] at h
  rw [cerwpT_eq] at h
  exact twp_frame_w hRm hapart hcρ hcov (fdAt_of_joinReady hen hFy hv₂ hesc hJ) h hR₂

/-! ### Where the join condition comes from -/

/-- **At a configuration, from the points.** In the cactus invariant, the branch to be resumed
owns `O`; each of its records is framed at an `α` no other branch's point is inside (`JoinPtT`).
Then any part `ρ₂` of the other branches holds nothing of those lends, is valid, and the escrows
are valid: `sched_resume`'s `hJ`, `hv₂`, `hesc`. -/
theorem joinReady_of_cactus {w : TWd} {ρ : TRes w.K} {O : List (FrameRecT w.K)}
    {others : List (TBranch w.K)} {n₀ : Life} {ns : List Life} {W : TRes w.K}
    {ps : List (FrameRecT w.K)} {ls : List (SRecT w.K)} {μ : Heap}
    (hC : CactusInvT w ((ρ, O) :: others) (n₀ :: ns) W ps ls μ)
    (hpt : ∀ p ∈ O, ∃ α, FrameLifeT w.K W p α ∧ JoinPtT (K := w.K) ns α)
    {ρf ρ₂ ρx : TRes w.K} (hf : CompAllT (others.map Prod.fst) ρf)
    (h₂ : ResUT.CompS ρ₂ ρx ρf) :
    ResUT.Valid ρ₂ ∧ (∀ p ∈ O, ResUT.Valid p.R) ∧ ∀ p ∈ O, FdEsc p.le p.R ρ₂ := by
  obtain ⟨ρf', hr', -, hcW, -⟩ := cactusT_frame hC
  have hW := hC.2.2.2.2.1
  obtain rfl := compAllT_functional hf hr'
  have hvf : ResUT.Valid ρf := covf_valid hcW hW
  have hvf' := ResUT.Valid.split h₂ hvf
  refine ⟨hvf'.1, fun p hp => TWNT.esc_valid hC.2.2.2.1.1 p ((hC.2.1 p).mpr (by simp [hp])),
    fun p hp => ?_⟩
  obtain ⟨α, hFL, hJ⟩ := hpt p hp
  exact fdEsc_iff_noneAt.mpr (NoneAt.of_compS_left h₂ hvf
    (fdEsc_iff_noneAt.mp (fdEsc_at_join hC hp hFL hJ hf)))

/-- **Across another branch's run, from `EndT`.** Branch 2 runs at `twp` with branch 1's share
`ρₛ` and records `Oₛ` as its frame, holding nothing of their lends (`h₀`). At every end `EndT`
admits, opening or ending lends along the way, the end resource `ρ'` holds nothing of the re-read
records' lends, is valid, and their escrows are valid; the share and the records are re-read to
the end world (`hE`, `hr`, `hO`): every premise of `sched_resume` about branch 1 and the state. -/
theorem joinReady_after_run {F : TFrame} {Q : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O₂ ps Oₛ : List (FrameRecT w.K)} {e : Expr} {ρ₂ ρₛ fρ : TRes w.K}
    {μ : Heap} (h : twp (ℍ := ℍ) F Q n w ls O₂ e ρ₂) (hF : F w ρₛ) (hf : ResUT.Hash ρₛ ρ₂)
    (hc : ResUT.CompS ρₛ ρ₂ fρ) (hS : SplitT ps O₂ Oₛ) (hR : RecInv w fρ ps ls)
    (hI : WInv w fρ μ) (hfd : FinDom μ) (h₀ : ∀ p ∈ Oₛ, FdEsc p.le p.R ρ₂)
    {j : Nat} {μ' : Heap} {e' : Expr} (hj : j < n) (hrun : StepsN (ℍ := ℍ) j μ e μ' e')
    (hfin : Final (ℍ := ℍ) μ' e') :
    ∃ (w' : TWd) (ρk ρ' : TRes w'.K) (O₁ O' : List (FrameRecT w'.K)) (ls' : List (SRecT w'.K)),
      w.Ext w' ρₛ ∧ RRw (w := w) (w' := w') ρₛ ρk ∧ RecsRR w'.Θ Oₛ O₁ ∧
      Q (n - j) w' ls' O' e' ρ' ∧ (∀ p ∈ O₁, ∀ q ∈ O', p.le ≠ q.le) ∧
      ResUT.Valid ρ' ∧ (∀ p ∈ O₁, ResUT.Valid p.R) ∧ ∀ p ∈ O₁, FdEsc p.le p.R ρ' := by
  have hcov : CovR (sem w.Θ) w.K ρ₂ := cov_of_comp hc hI
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    h w ρ₂ ρₛ fρ ls O₂ ps Oₛ μ (TWd.Ext.refl _ _) (RR.refl hcov) (SRecsRR.refl hR.cov_ls)
      (RecsRR.refl fun r hr' => hR.cov_ps r (hS.left r hr')) hF hf hc hS hR hI hfd j μ' e' hj
      hrun hfin
  refine ⟨w', ρf', ρ', psF', O', ls', g₀, g₁, g₂, g₈, fun p hp q hq e => g₅.2 q hq p hp e.symm,
    cov_valid g₄ g₇,
    fun p hp => TWNT.esc_valid g₆.1 p (g₅.right p hp), fun p' hp' => ?_⟩
  obtain ⟨p, hp, hpp⟩ := forall₂_mem_right g₂ hp'
  exact stepKeepsFdEsc (ℍ := ℍ) w F Q n ls O₂ ps Oₛ e ρ₂ ρₛ fρ μ p h hF hf
    hc hS hR hI hfd hp (h₀ p hp) j μ' e' hj hrun hfin w' ρf' ρ' fρ' psF' ps' O' ls' g₀ g₁ g₂ g₃
    g₄ g₅ g₆ g₇ g₈ g₉ g₁₀ p' hp' hpp

/-! ### Store, run, resume -/

/-- **Store, another branch's run, resume.** At a configuration of the cactus invariant, branch 1
is stored: its share `ρₛ` (a stop's `contShareT`) and records `Oₛ`, at its point; branch 2, at
a point inside no frame of branch 1's records, holds `ρ₂` and `O₂`. Branch 2 runs at `twp` with
the stored share as its frame, opening and ending lends as it goes. At every end `EndT` admits,
branch 1 is resumable beside branch 2's end resource `ρ′`: under the empty outer frame, at every
answer the entry accepts, the resume is a `twp` run at the resumed branch's `cerwpT` end beside
the state's predicate. What is left to the caller is what the resume is about other than the join:
the resume list (`hl`), the answer, the cover of the composite, the state's predicate, the entry's
`fd`, and the stored branch's own frame condition `F` at the state. -/
theorem sched_store_run_resume {T : OpTabT} {Q : TPostV} {en : OpEntT} {F F₂ : TFrame}
    {Q₂ : TPost} {k n : Nat} {w : TWd} {lsₛ ls : List (SRecT w.K)}
    {Oₛ O₂ ps : List (FrameRecT w.K)} {K : Kont} {v : Val} {ρₛ ρ₂ W : TRes w.K} {μ : Heap}
    {n₁ n₂ : Life} {e : Expr}
    (hC : CactusInvT w [(ρₛ, Oₛ), (ρ₂, O₂)] [n₁, n₂] W ps ls μ)
    (hpt : ∀ p ∈ Oₛ, ∃ α, FrameLifeT w.K W p α ∧ JoinPtT (K := w.K) [n₂] α)
    (hsh : contShareT en F k w lsₛ Oₛ K v (cerwpTC (ℍ := ℍ) (opTableT T) Q k) ρₛ)
    (h : twp (ℍ := ℍ) F₂ Q₂ n w ls O₂ e ρ₂) (hF₂ : F₂ w ρₛ) (hfd : FinDom μ)
    {j : Nat} {μ' : Heap} {e' : Expr} (hj : j < n) (hrun : StepsN (ℍ := ℍ) j μ e μ' e')
    (hfin : Final (ℍ := ℍ) μ' e') :
    ∃ (w' : TWd) (O₁ O' : List (FrameRecT w'.K)) (ls' : List (SRecT w'.K)) (ρk ρ' : TRes w'.K),
      RRw (w := w) (w' := w') ρₛ ρk ∧ Q₂ (n - j) w' ls' O' e' ρ' ∧
      ∀ (ls'' : List (SRecT w'.K)) (k' : Nat) (a : Val) (σ σ' ρ : TRes w'.K) (R : TRProp),
        SRecsRR w'.Θ lsₛ ls'' → k' < k → en.PBv v k' w' ls'' a σ →
        ResUT.CompS ρk σ σ' →
        ResUT.CompS σ' ρ' ρ → CovR (sem w'.Θ) w'.K ρ → R.Mono → R w' O' ρ' →
        (∀ v w O ρf, fdJoinT v w O ρf → en.fd v w O ρf) →
        (∀ (w₀ : TWd) (ρ₂₀ : TRes w₀.K), w'.Ext w₀ ρ' → RRw (w := w') (w' := w₀) ρ' ρ₂₀ →
          F w₀ ρ₂₀) →
        twp (ℍ := ℍ) emptyFrameT
          ((cerwpPostT (opTableT T) Q (cerwpTC (ℍ := ℍ) (opTableT T) Q k')
            (fdAt en v F O₁)).sep R)
          k' w' ls'' (O₁ ++ O') (K.plug (.val a)) ρ := by
  obtain ⟨hCA, hps, hA, hR, hI, -⟩ := id hC
  -- the configuration: `W = ρₛ ● ρ₂`, the records proper split between the two branches
  have hcW : ResUT.CompS ρₛ ρ₂ W := by
    simp only [List.map_cons, List.map_nil] at hCA
    cases hCA with
    | cons h₁ hc =>
    cases h₁ with
    | cons h₀ hc₀ =>
    cases h₀
    obtain rfl := ResUT.CompS.functional hc₀ (ResUT.compS_empty_right _)
    exact hc
  have hS : SplitT ps O₂ Oₛ := by
    refine ⟨fun p => ?_, fun p hp q hq => ?_⟩
    · rw [hps p]; simp; tauto
    · simp only [List.map_cons, List.map_nil] at hA
      exact fun e => (List.pairwise_cons.mp hA).1 O₂ List.mem_cons_self q hq p hp e.symm
  have h1 : CompAllT ([(ρ₂, O₂)].map Prod.fst) ρ₂ := .cons .nil (ResUT.compS_empty_right _)
  obtain ⟨-, -, h₀⟩ := joinReady_of_cactus hC hpt h1 (ResUT.compS_empty_right _)
  obtain ⟨w', ρk, ρ', O₁, O', ls', hE, hr, hO, hQ, hap, hv', hesc, hJ⟩ :=
    joinReady_after_run h hF₂ (hash_of_inv hcW hI) hcW hS hR hI hfd h₀ hj hrun hfin
  refine ⟨w', O₁, O', ls', ρk, ρ', hr, hQ, fun ls'' k' a σ σ' ρ R hl hk hB hcσ hcρ hcov hRm hR₂ hen
    hFy => ?_⟩
  exact sched_resume hsh hE hr hl hO hk hB hcσ hcρ hcov hap hRm hR₂ hen hFy hv' hesc hJ

end BoCa.Fig16.Tree.Wp

end
