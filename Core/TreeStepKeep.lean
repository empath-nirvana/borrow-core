import Core.TreeCactus
import Support.Model.Tree.World.StepKeep

/-!
# A step keeps every other branch's open lend: `stepKeepsFdEsc`  `[spec §62]`

A join reaches its condition through `fdEsc_at_join` (`Core/TreeCactus.lean`): the joiner's record
is framed at `α`, and every other branch sits at a point not inside `α` (`JoinPtT`). The branches
that are not the joiner's descendants must keep holding nothing of `α`'s lend across their own
steps. `cactusT_step` hands the scheduler the post-configuration that `twp`'s `EndT` names, and
nothing else of the run.

**`StepKeepsFdEsc`** is that requirement at the escrow's frame condition: a branch stepping at
`twp` beside a record proper of its frame, holding nothing at the record's location or escrow
(`FdEsc`), still holds nothing there in every post-configuration `EndT` admits. It holds
(`stepKeepsFdEsc`), by `fdEsc_of_updA` (`Support/Model/Tree/World/UpdAInv.lean`): `EndT` relates
the run's start and end by row 5.27's `↭`, masked only at the run's own records.

**Without `↭` it fails** (`not_stepKeepsFdEscNoUpd`). `StepKeepsFdEscNoUpd` is the same
requirement at `EndT`'s clauses less `↭` and the frame clause. At the world of `cactusT_config`
(the record `ℓ ↦ imm({α}, loc m, m ↦ own(()))` framed at `α`), the running branch is empty, its run
is the value `()`, its frame condition is `True`, and its postcondition asks only that its resource
sit at a point. The post-configuration in which the branch holds a copy of the frame's lent cell
`ℓ ↦ imm({α}, …)` meets every one of those clauses: the world is the start's (an `imm` cell
composes with itself, `compS_self_of_imm`), so `RecInv` and `WInv` are the start's. In it the
branch fails `FdEsc` at `ℓ`, and every point its resource sits on is inside `α` (`copy_inside`), so
`JoinPtT` fails too. `↭` refuses that end (`copy_end_refused`, and along the walks
`copy_not_updA`), and no run at `twp` beside the
parent ends holding anything of its lend (`copy_run_keeps_fdEsc`).

`copy_config` states the same step at `CactusInvT`: the invariant holds before and after, the
empty branch's point is outside `α` before, and no point of the stepped branch is outside `α`
after.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)

/-- **What a join through `fdEsc_at_join` reads of a step.** A branch running `e` at `twp`,
under a frame meeting its condition, holding nothing at the location or the escrow of a record
proper `p` of the frame, holds nothing there in every post-configuration `EndT` admits (the
clauses below are `EndT`'s, at the start's world). -/
def StepKeepsFdEsc : Prop :=
  ∀ (w : TWd) (F : TFrame) (Q : TPost) (n : Nat) (ls : List (SRecT w.K))
    (O ps psF : List (FrameRecT w.K)) (e : Expr) (ρ ρf fρ : TRes w.K) (μ : Heap)
    (p : FrameRecT w.K),
    twp (ℍ := ℍ) F Q n w ls O e ρ → F w ρf → ResUT.Hash ρf ρ → ResUT.CompS ρf ρ fρ →
    SplitT ps O psF → RecInv w fρ ps ls → WInv w fρ μ → FinDom μ → p ∈ psF →
    FdEsc p.le p.R ρ →
    ∀ (j : Nat) (μ' : Heap) (e' : Expr), j < n → StepsN (ℍ := ℍ) j μ e μ' e' →
      Final (ℍ := ℍ) μ' e' →
    ∀ (w' : TWd) (ρf' ρ' fρ' : TRes w'.K) (psF' ps' O' : List (FrameRecT w'.K))
      (ls' : List (SRecT w'.K)),
      w.Ext w' ρf → RRw (w := w) (w' := w') ρf ρf' → RecsRR w'.Θ psF psF' →
      ResUT.Hash ρ' ρf' → ResUT.CompS ρf' ρ' fρ' → SplitT ps' O' psF' →
      RecInv w' fρ' ps' ls' → WInv w' fρ' μ' → Q (n - j) w' ls' O' e' ρ' →
      UpdA (sem w'.Θ) (recMask O) (recMask O') ρ ρ' fρ' →
      NoneAt (MaskDiff (recMask O) (recMask O')) ρf' →
      ∀ p' ∈ psF', RecRR w'.Θ p p' → FdEsc p'.le p'.R ρ'

/-- **`StepKeepsFdEsc`.** -/
theorem stepKeepsFdEsc : StepKeepsFdEsc (ℍ := ℍ) := by
  intro w F Q n ls O ps psF e ρ ρf fρ μ p _ _ _ _ hS hR _ _ hp h₀ _ _ _ _ _ _ w' ρf' ρ' fρ' psF'
    ps' O' ls' hE _ _ _ hc hS' hR' _ _ hu _ p' hp' hpp
  exact fdEsc_of_updA hE.1 (TWNT.esc_valid hR.1 p (hS.right p hp)) h₀ hR'.1 hc hS' hp' hpp hu

/-- `StepKeepsFdEsc` at `EndT`'s clauses less `↭` and the frame clause: the post-configuration
`crwpG` asked for. -/
def StepKeepsFdEscNoUpd : Prop :=
  ∀ (w : TWd) (F : TFrame) (Q : TPost) (n : Nat) (ls : List (SRecT w.K))
    (O ps psF : List (FrameRecT w.K)) (e : Expr) (ρ ρf fρ : TRes w.K) (μ : Heap)
    (p : FrameRecT w.K),
    twp (ℍ := ℍ) F Q n w ls O e ρ → F w ρf → ResUT.Hash ρf ρ → ResUT.CompS ρf ρ fρ →
    SplitT ps O psF → RecInv w fρ ps ls → WInv w fρ μ → FinDom μ → p ∈ psF →
    FdEsc p.le p.R ρ →
    ∀ (j : Nat) (μ' : Heap) (e' : Expr), j < n → StepsN (ℍ := ℍ) j μ e μ' e' →
      Final (ℍ := ℍ) μ' e' →
    ∀ (w' : TWd) (ρf' ρ' fρ' : TRes w'.K) (psF' ps' O' : List (FrameRecT w'.K))
      (ls' : List (SRecT w'.K)),
      w.Ext w' ρf → RRw (w := w) (w' := w') ρf ρf' → RecsRR w'.Θ psF psF' →
      ResUT.Hash ρ' ρf' → ResUT.CompS ρf' ρ' fρ' → SplitT ps' O' psF' →
      RecInv w' fρ' ps' ls' → WInv w' fρ' μ' → Q (n - j) w' ls' O' e' ρ' →
      ∀ p' ∈ psF', RecRR w'.Θ p p' → FdEsc p'.le p'.R ρ'

/-! ### An `imm` cell composes with itself -/

theorem cellCompS_self_of_imm {K : WCactus} {ψ : TCell K} (hk : ψ.kind = Kind.imm) :
    CellUT.CompatS ψ ψ ∧ CellUT.CompS ψ ψ ψ := by
  rcases CellUT.rep' ψ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b, _, v, χ, hb, P, hP, rfl⟩
  · simp [CellUT.kind, CellUT.ownOf] at hk
  · have hc : CellUT.CompatS (CellUT.immOf s v χ hs) (CellUT.immOf s v χ hs) :=
      ⟨s, s, v, χ, hs, hs, rfl, rfl⟩
    have h := CellUT.compS_spec _ _ hc
    rw [CellUT.compS_self _ hc] at h
    exact ⟨hc, h⟩
  · simp [CellUT.kind, CellUT.mutOf] at hk

/-- **A resource of `imm` cells composes with itself to itself** (`ρᵢ = ρᵢ ● ρᵢ`). -/
theorem compS_self_of_imm {K : WCactus} {ρ : TRes K}
    (hk : ∀ l ψ, ρ.get l = some ψ → ψ.kind = Kind.imm) : ResUT.CompS ρ ρ ρ := by
  refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => ?_, fun l => ?_⟩
  · rw [e₁] at e₂; cases Option.some.inj e₂
    exact (cellCompS_self_of_imm (hk l _ e₁)).1
  · cases e : ρ.get l with
    | none => rfl
    | some ψ => exact ⟨ψ, rfl, (cellCompS_self_of_imm (hk l ψ e)).2⟩

/-- A part of a world that holds only `imm` cells may be added to the world without changing it. -/
theorem compS_absorb {K : WCactus} {a b W : TRes K} (hab : ResUT.CompS a b W)
    (hk : ∀ l ψ, a.get l = some ψ → ψ.kind = Kind.imm) : ResUT.CompS W a W := by
  obtain ⟨y, hy, hyW⟩ :=
    (ResUT.CompS.assoc a a b W).mpr ⟨a, compS_self_of_imm hk, hab⟩
  obtain rfl := ResUT.CompS.functional hy hab
  exact ResUT.CompS.comm hyW

/-! ### The configuration -/

theorem parentRes_imm : ∀ l ψ, (parentRes : TRes KC).get l = some ψ → ψ.kind = Kind.imm := by
  intro l ψ e
  obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
  exact CellUT.kind_immOf _ _ _ _

/-- The flattening of the lent cell holds `ℓ`. -/
theorem flat_parentRes_at {τ : TRes KC} (hτ : ResUT.Flat parentRes τ) : τ.get ℓC ≠ none := by
  obtain ⟨e, a, -, ha, hc⟩ := hτ
  intro hn
  have := none_of_comp_none_right hc hn
  rw [(ag_lend ℓC_ne_mC ha).1] at this
  cases this

/-- **Every point the copy sits on is inside `α`.** -/
theorem copy_inside {n : Life} (h : OnBranchResT KC n parentRes) : KC.le n αC :=
  h ℓC (lendCell αC mC) (ResUT.single_get_self _ _) (TSet.single αC) rfl αC
    (by simp [TSet.single_set])

theorem finDom_of_pmap {K : WCactus} (σ : TRes K) :
    FinDom (fun x => (σ.get x).map CellUT.erase) := by
  classical
  obtain ⟨d, hd⟩ := σ.finite
  exact ⟨d, fun l hl => hd l fun e => hl (by simp [e])⟩

/-- The empty branch's run: the value `()`, under any frame, ending where its resource sits at a
point. -/
def Qpt : TPost := fun _ w' _ _ _ ρ' => ∃ n', OnBranchResT w'.K n' ρ'

theorem twp_unit_empty (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    twp (ℍ := ℍ) (fun _ _ => True) Qpt n w ls [] (Val.unit).1 PMap.empty :=
  twp_here (fun μ => final_val μ Val.unit) fun _ ρ₀ _ _ _ hr _ _ => by
    obtain rfl := RR.of_empty hr
    exact ⟨⊤, OnBranchResT.empty ⊤⟩

/-- **`StepKeepsFdEscNoUpd` fails.** The empty branch's run of `()` beside the parent's lent cell
may end holding a copy of that cell: every clause of `crwpG`'s post-configuration holds there, and
the branch holds the lent location. -/
theorem not_stepKeepsFdEscNoUpd : ¬ StepKeepsFdEscNoUpd (ℍ := ℍ) := by
  intro hK
  obtain ⟨W, μ, hW, hI⟩ := cactusT_config
  obtain ⟨-, -, -, hR, hWI, -⟩ := hI
  have hv : ResUT.Valid W := hWI.valid
  have hfd : FinDom μ := by
    obtain ⟨σ, -, hμ⟩ := hWI.2
    rw [show μ = fun x => (σ.get x).map CellUT.erase from funext hμ]
    exact finDom_of_pmap σ
  have hWW : ResUT.CompS W PMap.empty W := ResUT.compS_empty_right _
  have hcopy : ResUT.CompS W parentRes W := compS_absorb hW parentRes_imm
  have hS : SplitT [recE (K := KC) ℓC mC] [] [recE ℓC mC] :=
    ⟨fun p => by simp, fun p hp => by cases hp⟩
  have hrec : RecsRR wC.Θ [recE (K := KC) ℓC mC] [recE ℓC mC] :=
    RecsRR.refl fun r hr => hR.cov_ps r hr
  have hpp : RecRR wC.Θ (recE (K := KC) ℓC mC) (recE (K := KC) ℓC mC) := by
    cases hrec with | cons h _ => exact h
  have hFd₀ : FdEsc (recE (K := KC) ℓC mC).le (recE (K := KC) ℓC mC).R PMap.empty :=
    fdEsc_iff_noneAt.mpr (noneAt_empty _)
  have h := hK wC (fun _ _ => True) Qpt 1 lsC [] [recE ℓC mC] [recE ℓC mC] (Val.unit).1
    PMap.empty W W μ (recE ℓC mC) (twp_unit_empty 1 wC lsC) trivial
    (ResUT.Hash.of_compS hWW hv) hWW hS hR hWI hfd (List.mem_singleton_self _)
    hFd₀ 0 μ (Val.unit).1 (by omega) (.refl _ _) (final_val μ Val.unit)
    wC W parentRes W [recE ℓC mC] [recE ℓC mC] [] lsC (TWd.Ext.refl _ _) (RR.refl hWI.1) hrec
    (ResUT.Hash.of_compS (ResUT.CompS.comm hcopy) hv) hcopy hS hR hWI
    ⟨αC, fun l ψ e t ht x hx => by
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
      change some (TSet.single αC) = some t at ht
      cases Option.some.inj ht
      simp only [TSet.single_set, Finset.mem_singleton] at hx
      subst hx; exact KC.refl _⟩
    (recE ℓC mC) (List.mem_singleton_self _) hpp
  obtain ⟨τ, hτ⟩ := (ResUT.Valid.split hcopy hv).2
  exact flat_parentRes_at hτ (h τ hτ).1

/-! ### `↭` refuses the copy -/

/-- **`↭` refuses the copy**: from the empty resource, no update masked at no records ends at a
resource whose flattening holds a borrow at the parent's lent location, at any re-reading. -/
theorem copy_not_updX {K' : WCactus} {Θ : LocTy} {ρ' : TRes K'}
    (hρ' : ∃ τ, ResUT.Flat ρ' τ ∧ ∃ ψ, τ.get ℓC = some ψ ∧ ψ.kind ≠ Kind.own) :
    ¬ UpdX (K := KC) Θ (recMask ([] : List (FrameRecT KC)))
      (recMask ([] : List (FrameRecT K'))) PMap.empty ρ' := by
  rintro ⟨σ, σ', hσ, hσ', hx⟩
  obtain ⟨τ, hτ, ψ, eψ, hk⟩ := hρ'
  obtain rfl := ResUT.Flat.functional hτ hσ'
  obtain ⟨-, ψ₀, e₀, -⟩ := (hx ℓC).2 ψ eψ hk (by simp [recMask])
  have := noneAt_empty (K := KC) (fun _ => True) σ hσ ℓC trivial
  rw [this] at e₀; cases e₀

/-- **`↭` along the walks refuses the copy too**: the start is empty, so an end borrow has no
start cell and no start ancestor, at any end world. -/
theorem copy_not_updA {K' : WCactus} {Θ : LocTy} {ρ' fρ' : TRes K'}
    (hρ' : ∃ τ, ResUT.Flat ρ' τ ∧ ∃ ψ, τ.get ℓC = some ψ ∧ ψ.kind ≠ Kind.own) :
    ¬ UpdA (K := KC) Θ (recMask ([] : List (FrameRecT KC)))
      (recMask ([] : List (FrameRecT K'))) PMap.empty ρ' fρ' := by
  rintro ⟨σ, σ', τw, hσ, hσ', -, hx⟩
  obtain ⟨τ, hτ, ψ, eψ, hk⟩ := hρ'
  obtain rfl := ResUT.Flat.functional hτ hσ'
  have hσe := noneAt_empty (K := KC) (fun _ => True) σ hσ
  obtain ⟨-, ⟨ψ₀, e₀, -⟩ | ⟨-, m, ζ, ξ, hb, -⟩⟩ := (hx ℓC).2 ψ eψ hk (by simp [recMask])
  · rw [hσe ℓC trivial] at e₀; cases e₀
  · have := hb.1; rw [hσe m trivial] at this; cases this

/-- The parent's lent cell sits in its flattening at `ℓ`, an `imm` cell. -/
theorem flat_parentRes_imm : ∃ τ, ResUT.Flat (parentRes : TRes KC) τ ∧
    ∃ ψ, τ.get ℓC = some ψ ∧ ψ.kind ≠ Kind.own := by
  obtain ⟨W, μ, hW, hI⟩ := cactusT_config
  obtain ⟨-, -, -, -, hWI, -⟩ := hI
  obtain ⟨τ, hτ⟩ := (ResUT.Valid.split hW hWI.valid).1
  refine ⟨τ, hτ, ?_⟩
  obtain ⟨e, a, -, ha, hc⟩ := hτ
  have ea := (ag_lend ℓC_ne_mC ha).1
  rcases ResUT.Comp.get hc ℓC with ⟨-, f, -⟩ | ⟨ψ₁, -, f, -⟩ | ⟨ψ₁, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ₃, -, -, f, hC⟩
  · rw [ea] at f; cases f
  · rw [ea] at f; cases f
  · rw [ea] at f₂; cases Option.some.inj f₂
    exact ⟨_, f, by simp [lendCell]⟩
  · exact ⟨_, f, by rw [CellUT.CompS.kind hC]; simp⟩

/-- **The copy end is refused**: at the world of `cactusT_config`, the empty branch's run ending
at the parent's lent cell, with no records of its own, fails `EndT`'s `↭`. -/
theorem copy_end_refused :
    ¬ UpdX (sem wC.Θ) (recMask ([] : List (FrameRecT wC.K)))
      (recMask ([] : List (FrameRecT wC.K))) (PMap.empty : TRes wC.K) parentRes :=
  copy_not_updX flat_parentRes_imm

/-- **No run at `twp` beside the parent ends holding anything of its lend.** At the world of
`cactusT_config`, the empty branch's run of `()` (the run `not_stepKeepsFdEscNoUpd` ends at the
copy), in every post-configuration `EndT` admits, holds nothing at the parent's lent location or
escrow. -/
theorem copy_run_keeps_fdEsc :
    ∃ (W : TRes wC.K) (μ : Heap), ResUT.CompS W PMap.empty W ∧
      ∀ (j : Nat) (μ' : Heap) (e' : Expr), j < 1 →
        StepsN (ℍ := ℍ) j μ (Val.unit).1 μ' e' → Final (ℍ := ℍ) μ' e' →
      ∀ (w' : TWd) (ρf' ρ' fρ' : TRes w'.K) (psF' ps' O' : List (FrameRecT w'.K))
        (ls' : List (SRecT w'.K)),
        wC.Ext w' W → RRw (w := wC) (w' := w') W ρf' →
        RecsRR w'.Θ [recE (K := wC.K) ℓC mC] psF' →
        ResUT.Hash ρ' ρf' → ResUT.CompS ρf' ρ' fρ' → SplitT ps' O' psF' →
        RecInv w' fρ' ps' ls' → WInv w' fρ' μ' →
        UpdX (sem w'.Θ) (recMask ([] : List (FrameRecT wC.K))) (recMask O')
          (PMap.empty : TRes wC.K) ρ' →
        NoneAt (MaskDiff (recMask ([] : List (FrameRecT wC.K))) (recMask O')) ρf' →
        ∀ p' ∈ psF', RecRR w'.Θ (recE (K := wC.K) ℓC mC) p' → FdEsc p'.le p'.R ρ' := by
  obtain ⟨W, μ, hW, hI⟩ := cactusT_config
  obtain ⟨-, -, -, hR, hWI, -⟩ := hI
  have hv : ResUT.Valid W := hWI.valid
  have hfd : FinDom μ := by
    obtain ⟨σ, -, hμ⟩ := hWI.2
    rw [show μ = fun x => (σ.get x).map CellUT.erase from funext hμ]
    exact finDom_of_pmap σ
  have hWW : ResUT.CompS W PMap.empty W := ResUT.compS_empty_right _
  have hS : SplitT [recE (K := KC) ℓC mC] [] [recE ℓC mC] :=
    ⟨fun p => by simp, fun p hp => by cases hp⟩
  have hFd₀ : FdEsc (recE (K := KC) ℓC mC).le (recE (K := KC) ℓC mC).R PMap.empty :=
    fdEsc_iff_noneAt.mpr (noneAt_empty _)
  refine ⟨W, μ, hWW, fun j μ' e' hj hrun hfin w' ρf' ρ' fρ' psF' ps' O' ls' hE hr hrecs hh hc
    hS' hR' hI' hu hn p' hp' hpp => ?_⟩
  exact stepKeepsFdEsc (ℍ := ℍ) wC (fun _ _ => True) (fun _ _ _ _ _ _ => True) 1 lsC []
    [recE ℓC mC] [recE ℓC mC] (Val.unit).1 PMap.empty W W μ (recE ℓC mC)
    (twp_here (fun μ => final_val μ Val.unit) fun _ _ _ _ _ _ _ _ => trivial) trivial
    (ResUT.Hash.of_compS hWW hv) hWW hS hR hWI hfd (List.mem_singleton_self _) hFd₀ j μ' e' hj
    hrun hfin w' ρf' ρ' fρ' psF' ps' O' ls' hE hr hrecs hh hc hS' hR' hI' trivial
    (hu.toA hI'.valid) hn p' hp' hpp

/-! ### At the scheduler-wide invariant -/

theorem top_not_le_αC : ¬ KC.le ⊤ αC := fun h => by
  have h' : KC.le αC ⊤ := ParentFn.anc_zero graftP 2
  have := KC.antisymm h h'
  exact absurd (congrArg OrderDual.ofDual this) (by decide)

theorem onBranch_single {n : Life} {l : BoCa.Loc} {ψ : TCell KC} {s : TSet}
    (hs : ψ.lsOf = some s) (h : ∀ x ∈ s.set, KC.le n x) : OnBranchResT KC n (ResUT.single l ψ) := by
  intro l' ψ' e t ht x hx
  obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
  rw [hs] at ht; cases ht
  exact h x hx

/-- **The step at the scheduler-wide invariant.** Before: the empty branch at `⊤`, outside the
lend `α`, and the record's owner at `β`; `CactusInvT` holds and the owner's join reads `JoinPtT`.
After the run of `()` ending at the copy (`not_stepKeepsFdEsc`): `CactusInvT` holds with the same
world, records and memory; the stepped branch sits only at points inside `α`, so no choice of its
point meets `JoinPtT`; and it fails `FdEsc` at the record. -/
theorem copy_config :
    ∃ (W : TRes wC.K) (μ : BoCa.Loc → Option BoCa.Val),
      CactusInvT wC [(PMap.empty, []), (W, [recE ℓC mC])] [⊤, βC] W [recE ℓC mC] lsC μ ∧
      JoinPtT (K := KC) [⊤] αC ∧
      CactusInvT wC [(parentRes, []), (W, [recE ℓC mC])] [αC, βC] W [recE ℓC mC] lsC μ ∧
      (∀ n, OnBranchResT KC n parentRes → ¬ JoinPtT (K := KC) [n] αC) ∧
      ¬ FdEsc (recE (K := KC) ℓC mC).le (recE (K := KC) ℓC mC).R parentRes := by
  obtain ⟨W, μ, hW, hI⟩ := cactusT_config
  obtain ⟨-, -, -, hR, hWI, -⟩ := hI
  have hv : ResUT.Valid W := hWI.valid
  have hcopy : ResUT.CompS W parentRes W := compS_absorb hW parentRes_imm
  have hpα : OnBranchResT KC αC parentRes :=
    onBranch_single (s := TSet.single αC) rfl fun x hx => by
      simp only [TSet.single_set, Finset.mem_singleton] at hx; subst hx; exact KC.refl _
  have hpβ : OnBranchResT KC βC parentRes :=
    onBranch_single (s := TSet.single αC) rfl fun x hx => by
      simp only [TSet.single_set, Finset.mem_singleton] at hx; subst hx; exact βC_lt_αC.1
  have hcβ : OnBranchResT KC βC childRes :=
    onBranch_single (s := TSet.single βC) rfl fun x hx => by
      simp only [TSet.single_set, Finset.mem_singleton] at hx; subst hx; exact KC.refl _
  have hWβ : OnBranchResT KC βC W := OnBranchResT.compS hW hpβ hcβ
  have hrest : CompAllT [W] W := .cons .nil (ResUT.compS_empty_right _)
  refine ⟨W, μ, ⟨.cons hrest (ResUT.CompS.comm (ResUT.compS_empty_right _)), fun p => by simp,
    by simp [Apart], hR, hWI, .cons (OnBranchResT.empty _) (.cons hWβ .nil)⟩,
    fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact top_not_le_αC,
    ⟨.cons hrest (ResUT.CompS.comm hcopy), fun p => by simp, by simp [Apart], hR, hWI,
      .cons hpα (.cons hWβ .nil)⟩,
    fun n hn hJ => hJ n (List.mem_singleton_self _) (copy_inside hn), fun hF => ?_⟩
  obtain ⟨τ, hτ⟩ := (ResUT.Valid.split hcopy hv).2
  exact flat_parentRes_at hτ (hF τ hτ).1

end BoCa.Fig16.Tree.Wp

end
