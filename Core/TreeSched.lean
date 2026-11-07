import Core.TreeHandle

/-!
# Multi-branch adequacy over the tree world  `[spec §62]`

**The guarantee.** A closed program `hnd H e₀`, `H` a scheduler meeting `SchedOKT` and `e₀` a
task verified at `cerwpT` at the scheduler's table, is safe or diverges: every configuration it
reaches steps or is a value, a value is reached only at the empty memory, and every `free` finds
its cell (`MultiBranchAdequacyT`, `multiBranchAdequacyT`). Nothing in `SchedOKT` fixes how many
continuations a clause holds or which it resumes next. Divergence is allowed and there is no fuel.
A continuation a clause holds across another branch's run is resumed at any list keeping the
records of its stop list its share reads (`KapSchedT`'s `KeepRel` premise); `Core/TreeResume.lean`
derives it across another branch's run, that branch opening and ending lends of its own.

**What the scheduler must satisfy** (`SchedOKT`, `Core/TreeHandle.lean`): its clauses at the empty
table, each continuation `κ` read by `KapSchedT`. `κ` may be resumed beside a state the clause
keeps, under any frame condition whose frames hold nothing at the masks `M` of the records the
branch owns at its stop, and are valid (`fdMask M`). So the state a scheduler
keeps beside a resumed branch must be valid and hold nothing of that branch's lends: the join
condition, in location form. The table's resumer guarantee `fd` must follow from it (`fdJoinT`).

**How it is proved.** `cerwpT_schedHandle` (`[handle]` for the scheduler, by induction on the
index, no `hdv`) turns the task and the clauses into the program at `cerwpT` at the empty table,
under the empty frame; `cerwpT_adequacy` derives adequacy from it through `CactusInvT`'s
`cactusT_step` at one branch (the running one, with no other branch in the invariant). The stored
branches are not branches of `CactusInvT`: each is a continuation the scheduler's clause holds,
read by `KapSchedT` (and, for a scheduler keeping a pool, by `PoolT`, `Core/TreeSchedPool.lean`),
and `cerwpT_schedHandle`'s induction on the index carries them. The invariant over them is in pool
form: each stored share resumes at `KeepRel`, and every two are apart (`fdMask`, `recMask`, with no
branch points), as decision 74 records (`docs/new-core/scope-781.md` §4).
Each resume goes through `contShareT_resume`; the frame a stopped branch's clause runs under is
told the branch's masks by `twp_bind_fd` (`noneAt_recMask_end`: a record the branch opened during
the segment is avoided by the frame from its opening).

**The task's frame conditions.** The task runs at base and present frame conditions every valid
frame meets (`⊤` among them), not at the empty frame. A scheduler that keeps a state beside a
resumed branch puts it in that branch's frame, and under the empty frame the branch admits only an
empty state. The state could instead be carried through the answer, in the
task's own resource. That is not chosen: a task would then hold the other branches' shares, and
ending a lend of its own would need them to hold nothing of it. `PBv` reads neither the task's
records nor its frame, so it cannot say so. `fdAt` can, and the frame is where the scheduler's
state is.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap hndE hndVal)

/-- The empty frame condition is carried along re-reading. -/
theorem emptyFrame_mono : TFrame.Mono (fun _ ρf => ρf = PMap.empty) := by
  intro w w' ρ ρ' _ hr h
  subst h
  exact RR.of_empty hr

/-! ### The frame condition at a resume, along re-reading -/

/-- An entry's `fd` read at two re-readings of one record list, carried along the extension
between them. -/
def OpEntT.FdMono (en : OpEntT) : Prop :=
  ∀ (v : Val) (w₀ w w₁ : TWd) (O : List (FrameRecT w₀.K)) (O' : List (FrameRecT w.K))
    (O₁ : List (FrameRecT w₁.K)) (ρ : TRes w.K) (ρ₁ : TRes w₁.K),
    RecsRR w.Θ O O' → RecsRR w₁.Θ O O₁ → w.Ext w₁ ρ → RRw (w := w) (w' := w₁) ρ ρ₁ →
    en.fd v w O' ρ → en.fd v w₁ O₁ ρ₁

/-- **`fdAt` is carried along re-reading** (`TFrame.Mono (fdAt …)`), where the entry's `fd` is
(`OpEntT.FdMono`) and the records have a re-reading at every world the frame condition holds at.
A run resumed at `fdAt` binds through it (`twp_bind`'s `hFm`). -/
theorem fdAt_mono {en : OpEntT} {v : Val} {F : TFrame} {w' : TWd} {O' : List (FrameRecT w'.K)}
    (hF : F.Mono) (hfd : en.FdMono)
    (hex : ∀ (w : TWd) (ρf : TRes w.K), F w ρf → ∃ O'' : List (FrameRecT w.K), RecsRR w.Θ O' O'') :
    (fdAt en v F O').Mono := by
  intro w w₁ ρ ρ₁ hE hr hw
  refine ⟨hF w w₁ ρ ρ₁ hE hr hw.1, fun O₁ hO₁ => ?_⟩
  obtain ⟨O'', hO''⟩ := hex w ρ hw.1
  exact hfd v w' w w₁ O' O'' O₁ ρ ρ₁ hO'' hO₁ hE hr (hw.2 O'' hO'')

/-- The join's guarantee is read at the records' locations, which re-reading keeps. -/
theorem fdJoinT_fdMono {en : OpEntT} (h : ∀ v w O ρf, en.fd v w O ρf ↔ fdJoinT v w O ρf) :
    en.FdMono := by
  intro v w₀ w w₁ O O' O₁ ρ ρ₁ hO' hO₁ hE hr hfd
  refine (h v w₁ O₁ ρ₁).mpr ?_
  have h₀ := fdMask_mono _ w w₁ ρ ρ₁ hE hr ((h v w O' ρ).mp hfd)
  exact fdMask_le (fun x hx => (recMask_rr hO' x).mp ((recMask_rr hO₁ x).mpr hx)) h₀

/-! ### Resuming a stored branch beside the scheduler's state -/

/-- **A stored branch resumed beside a state the scheduler keeps.** The clause holds `κ`
(`KapSchedT` at the masks `M`) and a state `ρ₂` in `R` (owning `O₂`), valid and holding nothing at
`M`; under a frame condition whose frames avoid `M`, the resume of `κ` at an answer the entry
accepts runs with the state beside it, and ends beside the state re-read. -/
theorem kapSchedT_resume_beside {Qout : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {H : Val} {k : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O O₂ : List (FrameRecT w.K)} {v κ : Val} {ρk : TRes w.K}
    (hκ : KapSchedT (ℍ := ℍ) Qout M en H k w ls O v κ ρk) {F : TFrame}
    (hFM : ∀ w' ρf, F w' ρf → fdMask M w' ρf) {k' : Nat} (hk' : k' < k) {a : Val}
    {σ σ' ρ₂ ρ : TRes w.K} (hB : en.PBv v k' w ls a σ) (hcσ : ResUT.CompS ρk σ σ')
    (hcρ : ResUT.CompS σ' ρ₂ ρ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hls : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) (hO : ∀ r ∈ O, CovR (sem w.Θ) w.K r.R)
    {R : TRProp} (hR : R.Mono) (hap : ∀ p ∈ O, ∀ q ∈ O₂, p.le ≠ q.le) (hR₂ : R w O₂ ρ₂)
    (hM₂ : fdMask M w ρ₂) :
    twp (ℍ := ℍ) F ((valPost Qout).sep R) k' w ls (O ++ O₂)
      (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val a)) ρ := by
  have hcovk : CovR (sem w.Θ) w.K ρk :=
    CovR.of_compS_left hcσ (CovR.of_compS_left hcρ hcov)
  have h := cerwpTE_iff.mp (hκ.2.1 w ρk ls O (TWd.Ext.refl _ _) (RR.refl hcovk)
    (KeepRel.refl hls ρk) (RecsRR.refl hO) k' hk' a σ σ' hB hcσ (fdMask M)
    (fdMask_mono M) (fun _ _ h => h))
  refine twp_frame_w hR hap hcρ hcov ?_ h hR₂
  intro w₀ ρf ρ₁₀ ρ₂₀ y fρ O₁₀ O₂₀ ps psF ls₀ μ hE h₂₀ _ _ hFρ hy hyf _ _ _ hI
  have hvy : ResUT.Valid y := (ResUT.Valid.split hyf hI.valid).1
  have hvf := ResUT.Valid.split hy hvy
  exact ⟨hvy, NoneAt.compS hy hvf.1 hvf.2 (hFM w₀ ρf hFρ).2
    (NoneAt.rr hE.1 hM₂.1 h₂₀ hM₂.2)⟩

/-- **Multi-branch adequacy over the tree world.** A closed program `hnd H e₀`: the task `e₀` at
`cerwpT` at the scheduler's table `T`, from the empty world at any tree, at a base frame condition
`Fb` every valid frame meets and a present one `Fe` every valid frame meets (so a task may end a
lend it opened: its frames are valid, and avoid its records from their opening, `twp_bind_fd`);
the scheduler `H = hndVal n₀ qs hr hs` meeting `SchedOKT`; the program's answers holding nothing. -/
def MultiBranchAdequacyT : Prop :=
  ∀ (P : ParentFn) (T : OpTabT) (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : TPostV)
    (Fb Fe : TFrame) (e₀ : Expr),
    (∀ k w ls O v ρ, Qout k w ls O v ρ → ρ = PMap.empty) →
    SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin Qout →
    (∀ w ρf, ResUT.Valid ρf → Fb w ρf) → (∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf) →
    (∀ n, cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n
      ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ [] [] e₀
      (PMap.empty : TRes (WCactus.ofParent P))) →
    OrDiverges (ℍ := ℍ) (hndE (hndVal n₀ qs hr hs) e₀)

/-- **The scheduled program at `twp`**, under any frame condition whose frames are valid: `[handle]`
for the scheduler at the empty mask. -/
theorem schedProgram_twp {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val}
    {Qin Qout : TPostV} {Fb Fe F : TFrame} {e₀ : Expr} (hS : SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin Qout)
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf)
    (hFm : F.Mono) (hF : ∀ w ρf, F w ρf → fdMask (fun _ => False) w ρf) {n : Nat} {w : TWd}
    {ρ : TRes w.K}
    (he : cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n w [] [] e₀ ρ) :
    twp (ℍ := ℍ) F (valPost Qout) n w [] [] (hndE (hndVal n₀ qs hr hs) e₀) ρ :=
  cerwpT_schedHandle hS n (fun _ => False) _ _ _ _ _ _ e₀ _ hFm hF
    (fun x hx => by simp [recMask] at hx) hFb hFe he

/-- **The program at the empty table**: `[handle]` for the scheduler, under the empty frame, at
the empty mask. -/
theorem schedProgram_cerwpT {P : ParentFn} {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val}
    {Qin Qout : TPostV} {Fb Fe : TFrame} {e₀ : Expr} (hS : SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin Qout)
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf)
    (he : ∀ n, cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n
      ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ [] [] e₀
      (PMap.empty : TRes (WCactus.ofParent P))) (n : Nat) :
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Qout (fun _ ρf => ρf = PMap.empty)
      (fun _ ρf => ρf = PMap.empty) n
      ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ [] [] (hndE (hndVal n₀ qs hr hs) e₀)
      (PMap.empty : TRes (WCactus.ofParent P)) :=
  cerwpTE_iff.mpr (schedProgram_twp hS hFb hFe emptyFrame_mono
    (fun w ρf h => by subst h; exact fdMask_empty _ w) (he n))

theorem multiBranchAdequacyT : MultiBranchAdequacyT (ℍ := ℍ) :=
  fun P _ _ _ _ _ _ _ _ _ _ hQ hS hFb hFe he =>
    cerwpT_adequacy (ℍ := ℍ) P hQ (schedProgram_cerwpT hS hFb hFe he)

end BoCa.Fig16.Tree.Wp

end
