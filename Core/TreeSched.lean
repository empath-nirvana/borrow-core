import Core.TreeHandle

/-!
# Multi-branch adequacy over the tree world  `[spec §62]`

**The guarantee.** A closed program `hnd H e₀`, `H` a scheduler meeting `SchedOKT` and `e₀` a
task verified at `cerwpT` at the scheduler's table, is safe or diverges: every configuration it
reaches steps or is a value, a value is reached only at the empty memory, and every `free` finds
its cell (`MultiBranchAdequacyT`, `multiBranchAdequacyT`). The scheduler may store any number of
branches, each a continuation it was handed or a task it starts, and resume them in any order:
nothing in `SchedOKT` fixes how many it holds or which it resumes next. Divergence is allowed and
there is no fuel.

**What the scheduler must satisfy** (`SchedOKT`, `Core/TreeHandle.lean`): its clauses at the empty
table, each continuation `κ` read by `KapSchedT`. `κ` may be resumed beside a state the clause
keeps, under any frame condition whose frames hold nothing at the masks `M` of the records the
branch owned at its resumes and at its stop, and are valid (`fdMask M`). So the state a scheduler
keeps beside a resumed branch must be valid and hold nothing of that branch's lends: the join
condition, in location form. The table's resumer guarantee `fd` must follow from it (`fdJoinT`).

**How it is proved.** `cerwpT_schedHandle` (`[handle]` for the scheduler, by induction on the
index, no `hdv`) turns the task and the clauses into the program at `cerwpT` at the empty table,
under the empty frame; `cerwpT_adequacy` derives adequacy from it through `CactusInvT`'s
`cactusT_step`. Each resume goes through `contShareT_resume`; the frame a stopped branch's clause
runs under is told the branch's masks by `twp_bind_fd` (`noneAt_recMask_end`: a record the branch
opened during the segment is avoided by the frame from its opening).

**Departure from `docs/new-core/scope-781.md` §4's draft** (item 2 of the slice): the task runs at
the frame condition `⊤`, not `emptyFrameT`. A scheduler that keeps a state beside a resumed branch
puts it in that branch's frame; under `emptyFrameT` the branch admits only an empty state
(`hFy_emptyFrame` of the spike). The state could instead be carried through the answer, in the
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

/-- **Multi-branch adequacy over the tree world.** A closed program `hnd H e₀`: the task `e₀` at
`cerwpT` at the scheduler's table `T`, from the empty world at any tree, under any frame; the
scheduler `H = hndVal n₀ qs hr hs` meeting `SchedOKT`; the program's answers holding nothing. -/
def MultiBranchAdequacyT : Prop :=
  ∀ (P : ParentFn) (T : OpTabT) (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : TPostV) (e₀ : Expr),
    (∀ k w ls O v ρ, Qout k w ls O v ρ → ρ = PMap.empty) →
    SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin Qout →
    (∀ n, cerwpT (ℍ := ℍ) (opTableT T) Qin (fun _ _ => True) n
      ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ [] [] e₀
      (PMap.empty : TRes (WCactus.ofParent P))) →
    OrDiverges (ℍ := ℍ) (hndE (hndVal n₀ qs hr hs) e₀)

/-- **The program at the empty table**: `[handle]` for the scheduler, under the empty frame, at
the empty mask. -/
theorem schedProgram_cerwpT {P : ParentFn} {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val}
    {Qin Qout : TPostV} {e₀ : Expr} (hS : SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin Qout)
    (he : ∀ n, cerwpT (ℍ := ℍ) (opTableT T) Qin (fun _ _ => True) n
      ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ [] [] e₀
      (PMap.empty : TRes (WCactus.ofParent P))) (n : Nat) :
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Qout (fun _ ρf => ρf = PMap.empty) n
      ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ [] [] (hndE (hndVal n₀ qs hr hs) e₀)
      (PMap.empty : TRes (WCactus.ofParent P)) :=
  cerwpTE_iff.mpr (cerwpT_schedHandle hS n (fun _ => False) _ _ _ _ _ e₀ _ emptyFrame_mono
    (fun w ρf h => by subst h; exact fdMask_empty _ w) (fun x hx => by simp [recMask] at hx)
    (fun _ _ _ => trivial) (he n))

theorem multiBranchAdequacyT : MultiBranchAdequacyT (ℍ := ℍ) :=
  fun P _ _ _ _ _ _ _ _ hQ hS he => cerwpT_adequacy (ℍ := ℍ) P hQ (schedProgram_cerwpT hS he)

end BoCa.Fig16.Tree.Wp

end
