import Frontend.Check.Program

/-!
# Frontend — Check — the names handled inside a handled computation  `[spec §19]`

Condition 2 of the direct call of a tail-resumptive clause (`docs/effect-lowering.md` §2.3) is
`UnhandledIn Σ K`: no frame of the continuation `K` between a `perform` and its handler catches a
name of the clause's row `Σ` (`Core/ClauseNames.lean`). Two records decide it.

* **At `[handle]`**, the node's `inside`: the frames its handled computation holds, its erasure's
  `Expr.hin` (`Core/HandledNames.lean`), through the bodies of `use` nodes, which the erasure
  places at each use, and through the code of a recursive group, which is the group's generator.
  The typed rule pins it (`TDerivesAt.inside_eq`, `TDerivesP.inside_eq`).
* **At the program**, `Checked.flows`: what may flow in a run of `main` (`ClauseKinds.flows`):
  the frames of the code a value holds (a `λ` that is not applied in place, a `def`'s body, a
  recursive group's generator, a clause), the frames of every handled computation (a continuation
  captures them), the name of every handler a continuation may capture (a name the program
  performs) and the cancel delimiter's `0`. `Expr.fl` counts the frames of every handled
  computation of the erasure, since a continuation may capture them, so a node's `inside` is
  among them wherever the erasure holds the node.

**The theorem** (`Checked.unhandledIn`): in every run of `main` from the empty memory, at every
configuration that holds a handler frame over a context `K` (at an operation it catches, the
point where its clause runs), a row `Σ` none of whose names `Checked.flows` may catch
(`cond2B`) is unhandled in `K`.

**The run invariant** (`Checked.frame_of_node`): every handler frame of a configuration such a run
reaches has the name of a handle node of `main`'s erasure (or the reserved `0`, or `main` holds a
handler whose name is not a literal, which `bcc handled` reports for each program).

Recursion is covered without unique names: a recursive group's code is its generator, a value, so
the frames its body holds are in `Checked.flows`, and a second handler of a name a recursive call
puts into `K` is one of them.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.ClauseKinds
open BoCa.Lifetime (LifeCtx)

/-! ### The record at `[handle]`, pinned by the derivation -/

/-- **The record is the derivation's**: a typed derivation of a `handle` node holds its `inside`
as the frames of its handled computation's erasure.  `[spec §19]` -/
theorem TDerivesAt.inside_eq {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite} {ins : HIn} {tc te : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.effHandleV i J S E fs n A R u ks site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleV _ _ _ _ _ _ _ _ _ _ _ hins => exact hins

theorem TDerivesAt.inside_eqB {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {d : Lifetime.Life} {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite}
    {ins : HIn} {tc te : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.effHandleVB i J S E fs n A R d u ks site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleVB _ _ _ _ _ _ _ _ _ _ _ _ _ hins => exact hins

theorem TDerivesAt.inside_eqT {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S SN : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {site : Option HSite} {ins : HIn} {tc te : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.effHandleT i J S SN E fs n A R u site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hins => exact hins

theorem TDerivesP.inside_eq {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite} {ins : HIn} {tc te : TExpr}
    (h : TDerivesP Δ Γ (.effHandleV i J S E fs n A R u ks site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleV _ _ _ _ _ _ _ _ _ _ hins => exact hins

theorem TDerivesP.inside_eqB {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {d : Lifetime.Life} {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite}
    {ins : HIn} {tc te : TExpr}
    (h : TDerivesP Δ Γ (.effHandleVB i J S E fs n A R d u ks site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleVB _ _ _ _ _ _ _ _ _ _ _ _ hins => exact hins

theorem TDerivesP.inside_eqT {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S SN : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {site : Option HSite} {ins : HIn} {tc te : TExpr}
    (h : TDerivesP Δ Γ (.effHandleT i J S SN E fs n A R u site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleT _ _ _ _ _ _ _ _ _ _ _ _ _ _ hins => exact hins


end BoCa.Fig16.LogRel.Core.Check

namespace Frontend.Check
open BoCa BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.ClauseKinds
open BoCa.Fig16.LogRel.Core.Check

/-! ### The record at the program -/

/-- **Condition 2, decided**: no name of the row `Σ` (its names `row`) is one the record `V` may
catch.  `[spec §19]` -/
def cond2B (V : HIn) (row : List UInt32) : Bool := row.all fun m => !V.catchesB m

theorem cond2B_sound {V : HIn} {S : CRow} (h : cond2B V (S.map (·.n)) = true) :
    ∀ o ∈ S, ¬ V.Catches o.n := by
  intro o ho hc
  simp only [cond2B, List.all_eq_true, List.mem_map, Bool.not_eq_true'] at h
  have := h o.n ⟨o, ho, rfl⟩
  rw [HIn.catchesB_iff.mpr hc] at this
  cases this

/-- **What may flow in a run of `main`**: `ClauseKinds.flows` of the checked term.  `[spec §19]` -/
def Checked.flows (c : Checked) : HIn := ClauseKinds.flows c.e

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem emptyMem_clean : ∀ ℓ v, BoCa.Adequacy.emptyMem ℓ = some v → v.1.hin = {} ∧ v.1.pn = {} :=
  fun _ _ h => by simp [BoCa.Adequacy.emptyMem] at h

/-- **Condition 2 at a checked program.** In a run of `main` from the empty memory, at every
configuration that holds a handler frame `hnd H K[p]` (at `p = perform (n, …)` the point where the
handler's clause runs), a row `Σ` that `cond2B` accepts at `main`'s flow record is unhandled in
`K`: no frame of `K` catches an operation or a raise of a name of `Σ`.  `[spec §19]` -/
theorem Checked.unhandledIn (c : Checked) {μ : BoLo.Heap} {e : BoCa.Expr}
    (h : BoLo.Steps (ℍ := ℍ) BoCa.Adequacy.emptyMem c.e μ e) {K₀ K : BoLo.Kont} {H : BoCa.Val}
    {p : BoCa.Expr} (he : e = K₀.plug (BoLo.hndE H (K.plug p))) {S : CRow}
    (hS : cond2B c.flows (S.map (·.n)) = true) : UnhandledIn S K :=
  steps_unhandledIn h emptyMem_clean he (cond2B_sound hS)

/-- **The run invariant at a checked program**: every handler frame a run of `main` from the
empty memory reaches is of a handle node of `main`'s erasure: its name is one of a literal `hnd`
in it, or the reserved `0`, or `main` holds a handler whose name is not a literal.
`[spec §19]` -/
theorem Checked.frame_of_node (c : Checked) {μ : BoLo.Heap} {e : BoCa.Expr}
    (h : BoLo.Steps (ℍ := ℍ) BoCa.Adequacy.emptyMem c.e μ e) {K : BoLo.Kont} {a : BoCa.Expr}
    (he : e = K.plug a) {m : UInt32} (hm : K.HasHnd m = true) :
    m ∈ c.e.hin.names ∨ m = 0 ∨ c.e.hin.any = true :=
  steps_frame_of_node h (fun ℓ v hv => (emptyMem_clean ℓ v hv).1) he hm

end Frontend.Check
