import Frontend.Check.Program

/-!
# Frontend — Check — condition 2: the clause's names and the names handled inside  `[spec §19]`

Condition 2 of the direct call of a tail-resumptive clause (`docs/effect-lowering.md` §2.3) is
that no frame of the continuation `K` between a `perform` and its handler catches a name the
clause's work performs or raises. It is stated over the names the clause's own code performs or
raises (`UnhandledNames ns K`, `Core/ClauseOwn.lean`), read off the clause the node's erasure
holds (`handlerNames`, `Frontend/Check/Kinds.lean`), and over the clause's row `Σ`
(`UnhandledIn Σ K`, `Core/ClauseNames.lean`) where the clause may run code it does not hold.

* **The names bound the work** (`tail_clause_names`): at a node whose kind for an operation is
  `tail`, every run of the clause's work, its body without its resumes, at any values of its
  variables and from any memory, performs and raises only the clause's names
  (`tail_work_names`). A clause with no names meets condition 2 in every `K`
  (`unhandledNames_nil`).

Where a clause has names, two records decide it.

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

**The theorem** (`Checked.unhandledNames`, and `Checked.unhandledIn` over a row): in every run of
`main` from the empty memory, at every configuration that holds a handler frame over a context
`K` (at an operation it catches, the point where its clause runs), names none of which
`Checked.flows` may catch (`cond2B`) are unhandled in `K`.

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
    {S : Row} {E : List (Count × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite} {ins : HIn} {tc te : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.effHandleV i J S E fs n A R u ks site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleV _ _ _ _ _ _ _ _ _ _ _ hins => exact hins

theorem TDerivesAt.inside_eqB {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S : Row} {E : List (Count × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {d : Lifetime.Life} {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite}
    {ins : HIn} {tc te : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.effHandleVB i J S E fs n A R d u ks site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleVB _ _ _ _ _ _ _ _ _ _ _ _ _ hins => exact hins

theorem TDerivesAt.inside_eqT {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S SN : Row} {E : List (Count × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {site : Option HSite} {ins : HIn} {tc te : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.effHandleT i J S SN E fs n A R u site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hins => exact hins

theorem TDerivesP.inside_eq {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S : Row} {E : List (Count × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite} {ins : HIn} {tc te : TExpr}
    (h : TDerivesP Δ Γ (.effHandleV i J S E fs n A R u ks site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleV _ _ _ _ _ _ _ _ _ _ hins => exact hins

theorem TDerivesP.inside_eqB {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S : Row} {E : List (Count × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {d : Lifetime.Life} {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite}
    {ins : HIn} {tc te : TExpr}
    (h : TDerivesP Δ Γ (.effHandleVB i J S E fs n A R d u ks site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleVB _ _ _ _ _ _ _ _ _ _ _ _ hins => exact hins

theorem TDerivesP.inside_eqT {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J J' : Jdg}
    {S SN : Row} {E : List (Count × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {site : Option HSite} {ins : HIn} {tc te : TExpr}
    (h : TDerivesP Δ Γ (.effHandleT i J S SN E fs n A R u site ins tc te) J') :
    ins = te.erase.hin := by
  cases h with
  | effHandleT _ _ _ _ _ _ _ _ _ _ _ _ _ _ hins => exact hins

/-! ### The names a clause's own code performs or raises -/

theorem tupleAt_eq_clauseExpr : ∀ (j : Nat) (e : Expr), tupleAt j e = clauseExpr e j
  | 0, .pair _ _ => rfl
  | j + 1, .pair _ b => tupleAt_eq_clauseExpr j b
  | 0, .var _ | 0, .unit | 0, .inj₁ _ | 0, .inj₂ _ | 0, .lam _ | 0, .loc _ | 0, .prim _
  | 0, .seq .. | 0, .letpair .. | 0, .case .. | 0, .app .. => rfl
  | _ + 1, .var _ | _ + 1, .unit | _ + 1, .inj₁ _ | _ + 1, .inj₂ _ | _ + 1, .lam _
  | _ + 1, .loc _ | _ + 1, .prim _ | _ + 1, .seq .. | _ + 1, .letpair .. | _ + 1, .case ..
  | _ + 1, .app .. => rfl

/-- A name list `handlerNames` records for the operation `j` is the names of the clause of the
handler's pair the machine runs for it. -/
theorem handlerNames_some {E : List (Count × VTy × VTy)} {H : Expr} {j : Nat}
    {o : Count × VTy × VTy} {ns : List UInt32} (ho : E[j]? = some o)
    (hn : (handlerNames E H)[j]? = some (some ns)) :
    ∃ c, clauseAt j H = some c ∧ clauseNames o c = some ns := by
  unfold handlerNames at hn
  split at hn
  · rename_i hr hs
    rw [List.getElem?_map] at hn
    have hj : j < E.length := (List.getElem?_eq_some_iff.mp ho).1
    have hz : ((List.range E.length).zip E)[j]? = some (j, o) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_range hj, ho⟩
    rw [hz] at hn
    simp only [Option.map_some, Option.some.injEq] at hn
    obtain ⟨c, hc, hcn⟩ := Option.bind_eq_some_iff.mp hn
    exact ⟨c, by simp only [clauseAt]; rw [tupleAt_eq_clauseExpr]; exact hc, hcn⟩
  · rw [List.getElem?_map, ho] at hn
    cases hn

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ] in
/-- **A tail-resumptive clause's work performs and raises only its names.** At a `handle` node
whose kind for the operation `j` is `tail` (`classifyHandler`) and whose names for it are `ns`
(`handlerNames`), the clause of the node's pair is `λp. let (x, κ) = p; M`, `M'` is `M` without
its resumes (`TailResumesAt 0 M M'`), and every run of the work `M'`, at any values of its
variables, from any memory, performs and raises only names of `ns` (`tail_work_names`).
`[spec §19]` -/
theorem tail_clause_names (E : List (Count × VTy × VTy)) (tH : TExpr) {j : Nat}
    {o : Count × VTy × VTy} {k : HKind} {ns : List UInt32} (ho : E[j]? = some o)
    (hk : (classifyHandler E tH)[j]? = some k) (ht : k.kind = .tail)
    (hn : (handlerNames E tH.erase)[j]? = some (some ns)) :
    ∃ M M', clauseAt j tH.erase = some (.lam (.letpair (.var 0) M)) ∧ TailResumesAt 0 M M' ∧
      ∀ {W : Expr}, SubstOf M' W → ∀ {μ μ' : BoLo.Heap} {e : Expr},
        BoLo.Steps (ℍ := ℍ) μ W μ' e → ∀ {K : BoLo.Kont} {m i : UInt32} {v : Val},
          (e = K.plug (BoLo.performE (.val (BoLo.opPayload m i v))) → m ∈ ns) ∧
          (e = K.plug (BoLo.raiseE (.val (BoLo.opPayload m i v))) → m ∈ ns) := by
  obtain ⟨c, hc, hcn⟩ := handlerNames_some ho hn
  have hP := classifyHandler_sound E tH ho hk hc
  rw [ht] at hP
  obtain ⟨ha, M, rfl, M', hM⟩ := hP
  simp only [clauseNames, ha, Bool.false_eq_true, if_false] at hcn
  exact ⟨M, M', hc, hM, fun hW _ _ _ hs _ _ _ _ => tail_work_names hM hcn hW hs⟩

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

/-- Condition 2, decided, is sound over names: no name it accepts is one the record may catch. -/
theorem cond2B_names_sound {V : HIn} {ns : List UInt32} (h : cond2B V ns = true) :
    ∀ m ∈ ns, ¬ V.Catches m := by
  intro m hm hc
  simp only [cond2B, List.all_eq_true, Bool.not_eq_true'] at h
  have := h m hm
  rw [HIn.catchesB_iff.mpr hc] at this
  cases this

/-- **The names condition 2 is over at a clause** (form (b), SPEC §19): the names its own code
performs or raises (`clauseNames`), or, where it may run code it does not hold, its row's. -/
def cond2Names (row : List UInt32) (ns : Option (List UInt32)) : List UInt32 := ns.getD row

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

/-- **Condition 2 over a clause's names, at a checked program.** In a run of `main` from the
empty memory, at every configuration that holds a handler frame `hnd H K[p]`, names that
`cond2B` accepts at `main`'s flow record are unhandled in `K`. At no names, they are unhandled in
every `K` (`unhandledNames_nil`).  `[spec §19]` -/
theorem Checked.unhandledNames (c : Checked) {μ : BoLo.Heap} {e : BoCa.Expr}
    (h : BoLo.Steps (ℍ := ℍ) BoCa.Adequacy.emptyMem c.e μ e) {K₀ K : BoLo.Kont} {H : BoCa.Val}
    {p : BoCa.Expr} (he : e = K₀.plug (BoLo.hndE H (K.plug p))) {ns : List UInt32}
    (hS : cond2B c.flows ns = true) : UnhandledNames ns K :=
  steps_unhandledNames h emptyMem_clean he (cond2B_names_sound hS)

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
