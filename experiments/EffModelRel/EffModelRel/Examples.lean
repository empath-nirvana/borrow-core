import EffModelRel.Tensor

/-!
# EffModelRel — a concrete signature: sum versus tensor, and counterexamples

The effects of phase A: `Log` (linear), `Fail` (abortive), `Ctr` (linear, run by a capability),
`Yield` (affine) and `Choose` (multi-shot). With them:

- **Absorption, exactly where it should hold.** `log m; raise ≡ raise` inside a writer `Log`, for
  every `Fail` handler around it (`absorb_writer`), and not for the other five placements of
  phase A's family (`not_absorb_*`): the sum and the tensor of the two theories.
- **Lent state survives an abort** (`lent_state_survives`): the sum, for a borrowed capability.
- **Two printing `Log`s do not commute** (`print_print_not_commute`).
- **`ν/op` fails for a multi-shot operation** (`nu_op_fails_multishot`): a fresh instance shared by
  two resumptions is observable. Phase A checked `ν/op` only at a linear operation.

Every negative result is a context in which the two sides observe differently, checked by
`decide`.
-/

namespace EffRel

inductive Eff where
  | log | fail | ctr | yld | choose
  deriving DecidableEq, Repr

inductive Op : Eff → Type where
  | log : Op .log
  | inc : Op .ctr
  | get : Op .ctr
  | yield : Op .yld
  | choose : Op .choose

inductive Ab : Eff → Type where
  | raise : Ab .fail

abbrev σ : Sig where
  E := Eff
  O := Op
  A := Ab
  arg := fun _ o => match o with
    | .log => .int | .inc => .unit | .get => .unit | .yield => .int | .choose => .unit
  res := fun _ o => match o with
    | .log => .unit | .inc => .unit | .get => .int | .yield => .unit | .choose => .bool
  q := fun _ o => match o with
    | .log => Mode.lin | .inc => Mode.lin | .get => Mode.lin | .yield => Mode.aff
    | .choose => Mode.unr
  aarg := fun _ _ => .unit
  bnd := fun e => match e with
    | .log => Mode.lin | .fail => Mode.aff | .ctr => Mode.lin | .yld => Mode.aff
    | .choose => Mode.unr
  bnd_q := by intro e o; cases o <;> rfl
  bnd_ab := by intro e a; cases a; rfl

variable {Ψ : List Eff} {Γ : List (VTy σ)}

abbrev V (Ψ : List Eff) (Γ : List (VTy σ)) (A : VTy σ) := Val σ Ψ Γ A
abbrev M (Ψ : List Eff) (Γ : List (VTy σ)) (C : CTy σ) := Cmp σ Ψ Γ C

def v0 : V Ψ (A :: Γ) A := .var .z
def v1 : V Ψ (B :: A :: Γ) A := .var (.s .z)
def v2 : V Ψ (C :: B :: A :: Γ) A := .var (.s (.s .z))

def tInt : VTy σ := .g .int
def tUnit : VTy σ := .g .unit

/-! ## Handlers -/

/-- `Log` printed to the world, `κ` resumed in place. -/
def printOps {Γ : List (VTy σ)} {C : CTy σ} : (o : Op .log) →
    M Ψ (kty (σ.q .log o) Eb.top (σ.res .log o) C :: .g (σ.arg .log o) :: Γ) C
  | .log => .bind (.emit v1) (.app (.force v1) .unit)

/-- `Log` as a writer: a handler into `int → F (A × int)`. -/
def writerOps {Γ : List (VTy σ)} {A : VTy σ} : (o : Op .log) →
    M Ψ (kty (σ.q .log o) Eb.top (σ.res .log o) (.arr tInt Eb.top (.F (.prod A tInt))) :: .g (σ.arg .log o) :: Γ)
      (.arr tInt Eb.top (.F (.prod A tInt)))
  | .log => .lam (.bind (.prim .add v0 v2) (.app (.app (.force v2) .unit) v0))

def writerRet {Γ : List (VTy σ)} {A : VTy σ} : M Ψ (A :: Γ) (.arr tInt Eb.top (.F (.prod A tInt))) :=
  .lam (.ret (.pair v1 v0))

/-- Run `M` under a writer `Log` from 0: its answer and the total logged. -/
def writer {A : VTy σ} (N : M (.log :: Ψ) Γ (.F A)) : M Ψ Γ (.F (.prod A tInt)) :=
  .app (.handle .log Eb.top writerRet writerOps (fun a => nomatch a) N) (.int 0)

/-- `Fail` to a default. -/
def failDefault {A : VTy σ} (d : V Ψ Γ A) (N : M (.fail :: Ψ) Γ (.F A)) : M Ψ Γ (.F A) :=
  .handle .fail Eb.top (.ret v0) (fun o => nomatch o) (fun _ => .ret (d.wk)) N

def printLog {A : VTy σ} (N : M (.log :: Ψ) Γ (.F A)) : M Ψ Γ (.F A) :=
  .handle .log Eb.top (.ret v0) printOps (fun a => nomatch a) N

def raise (f : Var Ψ .fail) : M Ψ Γ C := .ab f .raise .unit
def logm (l : Var Ψ .log) (m : Int) (N : M Ψ (tUnit :: Γ) C) : M Ψ Γ C := .op l .log (.int m) N

/-! ## Absorption: `log m; raise ≡ raise` inside a writer -/

theorem writer_pure {Ψ : List Eff} {Γ : List (VTy σ)} {A : VTy σ} :
    PureClause (S := σ) (Ψ := Ψ) (Γ := Γ) (e := .log) (bA := Eb.top) (bh := Eb.top) Op.log
      (writerOps (A := A) Op.log)
      (fun _ => ()) (fun v s => (show Int from s) + (show Int from v)) := by
  intro η ρ v k d; rfl

/-- Inside a writer `Log`, under any `Fail` handler: `log m; raise ≡ raise`. -/
theorem absorb_writer (f : Var Ψ .fail) (m : Int) :
    CtxEq (Γ := Γ) (writer (A := tInt) (logm .z m (raise (.s f)))) (writer (raise (.s f))) :=
  absorb_pure (S := σ) (e := .log) (f := .fail) (bh := Eb.top) (bA := Eb.top) (by decide) writerRet writerOps
    (fun a => nomatch a) Op.log writer_pure m f Ab.raise () (.int 0)

/-! ## Observations of closed programs -/

theorem CtxEq.prog_obs {g : G} {M N : Prog S g} (h : CtxEq M N) : M.obs = N.obs :=
  h g (.force (.var .z))

/-- Answer `N`'s answer, emitting the writer's total first. -/
def observeW (N : M [] [] (.F (.prod tInt tInt))) : Prog σ .int :=
  .bind N (.split v0 (.bind (.emit v0) (.ret v2)))

/-- A comodel of `Log` that totals what is logged. -/
def coLog : (o : Op .log) → Cmp σ [] [.g .int, .g (σ.arg .log o)] (.F (coRes σ .log .int o))
  | .log => .bind (.prim .add v0 v1) (.ret (.inl (.pair .unit v0)))

/-! ## Where absorption fails: the sum -/

/-- `Fail` outside a printing `Log`: the log reached the world before the abort. -/
theorem not_absorb_print_inside :
    ¬ CtxEq (S := σ) (Ψ := []) (Γ := []) (failDefault (.int 0) (printLog (logm .z 7 (raise (.s .z)))) : Prog σ .int)
      (failDefault (.int 0) (printLog (raise (.s .z)))) :=
  fun h => absurd h.prog_obs (by decide)

/-- `Log` (a writer) outside `Fail`: the writer keeps the log. -/
theorem not_absorb_writer_outside :
    ¬ CtxEq (S := σ) (Ψ := []) (Γ := []) (observeW (writer (failDefault (.int 0) (logm (.s .z) 7 (raise .z)))))
      (observeW (writer (failDefault (.int 0) (raise .z)))) :=
  fun h => absurd h.prog_obs (by decide)

/-- `Log` printed, outside `Fail`. -/
theorem not_absorb_print_outside :
    ¬ CtxEq (S := σ) (Ψ := []) (Γ := []) (printLog (failDefault (.int 0) (logm (.s .z) 7 (raise .z))) : Prog σ .int)
      (printLog (failDefault (.int 0) (raise .z))) :=
  fun h => absurd h.prog_obs (by decide)

/-- `Log` run against a lent capability, the lend inside `Fail`: the abort's destructor writes
the borrowed state back, so the owner sees the log. -/
theorem not_absorb_runner_inside :
    ¬ CtxEq (S := σ) (Ψ := []) (Γ := [])
      (.bind (.newcap Eff.log .int coLog (.int 0))
        (.bind (failDefault (.inl (.int 0)) (.lend v0 (logm .z 7 (raise (.s .z)))))
          (.bind (.getcap v1) (.bind (.emit v0) (.ret (.int 0))))))
      (.bind (.newcap Eff.log .int coLog (.int 0))
        (.bind (failDefault (.inl (.int 0)) (.lend v0 (raise (.s .z))))
          (.bind (.getcap v1) (.bind (.emit v0) (.ret (.int 0)))))) :=
  fun h => absurd h.prog_obs (by decide)

/-- **Lent state survives an abort**: `Log` run against a lent capability outside `Fail`. This is
the sum for a borrowed capability: the lender keeps the state. -/
theorem lent_state_survives :
    ¬ CtxEq (S := σ) (Ψ := []) (Γ := [])
      (.bind (.newcap Eff.log .int coLog (.int 0))
        (.bind (.lend v0 (failDefault (.int 0) (logm (.s .z) 7 (raise .z))))
          (.bind (.getcap v1) (.bind (.emit v0) (.ret (.int 0))))))
      (.bind (.newcap Eff.log .int coLog (.int 0))
        (.bind (.lend v0 (failDefault (.int 0) (raise .z)))
          (.bind (.getcap v1) (.bind (.emit v0) (.ret (.int 0)))))) :=
  fun h => absurd h.prog_obs (by decide)

/-- Two printing `Log`s do not commute: the world sees the order. -/
theorem print_print_not_commute :
    ¬ CtxEq (S := σ) (Ψ := []) (Γ := [])
      (printLog (printLog (logm (.s .z) 1 (logm .z 2 (.ret (.int 0))))) : Prog σ .int)
      (printLog (printLog (logm .z 2 (logm (.s .z) 1 (.ret (.int 0)))))) :=
  fun h => absurd h.prog_obs (by decide)

/-! ## `ν/op` fails at a multi-shot operation

`ν b. op_a(v; y. M b) ≡ op_a(v; y. ν b. M b)`, with `M b` returning a predicate that tests an
instance against `b` and a function that applies a predicate to `b`. A handler of `a` that
resumes twice keeps the predicate of the first run and the function of the second, and applies
one to the other: on the left both runs share `b` (true); on the right each run has its own
(false). -/

def predT : VTy σ := .U Mode.unr Eb.top (.pi .log (.F (.g .bool)))
def appT : VTy σ := .U Mode.unr Eb.top (.arr predT Eb.top (.F (.g .bool)))

/-- The two closures over `b` (instance index 0). -/
def twoClosures {Γ : List (VTy σ)} : M [.log, .choose] Γ (.F (.prod predT appT)) :=
  .ret (.pair (.thunk Mode.unr (.ilam (.ieq (.s .z) .z)))
    (.thunk Mode.unr (.lam (.iapp (.force v0) .z))))

def nuOpL : M [.choose] [] (.F (.prod predT appT)) :=
  .nu .log (.op (.s .z) Op.choose .unit twoClosures)

def nuOpR : M [.choose] [] (.F (.prod predT appT)) :=
  .op .z Op.choose .unit (.nu .log twoClosures)

/-- Resume twice; keep the first run's predicate and the second run's function. -/
def chooseOps {Γ : List (VTy σ)} : (o : Op .choose) →
    M Ψ (kty (σ.q .choose o) Eb.top (σ.res .choose o) (.F (.prod predT appT)) :: .g (σ.arg .choose o) :: Γ)
      (.F (.prod predT appT))
  | .choose =>
      .bind (.app (.prj1 (.force v0)) (.bool true))
        (.bind (.app (.prj1 (.force v1)) (.bool false))
          (.split v1 (.split v2 (.ret (.pair (.var (.s (.s (.s .z)))) v0)))))

/-- The context: handle the hole's instance with `chooseOps`, then apply. -/
def nuOpCtx : Context σ [.choose] [] (.F (.prod predT appT)) .bool :=
  .bind (.handle .choose Eb.top (.ret v0) chooseOps (fun a => nomatch a) (.iapp (.force v0) .z))
    (.split v0 (.app (.force v0) v1))

theorem nuOp_obs : nuOpCtx.obs nuOpL.den = ⟨.ret (.bool true), []⟩ ∧
    nuOpCtx.obs nuOpR.den = ⟨.ret (.bool false), []⟩ := by decide

theorem nu_op_fails_multishot : ¬ CtxEq nuOpL nuOpR := fun h => by
  have := h .bool nuOpCtx
  rw [nuOp_obs.1, nuOp_obs.2] at this
  cases this

end EffRel
