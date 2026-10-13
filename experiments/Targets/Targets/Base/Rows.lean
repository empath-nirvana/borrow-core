import Core.EffBorrow

/-!
# Base — rows, row variables, row contexts, effect contexts (RESTRUCTURE §0, base)

Core's rows as B, I and the Instance read them (DESIGN D1, D4):
`RVar`, `Row.NU` (no resuming `unr` operation, decision 63), `RowClass`, `RowCon`, `RowCtx`,
`RowEnv`, `RowCtx.Models`, `EffCtx`, `RowEq`, `Row.Has`; the frozen finalisers of a context
(`Kont.fins`) and the cancel branch (`cancelOf`).  The effect algebra is A's
(`Targets/A/EffAlg.lean`); the row forms are the Instance's (`Targets/Instance/Rows.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont hndE raiseE cancelVal ccatchE)

/-- A row variable. -/
abbrev RVar := Nat

/-- No operation the row's lookup finds is a resuming `unr` one (decision 63: the end state is
stated over the unr-free fragment).  Read through `Row.find`, as the row's protocol reads it. -/
def Row.NU (S : Row) : Prop := ∀ n i o, Row.find S n i = some o → o.abort = true ∨ o.q ≠ .unr

/-- The class of operations a row admits.  `.any` is every unr-free row. -/
inductive RowClass
  | abortive
  | resumeOnce
  | any
  deriving DecidableEq, Repr

/-- The rows of a class. -/
def RowClass.Admits : RowClass → Row → Prop
  | .abortive,   S => ∀ o ∈ S, o.abort = true
  | .resumeOnce, S => ∀ o ∈ S, o.abort = true ∨ o.q = .lin
  | .any,        S => Row.NU S

/-- The constraint a row variable carries: the class of its operations, and an admissibility
condition on each operation (OQ-56's question, at a row variable). -/
structure RowCon where
  cls : RowClass
  adm : OpSig → Prop

/-- A row context: the row variables in scope with their constraints. -/
abbrev RowCtx := List (RVar × RowCon)

/-- A row environment: each row variable is a closed row. -/
abbrev RowEnv := RVar → Row

/-- `η` is an admissible instance of `Θ`. -/
def RowCtx.Models (Θ : RowCtx) (η : RowEnv) : Prop :=
  ∀ ρ c, (ρ, c) ∈ Θ → c.cls.Admits (η ρ) ∧ ∀ o ∈ η ρ, c.adm o

/-- An effect context: each name's signature, its operations numbered from `0`. -/
abbrev EffCtx := UInt32 → List (Qual × VTy × VTy)

/-- Two rows with the same operations: equal first-match lookup. -/
def RowEq (S S' : Row) : Prop := ∀ n i, Row.find S n i = Row.find S' n i

/-- The row has the operation `i` of the name `n`. -/
def Row.Has (S : Row) (n i : UInt32) : Prop := (Row.find S n i).isSome

/-- The finalisers of `K`'s `[then]` frames (`ubind (N, D)`), innermost first.  In `.appR f K` the
frame `f` is outside `K`. -/
def _root_.BoCa.BoLo.Kont.fins : Kont → List Expr
  | .hole => []
  | .appR f K => K.fins ++ (match f with
      | .app (.prim .ubind) (.pair _ D) => [D]
      | _ => [])
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.fins

/-- The cancel branch of `κ = kappa n H K` after its three administrative steps. -/
def cancelOf (n : UInt32) (H : Val) (K : Kont) : Expr :=
  ccatchE (hndE H (K.plug (raiseE (.val (cancelVal (n :: K.hndNames) none)))))

end Targets

end
