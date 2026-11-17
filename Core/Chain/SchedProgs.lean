import Core.Types
import Support.Model.Tree.World.Recs

/-!
# The scheduler programs the chain runs  `[spec §62]`

The spawn scheduler as closed programs: its handler `HS` (park, spawn, cancel and par clauses
over a stack of stored tasks), the operations a task performs (`parkE`, `spawnE`, `cancelE`), and
`progOf`, a root run under it. The chain's pool results (`Core/Chain/PoolSpawnN.lean`) and the
hardest case (`Core/Chain/HardestCase791.lean`) are about these programs. Also here: the records
a stored task carries (`StoredT`, `StoredJ`, `OpEntT`), which the scheduler's state is built from.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-- A world-indexed predicate over values at a step index, reading the list. -/
abbrev TVProp : Type := Nat → (w : TWd) → List (SRecT w.K) → Val → TRes w.K → Prop

/-- An operation's entry over the tree world. -/
structure OpEntT where
  q : Qual
  abort : Bool
  PA : TVProp
  /-- The answer, read at the payload. -/
  PBv : Val → TVProp
  /-- Whether the continuation's cancel branch is owed: at a cancellable entry (`q ≠ lin`), the
  unwinding `ccatch (K†[raise …])` is owed as a continuation, like a resume (`contShareT`). -/
  fin : Bool
  /-- What the resumer guarantees of the frame at the resume, read at the payload and at the
  records the resumed run owns there. -/
  fd : Val → (w : TWd) → List (FrameRecT w.K) → TRes w.K → Prop
  /-- What the stopped branch may own at the stop. -/
  oc : (w : TWd) → List (FrameRecT w.K) → Prop

/-- A postcondition over values. -/
abbrev TPostV : Type :=
  Nat → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → Val → TRes w.K → Prop

/-- **A stored task**: what its continuation `κ` answers (`Q`), its mask, its entry, the scheduler
it runs under (`H`), its index and payload. -/
structure StoredT where
  Q : TPostV
  M : BoCa.Loc → Prop
  en : OpEntT
  H : Val
  k : Nat
  v : Val
  κ : Val

/-- **A pool entry**: a stored task, whether it waits for the tasks above it (`join`), the lent
locations it shares with them (`sh`), and the tag the scheduler's code stores beside it. -/
structure StoredJ where
  t : StoredT
  join : Bool
  sh : BoCa.Loc → Prop
  tag : Val

/-- **The scheduler's state**: the stored entries, each its tag beside its continuation, as a list
value, `inj₁ ((tag, κ), rest)` or `inj₂ ()`. -/
def poolVal : List StoredJ → Val
  | [] => Val.inj₂ Val.unit
  | s :: ss => Val.inj₁ (Val.pair (Val.pair s.tag s.t.κ) (poolVal ss))

/-- **The scheduler's state**: its own handler value, so a clause can run a task under it (a new
task, or a stored task's cancel branch) without naming itself, and its stack. -/
def stateVal (H : Val) (ss : List StoredJ) : Val := Val.pair H (poolVal ss)

end BoCa.Fig16.Tree.Wp

namespace BoCa.Fig16.Tree.Wp.SchedProgs.Park

/-- The stepper's name. -/
abbrev nP : UInt32 := 3

end BoCa.Fig16.Tree.Wp.SchedProgs.Park

namespace BoCa.Fig16.Tree.Wp.SchedProgs.Stack
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.Tree.Wp

/-- The return clause's body under `λv. λs.`, and its first branch: the top's entry
`((tag, κ), s′)`, `κ` resumed with `(h, s′)`. -/
def retL : Expr :=
  .letpair (.var 0) (.letpair (.var 1)
    (.app (.app (.app (.var 0) (.inj₁ .unit)) .unit) (.pair (.var 6) (.var 2))))

def retBody : Expr := .letpair (.var 0) (.case (.var 0) retL (.var 4))

/-- `λv. λ(h, p). case p {inj₁ q. let (e, s′) = q in let (_, κ) = e in κ (inj₁ ()) () (h, s′) |
inj₂ _. v}`. -/
def stackRet : Val := Val.lam (.lam retBody)

/-- A substitution below a shift by more than its index undoes one step of the shift. -/
theorem subst_shift0' (d j : Nat) (s : Val) (e : Expr) (h : j ≤ d) :
    Expr.subst j s (Expr.shift (d + 1) 0 e) = Expr.shift d 0 e :=
  Expr.subst_shift d 0 j s e (Nat.zero_le _) (by omega)

end BoCa.Fig16.Tree.Wp.SchedProgs.Stack

namespace BoCa.Fig16.Tree.Wp.SchedProgs.Spawn
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack
open BoCa.BoLo (hndVal)

/-- The common prefix `λ(v, κ). λs. let (h, p) = s in b`. -/
def clauseOf (b : Expr) : Val := Val.lam (.letpair (.var 0) (.lam (.letpair (.var 0) b)))

/-- The stopped task as a ready entry, under `h, p, s, κ, v` and `n` more binders. -/
def readyE (n : Nat) : Expr := .pair (.inj₁ .unit) (.var (3 + n))

/-- `park`'s body: the top ready, `κ' (inj₁ ()) () (h, inj₁ ((inj₁ (), κ), p′))`; the top a
joiner or the stack empty, `κ (inj₁ ()) () (h, p)`. -/
def parkB : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.letpair (.var 1) (.case (.var 1)
      (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit)
        (.pair (.var 7) (.inj₁ (.pair (readyE 6) (.var 3)))))
      (.app (.app (.app (.var 9) (.inj₁ .unit)) .unit) (.pair (.var 7) (.var 6))))))
    (.app (.app (.app (.var 4) (.inj₁ .unit)) .unit) (.pair (.var 2) (.var 1)))

/-- `cancel`'s body: the top ready, `(hnd h (κ' (inj₂ ()))) (h, inj₁ ((inj₁ (), κ), p′))`;
otherwise `κ (inj₁ ()) () (h, p)`. -/
def cancelB : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.letpair (.var 1) (.case (.var 1)
      (.app (.app (.app (.prim .hnd) (.var 7)) (.app (.var 1) (.inj₂ .unit)))
        (.pair (.var 7) (.inj₁ (.pair (readyE 6) (.var 3)))))
      (.app (.app (.app (.var 9) (.inj₁ .unit)) .unit) (.pair (.var 7) (.var 6))))))
    (.app (.app (.app (.var 4) (.inj₁ .unit)) .unit) (.pair (.var 2) (.var 1)))

/-- `spawn`'s body: `(hnd h (th ())) (h, inj₁ ((inj₁ (), κ), p))`. -/
def spawnB : Expr :=
  .app (.app (.app (.prim .hnd) (.var 1)) (.app (.var 4) .unit))
    (.pair (.var 1) (.inj₁ (.pair (readyE 0) (.var 0))))

/-- The unstarted second child, under `th₂, th₁, p, h`: `λx. case x {inj₁ _. λ_. hnd h (th₂ ())
| inj₂ _. ()}`. -/
def kUB : Expr :=
  .lam (.case (.var 0) (.lam (.app (.app (.prim .hnd) (.var 6)) (.app (.var 3) .unit))) .unit)

/-- `par`'s body: `let (th₁, th₂) = v in (hnd h (th₁ ())) (h, inj₁ ((inj₁ (), κU), inj₁ ((inj₂ (),
κ), p)))`. -/
def parB : Expr :=
  .letpair (.var 4) (.app (.app (.app (.prim .hnd) (.var 3)) (.app (.var 1) .unit))
    (.pair (.var 3) (.inj₁ (.pair (.pair (.inj₁ .unit) kUB)
      (.inj₁ (.pair (.pair (.inj₂ .unit) (.var 5)) (.var 2)))))))

def parkCl : Val := clauseOf parkB
def spawnCl : Val := clauseOf spawnB
def cancelCl : Val := clauseOf cancelB
def parCl : Val := clauseOf parB

def qsS : Val :=
  Val.pair (Val.i32 1) (Val.pair (Val.i32 1) (Val.pair (Val.i32 1) (Val.pair (Val.i32 0) Val.unit)))
def hsS : Val := Val.pair parkCl (Val.pair spawnCl (Val.pair cancelCl (Val.pair parCl Val.unit)))
def HS : Val := hndVal nP qsS stackRet hsS

/-- A substitution below a shift by more than its index undoes one step of the shift. -/
theorem subst_shift0 (d j : Nat) (s : Val) (e : Expr) (h : j ≤ d) :
    Expr.subst j s (Expr.shift (d + 1) 0 e) = Expr.shift d 0 e :=
  Expr.subst_shift d 0 j s e (Nat.zero_le _) (by omega)

end BoCa.Fig16.Tree.Wp.SchedProgs.Spawn

namespace BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa.Fig16.Tree.Wp.SchedProgs.Spawn
open BoCa.BoLo (performE opPayload hndE)

def parkE : Expr := performE (.val (opPayload nP 0 Val.unit))
def cancelE : Expr := performE (.val (opPayload nP 2 Val.unit))
def spawnE (th : Val) : Expr := performE (.val (opPayload nP 1 th))

/-- `(hnd HS root) (HS, [])`. -/
def progOf (root : Expr) : Expr := .app (hndE HS root) (stateVal HS []).1

end BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs

end
