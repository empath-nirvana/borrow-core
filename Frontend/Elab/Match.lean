import Frontend.Elab.Meta

/-!
# Frontend — Elab — matching a type against a pattern  `[#54, docs/typed-elaboration.md §2.2]`

First-order matching of a type against a pattern whose placeholders are type parameters, used by
the typed elaboration for generic calls (`Frontend/Sugar.lean`) and by the effects pass for the
type arguments of an operation and of a generic call (`Frontend/Elab/Instances.lean`).
-/

namespace Frontend.Sugar
open Frontend.Elab (TCx)
open Frontend.Check (CVTy CCTy)

/-! #### Generic calls

A call's callee may be generic in three ways, and the elaborator fills what the call leaves out
(typed elaboration §2.2–§2.3):

* **A template**: a `fn f[A, …](…)`. It is not elaborated as written, and
  a call of it is a call of its instance at the types of the call, the template with the types
  substituted for its parameters (`Frontend/Elab/Subst.lean`), made and elaborated on first use
  (whole-program monomorphization, as Rust's generics). Its body is elaborated at the instance's
  types, so an operation that needs a persistent element (`*g`) is accepted at `u8` and rejected
  at a type that is not.
* **A `def` with type parameters** written in core, `def f[A, …] : …`: its call is `f[T, …]`,
  checked at each use by the checker.
* **Lifetime parameters**, `!(all 'a < @. all 'b < @'. P => Q)`: its call is
  `(unbang f) ['x] ['y]`.

The type arguments are written, `f[T, …](…)`, or read off the arguments' types by first-order
matching against the parameter's type, in which each type parameter is a placeholder; what the
arguments leave open is matched against the type expected of the call's result. Each lifetime
parameter is read off the argument whose type mentions it; when two arguments give it different
lifetimes, it is their meet, and an argument that is a borrow is shortened to it with `:>` (§2.3;
there is no other solving). A closure argument whose parameter's type is a hole, and an
injection, are typed last, from the parameter's type with what the other arguments determined. -/

/-- The placeholders of type parameters in a pattern: type variables no type of a program has. -/
def phBase : Nat := 1 <<< 24

/-- What matching has found: the type parameters, by placeholder; the lifetime parameters of the
call (`binders`), with the lifetime each is matched with; and those matched with two lifetimes. -/
structure MatchSt where
  ty : Array (Option CVTy)
  binders : List BoCa.Lifetime.LifeVar := []
  life : List (BoCa.Lifetime.LifeVar × BoCa.Lifetime.Life) := []
  conflicts : List BoCa.Lifetime.LifeVar := []

/-- `l` is `a`, or one of the lifetimes `a` is the meet of. -/
def inMeet (l : BoCa.Lifetime.Life) : BoCa.Lifetime.Life → Bool
  | .meet a b => l == .meet a b || inMeet l a || inMeet l b
  | a => l == a

/-- The lifetime `a'` of an argument where the pattern has `a`: a lifetime parameter of the call is
matched with it, or with the meet of it and what it was matched with before. -/
def matchLife (m : MatchSt) (a a' : BoCa.Lifetime.Life) : MatchSt :=
  match a with
  | .var v =>
    if !m.binders.contains v then m else
    match m.life.lookup v with
    | none => { m with life := (v, a') :: m.life }
    | some l => if inMeet a' l then m else
      { m with life := (v, .meet l a') :: m.life.filter (·.1 != v), conflicts := v :: m.conflicts }
  | _ => m

mutual
/-- `t` matches the pattern `p`, whose placeholders are bound in `m`, under `d` binders of type
variables (`μ`, `ν`), which shift a placeholder's index by `d`. A lifetime of the pattern that is
not a lifetime parameter of the call matches any lifetime: the checker decides it. -/
def matchV (m : MatchSt) (d : Nat) : CVTy → CVTy → Option MatchSt
  | .tvar i, t =>
    if i ≥ phBase + d then match m.ty[i - phBase - d]? with
      | some (some u) => if u = t then some m else none
      | some none => some { m with ty := m.ty.set! (i - phBase - d) (some t) }
      | none => none
    else if t = .tvar i then some m else none
  | .tensor A B, .tensor A' B' | .sum A B, .sum A' B' => (matchV m d A A').bind (matchV · d B B')
  | .thunk C, .thunk C' => matchC m d C C'
  | .mu A, .mu A' => matchV m (d + 1) A A'
  | .ref A, .ref A' | .bang A, .bang A' | .fam A, .fam A' => matchV m d A A'
  | .imm a A, .imm a' A' | .mut a A, .mut a' A' | .box a A, .box a' A' =>
    matchV (matchLife m a a') d A A'
  | p, t => if p = t then some m else none

/-- `t` matches the computation-type pattern `p`. -/
def matchC (m : MatchSt) (d : Nat) : CCTy → CCTy → Option MatchSt
  | .ret A, .ret A' => matchV m d A A'
  | .arr A C, .arr A' C' => (matchV m d A A').bind (matchC · d C C')
  | .amp C D, .amp C' D' => (matchC m d C C').bind (matchC · d D D')
  | .nu C, .nu C' => matchC m (d + 1) C C'
  | .all _ _ C, .all _ _ C' => matchC m d C C'
  | .eff n i q A B fin cg C, .eff n' i' q' A' B' fin' cg' C' =>
    if n == n' && i == i' && q == q' && cg == cg' then
      (matchV m d A A').bind fun m => (matchV m d B B').bind fun m =>
        (matchC m d fin fin').bind (matchC · d C C')
    else none
  | p, t => if p = t then some m else none
end

mutual
/-- A pattern with placeholders. -/
def hasPhV : CVTy → Bool
  | .tvar i => i ≥ phBase
  | .tensor A B | .sum A B => hasPhV A || hasPhV B
  | .thunk C => hasPhC C
  | .ref A | .bang A | .mu A | .fam A | .imm _ A | .mut _ A | .box _ A => hasPhV A
  | _ => false

def hasPhC : CCTy → Bool
  | .ret A => hasPhV A
  | .arr A C => hasPhV A || hasPhC C
  | .amp C D => hasPhC C || hasPhC D
  | .nu C | .all _ _ C => hasPhC C
  | .top => false
  | .eff _ _ _ A B fin _ C => hasPhV A || hasPhV B || hasPhC fin || hasPhC C
end

mutual
/-- A pattern with its solved placeholders replaced, under `d` binders of type variables. The
types solved are closed, so they need no shift. -/
def solvedV (σ : Array (Option CVTy)) (d : Nat) : CVTy → CVTy
  | .tvar i => if i ≥ phBase + d then ((σ[i - phBase - d]?).join).getD (.tvar i) else .tvar i
  | .tensor A B => .tensor (solvedV σ d A) (solvedV σ d B)
  | .sum A B => .sum (solvedV σ d A) (solvedV σ d B)
  | .thunk C => .thunk (solvedC σ d C)
  | .ref A => .ref (solvedV σ d A)
  | .bang A => .bang (solvedV σ d A)
  | .mu A => .mu (solvedV σ (d + 1) A)
  | .fam A => .fam (solvedV σ d A)
  | .imm a A => .imm a (solvedV σ d A)
  | .mut a A => .mut a (solvedV σ d A)
  | .box a A => .box a (solvedV σ d A)
  | t => t

def solvedC (σ : Array (Option CVTy)) (d : Nat) : CCTy → CCTy
  | .ret A => .ret (solvedV σ d A)
  | .arr A C => .arr (solvedV σ d A) (solvedC σ d C)
  | .amp C D => .amp (solvedC σ d C) (solvedC σ d D)
  | .nu C => .nu (solvedC σ (d + 1) C)
  | .all v b C => .all v b (solvedC σ d C)
  | .top => .top
  | .eff n i q A B fin cg C =>
      .eff n i q (solvedV σ d A) (solvedV σ d B) (solvedC σ d fin) cg (solvedC σ d C)
end

/-- A pattern with what matching found: its placeholders and its lifetime parameters solved. -/
def MatchSt.solved (m : MatchSt) (P : CVTy) : CVTy := (solvedV m.ty 0 P).applyLSub m.life

/-- The pattern, solved as far as matching has gone, still has an unknown: a placeholder, or a
lifetime parameter not yet matched. -/
def MatchSt.isOpen (m : MatchSt) (P : CVTy) : Bool :=
  let P' := m.solved P
  hasPhV P' || m.binders.any fun v => BoCa.Fig16.LogRel.Core.Check.vfreeB v P'

/-- The parameter type of a written function type, `!(all 'a < @. … P => Q)`. -/
def paramTy : VTy → Option VTy
  | .bang _ A | .all _ _ _ A => paramTy A
  | .lolli _ P _ | .thunk _ (.arr _ P _) => some P
  | _ => none

/-- The components of an argument against a written parameter type, as `compsC`. -/
def argComps : VTy → Val → List (VTy × Val)
  | .tensor _ P Q, .pair _ V W => (P, V) :: argComps Q W
  | P, W => [(P, W)]

/-- A type as a pattern: the type parameters `ps` as placeholders. -/
def patOf (c : TCx) (ps : List String) (P : VTy) : Option CVTy :=
  ({ c.E with tps := ps.zipIdx.map fun (x, k) => (x, .tvar (phBase + k)) }.elabV c.Δ P).toOption

/-- Why `patOf` fails, for messages. -/
def patErr (c : TCx) (ps : List String) (P : VTy) : String :=
  match ({ c.E with tps := ps.zipIdx.map fun (x, k) => (x, .tvar (phBase + k)) }.elabV c.Δ P) with
  | .error e => s!": {e.msg}"
  | .ok _ => ""

end Frontend.Sugar
