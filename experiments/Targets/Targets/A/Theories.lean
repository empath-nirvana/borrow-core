import Targets.A.UnaryLaws

/-!
# System A — theories: equations in signatures, handlers as models, comodels (D1.h3, D1.h4)

**Equations writable in signatures** (OQ-22 (a), D1.h4 (a)).  An equation of a label's signature
is two straight-line computations over the label's operations and the same parameters (`Eqn`).  A
straight-line computation performs operations one after another, each at an argument written over
the parameters and the answers so far (`VExpr`), and ends in the continuation applied to such a
value (`SLComp`).  A theory attaches equations to labels (`Theory`).  These are the algebraic
theories of Plotkin–Power (*Algebraic operations and generic effects*, 2003): each side is a term
over the operations with the continuation as its only computation variable.

**A handler as a model** (D1.h4 (b), Plotkin–Pretnar, *Handling algebraic effects*, 2013, Def.
4.5: "a handler is correct if … the interpretation of both sides of each equation is equal").  At
the answering class the handler is the state-passing handler of co-operations `co_j : S ⊗ A_j →
F(S ⊗ B_j)` (`ansHnd`, decision 59's state passing).  `AnsCorrect` reads Def. 4.5 at A's unary
equivalence `RunsAlike`: for each equation, each value of the parameters and of the state, and
each continuation, the two sides handled and run from the state run alike in every evaluation
context.  The continuation runs inside the handler, so it is handled too (Plotkin–Pretnar's
deep reading).

**A comodel** (D1.h3, Ahman–Bauer, *Runners in action*, 2020, Def. 1 with equations): the
co-operations' own runs validate each equation on the carrier: from each state and each value of
the parameters, the two sides' co-operation runs (`coRun`) reach one final state and one
continuation argument (`IsComodel`).  Ahman–Bauer Prop. 3 (a runner is determined by its
co-operations) is what makes a tail-resumptive handler's correctness fall on its co-operations,
D1.h4 (c): at our instance, `IsComodel` gives `AnsCorrect` for co-operations that run quietly
(`Targets/Instance/Theories.lean`, `ansCorrect_of_comodel`).

**Global state** is the first theory (`stateTheory`): `get : 1 ↠ T` and `put : T ↠ 1`, linear,
with Plotkin–Power's four laws of one location (lookup–lookup, lookup–update, update–update,
update–lookup).  `stateCo` is its comodel; `badPutCo`, whose `put` keeps the old state, is not.

Nothing here mentions our calculus.  A has no substitution, so a computation's parameters are
bound by `lets`, and a closed value (a co-operation, the start state) is written under binders it
does not mention, as A₂ writes such terms.
-/

namespace Targets.A

/-- A value written over an equation's parameters and the answers of its operations so far:
`res r` is the answer of the `r`-th operation (from `0`), `param p` the `p`-th parameter. -/
inductive VExpr
  | param (p : ℕ)
  | res (r : ℕ)
  | unit
  | pair (a b : VExpr)
  | inl (a : VExpr)
  | inr (a : VExpr)

/-- **A straight-line computation over one label's operations**: the `j`-th step performs the
operation of index `steps[j].1` at the argument `steps[j].2`; the computation ends in the
continuation, applied to `fin`. -/
structure SLComp where
  steps : List (ℕ × VExpr)
  fin   : VExpr

/-- **An equation of a signature**: two straight-line computations over the same parameters. -/
structure Eqn (Ty : Type) where
  params : List Ty
  lhs    : SLComp
  rhs    : SLComp

namespace EffectSystem

variable (S : EffectSystem)

/-- **A theory**: equations attached to each label's signature (OQ-22 (a)). -/
def Theory : Type := S.EA.Lab → List (Eqn S.Ty)

/-! ### Straight-line computations as terms -/

/-- A value expression after `j` operations, in a computation's layout: the answers so far
innermost (`res r` at `j - 1 - r`), then the parameters (`param p` at `j + p`), then the
continuation. -/
def vAt (j : ℕ) : VExpr → S.Val
  | .param p => S.var (j + p)
  | .res r => S.var (j - 1 - r)
  | .unit => S.unitV
  | .pair a b => S.pair (vAt j a) (vAt j b)
  | .inl a => S.inl (vAt j a)
  | .inr a => S.inr (vAt j a)

/-- The computation from its `j`-th step, at `np` parameters: `op_i a to x. …`, then `k fin`. -/
def slFrom (l : S.EA.Lab) (np : ℕ) (fin : VExpr) : List (ℕ × VExpr) → ℕ → S.Term
  | [], j => S.app (S.force (S.var (j + np))) (S.vAt j fin)
  | (i, a) :: rest, j => S.bind (S.perform l i (S.vAt j a)) (slFrom l np fin rest (j + 1))

/-- **A straight-line computation at the label `l`**, over `np` parameters (variables `0, …,
np - 1`) and the continuation (variable `np`). -/
def slTerm (l : S.EA.Lab) (np : ℕ) (c : SLComp) : S.Term := S.slFrom l np c.fin c.steps 0

/-! ### Straight-line computations run by co-operations -/

/-- A value expression after `j` co-operation calls, in the co-run's layout: each call binds its
answer pair and splits it into the new state and the answer (three variables), so the `r`-th
answer is at `3 (j - 1 - r)`; the start state and then the parameters are outermost. -/
def vAtCo (j : ℕ) : VExpr → S.Val
  | .param p => S.var (3 * j + 1 + p)
  | .res r => S.var (3 * (j - 1 - r))
  | .unit => S.unitV
  | .pair a b => S.pair (vAtCo j a) (vAtCo j b)
  | .inl a => S.inl (vAtCo j a)
  | .inr a => S.inr (vAtCo j a)

/-- The current state's variable after `j` co-operation calls. -/
def coState : ℕ → ℕ
  | 0 => 0
  | _ + 1 => 1

/-- The co-run from the `j`-th call: `co_i (s, a) to q. let (s', x) = q in …`, then
`ret (s, fin)`. -/
def coFrom (co : List S.Val) (fin : VExpr) : List (ℕ × VExpr) → ℕ → S.Term
  | [], j => S.ret (S.pair (S.var (coState j)) (S.vAtCo j fin))
  | (i, a) :: rest, j =>
      S.bind (S.app (S.force (co.getD i S.unitV)) (S.pair (S.var (coState j)) (S.vAtCo j a)))
        (S.split (S.var 0) (coFrom co fin rest (j + 1)))

/-- **A straight-line computation run by the co-operations `co`**, over the start state (variable
`0`) and the parameters (variables `1, 2, …`): it answers the final state and the continuation's
argument. -/
def coRun (co : List S.Val) (c : SLComp) : S.Term := S.coFrom co c.fin c.steps 0

/-! ### The answering handler of co-operations -/

/-- The clause of the co-operation `co`, decision 59's state passing:
`λ(a, κ). ret (λs. co (s, a) to q. let (s', b) = q in κ.resume b to f. f s')`. -/
def ansClause (co : S.Val) : S.Val :=
  S.lam (S.split (S.var 0) (S.ret (S.lam
    (S.bind (S.app (S.force co) (S.pair (S.var 0) (S.var 2)))
      (S.split (S.var 0)
        (S.bind (S.resume (S.var 4) (S.var 0)) (S.app (S.force (S.var 0)) (S.var 2))))))))

/-- The answer clause: `λr. ret (λs. ret (s, r))`. -/
def ansRet : S.Val := S.lam (S.ret (S.lam (S.ret (S.pair (S.var 0) (S.var 1)))))

/-- **The state-passing handler of the co-operations `co`.** -/
def ansHnd (co : List S.Val) : S.Hnd := S.hnd S.ansRet (co.map S.ansClause)

/-- **`M` handled by `ansHnd co` and run from the state `s₀`**: the handled computation answers a
state function, applied to `s₀`.  Its closing frame `□ to f. f s₀` is the clause's own, so that
after each operation the run is again `runAt` at the new state. -/
def runAt (l : S.EA.Lab) (co : List S.Val) (s₀ : S.Val) (M : S.Term) : S.Term :=
  S.bind (S.handle l (S.ansHnd co) M) (S.app (S.force (S.var 0)) s₀)

/-! ### Models and comodels -/

/-- **Handler correctness at the answering class** (Plotkin–Pretnar Def. 4.5, at `RunsAlike`):
for each equation of `l`, each continuation `k`, each value `vs` of the parameters and each state
`s₀` of the carrier `T`, the two sides handled by `ansHnd co` and run from `s₀` run alike.  The
continuation is bound outermost, so that it is under no binder of the parameters. -/
def AnsCorrect (th : S.Theory) (l : S.EA.Lab) (co : List S.Val) (T : S.Ty) : Prop :=
  ∀ eq ∈ th l, ∀ (vs : List S.Val) (k s₀ : S.Val), S.derV [] s₀ T →
    List.Forall₂ (S.derV []) vs eq.params →
    S.RunsAlike (S.runAt l co s₀ (S.lets (vs ++ [k]) (S.slTerm l eq.params.length eq.lhs)))
      (S.runAt l co s₀ (S.lets (vs ++ [k]) (S.slTerm l eq.params.length eq.rhs)))

/-- **A comodel** (Ahman–Bauer Def. 1 with equations): for each equation of `l`, each value of
the parameters and each state of the carrier `T`, the two sides' co-operation runs reach one
final state and one continuation argument. -/
def IsComodel (th : S.Theory) (l : S.EA.Lab) (co : List S.Val) (T : S.Ty) : Prop :=
  ∀ eq ∈ th l, ∀ (vs : List S.Val) (s : S.Val), S.derV [] s T →
    List.Forall₂ (S.derV []) vs eq.params →
    ∃ w, S.RunsTo S.R₀ (S.lets (s :: vs) (S.coRun co eq.lhs)) w [] ∧
      S.RunsTo S.R₀ (S.lets (s :: vs) (S.coRun co eq.rhs)) w []

/-! ### Global state -/

/-- `get : 1 ↠ T` and `put : T ↠ 1`, linear. -/
def stateSig (T : S.Ty) : List (OpSig S.Ty) := [⟨S.UnitT, T, .linear⟩, ⟨T, S.UnitT, .linear⟩]

/-- `get` then `get`, at `(x, y)`, is one `get` at `(x, x)`. -/
def eqnGG : Eqn S.Ty :=
  ⟨[], ⟨[(0, .unit), (0, .unit)], .pair (.res 0) (.res 1)⟩, ⟨[(0, .unit)], .pair (.res 0) (.res 0)⟩⟩

/-- `get` then `put` back is no operation. -/
def eqnGP : Eqn S.Ty := ⟨[], ⟨[(0, .unit), (1, .res 0)], .unit⟩, ⟨[], .unit⟩⟩

/-- `put s` then `put t` is `put t`. -/
def eqnPP (T : S.Ty) : Eqn S.Ty :=
  ⟨[T, T], ⟨[(1, .param 0), (1, .param 1)], .unit⟩, ⟨[(1, .param 1)], .unit⟩⟩

/-- `put s` then `get` is `put s`, answering `s`. -/
def eqnPG (T : S.Ty) : Eqn S.Ty :=
  ⟨[T], ⟨[(1, .param 0), (0, .unit)], .res 1⟩, ⟨[(1, .param 0)], .param 0⟩⟩

/-- **The four laws of global state** (Plotkin–Power, one location). -/
def stateEqns (T : S.Ty) : List (Eqn S.Ty) := [S.eqnGG, S.eqnGP, S.eqnPP T, S.eqnPG T]

open Classical in
/-- **The theory of global state**: the four laws at every label whose signature is state's. -/
noncomputable def stateTheory (T : S.Ty) : S.Theory :=
  fun l => if S.sig l = S.stateSig T then S.stateEqns T else []

/-- `get`'s co-operation: `λ(s, u). ret (s, s)`. -/
def getCo : S.Val := S.lam (S.split (S.var 0) (S.ret (S.pair (S.var 1) (S.var 1))))

/-- `put`'s co-operation: `λ(s, t). ret (t, ())`. -/
def putCo : S.Val := S.lam (S.split (S.var 0) (S.ret (S.pair (S.var 0) S.unitV)))

/-- **The comodel of global state.** -/
def stateCo : List S.Val := [S.getCo, S.putCo]

/-- A `put` that keeps the old state: `λ(s, t). ret (s, ())`. -/
def badPutCo : S.Val := S.lam (S.split (S.var 0) (S.ret (S.pair (S.var 1) S.unitV)))

/-- **Co-operations that are no comodel of state**: `put` forgets its argument. -/
def badStateCo : List S.Val := [S.getCo, S.badPutCo]

end EffectSystem

end Targets.A
