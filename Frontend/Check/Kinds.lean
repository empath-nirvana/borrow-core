import Frontend.Check.TExpr

/-!
# Frontend — Check — the clause kinds  `[spec §19]`

At `[handle]` the checker classifies each operation's clause from its typed term, and records
the kinds on the `handle` node (`TExpr.effHandleV`'s `ks`). The clauses are the components of the
value the handler's clauses variable is bound to, which the checker checked there
(`Frontend/Check/Checker.lean`, `Env.vals`).

The classification reads the derivation: an abortive operation is one whose signature gives its
clause no `κ` (`clauseTy`); a control clause is `!thunkv λp. let (x, κ) = p; M`, and `M`'s paths
run through the rules `[⊕E]`, `[⊗E]`, `[1E]`, `[let]` and `[let]` at a row, to the uses of `κ`:
`[app]` of `[&E₁]` of `[force]` at `κ`'s slot, of the type `(B ⊸ F_Σ R) & C`, is its resume;
`[&E₂]` is its cancel. A state-passing clause (§21) answers `[thunkV]` of `λs. S`, and `S` resumes,
then forces the answer at the type `St ⊸ F_Σ R` on the new state. Where a use's absence matters,
it is read off the premise's term (`mentions` of its erasure).

`classify_sound`: each kind the classifier returns gives the premise of that kind's law
(`ClauseKind.Premise`, `Core/ClauseKinds.lean`) at the clause's erasure, the term the handler
runs.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.ClauseKinds

/-! ### Uses of `κ` -/

/-- `[sub]` at a row (`effSub`), which keeps its premise's term, removed. -/
def TExpr.unSub : TExpr → TExpr
  | .effSub _ _ _ _ _ t => t.unSub
  | t => t

/-- `t` is the resume of `κ` in the slot `k` applied to an answer that is not `κ`: `[app]` of
`[&E₁]` of `[force]` at the slot, of a `&` type. -/
def resumeB (k : Nat) (t : TExpr) : Bool :=
  match t.unSub with
  | .app _ _ y _ _ _ (.proj₁ _ _ _ _ (.force _ _ i (.amp _ _))) => i == k && y != k
  | _ => false

/-- `t` is the cancel of `κ` in the slot `k`: `[&E₂]` of `[force]` at the slot. -/
def cancelHeadB (k : Nat) (t : TExpr) : Bool :=
  match t.unSub with
  | .proj₂ _ _ _ _ (.force _ _ i (.amp _ _)) => i == k
  | _ => false

/-- `t` cancels `κ`, then goes on without it: `[let]` whose bound computation is the cancel. -/
def cancelB (k : Nat) : TExpr → Bool
  | .bind _ _ _ _ _ tM tN => cancelHeadB k tM && !mentions (k + 1) tN.erase
  | .effLet _ _ _ _ _ _ tM tN => cancelHeadB k tM && !mentions (k + 1) tN.erase
  | _ => false

/-- `t` answers its variable `0`, through `[let]`s of `return x` that rebind it. -/
def returns0B : TExpr → Bool
  | .ret _ _ _ (.var _ _ 0 _) => true
  | .bind _ _ _ _ _ tM tN => isVar0 tM.unSub && returns0B tN
  | .effLet _ _ _ _ _ _ tM tN => isVar0 tM.unSub && returns0B tN
  | .effSub _ _ _ _ _ t => returns0B t
  | _ => false
where
  isVar0 : TExpr → Bool
    | .ret _ _ _ (.var _ _ 0 _) => true
    | _ => false

/-- `t` is `[force]` at the slot `g`, of a `⊸` type. -/
def forceArrB (g : Nat) (t : TExpr) : Bool :=
  match t.unSub with
  | .force _ _ i (.arr _ _) => i == g
  | _ => false

/-- `t` applies the state function in the slot `g` to the new state in tail position, using
neither it nor `κ` (the slot `k`) before: `[app]` of `[force]` at `g`, of a `⊸` type. -/
def appliesB : Nat → Nat → TExpr → Bool
  | g, k, .app _ _ s _ _ _ f => forceArrB g f && s != g && s != k
  | g, k, .effSub _ _ _ _ _ t => appliesB g k t
  | g, k, .bind _ _ _ _ _ tM tN =>
      (!mentions g tM.erase && !mentions k tM.erase && appliesB (g + 1) (k + 1) tN) ||
        (appliesB g k tM && returns0B tN)
  | g, k, .effLet _ _ _ _ _ _ tM tN =>
      (!mentions g tM.erase && !mentions k tM.erase && appliesB (g + 1) (k + 1) tN) ||
        (appliesB g k tM && returns0B tN)
  | _, _, _ => false

/-- The state-passing resume in tail position: `[let]` of the resume, then its answer applied to
the new state (`appliesB`). -/
def stateLeafB (k : Nat) : TExpr → Bool
  | .bind _ _ _ _ _ tM tN => resumeB k tM && appliesB 0 (k + 1) tN
  | .effLet _ _ _ _ _ _ tM tN => resumeB k tM && appliesB 0 (k + 1) tN
  | _ => false

/-- `κ` used once, by its resume or its cancel in evaluation position: the use itself, or the
bound computation of a `[let]` whose body does not use `κ`. -/
def onceB (k : Nat) : TExpr → Bool
  | .bind _ _ _ _ _ tM tN => onceB k tM && !mentions (k + 1) tN.erase
  | .effLet _ _ _ _ _ _ tM tN => onceB k tM && !mentions (k + 1) tN.erase
  | .effSub _ _ _ _ _ t => onceB k t
  | t => resumeB k t || cancelHeadB k t

/-! ### Paths -/

/-- Every path of `t` ends in a leaf `leaf`, through `[⊕E]`, `[⊗E]`, `[1E]` and `[let]`, with `κ`
(the slot `k`) not used on the way. -/
def onPaths (leaf : Nat → TExpr → Bool) : Nat → TExpr → Bool
  | k, t@(.sumE _ _ _ _ _ _ tV t₁ t₂) =>
      leaf k t || (!mentions k tV.erase && onPaths leaf (k + 1) t₁ && onPaths leaf (k + 1) t₂)
  | k, t@(.tensorE _ _ _ _ _ _ tV tM) =>
      leaf k t || (!mentions k tV.erase && onPaths leaf (k + 2) tM)
  | k, t@(.unitE _ _ _ _ tV tM) => leaf k t || (!mentions k tV.erase && onPaths leaf k tM)
  | k, t@(.bind _ _ _ _ _ tM tN) =>
      leaf k t || (!mentions k tM.erase && onPaths leaf (k + 1) tN)
  | k, t@(.effLet _ _ _ _ _ _ tM tN) =>
      leaf k t || (!mentions k tM.erase && onPaths leaf (k + 1) tN)
  | k, t@(.effSub _ _ _ _ _ t') => leaf k t || onPaths leaf k t'
  | k, t => leaf k t

/-- The clause answers the state-passing function `[thunkV]` of `λs. S`, and `S`'s paths end in
`leaf`. -/
def stateFnB (leaf : Nat → TExpr → Bool) (k : Nat) : TExpr → Bool
  | .ret _ _ _ (.thunkV _ _ _ (.lam _ _ _ _ tS)) => onPaths leaf (k + 1) tS
  | _ => false

/-! ### The classifier -/

/-- The kind of a control clause's body `M`, `κ` in its slot `0`: the first kind whose premise
the paths meet, from the most particular. -/
def classifyBody (tM : TExpr) : ClauseKind :=
  if onPaths resumeB 0 tM then .tail
  else if onPaths (stateFnB stateLeafB) 0 tM then .tailState
  else if onPaths (fun k t => resumeB k t || cancelB k t) 0 tM then .resumeOrCancel false
  else if onPaths (stateFnB fun k t => stateLeafB k t || cancelB k t) 0 tM then .resumeOrCancel true
  else if onPaths onceB 0 tM then .resumeOnce false
  else if onPaths (stateFnB onceB) 0 tM then .resumeOnce true
  else .stored

/-- A control clause `!thunkv λp. let (x, κ) = p; M`: its body `M`. -/
def clauseBody? : TExpr → Option TExpr
  | .bangThunkV _ _ _ (.lam _ _ _ _ (.tensorE _ _ _ _ _ _ (.var _ _ 0 _) tM)) => some tM
  | _ => none

/-- **The kind of the clause `c` of the operation `o`**, with the operation's qualifier: abortive
when the signature gives the clause no `κ`; otherwise the kind of its body, or `stored` when the
clause is not in reach or not of the clause's form. -/
def classifyClause (o : Qual × VTy × VTy) (c : Option TExpr) : HKind :=
  ⟨o.1, if isAbortive o then .abortive else
    match c.bind clauseBody? with
    | some tM => classifyBody tM
    | none => .stored⟩

/-- The components of a clause tuple `(c₀, (c₁, … ()))`, `n` of them: `[⊗I]`'s children, through
the nodes that keep their premise's term. -/
def clauseParts : Nat → TExpr → List (Option TExpr)
  | 0, _ => []
  | n + 1, .tensorI _ _ _ _ _ c t => some c :: clauseParts n t
  | n + 1, .ret _ _ _ t => clauseParts (n + 1) t
  | n + 1, _ => List.replicate (n + 1) none

/-- The kinds of a handler's clauses, from the typed term its clauses variable is bound to. -/
def classifyHandler (E : List (Qual × VTy × VTy)) (cls : Option TExpr) : List HKind :=
  let parts := match cls with
    | some t => clauseParts E.length t
    | none => List.replicate E.length none
  E.zipWith (fun o c => classifyClause o c) (parts ++ List.replicate E.length none)

/-! ### The handler sites of a typed term -/

/-- A `handle` node of a typed term: its source, its static name, its clauses' kinds, and whether
its clauses receive `κ` boxed (BOXED-κ, §28). At `effHandleV` and `effHandleVB` the kinds are the
checker's classification (`ks`); at `effHandleT` they are its rule's, `tail` or `abortive`
(`tailKind`), which `tailClause_premise` shows are the same `tail` kind. -/
structure HandleSite where
  sp : Frontend.Span
  n : UInt32
  ks : List HKind
  boxed : Bool
  deriving DecidableEq, Inhabited

/-- The `handle` nodes of `t`, outermost first, within the depth `fuel`. -/
def TExpr.handleSites : Nat → TExpr → List HandleSite
  | 0, _ => []
  | f + 1, t =>
    let here : List HandleSite := match t with
      | .effHandleV i _ _ _ _ n _ _ _ ks _ _ => [⟨i.sp, n, ks, false⟩]
      | .effHandleVB i _ _ _ _ n _ _ _ _ ks _ _ => [⟨i.sp, n, ks, true⟩]
      -- `effHandleT`'s clauses are tail-resumptive by its rule (`tailClause_premise`).
      | .effHandleT i _ _ _ _ _ E _ n _ _ _ _ _ => [⟨i.sp, n, E.map tailKind, false⟩]
      | _ => []
    here ++ t.children.flatMap fun (_, k) => TExpr.handleSites f k

/-- The qualifier as SPEC writes it. -/
def qualWord : Qual → String
  | .lin => "linear"
  | .aff => "affine"
  | .unr => "unrestricted"

/-- What a kind says of its clause, for the reports. -/
def _root_.BoCa.Fig16.LogRel.Core.ClauseKinds.ClauseKind.describe : ClauseKind → String
  | .abortive => "abortive: a branch per call (final ctl)"
  | .tail => "tail-resumptive on every path"
  | .tailState => "tail-resumptive on every path, with the handler's state"
  | .resumeOrCancel s => "resumed in tail position or cancelled on each path" ++
      (if s then ", with the handler's state" else "")
  | .resumeOnce s => "resumed or cancelled once on each path, not all in tail position" ++
      (if s then ", with the handler's state" else "")
  | .stored => "its continuation may be kept"

/-- The kind's name, for `bcc kinds`. -/
def _root_.BoCa.Fig16.LogRel.Core.ClauseKinds.ClauseKind.tag : ClauseKind → String
  | .abortive => "abortive"
  | .tail => "tail"
  | .tailState => "tail+state"
  | .resumeOrCancel s => "resume-or-cancel" ++ (if s then "+state" else "")
  | .resumeOnce s => "once" ++ (if s then "+state" else "")
  | .stored => "stored"

/-- The operation `n.i`'s clause, for `bcc kinds`. -/
def _root_.BoCa.Fig16.LogRel.Core.ClauseKinds.HKind.render (n : UInt32) (i : Nat) (h : HKind) : String :=
  s!"{n}.{i} {qualWord h.q} {h.kind.tag}"

/-- A handler site's operations as the report says them, from the kinds of the `handle` nodes of
its static name `n` among `hs`: each operation with its qualifier and its clause's kind, one kind
per distinct kind at those nodes, in the term's order, separated by ` / `. -/
def siteOps (hs : List HandleSite) (n : Nat) (ops : List String) : String :=
  let nodes := hs.filter (·.n.toNat == n)
  ", ".intercalate (((List.range ops.length).zip ops).map fun (j, op) =>
    match (nodes.filterMap (·.ks[j]?)).eraseDups with
    | [] => s!"{op}: in no checked term"
    | k :: ks =>
      if k.kind == .abortive && ks.isEmpty then s!"{op} {k.kind.describe}"
      else s!"{op} {qualWord k.q}: {" / ".intercalate ((k :: ks).map (·.kind.describe))}")

end BoCa.Fig16.LogRel.Core.Check
