import Frontend.Check.TExpr
import Core.ClauseOwn

/-!
# Frontend — Check — the clause kinds  `[spec §19]`

At `[handle]` the checker classifies each operation's clause from its typed term, and records
the kinds on the `handle` node (`TExpr.effHandleV`'s `ks`). The clauses are the components of the
node's own handler pair `(h_ret, hs)`: the elaboration writes them inline, so the node holds the
term the handler runs. A clause a program names by a `def` is the `def`'s body at the use (its
`use` node). A clause the node does not hold, a variable a program writes in core, is `stored`.

The classification reads the derivation: an abortive operation is one whose signature gives its
clause no `κ` (`clauseTy`); a control clause is `!thunkv λp. let (x, κ) = p; M`, and `M`'s paths
run through the rules `[⊕E]`, `[⊗E]`, `[1E]`, `[let]` and `[let]` at a row, to the uses of `κ`:
`[app]` of `[&E₁]` of `[force]` at `κ`'s slot, of the type `(B ⊸ F_Σ R) & C`, is its resume;
`[&E₂]` is its cancel; `[let]` of the resume whose body answers its variable is the resume under
the right unit; `[let]` of `return κ` is an alias of `κ`. A state-passing clause (§21) answers
`[thunkV]` of `λs. S`, and `S` resumes, then forces the answer at the type `St ⊸ F_Σ R` on the new
state. Where a use's absence matters, it is read off the premise's term (`mentions` of its
erasure).

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

/-- `t` is the resume of `κ` in the slot `k` in tail position (`resumeB`), or such a resume under
the right unit: `[let]` of it whose body answers its variable (`returns0B`). -/
def tailLeafB (k : Nat) : TExpr → Bool
  | t@(.bind _ _ _ _ _ tM tN) => resumeB k t || (tailLeafB k tM && returns0B tN)
  | t@(.effLet _ _ _ _ _ _ tM tN) => resumeB k t || (tailLeafB k tM && returns0B tN)
  | t => resumeB k t

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

/-- The erased term is the variable `k`. -/
def isVarB (k : Nat) : Expr → Bool
  | .var i => i == k
  | _ => false

/-- Every path of `t` ends in a leaf `leaf`, through `[⊕E]`, `[⊗E]`, `[1E]` and `[let]`, with `κ`
(the slot `k`) not used on the way; a `[let]` of `return κ` (through the nodes that keep their
premise's term, as `unbox`) moves `κ` to its binder's slot, its body not using the old one. -/
def onPaths (leaf : Nat → TExpr → Bool) : Nat → TExpr → Bool
  | k, t@(.sumE _ _ _ _ _ _ tV t₁ t₂) =>
      leaf k t || (!mentions k tV.erase && onPaths leaf (k + 1) t₁ && onPaths leaf (k + 1) t₂)
  | k, t@(.tensorE _ _ _ _ _ _ tV tM) =>
      leaf k t || (!mentions k tV.erase && onPaths leaf (k + 2) tM)
  | k, t@(.unitE _ _ _ _ tV tM) => leaf k t || (!mentions k tV.erase && onPaths leaf k tM)
  | k, t@(.bind _ _ _ _ _ tM tN) =>
      leaf k t || (!mentions k tM.erase && onPaths leaf (k + 1) tN) ||
        (isVarB k tM.erase && !mentions (k + 1) tN.erase && onPaths leaf 0 tN)
  | k, t@(.effLet _ _ _ _ _ _ tM tN) =>
      leaf k t || (!mentions k tM.erase && onPaths leaf (k + 1) tN) ||
        (isVarB k tM.erase && !mentions (k + 1) tN.erase && onPaths leaf 0 tN)
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
  if onPaths tailLeafB 0 tM then .tail
  else if onPaths (stateFnB stateLeafB) 0 tM then .tailState
  else if onPaths (fun k t => tailLeafB k t || cancelB k t) 0 tM then .resumeOrCancel false
  else if onPaths (stateFnB fun k t => stateLeafB k t || cancelB k t) 0 tM then .resumeOrCancel true
  else if onPaths onceB 0 tM then .resumeOnce false
  else if onPaths (stateFnB onceB) 0 tM then .resumeOnce true
  else .stored

/-- A `def`'s use nodes removed: the node of a `def` named in place of a value is the `def`'s
body, checked at the use, which is the term it erases to. -/
def TExpr.unUse : TExpr → TExpr
  | .use _ _ _ _ _ _ t => t.unUse
  | t => t

/-- **The kind of the clause `c` of the operation `o`**, with the operation's qualifier: abortive
when the signature gives the clause no `κ`; the kind of its body `M` when it is a control clause
`!thunkv λp. let (x, κ) = p; M`; otherwise `stored`. -/
def classifyClause (o : Count × VTy × VTy) (c : Option TExpr) : HKind :=
  ⟨o.1, if isAbortive o then .abortive else
    match c.map TExpr.unUse with
    | some (.bangThunkV _ _ _ (.lam _ _ _ _ (.tensorE _ _ _ _ _ _ (.var _ _ 0 _) tM))) =>
        classifyBody tM
    | _ => .stored⟩

/-- The components of a clause tuple `(c₀, (c₁, … ()))`, `n` of them: `[⊗I]`'s children. -/
def clauseParts : Nat → TExpr → List (Option TExpr)
  | 0, _ => []
  | n + 1, t => match t.unUse with
    | .tensorI _ _ _ _ _ c t => some c :: clauseParts n t
    | _ => List.replicate (n + 1) none

/-- The kinds of a handler's clauses, from the handler's pair `tH`, the `handle` node's own
`(h_ret, hs)`. -/
def classifyHandler (E : List (Count × VTy × VTy)) (tH : TExpr) : List HKind :=
  let parts := match tH with
    | .tensorI _ _ _ _ _ _ tc => clauseParts E.length tc
    | _ => List.replicate E.length none
  E.zipWith (fun o c => classifyClause o c) (parts ++ List.replicate E.length none)

/-! ### What a clause asks of its operation's count  `[spec §53]` -/

/-- **What a clause asks of its operation's count** (SPEC §53): `0` at an abortive operation (its
clause takes no `κ`); `1` when it resumes `κ` exactly once on every path, provided each operation
of `deps` is at `1`: the operations of the rows of the `[let]`s that hold `κ` across their bound
computation, each with the count the check gave it (`[let]`'s `hW`: at a row with an operation
with weakening, `κ` would have to drop); `1?` otherwise, for the reason `why`. -/
inductive Need where
  | zero
  | one (deps : List ((UInt32 × UInt32) × Count))
  | opt (why : String)
  deriving Inhabited, BEq

/-- `κ` in the slot `k` resumed or cancelled once on each path, a cancel nowhere: `onceB` with its
cancel leaf taken out. -/
def onceResumeB (k : Nat) : TExpr → Bool
  | .bind _ _ _ _ _ tM tN => onceResumeB k tM && !mentions (k + 1) tN.erase
  | .effLet _ _ _ _ _ _ tM tN => onceResumeB k tM && !mentions (k + 1) tN.erase
  | .effSub _ _ _ _ _ t => onceResumeB k t
  | t => resumeB k t

/-- **The operations a clause holds `κ` across**: along the paths `onPaths` reads, the operations
of the row of each `[let]` at a row whose body uses `κ` (the slot `k`), with their counts. -/
def liveDeps : Nat → TExpr → List ((UInt32 × UInt32) × Count)
  | k, .sumE _ _ _ _ _ _ _ t₁ t₂ => liveDeps (k + 1) t₁ ++ liveDeps (k + 1) t₂
  | k, .tensorE _ _ _ _ _ _ _ tM => liveDeps (k + 2) tM
  | k, .unitE _ _ _ _ _ tM => liveDeps k tM
  | k, .bind _ _ _ _ _ tM tN =>
      if isVarB k tM.erase then liveDeps 0 tN else liveDeps (k + 1) tN
  | k, .effLet _ _ _ _ S _ tM tN =>
      (if mentions (k + 1) tN.erase then S.map fun o => ((o.n, o.i), o.cnt) else []) ++
        (if isVarB k tM.erase then liveDeps 0 tN else liveDeps (k + 1) tN)
  | k, .effSub _ _ _ _ _ t => liveDeps k t
  | k, .ret _ _ _ (.thunkV _ _ _ (.lam _ _ _ _ tS)) => liveDeps (k + 1) tS
  | _, _ => []

/-- **What the clause `c` of the operation `o` asks of its count**: `0` at an abortive operation;
at a control clause, `1` when its kind resumes `κ` once on every path (`tail`, `tail+state`, or
`once` with no cancel), else `1?`; `1?` at a clause that may keep `κ`. -/
def clauseNeed (o : Count × VTy × VTy) (c : Option TExpr) : Need :=
  if isAbortive o then .zero else
    match c.map TExpr.unUse with
    | some (.bangThunkV _ _ _ (.lam _ _ _ _ (.tensorE _ _ _ _ _ _ (.var _ _ 0 _) tM))) =>
        match classifyBody tM with
        | .tail | .tailState => .one (liveDeps 0 tM)
        | .resumeOnce s =>
            if onPaths (if s then stateFnB onceResumeB else onceResumeB) 0 tM then .one (liveDeps 0 tM)
            else .opt "it cancels its continuation on a path"
        | .resumeOrCancel _ => .opt "it may cancel its continuation"
        | .abortive | .stored => .opt "it may keep its continuation"
    | _ => .opt "it may keep its continuation"

/-- What each clause of a handler asks of its operation's count, from the handler's pair `tH`. -/
def handlerNeeds (E : List (Count × VTy × VTy)) (tH : TExpr) : List Need :=
  let parts := match tH with
    | .tensorI _ _ _ _ _ _ tc => clauseParts E.length tc
    | _ => List.replicate E.length none
  E.zipWith (fun o c => clauseNeed o c) (parts ++ List.replicate E.length none)

/-! ### The names a clause's own code performs or raises -/

/-- **The names a clause's own code performs or raises** (`Expr.own`, SPEC §19 *The clause's
names in the continuation*): an abortive clause `λx. M`'s body's; a control clause
`λp. let (x, κ) = p; M`'s body's, `κ` its continuation slot. `none` where the clause may run code
it does not hold, or is not of its operation's shape. -/
def clauseNames (o : Count × VTy × VTy) (c : Expr) : Option (List UInt32) :=
  if isAbortive o then match c with
    | .lam M => M.own []
    | _ => none
  else match c with
    | .lam (.letpair (.var 0) M) => M.own [0]
    | _ => none

/-- The `j`-th component of a right-nested tuple of clauses. -/
def clauseExpr : Expr → Nat → Option Expr
  | .pair c _, 0 => some c
  | .pair _ r, j + 1 => clauseExpr r j
  | _, _ => none

/-- The clause the machine runs for the operation `j` (`BoLo.clauseAt`, at `[op]` and
`[unwind]`) is the tuple's component. -/
theorem clauseExpr_of_clauseAt : ∀ {hs : Expr} {j : Nat} {c : Val},
    BoLo.clauseAt hs j = some c → clauseExpr hs j = some c.1
  | .pair c' _, 0, c, h => by
      simp only [BoLo.clauseAt] at h
      split at h
      · cases h; rfl
      · cases h
  | .pair _ r, j + 1, c, h => by
      simp only [BoLo.clauseAt] at h
      exact clauseExpr_of_clauseAt (hs := r) h
  | .var _, _, _, h | .unit, _, _, h | .inj₁ _, _, _, h | .inj₂ _, _, _, h | .lam _, _, _, h
  | .loc _, _, _, h | .prim _, _, _, h | .seq .., _, _, h | .letpair .., _, _, h
  | .case .., _, _, h | .app .., _, _, h => by simp [BoLo.clauseAt] at h

/-- **The names of each clause of a handler** whose erasure is `H = (h_ret, hs)`: the clause the
machine runs for the operation `j` (`clauseExpr hs j`, `BoLo.clauseAt` at `[op]` and
`[unwind]`), read by `clauseNames`. -/
def handlerNames (E : List (Count × VTy × VTy)) (H : Expr) : List (Option (List UInt32)) :=
  match H with
  | .pair _ hs => ((List.range E.length).zip E).map fun (j, o) =>
      (clauseExpr hs j).bind (clauseNames o)
  | _ => E.map fun _ => none

/-! ### The handler sites of a typed term -/

/-- A `handle` node of a typed term: its source, its static name, its clauses' kinds, whether
its clauses receive `κ` boxed (BOXED-κ, §28), its site as the elaboration records it, the names of
its outer row and the frames its handled computation holds. At `effHandleV` and `effHandleVB` the kinds are the
checker's classification (`ks`); at `effHandleT` they are its rule's, `tail` or `abortive`
(`tailKind`), which `tailClause_premise` shows are the same `tail` kind; at `effHandleL` its rule's,
`resume-or-cancel` or `abortive` (§51). -/
structure HandleSite where
  sp : Frontend.Span
  n : UInt32
  ks : List HKind
  boxed : Bool
  site : Option HSite
  /-- The names of the handler's outer row `Σ`, the row its clauses run at. -/
  row : List UInt32
  /-- The frames its handled computation holds (`inside`). -/
  inside : HIn
  /-- The names each clause's own code performs or raises (`handlerNames`), at the clauses the
  node's erasure holds. -/
  names : List (Option (List UInt32))
  /-- What each clause asks of its operation's count (`handlerNeeds`).  `[spec §53]` -/
  needs : List Need := []
  /-- The lifetime its clauses receive `κ` boxed at (BOXED-κ), at `effHandleVB`. -/
  boxAt : Option Lifetime.Life := none
  deriving Inhabited

/-- Two `handle` nodes report alike when their sources, names, kinds and boxing agree. -/
instance : BEq HandleSite := ⟨fun a b => a.sp == b.sp && a.n == b.n && a.ks == b.ks && a.boxed == b.boxed⟩

/-- The `handle` nodes of `t`, in the order of the source, within the depth `fuel`: a node's
clauses, which are written before it, then the node, then its handled computation. -/
def TExpr.handleSites : Nat → TExpr → List HandleSite
  | 0, _ => []
  | f + 1, t =>
    let here : List HandleSite := match t with
      | .effHandleV i _ S E _ n _ _ _ ks st ins tc _ =>
          [⟨i.sp, n, ks, false, st, (S.map (·.n)).eraseDups, ins, handlerNames E tc.erase,
            handlerNeeds E tc, none⟩]
      | .effHandleVB i _ S E _ n _ _ d _ ks st ins tc _ =>
          [⟨i.sp, n, ks, true, st, (S.map (·.n)).eraseDups, ins, handlerNames E tc.erase,
            handlerNeeds E tc, some d⟩]
      -- `effHandleT`'s clauses are tail-resumptive by its rule (`tailClause_premise`), at rows of
      -- linear operations (`hLin`).
      | .effHandleT i _ S _ E _ n _ _ _ st ins tc _ =>
          [⟨i.sp, n, E.map tailKind, false, st, (S.map (·.n)).eraseDups, ins,
            handlerNames E (.pair (Expr.pairL tc.erase) (tailTuple E 0 (Expr.pairR tc.erase))),
            E.map fun o => if isAbortive o then .zero else .one [], none⟩]
      -- `effHandleL`'s clauses resume `κ` in tail position or cancel it (§51), at affine or abortive
      -- operations (`hAff`).
      | .effHandleL i _ S _ E _ _ n _ _ _ st ins tc _ =>
          [⟨i.sp, n, E.map fun o => ⟨o.1, if isAbortive o then .abortive else .resumeOrCancel false⟩,
            false, st, (S.map (·.n)).eraseDups, ins, E.map fun _ => none,
            E.map fun o => if isAbortive o then .zero else
              .opt "it may cancel its continuation ([handle-last])", none⟩]
      | _ => []
    match here, t.children with
    | _ :: _, (_, tc) :: rest =>
        TExpr.handleSites f tc ++ here ++ rest.flatMap fun (_, k) => TExpr.handleSites f k
    | _, ks => here ++ ks.flatMap fun (_, k) => TExpr.handleSites f k

/-- **The site kind the elaboration claims, against the clause kinds** at the `handle` nodes of
each name: a `for`'s site runs the loop's body as its clause, resumed or cancelled in place, so no
clause of it keeps `κ` (`stored`); a stored generator's site keeps `κ` as the rest of the
generator, so a clause of it does. The first name whose nodes contradict their site's claim, with
the claim. -/
def siteKindMismatch (hs : List HandleSite) : Option (HandleSite × String) :=
  hs.findSome? fun h => match h.site with
    | some s =>
      let nodes := hs.filter (·.n == h.n)
      let stored := nodes.any fun h' => h'.ks.any (·.kind == .stored)
      match s.kind with
      | .forSite => if stored then some (h, "a `for`'s site whose clause may keep `κ`") else none
      | .pullSite =>
          if stored then none else some (h, "a stored generator's site whose clauses keep no `κ`")
      | .handler => none
    | none => none

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
  s!"{n}.{i} {qualWord h.cnt.toQual} {h.kind.tag}"

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
      else s!"{op} {qualWord k.cnt.toQual}: {" / ".intercalate ((k :: ks).map (·.kind.describe))}")

end BoCa.Fig16.LogRel.Core.Check
