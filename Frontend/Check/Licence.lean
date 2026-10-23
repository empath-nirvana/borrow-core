import Frontend.Check.Kinds
import Frontend.Check.Decide
import Core.HandledNames
import Core.Fix

/-!
# Frontend — Check — the tail-resuming rule's licence  `[spec §47, §54]`

**The licence** (SPEC §47, recomputed for R1, SPEC §54): a name `n` is admitted when every
`handle` node of `n` in the checked terms

- is the tail-resuming rule's (`effHandleT`): the checker classified its every clause `tail` and
  the rule's premises accept the works written from them (`Frontend/Check/Checker.lean`);
- holds no abortive operation;
- is at one outer row `Σ`, one row `Σ_N` of its works, and one signature `E`;
- holds one tuple of works written in place, equal at every node, each closed (`closedAt 0`), at
  the empty row `Σ_N = []`: a work performs nothing, the scope of the per-perform law
  `tail_resume_direct` and of `obl_tV`;
- holds works that mention no lifetime variable of the node's context (`TExpr.lifeFreeIn`): a work
  is a declaration of the program (R1), at the empty lifetime context;
- meets condition 2 at each operation (`cond2B` at the program's flow record, over the names the
  work performs, `tailNames`): no frame between a `perform` and its handler catches them.

So the work a `perform` of `n` reaches is known and needs nothing of its node's frame: R1
(`Rewrite/Tail.lean`) calls it where the operation is performed and removes the node.

The checker reads the licence off a check that writes the rule's node wherever its premises accept
it (`TailGate.all`), and checks the program again writing it at the admitted names only
(`TailGate.names`, `checkCounted`); the rewriter reads the same licence off that check, as its
admission (`Rewrite/Admission.lean`). Every walk is bounded by a fuel whose exhaustion is an error.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check (TExpr TInfo handlerNames clauseExpr tailNames vfreeB cfreeB)
open BoCa.Fig16.LogRel.Core.ClauseKinds (HIn)

/-- **Condition 2, decided**: no name of the row `Σ` (its names `row`) is one the record `V` may
catch.  `[spec §19]` -/
def cond2B (V : HIn) (row : List UInt32) : Bool := row.all fun m => !V.catchesB m

/-- **The names condition 2 is over at a clause** (form (b), SPEC §19): the names its own code
performs or raises (`clauseNames`), or, where it may run code it does not hold, its row's. -/
def cond2Names (row : List UInt32) (ns : Option (List UInt32)) : List UInt32 := ns.getD row

/-- The depth bound of the licence's walks. -/
def licenceFuel : Nat := 1 <<< 20

/-- The judgment mentions the lifetime variable `x` free. -/
def jdgFree (x : LifeVar) : BoCa.Fig16.LogRel.Core.Jdg → Bool
  | .val A => vfreeB x A
  | .comp C => cfreeB x C

/-- The lifetimes a node takes besides its judgment's: an instantiation's, a box's, a
subsumption's two, and the witness the node records (`TInfo.wit`). -/
def lifeArgs (t : TExpr) : List Lifetime.Life :=
  let own : List Lifetime.Life := match t with
    | .allE _ _ _ _ a _ _ | .allEV _ _ _ _ a _ _ | .boxI _ _ a _ _ | .boxE _ _ a _ _ => [a]
    | .immSub _ _ a b _ _ | .mutSub _ _ a b _ _ => [a, b]
    | _ => []
  own ++ t.info.wit.toList

/-- **The typed term mentions one of the lifetime variables `xs`**: at a node's judgment or at a
lifetime it takes (`lifeArgs`). A variable a node of the term binds is fresh for the context it
is checked at (`LifeCtx.freshVar`), so none is one of `xs`. -/
def TExpr.lifeFreeIn (xs : List LifeVar) : Nat → TExpr → Except String Bool
  | 0, _ => throw "licence: a term nested too deeply"
  | f + 1, t => do
    if xs.any (fun x => jdgFree x t.jdg || (lifeArgs t).any (·.mentions x)) then return true
    t.children.anyM fun (_, c) => TExpr.lifeFreeIn xs f c

/-- The components of a tuple written in place, `(g₀, (g₁, … ()))`, `n` of them. -/
def tupleParts : Nat → TExpr → Option (List TExpr)
  | 0, .unitI .. => some []
  | n + 1, .tensorI _ _ _ _ _ c rest => (c :: ·) <$> tupleParts n rest
  | _, _ => none

/-- **A `handle` node, as the licence reads it**: its span, name, whether it is the tail-resuming
rule's, its signature, outer row and works' row, its works' tuple's erasure, whether its works
mention a lifetime variable of its context, and whether it holds an abortive operation. -/
structure LNode where
  sp : Frontend.Span
  n : UInt32
  tail : Bool
  E : List (BoCa.Fig16.LogRel.Core.Count × BoCa.Fig16.LogRel.Core.VTy × BoCa.Fig16.LogRel.Core.VTy)
  S : BoCa.Fig16.LogRel.Core.Row
  SN : BoCa.Fig16.LogRel.Core.Row := []
  Hc : Expr := .val .unit
  lfree : Bool := false
  /-- Its works are a tuple written in place (`tupleParts`). -/
  inPlace : Bool := false

/-- The `handle` nodes of a typed term at the lifetime context `Δ`, added to `acc`, in pre-order. -/
def lnodes : Nat → LifeCtx → TExpr → Array LNode → Except String (Array LNode)
  | 0, _, _, _ => throw "licence: a term nested too deeply"
  | f + 1, Δ, t, acc => do
    let acc ← match t with
      | .effHandleV i _ S E _ n .. | .effHandleVB i _ S E _ n .. | .effHandleL i _ S _ E _ _ n .. =>
        pure (acc.push { sp := i.sp, n, tail := false, E, S })
      | .effHandleT i _ S SN E _ n _ _ _ _ _ tc _ =>
        let tw := match tc with
          | .tensorI _ _ _ _ _ _ tw => some tw
          | _ => none
        let lfree ← match tw with
          | some tw => TExpr.lifeFreeIn (Δ.entries.map (·.1)) licenceFuel tw
          | none => pure true
        let inPlace := (tw.bind (tupleParts E.length)).isSome
        let Hc := BoCa.Fig16.LogRel.Core.Check.Expr.pairR tc.erase
        pure (acc.push { sp := i.sp, n, tail := true, E, S, SN, Hc, lfree, inPlace })
      | _ => pure acc
    -- The lifetime context of the children: `Fun`'s binder, and R1's at its body.
    let Δc : LifeCtx := match t with
      | .allI _ _ x b _ _ _ | .lendR _ _ x b _ _ _ _ _ => Δ.extend x b
      | _ => Δ
    t.children.foldlM (init := acc) fun acc (_, c) => lnodes f Δc c acc

/-- **A typed term has a node the checker may write by the tail-resuming rule**: a `[handle]` node
whose every clause it classifies `tail` or abortive, one of them `tail`, of a name other than
`Div`'s. -/
def tailCandidate : Nat → TExpr → Except String Bool
  | 0, _ => throw "licence: a term nested too deeply"
  | f + 1, t => do
    let here : Bool := match t with
      | .effHandleV _ _ _ _ _ n _ _ _ ks .. =>
        n != BoCa.divEff && ks.all (fun k => k.kind == .abortive || k.kind == .tail) &&
          ks.any (·.kind == .tail)
      | _ => false
    if here then return true
    t.children.anyM fun (_, c) => tailCandidate f c

/-- A name's standing under the licence: admitted, or left with the conjunct it fails. -/
inductive Licence where
  | admitted
  | left (why : String)
  deriving DecidableEq, Repr, Inhabited

/-- The word a standing is reported by. -/
def Licence.word : Licence → String
  | .admitted => "admitted"
  | .left why => s!"left: admission ({why})"

/-- **The licence of one name** over its nodes `ns` (none empty), at the flow record `V`. -/
def licenceOf (V : HIn) (ns : List LNode) : Licence := Id.run do
  let some h := ns.head? | return .left "no node"
  unless ns.all (·.tail) do return .left "a node not the tail-resuming rule's"
  unless h.E.all (·.1 != BoCa.Fig16.LogRel.Core.Count.zero) do return .left "an abortive operation"
  unless ns.all (fun g => decide (g.E = h.E) && decide (g.S = h.S) && decide (g.SN = h.SN)) do
    return .left "the nodes' rows or signatures differ"
  unless ns.all (·.inPlace) do return .left "works not written in place"
  unless ns.all (fun g => g.Hc == h.Hc) do return .left "the nodes' works differ"
  unless h.SN.isEmpty do return .left "a work performs"
  let works := (List.range h.E.length).map fun j => clauseExpr h.Hc j
  unless works.all (fun w => match w with
      | some w => BoCa.Fig16.LogRel.Core.closedAt 0 w
      | none => false) do
    return .left "a work not closed"
  if ns.any (·.lfree) then return .left "a work mentions a lifetime of its node's context"
  let row := (h.S.map (·.n)).eraseDups
  let names := tailNames h.E h.Hc
  unless (List.range h.E.length).all (fun j => cond2B V (cond2Names row ((names[j]?).getD none))) do
    return .left "condition 2"
  return .admitted

/-- **The licence** over the typed terms `ts` at the flow record `V`: each name with a node of the
tail-resuming rule, in the order of its first node, admitted or left. -/
def licence (V : HIn) (ts : List TExpr) : Except String (List (UInt32 × Licence)) := do
  let nodes ← ts.foldlM (init := #[]) fun acc t =>
    lnodes licenceFuel ⟨[]⟩ t acc
  let names := ((nodes.toList.filter (·.tail)).map (·.n)).eraseDups
  pure (names.map fun n => (n, licenceOf V (nodes.toList.filter (·.n == n))))

/-- The nodes of the tail-resuming rule of each name over the typed terms `ts`, each source node
once (by its span: a `def`'s body is in the terms at each use). -/
def tailNodes (ts : List TExpr) : Except String (List (UInt32 × Nat)) := do
  let nodes ← ts.foldlM (init := #[]) fun acc t => lnodes licenceFuel ⟨[]⟩ t acc
  let tl := (nodes.toList.filter (·.tail)).map fun g => (g.n, g.sp)
  let tl := tl.eraseDups
  pure ((tl.map (·.1)).eraseDups.map fun n => (n, (tl.filter (·.1 == n)).length))

/-- The admitted names of a licence. -/
def admittedOf (l : List (UInt32 × Licence)) : List UInt32 :=
  l.filterMap fun (n, s) => if s == .admitted then some n else none

end Frontend.Check
