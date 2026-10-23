import Rewrite.Hom
import Frontend.Check.Handled

/-!
# Rewrite — R1's admission  `[spec §54]`

**The key** (the scope's §R1): a name every `handle` node of which is the tail-resuming rule's
(`effHandleT`), which the checker writes at the names its licence admits
(`Frontend/Check/Licence.lean`, `TailGate.names`). **The admission** is that licence, read off the
source's checked `main` (its typed term and its flow record `Checked.flows`): every node of the
name is the rule's, at one outer row `Σ`, one works' row `Σ_N` and one signature `E`, holding no
abortive operation; its works are written in place, equal at every node, closed, at the empty
lifetime context; and condition 2 holds of the names each work performs. A name with a node of the
rule that the admission leaves is a hard error: its node would reach the conversion, which has no
arm for it.

The admitted name's works are the typed works of its first node (`tc`'s second component, the
scope's typed witness, review S2): `TDerives.effHandleT`'s `hc` types them, and the rule's clause
for the operation `j` runs the `j`-th (`tailClause_premise`). No work is rebuilt from an erased
clause. Every walk is bounded by a fuel whose exhaustion is a hard error.
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core (VTy CTy OpSig Row Count)
open BoCa.Fig16.LogRel.Core.Check (TExpr)
open Frontend.Check (Licence licence tupleParts)

/-- **A name R1 rewrites**: its number, its nodes' outer row, works' row and signature, and its
works, typed, in operation order. -/
structure TailName where
  n : UInt32
  S : Row
  SN : Row
  E : List (Count × VTy × VTy)
  works : List TExpr
  deriving Inhabited

/-- The first node of the tail-resuming rule of the name `n` in a typed term, its rows, signature
and works' tuple (`tc`'s second component). -/
def firstTail (n : UInt32) : Nat → TExpr → Except String (Option (Row × Row × List (Count × VTy × VTy) × TExpr))
  | 0, _ => throw "R1: a term nested too deeply to find a node"
  | f + 1, t => do
    match t with
    | .effHandleT _ _ S SN E _ m _ _ _ _ _ (.tensorI _ _ _ _ _ _ tw) _ =>
      if m == n then return some (S, SN, E, tw)
    | _ => pure ()
    t.children.foldlM (init := none) fun acc (_, c) => do
      if acc.isSome then pure acc else firstTail n f c

/-- **R1's names** in the source's checked `main` `c`, in the order of their first nodes, read off
the term `t` the rules have reached (R0's rewrite of `c.t`, whose works R0 keeps as they are): each
name with a node of the tail-resuming rule but those R0 rewrote (`r0`: a node of the rule whose
operations are all abortive is R0's), which the admission must admit. -/
def r1Keys (c : Frontend.Check.Checked) (t : TExpr) (fuel : Nat) (r0 : List UInt32 := []) :
    Except String (List TailName) := do
  let lic ← licence c.flows [c.t]
  (lic.filter fun (n, _) => !r0.contains n).mapM fun (n, s) => do
    if let .left why := s then
      throw s!"R1: the name {n} has a node of the tail-resuming rule, and the admission leaves it ({why}): the node would reach the conversion"
    let some (S, SN, E, tw) ← firstTail n fuel t
      | throw s!"R1: no node of the tail-resuming rule of the name {n} in the rewritten term"
    let some works := tupleParts E.length tw
      | throw s!"R1: the works of the name {n} are not written in place"
    pure { n, S, SN, E, works }

end Rewrite
