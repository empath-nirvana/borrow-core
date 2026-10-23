import Rewrite.Abort

/-!
# Rewrite — R0's keys  `[spec §54]`

Which names R0 rewrites, read off the source's typed program (`main`'s, every `def` body at each
use), and its run over them.

* **The key** (the scope's §R0): a name `n` every handler node of which holds every operation at
  the count `0` (`E[j].1 = 0`, the counts the check inferred, §53). No name is mixed: a name with
  an operation at another count is not keyed.
* **Left alone, with the reason recorded:** a name in the row of an R1 relaxed lend (`lendR`): its
  abort crosses a lend the rule does not rewrite through (`left: lendR`). A name in the outer row
  of a handler node with an operation at `1?` (`left: cancel row`): that operation's `κ` cancels
  at the handler's outer row (`cancelTy Σ F = F_{F ++ Σ} 1`, SPEC §38), so `κ`'s type holds the
  name in a cancel run whose answer the kernel fixes at `1`; the scope's translation of `κ`'s
  type, homomorphic, gives it the answer `1 ⊕ P_n`, which no `[handle]` types. The scope has no
  rule for it (reported, #680).
* **The order**: inside out, the post-order of the handler nodes (a node's handled computation
  before the node), each name at its first node there. The sums nest in that order:
  `(A ⊕ P_n) ⊕ P_m` for `n` before `m`.
* **The payload** `P_n`: the operations' arguments of the name's handler nodes, which agree.

Every walk is bounded by a fuel whose exhaustion is a hard error (the scope's §1.3).
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core (VTy CTy OpSig Row Count)
open BoCa.Fig16.LogRel.Core.Check (TExpr)

/-- What R0's keys read of the source's typed program, in one walk: each handler node's name and
operations in post-order, and the names in each `lendR`'s row. -/
structure R0Scan where
  handled : Array (UInt32 × List (Count × VTy × VTy)) := #[]
  lendR : Array UInt32 := #[]
  /-- The names of the outer row of each handler node with an operation at `1?`: its `κ`'s cancel
  run is at that row (`cancelTy`, SPEC §38). -/
  cancel : Array UInt32 := #[]

/-- The scan of a typed term, added to `acc`. -/
def scan : Nat → TExpr → R0Scan → Except String R0Scan
  | 0, _, _ => throw "R0: a term nested too deeply to scan"
  | f + 1, t, acc => do
    let acc ← t.children.foldlM (init := acc) fun acc (_, c) => scan f c acc
    let acc := match t with
      | .lendR _ _ _ _ _ _ S _ _ => { acc with lendR := acc.lendR ++ (S.map (·.n)).toArray }
      | _ => acc
    pure <| match t with
      | .effHandleV _ _ S E _ n .. | .effHandleVB _ _ S E _ n .. | .effHandleT _ _ S _ E _ n ..
      | .effHandleL _ _ S _ E _ _ n .. =>
        { acc with handled := acc.handled.push (n, E),
                   cancel := if E.any (·.1 == .opt) then acc.cancel ++ (S.map (·.n)).toArray
                             else acc.cancel }
      | _ => acc

/-- A name's status under R0. -/
inductive R0Status where
  | rewritten
  | left (reason : String)
  deriving DecidableEq, Repr

/-- **R0's keys**: the names whose every handler node holds every operation at `0`, in the
inside-out order, each rewritten or left with its reason. -/
def r0Keys (c : Frontend.Check.Checked) (fuel : Nat) :
    Except String (List (AbortName × R0Status)) := do
  let sc ← scan fuel c.t {}
  let names := (sc.handled.toList.map (·.1)).eraseDups
  let mut out : List (AbortName × R0Status) := []
  for n in names do
    let Es := (sc.handled.toList.filter (·.1 == n)).map (·.2)
    unless Es.all (fun E => !E.isEmpty && E.all (·.1 == .zero)) do continue
    let some E := Es.head? | continue
    let args := E.map (·.2.1)
    unless Es.all (fun E' => decide (E'.map (·.2.1) = args)) do
      throw s!"R0: the handler nodes of the abortive name {n} disagree on its operations' arguments"
    let a : AbortName := ⟨n, args⟩
    if args.any (fun A => decide (trV a A ≠ A)) then
      throw s!"R0: an argument of the abortive name {n} mentions it"
    if sc.lendR.contains n then out := out ++ [(a, .left "lendR")]
    else if sc.cancel.contains n then out := out ++ [(a, .left "cancel row")]
    else out := out ++ [(a, .rewritten)]
  pure out

end Rewrite
