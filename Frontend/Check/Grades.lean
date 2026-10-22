import Frontend.Check.Kinds

/-!
# Frontend — Check — the counts of a program's operations  `[spec §53]`

An operation's grade on `eff` is its count, `0`, `1` or `1?` (`Core.Count`), and its world, `⊤`
at this stage. The checker infers the count of each operation `n.i` a handler site serves and the
effect declares `ctl`: **the strictest count every `handle` node of `n` allows** (SPEC §53). One
`handle` node's clause for the operation asks (`Need`, `Frontend/Check/Kinds.lean`):

* `0`, at an abortive operation;
* `1`, when it resumes `κ` exactly once on every path, its kind `tail`, `tail+state` or a `once`
  with no cancel, provided each operation of a row a `[let]` holds `κ` across is at `1`: an
  operation with weakening there, a raise or a `1?` operation, may drop `κ`;
* `1?` otherwise: the clause may cancel `κ` or keep it.

The count is `1` where every node asks `1` and every operation their `[let]`s hold `κ` across is
at `1`, the greatest such assignment (`inferCounts`, a fixed point from all `1` down); it is `1?`
where a node asks `1?`, or holds `κ` across an operation that is not at `1`, and that node and its
reason pin it (`Grade.pin`). A `linear ctl` operation declares `1`, a bound: a node that asks more
is refused, by name (`Grades.violation`). An operation the program writes in core (`lin`, `aff`)
is at its written count.

The inference picks the counts; the kernel checks them: the program is checked again at them
(`checkProgram`), and every handler's clause and every performer is typed at its operation's count.
Lowering a count from `1?` to `1` only weakens what a performer is asked (`[let]`'s `hW`).

Counts are inferred per operation name: one node that may cancel or keep `κ` pins its operation at
`1?` at every node of the name.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.ClauseKinds

instance : Inhabited Count := ⟨.opt⟩

/-- An operation `n.i` of the program. -/
abbrev OpKey := UInt32 × UInt32

/-- **How an operation's count is fixed**: inferred (`ctl`), declared `1` (`linear ctl`), or
written in a core row (`lin`, `aff`). -/
inductive GradeSrc where
  | inferred
  | declared
  | written
  deriving DecidableEq, Repr, Inhabited

def GradeSrc.word : GradeSrc → String
  | .inferred => "inferred"
  | .declared => "declared"
  | .written => "written"

/-- **An operation's grade**: its count, how the count is fixed, and, at `1?`, the node that pins it
and why. -/
structure Grade where
  key : OpKey
  cnt : Count
  src : GradeSrc
  pin : Option (Frontend.Span × String) := none
  deriving Inhabited

/-- What inference gives a program: each operation's grade, and the first declared `linear ctl`
operation a node forces above `1`, with that node and its reason. -/
structure Grades where
  grades : List Grade := []
  violation : Option (OpKey × Frontend.Span × String) := none
  deriving Inhabited

/-- The count as the census writes it. -/
def _root_.BoCa.Fig16.LogRel.Core.Count.word : Count → String
  | .zero => "0"
  | .one => "1"
  | .opt => "1?"

/-- The declared counts of the operation `j` at the nodes of a name: each node's site record's. -/
def declsAt (nodes : List HandleSite) (j : Nat) : List (Option Frontend.Qual) :=
  nodes.map fun h => (h.site.bind fun s => s.decl[j]?)

/-- A node's need for the operation `j`, as it is when inference starts. -/
def needAt (h : HandleSite) (j : Nat) : Need := (h.needs[j]?).getD (.opt "its clause is not read")

/-- **The operations whose count inference fixes**, with the counts the first check gave them
(`ks`): each operation of a handler site whose every node of the name records it `ctl`
(inferred) or `linear ctl` (declared). -/
def inferKeys (hs : List HandleSite) : List (OpKey × GradeSrc) :=
  let names := (hs.map (·.n)).eraseDups
  names.flatMap fun n =>
    let nodes := hs.filter (·.n == n)
    let width := (nodes.map (·.ks.length)).foldl max 0
    (List.range width).filterMap fun j =>
      let ds := declsAt nodes j
      if !ds.isEmpty && ds.all (· == some .infer) then some ((n, UInt32.ofNat j), .inferred)
      else if !ds.isEmpty && ds.all (fun d => d == some .infer || d == some .lin) then
        some ((n, UInt32.ofNat j), .declared)
      else none

/-- One round of the fixed point: each candidate at `1` whose nodes hold `κ` across an operation
not at `1` goes to `1?`, pinned by that node. `cur` is the candidates; `cntOf` the count the first
check gave an operation outside them. -/
def demote (hs : List HandleSite) (cur : List (OpKey × Count × Option (Frontend.Span × String))) :
    List (OpKey × Count × Option (Frontend.Span × String)) :=
  cur.map fun (k, c, pin) =>
    if c != .one then (k, c, pin) else
      let nodes := hs.filter (·.n == k.1)
      let bad := nodes.findSome? fun h => match needAt h k.2.toNat with
        | .one deps => deps.findSome? fun ((dk, dc)) =>
            let now := match cur.find? (·.1 == dk) with
              | some (_, c', _) => c'
              | none => dc
            if now == .one then none
            else some (h.sp, s!"its continuation is held across {dk.1}.{dk.2}, at {now.word}")
        | _ => none
      match bad with
      | some p => (k, .opt, some p)
      | none => (k, c, pin)

/-- **The counts of a program's operations** (SPEC §53), from the `handle` nodes of its checked
terms: for each operation inference fixes (`inferKeys`), the strictest count its nodes allow,
the greatest fixed point of `demote` from each node's need; the first node that pins each `1?`,
with its reason; and the first declared `linear ctl` operation forced above `1`. -/
def inferCounts (hs : List HandleSite) : Grades :=
  let keys := inferKeys hs
  let start : List (OpKey × Count × Option (Frontend.Span × String)) := keys.map fun (k, _) =>
    let nodes := hs.filter (·.n == k.1)
    let needs := nodes.map fun h => (h, needAt h k.2.toNat)
    match needs.findSome? (fun (h, nd) => match nd with
        | .opt why => some (h.sp, why)
        | _ => none) with
    | some p => (k, .opt, some p)
    | none => if needs.all (fun (_, nd) => nd == .zero) then (k, .zero, none) else (k, .one, none)
  let fin := (List.range (keys.length + 1)).foldl (fun cur _ => demote hs cur) start
  let grades := fin.filterMap fun (k, c, pin) =>
    (keys.lookup k).map fun src => ({ key := k, cnt := c, src, pin } : Grade)
  let violation := grades.findSome? fun g =>
    if g.src == .declared && g.cnt != .one then
      g.pin.map fun (sp, why) => (g.key, sp, why)
    else none
  { grades, violation }

/-- The table the check reads the inferred counts from (`Frontend.Check.Scope.cnts`). -/
def Grades.table (g : Grades) : List ((Nat × Nat) × Count) :=
  g.grades.filterMap fun gr =>
    if gr.src == .inferred then some ((gr.key.1.toNat, gr.key.2.toNat), gr.cnt) else none

/-- **A handler site's line of the grade census** (`bcc grades`): each operation's count and how it
is fixed (`abortive` at a count `0` no inference fixes), the node that pins a `1?`, its world, its clause's position (`tail`, `once`, or `-` at a
clause that keeps `κ` and at an abortive one) and where `κ` is kept (`in-clause`, `stored`, or
`stored @d` under BOXED-κ). `gs` is the program's grades. -/
def HandleSite.gradeLine (h : HandleSite) (gs : Grades) : String :=
  let ops := (List.range h.ks.length).zip h.ks |>.map fun (j, k) =>
    let key : OpKey := (h.n, UInt32.ofNat j)
    let g := gs.grades.find? (·.key == key)
    let src := match g with
      | some g => g.src.word
      | none => if k.cnt == Count.zero then "abortive" else GradeSrc.written.word
    let pin := match g.bind (·.pin) with
      | some (sp, why) => s!" (pinned at {sp.start.render}: {why})"
      | none => ""
    let pos := match k.kind with
      | .abortive => "-"
      | .tail | .tailState | .resumeOrCancel _ => "tail"
      | .resumeOnce _ => "once"
      | .stored => "-"
    let store := match k.kind, h.boxAt with
      | .stored, some d => s!"stored @{match d with | .top => "top" | _ => "d"}"
      | .stored, none => "stored"
      | .abortive, _ => "-"
      | _, _ => "in-clause"
    s!"{h.n}.{j} {k.cnt.word} {src}{pin}, world top, {pos}, {store}"
  s!"{h.sp.start.render}: handle {h.n}: {"; ".intercalate ops}"

end BoCa.Fig16.LogRel.Core.Check
