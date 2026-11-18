import Frontend.Sugar

/-!
# Frontend — Elab — the elaboration pipeline  `[#54, docs/typed-elaboration.md §1, §3]`

    parse ─▶ sugar ─▶ core ─▶ the checker ─▶ the typed term

The sugar of SPEC §11 and §14 is elaborated syntactically (`Frontend.Sugar`), typing what it needs
with its own inference (`TCx`, `Frontend.Elab.Infer`), and the checker checks the core it
produces. The checker returns the typed term (`Frontend/Check/TExpr.lean`), from which nothing is
inferred again.

**Errors.** Generated code carries the span of the sugar that produced it, and the pipeline
keeps the sugar's name for that span (its origins). `renderError` adds that name to an error the
checker reports at such a span.
-/

namespace Frontend.Elab
open Frontend.Check

/-! ### The pipeline -/

/-- An elaborated program: the core the checker checks, the number of library declarations it
begins with, and the origins of its generated code. The handler sites the elaboration of effects
made are on their `handle` nodes (`SiteRec`). -/
structure Elaborated where
  prog : Program
  lib : Nat
  origins : Sugar.Origins
  /-- The key of each `def` the elaboration generates (`DefKey`). -/
  keys : List DefKey := []

/-! ### Lends the callee's parameter gives  `[spec §82]`

A bare place at a shared-borrow parameter is lent, as `&x` today (SPEC §82 P8). Which arguments
those are is decided by types: an elaboration records each one's position (`Origin.autoLent`), and
the text is parsed again with those positions read as `&x` (`parseProgram (lendAt := …)`), so that
every stage after the parse reads the lend as written. The rounds repeat until an elaboration
records no new position; that elaboration is the program's, and its result, or error, is the one
reported. An elaboration that fails is followed by one that only finds positions
(`AutoLend.find`, which stops before the lends are placed in their bindings): when it finds new
ones the rounds go on, and otherwise the failure is the program's. A library text's positions are
found in the same rounds as the program's, once. -/

/-- The library modules whose text is in the new spelling (SPEC §82).  `[spec §82]` -/
def newLibTexts : List String :=
  Sugar.libNames.filter fun m => (Sugar.libSrc m).any isNewDialect

/-- A bound on the rounds of finding places to lend in the texts `srcs`: each round that does not
stop finds a new position, and a position is a character of a text.  `[spec §82]` -/
def lendRounds (srcs : List String) : Nat := srcs.foldl (· + ·.length) 1

/-- The error of rounds that did not settle within `lendRounds`: not expected, since each round
finds a new position, and reported rather than taken as settled.  `[spec §82]` -/
def lendRoundsError (n : Nat) : Error :=
  ⟨Span.none, s!"finding the places a call lends (SPEC §82 P8) did not settle in {n} rounds"⟩

/-- The elaboration for the checker, from the sugar's.  `[spec §82]` -/
def ofSugared (s : Sugar.Sugared) : Elaborated :=
  ⟨s.prog, s.lib, s.origins, s.origins.filterMap fun | (_, .defKey k) => some k | _ => none⟩

/-- The positions an elaboration lent at.  `[spec §82]` -/
def lentAt (s : Sugar.Sugared) : List Pos :=
  (s.origins.filterMap fun | (sp, .autoLent) => some sp.start | _ => none).eraseDups

/-- One round: `p` elaborated, lending in the texts `texts` with the library positions `libAt`
read as `&x`, and the positions it lent at; when it fails, those an elaboration that only finds
them lends at.  `[spec §82]` -/
def lendRound (p : Program) (texts : List String) (libAt : List Pos) :
    Except Error Elaborated × List Pos :=
  match Sugar.elaborateO p { texts, lendAt := libAt } with
  | .ok s => (.ok (ofSugared s), lentAt s)
  | .error e => match Sugar.elaborateO p { texts, lendAt := libAt, find := true } with
    | .ok s => (.error e, lentAt s)
    | .error _ => (.error e, [])

/-- The rounds over the program `parse` gives with the program-text positions found so far, in
the texts `texts`, at most `n`: the last parse and its elaboration.  `[spec §82]` -/
def lendLoop (parse : List Pos → Except Error Program) (texts : List String) (n : Nat) :
    Except Error (Program × Except Error Elaborated) := do
  let mut p ← parse []
  let mut acc : List Pos := []
  for _ in [0:n] do
    let (r, ps) := lendRound p texts (acc.filter (·.file != ""))
    let new := ps.filter (!acc.contains ·)
    if new.isEmpty then return (p, r)
    acc := acc ++ new
    if new.any (·.file == "") then p ← parse (acc.filter (·.file == ""))
  throw (lendRoundsError n)

/-- Elaborate a parsed program for the checker, the library texts in the new spelling read with
their lends.  `[spec §82]` -/
def elaborate (p : Program) : Except Error Elaborated := do
  let texts := newLibTexts
  if texts.isEmpty then return ofSugared (← Sugar.elaborateO p)
  (← lendLoop (fun _ => pure p) texts (lendRounds (texts.filterMap Sugar.libSrc))).2

/-- Parse and elaborate a program's source: the parse (an error, thrown) and the elaboration (an
error, returned, so that a check of the parse comes first). A text in the new spelling lends its
bare places (`lendLoop`); a text in today's spelling is parsed once. `nd` is the text's spelling
(its first line, or the driver's); `lends`, whether its calls lend bare places (the new
spelling's, or a test of today's text); `rounds` replaces `lendRounds`.  `[spec §82]` -/
def parseLent (src : String) (lib : String → Option String := Sugar.libSrc)
    (nd : Bool := isNewDialect src) (lends : Bool := nd) (rounds : Option Nat := none) :
    Except Error (Program × Except Error Elaborated) := do
  let texts := (if lends then [""] else []) ++ newLibTexts
  if texts.isEmpty then
    let p ← parseProgram src (lib := lib) (nd := nd)
    return (p, ofSugared <$> Sugar.elaborateO p)
  lendLoop (fun ps => parseProgram src (lib := lib) (lendAt := ps) (nd := nd)) texts
    (rounds.getD (lendRounds (src :: texts.filterMap Sugar.libSrc)))

/-! ### Errors -/

/-- An error, with a note naming the sugar whose generated code it is in, when its span is the
span of one. -/
def renderError (os : Sugar.Origins) (e : Error) : Error :=
  let shown (m : String) : Span × Sugar.Origin → String
    | (_, .shown x what) => m.replace s!"`{x}`" what
    | _ => m
  let e := { e with msg := os.foldl shown e.msg }
  match os.findSome? (fun (s, o) => match o with
      | .sugar what => if s == e.span then some what else none
      | _ => none) with
  | some what =>
    { e with msg := s!"{e.msg}\n  in the core generated for {what} here (`bcc desugar` shows it)" }
  | none => e

end Frontend.Elab
