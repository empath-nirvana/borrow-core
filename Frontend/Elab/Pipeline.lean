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
those are is decided by types: an elaboration that finds them (`AutoLend.find`) records each one's
position (`Origin.autoLent`), and the text is parsed again with those positions read as `&x`
(`parseProgram (lendAt := …)`), so that every stage after the parse reads the lend as written.
This repeats until an elaboration records no new position. The last elaboration is the one whose
result, or error, is reported: an elaboration that finds places and fails reports its error, since
the next would fail the same way; and the program's own elaboration lends in the library texts in
the new spelling too, finding nothing new when the rounds have converged. -/

/-- The library modules whose text is in the new spelling (SPEC §82).  `[spec §82]` -/
def newLibTexts : List String :=
  Sugar.libNames.filter fun m => (Sugar.libSrc m).any isNewDialect

/-- The rounds of finding places to lend before the last parse.  `[spec §82]` -/
def lendRounds : Nat := 8

/-- The positions an elaboration of `p` lends at, in the texts `texts`, with the library positions
`libAt` read as `&x`.  `[spec §82]` -/
def lentPositions (p : Program) (texts : List String) (libAt : List Pos) :
    Except Error (List Pos) := do
  let s ← Sugar.elaborateO p { texts, lendAt := libAt, find := true }
  pure (s.origins.filterMap fun | (sp, .autoLent) => some sp.start | _ => none).eraseDups

/-- The positions to lend at in the library texts in the new spelling, found to the round that
finds none new (at most `lendRounds`), or to one that fails, which the program's own elaboration
then reports.  `[spec §82]` -/
def libLends (p : Program) : List Pos := Id.run do
  let texts := newLibTexts
  if texts.isEmpty then return []
  let mut acc : List Pos := []
  for _ in [0:lendRounds] do
    let .ok ps := lentPositions p texts acc | return acc
    let new := ps.filter fun q => q.file != "" && !acc.contains q
    if new.isEmpty then return acc
    acc := acc ++ new
  return acc

/-- Parse a program's source. In the new spelling, its bare places at shared-borrow parameters are
read as lends: found by elaboration and the source parsed again, until no new one is found (at
most `lendRounds`). A source with none is parsed once. An elaboration that fails while finding
them is the last one, and its error is the program's.  `[spec §82]` -/
def parseLent (src : String) (lib : String → Option String := Sugar.libSrc) :
    Except Error Program := do
  let p ← parseProgram src (lib := lib)
  if !isNewDialect src then return p
  let texts := "" :: newLibTexts
  let mut p := p
  let mut acc : List Pos := []
  for _ in [0:lendRounds] do
    let ps ← lentPositions p texts (acc.filter (·.file != ""))
    let new := ps.filter (!acc.contains ·)
    if new.isEmpty then return p
    acc := acc ++ new
    if new.any (·.file == "") then
      p ← parseProgram src (lib := lib) (lendAt := acc.filter (·.file == ""))
  return p

/-- Elaborate a parsed program for the checker. The library texts in the new spelling are read
with their lends (`libLends`).  `[spec §82]` -/
def elaborate (p : Program) : Except Error Elaborated := do
  let s ← Sugar.elaborateO p { texts := newLibTexts, lendAt := libLends p }
  let keys := s.origins.filterMap fun | (_, .defKey k) => some k | _ => none
  pure ⟨s.prog, s.lib, s.origins, keys⟩

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
