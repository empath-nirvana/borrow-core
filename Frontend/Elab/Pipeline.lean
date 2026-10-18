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
begins with, the origins of its generated code, and whether `main` is served `Fail[DivError]` by
`main_div_error` (SPEC §39). -/
structure Elaborated where
  prog : Program
  lib : Nat
  origins : Sugar.Origins
  exits : Bool

/-- Elaborate a parsed program for the checker. -/
def elaborate (p : Program) : Except Error Elaborated := do
  let s ← Sugar.elaborateO p
  pure ⟨s.prog, s.lib, s.origins, s.exits⟩

/-! ### Errors -/

/-- An error, with a note naming the sugar whose generated code it is in, when its span is the
span of one. -/
def renderError (os : Sugar.Origins) (e : Error) : Error :=
  match os.find? (fun (s, w) => s == e.span && !w.startsWith Sugar.reportTag &&
      !w.startsWith Sugar.effectsTag) with
  | some (_, what) =>
    { e with msg := s!"{e.msg}\n  in the core generated for {what} here (`bcc desugar` shows it)" }
  | none => e

end Frontend.Elab
