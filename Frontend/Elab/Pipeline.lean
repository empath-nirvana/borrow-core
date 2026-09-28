import Frontend.Elab.Infer
import Frontend.Sugar

/-!
# Frontend — Elab — the elaboration pipeline  `[#54, docs/typed-elaboration.md §1, §3]`

    parse ─▶ sugar ─▶ core ─infer─▶ typed IR ─lower─▶ core ─▶ the checker

This is stage 1 of the plan (docs/typed-elaboration.md §7). The sugar of SPEC §11 and §14 is
still elaborated syntactically first (`Frontend.Sugar`), and the typed IR is inferred on the
core it produces. Lowering is the identity on core: it rebuilds each node from its lowered
children (`Head.rebuild`). The checker checks the lowered program, unchanged. Later stages move
the sugar into inference and lowering, so that it can use types.

**Errors.** Generated code carries the span of the sugar that produced it, and the pipeline
keeps the sugar's name for that span (its origins). `renderError` adds that name to an error the
checker reports at such a span.
-/

namespace Frontend.Elab
open Frontend.Check

/-! ### Lowering -/

mutual
/-- A node lowered to core: its source node, rebuilt from its lowered children. -/
def TNode.lower : TNode → Option Head
  | .mk h _ _ ks => do h.rebuild (← TNode.lowerL ks)

def TNode.lowerL : List TNode → Option (List Head)
  | [] => some []
  | k :: ks => do pure ((← k.lower) :: (← TNode.lowerL ks))
end

def TDecl.lower : TDecl → Option Decl
  | .def_ sp n A b mk => match b.lower with
    | some (.val V) => some (.def_ sp n [] A V mk)
    | _ => none
  | .main sp C b => match b.lower with
    | some (.comp M) => some (.main sp C M)
    | _ => none
  | .plain d => some d

def TProgram.lower (t : TProgram) : Option Program := do
  pure ⟨← t.decls.mapM TDecl.lower⟩

/-! ### The pipeline -/

/-- An elaborated program: the core the checker checks, the number of library declarations it
begins with, the origins of its generated code, and its typed IR. -/
structure Elaborated where
  prog : Program
  lib : Nat
  origins : Sugar.Origins
  tir : TProgram

/-- Elaborate a parsed program for the checker. -/
def elaborate (p : Program) : Except Error Elaborated := do
  let (q, lib, os) ← Sugar.elaborateO p
  let t := inferProgram q
  match t.lower with
  | some q' => pure ⟨q', lib, os, t⟩
  | none => throw ⟨Span.none, "internal error: the typed IR does not lower to core"⟩

/-! ### Errors -/

/-- An error, with a note naming the sugar whose generated code it is in, when its span is the
span of one. -/
def renderError (os : Sugar.Origins) (e : Error) : Error :=
  match os.find? (·.1 == e.span) with
  | some (_, what) =>
    { e with msg := s!"{e.msg}\n  in the core generated for {what} here (`bcc desugar` shows it)" }
  | none => e

/-! ### Inspection (`bcc tir`) -/

/-- A binder, as `bcc tir` prints it. -/
def Binder.render (b : Binder) : String :=
  match b.ty with
  | some A => s!"{b.name}#{b.id} : {ppVTy A} ({(Class.of A).name})"
  | none => s!"{b.name}#{b.id} : ?"

def TDecl.name : TDecl → String
  | .def_ _ n _ _ _ => s!"def {n.name}"
  | .main .. => "main"
  | .plain d => match d with
    | .def_ _ n _ _ _ _ => s!"def {n.name}"
    | .type _ n _ => s!"type {n.name}"
    | .shape _ n _ => s!"shape {n.name}"
    | .extern _ n _ => s!"extern {n.name}"
    | .main .. => "main"

/-- What `bcc tir` prints for a declaration with a body: its name, effect, node count, the
nodes whose type is not known, and its binders. The library declarations (the first `lib`) are
counted but not listed. -/
def TDecl.report (d : TDecl) : List String :=
  match d.body? with
  | none => []
  | some b =>
    let (n, u) := b.counts
    let eff := match d with
      | .main .. => if b.effect == Effect.div then " (div)" else ""
      | _ => ""
    [s!"{d.name}{eff}: {n} nodes, {u} untyped"] ++
      (b.untyped.map fun sp => s!"  untyped at {sp.start.render}") ++
      (b.allBinders.map fun bd => s!"  {bd.render}")

/-- The typed IR of a program, as `bcc tir` prints it, and whether every node of every
declaration is typed and lowering gives back the program the checker is given. -/
def tirReport (p : Program) : Except Error (List String × Bool) := do
  let el ← elaborate p
  let (q, _, _) ← Sugar.elaborateO p
  let user := el.tir.decls.drop el.lib
  let lines := user.flatMap TDecl.report
  let typed := el.tir.decls.all fun d => match d.body? with
    | some b => b.counts.2 == 0
    | none => true
  pure (lines, typed && decide (el.prog = q))

end Frontend.Elab
