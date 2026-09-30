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
  let e := abandoned os e
  match os.find? (fun (s, w) => s == e.span && !w.startsWith Sugar.reportTag &&
      !w.startsWith Sugar.effectsTag && !w.startsWith Sugar.abortTag) with
  | some (_, what) =>
    { e with msg := s!"{e.msg}\n  in the core generated for {what} here (`bcc desugar` shows it)" }
  | none => e
where
  /-- A value with no destructor left live by an abort (SPEC §18): the `raise` or raising call
  whose abort path leaves it, when the error is at a binder in scope there, or at a `case` one of
  whose arms aborts without consuming it. -/
  abandoned (os : Sugar.Origins) (e : Error) : Error :=
    let unconsumed := (e.msg.splitOn "is not consumed in its scope").length > 1
    let unbalanced := (e.msg.splitOn "but not in the").length > 1 &&
      (e.msg.splitOn "has no destructor").length > 1
    if !unconsumed && !unbalanced then e else
    let at_ := e.span.start.render
    let within (p : Pos) : Bool := !e.span.start.later p && !p.later e.span.stop
    let pos (r : String) : Option Pos := match r.splitOn ":" with
      | [l, c] => do pure ⟨← l.toNat?, ← c.toNat?⟩
      | _ => none
    match os.findSome? (fun (_, w) =>
        if !w.startsWith Sugar.abortTag then none else
        match (w.drop Sugar.abortTag.length).toString.splitOn "|" with
        | [r, bs] =>
          if unconsumed && (bs.splitOn ",").contains at_ then some r
          else if unbalanced && ((pos r).map within).getD false then some r
          else none
        | _ => none) with
    | some r =>
      { e with msg := s!"{e.msg}; an abort at {r} leaves it (a `raise` cannot abandon a value " ++
          "with no destructor, SPEC §18)" }
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
    | .include _ n => s!"include {n.name}"
    | .effect _ n _ => s!"effect {n.name}"
    | .handler _ n _ _ _ _ => s!"handler {n.name}"

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
