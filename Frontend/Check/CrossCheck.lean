import Frontend.Check.Program
import Frontend.Parser
import Core.CommonList
import Core.DelayPrograms

/-!
# Frontend — Check — cross-check against the library

What `bcc` elaborates, compared with the terms written by hand in `Core/`, by kernel
evaluation (`decide +kernel`) of the checker.

* The ten `def`s of syntax-core §13.1 (`corpus/13-1-library.bc`) erase to the library's
  `countAlgV`, `natCopyE`, `freeLAlgV`, `freeNatE`, `addAlgV`, `addE`, `sumAlgV`, `sumCE`,
  `freeCAlgV` and `freeCE` (§13.1, *Erasures*).
* `corpus/sum-prog-exact.bc` and `corpus/count-down-exact.bc` transcribe `sumProg`
  (`Core/CommonList.lean`) and `countDownProg` (`Core/DelayPrograms.lean`); their `main`s check
  at the empty context and erase to those terms exactly. The judgments `sumProg_derives` and
  `countDownProg_derives` then follow a second time, from `bcc`'s derivations
  (`sumProg_derives_bcc`, `countDownProg_derives_bcc`).

The parser runs at elaboration time (`bcc_program%` reads a corpus file and embeds its AST);
the kernel evaluates only the checker. Parsing in the kernel is not cheap enough for files of
this size. That the embedded AST is the parser's output is by construction of `bcc_program%`,
not a theorem.
-/

open Lean

deriving instance ToExpr for BoCa.Width
deriving instance ToExpr for BoCa.IntLit
deriving instance ToExpr for BoCa.BinOp
deriving instance ToExpr for BoCa.DivOp
deriving instance ToExpr for BoCa.UnOp
deriving instance ToExpr for BoCa.RelOp
deriving instance ToExpr for BoCa.FWidth
deriving instance ToExpr for BoCa.IWidth
deriving instance ToExpr for BoCa.Sx
deriving instance ToExpr for BoCa.FBinOp
deriving instance ToExpr for BoCa.FUnOp
deriving instance ToExpr for BoCa.FRelOp
deriving instance ToExpr for BoCa.HostOp
deriving instance ToExpr for Frontend.Pos
deriving instance ToExpr for Frontend.Span
deriving instance ToExpr for Frontend.Ident
deriving instance ToExpr for Frontend.Life
deriving instance ToExpr for Frontend.Mode
deriving instance ToExpr for Frontend.Qual
deriving instance ToExpr for Frontend.HostKind
deriving instance ToExpr for Frontend.VTy, Frontend.CTy, Frontend.Row, Frontend.Shape
deriving instance ToExpr for Frontend.Const
deriving instance ToExpr for Frontend.SurfOp
deriving instance ToExpr for Frontend.BorrowKind
deriving instance ToExpr for Frontend.HInfo
deriving instance ToExpr for Frontend.ItInfo
deriving instance ToExpr for Frontend.VSugar
deriving instance ToExpr for Frontend.Val, Frontend.Comp
deriving instance ToExpr for Frontend.Mark
deriving instance ToExpr for Frontend.OpKind
deriving instance ToExpr for Frontend.OpDecl
deriving instance ToExpr for Frontend.Clause
deriving instance ToExpr for Frontend.CHandler
deriving instance ToExpr for Frontend.Decl
deriving instance ToExpr for Frontend.Program

namespace Frontend.Check

open Elab Term in
/-- `bcc_program% "file"`: the AST the parser gives the file, as a term. -/
elab "bcc_program% " s:str : term => do
  let src ← IO.FS.readFile s.getString
  match Frontend.parseProgram src with
  | .ok p => return toExpr p
  | .error e => throwError m!"{s.getString}:{e.render}"

open BoCa BoCa.Fig16.LogRel.Core

/-- The erasure of the `def` at index `k`, checked at `Δ = ∅` and the empty context. -/
def defErasure (p : Program) (k : Nat) : Option BoCa.Expr :=
  let ds := p.decls.toArray
  match ds[k]? with
  | some (.def_ _ _ _ A V _) =>
    let E := Env.top ds k
    match E.elabV BoCa.Lifetime.LifeCtx.empty A with
    | .error _ => none
    | .ok A' => match chkV checkFuel E BoCa.Lifetime.LifeCtx.empty [] V A' with
      | .ok r => some r.e
      | .error _ => none
  | _ => none

/-- The checked `main` of a program, if it checks. -/
def mainOf (p : Program) : Option Checked :=
  match checkProgram p with
  | .ok r => r.main
  | .error _ => none

/-- `corpus/13-1-library.bc`. -/
def library : Program := bcc_program% "corpus/13-1-library.bc"

set_option maxRecDepth 100000 in
/-- §13.1's `def`s erase to the library's terms. -/
theorem library_erasures :
    [defErasure library 3, defErasure library 4, defErasure library 5, defErasure library 6,
      defErasure library 7, defErasure library 8, defErasure library 9, defErasure library 10,
      defErasure library 11, defErasure library 12] =
    [some (Expr.val countAlgV), some natCopyE, some (Expr.val freeLAlgV), some freeNatE,
      some (Expr.val addAlgV), some addE, some (Expr.val sumAlgV), some sumCE,
      some (Expr.val freeCAlgV), some freeCE] := by
  decide +kernel

/-- A checked `main` with the context, erasure and type given, using no relaxed rule. -/
theorem derives_of_mainOf {p : Program} {Γ : BoCa.Ctx CVTy} {e : BoCa.Expr} {C : CCTy}
    (h : (mainOf p).map (fun c => (c.ctx, c.e, c.C, c.pins)) = some (Γ, e, C, [])) :
    CDerives BoCa.Lifetime.LifeCtx.empty Γ e (.comp C) := by
  cases hm : mainOf p with
  | none => rw [hm] at h; cases h
  | some c =>
      rw [hm] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, hp⟩ := h
      exact c.deriv hp

/-- `corpus/sum-prog-exact.bc`. -/
def sumProgExact : Program := bcc_program% "corpus/sum-prog-exact.bc"

set_option maxRecDepth 100000 in
/-- Its `main` checks at the empty context and `F N`, and erases to `sumProg`. -/
theorem sumProgExact_main :
    (mainOf sumProgExact).map (fun c => (c.ctx, c.e, c.C, c.pins)) =
      some ([], sumProg, .ret natN, []) := by
  decide +kernel

/-- `sumProg_derives`, from `bcc`'s derivation. -/
theorem sumProg_derives_bcc :
    CDerives BoCa.Lifetime.LifeCtx.empty [] sumProg (.comp (.ret natN)) :=
  derives_of_mainOf sumProgExact_main

/-- `corpus/count-down-exact.bc`. -/
def countDownExact : Program := bcc_program% "corpus/count-down-exact.bc"

set_option maxRecDepth 100000 in
/-- Its `main` checks at the empty context and `F (N ⊕ 1)`, and erases to `countDownProg`. -/
theorem countDownExact_main :
    (mainOf countDownExact).map (fun c => (c.ctx, c.e, c.C, c.pins)) =
      some ([], countDownProg, .ret (.sum natN .unit), []) := by
  decide +kernel

/-- `countDownProg_derives`, from `bcc`'s derivation. -/
theorem countDownProg_derives_bcc :
    CDerives BoCa.Lifetime.LifeCtx.empty [] countDownProg (.comp (.ret (.sum natN .unit))) :=
  derives_of_mainOf countDownExact_main

end Frontend.Check
