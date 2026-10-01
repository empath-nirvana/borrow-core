import Frontend.Check.Checker
import Frontend.Elab.Pipeline
import Frontend.Elab.Copies

/-!
# Frontend — Check — programs

`checkProgram` checks the declarations in order (syntax-core §10): each `type` and `shape`
elaborates at `Δ = ∅`; each `def` without parameters is checked once at its declaration, at
`Δ = ∅` and the empty context (and again at every use); a `def` with type parameters is checked
only at its uses; `main` is checked at `Δ = ∅` and the context of the externs, the last declared
at index `0`, all live.

**Soundness.** A successful check of `main` returns a `Checked`: the erased `Expr` with a
`CDerives LifeCtx.empty Γ e (comp C)` derivation, `Γ` the externs. The derivation is built by
the rule builders from the checked premises, so it is a proof, not a claim; `checkProgram_sound`
reads it off, `checked_sem` applies the Fundamental Property, and `checked_runs` applies
adequacy to a closed `main : F 1`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerives Jdg SemC fundamentalC adequacyC)

/-- A checked `main`: its context, erasure and type, with the derivation. -/
structure Checked where
  ctx : Ctx CVTy
  e : CExpr
  C : CCTy
  deriv : CDerives LifeCtx.empty ctx e (.comp C)

/-- What `bcc check` prints, and the checked `main`. -/
structure Report where
  lines : List String
  main : Option Checked

/-- The depth bound for checking a term. -/
def checkFuel : Nat := 1 <<< 20

def Env.top (ds : Array Decl) (k : Nat) : Env := ⟨⟨ds, k⟩, [], [], [], [], 0, none⟩

/-- The externs, in declaration order, each elaborated in the declarations before it. -/
def externs (ds : Array Decl) : Except Error (List (String × CVTy)) :=
  (List.range ds.size).foldlM (init := []) fun acc k =>
    match (ds[k]? : Option Decl) with
    | some (.extern _ n A) => do
        let A' ← (Env.top ds k).elabV LifeCtx.empty A
        pure (acc ++ [(n.name, A')])
    | _ => pure acc

/-- The first extern neither consumed nor droppable. -/
def firstUnconsumed : List Bool → List Bool → Option Nat
  | a :: as, b :: bs => if !(a || b) then some 0 else (firstUnconsumed as bs).map (· + 1)
  | _, _ => none

/-- Check `main : C = M`. -/
def checkMain (ds : Array Decl) (k : Nat) (sp : Span) (C : CTy) (M : Comp) :
    Except Error Checked := do
  let xs ← externs ds
  let T := (xs.map (·.2)).reverse
  let E : Env := { Env.top ds k with vars := (xs.map (some ·.1)).reverse, nExt := xs.length }
  let C' ← E.elabC LifeCtx.empty C
  let r ← chkC checkFuel E LifeCtx.empty T M C'
  if h : subL (allL T) (orL r.F.u r.F.w) = true then
    pure ⟨mkCtx T (allL T), r.e, C', r.F.d _ (btw_allL T _ _ r.F.hu r.F.hw h)⟩
  else match firstUnconsumed r.F.u r.F.w with
    | some i => throw ⟨sp, s!"`main` does not consume the extern {E.slotName i}, of type " ++
        s!"`{E.slotTy T i}`, which is not persistent"⟩
    | none => throw ⟨sp, "internal error: main"⟩

/-- Check one declaration; the line `bcc check` prints for it, and `main`'s result. -/
def checkDecl (ds : Array Decl) (k : Nat) : Decl → Except Error (String × Option Checked)
  | .type _ n A => do
      let A' ← (Env.top ds k).elabV LifeCtx.empty A
      pure (s!"type {n.name} = {ppVTy A'}", none)
  | .shape _ n σ => do
      let _ ← (Env.top ds k).elabS LifeCtx.empty σ
      pure (s!"shape {n.name}", none)
  | .def_ _ n ps A V _ =>
      if ps.isEmpty then do
        -- At the persistent externs declared before it (SPEC §11).
        let xs ← externs (ds.extract 0 k)
        let T := (xs.map (·.2)).reverse
        let E : Env := { Env.top ds k with
          vars := (xs.map fun (x, B) => if B.persistent then some x else none).reverse,
          nExt := xs.length }
        let A' ← E.elabV LifeCtx.empty A
        let _ ← chkV checkFuel E LifeCtx.empty T V A'
        pure (s!"def {n.name} : {ppVTy A'}", none)
      else
        pure (s!"def {n.name}[{", ".intercalate (ps.map (·.name))}] : checked at each use", none)
  | .include sp n => throw ⟨sp, s!"internal error: `include {n.name}` was not resolved"⟩
  | .effect sp n _ => throw ⟨sp, s!"internal error: `effect {n.name}` was not elaborated"⟩
  | .handler sp n _ _ _ _ => throw ⟨sp, s!"internal error: `handler {n.name}` was not elaborated"⟩
  | .extern _ n A => do
      let A' ← (Env.top ds k).elabV LifeCtx.empty A
      pure (s!"extern {n.name} : {ppVTy A'}", none)
  | .main sp C M => do
      let c ← checkMain ds k sp C M
      pure (s!"main : {ppCTy c.C}", some c)

/-- Check a program, after elaborating it (`Frontend.Elab.elaborate`: the sugar of SPEC §11 and
§14, then the typed IR and its lowering): the checker sees only the elaborated program. The lines
of the libraries, when they are included, are not reported. An error in code generated for a
sugar names the sugar (`Frontend.Elab.renderError`). A checked program is then rejected if it
copies recursive data implicitly (`Frontend.Elab.implicitCopy`): such a use is written
`clone(x)`. With `copies := false` that check is skipped: for a program rebuilt from the printed
core of one already checked with it, where `clone(x)` is `x` (`run_io`'s wrapper). -/
def checkProgram (p : Program) (copies : Bool := true) : Except Error Report := do
  let el ← Frontend.Elab.elaborate p
  let ds := el.prog.decls.toArray
  let lib := el.lib
  let r : Except Error Report := (List.range ds.size).foldlM (init := (⟨[], none⟩ : Report))
    fun acc k => match (ds[k]? : Option Decl) with
      | some d => do
          let (line, m) ← checkDecl ds k d
          pure (⟨if k < lib then acc.lines else acc.lines ++ [line], m <|> acc.main⟩ : Report)
      | none => pure acc
  let rep ← r.mapError (Frontend.Elab.renderError el.origins)
  -- What the elaboration reports about the program's loops (SPEC §16): total or div, and code
  -- that does not run after a loop that never ends.
  let loops := el.origins.filterMap fun (_, w) =>
    if w.startsWith Frontend.Sugar.reportTag then some ("loop " ++ w.drop Frontend.Sugar.reportTag.length)
    else none
  -- What the elaboration of effects reports (SPEC §18): each function's row, each handler's
  -- shape, and each operation's call.
  let fx := el.origins.filterMap fun (_, w) =>
    if w.startsWith Frontend.Sugar.effectsTag then some (w.drop Frontend.Sugar.effectsTag.length).toString
    else none
  let rep := { rep with lines := rep.lines ++ loops.eraseDups ++ fx.eraseDups }
  if !copies then return rep
  let marked := (el.origins.filter (·.2 == Frontend.Sugar.cloneOrigin)).map (·.1)
  match Frontend.Elab.implicitCopy el.tir marked with
  | some e => throw (Frontend.Elab.renderError el.origins e)
  | none => pure rep

/-! ### Soundness -/

/-- **Soundness of the checker.** If `bcc` accepts a program, its `main` erases to an `Expr`
with a `CDerives` derivation at `Δ = ∅` and the context of its externs. -/
theorem checkProgram_sound {p : Program} {r : Report} {c : Checked}
    (_h : checkProgram p = .ok r) (_hc : r.main = some c) :
    CDerives LifeCtx.empty c.ctx c.e (.comp c.C) :=
  c.deriv

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The Fundamental Property at a checked `main`: it is semantically well typed at every
host. -/
theorem checked_sem (c : Checked) : SemC LifeCtx.empty c.ctx c.e c.C :=
  fundamentalC c.deriv

/-- Adequacy at a checked `main : F 1` with no externs: it runs from the empty memory to `()`
and the empty memory. -/
theorem checked_runs (c : Checked) (hΓ : c.ctx = []) (hC : c.C = .ret .unit) :
    BoCa.BoLo.Steps BoCa.Adequacy.emptyMem c.e BoCa.Adequacy.emptyMem (Expr.val BoCa.Val.unit) := by
  have h := c.deriv
  rw [hΓ, hC] at h
  exact adequacyC h

end Frontend.Check
