import Frontend.Check.Checker

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

def Env.top (ds : Array Decl) (k : Nat) : Env := ⟨⟨ds, k⟩, [], [], []⟩

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
  let E : Env := { Env.top ds k with vars := (xs.map (some ·.1)).reverse }
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
  | .def_ _ n ps A V =>
      if ps.isEmpty then do
        let E := Env.top ds k
        let A' ← E.elabV LifeCtx.empty A
        let _ ← chkV checkFuel E LifeCtx.empty [] V A'
        pure (s!"def {n.name} : {ppVTy A'}", none)
      else
        pure (s!"def {n.name}[{", ".intercalate (ps.map (·.name))}] : checked at each use", none)
  | .extern _ n A => do
      let A' ← (Env.top ds k).elabV LifeCtx.empty A
      pure (s!"extern {n.name} : {ppVTy A'}", none)
  | .main sp C M => do
      let c ← checkMain ds k sp C M
      pure (s!"main : {ppCTy c.C}", some c)

/-- Check a program. -/
def checkProgram (p : Program) : Except Error Report := do
  let ds := p.decls.toArray
  (List.range ds.size).foldlM (init := (⟨[], none⟩ : Report)) fun acc k =>
    match (ds[k]? : Option Decl) with
    | some d => do
        let (line, m) ← checkDecl ds k d
        pure ⟨acc.lines ++ [line], m <|> acc.main⟩
    | none => pure acc

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
