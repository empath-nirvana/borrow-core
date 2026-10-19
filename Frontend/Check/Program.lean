import Frontend.Check.Checker
import Frontend.Elab.Pipeline
import Frontend.Check.Copies
import Frontend.Check.KindsSound
import Frontend.Check.Cells

/-!
# Frontend — Check — programs

`checkProgram` checks the declarations in order (syntax-core §10): each `type` and `shape`
elaborates at `Δ = ∅`; each `def` without parameters is checked at its declaration, at `Δ = ∅`
and the persistent externs before it, which is its key's check there; a `def` is checked once per
key (`DefEntry`: the declaration, its type arguments, the lifetime context and the externs), and
each use places its key's body (`useDef`); a `def` with type parameters is checked only at its
uses; `main` is checked at `Δ = ∅` and the context of the externs, the last declared
at index `0`, all live.

**Soundness.** A successful check of `main` returns a `Checked`: the typed term `c.t` of `main`
(`Frontend/Check/TExpr.lean`), one node per rule application, with its derivation at `Δ = ∅` and
`Γ` the externs, tied (decision R): `TDerivesAt Ξ` at every effect context `Ξ` at which the rows it
reads at `[perform]`, `[raise]` and `[handle]` are. The checked term is the typed term's erasure,
`c.e := c.t.erase`, so the term the backend compiles is the term the derivation types, by
definition. The check decides that those rows give each operation one signature, of a nonzero
name, and that no unrestricted operation among them answers `0` (decision 63); the program's effect
context `c.Ξ` is the one they give. The derivation is built by the rule builders from the checked
premises, so it is a proof, not a claim. `checkProgram_typed` and `checkProgram_typedAt` read the
typed derivation off; its projections (`TDerivesAt.erase`, `TDerivesP.erase`) give the rest at
`c.t.erase`: `checkProgram_tied` at every such context, `checkProgram_tiedAt` at the program's own,
`checkProgram_sound` the `CDerives` derivation it is, `checked_sem` the Fundamental Property, and
`checked_runs` adequacy at a closed `main : F 1`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerives CDerivesAt CDerivesP Jdg SemC fundamentalC adequacyC EffCtx
  SigsAt PinLaw fundamentalC_pin adequacyC_pin)

/-- A checked `main`: its context, typed term and type, the rows its derivation reads at
`[perform]`, `[raise]` and `[handle]`, which give each operation one signature (`sigsOkB`), the
relaxed rules its derivation uses (SPEC §29), and the derivation of the typed term: of `TDerivesP`,
and, when it uses no relaxed rule, tied at every effect context at which those rows are. -/
structure Checked where
  ctx : Ctx CVTy
  t : TExpr
  C : CCTy
  sigs : CRow
  ok : sigsOkB sigs = true
  pins : Pins
  tied : TTied pins sigs LifeCtx.empty ctx t (.comp C)
  /-- Each type a cell of `main` is allocated at, with every type such a cell may hold
  (`Frontend/Check/Cells.lean`). -/
  cells : List CellClass
  cellsOk : cellsOkB t.cells.1 t.cells.2 cells = true

/-- **`main` answers an exit status**: it is served `Fail[DivError]` by the platform's handler
`main_div_error`, read from the site of a `handle` node of its typed term (`HSite`), so that its
value `inr ()` is an exit status (SPEC §39). -/
def Checked.exitsOnDivError (c : Checked) : Bool :=
  (c.t.handleSites copiesFuel).any fun h => match h.site with
    | some s => s.handler == Frontend.Elab.Effects.mainDivHandler && s.eff == "Fail"
    | none => false

/-- **The checked term**: the typed term's erasure, the term the derivation types and the backend
compiles. -/
def Checked.e (c : Checked) : CExpr := c.t.erase

/-- **The program's effect context**: each name's signature, as the rows `main`'s derivation reads
give it. For an elaborated program these are its effect declarations' signatures at its handler
sites: the elaborator writes each row and each handler's clauses from the declarations (SPEC §18).
`[spec §19]` -/
def Checked.Ξ (c : Checked) : EffCtx := effCtxOf c.sigs

/-- `main`'s typed derivation at the program's effect context, when it uses no relaxed rule. -/
theorem Checked.typedAt (c : Checked) (hp : c.pins = []) :
    TDerivesAt c.Ξ LifeCtx.empty c.ctx c.t (.comp c.C) :=
  c.tied.1 hp _ (sigsAt_effCtxOf c.ok)

/-- `main`'s typed derivation, of `TDerivesP`.  `[spec §29]` -/
theorem Checked.typedP (c : Checked) : TDerivesP LifeCtx.empty c.ctx c.t (.comp c.C) :=
  c.tied.2

/-- `main`'s derivation at the program's effect context, when it uses no relaxed rule. -/
theorem Checked.derivAt (c : Checked) (hp : c.pins = []) :
    CDerivesAt c.Ξ LifeCtx.empty c.ctx c.t.erase (.comp c.C) :=
  (c.typedAt hp).erase

/-- `main`'s derivation, a `CDerives` derivation when it uses no relaxed rule. -/
theorem Checked.deriv (c : Checked) (hp : c.pins = []) :
    CDerives LifeCtx.empty c.ctx c.t.erase (.comp c.C) :=
  (c.derivAt hp).toCDerives

/-- `main`'s derivation, of `CDerivesP`.  `[spec §29]` -/
theorem Checked.derivP (c : Checked) : CDerivesP LifeCtx.empty c.ctx c.t.erase (.comp c.C) :=
  c.typedP.erase

/-- What `bcc check` prints of a checked `main`'s assurance: `unconditional` when its derivation
is of `CDerives`, else `PinLaw` and where each relaxed rule is used.  `[spec §29]` -/
def Pins.assurance : Pins → String
  | [] => "assurance: unconditional"
  | ps =>
    let sites (r : String) : List String :=
      ((ps.filter (·.rule == r)).map fun p => s!"{p.line}:{p.col}").eraseDups
    let parts := ["R1", "R2"].filterMap fun r =>
      match sites r with
      | [] => none
      | xs => some s!"{r} at {", ".intercalate xs}"
    s!"assurance: PinLaw ({"; ".intercalate parts})"

/-- What `bcc check` prints, the checked `main`, and the elaborated program the checker checked:
the backend reads the program, and whether `main` is served `Fail[DivError]` (SPEC §39), from it. -/
structure Report where
  lines : List String
  main : Option Checked
  el : Frontend.Elab.Elaborated
  /-- The `handle` nodes of the checked terms, each once: their static names and clause kinds
  (SPEC §19, *Clause kinds*). -/
  handles : List HandleSite := []

/-- The depth bound for checking a term. -/
def checkFuel : Nat := 1 <<< 20

/-- The environment at the top of the declaration `k`, with the handler sites the elaboration
made (`SiteRec`). -/
def Env.top (ds : Array Decl) (k : Nat) (sites : List SiteRec := []) : Env :=
  ⟨⟨ds, k, sites⟩, [], [], [], [], 0, none, []⟩

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

/-- Why the rows `main`'s derivation reads fail `sigsOkB`: an operation of the reserved name `0`,
an unrestricted operation answering `0`, or an operation with two signatures.  `[spec §18, §19]` -/
def sigsErr (s : CRow) : String :=
  let sig (o : COpSig) : String := s!"`{qualStr o.q} {ppVTy o.A} ~> {ppVTy o.B}`"
  match s.find? (·.n == 0) with
  | some o => s!"`main` performs or handles the operation 0.{o.i}, of the reserved name 0"
  | none =>
    match s.find? (fun o => o.q == .unr && o.B.isZero) with
    | some o => s!"the operation {o.n}.{o.i} is unrestricted and answers `0`: an abortive " ++
        "operation is affine (decision 63)"
    | none =>
      match s.findSome? (fun o => (s.find? fun o' => o'.n == o.n && o'.i == o.i &&
          !(o'.q == o.q && o'.A == o.A && o'.B == o.B)).map (o, ·)) with
      | some (o, o') => s!"the operation {o.n}.{o.i} has two signatures in this program, " ++
          s!"{sig o} and {sig o'}: an operation has one signature (decision R)"
      | none => "internal error: the operations' signatures"

/-- Check `main : C = M`. -/
def checkMain (ds : Array Decl) (k : Nat) (sites : List SiteRec) (sp : Span) (C : CTy) (M : Comp) :
    CheckM Checked := do
  let xs ← externs ds
  let T := (xs.map (·.2)).reverse
  let E : Env := { Env.top ds k sites with vars := (xs.map (some ·.1)).reverse, nExt := xs.length }
  let C' ← E.elabC LifeCtx.empty C
  let r ← chkC checkFuel E LifeCtx.empty T M C'
  if h : subL (allL T) (orL r.F.u r.F.w) = true then
    if hs : sigsOkB r.sigs = true then
      let cs := cellClasses r.t.cells.1 r.t.cells.2
      if hc : cellsOkB r.t.cells.1 r.t.cells.2 cs = true then
        pure { ctx := mkCtx T (allL T), t := r.t, C := C', sigs := r.sigs, ok := hs, pins := r.pins,
               tied := r.F.d _ (btw_allL T _ _ r.F.hu r.F.hw h), cells := cs, cellsOk := hc }
      else throw ⟨sp, "internal error: the cell classes of `main` are not closed"⟩
    else throw ⟨sp, sigsErr r.sigs⟩
  else match firstUnconsumed r.F.u r.F.w with
    | some i => throw ⟨sp, s!"`main` does not consume the extern {E.slotName i}, of type " ++
        s!"`{E.slotTy T i}`, which is not persistent"⟩
    | none => throw ⟨sp, "internal error: main"⟩

/-- Check one declaration; the line `bcc check` prints for it, `main`'s result, and the typed term
of a `def` without parameters checked at its declaration, at its context's length. That check is
its key's at `Δ = ∅` and the externs before it (`DefEntry`), which its uses read. -/
def checkDecl (ds : Array Decl) (k : Nat) (sites : List SiteRec) :
    Decl → CheckM (String × Option Checked × List (Nat × TExpr))
  | .type _ n [] [] A => do
      let A' ← (Env.top ds k).elabV LifeCtx.empty A
      pure (s!"type {n.name} = {ppVTy A'}", none, [])
  | .type _ n ps ls _ =>
      -- A parameterised abbreviation is elaborated at each use, at its arguments.
      let tps := if ps.isEmpty then "" else s!"[{", ".intercalate (ps.map (·.name))}]"
      let lps := if ls.isEmpty then "" else s!"<{", ".intercalate (ls.map ("'" ++ ·.name))}>"
      pure (s!"type {n.name}{tps}{lps} : elaborated at each use", none, [])
  | .shape _ n σ => do
      let _ ← (Env.top ds k).elabS LifeCtx.empty σ
      pure (s!"shape {n.name}", none, [])
  | .def_ _ n ps A V _ =>
      if ps.isEmpty then do
        -- At the persistent externs declared before it (SPEC §11).
        let xs ← externs (ds.extract 0 k)
        let T := (xs.map (·.2)).reverse
        let E : Env := { Env.top ds k sites with
          vars := (xs.map fun (x, B) => if B.persistent then some x else none).reverse,
          nExt := xs.length }
        let A' ← E.elabV LifeCtx.empty A
        let r ← chkV checkFuel E LifeCtx.empty T V A'
        modify (⟨k, [], LifeCtx.empty, T, A', r, r.t.absF LifeCtx.empty, rfl⟩ :: ·)
        pure (s!"def {n.name} : {ppVTy A'}", none, [(T.length, r.t)])
      else
        pure (s!"def {n.name}[{", ".intercalate (ps.map (·.name))}] : checked at each use", none, [])
  | .include sp n => throw ⟨sp, s!"internal error: `include {n.name}` was not resolved"⟩
  | .effect sp n _ _ => throw ⟨sp, s!"internal error: `effect {n.name}` was not elaborated"⟩
  | .handler sp n _ _ _ _ _ => throw ⟨sp, s!"internal error: `handler {n.name}` was not elaborated"⟩
  | .chandler sp h => throw ⟨sp, s!"internal error: `handler {h.name.name}` was not elaborated"⟩
  | .poly sp n _ _ _ _ _ => throw ⟨sp, s!"internal error: `poly {n.name}` was not elaborated"⟩
  | .extern _ n A => do
      let A' ← (Env.top ds k).elabV LifeCtx.empty A
      pure (s!"extern {n.name} : {ppVTy A'}", none, [])
  | .main sp C M => do
      let c ← checkMain ds k sites sp C M
      pure (s!"main : {ppCTy c.C}", some c, [(c.ctx.length, c.t)])

/-- Check a program, after elaborating it (`Frontend.Elab.elaborate`: the sugar of SPEC §11 and
§14): the checker sees only the elaborated program, which the report carries, so that nothing
after the check elaborates the program again. The lines of the libraries, when they are included,
are not reported. An error in code generated for a sugar names the sugar
(`Frontend.Elab.renderError`). A checked program is then rejected if it copies recursive data
implicitly (`Frontend.Check.implicitCopy`, on the typed terms the check returns): such a use is
written `clone(x)`. With `copies := false` that check is skipped: for a program rebuilt from the
printed core of one already checked with it (`run_io`'s wrapper). -/
def checkProgram (p : Program) (copies : Bool := true) : Except Error Report := do
  let el ← Frontend.Elab.elaborate p
  let ds := el.prog.decls.toArray
  let lib := el.lib
  let r : Except Error (Report × List (Nat × TExpr)) :=
    ((List.range ds.size).foldlM (init := ((⟨[], none, el, []⟩ : Report), [])) fun (acc, ts) k =>
      match (ds[k]? : Option Decl) with
      | some d => do
          let (line, m, t) ← checkDecl ds k el.sites d
          pure ({ acc with lines := if k < lib then acc.lines else acc.lines ++ [line],
                           main := m <|> acc.main }, ts ++ t)
      | none => pure (acc, ts) : CheckM _).run' []
  let (rep, terms) ← r.mapError (Frontend.Elab.renderError el.origins)
  -- What the elaboration reports about the program's loops (SPEC §16): total or div, and code
  -- that does not run after a loop that never ends.
  let loops := el.origins.filterMap fun (_, o) => match o with
    | .loop m => some ("loop " ++ m)
    | _ => none
  -- What the elaboration of effects reports (SPEC §18): each function's row, each handler's
  -- shape, and each operation's call; and at each handler site, its operations' lowering, read
  -- from the kinds the checker gave their clauses at the `handle` nodes of its name (SPEC §19).
  let handles := (terms.flatMap fun (_, t) => t.handleSites copiesFuel).eraseDups
  -- The kind of site the elaboration of effects claims, checked against the clause kinds.
  if let some (h, what) := siteKindMismatch handles then
    throw ⟨h.sp, s!"internal error: the site {h.n} is {what}"⟩
  let fx := el.origins.filterMap fun (sp, o) => match o with
    | .effects (.line k m) => some s!"{k} {sp.start.render}: {m}"
    | .effects (.site n head ops tail) =>
      some s!"lowering {sp.start.render}: {head}; {siteOps handles n ops}{tail}"
    | _ => none
  -- The assurance of `main`'s derivation (SPEC §29): unconditional, or under `PinLaw` at the
  -- relaxed rules it uses.
  let assurance := match rep.main with
    | some c => [c.pins.assurance]
    | none => []
  let rep := { rep with lines := rep.lines ++ loops.eraseDups ++ fx.eraseDups ++ assurance, handles }
  if !copies then return rep
  match implicitCopy terms with
  | some e => throw (Frontend.Elab.renderError el.origins e)
  | none => pure rep

/-! ### Soundness -/

/-- **The checker returns a typed derivation of the typed term** (`Frontend/Check/TDerives.lean`):
if `bcc` accepts a program, its `main`'s typed term `c.t` has a `TDerivesP` derivation at `Δ = ∅`
and the context of its externs. Every field of every node is the argument its rule was applied
at.  `[spec §3, §29]` -/
theorem checkProgram_typed {p : Program} {r : Report} {c : Checked}
    (_h : checkProgram p = .ok r) (_hc : r.main = some c) :
    TDerivesP LifeCtx.empty c.ctx c.t (.comp c.C) :=
  c.typedP

/-- **The typed derivation is tied** (decision R): when it uses no relaxed rule, `TDerivesAt Ξ` at
every effect context `Ξ` at which the rows it reads are.  `[spec §19]` -/
theorem checkProgram_typedAt {p : Program} {r : Report} {c : Checked}
    (_h : checkProgram p = .ok r) (_hc : r.main = some c) (hp : c.pins = []) :
    ∀ Ξ : EffCtx, SigsAt Ξ c.sigs → TDerivesAt Ξ LifeCtx.empty c.ctx c.t (.comp c.C) :=
  c.tied.1 hp

/-- **Every derivation the checker emits is tied** (decision R): if `bcc` accepts a program, its
`main`'s typed term erases to an `Expr` with a `CDerivesAt Ξ` derivation at `Δ = ∅` and the context
of its externs, at every effect context `Ξ` at which the rows the derivation reads at
`[perform]`, `[raise]` and `[handle]` are.  `[spec §19]` -/
theorem checkProgram_tied {p : Program} {r : Report} {c : Checked}
    (_h : checkProgram p = .ok r) (_hc : r.main = some c) (hp : c.pins = []) :
    ∀ Ξ : EffCtx, SigsAt Ξ c.sigs → CDerivesAt Ξ LifeCtx.empty c.ctx c.t.erase (.comp c.C) :=
  c.tied.tied.1 hp

/-- **At the program's own effect context**, whose abortive operations are affine (decision 63):
`main`'s derivation is `CDerivesAt c.Ξ`, and `c.Ξ` has no unrestricted operation answering `0`.
`[spec §18, §19]` -/
theorem checkProgram_tiedAt {p : Program} {r : Report} {c : Checked}
    (_h : checkProgram p = .ok r) (_hc : r.main = some c) (hp : c.pins = []) :
    CDerivesAt c.Ξ LifeCtx.empty c.ctx c.t.erase (.comp c.C) ∧ c.Ξ.NoUnrExn :=
  ⟨c.derivAt hp, noUnrExn_effCtxOf c.ok⟩

/-- **The checker's copies are `[let-poly]`'s premise** (decision 45): a `def` is checked at each
use, so `main`'s erasure holds a function at each of its uses. For a closed λ-value `λb` typed at
the empty context, `main`'s derivation gives `[let-poly]`'s, tied at the program's effect context,
of the let that binds `λb` once: its body is `main`'s erasure with `λb`'s occurrences replaced by
the bound variable (`Expr.unfill`), whose filling is `main`'s erasure (`subst_unfill`).
`[spec §18, §24]` -/
theorem checkProgram_letPoly {p : Program} {r : Report} {c : Checked}
    (_h : checkProgram p = .ok r) (_hc : r.main = some c) (hp : c.pins = []) {b : BoCa.Expr}
    {j : Jdg} (hcl : BoCa.Fig16.LogRel.Core.closedAt 0 (BoCa.Val.lam b).1 = true)
    (hV : CDerivesAt c.Ξ LifeCtx.empty [] (.val (.lam b)) j) :
    CDerivesAt c.Ξ LifeCtx.empty c.ctx
      (.app (.val (.lam (c.t.erase.unfill b 0))) (.val (.lam b))) (.comp c.C) :=
  BoCa.Fig16.LogRel.Core.CDerivesAt.letPoly_copy b hcl hV (c.derivAt hp)

/-- **A cell's class is closed under the program's swaps** (SPEC §5): every type `main` allocates a
cell at has a class in `c.cells`, which holds it and every type a `swap` node of `main`'s typed
term (or `fold_reuse`'s emptying swap) puts into a cell holding a type of the class. The swap
nodes' types are their rule's arguments, fixed by the derivation (`checkProgram_typed`).
`[spec §3, §5]` -/
theorem Checked.cells_closed (c : Checked) :
    (∀ A ∈ c.t.cells.1, ∃ cl ∈ c.cells, cl.root = A) ∧
      ∀ cl ∈ c.cells, cl.root ∈ cl.tys ∧ ∀ e ∈ c.t.cells.2, e.1 ∈ cl.tys → e.2 ∈ cl.tys :=
  cellsOkB_sound c.cellsOk

/-- **Soundness of the checker.** If `bcc` accepts a program and reports `assurance:
unconditional`, its `main`'s typed term erases to an `Expr` with a `CDerives` derivation at
`Δ = ∅` and the context of its externs. -/
theorem checkProgram_sound {p : Program} {r : Report} {c : Checked}
    (_h : checkProgram p = .ok r) (_hc : r.main = some c) (hp : c.pins = []) :
    CDerives LifeCtx.empty c.ctx c.t.erase (.comp c.C) :=
  c.deriv hp

/-- **Soundness of the checker, at every assurance.** If `bcc` accepts a program, its `main`'s
typed term erases to an `Expr` with a `CDerivesP` derivation at `Δ = ∅` and the context of its
externs.  `[spec §29]` -/
theorem checkProgram_soundP {p : Program} {r : Report} {c : Checked}
    (_h : checkProgram p = .ok r) (_hc : r.main = some c) :
    CDerivesP LifeCtx.empty c.ctx c.t.erase (.comp c.C) :=
  c.derivP

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The Fundamental Property at a checked `main` that uses no relaxed rule: it is semantically
well typed at every host. -/
theorem checked_sem (c : Checked) (hp : c.pins = []) :
    SemC LifeCtx.empty c.ctx c.t.erase c.C :=
  fundamentalC (c.deriv hp)

/-- Adequacy at a checked `main : F 1` with no externs that uses no relaxed rule: it runs from
the empty memory to `()` and the empty memory. -/
theorem checked_runs (c : Checked) (hp : c.pins = []) (hΓ : c.ctx = []) (hC : c.C = .ret .unit) :
    BoCa.BoLo.Steps BoCa.Adequacy.emptyMem c.t.erase BoCa.Adequacy.emptyMem
      (Expr.val BoCa.Val.unit) := by
  have h := c.deriv hp
  rw [hΓ, hC] at h
  exact adequacyC h

/-- The Fundamental Property at every checked `main`, under `PinLaw`.  `[spec §29]` -/
theorem checked_sem_pin (hPin : PinLaw (ℍ := ℍ)) (c : Checked) :
    SemC LifeCtx.empty c.ctx c.t.erase c.C :=
  fundamentalC_pin hPin c.derivP

/-- Adequacy at every checked `main : F 1` with no externs, under `PinLaw`.  `[spec §29]` -/
theorem checked_runs_pin (hPin : PinLaw (ℍ := ℍ)) (c : Checked) (hΓ : c.ctx = [])
    (hC : c.C = .ret .unit) :
    BoCa.BoLo.Steps BoCa.Adequacy.emptyMem c.t.erase BoCa.Adequacy.emptyMem
      (Expr.val BoCa.Val.unit) := by
  have h := c.derivP
  rw [hΓ, hC] at h
  exact adequacyC_pin hPin h

end Frontend.Check
