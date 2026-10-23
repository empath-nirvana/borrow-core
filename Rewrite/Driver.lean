import Rewrite.ReadBack
import Rewrite.Guard
import Rewrite.Report
import Backend.Driver

/-!
# Rewrite — the driver  `[spec §54]`

**The Core → Core rewriter** (#680), on the new backend's path (`Backend2.lirOf`): from a checked
program `k`, the rules over its typed program (none at step 0), the read-back of the typed program
into a program (`readBack`), the kernel's one re-check of that program at the counts the source's
check inferred (`checkEl` at `k.cnts`, no elaboration and no inference), and the guard
(`Rewrite/Guard.lean`). The result is `k` with the re-checked `main`; `exitsOnDivError` is carried
from the source's check (`CheckedProg.exits`). A refused re-check, a read-back with no rule for a
node and a failed guard are each a hard error: there is no fallback to the unrewritten program.

**The read-back is a program.** Its declarations are the elaborated program's (`k.el`) but its
`def`s, then one monomorphic `def` per key `(decl, targs)` of a `use` node of `main`'s typed term,
its body read back once from the key's typed body (inner keys first), then `main` read back. Each
use reads back as a reference to its key's declaration; no body is placed at its use. A key's
declaration carries the elaborated program's key of the `def` (`DefKey`), its body naming the
source's `def` at its type arguments, so that copies the source shares stay shared.

The read-back carries verbatim the records the checker's input holds and its output keeps: a
`def`'s key (from the elaborated program) and a handler site's record (from the node's `HSite`),
so that the re-checked program is the source's. No rule reads them (the scope's §2).
-/

namespace Rewrite
open Frontend (Span Ident Decl Program DefKey)
open Frontend.Check (CVTy Checked ppVTy checkEl)
open BoCa.Fig16.LogRel.Core.Check (TExpr TInfo TScope)

/-- A key's first use in `main`'s typed term: the `def`'s name, its type at the key, its typed
body, and the use's context: its number of slots and of extern slots, and its lifetime context. -/
structure Use where
  key : Key
  name : String
  A : CVTy
  body : TExpr
  len : Nat
  nExt : Nat
  Δ : BoCa.Lifetime.LifeCtx
  sp : Span

/-- **The keys of a typed term**, each at its first use, inner keys (those a key's body uses)
before it. -/
def collect : Nat → Nat → Nat → BoCa.Lifetime.LifeCtx → TExpr → List Use → Except String (List Use)
  | 0, _, _, _, _, _ => throw "rewrite: a term nested too deeply to collect its keys"
  | f + 1, len, nExt, Δ, t, acc => do
    match t with
    | .use i (.val A) name decl targs _ b =>
      if acc.any (·.key == (decl, targs)) then pure acc
      else do
        let acc ← collect f len nExt Δ b acc
        pure (acc ++ [⟨(decl, targs), name, A, b, len, nExt, Δ, i.sp⟩])
    | .use .. => throw "rewrite: a `use` node at a computation type"
    | t =>
      -- The lifetime context of the children: `Fun`'s binder, and R1's at its body.
      let Δc : BoCa.Lifetime.LifeCtx := match t with
        | .allI _ _ x b _ _ _ | .lendR _ _ x b _ _ _ _ _ => Δ.extend x b
        | _ => Δ
      t.children.foldlM (init := acc) fun acc (sc, c) => match sc with
        | .push n => collect f (len + n) nExt Δc c acc
        | .fresh n => collect f n 0 Δc c acc

/-- The declaration name of a key: its `def`'s name and its position among the keys, which no
program writes. -/
def keyName (u : Use) (k : Nat) : String := s!"{u.name}#{k}"

/-- The elaborator's key of a key's declaration: the elaborated program's key of the `def`
(`Elaborated.keys`, by the `def`'s name, as the checker finds it at a use), carried verbatim, its
body naming the `def` (or its copy) at the key's type arguments, so that two keys share a body
exactly when the source's do. No rule reads it. -/
def keyOf (keys : List DefKey) (u : Use) (name : String) : DefKey :=
  let dk := keys.find? (·.name == u.name)
  let body := (dk.map (·.body)).getD u.name
  { name, origin := (dk.map (·.origin)).getD u.name, keys := (dk.map (·.keys)).getD [],
    body := s!"{body}[{", ".intercalate (u.key.2.map ppVTy)}]" }

/-- The names of the externs of a program, in declaration order. -/
def externNames (ds : List Decl) : List String :=
  ds.filterMap fun | .extern _ n _ => some n.name | _ => none

/-- **The read-back of a checked program**: the elaborated program `el` with its `def`s replaced
by one monomorphic `def` per key, and `main` read back from `c`. -/
def readBack (el : Frontend.Elab.Elaborated) (c : Checked) (tbl : Frontend.Check.CntTable) :
    Except String (Frontend.Elab.Elaborated × Nat) := do
  let ds := el.prog.decls
  let some (msp, _) := ds.findSome? (fun | .main sp C _ => some (sp, C) | _ => none)
    | throw "rewrite: the program has no `main`"
  let exts := externNames ds
  let extVars : List (Option String) := (exts.map some).reverse
  let uses ← collect fuel c.ctx.length exts.length ⟨[]⟩ c.t []
  let names := uses.zipIdx.map fun (u, k) => (u.key, keyName u k)
  let cx0 : Cx := { vars := extVars, nExt := exts.length, names, tbl }
  let defs ← uses.zipIdx.mapM fun (u, k) => do
    unless u.len ≥ u.nExt do throw "rewrite: a use's context is shorter than its externs"
    let vars := List.replicate (u.len - u.nExt) none ++ (if u.nExt == 0 then [] else extVars)
    let V ← (← rd fuel { cx0 with vars, nExt := u.nExt, Δ := u.Δ } true false u.body).val
    let A ← rbV ⟨tbl, u.Δ⟩ u.sp fuel [] u.A
    pure (Decl.def_ u.sp ⟨keyName u k, u.sp⟩ [] A V .none)
  let C ← rbC ⟨tbl, ⟨[]⟩⟩ msp fuel [] c.C
  let M ← (← rd fuel cx0 true false c.t).comp
  let kept := ds.zipIdx.filter fun (d, _) => match d with
    | .def_ .. | .main .. => false
    | _ => true
  let lib := (kept.filter (·.2 < el.lib)).length
  let ds' := kept.map (·.1) ++ defs ++ [Decl.main msp C M]
  let keys := uses.zipIdx.map fun (u, k) => keyOf el.keys u (keyName u k)
  pure ({ el with prog := ⟨ds'⟩, lib, keys := el.keys ++ keys }, uses.length)

/-- **The rewriter's run** on a checked program: no rule (step 0), the read-back, the kernel's one
re-check at the source's counts, and the guard. -/
def run (k : Backend.CheckedProg) : Except String (Backend.CheckedProg × Report) := do
  let c := k.main
  let (el', nkeys) ← readBack k.el c k.cnts
  let (rep', terms') ← (checkEl el' k.cnts).mapError fun e =>
    s!"rewrite: the kernel refuses the rewritten program at {e.span.start.render}: {e.msg}"
  let some c' := rep'.main | throw "rewrite: the rewritten program has no `main`"
  unless externNames el'.prog.decls == externNames k.el.prog.decls do
    throw "guard G-main: the rewritten program has other externs"
  guard fuel c c' [] [] terms'
  pure ({ k with main := c', rewritten := true }, { keys := nkeys, decls := el'.prog.decls.length })

/-- **The identity criterion** of step 0, between the source's checked `main` `c` and the
rewritten `c′`: `main`'s erasure, each key's body's erasure (the key's first use in each), and the
typed term's mismatches by node kind. -/
def identity (c c' : Checked) : Except String Identity := do
  let src ← collect fuel c.ctx.length 0 ⟨[]⟩ c.t []
  let out ← collect fuel c'.ctx.length 0 ⟨[]⟩ c'.t []
  let keysEq := (src.zip out).filter (fun (a, b) => a.body.erase == b.body.erase) |>.length
  pure { mainEq := c.t.erase == c'.t.erase, keysEq, keys := src.length,
         mismatches := ← mismatches fuel c.t c'.t [] }

end Rewrite
