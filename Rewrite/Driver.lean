import Rewrite.ReadBack
import Rewrite.Guard
import Rewrite.Report
import Rewrite.R0
import Rewrite.Tail
import Backend.Driver
import Frontend.Elab.RenameLife

/-!
# Rewrite — the driver  `[spec §54]`

**The Core → Core rewriter** (#680), on the new backend's path (`Backend2.lirOf`): from a checked
program `k`, the rules over its typed program (R0, then R1, `rules`), the read-back of the typed program
into a program (`readBack`), the kernel's one re-check of that program at the counts the source's
check inferred (`checkEl` at `k.cnts`, no elaboration and no inference), and the guard
(`Rewrite/Guard.lean`). The result is `k` with the re-checked `main`; `exitsOnDivError` is carried
from the source's check (`CheckedProg.exits`). A refused re-check, a read-back with no rule for a
node and a failed guard are each a hard error: there is no fallback to the unrewritten program.

**The read-back is a program.** Its declarations are the elaborated program's (`k.el`) but its
`def`s, then one declaration per instance of a `def` that `main`'s typed term uses (`Key`, the
checker's instance key: declaration, type arguments, lifetime context, extern context), its body
read back once from the instance's typed body (inner instances first), then `main` read back.
Each use reads back as a reference to its instance's declaration; no body is placed at its use.
The monomorphic instances of one `def` at one type arguments and extern context share one
declaration, the `def`'s text at them, which the checker instantiates at each use; polymorphic
instances whose declarations read back alike share one.

**A lifetime-polymorphic declaration.** An instance checked under a use's lifetime binders may
mention them: through its type arguments, or through a type the program writes with `dom`, which
elaborates to the meet of the context. (A bound or witness the program writes `dom` is read back
as `dom`, `TInfo.dom`, and mentions none.) A top-level declaration cannot name them, so such an
instance is declared polymorphic in its whole lifetime context, by Core's `∀` (`VTy.all`,
`Fun 'x < @b`) at each of the context's variables with its bound, outermost first, and each use
instantiates it at those variables (`inst`); its bounds name only variables before them in the
context, so Core states every one. The checker checks the declaration's body again at each use,
at the use's context extended by the abstraction's binders: its erasure is the source's, under the
instantiation (`beta`, `Rewrite.identity`).

**R1's works** (`Rewrite/Tail.lean`) are declarations of the read-back program: each work a
`perform` reaches (`worksUsed`), read back once at the empty context, after the instances its body
uses and before every declaration that calls it; a `use` of one reads back as a reference to it.

**Records carried, not rebuilt** (the scope's §2, amended by the user's decision of 2026-10-23):
a use's key (`TInfo.key`, which the checker records) is the declaration's key, named by it; a
handler site's record is the one the checker records on its node (`TInfo.srec`). No rule reads
them.
-/

namespace Rewrite
open Frontend (Span Ident Decl Program DefKey)
open Frontend.Check (CVTy Checked checkEl)
open BoCa.Fig16.LogRel.Core.Check (TExpr TInfo TScope)

/-- An instance's first use in `main`'s typed term: the `def`'s name, its type at the instance,
its typed body, the key the checker records at the use, and the use's context: its number of
slots and of extern slots, and its lifetime context. -/
structure Use where
  key : Key
  name : String
  A : CVTy
  body : TExpr
  dkey : Option DefKey
  len : Nat
  nExt : Nat
  Δ : BoCa.Lifetime.LifeCtx
  sp : Span

/-- **The instances of a typed term**, each at its first use, inner instances (those an instance's
body uses) before it. A use of one of R1's works (a declaration from `workBase`) is not one: the
work's declaration is read back on its own (`readBack`). -/
def collect : Nat → Nat → Nat → BoCa.Lifetime.LifeCtx → TExpr → List Use → Except String (List Use)
  | 0, _, _, _, _, _ => throw "rewrite: a term nested too deeply to collect its instances"
  | f + 1, len, nExt, Δ, t, acc => do
    match t with
    | .use i (.val A) name decl targs _ b =>
      if decl ≥ workBase then pure acc else
      let k : Key := (decl, targs, Δ.entries, nExt)
      if acc.any (·.key == k) then pure acc
      else do
        let acc ← collect f len nExt Δ b acc
        pure (acc ++ [⟨k, name, A, b, i.key, len, nExt, Δ, i.sp⟩])
    | .use .. => throw "rewrite: a `use` node at a computation type"
    | t =>
      -- The lifetime context of the children: `Fun`'s binder, and R1's at its body.
      let Δc : BoCa.Lifetime.LifeCtx := match t with
        | .allI _ _ x b _ _ _ | .lendR _ _ x b _ _ _ _ _ => Δ.extend x b
        | _ => Δ
      t.children.foldlM (init := acc) fun acc (sc, c) => match sc with
        | .push n => collect f (len + n) nExt Δc c acc
        | .fresh n => collect f n 0 Δc c acc

/-- The read-back mentions the lifetime variable `v` (`Frontend.Comp.mentionsLife`'s renaming).
No binder of an instance's body is a variable of its lifetime context: a binder is numbered fresh
for the context the body is checked at (`LifeCtx.freshVar`). -/
def mentionsV (v : Nat) (V : Frontend.Val) : Bool :=
  V.renameLife (fun s y => .var s (if y == lname v then y ++ "'" else y)) != V

def mentionsT (v : Nat) (A : Frontend.VTy) : Bool :=
  A.renameLife (fun s y => .var s (if y == lname v then y ++ "'" else y)) != A

/-- An instance's declaration, named `name`: its type and body read back; polymorphic in its
lifetime context (outermost first) when they mention one of its variables. -/
def declOf (tbl : Frontend.Check.CntTable) (cx : Cx) (u : Use) (name : String) :
    Except String (Decl × List Nat) := do
  let V ← (← rd fuel cx u.body).val
  let A ← rbV tbl u.sp fuel [] u.A
  let ctx := u.Δ.entries.reverse
  if ctx.any fun (v, _) => mentionsV v V || mentionsT v A then
    let A' := ctx.foldr (fun (x, b) A => .all u.sp ⟨lname x, u.sp⟩ (rbL u.sp b) A) A
    let V' := ctx.foldr (fun (x, b) V =>
      .thunkv u.sp (.lamL u.sp ⟨lname x, u.sp⟩ (rbL u.sp b) (.ret u.sp V))) V
    pure (.def_ u.sp ⟨name, u.sp⟩ [] A' V' .none, ctx.map (·.1))
  else pure (.def_ u.sp ⟨name, u.sp⟩ [] A V .none, [])

/-- The declaration with another name. -/
def Decl.rename (x : String) : Decl → Decl
  | .def_ sp n ps A V mk => .def_ sp { n with name := x } ps A V mk
  | d => d

/-- The names of the externs of a program, in declaration order. -/
def externNames (ds : List Decl) : List String :=
  ds.filterMap fun | .extern _ n _ => some n.name | _ => none

/-- **The read-back of a checked program**: the elaborated program `el` with its `def`s replaced
by one declaration per instance (`declOf`), and `main` read back from `t` (`c`'s typed term, or the rules' rewrite of it); the number of
instances, of declarations, and of polymorphic ones. -/
def readBack (el : Frontend.Elab.Elaborated) (c : Checked) (tbl : Frontend.Check.CntTable)
    (t : TExpr := c.t) (works : List (Nat × String × TExpr) := []) :
    Except String (Frontend.Elab.Elaborated × Nat × Nat × Nat) := do
  let ds := el.prog.decls
  let some (msp, _) := ds.findSome? (fun | .main sp C _ => some (sp, C) | _ => none)
    | throw "rewrite: the program has no `main`"
  let exts := externNames ds
  let extVars : List (Option String) := (exts.map some).reverse
  -- R1's works the term uses (SPEC §54), each a declaration at the empty context (a work is closed
  -- and mentions no lifetime of its node's context, the admission), after the instances its body
  -- uses; a work refers only to the works of names R1 rewrote after its own, so those first.
  let used := (← worksUsed fuel t).eraseDups
  let mut uses : List Use := []
  for (d, nm, w) in works.reverse do
    if used.contains d then
      let .val A := w.jdg | throw "rewrite: an R1 work at a computation type"
      uses ← collect fuel 0 0 ⟨[]⟩ w uses
      uses := uses ++ [⟨(d, [], [], 0), nm, A, w, none, 0, 0, ⟨[]⟩, w.info.sp⟩]
  uses ← collect fuel c.ctx.length exts.length ⟨[]⟩ t uses
  -- Each instance's declaration, inner instances first; one declaration per distinct read-back.
  let mut decls : List (Key × DeclOf) := []
  let mut defs : List Decl := []
  let mut keys : List DefKey := []
  let mut poly := 0
  let mut mono : List ((Nat × List CVTy × Nat) × String) := []
  for u in uses do
    unless u.len ≥ u.nExt do throw "rewrite: a use's context is shorter than its externs"
    let vars := List.replicate (u.len - u.nExt) none ++ (if u.nExt == 0 then [] else extVars)
    let cx : Cx := { vars, nExt := u.nExt, Δ := u.Δ, decls, tbl }
    let name := s!"{u.name}#{defs.length}"
    let (d, vs) ← declOf tbl cx u name
    -- A monomorphic instance's declaration is the `def`'s text at its type arguments, which does
    -- not depend on the lifetime context: the instances of one `def` at one type arguments and
    -- extern context share it, and the checker instantiates it at each use.
    let mk := (u.key.1, u.key.2.1, u.key.2.2.2)
    let shared := if vs.isEmpty then mono.lookup mk else
      (defs.find? (fun e => Decl.rename name e == d)).bind fun
        | .def_ _ n _ _ _ _ => some n.name
        | _ => none
    match shared with
    | some n => decls := decls ++ [(u.key, ⟨n, vs⟩)]
    | none =>
      if vs.isEmpty then mono := mono ++ [(mk, name)]
      decls := decls ++ [(u.key, ⟨name, vs⟩)]
      defs := defs ++ [d]
      if !vs.isEmpty then poly := poly + 1
      if let some k := u.dkey then keys := keys ++ [{ k with name }]
  let cx0 : Cx := { vars := extVars, nExt := exts.length, decls, tbl }
  let C ← rbC tbl msp fuel [] c.C
  let M ← (← rd fuel cx0 t).comp
  let kept := ds.zipIdx.filter fun (d, _) => match d with
    | .def_ .. | .main .. => false
    | _ => true
  let lib := (kept.filter (·.2 < el.lib)).length
  let ds' := kept.map (·.1) ++ defs ++ [Decl.main msp C M]
  pure ({ el with prog := ⟨ds'⟩, lib, keys := el.keys ++ keys }, uses.length, defs.length, poly)

/-- What the rules made of a typed program: the source's term as they read it (numbered, where a
rule rewrites it), the rewritten term, R0's keys and record, R1's names and record, R1's works
(each its declaration, name and typed term), `π`'s `inv(R1, work)` (the ids of the binders R1 drops
that are no binder of a declared work), `π` from each `perform` to its call, and the names the
licence leaves whose nodes R1 writes as `[handle]`'s. -/
structure Ruled where
  t₀ : TExpr
  t : TExpr
  keys : List (AbortName × R0Status)
  st : AbStats
  r1 : List UInt32 := []
  tst : TlStats := {}
  works : List (Nat × String × TExpr) := []
  inv : List String := []
  calls : List (String × UInt32 × UInt32) := []
  /-- The names the licence leaves whose nodes R1 writes as `[handle]`'s. -/
  r1v : List UInt32 := []

/-- **The rules over the typed program**: R0 over each name its keys rewrite, in their order
(`r0Keys`, `ab`), then R1 over each name it admits, in its order (`r1Keys`, `r1Pass`), on `main`'s
typed term and every `def` body at each use. -/
def rules (c : Checked) (lic : List (UInt32 × Frontend.Check.Licence)) (seed : Seed := .none) :
    Except String Ruled := do
  let keys ← r0Keys c fuel
  let tails := (← Frontend.Check.tailNodes [c.t]).map (·.1)
  -- The source's binders numbered (`numberBinders`) where a rule will rewrite it: `π`'s ids.
  let t₀ ← if keys.any (·.2 == .rewritten) || !tails.isEmpty then numberBinders c.t else pure c.t
  let mut t := t₀
  let mut st : AbStats := { seed }
  for (a, s) in keys do
    if s == .rewritten then
      let (t', st') ← (ab a t).run st
      t := t'
      st := st'
  -- R1 (SPEC §54), on R0's rewrite: each admitted name's works the declarations from `workBase`;
  -- each node of a name the licence leaves written as the `[handle]` node it erases to.
  let (names, left) ← r1Keys lic c t fuel
    (keys.filterMap fun (a, s) => if s == .rewritten then some a.n else none)
  let mut tst : TlStats := { seed }
  let mut works : List (Nat × String × TExpr) := []
  let mut next := workBase
  for a in names do
    let ((t', prev, ws), tst') ← (r1Pass a next t works).run tst
    t := t'
    works := prev ++ ws
    tst := tst'
    next := next + a.works.length
  for n in left do
    let (t', tst') ← (tToV n fuel t).run tst
    t := t'
    tst := tst'
  -- `π`'s `inv(R1, work)`: the dropped binders that are no binder of a declared work (a work a
  -- call reaches); a declared work's binder has its image, which G-qual checks.
  let used := (← worksUsed fuel t).eraseDups
  let mut declared : List String := []
  for (d, _, w) in works do
    if used.contains d then declared := declared ++ ((← nodeBinders fuel w).filterMap (·.id?))
  let inv := (tst.inv.filterMap (·.id?)).filter (!declared.contains ·)
  pure { t₀, t, keys, st, r1 := names.map (·.n), r1v := left, tst, works, inv, calls := tst.calls }

/-- The source nodes R0 rewrites, by rule. -/
structure R0Count where
  handles : Nat := 0
  performs : Nat := 0
  raises : Nat := 0
  lets : Nat := 0
  thens : Nat := 0
  subs : Nat := 0
  forwards : Nat := 0
  ulends : Nat := 0
  deriving Inhabited

/-- R0's nodes of a typed term outside the bodies of its uses, for the names `ruled`: their
handler nodes, the `perform`s of other names, `[let]`s, `[then]`s, `[sub]`s into a row and other
names' handler nodes at a row holding one, their `raise`s, and the unwinding borrows at a row
holding one. -/
def r0Nodes (ruled : List UInt32) : Nat → TExpr → R0Count → Except String R0Count
  | 0, _, _ => throw "rewrite: a term nested too deeply to count"
  | f + 1, t, c => do
    let has (S : BoCa.Fig16.LogRel.Core.Row) := S.any (ruled.contains ·.n)
    let c := match t with
      | .effHandleV _ _ S _ _ n .. | .effHandleVB _ _ S _ _ n .. | .effHandleT _ _ S _ _ _ n ..
      | .effHandleL _ _ S _ _ _ _ n .. =>
        if ruled.contains n then { c with handles := c.handles + 1 }
        else if has S then { c with forwards := c.forwards + 1 } else c
      | .effPerform _ _ S _ _ => if has S then { c with performs := c.performs + 1 } else c
      | .effRaise _ _ _ o _ _ => if ruled.contains o.n then { c with raises := c.raises + 1 } else c
      | .effLet _ _ _ _ S _ _ _ => if has S then { c with lets := c.lets + 1 } else c
      | .effThen _ _ _ _ S _ _ _ _ _ _ => if has S then { c with thens := c.thens + 1 } else c
      | .effSub _ _ S S' _ _ => if !has S && has S' then { c with subs := c.subs + 1 } else c
      | .withbor1U _ _ _ _ S _ _ | .withbor2U _ _ _ _ S _ _ | .withbor3U _ _ _ _ _ S _ _
      | .withloadU _ _ _ _ _ S _ | .sliceBorrowMU _ _ _ _ S _ _ | .sliceBorrowIU _ _ _ _ S _ _ =>
        if has S then { c with ulends := c.ulends + 1 } else c
      | _ => c
    match t with
    | .use .. => pure c
    | _ => t.children.foldlM (init := c) fun c (_, t') => r0Nodes ruled f t' c

/-- **R0's rewrites, per instance**: the source nodes R0 rewrites in `main`'s typed term and in
each instance's body once (`collect`), as the new backend's erasure line counts nodes. -/
def r0Counts (c : Checked) (ruled : List UInt32) : Except String R0Count := do
  let uses ← collect fuel c.ctx.length 0 ⟨[]⟩ c.t []
  uses.foldlM (init := ← r0Nodes ruled fuel c.t {}) fun acc u => r0Nodes ruled fuel u.body acc

/-- R1's nodes of a typed term outside the bodies of its uses, for the names `ruled`: their
handler nodes, and their `perform`s, added to `acc`. -/
def r1Nodes (ruled : List UInt32) : Nat → TExpr → Nat × Nat → Except String (Nat × Nat)
  | 0, _, _ => throw "rewrite: a term nested too deeply to count"
  | f + 1, t, (h, p) => do
    let acc := match t with
      | .effHandleT _ _ _ _ _ _ n .. => if ruled.contains n then (h + 1, p) else (h, p)
      | .effPerform _ _ _ o _ => if ruled.contains o.n then (h, p + 1) else (h, p)
      | _ => (h, p)
    match t with
    | .use .. => pure acc
    | _ => t.children.foldlM (init := acc) fun acc (_, t') => r1Nodes ruled f t' acc

/-- **R1's rewrites, per instance**: the nodes R1 removes and the `perform`s it makes calls, in
`main`'s typed term and in each instance's body once (`collect`). -/
def r1Counts (c : Checked) (ruled : List UInt32) : Except String (Nat × Nat) := do
  let uses ← collect fuel c.ctx.length 0 ⟨[]⟩ c.t []
  uses.foldlM (init := ← r1Nodes ruled fuel c.t (0, 0)) fun acc u => r1Nodes ruled fuel u.body acc

/-- **The rewriter's run** on a checked program: the rules (R0), the read-back, the kernel's one
re-check at the source's counts, and the guard. `seed` plants a fault in R0 for the reject tests
(`Seed`); the compile passes none. -/
def run (k : Backend.CheckedProg) (seed : Seed := .none) :
    Except String (Backend.CheckedProg × Report) := do
  let c := k.main
  let r ← rules c k.licence seed
  let keys := r.keys
  let (el', nkeys, ndecls, poly) ← readBack k.el c k.cnts r.t r.works
  let ruledAbort := keys.filterMap fun (a, s) => if s == .rewritten then some a.n else none
  let rows := (if ruledAbort.isEmpty then "" else s!" (R0 at the names {ruledAbort})") ++
    (if r.r1.isEmpty then "" else s!" (R1 at the names {r.r1})") ++
    (if r.r1v.isEmpty then "" else s!" (R1's `[handle]` at the names {r.r1v})")
  let (rep', terms') ← (checkEl el' k.cnts).mapError fun e =>
    s!"rewrite: the kernel refuses the rewritten program{rows} at {e.span.start.render}: {e.msg}"
  let some c' := rep'.main | throw "rewrite: the rewritten program has no `main`"
  unless externNames el'.prog.decls == externNames k.el.prog.decls do
    throw "guard G-main: the rewritten program has other externs"
  let π ← guard fuel c c' r.t₀ ruledAbort r.r1 (r.st.bangs + r.tst.bangs) r.inv r.calls terms'
  let r0 := keys.map fun (a, s) => (a.n, match s with
    | .rewritten => "rewritten"
    | .left r => s!"left: {r}")
  let used := (← worksUsed fuel r.t).eraseDups
  pure ({ k with main := c', rewritten := true },
    { keys := nkeys, decls := ndecls, poly, r0, stats := r.st,
      moved := (π.filter fun (k, img) => match img with
        | .binder k' => k' != k
        | _ => false).length,
      r1 := r.r1, r1v := r.r1v, r1calls := r.tst.performs, r1nodes := r.tst.handles,
      r1works := used.length })

/-- **The identity criterion** of step 0, between the source's checked `main` `c` and the
rewritten `c′`: the typed terms compared node by node and field by field at every use
(`cmpT`), and `main`'s erasure: the source's (`same`), or other only at the instantiations of
lifetime-polymorphic declarations (`beta`: no mismatch outside those declarations' bodies, whose
erasures are the source's). -/
def identity (c c' : Checked) : Except String Identity := do
  let ms ← cmpT "" fuel c.t c'.t []
  let uses := (← collect fuel c.ctx.length 0 ⟨[]⟩ c.t []).length
  -- Other than the source's only at the instantiations of polymorphic declarations: no mismatch
  -- outside their bodies, and none of their bodies' erasures.
  let outside := ms.filter fun (m, _) => !m.startsWith "poly:"
  let erasure := if c.t.erase == c'.t.erase then "same" else if outside.isEmpty then "beta" else "differs"
  pure { erasure, uses, mismatches := ms }

end Rewrite
