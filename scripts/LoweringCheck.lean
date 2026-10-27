import Backend.Driver
import Backend2.Driver
import Lowering.Own
import Lowering.LIRPrint

/-!
# `own` on the pure corpus  (`scripts/check-lowering.sh`, SPEC §54)

    lake build lowering-check && .lake/build/bin/lowering-check <file.bc>…

Each program is checked as `bcc check` does. A program is in the pure fragment when it has no
capability (`main` has no externs) and its typed term is in `Lowering.pureT`. For each:

* the masks' agreement with the leaves (`Lowering.agreeAt`), which `Lowering.agreeAt_of_typed`
  proves of every typed term in the fragment, is decided as well;
* `own`'s output is decided low as well (`Lowering.lowB`, sound by `Lowering.lowB_sound`), the
  kernel's constants being `copy`, `forget` and the erasures of the term's constant nodes;
* the source interpreter runs `own`'s output and the erasure, and the reports (the value and the
  live cells) must agree.

When `own`'s output is in the print's core fragment (`Lowering.coreB`, only `copy` and `forget` as
constants: SPEC §56), it is also printed (`Lowering.lirOf`) and run by the LIR interpreter, whose
value must be the source run's (literals as their words) with an empty frame and no live object.
Its static counts are listed beside the new backend's (`Backend2.lirOf`): functions, nodes,
closures, dynamic calls and direct calls.

A program outside the fragment is listed as skipped, with the reason. The exit status is `1` when
any program in the fragment fails a check.
-/

open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

namespace LoweringCheck

/-- The depth bound of the walks: the checker's. -/
def walkFuel : Nat := 1 <<< 20

/-- The erasures of the constant nodes of `t`, each once. -/
def consts : Nat → List Expr → TExpr → List Expr
  | 0, acc, _ => acc
  | n + 1, acc, t =>
    let acc := if Lowering.constNode t && !acc.contains t.erase then t.erase :: acc else acc
    t.children.foldl (fun a (_, c) => consts n a c) acc

/-- Where `explicitB` fails first, for the report: the failing node, printed short. -/
def why (isConst : Expr → Bool) : Nat → Expr → Option String
  | 0, _ => none
  | n + 1, e =>
  if isConst e then none else
  let sub (xs : List Expr) : Option String := xs.findSome? (why isConst n)
  match e with
  | .var _ | .unit | .loc _ | .prim _ => none
  | .pair a b | .seq a b | .app a b | .letpair a b => match sub [a, b] with
    | some w => some w
    | none => match e with
      | .letpair _ b => if Lowering.once (Lowering.occ b 0) && Lowering.once (Lowering.occ b 1)
          then none else some s!"letpair binders: {repr (Lowering.occ b 0)} {repr (Lowering.occ b 1)} in {(reprStr e).take 300}"
      | _ => none
  | .inj₁ a | .inj₂ a => why isConst n a
  | .lam b => match why isConst n b with
    | some w => some w
    | none => if Lowering.once (Lowering.occ b 0) && Lowering.capOnceB b then none
        else some s!"lam: binder {repr (Lowering.occ b 0)} caps {Lowering.capOnceB b} in {(reprStr e).take 400}"
  | .case s a b => match sub [s, a, b] with
    | some w => some w
    | none => if (a == BoLo.stuckE && b == BoLo.stuckE) || (Lowering.once (Lowering.occ a 0) && Lowering.once (Lowering.occ b 0)) then none
        else some s!"case arms {repr (Lowering.occ a 0)} {repr (Lowering.occ b 0)} in {(reprStr e).take 300}"

/-- The LIR value a first-order source value prints to, as `Lowering.VRel` relates them. -/
def lvOf : Expr → Option Backend2.LV
  | .unit => some .unit
  | .prim (.lit c) => some (Backend2.litV c)
  | .pair a b => do pure (.pair (← lvOf a) (← lvOf b))
  | .inj₁ a => do pure (.inj false (← lvOf a))
  | .inj₂ a => do pure (.inj true (← lvOf a))
  | _ => none

/-- Equality of first-order LIR values; a closure, a location or a family is equal to nothing. -/
def lvEq : Backend2.LV → Backend2.LV → Bool
  | .unit, .unit => true
  | .int a, .int b => a == b
  | .pair a b, .pair c d => lvEq a c && lvEq b d
  | .inj r a, .inj r' b => r == r' && lvEq a b
  | _, _ => false

/-- Static counts of an LIR term: nodes, closures, dynamic calls, direct calls. -/
def tmCounts : Backend2.Tm → Nat × Nat × Nat × Nat
  | .clos _ _ => (1, 1, 0, 0)
  | .app _ _ | .app0 _ | .sel _ _ => (1, 0, 1, 0)
  | .call _ _ => (1, 0, 0, 1)
  | .letv _ e b => add (tmCounts e) (tmCounts b)
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => add (1, 0, 0, 0) (tmCounts b)
  | .case _ _ b₁ _ b₂ => add (tmCounts b₁) (tmCounts b₂)
  | _ => (1, 0, 0, 0)
where add (a b : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (a.1 + b.1 + 1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

/-- A program's static counts: `fns nodes clos dyn direct`. -/
def progCounts (p : Backend2.Prog) : String :=
  let cs := p.fns.foldl (fun a f => tmCounts.add a (tmCounts f.body)) (tmCounts p.main)
  s!"fns {p.fns.size} nodes {cs.1} clos {cs.2.1} dyn {cs.2.2.1} direct {cs.2.2.2}"

/-- Print `e` and run it: `none` when it matches the source run, else the mismatch. -/
def printRun (e : Expr) : Except String String := do
  let p := Lowering.lirOf e
  let (v, s) ← (Backend2.eval p Backend.runFuel p.mainTy p.main).run { data := p.data }
  let (w, _) ← Backend.runSource Backend.runFuel Mem.empty e
  if !s.frame.isEmpty then throw s!"frame not empty: {s.frame.toList.map (·.1)}"
  if !s.objs.isEmpty then throw s!"{s.objs.size} live objects"
  match lvOf w.1, v with
  | some lv, v => if lvEq lv v then pure (progCounts p) else throw "value differs"
  | none, .clos _ _ => pure (progCounts p)
  | none, _ => throw "a function's print is not a closure"

end LoweringCheck

open LoweringCheck in
def main (files : List String) : IO UInt32 := do
  let mut bad : Nat := 0
  let mut pure : Nat := 0
  let mut skipped : Nat := 0
  let mut printed : Nat := 0
  for f in files do
    let src ← IO.FS.readFile f
    match Backend.checkedOf f src with
    | .error e =>
      IO.println s!"skip {f}: does not check: {(e.splitOn "\n").headD ""}"
      skipped := skipped + 1
    | .ok k =>
      if k.io.isSome then
        IO.println s!"skip {f}: has capabilities (U5)"
        skipped := skipped + 1
      else if !Lowering.pureT k.main.t then
        IO.println s!"skip {f}: outside the pure fragment"
        skipped := skipped + 1
      else
        pure := pure + 1
        let e := Lowering.own k.main.t
        let cs := consts walkFuel [BoCa.copy, BoCa.forget] k.main.t
        let low := Lowering.lowB (cs.contains ·) k.main.ctx.length e &&
          Lowering.agreeAt [] k.main.t
        let src := Backend.interpSource Backend.runFuel k.main.e
        let lowered := Backend.interpSource Backend.runFuel e
        let same := match src, lowered with
          | .ok a, .ok b => a.out == b.out
          | _, _ => false
        let show' (r : Except String Backend.Output) : String := match r with
          | .ok o => (String.fromUTF8? o.out).getD "<bytes>" |>.trimAscii |>.toString
          | .error m => s!"error: {m}"
        if low && same then
          IO.println s!"ok {f}: {show' lowered}"
          if Lowering.coreB e && Lowering.explicitB Lowering.isCF e then
            match printRun e with
            | .ok counts =>
              printed := printed + 1
              let b2 := match Backend2.lirOf k with
                | .ok (q, _) => progCounts q
                | .error m => s!"error: {(m.splitOn "\n").headD ""}"
              IO.println s!"  print: {counts}; backend2: {b2}"
            | .error m =>
              bad := bad + 1
              IO.println s!"FAIL {f}: print: {m}"
        else
          bad := bad + 1
          IO.println s!"FAIL {f}: low={low} same={same}; erasure: {show' src}; own: {show' lowered}"
          if !low then
            IO.println s!"  agree={Lowering.agreeAt [] k.main.t} explicit={Lowering.explicitB (cs.contains ·) e} effFree={Lowering.effFreeB e} ctx={(List.range k.main.ctx.length).all fun j => Lowering.once (Lowering.occ e j)} bound={Lowering.fvBound e}"
            IO.println s!"  {(why (cs.contains ·) walkFuel e).getD "-"}"
  IO.println s!"lowering-check: {pure} in the pure fragment, {printed} printed and run, {bad} failed, {skipped} skipped"
  return (if bad == 0 then 0 else 1)
