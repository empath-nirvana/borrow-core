import Backend.Driver
import Lowering.Own

/-!
# `own` on the pure corpus  (`scripts/check-lowering.sh`, SPEC §54)

    lake build lowering-check && .lake/build/bin/lowering-check <file.bc>…

Each program is checked as `bcc check` does. A program is in the pure fragment when it has no
capability (`main` has no externs) and its typed term is in `Lowering.pureT`. For each:

* the hypothesis of `Lowering.own_lowersInto` is decided: the masks agree with the leaves
  (`Lowering.agreeAt`), so the theorem gives `own`'s output low;
* `own`'s output is decided low as well (`Lowering.lowB`, sound by `Lowering.lowB_sound`), the
  kernel's constants being `copy`, `forget` and the erasures of the term's constant nodes;
* the source interpreter runs `own`'s output and the erasure, and the reports (the value and the
  live cells) must agree.

A program outside the fragment is listed as skipped, with the reason. The exit status is `1` when
any program in the fragment fails a check.
-/

open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

namespace LoweringCheck

/-- The erasures of the constant nodes of `t`, each once. -/
partial def consts (acc : List Expr) (t : TExpr) : List Expr :=
  let acc := if Lowering.constNode t && !acc.contains t.erase then t.erase :: acc else acc
  t.children.foldl (fun a (_, c) => consts a c) acc

/-- Where `explicitB` fails first, for the report: the failing node, printed short. -/
partial def why (isConst : Expr → Bool) (e : Expr) : Option String :=
  if isConst e then none else
  let sub (xs : List Expr) : Option String := xs.findSome? (why isConst)
  match e with
  | .var _ | .unit | .loc _ | .prim _ => none
  | .pair a b | .seq a b | .app a b | .letpair a b => match sub [a, b] with
    | some w => some w
    | none => match e with
      | .letpair _ b => if Lowering.once (Lowering.occ b 0) && Lowering.once (Lowering.occ b 1)
          then none else some s!"letpair binders: {repr (Lowering.occ b 0)} {repr (Lowering.occ b 1)} in {(reprStr e).take 300}"
      | _ => none
  | .inj₁ a | .inj₂ a => why isConst a
  | .lam b => match why isConst b with
    | some w => some w
    | none => if Lowering.once (Lowering.occ b 0) && Lowering.capOnceB b then none
        else some s!"lam: binder {repr (Lowering.occ b 0)} caps {Lowering.capOnceB b} in {(reprStr e).take 400}"
  | .case s a b => match sub [s, a, b] with
    | some w => some w
    | none => if (a == BoLo.stuckE && b == BoLo.stuckE) || (Lowering.once (Lowering.occ a 0) && Lowering.once (Lowering.occ b 0)) then none
        else some s!"case arms {repr (Lowering.occ a 0)} {repr (Lowering.occ b 0)} in {(reprStr e).take 300}"

end LoweringCheck

open LoweringCheck in
def main (files : List String) : IO UInt32 := do
  let mut bad : Nat := 0
  let mut pure : Nat := 0
  let mut skipped : Nat := 0
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
        let cs := consts [BoCa.copy, BoCa.forget] k.main.t
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
        else
          bad := bad + 1
          IO.println s!"FAIL {f}: low={low} same={same}; erasure: {show' src}; own: {show' lowered}"
          if !low then
            IO.println s!"  agree={Lowering.agreeAt [] k.main.t} explicit={Lowering.explicitB (cs.contains ·) e} effFree={Lowering.effFreeB e} ctx={(List.range k.main.ctx.length).all fun j => Lowering.once (Lowering.occ e j)} bound={Lowering.fvBound e}"
            IO.println s!"  {(why (cs.contains ·) e).getD "-"}"
  IO.println s!"lowering-check: {pure} in the pure fragment, {bad} failed, {skipped} skipped"
  return (if bad == 0 then 0 else 1)
