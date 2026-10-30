import Frontend
import Backend
import Backend2

/-!
# The insertion pins  `[spec §12, §19]` (#746)

Every site of the compiler that inserts a drop, a copy or an abandonment cites the kernel rule it
emits, and this file checks the citations. It fails to elaborate, or reports an error, when:

* a rule a citation names is not a declaration (the names are resolved when this file is
  elaborated: a renamed or deleted rule stops it);
* a statement an `UNPROVED:` citation names is not a definition of a `Prop`;
* a declaration of `Backend2/` or `Backend/` builds a `drop`, `copy` or `abandon` node at a rule
  (`Backend2.DropRule`, `Backend2.CopyRule`, `Backend2.Abandon`, `Backend.Clos.Licence`) that its
  entry in `sites` does not list, or an entry lists one it does not build: every site, and every
  rule each site uses, is in the table below;
* the elaboration emits a `copy`, `forget` or `tok_burn` constant at a declaration not in
  `elabSites`, or emits `tok_burn` (`Data.burnBind`) anywhere but the compilation of a written
  `match` (`Data.compile`).

Backend2's nodes carry their rule, and `Backend2.Lint` checks each rule's premise on the variable's
type at every node of every program it compiles (`Lint.copiesAt`, `Lint.dropsAt`,
`Lint.abandonable`). The old backend converts the erased term, so no stage has a type to check
its licences against: the licence names the rule the site relies on, and the `UNPROVED:` ones name
what is not read. The checker's drops are typed nodes: a `dtor` node's derivation carries
`HasDtor` (`TDerivesP.dtor_hasDtor`), and `checkProgram_soundP` projects every checked program to
`CDerivesP`, so the checker inserts no drop no kernel rule licenses.

    lake env lean scripts/PinSites.lean
-/

open Lean Elab Command
open BoCa.Fig16.LogRel.Core

namespace PinSites

/-- A rule's citation: the kernel declarations that license it, and the statement it would need
where that is not proved (`UNPROVED:`), or what is open. -/
structure Cite where
  tag : Name
  rules : List Name
  unproved : Option Name := none
  open_ : Option String := none

/-- **The rules**, each cited. -/
def cites : List Cite := [
  -- Backend2: the LIR's `drop` (`Backend2.DropRule`).
  ⟨``Backend2.DropRule.dead, [``Ctx.DeadP.drop, ``Ctx.SoloP.skip], none, none⟩,
  ⟨``Backend2.DropRule.forget, [``CDerives.forgetImm, ``CDerives.forgetMut, ``CDerives.forgetUnk,
    ``CDerives.arrForget], none, none⟩,
  ⟨``Backend2.DropRule.dtor, [``drop_derives, ``dtor_wf, ``HasDtor.arrayMut,
    ``Check.TDerivesP.dtor_hasDtor], none, none⟩,
  ⟨``Backend2.DropRule.unused, [``Ctx.DeadP.drop, ``vP_empty_of_persistent,
    ``Check.neitherAbsorbed_of], some ``Check.SplitMasks.NeitherAbsorbed, none⟩,
  ⟨``Backend2.DropRule.superseded, [``CDerives.effRaise], none, none⟩,
  ⟨``Backend2.DropRule.stackK, [], none,
    some "F3 (#746 item 5, step 4): no kernel rule; `Prog.stackKs` is the exemption"⟩,
  -- Backend2: the LIR's `copy` (`Backend2.CopyRule`).
  ⟨``Backend2.CopyRule.dup, [``Ctx.SplitP.dup, ``Check.SplitMasks.both_persistent], none, none⟩,
  ⟨``Backend2.CopyRule.const, [``CDerives.copy, ``CDerives.arrCopy], none, none⟩,
  ⟨``Backend2.CopyRule.derived, [``copy_derives, ``DerivedCopy], none, none⟩,
  -- Backend2: the LIR's `abandon` (`Backend2.Abandon`).
  ⟨``Backend2.Abandon.letAbort, [``CDerives.effLet, ``vC_noOwn_of_ownFree], none, none⟩,
  ⟨``Backend2.Abandon.top, [``CDerives.topI], none, none⟩,
  -- The old backend (`Backend.Clos.Licence`).
  ⟨``Backend.Clos.Licence.word, [``Ctx.DeadP.drop, ``Ctx.SplitP.dup], none, none⟩,
  ⟨``Backend.Clos.Licence.clauses, [``clausesTy_persistent, ``Ctx.DeadP.drop, ``Ctx.SplitP.dup],
    none, none⟩,
  ⟨``Backend.Clos.Licence.const, [``CDerives.swap], none, none⟩,
  ⟨``Backend.Clos.Licence.payload, [``CDerives.effRaise], none, none⟩,
  ⟨``Backend.Clos.Licence.split, [``Ctx.SplitP.dup, ``CDerives.copy, ``CDerives.arrCopy], none,
    some "rebuilt from free indices of the erased term; the typed split is not read"⟩,
  ⟨``Backend.Clos.Licence.unused, [``Ctx.DeadP.drop, ``CDerives.topI, ``CDerives.zeroE],
    some ``Check.UnmentionedAbsorbed, none⟩,
  ⟨``Backend.Clos.Licence.abort, [``CDerives.effLet], none,
    some "`effLet`'s `hW` and the cancel's premises are not read at the site"⟩,
  ⟨``Backend.Clos.Licence.kappa, [``kTy_unr, ``kTy_cancel_hasDtor_iff], none,
    some "the operation's qualifier is not read at the site"⟩,
  ⟨``Backend.Clos.Licence.step, [``Ctx.SplitP.dup], none,
    some "the step's type, `!`, is not read at the site"⟩]

/-- **The sites**: each declaration that builds a node at a rule, and the rules it uses. -/
def sites : List (Name × List Name) := [
  -- Backend2.
  (``Backend2.abortK, [``Backend2.DropRule.dead, ``Backend2.DropRule.unused,
    ``Backend2.DropRule.superseded]),
  (``Backend2.cancelK, [``Backend2.DropRule.dead, ``Backend2.DropRule.unused,
    ``Backend2.DropRule.superseded]),
  (``Backend2.conv, [``Backend2.DropRule.dead, ``Backend2.DropRule.unused,
    ``Backend2.DropRule.superseded, ``Backend2.Abandon.letAbort, ``Backend2.Abandon.top]),
  (``Backend2.convDrive, [``Backend2.DropRule.dead, ``Backend2.DropRule.unused,
    ``Backend2.CopyRule.dup]),
  (``Backend2.convDrive.proj, [``Backend2.DropRule.dead]),
  (``Backend2.convHandle, [``Backend2.DropRule.unused]),
  (``Backend2.convK, [``Backend2.DropRule.dead, ``Backend2.Abandon.letAbort]),
  (``Backend2.convSpine.go, [``Backend2.DropRule.dead, ``Backend2.DropRule.unused,
    ``Backend2.DropRule.superseded, ``Backend2.CopyRule.dup, ``Backend2.Abandon.letAbort,
    ``Backend2.Abandon.top]),
  (``Backend2.convUse, [``Backend2.DropRule.unused]),
  (``Backend2.convWork, [``Backend2.DropRule.dead, ``Backend2.DropRule.unused,
    ``Backend2.Abandon.letAbort]),
  (``Backend2.convWorkK, [``Backend2.DropRule.dead, ``Backend2.DropRule.unused,
    ``Backend2.Abandon.letAbort]),
  (``Backend2.dtorShape, [``Backend2.DropRule.dtor]),
  (``Backend2.expand, [``Backend2.DropRule.dead, ``Backend2.DropRule.forget,
    ``Backend2.CopyRule.const]),
  (``Backend2.freeStackThen, [``Backend2.DropRule.dead]),
  (``Backend2.genArrFree, [``Backend2.DropRule.dead, ``Backend2.CopyRule.dup]),
  (``Backend2.genCount, [``Backend2.DropRule.dead, ``Backend2.CopyRule.dup]),
  (``Backend2.genCountTry, [``Backend2.DropRule.dead, ``Backend2.CopyRule.dup]),
  (``Backend2.genDtor, [``Backend2.DropRule.dead, ``Backend2.DropRule.dtor, ``Backend2.CopyRule.dup]),
  (``Backend2.genFix, [``Backend2.DropRule.dead, ``Backend2.CopyRule.dup]),
  (``Backend2.genKap, [``Backend2.DropRule.unused]),
  (``Backend2.genLendU, [``Backend2.DropRule.dead]),
  (``Backend2.genMach, [``Backend2.DropRule.dead]),
  (``Backend2.genStackMach, [``Backend2.DropRule.dead, ``Backend2.DropRule.stackK,
    ``Backend2.CopyRule.dup]),
  (``Backend2.genTab, [``Backend2.DropRule.dead, ``Backend2.CopyRule.dup]),
  (``Backend2.ifLt, [``Backend2.DropRule.dead]),
  (``Backend2.leaf, [``Backend2.DropRule.unused]),
  (``Backend2.mapStates, [``Backend2.DropRule.dead, ``Backend2.CopyRule.dup]),
  (``Backend2.mkClosOf, [``Backend2.DropRule.dead]),
  (``Backend2.nodeAt, [``Backend2.CopyRule.dup]),
  (``Backend2.popThen, [``Backend2.DropRule.dead]),
  (``Backend2.releaseOpt, [``Backend2.DropRule.dead]),
  (``Backend2.releaseThen, [``Backend2.DropRule.dead]),
  (``Backend2.splitCtx, [``Backend2.DropRule.unused, ``Backend2.CopyRule.dup]),
  (``Backend2.takeClosOf, [``Backend2.DropRule.dead]),
  (``Backend2.travF, [``Backend2.CopyRule.dup]),
  (``Backend2.unitThen, [``Backend2.DropRule.dead]),
  (``Backend2.untuple, [``Backend2.DropRule.dead]),
  -- The lint reads the rules; it builds no node.
  (``Backend2.Lint.copyable, [``Backend2.CopyRule.dup, ``Backend2.CopyRule.derived]),
  -- The old backend.
  (``Backend.Clos.MEnv.cancelArm, [``Backend.Clos.Licence.abort]),
  (``Backend.Clos.MEnv.cancelArm.go, [``Backend.Clos.Licence.word]),
  (``Backend.Clos.MEnv.payload, [``Backend.Clos.Licence.word]),
  (``Backend.Clos.Tm.dropResume, [``Backend.Clos.Licence.word, ``Backend.Clos.Licence.kappa]),
  (``Backend.Clos.abortiveSite, [``Backend.Clos.Licence.word, ``Backend.Clos.Licence.clauses]),
  (``Backend.Clos.byName, [``Backend.Clos.Licence.word]),
  (``Backend.Clos.controlSite, [``Backend.Clos.Licence.word]),
  (``Backend.Clos.conv, [``Backend.Clos.Licence.word, ``Backend.Clos.Licence.const,
    ``Backend.Clos.Licence.unused]),
  (``Backend.Clos.directCalls, [``Backend.Clos.Licence.word]),
  (``Backend.Clos.dispatchOp, [``Backend.Clos.Licence.word]),
  (``Backend.Clos.drvBody, [``Backend.Clos.Licence.clauses]),
  (``Backend.Clos.errNext, [``Backend.Clos.Licence.word, ``Backend.Clos.Licence.payload]),
  (``Backend.Clos.finNormal, [``Backend.Clos.Licence.abort]),
  (``Backend.Clos.finalise, [``Backend.Clos.Licence.word, ``Backend.Clos.Licence.payload]),
  (``Backend.Clos.fixValue, [``Backend.Clos.Licence.word, ``Backend.Clos.Licence.step]),
  (``Backend.Clos.ioValue, [``Backend.Clos.Licence.word]),
  (``Backend.Clos.kapBody, [``Backend.Clos.Licence.word, ``Backend.Clos.Licence.clauses,
    ``Backend.Clos.Licence.payload]),
  (``Backend.Clos.mkValue, [``Backend.Clos.Licence.word]),
  (``Backend.Clos.propagateOn, [``Backend.Clos.Licence.abort]),
  (``Backend.Clos.takeValue, [``Backend.Clos.Licence.word]),
  (``Backend.Clos.unTuple, [``Backend.Clos.Licence.word]),
  (``Backend.Clos.withClause, [``Backend.Clos.Licence.clauses]),
  (``Backend.Clos.wrapCopies, [``Backend.Clos.Licence.split]),
  (``Backend.Clos.wrapDrops, [``Backend.Clos.Licence.unused]),
  (``Backend.Clos.wrapRaise, [``Backend.Clos.Licence.word])]

/-- **The checker's insertions**: each a typed node whose derivation is the rule's. -/
def checkerSites : List (Name × List Name) := [
  -- A dropped slot: a `dtor` node (`rDrop`), its derivation `TDerivesP.dtor`, which carries
  -- `HasDtor`; erased, `drop_derives`.
  (``Frontend.Check.rDrop, [``Check.TDerivesP.dtor_hasDtor, ``drop_derives,
    ``Frontend.Check.checkProgram_soundP]),
  (``Frontend.Check.dropOne, [``Frontend.Check.rDrop]),
  (``Frontend.Check.dropOwed, [``Frontend.Check.dropOne]),
  -- A `[then]` finaliser's destructor (`finalOf`, `finNode`): a `dtor` node.
  (``Frontend.Check.finNode, [``Check.TDerivesP.dtor_hasDtor, ``drop_derives]),
  (``Frontend.Check.finalOf, [``Frontend.Check.finNode])]

/-- The kernel constants that copy, forget or burn, as the elaboration writes them. -/
def elabConsts : List Name := [``Frontend.Const.copy, ``Frontend.Const.copyBang,
  ``Frontend.Const.forgetImm, ``Frontend.Const.forgetMut, ``Frontend.Const.forgetUnk,
  ``Frontend.Const.forgetBang, ``Frontend.Const.tokBurn, ``Frontend.Const.arrayCopy,
  ``Frontend.Const.arrayForget]

/-- **The elaboration's emitters of those constants**, each with the rule the checker then types
it by. The maps and tests over every constant rebuild the constant they read. -/
def elabSites : List (Name × List Name × List Name) := [
  -- `array_copy` of an `imm` view in a template: the constant, `CDerives.arrCopy`.
  (``Frontend.Sugar.surfV, [``Frontend.Const.arrayCopy], [``CDerives.arrCopy]),
  -- The burn at a written `match` (`burnCallers`): `CDerives.tokBurn`.
  (``Frontend.Data.burnBind, [``Frontend.Const.tokBurn], [``CDerives.tokBurn]),
  (``Frontend.Const.renameLife, elabConsts, []), (``Frontend.Const.respan, elabConsts, []),
  (``Frontend.Const.subst, elabConsts, []), (``Frontend.Elab.Instances.safeDivisor, elabConsts, []),
  (``Frontend.Sugar.safeDivisor, elabConsts, []), (``Frontend.Sugar.Const.unwinding, elabConsts, []),
  (``Frontend.Sugar.relaxedC?, elabConsts, []), (``Frontend.Sugar.unwindingC?, elabConsts, [])]

/-- The only callers of the burn, and the declarations that build a `tok_burn` constant: the
compilation of a written `match` (SPEC §42), and the maps over every constant. -/
def burnCallers : List Name := [``Frontend.Data.compile]

/-- The rule constructors whose uses locate the sites. -/
def tags : List Name := cites.map (·.tag)

/-- The declaration a compiler-made auxiliary belongs to. -/
def rootOf : Name → Name
  | n@(.str p s) => if s.startsWith "_" || s.startsWith "proof_" then rootOf p else n
  | .num p _ => rootOf p
  | n => n

def skipped (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  ci matches .thmInfo _ || isAuxRecursor env n || isNoConfusion env n || isCasesOnRecursor env n ||
    Meta.isMatcherCore env n ||
    n.components.any (fun c => let s := c.toString
      s.startsWith "match_" || s == "splitter" || s.startsWith "eq_" || s.startsWith "inst" ||
      s == "ofNat" || s == "toCtorIdx" || s == "ctorIdx" ||
      s == "elim" || s == "ctorElim" || s == "ctorElimType")

/-- The declarations of `mods` whose value uses one of `cs`, each with the ones it uses. -/
def usersOf (env : Environment) (mods : Name → Bool) (cs : List Name) :
    Std.HashMap Name (List Name) := Id.run do
  let mut out : Std.HashMap Name (List Name) := {}
  for (n, ci) in env.constants.toList do
    let some mod := env.getModuleIdxFor? n | continue
    unless mods env.header.moduleNames[mod.toNat]! do continue
    let some v := ci.value? | continue
    if skipped env n ci then continue
    let used := v.getUsedConstants
    let hits := cs.filter used.contains
    if hits.isEmpty then continue
    let r := rootOf n
    out := out.insert r ((out.getD r []) ++ hits).eraseDups
  return out

def sameSet (a b : List Name) : Bool := a.all b.contains && b.all a.contains

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut bad : Array String := #[]
  -- Every rule cited, once; every `UNPROVED:` statement a `Prop`.
  for c in cites do
    if (cites.filter (·.tag == c.tag)).length != 1 then bad := bad.push s!"{c.tag}: cited twice"
    if c.rules.isEmpty && c.open_.isNone then bad := bad.push s!"{c.tag}: no rule and nothing open"
    if let some u := c.unproved then
      match env.find? u with
      | some (.defnInfo d) =>
        unless d.type == .sort .zero do bad := bad.push s!"{c.tag}: {u} is not a `Prop`"
      | _ => bad := bad.push s!"{c.tag}: {u} is not a definition"
  for ty in [``Backend2.DropRule, ``Backend2.CopyRule, ``Backend2.Abandon, ``Backend.Clos.Licence] do
    let some (.inductInfo i) := env.find? ty | bad := bad.push s!"{ty}: not an inductive"; continue
    for k in i.ctors do
      unless tags.contains k do bad := bad.push s!"{k}: a rule with no citation"
  -- Every site in the table, with exactly the rules it uses.
  let found := usersOf env (fun m => (`Backend2).isPrefixOf m && m != `Backend2.LintTests ||
    (`Backend).isPrefixOf m) tags
  for (n, used) in found.toList do
    match sites.find? (·.1 == n) with
    | none => bad := bad.push s!"{n}: builds nodes at {used}, and has no entry"
    | some (_, listed) =>
      unless sameSet used listed do bad := bad.push s!"{n}: uses {used}, its entry lists {listed}"
  for (n, _) in sites do
    unless found.contains n do bad := bad.push s!"{n}: has an entry and builds no node"
  for (n, _) in checkerSites do
    unless env.contains n do bad := bad.push s!"{n}: not a declaration"
  -- The elaboration's constants: each emitter in the table, with exactly the constants it emits.
  let emits := usersOf env (fun m => (`Frontend.Elab).isPrefixOf m || m == `Frontend.Sugar) elabConsts
  for (n, used) in emits.toList do
    match elabSites.find? (·.1 == n) with
    | none => bad := bad.push s!"{n}: the elaboration emits {used}, and has no entry"
    | some (_, listed, _) =>
      unless sameSet used listed do bad := bad.push s!"{n}: emits {used}, its entry lists {listed}"
  for (n, _) in elabSites do
    unless emits.contains n do bad := bad.push s!"{n}: has an entry and emits no constant"
  -- The burn at a written `match` only.
  let burns := usersOf env (fun m => (`Frontend).isPrefixOf m) [``Frontend.Data.burnBind]
  for (n, _) in burns.toList do
    unless burnCallers.contains n do bad := bad.push s!"{n}: emits `tok_burn` outside a written `match`"
  if burns.isEmpty then bad := bad.push "no written `match` emits `tok_burn`"
  if bad.isEmpty then
    logInfo m!"insertion pins: {found.size} backend sites, {cites.length} rules cited, {emits.size} elaboration emitters, the burn at a written `match` only"
  else
    for b in bad do logError b

end PinSites
