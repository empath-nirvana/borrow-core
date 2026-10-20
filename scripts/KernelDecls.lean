import Core
import Frontend
import Backend

/-!
# Kernel declarations and their users  (`docs/kernel-usage.md`)

    lake env lean scripts/KernelDecls.lean

List every declaration of a `Core` module that is a derived rule (a theorem concluding with a
`CDerives` or `CDerivesP` judgment) or a derived form (a definition whose value is a value type,
a computation type, a term or a value), outside the files of programs and examples; and for each,
the `Frontend` and `Backend` declarations that mention it. Prints tab-separated lines
`<kind> <module> <name> <frontend users> <backend users>`, a user count and up to three users each.
-/

open Lean Meta

def isProgramModule (m : Name) : Bool :=
  let s := m.toString
  s.endsWith "Programs" || s.endsWith "Examples" || s.endsWith "Rejections" || s.endsWith "Stale"
    || s.endsWith "Demonic" || s.endsWith "DelayNaive" || s.endsWith "EmbeddingExamples"

def resultHead (t : Expr) : MetaM Name :=
  forallTelescopeReducing t fun _ b => pure (b.getAppFn.constName?.getD .anonymous)

#eval show MetaM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Option Name := (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!
  -- the users: every Frontend/Backend constant's used constants
  let mut users : Std.HashMap Name (Array Name × Array Name) := {}
  for (n, ci) in env.constants.toList do
    let some m := modOf n | continue
    let fe := (`Frontend).isPrefixOf m
    let be := (`Backend).isPrefixOf m
    if !(fe || be) then continue
    let used := ci.getUsedConstantsAsSet
    for u in used do
      let (a, b) := users.getD u (#[], #[])
      users := users.insert u (if fe then (a.push n, b) else (a, b.push n))
  let mut rows : Array (String × String × String) := #[]
  for (n, ci) in env.constants.toList do
    let some m := modOf n | continue
    if !(`Core).isPrefixOf m || isProgramModule m then continue
    if n.isInternal || n.isImplementationDetail then continue
    let kind ← match ci with
      | .thmInfo _ =>
        let h ← resultHead ci.type
        pure (if h == ``BoCa.Fig16.LogRel.Core.CDerives || h == ``BoCa.Fig16.LogRel.Core.CDerivesP
          then "rule" else "")
      | .defnInfo _ =>
        let h ← resultHead ci.type
        pure (if h == ``BoCa.Fig16.LogRel.Core.VTy || h == ``BoCa.Fig16.LogRel.Core.CTy then "type"
          else if h == ``BoCa.Expr || h == ``BoCa.Val then "term" else "")
      | _ => pure ""
    if kind == "" then continue
    let (fu, bu) := users.getD n (#[], #[])
    let show3 (a : Array Name) := s!"{a.size}\t{" ".intercalate ((a.toList.take 3).map toString)}"
    rows := rows.push (kind, s!"{m}\t{n}", s!"{show3 fu}\t{show3 bu}")
  let sorted := rows.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  for (k, mn, u) in sorted do IO.println s!"{k}\t{mn}\t{u}"
