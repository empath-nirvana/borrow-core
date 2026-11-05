import Frontend.Main

/-!
# The checker's type comparisons  (`scripts/check-type-eq.sh`)

    lake env lean scripts/TypeEq.lean

Lists every declaration of a `Frontend.*` module whose elaborated body decides an equality of a
kernel type: it uses the `DecidableEq`/`BEq` instance of `VTy`, `CTy` or `OpSig` (directly or
through an instance built from one, of a list, an option, a pair, a structure holding one), or
`VTy.alphaB`/`CTy.alphaB`/`Jdg.alphaB` itself. Read from the elaborated terms, not from the source
text, so it sees every `=`, `==`, `!=`, `≠`, `decide`, `contains`, `find?`, `∪` and `eraseDups`
whose operands are or hold a kernel type, whatever the spelling. Proofs are not read (they decide
nothing at run time), nor the recursors and `noConfusion` Lean generates.

Output: one tab-separated line `module  declaration  seeds` per declaration, compiler-generated
auxiliaries (`match_`, `_proof_`, `_unary`, …) folded into the declaration they belong to. A
declaration of the file being run itself is listed at the module `main` (the negative tests of
`scripts/check-type-eq.sh`).
-/

open Lean Meta

namespace TypeEq

/-- The kernel's types. -/
def baseTys : List Name :=
  [``BoCa.Fig16.LogRel.Core.VTy, ``BoCa.Fig16.LogRel.Core.CTy, ``BoCa.Fig16.LogRel.Core.OpSig]

/-- The α tests themselves. -/
def alphaNames : List Name :=
  [``BoCa.Fig16.LogRel.Core.VTy.alphaB, ``BoCa.Fig16.LogRel.Core.CTy.alphaB,
   ``BoCa.Fig16.LogRel.Core.Jdg.alphaB]

/-- A name of an instance or function Lean derives for an equality: `instDecidableEq…`,
`instBEq…`, `decEq…`. -/
def isEqName (n : Name) : Bool :=
  n.components.any fun c => match c with
    | .str _ s => s.startsWith "instDecidableEq" || s.startsWith "instBEq" || s.startsWith "decEq"
    | _ => false

/-- The declaration a compiler-generated auxiliary belongs to. -/
def root (n : Name) : Name :=
  let keep := n.components.takeWhile fun c => match c with
    | .str _ s => !(s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" ||
        s.startsWith "eq_" || s == "eq_def")
    | _ => false
  keep.foldl (fun acc c => match c with | .str _ s => .str acc s | _ => acc) .anonymous

/-- The seeds: the equality instances of the kernel's types, the instances built from them (to a
fixed point), and the α tests. -/
def seeds (env : Environment) : NameSet := Id.run do
  let eqs := env.constants.toList.filterMap fun (n, ci) =>
    if isEqName n then
      match ci with
      | .defnInfo d => some (n, ci.type.getUsedConstants, d.value.getUsedConstants)
      | _ => none
    else none
  let mut S : NameSet := alphaNames.foldl (·.insert ·) {}
  -- the instances at the kernel's own types
  for (n, ty, _) in eqs do
    if ty.any baseTys.contains then S := S.insert n
  -- the instances whose bodies reach one, to a fixed point
  let mut changed := true
  while changed do
    changed := false
    for (n, _, body) in eqs do
      if !S.contains n && body.any S.contains then
        S := S.insert n; changed := true
  return S

/-- The hits: `(module, declaration, seeds)`, by declaration. -/
def hits : MetaM (Array (Name × Name × List Name)) := do
  let env ← getEnv
  let S := seeds env
  let mut out : Std.HashMap Name (Name × List Name) := {}
  for (n, ci) in env.constants.toList do
    -- a declaration of a `Frontend` module, or of the file being run (`main`)
    let mod := match env.getModuleIdxFor? n with
      | some mi => env.header.moduleNames[mi.toNat]!
      | none => `main
    unless mod.getRoot == `Frontend || (mod == `main && !(`TypeEq).isPrefixOf n) do continue
    if isAuxRecursor env n || isNoConfusion env n || S.contains n then continue
    -- a proof decides nothing at run time
    if ← isProp ci.type then continue
    let some v := (match ci with
      | .defnInfo d => some d.value
      | .opaqueInfo d => some d.value
      | _ => none) | continue
    let hs := v.getUsedConstants.filter S.contains
    unless hs.isEmpty do
      let r := root n
      let (_, prev) := out.getD r (mod, [])
      out := out.insert r (mod, (prev ++ hs.toList).eraseDups)
  return (out.toArray.map fun (r, m, hs) => (m, r, hs)).qsort fun a b =>
    a.1.toString < b.1.toString || (a.1 == b.1 && a.2.1.toString < b.2.1.toString)

end TypeEq

#eval show MetaM Unit from do
  for (m, d, hs) in ← TypeEq.hits do
    let short := hs.map fun h => h.toString.replace "BoCa.Fig16.LogRel.Core." ""
    IO.println s!"{m}\t{d}\t{", ".intercalate short}"
