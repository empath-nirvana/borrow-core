import Frontend.Main
import Backend.Cells

/-!
# The compiler's type comparisons  (`scripts/check-type-eq.sh`)

    lake env lean scripts/TypeEq.lean

Lists every declaration of a compiled module (the import closure of `bcc` and `bcc-counts`: the
modules of this repository outside `Core`, `Support` and `Paper`, which are the kernel and its
proofs) whose elaborated body decides an equality of a kernel type. A body decides one when it uses
a *seed*:

* the `DecidableEq`/`BEq` instance of `VTy`, `CTy` or `OpSig`, or an instance built from one (of a
  list, an option, a pair, a structure holding one), wherever it is derived;
* `VTy.alphaB`/`CTy.alphaB`/`Jdg.alphaB`;
* any computable declaration of a module outside the compiled ones (`Core`, `Support`, `Paper`)
  whose body uses a seed, to a fixed point: a compiled declaration that compares types through a
  helper defined in the kernel is listed too.

Read from the elaborated terms, not from the source text, so it sees every `=`, `==`, `!=`, `≠`,
`decide`, `contains`, `find?`, `∪` and `eraseDups` whose operands are or hold a kernel type,
whatever the spelling. Proofs are not read (they decide nothing at run time), nor the recursors and
`noConfusion` Lean generates. The closure does not pass through the compiled modules' own
declarations: each one that compares types is listed itself, so its callers are not.

Output: a line `#scanned  roots` naming the compiled modules' roots, then one tab-separated line
`module  declaration  seeds` per declaration, compiler-generated auxiliaries (`match_`, `_proof_`,
`_unary`, …) folded into the declaration they belong to. A declaration of the file being run itself
is listed at the module `main` (the negative tests of `scripts/check-type-eq.sh`).
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

/-- The kernel and its proofs: the modules whose declarations are not listed, and through which
the seeds are closed. -/
def kernelRoots : List Name := [`Core, `Support, `Paper]

/-- A module of this repository: its source is in the working tree. -/
def ownModule (m : Name) : IO Bool :=
  (System.mkFilePath (m.components.map toString) |>.addExtension "lean").pathExists

/-- The modules of the environment: whether each is the repository's, and whether it is compiled
(the repository's, outside `kernelRoots`). -/
def modules (env : Environment) : IO (Array (Bool × Bool)) :=
  env.header.moduleNames.mapM fun m => do
    let own ← ownModule m
    return (own, own && !kernelRoots.contains m.getRoot)

/-- Whether the declaration `n` is of a compiled module, or of the file being run (`main`). -/
def compiled (env : Environment) (mods : Array (Bool × Bool)) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some mi => (mods[mi.toNat]!).2
  | none => !(`TypeEq).isPrefixOf n

/-- Whether the declaration `n` is of the repository (a compiled module, the kernel's, or `main`). -/
def own (env : Environment) (mods : Array (Bool × Bool)) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some mi => (mods[mi.toNat]!).1
  | none => !(`TypeEq).isPrefixOf n

/-- A declaration's run-time body: a computable definition that is neither a proof nor a
proposition or type (a `Prop`- or `Type`-valued function, such as `SigsAt`, decides nothing; the
`Decidable` instance that decides it is a definition of its own, and is read). -/
def body? (env : Environment) (n : Name) (ci : ConstantInfo) : MetaM (Option Expr) := do
  if isAuxRecursor env n || isNoConfusion env n || isNoncomputable env n then return none
  let some v := (match ci with
    | .defnInfo d => some d.value
    | .opaqueInfo d => some d.value
    | _ => none) | return none
  if ← isProp ci.type then return none
  if ← forallTelescopeReducing ci.type fun _ b => return (← whnf b).isSort then return none
  return some v

/-- The constants a term uses at run time: those outside its proofs and its types (an argument
that is a type, a binder's type, a proof of a premise). The instance that decides a comparison
(`instDecidableEqVTy A B` under `decide`, `instBEq…` under `contains`) is neither, and is kept. -/
partial def runtimeConsts (e : Expr) (acc : NameSet := {}) : MetaM NameSet := do
  let skip ← try (pure ((← isProof e) || (← isType e))) catch _ => pure false
  if skip then return acc
  match e with
  | .app f a => runtimeConsts a (← runtimeConsts f acc)
  | .lam n t b bi =>
      withLocalDecl n bi t fun x => runtimeConsts (b.instantiate1 x) acc
  | .letE n t v b _ => do
      let acc ← runtimeConsts v acc
      withLetDecl n t v fun x => runtimeConsts (b.instantiate1 x) acc
  | .mdata _ e | .proj _ _ e => runtimeConsts e acc
  | .const n _ => return acc.insert n
  | _ => return acc

/-- The seeds a body uses at run time: a cheap test on every constant it names, then
`runtimeConsts` where that finds one. -/
def runtimeSeeds (S : NameSet) (v : Expr) (used : Array Name) : MetaM (List Name) := do
  unless used.any S.contains do return []
  return (← runtimeConsts v).toList.filter S.contains

/-- The seeds: the equality instances of the kernel's types and the instances built from them,
the α tests, and every computable declaration of the kernel's modules that uses one at run time,
to a fixed point. -/
def seeds (env : Environment) (mods : Array (Bool × Bool)) : MetaM NameSet := do
  -- the candidates: an equality instance anywhere, any computable declaration of the kernel's
  let mut cands : Array (Name × Expr × Expr × Array Name) := #[]
  for (n, ci) in env.constants.toList do
    let eqi := isEqName n
    unless eqi || (own env mods n && !compiled env mods n) do continue
    let some v ← body? env n ci | continue
    cands := cands.push (n, ci.type, v, v.getUsedConstants)
  let mut S : NameSet := alphaNames.foldl (·.insert ·) {}
  -- the instances at the kernel's own types
  for (n, ty, _, _) in cands do
    if isEqName n && ty.getUsedConstants.any baseTys.contains then S := S.insert n
  -- every candidate whose body reaches one at run time, to a fixed point (an equality instance
  -- by any constant it names: it is derived, and decides by what it names)
  let mut changed := true
  while changed do
    changed := false
    for (n, _, v, used) in cands do
      if S.contains n then continue
      let reach ← if isEqName n then pure (used.any S.contains)
        else pure !(← runtimeSeeds S v used).isEmpty
      if reach then S := S.insert n; changed := true
  return S

/-- The hits: `(module, declaration, seeds)`, by declaration, and the compiled modules' roots. -/
def hits : MetaM (Array (Name × Name × List Name) × List Name) := do
  let env ← getEnv
  let mods ← modules env
  let S ← seeds env mods
  let mut out : Std.HashMap Name (Name × List Name) := {}
  for (n, ci) in env.constants.toList do
    unless compiled env mods n do continue
    if S.contains n then continue
    let mod := match env.getModuleIdxFor? n with
      | some mi => env.header.moduleNames[mi.toNat]!
      | none => `main
    let some v ← body? env n ci | continue
    let hs ← runtimeSeeds S v v.getUsedConstants
    unless hs.isEmpty do
      let r := root n
      let (_, prev) := out.getD r (mod, [])
      out := out.insert r (mod, (prev ++ hs).eraseDups)
  let roots := (env.header.moduleNames.zip mods).filterMap fun (m, _, c) =>
    if c then some m.getRoot else none
  let roots := roots.toList.eraseDups.mergeSort (·.toString ≤ ·.toString)
  let hs := (out.toArray.map fun (r, m, hs) => (m, r, hs)).qsort fun a b =>
    a.1.toString < b.1.toString || (a.1 == b.1 && a.2.1.toString < b.2.1.toString)
  return (hs, roots)

end TypeEq

#eval show MetaM Unit from do
  let (hs, roots) ← TypeEq.hits
  IO.println s!"#scanned\t{" ".intercalate (roots.map toString)}"
  for (m, d, hs) in hs do
    let short := hs.map fun h => h.toString.replace "BoCa.Fig16.LogRel.Core." ""
    IO.println s!"{m}\t{d}\t{", ".intercalate short}"
