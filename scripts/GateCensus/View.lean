import Lean

/-!
# A census's view of the loaded environment

`gate-census` loads the library once, the union of every census's imports. Each census reads only
the modules its own import list reaches (and `Init`, which every file imports), as it did when it
was a file of its own run by `lean`: a declaration of another module is not visited and does not
resolve. A declaration with no module (one the negative tests elaborate into the environment) is in
every view, as a declaration of the file being run was.
-/

open Lean

namespace GateCensus

/-- The modules a census reads, by module index. -/
structure View where
  mask : Array Bool

/-- The modules `roots` reach through their imports, and `Init`. -/
def View.ofRoots (env : Environment) (roots : Array Name) : View := Id.run do
  let names := env.header.moduleNames
  let mut idx : Std.HashMap Name Nat := {}
  for h : i in [0:names.size] do
    idx := idx.insert names[i] i
  let mut mask := Array.replicate names.size false
  let mut work := (roots.push `Init).toList
  while true do
    match work with
    | [] => break
    | m :: rest =>
      work := rest
      let some i := idx[m]? | continue
      if mask[i]! then continue
      mask := mask.set! i true
      work := (env.header.moduleData[i]!.imports.map (·.module)).toList ++ work
  return ⟨mask⟩

/-- Whether module `i` is in the view. -/
def View.hasModule (v : View) (i : Nat) : Bool := v.mask[i]!

/-- Whether the declaration `n` is in the view. -/
def View.has (v : View) (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => v.mask[i.toNat]!
  | none => true

/-- The roots of `roots` missing from the environment. -/
def missingRoots (env : Environment) (roots : Array Name) : Array Name :=
  roots.filter fun m => !env.header.moduleNames.contains m

end GateCensus
