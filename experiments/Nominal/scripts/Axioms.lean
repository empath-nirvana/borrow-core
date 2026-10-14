import Nominal
open Lean Meta Elab Command

/-- Every declaration of the `Nominal` modules, with the axioms it rests on outside
`propext`, `Classical.choice`, `Quot.sound`. -/
elab "#nominal_axioms" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if (`Nominal).isPrefixOf m then
        count := count + 1
        let axs ← liftCoreM (Lean.collectAxioms n)
        let extra := axs.filter (fun a => !allowed.contains a)
        if extra.size > 0 then bad := bad.push (n, extra)
    | none => pure ()
  logInfo m!"declarations: {count}; outside [propext, Classical.choice, Quot.sound]: {bad.size} {bad.toList}"

#nominal_axioms
