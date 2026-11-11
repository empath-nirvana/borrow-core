import Frontend.Elab.Fins

/-!
# Frontend — Elab — cancel rows of a held stored generator  `[spec §15, §27]`

A function given a stored generator over a row, `U (pull_Σc A B R)` (SPEC §15), holds it
across its own operations. The checker's consume glue closes it when one of them is cancelled
(`Frontend.Check.finalOf`): a `[then]` whose finaliser performs `Σc`, which every capturable
operation of the function's row must then hold in its cancel row (SPEC §27, `thenFinB`). This adds
those entries to the table `Fins.table` reads off the effects pass's output, per name, as `Fins`
does for a written finaliser.
-/

namespace Frontend.Elab.FinsHeld

open Frontend.Elab.Fins

/-- The parameter tuple's type of a function type as written, under its `!` and lifetimes. -/
def paramOf : VTy → Option VTy
  | .bang _ A | .all _ _ _ A => paramOf A
  | .lolli _ P _ => some P
  | .thunk _ C => paramOfC C
  | _ => none
where
  paramOfC : CTy → Option VTy
    | .arr _ P _ => some P
    | .all _ _ _ C => paramOfC C
    | _ => none

/-- The rows `Σc` of the stored generators over a row among a parameter tuple's components. -/
def pulledRows : VTy → List (List Ent)
  | .tensor _ A B => pulledRows A ++ pulledRows B
  | .thunk _ (.nu _ _ (.amp _ (.eff _ r _) (.eff _ r' _))) =>
    let es := Row.ents r'
    if es.isEmpty || (Row.ents r).isEmpty then [] else [es]
  | _ => []

/-- The table `t` with, for each function of `ds` given a stored generator over a row `Σc`, the
entries of `Σc` in the cancel row of each capturable operation of the function's row.
`[spec §15, §27]` -/
def add (t : Table) (ds : List Decl) : Table :=
  ds.foldl (fun t d => match d with
    | .def_ _ _ _ A _ _ =>
      let rs := ((paramOf A).map pulledRows).getD []
      if rs.isEmpty then t else
      let S := rowOfTy A
      let SD := addEnts [] (rs.flatten.filter fun e => S.any fun f => f.1 == e.1 && f.2.1 == e.2.1)
      S.foldl (fun t e => if e.captures then t.add e.1 e.2.1 SD else t) t
    | _ => t) t

end Frontend.Elab.FinsHeld
