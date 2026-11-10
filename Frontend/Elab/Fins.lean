import Frontend.Check.Elab
import Frontend.Check.Steps

/-!
# Frontend — Elab — cancel rows  `[spec §18, §27]`

The cancel row of an operation (SPEC §27) is what a cancel of a continuation captured at it
performs: the finalisers between the capture and its handler. It is inferred, as a function's row
is (§18), and the kernel checks it (`[then]`'s `F ⋈ Σ_D ≤ F`, `[handle]`'s cancel branch).

**The rule.** `x <- M unwind (D); N` (the core of `finally`, SPEC §42) is checked by `[then]` with
`M` at the site's row `Σ` and `D` at its own row `Σ_D`, the operations of `Σ` that `D` performs.
Each operation of `Σ` that captures a continuation (`capB`) is cancelled with its continuation
running `D`: its cancel row holds `Σ_D`. An operation's cancel row is the union of the `Σ_D`s of the
finalisers in whose site's row it is. Site names are static and each site has one name, so the
union is taken per name (`n.i`) over the whole elaborated program, and every row that has the
operation gives it that cancel row: a function's row, a block's, a handler site's.

`Σ_D` is what `D` performs at the names of `Σ`: its `perform[n.i]`s and `abort[n.i]`s, and the rows
of the functions it calls, less the operations of the sites inside `D`. `Σ` at a finaliser is the
row of the function it is in and the operations of the handler sites around it in that function.

An entry of a cancel row carries the empty cancel row. A finaliser that performs an operation that
itself captures a continuation needs that operation's cancel row to hold itself at every depth,
which is `⊤`: the kernel refuses it (SPEC §27, *Open*).

The table is read off the effects pass's output (`table`), and the pass runs again with it
(`Frontend.Elab.Effects.elaborate`'s `fins`), whose rows then carry it (`Env.rowOf`, the handler
sites' `HInfo.fins`).
-/

namespace Frontend.Elab.Fins

/-- A row entry: the name `n.i`, its qualifier and its types. -/
abbrev Ent := Nat × Nat × Qual × VTy × VTy

/-- The cancel rows inferred, each operation `n.i` with its cancel row's entries, in the order
they were met. -/
abbrev Table := List ((Nat × Nat) × List Ent)

/-- The entries of a written row. -/
def Row.ents : Row → List Ent
  | .nil => []
  | .cons n i q A B _ r => (n, i, q, A, B) :: Row.ents r

/-- The row of a function's or a block's type: the first `F[…]` on the spine of its result. -/
def rowOfTy : VTy → List Ent
  | .bang _ A | .all _ _ _ A => rowOfTy A
  | .lolli _ _ B => rowOfTy B
  | .thunk _ C => rowOfC C
  | _ => []
where
  rowOfC : CTy → List Ent
    | .arr _ _ C | .all _ _ _ C => rowOfC C
    | .eff _ r _ => Row.ents r
    | _ => []

/-- The answer `B` is `0` at the kernel's types (an abortive operation's, with a qualifier that
weakens). -/
def zeroTy (B : VTy) : Bool :=
  match Frontend.Check.elabV Frontend.Check.tyFuel
      ⟨⟨#[], 0, [], []⟩, .empty, .empty, [], [], [], [], []⟩ B with
  | .ok B => B.isZero
  | .error _ => match B with
    | .zero _ => true
    | _ => false

/-- The entry captures a continuation (`capB`): its cancel row is read. -/
def Ent.captures (e : Ent) : Bool := e.2.2.1 != .lin && !zeroTy e.2.2.2.2

/-- Add the entries `es` to a list of entries, each name once. -/
def addEnts (acc es : List Ent) : List Ent :=
  es.foldl (fun acc e => if acc.any fun f => f.1 == e.1 && f.2.1 == e.2.1 then acc else acc ++ [e])
    acc

/-- The table with `es` added to the cancel row of `n.i`. -/
def Table.add (t : Table) (n i : Nat) (es : List Ent) : Table :=
  if es.isEmpty then t else
  match t.find? (·.1 == (n, i)) with
  | some (_, cur) => t.map fun (k, v) => if k == (n, i) then (k, addEnts cur es) else (k, v)
  | none => t ++ [((n, i), addEnts [] es)]

/-- The cancel row of `n.i` in the table, as a written row (each entry's own cancel row empty). -/
def Table.finOf (t : Table) (n i : Nat) : Row :=
  match t.find? (·.1 == (n, i)) with
  | some (_, es) => es.foldr (fun (n, i, q, A, B) r => .cons n i q A B .nil r) .nil
  | none => .nil

/-- A handler site of the effects pass's output, `hndCtl i P R cls (thunk M)`: the site's info
and the computation it handles. -/
def hndSite? : Val → Option (HInfo × Val × Val × Val × Comp)
  | .app _ (.app _ (.app _ (.app _ (.sugar _ (.hndCtl i)) P) R) cls) (.thunk _ M) => some (i, P, R, cls, M)
  | _ => none

mutual
/-- The names a value performs and the functions it names, less the operations of the sites inside
it (`inner`): `(names, functions)`. -/
def perfV : Nat → List Nat → Val → List (Nat × Nat) × List String
  | 0, _, _ => ([], [])
  | k + 1, inner, V =>
    if let some (i, P, R, cls, M) := hndSite? V then
      let a := perfV k inner P; let b := perfV k inner R; let c := perfV k inner cls
      let d := perfC k (i.n :: inner) M
      (a.1 ++ b.1 ++ c.1 ++ d.1, a.2 ++ b.2 ++ c.2 ++ d.2)
    else match V with
    | .var _ x => ([], [x])
    | .pair _ V W | .app _ V W =>
      let a := perfV k inner V; let b := perfV k inner W; (a.1 ++ b.1, a.2 ++ b.2)
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => perfV k inner V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => perfC k inner M
    | _ => ([], [])

/-- `perfV` of a computation. -/
def perfC : Nat → List Nat → Comp → List (Nat × Nat) × List String
  | 0, _, _ => ([], [])
  | k + 1, inner, M =>
    let two (a b : List (Nat × Nat) × List String) := (a.1 ++ b.1, a.2 ++ b.2)
    match M with
    | .ret _ V | .absurd _ V => perfV k inner V
    | .bind _ _ _ M N | .with_ _ M N => two (perfC k inner M) (perfC k inner N)
    | .lam _ _ _ M | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ | .withbor2r _ _ _ _ _ _ _ _ M => perfC k inner M
    | .app _ M x => two (perfC k inner M) ([], [x.name])
    | .force _ x => ([], [x.name])
    | .letUnit _ V M | .letPair _ _ _ V M => two (perfV k inner V) (perfC k inner M)
    | .case _ V _ M _ N => two (perfV k inner V) (two (perfC k inner M) (perfC k inner N))
    | .loop _ _ _ V M N => two (perfV k inner V) (two (perfC k inner M) (perfC k inner N))
    | .perform _ n i V | .abort _ n i V =>
      two (if inner.contains n then [] else [(n, i)], []) (perfV k inner V)
    | .handle _ n _ hr hc M =>
      two (two (perfV k inner hr) (perfV k inner hc)) (perfC k (n :: inner) M)
    | .unwind _ _ _ M D N => two (perfC k inner M) (two (perfC k inner D) (perfC k inner N))
    | .top _ => ([], [])
end

/-- The finaliser's row `Σ_D` at the site's row `S`: the entries of `S` it performs, and those of
the rows of the functions it calls (`rows`) that are in `S`. -/
def finRow (rows : List (String × List Ent)) (S : List Ent) (D : Comp) : List Ent :=
  let (ns, fs) := perfC 100000 [] D
  let called := fs.flatMap fun f => (rows.lookup f).getD []
  let at_ (n i : Nat) : Option Ent := S.find? fun e => e.1 == n && e.2.1 == i
  addEnts [] ((ns.filterMap fun (n, i) => at_ n i) ++ (called.filterMap fun e => at_ e.1 e.2.1))

mutual
/-- The cancel rows that the finalisers of a value require, at the row `S` around it. -/
def walkV (rows : List (String × List Ent)) : Nat → List Ent → Table → Val → Table
  | 0, _, t, _ => t
  | k + 1, S, t, V =>
    if let some (i, P, R, cls, M) := hndSite? V then
      let t := walkV rows k S (walkV rows k S (walkV rows k S t P) R) cls
      let Si := (i.ents.zipIdx.map fun ((q, A, B), j) => ((i.n, j, q, A, B) : Ent)) ++ S
      walkC rows k Si t M
    else match V with
    | .pair _ V W | .app _ V W => walkV rows k S (walkV rows k S t V) W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => walkV rows k S t V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => walkC rows k S t M
    | _ => t

/-- `walkV` of a computation. -/
def walkC (rows : List (String × List Ent)) : Nat → List Ent → Table → Comp → Table
  | 0, _, t, _ => t
  | k + 1, S, t, M => match M with
    | .ret _ V | .absurd _ V => walkV rows k S t V
    | .bind _ _ _ M N | .with_ _ M N => walkC rows k S (walkC rows k S t M) N
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ | .withbor2r _ _ _ _ _ _ _ _ M => walkC rows k S t M
    | .letUnit _ V M | .letPair _ _ _ V M => walkC rows k S (walkV rows k S t V) M
    | .case _ V _ M _ N | .loop _ _ _ V M N =>
      walkC rows k S (walkC rows k S (walkV rows k S t V) M) N
    | .perform _ _ _ V | .abort _ _ _ V => walkV rows k S t V
    | .handle _ _ _ hr hc M => walkC rows k S (walkV rows k S (walkV rows k S t hr) hc) M
    | .unwind _ _ _ M D N =>
      -- `[then]`: each operation of `S` that captures a continuation is cancelled running `D`.
      let SD := finRow rows S D
      let t := S.foldl (fun t e => if e.captures then t.add e.1 e.2.1 SD else t) t
      walkC rows k S (walkC rows k S (walkC rows k S t M) D) N
    | .force .. | .top _ => t
end

/-- The cancel rows the finalisers of the effects pass's output `ds` require.  `[spec §27]` -/
def table (ds : List Decl) : Table :=
  let rows : List (String × List Ent) := ds.filterMap fun
    | .def_ _ n _ A _ _ => let r := rowOfTy A; if r.isEmpty then none else some (n.name, r)
    | _ => none
  ds.foldl (fun t d => match d with
    | .def_ _ n _ _ V _ => walkV rows 100000 ((rows.lookup n.name).getD []) t V
    | .main _ _ M => walkC rows 100000 [] t M
    | _ => t) []

end Frontend.Elab.Fins
