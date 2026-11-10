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
  | .nil | .top => []
  | .cons n i q A B _ r => (n, i, q, A, B) :: Row.ents r

/-- The row of a function's or a block's type: the first `F[…]` on the spine of its result.
`[spec §27]` -/
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
weakens). It is the checker's elaboration of the declared answer and Core's `isZero`, as
`OpDecl.abortive` reads it.  `[spec §27]` -/
def zeroTy (B : VTy) : Bool :=
  match Frontend.Check.elabV Frontend.Check.tyFuel
      ⟨⟨#[], 0, [], []⟩, .empty, .empty, [], [], [], [], []⟩ B with
  | .ok B => B.isZero
  | .error _ => match B with
    | .zero _ => true
    | _ => false

/-- The entry captures a continuation (`capB`): its cancel row is read.  `[spec §27]` -/
def Ent.captures (e : Ent) : Bool := e.2.2.1 != .lin && !zeroTy e.2.2.2.2

/-- Add the entries `es` to a list of entries, each name once.  `[spec §27]` -/
def addEnts (acc es : List Ent) : List Ent :=
  es.foldl (fun acc e => if acc.any fun f => f.1 == e.1 && f.2.1 == e.2.1 then acc else acc ++ [e])
    acc

/-- The table with `es` added to the cancel row of `n.i`.  `[spec §27]` -/
def Table.add (t : Table) (n i : Nat) (es : List Ent) : Table :=
  if es.isEmpty then t else
  match t.find? (·.1 == (n, i)) with
  | some (_, cur) => t.map fun (k, v) => if k == (n, i) then (k, addEnts cur es) else (k, v)
  | none => t ++ [((n, i), addEnts [] es)]

/-- The entries of the cancel row of `n.i` in the table.  `[spec §27]` -/
def Table.ents (t : Table) (n i : Nat) : List Ent :=
  match t.find? (·.1 == (n, i)) with
  | some (_, es) => es
  | none => []

/-- The entry is abortive: it answers `0` at a qualifier that weakens.  `[spec §27]` -/
def Ent.aborts (e : Ent) : Bool := e.2.2.1 != .lin && zeroTy e.2.2.2.2

/-- A handler's clauses, as the effects pass writes them: each its parameter and its body.
`[spec §27]` -/
def clauseBodies : Val → List (String × Comp)
  | .pair _ (.thunkv _ (.lam _ p _ M)) rest => (p.name, M) :: clauseBodies rest
  | .pair _ _ rest => ("", .top .none) :: clauseBodies rest
  | _ => []

/-- The cancel row of `n.i` in the table, as a written row (each entry's own cancel row empty).
`[spec §27]` -/
def Table.finOf (t : Table) (n i : Nat) : Row :=
  match t.find? (·.1 == (n, i)) with
  | some (_, es) => es.foldr (fun (n, i, q, A, B) r => .cons n i q A B .nil r) .nil
  | none => .nil

/-- A handler site of the effects pass's output, `hndCtl i P R cls (thunk M)`: the site's info
and the computation it handles.  `[spec §27]` -/
def hndSite? : Val → Option (HInfo × Val × Val × Val × Comp)
  | .app _ (.app _ (.app _ (.app _ (.sugar _ (.hndCtl i)) P) R) cls) (.thunk _ M) => some (i, P, R, cls, M)
  | _ => none

/-- A value that makes no call: the end of a path that returns it has no effect after the cancel
(a closure it builds runs later). Every call counts as an effect, an answering effect's (a
capability's, not in any row) included, so a cancel is never placed before one.  `[spec §27]` -/
def callFree : Val → Bool
  | .var .. | .unit _ | .clone .. | .sugar _ (.lit _) | .sugar _ (.flit ..) => true
  | .pair _ V W => callFree V && callFree W
  | .inl _ V | .inr _ V | .ascribe _ V _ | .roll _ V | .unroll _ V | .unbang _ V => callFree V
  | .thunk .. | .thunkv .. | .bangThunk .. | .bangThunkv .. => true
  | _ => false

/-- What follows a loop whose value is bound, `r <- return forRes; N₀` (`let r = for …`, with or
without `else`): its span, `r`, `r`'s written type, the value and `N₀`.  `[spec §27]` -/
def boundRes? : Comp → Option (Span × Ident × Option VTy × Val × Comp)
  | .bind bsp r A (.ret _ R@(.sugar _ .forRes)) N => some (bsp, r, A, R, N)
  | .bind bsp r A (.ret _ R@(.app _ (.sugar _ .forRes) _)) N => some (bsp, r, A, R, N)
  | _ => none

/-- `M`, which runs while the continuation `k` is live and not yet used, with `k` cancelled exactly
once on each of its paths that does not use it, as Rust drops a value: at the end of the path,
and on the way out of an abort or a cancel that passes through it.

* **The end of the path**: after every effect of the path, a performing terminal included. A
  terminal value `return V` (`callFree`) is the path's result: the cancel goes immediately before
  it (SPEC §12's insertion policy, *At the end of the path*). Any other terminal `T` performs, so
  it is the path's last effect: `x <- T; cancel k; return x`. A head `M₁` of `x <- M₁; N` or of
  `x <- M₁ unwind (D); N` that mentions `k` is owed it (*Tail positions*), by this rule inside it;
  a `case` arm or a `<M, N>` component that does not use it cancels it; `<>` and `absurd V` absorb
  it (their path does not finish).
* **An abort or a cancel through the path**: each head `M₁` of `x <- M₁; N` that does not mention
  `k`, through which an abort or a cancel can pass (`wrapHead`: its row, as the typing gives it,
  holds an abortive operation or one that captures a continuation), is
  `x <- M₁ unwind (cancel k); N` (`[then]` with the finaliser at the cancel's row, §27): when `M₁`
  aborts, or its continuation is cancelled, the finaliser cancels `k` and `N` does not run; when
  `M₁` answers, `N` runs with `k` still live. Any other head is left as it is. A region of the
  clause's own, `x <- M₁ unwind (D); N`, whose body does not mention `k` is such a head as a whole,
  so its own finaliser `D` runs first, then `k`'s cancel (inner regions unwind first); so is a loop
  whose body can abort; a loop whose value is bound is wrapped with the binding of its value
  (`boundRes?`), so the head is the loop as elaborated. (A loop's `break` and `continue` stay in
  the clause; a `return` in a clause is refused before.)

Exactly once: `k` is live from its binding until the first of a head's abort (its finaliser
cancels it, and nothing after runs), the end of the path (the cancel after its last effect), or a
use the program wrote (no cancel is inserted on that path after it). The finaliser and the rest
`N` are exclusive branches of `[then]`, and the kernel checks `k`'s linearity on each.

The cancel is `u <- (force k).2; let () = u; T`, the kernel's `[&E₂]`. With `inState`, the
path's terminal `return (thunkv M)` is the state's function of a handler with a state (§21), whose
body is the clause's own code: the path continues in it, by the same rule.  `[spec §12, §21, §27]` -/
def cancelAtEnds (wrapHead : Comp → Bool) (sp : Span) (k : Ident)
    (inState : Bool) : Nat → Comp → Comp
  | 0, M => M
  | n + 1, M =>
    let go := cancelAtEnds wrapHead sp k inState n
    let uses := Frontend.Check.mentionsC k.name
    let usesV := Frontend.Check.mentionsV k.name
    let cancelK : Comp := .proj sp false (.force sp k)
    let cancel (T : Comp) : Comp :=
      let u : Ident := ⟨s!"fx_cancel_{k.name}", sp⟩
      .bind sp u none cancelK (.letUnit sp (.var sp u.name) T)
    -- `x <- M₁; N` with `M₁` a head that does not mention `k`.
    let head (bsp : Span) (x : Ident) (A : Option VTy) (M₁ N : Comp) : Comp :=
      let wrap := wrapHead M₁ && match M₁ with
        | .loop .. => false
        | _ => true
      if wrap then .unwind bsp x A M₁ cancelK (go N) else .bind bsp x A M₁ (go N)
    -- A performing terminal, bound first: `x <- T; cancel k; return x`.
    let last (T : Comp) : Comp :=
      let x : Ident := ⟨s!"fx_last_{k.name}", sp⟩
      head sp x none T (.ret sp (.var sp x.name))
    match M with
    | .bind bsp x A M₁ N =>
      if uses M₁ then .bind bsp x A (go M₁) N else head bsp x A M₁ N
    | .letUnit lsp V N => if usesV V then M else .letUnit lsp V (go N)
    | .letPair lsp x y V N => if usesV V then M else .letPair lsp x y V (go N)
    | .case csp V x M₁ y N =>
      if usesV V then M else .case csp V x (go M₁) y (go N)
    | .with_ wsp M₁ N => .with_ wsp (go M₁) (go N)
    | .lam lsp x A N => .lam lsp x A (go N)
    | .lamL lsp x b N => .lamL lsp x b (go N)
    | .nuIn nsp N => .nuIn nsp (go N)
    | .ascribe asp N C => .ascribe asp (go N) C
    | .unwind usp x A M₁ D N =>
      if uses D then M
      else if uses M₁ then .unwind usp x A (go M₁) D N
      else if wrapHead M₁ then
        -- The region as a head: its finaliser `D` first, then `k`'s cancel.
        let x' : Ident := ⟨s!"fx_reg_{k.name}", usp⟩
        let R : Comp := .unwind usp x' A M₁ D (.ret usp (.var usp x'.name))
        .unwind usp x A R cancelK (go N)
      else .unwind usp x A M₁ D (go N)
    | .loop lsp ℓ src V M₁ N =>
      if usesV V || uses M₁ then M
      else if wrapHead M₁ then
        -- The loop as a head: an abort out of its body cancels `k` on the way out. A loop whose
        -- value is bound (`let r = for …; N₀`) keeps the binding of its value with it, so that the
        -- head is the loop and its value as the typed elaboration elaborates them, and the rest
        -- `N₀` binds `r` to the head's answer.
        match boundRes? N with
        | some (bsp, r, A, R, N₀) =>
          let L : Comp := .loop lsp ℓ src V M₁ (.bind bsp r A (.ret bsp R) (.ret bsp (.var bsp r.name)))
          .unwind lsp r A L cancelK (go N₀)
        | none =>
          let r : Ident := ⟨s!"fx_loop_{k.name}", lsp⟩
          .unwind lsp r none (.loop lsp ℓ src V M₁ (.ret lsp (.unit lsp))) cancelK (go N)
      else .loop lsp ℓ src V M₁ (go N)
    | .ret rsp (.thunkv tsp N) =>
      if inState then .ret rsp (.thunkv tsp (cancelAtEnds wrapHead sp k false n N))
      else if uses M then M else cancel M
    | .ret _ V => if usesV V then M else if callFree V then cancel M else last M
    | .top _ | .absurd .. => M
    | T => if uses T then T else last T

/-- The heads `M₁` of the `x <- M₁ unwind (cancel k); N` that `cancelAtEnds` inserted in `M`.
`[spec §27]` -/
def cancelHeads (k : String) : Nat → Comp → List Comp
  | 0, _ => []
  | n + 1, M => match M with
    | .unwind _ _ _ M₁ (.proj _ false (.force _ k')) N =>
      (if k'.name == k then [M₁] else []) ++ cancelHeads k n M₁ ++ cancelHeads k n N
    | .unwind _ _ _ M₁ D N => cancelHeads k n M₁ ++ cancelHeads k n D ++ cancelHeads k n N
    | .bind _ _ _ M₁ N | .with_ _ M₁ N => cancelHeads k n M₁ ++ cancelHeads k n N
    | .letUnit _ _ N | .letPair _ _ _ _ N | .lam _ _ _ N | .lamL _ _ _ N | .nuIn _ N
    | .ascribe _ N _ => cancelHeads k n N
    | .case _ _ _ M₁ _ N => cancelHeads k n M₁ ++ cancelHeads k n N
    | .ret _ (.thunkv _ N) => cancelHeads k n N
    | _ => []

mutual
/-- The names a value performs and the functions it names, less the operations of the sites inside
it (`inner`): `(names, functions)`.  `[spec §27]` -/
def perfV : Nat → List Nat → Val → List (Nat × Nat) × List String
  | 0, _, _ => ([], [])
  | k + 1, inner, V =>
    if let some (i, P, R, cls, M) := hndSite? V then
      let a := perfV k inner P; let b := perfV k inner R; let c := perfV k inner cls
      let d := perfC k (i.n :: inner) M
      (a.1 ++ b.1 ++ c.1 ++ d.1, a.2 ++ b.2 ++ c.2 ++ d.2)
    else match V with
    | .var _ x | .clone _ x | .defApp _ x _ => ([], [x])
    | .pair _ V W | .app _ V W =>
      let a := perfV k inner V; let b := perfV k inner W; (a.1 ++ b.1, a.2 ++ b.2)
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => perfV k inner V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => perfC k inner M
    | _ => ([], [])

/-- `perfV` of a computation.  `[spec §27]` -/
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

/-- The operations `n.i` a computation performs, by the one walk both the inference and the
typed elaboration use: its `perform`s and `abort`s, less those of the sites inside it, and the
row (`rowOf`) of every function it names. The rows are the facts the effects pass wrote in its
copies' types (`fnRows`); the typed elaboration gives a local's (a block parameter's) by its type.
`[spec §27]`

UNPROVED: a function with a row is named in a computation only to be called there (a copy, the
effects pass's: `io_fg <- return unbang f; …; force io_fg a`, or `f[A](a)` of a template's copy),
so naming it performs its row. Why it should hold: the effects pass names a copy only at its call,
and refuses a function with a row passed as a value. What breaks if it does not: a head that
performs an operation this walk misses is not wrapped in `unwind (cancel k)`, and the kernel
refuses `k` live across it (a refusal, never a wrong program); one it counts that the head does not
perform is wrapped, which the kernel checks too. -/
def opsOf (rowOf : String → List (Nat × Nat)) (M : Comp) : List (Nat × Nat) :=
  let (ns, fs) := perfC 100000 [] M
  ns ++ fs.flatMap rowOf

/-- The entries of `S` among the operations `ns`. -/
def entsAt (S : List Ent) (ns : List (Nat × Nat)) : List Ent :=
  addEnts [] (ns.filterMap fun (n, i) => S.find? fun e => e.1 == n && e.2.1 == i)

/-- Each function of the effects pass's output with a row, as the effects pass wrote it in its
type: the fact both the inference and the typed elaboration read for a call.  `[spec §27]` -/
def fnRows (ds : List Decl) : List (String × List (Nat × Nat)) :=
  ds.filterMap fun
    | .def_ _ n _ A _ _ =>
      let r := rowOfTy A
      if r.isEmpty then none else some (n.name, r.map fun e => (e.1, e.2.1))
    | _ => none

/-- A function's row by its name, as its written type gives it. -/
def rowNames (rows : List (String × List Ent)) (f : String) : List (Nat × Nat) :=
  ((rows.lookup f).getD []).map fun e => (e.1, e.2.1)

/-- The finaliser's row `Σ_D` at the site's row `S`: the entries of `S` it performs (`opsOf`).
`[spec §27]` -/
def finRow (rows : List (String × List Ent)) (S : List Ent) (D : Comp) : List Ent :=
  entsAt S (opsOf (rowNames rows) D)

mutual
/-- The cancel rows that the finalisers of a value require, at the row `S` around it.
`[spec §27]` -/
def walkV (rows : List (String × List Ent)) (glob : List Ent) : Nat → List Ent → Table → Val → Table
  | 0, _, t, _ => t
  | k + 1, S, t, V =>
    if let some (i, P, R, cls, M) := hndSite? V then
      let t := walkV rows glob k S (walkV rows glob k S t P) R
      let Si := (i.ents.zipIdx.map fun ((q, A, B), j) => ((i.n, j, q, A, B) : Ent)) ++ S
      let t := walkC rows glob k Si t M
      walkV rows glob k S t cls
    else match V with
    | .pair _ V W | .app _ V W => walkV rows glob k S (walkV rows glob k S t V) W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => walkV rows glob k S t V
    | .run _ M => walkC rows glob k S t M
    -- A thunk runs at its own row: the operations it performs (an effectful block's, at the sites
    -- where it is called), beside the row around it.
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M =>
      walkC rows glob k (addEnts S (entsAt glob (opsOf (rowNames rows) M))) t M
    | _ => t

/-- `walkV` of a computation.  `[spec §27]` -/
def walkC (rows : List (String × List Ent)) (glob : List Ent) : Nat → List Ent → Table → Comp → Table
  | 0, _, t, _ => t
  | k + 1, S, t, M => match M with
    | .ret _ V | .absurd _ V => walkV rows glob k S t V
    | .bind _ _ _ M N | .with_ _ M N => walkC rows glob k S (walkC rows glob k S t M) N
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ | .withbor2r _ _ _ _ _ _ _ _ M => walkC rows glob k S t M
    | .letUnit _ V M | .letPair _ _ _ V M => walkC rows glob k S (walkV rows glob k S t V) M
    | .case _ V _ M _ N | .loop _ _ _ V M N =>
      walkC rows glob k S (walkC rows glob k S (walkV rows glob k S t V) M) N
    | .perform _ _ _ V | .abort _ _ _ V => walkV rows glob k S t V
    | .handle _ _ _ hr hc M => walkC rows glob k S (walkV rows glob k S (walkV rows glob k S t hr) hc) M
    | .unwind _ _ _ M D N =>
      -- `[then]`: each operation of `S` that captures a continuation is cancelled running `D`.
      let SD := finRow rows S D
      let t := S.foldl (fun t e => if e.captures then t.add e.1 e.2.1 SD else t) t
      walkC rows glob k S (walkC rows glob k S (walkC rows glob k S t M) D) N
    | .force .. | .top _ => t
end

mutual
/-- The handler sites in a value.  `[spec §27]` -/
def sitesV : Nat → Val → List HInfo
  | 0, _ => []
  | k + 1, V =>
    if let some (i, P, R, cls, M) := hndSite? V then
      i :: (sitesV k P ++ sitesV k R ++ sitesV k cls ++ sitesC k M)
    else match V with
    | .pair _ V W | .app _ V W => sitesV k V ++ sitesV k W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => sitesV k V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => sitesC k M
    | _ => []

/-- `sitesV` of a computation.  `[spec §27]` -/
def sitesC : Nat → Comp → List HInfo
  | 0, _ => []
  | k + 1, M => match M with
    | .ret _ V | .absurd _ V | .perform _ _ _ V | .abort _ _ _ V => sitesV k V
    | .bind _ _ _ M N | .with_ _ M N => sitesC k M ++ sitesC k N
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ | .withbor2r _ _ _ _ _ _ _ _ M => sitesC k M
    | .letUnit _ V M | .letPair _ _ _ V M => sitesV k V ++ sitesC k M
    | .case _ V _ M _ N | .loop _ _ _ V M N => sitesV k V ++ sitesC k M ++ sitesC k N
    | .handle _ _ _ hr hc M => sitesV k hr ++ sitesV k hc ++ sitesC k M
    | .unwind _ _ _ M D N => sitesC k M ++ sitesC k D ++ sitesC k N
    | .force .. | .top _ => []
end

/-- The handler sites of the effects pass's output.  `[spec §27]` -/
def sitesOf (ds : List Decl) : List HInfo :=
  ds.flatMap fun
    | .def_ _ _ _ _ V _ => sitesV 100000 V
    | .main _ _ M => sitesC 100000 M
    | _ => []

/-- A site's entries.  `[spec §27]` -/
def HInfo.entries (i : HInfo) : List Ent :=
  i.ents.zipIdx.map fun ((q, A, B), j) => ((i.n, j, q, A, B) : Ent)

/-- Each operation `n.i` of a handler site by its surface name, `E.op`, the effects `effs` declare:
for messages.  `[spec §27]` -/
def opNames (effs : List (String × List String)) (ds : List Decl) : List ((Nat × Nat) × String) :=
  (sitesOf ds).flatMap fun i =>
    let ops := (effs.lookup i.site.eff).getD []
    (List.range i.ents.length).map fun j =>
      ((i.n, j), s!"{i.site.eff}.{ops.getD j s!"{j}"}")

/-- The cancel rows the finalisers of the effects pass's output `ds` require.  `[spec §27]` -/
def table (ds : List Decl) : Table :=
  let rows : List (String × List Ent) := ds.filterMap fun
    | .def_ _ n _ A _ _ => let r := rowOfTy A; if r.isEmpty then none else some (n.name, r)
    | _ => none
  -- Every entry by its name: the handler sites' and the functions' rows.
  let glob : List Ent := addEnts [] ((ds.flatMap fun
    | .def_ _ _ _ A _ _ => rowOfTy A
    | _ => []) ++ (sitesOf ds).flatMap HInfo.entries)
  ds.foldl (fun t d => match d with
    | .def_ _ n _ _ V _ => walkV rows glob 100000 ((rows.lookup n.name).getD []) t V
    | .main _ _ M => walkC rows glob 100000 [] t M
    | _ => t) []

end Frontend.Elab.Fins
