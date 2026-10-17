import Frontend.Syntax

/-!
# Frontend — Elab — divisions that raise  `[spec §38]`

An integer division `a / b` or `a % b` with no answer (a zero divisor, `MIN / -1`) raises
`arith_raise` of `lib/arith.bc`. Rows are inferred before types are known
(`Frontend/Elab/Effects.lean`), and whether a division can fail depends on its width (a float's
cannot) and on its divisor as elaborated at that width (a nonzero literal, not `-1` for a signed
`/`, cannot). So the typed elaboration decides it, in a first pass, and this pass writes the
divisions that can fail, before effects are resolved, as the program would by hand:

    a / b   ⟶   run (case checked_div(a, b) { inl q -> return q | inr e -> return arith_raise(e) })

**Candidates.** A division is a candidate unless it is evidently one that cannot fail: its divisor
is a literal `k` with `0 < k < 256` (nonzero at every integer width, and never `-1`), or a float
literal, or its dividend is a float literal. A program with no candidate is elaborated once.

**The passes** (`Frontend/Sugar.lean`, `elaborateS`). The first numbers the candidates in the
order of the declarations (`VSugar.opAt o k`), and the typed elaboration records each one that
can fail at a width it is elaborated at (`divTag`); a template instantiated at two widths fails if
it can at one. The second pass, on the same declarations, numbers them again in the same order
and writes those as above; the others are `VSugar.op` again.

`checked_div(a, b)` and `checked_rem(a, b)`, unless the program declares a function of that name,
are `VSugar.checked`.
-/

namespace Frontend.Elab.Divs

/-- What the pass does: in the first pass `raising` is `none` and each candidate is numbered;
in the second, the candidates whose numbers it holds are written to raise. -/
structure Pass where
  raising : Option (List Nat)
  /-- `checked_div` and `checked_rem` are the program's own functions. -/
  ownChecked : Bool := false

/-- The candidate is evidently a division that cannot fail. -/
def evident (a b : Val) : Bool :=
  match a, b with
  | .sugar _ (.flit ..), _ => true
  | _, .sugar _ (.flit ..) => true
  | _, .sugar _ (.lit k) => 0 < k && k < 256
  | _, _ => false

/-- The division `a o b`, numbered `k`, written to raise: `checked_div` taken apart, its error
performed as `arith_raise`. -/
def raiseForm (sp osp psp : Span) (o : SurfOp) (k : Nat) (a b : Val) : Val :=
  let q : Ident := ⟨s!"io_rq{k}", sp⟩
  let e : Ident := ⟨s!"io_re{k}", sp⟩
  .run sp (.case sp (.app sp (.sugar osp (.checked o)) (.pair psp a b))
    q (.ret sp (.var sp q.name))
    e (.ret sp (.app sp (.var osp "arith_raise") (.var sp e.name))))

/-- The candidates numbered so far, and whether a `checked_div` or `checked_rem` was rewritten. -/
abbrev DM := StateM (Nat × Bool)

mutual
/-- The pass over a value. -/
def goV (P : Pass) : Nat → Val → DM Val
  | 0, V => pure V
  | n + 1, V => match V with
    | .app sp (.sugar osp (.op o)) (.pair psp a b) => do
      let a' ← goV P n a
      let b' ← goV P n b
      if (o != .div && o != .rem) || evident a b then
        return .app sp (.sugar osp (.op o)) (.pair psp a' b')
      let k ← modifyGet fun (k, c) => (k, (k + 1, c))
      match P.raising with
      | none => pure (.app sp (.sugar osp (.opAt o k)) (.pair psp a' b'))
      | some rs =>
        if rs.contains k then pure (raiseForm sp osp psp o k a' b')
        else pure (.app sp (.sugar osp (.op o)) (.pair psp a' b'))
    | .app sp (.var vsp x) W => do
      let W' ← goV P n W
      if !P.ownChecked && (x == "checked_div" || x == "checked_rem") then
        if let .pair .. := W' then
          modify fun (k, _) => (k, true)
          return .app sp (.sugar vsp (.checked (if x == "checked_div" then .div else .rem))) W'
      pure (.app sp (.var vsp x) W')
    | .pair sp V W => do pure (.pair sp (← goV P n V) (← goV P n W))
    | .inl sp V => do pure (.inl sp (← goV P n V))
    | .inr sp V => do pure (.inr sp (← goV P n V))
    | .thunk sp M => do pure (.thunk sp (← goC P n M))
    | .thunkv sp M => do pure (.thunkv sp (← goC P n M))
    | .bangThunk sp M => do pure (.bangThunk sp (← goC P n M))
    | .bangThunkv sp M => do pure (.bangThunkv sp (← goC P n M))
    | .unbang sp V => do pure (.unbang sp (← goV P n V))
    | .boxed sp a V => do pure (.boxed sp a (← goV P n V))
    | .unbox sp V => do pure (.unbox sp (← goV P n V))
    | .sub sp V a => do pure (.sub sp (← goV P n V) a)
    | .roll sp V => do pure (.roll sp (← goV P n V))
    | .unroll sp V => do pure (.unroll sp (← goV P n V))
    | .run sp M => do pure (.run sp (← goC P n M))
    | .app sp V W => do pure (.app sp (← goV P n V) (← goV P n W))
    | .inst sp V a => do pure (.inst sp (← goV P n V) a)
    | .ascribe sp V A => do pure (.ascribe sp (← goV P n V) A)
    | .shorten sp m σ a V => do pure (.shorten sp m σ a (← goV P n V))
    | V => pure V

/-- The pass over a computation. -/
def goC (P : Pass) : Nat → Comp → DM Comp
  | 0, M => pure M
  | n + 1, M => match M with
    | .ret sp V => do pure (.ret sp (← goV P n V))
    | .bind sp x A M N lin => do pure (.bind sp x A (← goC P n M) (← goC P n N) lin)
    | .lam sp x A M => do pure (.lam sp x A (← goC P n M))
    | .app sp M x => do pure (.app sp (← goC P n M) x)
    | .with_ sp M N => do pure (.with_ sp (← goC P n M) (← goC P n N))
    | .proj sp i M => do pure (.proj sp i (← goC P n M))
    | .letUnit sp V M => do pure (.letUnit sp (← goV P n V) (← goC P n M))
    | .letPair sp x y V M => do pure (.letPair sp x y (← goV P n V) (← goC P n M))
    | .case sp V x M y N => do
      let V' ← goV P n V
      pure (.case sp V' x (← goC P n M) y (← goC P n N))
    | .absurd sp V => do pure (.absurd sp (← goV P n V))
    | .lamL sp x b M => do pure (.lamL sp x b (← goC P n M))
    | .inst sp M a => do pure (.inst sp (← goC P n M) a)
    | .nuIn sp M => do pure (.nuIn sp (← goC P n M))
    | .nuOut sp M => do pure (.nuOut sp (← goC P n M))
    | .ascribe sp M C => do pure (.ascribe sp (← goC P n M) C)
    | .for_ sp x V M N => do
      let V' ← goV P n V
      pure (.for_ sp x V' (← goC P n M) (← goC P n N))
    | .perform sp k i V => do pure (.perform sp k i (← goV P n V))
    | .abort sp k i V => do pure (.abort sp k i (← goV P n V))
    | .handle sp k hr hc M => do pure (.handle sp k hr hc (← goC P n M))
    | .unwind sp x A M D N => do
      let M' ← goC P n M
      let D' ← goC P n D
      pure (.unwind sp x A M' D' (← goC P n N))
    | .withbor2r sp x b A B r p m M => do pure (.withbor2r sp x b A B r p m (← goC P n M))
    | M => pure M
end

/-- The depth bound of the pass. -/
def fuel : Nat := 1 <<< 16

/-- A clause's body passed over. -/
def goClause (P : Pass) (c : Clause) : DM Clause := do
  pure { c with body := ← goC P fuel c.body }

/-- The pass over a declaration. -/
def goDecl (P : Pass) : Decl → DM Decl
  | .def_ sp n ps A V mk => do pure (.def_ sp n ps A (← goV P fuel V) mk)
  | .main sp C M => do pure (.main sp C (← goC P fuel M))
  | .handler sp n st S e cs l => do pure (.handler sp n st S e (← cs.mapM (goClause P)) l)
  | .chandler sp h => do
    let (x, A, M) := h.ret
    let M' ← goC P fuel M
    pure (.chandler sp { h with ret := (x, A, M'), clauses := ← h.clauses.mapM (goClause P) })
  | .poly sp n tps lps hd A V => do pure (.poly sp n tps lps hd A (← goV P fuel V))
  | d => pure d

/-- The declarations passed over, each paired with what it was; the number of candidates; and
whether any declaration changed. -/
def run (P : Pass) (ds : List Decl) : List (Decl × Decl) × Nat × Bool :=
  let ownChecked := ds.any fun
    | .def_ _ n _ _ _ _ => n.name == "checked_div" || n.name == "checked_rem"
    | _ => false
  let P := { P with ownChecked }
  let (out, k, c) := (ds.mapM fun d => do pure (d, ← goDecl P d)).run (0, false)
  (out, k, c || k > 0)

end Frontend.Elab.Divs
