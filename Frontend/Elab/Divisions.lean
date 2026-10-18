import Frontend.Elab.Instances

/-!
# Frontend — Elab — divisions that raise  `[spec §39]`

An integer division with no answer (a zero divisor, `MIN / -1`) raises `Fail[DivError]`
(`lib/arith.bc`). Whether `a / b` can fail depends on its operands' width (a float's cannot) and
on its divisor at that width (a nonzero literal, not `-1` for a signed `/`, cannot). The walk that
reads the instances (`Instances.found`, `Instances.divCanFail`) types the operands, and records
each division that can fail at its own span with the instance it raises, `[DivError]`, a
division whose width it cannot read among them. The effects pass then writes each of those,
before it infers a row, as a program would by hand:

    a / b   ⟶   run (case checked_div(a, b) { inl q -> return q | inr e -> return raise((e : DivError)) })

with the `raise` at the division's span, where the table holds its instance. So it is an ordinary
operation of `Fail[DivError]` for everything the pass does: rows, slots (SPEC §38), copies,
counted loops, unwinding borrows and drop glue. The other divisions are left as written, and the
typed elaboration gives them the bare operation (`Frontend/Sugar.lean`, `surfOp`).

The rewrite reaches every value and computation of a declaration's body, with the owner the walk
gives the declaration, so a division's key is the one the walk recorded.
-/

namespace Frontend.Elab.Divisions
open Frontend.Elab.Instances (Key key ownerKey divErrorTy)

/-- The division `a o b` at `sp`, written to raise. -/
def raiseForm (sp osp psp : Span) (o : SurfOp) (a b : Val) : Val :=
  let tag := s!"{sp.start.line}_{sp.start.col}_{sp.stop.line}_{sp.stop.col}"
  let q : Ident := ⟨s!"io_rq{tag}", sp⟩
  let e : Ident := ⟨s!"io_re{tag}", sp⟩
  .run sp (.case sp (.app sp (.sugar osp (.checked o)) (.pair psp a b))
    q (.ret sp (.var sp q.name))
    e (.ret sp (.app sp (.var osp "raise") (.ascribe sp (.var sp e.name) divErrorTy))))

mutual
/-- The divisions of a value that can fail (`ks`, in the declaration `owner`), written to raise. -/
def goV (ks : List Key) (owner : String) : Val → Val
  | .app sp (.sugar osp (.op o)) (.pair psp a b) =>
    let a := goV ks owner a
    let b := goV ks owner b
    if ks.contains (key owner sp) then raiseForm sp osp psp o a b
    else .app sp (.sugar osp (.op o)) (.pair psp a b)
  | .pair sp V W => .pair sp (goV ks owner V) (goV ks owner W)
  | .app sp V W => .app sp (goV ks owner V) (goV ks owner W)
  | .inl sp V => .inl sp (goV ks owner V)
  | .inr sp V => .inr sp (goV ks owner V)
  | .unbang sp V => .unbang sp (goV ks owner V)
  | .boxed sp l V => .boxed sp l (goV ks owner V)
  | .unbox sp V => .unbox sp (goV ks owner V)
  | .sub sp V l => .sub sp (goV ks owner V) l
  | .roll sp V => .roll sp (goV ks owner V)
  | .unroll sp V => .unroll sp (goV ks owner V)
  | .inst sp V l => .inst sp (goV ks owner V) l
  | .ascribe sp V A => .ascribe sp (goV ks owner V) A
  | .shorten sp m σ l V => .shorten sp m σ l (goV ks owner V)
  | .thunk sp M => .thunk sp (goC ks owner M)
  | .thunkv sp M => .thunkv sp (goC ks owner M)
  | .bangThunk sp M => .bangThunk sp (goC ks owner M)
  | .bangThunkv sp M => .bangThunkv sp (goC ks owner M)
  | .run sp M => .run sp (goC ks owner M)
  | V => V

/-- The divisions of a computation that can fail, written to raise. -/
def goC (ks : List Key) (owner : String) : Comp → Comp
  | .ret sp V => .ret sp (goV ks owner V)
  | .absurd sp V => .absurd sp (goV ks owner V)
  | .bind sp x A M N lin => .bind sp x A (goC ks owner M) (goC ks owner N) lin
  | .lam sp x A M => .lam sp x A (goC ks owner M)
  | .app sp M x => .app sp (goC ks owner M) x
  | .with_ sp M N => .with_ sp (goC ks owner M) (goC ks owner N)
  | .proj sp i M => .proj sp i (goC ks owner M)
  | .letUnit sp V M => .letUnit sp (goV ks owner V) (goC ks owner M)
  | .letPair sp x y V M => .letPair sp x y (goV ks owner V) (goC ks owner M)
  | .case sp V x M y N => .case sp (goV ks owner V) x (goC ks owner M) y (goC ks owner N)
  | .lamL sp x b M => .lamL sp x b (goC ks owner M)
  | .inst sp M a => .inst sp (goC ks owner M) a
  | .nuIn sp M => .nuIn sp (goC ks owner M)
  | .nuOut sp M => .nuOut sp (goC ks owner M)
  | .ascribe sp M C => .ascribe sp (goC ks owner M) C
  | .perform sp k i V => .perform sp k i (goV ks owner V)
  | .abort sp k i V => .abort sp k i (goV ks owner V)
  | .handle sp k hr hc M => .handle sp k hr hc (goC ks owner M)
  | .unwind sp x A M D N => .unwind sp x A (goC ks owner M) (goC ks owner D) (goC ks owner N)
  | .withbor2r sp x b A B r p m M => .withbor2r sp x b A B r p m (goC ks owner M)
  | .loop sp ℓ src V M N => .loop sp ℓ src (goV ks owner V) (goC ks owner M) (goC ks owner N)
  | M => M
end

/-- A declaration with its divisions that can fail (`ks`) written to raise, each body at the owner
the walk gives it (`Instances.found`). -/
def goDecl (ks : List Key) : Decl → Decl
  | .def_ sp n ps A V mk => .def_ sp n ps A (goV ks (ownerKey n.name n.span) V) mk
  | .main sp C M => .main sp C (goC ks (ownerKey "main" sp) M)
  | .chandler sp ch =>
    let owner := ownerKey ch.name.name ch.name.span
    let (x, A, M) := ch.ret
    .chandler sp { ch with ret := (x, A, goC ks owner M),
                           clauses := ch.clauses.map fun c => { c with body := goC ks owner c.body } }
  | .handler sp h st S e cs lent =>
    let owner := ownerKey h.name h.span
    .handler sp h st S e (cs.map fun c => { c with body := goC ks owner c.body }) lent
  | d => d

/-- A division that may fail, as written: `/` or `%` whose divisor is not a literal `k` with
`0 < k < 256` and with no float literal operand (`Instances.divCanFail` decides it). -/
def candidate (o : SurfOp) (a b : Val) : Bool :=
  let flit : Val → Bool := fun | .sugar _ (.flit ..) => true | _ => false
  (o == .div || o == .rem) && !flit a && !flit b && !Instances.safeDivisor none o b

mutual
/-- The value has a division that may fail (`candidate`). -/
def candV : Val → Bool
  | .app _ (.sugar _ (.op o)) (.pair _ a b) => candidate o a b || candV a || candV b
  | .pair _ V W | .app _ V W => candV V || candV W
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => candV V
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => candC M
  | _ => false

/-- The computation has a division that may fail. -/
def candC : Comp → Bool
  | .ret _ V | .absurd _ V | .perform _ _ _ V | .abort _ _ _ V => candV V
  | .bind _ _ _ M N _ | .with_ _ M N => candC M || candC N
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ | .handle _ _ _ _ M | .withbor2r _ _ _ _ _ _ _ _ M => candC M
  | .letUnit _ V M | .letPair _ _ _ V M => candV V || candC M
  | .case _ V _ M _ N | .loop _ _ _ V M N => candV V || candC M || candC N
  | .unwind _ _ _ M D N => candC M || candC D || candC N
  | _ => false
end

/-- The declaration has a division that may fail. -/
def Decl.hasCandidate : Decl → Bool
  | .def_ _ _ _ _ V _ => candV V
  | .main _ _ M => candC M
  | .chandler _ ch => candC ch.ret.2.2 || ch.clauses.any (candC ·.body)
  | .handler _ _ _ _ _ cs _ => cs.any (candC ·.body)
  | _ => false

/-- The declarations with their divisions that can fail written to raise. -/
def rewrite (ks : List Key) (ds : List Decl) : List Decl :=
  if ks.isEmpty then ds else ds.map (goDecl ks)

end Frontend.Elab.Divisions
