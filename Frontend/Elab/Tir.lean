import Frontend.Check.Checker

/-!
# Frontend — Elab — the typed IR  `[#54, docs/typed-elaboration.md §1.1]`

The typed IR (TIR) has one node per node of the program. Each node records:

* its span;
* its type, a value or computation type in the checker's own types (`CVTy`, `CCTy`), or `none`
  where it is not known;
* the variables it binds, each with its identity, its type and its class (SPEC §12);
* its effect: `div` when it is a computation that returns a loop (SPEC §14).

A node keeps its source node (`Head`), and its children are typed nodes in the order
`Head.kids` gives. `Head.rebuild` puts lowered children back, so lowering is a function of the
TIR alone.
-/

namespace Frontend.Elab
open Frontend.Check

/-- A node's type. -/
inductive Ty where
  | val (A : CVTy)
  | comp (C : CCTy)
  | none
  deriving Inhabited

def Ty.known : Ty → Bool
  | .none => false
  | _ => true

/-- SPEC §12's three classes of value type: persistent (copied and dropped freely), with a
destructor (dropped by the checker), and strictly linear (no destructor: it must be consumed or
handed back). -/
inductive Class where
  | persistent
  | dtor
  | linear
  deriving DecidableEq, Repr, Inhabited

def Class.of (A : CVTy) : Class :=
  if A.persistent then .persistent else if hasDtorB A then .dtor else .linear

def Class.name : Class → String
  | .persistent => "persistent"
  | .dtor => "destructor"
  | .linear => "linear"

/-- A variable a node binds: its name, identity, type and class. -/
structure Binder where
  name : String
  id : Nat
  ty : Option CVTy
  deriving Inhabited

def Binder.cls (b : Binder) : Option Class := b.ty.map Class.of

/-- A computation's effect (SPEC §14). -/
inductive Effect where
  | total
  | div
  deriving DecidableEq, Inhabited

/-- `F (U (loop B R))`: a computation that returns a loop. -/
def returnsLoop : CCTy → Bool
  | .ret (.thunk (.nu (.amp (.ret (.sum _ (.tvar 0))) (.ret _)))) => true
  | _ => false

def Ty.effect : Ty → Effect
  | .comp C => if returnsLoop C then .div else .total
  | _ => .total

/-- A source node. -/
inductive Head where
  | val (v : Val)
  | comp (M : Comp)

instance : Inhabited Head := ⟨.comp (.top Span.none)⟩

def Head.span : Head → Span
  | .val v => v.span
  | .comp M => M.span

/-- A node of the typed IR. -/
inductive TNode where
  | mk (head : Head) (ty : Ty) (binders : List Binder) (kids : List TNode)

instance : Inhabited TNode := ⟨.mk default .none [] []⟩

def TNode.head : TNode → Head | .mk h _ _ _ => h
def TNode.ty : TNode → Ty | .mk _ t _ _ => t
def TNode.binders : TNode → List Binder | .mk _ _ bs _ => bs
def TNode.kids : TNode → List TNode | .mk _ _ _ ks => ks
def TNode.span (t : TNode) : Span := t.head.span
def TNode.effect (t : TNode) : Effect := t.ty.effect

/-! ### Children -/

/-- The children of a source node, in order. -/
def Head.kids : Head → List Head
  | .val v => match v with
    | .pair _ V W | .app _ V W => [.val V, .val W]
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => [.val V]
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => [.comp M]
    | .var .. | .defApp .. | .unit _ | .const .. | .lend .. => []
  | .comp M => match M with
    | .ret _ V | .absurd _ V => [.val V]
    | .bind _ _ _ M N _ | .with_ _ M N => [.comp M, .comp N]
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ => [.comp M]
    | .letUnit _ V M | .letPair _ _ _ V M => [.val V, .comp M]
    | .case _ V _ M _ N | .for_ _ _ V M N => [.val V, .comp M, .comp N]
    | .force .. | .top _ => []

/-- A source node with its children replaced, in the order of `Head.kids`; `none` when the
children do not fit. -/
def Head.rebuild : Head → List Head → Option Head
  | .val v, ks => match v, ks with
    | .pair sp _ _, [.val V, .val W] => some (.val (.pair sp V W))
    | .app sp _ _, [.val V, .val W] => some (.val (.app sp V W))
    | .inl sp _, [.val V] => some (.val (.inl sp V))
    | .inr sp _, [.val V] => some (.val (.inr sp V))
    | .unbang sp _, [.val V] => some (.val (.unbang sp V))
    | .boxed sp a _, [.val V] => some (.val (.boxed sp a V))
    | .unbox sp _, [.val V] => some (.val (.unbox sp V))
    | .sub sp _ a, [.val V] => some (.val (.sub sp V a))
    | .roll sp _, [.val V] => some (.val (.roll sp V))
    | .unroll sp _, [.val V] => some (.val (.unroll sp V))
    | .inst sp _ a, [.val V] => some (.val (.inst sp V a))
    | .ascribe sp _ A, [.val V] => some (.val (.ascribe sp V A))
    | .shorten sp m σ a _, [.val V] => some (.val (.shorten sp m σ a V))
    | .thunk sp _, [.comp M] => some (.val (.thunk sp M))
    | .thunkv sp _, [.comp M] => some (.val (.thunkv sp M))
    | .bangThunk sp _, [.comp M] => some (.val (.bangThunk sp M))
    | .bangThunkv sp _, [.comp M] => some (.val (.bangThunkv sp M))
    | .run sp _, [.comp M] => some (.val (.run sp M))
    | v@(.var ..), [] | v@(.defApp ..), [] | v@(.unit _), [] | v@(.const ..), []
    | v@(.lend ..), [] => some (.val v)
    | _, _ => none
  | .comp M, ks => match M, ks with
    | .ret sp _, [.val V] => some (.comp (.ret sp V))
    | .absurd sp _, [.val V] => some (.comp (.absurd sp V))
    | .bind sp x A _ _ lin, [.comp M, .comp N] => some (.comp (.bind sp x A M N lin))
    | .with_ sp _ _, [.comp M, .comp N] => some (.comp (.with_ sp M N))
    | .lam sp x A _, [.comp M] => some (.comp (.lam sp x A M))
    | .app sp _ x, [.comp M] => some (.comp (.app sp M x))
    | .proj sp i _, [.comp M] => some (.comp (.proj sp i M))
    | .lamL sp x b _, [.comp M] => some (.comp (.lamL sp x b M))
    | .inst sp _ a, [.comp M] => some (.comp (.inst sp M a))
    | .nuIn sp _, [.comp M] => some (.comp (.nuIn sp M))
    | .nuOut sp _, [.comp M] => some (.comp (.nuOut sp M))
    | .ascribe sp _ C, [.comp M] => some (.comp (.ascribe sp M C))
    | .letUnit sp _ _, [.val V, .comp M] => some (.comp (.letUnit sp V M))
    | .letPair sp x y _ _, [.val V, .comp M] => some (.comp (.letPair sp x y V M))
    | .case sp _ x _ y _, [.val V, .comp M, .comp N] => some (.comp (.case sp V x M y N))
    | .for_ sp x _ _ _, [.val V, .comp M, .comp N] => some (.comp (.for_ sp x V M N))
    | M@(.force ..), [] | M@(.top _), [] => some (.comp M)
    | _, _ => none

/-! ### Declarations -/

/-- A declaration of the typed IR: a `def` without type parameters or `main`, with its typed
body; anything else as written (types, shapes and externs have no body, and a `def` with type
parameters is checked only at its uses, SPEC syntax-core §10). -/
inductive TDecl where
  | def_ (sp : Span) (n : Ident) (A : VTy) (body : TNode) (mark : Mark)
  | main (sp : Span) (C : CTy) (body : TNode)
  | plain (d : Decl)

instance : Inhabited TDecl := ⟨.main Span.none (.top Span.none) default⟩

/-- The typed IR of a program. -/
structure TProgram where
  decls : List TDecl
  deriving Inhabited

/-! ### Measures -/

mutual
/-- The number of nodes, and of nodes whose type is not known. -/
def TNode.counts : TNode → Nat × Nat
  | .mk _ ty _ ks => let (a, b) := TNode.countsL ks; (a + 1, b + if ty.known then 0 else 1)

def TNode.countsL : List TNode → Nat × Nat
  | [] => (0, 0)
  | k :: ks => let (a, b) := k.counts; let (c, d) := TNode.countsL ks; (a + c, b + d)
end

mutual
/-- The spans of the nodes whose type is not known. -/
def TNode.untyped : TNode → List Span
  | .mk h ty _ ks => (if ty.known then [] else [h.span]) ++ TNode.untypedL ks

def TNode.untypedL : List TNode → List Span
  | [] => []
  | k :: ks => k.untyped ++ TNode.untypedL ks
end

mutual
/-- Every binder, in order. -/
def TNode.allBinders : TNode → List Binder
  | .mk _ _ bs ks => bs ++ TNode.allBindersL ks

def TNode.allBindersL : List TNode → List Binder
  | [] => []
  | k :: ks => k.allBinders ++ TNode.allBindersL ks
end

def TDecl.body? : TDecl → Option TNode
  | .def_ _ _ _ b _ | .main _ _ b => some b
  | .plain _ => none

end Frontend.Elab
