import Frontend.Elab.Infer
import Frontend.Parser
import Frontend.Print
import Frontend.Elab.Respan

/-!
# Frontend — Elab — typing contexts and metavariables  `[#54, docs/typed-elaboration.md §2]`

**Typing contexts.** `TCx` is the typing context at a point of a body, as the sugar sees it: the
checker's environment over the declarations in scope, the slot types, and the variables the body
has bound so far with their types. `TCx.tyV` types a value with inference (`Elab.inferV`), which
reads a `def`'s type as declared and never checks its body, so it works on programs whose sugar is
not yet elaborated. `loopOf` and `iterOf` read a loop or an iterator off a type.

**Metavariables.** An injection has no type of its own: `inl ()` is `1 + ?`. The checker needs its
type from context, so `x <- return (inl ()); …` did not check without `(inl () : B)`. `fillDecl`
infers the types of such bindings with metavariables for the unknown parts, solved by first-order
unification against the uses of the bound variable (an argument of a known function, a component
of a tuple that is, a `case` arm, the declared result). Unification covers value types only, and
metavariables do not outlive one declaration. A binding whose head is synthesized by the checker,
contains an injection in a synthesized position, and whose type is fully solved is given that
type as its annotation, `x : A <- …`; the checker then checks the head against it. Nothing else
is changed, so a program the checker already accepts is left as it is.
-/

namespace Frontend.Elab
open Frontend.Check
open BoCa BoCa.Lifetime

/-! ### Typing contexts -/

/-- The typing context at a point of a body. -/
structure TCx where
  E : Env
  T : List CVTy
  /-- The variables the body has bound so far, newest first, with their types when known. -/
  locals : List (String × Option CVTy) := []
  /-- The lifetime context: the `Fun` binders entered, as the checker numbers them. -/
  Δ : LifeCtx := LifeCtx.empty

/-- Bind `x : A` (`A` unknown when `none`). -/
def TCx.push (c : TCx) (x : String) (A : Option CVTy) : TCx :=
  { c with E := c.E.push (some x), T := A.getD .unit :: c.T, locals := (x, A) :: c.locals }

/-- Enter `Fun 'x < @b`, as the checker does: a dead slot, `'x` named, `Δ` extended. -/
def TCx.pushLife (c : TCx) (x : String) (b : BoCa.Lifetime.Life) : TCx :=
  let v := c.Δ.freshVar
  { c with E := { c.E.push none with lenv := (x, v) :: c.E.lenv }, T := .unit :: c.T,
           Δ := c.Δ.extend v b }

/-- A slot with no name: a dead binder of the checker (`thunk M`, `<M, N>`, `Fun`). -/
def TCx.pushDead (c : TCx) : TCx := { c with E := c.E.push none, T := .unit :: c.T }

/-- The context of a body among the declarations `scope`: every extern when `all`, else the
persistent ones (the context of a `def`, SPEC §11). -/
def TCx.ofScope (scope : List Decl) (all : Bool) : TCx :=
  let ds := scope.toArray
  let xs := externsBefore ds ds.size
  let vars := (xs.map (fun (x, B) => if all || B.persistent then some x else none)).reverse
  { E := Env.mk ⟨ds, ds.size⟩ vars [] [] [] xs.length none, T := (xs.map (·.2)).reverse }

/-- A written type, elaborated. -/
def TCx.elabV (c : TCx) (A : VTy) : Option CVTy := (c.E.elabV c.Δ A).toOption

/-- A written lifetime, elaborated. -/
def TCx.elabL (c : TCx) (a : Frontend.Life) : Option BoCa.Lifetime.Life := (c.E.elabL c.Δ a).toOption

/-- The type inference synthesizes for a value. -/
def TCx.tyV (c : TCx) (V : Val) : Option CVTy :=
  ((inferV inferFuel c.E c.Δ c.T none V).run' 0).ty.v?

/-- The type inference synthesizes for a computation. -/
def TCx.tyC (c : TCx) (M : Comp) : Option CCTy :=
  ((inferC inferFuel c.E c.Δ c.T none M).run' 0).ty.c?

/-! ### Loops and iterators -/

/-- `U (Loop_Σ B R) = U (νX. F_Σ(B ⊕ U X) & F_Σ R)` (`U (loop B R)` at the empty row, SPEC §19): its
row, `B` and `R`. -/
def loopRowOf (A : CVTy) : Option (CRow × CVTy × CVTy) :=
  match A with
  | .thunk (.nu (.amp C D)) => do
    let (S, O) ← effRow? C
    let (_, R) ← effRow? D
    match O with
    | .sum B (.tvar 0) =>
      if A = .thunk (BoCa.Fig16.LogRel.Core.CTy.loopEff S B R) then some (S, B, R) else none
    | _ => none
  | _ => none

/-- `U (Loop_Σ B R)`, at any row: its `B` and `R`. -/
def loopOf (A : CVTy) : Option (CVTy × CVTy) := (loopRowOf A).map (·.2)

/-- `U (iter A R R')`: its `A`, `R` and `R'`. -/
def iterOf (V : CVTy) : Option (CVTy × CVTy × CVTy) :=
  match V with
  | .thunk (.nu (.amp (.ret (.sum (.tensor A (.tvar 0)) R)) (.ret R'))) =>
    if V = .thunk (BoCa.Fig16.LogRel.Core.CTy.iter A R R') then some (A, R, R') else none
  | _ => none

/-- `U (pull A B R)`: its `A`, `B` and `R`. -/
def pullOf (V : CVTy) : Option (CVTy × CVTy × CVTy) :=
  match V with
  | .thunk (.nu (.amp (.ret (.sum (.tensor A (.tvar 0)) (.sum B (.tvar 0)))) (.ret R))) =>
    if V = .thunk (Frontend.Check.pullTy A B R) then some (A, B, R) else none
  | _ => none

/-- The element type of an iterator or a generator. -/
def elemOf (V : CVTy) : Option CVTy :=
  ((iterOf V).map (·.1)).orElse fun _ => (pullOf V).map (·.1)

/-- A function returning a loop, `A => U (loop B R)` or `!(A => U (loop B R))`: `B` and `R`. -/
def loopFnOf : CVTy → Option (CVTy × CVTy)
  | .thunk (.arr _ (.ret L)) | .bang (.thunk (.arr _ (.ret L))) => loopOf L
  | _ => none

/-- The components of a right-nested tuple type. -/
def spineT : CVTy → List CVTy
  | .tensor A B => A :: spineT B
  | A => [A]

/-- A right-nested tuple type of the components (`1` when there are none). -/
def tupleT : List CVTy → CVTy
  | [] => .unit
  | [A] => A
  | A :: As => .tensor A (tupleT As)

/-- A type in the surface syntax, parseable (`ppVTy`). -/
def ppT (A : CVTy) : String := ppVTy A

/-- A type as surface syntax. -/
def toSurface (sp : Span) (A : CVTy) : Except Error VTy := do
  match parseProgram s!"type IoT = {ppT A}\n" with
  | .ok ⟨[.type _ _ _ _ B]⟩ => pure B
  | _ => throw ⟨sp, s!"internal error: the type `{ppT A}` does not print as surface syntax"⟩

/-- A type as surface syntax in a context, its lifetimes by the names the context gives them. -/
def TCx.surface (c : TCx) (sp : Span) (A : CVTy) : Except Error VTy := do
  let src := ppV c.E.lenv 0 0 A
  match parseProgram s!"type IoT = {src}\n" with
  | .ok ⟨[.type _ _ _ _ B]⟩ => pure (B.respan sp)
  | _ => throw ⟨sp, s!"internal error: the type `{src}` does not print as surface syntax"⟩

/-- A lifetime as surface syntax in a context. -/
def TCx.surfaceL (c : TCx) (sp : Span) : BoCa.Lifetime.Life → Except Error Frontend.Life
  | .var v => match c.E.lenv.find? (·.2 == v) with
    | some (x, _) => pure (.var sp x)
    | none => throw ⟨sp, "internal error: a lifetime with no name"⟩
  | .top => pure (.top sp)
  | .meet a b => do pure (.meet sp (← c.surfaceL sp a) (← c.surfaceL sp b))
  | .join a b => do pure (.join sp (← c.surfaceL sp a) (← c.surfaceL sp b))

/-! ### Lent capabilities -/

mutual
/-- The `&c` of a value outside nested computations, replaced by `c`. -/
def _root_.Frontend.Val.takeLends : Val → Val × List Ident
  | .lend _ x _ => (.var x.span x.name, [x])
  | .pair sp V W =>
    let (V', a) := V.takeLends
    let (W', b) := W.takeLends
    (.pair sp V' W', a ++ b)
  | .app sp V W =>
    let (V', a) := V.takeLends
    let (W', b) := W.takeLends
    (.app sp V' W', a ++ b)
  | .inl sp V => let (V', a) := V.takeLends; (.inl sp V', a)
  | .inr sp V => let (V', a) := V.takeLends; (.inr sp V', a)
  | .unbang sp V => let (V', a) := V.takeLends; (.unbang sp V', a)
  | .boxed sp l V => let (V', a) := V.takeLends; (.boxed sp l V', a)
  | .unbox sp V => let (V', a) := V.takeLends; (.unbox sp V', a)
  | .sub sp V l => let (V', a) := V.takeLends; (.sub sp V' l, a)
  | .roll sp V => let (V', a) := V.takeLends; (.roll sp V', a)
  | .unroll sp V => let (V', a) := V.takeLends; (.unroll sp V', a)
  | .inst sp V l => let (V', a) := V.takeLends; (.inst sp V' l, a)
  | .ascribe sp V A => let (V', a) := V.takeLends; (.ascribe sp V' A, a)
  | .shorten sp m σ l V => let (V', a) := V.takeLends; (.shorten sp m σ l V', a)
  | .run sp M => let (M', a) := M.takeLends; (.run sp M', a)
  | V => (V, [])

/-- The `&c` of the head of a bind, outside nested binders. -/
def _root_.Frontend.Comp.takeLends : Comp → Comp × List Ident
  | .ret sp V => let (V', a) := V.takeLends; (.ret sp V', a)
  | .absurd sp V => let (V', a) := V.takeLends; (.absurd sp V', a)
  | .app sp M x => let (M', a) := M.takeLends; (.app sp M' x, a)
  | .proj sp i M => let (M', a) := M.takeLends; (.proj sp i M', a)
  | .inst sp M l => let (M', a) := M.takeLends; (.inst sp M' l, a)
  | .nuIn sp M => let (M', a) := M.takeLends; (.nuIn sp M', a)
  | .nuOut sp M => let (M', a) := M.takeLends; (.nuOut sp M', a)
  | .ascribe sp M C => let (M', a) := M.takeLends; (.ascribe sp M' C, a)
  | .letPair sp x y V M => let (V', a) := V.takeLends; (.letPair sp x y V' M, a)
  | .perform sp k i V => let (V', a) := V.takeLends; (.perform sp k i V', a)
  | .abort sp k i V => let (V', a) := V.takeLends; (.abort sp k i V', a)
  | M => (M, [])
end

/-! ### Metavariables -/

mutual
/-- An injection (`inl`, `inr`, `roll`) in a position whose type the checker synthesizes. -/
def _root_.Frontend.Val.synthInj : Val → Bool
  | .inl .. | .inr .. | .roll .. => true
  | .pair _ V W => V.synthInj || W.synthInj
  | .unbang _ V | .unbox _ V | .unroll _ V | .inst _ V _ | .sub _ V _ | .boxed _ _ V => V.synthInj
  | .run _ M => M.synthInj
  | _ => false

/-- An injection in a position of a computation whose type the checker synthesizes: the value
returned, and the first arm of a `case` (the second is checked against it). -/
def _root_.Frontend.Comp.synthInj : Comp → Bool
  | .ret _ V => V.synthInj
  | .bind _ _ _ _ N _ | .letUnit _ _ N | .letPair _ _ _ _ N => N.synthInj
  | .case _ _ _ M _ _ => M.synthInj
  | .absurd .. => true
  | _ => false
end

/-- A value type with metavariables. -/
inductive MTy where
  | known (A : CVTy)
  | mvar (n : Nat)
  | tensor (A B : MTy)
  | sum (A B : MTy)
  deriving Inhabited

structure MSt where
  next : Nat := 0
  sub : List (Nat × MTy) := []
  /-- The unannotated bindings that need their type: the binding's span and its type. -/
  binds : List (Span × MTy) := []

abbrev MM := StateM MSt

def freshM : MM MTy := modifyGet fun s => (.mvar s.next, { s with next := s.next + 1 })

/-- A metavariable's solution, followed. -/
def MTy.walk (sub : List (Nat × MTy)) : Nat → MTy → MTy
  | 0, t => t
  | n + 1, .mvar k => match sub.lookup k with
    | some t => MTy.walk sub n t
    | none => .mvar k
  | _, t => t

/-- The type, when every metavariable in it is solved. -/
def MTy.zonk (sub : List (Nat × MTy)) : Nat → MTy → Option CVTy
  | 0, _ => none
  | n + 1, t => match t.walk sub 64 with
    | .known A => some A
    | .mvar _ => none
    | .tensor A B => do pure (.tensor (← A.zonk sub n) (← B.zonk sub n))
    | .sum A B => do pure (.sum (← A.zonk sub n) (← B.zonk sub n))

def zonkM (t : MTy) : MM (Option CVTy) := do pure (t.zonk (← get).sub 256)

/-- First-order unification. A clash is not an error here: the checker reports it. -/
def unify : Nat → MTy → MTy → MM Unit
  | 0, _, _ => pure ()
  | n + 1, a, b => do
    let s ← get
    match a.walk s.sub 64, b.walk s.sub 64 with
    | .mvar i, .mvar j => if i == j then pure () else set { s with sub := (i, .mvar j) :: s.sub }
    | .mvar i, t | t, .mvar i => set { s with sub := (i, t) :: s.sub }
    | .known (.tensor A B), .tensor x y | .tensor x y, .known (.tensor A B) => do
      unify n (.known A) x; unify n (.known B) y
    | .known (.sum A B), .sum x y | .sum x y, .known (.sum A B) => do
      unify n (.known A) x; unify n (.known B) y
    | .tensor a₁ a₂, .tensor b₁ b₂ | .sum a₁ a₂, .sum b₁ b₂ => do
      unify n a₁ b₁; unify n a₂ b₂
    | _, _ => pure ()

def unifyM (a b : MTy) : MM Unit := unify 256 a b

def ofOpt : Option CVTy → MM MTy
  | some A => pure (.known A)
  | none => freshM

/-- The typing context of the metavariable pass: the typing context, and each local's type with
metavariables. -/
structure MCx where
  tc : TCx
  env : List (String × MTy)

def MCx.push (c : MCx) (x : String) (t : MTy) : MM MCx := do
  pure ⟨c.tc.push x (← zonkM t), (x, t) :: c.env⟩

/-- The result a call in direct style binds: `B` for a call returning `U (loop B R)` (SPEC §14). -/
def direct (B : CVTy) : CVTy := match loopOf B with
  | some (B', _) => B'
  | none => B

mutual
/-- Synthesize a value's type. -/
def synM : Nat → MCx → Val → MM MTy
  | 0, _, _ => freshM
  | n + 1, c, v => match v with
    | .var _ x | .lend _ ⟨x, _⟩ _ => match c.env.lookup x with
      | some t => pure t
      | none => ofOpt (c.tc.tyV (.var Span.none x))
    | .unit _ => pure (.known .unit)
    | .pair _ V W => do pure (.tensor (← synM n c V) (← synM n c W))
    | .inl _ V => do pure (.sum (← synM n c V) (← freshM))
    | .inr _ V => do pure (.sum (← freshM) (← synM n c V))
    | .ascribe _ V A => match c.tc.elabV A with
      | some A' => do chkM n c V (.known A'); pure (.known A')
      | none => synM n c V
    | .app _ f W => do
      let tf ← synM n c f
      match tf.walk (← get).sub 64 with
      | .known (.thunk (.arr A (.ret B))) => do chkM n c W (.known A); pure (.known (direct B))
      | _ => do let _ ← synM n c W; freshM
    | .unbang _ V => do
      let t ← synM n c V
      match t.walk (← get).sub 64 with
      | .known (.bang A) => pure (.known A)
      | _ => freshM
    | v => ofOpt (c.tc.tyV v)

/-- Check a value against a type. -/
def chkM : Nat → MCx → Val → MTy → MM Unit
  | 0, _, _, _ => pure ()
  | n + 1, c, v, t => do unifyM (← synM n c v) t

/-- Synthesize the value type a computation returns (its `F A`). -/
def synCM : Nat → MCx → Comp → MM MTy
  | 0, _, _ => freshM
  | n + 1, c, m => match m with
    | .ret _ V => synM n c V
    | .bind sp x oA M N _ => do
      let t ← match oA.bind c.tc.elabV with
        | some A => do chkCM n c M (.known A); pure (.known A)
        | none => do
          let s ← synCM n c M
          if M.takeLends.2.isEmpty then pure s else do
            let a ← freshM
            let b ← freshM
            unifyM s (.tensor a b)
            pure b
      if oA.isNone && M.synthInj then modify fun st => { st with binds := (sp, t) :: st.binds }
      synCM n (← c.push x.name t) N
    | .letUnit _ V M => do chkM n c V (.known .unit); synCM n c M
    | .letPair _ x y V M => do
      let t ← synM n c V
      let a ← freshM
      let b ← freshM
      unifyM t (.tensor a b)
      synCM n (← (← c.push x.name a).push y.name b) M
    | .case _ V x M y N => do
      let t ← synM n c V
      let a ← freshM
      let b ← freshM
      unifyM t (.sum a b)
      let r₁ ← synCM n (← c.push x.name a) M
      let r₂ ← synCM n (← c.push y.name b) N
      unifyM r₁ r₂
      pure r₁
    | .for_ _ x V M N => do
      let el := (c.tc.tyV V).bind elemOf
      let _ ← synCM n (← c.push x.name (← ofOpt el)) M
      synCM n c N
    | m => match (c.tc.tyC m).bind effRow? with
      | some (_, A) => pure (.known A)
      | _ => freshM

/-- Check the value type a computation returns. -/
def chkCM : Nat → MCx → Comp → MTy → MM Unit
  | 0, _, _, _ => pure ()
  | n + 1, c, m, t => do unifyM (← synCM n c m) t
end

/-- Annotate the unannotated bindings at the spans `ann` with their types. -/
def _root_.Frontend.Comp.annotate (ann : List (Span × VTy)) : Comp → Comp
  | .bind sp x none M N lin =>
    .bind sp x (ann.lookup sp) (M.annotate ann) (N.annotate ann) lin
  | .bind sp x A M N lin => .bind sp x A (M.annotate ann) (N.annotate ann) lin
  | .letUnit sp V M => .letUnit sp V (M.annotate ann)
  | .letPair sp x y V M => .letPair sp x y V (M.annotate ann)
  | .case sp V x M y N => .case sp V x (M.annotate ann) y (N.annotate ann)
  | .for_ sp x V M N => .for_ sp x V (M.annotate ann) (N.annotate ann)
  | .handle sp k hr hc M => .handle sp k hr hc (M.annotate ann)
  | .unwind sp x A M D N => .unwind sp x A (M.annotate ann) (D.annotate ann) (N.annotate ann)
  | M => M

/-- An unannotated binding whose head has an injection in a synthesized position. -/
def _root_.Frontend.Comp.needsFill : Comp → Bool
  | .bind _ _ A M N _ => (A.isNone && M.synthInj) || M.needsFill || N.needsFill
  | .letUnit _ _ M | .letPair _ _ _ _ M => M.needsFill
  | .case _ _ _ M _ N | .for_ _ _ _ M N => M.needsFill || N.needsFill
  | .handle _ _ _ _ M => M.needsFill
  | .unwind _ _ _ M D N => M.needsFill || D.needsFill || N.needsFill
  | _ => false

/-- The bindings of a body that need their type, with the type metavariables solve for them. -/
def fillBody (c : TCx) (B : Option CVTy) (M : Comp) : List (Span × VTy) :=
  if !M.needsFill then [] else
  let go : MM (List (Span × Option CVTy)) := do
    let t ← synCM inferFuel ⟨c, []⟩ M
    if let some B := B then unifyM t (.known B)
    let st ← get
    pure (st.binds.map fun (sp, t) => (sp, t.zonk st.sub 256))
  (go.run' {}).filterMap fun (sp, A) => do
    let A ← A
    (toSurface sp A).toOption.map (sp, ·)

/-- A declaration with the bindings metavariables determine annotated, in the declarations
before it (`scope`, the libraries first). `main` sees every extern and the capabilities `caps`
may make ambient (SPEC §11). -/
def fillDecl (scope : List Decl) (caps : List Decl) : Decl → Decl
  | d@(.def_ _ _ [] _ (.thunkv _ (.lam _ _ _ M)) _) | d@(.def_ _ _ [] _ (.bangThunkv _ (.lam _ _ _ M)) _)
  | d@(.main _ _ M) => if M.needsFill then fillDecl' scope caps d else d
  | d => d
where
  fillDecl' (scope : List Decl) (caps : List Decl) : Decl → Decl
  | .def_ sp n [] A (.thunkv vsp (.lam lsp x Ax M)) mk =>
    let c := TCx.ofScope scope false
    match c.elabV A, c.elabV Ax with
    | some (.thunk (.arr _ (.ret B))), some Ax' =>
      let ann := fillBody (c.push x.name Ax') (some (direct B)) M
      .def_ sp n [] A (.thunkv vsp (.lam lsp x Ax (M.annotate ann))) mk
    | _, _ => .def_ sp n [] A (.thunkv vsp (.lam lsp x Ax M)) mk
  | .def_ sp n [] A (.bangThunkv vsp (.lam lsp x Ax M)) mk =>
    let c := TCx.ofScope scope false
    match c.elabV A, c.elabV Ax with
    | some (.bang (.thunk (.arr _ (.ret B)))), some Ax' =>
      let ann := fillBody (c.push x.name Ax') (some (direct B)) M
      .def_ sp n [] A (.bangThunkv vsp (.lam lsp x Ax (M.annotate ann))) mk
    | _, _ => .def_ sp n [] A (.bangThunkv vsp (.lam lsp x Ax M)) mk
  | .main sp C M =>
    let c := TCx.ofScope (scope ++ caps) true
    let B := match (c.E.elabC LifeCtx.empty C).toOption with
      | some (.ret B) => some (direct B)
      | _ => none
    .main sp C (M.annotate (fillBody c B M))
  | d => d

/-- A program with the bindings metavariables determine annotated. `lib` is in scope before it. -/
def fillProgram (lib caps : List Decl) (p : Program) : Program :=
  ⟨(List.range p.decls.length).map fun k =>
    fillDecl (lib ++ p.decls.take k) caps (p.decls.getD k (.main Span.none (.top Span.none)
      (.top Span.none)))⟩

end Frontend.Elab
