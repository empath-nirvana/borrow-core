import Frontend.Parser
import Frontend.Print
import Frontend.Check.Steps
import Frontend.Elab.Respan
import Frontend.Elab.Meta

/-!
# Frontend — the sugar  `[spec §11, §14]`

The forms below are elaborated here into ordinary core syntax before checking. The checker, the
kernel and the theorems never see them: what they check is a program a user could have written
by hand (`bcc desugar` prints it). Divergence (§14) is elaborated here too: see the section
*Divergence* below. The elaboration uses types (docs/typed-elaboration.md): inference types the
program as written (`Frontend.Elab.TCx`), bindings whose type only their uses determine are
annotated first (`Frontend.Elab.fillProgram`), and each decision below reads those types.

* **Ambient capabilities in `main`.** A program that declares no externs and whose `main`
  mentions `stdin`, `stdout` or `stderr` gets the I/O library (`lib/io.bc`), which declares the
  operations, and an `extern` for each capability it mentions, in the order `stdin`, `stdout`,
  `stderr`. `main : F A` becomes `main : F (Caps * A)`: each terminal `return V` of its body
  becomes `return (caps, V)`, and any other terminal `T` becomes `r <- T; return (caps, r)`,
  with the capabilities read by name where the path ends (`wrapTail`).
* **`for x in V { M }; N`**, `V` an iterator made from a capability, in any function or `main`
  becomes a loop by `unfold` over the state (iterator, other capabilities, threaded variables at
  their inferred types), and makes the function div (`forLoop`, §14).
* **`&c`** in the head of `x <- M; N` becomes `r <- M[c/&c]; let (c, x) = r; N` (`Comp.elab`).

The generated code is a template, printed and parsed, whose holes are filled with the program's
own syntax, so errors inside the program's code keep its positions. The template's own nodes are
given the span of the sugar that produced them (`respan`), and the elaboration records that span
with the sugar's name in its **origins**, so that an error the checker finds in generated code is
reported at the sugar, with a note naming it (`Frontend.Elab.renderError`).
-/

namespace Frontend.Sugar
open Frontend.Check (mentionsV mentionsC)

/-- The I/O library, `lib/io.bc`. -/
def ioLibrary : String := include_str "../lib/io.bc"

/-- The divergence library, `lib/div.bc`: the delay bind and the fuel handler. -/
def divLibrary : String := include_str "../lib/div.bc"

def capNames : List String := ["stdin", "stdout", "stderr"]

def capTy (sp : Span) (c : String) : VTy := .ref sp (.handle sp (c != "stdin"))

/-! ### Lending a capability to one call -/

mutual
/-- Elaborate `&c` in a value; with `lend`, a `&c` outside nested computations becomes `c`. -/
def _root_.Frontend.Val.elab (lend : Bool) : Val → Except Error Val
  | .lend sp x =>
    if lend then pure (.var x.span x.name) else
    throw ⟨sp, s!"`&{x.name}` lends a capability to one call: it may appear only " ++
      "in the head `M` of `y <- M; N` (SPEC §11)"⟩
  | .pair sp V W => return .pair sp (← V.elab lend) (← W.elab lend)
  | .app sp V W => return .app sp (← V.elab lend) (← W.elab lend)
  | .inl sp V => return .inl sp (← V.elab lend)
  | .inr sp V => return .inr sp (← V.elab lend)
  | .unbang sp V => return .unbang sp (← V.elab lend)
  | .boxed sp l V => return .boxed sp l (← V.elab lend)
  | .unbox sp V => return .unbox sp (← V.elab lend)
  | .sub sp V l => return .sub sp (← V.elab lend) l
  | .roll sp V => return .roll sp (← V.elab lend)
  | .unroll sp V => return .unroll sp (← V.elab lend)
  | .inst sp V l => return .inst sp (← V.elab lend) l
  | .ascribe sp V A => return .ascribe sp (← V.elab lend) A
  | .shorten sp m σ l V => return .shorten sp m σ l (← V.elab lend)
  | .thunk sp M => return .thunk sp (← M.elab false)
  | .thunkv sp M => return .thunkv sp (← M.elab false)
  | .bangThunk sp M => return .bangThunk sp (← M.elab false)
  | .bangThunkv sp M => return .bangThunkv sp (← M.elab false)
  | .run sp M => return .run sp (← M.elab false)
  | V@(.var ..) | V@(.defApp ..) | V@(.unit ..) | V@(.const ..) => pure V

/-- Elaborate `&c` in a computation: in `x <- M; N`, one `&c` in `M` becomes
`io_lend <- M[c/&c]; let (c, x) = io_lend; N`. With `lend`, the computation is such a head, and
its `&c` outside nested binders becomes `c`. -/
def _root_.Frontend.Comp.elab (lend : Bool) : Comp → Except Error Comp
  | .bind sp x A M N lin => do
    match M.takeLends.2 with
    | [] => return .bind sp x A (← M.elab false) (← N.elab false) lin
    | [c] =>
      if A.isSome || lin then
        throw ⟨sp, s!"`&{c.name}` cannot be used in an annotated or `linear` binding"⟩
      let r : Ident := ⟨"io_lend", c.span⟩
      return .bind sp r none (← M.elab true) (.letPair sp c x (.var c.span r.name) (← N.elab false))
        false
    | _ => throw ⟨sp, "a call lends at most one capability with `&`"⟩
  | .ret sp V => return .ret sp (← V.elab lend)
  | .absurd sp V => return .absurd sp (← V.elab lend)
  | .force sp x => pure (.force sp x)
  | .lam sp x A M => return .lam sp x A (← M.elab false)
  | .app sp M x => return .app sp (← M.elab lend) x
  | .with_ sp M N => return .with_ sp (← M.elab false) (← N.elab false)
  | .proj sp i M => return .proj sp i (← M.elab lend)
  | .top sp => pure (.top sp)
  | .letUnit sp V M => return .letUnit sp (← V.elab false) (← M.elab false)
  | .letPair sp x y V M => return .letPair sp x y (← V.elab false) (← M.elab false)
  | .case sp V x M y N => return .case sp (← V.elab false) x (← M.elab false) y (← N.elab false)
  | .lamL sp x b M => return .lamL sp x b (← M.elab false)
  | .inst sp M a => return .inst sp (← M.elab lend) a
  | .nuIn sp M => return .nuIn sp (← M.elab lend)
  | .nuOut sp M => return .nuOut sp (← M.elab lend)
  | .ascribe sp M C => return .ascribe sp (← M.elab lend) C
  | .for_ sp _ _ _ _ => throw ⟨sp, "`for` may appear only on the spine of a function's body " ++
      "or of `main`: not inside a value, the head of `x <- M; N`, or the body of another `for` " ++
      "(SPEC §14)"⟩
end

/-! ### Filling a template's holes -/

mutual
def _root_.Frontend.Val.fill (hv : String → Option Val) (hc : String → Option Comp) : Val → Val
  | V@(.var _ x) => (hv x).getD V
  | .pair sp V W => .pair sp (V.fill hv hc) (W.fill hv hc)
  | .app sp V W => .app sp (V.fill hv hc) (W.fill hv hc)
  | .inl sp V => .inl sp (V.fill hv hc)
  | .inr sp V => .inr sp (V.fill hv hc)
  | .unbang sp V => .unbang sp (V.fill hv hc)
  | .boxed sp l V => .boxed sp l (V.fill hv hc)
  | .unbox sp V => .unbox sp (V.fill hv hc)
  | .sub sp V l => .sub sp (V.fill hv hc) l
  | .roll sp V => .roll sp (V.fill hv hc)
  | .unroll sp V => .unroll sp (V.fill hv hc)
  | .inst sp V l => .inst sp (V.fill hv hc) l
  | .ascribe sp V A => .ascribe sp (V.fill hv hc) A
  | .shorten sp m σ l V => .shorten sp m σ l (V.fill hv hc)
  | .thunk sp M => .thunk sp (M.fill hv hc)
  | .thunkv sp M => .thunkv sp (M.fill hv hc)
  | .bangThunk sp M => .bangThunk sp (M.fill hv hc)
  | .bangThunkv sp M => .bangThunkv sp (M.fill hv hc)
  | .run sp M => .run sp (M.fill hv hc)
  | V => V

def _root_.Frontend.Comp.fill (hv : String → Option Val) (hc : String → Option Comp) : Comp → Comp
  | M@(.force _ x) => (hc x.name).getD M
  | .ret sp V => .ret sp (V.fill hv hc)
  | .absurd sp V => .absurd sp (V.fill hv hc)
  | .bind sp x A M N lin => .bind sp x A (M.fill hv hc) (N.fill hv hc) lin
  | .lam sp x A M => .lam sp x A (M.fill hv hc)
  | .app sp M x => .app sp (M.fill hv hc) x
  | .with_ sp M N => .with_ sp (M.fill hv hc) (N.fill hv hc)
  | .proj sp i M => .proj sp i (M.fill hv hc)
  | .letUnit sp V M => .letUnit sp (V.fill hv hc) (M.fill hv hc)
  | .letPair sp x y V M => .letPair sp x y (V.fill hv hc) (M.fill hv hc)
  | .case sp V x M y N => .case sp (V.fill hv hc) x (M.fill hv hc) y (N.fill hv hc)
  | .lamL sp x b M => .lamL sp x b (M.fill hv hc)
  | .inst sp M a => .inst sp (M.fill hv hc) a
  | .nuIn sp M => .nuIn sp (M.fill hv hc)
  | .nuOut sp M => .nuOut sp (M.fill hv hc)
  | .ascribe sp M C => .ascribe sp (M.fill hv hc) C
  | M => M
end

/-! ### Ambient capabilities in `main` -/

/-- Apply `f` to every terminal computation reached through tail positions: the body of a bind
or a `let`, both arms of a `case`, and what follows a `for`. -/
def wrapTail (f : Comp → Comp) : Comp → Comp
  | .bind sp x A M N lin => .bind sp x A M (wrapTail f N) lin
  | .letUnit sp V M => .letUnit sp V (wrapTail f M)
  | .letPair sp x y V M => .letPair sp x y V (wrapTail f M)
  | .case sp V x M y N => .case sp V x (wrapTail f M) y (wrapTail f N)
  | .for_ sp x V M N => .for_ sp x V M (wrapTail f N)
  | T => f T

/-- A right-nested tuple of variables (`()` when empty). -/
def tupleVal (sp : Span) : List String → Val
  | [] => .unit sp
  | [x] => .var sp x
  | x :: xs => .pair sp (.var sp x) (tupleVal sp xs)

def tupleSrc : List String → String
  | [] => "()"
  | [x] => x
  | x :: xs => s!"({x}, {tupleSrc xs})"

def tupleTySrc : List String → String
  | [] => "1"
  | [A] => s!"({A})"
  | A :: As => s!"(({A}) * {tupleTySrc As})"

def tupleTy (sp : Span) : List VTy → VTy
  | [] => .unit sp
  | [A] => A
  | A :: As => .tensor sp A (tupleTy sp As)

/-- Bind the names of a right-nested tuple held in `v`. -/
def destructSrc (v : String) : List String → String
  | [] => s!"let () = {v};\n"
  | [x] => s!"{x} <- return {v};\n"
  | [x, y] => s!"let ({x}, {y}) = {v};\n"
  | x :: xs => s!"let ({x}, {v}_t) = {v};\n" ++ destructSrc s!"{v}_t" xs

/-- Parse the computation `src` as a `main` body. -/
def parseComp (src : String) : Except Error Comp := do
  let p ← parseProgram ("main : F 1 =\n" ++ src)
  match p.decls.findSome? (fun | .main _ _ M => some M | _ => none) with
  | some M => pure M
  | none => throw ⟨Span.none, "internal error: a template without main"⟩

/-! ### Divergence  `[spec §14]`

A function whose result type is a loop, `A => U (loop B R)`, is a **div function**: a call runs
its code up to its first loop and returns the rest of the run as a loop, which finishes with `B`
or, closed early, hands back the residual `R`. A function is div when its type says so, or when
its body loops: it has a `for`, or it runs a call of a div function in direct style, on its spine
(the tail positions of binds, `let`s, `case` arms and `for`s). Definitions are in dependency
order, so one pass infers this. A div function written with a plain result `A => B` is
elaborated to `A => U (loop B R)`, and so is `main`; `total def` asserts that the body does not
loop.

Everything here is decided by types (`Frontend.Elab.TCx`, docs/typed-elaboration.md §2.4):

* **A call run in direct style** is an application whose type is a loop, where the type expected
  of it is not that loop. It may stand at any depth of a bound or returned value, a scrutinee or
  a `let`'s value: the value's applications are then lifted out, innermost and leftmost first,
  into bindings (`liftApps`), and each call becomes the delay bind of `lib/div.bc`, `div_bind`,
  with the rest of the body as its continuation. Checked against its own loop type (an argument
  of `div_fuel`, an annotated binding) the call is the loop as a value.
* **A `for`** becomes a loop by `unfold` whose state is the iterator, the other capabilities, and
  the variables the body reads, at their inferred types; then the same bind.
* **A terminal** `return V` becomes the loop that finishes with `V` at its first observation.
* **The residual** `R` is `K * 1`, where `K` is the components of the result type `B` that have
  no destructor (SPEC §12), or `1` when there are none: a loop closed early hands back what it
  cannot drop. The variables that hold `K` are the ones a terminal `return` puts there.
-/

open Frontend.Elab (TCx loopOf iterOf loopFnOf spineT tupleT ppT toSurface Class)
open Frontend.Check (CVTy)

/-- A function returning a loop, as written: `A => U (loop B R)` or `!(A => U (loop B R))` (a
`delay B` is `loop B 1`): its `B` and `R`. Specialization reads it off a parameter's type. -/
def loopSig : VTy → Option (VTy × VTy)
  | .lolli _ _ (.thunk _ (.loop _ B R)) | .bang _ (.lolli _ _ (.thunk _ (.loop _ B R))) =>
    some (B, R)
  | .lolli _ _ (.thunk sp (.delay _ B)) | .bang _ (.lolli _ _ (.thunk sp (.delay _ B))) =>
    some (B, .unit sp)
  | _ => none

/-- `F (U (loop B R))` (or `F (U (delay B))`): a computation type that returns a loop, written
out; such a body is core, not elaborated. -/
def _root_.Frontend.CTy.returnsLoop : CTy → Bool
  | .ret _ (.thunk _ (.loop ..)) | .ret _ (.thunk _ (.delay ..)) => true
  | _ => false

/-- The depth bound for the traversals below. -/
def divFuel : Nat := 1 <<< 16

/-! #### Calls run in direct style -/

/-- The function a call applies, by name, for messages. -/
def calleeName : Val → Option String
  | .app _ (.var _ f) _ | .app _ (.unbang _ (.var _ f)) _ => some f
  | _ => none

/-- A call run in direct style: an application whose type is a loop, where the type expected of
it, when known, is not that loop. Its `B` and `R`. -/
def directCall (c : TCx) (exp : Option CVTy) : Val → Option (CVTy × CVTy)
  | V@(.app ..) => do
    let A ← c.tyV V
    if exp = some A then none else loopOf A
  | _ => none

/-- The subvalues of a value outside nested computations, each with the type expected of it. -/
def children (c : TCx) (exp : Option CVTy) : Val → List (Option CVTy × Val)
  | .app _ f W =>
    [(none, f), (match c.tyV f with | some (.thunk (.arr A _)) => some A | _ => none, W)]
  | .pair _ V W => match exp with
    | some (.tensor A B) => [(some A, V), (some B, W)]
    | _ => [(none, V), (none, W)]
  | .inl _ V => [(match exp with | some (.sum A _) => some A | _ => none, V)]
  | .inr _ V => [(match exp with | some (.sum _ B) => some B | _ => none, V)]
  | .ascribe _ V A => [(c.elabV A, V)]
  | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V | .unroll _ V
  | .inst _ V _ | .shorten _ _ _ _ V => [(none, V)]
  | _ => []

/-- A call run in direct style in a value, at any depth outside nested computations: its span
and callee. -/
def callIn (c : TCx) : Nat → Option CVTy → Val → Option (Span × Option String)
  | 0, _, _ => none
  | n + 1, exp, V => match directCall c exp V with
    | some _ => some (V.span, calleeName V)
    | none => (children c exp V).findSome? fun (e, W) => callIn c n e W

/-- A call run in direct style strictly below the top of a value. -/
def nestedCall (c : TCx) (exp : Option CVTy) (V : Val) : Option (Span × Option String) :=
  (children c exp V).findSome? fun (e, W) => callIn c divFuel e W

/-- The applications of a value outside nested computations, lifted out innermost and leftmost
first, the order its evaluation runs them in: each becomes a binding `io_nK <- return (f W)`,
and the value refers to its variable. -/
def liftApps : Nat → Val → StateM (List (Ident × Val)) Val
  | 0, V => pure V
  | n + 1, V => match V with
    | .app sp f W => do
      let f' ← liftApps n f
      let W' ← liftApps n W
      let x : Ident := ⟨s!"io_n{(← get).length}", sp⟩
      modify (· ++ [(x, .app sp f' W')])
      pure (.var sp x.name)
    | .pair sp V W => do pure (.pair sp (← liftApps n V) (← liftApps n W))
    | .inl sp V => do pure (.inl sp (← liftApps n V))
    | .inr sp V => do pure (.inr sp (← liftApps n V))
    | .ascribe sp V A => do pure (.ascribe sp (← liftApps n V) A)
    | .unbang sp V => do pure (.unbang sp (← liftApps n V))
    | .boxed sp l V => do pure (.boxed sp l (← liftApps n V))
    | .unbox sp V => do pure (.unbox sp (← liftApps n V))
    | .sub sp V l => do pure (.sub sp (← liftApps n V) l)
    | .roll sp V => do pure (.roll sp (← liftApps n V))
    | .unroll sp V => do pure (.unroll sp (← liftApps n V))
    | .inst sp V l => do pure (.inst sp (← liftApps n V) l)
    | .shorten sp m σ l V => do pure (.shorten sp m σ l (← liftApps n V))
    | V => pure V

/-- The applications below the top of a value, lifted (`liftApps`). -/
def liftBelow (V : Val) : Val × List (Ident × Val) :=
  let go : StateM (List (Ident × Val)) Val := match V with
    | .app sp f W => do pure (.app sp (← liftApps divFuel f) (← liftApps divFuel W))
    | V => liftApps divFuel V
  go.run []

/-- Every application of a value, lifted (`liftApps`). -/
def liftAll (V : Val) : Val × List (Ident × Val) := (liftApps divFuel V).run []

/-- The lifted applications bound before `M`. -/
def chain (bs : List (Ident × Val)) (M : Comp) : Comp :=
  bs.foldr (fun (x, V) N => .bind V.span x none (.ret V.span V) N false) M

/-! #### Types of bound variables -/

/-- The type `x <- M` gives `x`: the annotation; else the result of a call run in direct style,
the value's type, or the computation's result; with `&c` in `M`, the second component, since the
call hands the capability back first (SPEC §11). -/
def bindTy (c : TCx) (A : Option VTy) (M : Comp) : Option CVTy :=
  match A with
  | some A => c.elabV A
  | none =>
    let t := match M with
      | .ret _ V => match directCall c none V with
        | some (B, _) => some B
        | none => c.tyV V
      | M => match c.tyC M with
        | some (.ret A) => some A
        | _ => none
    if M.takeLends.2.isEmpty then t else match t with
      | some (.tensor _ B) => some B
      | _ => none

/-- The types `let (x, y) = V` gives its names. -/
def pairTys (c : TCx) (V : Val) : Option CVTy × Option CVTy :=
  match c.tyV V with
  | some (.tensor A B) => (some A, some B)
  | _ => (none, none)

/-- The types `case V { inl x -> … | inr y -> … }` gives its names. -/
def sumTys (c : TCx) (V : Val) : Option CVTy × Option CVTy :=
  match c.tyV V with
  | some (.sum A B) => (some A, some B)
  | _ => (none, none)

/-- A call found in a value, described. -/
def callMsg (sp : Span) : Option String → Span × String
  | some f => (sp, s!"it calls the div function `{f}`")
  | none => (sp, "it calls a div function")

/-- A call run in direct style in a bound or returned value: at its top (reported at the
computation) or below it. -/
def headLoops (c : TCx) (exp : Option CVTy) : Comp → Option (Span × String)
  | M@(.ret _ V) => match directCall c exp V with
    | some _ => some (callMsg M.span (calleeName V))
    | none => (nestedCall c exp V).map fun (sp, f) => callMsg sp f
  | _ => none

/-- Where a body loops, on its spine: a `for`, or a call run in direct style. `B` is the body's
result type. -/
def loopsAt (c : TCx) (B : Option CVTy) : Comp → Option (Span × String)
  | .bind _ x A M N _ =>
    (headLoops c (A.bind c.elabV) M).orElse fun _ => loopsAt (c.push x.name (bindTy c A M)) B N
  | .letUnit _ V M =>
    ((callIn c divFuel (some .unit) V).map fun (sp, f) => callMsg sp f).orElse fun _ =>
      loopsAt c B M
  | .letPair _ x y V M =>
    let (Ax, Ay) := pairTys c V
    ((callIn c divFuel none V).map fun (sp, f) => callMsg sp f).orElse fun _ =>
      loopsAt ((c.push x.name Ax).push y.name Ay) B M
  | .case _ V x M y N =>
    let (Ax, Ay) := sumTys c V
    ((callIn c divFuel none V).map fun (sp, f) => callMsg sp f).orElse fun _ =>
      (loopsAt (c.push x.name Ax) B M).orElse fun _ => loopsAt (c.push y.name Ay) B N
  | .for_ sp .. => some (sp, "it has a `for`")
  | T => headLoops c B T

mutual
/-- `n` occurs in a value, as a variable or a `def` applied to type arguments. -/
def _root_.Frontend.Val.names (n : String) : Val → Bool
  | .var _ x | .defApp _ x _ => x == n
  | .pair _ V W | .app _ V W => V.names n || W.names n
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => V.names n
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => M.names n
  | _ => false

/-- `n` occurs in a computation. -/
def _root_.Frontend.Comp.names (n : String) : Comp → Bool
  | .ret _ V | .absurd _ V => V.names n
  | .bind _ _ _ M N _ | .with_ _ M N => M.names n || N.names n
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ => M.names n
  | .letUnit _ V M | .letPair _ _ _ V M => V.names n || M.names n
  | .case _ V _ M _ N => V.names n || M.names n || N.names n
  | .for_ _ _ V M N => V.names n || M.names n || N.names n
  | .force .. | .top _ => false
end

/-! #### The residual -/

/-- A right-nested tuple of values against a right-nested tuple type's components: the value at
each component, where the value's tuple reaches it (its last component may cover the rest). -/
def alignV : List CVTy → Val → List (Option Val)
  | [], _ => []
  | [_], v => [some v]
  | _ :: ts, .pair _ v w => some v :: alignV ts w
  | ts, _ => ts.map fun _ => none

/-- The variables a value names a component of type `A` with: the variable itself, or one per
component of a tuple. -/
def varsFor (A : CVTy) : Val → Option (List (String × CVTy))
  | .var _ x => some [(x, A)]
  | V => ((alignV (spineT A) V).zip (spineT A)).mapM fun
    | (some (.var _ x), T) => some (x, T)
    | _ => none

def isLinear (A : CVTy) : Bool := Class.of A == .linear

/-- The variables a terminal `return V` of the body puts in each component of the result that
has no destructor. -/
def termParts (parts : List CVTy) : Comp → Option (List (List (String × CVTy)))
  | .bind _ _ _ _ N _ | .letUnit _ _ N | .letPair _ _ _ _ N | .for_ _ _ _ _ N => termParts parts N
  | .case _ _ _ M _ N => (termParts parts M).orElse fun _ => termParts parts N
  | .ret _ V => ((parts.zip (alignV parts V)).filter (isLinear ·.1)).mapM fun (A, v) =>
      v.bind (varsFor A)
  | _ => none

/-- What a div body is elaborated at: its result `B`, its residual `R = K * 1` (or `1`), `K`, and
the variables holding each component of `K`. -/
structure LoopCx where
  B : CVTy
  R : CVTy
  K : CVTy
  parts : List (List (String × CVTy))

def LoopCx.caps (cx : LoopCx) : List (String × CVTy) := cx.parts.flatten

def LoopCx.capNames (cx : LoopCx) : List String := cx.caps.map (·.1)

def LoopCx.kSrc (cx : LoopCx) : String := tupleSrc (cx.parts.map fun p => tupleSrc (p.map (·.1)))

/-- The residual built from the capabilities in scope. -/
def LoopCx.rSrc (cx : LoopCx) : String :=
  if cx.parts.isEmpty then "()" else s!"({cx.kSrc}, ())"

/-- Bind the variables of each component of `K`, held in `v`. -/
def destructParts (v : String) (parts : List (List (String × CVTy))) : String :=
  match parts with
  | [p] => destructSrc v (p.map (·.1))
  | ps =>
    let ns := (List.range ps.length).map (s!"{v}_p{·}")
    destructSrc v ns ++ String.join ((ns.zip ps).map fun (n, p) => destructSrc n (p.map (·.1)))

/-- The context a div function with result `B` and body `M` is elaborated at.  `[spec §14]` -/
def loopCxOf (sp : Span) (B : CVTy) (M : Comp) : Except Error LoopCx := do
  let parts := spineT B
  let lin := parts.filter isLinear
  if lin.isEmpty then return ⟨B, .unit, .unit, []⟩
  let K := tupleT lin
  match termParts parts M with
  | some ps => pure ⟨B, .tensor K .unit, K, ps⟩
  | none => throw ⟨sp, s!"a div function whose result holds `{ppT K}`, which has no destructor, " ++
      "must hand it back by name: `return (c, …)` (SPEC §14)"⟩

def internalError (sp : Span) (what : String) (e : Error) : Error :=
  ⟨sp, s!"internal error in {what}: {e.render}"⟩

/-- Where generated code came from: the span of each sugar that produced core, and the sugar's
name. -/
abbrev Origins := List (Span × String)

/-- Elaboration, recording origins. -/
abbrev SM := StateT Origins (Except Error)

/-- Record that the core at `sp` was generated by `what`. -/
def note (sp : Span) (what : String) : SM Unit := modify (· ++ [(sp, what)])

/-- A parsed template, with its own nodes at the span `sp` of the sugar it elaborates. -/
def template (sp : Span) (what : String) (src : String) : SM Comp := do
  let L ← (parseComp src).mapError (internalError sp what)
  note sp what
  pure (L.respan sp)

/-! #### Elaborating a div body -/

/-- A terminal `T` of a div body: `io_v : B <- T`, then the loop that finishes with `io_v` at
its first observation; closed instead, it hands back the components of `io_v` that have no
destructor, and the checker drops the others. -/
def dret (cx : LoopCx) (T : Comp) : SM Comp := do
  let parts := spineT cx.B
  let lin := parts.map isLinear
  let last := (lin.zip (List.range lin.length)).foldl (fun a (b, i) => if b then i + 1 else a) 0
  let close := if last == 0 then "return ()" else
    let ns := (List.range last).map (s!"io_w{·}") ++ (if last < parts.length then ["io_wr"] else [])
    let keep := ((List.range last).zip lin).filterMap fun (i, b) => if b then some s!"io_w{i}" else none
    destructSrc "io_v" ns ++ s!"return ({tupleSrc keep}, ())"
  let src := s!"io_v : {ppT cx.B} <- force io_hole_t;
return (thunkv nu_in < return (inl io_v), {close} >)"
  let L ← template T.span "the loop a div function's result becomes" src
  let L := L.fill (fun _ => none) (fun n => if n == "io_hole_t" then some T else none)
  -- A terminal that lends keeps its binding unannotated, as `&c` requires.
  match T.takeLends.2, L with
  | [], _ => pure L
  | _, .bind sp x _ M N lin => pure (.bind sp x none M N lin)
  | _, L => pure L

/-- `x <- f V; N` with `f` a div function, `V` its argument with the lent capability `c`
replaced: the delay bind of `f`'s loop and the continuation, which binds `x` (with `c`, when
lent) and runs `N'`; closed during `f`'s loop, the continuation turns `f`'s residual into the
body's. -/
def divBind (cx : LoopCx) (sp : Span) (x : Ident) (A : Option VTy) (call : Comp)
    (lend : Option Ident) (Bf Rf : CVTy) (N' : Comp) : SM Comp := do
  let bindX := match lend, A with
    | some c, _ => s!"let ({c.name}, {x.name}) = io_a;"
    | none, some A => s!"{x.name} : {A.pp} <- return io_a;"
    | none, none => s!"{x.name} <- return io_a;"
  let abort ← if Rf = cx.R then pure "return io_r"
    else match Rf, lend with
      | .unit, _ => pure s!"let () = io_r; return {cx.rSrc}"
      | .tensor _ .unit, some c =>
        if cx.capNames.contains c.name then
          pure s!"let ({c.name}, io_u) = io_r; return {cx.rSrc}"
        else throw ⟨sp, s!"the call lends `{c.name}`, which is not among what this function " ++
          "hands back"⟩
      | _, _ => throw ⟨sp, s!"a call of a div function whose loop hands back `{ppT Rf}` when " ++
          "closed must lend what it hands back with `&c`, or hand back what this function hands " ++
          s!"back, `{ppT cx.R}` (SPEC §14)"⟩
  let src := s!"io_m <- force io_hole_call;
return (div_bind[{ppT Bf}, {ppT cx.B}, {ppT Rf}, {ppT cx.R}] (io_m, thunkv
  < fun (io_a : {ppT Bf}) -> {bindX} force io_hole_rest,
    fun (io_r : {ppT Rf}) -> {abort} >))"
  let L ← template sp "a call of a div function (`div_bind`)" src
  pure (L.fill (fun _ => none)
    (fun n => if n == "io_hole_call" then some call else if n == "io_hole_rest" then some N'
      else none))

/-- The latest binding of each name, oldest first. -/
def latest (env : List (String × Option CVTy)) : List (String × Option CVTy) :=
  env.reverse.foldl (fun acc (y, T) => (acc.filter (·.1 != y)) ++ [(y, T)]) []

/-- `for x in V { M }; N` in a div body: a loop by `unfold` whose state is the iterator `V`,
the other capabilities and the variables the loop threads, at their inferred types. Its `close`
closes the iterator and hands the capabilities back. When `N` is total, `rest` is `.inl N`: at
the end of the stream the loop runs `N` and finishes with its value, and it threads the
variables `M` or `N` mentions. Otherwise `rest` is `.inr N'`, `N` elaborated: the loop threads
the variables `M` mentions, finishes with the capabilities and those variables, and the delay
bind runs `N'` with them rebound.  `[spec §14]` -/
def forLoop (cx : LoopCx) (c : TCx) (sp : Span) (x : Ident) (V : Val) (M : Comp)
    (rest : Comp ⊕ Comp) : SM Comp := do
  let Vt ← match c.tyV V with
    | some Vt => pure Vt
    | none => throw ⟨V.span, "the type of the iterator of this `for` is not determined"⟩
  let (Ax, _, _) ← match iterOf Vt with
    | some it => pure it
    | none => throw ⟨V.span, s!"`for` iterates over an iterator `U (iter A R R')`, but this has " ++
        s!"type `{ppT Vt}`"⟩
  if let some (sp', what) := loopsAt (c.push x.name (some Ax)) none M then
    throw ⟨sp', s!"the body of a `for` is one step of its loop and must be total, but {what} " ++
      "(SPEC §14)"⟩
  let cs := cx.capNames
  let cap ← match cs.filter (mentionsV · V) with
    | [cap] => pure cap
    | _ => throw ⟨V.span, "the iterator of a `for` must be made from one capability that the " ++
        "function hands back, which the iterator hands back at its end"⟩
  let reads (y : String) : Bool := match rest with
    | .inl N => mentionsC y M || mentionsC y N
    | .inr _ => mentionsC y M
  let used := (latest c.locals).filter fun (y, _) => !cs.contains y && y != x.name && reads y
  let ws ← used.mapM fun (y, T) => match T with
    | some T => pure (y, T)
    | none => throw ⟨sp, s!"the loop threads `{y}`, whose type is not determined: ascribe it"⟩
  let th := cx.caps.filter (·.1 != cap)
  let sv := th.map (·.1) ++ ws.map (·.1)
  let svTy := th.map (ppT ·.2) ++ ws.map (ppT ·.2)
  let st := s!"{ppT Vt} * {tupleTySrc svTy}"
  let wT := tupleTySrc (ws.map (ppT ·.2))
  let fin := match rest with
    | .inl _ => s!"({ppT cx.B})"
    | .inr _ => s!"(({ppT cx.K}) * {wT})"
  let wv := tupleSrc (ws.map (·.1))
  let finish := match rest with
    | .inl _ => "force io_hole_fin"
    | .inr _ => s!"return (inl ({cx.kSrc}, {wv}))"
  let R := ppT cx.R
  let ds := destructSrc "io_st" sv
  let wn : List String := ws.map (·.1)
  let result := match rest with
    | .inl _ => "return (thunkv nu_in < (nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2 >)"
    | .inr _ => s!"io_l <- return (thunkv nu_in < (nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2 >);
return (div_bind[{fin}, {ppT cx.B}, ({R}), ({R})] (io_l, thunkv
  < fun (io_a : {fin}) ->
      let (io_ka, io_wa) = io_a;
      {destructParts "io_ka" cx.parts}      {destructSrc "io_wa" wn}      force io_hole_rest,
    fun (io_r : {R}) -> return io_r >))"
  let src := s!"io_step : !U ({st} -o F ({fin} + ({st})) & F ({R})) <- return (!thunkv fun (io_s : {st}) ->
  < let (io_it, io_st) = io_s;
    {ds}    io_o <- (nu_out (force io_it)).1;
    case io_o \{
      inl io_p ->
        let ({x.name}, io_it) = io_p;
        force io_hole_body
    | inr io_c ->
        {cap} <- return io_c;
        {finish}
    },
    let (io_it, io_st) = io_s;
    {ds}    io_c <- (nu_out (force io_it)).2;
    {cap} <- return io_c;
    return {cx.rSrc} >);
io_f <- return (unbang (unfold[loop {fin} ({R}), {st}] io_step));
io_s0 : {st} <- return (io_hole_v, {tupleSrc sv});
{result}"
  let L ← template sp "`for`" src
  let Bs ← toSurface sp cx.B
  let body := wrapTail (fun T => .bind T.span ⟨"io_u", T.span⟩ none T
      (.ret T.span (.inr T.span (.pair T.span (.var T.span "io_it") (tupleVal T.span sv)))) false) M
  let hole : String → Option Comp := match rest with
    | .inl N => fun n =>
      if n == "io_hole_body" then some body
      else if n == "io_hole_fin" then some (wrapTail (fun T =>
        let fin := Comp.bind T.span ⟨"io_v", T.span⟩ (some Bs) T
          (.ret T.span (.inl T.span (.var T.span "io_v"))) false
        -- A terminal that lends keeps its binding unannotated, as `&c` requires.
        match T.takeLends.2, fin with
        | [], _ => fin
        | _, .bind sp y _ M N lin => .bind sp y none M N lin
        | _, fin => fin) N)
      else none
    | .inr N' => fun n =>
      if n == "io_hole_body" then some body else if n == "io_hole_rest" then some N' else none
  pure (L.fill (fun v => if v == "io_hole_v" then some V else none) hole)

/-- A div body, elaborated to compute its loop (see the section's comment). `c` is the typing
context at the point reached.  `[spec §14]` -/
def loopBody (cx : LoopCx) : Nat → TCx → Comp → SM Comp
  | 0, _, M => throw ⟨M.span, "internal error: a div body nested too deeply"⟩
  | n + 1, c, .bind sp x A M N lin => do
    let exp := A.bind c.elabV
    -- Calls run in direct style below the top of the bound value are lifted out first.
    if let .ret sp' V := M then
      if (nestedCall c exp V).isSome then
        let (V', bs) := liftBelow V
        return (← loopBody cx n c (chain bs (.bind sp x A (.ret sp' V') N lin)))
    let (M', lends) := M.takeLends
    match (match M' with | .ret _ V => directCall c exp V | _ => none) with
    | none =>
      let N' ← loopBody cx n (c.push x.name (bindTy c A M)) N
      pure (.bind sp x A M N' lin)
    | some (Bf, Rf) =>
      let lend ← match lends with
        | [] => pure none
        | [l] => pure (some l)
        | _ => throw ⟨sp, "a call lends at most one capability with `&`"⟩
      let c' := match lend, Bf with
        | some l, .tensor K Vx => (c.push l.name (some K)).push x.name (exp <|> some Vx)
        | some l, _ => (c.push l.name none).push x.name exp
        | none, _ => c.push x.name (exp <|> some Bf)
      let N' ← loopBody cx n c' N
      divBind cx sp x A M' lend Bf Rf N'
  | n + 1, c, .letUnit sp V M => do
    if (callIn c divFuel (some .unit) V).isSome then
      let (V', bs) := liftAll V
      return (← loopBody cx n c (chain bs (.letUnit sp V' M)))
    return .letUnit sp V (← loopBody cx n c M)
  | n + 1, c, .letPair sp x y V M => do
    if (callIn c divFuel none V).isSome then
      let (V', bs) := liftAll V
      return (← loopBody cx n c (chain bs (.letPair sp x y V' M)))
    let (Ax, Ay) := pairTys c V
    return .letPair sp x y V (← loopBody cx n ((c.push x.name Ax).push y.name Ay) M)
  | n + 1, c, .case sp V x M y N => do
    if (callIn c divFuel none V).isSome then
      let (V', bs) := liftAll V
      return (← loopBody cx n c (chain bs (.case sp V' x M y N)))
    let (Ax, Ay) := sumTys c V
    return .case sp V x (← loopBody cx n (c.push x.name Ax) M) y
      (← loopBody cx n (c.push y.name Ay) N)
  | n + 1, c, .for_ sp x V M N => do
    -- What follows runs inside the loop's last step when it is total and every variable it
    -- reads has a type; otherwise it follows by the delay bind.
    let cs := cx.capNames
    let typed := (latest c.locals).all fun (y, T) =>
      cs.contains y || y == x.name || !mentionsC y N || T.isSome
    if (loopsAt c (some cx.B) N).isNone && typed then forLoop cx c sp x V M (.inl N)
    else forLoop cx c sp x V M (.inr (← loopBody cx n c N))
  | n + 1, c, T => do
    if let .ret sp V := T then
      if (nestedCall c (some cx.B) V).isSome then
        let (V', bs) := liftBelow V
        return (← loopBody cx n c (chain bs (.ret sp V')))
    let (T', lends) := T.takeLends
    match (match T' with | .ret _ V => directCall c (some cx.B) V | _ => none), lends with
    | some (Bf, Rf), [] =>
      let x : Ident := ⟨"io_t", T.span⟩
      divBind cx T.span x none T' none Bf Rf (← dret cx (.ret T.span (.var T.span "io_t")))
    | some _, _ =>
      -- A terminal call that lends is bound first, as a lend in a terminal is (SPEC §11).
      let x : Ident := ⟨"io_t", T.span⟩
      loopBody cx n c (.bind T.span x none T (.ret T.span (.var T.span "io_t")) false)
    | none, _ => dret cx T

/-! ### Programs -/

/-- The capabilities a program uses ambiently: none if it declares an extern. A `main` that loops
but mentions no capability has none: the runtime drives its loop without them (SPEC §14). -/
def ambientCaps (p : Program) : List String :=
  if p.decls.any (fun | .extern .. => true | _ => false) then [] else
  match p.decls.findSome? (fun | .main _ _ M => some M | _ => none) with
  | some M => capNames.filter (mentionsC · M)
  | none => []

/-- A capability's type. -/
def capTyC (c : String) : CVTy := .ref (.opq (if c == "stdin" then .input else .output))

/-- `main` with ambient capabilities, elaborated: its new type and body. `c` is the typing
context of `main`.  `[spec §11, §14]` -/
def ambientMain (c : TCx) (cs : List String) (sp : Span) (C : CTy) (M : Comp) :
    SM (CTy × Comp) := do
  let A ← match C with
    | .ret _ A => pure A
    | _ => throw ⟨C.span, "a `main` that uses the capabilities ambiently has type `F A`"⟩
  let capsV := tupleVal sp cs
  let M' := wrapTail (fun
      | .ret sp V => if V.takeLends.2.isEmpty then .ret sp (.pair sp capsV V)
          else .bind sp ⟨"io_r", sp⟩ none (.ret sp V) (.ret sp (.pair sp capsV (.var sp "io_r")))
            false
      | T => .bind T.span ⟨"io_r", T.span⟩ none T
          (.ret T.span (.pair T.span capsV (.var T.span "io_r"))) false) M
  let capsT := tupleTy sp (cs.map (capTy sp))
  let B := .tensor sp capsT A
  let Ac := c.elabV A
  if (loopsAt c Ac M).isNone then return (.ret sp B, M')
  let some Ac := Ac | throw ⟨A.span, "internal error: `main`'s result type"⟩
  let K := tupleT (cs.map capTyC)
  let cx : LoopCx := ⟨.tensor K Ac, .tensor K .unit, K, [cs.map fun n => (n, capTyC n)]⟩
  pure (.ret sp (.thunk sp (.loop sp B (.tensor sp capsT (.unit sp)))), ← loopBody cx divFuel c M')

/-- The result `B` of a function type `A => B` or `!(A => B)`. -/
def resultOf : Option CVTy → Option CVTy
  | some (.thunk (.arr _ (.ret B))) | some (.bang (.thunk (.arr _ (.ret B)))) => some B
  | _ => none

/-- A written function type whose result may be a loop: a thunk or a name there. -/
def _root_.Frontend.VTy.mayReturnLoop : VTy → Bool
  | .lolli _ _ B | .bang _ (.lolli _ _ B) => match B with
    | .thunk .. | .name .. => true
    | _ => false
  | .name .. => true
  | _ => false

/-- A `def`, with divergence inferred: the declaration as elaborated, and its entry in the div
functions when it is one. A div function is `thunkv fun (x : A) -> M` at `A => B`, or
`!thunkv fun (x : A) -> M` at `!(A => B)`. `scope` is the declarations before it, the
libraries first.  `[spec §14]` -/
def elabDef (scope : List Decl) : Decl → SM (Decl × Option (String × VTy))
  | d@(.def_ sp n ps A V mk) => do
    let c := TCx.ofScope scope false
    if (loopSig A).isSome || (A.mayReturnLoop && ((c.elabV A).bind loopFnOf).isSome) then
      return (d, some (n.name, A))
    let lam := match V with
      | .thunkv _ (.lam _ x Ax M) | .bangThunkv _ (.lam _ x Ax M) => some (x, Ax, M)
      | _ => none
    let why := lam.bind fun (x, Ax, M) =>
      loopsAt (c.push x.name (c.elabV Ax)) (resultOf (c.elabV A)) M
    match mk, why with
    | .total, some (sp', what) =>
      throw ⟨sp', s!"`{n.name}` is declared `total`, but {what} (SPEC §14)"⟩
    | .total, none | .none, none => return (d, none)
    | _, _ =>
      let some (x, Ax, M) := lam
        | throw ⟨sp, s!"a div function is written `thunkv fun (x : A) -> M` (SPEC §14)"⟩
      let (bang, Ar, B) ← match A, V with
        | .lolli _ Ar B, .thunkv .. => pure (false, Ar, B)
        | .bang _ (.lolli _ Ar B), .bangThunkv .. => pure (true, Ar, B)
        | _, _ => throw ⟨A.span, "a div function has type `A => B` or `!(A => B)` (SPEC §14)"⟩
      if !ps.isEmpty then
        throw ⟨sp, "a div function has no type parameters (SPEC §14)"⟩
      let some Bc := resultOf (c.elabV A)
        | throw ⟨A.span, s!"the type of `{n.name}` does not elaborate"⟩
      let cx ← loopCxOf sp Bc M
      let M' ← loopBody cx divFuel (c.push x.name (c.elabV Ax)) M
      let Rs ← toSurface sp cx.R
      let F := VTy.lolli A.span Ar (.thunk B.span (.loop B.span B Rs))
      let A' := if bang then VTy.bang A.span F else F
      let V' := match V with
        | .thunkv vsp (.lam lsp _ _ _) => Val.thunkv vsp (.lam lsp x Ax M')
        | .bangThunkv vsp (.lam lsp _ _ _) => Val.bangThunkv vsp (.lam lsp x Ax M')
        | V => V
      return (.def_ sp n ps A' V' mk, some (n.name, A'))
  | d => pure (d, none)

/-! ### Specialization at a callback's computation type

A higher-order function takes a callback at a function type, `A => B` or `!(A => B)`. Given a
callback whose type is a div function's, `A => U (loop B R)`, it is specialized: the elaborator
makes a copy of it with that parameter at the callback's type and infers the copy's divergence,
so calls through the parameter become calls of a div function in direct style, and the copy is
div. There is one copy per function and instantiation. A total callback uses the function as
written, which stays total. So one definition serves both kinds of callback, and the core never
has a type that ranges over them.

The callback's type is the type inference gives the argument (`TCx`), so any callback whose type
is known is covered: a named function, a local variable holding one, a callback an earlier call
returned, a component of a tuple held in a variable. A closure `thunkv fun (x : A) -> M` passed
at a callback type is elaborated first: when its body loops, it is elaborated as a div function
body in place, and its type is that of a div function. Only parameter types are instantiated
(decision 36): a callback's effect in a stored or returned type is the one its type says.
`[spec §14]` -/

/-- A higher-order function as written: `def h : P => Q = thunkv fun (x : P) -> M`, or its
persistent form `def h : !(P => Q) = !thunkv fun (x : P) -> M`. -/
structure Hof where
  sp : Span
  name : Ident
  bang : Bool
  P : VTy
  Q : VTy
  x : Ident
  M : Comp

/-- The latest source `def` named `h`, when it is a function without type parameters. -/
def hofOf (srcs : List Decl) (h : String) : Option Hof :=
  match srcs.find? (fun | .def_ _ n _ _ _ _ => n.name == h | _ => false) with
  | some (.def_ sp n [] (.lolli _ P Q) (.thunkv _ (.lam _ x _ M)) _) =>
    some ⟨sp, n, false, P, Q, x, M⟩
  | some (.def_ sp n [] (.bang _ (.lolli _ P Q)) (.bangThunkv _ (.lam _ x _ M)) _) =>
    some ⟨sp, n, true, P, Q, x, M⟩
  | _ => none

/-- A function of a callback's type at a function type `P` (`A => B`, or `!(A => B)`) that is
total: its argument type, its result, and whether it is persistent. -/
def totalFn : CVTy → Option (CVTy × CVTy × Bool)
  | .thunk (.arr A (.ret B)) => if (loopOf B).isSome then none else some (A, B, false)
  | .bang (.thunk (.arr A (.ret B))) => if (loopOf B).isSome then none else some (A, B, true)
  | _ => none

/-- The parameter type at which a function with parameter type `P` is called with an argument of
type `T`: where `P` has a total function type and `T` a div function's type of the same argument,
result and shape, `T`. `none` when the call needs no copy. -/
def specTy : CVTy → CVTy → Option CVTy
  | .tensor P Q, .tensor S T =>
    match specTy P S, specTy Q T with
    | none, none => none
    | a, b => some (.tensor (a.getD P) (b.getD Q))
  | P, T => do
    let (A, B, bang) ← totalFn P
    let (B', _) ← loopFnOf T
    let A' ← match T with
      | .thunk (.arr A' _) => if bang then none else some A'
      | .bang (.thunk (.arr A' _)) => if bang then some A' else none
      | _ => none
    if A' = A ∧ B' = B then some T else none

/-- The elaboration so far: the libraries (in scope for typing); the source declarations in
scope, newest first; the elaborated ones, in order; whether any body became a loop; and the
copies made, by function and parameter type. -/
structure DivSt where
  lib : List Decl := []
  srcs : List Decl := []
  out : List Decl := []
  any : Bool := false
  copies : List ((String × VTy) × String) := []

/-- Elaboration with the state of the declarations. -/
abbrev DM := StateT DivSt SM

/-- The function a call applies, by name, when it is a higher-order function as written. -/
def hofCallee : Val → Option String
  | .var _ h | .unbang _ (.var _ h) => some h
  | _ => none

/-- A callee renamed. -/
def renameCallee (name : String) : Val → Val
  | .var sp _ => .var sp name
  | .unbang sp (.var sp' _) => .unbang sp (.var sp' name)
  | f => f

/-- A closure passed at a callback type, elaborated when its body loops: the closure, and its
type when known. `P` is the parameter type it is passed at. -/
def closureAt (c : TCx) (P : CVTy) (V : Val) : DM (Val × Option CVTy) := do
  let some (_, B, bang) := totalFn P | return (V, c.tyV V)
  match V, bang with
  | .thunkv sp (.lam lsp x A M), false | .bangThunkv sp (.lam lsp x A M), true =>
    let Ac := c.elabV A
    let c' := c.push x.name Ac
    if (loopsAt c' (some B) M).isNone then return (V, c.tyV V)
    let cx ← (loopCxOf lsp B M : Except Error LoopCx)
    let M' ← (loopBody cx divFuel c' M : SM Comp)
    modify fun st => { st with any := true }
    let some Ac := Ac | return (V, none)
    let F : CVTy := .thunk (.arr Ac (.ret (.thunk (BoCa.Fig16.LogRel.Core.CTy.loop B cx.R))))
    let lam := Comp.lam lsp x A M'
    return (if bang then (.bangThunkv sp lam, some (.bang F)) else (.thunkv sp lam, some F))
  | V, _ => return (V, c.tyV V)

/-- The argument of a call at parameter type `P`, with its closures at callback types elaborated,
and the argument's type. -/
def argAt (c : TCx) : CVTy → Val → DM (Val × Option CVTy)
  | .tensor P Q, .pair sp V W => do
    let (V', a) ← argAt c P V
    let (W', b) ← argAt c Q W
    pure (.pair sp V' W', do pure (.tensor (← a) (← b)))
  | P, V => closureAt c P V

mutual
/-- Elaborate one declaration: first the copies its calls need (each elaborated the same way),
then its own divergence, with its calls renamed to the copies.  `[spec §14]` -/
def elabDecl : Nat → DivSt → Decl → SM DivSt
  | 0, _, d => throw ⟨(match d with | .def_ sp .. | .main sp .. => sp | _ => Span.none),
      "specialization at callback types does not terminate"⟩
  | fuel + 1, st, d => do
    let (d, st) ← (specDecl fuel d).run st
    let (d', e) ← elabDef (st.lib ++ st.out) d
    let elaborated := e.isSome && decide (d' ≠ d)
    pure { st with srcs := d :: st.srcs, out := st.out ++ [d'], any := st.any || elaborated }

/-- A declaration with each call of a higher-order function at a div callback renamed to a copy
at the callback's type, made on first use. -/
def specDecl : Nat → Decl → DM Decl
  | 0, d => pure d
  | n + 1, .def_ sp nm ps A V mk => do
    let st ← get
    let c := TCx.ofScope (st.lib ++ st.out) false
    pure (.def_ sp nm ps A (← specV n c V) mk)
  | n + 1, .main sp C M => do
    let st ← get
    let caps := capNames.map fun x => Decl.extern Span.none ⟨x, Span.none⟩ (capTy Span.none x)
    let c := TCx.ofScope (st.lib ++ st.out ++ caps) true
    pure (.main sp C (← specC n c M))
  | _, d => pure d

/-- The copy of `h` with parameter type `P'`, made on first use. -/
def copyOf : Nat → Hof → VTy → DM String
  | 0, hof, _ => pure hof.name.name
  | n + 1, hof, P' => do
    let st ← get
    if let some name := st.copies.lookup (hof.name.name, P'.strip) then return name
    let name := s!"{hof.name.name}__{st.copies.length}"
    let F := VTy.lolli hof.P.span P' hof.Q
    let lam := Comp.lam hof.sp hof.x P' hof.M
    let copy := if hof.bang then Decl.def_ hof.sp ⟨name, hof.name.span⟩ [] (.bang hof.P.span F)
        (.bangThunkv hof.sp lam) .none
      else Decl.def_ hof.sp ⟨name, hof.name.span⟩ [] F (.thunkv hof.sp lam) .none
    let st' ← (elabDecl n { st with copies := ((hof.name.name, P'.strip), name) :: st.copies }
      copy : SM DivSt)
    set st'
    pure name

/-- A value with its calls of higher-order functions specialized. -/
def specV : Nat → TCx → Val → DM Val
  | 0, _, V => pure V
  | n + 1, c, V => match V with
    | .app sp f W => do
      let W ← specV n c W
      let some h := hofCallee f | return .app sp (← specV n c f) W
      let some hof := hofOf (← get).srcs h | return .app sp f W
      let some P := c.elabV hof.P | return .app sp f W
      let (W', T) ← argAt c P W
      match T.bind (specTy P) with
      | none => return .app sp f W'
      | some P' =>
        let P's ← (toSurface sp P' : Except Error VTy)
        return .app sp (renameCallee (← copyOf n hof P's) f) W'
    | .pair sp V W => do pure (.pair sp (← specV n c V) (← specV n c W))
    | .inl sp V => do pure (.inl sp (← specV n c V))
    | .inr sp V => do pure (.inr sp (← specV n c V))
    | .unbang sp V => do pure (.unbang sp (← specV n c V))
    | .boxed sp l V => do pure (.boxed sp l (← specV n c V))
    | .unbox sp V => do pure (.unbox sp (← specV n c V))
    | .sub sp V l => do pure (.sub sp (← specV n c V) l)
    | .roll sp V => do pure (.roll sp (← specV n c V))
    | .unroll sp V => do pure (.unroll sp (← specV n c V))
    | .inst sp V l => do pure (.inst sp (← specV n c V) l)
    | .ascribe sp V A => do pure (.ascribe sp (← specV n c V) A)
    | .shorten sp m σ l V => do pure (.shorten sp m σ l (← specV n c V))
    | .thunk sp M => do pure (.thunk sp (← specC n c.pushDead M))
    | .thunkv sp M => do pure (.thunkv sp (← specC n c M))
    | .bangThunk sp M => do pure (.bangThunk sp (← specC n c.pushDead M))
    | .bangThunkv sp M => do pure (.bangThunkv sp (← specC n c M))
    | .run sp M => do pure (.run sp (← specC n c M))
    | V => pure V

/-- A computation with its calls of higher-order functions specialized. -/
def specC : Nat → TCx → Comp → DM Comp
  | 0, _, M => pure M
  | n + 1, c, M => match M with
    | .ret sp V => do pure (.ret sp (← specV n c V))
    | .absurd sp V => do pure (.absurd sp (← specV n c V))
    | .bind sp x A M N lin => do
      let t := bindTy c A M
      pure (.bind sp x A (← specC n c M) (← specC n (c.push x.name t) N) lin)
    | .lam sp x A M => do pure (.lam sp x A (← specC n (c.push x.name (c.elabV A)) M))
    | .app sp M x => do pure (.app sp (← specC n c M) x)
    | .with_ sp M N => do pure (.with_ sp (← specC n c.pushDead.pushDead M)
        (← specC n c.pushDead.pushDead N))
    | .proj sp i M => do pure (.proj sp i (← specC n c M))
    | .letUnit sp V M => do pure (.letUnit sp (← specV n c V) (← specC n c M))
    | .letPair sp x y V M => do
      let (Ax, Ay) := pairTys c V
      pure (.letPair sp x y (← specV n c V) (← specC n ((c.push x.name Ax).push y.name Ay) M))
    | .case sp V x M y N => do
      let (Ax, Ay) := sumTys c V
      pure (.case sp (← specV n c V) x (← specC n (c.push x.name Ax) M) y
        (← specC n (c.push y.name Ay) N))
    | .lamL sp x b M => do pure (.lamL sp x b (← specC n c.pushDead M))
    | .inst sp M a => do pure (.inst sp (← specC n c M) a)
    | .nuIn sp M => do pure (.nuIn sp (← specC n c M))
    | .nuOut sp M => do pure (.nuOut sp (← specC n c M))
    | .ascribe sp M C => do pure (.ascribe sp (← specC n c M) C)
    | .for_ sp x V M N => do
      let el := (c.tyV V).bind iterOf |>.map (·.1)
      pure (.for_ sp x (← specV n c V) (← specC n (c.push x.name el) M) (← specC n c N))
    | M => pure M
end

/-- The declarations with divergence inferred, in order (copies before their first use), and
whether any body was elaborated as a loop. -/
def elabDivs (lib decls : List Decl) : SM (List Decl × Bool) := do
  let st ← decls.foldlM (init := ({ lib } : DivSt)) (elabDecl divFuel)
  pure (st.out, st.any)

/-- A `main` that is not ambient, elaborated as a loop when its body loops. `c` is the typing
context of `main`. -/
def plainMain (c : TCx) (sp : Span) (C : CTy) (M : Comp) : SM (CTy × Comp) := do
  if C.returnsLoop then return (C, M)
  let Bc := match C with
    | .ret _ B => c.elabV B
    | _ => none
  match C, Bc, loopsAt c Bc M with
  | .ret _ B, some Bc, some _ =>
    let cx ← loopCxOf sp Bc M
    pure (.ret sp (.thunk sp (.loop sp B (← toSurface sp cx.R))), ← loopBody cx divFuel c M)
  | _, _, some (sp', what) =>
    throw ⟨sp', s!"`main` loops ({what}), so its type is written `F A` (SPEC §14)"⟩
  | _, _, none => pure (C, M)

/-- A program uses the library function `n` without defining it. -/
def usesName (n : String) (p : Program) : Bool :=
  p.decls.any (fun | .def_ _ _ _ _ V _ => V.names n | .main _ _ M => M.names n | _ => false) &&
    !(p.decls.any fun | .def_ _ m _ _ _ _ => m.name == n | _ => false)

/-- The program with its sugar elaborated, and the number of library declarations it begins
with, recording the origins of generated code.  `[spec §11, §14]` -/
def elaborateS (p : Program) : SM (Program × Nat) := do
  let libOf (name src : String) : Except Error (List Decl) :=
    match parseProgram src with
    | .ok l => pure l.decls
    | .error e => throw ⟨e.span, s!"{name}: {e.msg}"⟩
  -- The libraries are in scope for typing when the program may use them: the I/O library when
  -- `main` may use the capabilities ambiently, the divergence library when the program names
  -- its functions. They are emitted below only when the program uses them. The capabilities are
  -- in scope for typing `main`, which may use them ambiently.
  let mayIO := !(ambientCaps p).isEmpty
  let mayDiv := usesName "div_fuel" p || usesName "div_bind" p
  let ioAll ← if mayIO then libOf "lib/io.bc" ioLibrary else pure []
  let divAll ← if mayDiv then libOf "lib/div.bc" divLibrary else pure []
  let typing := ioAll ++ divAll
  let capDecls := if mayIO then capNames.map fun c =>
      Decl.extern Span.none ⟨c, Span.none⟩ (capTy Span.none c) else []
  -- Bindings whose type only their uses determine (an injection) are annotated first.
  let p := Elab.fillProgram typing capDecls p
  -- Divergence of the user's definitions, before the libraries (which do not loop) come in.
  let (decls, anyDiv) ← elabDivs typing p.decls
  let rest := decls.filter fun | .main .. => false | _ => true
  let mc := TCx.ofScope (typing ++ rest ++ capDecls) true
  let mainLoops := match decls.findSome? (fun | .main _ C M => some (C, M) | _ => none) with
    | some (C@(.ret _ B), M) => !C.returnsLoop && (loopsAt mc (mc.elabV B) M).isSome
    | _ => false
  let cs := ambientCaps p
  let needDiv := anyDiv || mainLoops || usesName "div_fuel" p || usesName "div_bind" p
  let ioLib ← if cs.isEmpty then pure [] else
    if mayIO then pure ioAll else libOf "lib/io.bc" ioLibrary
  let divLib ← if needDiv then
    if mayDiv then pure divAll else libOf "lib/div.bc" divLibrary else pure []
  let exts := cs.map fun c => Decl.extern Span.none ⟨c, Span.none⟩ (capTy Span.none c)
  let mains ← decls.filterMapM fun
    | .main sp C M => do
      let (C', M') ← if cs.isEmpty then plainMain mc sp C M else ambientMain mc cs sp C M
      pure (some (Decl.main sp C' M'))
    | _ => pure none
  let lib := ioLib ++ divLib
  let decls ← (lib ++ rest ++ exts ++ mains).mapM fun
    | .def_ sp n ps A V mk => return .def_ sp n ps A (← V.elab false) mk
    | .main sp C M => return .main sp C (← M.elab false)
    | d => pure d
  pure (⟨decls⟩, lib.length)

/-- The program with its sugar elaborated, the number of library declarations it begins with,
and the origins of its generated code. -/
def elaborateO (p : Program) : Except Error (Program × Nat × Origins) := do
  let ((q, n), os) ← (elaborateS p).run []
  pure (q, n, os)

/-- The program with its sugar elaborated, and the number of library declarations it begins
with.  `[spec §11, §14]` -/
def elaborate (p : Program) : Except Error (Program × Nat) := do
  let (q, n, _) ← elaborateO p
  pure (q, n)

end Frontend.Sugar
