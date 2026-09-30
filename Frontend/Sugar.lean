import Frontend.Parser
import Frontend.Print
import Frontend.Check.Steps
import Frontend.Elab.Respan
import Frontend.Elab.Subst
import Frontend.Elab.Meta
import Frontend.Elab.LoopLend

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
  their inferred types), and makes the function div (§14): a state of the body's one state
  machine (`divMachine`, §15), or `forLoop` where the machine does not apply.
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

/-- The generator library, `lib/gen.bc`: `gen_bind`. -/
def genLibrary : String := include_str "../lib/gen.bc"

/-- The per-observation lend, `lib/lend.bc`: loops and generators that lend their owner at each
observation. -/
def lendLibrary : String := include_str "../lib/lend.bc"
/-- The generator adapters, `lib/adapters.bc`: `map`, `filter`, `take`, … (`include adapters`). -/
def adaptersLibrary : String := include_str "../lib/adapters.bc"

/-- The slice library, `lib/slice.bc`: functions on the views an array lends (`include slice`). -/
def sliceLibrary : String := include_str "../lib/slice.bc"

/-- The prelude, `lib/prelude.bc`: `true`, `false`, `not`, `to_i32`, `to_u8`. -/
def preludeLibrary : String := include_str "../lib/prelude.bc"

/-- The library modules, by the name `include` gives them (#59). A module is a file of `lib/`,
embedded in the compiler; adding one is adding its line here. -/
def libModules : List (String × String) :=
  [("io", ioLibrary), ("div", divLibrary), ("prelude", preludeLibrary), ("lend", lendLibrary),
   ("adapters", adaptersLibrary), ("slice", sliceLibrary)]

def capNames : List String := ["stdin", "stdout", "stderr"]

def capTy (sp : Span) (c : String) : VTy := .ref sp (.handle sp (c != "stdin"))

/-! ### Lending a capability to one call -/

mutual
/-- Elaborate `&c` in a value; with `lend`, a `&c` outside nested computations becomes `c`. -/
def _root_.Frontend.Val.elab (lend : Bool) : Val → Except Error Val
  | .lend sp x m =>
    if lend then pure (.var x.span x.name) else
    throw ⟨sp, s!"`{if m == .mut then "&mut " else "&"}{x.name}` lends a place to one call: it may appear only " ++
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
  | .run sp M => return .run sp (← M.elab lend)
  | V@(.var ..) | V@(.defApp ..) | V@(.unit ..) | V@(.const ..) | V@(.sugar ..) => pure V

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
  | .letPair sp x y V M => return .letPair sp x y (← V.elab lend) (← M.elab false)
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

open Frontend.Elab (TCx loopOf iterOf genOf elemOf loopFnOf spineT tupleT ppT toSurface Class)
open Frontend.Check (CVTy CCTy)

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
  | .ret _ (.app _ (.sugar _ .retE) V) | .ret _ V =>
    ((parts.zip (alignV parts V)).filter (isLinear ·.1)).mapM fun (A, v) => v.bind (varsFor A)
  | _ => none

/-- What a div body is elaborated at: its result `B`, its residual `R = K * 1` (or `1`), `K`, and
the variables holding each component of `K`. A generator's residual is `K` itself (`tail1`
false): a generator that finishes with what it holds hands back the same when it is closed. -/
structure LoopCx where
  B : CVTy
  R : CVTy
  K : CVTy
  parts : List (List (String × CVTy))
  tail1 : Bool := true

def LoopCx.caps (cx : LoopCx) : List (String × CVTy) := cx.parts.flatten

def LoopCx.capNames (cx : LoopCx) : List String := cx.caps.map (·.1)

def LoopCx.kSrc (cx : LoopCx) : String := tupleSrc (cx.parts.map fun p => tupleSrc (p.map (·.1)))

/-- The residual built from the capabilities in scope. -/
def LoopCx.rSrc (cx : LoopCx) : String :=
  if cx.parts.isEmpty then "()" else if cx.tail1 then s!"({cx.kSrc}, ())" else cx.kSrc

/-- Bind the variables of each component of `K`, held in `v`. -/
def destructParts (v : String) (parts : List (List (String × CVTy))) : String :=
  match parts with
  | [p] => destructSrc v (p.map (·.1))
  | ps =>
    let ns := (List.range ps.length).map (s!"{v}_p{·}")
    destructSrc v ns ++ String.join ((ns.zip ps).map fun (n, p) => destructSrc n (p.map (·.1)))

/-- The context a div function with result `B` and body `M` is elaborated at, or a generator
(`gen`), whose residual is `K`.  `[spec §14, §15]` -/
def loopCxOf (sp : Span) (B : CVTy) (M : Comp) (gen : Bool := false) : Except Error LoopCx := do
  let parts := spineT B
  let lin := parts.filter isLinear
  if lin.isEmpty then return ⟨B, .unit, .unit, [], true⟩
  let K := tupleT lin
  match termParts parts M with
  | some ps => pure (if gen then ⟨B, K, K, ps, false⟩ else ⟨B, .tensor K .unit, K, ps, true⟩)
  | none => throw ⟨sp, s!"a div function whose result holds `{ppT K}`, which has no destructor, " ++
      "must hand it back by name: `return (c, …)` (SPEC §14)"⟩

def internalError (sp : Span) (what : String) (e : Error) : Error :=
  ⟨sp, s!"internal error in {what}: {e.render}"⟩

/-- Where generated code came from: the span of each sugar that produced core, and the sugar's
name. -/
abbrev Origins := List (Span × String)

/-- Elaboration, recording origins. -/
abbrev SM := StateT Origins (Except Error)

/-- The origin that marks a use written `clone(x)` (`Frontend/Elab/Copies.lean`). -/
def cloneOrigin : String := "`clone`"

/-- Record that the core at `sp` was generated by `what`. -/
def note (sp : Span) (what : String) : SM Unit := modify (· ++ [(sp, what)])

/-- A parsed template, with its own nodes at the span `sp` of the sugar it elaborates. -/
def template (sp : Span) (what : String) (src : String) : SM Comp := do
  let L ← (parseComp src).mapError (internalError sp what)
  note sp what
  pure (L.respan sp)

/-! #### Exits: `break`, `return` and `yield` -/

/-- A computation has a loop on its spine or anywhere in it. -/
def _root_.Frontend.Comp.hasFor : Comp → Bool
  | .bind _ _ _ M N _ | .with_ _ M N => M.hasFor || N.hasFor
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ | .letUnit _ _ M | .letPair _ _ _ _ M => M.hasFor
  | .case _ _ _ M _ N => M.hasFor || N.hasFor
  | .for_ .. => true
  | _ => false

mutual
/-- The first `yield`, `break` or `return e` (of a generator) in a value. -/
def _root_.Frontend.Val.yieldAt : Val → Option Span
  | .app sp (.sugar _ .yield_) _ | .sugar sp .brk | .app sp (.sugar _ .retE) _
  | .app sp (.sugar _ .yieldFrom) _ => some sp
  | .pair _ V W | .app _ V W => V.yieldAt.orElse fun _ => W.yieldAt
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => V.yieldAt
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => M.yieldAt
  | _ => none

/-- The first `yield` or `break` in a computation. -/
def _root_.Frontend.Comp.yieldAt : Comp → Option Span
  | .ret _ V | .absurd _ V => V.yieldAt
  | .bind _ _ _ M N _ | .with_ _ M N => M.yieldAt.orElse fun _ => N.yieldAt
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ => M.yieldAt
  | .letUnit _ V M | .letPair _ _ _ V M => V.yieldAt.orElse fun _ => M.yieldAt
  | .case _ V _ M _ N => V.yieldAt.orElse fun _ => M.yieldAt.orElse fun _ => N.yieldAt
  | .for_ _ _ V M N => V.yieldAt.orElse fun _ => M.yieldAt.orElse fun _ => N.yieldAt
  | .force .. | .top _ => none
end

/-- A `yield` or `break` in a value. -/
def _root_.Frontend.Val.hasYield (V : Val) : Bool := V.yieldAt.isSome

/-- A `yield` or `break` in a computation. -/
def _root_.Frontend.Comp.hasYield (M : Comp) : Bool := M.yieldAt.isSome

mutual
/-- A surface leaf satisfying `p` in a value. -/
def _root_.Frontend.Val.anySugar (p : VSugar → Bool) : Val → Bool
  | .sugar _ s => p s
  | .pair _ V W | .app _ V W => V.anySugar p || W.anySugar p
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => V.anySugar p
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => M.anySugar p
  | _ => false

/-- A surface leaf satisfying `p` in a computation. -/
def _root_.Frontend.Comp.anySugar (p : VSugar → Bool) : Comp → Bool
  | .ret _ V | .absurd _ V => V.anySugar p
  | .bind _ _ _ M N _ | .with_ _ M N => M.anySugar p || N.anySugar p
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ => M.anySugar p
  | .letUnit _ V M | .letPair _ _ _ V M => V.anySugar p || M.anySugar p
  | .case _ V _ M _ N => V.anySugar p || M.anySugar p || N.anySugar p
  | .for_ _ _ V M N => V.anySugar p || M.anySugar p || N.anySugar p
  | .force .. | .top _ => false
end

mutual
/-- The first surface leaf satisfying `p` in a value. -/
def _root_.Frontend.Val.sugarAt (p : VSugar → Bool) : Val → Option Span
  | .sugar sp s => if p s then some sp else none
  | .pair _ V W | .app _ V W => (V.sugarAt p).orElse fun _ => W.sugarAt p
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => V.sugarAt p
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => M.sugarAt p
  | _ => none

/-- The first surface leaf satisfying `p` in a computation. -/
def _root_.Frontend.Comp.sugarAt (p : VSugar → Bool) : Comp → Option Span
  | .ret _ V | .absurd _ V => V.sugarAt p
  | .bind _ _ _ M N _ | .with_ _ M N => (M.sugarAt p).orElse fun _ => N.sugarAt p
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ => M.sugarAt p
  | .letUnit _ V M | .letPair _ _ _ V M => (V.sugarAt p).orElse fun _ => M.sugarAt p
  | .case _ V _ M _ N => ((V.sugarAt p).orElse fun _ => M.sugarAt p).orElse fun _ => N.sugarAt p
  | .for_ _ _ V M N => ((V.sugarAt p).orElse fun _ => M.sugarAt p).orElse fun _ => N.sugarAt p
  | .force .. | .top _ => none
end

/-- A `yield` or `yield from`: of a generator's body only. -/
def isYieldKw (k : VSugar) : Bool := k == .yield_ || k == .yieldFrom

/-- A generator's `return e` in a computation, at any depth of its loops. -/
def _root_.Frontend.Comp.hasRet (M : Comp) : Bool := M.anySugar (· == .retE)

/-- A computation yields or loops: what follows a generator's loop runs in the loop's last step
when it does neither. -/
def _root_.Frontend.Comp.yieldsOrLoops (M : Comp) : Bool :=
  M.anySugar (fun k => k == .yield_ || k == .yieldFrom) || M.hasFor

/-- A terminal that leaves: `break`, `break e` or a generator's `return e`. -/
def _root_.Frontend.Comp.isExit : Comp → Bool
  | .ret _ (.sugar _ .brk) | .ret _ (.app _ (.sugar _ .brk) _) | .ret _ (.app _ (.sugar _ .retE) _) =>
    true
  | _ => false

/-- A `break` on the spine outside every loop. -/
def _root_.Frontend.Comp.spineBreak : Comp → Option Span
  | .bind _ _ _ _ N _ | .letUnit _ _ N | .letPair _ _ _ _ N | .for_ _ _ _ _ N => N.spineBreak
  | .case _ _ _ M _ N => M.spineBreak.orElse fun _ => N.spineBreak
  | .ret sp (.sugar _ .brk) | .ret sp (.app _ (.sugar _ .brk) _) => some sp
  | _ => none

/-- The `break`s on the spine outside every inner loop, with their values. -/
def _root_.Frontend.Comp.spineBreaks : Comp → List (Span × Option Val)
  | .bind _ _ _ _ N _ | .letUnit _ _ N | .letPair _ _ _ _ N | .for_ _ _ _ _ N => N.spineBreaks
  | .case _ _ _ M _ N => M.spineBreaks ++ N.spineBreaks
  | .ret sp (.sugar _ .brk) => [(sp, none)]
  | .ret sp (.app _ (.sugar _ .brk) e) => [(sp, some e)]
  | _ => []

/-- What follows a loop whose value is bound (`let r = for …; N`): `r`, its written type, and
`N`. -/
def _root_.Frontend.Comp.forRes? : Comp → Option (Ident × Option VTy × Comp)
  | .bind _ r A (.ret _ (.sugar _ .forRes)) N _ => some (r, A, N)
  | _ => none

/-- A right-nested tuple of values (`()` when empty). -/
def tupleVals (sp : Span) : List Val → Val
  | [] => .unit sp
  | [v] => v
  | v :: vs => .pair sp v (tupleVals sp vs)

/-- What an iterator or a generator finishes with: the value of a `for` over it. -/
def finOf (T : CVTy) : Option CVTy :=
  ((genOf T).map (·.2.1)).orElse fun _ => (iterOf T).map (·.2.1)

/-- The `break`s of a loop's body against whether the loop's value is bound (`keep`, of type
`T`): a bare `break` gives `()` only when the value is `1`, and `break e` needs a bound value. -/
def checkBreaks (M : Comp) (keep : Option CVTy) : Except Error Unit :=
  for (bsp, e) in M.spineBreaks do
    match keep, e with
    | none, some _ => throw ⟨bsp, "`break e` gives the value of a `for` whose value is bound: " ++
        "`let r = for x in … { … }; …`"⟩
    | some T, none => if T != .unit then
        throw ⟨bsp, s!"this `for`'s value, of type `{ppT T}`, is bound: `break e` gives it"⟩
    | _, _ => pure ()

/-- A generator's `return e` terminals as the plain terminal `e`: at the generator's top level, where
finishing with `e` is what the terminal does. -/
def stripRet : Comp → Comp :=
  wrapTail fun
    | .ret sp (.app _ (.sugar _ .retE) V) => .ret sp V
    | T => T

/-- The error for a `yield` or `break` off the spine. -/
def yieldOffSpine (sp : Span) : Error :=
  ⟨sp, "`yield` and `break` may appear only on the spine of a generator's body (the tail " ++
    "positions of binds, `let`s, `match` arms, loops and borrow blocks): not inside a value or a " ++
    "call's argument"⟩

/-- Moved to tail positions: the exits (`break`, `return e`) and `yield`s of a body's heads. What
follows a head that leaves or yields goes into it (a commuting conversion): into both arms of a
`match` or `if`, after the body of a `let`, into what follows a loop; and what follows an exit is
dropped, since it never runs. A `yield` then stands on the spine, and every `break` and `return`
is a terminal. The bodies of loops are left as they are: each is moved when its loop is
elaborated. -/
def normExits : Nat → Comp → Except Error Comp
  | 0, M => pure M
  | n + 1, .bind sp x A M N lin => do
    if M.isExit then return M
    if !M.hasYield then return .bind sp x A M (← normExits n N) lin
    let capture (ys : List Ident) : Except Error Unit :=
      if ys.any (fun y => mentionsC y.name N) then throw (yieldOffSpine (M.yieldAt.getD M.span))
      else pure ()
    match M with
    | .case csp V y M₁ z M₂ =>
      capture [y, z]
      normExits n (.case csp V y (.bind sp x A M₁ N lin) z (.bind sp x A M₂ N lin))
    | .bind bsp y B M₁ M₂ lin' =>
      capture [y]
      normExits n (.bind bsp y B M₁ (.bind sp x A M₂ N lin) lin')
    | .letPair lsp y z V M₁ =>
      capture [y, z]
      normExits n (.letPair lsp y z V (.bind sp x A M₁ N lin))
    | .letUnit lsp V M₁ => normExits n (.letUnit lsp V (.bind sp x A M₁ N lin))
    | .for_ fsp y V M₁ M₂ => normExits n (.for_ fsp y V M₁ (.bind sp x A M₂ N lin))
    | _ => pure (.bind sp x A M (← normExits n N) lin)
  | n + 1, .letUnit sp V M => do pure (.letUnit sp V (← normExits n M))
  | n + 1, .letPair sp x y V M => do pure (.letPair sp x y V (← normExits n M))
  | n + 1, .case sp V x M y N => do pure (.case sp V x (← normExits n M) y (← normExits n N))
  | n + 1, .for_ sp x V M N => do pure (.for_ sp x V M (← normExits n N))
  | _, T => pure T

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

/-- A computation binds `y` on its spine. -/
def _root_.Frontend.Comp.rebindsN (y : String) : Comp → Bool
  | .bind _ x _ M N _ => x.name == y || M.rebindsN y || N.rebindsN y
  | .letUnit _ _ M => M.rebindsN y
  | .letPair _ a b _ M => a.name == y || b.name == y || M.rebindsN y
  | .case _ _ _ M _ N => M.rebindsN y || N.rebindsN y
  | .for_ _ _ _ M N => M.rebindsN y || N.rebindsN y
  | _ => false

/-- A computation binds `y` on its spine: a `let mut` variable assigned in it. The wildcard `_`
names nothing. -/
def _root_.Frontend.Comp.rebinds (y : String) (M : Comp) : Bool := y != "_" && M.rebindsN y

/-- Bind the capability `cap` (when there is one) from `v`, the value an iterator hands back
of type `Q`: itself, or `(cap, ())` as a residual. -/
def bindCap (cap : Option String) (Q : CVTy) (v : String) : String :=
  match cap, Q with
  | none, _ => ""
  | some c, .tensor _ .unit => s!"let ({c}, {v}_u) = {v};\n"
  | some c, _ => s!"{c} <- return {v};\n"

/-- `for x in V { M }; N` in a div body: a loop by `unfold` whose state is the iterator `V`,
the other capabilities and the variables the loop threads, at their inferred types. Its `close`
closes the iterator and hands the capabilities back. When `N` is total, `rest` is `.inl N`: at
the end of the stream the loop runs `N` and finishes with its value, and it threads the
variables `M` or `N` mentions. Otherwise `rest` is `.inr N'`, `N` elaborated: the loop threads
the variables `M` mentions, finishes with the capabilities and those variables, and the delay
bind runs `N'` with them rebound.  `[spec §14]` -/
def forLoop (cx : LoopCx) (c : TCx) (sp : Span) (x : Ident) (V : Val) (M : Comp)
    (keep₀ : Option Ident) (rest : Comp ⊕ Comp) : SM Comp := do
  if let .app _ (.sugar wsp .while_) _ := V then
    throw ⟨wsp, "`while` is a generator's loop: it may appear only in the body of a `gen fn`"⟩
  -- `bytes(&mut c)`: the iterator takes `c`, and hands it back at its end (typed elaboration §5.1).
  let V := V.takeLends.1
  let Vt ← match c.tyV V with
    | some Vt => pure Vt
    | none => throw ⟨V.span, "the type of the iterator of this `for` is not determined"⟩
  let (Ax, isGen, Q, Q') ← match iterOf Vt, genOf Vt with
    | some (A, Q, Q'), _ => pure (A, false, Q, Q')
    | none, some (A, Q, Q') => pure (A, true, Q, Q')
    | none, none => throw ⟨V.span, s!"`for` iterates over an iterator `U (iter A R R')` or a " ++
        s!"generator `U (gen A B R)`, but this has type `{ppT Vt}`"⟩
  if let some (sp', what) := loopsAt (c.push x.name (some Ax)) none M then
    throw ⟨sp', s!"the body of a `for` is one step of its loop and must be total, but {what} " ++
      "(SPEC §14)"⟩
  let M ← normExits divFuel M
  let cs := cx.capNames
  -- The capability the iterator is made from, which it hands back at its end; none for an
  -- iterator that holds no capability.
  let cap ← match cs.filter (mentionsV · V) with
    | [] => pure none
    | [cap] => pure (some cap)
    | _ => throw ⟨V.span, "the iterator of a `for` is made from at most one capability"⟩
  -- `let c = for …` with `c` a capability the body hands back: the iterator hands `c` back when
  -- it finishes or is closed, as an iterator made from `c` does.
  let (cap, keep₀) := match keep₀ with
    | some r => if cs.contains r.name && (cap.isNone || cap == some r.name) then (some r.name, none)
      else (cap, keep₀)
    | none => (cap, keep₀)
  -- `let r = for …`: the loop's value, what the iterator finishes with or a `break e`.
  let keep : Option (String × CVTy) ← match keep₀, cap with
    | none, _ => pure none
    | some r, none => pure (some (r.name, Q))
    | some r, some c =>
      throw ⟨r.span, s!"the iterator of this `for` is made from `{c}`, which it hands back " ++
        "when it finishes: the loop's value is not bound"⟩
  checkBreaks M (keep.map (·.2))
  -- A variable the body reads or assigns (a `let mut` rebound in it) is threaded.
  let reads (y : String) : Bool := match rest with
    | .inl N => mentionsC y M || M.rebinds y || mentionsC y N
    | .inr _ => mentionsC y M || M.rebinds y
  let used := (latest c.locals).filter fun (y, _) => !cs.contains y && y != x.name && reads y
  let ws ← used.mapM fun (y, T) => match T with
    | some T => pure (y, T)
    | none => throw ⟨sp, s!"the loop threads `{y}`, whose type is not determined: ascribe it"⟩
  let th := cx.caps.filter (some ·.1 != cap)
  let sv := th.map (·.1) ++ ws.map (·.1)
  let svTy := th.map (ppT ·.2) ++ ws.map (ppT ·.2)
  let st := s!"{ppT Vt} * {tupleTySrc svTy}"
  -- What the loop finishes with when what follows it runs after it: the capabilities, the
  -- variables the body threads, and the loop's value when it is bound.
  let wT := tupleTySrc ((ws ++ keep.toList).map (ppT ·.2))
  let fin := match rest with
    | .inl _ => s!"({ppT cx.B})"
    | .inr _ => s!"(({ppT cx.K}) * {wT})"
  let wv := tupleSrc ((ws ++ keep.toList).map (·.1))
  let finish := match rest with
    | .inl _ => "force io_hole_fin"
    | .inr _ => s!"return (inl ({cx.kSrc}, {wv}))"
  let R := ppT cx.R
  let ds := destructSrc "io_st" sv
  let wn : List String := (ws ++ keep.toList).map (·.1)
  -- At the end of the stream: the capability handed back, or the loop's value bound.
  let atEnd (v : String) : String := match keep with
    | some (r, _) => s!"{r} <- return {v};\n"
    | none => bindCap cap Q v
  let result := match rest with
    | .inl _ => "return (thunkv nu_in < (nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2 >)"
    | .inr _ => s!"io_l <- return (thunkv nu_in < (nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2 >);
return (div_bind[{fin}, {ppT cx.B}, ({R}), ({R})] (io_l, thunkv
  < fun (io_a : {fin}) ->
      let (io_ka, io_wa) = io_a;
      {destructParts "io_ka" cx.parts}      {destructSrc "io_wa" wn}      force io_hole_rest,
    fun (io_r : {R}) -> return io_r >))"
  let ended := if isGen then s!"case io_d \{
          inl io_c -> {atEnd "io_c"}{finish}
        | inr io_it -> return (inr (io_it, {tupleSrc sv}))
        }" else s!"{atEnd "io_c"}{finish}"
  let src := s!"io_step : !U ({st} -o F ({fin} + ({st})) & F ({R})) <- return (!thunkv fun (io_s : {st}) ->
  < let (io_it, io_st) = io_s;
    {ds}    io_o <- (nu_out (force io_it)).1;
    case io_o \{
      inl io_p ->
        let ({x.name}, io_it) = io_p;
        force io_hole_body
    | inr {if isGen then "io_d" else "io_c"} ->
        {ended}
    },
    let (io_it, io_st) = io_s;
    {ds}    io_c <- (nu_out (force io_it)).2;
    {bindCap cap Q' "io_c"}return {cx.rSrc} >);
io_f <- return (unbang (unfold[loop {fin} ({R}), {st}] io_step));
io_s0 : {st} <- return (io_hole_v, {tupleSrc sv});
{result}"
  let L ← template sp "`for`" src
  let Bs ← toSurface sp cx.B
  let finN : Option Comp := match rest with
    | .inl N => some (wrapTail (fun T =>
        let fin := Comp.bind T.span ⟨"io_v", T.span⟩ (some Bs) T
          (.ret T.span (.inl T.span (.var T.span "io_v"))) false
        -- A terminal that lends keeps its binding unannotated, as `&c` requires.
        match T.takeLends.2, fin with
        | [], _ => fin
        | _, .bind sp y _ M N lin => .bind sp y none M N lin
        | _, fin => fin) N)
    | .inr _ => none
  -- `break`: the iterator closed, then what follows the loop, as at the end of the stream.
  let brk ← template sp "`break`" s!"io_c <- (nu_out (force io_it)).2;\n{bindCap cap Q' "io_c"}{finish}"
  let brk := brk.fill (fun _ => none) (fun n => if n == "io_hole_fin" then finN else none)
  -- `break e` binds the loop's value first.
  let brkWith (bsp : Span) (e : Val) : Comp := match keep with
    | some (r, _) => .bind bsp ⟨r, bsp⟩ none (.ret bsp e) brk false
    | none => brk
  let body := wrapTail (fun
      | .ret bsp (.sugar _ .brk) => brkWith bsp (.unit bsp)
      | .ret bsp (.app _ (.sugar _ .brk) e) => brkWith bsp e
      | T => .bind T.span ⟨"io_u", T.span⟩ none T
        (.ret T.span (.inr T.span (.pair T.span (.var T.span "io_it") (tupleVal T.span sv)))) false) M
  let hole : String → Option Comp := match rest with
    | .inl _ => fun n =>
      if n == "io_hole_body" then some body
      else if n == "io_hole_fin" then finN
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
    -- `let r = for …; N`: `r` is bound in `N` to the loop's value.
    let (keep, N) := match N.forRes? with
      | some (r, _, N₀) => (some r, N₀)
      | none => (none, N)
    let cr := match keep with
      | some r => c.push r.name ((c.tyV V.takeLends.1).bind finOf)
      | none => c
    -- What follows runs inside the loop's last step when it is total and every variable it
    -- reads has a type; otherwise it follows by the delay bind.
    let cs := cx.capNames
    let typed := (latest c.locals).all fun (y, T) =>
      cs.contains y || y == x.name || !mentionsC y N || T.isSome
    if (loopsAt cr (some cx.B) N).isNone && typed then forLoop cx c sp x V M keep (.inl N)
    else forLoop cx c sp x V M keep (.inr (← loopBody cx n cr N))
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

/-! ### Generators  `[spec §15]`

A `gen fn f(ps) -> A, B = S` is a generator of `A` finishing with `B`: it is elaborated to a function
returning `U (gen A B R)` (`lib/gen.bc`), whose residual `R` is read off `B` as a div function's is
(`loopCxOf`). The call runs nothing: it returns `thunkv nu_in < S', abort >`, where `S'` is the
body elaborated to its **first observation** (the code up to the first `yield`, then what it
yields), and `abort` hands back the residual without running anything. On the body's spine:

* **`yield e; N`** is `return (inl (e, thunkv nu_in < N', abort >))`: the element, and the rest,
  which runs `N` only when it is observed.
* **A terminal** `T` finishes: `return (inr (inl T))`.
* **`for x in V { M }; N`** (`V` an iterator or a generator) and **`while c { M }; N`** are a
  generator by `unfold` over the loop's state (the iterator and the threaded variables, or the
  body's own generator while it runs), whose body `M` is itself a generator body that may `yield`
  and `break`. The loop's head starts an iteration; one that the head started and that ends
  without yielding is a skip, and one resumed after a `yield` starts the next at once. What
  follows the loop runs in its last step when it neither yields nor loops, and is sequenced by
  `gen_bind` otherwise.
* **A body that is code, one loop, and code after it that neither yields nor loops** is one
  `unfold` whose first state is the parameters (`splitLoop`).

This is the elaboration by nested binds, used where a body's state machine (the section *One
state machine per body* below, SPEC §15) does not apply; the machine is tried first.
* **A `yield` in a bound computation** (`x <- if c { yield e } else { … }; N`) takes `N` into
  the computation's arms, so that the `yield` is on the spine.

* **A borrow block whose body yields** is a delegation to the generator its body makes
  (`Parser.borrowBlock`), which the typing of the block rejects: its result is boxed at the
  block's lifetime, and a thunk has no outlives rule (SPEC §15, Self-reference).

A `yield` anywhere else, such as inside a value or a call's argument, is an error. -/

/-- A thunk's `<next, close>` consumes what it captures in both components: `close`, which does not
run `next`, binds each captured variable of `M` other than `keep` (the capabilities it hands
back), so that its destructor runs (SPEC §12). -/
def dropsFor (c : TCx) (keep : List String) (M : Comp) : String :=
  String.join ((latest c.locals).filterMap fun (y, _) =>
    if !keep.contains y && mentionsC y M then some s!"io_dr_{y} <- return {y};\n" else none)

/-- The bindings of a `fn`'s parameters at the start of its body (`Parser.fnRest`), before `T`. -/
def paramPrefix : Comp → Comp → Comp
  | .letPair sp x y V@(.var ..) M, T => .letPair sp x y V (paramPrefix M T)
  | .letUnit sp V@(.var ..) M, T => .letUnit sp V (paramPrefix M T)
  | .bind sp x A (.ret s V@(.var ..)) M lin, T => .bind sp x A (.ret s V) (paramPrefix M T) lin
  | _, T => T

/-- What a generator body is elaborated at: the element type `A`, and its result and residual. -/
structure GenCx where
  A : CVTy
  L : LoopCx
  /-- Types printed in the generator's context, its lifetime parameter by name. -/
  pp : CVTy → String := ppT
  /-- The generator's own result, which `return e` finishes it with, and the variables of its
  residual (`LoopCx.parts`). -/
  R0 : CVTy := L.B
  parts0 : List (List (String × CVTy)) := L.parts
  /-- In the body of a loop: a body with a `return` finishes with `inr (inr v)` for `return v`. -/
  inLoop : Bool := false

def GenCx.gTy (g : GenCx) : String := s!"gen ({g.pp g.A}) ({g.pp g.L.B}) ({g.pp g.L.R})"

/-- What the body finishes with for `return v`. -/
def GenCx.retS (g : GenCx) (v : String) : String := if g.inLoop then s!"inr (inr {v})" else v

/-- Bind the components of `v`, a value of the generator's result `g.R0`, by the names of its
residual (`g.parts0`), the others by fresh names; then the residual of the level `g` is built by
its names (`LoopCx.rSrc`). This is the `close` of a generator that has finished with `return v`. -/
def bindRet (g : GenCx) (v : String) : String := Id.run do
  let comps := spineT g.R0
  let mut parts := g.parts0
  let mut names : List String := []
  let mut inner := ""
  for (A, i) in comps.zip (List.range comps.length) do
    if isLinear A then
      match parts with
      | [(x, _)] :: ps => names := names ++ [x]; parts := ps
      | p :: ps =>
        let w := s!"{v}_c{i}"
        names := names ++ [w]; inner := inner ++ destructSrc w (p.map (·.1)); parts := ps
      | [] => names := names ++ [s!"{v}_n{i}"]
    else names := names ++ [s!"{v}_n{i}"]
  pure (destructSrc v names ++ inner)

/-- Bind the variables of each component of `K` from `v`, a residual `K * 1` (or `1`). -/
def destructR (v : String) (parts : List (List (String × CVTy))) : String :=
  if parts.isEmpty then s!"let () = {v};\n" else
    s!"let ({v}_k, {v}_u) = {v};\nlet () = {v}_u;\n" ++ destructParts s!"{v}_k" parts

/-- A generator's loop, planned: its condition (`while`) or iterator (its type, element, whether
it is a generator, what it finishes and closes with), the capability the iterator is made from,
the threaded variables (capabilities first), those the loop finishes with, the body's context,
and the body with its terminals going on (`inl`) with the threaded variables or breaking (`inr`)
with those it finishes with, and the typing context of the body. -/
structure GenLoop where
  cond : Option Val
  V : Val
  it : Option (CVTy × CVTy × Bool × CVTy × CVTy)
  cap : Option String
  svs : List (String × CVTy)
  ws : List (String × CVTy)
  /-- The threaded variables the loop finishes with: those what follows it reads, and the linear
  ones. A variable nothing after the loop reads is dropped where the loop ends, so a `break` does
  not name it: naming a persistent value there, after the body took it apart, would copy it. -/
  outs : List (String × CVTy)
  bcx : LoopCx
  bodyW : Comp
  cb : TCx
  /-- What follows the loop, when it has no `yield` and no loop: it runs in the loop's last step,
  and the loop finishes with its value. -/
  direct : Option Comp
  /-- The body has a `return`: it finishes with `inr (inr v)` for `return v`, and `inr (inl …)`
  after `break`. -/
  hasRet : Bool := false
  /-- `let r = for …`: the loop's value `r` and its type. -/
  keep : Option (String × CVTy) := none
  /-- What follows the loop (without the binding of `r`). -/
  rest : Comp

/-- `for x in V { M }; N` or `while c { M }; N` in a generator body: a generator by `unfold` over
the loop's state, then `gen_bind` of what follows. -/
def genLoopPlan (g : GenCx) (c : TCx) (sp : Span) (x : Ident) (V : Val) (M N : Comp) :
    SM GenLoop := do
  let cx := g.L
  let cond := match V with
    | .app _ (.sugar _ .while_) b => some b
    | _ => none
  if V.hasYield && cond.isNone then throw (yieldOffSpine (V.yieldAt.getD V.span))
  let M ← normExits divFuel M
  let hasRet := M.hasRet
  let V := V.takeLends.1
  -- `let r = for …; N`: the loop's value is bound to `r` in `N`.
  let (keep₀, N) := match N.forRes? with
    | some (r, _, N₀) => (some r, N₀)
    | none => (none, N)
  -- The iterator: its type, whether it is a generator, and what it finishes and closes with.
  let it ← match cond with
    | some _ => pure none
    | none => do
      let Vt ← match c.tyV V with
        | some Vt => pure Vt
        | none => throw ⟨V.span, "the type of the iterator of this `for` is not determined"⟩
      match iterOf Vt, genOf Vt with
      | some (E, Q, Q'), _ => pure (some (Vt, E, false, Q, Q'))
      | none, some (E, Q, Q') => pure (some (Vt, E, true, Q, Q'))
      | none, none => throw ⟨V.span, s!"`for` iterates over an iterator `U (iter A R R')` or a " ++
          s!"generator `U (gen A B R)`, but this has type `{ppT Vt}`"⟩
  let cs := cx.capNames
  let cap ← match cond with
    | some _ => pure none
    | none => match cs.filter (mentionsV · V) with
      | [] => pure none
      | [c] => pure (some c)
      | _ => throw ⟨V.span, "the iterator of a `for` is made from at most one capability"⟩
  let xs := match it with
    | some (_, E, _, _, _) => [(x.name, E)]
    | none => []
  -- `let c = for …` with `c` among what the generator hands back: the iterator hands `c` back
  -- when it finishes or is closed, as an iterator made from `c` does.
  let (cap, keep₀) := match keep₀ with
    | some r => if cs.contains r.name && (cap.isNone || cap == some r.name) then (some r.name, none)
      else (cap, keep₀)
    | none => (cap, keep₀)
  let keep : Option (String × CVTy) ← match keep₀, it with
    | none, _ => pure none
    | some r, some (_, _, _, Q, _) => do
      if let some c := cap then
        throw ⟨r.span, s!"the iterator of this `for` is made from `{c}`, which it hands back " ++
          "when it finishes: the loop's value is not bound"⟩
      pure (some (r.name, Q))
    | some r, none => throw ⟨r.span, "a `while` has no value"⟩
  checkBreaks M (keep.map (·.2))
  -- What follows runs in the loop's last step when it neither yields nor loops (a `for`, or a
  -- call of a div function in direct style).
  let cN := match keep with
    | some (r, T) => c.push r (some T)
    | none => c
  let direct := if N.yieldsOrLoops || (loopsAt cN none N).isSome then none else some (if g.inLoop then N else stripRet N)
  if hasRet then if let some c := cap then
    throw ⟨sp, s!"a `return` inside a `for` over an iterator made from `{c}` cannot hand `{c}` " ++
      "back: the iterator holds it until the loop ends. `break`, and `return` after the loop"⟩
  -- A variable the body reads or assigns (a `let mut` rebound in it) is threaded.
  let reads (y : String) : Bool := mentionsC y M || M.rebinds y ||
    (cond.map (mentionsV y)).getD false || (direct.map (mentionsC y)).getD false
  let used := (latest c.locals).filter fun (y, _) => !cs.contains y && y != x.name && reads y
  let ws ← used.mapM fun (y, T) => match T with
    | some T => pure (y, T)
    | none => throw ⟨sp, s!"the loop threads `{y}`, whose type is not determined: ascribe it"⟩
  let th := cx.caps.filter (some ·.1 != cap)
  let svs := th ++ ws
  let sv := svs.map (·.1)
  let svT := tupleT (svs.map (·.2))
  let outs := ws.filter fun (y, T) => isLinear T || mentionsC y N
  -- What the loop finishes with: the capabilities, the variables what follows reads, and the
  -- loop's value when it is bound.
  let bvT := tupleT ((th ++ outs ++ keep.toList).map (·.2))
  let bvs := (th ++ outs).map (·.1)
  -- The body: a generator of `A` finishing with the threaded variables, `inl` to go on and `inr`
  -- after `break` (with those the loop finishes with); its residual is the threaded capabilities.
  let lin := svs.filter (isLinear ·.2)
  -- A `return` leaves this loop and every loop around it: what the loop threads and has no
  -- destructor must be what the returned value hands back.
  if hasRet then
    let names := g.parts0.flatten.map (·.1)
    if let some (y, _) := lin.find? (fun (y, _) => !names.contains y) then
      throw ⟨sp, s!"a `return` inside this loop leaves `{y}` behind, which has no destructor: " ++
        "the generator's result must hand it back"⟩
  let Bb : CVTy := if hasRet then .sum svT (.sum bvT g.R0) else .sum svT bvT
  let bcx : LoopCx := if lin.isEmpty then ⟨Bb, .unit, .unit, [], true⟩ else
    ⟨Bb, .tensor (tupleT (lin.map (·.2))) .unit, tupleT (lin.map (·.2)), lin.map ([·]), true⟩
  let brkV (tsp : Span) (w : Val) : Val := if hasRet then .inr tsp (.inl tsp w) else .inr tsp w
  let brkVal (tsp : Span) (e : Val) : Val :=
    brkV tsp (tupleVals tsp (bvs.map (Val.var tsp ·) ++ (if keep.isSome then [e] else [])))
  let bodyW := wrapTail (fun
    | .ret tsp (.sugar _ .brk) => .ret tsp (brkVal tsp (.unit tsp))
    | .ret tsp (.app _ (.sugar _ .brk) e) => .ret tsp (brkVal tsp e)
    | .ret tsp (.app _ (.sugar _ .retE) v) => .ret tsp (.inr tsp (.inr tsp v))
    | T => .bind T.span ⟨"io_u", T.span⟩ none T (.ret T.span (.inl T.span (tupleVal T.span sv))) false) M
  let cb := xs.foldl (fun c (y, E) => c.push y (some E)) (svs.foldl (fun c (y, T) => c.push y (some T)) c)
  pure ⟨cond, V, it, cap, svs, ws, outs, bcx, bodyW, cb, direct, hasRet, keep, N⟩

/-- The core of a generator's loop, around its elaborated body and what follows it. -/
def genLoopSrc (g : GenCx) (c : TCx) (sp : Span) (x : Ident) (P : GenLoop) (body N N' : Comp)
    (start : Option (String × String × (Comp → Comp) × Comp) := none) : SM Comp := do
  let cx := g.L
  let ppT := g.pp
  -- A loop that starts a generator's body has a state before it, the parameter, whose
  -- observation runs the code before the loop (`start`): the loop's own states are `inr`.
  let stv (v : String) : String := if start.isSome then s!"(inr {v})" else v
  let ⟨cond, V, it, cap, svs, ws, outs, bcx, _, _, direct, hasRet, keep, _⟩ := P
  let bg : GenCx := { g with L := bcx, inLoop := true }
  let sv := svs.map (·.1)
  let svT := tupleT (svs.map (·.2))
  let svTs := s!"({ppT svT})"
  let svSrc := tupleSrc sv
  -- What a `break` hands on: the capabilities and the variables the loop finishes with.
  let bv := svs.filter (fun (y, _) => !ws.any (·.1 == y)) ++ outs ++ keep.toList |>.map (·.1)
  let wn := (outs ++ keep.toList).map (·.1)
  let wT := tupleTySrc ((outs ++ keep.toList).map (ppT ·.2))
  -- The loop finishes with what follows it (`direct`), or with the capabilities and the variables
  -- it hands on; after a `return`, with the returned value (`inr`).
  let fin := if direct.isSome then s!"({ppT cx.B})"
    else if hasRet then s!"((({ppT cx.K}) * {wT}) + ({ppT g.R0}))" else s!"(({ppT cx.K}) * {wT})"
  let finish := if direct.isSome then s!"io_v : {fin} <- force io_hole_fin;\nreturn (inr (inl io_v))"
    else if hasRet then s!"return (inr (inl (inl ({cx.kSrc}, {tupleSrc wn}))))"
    else s!"return (inr (inl ({cx.kSrc}, {tupleSrc wn})))"
  let A := ppT g.A
  let R := ppT cx.R
  let gb := bg.gTy
  let obsB := s!"({A}) * U ({gb}) + ({ppT bcx.B}) + U ({gb})"
  let ds := destructSrc "io_st" sv
  let brk (itClose : String) := s!"{destructSrc "io_sv" bv}{itClose}{finish}"
  let closeIt := match it with
    | some (_, _, _, _, Q') => s!"io_c <- (nu_out (force io_it)).2;\n{bindCap cap Q' "io_c"}"
    | none => ""
  -- After `return v`: the iterator closed, the loop finishes with `v`.
  let retK := if direct.isSome then
      s!"{closeIt}io_v : {fin} <- return ({g.retS "io_rv"});\nreturn (inr (inl io_v))"
    else s!"{closeIt}return (inr (inl (inr io_rv)))"
  -- The body finished to leave the loop: `break`, or `return` when the body has one.
  let ended := if hasRet then s!"inr io_x -> case io_x \{ inl io_sv -> {brk closeIt} | inr io_rv -> {retK} }"
    else s!"inr io_sv -> {brk closeIt}"
  -- One observation of the body's generator `io_b`, with the loop's state rebuilt around it; the
  -- body finishing to go on is `cont`.
  let step (wrap : String → String) (cont : String) :=
    s!"case io_b \{
  inl io_y -> let (io_e, io_g2) = io_y; return (inl (io_e, {wrap "io_g2"}))
| inr io_bd ->
    case io_bd \{
      inl io_r ->
        case io_r \{
          inl io_sv -> {cont}
        | {ended}
        }
    | inr io_g2 -> return (inr (inr {wrap "io_g2"}))
    }
}"
  -- The loop's head, `io_head`, starts an iteration from the loop's variables (and iterator): it
  -- runs the body up to its first observation. An iteration that ends without yielding is a skip
  -- when it started at the head, and starts the next one at once when it resumed the body: so a
  -- loop whose body yields once per iteration yields at every observation.
  let (St, Sa, head, resume, close, s0) := match it, cond with
    | some (Vt, _, isGen, Q, _), _ =>
      let It := ppT Vt
      let St := s!"(({It}) * {svTs}) + (U ({gb}) * ({It}))"
      let wrap (g2 : String) := stv s!"(inr ({g2}, io_it))"
      let ended := match keep with
        | some (r, _) => s!"{r} <- return io_q;\n{finish}"
        | none => s!"{bindCap cap Q "io_q"}{finish}"
      let fin := if isGen then s!"case io_d \{
          inl io_q -> {ended}
        | inr io_it -> return (inr (inr {stv s!"(inl (io_it, {svSrc}))"}))
        }" else s!"io_q <- return io_d;\n{ended}"
      let head := s!"let (io_it, io_st) = io_a;
{ds}io_o <- (nu_out (force io_it)).1;
case io_o \{
  inl io_p ->
    let ({x.name}, io_it) = io_p;
    io_b : {obsB} <- force io_hole_body;
    {step wrap s!"return (inr (inr {stv "(inl (io_it, io_sv))"}))"}
| inr io_d ->
    {fin}
}"
      let resume := s!"let (io_g, io_it) = io_a;
io_b <- (nu_out (force io_g)).1;
{step wrap "return ((unbang io_head) (io_it, io_sv))"}"
      let close := s!"case io_s \{
  inl io_a ->
    let (io_it, io_st) = io_a;
    {ds}{closeIt}return {cx.rSrc}
| inr io_a ->
    let (io_g, io_it) = io_a;
    io_rb <- (nu_out (force io_g)).2;
    {destructR "io_rb" bcx.parts}{closeIt}return {cx.rSrc}
}"
      (St, s!"({It}) * {svTs}", head, resume, close, "(io_hole_v, " ++ svSrc ++ ")")
    | none, _ =>
      let St := s!"{svTs} + U ({gb})"
      let wrap (g2 : String) := stv s!"(inr {g2})"
      let head := s!"io_st <- return io_a;
{ds}case io_hole_c \{
  inl io_f -> {finish}
| inr io_t ->
    io_b : {obsB} <- force io_hole_body;
    {step wrap s!"return (inr (inr {stv "(inl io_sv)"}))"}
}"
      let resume := s!"io_g <- return io_a;
io_b <- (nu_out (force io_g)).1;
{step wrap "return ((unbang io_head) io_sv)"}"
      let close := s!"case io_s \{
  inl io_st -> {ds}return {cx.rSrc}
| inr io_g ->
    io_rb <- (nu_out (force io_g)).2;
    {destructR "io_rb" bcx.parts}return {cx.rSrc}
}"
      (St, svTs, head, resume, close, svSrc)
  let next := s!"case io_s \{
  inl io_a -> return ((unbang io_head) io_a)
| inr io_a ->
    {resume}
}"
  let (St, next, close, s0) := match start with
    | some (p, Pt, _, _) =>
      (s!"({Pt}) + ({St})", s!"case io_s \{ inl io_p0 -> force io_hole_start | inr io_s -> {next} }",
        s!"case io_s \{ inl io_p0 -> force io_hole_stclose | inr io_s -> {close} }", p)
    | none => (St, next, close, s0)
  let obsL := s!"({A}) * ({St}) + ({fin} + ({St}))"
  -- What follows the loop, given what the loop finished with; after a `return`, the generator
  -- that finishes with the returned value at once.
  let goOn₀ := s!"let (io_ka, io_wa) = io_a;
      {destructParts "io_ka" cx.parts}{destructSrc "io_wa" wn}return (thunkv nu_in < force io_hole_rest, {dropsFor c cx.capNames N}return {cx.rSrc} >)"
  let goOn := if hasRet then s!"case io_a \{
      inl io_a -> {goOn₀}
    | inr io_rv -> {dropsFor c cx.capNames N}return (thunkv nu_in < return (inr (inl ({g.retS "io_rv"}))), {bindRet g "io_rv"}return {cx.rSrc} >)
    }" else goOn₀
  let src := s!"io_head : !(({Sa}) => {obsL}) <-
  return (!thunkv fun (io_a : {Sa}) -> {head});
io_step : !U ({St} -o F ({obsL}) & F ({R})) <-
  return (!thunkv fun (io_s : {St}) -> < {next}, {close} >);
io_f <- return (unbang (unfold[gen ({A}) {fin} ({R}), {St}] io_step));
io_s0 : {St} <- return (inl {s0});
" ++ if start.isSome then "return (thunkv nu_in < (nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2 >)"
  else "io_l <- return (thunkv nu_in < (nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2 >);
" ++ if direct.isSome then "(nu_out (force io_l)).1" else s!"io_gb <- return (gen_bind[{A}, {fin}, ({R}), ({ppT cx.B}), ({R})] (io_l, thunkv
  < fun (io_a : {fin}) ->
      {goOn},
    fun (io_r : {R}) -> {dropsFor c (cx.capNames ++ ws.map (·.1) ++ [x.name]) N}return io_r >));
(nu_out (force io_gb)).1"
  let what := if cond.isSome then "`while`" else "`for` in a generator"
  let L ← template sp what src
  -- The start: the code before the loop, then the loop's head on its first state.
  let (stCode, stClose) ← match start with
    | some (p, _, pre, cl) => do
      let go ← template sp what (if cond.isSome then s!"return ((unbang io_head) {svSrc})"
        else s!"return ((unbang io_head) (io_hole_v, {svSrc}))")
      let go := go.fill (fun v => if v == "io_hole_v" then some V else none) (fun _ => none)
      let pb (M : Comp) : Comp := .bind sp ⟨p, sp⟩ none (.ret sp (.var sp "io_p0")) M false
      pure (some (pb (pre go)), some (pb cl))
    | none => pure (none, none)
  pure (L.fill (fun v => if v == "io_hole_v" then some V
      else if v == "io_hole_c" then cond else none)
    (fun v => if v == "io_hole_body" then some body else if v == "io_hole_rest" then some N'
      else if v == "io_hole_fin" then direct else if v == "io_hole_start" then stCode
      else if v == "io_hole_stclose" then stClose else none))
/-- `x <- M; N` in a generator's body, where `M` computes a computation of its own that the
generator runs before going on: a loop, from a call of a div function in direct style
(`gen_bind_loop`), or another generator, from `yield from` (`gen_bind`). `call` computes it, its
argument with the lent capability `lend` replaced; `Bf` and `Rf` are what it finishes and closes
with; `N'` is the rest elaborated to its first observation in the context `cN` (with `x` bound).
The continuation binds `x` (and the lent capability) and is the generator of the rest; closed
during the call, it turns the call's residual into the generator's. The result is the bind's first
observation.  `[spec §15]` -/
def genDelegate (g : GenCx) (c cN : TCx) (sp : Span) (x : Ident) (A : Option VTy) (call : Comp)
    (lend : Option Ident) (isGen : Bool) (Bf Rf : CVTy) (N N' : Comp) : SM Comp := do
  let cx := g.L
  let bindX := match lend, A with
    | some l, _ => match Bf with
      | .tensor .. => s!"let ({l.name}, {x.name}) = io_a;"
      | _ => s!"{l.name} <- return io_a; {x.name} <- return ();"
    | none, some A => s!"{x.name} : {A.pp} <- return io_a;"
    | none, none => s!"{x.name} <- return io_a;"
  let drops := dropsFor c cx.capNames N
  let abort ← match Rf, lend with
    | .unit, _ => pure s!"let () = io_r; {drops}return {cx.rSrc}"
    | .tensor _ .unit, some l =>
      if cx.capNames.contains l.name then
        pure s!"let ({l.name}, io_u) = io_r; {drops}return {cx.rSrc}"
      else throw ⟨sp, s!"the call lends `{l.name}`, which is not among what this generator " ++
          "hands back"⟩
    | _, some l =>
      -- A generator lent the capability hands it back as its residual.
      if cx.capNames.contains l.name then pure s!"{l.name} <- return io_r; {drops}return {cx.rSrc}"
      else throw ⟨sp, s!"the call lends `{l.name}`, which is not among what this generator " ++
          "hands back"⟩
    | _, _ =>
      if Rf = cx.R then pure s!"{drops}return io_r" else
      throw ⟨sp, s!"a call whose {if isGen then "generator" else "loop"} hands back `{ppT Rf}` " ++
        "when closed must lend what it hands back with `&mut c`, or hand back what this " ++
        s!"generator hands back, `{ppT cx.R}` (SPEC §14)"⟩
  let fn := if isGen then "gen_bind" else "gen_bind_loop"
  let src := s!"io_m <- force io_hole_call;
io_gb <- return ({fn}[{g.pp g.A}, {g.pp Bf}, {g.pp Rf}, {g.pp cx.B}, {g.pp cx.R}] (io_m, thunkv
  < fun (io_a : {g.pp Bf}) -> {bindX}
      return (thunkv nu_in < force io_hole_rest, {dropsFor cN cx.capNames N}return {cx.rSrc} >),
    fun (io_r : {g.pp Rf}) -> {abort} >));
(nu_out (force io_gb)).1"
  let what := if isGen then "`yield from` (`gen_bind`)" else
    "a call of a div function in a generator (`gen_bind_loop`)"
  let L ← template sp what src
  pure (L.fill (fun _ => none)
    (fun n => if n == "io_hole_call" then some call else if n == "io_hole_rest" then some N'
      else none))

mutual
/-- A generator body, elaborated to its first observation: code of type
`F (A * U (gen A B R) + (B + U (gen A B R)))`. -/
def genBody (g : GenCx) : Nat → TCx → Comp → SM Comp
  | 0, _, M => throw ⟨M.span, "internal error: a generator body nested too deeply"⟩
  | n + 1, c, .bind sp x A (.ret ysp (.app ksp (.sugar k .yield_) e)) N lin => do
    if e.hasYield then throw (yieldOffSpine (e.yieldAt.getD e.span))
    -- Calls of div functions run in direct style in the element are lifted out first.
    if (callIn c divFuel (some g.A) e).isSome then
      let (e', bs) := liftAll e
      return (← genBody g n c (chain bs (.bind sp x A (.ret ysp (.app ksp (.sugar k .yield_) e')) N lin)))
    let N' ← genBody g n (c.push x.name (some .unit)) N
    let L ← template ysp "`yield`" s!"return (inl (io_hole_e, thunkv nu_in < force io_hole_rest, {dropsFor c g.L.capNames N}return {g.L.rSrc} >))"
    -- The rest binds the `yield`'s own result, `()`, to the name the program gave it.
    let rest := Comp.bind sp x A (.ret ysp (.unit ysp)) N' lin
    pure (L.fill (fun v => if v == "io_hole_e" then some e else none)
      (fun v => if v == "io_hole_rest" then some rest else none))
  | n + 1, c, .bind sp x A (.ret ysp (.app _ (.sugar _ .yieldFrom) e)) N _ => do
    -- `x <- yield from e; N`: the generator `e` runs first, and `x` is what it finishes with.
    if e.hasYield then throw (yieldOffSpine (e.yieldAt.getD e.span))
    let (e', lends) := e.takeLends
    let lend ← match lends with
      | [] => pure none
      | [l] => pure (some l)
      | _ => throw ⟨ysp, "a call lends at most one capability with `&mut`"⟩
    let Te ← match c.tyV e' with
      | some T => pure T
      | none => throw ⟨e.span, "the type of the generator of this `yield from` is not determined"⟩
    let (Ae, Bf, Rf) ← match genOf Te with
      | some t => pure t
      | none => throw ⟨e.span, s!"`yield from` delegates to a generator `U (gen A B R)`, but " ++
          s!"this has type `{ppT Te}`"⟩
    unless Ae == g.A do
      throw ⟨e.span, s!"this generator yields `{ppT Ae}`, and the one it is delegated from " ++
        s!"yields `{ppT g.A}`"⟩
    let c' := match lend, Bf with
      | some l, .tensor K X => (c.push l.name (some K)).push x.name (some X)
      | some l, K => (c.push l.name (some K)).push x.name (some .unit)
      | none, _ => c.push x.name ((A.bind c.elabV).orElse fun _ => some Bf)
    let N' ← genBody g n c' N
    genDelegate g c c' sp x A (.ret ysp e') lend true Bf Rf N N'
  | n + 1, c, .bind sp x A M N lin => do
    if M.hasYield then
      -- A head that yields: what follows goes into it (a commuting conversion), so the `yield`
      -- is on the spine. A `match` or `if` duplicates what follows into its arms.
      match M with
      | .case csp V y M₁ z M₂ =>
        if mentionsC y.name N || mentionsC z.name N then throw (yieldOffSpine (M.yieldAt.getD M.span))
        return (← genBody g n c (.case csp V y (.bind sp x A M₁ N lin) z (.bind sp x A M₂ N lin)))
      | .bind bsp y B M₁ M₂ lin' =>
        if mentionsC y.name N then throw (yieldOffSpine (M.yieldAt.getD M.span))
        return (← genBody g n c (.bind bsp y B M₁ (.bind sp x A M₂ N lin) lin'))
      | .letPair lsp y z V M₁ =>
        if mentionsC y.name N || mentionsC z.name N then throw (yieldOffSpine (M.yieldAt.getD M.span))
        return (← genBody g n c (.letPair lsp y z V (.bind sp x A M₁ N lin)))
      | .letUnit lsp V M₁ => return (← genBody g n c (.letUnit lsp V (.bind sp x A M₁ N lin)))
      | _ => throw (yieldOffSpine (M.yieldAt.getD M.span))
    let exp := A.bind c.elabV
    -- Calls of div functions run in direct style below the top of the bound value are lifted
    -- out first, as in a div body.
    if let .ret sp' V := M then
      if (nestedCall c exp V).isSome then
        let (V', bs) := liftBelow V
        return (← genBody g n c (chain bs (.bind sp x A (.ret sp' V') N lin)))
    let (M', lends) := M.takeLends
    match (match M' with | .ret _ V => directCall c exp V | _ => none) with
    | some (Bf, Rf) =>
      -- A call of a div function in direct style: its loop runs inside the generator, each turn
      -- a skip.
      let lend ← match lends with
        | [] => pure none
        | [l] => pure (some l)
        | _ => throw ⟨sp, "a call lends at most one capability with `&mut`"⟩
      let c' := match lend, Bf with
        | some l, .tensor K Vx => (c.push l.name (some K)).push x.name (exp <|> some Vx)
        | some l, _ => (c.push l.name none).push x.name exp
        | none, _ => c.push x.name (exp <|> some Bf)
      let N' ← genBody g n c' N
      genDelegate g c c' sp x A M' lend false Bf Rf N N'
    | none =>
      let N' ← genBody g n (c.push x.name (bindTy c A M)) N
      pure (.bind sp x A M N' lin)
  | n + 1, c, .letUnit sp V M => do
    if V.hasYield then throw (yieldOffSpine (V.yieldAt.getD V.span))
    if (callIn c divFuel (some .unit) V).isSome then
      let (V', bs) := liftAll V
      return (← genBody g n c (chain bs (.letUnit sp V' M)))
    return .letUnit sp V (← genBody g n c M)
  | n + 1, c, .letPair sp x y V M => do
    if V.hasYield then throw (yieldOffSpine (V.yieldAt.getD V.span))
    if (callIn c divFuel none V).isSome then
      let (V', bs) := liftAll V
      return (← genBody g n c (chain bs (.letPair sp x y V' M)))
    let (Ax, Ay) := pairTys c V
    return .letPair sp x y V (← genBody g n ((c.push x.name Ax).push y.name Ay) M)
  | n + 1, c, .case sp V x M y N => do
    if V.hasYield then throw (yieldOffSpine (V.yieldAt.getD V.span))
    if (callIn c divFuel none V).isSome then
      let (V', bs) := liftAll V
      return (← genBody g n c (chain bs (.case sp V' x M y N)))
    let (Ax, Ay) := sumTys c V
    return .case sp V x (← genBody g n (c.push x.name Ax) M) y (← genBody g n (c.push y.name Ay) N)
  | n + 1, c, .for_ sp x V M N => genLoop g n c sp x V M N
  | n + 1, c, T@(.ret sp (.app _ (.sugar _ .yield_) _)) =>
    -- A `yield` last: yield, then finish with `()`.
    genBody g n c (.bind sp ⟨"io_y", sp⟩ none T (.ret sp (.unit sp)) false)
  | n + 1, c, T@(.ret sp (.app _ (.sugar _ .yieldFrom) _)) =>
    -- A `yield from` last: the generator finishes with what the delegate finishes with.
    genBody g n c (.bind sp ⟨"io_t", sp⟩ none T (.ret sp (.var sp "io_t")) false)
  | _ + 1, _, .ret sp (.app _ (.sugar _ .retE) v) => do
    -- `return v`: the generator finishes with `v`.
    if v.hasYield then throw (yieldOffSpine (v.yieldAt.getD v.span))
    let L ← template sp "`return`" s!"io_v : {g.pp g.L.B} <- return ({g.retS "io_hole_rv"});
return (inr (inl io_v))"
    pure (L.fill (fun x => if x == "io_hole_rv" then some v else none) (fun _ => none))
  | _ + 1, _, .ret sp (.sugar _ .brk) | _ + 1, _, .ret sp (.app _ (.sugar _ .brk) _) =>
    throw ⟨sp, "`break` is outside every loop"⟩
  | n + 1, c, T => do
    if T.hasYield then throw (yieldOffSpine (T.yieldAt.getD T.span))
    -- A call of a div function in direct style last: bound, then finished with.
    if let .ret sp V := T then
      if (nestedCall c (some g.L.B) V).isSome then
        let (V', bs) := liftBelow V
        return (← genBody g n c (chain bs (.ret sp V')))
    let (T', _) := T.takeLends
    if (match T' with | .ret _ V => directCall c (some g.L.B) V | _ => none).isSome then
      return (← genBody g n c (.bind T.span ⟨"io_t", T.span⟩ none T (.ret T.span (.var T.span "io_t")) false))
    let L ← template T.span "a generator's result" s!"io_v : {g.pp g.L.B} <- force io_hole_t;
return (inr (inl io_v))"
    pure (L.fill (fun _ => none) (fun v => if v == "io_hole_t" then some T else none))

/-- `for x in V { M }; N` or `while c { M }; N` in a generator body: a generator by `unfold` over
the loop's state, then `gen_bind` of what follows. -/
def genLoop (g : GenCx) : Nat → TCx → Span → Ident → Val → Comp → Comp → SM Comp
  | 0, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a generator body nested too deeply"⟩
  | n + 1, c, sp, x, V, M, N => do
    let P ← genLoopPlan g c sp x V M N
    let body ← genBody { g with L := P.bcx, inLoop := true } n P.cb P.bodyW
    let cr := match P.keep with
      | some (r, T) => c.push r (some T)
      | none => c
    let N' ← if P.direct.isSome then pure P.rest else genBody g n cr P.rest
    genLoopSrc g c sp x P body P.rest N'
end

/-- The names a `fn`'s body binds from its parameter before the rest (`paramPrefix`), with their
types. -/
def paramsOf : Nat → TCx → Comp → List (String × Option CVTy)
  | 0, _, _ => []
  | n + 1, c, .letPair _ x y V@(.var ..) M =>
    let (Ax, Ay) := pairTys c V
    (x.name, Ax) :: (y.name, Ay) :: paramsOf n ((c.push x.name Ax).push y.name Ay) M
  | n + 1, c, .bind _ x A M@(.ret _ (.var ..)) N _ =>
    let T := bindTy c A M
    (x.name, T) :: paramsOf n (c.push x.name T) N
  | n + 1, c, .letUnit _ _ M => paramsOf n c M
  | _, _, _ => []

/-- Closing a generator before it starts: it closes the generators and iterators it was given
(`gs`, with their types), to hand back what they hold. Each variable of the residual that is not
among `gs` is bound from the residual of the first of them that hands back its type. The code,
and the generators it closes. -/
def closeGiven (cx : LoopCx) (gs : List (String × Option CVTy)) : String × List String := Id.run do
  let names := gs.map (·.1)
  let mut used : List String := []
  let mut out := ""
  for (p, T) in cx.caps do
    if names.contains p then continue
    let hands (g : String) (Tg : Option CVTy) : Bool := !used.contains g && match Tg with
      | some Tg => (((genOf Tg).map (·.2.2)).orElse fun _ => (iterOf Tg).map (·.2.2)) == some T
      | none => false
    match gs.find? (fun (g, Tg) => hands g Tg) with
    | some (g, _) => used := g :: used; out := out ++ s!"{p} <- (nu_out (force {g})).2;\n"
    | none => pure ()
  pure (out, used)

/-! ### One state machine per body  `[spec §15, §14]`

A generator body, or a div body, is elaborated to **one `unfold`**: its state is a sum with one
summand per **resumption point** (a `yield`'s continuation, a loop's head, a `yield from` or a
call of a div function in progress), each holding the variables live there, and its step is one
code with a `case` on the state. Every observation is then a call of known code: no closure is
dispatched on, and no bind is nested in another.

* **The code between points** is the program's own, with its transitions replaced: a `yield e`
  returns `e` with the state of its continuation; reaching a loop's head, a delegation or a call
  is a **move** to its point; `break` closes the loop's iterator and moves to the code after the
  loop (its **join**); the end of a loop's body moves back to its head; a terminal finishes.
* **A move** calls the point's code (`io_run_k`, a `!` function) when that runs in the same
  observation, and otherwise returns the point's state as a skip. A function calls only the
  functions of points after it in the body, so none calls itself: a move back to a loop's head
  from the code of a point inside the loop is a skip, and one from a `yield`'s continuation (code
  of the step itself) is a call, so a loop whose body yields once per iteration yields at every
  observation. In a div body every move to a summand is a skip, so each iteration of a loop is
  one observation, as with the delay bind.
* **The residual** is handed back by name at every summand: its `close` closes what the state
  holds (the iterators of the loops around it, the delegate or the call's loop), binding the
  capabilities they hand back, and returns the residual from the names.
* **A generator runs nothing when called**: its first state holds the parameters (or what a
  `gen { … }` block captures). **A div body runs its code up to its first point when called**,
  and returns the machine at that point (`io_mk`), as `div_bind` did.

A shape the machine does not cover is elaborated as before (`genBody`, `loopBody`). -/

/-- A resumption point of a body's machine, or a join. -/
structure MPoint where
  id : Nat
  /-- Its place in the body: the functions are defined last to first, and a function calls only
  the functions of later points. -/
  pos : Nat
  /-- A summand of the state: the machine may stop here between observations. A join is not. -/
  summand : Bool
  /-- It has a function of its own, `io_run_{id}`. -/
  fn : Bool
  vars : List (String × CVTy)
  /-- The sugar it comes from, where errors in its code are reported. -/
  sp : Span
  what : String
  code : Comp := .top Span.none
  close : Comp := .top Span.none

/-- What a state holds that must be closed: a loop's iterator, a delegate, or a call's loop, by
its variable, with the code that closes it and binds the capabilities it hands back. -/
structure MHeld where
  v : String
  T : CVTy
  closeSrc : String
  caps : List String

/-- A loop around the code being elaborated. -/
structure MLoop where
  head : Nat
  held : Option MHeld
  needs : List String
  keep : Option (String × CVTy)
  join : Option Nat

/-- What a machine's code is elaborated at. -/
structure MCx where
  gen : Bool
  A : CVTy
  L : LoopCx
  pp : CVTy → String
  loops : List MLoop := []
  /-- What the loops around hold, innermost first. -/
  held : List MHeld := []
  /-- The place of the function whose code this is; none in the step's own code. -/
  cur : Option Nat := none
  /-- In a div body's code before its first point, run when it is called. -/
  pre : Bool := false

structure MSt where
  pts : Array MPoint := #[]
  pos : Nat := 0

abbrev MM := StateT MSt SM

def mNew (sp : Span) (what : String) (summand fn : Bool) (vars : List (String × CVTy)) : MM Nat := do
  let st ← get
  let id := st.pts.size
  set { st with pts := st.pts.push { id, pos := st.pos, summand, fn, vars, sp, what },
                pos := st.pos + 1 }
  pure id

def mSet (id : Nat) (code close : Comp) : MM Unit :=
  modify fun st => { st with pts := st.pts.modify id fun p => { p with code, close } }

def mSetPos (id : Nat) : MM Unit :=
  modify fun st => { st with pts := st.pts.modify id fun p => { p with pos := st.pos }, pos := st.pos + 1 }

def mPt (id : Nat) : MM MPoint := do
  match (← get).pts[id]? with
  | some p => pure p
  | none => throw ⟨Span.none, "internal error: a machine point"⟩

def mTemplate (sp : Span) (what src : String) (vs : List (String × Val)) (cs : List (String × Comp)) :
    MM Comp := do
  let L ← (template sp what src : SM Comp)
  pure (L.fill (fun v => vs.lookup v) (fun v => cs.lookup v))

/-- `M` with each terminal that goes on (the end of a loop's body, or a `break`) also naming
`needs`: what a point inside the loop must carry for the loop's next iteration. -/
def augment (needs : List String) (M : Comp) : Comp :=
  if needs.isEmpty then M else wrapTail (fun
    | T@(.ret _ (.app _ (.sugar _ .retE) _)) => T
    | T => .bind T.span ⟨"io_u", T.span⟩ none T (.ret T.span (tupleVal T.span needs)) false) M

def MCx.restOf (m : MCx) (M : Comp) : Comp := match m.loops with
  | [] => M
  | l :: _ => augment l.needs M

/-- The extern slots of a context, with their types. -/
def mExterns (c : TCx) : List (String × CVTy) :=
  let vs := c.E.vars.zip c.T
  (vs.drop (vs.length - c.E.nExt)).filterMap fun (x, T) => x.map (·, T)

/-- The locals, other than capabilities and `excl`, that `rest` uses, with their types. -/
def mLive (m : MCx) (c : TCx) (rest : Comp) (excl : List String) : MM (List (String × CVTy)) := do
  let caps := m.L.capNames
  for (y, T) in mExterns c do
    if !T.persistent && !caps.contains y && mentionsC y rest && !c.locals.any (·.1 == y) then
      throw ⟨rest.span, s!"machine: the extern `{y}` is not a capability of the body"⟩
  (latest c.locals).filterMapM fun (y, T) =>
    if caps.contains y || excl.contains y || !mentionsC y rest then pure none
    else match T with
      | some T => pure (some (y, T))
      | none => throw ⟨rest.span, s!"machine: the type of `{y}` is not determined"⟩

/-- The state at a point that holds `own` besides what the loops around hold, before `rest`. -/
def mVars (m : MCx) (c : TCx) (own : List MHeld) (rest : Comp) (excl : List String) :
    MM (List (String × CVTy)) := do
  let held := own ++ m.held
  let hcaps := held.flatMap (·.caps)
  let hv := held.reverse.map fun h => (h.v, h.T)
  let caps := m.L.caps.filter fun (y, _) => !hcaps.contains y && !excl.contains y
  pure (hv ++ caps ++ (← mLive m c (m.restOf rest) excl))

/-- A state value: the injection of point `id`'s tuple, resolved when the summands are known. -/
def mInj (sp : Span) (id : Nat) (vars : List (String × CVTy)) : Val :=
  .app sp (.var sp s!"io_inj_{id}") (tupleVal sp (vars.map (·.1)))

/-- A skip to the state `s`. -/
def MCx.skip (m : MCx) (sp : Span) (s : Val) : Val := if m.gen then .inr sp (.inr sp s) else .inr sp s

/-- A move to point `q`, from the code of `m`. -/
def mGoto (m : MCx) (sp : Span) (q : Nat) : MM Comp := do
  let p ← mPt q
  if m.pre then
    return .ret sp (.app sp (.unbang sp (.var sp "io_mk")) (mInj sp q p.vars))
  let later := match m.cur with
    | none => true
    | some k => k < p.pos
  let call := p.fn && (!p.summand || (m.gen && later))
  if call then return .ret sp (.app sp (.unbang sp (.var sp s!"io_run_{q}")) (tupleVal sp (p.vars.map (·.1))))
  if !p.summand then throw ⟨sp, "internal error: a join reached by a skip"⟩
  pure (.ret sp (m.skip sp (mInj sp q p.vars)))

/-- The `close` of a state that holds `held` (innermost first): each closed, then the residual. -/
def mClose (m : MCx) (sp : Span) (what : String) (held : List MHeld) : MM Comp :=
  mTemplate sp what (String.join (held.map (·.closeSrc)) ++ s!"return {m.L.rSrc}")
    [] []

/-- The machine's finish with the value `T` computes. -/
def mFinish (m : MCx) (T : Comp) : MM Comp := do
  if m.pre then return (← (dret m.L T : SM Comp))
  let fin := if m.gen then "inr (inl io_v)" else "inl io_v"
  let L ← mTemplate T.span "a body's result" s!"io_v : {m.pp m.L.B} <- force io_hole_t;\nreturn ({fin})"
    [] [("io_hole_t", T)]
  match T.takeLends.2, L with
  | [], _ => pure L
  | _, .bind sp x _ M N lin => pure (.bind sp x none M N lin)
  | _, L => pure L

/-- The residual `io_r` of a delegate or a call closed early (`Rf`), bound by name: the lent
capability, nothing, or the body's own residual; and the capabilities it holds. -/
def mAbort (m : MCx) (sp : Span) (lend : Option Ident) (Rf : CVTy) : MM (String × List String) := do
  let cx := m.L
  -- A lent place other than a capability (a borrowed owner) comes back in the result only.
  match lend.filter (cx.capNames.contains ·.name) with
  | some l =>
    match Rf with
    | .tensor _ .unit => pure (s!"let ({l.name}, io_ru) = io_r;\n", [l.name])
    | _ => pure (s!"{l.name} <- return io_r;\n", [l.name])
  | none =>
    if Rf == .unit then pure ("let () = io_r;\n", [])
    else if Rf == cx.R && !cx.parts.isEmpty then
      pure ((if cx.tail1 then destructR "io_r" cx.parts else destructParts "io_r" cx.parts), cx.capNames)
    else throw ⟨sp, s!"machine: a residual `{ppT Rf}` other than the body's"⟩

/-- `break` (with the loop's value `e`): the innermost loop's iterator closed, then its join. -/
def mBreak (m : MCx) (sp : Span) (e : Val) : MM Comp := do
  let some l := m.loops.head? | throw ⟨sp, "`break` is outside every loop"⟩
  let some j := l.join | throw ⟨sp, "internal error: a loop without its join"⟩
  let keepSrc := match l.keep with
    | some (r, _) => s!"{r} <- return io_hole_e;\n"
    | none => ""
  let go ← mGoto { m with loops := m.loops.drop 1 } sp j
  mTemplate sp "`break`" (((l.held.map (·.closeSrc)).getD "") ++ keepSrc ++ "force io_hole_go")
    [("io_hole_e", e)] [("io_hole_go", go)]

set_option maxHeartbeats 1000000 in
mutual
/-- The code of a machine from a point of the body `M`, in the context `c`: it runs `M` within
one observation, to a `yield`, a move or a finish. -/
def mWalk (m : MCx) : Nat → TCx → Comp → MM Comp
  | 0, _, M => throw ⟨M.span, "internal error: a body nested too deeply"⟩
  | n + 1, c, .bind sp x A (.ret ysp (.app ksp (.sugar k .yield_) e)) N lin => do
    unless m.gen do throw ⟨ysp, "machine: a `yield` outside a generator"⟩
    if e.hasYield then throw (yieldOffSpine (e.yieldAt.getD e.span))
    if (callIn c divFuel (some m.A) e).isSome then
      let (e', bs) := liftAll e
      return (← mWalk m n c (chain bs (.bind sp x A (.ret ysp (.app ksp (.sugar k .yield_) e')) N lin)))
    let vars ← mVars m c [] N [x.name]
    let y ← mNew ysp "`yield`" true false vars
    let code ← mWalk { m with cur := none } n (c.push x.name (some .unit)) N
    mSet y (.bind sp x A (.ret ysp (.unit ysp)) code lin) (← mClose m ysp "`yield`" m.held)
    pure (.ret ysp (.inl ysp (.pair ysp e (mInj ysp y vars))))
  | n + 1, c, .bind sp x A (.ret ysp (.app _ (.sugar _ .yieldFrom) e)) N _ => do
    unless m.gen do throw ⟨ysp, "machine: `yield from` outside a generator"⟩
    if e.hasYield then throw (yieldOffSpine (e.yieldAt.getD e.span))
    let (e', lends) := e.takeLends
    let lend ← match lends with
      | [] => pure none
      | [l] => pure (some l)
      | _ => throw ⟨ysp, "a call lends at most one capability with `&mut`"⟩
    let some Te := c.tyV e' | throw ⟨e.span, "machine: the delegate's type"⟩
    let some (Ae, Bf, Rf) := genOf Te | throw ⟨e.span, "machine: not a generator"⟩
    unless Ae == m.A do throw ⟨e.span, "machine: the delegate's elements"⟩
    let c' := match lend, Bf with
      | some l, .tensor K X => (c.push l.name (some K)).push x.name (some X)
      | some l, K => (c.push l.name (some K)).push x.name (some .unit)
      | none, _ => c.push x.name ((A.bind c.elabV).orElse fun _ => some Bf)
    mCall m n c c' sp x A (.ret ysp e') lend true Te Bf Rf N
  | n + 1, c, .bind sp x A M N lin => do
    if M.hasYield then
      match M with
      | .case csp V y M₁ z M₂ =>
        if mentionsC y.name N || mentionsC z.name N then throw (yieldOffSpine (M.yieldAt.getD M.span))
        return (← mWalk m n c (.case csp V y (.bind sp x A M₁ N lin) z (.bind sp x A M₂ N lin)))
      | .bind bsp y B M₁ M₂ lin' =>
        if mentionsC y.name N then throw (yieldOffSpine (M.yieldAt.getD M.span))
        return (← mWalk m n c (.bind bsp y B M₁ (.bind sp x A M₂ N lin) lin'))
      | .letPair lsp y z V M₁ =>
        if mentionsC y.name N || mentionsC z.name N then throw (yieldOffSpine (M.yieldAt.getD M.span))
        return (← mWalk m n c (.letPair lsp y z V (.bind sp x A M₁ N lin)))
      | .letUnit lsp V M₁ => return (← mWalk m n c (.letUnit lsp V (.bind sp x A M₁ N lin)))
      | _ => throw (yieldOffSpine (M.yieldAt.getD M.span))
    let exp := A.bind c.elabV
    if let .ret sp' V := M then
      if (nestedCall c exp V).isSome then
        let (V', bs) := liftBelow V
        return (← mWalk m n c (chain bs (.bind sp x A (.ret sp' V') N lin)))
    let (M', lends) := M.takeLends
    match (match M' with | .ret _ V => (directCall c exp V).map (V, ·) | _ => none) with
    | some (V, Bf, Rf) =>
      let lend ← match lends with
        | [] => pure none
        | [l] => pure (some l)
        | _ => throw ⟨sp, "a call lends at most one capability with `&mut`"⟩
      let c' := match lend, Bf with
        | some l, .tensor K Vx => (c.push l.name (some K)).push x.name (exp <|> some Vx)
        | some l, _ => (c.push l.name none).push x.name exp
        | none, _ => c.push x.name (exp <|> some Bf)
      let some Tm := c.tyV V | throw ⟨sp, "machine: the call's type"⟩
      mCall m n c c' sp x A M' lend false Tm Bf Rf N
    | none =>
      pure (.bind sp x A M (← mWalk m n (c.push x.name (bindTy c A M)) N) lin)
  | n + 1, c, .letUnit sp V M => do
    if V.hasYield then throw (yieldOffSpine (V.yieldAt.getD V.span))
    if (callIn c divFuel (some .unit) V).isSome then
      let (V', bs) := liftAll V
      return (← mWalk m n c (chain bs (.letUnit sp V' M)))
    return .letUnit sp V (← mWalk m n c M)
  | n + 1, c, .letPair sp x y V M => do
    if V.hasYield then throw (yieldOffSpine (V.yieldAt.getD V.span))
    if (callIn c divFuel none V).isSome then
      let (V', bs) := liftAll V
      return (← mWalk m n c (chain bs (.letPair sp x y V' M)))
    let (Ax, Ay) := pairTys c V
    return .letPair sp x y V (← mWalk m n ((c.push x.name Ax).push y.name Ay) M)
  | n + 1, c, .case sp V x M y N => do
    if V.hasYield then throw (yieldOffSpine (V.yieldAt.getD V.span))
    if (callIn c divFuel none V).isSome then
      let (V', bs) := liftAll V
      return (← mWalk m n c (chain bs (.case sp V' x M y N)))
    let (Ax, Ay) := sumTys c V
    return .case sp V x (← mWalk m n (c.push x.name Ax) M) y (← mWalk m n (c.push y.name Ay) N)
  | n + 1, c, .for_ sp x V M N => mLoop m n c sp x V M N
  | n + 1, c, T@(.ret sp (.app _ (.sugar _ .yield_) _)) =>
    mWalk m n c (.bind sp ⟨"io_y", sp⟩ none T (.ret sp (.unit sp)) false)
  | n + 1, c, T@(.ret sp (.app _ (.sugar _ .yieldFrom) _)) =>
    mWalk m n c (.bind sp ⟨"io_t", sp⟩ none T (.ret sp (.var sp "io_t")) false)
  | _ + 1, _, .ret sp (.app _ (.sugar _ .retE) v) => do
    unless m.gen do throw ⟨sp, "machine: a generator's `return` outside one"⟩
    if v.hasYield then throw (yieldOffSpine (v.yieldAt.getD v.span))
    -- Every loop it leaves closes its iterator.
    mTemplate sp "`return`" (String.join (m.held.map (·.closeSrc)) ++
      s!"io_v : {m.pp m.L.B} <- return io_hole_rv;\nreturn (inr (inl io_v))") [("io_hole_rv", v)] []
  | _ + 1, _, .ret sp (.sugar _ .brk) => mBreak m sp (.unit sp)
  | _ + 1, _, .ret sp (.app _ (.sugar _ .brk) e) => mBreak m sp e
  | n + 1, c, T => do
    if T.hasYield then throw (yieldOffSpine (T.yieldAt.getD T.span))
    if let .ret sp V := T then
      if (nestedCall c (if m.loops.isEmpty then some m.L.B else none) V).isSome then
        let (V', bs) := liftBelow V
        return (← mWalk m n c (chain bs (.ret sp V')))
    let (T', _) := T.takeLends
    if (match T' with | .ret _ V => directCall c (if m.loops.isEmpty then some m.L.B else none) V | _ => none).isSome then
      return (← mWalk m n c (.bind T.span ⟨"io_t", T.span⟩ none T (.ret T.span (.var T.span "io_t")) false))
    match m.loops.head? with
    | some l =>
      -- The end of a loop's body: back to its head.
      let go ← mGoto m T.span l.head
      pure (.bind T.span ⟨"io_u", T.span⟩ none T go false)
    | none => mFinish m T

/-- `x <- M; N` where `M` computes a delegate (`yield from`, `isGen`) or a call's loop, of type
`Tm`, finishing with `Bf` and closed with `Rf`: a point holding it with what `N` uses. -/
def mCall (m : MCx) : Nat → TCx → TCx → Span → Ident → Option VTy → Comp → Option Ident → Bool →
    CVTy → CVTy → CVTy → Comp → MM Comp
  | 0, _, _, sp, _, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | n + 1, c, c', sp, x, A, call, lend, isGen, Tm, Bf, Rf, N => do
    let (abort, hcaps) ← mAbort m sp lend Rf
    let k := (← get).pts.size
    let v := s!"io_d{k}"
    let h : MHeld := { v, T := Tm, closeSrc := s!"io_r <- (nu_out (force {v})).2;\n{abort}", caps := hcaps }
    let excl := x.name :: lend.toList.map (·.name)
    let vars ← mVars m c [h] N excl
    let d ← mNew sp (if isGen then "`yield from`" else "a call of a div function") true true vars
    let bindX := match lend, A with
      | some l, _ => match Bf with
        | .tensor .. => s!"let ({l.name}, {x.name}) = io_b;\n"
        | _ => s!"{l.name} <- return io_b;\n{x.name} <- return ();\n"
      | none, some A => s!"{x.name} : {A.pp} <- return io_b;\n"
      | none, none => s!"{x.name} <- return io_b;\n"
    let pd ← mPt d
    let rest ← mWalk { m with cur := some pd.pos, pre := false } n c' N
    let skip := m.skip sp (mInj sp d vars)
    let src := if isGen then s!"io_o <- (nu_out (force {v})).1;
  case io_o \{
    inl io_y -> let (io_e, {v}) = io_y; return (inl (io_e, io_hole_s))
  | inr io_dd ->
      case io_dd \{
        inl io_b -> {bindX}force io_hole_rest
      | inr {v} -> return io_hole_k
      }
  }" else s!"io_o <- (nu_out (force {v})).1;
  case io_o \{
    inl io_b -> {bindX}force io_hole_rest
  | inr {v} -> return io_hole_k
  }"
    let what := if isGen then "`yield from`" else "a call of a div function"
    let code ← mTemplate sp what src [("io_hole_s", mInj sp d vars), ("io_hole_k", skip)] [("io_hole_rest", rest)]
    mSet d code (← mClose { m with pre := false } sp (if isGen then "`yield from`" else "a call of a div function") (h :: m.held))
    let go ← mGoto m sp d
    pure (.bind sp ⟨v, sp⟩ none call go false)

/-- `for x in V { M }; N` or `while c { M }; N`: a point at its head, and a join after it when its
body has a `break`. -/
def mLoop (m : MCx) : Nat → TCx → Span → Ident → Val → Comp → Comp → MM Comp
  | 0, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | n + 1, c, sp, x, V, M, N => do
    let P ← (genLoopPlan { A := m.A, L := m.L, pp := m.pp } c sp x V M N : SM GenLoop)
    let M ← (normExits divFuel M : Except Error Comp)
    if !m.gen then
      if P.cond.isSome then throw ⟨sp, "machine: `while` in a div body"⟩
      if (M.sugarAt isYieldKw).isSome then throw ⟨sp, "machine: a `yield` in a div body"⟩
      if (loopsAt (c.push x.name ((P.it.map (·.2.1)))) none M).isSome then
        throw ⟨sp, "machine: a loop's body that loops, in a div body"⟩
    let N := P.rest
    let cr := match P.keep with
      | some (r, T) => c.push r (some T)
      | none => c
    let caps := m.L.capNames
    let needs := ((latest c.locals).map (·.1)).filter fun y => !caps.contains y &&
      ((y != x.name && mentionsC y M) || (P.cond.map (mentionsV y)).getD false || mentionsC y (m.restOf N))
    let k := (← get).pts.size
    let own : Option MHeld := P.it.map fun (Vt, _, _, _, Q') =>
      { v := s!"io_it{k}", T := Vt, closeSrc := s!"io_c <- (nu_out (force io_it{k})).2;\n{bindCap P.cap Q' "io_c"}",
        caps := P.cap.toList }
    let held := own.toList ++ m.held
    let hcaps := held.flatMap (·.caps)
    let needVars ← ((latest c.locals).filter (needs.contains ·.1)).mapM fun (y, T) => match T with
      | some T => pure (y, T)
      | none => (throw ⟨sp, s!"machine: the type of `{y}` is not determined"⟩ : MM _)
    let vars := held.reverse.map (fun h => (h.v, h.T)) ++ m.L.caps.filter (!hcaps.contains ·.1) ++ needVars
    let what := if P.cond.isSome then "`while`" else if m.gen then "`for` in a generator" else "`for`"
    let h ← mNew sp what true true vars
    let ph ← mPt h
    let join ← if M.spineBreaks.isEmpty then pure none else do
      let jv ← mVars m cr [] N []
      pure (some (← mNew sp what false true jv))
    let ml : MLoop := { head := h, held := own, needs, keep := P.keep, join }
    let mb : MCx := { m with loops := ml :: m.loops, held := held, cur := some ph.pos, pre := false }
    let cb := match P.it with
      | some (_, E, _, _, _) => c.push x.name (some E)
      | none => c
    let body ← mWalk mb n cb M
    let after ← match join with
      | some j => do
        mSetPos j
        let pj ← mPt j
        let jc ← mWalk { m with cur := some pj.pos, pre := false } n cr N
        mSet j jc (.top sp)
        mGoto { m with cur := some ph.pos, pre := false } sp j
      | none => mWalk { m with cur := some ph.pos, pre := false } n cr N
    let skip := m.skip sp (mInj sp h vars)
    let code ← match P.it, P.cond with
      | some (_, _, isGen, Q, _), _ => do
        let v := s!"io_it{k}"
        let ended := match P.keep with
          | some (r, _) => s!"{r} <- return io_q;\nforce io_hole_after"
          | none => s!"{bindCap P.cap Q "io_q"}force io_hole_after"
        let fin := if isGen then s!"case io_d \{ inl io_q -> {ended} | inr {v} -> return io_hole_k }"
          else s!"io_q <- return io_d;\n{ended}"
        let src := s!"io_o <- (nu_out (force {v})).1;\ncase io_o \{ inl io_p -> let ({x.name}, {v}) = io_p; force io_hole_body | inr io_d -> {fin} }"
        mTemplate sp what src [("io_hole_k", skip)] [("io_hole_body", body), ("io_hole_after", after)]
      | none, some cnd => do
        mTemplate sp what "case io_hole_c { inl io_f -> force io_hole_after | inr io_t -> force io_hole_body }"
          [("io_hole_c", cnd)] [("io_hole_body", body), ("io_hole_after", after)]
      | none, none => throw ⟨sp, "internal error: a loop with neither iterator nor condition"⟩
    mSet h code (← mClose { m with pre := false } sp what held)
    let go ← mGoto m sp h
    match own with
    | some o => pure (.bind sp ⟨o.v, sp⟩ none (.ret sp P.V) go false)
    | none => pure go
end

mutual
/-- The injections of a machine's states resolved: `io_inj_k V` is the injection of point `k`'s
summand, the `r`-th of `n`. -/
def mResV (inj : Nat → Option (Nat × Nat)) : Val → Val
  | .app sp (.var vsp f) V =>
    let V := mResV inj V
    match (if f.startsWith "io_inj_" then (f.drop 7).toNat? else none).bind inj with
    | some (r, n) =>
      let base := if r + 1 == n then V else .inl sp V
      (List.range (min r (n - 1))).foldl (fun W _ => .inr sp W) base
    | none => .app sp (.var vsp f) V
  | .pair sp V W => .pair sp (mResV inj V) (mResV inj W)
  | .app sp V W => .app sp (mResV inj V) (mResV inj W)
  | .inl sp V => .inl sp (mResV inj V)
  | .inr sp V => .inr sp (mResV inj V)
  | .unbang sp V => .unbang sp (mResV inj V)
  | .boxed sp l V => .boxed sp l (mResV inj V)
  | .unbox sp V => .unbox sp (mResV inj V)
  | .sub sp V l => .sub sp (mResV inj V) l
  | .roll sp V => .roll sp (mResV inj V)
  | .unroll sp V => .unroll sp (mResV inj V)
  | .inst sp V l => .inst sp (mResV inj V) l
  | .ascribe sp V A => .ascribe sp (mResV inj V) A
  | .shorten sp md σ l V => .shorten sp md σ l (mResV inj V)
  | .thunk sp M => .thunk sp (mResC inj M)
  | .thunkv sp M => .thunkv sp (mResC inj M)
  | .bangThunk sp M => .bangThunk sp (mResC inj M)
  | .bangThunkv sp M => .bangThunkv sp (mResC inj M)
  | .run sp M => .run sp (mResC inj M)
  | V => V

def mResC (inj : Nat → Option (Nat × Nat)) : Comp → Comp
  | .ret sp V => .ret sp (mResV inj V)
  | .absurd sp V => .absurd sp (mResV inj V)
  | .bind sp x A M N lin => .bind sp x A (mResC inj M) (mResC inj N) lin
  | .lam sp x A M => .lam sp x A (mResC inj M)
  | .app sp M x => .app sp (mResC inj M) x
  | .with_ sp M N => .with_ sp (mResC inj M) (mResC inj N)
  | .proj sp i M => .proj sp i (mResC inj M)
  | .letUnit sp V M => .letUnit sp (mResV inj V) (mResC inj M)
  | .letPair sp x y V M => .letPair sp x y (mResV inj V) (mResC inj M)
  | .case sp V x M y N => .case sp (mResV inj V) x (mResC inj M) y (mResC inj N)
  | .lamL sp x b M => .lamL sp x b (mResC inj M)
  | .inst sp M a => .inst sp (mResC inj M) a
  | .nuIn sp M => .nuIn sp (mResC inj M)
  | .nuOut sp M => .nuOut sp (mResC inj M)
  | .ascribe sp M C => .ascribe sp (mResC inj M) C
  | .for_ sp x V M N => .for_ sp x (mResV inj V) (mResC inj M) (mResC inj N)
  | M => M
end

/-- A right-nested sum type of the summands (`T₀ + (T₁ + …)`). -/
def sumTySrc : List String → String
  | [] => "0"
  | [T] => T
  | T :: Ts => s!"({T}) + ({sumTySrc Ts})"

/-- A `case` on a state held in `v`, over the summands `ps`, with `f p` the arm of `p`, which
finds its tuple in `io_a`. -/
def mTree (f : MPoint → String) (v : String) : List MPoint → String
  | [] => "return ()"
  | [p] => f p
  | [p, q] => s!"case {v} \{ inl io_a -> {f p} | inr io_a -> {f q} }"
  | p :: ps => s!"case {v} \{ inl io_a -> {f p} | inr io_b{p.id} -> {mTree f s!"io_b{p.id}" ps} }"

/-- The machine, assembled around its points: the functions (last point first), the step, and
then `tail`: for a generator, the codata at the first state `s0`; for a div body, `io_mk` and the
code before the first point. -/
def mAssemble (m : MCx) (sp : Span) (st : MSt) (s0 : Option Val) (pre : Option Comp) : SM Comp := do
  let pts := st.pts.toList
  let sums := pts.filter (·.summand)
  if sums.isEmpty then throw ⟨sp, "machine: no point"⟩
  let tyOf (p : MPoint) : String := tupleTySrc (p.vars.map (m.pp ·.2))
  let S := sumTySrc (sums.map tyOf)
  let Obs := if m.gen then s!"({m.pp m.A}) * ({S}) + (({m.pp m.L.B}) + ({S}))" else s!"({m.pp m.L.B}) + ({S})"
  let Cod := if m.gen then s!"gen ({m.pp m.A}) ({m.pp m.L.B}) ({m.pp m.L.R})" else s!"loop ({m.pp m.L.B}) ({m.pp m.L.R})"
  let fns := (pts.filter (·.fn)).toArray.qsort (fun a b => a.pos > b.pos) |>.toList
  let defs := String.join (fns.map fun p =>
    s!"io_run_{p.id} : !(({tyOf p}) => {Obs}) <-\n  return (!thunkv fun (io_a : {tyOf p}) -> force io_hole_c{p.id});\n")
  let arm (p : MPoint) : String :=
    if p.fn then s!"return ((unbang io_run_{p.id}) io_a)" else s!"force io_hole_c{p.id}"
  let carm (p : MPoint) : String := s!"force io_hole_k{p.id}"
  let obs := s!"(nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2"
  let tail := match s0 with
    | some _ => s!"io_f <- return (unbang (unfold[{Cod}, {S}] io_step));
io_s0 : {S} <- return io_hole_s0;
return (thunkv nu_in < {obs} >)"
    | none => s!"io_mk : !(({S}) => U ({Cod})) <- return (!thunkv fun (io_s0 : {S}) ->
  io_f <- return (unbang (unfold[{Cod}, {S}] io_step));
  return (thunkv nu_in < {obs} >));
force io_hole_pre"
  let src := defs ++ s!"io_step : !U ({S} -o F ({Obs}) & F ({m.pp m.L.R})) <-
  return (!thunkv fun ({if sums.length == 1 then "io_a" else "io_s"} : {S}) -> < {mTree arm "io_s" sums}, {mTree carm "io_s" sums} >);
" ++ tail
  let what := if m.gen then "a generator's state machine" else "a div body's state machine"
  let L ← template sp what src
  -- Each point's code and `close`, from its tuple in `io_a`, at the sugar it comes from.
  let bound (p : MPoint) (M : Comp) : SM Comp := do
    let L ← template p.sp p.what s!"{destructSrc "io_a" (p.vars.map (·.1))}force io_hole_body"
    pure (L.fill (fun _ => none) (fun v => if v == "io_hole_body" then some M else none))
  let codes ← pts.mapM fun p => do pure (s!"io_hole_c{p.id}", ← bound p p.code)
  let closes ← (pts.filter (·.summand)).mapM fun p => do pure (s!"io_hole_k{p.id}", ← bound p p.close)
  let L := L.fill (fun v => if v == "io_hole_s0" then s0 else none)
    (fun v => if v == "io_hole_pre" then pre else (codes.lookup v).orElse fun _ => closes.lookup v)
  let n := sums.length
  let ranks := sums.zip (List.range n) |>.map fun (p, r) => (p.id, r)
  pure (mResC (fun id => (ranks.lookup id).map (·, n)) L)

/-- A generator's machine: the code, in the body's context, that returns the generator. Its first
state holds `start` (the parameter, or what a block captures), where its first observation runs
the body `M` from the top; `close0` is the `close` there. -/
def genMachine (g : GenCx) (c : TCx) (sp : Span) (start : List (String × CVTy)) (close0 : Comp)
    (M : Comp) : SM Comp := do
  let m : MCx := { gen := true, A := g.A, L := g.L, pp := g.pp }
  let go : MM Unit := do
    let s ← mNew sp "a generator's body" true false start
    let code ← mWalk m divFuel c M
    mSet s code close0
  let ((), st) ← go.run {}
  mAssemble m sp st (some (mInj sp 0 start)) none

/-- A div body's machine: its code before the first point, then the machine there.  `[spec §14]` -/
def divMachine (cx : LoopCx) (c : TCx) (M : Comp) : SM Comp := do
  let m : MCx := { gen := false, A := .unit, L := cx, pp := ppT, pre := true }
  let (pre, st) ← (mWalk m divFuel c M).run {}
  mAssemble m M.span st none (some pre)

/-- `x`, else `y` from the same origins: a shape the machine does not cover is elaborated by the
nested binds. -/
def orElseM {α} (x y : SM α) : SM α := fun s => match x s with
  | .ok r => .ok r
  | .error _ => y s

/-- A div body: its machine, or the delay binds where the machine does not apply. -/
def divBody (cx : LoopCx) (c : TCx) (M : Comp) : SM Comp :=
  orElseM (divMachine cx c M) (loopBody cx divFuel c M)

/-! ### Blocks and callbacks that yield -/

/-- The type of the first element a body yields: of its first `yield e`, or the element type of
its first `yield from g`. -/
def firstYieldTy : Nat → TCx → Comp → Option CVTy
  | 0, _, _ => none
  | n + 1, c, M => match M with
    | .ret _ (.app _ (.sugar _ .yield_) e) => c.tyV e
    | .ret _ (.app _ (.sugar _ .yieldFrom) e) => ((c.tyV e.takeLends.1).bind genOf).map (·.1)
    | .bind _ x A M N _ =>
      (firstYieldTy n c M).orElse fun _ => firstYieldTy n (c.push x.name (bindTy c A M)) N
    | .letUnit _ _ M => firstYieldTy n c M
    | .letPair _ x y V M =>
      let (Ax, Ay) := pairTys c V
      firstYieldTy n ((c.push x.name Ax).push y.name Ay) M
    | .case _ V x M y N =>
      let (Ax, Ay) := sumTys c V
      (firstYieldTy n (c.push x.name Ax) M).orElse fun _ => firstYieldTy n (c.push y.name Ay) N
    | .for_ _ x V M N =>
      (firstYieldTy n (c.push x.name ((c.tyV V.takeLends.1).bind elemOf)) M).orElse fun _ =>
        match N.forRes? with
        | some (r, _, N₀) => firstYieldTy n (c.push r.name ((c.tyV V.takeLends.1).bind finOf)) N₀
        | none => firstYieldTy n c N
    | _ => none

/-- The type a body finishes with: of its last terminal on the spine. -/
def lastTy : Nat → TCx → Comp → Option CVTy
  | 0, _, _ => none
  | n + 1, c, M => match M with
    | .bind _ x A M N _ => lastTy n (c.push x.name (bindTy c A M)) N
    | .letUnit _ _ M => lastTy n c M
    | .letPair _ x y V M =>
      let (Ax, Ay) := pairTys c V
      lastTy n ((c.push x.name Ax).push y.name Ay) M
    | .case _ V x M y N =>
      let (Ax, Ay) := sumTys c V
      (lastTy n (c.push x.name Ax) M).orElse fun _ => lastTy n (c.push y.name Ay) N
    | .for_ _ _ V _ N => match N.forRes? with
      | some (r, _, N₀) => lastTy n (c.push r.name ((c.tyV V.takeLends.1).bind finOf)) N₀
      | none => lastTy n c N
    | .ret _ (.app _ (.sugar _ .yield_) _) => some .unit
    | .ret _ (.app _ (.sugar _ .yieldFrom) e) => ((c.tyV e.takeLends.1).bind genOf).map (·.2.1)
    | .ret _ (.app _ (.sugar _ .retE) V) => c.tyV V
    | .ret _ V => c.tyV V
    | T => match c.tyC T with
      | some (.ret B) => some B
      | _ => none

/-- A generator body `M` in the context `c`, as a generator: `thunkv nu_in < M', close >`, with
`M'` its first observation and `close` handing back its residual without running it; and its
type. The element type is `A`, or what `M` yields first; the result `B`, or what `M` finishes
with. `what` names the form in messages.  `[spec §15]` -/
def genValue (c : TCx) (sp : Span) (M : Comp) (A B : Option CVTy) (what : String) :
    SM (Val × CVTy) := do
  let M ← normExits divFuel M
  if let some bsp := M.spineBreak then throw ⟨bsp, "`break` is outside every loop"⟩
  let some A := A.orElse fun _ => firstYieldTy divFuel c M
    | throw ⟨sp, s!"the element type of {what} is not determined: it yields nothing, or what " ++
        "it yields has no type here"⟩
  let some B := B.orElse fun _ => lastTy divFuel c M
    | throw ⟨sp, s!"what {what} finishes with is not determined here"⟩
  let cx ← loopCxOf sp B M (gen := true)
  let g : GenCx := { A := A, L := cx, pp := fun T => Frontend.Check.ppV c.E.lenv 0 0 T }
  let G : CVTy := .thunk (Frontend.Check.genTy A B cx.R)
  -- Ascribed its type, so that inference types it where it is used.
  let Gs ← (c.surface sp G : Except Error VTy)
  -- Its machine, whose first state holds what the block captures.
  let machine : SM Val := do
    let caps := cx.caps.filter (mentionsC ·.1 M)
    let locs := (latest c.locals).filter fun (y, _) => mentionsC y M && !cx.capNames.contains y
    for (y, T) in mExterns c do
      if !T.persistent && !cx.capNames.contains y && mentionsC y M && !c.locals.any (·.1 == y) then
        throw ⟨sp, s!"machine: the block captures the extern `{y}`"⟩
    let start ← locs.mapM fun (y, T) => match T with
      | some T => pure (y, T)
      | none => (throw ⟨sp, s!"machine: the type of `{y}` is not determined"⟩ : SM _)
    let (closes, _) := closeGiven cx (locs ++ caps.map fun (y, T) => (y, some T))
    let close0 ← template sp s!"the `close` of {what} before it starts" s!"{closes}return {cx.rSrc}"
    let Mm ← genMachine g c sp (start ++ caps) close0 M
    pure (.ascribe sp (.run sp Mm) Gs)
  let old : SM Val := do
    let M' ← genBody g divFuel c M
    let (closes, closed) := closeGiven cx ((latest c.locals).filter (mentionsC ·.1 M))
    let ab ← template sp s!"the `close` of {what} before it starts"
      s!"{closes}{dropsFor c (cx.capNames ++ closed) M}return {cx.rSrc}"
    pure (.ascribe sp (.thunkv sp (.nuIn sp (.with_ sp M' ab))) Gs)
  pure (← orElseM machine old, G)

/-- In the copy of a higher-order function made at a callback type that yields, the calls through
the callback: an application of a function of one of the types `Fs` (the callbacks' types, as
thunks). Each is a `yield from` of the generator the call returns: the function was written
against a callback that returns a value, so every call of it expects that value, which the
generator finishes with. -/
def delegateC (Fs : List CVTy) : Nat → TCx → Comp → Comp
  | 0, _, M => M
  | n + 1, c, M =>
    let isCb (V : Val) : Bool := match V with
      | .app _ f _ => match c.tyV f with
        | some T => Fs.contains T
        | none => false
      | _ => false
    let wrap (V : Val) : Val := if isCb V then .app V.span (.sugar V.span .yieldFrom) V else V
    match M with
    | .bind sp x A M N lin =>
      let M' := match M with
        | .ret rsp V => .ret rsp (wrap V)
        | M => delegateC Fs n c M
      .bind sp x A M' (delegateC Fs n (c.push x.name (bindTy c A M)) N) lin
    | .letUnit sp V M => .letUnit sp V (delegateC Fs n c M)
    | .letPair sp x y V M =>
      let (Ax, Ay) := pairTys c V
      .letPair sp x y V (delegateC Fs n ((c.push x.name Ax).push y.name Ay) M)
    | .case sp V x M y N =>
      let (Ax, Ay) := sumTys c V
      .case sp V x (delegateC Fs n (c.push x.name Ax) M) y (delegateC Fs n (c.push y.name Ay) N)
    | .for_ sp x V M N =>
      .for_ sp x V (delegateC Fs n (c.push x.name ((c.tyV V.takeLends.1).bind elemOf)) M)
        (delegateC Fs n c N)
    | .ret sp V => .ret sp (wrap V)
    | M => M

/-- A generator function type `A => U (gen E B R)` (or its `!` form): `A`, `E`, `B`, `R`, and
whether it is persistent. -/
def genFnOf : CVTy → Option (CVTy × CVTy × CVTy × CVTy × Bool)
  | .thunk (.arr A (.ret G)) => (genOf G).map fun (E, B, R) => (A, E, B, R, false)
  | .bang (.thunk (.arr A (.ret G))) => (genOf G).map fun (E, B, R) => (A, E, B, R, true)
  | _ => none

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
  let cx : LoopCx := ⟨.tensor K Ac, .tensor K .unit, K, [cs.map fun n => (n, capTyC n)], true⟩
  pure (.ret sp (.thunk sp (.loop sp B (.tensor sp capsT (.unit sp)))), ← divBody cx c M')

/-- The result `B` of a function type `A => B` or `!(A => B)`. -/
def resultOf : Option CVTy → Option CVTy
  | some (.thunk (.arr _ (.ret B))) | some (.bang (.thunk (.arr _ (.ret B)))) => some B
  | _ => none

/-- A value that must be known here. -/
def need' {α} (sp : Span) (what : String) : Option α → SM α
  | some a => pure a
  | none => throw ⟨sp, s!"{what} is not determined here"⟩

/-- A generator body that is straight-line code, then one loop, then code with no `yield` and no
loop: the code before the loop (as a function of what replaces the loop), the typing context at
the loop, the loop, and whether the code before it has a `match` or `if` whose other arm finishes
the generator without looping (`fin` elaborates that arm's terminals as the generator's finish). -/
def splitLoop (fin : Comp → Comp) : Nat → TCx → Comp →
    Option ((Comp → Comp) × TCx × Span × Ident × Val × Comp × Comp × Bool)
  | 0, _, _ => none
  | n + 1, c, .bind sp x A M N lin =>
    if M.hasYield || M.hasFor || (headLoops c (A.bind c.elabV) M).isSome then none else
    (splitLoop fin n (c.push x.name (bindTy c A M)) N).map fun (pre, r) =>
      (fun T => .bind sp x A M (pre T) lin, r)
  | n + 1, c, .letUnit sp V M =>
    if V.hasYield || (callIn c divFuel (some .unit) V).isSome then none else
    (splitLoop fin n c M).map fun (pre, r) => (fun T => .letUnit sp V (pre T), r)
  | n + 1, c, .letPair sp x y V M =>
    if V.hasYield || (callIn c divFuel none V).isSome then none else
    let (Ax, Ay) := pairTys c V
    (splitLoop fin n ((c.push x.name Ax).push y.name Ay) M).map fun (pre, r) =>
      (fun T => .letPair sp x y V (pre T), r)
  | n + 1, c, .case sp V x M y N =>
    if V.hasYield || (callIn c divFuel none V).isSome then none else
    let (Ax, Ay) := sumTys c V
    -- An arm that finishes: no yield, loop, `break` or call of a div function.
    let plain (c : TCx) (N : Comp) : Bool := !N.yieldsOrLoops && N.spineBreaks.isEmpty &&
      (loopsAt c none N).isNone && (N.sugarAt (· == .yieldFrom)).isNone
    match splitLoop fin n (c.push x.name Ax) M, splitLoop fin n (c.push y.name Ay) N with
    | some (pre, cm, r), none =>
      if plain (c.push y.name Ay) N then
        some (fun T => .case sp V x (pre T) y (fin N), cm, r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, true)
      else none
    | none, some (pre, cm, r) =>
      if plain (c.push x.name Ax) M then
        some (fun T => .case sp V x (fin M) y (pre T), cm, r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, true)
      else none
    | _, _ => none
  | _ + 1, c, .for_ sp x V M N =>
    if N.hasYield || N.hasFor || (loopsAt c none N).isSome then none
    else some (id, c, sp, x, V, M, N, false)
  | _, _, _ => none

/-- A `gen fn`, elaborated: `gen[E] def f : !(P => B) = !thunkv fun (x : P) -> M` becomes
`def f : !(P => U (gen E B R)) = !thunkv fun (x : P) -> return (thunkv nu_in < M', abort >)`, which
runs nothing until the generator is observed. `scope` is the declarations before it. -/
def genDef (scope : List Decl) : Decl → SM Decl
  | .def_ sp n ps A V (.gen E) => do
    let c := TCx.ofScope scope false
    -- `!thunkv fun (x : P) -> M`, or with a lifetime parameter `'y`,
    -- `!thunkv Fun 'y < b. return (thunkv fun (x : P) -> M)` (`gen fn f<'y>(…)`).
    let (life, x, Ax, M) ← match V with
      | .thunkv _ (.lam _ x Ax M) | .bangThunkv _ (.lam _ x Ax M) => pure (none, x, Ax, M)
      | .bangThunkv _ (.lamL _ y b (.ret _ (.thunkv _ (.lam _ x Ax M)))) =>
        pure (some (y, b), x, Ax, M)
      | _ => throw ⟨sp, "a generator is written `gen fn f(…) -> A = S`"⟩
    let (bang, Ar, B) ← match A, V, life with
      | .lolli _ Ar B, .thunkv .., none => pure (false, Ar, B)
      | .bang _ (.lolli _ Ar B), .bangThunkv .., none => pure (true, Ar, B)
      | .bang _ (.all _ _ _ (.lolli _ Ar B)), .bangThunkv .., some _ => pure (true, Ar, B)
      | _, _, _ => throw ⟨A.span, "a generator has type `A => B` or `!(A => B)`"⟩
    if !ps.isEmpty then throw ⟨sp, "a generator has no type parameters"⟩
    let M ← normExits divFuel M
    if let some bsp := M.spineBreak then throw ⟨bsp, "`break` is outside every loop"⟩
    let cl ← match life with
      | none => pure c
      | some (y, b) => do
        let bl ← need' b.span "the lifetime's bound" (c.elabL b)
        pure (c.pushLife y.name bl)
    let some Bc := cl.elabV B
      | throw ⟨B.span, s!"the result type of `{n.name}` does not elaborate"⟩
    let some Ec := cl.elabV E
      | throw ⟨E.span, s!"the element type of `{n.name}` does not elaborate"⟩
    let cx ← loopCxOf sp Bc M (gen := true)
    let c₀ := cl.push x.name (cl.elabV Ax)
    let g : GenCx := { A := Ec, L := cx, pp := fun T => Frontend.Check.ppV cl.E.lenv 0 0 T }
    let (closes, _) := closeGiven cx (paramsOf divFuel c₀ M)
    let ab ← template sp "a generator's `close` before it starts" s!"{closes}return {cx.rSrc}"
    let abort := paramPrefix M ab
    let Rs ← toSurface sp cx.R
    let G := VTy.thunk B.span (.gen B.span E B Rs)
    let F := VTy.lolli A.span Ar G
    -- An arm before the loop that finishes the generator, as the start's observation.
    let Bs ← cl.surface sp Bc
    let fin (T : Comp) : Comp := wrapTail (fun T => .bind T.span ⟨"io_v", T.span⟩ (some Bs) T
      (.ret T.span (.inr T.span (.inl T.span (.var T.span "io_v")))) false) (stripRet T)
    let whole : SM Comp := do
      let M' ← genBody g divFuel c₀ M
      pure (Comp.ret sp (.thunkv sp (.nuIn sp (.with_ sp M' abort))))
    let machine : SM Comp := do
      let some Pc := cl.elabV Ax | throw ⟨sp, "machine: the parameter's type"⟩
      genMachine g c₀ sp [(x.name, Pc)] abort M
    let old : SM Comp := match splitLoop fin divFuel c₀ M with
      | some (pre, cm, lsp, lx, LV, LM, LN, arm) => do
        -- One loop: the generator is that loop's `unfold`, with a first state that runs the code
        -- before it. Every observation is then a call of one known code. An arm before it that
        -- finishes is the start's observation when the loop finishes with the generator's result.
        let P ← genLoopPlan g cm lsp lx LV LM LN
        if arm && P.direct.isNone then whole else
        let bodyL ← genBody { g with L := P.bcx, inLoop := true } divFuel P.cb P.bodyW
        genLoopSrc g cm lsp lx P bodyL P.rest P.rest (some (x.name, Ax.pp, pre, abort))
      | none => whole
    let body ← orElseM machine old
    let lam := Comp.lam sp x Ax body
    match life with
    | none =>
      let A' := if bang then VTy.bang A.span F else F
      let V' := if bang then Val.bangThunkv sp lam else Val.thunkv sp lam
      pure (.def_ sp n ps A' V' .none)
    | some (y, b) =>
      pure (.def_ sp n ps (.bang A.span (.all A.span y b F))
        (.bangThunkv sp (.lamL sp y b (.ret sp (.thunkv sp lam)))) .none)
  | d => pure d


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
      let M' ← divBody cx (c.push x.name (c.elabV Ax)) M
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
  /-- `gen fn`: a generator. -/
  mark : Mark := .none

/-- The latest source `def` named `h`, when it is a function without type parameters. -/
def hofOf (srcs : List Decl) (h : String) : Option Hof :=
  match srcs.find? (fun | .def_ _ n _ _ _ _ => n.name == h | _ => false) with
  | some (.def_ sp n [] (.lolli _ P Q) (.thunkv _ (.lam _ x _ M)) mk) =>
    some ⟨sp, n, false, P, Q, x, M, mk⟩
  | some (.def_ sp n [] (.bang _ (.lolli _ P Q)) (.bangThunkv _ (.lam _ x _ M)) mk) =>
    some ⟨sp, n, true, P, Q, x, M, mk⟩
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
    let A' ← match T with
      | .thunk (.arr A' _) => if bang then none else some A'
      | .bang (.thunk (.arr A' _)) => if bang then some A' else none
      | _ => none
    -- A div callback's result is a loop of `B`; a yielding callback's, a generator finishing
    -- with `B`.
    let B' ← ((loopFnOf T).map (·.1)).orElse fun _ => (genFnOf T).map (·.2.2.1)
    if A' = A ∧ B' = B then some T else none

/-- The callbacks a parameter type `P'` made by `specTy` has that yield: their function types,
as thunks. -/
def genCallbacks : CVTy → List CVTy
  | .tensor P Q => genCallbacks P ++ genCallbacks Q
  | T => match genFnOf T, T with
    | some _, .bang F => [F]
    | some _, F => [F]
    | none, _ => []

/-- The elaboration so far: the libraries (in scope for typing); the source declarations in
scope, newest first; the elaborated ones, in order; whether any body became a loop; and the
copies made, by function and parameter type. -/
structure DivSt where
  lib : List Decl := []
  srcs : List Decl := []
  out : List Decl := []
  any : Bool := false
  copies : List ((String × VTy) × String) := []
  /-- The copies made at a callback type that yields, with the callbacks' types: in each, the
  calls through those callbacks are `yield from`s (`delegateC`). -/
  genCopies : List (String × List CVTy) := []
  /-- The capabilities in scope of the declaration being elaborated (`main`'s), for typing. -/
  caps : List Decl := []
  /-- The templates (`gen fn f[A, …]`, `fn f[A, …]`), as written: each is instantiated at the
  types of a call, on first use. -/
  templates : List Decl := []
  /-- The instances made, by template and type arguments. -/
  insts : List ((String × List VTy) × String) := []

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
    if (M.sugarAt isYieldKw).isSome then
      -- A callback that yields: a generator function, whose body is elaborated in place.
      let (g, G) ← (genValue c' lsp M none (some B) "this callback" : SM (Val × CVTy))
      modify fun st => { st with any := true }
      let some Ac := Ac | return (V, none)
      let F : CVTy := .thunk (.arr Ac (.ret G))
      let lam := Comp.lam lsp x A (.ret lsp g)
      return (if bang then (.bangThunkv sp lam, some (.bang F)) else (.thunkv sp lam, some F))
    if (loopsAt c' (some B) M).isNone then return (V, c.tyV V)
    let cx ← (loopCxOf lsp B M : Except Error LoopCx)
    let M' ← (divBody cx c' M : SM Comp)
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

/-! ### The surface forms that need types  `[#54, docs/typed-elaboration.md §5]`

Draft 0's surface (docs/surface-cbpv.md) is parsed into core, with the forms that need types left
as `Val.sugar` nodes (`Frontend/Parser.lean`). They are elaborated here, on the types inference
gives (`TCx`), into core with every bracket argument written:

* **Literals** are `i32[n]`, or `i64[n]`/`u8[n]` where an `i64`/`u8` is expected. An operator
  at `u8` widens its operands and works at `i32` (`byteOp`).
* **Operators** `+ - * == != < <= > >=` are the host operation at the width of their operands:
  `add32` or `add64`, …, `lt_s32`, …; a comparison returns `1 + 1`, `inr ()` for true.
* **`alloc(e)`, `free(e)`, `swap(c, e)`** are the constants with their type arguments read off
  their operands.
* **A call `f(e)` of a persistent function** `f : !(A => B)` is `(unbang f) e`: `!` is not a
  shift, and `unbang` erases.
* **A closure `{ x -> S }`** takes its parameter's type from the function type expected of it.
* **A block `{ S }`** is `thunk S`; when `S` loops, it is the loop that runs `S` at its first
  observation and not before, `div_defer[B, R] (thunkv < S', abort >)` (SPEC §14, decision 2 of
  typed elaboration), `abort` handing back the residual without running anything.
* **Borrow blocks** `borrow imm r { 'x, b -> S }` (`withbor1`), `borrow mut r { … }` (`withbor2`),
  `borrow mut (r₁, r₂) { 'c, (m₁, m₂) -> S }` (`withbor_f2_mut`) and `modify m { x -> S }`
  (`withswap`) take their type arguments from the place and the body, and the body's tail is
  boxed at the lifetime (`boxed['x]`). `modify`'s body returns the new content and a result, or
  the new content alone, which is the new content and `()` (unit elision). The parser has already
  rebound the place where the block is bound or a statement.
-/

/-- The host operation of a surface operator at a width. -/
def _root_.Frontend.SurfOp.host (w : BoCa.Width) : SurfOp → BoCa.HostOp
  | .add => .bin w .add | .sub => .bin w .sub | .mul => .bin w .mul
  | .eq => .rel w .eq | .ne => .rel w .ne | .lt => .rel w .lt_s | .le => .rel w .le_s
  | .gt => .rel w .gt_s | .ge => .rel w .ge_s

/-- The width of an integer type. -/
def widthOf : Option CVTy → Option BoCa.Width
  | some (.int w) => some w
  | _ => none

/-- A literal at a width. -/
def litAt (sp : Span) (w : BoCa.Width) (n : Nat) : Val :=
  .const sp (.lit (match w with
    | .w32 => .i32 (UInt32.ofNat n) | .w64 => .i64 (UInt64.ofNat n) | .w8 => .u8 (UInt8.ofNat n)))

/-- An operator at `u8`: the operands widened by `extend8_u`, the operation at `i32`, and an
arithmetic result narrowed by `wrap8`. A byte has no arithmetic of its own (SPEC §8). -/
def byteOp (sp osp psp : Span) (o : SurfOp) (a b : Val) : Val :=
  let h (op : BoCa.HostOp) (x : Val) : Val := .app sp (.unbang osp (.const osp (.host op))) x
  let r := h (o.host .w32) (.pair psp (h .extend8_u a) (h .extend8_u b))
  match o with
  | .add | .sub | .mul => h .wrap8 r
  | _ => r

def isHoleTy : VTy → Bool
  | .name _ "_" => true
  | _ => false

/-- A value or a type that must be known here. -/
def need {α} (sp : Span) (what : String) : Option α → DM α
  | some a => pure a
  | none => throw ⟨sp, s!"the type of {what} is not determined here: ascribe it"⟩

/-- The body `S` of a block with its tail values boxed at `'x`: a tail value is bound first, so
that what it computes from the borrow is not inside the box (`boxI`'s context outlives `'x`). -/
def boxTail (x : String) (S : Comp) : Comp :=
  wrapTail (fun
    | .ret sp V@(.var ..) | .ret sp V@(.unit _) => .ret sp (.boxed sp (.var sp x) V)
    | T => .bind T.span ⟨"io_bx", T.span⟩ none T
        (.ret T.span (.boxed T.span (.var T.span x) (.var T.span "io_bx"))) false) S

/-- The body `S` of `modify` returning the new content alone, with `()` for the result. -/
def unitTail (S : Comp) : Comp :=
  wrapTail (fun
    | .ret sp V => .ret sp (.pair sp V (.unit sp))
    | T => .bind T.span ⟨"io_mv", T.span⟩ none T
        (.ret T.span (.pair T.span (.var T.span "io_mv") (.unit T.span))) false) S

/-- The result type of a computation, as its tail gives it. -/
def resultOfC : Option CCTy → Option CVTy
  | some (.ret A) => some A
  | _ => none

/-! #### Lending a place: `&mut x` and `&x`  (typed elaboration §5.1)

A lent place is handed back to its name: the lent value is the place of a borrow, and the
borrow's result `(x, B)` rebinds `x` as `&c` always has (`Comp.elab`). Which borrow is chosen by
types. A call `f(…, &mut x, …)` of a function whose parameter there is a `mut 'a A` (or, for `&x`,
an `imm 'a A`) under its lifetime binder borrows `x` for the call: `withbor2` (or `withbor1`) when
`x : ref A`, and a cell scoped to the call when `x : A` is a value (a `let mut`): `alloc`, the
borrow, `free`. A parameter of `x`'s own type takes `x` and hands it back first, as a capability
is lent (SPEC §11). `modify &mut x { … }` borrows the same way around the `withswap`. -/

/-- The place lent in an argument, outside nested computations, with the parameter type at it. -/
def lendParam : CVTy → Val → Option (Ident × Mode × CVTy)
  | P, .lend _ x m => some (x, m, P)
  | .tensor P Q, .pair _ V W => (lendParam P V).orElse fun _ => lendParam Q W
  | _, _ => none

/-- The argument with its lent place replaced by `y`. -/
def replaceLend (y : String) : Val → Val
  | .lend sp _ _ => .var sp y
  | .pair sp V W => .pair sp (replaceLend y V) (replaceLend y W)
  | V => V

/-- A borrow of the place `x`, lent at the call `sp`, around the body `body` that uses the
borrow `m : mut 'l A` (or `imm 'l A`) and returns `B`: its value, which the lend rebinds. -/
def lendBorrow (c : TCx) (sp : Span) (x : Ident) (m : Mode) (A B : CVTy)
    (body : String → String → Comp) : DM Val := do
  let l := s!"io_lb{sp.start.line}_{sp.start.col}"
  let mv := s!"io_lm{sp.start.line}_{sp.start.col}"
  let As ← (c.surface sp A : Except Error VTy)
  let Bs ← (c.surface sp B : Except Error VTy)
  let li : Ident := ⟨l, sp⟩
  let Tm : VTy := if m == .mut then .mut sp (.var sp l) As else .imm sp (.var sp l) As
  let cb : Val := .thunkv sp (.lamL sp li (.dom sp) (.ret sp (.thunkv sp
    (.lam sp ⟨mv, sp⟩ Tm (body l mv)))))
  let C : Const := if m == .mut then .withbor2 li (.top sp) As Bs else .withbor1 li As Bs
  let place := Val.lend sp x m
  match c.tyV (.var sp x.name) with
  | some (.ref _) => pure (.app sp (.app sp (.const sp C) place) cb)
  | some (.mut ..) | some (.imm ..) =>
    throw ⟨x.span, s!"`{x.name}` is a borrow; lend it by passing it (a reborrow is not provided)"⟩
  | _ =>
    -- A value: a cell scoped to the call.
    let cell : Val := .app sp (.const sp (.alloc As)) place
    pure (.run sp (.letPair sp ⟨"io_sc", sp⟩ ⟨"io_sr", sp⟩
      (.app sp (.app sp (.const sp C) cell) cb)
      (.ret sp (.pair sp (.app sp (.const sp (.free As)) (.var sp "io_sc")) (.var sp "io_sr")))))

/-- The body of a borrow callback: `r <- M; return (boxed['l] r)`. -/
def boxedResult (sp : Span) (l : String) (M : Comp) : Comp :=
  .bind sp ⟨"io_lr", sp⟩ none M (.ret sp (.boxed sp (.var sp l) (.var sp "io_lr"))) false

/-- A call `f W` whose argument lends a place at a borrow parameter of `f`: the borrow around
the call. `none` when it does not. -/
def lendCall (c : TCx) (sp : Span) (f W : Val) : DM (Option Val) := do
  -- `f : !(all 'a < b. P => Q)` or `all 'a < b. P => Q`.
  let (bang, v, P, Q) ← match c.tyV f with
    | some (.bang (.thunk (.all v _ (.ret (.thunk (.arr P (.ret Q))))))) => pure (true, v, P, Q)
    | some (.thunk (.all v _ (.ret (.thunk (.arr P (.ret Q)))))) => pure (false, v, P, Q)
    | _ => return none
  let some (x, m, Px) := lendParam P W | return none
  let (pm, A) ← match Px with
    | .mut (.var w) A => if w == v then pure (Mode.mut, A) else return none
    | .imm (.var w) A => if w == v then pure (Mode.imm, A) else return none
    | _ => return none
  if pm != m then
    throw ⟨x.span, s!"the parameter here is {if pm == .mut then "a `mut`" else "an `imm`"} borrow: " ++
      s!"lend `{x.name}` as `{if pm == .mut then "&mut " else "&"}{x.name}`"⟩
  if BoCa.Fig16.LogRel.Core.Check.vfreeB v Q then
    throw ⟨sp, "the call's result mentions the lifetime of the lent place, so the place cannot " ++
      "be handed back after it"⟩
  let f' := if bang then Val.unbang f.span f else f
  some <$> lendBorrow c sp x m A Q fun l mv =>
    boxedResult sp l (.ret sp (.app sp (.inst sp f' (.var sp l)) (replaceLend mv W)))

/-- The typing context `c` with the declarations made so far in scope (the instances and copies
made while elaborating the declaration it is in). -/
def refresh (c : TCx) : DM TCx := do
  let st ← get
  let ds := (st.lib ++ st.out ++ st.caps).toArray
  pure { c with E := { c.E with scope := ⟨ds, ds.size⟩ } }

/-! #### Generic calls

A call's callee may be generic in three ways, and the elaborator fills what the call leaves out
(typed elaboration §2.2–§2.3):

* **A template**: a `gen fn f[A, …](…)` or a `fn f[A, …](…)`. It is not elaborated as written, and
  a call of it is a call of its instance at the types of the call, the template with the types
  substituted for its parameters (`Frontend/Elab/Subst.lean`), made and elaborated on first use
  (whole-program monomorphization, as Rust's generics). Its body is elaborated at the instance's
  types, so an operation that needs a persistent element (`*g`) is accepted at `u8` and rejected
  at a type that is not.
* **A `def` with type parameters** written in core, `def f[A, …] : …`: its call is `f[T, …]`,
  checked at each use by the checker.
* **Lifetime parameters**, `!(all 'a < @. all 'b < @'. P => Q)`: its call is
  `(unbang f) ['x] ['y]`.

The type arguments are written, `f[T, …](…)`, or read off the arguments' types by first-order
matching against the parameter's type, in which each type parameter is a placeholder; what the
arguments leave open is matched against the type expected of the call's result. Each lifetime
parameter is read off the argument whose type mentions it; when two arguments give it different
lifetimes, it is their meet, and an argument that is a borrow is shortened to it with `:>` (§2.3;
there is no other solving). A closure argument whose parameter's type is a hole, and an
injection, are typed last, from the parameter's type with what the other arguments determined. -/

/-- The placeholders of type parameters in a pattern: type variables no type of a program has. -/
def phBase : Nat := 1 <<< 24

/-- What matching has found: the type parameters, by placeholder; the lifetime parameters of the
call (`binders`), with the lifetime each is matched with; and those matched with two lifetimes. -/
structure MatchSt where
  ty : Array (Option CVTy)
  binders : List BoCa.Lifetime.LifeVar := []
  life : List (BoCa.Lifetime.LifeVar × BoCa.Lifetime.Life) := []
  conflicts : List BoCa.Lifetime.LifeVar := []

/-- `l` is `a`, or one of the lifetimes `a` is the meet of. -/
def inMeet (l : BoCa.Lifetime.Life) : BoCa.Lifetime.Life → Bool
  | .meet a b => l == .meet a b || inMeet l a || inMeet l b
  | a => l == a

/-- The lifetime `a'` of an argument where the pattern has `a`: a lifetime parameter of the call is
matched with it, or with the meet of it and what it was matched with before. -/
def matchLife (m : MatchSt) (a a' : BoCa.Lifetime.Life) : MatchSt :=
  match a with
  | .var v =>
    if !m.binders.contains v then m else
    match m.life.lookup v with
    | none => { m with life := (v, a') :: m.life }
    | some l => if inMeet a' l then m else
      { m with life := (v, .meet l a') :: m.life.filter (·.1 != v), conflicts := v :: m.conflicts }
  | _ => m

mutual
/-- `t` matches the pattern `p`, whose placeholders are bound in `m`, under `d` binders of type
variables (`μ`, `ν`), which shift a placeholder's index by `d`. A lifetime of the pattern that is
not a lifetime parameter of the call matches any lifetime: the checker decides it. -/
def matchV (m : MatchSt) (d : Nat) : CVTy → CVTy → Option MatchSt
  | .tvar i, t =>
    if i ≥ phBase + d then match m.ty[i - phBase - d]? with
      | some (some u) => if u = t then some m else none
      | some none => some { m with ty := m.ty.set! (i - phBase - d) (some t) }
      | none => none
    else if t = .tvar i then some m else none
  | .tensor A B, .tensor A' B' | .sum A B, .sum A' B' => (matchV m d A A').bind (matchV · d B B')
  | .thunk C, .thunk C' => matchC m d C C'
  | .mu A, .mu A' => matchV m (d + 1) A A'
  | .ref A, .ref A' | .bang A, .bang A' | .fam A, .fam A' => matchV m d A A'
  | .imm a A, .imm a' A' | .mut a A, .mut a' A' | .box a A, .box a' A' =>
    matchV (matchLife m a a') d A A'
  | p, t => if p = t then some m else none

/-- `t` matches the computation-type pattern `p`. -/
def matchC (m : MatchSt) (d : Nat) : CCTy → CCTy → Option MatchSt
  | .ret A, .ret A' => matchV m d A A'
  | .arr A C, .arr A' C' => (matchV m d A A').bind (matchC · d C C')
  | .amp C D, .amp C' D' => (matchC m d C C').bind (matchC · d D D')
  | .nu C, .nu C' => matchC m (d + 1) C C'
  | .all _ _ C, .all _ _ C' => matchC m d C C'
  | p, t => if p = t then some m else none
end

mutual
/-- A pattern with placeholders. -/
def hasPhV : CVTy → Bool
  | .tvar i => i ≥ phBase
  | .tensor A B | .sum A B => hasPhV A || hasPhV B
  | .thunk C => hasPhC C
  | .ref A | .bang A | .mu A | .fam A | .imm _ A | .mut _ A | .box _ A => hasPhV A
  | _ => false

def hasPhC : CCTy → Bool
  | .ret A => hasPhV A
  | .arr A C => hasPhV A || hasPhC C
  | .amp C D => hasPhC C || hasPhC D
  | .nu C | .all _ _ C => hasPhC C
  | .top => false
end

mutual
/-- A pattern with its solved placeholders replaced, under `d` binders of type variables. The
types solved are closed, so they need no shift. -/
def solvedV (σ : Array (Option CVTy)) (d : Nat) : CVTy → CVTy
  | .tvar i => if i ≥ phBase + d then ((σ[i - phBase - d]?).join).getD (.tvar i) else .tvar i
  | .tensor A B => .tensor (solvedV σ d A) (solvedV σ d B)
  | .sum A B => .sum (solvedV σ d A) (solvedV σ d B)
  | .thunk C => .thunk (solvedC σ d C)
  | .ref A => .ref (solvedV σ d A)
  | .bang A => .bang (solvedV σ d A)
  | .mu A => .mu (solvedV σ (d + 1) A)
  | .fam A => .fam (solvedV σ d A)
  | .imm a A => .imm a (solvedV σ d A)
  | .mut a A => .mut a (solvedV σ d A)
  | .box a A => .box a (solvedV σ d A)
  | t => t

def solvedC (σ : Array (Option CVTy)) (d : Nat) : CCTy → CCTy
  | .ret A => .ret (solvedV σ d A)
  | .arr A C => .arr (solvedV σ d A) (solvedC σ d C)
  | .amp C D => .amp (solvedC σ d C) (solvedC σ d D)
  | .nu C => .nu (solvedC σ (d + 1) C)
  | .all v b C => .all v b (solvedC σ d C)
  | .top => .top
end

/-- A pattern with what matching found: its placeholders and its lifetime parameters solved. -/
def MatchSt.solved (m : MatchSt) (P : CVTy) : CVTy := (solvedV m.ty 0 P).applyLSub m.life

/-- The pattern, solved as far as matching has gone, still has an unknown: a placeholder, or a
lifetime parameter not yet matched. -/
def MatchSt.isOpen (m : MatchSt) (P : CVTy) : Bool :=
  let P' := m.solved P
  hasPhV P' || m.binders.any fun v => BoCa.Fig16.LogRel.Core.Check.vfreeB v P'

/-- The parameter type of a written function type, `!(all 'a < @. … P => Q)`. -/
def paramTy : VTy → Option VTy
  | .bang _ A | .all _ _ _ A => paramTy A
  | .lolli _ P _ | .thunk _ (.arr _ P _) => some P
  | _ => none

/-- The components of an argument against a written parameter type, as `compsC`. -/
def argComps : VTy → Val → List (VTy × Val)
  | .tensor _ P Q, .pair _ V W => (P, V) :: argComps Q W
  | P, W => [(P, W)]

/-- A type as a pattern: the type parameters `ps` as placeholders. -/
def patOf (c : TCx) (ps : List String) (P : VTy) : Option CVTy :=
  ({ c.E with tps := ps.zipIdx.map fun (x, k) => (x, .tvar (phBase + k)) }.elabV c.Δ P).toOption

/-- A function's signature: whether it is persistent (`!`), its lifetime parameters with their
bounds, outermost first, its parameter type and its result. -/
structure Sig where
  bang : Bool
  binders : List (BoCa.Lifetime.LifeVar × BoCa.Lifetime.Life)
  P : CVTy
  R : CCTy

/-- The lifetime parameters, parameter type and result of `all 'a < @. … P => Q`. -/
def sigGo : Nat → CVTy → Option (List (BoCa.Lifetime.LifeVar × BoCa.Lifetime.Life) × CVTy × CCTy)
  | 0, _ => none
  | k + 1, .thunk (.all v b (.ret X)) => do let (bs, P, R) ← sigGo k X; pure ((v, b) :: bs, P, R)
  | _, .thunk (.arr P R) => some ([], P, R)
  | _, _ => none

/-- The signature of a function type, `!(all 'a < @. … P => Q)` or without `!`. -/
def sigOf : CVTy → Option Sig
  | .bang T => (sigGo 64 T).map fun (bs, P, R) => ⟨true, bs, P, R⟩
  | T => (sigGo 64 T).map fun (bs, P, R) => ⟨false, bs, P, R⟩

/-- The names of a written function type's lifetime parameters, outermost first. -/
def lifeNames : VTy → List String
  | .bang _ A => lifeNames A
  | .all _ x _ A => x.name :: lifeNames A
  | _ => []

/-- The components of an argument against a parameter's type: along the right-nested tuple of
the call's arguments. -/
def compsC : CVTy → Val → List (CVTy × Val)
  | .tensor P Q, .pair _ V W => (P, V) :: compsC Q W
  | P, W => [(P, W)]

/-- The argument rebuilt from its components (as `compsC` split it). -/
def argOf : Val → List Val → Val
  | .pair sp _ W, V :: Vs => .pair sp V (argOf W Vs)
  | _, [V] => V
  | W, _ => W

/-- A closure whose parameter's type is left to the context. -/
def holeClosure : Val → Bool
  | .thunkv _ (.lam _ _ A _) | .bangThunkv _ (.lam _ _ A _) => isHoleTy A
  | _ => false

/-- An argument whose type only the context gives: a closure with a hole, or an injection. -/
def checkOnly : Val → Bool
  | .inl .. | .inr .. | .roll .. => true
  | V => holeClosure V

/-- The function a call applies when it may be generic by name: its name, and its type
arguments when written. -/
def genericCallee : Val → Option (String × Option (List VTy))
  | .var _ h => some (h, none)
  | .defApp _ h args => some (h, some args)
  | _ => none

/-- The written type of the `def` a callee names, for the names of its lifetime parameters. -/
def calleeTy (c : TCx) : Val → Option VTy
  | .var _ h | .defApp _ h _ => (c.E.scope.findDef h).map (·.ty)
  | .unbang _ f | .inst _ f _ => calleeTy c f
  | _ => none

/-- A callee: a template, with its type arguments when written; a core `def` with type
parameters; or any function, elaborated, with the written type of the `def` it names. -/
inductive Head where
  | tmpl (t : Decl) (targs : Option (List VTy))
  | gdef (name : String) (ps : List String) (ty : VTy)
  | plain (f : Val) (ty : Option VTy)

mutual
/-- A value with its surface forms elaborated; `exp` is the type expected of it, when known. -/
def surfV : Nat → TCx → Option CVTy → Val → DM Val
  | 0, _, _, V => pure V
  | n + 1, c, exp, V => match V with
    | .sugar sp (.lit k) => pure (litAt sp ((widthOf exp).getD .w32) k)
    | .app sp (.sugar osp (.op o)) (.pair psp a b) => do
      let arith := match o with | .add | .sub | .mul => true | _ => false
      -- The width: expected of an arithmetic result, or an operand's other than a literal's
      -- (a literal takes the width of the other operand); `i32` by default.
      let a₀ ← surfV n c none a
      let b₀ ← surfV n c none b
      let isLit : Val → Bool := fun | .sugar _ (.lit _) => true | _ => false
      let wOf (v v₀ : Val) : Option BoCa.Width := if isLit v then none else widthOf (c.tyV v₀)
      let w := ((if arith then widthOf exp else none).orElse fun _ =>
        (wOf a a₀).orElse fun _ => wOf b b₀).getD .w32
      let a' ← surfV n c (some (.int w)) a
      let b' ← surfV n c (some (.int w)) b
      if w == .w8 then return byteOp sp osp psp o a' b'
      pure (.app sp (.unbang osp (.const osp (.host (o.host w)))) (.pair psp a' b'))
    | .app sp (.sugar ksp (.call k)) W => do
      let W' ← surfV n c none W
      match k, W' with
      | "alloc", W' => do
        let A ← need W.span "`alloc`'s argument" ((← refresh c).tyV W')
        pure (.app sp (.const ksp (.alloc (← c.surface ksp A))) W')
      | "free", W' => do
        let A ← match (← refresh c).tyV W' with
          | some (.ref A) => pure A
          | _ => throw ⟨W.span, "`free` takes a cell, `ref A`"⟩
        pure (.app sp (.const ksp (.free (← c.surface ksp A))) W')
      | "swap", .pair _ r v => do
        let A ← match c.tyV r with
          | some (.ref A) => pure A
          | _ => throw ⟨W.span, "`swap` takes a cell, `ref A`, and a value"⟩
        let B ← need W.span "`swap`'s value" (c.tyV v)
        pure (.app sp (.app sp (.const ksp (.swap (← c.surface ksp A) (← c.surface ksp B))) r) v)
      | "clone", .var _ x => do
        -- An explicit copy: the variable itself, at the span of `clone(x)`, recorded so that
        -- the check of implicit copies knows it is written (decision 39).
        let A ← need W.span "`clone`'s argument" ((← refresh c).tyV W')
        unless Class.of A == .persistent do
          throw ⟨ksp, s!"`clone` copies a persistent value, and `{ppT A}` is not persistent"⟩
        note sp cloneOrigin
        pure (.var sp x)
      | "clone", _ => throw ⟨W.span, "`clone` takes a variable: `clone(x)`"⟩
      | k, _ => throw ⟨ksp, s!"`{k}` is written with its arguments: `{k}(…)`"⟩
    | .app sp (.sugar k .genBlock) (.thunk tsp M) => do
      -- `gen { S }`: elaborated as a generator after specialization (`specV`).
      pure (.app sp (.sugar k .genBlock) (.thunk tsp (← surfC n c none M)))
    | .app sp (.sugar _ .brace) (.thunk tsp M) => do
      let c' := c.pushDead
      let M' ← surfC n c' none M
      if (loopsAt c' none M').isNone then return .thunk tsp M'
      -- A block whose body loops: the loop that runs it at its first observation.
      let B ← match exp.bind loopOf with
        | some (B, _) => pure B
        | none => need sp "the block's result" ((resultOfC ((← refresh c).tyC M')).map Frontend.Elab.direct)
      let cx ← (loopCxOf sp B M' : Except Error LoopCx)
      let M'' ← (divBody cx c M' : SM Comp)
      let abort ← (template sp "a block that loops (`div_defer`)" s!"return {cx.rSrc}" : SM Comp)
      modify fun st => { st with any := true }
      let Bs ← c.surface sp B
      let Rs ← c.surface sp cx.R
      -- Ascribed its loop type, it is the loop as a value, not a call run in direct style.
      pure (.ascribe sp (.app sp (.defApp sp "div_defer" [Bs, Rs]) (.thunkv sp (.with_ sp M'' abort)))
        (.thunk sp (.loop sp Bs Rs)))
    | .app sp (.sugar dsp .deref) V => do
      let V' ← surfV n c none V
      -- `*e`: `withload` at the identity, reading a persistent content (its view is itself).
      let y : Ident := ⟨s!"io_ly{dsp.start.line}_{dsp.start.col}", dsp⟩
      let load (a : Frontend.Life) (As : VTy) (b : Val) : Val :=
        .app sp (.app sp (.const dsp (.withload a y As As)) b)
          (.thunkv sp (.lamL sp y (.dom sp) (.ret sp (.thunkv sp (.lam sp ⟨"io_dv", sp⟩
            (.view sp (.var sp y.name) As) (.ret sp (.boxed sp (.var sp y.name) (.var sp "io_dv"))))))))
      let content (A : CVTy) : DM VTy := do
        unless Class.of A == .persistent do
          throw ⟨dsp, s!"`*` copies the content, and `{ppT A}` is not persistent"⟩
        (c.surface dsp A : Except Error VTy)
      match (← refresh c).tyV V', V' with
      | some (.imm a A), _ =>
        pure (load (← (c.surfaceL dsp a : Except Error Frontend.Life)) (← content A) V')
      | some (.ref A), .var vsp x => do
        -- An owned cell: borrowed `imm` around the read, and handed back to its name.
        let As ← content A
        lendBorrow c dsp ⟨x, vsp⟩ .imm A A fun l mv =>
          boxedResult sp l (.ret sp (load (.var sp l) As (.var sp mv)))
      | t, _ => throw ⟨dsp, s!"`*` reads an `imm` borrow or a cell, but this has type " ++
          s!"`{(t.map ppT).getD "?"}`"⟩
    | .app sp (.sugar _ .brace) (.bangThunk tsp M) => do
      pure (.bangThunk tsp (← surfC n c.pushDead none M))
    | .app sp (.app sp₂ (.sugar ksp (.borrow .modify _)) (.lend psp px pm))
        (.thunkv tsp (.lam lsp b _ S)) => do
      -- `modify &mut x { … }`: `x` borrowed around the `withswap` (a cell or a scoped cell).
      unless pm == .mut do throw ⟨psp, s!"`modify` changes the place: lend it with `&mut {px.name}`"⟩
      let A ← match c.tyV (.var psp px.name) with
        | some (.ref A) => pure A
        | some (.mut ..) | some (.imm ..) =>
          throw ⟨psp, s!"`{px.name}` is a borrow: `modify {px.name} \{ … }` takes it as it is"⟩
        | some A => pure A
        | none => throw ⟨psp, s!"the type of `{px.name}` is not determined here: ascribe it"⟩
      let S' ← surfC n (c.push b.name (some A)) none S
      let X ← need tsp "`modify`'s body" (resultOfC (((← refresh c).push b.name (some A)).tyC S'))
      let (S'', B) := match X with
        | .tensor A' B => if A' = A then (S', B) else (unitTail S', .unit)
        | _ => (unitTail S', .unit)
      let As ← (c.surface ksp A : Except Error VTy)
      let Bs ← (c.surface ksp B : Except Error VTy)
      lendBorrow c sp px .mut A B fun l mv =>
        .bind sp ⟨"io_mw", sp⟩ none
          (.ret sp (.app sp (.app sp (.const ksp (.withswap (.var ksp l) As Bs)) (.var sp mv))
            (.thunkv tsp (.lam lsp b As S''))))
          (.letPair sp ⟨"io_mm", sp⟩ ⟨"io_mr", sp⟩ (.var sp "io_mw")
            (.ret sp (.boxed sp (.var sp l) (.var sp "io_mr")))) false
    | .app sp (.app sp₂ (.sugar ksp (.borrow k x)) P) (.thunkv tsp (.lam lsp b _ S)) => do
      let P' ← surfV n c none P
      let tP ← need P.span "the borrowed place" (c.tyV P')
      match k, tP with
      | .imm, .ref A | .mut, .ref A => do
        let dom ← need lsp "the block's bound" (c.elabL (.dom lsp))
        let c₁ := c.pushLife x dom
        let some v := c₁.E.lenv.lookup x | throw ⟨lsp, "internal error: a borrow block"⟩
        let Tb : CVTy := if k == .imm then .imm (.var v) A else .mut (.var v) A
        let S' ← surfC n (c₁.push b.name (some Tb)) none S
        -- A body that yields is a generator made in the block (`Parser.borrowBlock`), elaborated
        -- here, where the borrow is in scope: the typing of the block then rejects it, since its
        -- result is boxed at `'x` and a thunk has no outlives rule.  `[spec §15]`
        let S' ← match S' with
          | .ret rsp (.app gsp (.sugar _ .genBlock) (.thunk _ M)) => do
            let (g, _) ← (genValue (c₁.push b.name (some Tb)) gsp M none none
              "the generator of a borrow block that yields" : SM (Val × CVTy))
            pure (Comp.ret rsp g)
          | S' => pure S'
        let B ← need tsp "the block's result" (resultOfC (((← refresh c₁).push b.name (some Tb)).tyC S'))
        if BoCa.Fig16.LogRel.Core.Check.vfreeB v B then
          throw (Frontend.Elab.LoopLend.escapeError tsp x (Frontend.Check.ppV c₁.E.lenv 0 0 B))
        let As ← c.surface ksp A
        let Bs ← c.surface ksp B
        let xi : Ident := ⟨x, ksp⟩
        let C := if k == .imm then Const.withbor1 xi As Bs else .withbor2 xi (.top ksp) As Bs
        let Tbs := if k == .imm then VTy.imm lsp (.var lsp x) As else .mut lsp (.var lsp x) As
        pure (.app sp (.app sp₂ (.const ksp C) P') (.thunkv tsp (.lamL lsp xi (.dom lsp)
          (.ret lsp (.thunkv lsp (.lam lsp b Tbs (boxTail x S')))))))
      | .imm, .fam (.ref A) | .mut, .fam (.ref A) => do
        -- An owned array lent as a family of leaf borrows, with no cell (`slice_borrow_*`,
        -- SPEC §9).
        let dom ← need lsp "the block's bound" (c.elabL (.dom lsp))
        let c₁ := c.pushLife x dom
        let some v := c₁.E.lenv.lookup x | throw ⟨lsp, "internal error: a borrow block"⟩
        let Tb : CVTy := .fam (if k == .imm then .imm (.var v) A else .mut (.var v) A)
        let S' ← surfC n (c₁.push b.name (some Tb)) none S
        let B ← need tsp "the block's result" (resultOfC (((← refresh c₁).push b.name (some Tb)).tyC S'))
        if BoCa.Fig16.LogRel.Core.Check.vfreeB v B then
          throw (Frontend.Elab.LoopLend.escapeError tsp x (Frontend.Check.ppV c₁.E.lenv 0 0 B))
        let As ← c.surface ksp A
        let Bs ← c.surface ksp B
        let xi : Ident := ⟨x, ksp⟩
        let C := if k == .imm then Const.sliceBorrowImm xi (.top ksp) As Bs
          else .sliceBorrowMut xi (.top ksp) As Bs
        let Tbs := if k == .imm then VTy.arrayImm lsp (.var lsp x) As else .arrayMut lsp (.var lsp x) As
        pure (.app sp (.app sp₂ (.const ksp C) P') (.thunkv tsp (.lamL lsp xi (.dom lsp)
          (.ret lsp (.thunkv lsp (.lam lsp b Tbs (boxTail x S')))))))
      | .famMut, .tensor (.ref A) (.ref B) => do
        let dom ← need lsp "the block's bound" (c.elabL (.dom lsp))
        let c₁ := c.pushLife x dom
        let some v := c₁.E.lenv.lookup x | throw ⟨lsp, "internal error: a borrow block"⟩
        let Tb : CVTy := .tensor (.mut (.var v) A) (.mut (.var v) B)
        let S' ← surfC n (c₁.push b.name (some Tb)) none S
        let T ← need tsp "the block's result" (resultOfC (((← refresh c₁).push b.name (some Tb)).tyC S'))
        if BoCa.Fig16.LogRel.Core.Check.vfreeB v T then
          throw (Frontend.Elab.LoopLend.escapeError tsp x (Frontend.Check.ppV c₁.E.lenv 0 0 T))
        let As ← c.surface ksp A
        let Bs ← c.surface ksp B
        let Ts ← c.surface ksp T
        let xi : Ident := ⟨x, ksp⟩
        let C := Const.withborF2Mut xi ⟨x ++ "_a", ksp⟩ ⟨x ++ "_b", ksp⟩ (.top ksp) As Bs Ts
        let Tbs := VTy.tensor lsp (.mut lsp (.var lsp x) As) (.mut lsp (.var lsp x) Bs)
        pure (.app sp (.app sp₂ (.const ksp C) P') (.thunkv tsp (.lamL lsp xi (.dom lsp)
          (.ret lsp (.thunkv lsp (.lam lsp b Tbs (boxTail x S')))))))
      | .modify, .mut a A => do
        let S' ← surfC n (c.push b.name (some A)) none S
        let X ← need tsp "`modify`'s body" (resultOfC (((← refresh c).push b.name (some A)).tyC S'))
        let (S'', B) := match X with
          | .tensor A' B => if A' = A then (S', B) else (unitTail S', .unit)
          | _ => (unitTail S', .unit)
        let C := Const.withswap (← c.surfaceL ksp a) (← c.surface ksp A) (← c.surface ksp B)
        pure (.app sp (.app sp₂ (.const ksp C) P')
          (.thunkv tsp (.lam lsp b (← c.surface lsp A) S'')))
      | _, _ => throw ⟨P.span, s!"this borrow block's place has type `{ppT tP}`: `borrow imm`/" ++
          "`borrow mut` take a cell `ref A` or an array (a pair of cells for a family), `modify` a `mut` " ++
          "borrow"⟩
    | .app sp f W => do
      -- A call of a generic function: its type and lifetime arguments filled.
      if let some V' ← genericCall n c sp exp f W then return V'
      let f' ← surfV n c none f
      if W.lends then
        if let some V' ← lendCall c sp f' (← surfV n c none W) then return V'
      let tf := c.tyV f'
      let (f', pW) := match tf with
        | some (.bang (.thunk (.arr A _))) => (Val.unbang f.span f', some A)
        | some (.thunk (.arr A _)) => (f', some A)
        | _ => (f', none)
      pure (.app sp f' (← surfV n c pW W))
    | .thunkv sp (.lam lsp x A M) =>
      if isHoleTy A then do
        let (A', C) ← match exp with
          | some (.thunk (.arr A' C)) => pure (A', C)
          | _ => throw ⟨lsp, s!"the type of the closure's parameter `{x.name}` is not " ++
              "determined here: pass it where a function type is expected, or write `thunkv fun`"⟩
        pure (.thunkv sp (.lam lsp x (← c.surface lsp A') (← surfC n (c.push x.name (some A')) (some C) M)))
      else do pure (.thunkv sp (← surfC n c (exp.bind fun | .thunk C => some C | _ => none) (.lam lsp x A M)))
    | .bangThunkv sp (.lam lsp x A M) =>
      if isHoleTy A then do
        let (A', C) ← match exp with
          | some (.bang (.thunk (.arr A' C))) => pure (A', C)
          | _ => throw ⟨lsp, s!"the type of the closure's parameter `{x.name}` is not " ++
              "determined here: pass it where a function type is expected, or write `!thunkv fun`"⟩
        pure (.bangThunkv sp (.lam lsp x (← c.surface lsp A') (← surfC n (c.push x.name (some A')) (some C) M)))
      else do
        pure (.bangThunkv sp (← surfC n c (exp.bind fun | .bang (.thunk C) => some C | _ => none)
          (.lam lsp x A M)))
    | .pair sp V W => do
      let (a, b) := match exp with
        | some (.tensor A B) => (some A, some B)
        | _ => (none, none)
      pure (.pair sp (← surfV n c a V) (← surfV n c b W))
    | .inl sp V => do pure (.inl sp (← surfV n c (match exp with | some (.sum A _) => some A | _ => none) V))
    | .inr sp V => do pure (.inr sp (← surfV n c (match exp with | some (.sum _ B) => some B | _ => none) V))
    | .ascribe sp V A => do pure (.ascribe sp (← surfV n c (c.elabV A) V) A)
    | .unbang sp V => do pure (.unbang sp (← surfV n c (exp.map .bang) V))
    | .boxed sp l V => do pure (.boxed sp l (← surfV n c none V))
    | .unbox sp V => do pure (.unbox sp (← surfV n c none V))
    | .sub sp V l => do pure (.sub sp (← surfV n c none V) l)
    | .roll sp V => do
      let e := match exp with
        | some (.mu A) => some (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)
        | _ => none
      pure (.roll sp (← surfV n c e V))
    | .unroll sp V => do pure (.unroll sp (← surfV n c none V))
    | .inst sp V l => do
      -- A persistent function with lifetime parameters is instantiated through `unbang`.
      let V' ← surfV n c none V
      match (← refresh c).tyV V' with
      | some (.bang (.thunk (.all ..))) => pure (.inst sp (.unbang V.span V') l)
      | _ => pure (.inst sp V' l)
    | .defApp sp h args => do
      -- A template at written type arguments: its instance.
      match (← get).templates.find? (fun | .def_ _ m _ _ _ _ => m.name == h | _ => false) with
      | some t => pure (.var sp (← makeInst n c sp t (args.map c.elabV).toArray))
      | none => pure V
    | .shorten sp m σ l V => do pure (.shorten sp m σ l (← surfV n c none V))
    | .thunk sp M => do
      pure (.thunk sp (← surfC n c.pushDead (exp.bind fun | .thunk C => some C | _ => none) M))
    | .thunkv sp M => do
      pure (.thunkv sp (← surfC n c (exp.bind fun | .thunk C => some C | _ => none) M))
    | .bangThunk sp M => do
      pure (.bangThunk sp (← surfC n c.pushDead (exp.bind fun | .bang (.thunk C) => some C | _ => none) M))
    | .bangThunkv sp M => do
      pure (.bangThunkv sp (← surfC n c (exp.bind fun | .bang (.thunk C) => some C | _ => none) M))
    | .run sp M => do pure (.run sp (← surfC n c (exp.map .ret) M))
    | V => pure V

/-- A computation with its surface forms elaborated; `exp` is its type, when known. -/
def surfC : Nat → TCx → Option CCTy → Comp → DM Comp
  | 0, _, _, M => pure M
  | n + 1, c, exp, M => match M with
    | .ret sp V => do pure (.ret sp (← surfV n c (match exp with | some (.ret A) => some A | _ => none) V))
    | .absurd sp V => do pure (.absurd sp (← surfV n c (some .zero) V))
    | .bind sp x A M N lin => do
      -- A borrow block over a loop, or a `let r = &x`: lent per observation (`LoopLend`).
      if let some L ← (Frontend.Elab.LoopLend.hook c sp x A M N lin : Except Error (Option Comp)) then
        return (← surfC n c exp L)
      let M' ← surfC n c ((A.bind c.elabV).map .ret) M
      let c ← refresh c
      let N' ← surfC n (c.push x.name (bindTy c A M')) exp N
      pure (.bind sp x A M' N' lin)
    | .lam sp x A M => do
      let (A', C) := match exp with
        | some (.arr A' C) => (some A', some C)
        | _ => (c.elabV A, none)
      let As ← if isHoleTy A then c.surface sp (← need sp s!"`{x.name}`" A') else pure A
      pure (.lam sp x As (← surfC n (c.push x.name (c.elabV As)) C M))
    | .app sp M x => do pure (.app sp (← surfC n c none M) x)
    | .with_ sp M N => do
      let (a, b) := match exp with
        | some (.amp C D) => (some C, some D)
        | _ => (none, none)
      pure (.with_ sp (← surfC n c.pushDead.pushDead a M) (← surfC n c.pushDead.pushDead b N))
    | .proj sp i M => do pure (.proj sp i (← surfC n c none M))
    | .letUnit sp V M => do pure (.letUnit sp (← surfV n c (some .unit) V) (← surfC n c exp M))
    | .letPair sp x y V M => do
      let V' ← surfV n c none V
      let c ← refresh c
      let (Ax, Ay) := pairTys c V'
      pure (.letPair sp x y V' (← surfC n ((c.push x.name Ax).push y.name Ay) exp M))
    | .case sp V x M y N => do
      let V' ← surfV n c none V
      let c ← refresh c
      let (Ax, Ay) := sumTys c V'
      pure (.case sp V' x (← surfC n (c.push x.name Ax) exp M) y (← surfC n (c.push y.name Ay) exp N))
    | .lamL sp x b M => do
      let bl := (c.elabL b).getD .top
      let e := match exp with | some (.all _ _ C) => some C | _ => none
      pure (.lamL sp x b (← surfC n (c.pushLife x.name bl) e M))
    | .inst sp M a => do pure (.inst sp (← surfC n c none M) a)
    | .nuIn sp M => do pure (.nuIn sp (← surfC n c (exp.bind fun | .nu B => some B.unroll | _ => none) M))
    | .nuOut sp M => do pure (.nuOut sp (← surfC n c none M))
    | .ascribe sp M C => do pure (.ascribe sp (← surfC n c (c.E.elabC c.Δ C).toOption M) C)
    | .for_ sp x V M N => do
      let V' ← surfV n c none V
      let c ← refresh c
      let el := ((← refresh c).tyV V').bind elemOf
      let M' ← surfC n (c.push x.name el) none M
      -- `let r = for …; N`: `r` has the type the iterator finishes with.
      match N.forRes? with
      | some (r, A, N₀) =>
        let rT := (A.bind c.elabV).orElse fun _ => (c.tyV V'.takeLends.1).bind finOf
        let N₀' ← surfC n (c.push r.name rT) exp N₀
        pure (.for_ sp x V' M' (.bind N.span r A (.ret r.span (.sugar r.span .forRes)) N₀' false))
      | none => pure (.for_ sp x V' M' (← surfC n c exp N))
    | M => pure M

/-- A declaration with its surface forms elaborated, in the context the checker checks it in. -/
def surfDecl : Nat → Decl → DM Decl
  | 0, d => pure d
  | n + 1, .def_ sp nm ps A V mk => do
    let st ← get
    let c := TCx.ofScope (st.lib ++ st.out) false
    pure (.def_ sp nm ps A (← surfV n c (c.elabV A) V) mk)
  | n + 1, .main sp C M => do
    let st ← get
    let caps := capNames.map fun x => Decl.extern Span.none ⟨x, Span.none⟩ (capTy Span.none x)
    let c := TCx.ofScope (st.lib ++ st.out ++ caps) true
    let exp := match (c.E.elabC c.Δ C).toOption with
      | some (.ret A) => some (BoCa.Fig16.LogRel.Core.CTy.ret A)
      | e => e
    set { st with caps := caps }
    let M' ← surfC n c exp M
    modify fun st => { st with caps := [] }
    pure (.main sp C M')
  | _, d => pure d

/-- The instance of the template `t` at the type arguments `σ` (one per type parameter, each
known): its name, made and elaborated on first use.  `[spec §15]` -/
def makeInst : Nat → TCx → Span → Decl → Array (Option CVTy) → DM String
  | 0, _, sp, _, _ => throw ⟨sp, "instantiation of generic functions does not terminate"⟩
  | n + 1, c, sp, t, σ => do
    let .def_ tsp tn ps A V mk := t | throw ⟨sp, "internal error: a generic function"⟩
    let names := ps.map (·.name)
    let mut σs : TySubst := []
    for (x, t) in names.zip σ.toList do
      let some t := t
        | throw ⟨sp, s!"the type `{x}` of `{tn.name}` is not determined by its arguments: " ++
            s!"write them, `{tn.name}[…](…)`"⟩
      let ts ← c.surface sp t
      if ts.pp.contains '\'' then
        throw ⟨sp, s!"`{tn.name}` is instantiated at `{ts.pp}`, which has a lifetime: a generic " ++
          "function is instantiated at types without one"⟩
      σs := σs ++ [(x, ts)]
    let key := (tn.name, σs.map (·.2.strip))
    let st ← get
    if let some name := st.insts.lookup key then return name
    let name := s!"{tn.name}__g{st.insts.length}"
    let mk' := match mk with
      | .gen E => Mark.gen (E.subst σs)
      | .template m => m
      | mk => mk
    let inst := Decl.def_ tsp ⟨name, tn.span⟩ [] (A.subst σs) (V.subst σs) mk'
    let inst := Elab.fillDecl (st.lib ++ st.out) st.caps inst
    let st' ← (elabDecl n { st with insts := (key, name) :: st.insts } inst : SM DivSt)
    set st'
    return name

/-- A call `f W` of a generic callee (a template, a core `def` with type parameters, or a
function with lifetime parameters), with the type and lifetime arguments it leaves out filled and
`unbang` inserted; `none` when the callee is none of these. `exp` is the type expected of the
call's result. -/
def genericCall : Nat → TCx → Span → Option CVTy → Val → Val → DM (Option Val)
  | 0, _, _, _, _, _ => pure none
  | n + 1, c, sp, exp, f, W => do
    let st ← get
    let isLocal (h : String) : Bool := c.locals.any (·.1 == h)
    let head ← match genericCallee f with
      | some (h, targs) =>
        match (if isLocal h then none else
            st.templates.find? (fun | .def_ _ m _ _ _ _ => m.name == h | _ => false)) with
        | some t => pure (Head.tmpl t targs)
        | none => match targs, (if isLocal h then none else c.E.scope.findDef h) with
          | none, some d =>
            if d.params.isEmpty then pure (Head.plain f (some d.ty))
            else pure (Head.gdef h (d.params.map (·.name)) d.ty)
          | _, _ => do
            let f' ← surfV n c none f
            pure (Head.plain f' (calleeTy c f'))
      | none => do
        let f' ← surfV n c none f
        pure (Head.plain f' (calleeTy c f'))
    let (fname, ps, pat?, tyW) : String × List String × Option CVTy × Option VTy := match head with
      | .tmpl (.def_ _ tn tps A _ _) _ =>
        (tn.name, tps.map (·.name), patOf c (tps.map (·.name)) A, some A)
      | .tmpl _ _ => ("?", [], none, none)
      | .gdef h tps A => (h, tps, patOf c tps A, some A)
      | .plain f' ty =>
        ((genericCallee f).map (·.1) |>.getD "the function", [], c.tyV f', ty)
    let generic := !ps.isEmpty
    let some pat := pat?
      | if generic then throw ⟨f.span, s!"the type of `{fname}` does not elaborate here"⟩
        else return none
    let some sig := sigOf pat
      | if generic then throw ⟨f.span, s!"`{fname}` is not a function"⟩ else return none
    if !generic && sig.binders.isEmpty then return none
    -- The names of the lifetime parameters, for errors.
    let lnames := (tyW.map lifeNames).getD []
    let lnames := lnames.drop (lnames.length - sig.binders.length)
    let lname (v : BoCa.Lifetime.LifeVar) : String :=
      match (sig.binders.map (·.1)).idxOf? v with
      | some k => let x := lnames.getD k "?"; if x.startsWith "'" then x else "'" ++ x
      | none => "'?"
    -- How the lifetimes are written at a call: after the type arguments, which are then written.
    let writeLives (h : String) : String :=
      let ls := String.intercalate "" (sig.binders.map fun _ => "['x]")
      if generic then s!"{h}[…]{ls}(…)`, the types and then the lifetimes"
      else s!"{h}{ls}(…)`, one lifetime per parameter"
    let comps := compsC sig.P W
    let mut m : MatchSt := { ty := Array.replicate ps.length none, binders := sig.binders.map (·.1) }
    if let .tmpl _ (some as) := head then
      if as.length != ps.length then
        throw ⟨sp, s!"`{fname}` takes {ps.length} type arguments"⟩
      for (a, k) in as.zipIdx do
        m := { m with ty := m.ty.set! k (c.elabV a) }
    let mut args : Array (Option Val) := Array.replicate comps.length none
    let mut tys : Array (Option CVTy) := Array.replicate comps.length none
    let mut c := c
    for pass in [0, 1] do
      for ((Pi, Wi), k) in comps.zipIdx do
        if args[k]!.isSome then continue
        if pass == 0 && checkOnly Wi && m.isOpen Pi then continue
        let pat' := m.solved Pi
        let opn := m.isOpen Pi
        -- A lent place: its content matches the borrow's, and `lendCall` lends it.
        if let .lend _ x _ := Wi then
          match pat', c.tyV (.var x.span x.name) with
          | .imm _ A, some (.ref A') | .mut _ A, some (.ref A') =>
            if let some m' := matchV m 0 A A' then m := m'
          | .imm _ A, some A' | .mut _ A, some A' =>
            if let some m' := matchV m 0 A A' then m := m'
          | _, _ => pure ()
          args := args.set! k (some Wi)
          continue
        -- A closure whose parameter's type is a hole: the parameter's, as solved.
        let Wi ← match Wi, pat' with
          | .bangThunkv wsp (.lam lsp x Ax M), .bang (.thunk (.arr X _))
          | .thunkv wsp (.lam lsp x Ax M), .thunk (.arr X _) =>
            if isHoleTy Ax then
              if hasPhV X || m.binders.any (BoCa.Fig16.LogRel.Core.Check.vfreeB · X) then
                throw ⟨lsp, s!"the type of the closure's parameter `{x.name}` is not determined " ++
                  s!"by the other arguments of `{fname}`: write it"⟩
              let Xs ← c.surface lsp X
              pure (match Wi with
                | .bangThunkv .. => Val.bangThunkv wsp (.lam lsp x Xs M)
                | _ => Val.thunkv wsp (.lam lsp x Xs M))
            else pure Wi
          | Wi, _ => pure Wi
        let Wi' ← surfV n c (if opn then none else some pat') Wi
        c ← refresh c
        let some T := c.tyV Wi'
          | if !opn then
              args := args.set! k (some Wi')
              continue
            else if pass == 0 then continue
            else throw ⟨Wi.span, s!"the type of this argument of `{fname}` is not determined here"⟩
        -- A callback that loops or yields where a function is expected: its result is what its
        -- loop or generator finishes with (it is specialized at its own type, `specV`), unless
        -- the parameter's result is itself a loop or a generator.
        let T := if (matchV m 0 Pi T).isSome then T else match Pi, T with
          | .thunk (.arr _ (.ret Q)), .thunk (.arr A' (.ret L))
          | .bang (.thunk (.arr _ (.ret Q))), .bang (.thunk (.arr A' (.ret L))) =>
            if !hasPhV Q then T else
            match ((loopOf L).map (·.1)).orElse fun _ => (genOf L).map (·.2.1) with
            | some B' => match T with
              | .bang _ => .bang (.thunk (.arr A' (.ret B')))
              | _ => .thunk (.arr A' (.ret B'))
            | none => T
          | _, _ => T
        match matchV m 0 Pi T with
        | some m' => m := m'
        | none =>
          if generic then
            let written : String := match (tyW.bind paramTy).map (argComps · W) with
              | some cs => ((cs[k]?).map fun (q : VTy × Val) => q.1.pp).getD (ppT (m.solved Pi))
              | none => ppT (m.solved Pi)
            throw ⟨Wi.span, s!"this argument of `{fname}` has type `{ppT T}`, which is not " ++
              s!"`{written}`"⟩
        args := args.set! k (some Wi')
        tys := tys.set! k (some T)
    -- What the arguments leave open, from the type expected of the result.
    if let (some e, .ret Q) := (exp, sig.R) then
      if m.isOpen Q then
        if let some m' := matchV m 0 Q e then m := m'
    let lends := W.lends
    for (v, _) in sig.binders do
      if (m.life.lookup v).isNone && !(lends && sig.binders.length == 1) then
        throw ⟨sp, s!"the lifetime `{lname v}` of `{fname}` is not determined by its arguments " ++
          s!"here: write it, `{writeLives fname}"⟩
    -- The callee at its type arguments.
    let base ← match head with
      | .tmpl t _ => do pure (Val.var f.span (← makeInst n c sp t m.ty))
      | .gdef h tps _ => do
        let mut ts : List VTy := []
        for (x, t) in tps.zip m.ty.toList do
          let some t := t
            | throw ⟨sp, s!"the type `{x}` of `{h}` is not determined by its arguments: " ++
                s!"write them, `{h}[…](…)`"⟩
          ts := ts ++ [← c.surface sp t]
        pure (Val.defApp f.span h ts)
      | .plain f' _ => pure f'
    c ← refresh c
    let argsL := args.toList.filterMap id
    if lends then
      if sig.binders.length != 1 then
        throw ⟨sp, s!"`{fname}` has several lifetime parameters: a lend `&x` in its call is " ++
          "not provided; borrow in a block and pass the borrow"⟩
      match ← lendCall c sp base (argOf W argsL) with
      | some V => return some V
      | none => throw ⟨sp, s!"the lend in this call of `{fname}` is not at a borrow parameter"⟩
    let mut g := if sig.bang then Val.unbang f.span base else base
    for (v, _) in sig.binders do
      let some l := m.life.lookup v | throw ⟨sp, "internal error: a lifetime parameter"⟩
      g := .inst sp g (← c.surfaceL sp l)
    -- An argument that gave a lifetime parameter a longer lifetime than the meet is shortened.
    let mut args' : List Val := []
    for (((Pi, _), Wi'), k) in (comps.zip argsL).zipIdx do
      if m.conflicts.isEmpty then args' := args' ++ [Wi']; continue
      let Pf := m.solved Pi
      match tys[k]!, Pf with
      | some (.imm a _), .imm a' _ | some (.mut a _), .mut a' _ =>
        if a == a' then args' := args' ++ [Wi']
        else args' := args' ++ [.sub Wi'.span Wi' (← c.surfaceL sp a')]
      | some T, _ =>
        match m.conflicts.find? (BoCa.Fig16.LogRel.Core.Check.vfreeB · Pi) with
        | some v =>
          if T != Pf then
            throw ⟨Wi'.span, s!"the lifetime `{lname v}` of `{fname}` is given different lifetimes " ++
              "by its arguments, and this one cannot be shortened to their meet: write it, " ++
              s!"`{writeLives fname}"⟩
          args' := args' ++ [Wi']
        | none => args' := args' ++ [Wi']
      | none, _ => args' := args' ++ [Wi']
    return some (.app sp g (argOf W args'))

/-- Elaborate one declaration: first the copies its calls need (each elaborated the same way),
then its own divergence, with its calls renamed to the copies.  `[spec §14]` -/
def elabDecl : Nat → DivSt → Decl → SM DivSt
  | 0, _, d => throw ⟨(match d with | .def_ sp .. | .main sp .. => sp | _ => Span.none),
      "specialization at callback types does not terminate"⟩
  | fuel + 1, st, d => do
    -- A generic generator or function is a template, instantiated where it is called.
    if let .def_ _ _ (_ :: _) _ _ (.gen _) := d then
      return { st with templates := st.templates ++ [d] }
    if let .def_ _ _ (_ :: _) _ _ (.template _) := d then
      return { st with templates := st.templates ++ [d] }
    -- A div function taking a borrow takes the owner, lent at each step (`LoopLend.lentDef`).
    let d := (← (Frontend.Elab.LoopLend.lentDef (TCx.ofScope (st.lib ++ st.out) false) d :
      Except Error (Option Decl))).getD d
    let (d, st) ← (surfDecl fuel d).run st
    let (d, st) ← (specDecl fuel d).run st
    -- In a copy made at a callback that yields, the calls through the callback delegate to it.
    let d := match d with
      | .def_ sp nm ps A V mk => match st.genCopies.lookup nm.name, V with
        | some Fs, .bangThunkv vsp (.lam lsp x Ax M) | some Fs, .thunkv vsp (.lam lsp x Ax M) =>
          let c := (TCx.ofScope (st.lib ++ st.out) false).push x.name
            ((TCx.ofScope (st.lib ++ st.out) false).elabV Ax)
          let M' := delegateC Fs divFuel c M
          let V' := match V with
            | .bangThunkv .. => Val.bangThunkv vsp (.lam lsp x Ax M')
            | _ => Val.thunkv vsp (.lam lsp x Ax M')
          .def_ sp nm ps A V' mk
        | _, _ => d
      | d => d
    -- `yield` outside a generator's body.
    let yieldSp := match d with
      | .def_ _ _ _ _ _ (.gen _) => none
      | .def_ _ _ _ _ V _ => V.sugarAt isYieldKw
      | .main _ _ M => M.sugarAt isYieldKw
      | _ => none
    if let some ysp := yieldSp then
      throw ⟨ysp, "`yield` is in the body of a generator only, a `gen fn` or a `gen { … }` " ++
        "block; so is a call whose callback yields, which delegates to the generator it makes"⟩
    if let .def_ _ _ _ _ _ (.gen _) := d then
      let d' ← genDef (st.lib ++ st.out) d
      return { st with srcs := d :: st.srcs, out := st.out ++ [d'] }
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
    set { st with caps := caps }
    let M' ← specC n c M
    modify fun st => { st with caps := [] }
    pure (.main sp C M')
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
    -- At a callback that yields, the copy is a generator of what the callback yields.
    let c := TCx.ofScope (st.lib ++ st.out) false
    let gcb := ((c.elabV P').map genCallbacks).getD []
    let mark ← match gcb, hof.mark with
      | [], mk => pure mk
      | _, .gen E => pure (Mark.gen E)
      | Fc :: _, _ => match Fc with
        | .thunk (.arr _ (.ret G)) => match genOf G with
          | some (E, _, _) => do pure (Mark.gen (← (toSurface hof.sp E : Except Error VTy)))
          | none => pure hof.mark
        | _ => pure hof.mark
    let copy := if hof.bang then Decl.def_ hof.sp ⟨name, hof.name.span⟩ [] (.bang hof.P.span F)
        (.bangThunkv hof.sp lam) mark
      else Decl.def_ hof.sp ⟨name, hof.name.span⟩ [] F (.thunkv hof.sp lam) mark
    let genCopies := if gcb.isEmpty then st.genCopies else (name, gcb) :: st.genCopies
    let copies := ((hof.name.name, P'.strip), name) :: st.copies
    let st₁ : DivSt := { st with copies := copies, genCopies := genCopies }
    let st' ← (elabDecl n st₁ copy : SM DivSt)
    set st'
    pure name

/-- A value with its calls of higher-order functions specialized. -/
def specV : Nat → TCx → Val → DM Val
  | 0, _, V => pure V
  | n + 1, c, V => match V with
    | .app sp (.sugar _ .genBlock) (.thunk _ M) => do
      -- `gen { S }`: its body specialized first, then elaborated as a generator, typed among the
      -- declarations made so far (the copies its calls were renamed to).
      let M' ← specC n c M
      let st ← get
      let c' := { c with E := { c.E with scope := ⟨(st.lib ++ st.out ++ st.caps).toArray,
        (st.lib ++ st.out ++ st.caps).length⟩ } }
      let (g, _) ← (genValue c' sp M' none none "this `gen { … }` block" : SM (Val × CVTy))
      pure g
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
        let name ← copyOf n hof P's
        let call := Val.app sp (renameCallee name f) W'
        -- A function made a generator by a callback that yields: its call is a `yield from`.
        if (← get).genCopies.any (·.1 == name) && !(hof.mark matches .gen _) then
          return .app sp (.sugar sp .yieldFrom) call
        return call
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
      let el := (c.tyV V).bind elemOf
      let M' ← specC n (c.push x.name el) M
      match N.forRes? with
      | some (r, A, N₀) =>
        let rT := (A.bind c.elabV).orElse fun _ => (c.tyV V.takeLends.1).bind finOf
        let N₀' ← specC n (c.push r.name rT) N₀
        pure (.for_ sp x (← specV n c V) M' (.bind N.span r A (.ret r.span (.sugar r.span .forRes)) N₀' false))
      | none => pure (.for_ sp x (← specV n c V) M' (← specC n c N))
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
    pure (.ret sp (.thunk sp (.loop sp B (← toSurface sp cx.R))), ← divBody cx c M)
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
  -- The capabilities `main` uses ambiently are read off the program as written: an included
  -- module's externs (`include io`) do not make them declared.
  let p₀ := p
  let mayIO := !(ambientCaps p₀).isEmpty
  -- `include m`: the module's declarations, in place (at most once each).
  let (decls, incl) ← p.decls.foldlM (init := (([] : List Decl), ([] : List String))) fun (acc, inc) d =>
    match d with
    | .include sp m =>
      if inc.contains m.name then pure (acc, inc) else
      match libModules.lookup m.name with
      | some src => do pure (acc ++ (← libOf s!"lib/{m.name}.bc" src), m.name :: inc)
      | none => throw ⟨sp, s!"no library module `{m.name}`: the modules are " ++
          ", ".intercalate (libModules.map (·.1))⟩
    | d => pure (acc ++ [d], inc)
  let p : Program := ⟨decls⟩
  let mayDiv := usesName "div_fuel" p || usesName "div_bind" p || usesName "div_defer" p
  -- The prelude is in scope when the program names one of its declarations.
  let preludeNames := ["true", "false", "not", "to_i32", "to_u8"]
  let mayPrelude := !incl.contains "prelude" && preludeNames.any (usesName · p)
  let ioAll ← if mayIO && !incl.contains "io" then libOf "lib/io.bc" ioLibrary else pure []
  -- The generator library is in scope for typing when the program names it (`gen_pull` in
  -- `lib/adapters.bc`).
  let mayGen := ["gen_bind", "gen_bind_loop", "gen_pull"].any (usesName · p)
  let genAll ← if mayGen && !incl.contains "gen" then libOf "lib/gen.bc" genLibrary else pure []
  let divAll ← if mayDiv && !incl.contains "div" then libOf "lib/div.bc" divLibrary else pure []
  let preludeAll ← if mayPrelude then libOf "lib/prelude.bc" preludeLibrary else pure []
  let typing := preludeAll ++ ioAll ++ divAll ++ genAll
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
  let cs := ambientCaps p₀
  let ioLib ← if cs.isEmpty || incl.contains "io" then pure [] else
    if mayIO then pure ioAll else libOf "lib/io.bc" ioLibrary
  let exts := cs.map fun c => Decl.extern Span.none ⟨c, Span.none⟩ (capTy Span.none c)
  let mains ← decls.filterMapM fun
    | .main sp C M => do
      let (C', M') ← if cs.isEmpty then plainMain mc sp C M else ambientMain mc cs sp C M
      pure (some (Decl.main sp C' M'))
    | _ => pure none
  -- The divergence library when the elaborated program names it: a div body elaborated as a
  -- state machine (`divMachine`) does not.
  let uses (ns : List String) : Bool := (rest ++ mains).any fun
    | .def_ _ _ _ _ V _ => ns.any V.names | .main _ _ M => ns.any M.names | _ => false
  let needDiv := (anyDiv || mainLoops || mayDiv) && uses ["div_bind", "div_fuel", "div_defer"]
  let divLib ← if !needDiv || incl.contains "div" then pure [] else
    if mayDiv then pure divAll else libOf "lib/div.bc" divLibrary
  -- The generator library when an elaborated generator sequences with `gen_bind`.
  -- (A program that defines them itself, a core form written by hand, uses its own.)
  let genNames := ["gen_bind", "gen_bind_loop", "gen_pull"].filter fun n =>
    !(p.decls.any fun | .def_ _ m _ _ _ _ => m.name == n | _ => false)
  let usesBind := (rest ++ mains).any fun
    | .def_ _ _ _ _ V _ => genNames.any V.names | .main _ _ M => genNames.any M.names | _ => false
  let genLib ← if usesBind && !incl.contains "gen" then
    (if mayGen then pure genAll else libOf "lib/gen.bc" genLibrary) else pure []
  let lib := preludeAll ++ ioLib ++ divLib ++ genLib
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
