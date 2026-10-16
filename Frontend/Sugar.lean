import Frontend.Parser
import Frontend.Print
import Frontend.Check.Steps
import Frontend.Elab.Respan
import Frontend.Elab.RenameLife
import Frontend.Elab.Subst
import Frontend.Elab.Meta
import Frontend.Elab.LoopLend
import Frontend.Elab.Effects

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
  machine (`divMachine`, §15).
* **`&c`** in the head of `x <- M; N` becomes `r <- M[c/&c]; let (c, x) = r; N` (`Comp.elab`).

The generated code is a template, printed and parsed, whose holes are filled with the program's
own syntax, so errors inside the program's code keep its positions. The template's own nodes are
given the span of the sugar that produced them (`respan`), and the elaboration records that span
with the sugar's name in its **origins**, so that an error the checker finds in generated code is
reported at the sugar, with a note naming it (`Frontend.Elab.renderError`).
-/

namespace Frontend.Sugar
open Frontend.Check (mentionsV mentionsC)

/-- The library modules, by the name `include` gives them (#59). A module `m` is the file
`lib/m.bc`, read when `bcc` starts (`libSources`), so editing one rebuilds no Lean (#113); adding
one is adding its name here. The elaboration brings in `io`, `div` and `prelude` by itself
(`elaborateS`); `include m` brings in any of them. -/
def libNames : List String :=
  ["io", "div", "prelude", "lend", "adapters", "slice", "buf", "text", "textio", "iters", "fail",
   "yield", "rec", "aff", "async"]

/-- The directory of the library: `$BCC_LIB` when it is set; otherwise `lib/` of the checkout
whose `.lake/build/bin/` holds the running `bcc`; otherwise `lib/` of the working directory. -/
def libDir : IO System.FilePath := do
  if let some d ← IO.getEnv "BCC_LIB" then return d
  let app ← IO.appPath
  match app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent) with
  | some root => if ← (root / "lib" / "prelude.bc").pathExists then return root / "lib" else return "lib"
  | none => return "lib"

/-- Each library module's source, or why it could not be read: read once, when the program
starts. (A failure surfaces only when a program needs the module.) -/
initialize libSources : List (String × Except String String) ← do
  let dir ← try libDir catch _ => pure "lib"
  libNames.mapM fun m => do
    let f := dir / s!"{m}.bc"
    try pure (m, .ok (← IO.FS.readFile f)) catch e => pure (m, .error s!"cannot read {f}: {e}")

/-- The library module `m`'s source (`lib/m.bc`), or why it could not be read; `none` when there
is no module `m`. -/
def library (m : String) : Option (Except String String) := libSources.lookup m

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
  | .perform sp k i V => return .perform sp k i (← V.elab lend)
  | .abort sp k i V => return .abort sp k i (← V.elab lend)
  | .handle sp k hr hc M => return .handle sp k hr hc (← M.elab false)
  | .unwind sp x A M D N => return .unwind sp x A (← M.elab false) (← D.elab false) (← N.elab false)
  | .withbor2r sp x b A B r p m M => return .withbor2r sp x b A B r p m (← M.elab false)
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
  | .perform sp k i V => .perform sp k i (V.fill hv hc)
  | .abort sp k i V => .abort sp k i (V.fill hv hc)
  | .handle sp k hr hc' M => .handle sp k hr hc' (M.fill hv hc)
  | .unwind sp x A M D N => .unwind sp x A (M.fill hv hc) (D.fill hv hc) (N.fill hv hc)
  | .withbor2r sp x b A B r p m M => .withbor2r sp x b A B r p m (M.fill hv hc)
  | .for_ sp x V M N => .for_ sp x (V.fill hv hc) (M.fill hv hc) (N.fill hv hc)
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
  | .unwind sp x A M D N => .unwind sp x A M D (wrapTail f N)
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

open Frontend.Elab (TCx loopOf loopRowOf iterOf pullOf elemOf loopFnOf spineT tupleT ppT toSurface Class)
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
      -- An operation answers its result type in the row (SPEC §19).
      | .perform sp k i _ => (Frontend.Check.findOp c.E sp "perform" k i).toOption.map (·.2.1.B)
      | M => match (c.tyC M).bind Frontend.Check.effRow? with
        | some (_, A) => some A
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
  | some f =>
    -- The loop a `for` over a generator whose body loops runs (`forYield`).
    if f.startsWith "io_hwf" then (sp, "it has a `for` over a generator whose body loops")
    else (sp, s!"it calls the div function `{(f.splitOn "__").headD f}`")
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
  | .for_ sp .. => some (sp, "it has a `for` over an unbounded source (a drain)")
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
  | .perform _ _ _ V | .abort _ _ _ V => V.names n
  | .handle _ _ hr hc M => hr.name == n || hc.name == n || M.names n
  | .unwind _ _ _ M D N => M.names n || D.names n || N.names n
  | .withbor2r _ _ _ _ _ _ p m M => p.name == n || m.name == n || M.names n
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
the variables holding each component of `K`. At a row (a generator, SPEC §15) the residual is `K`
itself (`tail1` false): a generator that finishes with what it holds hands back the same when it
is closed. -/
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

/-- The context a div function with result `B` and body `M` is elaborated at; at a row (`bare`),
its residual is `K`.  `[spec §14, §15]` -/
def loopCxOf (sp : Span) (B : CVTy) (M : Comp) (bare : Bool := false) : Except Error LoopCx := do
  let parts := spineT B
  let lin := parts.filter isLinear
  if lin.isEmpty then return ⟨B, .unit, .unit, [], true⟩
  let K := tupleT lin
  match termParts parts M with
  | some ps => pure (if bare then ⟨B, K, K, ps, false⟩ else ⟨B, .tensor K .unit, K, ps, true⟩)
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

/-! #### Exits: `break`, `continue` and `return` -/

/-- A computation has a loop on its spine or anywhere in it. -/
def _root_.Frontend.Comp.hasFor : Comp → Bool
  | .bind _ _ _ M N _ | .with_ _ M N => M.hasFor || N.hasFor
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ | .letUnit _ _ M | .letPair _ _ _ _ M => M.hasFor
  | .case _ _ _ M _ N => M.hasFor || N.hasFor
  | .handle _ _ _ _ M => M.hasFor
  | .unwind _ _ _ M D N => M.hasFor || D.hasFor || N.hasFor
  | .withbor2r _ _ _ _ _ _ _ _ M => M.hasFor
  | .for_ .. => true
  | _ => false

mutual
/-- The first `break`, `continue` or `return e` (of a loop's body) in a value. -/
def _root_.Frontend.Val.exitAt : Val → Option Span
  | .sugar sp .brk | .sugar sp .cont | .app sp (.sugar _ .retE) _ => some sp
  | .pair _ V W | .app _ V W => V.exitAt.orElse fun _ => W.exitAt
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => V.exitAt
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => M.exitAt
  | _ => none

/-- The first `break`, `continue` or `return e` in a computation. -/
def _root_.Frontend.Comp.exitAt : Comp → Option Span
  | .ret _ V | .absurd _ V => V.exitAt
  | .bind _ _ _ M N _ | .with_ _ M N => M.exitAt.orElse fun _ => N.exitAt
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ => M.exitAt
  | .letUnit _ V M | .letPair _ _ _ V M => V.exitAt.orElse fun _ => M.exitAt
  | .case _ V _ M _ N => V.exitAt.orElse fun _ => M.exitAt.orElse fun _ => N.exitAt
  | .for_ _ _ V M N => V.exitAt.orElse fun _ => M.exitAt.orElse fun _ => N.exitAt
  | .perform _ _ _ V | .abort _ _ _ V => V.exitAt
  | .handle _ _ _ _ M => M.exitAt
  | .unwind _ _ _ M D N => M.exitAt.orElse fun _ => D.exitAt.orElse fun _ => N.exitAt
  | .withbor2r _ _ _ _ _ _ _ _ M => M.exitAt
  | .force .. | .top _ => none
end

/-- An exit in a value. -/
def _root_.Frontend.Val.hasExit (V : Val) : Bool := V.exitAt.isSome

/-- An exit in a computation. -/
def _root_.Frontend.Comp.hasExit (M : Comp) : Bool := M.exitAt.isSome

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
  | .perform _ _ _ V | .abort _ _ _ V => V.anySugar p
  | .handle _ _ _ _ M => M.anySugar p
  | .unwind _ _ _ M D N => M.anySugar p || D.anySugar p || N.anySugar p
  | .withbor2r _ _ _ _ _ _ _ _ M => M.anySugar p
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
  | .perform _ _ _ V | .abort _ _ _ V => V.sugarAt p
  | .handle _ _ _ _ M => M.sugarAt p
  | .unwind _ _ _ M D N => ((M.sugarAt p).orElse fun _ => D.sugarAt p).orElse fun _ => N.sugarAt p
  | .withbor2r _ _ _ _ _ _ _ _ M => M.sugarAt p
  | .force .. | .top _ => none
end

/-- A loop body's `return e` in a computation, at any depth of its loops. -/
def _root_.Frontend.Comp.hasRet (M : Comp) : Bool := M.anySugar (· == .retE)

/-- A terminal that leaves: `break`, `break e`, `continue` or `return e`. -/
def _root_.Frontend.Comp.isExit : Comp → Bool
  | .ret _ (.sugar _ .brk) | .ret _ (.app _ (.sugar _ .brk) _) | .ret _ (.app _ (.sugar _ .retE) _)
  | .ret _ (.sugar _ .cont) =>
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

/-- What follows a loop whose value is bound with an `else` (`let r = for … else { d }; N`):
`r`, its written type, `d`, and `N`. -/
def _root_.Frontend.Comp.forElse? : Comp → Option (Ident × Option VTy × Comp × Comp)
  | .bind _ r A (.ret _ (.app _ (.sugar _ .forRes) (.thunk _ d))) N _ => some (r, A, d, N)
  | _ => none

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

/-- What an iterator or a stored generator finishes with: the value of a `for` over it. -/
def finOf (T : CVTy) : Option CVTy :=
  ((pullOf T).map (·.2.1)).orElse fun _ => (iterOf T).map (·.2.1)

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

/-- The error for an exit off the spine. -/
def exitOffSpine (sp : Span) : Error :=
  ⟨sp, "`break`, `continue` and `return` may appear only on the spine of a loop's body (the " ++
    "tail positions of binds, `let`s, `match` arms and loops): not inside a value or a call's " ++
    "argument"⟩

/-- Moved to tail positions: the exits (`break`, `continue`, `return e`) of a body's heads. What
follows a head that leaves goes into it (a commuting conversion): into both arms of a `match` or
`if`, after the body of a `let`, into what follows a loop; and what follows an exit is dropped,
since it never runs. Every exit is then a terminal. The bodies of loops are left as they are:
each is moved when its loop is elaborated. -/
def normExits : Nat → Comp → Except Error Comp
  | 0, M => pure M
  | n + 1, .bind sp x A M N lin => do
    if M.isExit then return M
    if !M.hasExit then return .bind sp x A M (← normExits n N) lin
    let capture (ys : List Ident) : Except Error Unit :=
      if ys.any (fun y => mentionsC y.name N) then throw (exitOffSpine (M.exitAt.getD M.span))
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

/-! ### The loops of a div body  `[spec §14, §15]`

A div body's loops are `while c { M }`, `loop { M }` and the `for`s over a source that is not
data: an iterator (`U (iter A R R')`, made from a capability as `bytes(c)` is) or a stored generator
(`U (pull A B R)`, SPEC §15), drained one element per observation. A `for` over data is a counted
loop (`forData`), and a `for` over a call of a function that performs an iteration effect a handler
site (`forYield`), both elaborated before the body's machine is. -/

/-- The bindings of a `fn`'s parameters at the start of its body (`Parser.fnRest`), before `T`. -/
def paramPrefix : Comp → Comp → Comp
  | .letPair sp x y V@(.var ..) M, T => .letPair sp x y V (paramPrefix M T)
  | .letUnit sp V@(.var ..) M, T => .letUnit sp V (paramPrefix M T)
  | .bind sp x A (.ret s V@(.var ..)) M lin, T => .bind sp x A (.ret s V) (paramPrefix M T) lin
  | _, T => T

/-- Bind the variables of each component of `K` from `v`, a residual `K * 1` (or `1`). -/
def destructR (v : String) (parts : List (List (String × CVTy))) : String :=
  if parts.isEmpty then s!"let () = {v};\n" else
    s!"let ({v}_k, {v}_u) = {v};\nlet () = {v}_u;\n" ++ destructParts s!"{v}_k" parts

/-- A loop of a div body, planned: its condition (`while`) or source (its type, element, whether
it is a stored generator, what it finishes and closes with), the capability the source is made
from, the loop's value when it is bound, what follows the loop, the `else` value, and whether the
source never ends. -/
structure LoopPlan where
  cond : Option Val
  V : Val
  it : Option (CVTy × CVTy × Bool × CVTy × CVTy)
  cap : Option String
  /-- `let r = for …`: the loop's value `r` and its type. -/
  keep : Option (String × CVTy) := none
  /-- What follows the loop (without the binding of `r`). -/
  rest : Comp
  /-- `for … else { d }`: the loop's value when its source ends (SPEC §16). -/
  els : Option Comp := none
  /-- The source never ends (a stored generator that finishes with `0`, or `loop { … }`): what
  follows the loop runs only after `break`. -/
  never : Bool := false

/-- `for x in V { M }; N` or `while c { M }; N` in a div body of context `cx`, planned. -/
def loopPlan (cx : LoopCx) (c : TCx) (x : Ident) (V : Val) (M N : Comp) : SM LoopPlan := do
  let cond := match V with
    | .app _ (.sugar _ .while_) b => some b
    | _ => none
  let M ← normExits divFuel M
  let V := V.takeLends.1
  -- `let r = for …; N`: the loop's value is bound to `r` in `N`.
  let (keep₀, keepA, els, N) := match N.forElse?, N.forRes? with
    | some (r, A, d, N₀), _ => (some r, A, some d, N₀)
    | none, some (r, A, N₀) => (some r, A, none, N₀)
    | none, none => (none, none, none, N)
  -- The source: its type, whether it is a stored generator, and what it finishes and closes with.
  let it ← match cond with
    | some _ => pure none
    | none => do
      let Vt ← match c.tyV V with
        | some Vt => pure Vt
        | none => throw ⟨V.span, "the type of the source of this `for` is not determined"⟩
      match iterOf Vt, pullOf Vt with
      | some (E, Q, Q'), _ => pure (some (Vt, E, false, Q, Q'))
      | none, some (E, Q, Q') => pure (some (Vt, E, true, Q, Q'))
      | none, none => throw ⟨V.span, s!"`for` iterates over data, an iterator `U (iter A R R')`, " ++
          s!"a stored generator `U (pull A B R)` or a call of a function that performs an " ++
          s!"iteration effect, but this has type `{ppT Vt}`"⟩
  let cs := cx.capNames
  let cap ← match cond with
    | some _ => pure none
    | none => match cs.filter (mentionsV · V) with
      | [] => pure none
      | [c] => pure (some c)
      | _ => throw ⟨V.span, "the source of a `for` is made from at most one capability"⟩
  -- `let c = for …` with `c` among what the body hands back: the source hands `c` back when it
  -- finishes or is closed, as an iterator made from `c` does.
  let (cap, keep₀) := match keep₀ with
    | some r => if cs.contains r.name && (cap.isNone || cap == some r.name) then (some r.name, none)
      else (cap, keep₀)
    | none => (cap, keep₀)
  let keep : Option (String × CVTy) ← match keep₀, it with
    | none, _ => pure none
    | some r, some (_, E, _, Q, _) => do
      if let some c := cap then if els.isNone then
        throw ⟨r.span, s!"the source of this `for` is made from `{c}`, which it hands back " ++
          "when it finishes: the loop's value is not bound"⟩
      -- The loop's value: written, or the `else` value's type, or what the source finishes with;
      -- a source that never ends (`0`) gives only `break e`'s.
      match keepA.bind c.elabV, els with
      | some T, _ => pure (some (r.name, T))
      | none, some d => match c.tyC d with
        | some (.ret T) => pure (some (r.name, T))
        | _ => throw ⟨d.span, "the type of the `else` value is not determined here"⟩
      | none, none =>
        if Q != .zero then pure (some (r.name, Q)) else
        match (M.spineBreaks.filterMap (·.2)).head? with
        | some e => match (c.push x.name (some E)).tyV e with
          | some T => pure (some (r.name, T))
          | none => throw ⟨e.span, s!"the type of this loop's value is not determined: write it, " ++
              s!"`let {r.name} : T = for …`"⟩
        | none => pure (some (r.name, .zero))
    | some r, none => throw ⟨r.span, "a `while` has no value"⟩
  checkBreaks M (keep.map (·.2))
  if M.hasRet then if let some c := cap then
    throw ⟨V.span, s!"a `return` inside a `for` over a source made from `{c}` cannot hand `{c}` " ++
      "back: the source holds it until the loop ends. `break`, and `return` after the loop"⟩
  let never := match cond, it with
    | some (.sugar _ .forever), _ => true
    | _, some (_, _, _, Q, _) => Q == .zero
    | _, _ => false
  pure { cond, V, it, cap, keep, rest := N, els, never }

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

/-- Closing a body before it starts: it closes the stored generators and iterators it was given
(`gs`, with their types), to hand back what they hold. Each variable of the residual that is not
among `gs` is bound from the residual of the first of them that hands back its type. The code,
and the sources it closes. -/
def closeGiven (cx : LoopCx) (gs : List (String × Option CVTy)) : String × List String := Id.run do
  let names := gs.map (·.1)
  let mut used : List String := []
  let mut out := ""
  for (p, T) in cx.caps do
    if names.contains p then continue
    let hands (g : String) (Tg : Option CVTy) : Bool := !used.contains g && match Tg with
      | some Tg => (((pullOf Tg).map (·.2.2)).orElse fun _ => (iterOf Tg).map (·.2.2)) == some T
      | none => false
    match gs.find? (fun (g, Tg) => hands g Tg) with
    | some (g, _) => used := g :: used; out := out ++ s!"{p} <- (nu_out (force {g})).2;\n"
    | none => pure ()
  pure (out, used)

/-! ### One state machine per body  `[spec §14, §15]`

A div body is elaborated to **one `unfold`**: its state is a sum with one summand per
**resumption point** (a loop's head, or a call of a div function in progress), each holding the
variables live there, and its step is one code with a `case` on the state. Every observation is
then a call of known code: no closure is dispatched on, and no bind is nested in another.

* **The code between points** is the program's own, with its transitions replaced: reaching a
  loop's head or a call is a **move** to its point; `break` closes the loop's source and moves to
  the code after the loop (its **join**); the end of a loop's body moves back to its head;
  `return e` closes the sources of the loops it leaves and finishes; a terminal finishes.
* **A move** to a summand is a skip: the observation returns the point's state, so each iteration
  of a loop is one observation, as with the delay bind. A move to a join calls the join's code
  (`io_run_k`, a `!` function), defined before the step.
* **The residual** is handed back by name at every summand: its `close` closes what the state
  holds (the sources of the loops around it, or the call's loop), binding the capabilities they
  hand back, and returns the residual from the names.
* **At a row** (a function that performs control operations, SPEC §19), the loop is
  `Loop_Σ B R = νX. F_Σ(B ⊕ U X) & F_Σ R`: its observations perform the operations, and so does
  its code. Such a body **runs nothing when called**: its first state holds the parameter, and a
  call is the loop. A body at the empty row **runs its code up to its first point when called**,
  and returns the machine at that point (`io_mk`), as `div_bind` did. -/

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
  L : LoopCx
  /-- The row of the body's observations (SPEC §19). -/
  row : Frontend.Check.CRow := []
  pp : CVTy → String
  loops : List MLoop := []
  /-- What the loops around hold, innermost first. -/
  held : List MHeld := []
  /-- The place of the function whose code this is; none in the step's own code. -/
  cur : Option Nat := none
  /-- In a div body's code before its first point, run when it is called. -/
  pre : Bool := false

/-- `F_Σ A` at the machine's row, written: `F[n.i q A ~> B, …] A`, or `F A`. -/
def MCx.fSrc (m : MCx) (A : String) : String :=
  if m.row.isEmpty then s!"F ({A})" else
  "F[" ++ ", ".intercalate (m.row.map fun o =>
    s!"{o.n}.{o.i} {Frontend.Check.qualStr o.q} {m.pp o.A} ~> {m.pp o.B}") ++ s!"] ({A})"

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
      throw ⟨rest.span, s!"the extern `{y}` is used across a loop, and it is not a capability of the body"⟩
  (latest c.locals).filterMapM fun (y, T) =>
    if caps.contains y || excl.contains y || !mentionsC y rest then pure none
    else match T with
      | some T => pure (some (y, T))
      | none => throw ⟨rest.span, s!"the loop threads `{y}`, whose type is not determined: ascribe it"⟩

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
def MCx.skip (_ : MCx) (sp : Span) (s : Val) : Val := .inr sp s

/-- A move to point `q`, from the code of `m`. -/
def mGoto (m : MCx) (sp : Span) (q : Nat) : MM Comp := do
  let p ← mPt q
  if m.pre then
    return .ret sp (.app sp (.unbang sp (.var sp "io_mk")) (mInj sp q p.vars))
  -- At a row, a move forward runs in the same observation (from the step's own code, or to a
  -- later point), so that an observation reaches the next operation; a move back to a loop's
  -- head is a skip. At the empty row every move to a summand is a skip.
  let later := match m.cur with
    | none => true
    | some k => k < p.pos
  let call := p.fn && (!p.summand || (!m.row.isEmpty && later))
  if call then
    let f : Val := .unbang sp (.var sp s!"io_run_{q}")
    let a := tupleVal sp (p.vars.map (·.1))
    if m.row.isEmpty then return .ret sp (.app sp f a)
    -- At a row, the join's code is a computation that performs the row's operations.
    let fv : Ident := ⟨s!"io_rf{q}", sp⟩
    let av : Ident := ⟨s!"io_ra{q}", sp⟩
    return .bind sp fv none (.ret sp f) (.bind sp av none (.ret sp a) (.app sp (.force sp fv) av) false) false
  if !p.summand then throw ⟨sp, "internal error: a join reached by a skip"⟩
  pure (.ret sp (m.skip sp (mInj sp q p.vars)))

/-- The `close` of a state that holds `held` (innermost first): each closed, then the residual. -/
def mClose (m : MCx) (sp : Span) (what : String) (held : List MHeld) : MM Comp :=
  mTemplate sp what (String.join (held.map (·.closeSrc)) ++ s!"return {m.L.rSrc}")
    [] []

/-- The machine's finish with the value `T` computes. -/
def mFinish (m : MCx) (T : Comp) : MM Comp := do
  if m.pre then return (← (dret m.L T : SM Comp))
  let L ← mTemplate T.span "a body's result" s!"io_v : {m.pp m.L.B} <- force io_hole_t;\nreturn (inl io_v)"
    [] [("io_hole_t", T)]
  match T.takeLends.2, L with
  | [], _ => pure L
  | _, .bind sp x _ M N lin => pure (.bind sp x none M N lin)
  | _, L => pure L

/-- Bind the components of `v`, of type `T`, at each leaf of its tensors however they nest: a
leaf `name` names, or a fresh variable. The code, and each leaf's name (when `name` gave it) and
type. -/
def destructLeaves : Nat → String → CVTy → (CVTy → Option String) →
    String × List (Option String × CVTy)
  | k + 1, v, .tensor A B, name =>
    let (s₁, l₁) := destructLeaves k s!"{v}a" A name
    let (s₂, l₂) := destructLeaves k s!"{v}b" B name
    (s!"let ({v}a, {v}b) = {v};\n" ++ s₁ ++ s₂, l₁ ++ l₂)
  | _, v, T, name => match name T with
    | some p => (s!"{p} <- return {v};\n", [(some p, T)])
    | none => ("", [(none, T)])

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
    else
      -- The loop hands back, by their types, capabilities of the body it was given (the variables
      -- a `for` over a generator threads, say); what else it hands back is dropped.
      let capOf (T : CVTy) : Option String := match cx.caps.filter (·.2 == T) with
        | [(p, _)] => some p
        | _ => none
      let (src, leaves) := destructLeaves divFuel "io_r" Rf capOf
      let caps := leaves.filterMap (·.1)
      if !caps.isEmpty && caps.eraseDups.length == caps.length &&
          leaves.all (fun (p, T) => !isLinear T || p.isSome) then
        pure (src, caps)
      else throw ⟨sp, s!"a call whose loop hands back `{ppT Rf}` when closed, which is neither " ++
          s!"nothing, a capability it was lent, one capability of the body, nor what the body " ++
          s!"hands back (`{ppT cx.R}`)"⟩

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
one observation, to a move or a finish. -/
def mWalk (m : MCx) : Nat → TCx → Comp → MM Comp
  | 0, _, M => throw ⟨M.span, "internal error: a body nested too deeply"⟩
  | n + 1, c, .bind sp x A M N lin => do
    if M.hasExit then
      match M with
      | .case csp V y M₁ z M₂ =>
        if mentionsC y.name N || mentionsC z.name N then throw (exitOffSpine (M.exitAt.getD M.span))
        return (← mWalk m n c (.case csp V y (.bind sp x A M₁ N lin) z (.bind sp x A M₂ N lin)))
      | .bind bsp y B M₁ M₂ lin' =>
        if mentionsC y.name N then throw (exitOffSpine (M.exitAt.getD M.span))
        return (← mWalk m n c (.bind bsp y B M₁ (.bind sp x A M₂ N lin) lin'))
      | .letPair lsp y z V M₁ =>
        if mentionsC y.name N || mentionsC z.name N then throw (exitOffSpine (M.exitAt.getD M.span))
        return (← mWalk m n c (.letPair lsp y z V (.bind sp x A M₁ N lin)))
      | .letUnit lsp V M₁ => return (← mWalk m n c (.letUnit lsp V (.bind sp x A M₁ N lin)))
      | _ => throw (exitOffSpine (M.exitAt.getD M.span))
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
      let some Tm := c.tyV V | throw ⟨sp, "the type of this call of a div function is not determined"⟩
      mCall m n c c' sp x A M' lend Tm Bf Rf N
    | none =>
      pure (.bind sp x A M (← mWalk m n (c.push x.name (bindTy c A M)) N) lin)
  | n + 1, c, .letUnit sp V M => do
    if V.hasExit then throw (exitOffSpine (V.exitAt.getD V.span))
    if (callIn c divFuel (some .unit) V).isSome then
      let (V', bs) := liftAll V
      return (← mWalk m n c (chain bs (.letUnit sp V' M)))
    return .letUnit sp V (← mWalk m n c M)
  | n + 1, c, .letPair sp x y V M => do
    if V.hasExit then throw (exitOffSpine (V.exitAt.getD V.span))
    if (callIn c divFuel none V).isSome then
      let (V', bs) := liftAll V
      return (← mWalk m n c (chain bs (.letPair sp x y V' M)))
    let (Ax, Ay) := pairTys c V
    return .letPair sp x y V (← mWalk m n ((c.push x.name Ax).push y.name Ay) M)
  | n + 1, c, .case sp V x M y N => do
    if V.hasExit then throw (exitOffSpine (V.exitAt.getD V.span))
    if (callIn c divFuel none V).isSome then
      let (V', bs) := liftAll V
      return (← mWalk m n c (chain bs (.case sp V' x M y N)))
    let (Ax, Ay) := sumTys c V
    return .case sp V x (← mWalk m n (c.push x.name Ax) M) y (← mWalk m n (c.push y.name Ay) N)
  | n + 1, c, .for_ sp x V M N => mLoop m n c sp x V M N
  | _ + 1, _, .ret sp (.app _ (.sugar _ .retE) v) => do
    if v.hasExit then throw (exitOffSpine (v.exitAt.getD v.span))
    -- `return e` from inside loops: every loop it leaves closes its source, and the body finishes.
    mTemplate sp "`return`" (String.join (m.held.map (·.closeSrc)) ++
      s!"io_v : {m.pp m.L.B} <- return io_hole_rv;\nreturn (inl io_v)") [("io_hole_rv", v)] []
  | _ + 1, _, .ret sp (.sugar _ .brk) => mBreak m sp (.unit sp)
  | _ + 1, _, .ret sp (.sugar _ .cont) => do
    -- `continue`: back to the head of the innermost loop.
    let some l := m.loops.head? | throw ⟨sp, "`continue` is outside every loop"⟩
    mGoto m sp l.head
  | _ + 1, _, .ret sp (.app _ (.sugar _ .brk) e) => mBreak m sp e
  | n + 1, c, T => do
    if T.hasExit then throw (exitOffSpine (T.exitAt.getD T.span))
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

/-- `x <- M; N` where `M` computes a call's loop, of type `Tm`, finishing with `Bf` and closed with
`Rf`: a point holding it with what `N` uses. -/
def mCall (m : MCx) : Nat → TCx → TCx → Span → Ident → Option VTy → Comp → Option Ident →
    CVTy → CVTy → CVTy → Comp → MM Comp
  | 0, _, _, sp, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | n + 1, c, c', sp, x, A, call, lend, Tm, Bf, Rf, N => do
    let (abort, hcaps) ← mAbort m sp lend Rf
    let k := (← get).pts.size
    let v := s!"io_d{k}"
    let h : MHeld := { v, T := Tm, closeSrc := s!"io_r <- (nu_out (force {v})).2;\n{abort}", caps := hcaps }
    let excl := x.name :: lend.toList.map (·.name)
    let vars ← mVars m c [h] N excl
    let what := "a call of a div function"
    let d ← mNew sp what true true vars
    let bindX := match lend, A with
      | some l, _ => match Bf with
        | .tensor .. => s!"let ({l.name}, {x.name}) = io_b;\n"
        | _ => s!"{l.name} <- return io_b;\n{x.name} <- return ();\n"
      | none, some A => s!"{x.name} : {A.pp} <- return io_b;\n"
      | none, none => s!"{x.name} <- return io_b;\n"
    let pd ← mPt d
    let rest ← mWalk { m with cur := some pd.pos, pre := false } n c' N
    let skip := m.skip sp (mInj sp d vars)
    let src := s!"io_o <- (nu_out (force {v})).1;
  case io_o \{
    inl io_b -> {bindX}force io_hole_rest
  | inr {v} -> return io_hole_k
  }"
    let code ← mTemplate sp what src [("io_hole_k", skip)] [("io_hole_rest", rest)]
    mSet d code (← mClose { m with pre := false } sp what (h :: m.held))
    let go ← mGoto m sp d
    pure (.bind sp ⟨v, sp⟩ none call go false)

/-- `for x in V { M }; N` or `while c { M }; N`: a point at its head, and a join after it when its
body has a `break`. -/
def mLoop (m : MCx) : Nat → TCx → Span → Ident → Val → Comp → Comp → MM Comp
  | 0, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | n + 1, c, sp, x, V, M, N => do
    let P ← (loopPlan m.L c x V M N : SM LoopPlan)
    let M ← (normExits divFuel M : Except Error Comp)
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
      | none => (throw ⟨sp, s!"the loop threads `{y}`, whose type is not determined: ascribe it"⟩ : MM _)
    let vars := held.reverse.map (fun h => (h.v, h.T)) ++ m.L.caps.filter (!hcaps.contains ·.1) ++ needVars
    let what := if P.cond.isSome then "`while`" else "`for`"
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
      -- A loop that never ends, with no `break`: what follows it does not run.
      | none => if P.never then pure (.top sp) else mWalk { m with cur := some ph.pos, pre := false } n cr N
    let skip := m.skip sp (mInj sp h vars)
    let code ← match P.it, P.cond with
      | some (_, _, isGen, Q, _), _ => do
        let v := s!"io_it{k}"
        let ended := if Q == .zero then "absurd io_q" else match P.keep, P.els with
          | some (r, _), some _ =>
            let drop := if P.cap.isSome then bindCap P.cap Q "io_q" else "io_dq <- return io_q;\n"
            s!"{drop}{r} <- force io_hole_else;\nforce io_hole_after"
          | some (r, _), none => s!"{r} <- return io_q;\nforce io_hole_after"
          | none, _ => s!"{bindCap P.cap Q "io_q"}force io_hole_after"
        let fin := if isGen then s!"case io_d \{ inl io_q -> {ended} | inr {v} -> return io_hole_k }"
          else s!"io_q <- return io_d;\n{ended}"
        let src := s!"io_o <- (nu_out (force {v})).1;\ncase io_o \{ inl io_p -> let ({x.name}, {v}) = io_p; force io_hole_body | inr io_d -> {fin} }"
        mTemplate sp what src [("io_hole_k", skip)]
          ([("io_hole_body", body), ("io_hole_after", after)] ++ (P.els.map ("io_hole_else", ·)).toList)
      | none, some (.sugar _ .forever) => do
        mTemplate sp what "force io_hole_body" [] [("io_hole_body", body)]
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
  | .perform sp k i V => .perform sp k i (mResV inj V)
  | .abort sp k i V => .abort sp k i (mResV inj V)
  | .handle sp k hr hc M => .handle sp k hr hc (mResC inj M)
  | .unwind sp x A M D N => .unwind sp x A (mResC inj M) (mResC inj D) (mResC inj N)
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
  if sums.isEmpty then throw ⟨sp, "internal error: a div body's machine has no state"⟩
  let tyOf (p : MPoint) : String := tupleTySrc (p.vars.map (m.pp ·.2))
  let S := sumTySrc (sums.map tyOf)
  let Obs := s!"({m.pp m.L.B}) + ({S})"
  let Fs := m.fSrc
  let Cod := if m.row.isEmpty then s!"loop ({m.pp m.L.B}) ({m.pp m.L.R})"
    else s!"nu X. {Fs s!"({m.pp m.L.B}) + U X"} & {Fs (m.pp m.L.R)}"
  let fns := (pts.filter (·.fn)).toArray.qsort (fun a b => a.pos > b.pos) |>.toList
  let defs := String.join (fns.map fun p =>
    s!"io_run_{p.id} : !U (({tyOf p}) -o {Fs Obs}) <-\n  return (!thunkv fun (io_a : {tyOf p}) -> force io_hole_c{p.id});\n")
  let arm (p : MPoint) : String :=
    if !p.fn then s!"force io_hole_c{p.id}"
    else if m.row.isEmpty then s!"return ((unbang io_run_{p.id}) io_a)"
    else s!"io_rf <- return (unbang io_run_{p.id}); force io_rf io_a"
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
  let src := defs ++ s!"io_step : !U ({S} -o {Fs Obs} & {Fs (m.pp m.L.R)}) <-
  return (!thunkv fun ({if sums.length == 1 then "io_a" else "io_s"} : {S}) -> < {mTree arm "io_s" sums}, {mTree carm "io_s" sums} >);
" ++ tail
  let L ← template sp "a div body's state machine" src
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

/-- A div body's machine. At the empty row: its code before the first point, then the machine
there. At a row: the machine, whose first state holds `start` (the parameter), where its first
observation runs the body `M` from the top; `close0` is the `close` there.  `[spec §14, §19]` -/
def divMachine (cx : LoopCx) (row : Frontend.Check.CRow) (c : TCx) (start : List (String × CVTy))
    (close0 : Comp) (M : Comp) : SM Comp := do
  -- Types are printed with the context's lifetimes by their names.
  let pp : CVTy → String := fun T => Frontend.Check.ppV c.E.lenv 0 0 T
  if row.isEmpty then
    let m : MCx := { L := cx, pp, pre := true }
    let (pre, st) ← (mWalk m divFuel c M).run {}
    mAssemble m M.span st none (some pre)
  else
    let m : MCx := { L := cx, row, pp }
    let go : MM Unit := do
      let s ← mNew M.span "a div body" true false start
      let code ← mWalk m divFuel c M
      mSet s code close0
    let ((), st) ← go.run {}
    mAssemble m M.span st (some (mInj M.span 0 start)) none

/-- A div body at the empty row: its machine.  `[spec §14]` -/
def divBody (cx : LoopCx) (c : TCx) (M : Comp) : SM Comp := divMachine cx [] c [] (.top M.span) M

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

/-- The row and the result of a function type `A ⇒ F[Σ] B` or its `!` form (`Σ` empty for
`A => B`), under its lifetime parameters. -/
def resultRowOf (A : Option CVTy) : Option (Frontend.Check.CRow × CVTy) :=
  -- By fuel, so that the kernel evaluates it (`Frontend/Check/CrossCheck.lean`).
  let rec go : Nat → CVTy → Option (Frontend.Check.CRow × CVTy)
    | _ + 1, .thunk (.arr _ C) => Frontend.Check.effRow? C
    | k + 1, .bang A => go k A
    | k + 1, .thunk (.all _ _ (.ret A)) => go k A
    | _, _ => none
  A.bind (go divFuel)

/-- A value that must be known here. -/
def need' {α} (sp : Span) (what : String) : Option α → SM α
  | some a => pure a
  | none => throw ⟨sp, s!"{what} is not determined here"⟩

/-- A function's type and code with its lifetime parameters peeled, outermost first, as
`fn f<'a, …>` writes them (`all 'a < b. …` around `Fun 'a < b. return (thunkv …)`). -/
def peelLives : Nat → VTy → Comp → List (Ident × Frontend.Life) × VTy × Comp
  | k + 1, .all _ y b A, .lamL _ y' _ (.ret _ (.thunkv _ M)) =>
    if y.name == y'.name then
      let (ls, A', M') := peelLives k A M
      ((y, b) :: ls, A', M')
    else ([], .all .none y b A, .lamL .none y' b (.ret .none (.thunkv .none M)))
  | _, A, M => ([], A, M)

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
    -- `fn f<'a, …>`: the lifetime parameters, outermost first, then the function.
    let (bang, A₀, M₀) : Bool × VTy × Option Comp := match A, V with
      | .bang _ A, .bangThunkv _ M => (true, A, some M)
      | A, .thunkv _ M => (false, A, some M)
      | A, _ => (false, A, none)
    let (lives, Ai, Mi) := match M₀ with
      | some M => peelLives divFuel A₀ M
      | none => ([], A₀, .top sp)
    let mut cl := c
    for (y, b) in lives do
      let some bl := c.elabL b | return (d, none)
      cl := cl.pushLife y.name bl
    let lam := match Mi with
      | .lam _ x Ax M => some (x, Ax, M)
      | _ => none
    let ty := cl.elabV (.thunk sp (match Ai with
      | .lolli _ Ar B => .arr sp Ar (.ret sp B)
      | .thunk _ C => C
      | T => .ret sp T))
    let why := lam.bind fun (x, Ax, M) =>
      loopsAt (cl.push x.name (cl.elabV Ax)) ((resultRowOf ty).map (·.2)) M
    match mk, why with
    | .total, some (sp', what) =>
      throw ⟨sp', s!"`{n.name}` is declared `total`, but {what} (SPEC §14)"⟩
    | .total, none | .none, none => return (d, none)
    | _, _ =>
      let some (x, Ax, M) := lam
        | throw ⟨sp, s!"a div function is written `thunkv fun (x : A) -> M` (SPEC §14)"⟩
      -- At a row (`A ⇒ F[Σ] B`, a copy for the handlers of its control effects), the loop's
      -- observations perform the row's operations (SPEC §19).
      let (Ar, B, row) ← match Ai with
        | .lolli _ Ar B => pure (Ar, B, Row.nil)
        | .thunk _ (.arr _ Ar (.eff _ r B)) => pure (Ar, B, r)
        | _ => throw ⟨A.span, "a div function has type `A => B` or `!(A => B)` (SPEC §14)"⟩
      if !ps.isEmpty then
        throw ⟨sp, "a div function has no type parameters (SPEC §14)"⟩
      let some (S, Bc) := resultRowOf ty
        | throw ⟨A.span, s!"the type of `{n.name}` does not elaborate"⟩
      let cx ← loopCxOf sp Bc M (bare := !S.isEmpty)
      let cP₀ := cl.push x.name (cl.elabV Ax)
      let cP := { cP₀ with E := { cP₀.E with row := if S.isEmpty then none else some S } }
      let M' ← if S.isEmpty then divBody cx cP M else do
        -- At a row, the body runs nothing when called: its first state holds the parameter, and
        -- closed there it closes the sources it was given and hands back the residual.
        let some Pc := cl.elabV Ax | throw ⟨Ax.span, s!"the parameter type of `{n.name}` does not elaborate"⟩
        let (closes, _) := closeGiven cx (paramsOf divFuel cP M)
        let ab ← template sp "a div body's `close` before it starts" s!"{closes}return {cx.rSrc}"
        divMachine cx S cP [(x.name, Pc)] (paramPrefix M ab) M
      let Rs ← (cl.surface sp cx.R : Except Error VTy)
      let L : CTy := match row with
        | .nil => .loop B.span B Rs
        | r => .nu B.span ⟨"X", B.span⟩ (.amp B.span (.eff B.span r (.sum B.span B (.thunk B.span (.name B.span "X"))))
            (.eff B.span r Rs))
      let F := VTy.lolli A.span Ar (.thunk B.span L)
      let lamC := Comp.lam (match Mi with | .lam lsp .. => lsp | _ => sp) x Ax M'
      let (F, body) := lives.foldr (fun (y, b) (T, Mb) =>
        (VTy.all sp y b T, Comp.lamL sp y b (.ret sp (.thunkv sp Mb)))) (F, lamC)
      let A' := if bang then VTy.bang A.span F else F
      let V' := match V with
        | .thunkv vsp _ => Val.thunkv vsp body
        | .bangThunkv vsp _ => Val.bangThunkv vsp body
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
    -- A div callback's result is a loop of `B`.
    let B' ← (loopFnOf T).map (·.1)
    if A' = A ∧ B' = B then some T else none

/-- A loop around the code being elaborated, for a `return` in the body of a counted loop inside
it: a counted loop leaves through its exit (`ret`, of type `Rt`); a drain passes the `return` on
as its own (`VSugar.retE`).  `[spec §16]` -/
inductive LoopExit where
  | total (Rt : CVTy) (ret : Span → Val → Comp)
  | drain

/-- The elaboration so far: the libraries (in scope for typing); the source declarations in
scope, newest first; the elaborated ones, in order; whether any body became a loop; and the
copies made, by function and parameter type. -/
structure DivSt where
  lib : List Decl := []
  srcs : List Decl := []
  out : List Decl := []
  any : Bool := false
  copies : List ((String × VTy) × String) := []
  /-- The capabilities in scope of the declaration being elaborated (`main`'s), for typing. -/
  caps : List Decl := []
  /-- The templates (`fn f[A, …]`), as written: each is instantiated at the types of a call, on
  first use. -/
  templates : List Decl := []
  /-- The instances made, by template and type arguments. -/
  insts : List ((String × List VTy) × String) := []
  /-- The loops around the code being elaborated, innermost first: how a `return` in the body of
  a counted loop inside them leaves (`forData`).  `[spec §16]` -/
  exits : List LoopExit := []
  /-- The declarations of the included library modules, and the instances of their templates:
  their loops are not reported. -/
  libNames : List String := []
  /-- The declaration being elaborated is one of `libNames`. -/
  quiet : Bool := false
  /-- The row of the callback of the borrow block being elaborated, when its body performs
  operations: the block is the unwinding form of its borrow (SPEC §19). -/
  cbRow : Option Frontend.Check.CRow := none
  /-- The answer type of each handler site whose clauses run after it (`HInfo.after`), as the type
  name `fx_res{n}`: an annotation that names it is its type.  `[spec §19]` -/
  siteRes : List (String × VTy) := []
  /-- The handler sites that observe their computation one turn at a time (a `for`'s site and a
  stored generator's, `Elab.Effects.St.perTurn`).  `[spec §16]` -/
  perTurn : List Nat := []

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

/-- The literal `"…"` of the bytes `bs`: the persistent value `(n, t)` of `lit`, `n` its length
and `t` the `!` function from an index to its byte, `0` past the end. `t` compares the index with
the length, then halves the range of indices down to one byte (design §5.7). -/
def litValue (sp : Span) (bs : List Nat) : Val :=
  let arr := bs.toArray
  let u : Ident := ⟨"io_lu", sp⟩
  let lt (k : Nat) : Val := .app sp (.unbang sp (.const sp (.host (.rel .w32 .lt_u))))
    (.pair sp (.var sp "io_li") (litAt sp .w32 k))
  let byte (k : Nat) : Comp := .ret sp (litAt sp .w8 (arr.getD k 0))
  -- `lt` answers `inr ()` for true: the lower half is the `inr` arm.
  let rec tree : Nat → Nat → Nat → Comp
    | 0, lo, _ => byte lo
    | f + 1, lo, hi =>
      if hi ≤ lo + 1 then byte lo
      else
        let mid := (lo + hi) / 2
        .case sp (lt mid) u (tree f mid hi) u (tree f lo mid)
  let n := bs.length
  let body := if n == 0 then .ret sp (litAt sp .w8 0)
    else .case sp (lt n) u (.ret sp (litAt sp .w8 0)) u (tree n 0 n)
  .pair sp (litAt sp .w32 n) (.bangThunkv sp (.lam sp ⟨"io_li", sp⟩ (.int sp .w32) body))

/-- The filler of a buffer's unused slots at the element type `A` (design §5.4): `0` at an
integer width, the empty view at a borrowed family, an empty array at an owned one (which
allocates nothing), the empty literal's function at `!(A => B)`, `()`, and componentwise at `*`
and `+`. `none` at a type with no filler (a cell, a capability). -/
def fillerOf (c : TCx) (sp : Span) : Nat → CVTy → Except Error (Option Val)
  | 0, _ => pure none
  | n + 1, A => match A with
    | .unit => pure (some (.unit sp))
    | .int w => pure (some (litAt sp w 0))
    | .tensor A B => do
      match ← fillerOf c sp n A, ← fillerOf c sp n B with
      | some a, some b => pure (some (.pair sp a b))
      | _, _ => pure none
    | .sum A _ => do pure ((← fillerOf c sp n A).map (.inl sp ·))
    | .fam (.imm a B) => do
      pure (some (.const sp (.sliceEmptyImm (← c.surfaceL sp a) (← c.surface sp B))))
    | .fam (.mut a B) => do
      pure (some (.const sp (.sliceEmptyMut (← c.surfaceL sp a) (← c.surface sp B))))
    | .fam (.ref B) => do
      match ← fillerOf c sp n B with
      | some b =>
        let Bs ← c.surface sp B
        pure (some (.app sp (.unbang sp (.const sp (.arrayNew Bs))) (.pair sp (litAt sp .w32 0)
          (.bangThunkv sp (.lam sp ⟨"io_fi", sp⟩ (.int sp .w32) (.ret sp b))))))
      | none => pure none
    | .bang (.thunk (.arr X (.ret B))) => do
      match ← fillerOf c sp n B with
      | some b =>
        pure (some (.bangThunkv sp (.lam sp ⟨"io_fx", sp⟩ (← c.surface sp X) (.ret sp b))))
      | none => pure none
    | _ => pure none

/-- The body `S` of a block with its tail values boxed at `'x`: a tail value is bound first, so
that what it computes from the borrow is not inside the box (`boxI`'s context outlives `'x`). -/
def boxTail (x : String) (S : Comp) : Comp :=
  wrapTail (fun
    | .ret sp V@(.var ..) | .ret sp V@(.unit _) => .ret sp (.boxed sp (.var sp x) V)
    | T => .bind T.span ⟨"io_bx", T.span⟩ none T
        (.ret T.span (.boxed T.span (.var T.span x) (.var T.span "io_bx"))) false) S

/-- `main`'s elaborated body `M` under its lifetime `'main`: a `mut` borrow of a unit cell,
allocated before it and freed after. A cell of `1` takes no words, so the backend allocates nothing
for it (`Flat.zeroCell`). The standard capabilities `caps` the body lends are handed back beside
its result, as a borrow block hands back what it lends. A body that names no `'main` is left as it
is: the borrow is not observable.  `[spec §23]` -/
def mainLife (sp : Span) (C : CTy) (caps : List String) (M : Comp) : Except Error Comp := do
  if !M.mentionsLife "main" then return M
  let .ret _ B := C
    | throw ⟨sp, "`main` uses its lifetime `'main`, so its type is written `F A` or `-> A`"⟩
  let x : Ident := ⟨"main", sp⟩
  let one := VTy.unit sp
  let rec tupTy : List String → VTy
    | [] => one
    | [c] => capTy sp c
    | c :: cs => .tensor sp (capTy sp c) (tupTy cs)
  let B' := if caps.isEmpty then B else .tensor sp B (tupTy caps)
  let M := if caps.isEmpty then M else
    wrapTail (fun T => .bind T.span ⟨"io_bt", T.span⟩ none T
      (.ret T.span (.pair T.span (.var T.span "io_bt") (tupleVal T.span caps))) false) M
  let cb : Val := .thunkv sp (.lamL sp x (.dom sp) (.ret sp (.thunkv sp
    (.lam sp ⟨"io_mainb", sp⟩ (.mut sp (.var sp "main") one) (boxTail "main" M)))))
  let borrow : Val :=
    .app sp (.app sp (.const sp (.withbor2 x (.dom sp) one B')) (.var sp "io_main")) cb
  -- `(r, caps)`, bound name by name.
  let rec unpack (v : String) : List String → Comp → Comp
    | [], N => N
    | [c], N => .bind sp ⟨c, sp⟩ none (.ret sp (.var sp v)) N false
    | c :: cs, N => .letPair sp ⟨c, sp⟩ ⟨v ++ "_", sp⟩ (.var sp v) (unpack (v ++ "_") cs N)
  let after : Comp := .bind sp ⟨"io_mainu", sp⟩ none
    (.ret sp (.app sp (.const sp (.free one)) (.var sp "io_main"))) (.ret sp (.var sp "io_mainr")) false
  let rest : Comp := if caps.isEmpty then
      .letPair sp ⟨"io_main", sp⟩ ⟨"io_mainr", sp⟩ (.var sp "io_mainp") after
    else
      .letPair sp ⟨"io_main", sp⟩ ⟨"io_mainq", sp⟩ (.var sp "io_mainp")
        (.letPair sp ⟨"io_mainr", sp⟩ ⟨"io_mainc", sp⟩ (.var sp "io_mainq")
          (unpack "io_mainc" caps after))
  pure (.bind sp ⟨"io_main", sp⟩ none (.ret sp (.app sp (.const sp (.alloc one)) (.unit sp)))
    (.bind sp ⟨"io_mainp", sp⟩ none (.ret sp borrow) rest false) false)

/-- The body `S` of `modify` returning the new content alone, with `()` for the result. -/
def unitTail (S : Comp) : Comp :=
  wrapTail (fun
    | .ret sp V => .ret sp (.pair sp V (.unit sp))
    | T => .bind T.span ⟨"io_mv", T.span⟩ none T
        (.ret T.span (.pair T.span (.var T.span "io_mv") (.unit T.span))) false) S

/-- The result type of a computation, as its tail gives it. -/
def resultOfC : Option CCTy → Option CVTy
  | some C => (Frontend.Check.effRow? C).map (·.2)
  | none => none

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

/-- An owned array `x : array A` lent as its view (`array_mut 'l A` with `&mut x`, `array_imm 'l A`
with `&x`) to the call `call l v`, whose result has type `Q` with the parameter's lifetime `v`:
`slice_borrow_mut` or `slice_borrow_imm` around it, with no cell (SPEC §9), the array rebound
from the pair. A view the call hands back, as its result or its result's first component, is
dropped there: the lend's result is the rest (`()` for a function that hands back only the view,
`reverse(&mut a)`).  `[spec §9]` -/
def lendSlice (c : TCx) (sp : Span) (x : Ident) (m : Mode) (A : CVTy) (v : BoCa.Lifetime.LifeVar)
    (Q : CVTy) (call : String → String → Comp) : DM Val := do
  let isView : CVTy → Bool
    | .fam (.mut (.var w) _) | .fam (.imm (.var w) _) => w == v
    | _ => false
  let vfree := BoCa.Fig16.LogRel.Core.Check.vfreeB v
  let (B, proj) : CVTy × Option Bool :=
    if isView Q then (.unit, some false) else match Q with
      | .tensor V B => if isView V && !vfree B then (B, some true) else (Q, none)
      | _ => (Q, none)
  if proj.isNone && vfree Q then
    throw ⟨sp, "the call's result mentions the lifetime of the lent array other than as the view " ++
      "it hands back, so the array cannot be handed back after it"⟩
  let l := s!"io_lb{sp.start.line}_{sp.start.col}"
  let mv := s!"io_lm{sp.start.line}_{sp.start.col}"
  let As ← (c.surface sp A : Except Error VTy)
  let Bs ← (c.surface sp B : Except Error VTy)
  let li : Ident := ⟨l, sp⟩
  let Tm : VTy := if m == .mut then .arrayMut sp (.var sp l) As else .arrayImm sp (.var sp l) As
  let r : Ident := ⟨"io_lr", sp⟩
  let boxR := Comp.ret sp (.boxed sp (.var sp l) (.var sp r.name))
  let body : Comp := match proj with
    | some false => .bind sp ⟨"io_lv", sp⟩ none (call l mv)
        (.ret sp (.boxed sp (.var sp l) (.unit sp))) false
    | some true => .bind sp ⟨"io_lp", sp⟩ none (call l mv)
        (.letPair sp ⟨"io_lv", sp⟩ r (.var sp "io_lp") boxR) false
    | none => .bind sp r none (call l mv) boxR false
  let cb : Val := .thunkv sp (.lamL sp li (.dom sp) (.ret sp (.thunkv sp
    (.lam sp ⟨mv, sp⟩ Tm body))))
  let C : Const := if m == .mut then .sliceBorrowMut li (.top sp) As Bs
    else .sliceBorrowImm li (.top sp) As Bs
  pure (.app sp (.app sp (.const sp C) (.lend sp x m)) cb)

/-- A call `f W` whose argument lends a place at a borrow parameter of `f`: the borrow around
the call. `none` when it does not. -/
def lendCall (c : TCx) (sp : Span) (f W : Val) : DM (Option Val) := do
  -- `f : !(all 'a < b. P => Q)` or `all 'a < b. P => Q`.
  let (bang, v, P, Q) ← match c.tyV f with
    | some (.bang (.thunk (.all v _ (.ret (.thunk (.arr P (.ret Q))))))) => pure (true, v, P, Q)
    | some (.thunk (.all v _ (.ret (.thunk (.arr P (.ret Q)))))) => pure (false, v, P, Q)
    | _ => return none
  let some (x, m, Px) := lendParam P W | return none
  let (pm, A, fam) ← match Px with
    | .mut (.var w) A => if w == v then pure (Mode.mut, A, false) else return none
    | .imm (.var w) A => if w == v then pure (Mode.imm, A, false) else return none
    | .fam (.mut (.var w) A) => if w == v then pure (Mode.mut, A, true) else return none
    | .fam (.imm (.var w) A) => if w == v then pure (Mode.imm, A, true) else return none
    | _ => return none
  if pm != m then
    throw ⟨x.span, s!"the parameter here is {if pm == .mut then "a `mut`" else "an `imm`"} borrow: " ++
      s!"lend `{x.name}` as `{if pm == .mut then "&mut " else "&"}{x.name}`"⟩
  let f' := if bang then Val.unbang f.span f else f
  if fam then return some (← lendSlice c sp x m A v Q fun l mv =>
    .ret sp (.app sp (.inst sp f' (.var sp l)) (replaceLend mv W)))
  if BoCa.Fig16.LogRel.Core.Check.vfreeB v Q then
    throw ⟨sp, "the call's result mentions the lifetime of the lent place, so the place cannot " ++
      "be handed back after it"⟩
  some <$> lendBorrow c sp x m A Q fun l mv =>
    boxedResult sp l (.ret sp (.app sp (.inst sp f' (.var sp l)) (replaceLend mv W)))

/-- The typing context `c` with the declarations made so far in scope (the instances and copies
made while elaborating the declaration it is in). -/
def refresh (c : TCx) : DM TCx := do
  let st ← get
  let ds := (st.lib ++ st.out ++ st.caps).toArray
  pure { c with E := { c.E with scope := ⟨ds, ds.size⟩ } }

/-! #### The total `for` over data  `[spec §16]`

`for x in V { M }` is Rust's: the source is turned into an iterator by its **type**, and the loop
calls its `next`. A source that is data, or an iterator made from data, is **sized**: its bound is
the length of that data, computed when the loop starts, so the loop is `count_try` (K0′, SPEC §16)
over the bound, calling `next` at each step, and it is total. The kinds of sized source, by type:

* a count `a..b` (`VSugar.count`): the bound is `b − a`, and the element at step `i` is `a + i`;
* a view `array_imm 'a A` or `array_mut 'a A`: the bound is its length, and the element at step `i`
  is the leaf at `i` (`array_get`), or the first leaf of the rest (`slice_split_mut`);
* `&a` or `&mut a` of an owned array `a : array A`: the array lent as its view around the loop
  (`slice_borrow_imm`/`_mut`, SPEC §9), then as a view;
* an owned array `array A` of a persistent `A`: lent `imm` around the loop, each element copied,
  and the array dropped after it;
* a sized iterator `sized D S A` (`lib/iter.bc`): its data `D` (a view, a count, or a pair of
  them), its state `S`, and its step. The bound is `len(D)`: a view's length, a count's `b − a`,
  and a pair's sum. Each step of the loop calls the step once, which answers an element, a skip, or
  the end.

No bound is a number the program gives: it is the length of the data the source's type holds.
Any other source (a generator, an iterator) is a drain, and div (SPEC §14, §15).

The loop's state is the source's cursor (for a sized iterator, its data, state and step) and the
variables the body reads or assigns; the step answers `inl` of the next state, or `inr` of the
threaded variables with the way out: `inl ()` when the source ended early, the value of `break e`,
or the value of `return e`. After the loop, the threaded variables are rebound, and the loop's
value is `e`, or the `else { d }` value when the source ended; `return e` returns from the function,
or leaves the counted loop around it by that loop's exit (`DivSt.exits`). -/

/-- A type of data whose length a sized iterator counts: a view, a count `i32 * i32`, or a pair of
data (a `zip`).  `[spec §16]` -/
def dataTy : Nat → CVTy → Bool
  | 0, _ => false
  | _ + 1, .fam (.imm _ _) | _ + 1, .fam (.mut _ _) => true
  | _ + 1, .tensor (.int .w32) (.int .w32) => true
  | n + 1, .tensor D₁ D₂ => dataTy n D₁ && dataTy n D₂
  | _ + 1, _ => false

/-- `sized D S A` (`D * (S * !(D * S => (D * S) * (A + (1 + 1))))`): its data, state and element
type, when `D` is data.  `[spec §16]` -/
def sizedOf : CVTy → Option (CVTy × CVTy × CVTy)
  | .tensor D (.tensor S (.bang (.thunk (.arr (.tensor D₁ S₁)
      (.ret (.tensor (.tensor D₂ S₂) (.sum A (.sum .unit .unit)))))))) =>
    if D == D₁ && D == D₂ && S == S₁ && S == S₂ && dataTy 64 D then some (D, S, A) else none
  | _ => none

/-- The source of a `for` that is sized, by its type (or its form, for `a..b` and `&a`).
`[spec §16]` -/
inductive DataSrc where
  /-- `a..b`. -/
  | count (lo hi : Val)
  /-- A view `array_imm @a A` (`m = false`) or `array_mut @a A`. -/
  | view (m : Bool) (a : BoCa.Lifetime.Life) (A : CVTy)
  /-- `&a` or `&mut a` (`m`) of an owned array `a : array A`. -/
  | lend (x : Ident) (m : Bool) (A : CVTy)
  /-- An owned array `array A`. -/
  | owned (A : CVTy)
  /-- A sized iterator `sized D S A`. -/
  | sized (D S A : CVTy)

/-- The sized source `V` is, in the context `c`: `none` when it is not data.  `[spec §16]` -/
def dataSrcOf (c : TCx) (V : Val) : Option DataSrc :=
  match V with
  | .app _ (.sugar _ .count) (.pair _ a b) => some (.count a b)
  | .lend _ x m => match c.tyV (.var x.span x.name) with
    | some (.fam (.ref A)) => some (.lend x (m == .mut) A)
    | _ => none
  | V => match c.tyV V with
    | some (.fam (.imm a A)) => some (.view false a A)
    | some (.fam (.mut a A)) => some (.view true a A)
    | some (.fam (.ref A)) => some (.owned A)
    | some T => (sizedOf T).map fun (D, S, A) => .sized D S A
    | none => none

/-- A written function type whose result is a sized iterator: `… => sized D S A`, under `!` and
lifetime binders. -/
def _root_.Frontend.VTy.sizedResult : VTy → Bool
  | .bang _ A | .all _ _ _ A => A.sizedResult
  | .lolli _ _ (.sized ..) => true
  | _ => false

/-- A `for x in V { M }; N` whose source is sized: a counted loop,
one computation (`forData`). A borrow block around it keeps its borrow for the whole loop
(`LoopLend`). A source not yet elaborated, a call of a generic function (a template, named in
`sized`) whose written result is a sized iterator, is sized too.  `[spec §16]` -/
def dataFor (sized : List String) (c : TCx) (V : Val) (M _N : Comp) : Bool :=
  let call := match V with
    | .app _ (.var _ h) _ | .app _ (.unbang _ (.var _ h)) _ | .app _ (.defApp _ h _) _ =>
      sized.contains h
    | _ => false
  (dataSrcOf c V).isSome || call

/-- The templates whose written result is a sized iterator (`dataFor`). -/
def DivSt.sizedFns (st : DivSt) : List String :=
  st.templates.filterMap fun
    | .def_ _ m _ A _ _ => if A.sizedResult then some m.name else none
    | _ => none


/-- The tag of a report on a loop, among the origins (`Frontend/Check/Program.lean` prints them). -/
def reportTag : String := "report: "

/-- The tag of a report on the program's effects (SPEC §18): rows, handlers and the calls of their
clauses. -/
def effectsTag : String := "effects: "

/-- Record a report on the loop at `sp`. -/
def report (sp : Span) (msg : String) : SM Unit :=
  note sp s!"{reportTag}{sp.start.render}: {msg}"

/-- The code that computes `len(D)` of the data held in `v` (a sized iterator's), handing `v`
back: the bindings, and the variable holding the length. A count's is `b − a`; a pair's is the sum
of its parts', at most `2³¹ − 1`.  `[spec §16]` -/
def boundSrc (c : TCx) (sp : Span) : Nat → String → CVTy → Except Error (String × String)
  | 0, _, _ => throw ⟨sp, "internal error: data nested too deeply"⟩
  | _ + 1, v, .fam (.imm a A) => do
    let a ← c.surfaceL sp a
    let A ← c.surface sp A
    pure (s!"let ({v}, {v}_c) = array_copy[{a.pp}, {A.pp}]({v});\n" ++
      s!"{v}_n <- return array_len[{a.pp}, {A.pp}]({v}_c);\n", s!"{v}_n")
  | _ + 1, v, .fam (.mut a A) => do
    let a ← c.surfaceL sp a
    let A ← c.surface sp A
    pure (s!"let ({v}, {v}_n) = slice_len_mut[{a.pp}, {A.pp}]({v});\n", s!"{v}_n")
  | _ + 1, v, .tensor (.int .w32) (.int .w32) =>
    pure (s!"let ({v}_lo, {v}_hi) = {v};\n{v}_n <- return ({v}_hi - {v}_lo);\n" ++
      s!"{v} <- return ({v}_lo, {v}_hi);\n", s!"{v}_n")
  | n + 1, v, .tensor D₁ D₂ => do
    let (s₁, n₁) ← boundSrc c sp n s!"{v}_a" D₁
    let (s₂, n₂) ← boundSrc c sp n s!"{v}_b" D₂
    pure (s!"let ({v}_a, {v}_b) = {v};\n{s₁}{s₂}{v}_s <- return ({n₁} + {n₂});\n" ++
      s!"{v}_n <- if {v}_s < 0 \{ 2147483647 } else \{ {v}_s };\n{v} <- return ({v}_a, {v}_b);\n",
      s!"{v}_n")
  | _ + 1, _, D => throw ⟨sp, s!"internal error: `{ppT D}` is not data"⟩

/-- A function's body under its `fun`s and lifetime binders, rewritten by `f`. -/
def mapFnBody (f : Comp → Except Error Comp) : Val → Except Error Val
  | .bangThunkv sp M => do pure (.bangThunkv sp (← mapLam M))
  | .thunkv sp M => do pure (.thunkv sp (← mapLam M))
  | V => pure V
where
  mapLam : Comp → Except Error Comp
    | .lam sp x A M => do pure (.lam sp x A (← f M))
    | .lamL sp x b (.ret rsp V) => do pure (.lamL sp x b (.ret rsp (← mapFnBody f V)))
    | M => pure M

/-! #### Generic calls

A call's callee may be generic in three ways, and the elaborator fills what the call leaves out
(typed elaboration §2.2–§2.3):

* **A template**: a `fn f[A, …](…)`. It is not elaborated as written, and
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
  | .eff _ _ _ A B fin C => hasPhV A || hasPhV B || hasPhC fin || hasPhC C
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
  | .eff n i q A B fin C =>
      .eff n i q (solvedV σ d A) (solvedV σ d B) (solvedC σ d fin) (solvedC σ d C)
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

/-- Why `patOf` fails, for messages. -/
def patErr (c : TCx) (ps : List String) (P : VTy) : String :=
  match ({ c.E with tps := ps.zipIdx.map fun (x, k) => (x, .tvar (phBase + k)) }.elabV c.Δ P) with
  | .error e => s!": {e.msg}"
  | .ok _ => ""

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

/-! #### Effects: handler sites and effectful calls  `[spec §19]` -/

/-- The kernel's qualifier. -/
def coreQual : Qual → BoCa.Fig16.LogRel.Core.Qual
  | .lin => .lin
  | .aff => .aff
  | .unr => .unr

/-- The type of the computation `C` when it is a returner chain `F[S] A`: `S` and `A`. -/
def rowRes? (C : CCTy) : Option (Frontend.Check.CRow × CVTy) := Frontend.Check.effRow? C

/-- The row a function type's result performs: `F[S]` under its `!`, `∀`s and arrow. -/
def fnRowOf : CVTy → List BoCa.Fig16.LogRel.Core.OpSig
  | .bang A => fnRowOf A
  | .thunk (.all _ _ (.ret A)) => fnRowOf A
  | .thunk (.arr _ C) => ((rowRes? C).map (·.1)).getD []
  | _ => []

/-- The name a call applies: `f(…)`, `f[A](…)`, `f ['x](…)`. -/
def calleeHead : Val → Option String
  | .var _ f | .defApp _ f _ => some f
  | .inst _ V _ | .unbang _ V => calleeHead V
  | _ => none

/-- A call of a function whose result is effectful (`A ⇒ F[S] B`, `S` not empty), as
elaborated in a value: the function and the argument. The function is known by its name. -/
def effCall? (c : TCx) : Val → Option (Val × Val)
  | .app _ f W => match calleeHead f with
    | some g => match c.tyV (.var .none g) with
      | some T => if (fnRowOf T).isEmpty then none else some (f, W)
      | none => none
    | none => none
  | _ => none

/-- An effectful call as the computation it is: `g <- return f; a <- return W; (force g) a`; the
argument's binding annotated with `P` when given. -/
def effCallC (sp : Span) (f W : Val) (P : Option VTy := none) : Comp :=
  let sfx := s!"{sp.start.line}_{sp.start.col}"
  let g : Ident := ⟨s!"io_fg{sfx}", sp⟩
  let a : Ident := ⟨s!"io_fa{sfx}", sp⟩
  .bind sp g none (.ret sp f) (.bind sp a P (.ret sp W) (.app sp (.force sp g) a) false) false

/-- The parameter type of an effectful function's type, outside lifetime binders. -/
def fnParamOf : CVTy → Option CVTy
  | .bang A => fnParamOf A
  | .thunk (.arr P _) => some P
  | _ => none

/-- A value is a closure written in place, or a tuple or injection with one in it: an effectful
block (SPEC §30) is checked against the parameter type, which gives its row. -/
def hasBlockLit : Val → Bool
  | .thunk .. | .thunkv .. | .bangThunk .. | .bangThunkv .. => true
  | .pair _ V W => hasBlockLit V || hasBlockLit W
  | .inl _ V | .inr _ V | .ascribe _ V _ => hasBlockLit V
  | _ => false

/-- A handler site of a control effect, as `Frontend.Elab.Effects` leaves it: the info, the
arguments, the return clause, the operation clauses and the body. -/
def hndCtl? : Val → Option (HInfo × Val × Val × Val × Comp)
  | .app _ (.app _ (.app _ (.app _ (.sugar _ (.hndCtl i)) P) R) cls) (.thunk _ M) => some (i, P, R, cls, M)
  | _ => none

/-- The components of a right-nested tuple of `k` values (`()` and one value for `k ≤ 1`). -/
def tupleArgs : Nat → Val → List Val
  | 0, _ => []
  | 1, V => [V]
  | k + 1, .pair _ V W => V :: tupleArgs k W
  | _, V => [V]

/-- Two types equal once elaborated (abbreviations expanded), or as written. -/
def sameTy (c : TCx) (A B : VTy) : Bool :=
  match c.elabV A, c.elabV B with
  | some A', some B' => A' == B'
  | _, _ => A.strip == B.strip

mutual
/-- The operations `(n, i)` a computation performs, outside closures, by name: its `perform`s and
`abort`s and those of the functions it calls (read off their types), less those of the handler
sites inside it. -/
def opsC (c : TCx) : Nat → Comp → List (Nat × Nat)
  | 0, _ => []
  | k + 1, M => match M with
    | .perform _ n i V | .abort _ n i V => (n, i) :: opsV c k V
    | .handle _ n _ _ M => (opsC c k M).filter (·.1 != n)
    | .ret _ V | .absurd _ V => opsV c k V
    | .bind _ _ _ M N _ | .with_ _ M N => opsC c k M ++ opsC c k N
    | .unwind _ _ _ M D N => opsC c k M ++ opsC c k D ++ opsC c k N
    | .withbor2r _ _ _ _ _ _ _ _ M => opsC c k M
    | .letUnit _ V M | .letPair _ _ _ V M => opsV c k V ++ opsC c k M
    | .case _ V _ M _ N | .for_ _ _ V M N => opsV c k V ++ opsC c k M ++ opsC c k N
    | .app _ M _ | .proj _ _ M | .inst _ M _ | .nuIn _ M | .nuOut _ M | .ascribe _ M _ | .lamL _ _ _ M
    | .lam _ _ _ M => opsC c k M
    | _ => []

/-- `opsC` of a value. -/
def opsV (c : TCx) : Nat → Val → List (Nat × Nat)
  | 0, _ => []
  | k + 1, V => match hndCtl? V with
    | some (i, P, R, cls, B) =>
      opsV c k P ++ opsV c k R ++ opsV c k cls ++ (opsC c k B).filter (·.1 != i.n)
    | none => match V with
      | .app _ f W =>
        let own := match f with
          | .var _ g | .defApp _ g _ | .unbang _ (.var _ g) =>
            ((c.tyV (.var .none g)).map fun T => (fnRowOf T).map fun o => (o.n.toNat, o.i.toNat)).getD []
          | _ => []
        own ++ opsV c k f ++ opsV c k W
      | .pair _ V W => opsV c k V ++ opsV c k W
      | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
      | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => opsV c k V
      | .run _ M | .thunkv _ M => opsC c k M
      | _ => []
end

/-- A callback's context at the row of the borrow block being elaborated, when it has one. -/
def cbRowed (r : Option Frontend.Check.CRow) (c : TCx) : TCx :=
  match r with
  | some S => { c with E := { c.E with row := some S } }
  | none => c

/-- A core row as surface syntax. -/
def surfRow (c : TCx) (sp : Span) : Frontend.Check.CRow → Except Error Frontend.Row
  | [] => pure .nil
  | o :: os => do
    let q : Qual := match o.q with | .lin => .lin | .aff => .aff | .unr => .unr
    pure (.cons o.n.toNat o.i.toNat q (← c.surface sp o.A) (← c.surface sp o.B) (← surfRow c sp os))

/-- A borrow block's constant in its unwinding form, at the row `r` (SPEC §19). -/
def Const.unwinding (r : Frontend.Row) : Const → Option Const
  | .withbor1 x A B => some (.withbor1U x A B r)
  | .withbor2 x b A B => some (.withbor2U x b A B r)
  | .withbor3 a x A B => some (.withbor3U a x A B r)
  | .sliceBorrowMut x b A B => some (.sliceBorrowMutU x b A B r)
  | .sliceBorrowImm x b A B => some (.sliceBorrowImmU x b A B r)
  | _ => none

/-- A borrow block whose constant is an unwinding form, as the computation it is:
`k <- return CONST; p <- return P; f <- return CB; ((force k) p) f`. -/
def unwindingC? (sp : Span) : Val → Option Comp
  | .app _ (.app _ (.const ksp C) P) cb => match C with
    | .withbor1U .. | .withbor2U .. | .withbor3U .. | .sliceBorrowMutU .. | .sliceBorrowImmU .. =>
      let sfx := s!"{sp.start.line}_{sp.start.col}"
      let k : Ident := ⟨s!"io_uk{sfx}", sp⟩
      let p : Ident := ⟨s!"io_up{sfx}", sp⟩
      let f : Ident := ⟨s!"io_uf{sfx}", sp⟩
      -- The callback is ascribed its type: a computation synthesized in a value performs
      -- nothing, and the callback's body performs the row's operations.
      let cbTy : Option VTy := match C with
        | .withbor1U x A B r => some (ty x (.imm sp (.var sp x.name) A) B r)
        | .withbor2U x _ A B r | .withbor3U _ x A B r => some (ty x (.mut sp (.var sp x.name) A) B r)
        | .sliceBorrowMutU x _ A B r => some (ty x (.arrayMut sp (.var sp x.name) A) B r)
        | .sliceBorrowImmU x _ A B r => some (ty x (.arrayImm sp (.var sp x.name) A) B r)
        | _ => none
      -- Its `∀` is over the computation `L ⊸ F[S] (['x] B)` itself, not over a returned thunk.
      let cb := match cb with
        | .thunkv tsp (.lamL lsp xi b (.ret _ (.thunkv _ L))) => Val.thunkv tsp (.lamL lsp xi b L)
        | cb => cb
      some (.bind sp k none (.ret sp (.const ksp C)) (.bind sp p none (.ret sp P)
        (.bind sp f cbTy (.ret sp cb) (.app sp (.app sp (.force sp k) p) f) false) false) false)
    | _ => none
  | _ => none
where
  ty (x : Ident) (L B : VTy) (r : Frontend.Row) : VTy :=
    .thunk sp (.all sp x (.dom sp) (.arr sp L (.eff sp r (.box sp (.var sp x.name) B))))

/-- A `mut` borrow block of an owned cell whose body performs resuming operations, as the relaxed
lend R1 (SPEC §29): `p <- return P; withbor2r['x, @b, A, B, [r]](p, m) M`, from the unwinding
form `withbor2u['x, @b, A, B, [r]] P (thunkv Fun 'x < @b. return (thunkv fun (m : …) -> M))` the
block elaborates to. -/
def relaxedC? (sp : Span) : Val → Option (Ident × Comp)
  | .app _ (.app _ (.const _ (.withbor2U x b A B r)) P)
      (.thunkv _ (.lamL _ _ _ (.ret _ (.thunkv _ (.lam _ m _ M))))) =>
    let p : Ident := ⟨s!"io_rp{sp.start.line}_{sp.start.col}", sp⟩
    some (m, .bind sp p none (.ret sp P) (.withbor2r sp x b A B r p m M) false)
  | _ => none

/-- A borrow block, as written. -/
def borrowBlock? : Val → Option Comp
  | .app _ (.app _ (.sugar _ (.borrow k _)) _) (.thunkv _ (.lam _ _ _ M)) =>
    if k == .modify then none else some M
  | _ => none

/-- A borrow block's kind and place. -/
def borrowKind? : Val → Option (BorrowKind × Val)
  | .app _ (.app _ (.sugar _ (.borrow k _)) P) (.thunkv _ (.lam _ _ _ _)) => some (k, P)
  | _ => none

/-- The components of a `()`-terminated tuple. -/
def clauseList : Val → List Val
  | .pair _ V W => V :: clauseList W
  | _ => []

/-- The marker binding around what follows a loop whose body is elaborated under the loop's exit
(`DivSt.exits`): `surfC` elaborates what it binds around without that exit, and drops it. -/
def restScope : String := "io_rest_scope"

/-- `N`, what follows a loop, marked as outside it (`restScope`). -/
def restOf (N : Comp) : Comp :=
  .bind N.span ⟨restScope, N.span⟩ none (.ret N.span (.unit N.span)) N false

/-! ### The machine of a recursion under a heap driver  `[spec §20]`

A recursive group driven by a heap driver (`with deep { … }`, `Frontend.Elab.Effects.deepCopy`)
is given as a machine: `start : !(A => Out)` runs a member's body on its tagged argument until it
answers `b` (`inl b`) or calls the group (`inr (a, f)`), and `resume : !(K * B => Out)` continues
a pending call's frame with the answer, `Out = B + A * (K + 1)`. The frames are first-order:
`K` has a variant per call of the group that is not in tail position, holding the variables the
rest of the body uses there, with their types; a call in tail position pushes none (`f = inr ()`).

The machine is made from the group's source `g__mach_src` after its sugar is elaborated: a
function of the members' self-references `fx_rself{j}` whose result is the body. A call of a
self-reference is lifted out of the value it is in, in the order its evaluation runs it, and the
rest of the body is moved into it (`x <- case …; N` into each arm), so that every call stands at a
binding `x <- return fx_rself{j}(W); N`. There the code answers the request, and the resume arm of
its frame binds the frame's variables and `x`, and goes on with `N`. -/

/-- The member a self-reference calls, and the argument: `(unbang fx_rself{j}) W`. -/
def rmSelfApp? : Val → Option (Nat × Val)
  | .app _ (.unbang _ (.var _ x)) W | .app _ (.var _ x) W =>
    if x.startsWith "fx_rself" then (x.drop 8).toNat?.map (·, W) else none
  | _ => none

mutual
/-- A value calls a self-reference. -/
def rmSelfIn : Val → Bool
  | V@(.app _ f W) => (rmSelfApp? V).isSome || rmSelfIn f || rmSelfIn W
  | .pair _ V W => rmSelfIn V || rmSelfIn W
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => rmSelfIn V
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => rmSelfInC M
  | _ => false

/-- A computation calls a self-reference. -/
def rmSelfInC : Comp → Bool
  | .ret _ V | .absurd _ V | .perform _ _ _ V | .abort _ _ _ V => rmSelfIn V
  | .bind _ _ _ M N _ | .with_ _ M N => rmSelfInC M || rmSelfInC N
  | .letUnit _ V M | .letPair _ _ _ V M => rmSelfIn V || rmSelfInC M
  | .case _ V _ M _ N | .for_ _ _ V M N => rmSelfIn V || rmSelfInC M || rmSelfInC N
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ | .handle _ _ _ _ M => rmSelfInC M
  | .unwind _ _ _ M D N => rmSelfInC M || rmSelfInC D || rmSelfInC N
  | .withbor2r _ _ _ _ _ _ _ _ M => rmSelfInC M
  | _ => false
end

/-- The first call of a self-reference `V` runs (its argument calls none), replaced by `y`: the
member, its argument, and `V` with the call replaced. -/
def rmTake (y : String) : Nat → Val → Option (Nat × Val × Val)
  | 0, _ => none
  | n + 1, V => match V with
    | .app sp f W =>
      -- The argument runs before the function.
      match rmTake y n W with
      | some (j, a, W') => some (j, a, .app sp f W')
      | none => match rmSelfApp? V with
        | some (j, a) => some (j, a, .var sp y)
        | none => (rmTake y n f).map fun (j, a, f') => (j, a, .app sp f' W)
    | .pair sp V W => match rmTake y n V with
      | some (j, a, V') => some (j, a, .pair sp V' W)
      | none => (rmTake y n W).map fun (j, a, W') => (j, a, .pair sp V W')
    | .inl sp V => (rmTake y n V).map fun (j, a, V') => (j, a, .inl sp V')
    | .inr sp V => (rmTake y n V).map fun (j, a, V') => (j, a, .inr sp V')
    | .ascribe sp V A => (rmTake y n V).map fun (j, a, V') => (j, a, .ascribe sp V' A)
    | .roll sp V => (rmTake y n V).map fun (j, a, V') => (j, a, .roll sp V')
    | .unroll sp V => (rmTake y n V).map fun (j, a, V') => (j, a, .unroll sp V')
    | .unbang sp V => (rmTake y n V).map fun (j, a, V') => (j, a, .unbang sp V')
    | _ => none

/-- What the machine's construction knows: the group's argument type and its member count, the
answer type, the number of frames (known on the second pass), and the context of a resume arm. -/
structure RMInfo where
  A : VTy
  members : Nat
  B : VTy
  B' : CVTy
  nf : Nat
  base : TCx

structure RMSt where
  frames : Array (List (String × CVTy)) := #[]
  /-- Each frame's resume arm: the variable its payload is bound to, and the code. -/
  arms : Array (String × Comp) := #[]
  fresh : Nat := 0

abbrev RMM := StateT RMSt SM

def rmFresh (pre : String) : RMM String :=
  modifyGet fun s => (s!"{pre}{s.fresh}", { s with fresh := s.fresh + 1 })

/-- The placeholder of `Out`, filled when the frames are known. -/
def rmOut (sp : Span) : VTy := .name sp "FX_REC_OUT"

/-- A value of `Out`, written. -/
def rmAns (sp : Span) (V : Val) : Comp := .ret sp (.ascribe sp V (rmOut sp))

/-- The variables bound from the tuple `v` of `vars`, then `M`. -/
def rmUnpack (sp : Span) (v : String) : List String → Comp → RMM Comp
  | [], M => pure (.letUnit sp (.var sp v) M)
  | [x], M => pure (.bind sp ⟨x, sp⟩ none (.ret sp (.var sp v)) M false)
  | x :: xs, M => do
    let r ← rmFresh "fx_rmr"
    pure (.letPair sp ⟨x, sp⟩ ⟨r, sp⟩ (.var sp v) (← rmUnpack sp r xs M))

mutual
/-- The machine's code for `M`: it answers `inl` of each value `M` finishes with, and a request
at each call of a self-reference. -/
def rmWalk (I : RMInfo) : Nat → TCx → Comp → RMM Comp
  | 0, _, M => throw ⟨M.span, "internal error: a body nested too deeply"⟩
  | n + 1, c, M => match M with
    | .bind sp x A (.ret rsp V) N lin =>
      match rmSelfApp? V with
      | some (j, W) =>
        if rmSelfIn W then do
          let y ← rmFresh "fx_rmy"
          let some (j', a, W') := rmTake y divFuel W | throw ⟨sp, "internal error: a call of the group"⟩
          rmWalk I n c (.bind sp ⟨y, sp⟩ none (.ret rsp (.app rsp (.var rsp s!"fx_rself{j'}") a))
            (.bind sp x A (.ret rsp (.app rsp (.var rsp s!"fx_rself{j}") W')) N lin) false)
        else rmCall I n c sp x j W N
      | none =>
        if rmSelfIn V then do
          let y ← rmFresh "fx_rmy"
          let some (j, a, V') := rmTake y divFuel V | throw ⟨sp, "internal error: a call of the group"⟩
          rmWalk I n c (.bind sp ⟨y, sp⟩ none (.ret rsp (.app rsp (.var rsp s!"fx_rself{j}") a))
            (.bind sp x A (.ret rsp V') N lin) false)
        else do
          pure (.bind sp x A (.ret rsp V) (← rmWalk I n (c.push x.name (bindTy c A (.ret rsp V))) N) lin)
    | .bind sp x A M₁ N lin =>
      if !rmSelfInC M₁ then do
        pure (.bind sp x A M₁ (← rmWalk I n (c.push x.name (bindTy c A M₁)) N) lin)
      else
        let shadow (ys : List String) : RMM Unit := do
          if ys.any (mentionsC · N) then
            throw ⟨sp, "a recursion under a heap driver binds a name the rest of its body uses: rename it"⟩
        match M₁ with
        | .bind bsp y B M₁₁ M₁₂ lin' => do
          shadow [y.name]
          rmWalk I n c (.bind bsp y B M₁₁ (.bind sp x A M₁₂ N lin) lin')
        | .case csp V y P z Q => do
          shadow [y.name, z.name]
          rmWalk I n c (.case csp V y (.bind sp x A P N lin) z (.bind sp x A Q N lin))
        | .letPair lsp y z V P => do
          shadow [y.name, z.name]
          rmWalk I n c (.letPair lsp y z V (.bind sp x A P N lin))
        | .letUnit lsp V P => rmWalk I n c (.letUnit lsp V (.bind sp x A P N lin))
        | _ => throw ⟨M₁.span, "a recursion under a heap driver calls itself in a form that is not provided here"⟩
    | .ret sp V =>
      if rmSelfIn V then do
        let y ← rmFresh "fx_rmy"
        let some (j, a, V') := rmTake y divFuel V | throw ⟨sp, "internal error: a call of the group"⟩
        rmWalk I n c (.bind sp ⟨y, sp⟩ none (.ret sp (.app sp (.var sp s!"fx_rself{j}") a))
          (.ret sp V') false)
      else pure (rmAns sp (.inl sp V))
    | .case sp V x M₁ y M₂ =>
      if rmSelfIn V then do
        let t ← rmFresh "fx_rmt"
        rmWalk I n c (.bind sp ⟨t, sp⟩ none (.ret sp V) (.case sp (.var sp t) x M₁ y M₂) false)
      else do
        let (Ax, Ay) := sumTys c V
        pure (.case sp V x (← rmWalk I n (c.push x.name Ax) M₁) y (← rmWalk I n (c.push y.name Ay) M₂))
    | .letPair sp x y V M₁ =>
      if rmSelfIn V then do
        let t ← rmFresh "fx_rmt"
        rmWalk I n c (.bind sp ⟨t, sp⟩ none (.ret sp V) (.letPair sp x y (.var sp t) M₁) false)
      else do
        let (Ax, Ay) := pairTys c V
        pure (.letPair sp x y V (← rmWalk I n ((c.push x.name Ax).push y.name Ay) M₁))
    | .letUnit sp V M₁ =>
      if rmSelfIn V then do
        let t ← rmFresh "fx_rmt"
        rmWalk I n c (.bind sp ⟨t, sp⟩ none (.ret sp V) (.letUnit sp (.var sp t) M₁) false)
      else do pure (.letUnit sp V (← rmWalk I n c M₁))
    | T => do
      if rmSelfInC T then
        throw ⟨T.span, "a recursion under a heap driver calls itself in a form that is not provided here"⟩
      let t ← rmFresh "fx_rmt"
      pure (.bind T.span ⟨t, T.span⟩ none T (rmAns T.span (.inl T.span (.var T.span t))) false)

/-- `x <- return fx_rself{j}(W); N`: the request `inr (inj_j W, f)`, with the frame `f` of what
`N` uses (none when `N` answers `x`), and the frame's resume arm. -/
def rmCall (I : RMInfo) : Nat → TCx → Span → Ident → Nat → Val → Comp → RMM Comp
  | 0, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | n + 1, c, sp, x, j, W, N => do
    let arg : Val := .ascribe sp (Elab.Effects.injAt sp j I.members W) I.A
    let tail := match N with
      | .ret _ (.var _ y) => y == x.name
      | _ => false
    if tail then return rmAns sp (.inr sp (.pair sp arg (.inr sp (.unit sp))))
    let mut vars : List (String × CVTy) := []
    for (y, T) in latest c.locals do
      if y == x.name || y.startsWith "fx_rself" || !mentionsC y N then continue
      match T with
      | some T => vars := vars ++ [(y, T)]
      | none => throw ⟨sp, s!"`{y}` is held across a call of the recursion, and its type is not determined: ascribe it"⟩
    let f := (← get).frames.size
    modify fun s => { s with frames := s.frames.push vars, arms := s.arms.push ("", .top sp) }
    -- The resume arm: the frame's variables, `x` the answer, then `N`.
    let cR := (vars.foldl (fun c (y, T) => c.push y (some T)) I.base).push x.name (some I.B')
    let rest ← rmWalk I n cR N
    let kv ← rmFresh "fx_rmk"
    let arm ← rmUnpack sp kv (vars.map (·.1)) (.bind sp x none (.ret sp (.var sp "fx_rmb")) rest false)
    modify fun s => { s with arms := s.arms.set! f (kv, arm) }
    let frame : Val := Elab.Effects.injAt sp f I.nf (tupleVal sp (vars.map (·.1)))
    pure (rmAns sp (.inr sp (.pair sp arg (.inl sp frame))))
end

/-- The machine `g__mach : !(A => Out) * !(K * B => Out)` of a recursive group's source
`g__mach_src` whose sugar is elaborated (SPEC §20, `rmWalk`): `start` on the tagged argument, and
`resume` on a frame and the answer. -/
def recMachine (scope : List Decl) (d : Decl) : SM Decl := do
  let .def_ sp n _ Ty V _ := d | return d
  let g := (n.name.dropEnd "__mach_src".length).toString
  let err (what : String) : Error := ⟨sp, s!"internal error: the machine of `{g}`: {what}"⟩
  let .bangThunkv _ (.lam _ p Pt M₀) := V | throw (err "its source")
  let .bang _ (.lolli _ _ (.bang _ (.lolli _ _ B))) := Ty | throw (err "its type")
  let c₀ := TCx.ofScope scope false
  let some Pc := c₀.elabV Pt | throw (err "the self-references' type")
  let some Bc := c₀.elabV B | throw (err "the answer type")
  let rec peel : Nat → TCx → Comp → Except Error (TCx × Ident × VTy × Comp)
    | k + 1, c, .bind _ x A M N _ => peel k (c.push x.name (bindTy c A M)) N
    | k + 1, c, .letPair _ x y W N =>
      let (Ax, Ay) := pairTys c W
      peel k ((c.push x.name Ax).push y.name Ay) N
    | k + 1, c, .letUnit _ _ N => peel k c N
    | _, c, .ret _ (.bangThunkv _ (.lam _ a A D)) => pure (c, a, A, D)
    | _, _, _ => throw (err "its body")
  let (c₁, a, A, D) ← peel 64 (c₀.push p.name (some Pc)) M₀
  let some Ac := c₁.elabV A | throw (err "the argument type")
  let c₂ := c₁.push a.name (some Ac)
  let members := (c₁.locals.filter (·.1.startsWith "fx_rself")).length
  let I : RMInfo := ⟨A, members, B, Bc, 0, c₀⟩
  let (_, st₁) ← (rmWalk I divFuel c₂ D).run {}
  let I := { I with nf := st₁.frames.size }
  let (S₀, st) ← (rmWalk I divFuel c₂ D).run {}
  let mut ks : List VTy := []
  for vs in st.frames do
    ks := ks ++ [tupleTy sp (← vs.mapM fun (_, T) => (c₀.surface sp T : Except Error VTy))]
  let K := Elab.Effects.sumTys sp ks
  let Out : VTy := .sum sp B (.tensor sp A (.sum sp K (.unit sp)))
  let σ : TySubst := [("FX_REC_OUT", Out)]
  let start : Val := .bangThunkv sp (.lam sp a A (S₀.subst σ))
  -- The resume: the frame's variant, then its arm.
  let rec dispatch : Nat → String → List (String × Comp) → Comp
    | _, v, [] => .absurd sp (.var sp v)
    | _, v, [(kv, arm)] => .bind sp ⟨kv, sp⟩ none (.ret sp (.var sp v)) (arm.subst σ) false
    | 0, v, _ => .absurd sp (.var sp v)
    | k + 1, v, (kv, arm) :: rest =>
      .case sp (.var sp v) ⟨kv, sp⟩ (arm.subst σ) ⟨s!"{v}r", sp⟩ (dispatch k s!"{v}r" rest)
  let resume : Val := .bangThunkv sp (.lam sp ⟨"fx_rmkb", sp⟩ (.tensor sp K B)
    (.letPair sp ⟨"fx_rmk", sp⟩ ⟨"fx_rmb", sp⟩ (.var sp "fx_rmkb")
      (dispatch (st.arms.size + 1) "fx_rmk" st.arms.toList)))
  report sp s!"recursion `{g}` under a heap driver: {st.frames.size} frame(s), each a variant of one buffer slot"
  pure (.def_ sp ⟨s!"{g}__mach", n.span⟩ []
    (.tensor sp (.bang sp (.lolli sp A Out)) (.bang sp (.lolli sp (.tensor sp K B) Out)))
    (.pair sp start resume) .none)

mutual
/-- A value with its surface forms elaborated; `exp` is the type expected of it, when known. -/
def surfV : Nat → TCx → Option CVTy → Val → DM Val
  | 0, _, _, V => pure V
  | n + 1, c, exp, V =>
    -- A value performs no operation: its computations are at no row, as the checker has them.
    let c := { c with E := { c.E with row := none } }
    match V with
    | .sugar sp (.lit k) => pure (litAt sp ((widthOf exp).getD .w32) k)
    | .sugar sp (.str bs) => pure (litValue sp bs)
    | .defApp sp "filler" [A] => do
      -- `filler[A]`: the filler of a buffer's unused slots, by the type (design §5.4).
      let A' ← need sp "`filler`'s type" (c.elabV A)
      match ← (fillerOf c sp 64 A' : Except Error (Option Val)) with
      | some v => pure v
      | none => throw ⟨sp, s!"`{ppT A'}` has no filler: a buffer holds elements that have one " ++
          "(integers, views, arrays, and pairs and sums of them)"⟩
    | .app sp (.sugar _ .count) (.pair _ a b) => do
      -- `a..b` as a value: the sized iterator of the count, its data `(a, b)` and its step
      -- (SPEC §16). A `for` over `a..b` itself is elaborated by `forData`.
      let T := "((i32 * i32) * 1) * (i32 + (1 + 1))"
      let L ← (template sp "a count `a..b`" s!"return ((io_hole_a, io_hole_b), ((), (!thunkv fun (io_cp : (i32 * i32) * 1) ->
  let (io_cd, io_cu) = io_cp;
  let (io_clo, io_chi) = io_cd;
  io_cr : {T} <- if io_clo < io_chi \{ return (((io_clo + 1, io_chi), io_cu), inl io_clo) }
    else \{ return (((io_clo, io_chi), io_cu), inr (inr ())) };
  return io_cr)))" : SM Comp)
      let L := L.fill (fun h => if h == "io_hole_a" then some a else if h == "io_hole_b" then some b
        else none) (fun _ => none)
      surfV n c exp (.run sp L)
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
      -- The callback's row, when this block is an unwinding borrow; blocks inside are not.
      let cbr := (← get).cbRow
      modify fun st => { st with cbRow := none }
      let P' ← surfV n c none P
      let tP ← need P.span "the borrowed place" (c.tyV P')
      match k, tP with
      | .imm, .ref A | .mut, .ref A => do
        let dom ← need lsp "the block's bound" (c.elabL (.dom lsp))
        let c₁ := c.pushLife x dom
        let some v := c₁.E.lenv.lookup x | throw ⟨lsp, "internal error: a borrow block"⟩
        let Tb : CVTy := if k == .imm then .imm (.var v) A else .mut (.var v) A
        let S' ← surfC n (cbRowed cbr (c₁.push b.name (some Tb))) none S
        let B ← need tsp "the block's result" (resultOfC (cbRowed cbr ((← refresh c₁).push b.name (some Tb)) |>.tyC S'))
        if BoCa.Fig16.LogRel.Core.Check.vfreeB v B then
          throw (Frontend.Elab.LoopLend.escapeError tsp x (Frontend.Check.ppV c₁.E.lenv 0 0 B))
        let As ← c.surface ksp A
        let Bs ← c.surface ksp B
        let xi : Ident := ⟨x, ksp⟩
        -- The side conditions' bound is `dom`: the result may hold a borrow of an enclosing
        -- block (a handler's capability, SPEC §18).
        let C := if k == .imm then Const.withbor1 xi As Bs else .withbor2 xi (.dom ksp) As Bs
        let C ← match cbr with
          | some r => do pure ((Const.unwinding (← (surfRow c ksp r : Except Error Frontend.Row)) C).getD C)
          | none => pure C
        let Tbs := if k == .imm then VTy.imm lsp (.var lsp x) As else .mut lsp (.var lsp x) As
        pure (.app sp (.app sp₂ (.const ksp C) P') (.thunkv tsp (.lamL lsp xi (.dom lsp)
          (.ret lsp (.thunkv lsp (.lam lsp b Tbs (boxTail x S')))))))
      | .mut, .mut a A => do
        -- A `mut` borrow reborrowed for the block (`withbor3`): the place gets it back after.
        let dom ← need lsp "the block's bound" (c.elabL (.dom lsp))
        let c₁ := c.pushLife x dom
        let some v := c₁.E.lenv.lookup x | throw ⟨lsp, "internal error: a borrow block"⟩
        let Tb : CVTy := .mut (.var v) A
        let S' ← surfC n (cbRowed cbr (c₁.push b.name (some Tb))) none S
        let B ← need tsp "the block's result" (resultOfC (cbRowed cbr ((← refresh c₁).push b.name (some Tb)) |>.tyC S'))
        if BoCa.Fig16.LogRel.Core.Check.vfreeB v B then
          throw (Frontend.Elab.LoopLend.escapeError tsp x (Frontend.Check.ppV c₁.E.lenv 0 0 B))
        let As ← c.surface ksp A
        let Bs ← c.surface ksp B
        let xi : Ident := ⟨x, ksp⟩
        let C := Const.withbor3 (← c.surfaceL ksp a) xi As Bs
        let C ← match cbr with
          | some r => do pure ((Const.unwinding (← (surfRow c ksp r : Except Error Frontend.Row)) C).getD C)
          | none => pure C
        let Tbs := VTy.mut lsp (.var lsp x) As
        pure (.app sp (.app sp₂ (.const ksp C) P') (.thunkv tsp (.lamL lsp xi (.dom lsp)
          (.ret lsp (.thunkv lsp (.lam lsp b Tbs (boxTail x S')))))))
      | .imm, .fam (.ref A) | .mut, .fam (.ref A) => do
        -- An owned array lent as a family of leaf borrows, with no cell (`slice_borrow_*`,
        -- SPEC §9).
        let dom ← need lsp "the block's bound" (c.elabL (.dom lsp))
        let c₁ := c.pushLife x dom
        let some v := c₁.E.lenv.lookup x | throw ⟨lsp, "internal error: a borrow block"⟩
        let Tb : CVTy := .fam (if k == .imm then .imm (.var v) A else .mut (.var v) A)
        let S' ← surfC n (cbRowed cbr (c₁.push b.name (some Tb))) none S
        let B ← need tsp "the block's result" (resultOfC (cbRowed cbr ((← refresh c₁).push b.name (some Tb)) |>.tyC S'))
        if BoCa.Fig16.LogRel.Core.Check.vfreeB v B then
          throw (Frontend.Elab.LoopLend.escapeError tsp x (Frontend.Check.ppV c₁.E.lenv 0 0 B))
        let As ← c.surface ksp A
        let Bs ← c.surface ksp B
        let xi : Ident := ⟨x, ksp⟩
        let C := if k == .imm then Const.sliceBorrowImm xi (.dom ksp) As Bs
          else .sliceBorrowMut xi (.dom ksp) As Bs
        let C ← match cbr with
          | some r => do pure ((Const.unwinding (← (surfRow c ksp r : Except Error Frontend.Row)) C).getD C)
          | none => pure C
        let Tbs := if k == .imm then VTy.arrayImm lsp (.var lsp x) As else .arrayMut lsp (.var lsp x) As
        pure (.app sp (.app sp₂ (.const ksp C) P') (.thunkv tsp (.lamL lsp xi (.dom lsp)
          (.ret lsp (.thunkv lsp (.lam lsp b Tbs (boxTail x S')))))))
      | .imm, .tensor (.fam (.ref A)) (.int .w32) | .mut, .tensor (.fam (.ref A)) (.int .w32) => do
        -- A buffer `buf A = array A * i32`: its array lent as a family (`slice_borrow_*`, SPEC
        -- §9), cut at the length (`slice_split_*`), and the initialised prefix lent to the block;
        -- the rest is dropped. The buffer is handed back whole.
        let imm := k == .imm
        let dom ← need lsp "the block's bound" (c.elabL (.dom lsp))
        let c₁ := c.pushLife x dom
        let some v := c₁.E.lenv.lookup x | throw ⟨lsp, "internal error: a borrow block"⟩
        let Tb : CVTy := .fam (if imm then .imm (.var v) A else .mut (.var v) A)
        let S' ← surfC n (cbRowed cbr (c₁.push b.name (some Tb))) none S
        let B ← need tsp "the block's result" (resultOfC (cbRowed cbr ((← refresh c₁).push b.name (some Tb)) |>.tyC S'))
        if BoCa.Fig16.LogRel.Core.Check.vfreeB v B then
          throw (Frontend.Elab.LoopLend.escapeError tsp x (Frontend.Check.ppV c₁.E.lenv 0 0 B))
        let As ← c.surface ksp A
        let Bs ← c.surface ksp B
        let xi : Ident := ⟨x, ksp⟩
        -- The side conditions' bound is `dom`: the elements (views, say) may have lifetimes.
        let C := if imm then Const.sliceBorrowImm xi (.dom ksp) As Bs else .sliceBorrowMut xi (.dom ksp) As Bs
        let Tbs := if imm then VTy.arrayImm lsp (.var lsp x) As else .arrayMut lsp (.var lsp x) As
        let splitC := if imm then Const.sliceSplitImm (.var lsp x) As else .sliceSplitMut (.var lsp x) As
        let id (s : String) : Ident := ⟨s, lsp⟩
        let body : Comp := .bind lsp b none
          (.case lsp (.app lsp (.unbang lsp (.const lsp splitC))
              (.pair lsp (.var lsp "io_bw") (.var lsp "io_bn")))
            (id "io_bp") (.letPair lsp (id "io_bv") (id "io_bq") (.var lsp "io_bp") (.ret lsp (.var lsp "io_bv")))
            (id "io_bo") (.ret lsp (.var lsp "io_bo")))
          (boxTail x S') false
        let cb : Val := .thunkv tsp (.lamL lsp xi (.dom lsp) (.ret lsp (.thunkv lsp
          (.lam lsp (id "io_bw") Tbs body))))
        let ids (s : String) : Ident := ⟨s, sp⟩
        -- Ascribed its type, which the typing of what follows it reads.
        let bufTy : VTy := .tensor sp (.array sp As) (.int sp .w32)
        pure <| (fun v => Val.ascribe sp v (.tensor sp bufTy Bs)) <| (.run sp (.letPair sp (ids "io_ba") (ids "io_bn") P'
          (.bind sp (ids "io_br") none (.ret sp (.app sp (.app sp₂ (.const ksp C) (.var sp "io_ba")) cb))
            (.letPair sp (ids "io_ba2") (ids "io_bv2") (.var sp "io_br")
              (.ret sp (.pair sp (.pair sp (.var sp "io_ba2") (.var sp "io_bn")) (.var sp "io_bv2"))))
            false)))
      | .imm, .tensor (.int .w32) (.bang (.thunk (.arr (.int .w32) (.ret (.int .w8))))) => do
        -- A literal `lit = i32 * !(i32 => u8)`: its bytes tabulated into an array, lent as a
        -- family, and the array freed (`lit_view`, design §5.7). The callback first copies the
        -- family (`array_copy`, only at an `imm` family), which the backend reads as the
        -- promise that the array is not written: it points the view at the literal's read-only
        -- data (`Backend/README.md`, Literals). The literal is handed back.
        let dom ← need lsp "the block's bound" (c.elabL (.dom lsp))
        let c₁ := c.pushLife x dom
        let some v := c₁.E.lenv.lookup x | throw ⟨lsp, "internal error: a borrow block"⟩
        let U8 : CVTy := .int .w8
        let Tb : CVTy := .fam (.imm (.var v) U8)
        let S' ← surfC n (cbRowed cbr (c₁.push b.name (some Tb))) none S
        let B ← need tsp "the block's result" (resultOfC (cbRowed cbr ((← refresh c₁).push b.name (some Tb)) |>.tyC S'))
        if BoCa.Fig16.LogRel.Core.Check.vfreeB v B then
          throw (Frontend.Elab.LoopLend.escapeError tsp x (Frontend.Check.ppV c₁.E.lenv 0 0 B))
        let U8s : VTy := .int ksp .w8
        let Bs ← c.surface ksp B
        let xi : Ident := ⟨x, ksp⟩
        let id (s : String) : Ident := ⟨s, lsp⟩
        let body : Comp := .letPair lsp (id "io_lc") (id "io_ld")
          (.app lsp (.unbang lsp (.const lsp (.arrayCopy (.var lsp x) U8s))) (.var lsp "io_lw"))
          (.bind lsp b none (.ret lsp (.var lsp "io_lc")) (boxTail x S') false)
        let cb : Val := .thunkv tsp (.lamL lsp xi (.dom lsp) (.ret lsp (.thunkv lsp
          (.lam lsp (id "io_lw") (.arrayImm lsp (.var lsp x) U8s) body))))
        let ids (s : String) : Ident := ⟨s, sp⟩
        let litTy : VTy := .tensor sp (.int sp .w32) (.bang sp (.lolli sp (.int sp .w32) U8s))
        pure <| (fun v => Val.ascribe sp v (.tensor sp litTy Bs)) <| (.run sp (.bind sp (ids "io_lp") none (.ret sp P')
          (.letPair sp (ids "io_ln") (ids "io_lt") (.var sp "io_lp")
            (.bind sp (ids "io_la") none (.ret sp (.app sp (.unbang sp (.const sp (.arrayNew U8s)))
                (.pair sp (.var sp "io_ln") (.var sp "io_lt"))))
              (.bind sp (ids "io_lr") none
                (.ret sp (.app sp (.app sp₂ (.const ksp (.sliceBorrowImm xi (.dom ksp) U8s Bs))
                  (.var sp "io_la")) cb))
                (.letPair sp (ids "io_la2") (ids "io_lv") (.var sp "io_lr")
                  (.ret sp (.pair sp (.var sp "io_lp") (.var sp "io_lv")))) false) false)) false))
      | .famMut, .tensor (.ref A) (.ref B) => do
        let dom ← need lsp "the block's bound" (c.elabL (.dom lsp))
        let c₁ := c.pushLife x dom
        let some v := c₁.E.lenv.lookup x | throw ⟨lsp, "internal error: a borrow block"⟩
        let Tb : CVTy := .tensor (.mut (.var v) A) (.mut (.var v) B)
        let S' ← surfC n (cbRowed cbr (c₁.push b.name (some Tb))) none S
        let T ← need tsp "the block's result" (resultOfC (cbRowed cbr ((← refresh c₁).push b.name (some Tb)) |>.tyC S'))
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
      if let some V' ← genericCall n c sp exp f W none then return V'
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
      | some t => do
        let (nm, extras) ← makeInst n c sp t (args.map c.elabV).toArray
        if extras.isEmpty then pure (.var sp nm) else
          -- The instance's own lifetimes at the call's.
          let mut g : Val := .unbang sp (.var sp nm)
          for v in extras do g := .inst sp g (← c.surfaceL sp (.var v))
          pure g
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
  | n + 1, c, exp, M =>
    -- The row of the expected type, as the checker sets it (SPEC §19).
    let c := match exp with
      | some C => { c with E := c.E.atC C }
      | none => c
    match M with
    | .ret sp V => do
      if let some (i, P, R, cls, B) := hndCtl? V then return ← hndCtlC n c sp i P R cls B
      if let .app _ (.sugar _ (.pullSite i)) call := V then return ← pullView n c sp i call
      if let some B := borrowBlock? V then
        if let some S := c.E.row then
          -- A borrow block whose body performs operations: the unwinding form of its borrow, at
          -- the operations of the names the body performs (SPEC §19).
          let used := (opsC c divFuel B).map (·.1)
          let r := S.filter fun o => used.contains o.n.toNat
          if !r.isEmpty then
            if let some o := r.find? (fun o => !o.abort) then
              -- A `mut` borrow of an owned cell: the relaxed lend R1 (SPEC §29).
              if let some (.mut, P) := borrowKind? V then
                if let some (.ref _) := c.tyV P then
                  if let some a := r.find? (·.abort) then
                    throw ⟨V.span, s!"this borrow block's body performs the operation {o.n}.{o.i}, " ++
                      s!"which resumes, and the abortive operation {a.n}.{a.i}: an abortive " ++
                      "operation does not cross a borrow held across a resumption (R1, SPEC §29)"⟩
                  let saved := (← get).cbRow
                  modify fun st => { st with cbRow := some r }
                  let V' ← surfV n c none V
                  modify fun st => { st with cbRow := saved }
                  match relaxedC? V.span V' with
                  | some (m, M') =>
                    let body := match M' with
                      | .bind _ _ _ _ (.withbor2r _ _ _ _ _ _ _ _ B) _ => B
                      | M => M
                    let outer := c.E.vars.filterMap id |>.filter fun y =>
                      y != m.name && Frontend.Check.mentionsC y body
                    if let some y := outer.head? then
                      throw ⟨V.span, s!"this borrow block's body uses `{y}`, which is outside " ++
                        s!"it, and performs the operation {o.n}.{o.i}, which resumes: a borrow held " ++
                        "across a resumption sees only its view (R1, SPEC §29)"⟩
                    return M'
                  | none => pure ()
              throw ⟨V.span, s!"this borrow block's body performs the operation {o.n}.{o.i}, which " ++
                "resumes: only an abortive operation crosses a borrow's scope (a continuation " ++
                "held across a lend is T1, #172)"⟩
            let saved := (← get).cbRow
            modify fun st => { st with cbRow := some r }
            let V' ← surfV n c none V
            modify fun st => { st with cbRow := saved }
            match unwindingC? sp V' with
            | some M' => return M'
            | none => throw ⟨V.span, "this borrow block's body performs an abortive operation, and " ++
                "its place (a buffer or a literal) has no unwinding form here: not provided"⟩
      let V' ← surfV n c (match exp.bind rowRes? with | some (_, A) => some A | _ => none) V
      let c' ← refresh c
      match effCall? c' V' with
      | some (f, W) =>
        -- An argument with a block written in place is bound at the parameter's type, which gives
        -- the block its row (SPEC §30).
        let P ← if !hasBlockLit W then pure none else
          match (calleeHead f).bind (fun g => c'.tyV (.var .none g)) |>.bind fnParamOf with
          | some P => do pure (some (← (c'.surface sp P : Except Error VTy)))
          | none => pure none
        pure (effCallC sp f W P)
      | none => pure (.ret sp V')
    | .absurd sp V => do pure (.absurd sp (← surfV n c (some .zero) V))
    | .bind sp x A M N lin => do
      -- The answer type of a handler site whose clauses run after it, by its name.
      let A ← match A with
        | some T => do pure (some (T.subst (← get).siteRes))
        | none => pure none
      -- What follows a loop (`restScope`): outside the loop, so the loop's exit is not its.
      if x.name == restScope then
        let saved := (← get).exits
        modify fun s => { s with exits := s.exits.drop 1 }
        let N' ← surfC n c exp N
        modify fun s => { s with exits := saved }
        return N'
      -- A borrow block over a loop, or a `let r = &x`: lent per observation (`LoopLend`).
      if let some L ← (Frontend.Elab.LoopLend.hook c (dataFor (← get).sizedFns) sp x A M N lin :
          Except Error (Option Comp)) then
        return (← surfC n c exp L)
      let M' ← match M with
        | .ret rsp V => match hndCtl? V with
          | some (i, P, R, cls, B) => hndCtlC n c rsp i P R cls B
          | none => surfC n c ((A.bind c.elabV).map .ret) M
        | _ => surfC n c ((A.bind c.elabV).map .ret) M
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
      let V' ← match V with
        | .app _ (.sugar _ .count) _ | .lend .. | .app _ (.sugar _ (.forSite _)) _ => pure V
        | _ => surfV n c none V
      let c ← refresh c
      -- Over a call of a function that performs an iteration effect: a handler site (SPEC §15).
      if let .app _ (.sugar _ (.forSite i)) call := V then return ← forYield n c exp sp x i call M N
      -- Over data: a counted loop, total (SPEC §16).
      if let some L ← forData n c exp sp x V V' M N then return L
      -- Otherwise a drain of a generator or an iterator, div (SPEC §14, §15).
      let T := c.tyV V'.takeLends.1
      if let .app _ (.sugar _ .while_) _ := V then pure () else if (← get).quiet then pure () else
        report sp (s!"`for` is div: its source{(T.map fun T => s!", of type `{ppT T}`,").getD ""} " ++
          "is unbounded (a drain)")
      let el := T.bind elemOf
      modify fun s => { s with exits := .drain :: s.exits }
      let M' ← surfC n (c.push x.name el) none M
      modify fun s => { s with exits := s.exits.drop 1 }
      -- A source that never ends (it finishes with `0`): what follows runs only after `break`.
      if (T.bind finOf) == some .zero && M.spineBreaks.isEmpty then
        let N₀ := match N.forElse?, N.forRes? with
          | some (_, _, _, N₀), _ => N₀
          | none, some (_, _, N₀) => N₀
          | none, none => N
        if N₀ != .ret N₀.span (.unit N₀.span) && !(← get).quiet then
          report N₀.span ("unreachable: the loop before this never ends (its source never ends, " ++
            "and its body does not `break`)")
      -- `let r = for …; N`: `r` has the type the iterator finishes with, or, with `else { d }`,
      -- the `else` value's.
      match N.forElse?, N.forRes? with
      | some (r, A, d, N₀), _ =>
        let d' ← surfC n c none d
        let c' ← refresh c
        let rT := (A.bind c.elabV).orElse fun _ => resultOfC (c'.tyC d')
        let N₀' ← surfC n (c.push r.name rT) exp N₀
        pure (.for_ sp x V' M' (.bind N.span r A (.ret r.span (.app r.span (.sugar r.span .forRes)
          (.thunk d.span d'))) N₀' false))
      | none, some (r, A, N₀) =>
        let rT := (A.bind c.elabV).orElse fun _ => (T.bind finOf).bind fun B =>
          -- A source that never ends: the loop's value is `break e`'s.
          if B == .zero then none else some B
        let N₀' ← surfC n (c.push r.name rT) exp N₀
        pure (.for_ sp x V' M' (.bind N.span r A (.ret r.span (.sugar r.span .forRes)) N₀' false))
      | none, none => pure (.for_ sp x V' M' (← surfC n c exp N))
    | .perform sp k i V => do
      let e := (Frontend.Check.findOp c.E sp "perform" k i).toOption.map (·.2.1.A)
      pure (.perform sp k i (← surfV n c e V))
    | .abort sp k i V => do
      let e := (Frontend.Check.findOp c.E sp "abort" k i).toOption.map (·.2.1.A)
      pure (.abort sp k i (← surfV n c e V))
    | .handle sp k hr hc M => do
      let ty (x : Ident) : Option CVTy := (Frontend.Check.lookupVar x.name c.E.vars).bind (c.T[·]?)
      let e : Option CCTy := do
        let ⟨S, A, R, _⟩ ← Frontend.Check.retRead (← ty hr)
        let ⟨Es, _⟩ ← Frontend.Check.clausesRead S R (← ty hc)
        pure (Frontend.Check.effOf
          (BoCa.Fig16.LogRel.Core.Row.ofEff (UInt32.ofNat k) Es 0 ++ S) A)
      pure (.handle sp k hr hc (← surfC n c e M))
    | .unwind sp x A M D N => do
      let M' ← surfC n c ((A.bind c.elabV).map (Frontend.Check.effOf (c.E.row.getD []))) M
      let c ← refresh c
      let hd := (c.tyC M').bind Frontend.Check.effRow?
      let S := c.E.row <|> hd.map (·.1)
      let c := { c with E := { c.E with row := S } }
      let D' ← surfC n c.pushDead
        (S.map fun _ => Frontend.Check.effOf [] .unit) D
      let N' ← surfC n (c.push x.name ((A.bind c.elabV) <|> hd.map (·.2))) exp N
      pure (.unwind sp x A M' D' N')
    | M => pure M

/-- A handler site of a control effect (SPEC §19): its arguments bound, its body elaborated
with the site's operations innermost in the row, the handler's type parameters matched against
its arguments' types and the body's, and its clauses as `!` closures at the types `[handle]`
gives them; then `handle_with[n](hr, hc) M`. -/
def hndCtlC : Nat → TCx → Span → HInfo → Val → Val → Val → Comp → DM Comp
  | 0, _, sp, _, _, _, _, _ => throw ⟨sp, "internal error: a handler nested too deeply"⟩
  | n + 1, c, sp, i, P, R, cls, M => do
    let S := c.E.row.getD []
    let mismatch (what : String) : Error :=
      ⟨sp, s!"the handler `{i.name}`: {what} does not have the type its declaration gives it"⟩
    let mut σ : TySubst := i.known
    -- The body, with the site's operations innermost; its type determines the return clause's.
    let ops ← i.ents.mapM fun (q, A, B) => do
      pure (coreQual q, ← need sp "an operation's type" (c.elabV A),
        ← need sp "an operation's type" (c.elabV B))
    let rowB := BoCa.Fig16.LogRel.Core.Row.ofEff (UInt32.ofNat i.n) ops 0 ++ S
    let cB : TCx := { c with E := { c.E with row := some rowB } }
    let M' ← surfC n cB none M
    let CM ← need M.span s!"the type of the body `{i.name}` handles" ((← refresh cB).tyC M')
    let (_, A) ← need M.span s!"the type of the body `{i.name}` handles" (rowRes? CM)
    let As ← (c.surface sp A : Except Error VTy)
    match Elab.Effects.matchTyBy (sameTy c) i.tps σ i.retA As with
    | some σ' => σ := σ'
    | none => throw (mismatch "the body it handles")
    -- The arguments, bound to the parameters' names.
    let mut cP := c
    let mut binds : List (Ident × VTy × Val) := []
    for ((x, Pt), a) in i.params.zip (tupleArgs i.params.length P) do
      let Pt' := Pt.subst σ
      let exp := if Elab.Effects.mentions i.tps Pt' then none else cP.elabV Pt'
      let a' ← surfV n cP exp a
      let T ← need a.span s!"the argument `{x}` of `{i.name}`"
        (exp.orElse fun _ => cP.tyV a' |>.orElse fun _ => none)
      let Ts ← (cP.surface sp T : Except Error VTy)
      match Elab.Effects.matchTyBy (sameTy cP) i.tps σ Pt' Ts with
      | some σ' => σ := σ'
      | none => throw (mismatch s!"the argument `{x}`")
      binds := binds ++ [(⟨x, sp⟩, Ts, a')]
      cP := cP.push x (some T)
    if let some x := i.tps.find? (fun x => (σ.lookup x).isNone) then
      throw ⟨sp, s!"the type parameter `{x}` of `{i.name}` is not determined here: write it, " ++
        s!"`with {i.name}[…]`"⟩
    let Rc ← need sp s!"the answer type of `{i.name}`" (cP.elabV (i.res.subst σ))
    let cS : TCx := { cP with E := { cP.E with row := some S } }
    let ans : CCTy := BoCa.Fig16.LogRel.Core.CTy.effOf S Rc
    -- The clauses run after the site: its handler's answer type, by name (`HInfo.after`).
    if let some Ra := i.after then
      let Rs ← (cP.surface sp (← need sp s!"the answer type of `{i.name}`" (cP.elabV (Ra.subst σ))) :
        Except Error VTy)
      modify fun st => { st with siteRes := (s!"fx_res{i.n}", Rs) :: st.siteRes }
    -- The return clause.
    let hr ← match R with
      | .thunkv _ (.lam lsp x _ body) => do
        let body' ← surfC n (cS.push x.name (some A)) (some ans) (body.subst σ)
        pure (Val.bangThunkv sp (.lam lsp x As body'))
      | _ => throw ⟨sp, "internal error: a handler's return clause"⟩
    -- The operation clauses, each at its type.
    let mut hcs : List Val := []
    for (cl, (q, Ai, Bi)) in (clauseList cls).zip ops do
      match cl with
      | .thunkv csp (.lam lsp x _ body) =>
        let K := BoCa.Fig16.LogRel.Core.kTy S Rc q Bi
        let T : CVTy := if Bi.isZero && q != .lin then Ai
          else .tensor Ai (if i.boxK then .box .top K else K)
        let body' ← surfC n (cS.push x.name (some T)) (some ans) (body.subst σ)
        hcs := hcs ++ [.bangThunkv csp (.lam lsp x (← (cP.surface lsp T : Except Error VTy)) body')]
      | _ => throw ⟨sp, "internal error: a handler's clause"⟩
    let hcV := hcs.foldr (fun v t => Val.pair sp v t) (.unit sp)
    let hrTy ← (cP.surface sp (BoCa.Fig16.LogRel.Core.retTy S A Rc) : Except Error VTy)
    let hcTy ← (cP.surface sp (if i.boxK then BoCa.Fig16.LogRel.Core.clausesTyB S Rc .top ops
      else BoCa.Fig16.LogRel.Core.clausesTy S Rc ops) : Except Error VTy)
    let hrN : Ident := ⟨s!"io_hr{i.n}", sp⟩
    let hcN : Ident := ⟨s!"io_hc{i.n}", sp⟩
    -- A site whose clauses run after it answers its arguments beside its own answer.
    let hd : Comp := .handle sp i.n hrN hcN M'
    let hd ← if i.after.isNone then pure hd else do
      let r : Ident := ⟨s!"io_ar{i.n}", sp⟩
      pure (.bind sp r none hd (.ret sp (binds.foldr (fun (x, _, _) t => Val.pair sp (.var sp x.name) t)
        (.var sp r.name))) false)
    let core : Comp := .bind sp hrN (some hrTy) (.ret sp hr)
      (.bind sp hcN (some hcTy) (.ret sp hcV) hd false) false
    pure (binds.foldr (fun (x, T, a) K => Comp.bind sp x (some T) (.ret sp a) K false) core)

/-- `for x in V' { M }; N` over a sized source (`dataSrcOf`), `V'` elaborated: a counted loop,
`count_try` over the length of the source's data (the section *The total `for` over data*);
`none` when the source is not sized. `V` is the source as written. A body that performs an
operation that resumes is a div loop at a site observed one turn at a time (`forDataDiv`), and a
loop at the row otherwise: `bounded_fix` whose budget is the count, its step the body at the row
(`rowLoop`).  `[spec §16, §30]` -/
def forData : Nat → TCx → Option CCTy → Span → Ident → Val → Val → Comp → Comp → DM (Option Comp)
  | 0, _, _, _, _, _, _, _, _ => pure none
  | n + 1, c, exp, sp, x, V, V', M, N => do
    let some src := dataSrcOf c V' | return none
    let st ← get
    let sfx := s!"{sp.start.line}_{sp.start.col}"
    let M ← (normExits divFuel M : Except Error Comp)
    let pp (T : CVTy) : DM String := do pure (← (c.surface sp T : Except Error VTy)).pp
    -- A body whose row has an operation that resumes (SPEC §16, *Effectful bodies*): of a site
    -- that observes its computation one turn at a time (a `for`'s site or a stored generator's),
    -- the loop is a div loop, one turn per observation; of any other site, the loop is total at
    -- the row, `bounded_fix` over the count (`rowLoop`).
    let S₀ := c.E.row.getD []
    let resumes := (opsC c divFuel M).filter fun (k, i) =>
      S₀.any fun o => o.n.toNat == k && o.i.toNat == i && !o.abort
    if let some (k, i) := resumes.find? (st.perTurn.contains ·.1) then
      return some (← forDataDiv n c exp sp x V src M N k i)
    let rowLoop := !resumes.isEmpty
    if rowLoop then
      match src with
      | .lend a m _ => throw ⟨sp, s!"the body of this `for` performs an operation that resumes, " ++
          s!"and its source `&{if m then "mut " else ""}{a.name}` lends `{a.name}` around the whole " ++
          "loop: an operation that resumes cannot cross a borrow (T1, #172). Iterate a view the " ++
          "function is given"⟩
      | .owned _ => throw ⟨sp, "the body of this `for` performs an operation that resumes, and a " ++
          "`for` over an owned array lends it around the whole loop: an operation that resumes " ++
          "cannot cross a borrow (T1, #172). Iterate a view the function is given"⟩
      | _ => pure ()
    -- The loop's value: `let r = for …` with or without `else { d }`, or `for … else { d }`.
    let (keep, els, N) : Option (Ident × Option VTy) × Option Comp × Comp :=
      match N.forElse?, N.forRes? with
      | some (r, A, d, N₀), _ => (some (r, A), some d, N₀)
      | none, some (r, A, N₀) => (some (r, A), none, N₀)
      | none, none => (none, none, N)
    -- The type of the loop's value: the `else` value's (or the written one), else `1`.
    let breaks := M.spineBreaks
    let B ← match keep.bind (·.2), els with
      | some A, _ => need sp "the loop's value" (c.elabV A)
      | none, some d => do
        let d' ← surfC n c none d
        need d.span "the `else` value" (resultOfC ((← refresh c).tyC d'))
      | none, none => pure .unit
    for (bsp, e) in breaks do
      if e.isSome && els.isNone then
        throw ⟨bsp, "this `for`'s source can end, so its value is `break e`'s or, when the " ++
          "source ends, the `else` value: `for … { … } else { d }` (SPEC §16)"⟩
      if e.isNone && B != .unit then
        throw ⟨bsp, s!"this `for`'s value, of type `{ppT B}`, is bound: `break e` gives it"⟩
    -- A `return`: the type it returns, and where it goes after the loop.
    let hasRet := M.hasRet
    let outer := st.exits.head?
    let Rt : CVTy ← if !hasRet then pure .unit else match outer with
      | some (.total Rt _) => pure Rt
      | _ => match exp with
        | some (.ret Q) => pure Q
        | _ => throw ⟨sp, "the type of the function's result, which a `return` in this loop " ++
            "returns, is not determined here"⟩
    let retOut (rsp : Span) (v : Val) : Comp := match outer with
      | some (.total _ f) => f rsp v
      | some .drain => .ret rsp (.app rsp (.sugar rsp .retE) v)
      | none => .ret rsp v
    -- The variables the loop threads: those the body reads or assigns, locals and capabilities.
    let lent := match src with
      | .lend a .. => [a.name]
      | _ => []
    for a in lent do
      if mentionsC a M then
        throw ⟨sp, s!"`{a}` is lent to this loop, so its body does not use it: it uses the elements"⟩
    let locals ← (latest c.locals).filterMapM fun (y, T) =>
      if y == x.name || lent.contains y || !(mentionsC y M || M.rebinds y) then pure none
      else match T with
        | some T => pure (some (y, T))
        | none => throw ⟨sp, s!"the loop threads `{y}`, whose type is not determined: ascribe it"⟩
    let exts := (mExterns c).filter fun (y, T) =>
      !T.persistent && mentionsC y M && !c.locals.any (·.1 == y)
    let ws := exts ++ locals
    let wsN := ws.map (·.1)
    let Wt := tupleTySrc (← ws.mapM fun (_, T) => pp T)
    let Bt ← pp B
    let Ot ← if hasRet then do pure s!"1 + (({Bt}) + ({← pp Rt}))" else pure s!"1 + ({Bt})"
    let Et := s!"({Wt}) * ({Ot})"
    let Rts ← pp Rt
    let Jt := if hasRet then s!"(({Wt}) * (1 + ({Bt}))) + ({Rts})" else s!"({Wt}) * (1 + ({Bt}))"
    -- The source: code before the loop, the cursor it threads, the bound, the first index, and
    -- the element at a step (which binds `x` and runs the body, or goes on or ends).
    let lv := s!"'io_l{sfx}"
    let view (m : Bool) (a A : String) (src : String) (el : String) :
        String × List (String × String) × String × String :=
      let v := s!"io_v{sfx}"
      if m then
        (s!"let ({v}, io_n{sfx}) = slice_len_mut[{a}, {A}]({src});\n",
          [(v, s!"array_mut {a} ({A})")], s!"io_n{sfx}",
          s!"case slice_split_mut[{a}, {A}]({v}, 1) \{
  inl io_vp{sfx} -> let (io_vh{sfx}, {v}) = io_vp{sfx};
    case slice_get_mut[{a}, {A}](io_vh{sfx}, 0) \{ inl {x.name} -> force io_hole_body | inr io_vu{sfx} -> io_hole_cont }
| inr {v} -> io_hole_cont }")
      else
        (s!"{v} <- return {src};\nlet ({v}, io_vc{sfx}) = array_copy[{a}, {A}]({v});\n" ++
          s!"io_n{sfx} <- return array_len[{a}, {A}](io_vc{sfx});\n",
          [(v, s!"array_imm {a} ({A})")], s!"io_n{sfx}",
          s!"let ({v}, io_vg{sfx}) = array_copy[{a}, {A}]({v});
case array_get[{a}, {A}](io_vg{sfx}, io_i{sfx}) \{ inl io_ve{sfx} -> {el}force io_hole_body | inr io_vu{sfx} -> io_hole_cont }")
    let (outerPre, wrap, pre, cur, bound, i0, elem, desc) ← match src with
      | .count _ _ =>
        pure ("", none, s!"io_lo{sfx} <- return io_hole_lo;\nio_hi{sfx} <- return io_hole_hi;\n" ++
            s!"io_n{sfx} <- return (io_hi{sfx} - io_lo{sfx});\n",
          [(s!"io_lo{sfx}", "i32")], s!"io_n{sfx}", "0",
          s!"{x.name} <- return (io_lo{sfx} + io_i{sfx});\nforce io_hole_body",
          match src with
          | .count a b => s!"len({a.pp 2}..{b.pp 2})"
          | _ => s!"len({V.pp})")
      | .view m a A => do
        let a' ← c.surfaceL sp a
        let (p, cu, b, e) := view m a'.pp (← pp A) "io_hole_src" s!"{x.name} <- return io_ve{sfx};\n"
        pure ("", none, p, cu, b, "0", e, s!"len({V.pp})")
      | .lend a m A => do
        let (p, cu, b, e) := view m lv (← pp A) s!"io_lv{sfx}" s!"{x.name} <- return io_ve{sfx};\n"
        pure ("", some (s!"borrow {if m then "mut" else "imm"} {a.name} \{ {lv}, io_lv{sfx} -> ",
            a.name), p, cu, b, "0", e, s!"len({a.name})")
      | .owned A => do
        unless Class.of A == .persistent do
          throw ⟨V.span, s!"a `for` over an owned array copies each element, and `{ppT A}` is " ++
            "not persistent: iterate `&a` or `&mut a`"⟩
        let (p, cu, b, e) := view false lv (← pp A) s!"io_lv{sfx}" s!"{x.name} <- return *io_ve{sfx};\n"
        pure (s!"io_oa{sfx} <- return io_hole_src;\n", some (s!"borrow imm io_oa{sfx} \{ {lv}, io_lv{sfx} -> ",
            s!"io_oa{sfx}"), p, cu, b, "0", e, s!"len({V.pp})")
      | .sized D S A => do
        let stepT ← pp (.bang (.thunk (.arr (.tensor D S)
          (.ret (.tensor (.tensor D S) (.sum A (.sum .unit .unit)))))))
        let (bs, bn) ← (boundSrc c sp 64 s!"io_sd{sfx}" D : Except Error _)
        pure ("", none, s!"let (io_sd{sfx}, io_st{sfx}) = io_hole_src;\nlet (io_ss{sfx}, io_sf{sfx}) = io_st{sfx};\n{bs}",
          [(s!"io_sd{sfx}", ← pp D), (s!"io_ss{sfx}", ← pp S), (s!"io_sf{sfx}", stepT)], bn, "0",
          s!"let (io_sp{sfx}, io_so{sfx}) = io_sf{sfx}((io_sd{sfx}, io_ss{sfx}));
let (io_sd{sfx}, io_ss{sfx}) = io_sp{sfx};
case io_so{sfx} \{
  inl {x.name} -> force io_hole_body
| inr io_sq{sfx} -> case io_sq{sfx} \{ inl io_su{sfx} -> io_hole_cont | inr io_su{sfx} -> return (inr ({tupleSrc wsN}, inl ())) } }",
          s!"len of the data of {V.pp}")
    let curN := cur.map (·.1)
    let St := tupleTySrc (cur.map (·.2) ++ (← ws.mapM fun (_, T) => pp T))
    let stateS := tupleSrc (curN ++ wsN)
    let elem := elem.replace "io_hole_cont" s!"return (inl {stateS})"
    let jEnded := if hasRet then s!"inl ({tupleSrc wsN}, inl ())" else s!"({tupleSrc wsN}, inl ())"
    let jExit := if hasRet then
        s!"case io_o{sfx} \{ inl io_q{sfx} -> return (inl ({tupleSrc wsN}, inl io_q{sfx}))
    | inr io_b{sfx} -> case io_b{sfx} \{ inl io_bv{sfx} -> return (inl ({tupleSrc wsN}, inr io_bv{sfx}))
      | inr io_rv{sfx} -> return (inr io_rv{sfx}) } }"
      else s!"return ({tupleSrc wsN}, io_o{sfx})"
    -- An abortive operation in the body (SPEC §19): `count_try`'s step is pure, so the step
    -- handles the operations of their site itself, each leaving the loop by its exit, and after
    -- the loop the operation is performed again.
    let S := c.E.row.getD []
    let used := (opsC c divFuel M).eraseDups.filter fun (k, _) => S.any (·.n.toNat == k)
    -- A loop at the row performs its operations where they stand.
    let names := if rowLoop then [] else (used.map (·.1)).eraseDups
    let (stepT, wrapStep, reabort) ← match names with
      | [] => pure (Et, fun (e : String) => e, "")
      | [k] => do
        let ops := S.filter (·.n.toNat == k)
        if let some o := ops.find? (fun o => !o.abort) then
          throw ⟨sp, s!"the body of this `for` performs a control operation that resumes " ++
            s!"(the operation {o.n}.{o.i}): the loop is a counted loop, whose step is pure " ++
            "(SPEC §16), and only an abortive operation may leave it"⟩
        let As ← ops.mapM fun o => pp o.A
        let P := " + ".intercalate (As.map fun a => s!"({a})")
        let m := As.length
        let inj (j : Nat) (v : String) : String :=
          (List.range j).foldr (fun _ t => s!"inr ({t})") (if j + 1 == m then v else s!"inl ({v})")
        let Et' := s!"({Et}) + ({P})"
        let T := s!"({St}) + ({Et})"
        let R := s!"({St}) + ({Et'})"
        let cls := (As.zipIdx.map fun (a, j) =>
          s!"!thunkv fun (io_ae{sfx} : {a}) -> return (inr (inr ({inj j s!"io_ae{sfx}"})))")
        let clsV := cls.foldr (fun c t => s!"({c}, {t})") "()"
        let clsT := (As.map fun a => s!"!(({a}) => {R})").foldr (fun c t => s!"({c}) * ({t})") "1"
        let wrap (e : String) : String :=
          s!"io_ahr{sfx} : !({T} => {R}) <- return (!thunkv fun (io_av{sfx} : {T}) ->
    case io_av{sfx} \{ inl io_ax{sfx} -> return (inl io_ax{sfx}) | inr io_ax{sfx} -> return (inr (inl io_ax{sfx})) });
  io_ahc{sfx} : {clsT} <- return {clsV};
  handle_with[{k}](io_ahr{sfx}, io_ahc{sfx}) ({e})"
        let rec reab : List (Nat × String) → String → String
          | [], _ => "absurd ()"
          | [(i, _)], v => s!"abort[{k}.{i}] {v}"
          | (i, _) :: rest, v =>
            s!"case {v} \{ inl io_aq{i}{sfx} -> abort[{k}.{i}] io_aq{i}{sfx} | inr io_ar{i}{sfx} -> {reab rest s!"io_ar{i}{sfx}"} }"
        let re := reab ((ops.map (·.i.toNat)).zip As) s!"io_ap{sfx}"
        if !(← get).quiet then
          report sp s!"an abortive operation in its body leaves the loop by its exit, handled at the step and performed again after it"
        pure (Et', wrap, s!"io_r{sfx} : ({St}) + ({Et}) <- case io_rr{sfx} \{
    inl io_aq{sfx} -> return (inl io_aq{sfx})
  | inr io_aq{sfx} -> case io_aq{sfx} \{ inl io_ae{sfx} -> return (inr io_ae{sfx}) | inr io_ap{sfx} -> {re} } };
")
      | _ => throw ⟨sp, "the body of this `for` performs abortive operations of two handlers: not provided"⟩
    let rname := if reabort.isEmpty then s!"io_r{sfx}" else s!"io_rr{sfx}"
    -- The loop at the row: `bounded_fix` whose budget is the count, so that the self-reference is
    -- `inl ()` once the body has run at each index; its step runs the body at the row and goes on
    -- with the self-reference, or leaves by an exit.
    let FR ← do
      let es ← S.mapM fun o => do
        pure s!"{o.n}.{o.i} {Frontend.Check.qualStr o.q} {← pp o.A} ~> {← pp o.B}"
      pure s!"F[{", ".intercalate es}] (({St}) + ({stepT}))"
    let At := s!"i32 * ({St})"
    let rowCore := s!"{pre}io_nb{sfx} <- if {bound} < 0 \{ 0 } else \{ {bound} };
io_gs{sfx} : !U (((1 + !U (({At}) -o {FR})) * ({At})) -o {FR}) <- return (!thunkv fun (io_gp{sfx} : (1 + !U (({At}) -o {FR})) * ({At})) ->
  let (io_self{sfx}, io_ga{sfx}) = io_gp{sfx};
  let (io_i{sfx}, io_s{sfx}) = io_ga{sfx};
  case io_self{sfx} \{
    inl io_z{sfx} -> return (inl io_s{sfx})
  | inr io_me{sfx} ->
      io_o{sfx} : ({St}) + ({stepT}) <- ({destructSrc s!"io_s{sfx}" (curN ++ wsN)}{elem});
      case io_o{sfx} \{
        inl io_s2{sfx} -> io_g{sfx} <- return (unbang io_me{sfx});
          io_a2{sfx} <- return (io_i{sfx} + 1, io_s2{sfx});
          force io_g{sfx} io_a2{sfx}
      | inr io_e{sfx} -> return (inr io_e{sfx})
      }
  });
io_fb{sfx} <- return (unbang bounded_fix[{At}, {FR}]);
io_fa{sfx} <- return (io_gs{sfx}, (io_nb{sfx}, ({i0}, {stateS})));
{rname} <- force io_fb{sfx} io_fa{sfx};
"
    let core := (if rowLoop then rowCore else
      s!"{pre}{rname} <- return count_try[{St}, {stepT}](!\{ (io_i{sfx}, io_s{sfx}) ->
  {destructSrc s!"io_s{sfx}" (curN ++ wsN)}{wrapStep elem} }, {bound}, {i0}, {stateS});
") ++ s!"{reabort}io_j{sfx} : {Jt} <- case io_r{sfx} \{
    inl io_s{sfx} -> {destructSrc s!"io_s{sfx}" (curN ++ wsN)}return ({jEnded})
  | inr io_e{sfx} -> let (io_w{sfx}, io_o{sfx}) = io_e{sfx};
      {destructSrc s!"io_w{sfx}" wsN}{jExit}
  };
"
    -- Around a borrow block (a lent array), the loop's result is the block's: the body binds
    -- `io_bt`, so the parser does not add the variables it hands back (`Parser.borrowBlock`),
    -- and the loop's threaded variables, capabilities included, come out in its result.
    let outN := wsN
    let reshape := s!"io_bt <- return io_j{sfx};\nreturn io_bt"
    let loopSrc := match wrap with
      | some (open_, back) => s!"{outerPre}io_bl{sfx} <- return ({open_}{core}{reshape} });
let ({back}, io_j{sfx}) = io_bl{sfx};
"
      | none => core
    -- After the loop: the threaded variables rebound, then the value, then what follows.
    let r := match keep with
      | some (r, _) => some r.name
      | none => if els.isSome then some s!"io_fv{sfx}" else none
    let value := match r with
      | some r => s!"{r} : {Bt} <- case io_ob{sfx} \{ inl io_q{sfx} -> {if els.isSome then "force io_hole_else" else "return ()"} | inr io_bv{sfx} -> return io_bv{sfx} };\n"
      | none => ""
    let after := if hasRet then
        s!"case io_j{sfx} \{
  inl io_jv{sfx} -> let (io_jw{sfx}, io_ob{sfx}) = io_jv{sfx};
    {destructSrc s!"io_jw{sfx}" outN}{value}force io_hole_rest
| inr io_rv{sfx} -> force io_hole_ret }"
      else s!"let (io_jw{sfx}, io_ob{sfx}) = io_j{sfx};\n{destructSrc s!"io_jw{sfx}" outN}{value}force io_hole_rest"
    let what := "a `for` over data (a counted loop)"
    let L ← (template sp what (loopSrc ++ after) : SM Comp)
    -- The body: its terminals go on, and its exits leave with the threaded variables.
    let st (tsp : Span) : Val := tupleVal tsp (curN ++ wsN)
    let exitV (tsp : Span) (o : Val) : Val := .inr tsp (.pair tsp (tupleVal tsp wsN) o)
    let brk (tsp : Span) (e : Val) : Val := if hasRet then .inr tsp (.inl tsp e) else .inr tsp e
    let body := wrapTail (fun
      | .ret tsp (.sugar _ .brk) => .ret tsp (exitV tsp (brk tsp (.unit tsp)))
      | .ret tsp (.app _ (.sugar _ .brk) e) => .ret tsp (exitV tsp (brk tsp e))
      | .ret tsp (.sugar _ .cont) => .ret tsp (.inl tsp (st tsp))
      | .ret tsp (.app _ (.sugar _ .retE) v) => .ret tsp (exitV tsp (.inr tsp (.inr tsp v)))
      | T => .bind T.span ⟨"io_u", T.span⟩ none T (.ret T.span (.inl T.span (st T.span))) false) M
    let (lo, hi) := match src with
      | .count a b => (some a, some b)
      | _ => (none, none)
    let hv (h : String) : Option Val :=
      if h == "io_hole_src" then some V else if h == "io_hole_lo" then lo
      else if h == "io_hole_hi" then hi else none
    let rsp := sp
    let hc (h : String) : Option Comp :=
      if h == "io_hole_body" then some body else if h == "io_hole_rest" then some (restOf N)
      else if h == "io_hole_else" then els.map restOf
      else if h == "io_hole_ret" then some (retOut rsp (.var rsp s!"io_rv{sfx}")) else none
    let L := L.fill hv hc
    if !(← get).quiet then
      if rowLoop then
        report sp (s!"`for` is total, bounded by {desc}: its body performs an operation that " ++
          "resumes, so it is a loop at the row (bounded_fix over the count)")
      else report sp s!"`for` is total, bounded by {desc}"
    -- The loops inside the body leave by this loop's exit on `return`.
    let ret (tsp : Span) (v : Val) : Comp := .ret tsp (exitV tsp (.inr tsp (.inr tsp v)))
    modify fun s => { s with exits := .total Rt ret :: s.exits }
    let L' ← surfC n c exp L
    modify fun s => { s with exits := s.exits.drop 1 }
    return some L'

/-- `for x in V { M }; N` over data whose body performs an operation that resumes (the operation
`k.i`): a div loop (SPEC §16). A counted loop's step is one total computation and cannot hold the
continuation of such an operation, so the loop is a `while` over the source's cursor, a loop of
the body's machine (SPEC §14, §15), one turn per element: a count's index, a view's index or rest,
an owned array's index (each element copied out under a borrow of one turn), a sized iterator's
data and state. `&a` and `&mut a` lend `a` around the whole loop, and an operation that resumes
cannot cross a borrow (T1, #172): they are rejected. The loop has no value (`else`, `break e`). -/
def forDataDiv : Nat → TCx → Option CCTy → Span → Ident → Val → DataSrc → Comp → Comp → Nat → Nat →
    DM Comp
  | 0, _, _, sp, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: a loop nested too deeply"⟩
  | n + 1, c, exp, sp, x, V, src, M, N, k, i => do
    let sfx := s!"{sp.start.line}_{sp.start.col}"
    let pp (T : CVTy) : DM String := do pure (← (c.surface sp T : Except Error VTy)).pp
    if N.forElse?.isSome || N.forRes?.isSome || M.spineBreaks.any (·.2.isSome) then
      throw ⟨sp, s!"the body of this `for` performs an operation that resumes (the operation " ++
        s!"{k}.{i}), so the loop is div (a `while` over its source), and it has no value: " ++
        "`break e` and `else` are not provided there"⟩
    let x' := x.name
    let w := s!"io_w{sfx}"
    let src ← match src with
      | .count _ _ => pure s!"{w}l <- return io_hole_lo;
{w}h <- return io_hole_hi;
while ({w}l < {w}h) \{
  {x'} <- return {w}l;
  {w}l <- return ({w}l + 1);
  force io_hole_body
};
force io_hole_rest"
      | .view false a A => do
        let a ← (c.surfaceL sp a : Except Error Frontend.Life)
        let At ← pp A
        pure s!"{w}v <- return io_hole_src;
let ({w}v, {w}c) = array_copy[{a.pp}, {At}]({w}v);
{w}n <- return array_len[{a.pp}, {At}]({w}c);
{w}i <- return 0;
while ({w}i < {w}n) \{
  let ({w}v, {w}g) = array_copy[{a.pp}, {At}]({w}v);
  {w}k <- return {w}i;
  {w}i <- return ({w}i + 1);
  case array_get[{a.pp}, {At}]({w}g, {w}k) \{ inl {x'} -> force io_hole_body | inr {w}u -> return () }
};
force io_hole_rest"
      | .view true a A => do
        let a ← (c.surfaceL sp a : Except Error Frontend.Life)
        let At ← pp A
        pure s!"{w}v <- return io_hole_src;
{w}m <- return (inr () : 1 + 1);
while ({w}m) \{
  case slice_split_mut[{a.pp}, {At}]({w}v, 1) \{
    inl {w}p -> let ({w}h, {w}v) = {w}p;
      case slice_get_mut[{a.pp}, {At}]({w}h, 0) \{ inl {x'} -> force io_hole_body | inr {w}u -> return () }
  | inr {w}v -> {w}m <- return (inl () : 1 + 1); return ()
  }
};
force io_hole_rest"
      | .owned A => do
        unless Class.of A == .persistent do
          throw ⟨V.span, s!"a `for` over an owned array copies each element, and `{ppT A}` is " ++
            "not persistent: iterate a view of it"⟩
        let At ← pp A
        pure s!"{w}a <- return io_hole_src;
let ({w}a, {w}n) = array_size[{At}]({w}a);
{w}i <- return 0;
while ({w}i < {w}n) \{
  {w}k <- return {w}i;
  {w}i <- return ({w}i + 1);
  {w}b <- return borrow imm {w}a \{ 'io_wl, {w}lv -> case array_get['io_wl, {At}]({w}lv, {w}k) \{
      inl {w}e -> return (inl *{w}e : {At} + 1) | inr {w}u -> return (inr () : {At} + 1) } };
  let ({w}a, {w}r) = {w}b;
  case {w}r \{ inl {x'} -> force io_hole_body | inr {w}u -> return () }
};
force io_hole_rest"
      | .sized _ _ _ => pure s!"let ({w}d, {w}t) = io_hole_src;
let ({w}s, {w}f) = {w}t;
{w}m <- return (inr () : 1 + 1);
while ({w}m) \{
  let ({w}p, {w}o) = {w}f(({w}d, {w}s));
  let ({w}d, {w}s) = {w}p;
  case {w}o \{
    inl {x'} -> force io_hole_body
  | inr {w}q -> case {w}q \{ inl {w}u -> return () | inr {w}u -> {w}m <- return (inl () : 1 + 1); return () }
  }
};
force io_hole_rest"
      | .lend a m _ => throw ⟨sp, s!"the body of this `for` performs an operation that resumes " ++
          s!"(the operation {k}.{i}), and its source `&{if m then "mut " else ""}{a.name}` lends " ++
          s!"`{a.name}` around the whole loop: an operation that resumes cannot cross a borrow " ++
          "(T1, #172). Iterate an owned array, or a view the function is given"⟩
    let (lo, hi) := match V with
      | .app _ (.sugar _ .count) (.pair _ a b) => (some a, some b)
      | _ => (none, none)
    let hv (h : String) : Option Val :=
      if h == "io_hole_src" then some V else if h == "io_hole_lo" then lo
      else if h == "io_hole_hi" then hi else none
    let hc (h : String) : Option Comp :=
      if h == "io_hole_body" then some M else if h == "io_hole_rest" then some N else none
    let L ← (template sp "a `for` over data whose body performs an operation that resumes (a div loop)"
      src : SM Comp)
    if !(← get).quiet then
      report sp s!"`for` is div: its body performs an operation that resumes ({k}.{i}), so it is a loop over the source's cursor"
    surfC n c exp (L.fill hv hc)

/-- `for x in g(e) { M }; N`, `g` performing an iteration effect (SPEC §15): the handler site
`Frontend.Elab.Effects` left (`VSugar.forSite`), assembled. The variables the body reads or
assigns, `ws`, are threaded through the operation: the copy of `g` for the site takes their tuple
first and hands it back first, and its operation `op(v)` is `w <- perform[n.0] (v, w)`. The body is the
operation's clause, at the row around the `for`: it binds `x` and `ws`, and resumes with them at
its end and at `continue`; `break` and `return` cancel the continuation, which runs what the
generator must finalise, and leave with them. When `g`'s body does not loop, the `for` is one
handled call, total. When it loops, `g`'s call is its loop, whose observations perform the
operation; the `for` is a call of a div function in direct style, of the loop that handles each
observation of `g`'s (`io_hw`), whose closing closes `g`'s loop. -/
def forYield : Nat → TCx → Option CCTy → Span → Ident → ItInfo → Val → Comp → Comp → DM Comp
  | 0, _, _, sp, _, _, _, _, _ => throw ⟨sp, "internal error: a `for` nested too deeply"⟩
  | n + 1, c, exp, sp, x, i, call, M, N => do
    let sfx := s!"{sp.start.line}_{sp.start.col}"
    let st ← get
    let M ← (normExits divFuel M : Except Error Comp)
    let pp (T : CVTy) : DM String := do pure (← (c.surface sp T : Except Error VTy)).pp
    let S := c.E.row.getD []
    let F (A : String) : DM String := do
      if S.isEmpty then return s!"F ({A})"
      let es ← S.mapM fun o => do
        pure s!"{o.n}.{o.i} {Frontend.Check.qualStr o.q} {← pp o.A} ~> {← pp o.B}"
      pure s!"F[{", ".intercalate es}] ({A})"
    -- The loop's value: `let r = for …`. A generator's loop ends when the generator returns.
    let (keep, N) := match N.forElse?, N.forRes? with
      | some (r, A, _, N₀), _ => (some (r, A), N₀)
      | none, some (r, A, N₀) => (some (r, A), N₀)
      | none, none => (none, N)
    if let some (_, _, d, _) := N.forElse? then
      throw ⟨d.span, "a `for` over a generator ends when the generator returns, with its result: " ++
        "it has no `else`"⟩
    -- A `return`: the type it returns, and where it goes after the loop.
    let hasRet := M.hasRet
    let outer := st.exits.head?
    let Rt : CVTy ← if !hasRet then pure .unit else match outer with
      | some (.total Rt _) => pure Rt
      | _ => match exp.bind rowRes? with
        | some (_, Q) => pure Q
        | none => throw ⟨sp, "the type of the function's result, which a `return` in this loop " ++
            "returns, is not determined here"⟩
    let retOut (rsp : Span) (v : Val) : Comp := match outer with
      | some (.total _ f) => f rsp v
      | some .drain => .ret rsp (.app rsp (.sugar rsp .retE) v)
      | none => .ret rsp v
    -- The variables the loop threads: those the body reads or assigns, locals and capabilities.
    let locals ← (latest c.locals).filterMapM fun (y, T) =>
      if y == x.name || !(mentionsC y M || M.rebinds y) then pure none
      else match T with
        | some T => pure (some (y, T))
        | none => throw ⟨sp, s!"the loop threads `{y}`, whose type is not determined: ascribe it"⟩
    let exts := (mExterns c).filter fun (y, T) =>
      !T.persistent && mentionsC y M && !c.locals.any (·.1 == y)
    let ws := exts ++ locals
    let wsN := ws.map (·.1)
    if let some (y, _) := ws.find? (fun (y, _) => mentionsV y call) then
      throw ⟨sp, s!"`{y}` is given to `{i.callee}` and used in the body of the `for` over it: " ++
        "a generator and its loop's body do not share a variable"⟩
    let Wc := tupleT (ws.map (·.2))
    let Wt ← pp Wc
    -- The call, with the threaded tuple: its instance, and whether its body loops.
    let cw := c.push i.w (some Wc)
    let call' ← surfV n cw none call
    let cw ← refresh cw
    let some g := (match call' with | .app _ f _ => calleeHead f | _ => none)
      | throw ⟨sp, "internal error: the call of a `for` over a generator"⟩
    let some Gt := cw.tyV (.var .none g)
      | throw ⟨sp, s!"the type of `{i.callee}` is not determined here"⟩
    let some (S0, Res) := resultRowOf (some Gt)
      | throw ⟨sp, s!"`{i.callee}`'s type is not a function's"⟩
    let (looping, Bw, rowG) := match loopRowOf Res with
      | some (S', B, _) => (true, B, S')
      | none => (false, Res, S0)
    -- What it yields: the operation's argument at the site, beside the threaded tuple.
    let some Tc := (rowG.find? (·.n.toNat == i.n)).bind fun o => match o.A with
        | .tensor T _ => some T
        | _ => none
      | throw ⟨sp, s!"the type of what `{i.callee}` yields is not determined here"⟩
    let Bg ← match Bw with
      | .tensor _ B => pure B
      | _ => throw ⟨sp, "internal error: a generator's copy for a `for` hands its variables back"⟩
    -- The body of a counted loop, or of a `for` over a generator, is one total step.
    if looping then if let some (.total ..) := st.exits.head? then
      throw ⟨sp, s!"`{i.callee}` loops, so a `for` over it is div, and it is inside the body of a " ++
        "loop that is one total step (a `for` over data, SPEC §16, or the clause of a `for` over a " ++
        "generator): store the generator and loop over it after, or loop over it in a function"⟩
    -- The loop's value: what the generator returns, or `break e`'s. A generator that never
    -- returns (`0`) gives only `break e`'s.
    let Vt : CVTy ← match keep with
      | some (_, some A) => need sp "the loop's value" (c.elabV A)
      | some (r, none) =>
        if Bg != .zero then pure Bg else
        match (M.spineBreaks.filterMap (·.2)).head? with
        | some e => match (ws.foldl (fun c (y, T) => c.push y (some T)) (c.push x.name (some Tc))).tyV e with
          | some T => pure T
          | none => throw ⟨e.span, s!"the type of this loop's value is not determined: write it, " ++
              s!"`let {r.name} : T = for …`"⟩
        | none => pure .zero
      | none => pure .unit
    checkBreaks M (keep.map fun _ => Vt)
    if keep.isNone && Class.of Bg == .linear then
      throw ⟨sp, s!"`{i.callee}` returns `{ppT Bg}`, which has no destructor: bind the loop's value, " ++
        "`let r = for …`"⟩
    if keep.isSome && Bg != Vt && Bg != .zero then
      throw ⟨sp, s!"the loop's value has type `{ppT Vt}`, and `{i.callee}` returns `{ppT Bg}`"⟩
    let Tt ← pp Tc
    let Bt ← pp Bg
    let Vs ← pp Vt
    let Rts ← pp Rt
    let Et := if hasRet then s!"({Vs}) + ({Rts})" else Vs
    let Jt := s!"(({Wt}) * ({Bt})) + (({Wt}) * ({Et}))"
    -- The answer of an observation of `g`'s loop, handled: what `g` returns or how the body left
    -- (`Jt`), or the rest of the loop.
    let Lg ← pp Res
    let Ot := if looping then s!"({Jt}) + {Lg}" else Jt
    let K ← do pure s!"U (({Wt} -o {← F Ot}) & {← F "1"})"
    let clT ← do pure s!"!U ((({Tt}) * ({Wt})) * {K} -o {← F Ot})"
    let hrIn := if looping then s!"(({Wt}) * ({Bt})) + {Lg}" else s!"({Wt}) * ({Bt})"
    let hrBody := if looping then
        s!"case io_hv{sfx} \{ inl io_ha{sfx} -> return (inl (inl io_ha{sfx})) | inr io_hl{sfx} -> return (inr io_hl{sfx}) }"
      else s!"return (inl io_hv{sfx})"
    let handler := s!"io_hr{sfx} : !U ({hrIn} -o {← F Ot}) <- return (!thunkv fun (io_hv{sfx} : {hrIn}) -> {hrBody});
io_hc{sfx} : ({clT}) * 1 <- return ((!thunkv fun (io_hp{sfx} : (({Tt}) * ({Wt})) * {K}) ->
  let (io_hxw{sfx}, io_k{sfx}) = io_hp{sfx};
  let ({x.name}, io_hw{sfx}) = io_hxw{sfx};
  {destructSrc s!"io_hw{sfx}" wsN}force io_hole_body), ());
"
    -- The body: its terminals resume, and its exits cancel the rest of `g` and leave.
    let leave (tsp : Span) (o : Val) : Comp :=
      let ex : Val := .inr tsp (.pair tsp (tupleVal tsp wsN) o)
      .bind tsp ⟨s!"io_c{sfx}", tsp⟩ none (.proj tsp false (.force tsp ⟨s!"io_k{sfx}", tsp⟩))
        (.ret tsp (if looping then .inl tsp ex else ex)) false
    let resume (tsp : Span) : Comp :=
      .bind tsp ⟨s!"io_wv{sfx}", tsp⟩ none (.ret tsp (tupleVal tsp wsN))
        (.app tsp (.proj tsp true (.force tsp ⟨s!"io_k{sfx}", tsp⟩)) ⟨s!"io_wv{sfx}", tsp⟩) false
    let brk (tsp : Span) (e : Val) : Val := if hasRet then .inl tsp e else e
    let body := wrapTail (fun
      | .ret tsp (.sugar _ .brk) => leave tsp (brk tsp (.unit tsp))
      | .ret tsp (.app _ (.sugar _ .brk) e) => leave tsp (brk tsp e)
      | .ret tsp (.sugar _ .cont) => resume tsp
      | .ret tsp (.app _ (.sugar _ .retE) v) => leave tsp (.inr tsp v)
      | T => .bind T.span ⟨"io_u", T.span⟩ none T (resume T.span) false) M
    -- The loop's value and the threaded variables after it.
    let valEnd := if keep.isSome then s!"io_jg{sfx}" else "()"
    let JJt := if hasRet then s!"(({Wt}) * ({Vs})) + ({Rts})" else s!"({Wt}) * ({Vs})"
    let inj (v : String) : String := if hasRet then s!"inl ({v})" else v
    let endRet := if Bg == .zero then s!"absurd io_jg{sfx}"
      else s!"return ({inj s!"(io_jw{sfx}, {valEnd})"})"
    let exitArm := if hasRet then
        s!"case io_jo{sfx} \{ inl io_jb{sfx} -> return (inl (io_jw{sfx}, io_jb{sfx})) | inr io_jr{sfx} -> return (inr io_jr{sfx}) }"
      else s!"return (io_jw{sfx}, io_jo{sfx})"
    let join := s!"io_jj{sfx} : {JJt} <- case io_j{sfx} \{
    inl io_ja{sfx} -> let (io_jw{sfx}, io_jg{sfx}) = io_ja{sfx}; {endRet}
  | inr io_je{sfx} -> let (io_jw{sfx}, io_jo{sfx}) = io_je{sfx}; {exitArm}
  };
"
    let r := match keep with
      | some (r, _) => s!"{r.name} : {Vs} <- return io_v{sfx};\n"
      | none => s!"let () = io_v{sfx};\n"
    let after := if hasRet then s!"case io_jj{sfx} \{
  inl io_jv{sfx} -> let (io_jx{sfx}, io_v{sfx}) = io_jv{sfx};
    {destructSrc s!"io_jx{sfx}" wsN}{r}force io_hole_rest
| inr io_rv{sfx} -> force io_hole_ret }"
      else s!"let (io_jx{sfx}, io_v{sfx}) = io_jj{sfx};\n{destructSrc s!"io_jx{sfx}" wsN}{r}force io_hole_rest"
    let bindW := s!"{i.w} : {Wt} <- return {tupleSrc wsN};\n"
    let plain := s!"{bindW}{handler}io_j{sfx} : {Jt} <- handle_with[{i.n}](io_hr{sfx}, io_hc{sfx}) (force io_hole_call);\n"
    let core ← if !looping then pure plain else do
      let some (_, _, Rg) := loopRowOf Res | throw ⟨sp, "internal error: a generator's loop"⟩
      let Rgs ← pp Rg
      let fOb ← F s!"({Jt}) + U X"
      let fCl ← F Rgs
      let Lw := if S.isEmpty then s!"loop ({Jt}) ({Rgs})" else s!"nu X. {fOb} & {fCl}"
      let Kc ← do pure s!"U (({Wt} -o {← F Rgs}) & {← F "1"})"
      let closer := s!"io_chr{sfx} : !U ({Rgs} -o {← F Rgs}) <- return (!thunkv fun (io_cv{sfx} : {Rgs}) -> return io_cv{sfx});
io_chc{sfx} : (!U ((({Tt}) * ({Wt})) * {Kc} -o {← F Rgs})) * 1 <- return ((!thunkv fun (io_cp{sfx} : (({Tt}) * ({Wt})) * {Kc}) ->
  let (io_cxw{sfx}, io_ck{sfx}) = io_cp{sfx};
  let (io_cx{sfx}, io_cw{sfx}) = io_cxw{sfx};
  (force io_ck{sfx}).1 io_cw{sfx}), ());
"
      pure s!"{bindW}io_l{sfx} : {Lg} <- force io_hole_call;
io_hwf{sfx} : !({Lg} => U ({Lw})) <- return (!thunkv fun (io_hl{sfx} : {Lg}) ->
  io_hf{sfx} <- return (unbang (unfold[{Lw}, {Lg}] (!thunkv fun (io_hs{sfx} : {Lg}) ->
    < {handler}handle_with[{i.n}](io_hr{sfx}, io_hc{sfx}) ((nu_out (force io_hs{sfx})).1),
      {closer}handle_with[{i.n}](io_chr{sfx}, io_chc{sfx}) ((nu_out (force io_hs{sfx})).2) >)));
  return (thunkv nu_in < (nu_out (force io_hf{sfx} io_hl{sfx})).1, (nu_out (force io_hf{sfx} io_hl{sfx})).2 >));
io_j{sfx} : {Jt} <- return ((unbang io_hwf{sfx}) io_l{sfx});
"
    let what := "a `for` over a generator"
    let L ← (template sp what (core ++ join ++ after) : SM Comp)
    let hc (h : String) : Option Comp :=
      if h == "io_hole_body" then some body else if h == "io_hole_rest" then some (restOf N)
      else if h == "io_hole_call" then some (.ret sp call')
      else if h == "io_hole_ret" then some (retOut sp (.var sp s!"io_rv{sfx}")) else none
    let L := L.fill (fun _ => none) hc
    if !(← get).quiet then
      report sp (if looping then s!"`for` is div: `{i.callee}` loops" else
        s!"`for` is total: `{i.callee}` does not loop")
      -- A generator that never returns (`0`): what follows runs only after `break`.
      if Bg == .zero && M.spineBreaks.isEmpty && N != .ret N.span (.unit N.span) then
        report N.span ("unreachable: the loop before this never ends (its generator never " ++
          "returns, and its body does not `break`)")
    -- The loops inside the body leave by this loop's exit on `return`.
    let ret (tsp : Span) (v : Val) : Comp := leave tsp (.inr tsp v)
    modify fun s => { s with exits := .total Rt ret :: s.exits }
    let L' ← surfC n c exp L
    modify fun s => { s with exits := s.exits.drop 1 }
    pure L'

/-- The stored generator of `g(e)`, `g` performing an iteration effect (SPEC §15): the handler
site `Frontend.Elab.Effects` left (`VSugar.pullSite`), assembled into `U (pull A B 1)`. Its clause
does not resume: it answers the element with the continuation as the rest, `nu_in < resume,
cancel >`, so the next observation resumes `g` where it yielded, and `close` cancels it. Nothing
runs until the first observation. When `g`'s body loops, the stored generator's state is `g`'s
loop, each of whose observations is handled (one that ends without performing the operation is a
skip), or the rest after the operation. -/
def pullView : Nat → TCx → Span → ItInfo → Val → DM Comp
  | 0, _, sp, _, _ => throw ⟨sp, "internal error: a stored generator nested too deeply"⟩
  | n + 1, c, sp, i, call => do
    let sfx := s!"{sp.start.line}_{sp.start.col}"
    let pp (T : CVTy) : DM String := do pure (← (c.surface sp T : Except Error VTy)).pp
    let call' ← surfV n c none call
    let c ← refresh c
    let some g := (match call' with | .app _ f _ => calleeHead f | _ => none)
      | throw ⟨sp, "internal error: the call of a stored generator"⟩
    let some Gt := c.tyV (.var .none g)
      | throw ⟨sp, s!"the type of `{i.callee}` is not determined here"⟩
    let some (S0, Res) := resultRowOf (some Gt)
      | throw ⟨sp, s!"`{i.callee}`'s type is not a function's"⟩
    let (looping, Bg, row) := match loopRowOf Res with
      | some (S, B, _) => (true, B, S)
      | none => (false, Res, S0)
    if row.any (·.n.toNat != i.n) then
      throw ⟨sp, s!"`{i.callee}` performs operations besides what it yields: its stored generator " ++
        "is not provided"⟩
    let some Tc := (row.find? (·.n.toNat == i.n)).map (·.A)
      | throw ⟨sp, s!"the type of what `{i.callee}` yields is not determined here"⟩
    let Tt ← pp Tc
    let Bt ← pp Bg
    let src ← if !looping then do
      let Q := s!"iter ({Tt}) ({Bt}) 1"
      let R := s!"(({Tt}) * U ({Q})) + ({Bt})"
      let K := s!"U ((1 -o F ({R})) & F 1)"
      pure s!"io_pq{sfx} : U ({Q}) <- return (thunkv nu_in <
    io_phr{sfx} : !({Bt} => {R}) <- return (!thunkv fun (io_pv{sfx} : {Bt}) -> return (inr io_pv{sfx}));
    io_phc{sfx} : (!(({Tt}) * {K} => {R})) * 1 <- return ((!thunkv fun (io_pp{sfx} : ({Tt}) * {K}) ->
      let (io_px{sfx}, io_pk{sfx}) = io_pp{sfx};
      return (inl (io_px{sfx}, thunkv nu_in < io_pu{sfx} <- return (); (force io_pk{sfx}).1 io_pu{sfx}, (force io_pk{sfx}).2 >))), ());
    handle_with[{i.n}](io_phr{sfx}, io_phc{sfx}) (force io_hole_call),
    return () >);
io_pf{sfx} <- return (unbang (unfold[pull ({Tt}) ({Bt}) 1, U ({Q})] (!thunkv fun (io_pa{sfx} : U ({Q})) ->
  < io_po{sfx} <- (nu_out (force io_pa{sfx})).1;
    case io_po{sfx} \{ inl io_pe{sfx} -> return (inl io_pe{sfx}) | inr io_pb{sfx} -> return (inr (inl io_pb{sfx})) },
    (nu_out (force io_pa{sfx})).2 >)));
return (thunkv nu_in < (nu_out (force io_pf{sfx} io_pq{sfx})).1, (nu_out (force io_pf{sfx} io_pq{sfx})).2 >)"
    else do
      let some (_, _, Rg) := loopRowOf Res | throw ⟨sp, "internal error: a generator's loop"⟩
      let Lg ← pp Res
      let Rgs ← pp Rg
      let Fn (A : String) : String :=
        let es := row.map fun o => s!"{o.n}.{o.i} {Frontend.Check.qualStr o.q} {Tt} ~> 1"
        s!"F[{", ".intercalate es}] ({A})"
      let Q := s!"nu Y. F (({Tt}) * U Y + (({Bt}) + {Lg})) & F 1"
      let R := s!"(({Tt}) * U ({Q})) + (({Bt}) + {Lg})"
      let K := s!"U ((1 -o F ({R})) & F 1)"
      let Kc := s!"U ((1 -o F ({Rgs})) & F 1)"
      let St := s!"{Lg} + U ({Q})"
      let _ := Fn
      pure s!"io_pl{sfx} <- force io_hole_call;
io_ps{sfx} : {St} <- return (inl io_pl{sfx});
io_pf{sfx} <- return (unbang (unfold[pull ({Tt}) ({Bt}) 1, {St}] (!thunkv fun (io_pa{sfx} : {St}) ->
  < -- One turn of the generator's loop, handled: one handler site, so that the continuation it
    -- keeps is of one code.
    io_pob{sfx} : !({Lg} => {R}) <- return (!thunkv fun (io_pl{sfx} : {Lg}) ->
      io_phr{sfx} : !(({Bt}) + {Lg} => {R}) <- return (!thunkv fun (io_pv{sfx} : ({Bt}) + {Lg}) -> return (inr io_pv{sfx}));
      io_phc{sfx} : (!(({Tt}) * {K} => {R})) * 1 <- return ((!thunkv fun (io_pp{sfx} : ({Tt}) * {K}) ->
        let (io_px{sfx}, io_pk{sfx}) = io_pp{sfx};
        return (inl (io_px{sfx}, thunkv nu_in < io_pu{sfx} <- return (); (force io_pk{sfx}).1 io_pu{sfx}, (force io_pk{sfx}).2 >))), ());
      handle_with[{i.n}](io_phr{sfx}, io_phc{sfx}) ((nu_out (force io_pl{sfx})).1));
    io_po{sfx} : {R} <- case io_pa{sfx} \{
        inl io_pg{sfx} -> return ((unbang io_pob{sfx}) io_pg{sfx})
      | inr io_pq{sfx} ->
          -- The rest after the operation: when it ends the turn, the next turn runs at once, so
          -- that an observation that performs it once per turn gives an element each time.
          io_pr{sfx} <- (nu_out (force io_pq{sfx})).1;
          case io_pr{sfx} \{
            inl io_py{sfx} -> return (inl io_py{sfx})
          | inr io_pd{sfx} -> case io_pd{sfx} \{
              inl io_pb{sfx} -> return (inr (inl io_pb{sfx}))
            | inr io_pn{sfx} -> return ((unbang io_pob{sfx}) io_pn{sfx})
            }
          }
      };
    case io_po{sfx} \{
      inl io_px{sfx} -> let (io_pe{sfx}, io_pr{sfx}) = io_px{sfx}; return (inl (io_pe{sfx}, inr io_pr{sfx}))
    | inr io_pd{sfx} -> case io_pd{sfx} \{
        inl io_pb{sfx} -> return (inr (inl io_pb{sfx}))
      | inr io_pn{sfx} -> return (inr (inr (inl io_pn{sfx})))
      }
    },
    case io_pa{sfx} \{
      inl io_pg{sfx} ->
        io_chr{sfx} : !({Rgs} => {Rgs}) <- return (!thunkv fun (io_cv{sfx} : {Rgs}) -> return io_cv{sfx});
        io_chc{sfx} : (!(({Tt}) * {Kc} => {Rgs})) * 1 <- return ((!thunkv fun (io_cp{sfx} : ({Tt}) * {Kc}) ->
          let (io_cx{sfx}, io_ck{sfx}) = io_cp{sfx};
          io_cu{sfx} <- return ();
          (force io_ck{sfx}).1 io_cu{sfx}), ());
        io_cz{sfx} <- handle_with[{i.n}](io_chr{sfx}, io_chc{sfx}) ((nu_out (force io_pg{sfx})).2);
        return ()
    | inr io_pq{sfx} -> (nu_out (force io_pq{sfx})).2
    } >)));
return (thunkv nu_in < (nu_out (force io_pf{sfx} io_ps{sfx})).1, (nu_out (force io_pf{sfx} io_ps{sfx})).2 >)"
    let L ← (template sp "a stored generator" src : SM Comp)
    let L := L.fill (fun _ => none) fun h => if h == "io_hole_call" then some (.ret sp call') else none
    surfC n c none L

/-- A declaration with its surface forms elaborated, in the context the checker checks it in. -/
def surfDecl : Nat → Decl → DM Decl
  | 0, d => pure d
  | n + 1, .def_ sp nm ps A V mk => do
    let st ← get
    let c := TCx.ofScope (st.lib ++ st.out) false
    -- A `return` in a loop's body returns from the function: its loop is moved onto the body's
    -- spine, so that what follows the loop is the rest of the body (`forData`).
    let V ← (mapFnBody (fun M => if M.hasRet then normExits divFuel M else pure M) V : Except Error Val)
    -- A `break` on the body's spine, outside every loop.
    discard <| (mapFnBody (fun M => do
      let M ← normExits divFuel M
      if let some bsp := M.spineBreak then throw ⟨bsp, "`break` is outside every loop"⟩
      pure M) V : Except Error Val)
    set { st with exits := [] }
    let V' ← surfV n c (c.elabV A) V
    pure (.def_ sp nm ps A V' mk)
  | n + 1, .main sp C M => do
    let st ← get
    let M ← (if M.hasRet then normExits divFuel M else pure M : Except Error Comp)
    let st := { st with exits := [] }
    let caps := capNames.map fun x => Decl.extern Span.none ⟨x, Span.none⟩ (capTy Span.none x)
    let c := TCx.ofScope (st.lib ++ st.out ++ caps) true
    let exp := match (c.E.elabC c.Δ C).toOption with
      | some (.ret A) => some (BoCa.Fig16.LogRel.Core.CTy.ret A)
      | e => e
    set { st with caps := caps }
    -- `main` runs under a lifetime of its own, `'main`: its body is elaborated once, inside the
    -- borrow `mainLife` writes out.  `[spec §23]`
    let c₀ := c.push "io_main" (some (.ref .unit))
    let some top := c₀.elabL (.dom sp) | throw ⟨sp, "internal error: main's lifetime"⟩
    let c₁ := c₀.pushLife "main" top
    let some v := c₁.E.lenv.lookup "main" | throw ⟨sp, "internal error: main's lifetime"⟩
    let M' ← surfC n (c₁.push "io_mainb" (some (.mut (.var v) .unit))) exp M
    let M' ← mainLife sp C (["stdin", "stdout", "stderr"].filter (M.lentNames true).contains) M'
    modify fun st => { st with caps := [] }
    pure (.main sp C M')
  | _, d => pure d

/-- A lifetime bound `b` met with `q` (`q` alone when `b` is `top`). -/
def meetBound (q : Life) : Life → Life
  | .top _ => q
  | b => .meet b.span b q

/-- The bound of the lifetime parameter `c` of a function's type, met with `q`: `all 'c < @.`
becomes `all 'c < @ /\ q.` (`q` alone when `@` is `top`).  `[spec §23]` -/
def boundTyLife (c : String) (q : Life) : VTy → VTy
  | .bang sp X => .bang sp (boundTyLife c q X)
  | .all sp a b X =>
    if a.name == c then .all sp a (meetBound q b) X else .all sp a b (boundTyLife c q X)
  | T => T

/-- `boundTyLife` at the function's code: its `Fun 'c < @.` binder.  `[spec §23]` -/
def boundValLife (c : String) (q : Life) : Val → Val
  | .bangThunkv sp N => .bangThunkv sp (go N)
  | .thunkv sp N => .thunkv sp (go N)
  | V => V
where
  go : Comp → Comp
    | .lamL sp a b M =>
      if a.name == c then .lamL sp a (meetBound q b) M else .lamL sp a b (go M)
    | .ret sp V => .ret sp (boundValLife c q V)
    | M => M

/-- The instance of the template `t` at the type arguments `σ` (one per type parameter, each
known): its name, made and elaborated on first use, and the lifetimes of the call that it takes
first. A type argument with lifetimes (a view, `array_imm 'x u8`) makes an instance with a
lifetime parameter of its own for each, outside the template's: `!(all 'io_q0 < top. …)`, and a
call instantiates them at the call's lifetimes.  `[spec §15]` -/
def makeInst : Nat → TCx → Span → Decl → Array (Option CVTy) →
    DM (String × List BoCa.Lifetime.LifeVar)
  | 0, _, sp, _, _ => throw ⟨sp, "instantiation of generic functions does not terminate"⟩
  | n + 1, c, sp, t, σ => do
    let .def_ tsp tn ps A V mk := t | throw ⟨sp, "internal error: a generic function"⟩
    let names := ps.map (·.name)
    let mut ts₀ : List CVTy := []
    for (x, t) in names.zip σ.toList do
      let some t := t
        | throw ⟨sp, s!"the type `{x}` of `{tn.name}` is not determined by its arguments: " ++
            s!"write them, `{tn.name}[…](…)`"⟩
      ts₀ := ts₀ ++ [t]
    -- The lifetimes of the type arguments, in the order of the context, renamed `'io_qk`.
    let extras := (c.E.lenv.map (·.2)).eraseDups.reverse.filter fun v =>
      ts₀.any (BoCa.Fig16.LogRel.Core.Check.vfreeB v)
    let fresh (v : BoCa.Lifetime.LifeVar) : Option String :=
      (extras.idxOf? v).map (s!"io_q{·}")
    let c' := { c with E := { c.E with lenv := c.E.lenv.map fun (nm, v) =>
      ((fresh v).getD nm, v) } }
    let mut σs : TySubst := []
    for (x, t) in names.zip ts₀ do
      σs := σs ++ [(x, ← c'.surface sp t)]
    let key := (tn.name, σs.map (·.2.strip))
    let st ← get
    if let some name := st.insts.lookup key then return (name, extras)
    let name := s!"{tn.name}__g{st.insts.length}"
    let mk' := match mk with
      | .template m _ => m
      | mk => mk
    let binders := (List.range extras.length).map fun k => (⟨s!"io_q{k}", tsp⟩ : Ident)
    -- A bound `S: 'c` bounds the instance's `'c` by the lifetimes of `S`'s type argument too.
    let mut A₁ := A.subst σs
    let mut V₁ := V.subst σs
    for (S, cv) in mk.bounds do
      let some k := names.idxOf? S.name | continue
      let some t := ts₀[k]? | continue
      let qs := (extras.zipIdx).filterMap fun (v, j) =>
        if BoCa.Fig16.LogRel.Core.Check.vfreeB v t then some (Life.var tsp s!"io_q{j}") else none
      if let q :: qs := qs then
        let q := qs.foldl (Life.meet tsp) q
        A₁ := boundTyLife cv.name q A₁
        V₁ := boundValLife cv.name q V₁
    let (A', V') ← if extras.isEmpty then pure (A₁, V₁) else
      match A₁, V₁ with
      | .bang asp X, .bangThunkv vsp N =>
        pure (VTy.bang asp (binders.foldr (fun b X => .all asp b (.top asp) X) X),
          Val.bangThunkv vsp (binders.foldr
            (fun b N => .lamL vsp b (.top vsp) (.ret vsp (.thunkv vsp N))) N))
      | _, _ => throw ⟨sp, s!"`{tn.name}` is instantiated at a type with a lifetime, and is " ++
          "not a function: a generic function is instantiated at types without one"⟩
    let inst := Decl.def_ tsp ⟨name, tn.span⟩ [] A' V' mk'
    let inst := Elab.fillDecl (st.lib ++ st.out) st.caps inst
    let libNames := if st.libNames.contains tn.name then name :: st.libNames else st.libNames
    let st' ← (elabDecl n { st with insts := (key, name) :: st.insts, libNames } inst : SM DivSt)
    set { st' with quiet := st.quiet }
    return (name, extras)

/-- A call `f W` of a generic callee (a template, a core `def` with type parameters, or a
function with lifetime parameters), with the type and lifetime arguments it leaves out filled and
`unbang` inserted; `none` when the callee is none of these. `exp` is the type expected of the
call's result. -/
def genericCall : Nat → TCx → Span → Option CVTy → Val → Val → Option Decl → DM (Option Val)
  | 0, _, _, _, _, _, _ => pure none
  | n + 1, c, sp, exp, f, W, pick => do
    let st ← get
    let isLocal (h : String) : Bool := c.locals.any (·.1 == h)
    -- Several templates of one name (a pull adapter of `lib/adapters.bc` and a sized one of
    -- `lib/iters.bc`): the first whose parameters the arguments' types match, as Rust chooses an
    -- iterator's `map` by the iterator's type.
    if pick.isNone then
      if let some (h, _) := genericCallee f then
        if !isLocal h then
          let cands := st.templates.filter fun | .def_ _ m _ _ _ _ => m.name == h | _ => false
          if cands.length ≥ 2 then
            let mut err : Option Error := none
            for t in cands do
              try
                return ← genericCall n c sp exp f W (some t)
              catch e =>
                if err.isNone then err := some e
            match err with
            | some e => throw e
            | none => return none
    let head ← match genericCallee f with
      | some (h, targs) =>
        match (if isLocal h then none else if pick.isSome then pick else
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
      | if generic then
          let why := match head with
            | .tmpl (.def_ _ _ tps A _ _) _ =>
              patErr c (tps.map Ident.name) A
            | _ => ""
          throw ⟨f.span, s!"the type of `{fname}` does not elaborate here{why}"⟩
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
          | .fam (.imm _ A), some (.fam (.ref A')) | .fam (.mut _ A), some (.fam (.ref A')) =>
            if let some m' := matchV m 0 A A' then m := m'
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
        -- A callback that loops where a function is expected: its result is what its loop
        -- finishes with (it is specialized at its own type, `specV`), unless the parameter's
        -- result is itself a loop.
        let T := if (matchV m 0 Pi T).isSome then T else match Pi, T with
          | .thunk (.arr _ (.ret Q)), .thunk (.arr A' (.ret L))
          | .bang (.thunk (.arr _ (.ret Q))), .bang (.thunk (.arr A' (.ret L))) =>
            if !hasPhV Q then T else
            match (loopOf L).map (·.1) with
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
            -- A copy made for the handlers of its effects is named for the function it copies.
            let shown := (fname.splitOn "__").headD fname
            throw ⟨Wi.span, s!"this argument of `{shown}` has type `{ppT T}`, which is not " ++
              s!"`{written}`"⟩
        args := args.set! k (some Wi')
        tys := tys.set! k (some T)
    -- What the arguments leave open, from the type expected of the result.
    if let (some e, .ret Q) := (exp, sig.R) then
      if m.isOpen Q then
        if let some m' := matchV m 0 Q e then m := m'
    let lends := W.lends
    -- A lifetime the call leaves undetermined is `dom`, the meet of the lifetimes in scope (in
    -- `main`, at least `'main`).  `[spec §23]`
    for (v, _) in sig.binders do
      if (m.life.lookup v).isNone && !(lends && sig.binders.length == 1) then
        if c.Δ.entries.isEmpty then
          throw ⟨sp, s!"the lifetime `{lname v}` of `{fname}` is not determined by its arguments " ++
            s!"here: write it, `{writeLives fname}"⟩
        m := { m with life := (v, c.Δ.meetOfDom) :: m.life }
    -- The callee at its type arguments.
    let mut extras : List BoCa.Lifetime.LifeVar := []
    let base ← match head with
      | .tmpl t _ => do
        let (nm, ex) ← makeInst n c sp t m.ty
        extras := ex
        pure (Val.var f.span nm)
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
      -- A lend at a borrow parameter is a borrow around the call (`lendCall`); a lend at a
      -- parameter of the place's own type moves the place and rebinds it (`Comp.elab`).
      let atBorrow := match lendParam sig.P W with
        | some (_, _, .mut ..) | some (_, _, .imm ..) => true
        -- An owned array lent at a view parameter (`lendSlice`, SPEC §9).
        | some (_, _, .fam (.mut ..)) | some (_, _, .fam (.imm ..)) => true
        | _ => false
      if atBorrow then
        if sig.binders.length != 1 then
          throw ⟨sp, s!"`{fname}` has several lifetime parameters: a lend `&x` in its call is " ++
            "not provided; borrow in a block and pass the borrow"⟩
        match ← lendCall c sp base (argOf W argsL) with
        | some V => return some V
        | none => throw ⟨sp, s!"the lend in this call of `{fname}` is not at a borrow parameter"⟩
    let mut g := if sig.bang then Val.unbang f.span base else base
    -- An instance at types with lifetimes takes the call's lifetimes first (`makeInst`).
    for v in extras do g := .inst sp g (← c.surfaceL sp (.var v))
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
    -- A generic function is a template, instantiated where it is called.
    if let .def_ _ _ (_ :: _) _ _ (.template _ _) := d then
      return { st with templates := st.templates ++ [d] }
    -- The loops of a library's declarations are not reported.
    let st := { st with quiet := match d with
      | .def_ _ nm _ _ _ _ => st.libNames.contains nm.name
      | _ => false }
    -- A div function taking a borrow takes the owner, lent at each step (`LoopLend.lentDef`).
    let c₀ := TCx.ofScope (st.lib ++ st.out) false
    let d := (← (Frontend.Elab.LoopLend.lentDef c₀ (dataFor st.sizedFns) d :
      Except Error (Option Decl))).getD d
    let (d, st) ← (surfDecl fuel d).run st
    -- A recursive group's source under a heap driver: its machine (SPEC §20).
    let d ← match d with
      | .def_ _ nm _ _ _ _ =>
        if nm.name.endsWith "__mach_src" then recMachine (st.lib ++ st.out) d else pure d
      | d => pure d
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
    let mark := hof.mark
    let copy := if hof.bang then Decl.def_ hof.sp ⟨name, hof.name.span⟩ [] (.bang hof.P.span F)
        (.bangThunkv hof.sp lam) mark
      else Decl.def_ hof.sp ⟨name, hof.name.span⟩ [] F (.thunkv hof.sp lam) mark
    let copies := ((hof.name.name, P'.strip), name) :: st.copies
    let st₁ : DivSt := { st with copies := copies }
    let st' ← (elabDecl n st₁ copy : SM DivSt)
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
        let name ← copyOf n hof P's
        let call := Val.app sp (renameCallee name f) W'
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
    | .perform sp k i V => do pure (.perform sp k i (← specV n c V))
    | .abort sp k i V => do pure (.abort sp k i (← specV n c V))
    | .handle sp k hr hc M => do pure (.handle sp k hr hc (← specC n c M))
    | .unwind sp x A M D N => do
      let t := bindTy c A M
      pure (.unwind sp x A (← specC n c M) (← specC n c.pushDead D) (← specC n (c.push x.name t) N))
    | .withbor2r sp x b A B r p m M => do
      pure (.withbor2r sp x b A B r p m (← specC n (c.push m.name none) M))
    | M => pure M
end

/-- The declarations with divergence inferred, in order (copies before their first use), and
whether any body was elaborated as a loop. -/
def elabDivs (lib decls : List Decl) (libNames : List String) (perTurn : List Nat := []) :
    SM (List Decl × Bool) := do
  let st ← decls.foldlM (init := ({ lib, libNames, perTurn } : DivSt)) (elabDecl divFuel)
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

/-- The declarations `ds` with each `include m` replaced by the module's declarations, at most
once each, a module's own `include`s first; `inc` the modules included so far. -/
def expandIncludes : Nat → List Decl → List Decl × List String →
    Except Error (List Decl × List String)
  | fuel, ds, st => ds.foldlM (init := st) fun (acc, inc) d =>
    match d with
    | .include sp m =>
      if inc.contains m.name then pure (acc, inc) else
      match library m.name with
      | some (.error e) => throw ⟨sp, e⟩
      | some (.ok src) => do
        let l ← match parseProgram src with
          | .ok l => pure l.decls
          | .error e => throw ⟨e.span, s!"lib/{m.name}.bc: {e.msg}"⟩
        match fuel with
        | 0 => throw ⟨sp, s!"the modules include each other: `{m.name}`"⟩
        | fuel + 1 => expandIncludes fuel l (acc, m.name :: inc)
      | none => throw ⟨sp, s!"no library module `{m.name}`: the modules are " ++
          ", ".intercalate libNames⟩
    | d => pure (acc ++ [d], inc)

/-- The program with its sugar elaborated, and the number of library declarations it begins
with, recording the origins of generated code.  `[spec §11, §14]` -/
def elaborateS (p : Program) : SM (Program × Nat) := do
  let libOf (m : String) : Except Error (List Decl) :=
    match library m with
    | some (.ok src) => match parseProgram src with
      | .ok l => pure l.decls
      | .error e => throw ⟨e.span, s!"lib/{m}.bc: {e.msg}"⟩
    | some (.error e) => throw ⟨Span.none, e⟩
    | none => throw ⟨Span.none, s!"no library module `{m}`"⟩
  -- The libraries are in scope for typing when the program may use them: the I/O library when
  -- `main` may use the capabilities ambiently, the divergence library when the program names
  -- its functions. They are emitted below only when the program uses them. The capabilities are
  -- in scope for typing `main`, which may use them ambiently.
  -- The capabilities `main` uses ambiently are read off the program as written: an included
  -- module's externs (`include io`) do not make them declared.
  let p₀ := p
  let mayIO := !(ambientCaps p₀).isEmpty
  -- `include m`: the module's declarations, in place (at most once each); a module's own
  -- `include`s come in first.
  let (decls₀, incl) ← expandIncludes libNames.length p.decls ([], [])
  -- Effects and handlers (SPEC §18), before the rest of the sugar: the clauses become functions,
  -- the functions with a row their copies, and each `with` a borrow block.
  let libFns := (decls₀.filter fun d => !p₀.decls.contains d).filterMap fun
    | .def_ _ m _ _ _ _ => some m.name
    | _ => none
  let (decls, fx, perTurn) ← (Elab.Effects.elaborate decls₀ libFns : Except Error _)
  -- Effects, then rows, lowering shapes and calls, each in source order.
  let kindOf (m : String) : Nat := match (m.splitOn " ").head? with
    | some "effect" => 0 | some "row" => 1 | some "lowering" => 2 | _ => 3
  let fx := (fx.eraseDups.toArray.qsort fun (a, m) (b, n) =>
    kindOf m < kindOf n || (kindOf m == kindOf n && b.start.later a.start)).toList
  for (sp, m) in fx do
    let (k, rest) := match m.splitOn " " with
      | k :: r => (k, " ".intercalate r)
      | [] => ("", m)
    note sp s!"{effectsTag}{k} {sp.start.render}: {rest}"
  let p : Program := ⟨decls⟩
  let mayDiv := usesName "div_fuel" p || usesName "div_bind" p || usesName "div_defer" p
  -- The prelude is in scope when the program names one of its declarations.
  let preludeNames := ["true", "false", "not", "to_i32", "to_u8"]
  let mayPrelude := !incl.contains "prelude" && preludeNames.any (usesName · p)
  let ioAll ← if mayIO && !incl.contains "io" then libOf "io" else pure []
  let divAll ← if mayDiv && !incl.contains "div" then libOf "div" else pure []
  let preludeAll ← if mayPrelude then libOf "prelude" else pure []
  let typing := preludeAll ++ ioAll ++ divAll
  let capDecls := if mayIO then capNames.map fun c =>
      Decl.extern Span.none ⟨c, Span.none⟩ (capTy Span.none c) else []
  -- Bindings whose type only their uses determine (an injection) are annotated first.
  let p := Elab.fillProgram typing capDecls p
  -- Divergence of the user's definitions, before the libraries (which do not loop) come in.
  let libNames := (decls₀.filter fun d => !p₀.decls.contains d).filterMap fun
    | .def_ _ m _ _ _ _ => some m.name
    | _ => none
  let (decls, anyDiv) ← elabDivs typing p.decls libNames perTurn
  let rest := decls.filter fun | .main .. => false | _ => true
  let mc := TCx.ofScope (typing ++ rest ++ capDecls) true
  let mainLoops := match decls.findSome? (fun | .main _ C M => some (C, M) | _ => none) with
    | some (C@(.ret _ B), M) => !C.returnsLoop && (loopsAt mc (mc.elabV B) M).isSome
    | _ => false
  let cs := ambientCaps p₀
  let ioLib ← if cs.isEmpty || incl.contains "io" then pure [] else
    if mayIO then pure ioAll else libOf "io"
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
    if mayDiv then pure divAll else libOf "div"
  let lib := preludeAll ++ ioLib ++ divLib
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
