import Frontend.Parser
import Frontend.Print
import Frontend.Check.Steps

/-!
# Frontend — the sugar  `[spec §11, §14]`

The forms below are elaborated here into ordinary core syntax before checking. The checker, the
kernel and the theorems never see them: what they check is a program a user could have written
by hand (`bcc desugar` prints it). Divergence (§14) is elaborated here too: see the section
*Divergence* below.

* **Ambient capabilities in `main`.** A program that declares no externs and whose `main`
  mentions `stdin`, `stdout` or `stderr` gets the I/O library (`lib/io.bc`), which declares the
  operations, and an `extern` for each capability it mentions, in the order `stdin`, `stdout`,
  `stderr`. `main : F A` becomes `main : F (Caps * A)`: each terminal `return V` of its body
  becomes `return (caps, V)`, and any other terminal `T` becomes `r <- T; return (caps, r)`,
  with the capabilities read by name where the path ends (`wrapTail`).
* **`for x in bytes c { M }; N`** in any function or `main` becomes a loop by `unfold` over the
  state (iterator, other capabilities, threaded variables), and makes the function div
  (`forLoop`, §14).
* **`&c`** in the head of `x <- M; N` becomes `r <- M[c/&c]; let (c, x) = r; N` (`Comp.elab`).

The generated code is a template, printed and parsed, whose holes are filled with the program's
own syntax, so errors inside the program's code keep its positions.
-/

namespace Frontend.Sugar
open Frontend.Check (mentionsV mentionsC)

/-- The I/O library, `lib/io.bc`. -/
def ioLibrary : String := include_str "../lib/io.bc"

/-- The divergence library, `lib/div.bc`: the delay bind and the fuel handler. -/
def divLibrary : String := include_str "../lib/div.bc"

def capNames : List String := ["stdin", "stdout", "stderr"]

def capTySrc (c : String) : String := if c == "stdin" then "ref input" else "ref output"

def capTy (sp : Span) (c : String) : VTy := .ref sp (.handle sp (c != "stdin"))

/-! ### Lending a capability to one call -/

mutual
/-- The `&c` of a value outside nested computations, replaced by `c`. -/
def _root_.Frontend.Val.takeLends : Val → Val × List Ident
  | .lend _ x => (.var x.span x.name, [x])
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
  | M => (M, [])
end

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
its body loops: it has a `for`, or a direct-style call `x <- return (f V); N` of a div function
`f`, on its spine (the tail positions of binds, `let`s, `case` arms and `for`s). Definitions are
in dependency order, so one pass infers this. A div function written with a plain result
`A => B` is elaborated to `A => U (loop B R)`, and so is `main`; `total def` asserts that the body
does not loop.

In a div body, a direct-style call becomes the delay bind of `lib/div.bc`, `div_bind`, with the
rest of the body as its continuation; a `for` becomes a loop by `unfold` followed by the same bind;
a terminal `return V` becomes the loop that finishes with `V` at its first observation. The
residual `R` is the capabilities the result hands back first (`K` of `K * V`, SPEC §11), paired
with `()`, or `1` when there are none: a loop closed early hands its capabilities back.
-/

/-- A function returning a loop, `A => U (loop B R)` or `!(A => U (loop B R))` (a `delay B`
is `loop B 1`): its `B` and `R`. -/
def loopSig : VTy → Option (VTy × VTy)
  | .lolli _ _ (.thunk _ (.loop _ B R)) | .bang _ (.lolli _ _ (.thunk _ (.loop _ B R))) =>
    some (B, R)
  | .lolli _ _ (.thunk sp (.delay _ B)) | .bang _ (.lolli _ _ (.thunk sp (.delay _ B))) =>
    some (B, .unit sp)
  | _ => none

/-- A capability type as written: `In`, `Out`, `ref input`, `ref output`, or a tuple of them. -/
def isCapTy : VTy → Bool
  | .name _ n => n == "In" || n == "Out"
  | .ref _ (.handle _ _) => true
  | .tensor _ A B => isCapTy A && isCapTy B
  | _ => false

/-- The capabilities a result hands back first: `K` of `K * V`. -/
def capPart : VTy → Option VTy
  | .tensor _ K _ => if isCapTy K then some K else none
  | _ => none

/-- The components of a right-nested tuple type. -/
def tupleParts : VTy → List VTy
  | .tensor _ A B => A :: tupleParts B
  | A => [A]

/-- A type with the I/O library's names for the capability types expanded, for comparing
residuals as written. -/
def capNorm : VTy → VTy
  | .name sp "In" => .ref sp (.handle sp false)
  | .name sp "Out" => .ref sp (.handle sp true)
  | .tensor sp A B => .tensor sp (capNorm A) (capNorm B)
  | A => A.strip

/-- The residual of a div function with result `B`: `K * 1`, or `1`. -/
def residual (B : VTy) : VTy :=
  match capPart B with
  | some K => .tensor K.span K (.unit K.span)
  | none => .unit B.span

/-- `F (U (loop B R))` (or `F (U (delay B))`): a computation type that returns a loop, written
out; such a body is core, not elaborated. -/
def _root_.Frontend.CTy.returnsLoop : CTy → Bool
  | .ret _ (.thunk _ (.loop ..)) | .ret _ (.thunk _ (.delay ..)) => true
  | _ => false

/-- The div functions in scope, with their types. -/
abbrev Divs := List (String × VTy)

/-- The variables bound so far, newest first, with the type their binding gives. -/
abbrev TyEnv := List (String × Option VTy)

/-- The type of a function name: a variable's, or else a div function's. -/
def fnTy (ds : Divs) (env : TyEnv) (f : String) : Option VTy :=
  match env.lookup f with
  | some T => T
  | none => ds.lookup f

/-- The callee of a direct-style call `return (f V)`, or `return ((unbang f) V)` at a `!` type. -/
def callee : Comp → Option String
  | .ret _ (.app _ (.var _ f) _) | .ret _ (.app _ (.unbang _ (.var _ f)) _) => some f
  | _ => none

/-- The head of `x <- M; N` is a direct-style call of a div function: its `B` and `R`. -/
def divCall (ds : Divs) (env : TyEnv) (M : Comp) : Option (VTy × VTy) := do
  let f ← callee M
  let T ← fnTy ds env f
  let bang := match M, T with
    | .ret _ (.app _ (.unbang ..) _), .bang .. | .ret _ (.app _ (.var ..) _), .lolli .. => true
    | _, _ => false
  if bang then loopSig T else none

/-- A direct-style call of a div function, described. -/
def divCallAt (ds : Divs) (env : TyEnv) (M : Comp) : Option (Span × String) :=
  match divCall ds env M.takeLends.1, callee M.takeLends.1 with
  | some _, some f => some (M.span, s!"it calls the div function `{f}`")
  | _, _ => none

/-- The type a `let (x, y) = V` gives its names, when `V` is a variable of known pair type. -/
def pairTypes (env : TyEnv) : Val → Option VTy × Option VTy
  | .var _ z => match env.lookup z with
    | some (some (.tensor _ A B)) => (some A, some B)
    | _ => (none, none)
  | _ => (none, none)

/-- Where a body loops, on its spine: a `for`, or a direct-style call of a div function. -/
def loopsAt (ds : Divs) : TyEnv → Comp → Option (Span × String)
  | env, .bind _ x A M N _ => (divCallAt ds env M).orElse fun _ => loopsAt ds ((x.name, A) :: env) N
  | env, .letUnit _ _ M => loopsAt ds env M
  | env, .letPair _ x y V M =>
    let (Ax, Ay) := pairTypes env V
    loopsAt ds ((y.name, Ay) :: (x.name, Ax) :: env) M
  | env, .case _ _ x M y N =>
    (loopsAt ds ((x.name, none) :: env) M).orElse fun _ => loopsAt ds ((y.name, none) :: env) N
  | _, .for_ sp .. => some (sp, "it has a `for`")
  | env, T => divCallAt ds env T

/-- The names of a tuple of variables. -/
def tupleVars : Val → Option (List String)
  | .var _ x => some [x]
  | .pair _ V W => do pure ((← tupleVars V) ++ (← tupleVars W))
  | _ => none

/-- The names under which a body hands back `n` capabilities: the first component of a
terminal `return (K, V)`. -/
def termCaps (n : Nat) : Comp → Option (List String)
  | .bind _ _ _ _ N _ | .letUnit _ _ N | .letPair _ _ _ _ N | .for_ _ _ _ _ N => termCaps n N
  | .case _ _ _ M _ N => (termCaps n M).orElse fun _ => termCaps n N
  | .ret _ (.pair _ K _) => (tupleVars K).filter (·.length == n)
  | _ => none

/-- What a div body is elaborated at: its result, its residual and its capabilities. -/
structure LoopCx where
  ds : Divs
  B : VTy
  R : VTy
  caps : List (String × VTy)

def LoopCx.kSrc (cx : LoopCx) : String := tupleSrc (cx.caps.map (·.1))

/-- The residual built from the capabilities in scope. -/
def LoopCx.rSrc (cx : LoopCx) : String :=
  if cx.caps.isEmpty then "()" else s!"({cx.kSrc}, ())"

def internalError (sp : Span) (what : String) (e : Error) : Error :=
  ⟨sp, s!"internal error in {what}: {e.render}"⟩

/-- A terminal `T` of a div body: `io_v : B <- T`, then the loop that finishes with `io_v` at
its first observation; closed instead, it hands back the capabilities of `io_v`. -/
def dret (cx : LoopCx) (T : Comp) : Except Error Comp := do
  let close := if cx.caps.isEmpty then "return ()"
    else "let (io_k, io_w) = io_v; return (io_k, ())"
  let src := s!"io_v : {cx.B.pp} <- force io_hole_t;
return (thunkv nu_in < return (inl io_v), {close} >)"
  let L ← (parseComp src).mapError (internalError T.span "a div function's result")
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
    (lend : Option Ident) (Bf Rf : VTy) (N' : Comp) : Except Error Comp := do
  let bindX := match lend, A with
    | some c, _ => s!"let ({c.name}, {x.name}) = io_a;"
    | none, some A => s!"{x.name} : {A.pp} <- return io_a;"
    | none, none => s!"{x.name} <- return io_a;"
  let abort ← if (capNorm Rf).strip == (capNorm cx.R).strip then pure "return io_r"
    else match Rf, lend with
      | .unit _, _ => pure s!"let () = io_r; return {cx.rSrc}"
      | .tensor _ _ (.unit _), some c =>
        if cx.caps.any (·.1 == c.name) then pure s!"let ({c.name}, io_u) = io_r; return {cx.rSrc}"
        else throw ⟨sp, s!"the call lends `{c.name}`, which is not among the capabilities this " ++
          "function hands back"⟩
      | _, _ => throw ⟨sp, s!"a call of a div function whose loop hands back `{Rf.pp}` when closed " ++
          "must lend its capability with `&c`, or hand back what this function hands back, " ++
          s!"`{cx.R.pp}` (SPEC §14)"⟩
  let src := s!"io_m <- force io_hole_call;
return (div_bind[{Bf.pp}, {cx.B.pp}, {Rf.pp}, {cx.R.pp}] (io_m, thunkv
  < fun (io_a : {Bf.pp}) -> {bindX} force io_hole_rest,
    fun (io_r : {Rf.pp}) -> {abort} >))"
  let L ← (parseComp src).mapError (internalError sp "a call of a div function")
  pure (L.fill (fun _ => none)
    (fun n => if n == "io_hole_call" then some call else if n == "io_hole_rest" then some N'
      else none))

/-- The latest binding of each name, oldest first. -/
def latest (env : List (String × Option VTy)) : List (String × Option VTy) :=
  env.reverse.foldl (fun acc (y, T) => (acc.filter (·.1 != y)) ++ [(y, T)]) []

/-- `for x in V { M }; N` in a div body: a loop by `unfold` whose state is the iterator `V`,
the other capabilities and the variables the loop threads, each at the type its binding gives.
Its `close` closes the iterator and hands the capabilities back. When `N` is total, `rest` is
`.inl N`: at the end of the stream the loop runs `N` and finishes with its value, and it threads
the variables `M` or `N` mentions. Otherwise `rest` is `.inr N'`, `N` elaborated: the loop
threads the variables `M` mentions, finishes with the capabilities and those variables, and
the delay bind runs `N'` with them rebound.  `[spec §14]` -/
def forLoop (cx : LoopCx) (env : TyEnv) (sp : Span) (x : Ident) (V : Val) (M : Comp)
    (rest : Comp ⊕ Comp) : Except Error Comp := do
  let Ax : VTy ← match V with
    | .app _ (.var _ "bytes") _ => pure (.int sp .w32)
    | _ => throw ⟨V.span, "`for` iterates over `bytes c`, the input `c` as a stream of bytes"⟩
  if let some (sp', what) := loopsAt cx.ds env M then
    throw ⟨sp', s!"the body of a `for` is one step of its loop and must be total, but {what} " ++
      "(SPEC §14)"⟩
  let cs := cx.caps.map (·.1)
  let c ← match cs.filter (mentionsV · V) with
    | [c] => pure c
    | _ => throw ⟨V.span, "the iterator of a `for` must be made from one capability that the " ++
        "function hands back, which the iterator hands back at its end"⟩
  let reads (y : String) : Bool := match rest with
    | .inl N => mentionsC y M || mentionsC y N
    | .inr _ => mentionsC y M
  let used := (latest env).filter fun (y, _) => !cs.contains y && y != x.name && reads y
  let ws ← used.mapM fun (y, T) => match T with
    | some T => pure (y, T)
    | none => throw ⟨sp, s!"the loop threads `{y}`: bind it with its type, `{y} : T <- …;`"⟩
  let th := cx.caps.filter (·.1 != c)
  let sv := th.map (·.1) ++ ws.map (·.1)
  let svTy := th.map (·.2.pp) ++ ws.map (·.2.pp)
  let cTy := ((cx.caps.lookup c).map (·.pp)).getD "1"
  let st := s!"U (iter ({Ax.pp}) ({cTy}) ({cTy})) * {tupleTySrc svTy}"
  let kT := tupleTySrc (cx.caps.map (·.2.pp))
  let wT := tupleTySrc (ws.map (·.2.pp))
  let fin := match rest with
    | .inl _ => s!"({cx.B.pp})"
    | .inr _ => s!"({kT} * {wT})"
  let wv := tupleSrc (ws.map (·.1))
  let finish := match rest with
    | .inl _ => "force io_hole_fin"
    | .inr _ => s!"return (inl ({cx.kSrc}, {wv}))"
  let R := cx.R.pp
  let ds := destructSrc "io_st" sv
  let wn : List String := ws.map (·.1)
  let result := match rest with
    | .inl _ => "return (thunkv nu_in < (nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2 >)"
    | .inr _ => s!"io_l <- return (thunkv nu_in < (nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2 >);
return (div_bind[{fin}, {cx.B.pp}, ({R}), ({R})] (io_l, thunkv
  < fun (io_a : {fin}) ->
      let (io_ka, io_wa) = io_a;
      {destructSrc "io_ka" cs}      {destructSrc "io_wa" wn}      force io_hole_rest,
    fun (io_r : {R}) -> return io_r >))"
  let src := s!"io_step : !U ({st} -o F ({fin} + ({st})) & F ({R})) <- return (!thunkv fun (io_s : {st}) ->
  < let (io_it, io_st) = io_s;
    {ds}    io_o <- (nu_out (force io_it)).1;
    case io_o \{
      inl io_p ->
        let ({x.name}, io_it) = io_p;
        force io_hole_body
    | inr io_c ->
        {c} <- return io_c;
        {finish}
    },
    let (io_it, io_st) = io_s;
    {ds}    io_c <- (nu_out (force io_it)).2;
    {c} <- return io_c;
    return {cx.rSrc} >);
io_f <- return (unbang (unfold[loop {fin} ({R}), {st}] io_step));
io_s0 : {st} <- return (io_hole_v, {tupleSrc sv});
{result}"
  let L ← (parseComp src).mapError (internalError sp "`for`")
  let body := wrapTail (fun T => .bind T.span ⟨"io_u", T.span⟩ none T
      (.ret T.span (.inr T.span (.pair T.span (.var T.span "io_it") (tupleVal T.span sv)))) false) M
  let hole : String → Option Comp := match rest with
    | .inl N => fun n =>
      if n == "io_hole_body" then some body
      else if n == "io_hole_fin" then some (wrapTail (fun T =>
        let fin := Comp.bind T.span ⟨"io_v", T.span⟩ (some cx.B) T
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

/-- A div body, elaborated to compute its loop (see the section's comment). `env` holds the
variables bound so far, newest first, with the type their binding gives.  `[spec §14]` -/
def loopBody (cx : LoopCx) : List (String × Option VTy) → Comp → Except Error Comp
  | env, .bind sp x A M N lin => do
    let (M', lends) := M.takeLends
    match divCall cx.ds env M' with
    | none =>
      let N' ← loopBody cx ((x.name, A) :: env) N
      pure (.bind sp x A M N' lin)
    | some (Bf, Rf) =>
      let lend ← match lends with
        | [] => pure none
        | [c] => pure (some c)
        | _ => throw ⟨sp, "a call lends at most one capability with `&`"⟩
      let env' := match lend with
        | some c =>
          let (Kc, Vx) := match Bf with
            | .tensor _ K V => (some K, some V)
            | _ => (none, none)
          (x.name, A.orElse fun _ => Vx) :: (c.name, Kc) :: env
        | none => (x.name, A.orElse fun _ => some Bf) :: env
      let N' ← loopBody cx env' N
      divBind cx sp x A M' lend Bf Rf N'
  | env, .letUnit sp V M => return .letUnit sp V (← loopBody cx env M)
  | env, .letPair sp x y V M => do
    let (Ax, Ay) := pairTypes env V
    return .letPair sp x y V (← loopBody cx ((y.name, Ay) :: (x.name, Ax) :: env) M)
  | env, .case sp V x M y N =>
    return .case sp V x (← loopBody cx ((x.name, none) :: env) M) y
      (← loopBody cx ((y.name, none) :: env) N)
  | env, .for_ sp x V M N => do
    -- What follows runs inside the loop's last step when it is total and every variable it
    -- reads has a type; otherwise it follows by the delay bind.
    let cs := cx.caps.map (·.1)
    let typed := (latest env).all fun (y, T) =>
      cs.contains y || y == x.name || !mentionsC y N || T.isSome
    if (loopsAt cx.ds env N).isNone && typed then forLoop cx env sp x V M (.inl N)
    else forLoop cx env sp x V M (.inr (← loopBody cx env N))
  | env, T => do
    let (T', lends) := T.takeLends
    match divCall cx.ds env T', lends with
    | some (Bf, Rf), [] =>
      let x : Ident := ⟨"io_t", T.span⟩
      divBind cx T.span x none T' none Bf Rf (← dret cx (.ret T.span (.var T.span "io_t")))
    | _, _ => dret cx T

/-- The context a div function with result `B` and body `M` is elaborated at: its capabilities
are those its result hands back first, named as a terminal `return (K, V)` names them. -/
def loopCxOf (ds : Divs) (sp : Span) (B : VTy) (M : Comp) : Except Error LoopCx := do
  let caps ← match capPart B with
    | none => pure []
    | some K =>
      let Ks := tupleParts K
      match termCaps Ks.length M with
      | some ns => pure (ns.zip Ks)
      | none => throw ⟨sp, s!"a div function whose result hands back capabilities, `{K.pp}`, " ++
          "must hand them back by name: `return (c, …)` (SPEC §14)"⟩
  pure ⟨ds, B, residual B, caps⟩

/-! ### Programs -/

/-- The capabilities a program uses ambiently: none if it declares an extern. A `main` that loops
but mentions no capability is driven by the runtime with `stdout`. -/
def ambientCaps (p : Program) (loops : Bool) : List String :=
  if p.decls.any (fun | .extern .. => true | _ => false) then [] else
  match p.decls.findSome? (fun | .main _ _ M => some M | _ => none) with
  | some M =>
    let cs := capNames.filter (mentionsC · M)
    if cs.isEmpty && loops then ["stdout"] else cs
  | none => []

/-- `main` with ambient capabilities, elaborated: its new type and body.  `[spec §11, §14]` -/
def ambientMain (ds : Divs) (cs : List String) (sp : Span) (C : CTy) (M : Comp) :
    Except Error (CTy × Comp) := do
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
  if (loopsAt ds [] M).isNone then return (.ret sp B, M')
  let cx : LoopCx := ⟨ds, B, .tensor sp capsT (.unit sp), cs.zip (cs.map (capTy sp))⟩
  pure (.ret sp (.thunk sp (.loop sp B cx.R)), ← loopBody cx [] M')

/-- A `def`, with divergence inferred: the declaration as elaborated, and its entry in the div
functions when it is one. A div function is `thunkv fun (x : A) -> M` at `A => B`, or
`!thunkv fun (x : A) -> M` at `!(A => B)`.  `[spec §14]` -/
def elabDef (ds : Divs) : Decl → Except Error (Decl × Option (String × VTy))
  | d@(.def_ sp n ps A V mk) => do
    if (loopSig A).isSome then return (d, some (n.name, A))
    let lam := match V with
      | .thunkv _ (.lam _ x Ax M) | .bangThunkv _ (.lam _ x Ax M) => some (x, Ax, M)
      | _ => none
    let why := lam.bind fun (x, Ax, M) => loopsAt ds [(x.name, some Ax)] M
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
      let cx ← loopCxOf ds sp B M
      let M' ← loopBody cx [(x.name, some Ax)] M
      let F := VTy.lolli A.span Ar (.thunk B.span (.loop B.span B cx.R))
      let A' := if bang then VTy.bang A.span F else F
      let V' := match V with
        | .thunkv vsp (.lam lsp _ _ _) => Val.thunkv vsp (.lam lsp x Ax M')
        | .bangThunkv vsp (.lam lsp _ _ _) => Val.bangThunkv vsp (.lam lsp x Ax M')
        | V => V
      return (.def_ sp n ps A' V' mk, some (n.name, A'))
  | d => pure (d, none)

/-! ### Specialization at a callback's type

A higher-order function takes a callback at a function type, `A => B` or `!(A => B)`. Passed a
div function there, `A => U (loop B R)`, it is specialized: the elaborator makes a copy of it
with that parameter at the callback's type and infers the copy's divergence, so calls through
the parameter become direct-style calls of a div function, and the copy is div. There is one
copy per function and parameter type. A total callback uses the function as written, which
stays total. So one definition serves both kinds of callback, and the core never has a type
that ranges over them.  `[spec §14]` -/

mutual
/-- The calls `h V` of a named function in a value. -/
def _root_.Frontend.Val.calls : Val → List (String × Val)
  | .app _ (.var _ h) V => (h, V) :: V.calls
  | .pair _ V W | .app _ V W => V.calls ++ W.calls
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => V.calls
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => M.calls
  | _ => []

/-- The calls `h V` of a named function in a computation. -/
def _root_.Frontend.Comp.calls : Comp → List (String × Val)
  | .ret _ V | .absurd _ V => V.calls
  | .bind _ _ _ M N _ | .with_ _ M N => M.calls ++ N.calls
  | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
  | .nuOut _ M | .ascribe _ M _ => M.calls
  | .letUnit _ V M | .letPair _ _ _ V M => V.calls ++ M.calls
  | .case _ V _ M _ N => V.calls ++ M.calls ++ N.calls
  | .for_ _ _ V M N => V.calls ++ M.calls ++ N.calls
  | .force .. | .top _ => []
end

mutual
/-- Rename the callee of each call `h V` that `f` names a copy for. -/
def _root_.Frontend.Val.renameCalls (f : String → Val → Option String) : Val → Val
  | .app sp (.var sp' h) V =>
    let V' := V.renameCalls f
    .app sp (.var sp' ((f h V').getD h)) V'
  | .pair sp V W => .pair sp (V.renameCalls f) (W.renameCalls f)
  | .app sp V W => .app sp (V.renameCalls f) (W.renameCalls f)
  | .inl sp V => .inl sp (V.renameCalls f)
  | .inr sp V => .inr sp (V.renameCalls f)
  | .unbang sp V => .unbang sp (V.renameCalls f)
  | .boxed sp l V => .boxed sp l (V.renameCalls f)
  | .unbox sp V => .unbox sp (V.renameCalls f)
  | .sub sp V l => .sub sp (V.renameCalls f) l
  | .roll sp V => .roll sp (V.renameCalls f)
  | .unroll sp V => .unroll sp (V.renameCalls f)
  | .inst sp V l => .inst sp (V.renameCalls f) l
  | .ascribe sp V A => .ascribe sp (V.renameCalls f) A
  | .shorten sp m σ l V => .shorten sp m σ l (V.renameCalls f)
  | .thunk sp M => .thunk sp (M.renameCalls f)
  | .thunkv sp M => .thunkv sp (M.renameCalls f)
  | .bangThunk sp M => .bangThunk sp (M.renameCalls f)
  | .bangThunkv sp M => .bangThunkv sp (M.renameCalls f)
  | .run sp M => .run sp (M.renameCalls f)
  | V => V

def _root_.Frontend.Comp.renameCalls (f : String → Val → Option String) : Comp → Comp
  | .ret sp V => .ret sp (V.renameCalls f)
  | .absurd sp V => .absurd sp (V.renameCalls f)
  | .bind sp x A M N lin => .bind sp x A (M.renameCalls f) (N.renameCalls f) lin
  | .lam sp x A M => .lam sp x A (M.renameCalls f)
  | .app sp M x => .app sp (M.renameCalls f) x
  | .with_ sp M N => .with_ sp (M.renameCalls f) (N.renameCalls f)
  | .proj sp i M => .proj sp i (M.renameCalls f)
  | .letUnit sp V M => .letUnit sp (V.renameCalls f) (M.renameCalls f)
  | .letPair sp x y V M => .letPair sp x y (V.renameCalls f) (M.renameCalls f)
  | .case sp V x M y N => .case sp (V.renameCalls f) x (M.renameCalls f) y (N.renameCalls f)
  | .lamL sp x b M => .lamL sp x b (M.renameCalls f)
  | .inst sp M a => .inst sp (M.renameCalls f) a
  | .nuIn sp M => .nuIn sp (M.renameCalls f)
  | .nuOut sp M => .nuOut sp (M.renameCalls f)
  | .ascribe sp M C => .ascribe sp (M.renameCalls f) C
  | .for_ sp x V M N => .for_ sp x (V.renameCalls f) (M.renameCalls f) (N.renameCalls f)
  | M => M
end

/-- `A => B` (`false`) or `!(A => B)` (`true`). -/
def fnShape : VTy → Option Bool
  | .lolli .. => some false
  | .bang _ (.lolli ..) => some true
  | _ => none

/-- The parameter type at which a call passes `V` to a parameter of type `P`: where a component
of `V` names a div function and `P` has a function type of the same shape there that is not
div, the div function's type. `none` when the call needs no copy. The recursion is bounded by
the depth `n` of the tuple, so the checker's own evaluation in the kernel can run it. -/
def specParamN (ds : Divs) : Nat → VTy → Val → Option VTy
  | n + 1, .tensor sp P Q, .pair _ V W =>
    match specParamN ds n P V, specParamN ds n Q W with
    | none, none => none
    | a, b => some (.tensor sp (a.getD P) (b.getD Q))
  | _, P, .var _ g =>
    match fnShape P, loopSig P, ds.lookup g with
    | some b, none, some T => if fnShape T == some b then some T else none
    | _, _, _ => none
  | _, _, _ => none

def specParam (ds : Divs) (P : VTy) (V : Val) : Option VTy := specParamN ds 64 P V

/-- A higher-order function as written: `def h : P => Q = thunkv fun (x : P) -> M`. -/
structure Hof where
  sp : Span
  name : Ident
  P : VTy
  Q : VTy
  x : Ident
  M : Comp

/-- The latest source `def` named `h`, when it is a function without type parameters. -/
def hofOf (srcs : List Decl) (h : String) : Option Hof :=
  match srcs.find? (fun | .def_ _ n _ _ _ _ => n.name == h | _ => false) with
  | some (.def_ sp n [] (.lolli _ P Q) (.thunkv _ (.lam _ x _ M)) _) => some ⟨sp, n, P, Q, x, M⟩
  | _ => none

/-- The elaboration so far: the source declarations in scope, newest first; the elaborated
ones, in order; the div functions; whether any body became a loop; and the copies made, by
function and parameter type. -/
structure DivSt where
  srcs : List Decl := []
  out : List Decl := []
  ds : Divs := []
  any : Bool := false
  copies : List ((String × VTy) × String) := []

def _root_.Frontend.Decl.calls : Decl → List (String × Val)
  | .def_ _ _ _ _ V _ => V.calls
  | .main _ _ M => M.calls
  | _ => []

/-- The copy of `h` a call `h V` names, if one was made. -/
def DivSt.copyFor (st : DivSt) (h : String) (V : Val) : Option String := do
  let hof ← hofOf st.srcs h
  let P' ← specParam st.ds hof.P V
  st.copies.lookup (h, P'.strip)

/-- Elaborate one declaration: first the copies its calls need (each elaborated the same way),
then its own divergence, with its calls renamed to the copies.  `[spec §14]` -/
def elabDecl : Nat → DivSt → Decl → Except Error DivSt
  | 0, _, d => throw ⟨(match d with | .def_ sp .. | .main sp .. => sp | _ => Span.none),
      "specialization at callback types does not terminate"⟩
  | fuel + 1, st, d => do
    let st ← d.calls.foldlM (init := st) fun st (h, V) => do
      let some hof := hofOf st.srcs h | pure st
      let some P' := specParam st.ds hof.P V | pure st
      if (st.copies.lookup (h, P'.strip)).isSome then return st
      let name := s!"{h}__{st.copies.length}"
      let copy := Decl.def_ hof.sp ⟨name, hof.name.span⟩ [] (.lolli hof.P.span P' hof.Q)
        (.thunkv hof.sp (.lam hof.sp hof.x P' hof.M)) .none
      elabDecl fuel { st with copies := ((h, P'.strip), name) :: st.copies } copy
    let d := match d with
      | .def_ sp n ps A V mk => Decl.def_ sp n ps A (V.renameCalls st.copyFor) mk
      | .main sp C M => .main sp C (M.renameCalls st.copyFor)
      | d => d
    let (d', e) ← elabDef st.ds d
    let elaborated := match d, e with
      | .def_ _ _ _ A _ _, some _ => (loopSig A).isNone
      | _, _ => false
    pure { st with srcs := d :: st.srcs, out := st.out ++ [d'], ds := e.toList ++ st.ds,
                   any := st.any || elaborated }

/-- The declarations with divergence inferred, in order (copies before their first use), the
div functions, and whether any body was elaborated as a loop. -/
def elabDivs (decls : List Decl) : Except Error (List Decl × Divs × Bool) := do
  let st ← decls.foldlM (init := ({} : DivSt)) (elabDecl (4 * decls.length + 4))
  pure (st.out, st.ds, st.any)

/-- A `main` that is not ambient, elaborated as a loop when its body loops. -/
def plainMain (ds : Divs) (sp : Span) (C : CTy) (M : Comp) : Except Error (CTy × Comp) := do
  if C.returnsLoop then return (C, M)
  match C, loopsAt ds [] M with
  | .ret _ B, some _ =>
    let cx ← loopCxOf ds sp B M
    pure (.ret sp (.thunk sp (.loop sp B cx.R)), ← loopBody cx [] M)
  | _, some (sp', what) =>
    throw ⟨sp', s!"`main` loops ({what}), so its type is written `F A` (SPEC §14)"⟩
  | _, none => pure (C, M)

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

/-- A program uses the library function `n` without defining it. -/
def usesName (n : String) (p : Program) : Bool :=
  p.decls.any (fun | .def_ _ _ _ _ V _ => V.names n | .main _ _ M => M.names n | _ => false) &&
    !(p.decls.any fun | .def_ _ m _ _ _ _ => m.name == n | _ => false)

/-- The program with its sugar elaborated, and the number of library declarations it begins
with.  `[spec §11, §14]` -/
def elaborate (p : Program) : Except Error (Program × Nat) := do
  -- Divergence of the user's definitions, before the libraries (which do not loop) come in.
  let (decls, ds, anyDiv) ← elabDivs p.decls
  let mainLoops := match decls.findSome? (fun | .main _ C M => some (C, M) | _ => none) with
    | some (C@(.ret _ _), M) => !C.returnsLoop && (loopsAt ds [] M).isSome
    | _ => false
  let cs := ambientCaps p mainLoops
  let needDiv := anyDiv || mainLoops || usesName "div_fuel" p || usesName "div_bind" p
  let libOf (name src : String) : Except Error (List Decl) :=
    match parseProgram src with
    | .ok l => pure l.decls
    | .error e => throw ⟨e.span, s!"{name}: {e.msg}"⟩
  let ioLib ← if cs.isEmpty then pure [] else libOf "lib/io.bc" ioLibrary
  let divLib ← if needDiv then libOf "lib/div.bc" divLibrary else pure []
  let rest := decls.filter fun | .main .. => false | _ => true
  let exts := cs.map fun c => Decl.extern Span.none ⟨c, Span.none⟩ (capTy Span.none c)
  let mains ← decls.filterMapM fun
    | .main sp C M => do
      let (C', M') ← if cs.isEmpty then plainMain ds sp C M else ambientMain ds cs sp C M
      pure (some (Decl.main sp C' M'))
    | _ => pure none
  let lib := ioLib ++ divLib
  let decls ← (lib ++ rest ++ exts ++ mains).mapM fun
    | .def_ sp n ps A V mk => return .def_ sp n ps A (← V.elab false) mk
    | .main sp C M => return .main sp C (← M.elab false)
    | d => pure d
  pure (⟨decls⟩, lib.length)

end Frontend.Sugar
