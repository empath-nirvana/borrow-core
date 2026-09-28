import Frontend.Parser
import Frontend.Print
import Frontend.Check.Steps

/-!
# Frontend — the I/O sugar  `[spec §11]`

Three forms, each elaborated here into ordinary core syntax before checking. The checker, the
kernel and the theorems never see them: what they check is a program a user could have written
by hand (`bcc desugar` prints it).

* **Ambient capabilities in `main`.** A program that declares no externs and whose `main`
  mentions `stdin`, `stdout` or `stderr` gets the I/O library (`lib/io.bc`), which declares the
  operations, and an `extern` for each capability it mentions, in the order `stdin`, `stdout`,
  `stderr`. `main : F A` becomes `main : F (Caps * A)`: each terminal `return V` of its body
  becomes `return (caps, V)`, and any other terminal `T` becomes `r <- T; return (caps, r)`,
  with the capabilities read by name where the path ends (`wrapTail`).
* **`for (x : A) in V with (y : T, …) { M }; N`** at the end of such a `main` becomes a loop by
  `unfold` over the state (iterator, other capabilities, listed variables), and `main : F A`
  becomes `main : F (U (loop (Caps * A) (Caps * 1)))` (`forLoop`).
* **`&c`** in the head of `x <- M; N` becomes `r <- M[c/&c]; let (c, x) = r; N` (`Comp.elab`).

The generated code is a template, printed and parsed, whose holes are filled with the program's
own syntax, so errors inside the program's code keep its positions.
-/

namespace Frontend.Sugar
open Frontend.Check (mentionsV mentionsC)

/-- The I/O library, `lib/io.bc`. -/
def ioLibrary : String := include_str "../lib/io.bc"

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
  | .for_ sp x V M N => return .for_ sp x (← V.elab false) (← M.elab false) (← N.elab false)
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
or a `let`, and both arms of a `case`. -/
def wrapTail (f : Comp → Comp) : Comp → Comp
  | .bind sp x A M N lin => .bind sp x A M (wrapTail f N) lin
  | .letUnit sp V M => .letUnit sp V (wrapTail f M)
  | .letPair sp x y V M => .letPair sp x y V (wrapTail f M)
  | .case sp V x M y N => .case sp V x (wrapTail f M) y (wrapTail f N)
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

/-- The capabilities a program uses ambiently: none if it declares an extern. -/
def ambientCaps (p : Program) : List String :=
  if p.decls.any (fun | .extern .. => true | _ => false) then [] else
  match p.decls.findSome? (fun | .main _ _ M => some M | _ => none) with
  | some M => capNames.filter (mentionsC · M)
  | none => []

/-- A `for` at the end of `main`: its position, element, iterator, body and what follows. -/
abbrev ForNode := Span × Ident × Val × Comp × Comp

/-- The prefix of `main`'s body before a `for`, the variables the prefix binds (with their
types where the binding gives one), and the `for`. -/
def splitFor : Comp → Option ((Comp → Comp) × List (String × Option VTy) × ForNode)
  | .bind sp x A M N lin => (splitFor N).map fun (k, bs, f) =>
      (fun c => .bind sp x A M (k c) lin, (x.name, A) :: bs, f)
  | .letUnit sp V M => (splitFor M).map fun (k, bs, f) => (fun c => .letUnit sp V (k c), bs, f)
  | .letPair sp x y V M => (splitFor M).map fun (k, bs, f) =>
      (fun c => .letPair sp x y V (k c), (x.name, none) :: (y.name, none) :: bs, f)
  | .for_ sp x V M N => some (id, [], (sp, x, V, M, N))
  | _ => none

/-- Parse the computation `src` as a `main` body. -/
def parseComp (src : String) : Except Error Comp := do
  let p ← parseProgram ("main : F 1 =\n" ++ src)
  match p.decls.findSome? (fun | .main _ _ M => some M | _ => none) with
  | some M => pure M
  | none => throw ⟨Span.none, "internal error: a template without main"⟩

/-- The loop a `for` at the end of `main` elaborates to, and `main`'s new type. The state is the
iterator, the capabilities other than the one it holds, and the variables of the prefix `bs`
that the body or what follows mentions, each at the type its binding gives it.
`[spec §11]` -/
def forLoop (cs : List String) (A : VTy) (bs : List (String × Option VTy)) (f : ForNode) :
    Except Error (Comp × CTy) := do
  let (sp, x, V, M, N) := f
  let Ax : VTy ← match V with
    | .app _ (.var _ "bytes") _ => pure (.int sp .w32)
    | _ => throw ⟨V.span, "`for` iterates over `bytes c`, the input `c` as a stream of bytes"⟩
  -- The last binding of each name, in binding order.
  let latest := bs.foldl (fun acc (y, T) => (acc.filter (·.1 != y)) ++ [(y, T)]) []
  let used := latest.filter fun (y, _) =>
    !cs.contains y && y != x.name && (mentionsC y M || mentionsC y N)
  let ws ← used.mapM fun (y, T) => match T with
    | some T => pure ((⟨y, sp⟩ : Ident), T)
    | none => throw ⟨sp, s!"the loop threads `{y}`: bind it with its type, `{y} : T <- …;`"⟩
  let iterated := cs.filter (mentionsV · V)
  let c ← match iterated with
    | [c] => pure c
    | _ => throw ⟨V.span, "the iterator of a `for` must be made from one capability, which it " ++
        "hands back at its end"⟩
  let th := cs.filter (· != c)
  let sv := th ++ ws.map (·.1.name)
  let svTy := th.map capTySrc ++ ws.map (·.2.pp)
  let caps := tupleSrc cs
  let capsT := tupleTySrc (cs.map capTySrc)
  let a := A.pp
  let st := s!"U (iter ({Ax.pp}) ({capTySrc c}) ({capTySrc c})) * {tupleTySrc svTy}"
  let fin := s!"({capsT} * ({a}))"
  let fin' := s!"({capsT} * 1)"
  let ds := destructSrc "io_st" sv
  let xn := x.name
  let src := s!"io_step : !U ({st} -o F ({fin} + ({st})) & F {fin'}) <- return (!thunkv fun (io_s : {st}) ->
  < let (io_it, io_st) = io_s;
    {ds}    io_o <- (nu_out (force io_it)).1;
    case io_o \{
      inl io_p ->
        let ({xn}, io_it) = io_p;
        force io_hole_body
    | inr io_c ->
        {c} <- return io_c;
        force io_hole_fin
    },
    let (io_it, io_st) = io_s;
    {ds}    io_c <- (nu_out (force io_it)).2;
    {c} <- return io_c;
    return ({caps}, ()) >);
io_f <- return (unbang (unfold[loop {fin} {fin'}, {st}] io_step));
io_s0 : {st} <- return (io_hole_v, {tupleSrc sv});
return (thunkv nu_in < (nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2 >)
"
  let T ← match parseComp src with
    | .ok T => pure T
    | .error e => throw ⟨sp, s!"internal error in `for`: {e.render}"⟩
  let body := wrapTail (fun T => .bind T.span ⟨"io_u", T.span⟩ none T
      (.ret T.span (.inr T.span (.pair T.span (.var T.span "io_it") (tupleVal T.span sv)))) false) M
  let finish := wrapTail (fun
      | .ret sp V => if V.takeLends.2.isEmpty then .ret sp (.inl sp (.pair sp (tupleVal sp cs) V))
          else .bind sp ⟨"io_v", sp⟩ none (.ret sp V)
            (.ret sp (.inl sp (.pair sp (tupleVal sp cs) (.var sp "io_v")))) false
      | T => .bind T.span ⟨"io_v", T.span⟩ none T
          (.ret T.span (.inl T.span (.pair T.span (tupleVal T.span cs) (.var T.span "io_v"))))
          false) N
  let T := T.fill (fun v => if v == "io_hole_v" then some V else none)
    (fun n => if n == "io_hole_body" then some body else if n == "io_hole_fin" then some finish
      else none)
  let C ← match parseProgram s!"main : F (U (loop {fin} {fin'})) = return ()" with
    | .ok p => match p.decls.findSome? (fun | .main _ C _ => some C | _ => none) with
      | some C => pure C
      | none => throw ⟨sp, "internal error: `for`"⟩
    | .error e => throw ⟨sp, s!"internal error in `for`: {e.render}"⟩
  pure (T, C)

/-- `main` with ambient capabilities, elaborated: its new type and body.  `[spec §11]` -/
def ambientMain (cs : List String) (sp : Span) (C : CTy) (M : Comp) : Except Error (CTy × Comp) := do
  let A ← match C with
    | .ret _ A => pure A
    | _ => throw ⟨C.span, "a `main` that uses the capabilities ambiently has type `F A`"⟩
  match splitFor M with
  | some (k, bs, f) =>
    let (L, C') ← forLoop cs A bs f
    pure (C', k L)
  | none =>
    let capsV := tupleVal sp cs
    let M' := wrapTail (fun
        | .ret sp V => if V.takeLends.2.isEmpty then .ret sp (.pair sp capsV V)
            else .bind sp ⟨"io_r", sp⟩ none (.ret sp V) (.ret sp (.pair sp capsV (.var sp "io_r")))
              false
        | T => .bind T.span ⟨"io_r", T.span⟩ none T
            (.ret T.span (.pair T.span capsV (.var T.span "io_r"))) false) M
    pure (.ret sp (.tensor sp (tupleTy sp (cs.map (capTy sp))) A), M')

/-- The program with its sugar elaborated, and the number of library declarations it begins
with.  `[spec §11]` -/
def elaborate (p : Program) : Except Error (Program × Nat) := do
  let cs := ambientCaps p
  let (p, k) ← if cs.isEmpty then pure (p, 0) else do
    let lib ← match parseProgram ioLibrary with
      | .ok l => pure l
      | .error e => throw ⟨e.span, s!"lib/io.bc: {e.msg}"⟩
    let rest := p.decls.filter fun | .main .. => false | _ => true
    let exts := cs.map fun c => Decl.extern Span.none ⟨c, Span.none⟩ (capTy Span.none c)
    let mains ← p.decls.filterMapM fun
      | .main sp C M => do
        let (C', M') ← ambientMain cs sp C M
        pure (some (Decl.main sp C' M'))
      | _ => pure none
    pure (⟨lib.decls ++ rest ++ exts ++ mains⟩, lib.decls.length)
  let decls ← p.decls.mapM fun
    | .def_ sp n ps A V => return .def_ sp n ps A (← V.elab false)
    | .main sp C M => return .main sp C (← M.elab false)
    | d => pure d
  pure (⟨decls⟩, k)

end Frontend.Sugar
