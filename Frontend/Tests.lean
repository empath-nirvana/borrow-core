import Frontend.Parser
import Frontend.Print
/-!
# Frontend — Tests

Small cases of the parser and of the round-trip property `(parse (print t)).strip = t.strip`,
checked by the kernel (`decide +kernel`: the kernel evaluates the lexer, the parser and the
printer; no `native_decide`). The corpus (`scripts/parse-corpus.sh`) checks the same property
on whole programs by running `bcc parse`.
-/

namespace Frontend.Tests

open Frontend

/-- `s` parses to `t` up to spans. -/
def parsesTo {α} [BEq α] (p : String → Except Error α) (strip : α → α) (s : String) (t : α) :
    Bool :=
  match p s with
  | .ok a => strip a == t
  | .error _ => false

/-- `s` parses, and printing and re-parsing the result gives it back up to spans. -/
def roundTrips {α} [BEq α] (p : String → Except Error α) (strip : α → α) (pp : α → String)
    (s : String) : Bool :=
  match p s with
  | .ok a => match p (pp a) with
    | .ok b => strip b == strip a
    | .error _ => false
  | .error _ => false

def rejects {α} (p : String → Except Error α) (s : String) : Bool :=
  match p s with
  | .ok _ => false
  | .error _ => true

private def n : Span := .none

/-! ### Precedence (syntax-core §4, §6.5) -/

/-- `S -o F (A + S) & F 1` is `S -o ((F (A + S)) & (F 1))`. -/
theorem prec_amp :
    parsesTo parseCTy CTy.strip "S -o F (A + S) & F 1"
      (.arr n (.name n "S") (.amp n (.ret n (.sum n (.name n "A") (.name n "S"))) (.ret n (.unit n))))
      = true := by decide +kernel

/-- `imm 'a Nat * Nat` is `(imm 'a Nat) * Nat`. -/
theorem prec_imm :
    parsesTo parseVTy VTy.strip "imm 'a Nat * Nat"
      (.tensor n (.imm n (.var n "a") (.name n "Nat")) (.name n "Nat")) = true := by
  decide +kernel

/-- `F A * B` is a sort error. -/
theorem sort_error : rejects parseVTy "F A * B" = true := by decide +kernel

/-- `force f s .1` is `((force f) s).1`. -/
theorem prec_spine :
    parsesTo parseComp Comp.strip "force f s .1"
      (.proj n true (.app n (.force n ⟨"f", n⟩) ⟨"s", n⟩)) = true := by decide +kernel

/-- `roll inr n` is `roll (inr n)`. -/
theorem prec_prefix :
    parsesTo parseVal Val.strip "roll inr n" (.roll n (.inr n (.var n "n"))) = true := by
  decide +kernel

/-- `f['y]` is a `def` at a type argument; `f ['y]` is an instantiation. -/
theorem brackets :
    parsesTo parseVal Val.strip "f [top] x"
      (.app n (.inst n (.var n "f") (.top n)) (.var n "x")) = true ∧
    parsesTo parseVal Val.strip "f[A]" (.defApp n "f" [.name n "A"]) = true := by
  decide +kernel

/-- `'a /\ 'b \/ top` is `('a /\ 'b) \/ top`. -/
theorem prec_life :
    parsesTo parseVTy VTy.strip "box ('a /\\ 'b \\/ top) 1"
      (.box n (.join n (.meet n (.var n "a") (.var n "b")) (.top n)) (.unit n)) = true := by
  decide +kernel

/-! ### Round trips -/

theorem rt_val : roundTrips parseVal Val.strip (Val.pp · 0 0)
    "roll (inr (x, boxed['a] (unbang f) ['b] y))" = true := by decide +kernel

theorem rt_comp : roundTrips parseComp Comp.strip (Comp.pp · 0 0)
    "x <- (force f).1; case x { inl u -> return u | inr v -> < return v, <> > }" = true := by
  decide +kernel

theorem rt_ty : roundTrips parseVTy VTy.strip (VTy.pp · 0)
    "!U (Nat -o F (all 'y < top. imm 'y Nat => Nat) & top) * mu X. 1 + ref X" = true := by
  decide +kernel

theorem rt_array : roundTrips parseVTy VTy.strip (VTy.pp · 0)
    "array (ref i32) * array_imm 'a i32 => ref array i32" = true := by
  decide +kernel

theorem rt_program : roundTrips parseProgram Program.strip Program.pp
    "type Nat = mu X. 1 + X
     shape Node = node (leaf Nat) (leaf (ref Nat))
     def one : Nat = roll (inr (roll (inl ())))
     def id[A] : A => A = thunkv fun (x : A) -> return x
     extern e : !(1 => 1)
     main : F Nat = r <- return (alloc_s[Node] (one, alloc[Nat] one)); let (a, b) = r; return (id[Nat] a)"
    = true := by decide +kernel

/-- A declaration with fields marked `must_close` (SPEC §42). -/
theorem rt_decl : roundTrips parseProgram Program.strip Program.pp
    "data Txn = { id: i32, must_close(commit) log: i32 }
     data Lock = Held(must_close i32) | Free
     main : F 1 = return ()"
    = true := by decide +kernel


/-! ### The new spelling (SPEC §82): each form parses to today's tree, and today's surface forms are refused  `[spec §82]` -/

/-- The text `nw`, in the new spelling (SPEC §82) after its pragma, parses to the program the text
`old` in today's spelling does, up to spans. -/
def sameProgram (old nw : String) : Bool :=
  match parseProgram old, parseProgram ("#! dialect 82\n" ++ nw) with
  | .ok p, .ok q => p.strip == q.strip
  | _, _ => false

/-- The new-spelling text `nw` is refused. -/
def ndRejects (nw : String) : Bool :=
  match parseProgram ("#! dialect 82\n" ++ nw) with
  | .ok _ => false
  | .error _ => true

theorem nd_pragma : isNewDialect "#! dialect 82\nfn" = true ∧ isNewDialect "#! dialect 821" = false
    := by decide +kernel

-- Comments; statements end at a newline; a line that starts with a binary operator continues.
theorem nd_layout : sameProgram "main -> i32 = let a = 1; a * 3"
    "# c\nfn main() : i32 {\n  let a = 1 # d\n  a\n    * 3\n}" = true := by decide +kernel

-- Arms one per line, a block's statements, `var` and assignment.
theorem nd_arms : sameProgram "main -> i32 = let mut y = 0; match 1 { 0 -> 5 | k -> y = k; y }"
    "fn main() : i32 {\n  var y = 0\n  match 1 {\n    0 -> 5\n    k -> { y = k; y }\n  }\n}" = true
    := by decide +kernel

-- A header's row, `let x = M` for a computation, an effect and an answering handler.
theorem nd_fn : sameProgram
    "effect E { fn op() -> i32 }\nhandler h(mut s: i32): E = { op() = s }\nfn f() -> i32 with E = z <- force g; z"
    "effect E { op() : i32 }\nhandler h(mut s: i32) : E { op() -> s }\nfn f() : i32 / E {\n  let z = force g\n  z\n}" = true
    := by decide +kernel

-- `handle { … } with h(e) as n finally { … }`, and a trailing block.
theorem nd_handle : sameProgram "main -> i32 = with n = h(1) { ap(2, { y -> y }) } finally { () }"
    "fn main() : i32 = handle { ap(2) { y -> y } } with h(1) as n finally { () }" = true
    := by decide +kernel

-- Modes: a bare `array i32` is a lend of a fresh region, `inout` a mutable one (the fresh
-- lifetimes are named as the parser names them); `&x` is today's `&mut x`.
theorem nd_modes : sameProgram
    ("fn f<'io_lf0>(l: array_imm 'io_lf0 i32) -> i32 = 0\n" ++
     "fn g<'io_lf1>(m: array_mut 'io_lf1 i32) -> i32 = 0\nmain -> i32 = modify &mut a { v -> v }")
    "fn f(l: array i32) : i32 = 0\nfn g(m: inout array i32) : i32 = 0\nfn main() : i32 = modify &a { v -> v }"
    = true := by decide +kernel

-- Hazards of the layout rule: a line that starts with `&` begins a statement, a line-leading `|`
-- separates arms, a label alone on its line joins the next, a call's `{` in the head of `if` is
-- the `if`'s, `x = M` for a computation assigns.
theorem nd_hazards : sameProgram
    ("main -> i32 = let mut a = 0; 'l: for i in 0..3 { () }; a <- force g; " ++
     "let b = match 1 { 0 -> 5 | k -> k }; let c = if f(a) { 1 } else { 2 }; &mut a")
    ("fn main() : i32 {\n  var a = 0\n  'l:\n  for i in 0..3 { () }\n  a = force g\n" ++
     "  let b = match 1 {\n    0 -> 5\n    | k -> k\n  }\n  let c = if f(a) { 1 } else { 2 }\n  &a\n}")
    = true := by decide +kernel

-- A line starting with `.` continues the statement before it.
theorem nd_dot : sameProgram "data P = { f: i32 }\nmain -> i32 = let q = P { f: 1 }; let y = q.f; y"
    "data P = { f: i32 }\nfn main() : i32 {\n  let q = P { f: 1 }\n  let y = q\n    .f\n  y\n}" = true
    := by decide +kernel

-- An arm's `-> { S }` is its statements, `-> ({ S })` the block value.
theorem nd_block_arm : sameProgram "main -> i32 = match 1 { _ -> { 5 } }"
    "fn main() : i32 = match 1 { _ -> ({ 5 }) }" = true ∧
    sameProgram "main -> i32 = match 1 { _ -> let x = 5; x }"
    "fn main() : i32 = match 1 { _ -> { let x = 5; x } }" = true := by decide +kernel

-- A body without braces ends at a newline at its own nesting, also inside a `fun` it ends with:
-- an arm's, a clause's and a `= e` body.
theorem nd_one_expr : sameProgram
    ("effect E { fn op() -> i32; fn op2() -> i32 }\n" ++
     "handler h(mut s: i32): E = { op() = (!thunkv fun (x : i32) -> return x); op2() = s }\n" ++
     "fn g() -> i32 = !thunkv fun (x : i32) -> return x\n" ++
     "main -> i32 = match 1 { 0 -> !thunkv fun (x : i32) -> return x | k -> k }")
    ("effect E { op() : i32; op2() : i32 }\n" ++
     "handler h(mut s: i32) : E {\n  op() -> !thunkv fun (x : i32) -> return x\n  op2() -> s\n}\n" ++
     "fn g() : i32 = !thunkv fun (x : i32) -> return x\n" ++
     "fn main() : i32 = match 1 {\n  0 -> !thunkv fun (x : i32) -> return x\n  k -> k\n}")
    = true := by decide +kernel

-- Inside `(…)` a newline does not end a statement; a block `{ … }` there (of `if`, `match`, a
-- closure) has the layout rule again.
theorem nd_paren_block : sameProgram
    ("main -> i32 = let a = f(1,\n 2); f(if c { let a = 1; a } else { 2 }, " ++
     "match 1 { 0 -> 1 | k -> k }, { y -> let z = y; z })")
    ("fn main() : i32 {\n  let a = f(1,\n    2)\n  f(if c {\n    let a = 1\n    a\n  } else { 2 }, " ++
     "match 1 {\n    0 -> 1\n    k -> k\n  }, { y ->\n    let z = y\n    z\n  })\n}")
    = true := by decide +kernel

/-- The new-spelling text `nw` is refused with the message `msg`. -/
def ndRejectsWith (nw msg : String) : Bool :=
  match parseProgram ("#! dialect 82\n" ++ nw) with
  | .ok _ => false
  | .error e => e.msg == msg

-- Refused in the new spelling: today's surface forms.
theorem nd_refused :
    ndRejects "fn main() : i32 {\n  x <- return 1\n  x\n}" = true ∧
    ndRejects "fn main() : i32 = let mut x = 1; x" = true ∧
    ndRejects "fn main() : i32 = modify &mut x { v -> v }" = true ∧
    ndRejects "main -> i32 = 1" = true ∧
    ndRejectsWith "fn main() : i32 = modify &mut x { v -> v }"
      "`&mut x` is written `&x` in the new spelling (SPEC §82 P7)" = true ∧
    ndRejectsWith "fn main() : i32 {\n  x <- return 1\n  x\n}"
      "`x <- M` is written `let x = M` in a surface body of the new spelling (SPEC §82 E2)" = true
    := by decide +kernel

end Frontend.Tests
