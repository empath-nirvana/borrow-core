import Std.Data.HashMap
import Support.Dynamics.Host
import Support.Dynamics.Arrays
import Backend.Value
import Backend.Clos.Syntax

/-!
# Backend — closure-IR interpreter

A fuelled interpreter for the closure IR over an explicit heap of objects (pairs, injections,
closures, boxed `i64`s, cells), counting live objects, with a scripted standard input and
collected standard output and error for the I/O operations (SPEC §11). An array is consecutive cells, as in the
source machine (SPEC §9). This is the uniform boxed representation, independent of the layout
types the flat IR uses (`Backend/Clos/Types.lean`). It checks the ownership discipline as it
runs: using a variable consumes it, a consumed variable cannot be used again, and a call or
`main` must end with every variable of its frame consumed. Host operations go through
`Host.call` at `wasmHost`, as in the source interpreter.
-/

namespace Backend.Clos
open BoCa

/-- A word: an immediate or a heap address. -/
inductive CV where
  | unit
  | i32 (n : UInt32)
  | u8 (n : UInt8)
  | ptr (a : Nat)
  deriving Repr, BEq, Inhabited

inductive Obj where
  | pair (a b : CV)
  | inj (right : Bool) (a : CV)
  | clos (code : Nat) (env : List CV)
  | i64 (n : UInt64)
  | cell (v : CV)
  deriving Repr, Inhabited

structure St where
  heap : Std.HashMap Nat Obj
  next : Nat
  /-- The standard input not yet read. -/
  input : List UInt8
  out : ByteArray
  err : ByteArray

abbrev IM := StateT St (Except String)

abbrev Env := List (Var × CV)

def allocObj (o : Obj) : IM CV := do
  let s ← get
  set { s with heap := s.heap.insert s.next o, next := s.next + 1 }
  pure (.ptr s.next)

def getObj (a : Nat) : IM Obj := do
  match (← get).heap[a]? with
  | some o => pure o
  | none => throw s!"closure IR: dangling address {a}"

def freeObj (a : Nat) : IM Unit := do
  let _ ← getObj a
  modify fun s => { s with heap := s.heap.erase a }

def setObj (a : Nat) (o : Obj) : IM Unit :=
  modify fun s => { s with heap := s.heap.insert a o }

/-- Consume `x` from the frame. -/
def take (env : Env) (x : Var) : IM (CV × Env) :=
  match env.lookup x with
  | some v => pure (v, env.filter (·.1 != x))
  | none => throw s!"closure IR: variable {x} used after it was consumed, or unbound"

def takeAll (env : Env) : List Var → IM (List CV × Env)
  | [] => pure ([], env)
  | x :: xs => do
    let (v, env) ← take env x
    let (vs, env) ← takeAll env xs
    pure (v :: vs, env)

/-- Deep copy: structure is copied, cells are shared (a location is copied as a word). Address
    `0` is never an object: it is the null base of the empty family. -/
def deepCopy : Nat → CV → IM CV
  | 0, _ => throw "closure IR: out of fuel"
  | n + 1, v => do
    match v with
    | .ptr 0 => pure v
    | .ptr a =>
      match ← getObj a with
      | .pair x y => do let x ← deepCopy n x; let y ← deepCopy n y; allocObj (.pair x y)
      | .inj r x => do let x ← deepCopy n x; allocObj (.inj r x)
      | .clos c xs => do let xs ← xs.mapM (deepCopy n); allocObj (.clos c xs)
      | .i64 k => allocObj (.i64 k)
      | .cell _ => pure v
    | _ => pure v

/-- Deep free: structure is freed, cells are not. -/
def deepDrop : Nat → CV → IM Unit
  | 0, _ => throw "closure IR: out of fuel"
  | n + 1, v => do
    match v with
    | .ptr 0 => pure ()
    | .ptr a =>
      match ← getObj a with
      | .pair x y => do deepDrop n x; deepDrop n y; freeObj a
      | .inj _ x => do deepDrop n x; freeObj a
      | .clos _ xs => do xs.forM (deepDrop n); freeObj a
      | .i64 _ => freeObj a
      | .cell _ => pure ()
    | _ => pure ()

/-- The source value a word denotes (for host operations). -/
def toSource : Nat → CV → IM Val
  | 0, _ => throw "closure IR: out of fuel"
  | n + 1, v => do
    match v with
    | .unit => pure .unit
    | .i32 k => pure (.i32 k)
    | .u8 k => pure (.u8 k)
    | .ptr a =>
      match ← getObj a with
      | .pair x y => do pure (.pair (← toSource n x) (← toSource n y))
      | .inj false x => do pure (.inj₁ (← toSource n x))
      | .inj true x => do pure (.inj₂ (← toSource n x))
      | .i64 k => pure (.i64 k)
      | _ => throw "closure IR: a host operation applied to a function or location"

/-- Allocate the representation of a data value. -/
def ofSource : Expr → IM CV
  | .unit => pure .unit
  | .prim (.lit (.i32 k)) => pure (.i32 k)
  | .prim (.lit (.i64 k)) => allocObj (.i64 k)
  | .prim (.lit (.u8 k)) => pure (.u8 k)
  | .pair a b => do let a ← ofSource a; let b ← ofSource b; allocObj (.pair a b)
  | .inj₁ a => do let a ← ofSource a; allocObj (.inj false a)
  | .inj₂ a => do let a ← ofSource a; allocObj (.inj true a)
  | _ => throw "closure IR: a host result that is not data"

def cellOf (v : CV) : IM (Nat × CV) := do
  match v with
  | .ptr a => match ← getObj a with
    | .cell c => pure (a, c)
    | _ => throw "closure IR: not a cell"
  | _ => throw "closure IR: not a cell"

def objFuel : Nat := 1 <<< 20

/-- Take a pair apart, freeing it. -/
def unpair (v : CV) : IM (CV × CV) := do
  match v with
  | .ptr a => match ← getObj a with
    | .pair x y => do freeObj a; pure (x, y)
    | _ => throw "closure IR: not a pair"
  | _ => throw "closure IR: not a pair"

/-- An array of `n` elements is `max n 1` consecutive cells (SPEC §9); the handle is
    `(base, i32[n])`. The extra cell of an empty array keeps the base an object. -/
def arrSlots (n : Nat) : Nat := max n 1

/-- Bytes written to the stream `fd`: `1` standard output, `2` standard error. -/
def emitBytes (fd : UInt32) (bs : List UInt8) : IM Unit :=
  match fd with
  | 1 => modify fun s => { s with out := bs.foldl ByteArray.push s.out }
  | 2 => modify fun s => { s with err := bs.foldl ByteArray.push s.err }
  | _ => throw "closure IR: a write to a stream that is not an output"

def applyOp : Op → List CV → IM CV
  | .alloc, [v] => allocObj (.cell v)
  | .free, [l] => do let (a, c) ← cellOf l; freeObj a; pure c
  | .load, [l] => do let (_, c) ← cellOf l; deepCopy objFuel c
  | .store, [l, v] => do
      let (a, c) ← cellOf l
      deepDrop objFuel c
      setObj a (.cell v)
      pure .unit
  | .swap, [l, v] => do
      let (a, c) ← cellOf l
      setObj a (.cell v)
      allocObj (.pair l c)
  | .host op, [v] => do
      let sv ← toSource objFuel v
      deepDrop objFuel v
      match wasmHost.call op sv with
      | some r => ofSource r.1
      | none => throw "closure IR: host operation stuck"
  | .idx, [v] => do
      let (arr, i) ← unpair v
      let (base, n) ← unpair arr
      match base, n, i with
      | .ptr a, .i32 n, .i32 i =>
        if i < n then allocObj (.inj false (.ptr (a + i.toNat)))
        else allocObj (.inj true .unit)
      | _, _, _ => throw "closure IR: idx of a non-array"
  | .split, [v] => do
      let (arr, i) ← unpair v
      let (base, n) ← unpair arr
      match base, n, i with
      | .ptr a, .i32 n, .i32 i =>
        if i ≤ n then
          -- An empty right part keeps the family's base, which is live or null.
          let r := if i < n then a + i.toNat else a
          let pl ← allocObj (.pair (.ptr a) (.i32 i))
          let pr ← allocObj (.pair (.ptr r) (.i32 (n - i)))
          allocObj (.inj false (← allocObj (.pair pl pr)))
        else allocObj (.inj true (← allocObj (.pair (.ptr a) (.i32 n))))
      | _, _, _ => throw "closure IR: split of a non-array"
  | .nullLoc, [] => pure (.ptr 0)
  | .io .readByte, [m] => do
      let (_, c) ← cellOf m
      let .i32 _ := c | throw "closure IR: read_byte on a cell that holds no stream"
      let s ← get
      match s.input with
      | [] => do allocObj (.pair m (← allocObj (.inj true .unit)))
      | b :: bs => do
        set { s with input := bs }
        allocObj (.pair m (← allocObj (.inj false (.u8 b))))
  | .io .writeByte, [p] => do
      let (m, w) ← unpair p
      let (_, c) ← cellOf m
      match c, w with
      | .i32 fd, .u8 b => do emitBytes fd [b]; pure m
      | _, _ => throw "closure IR: write_byte on a cell that holds no output stream"
  | .io .writeAll, [p] => do
      let (m, v) ← unpair p
      let (_, c) ← cellOf m
      let (base, n) ← unpair v
      match c, base, n with
      | .i32 fd, .ptr a, .i32 n => do
        let bs ← (List.range n.toNat).mapM fun i => do
          match ← cellOf (.ptr (a + i)) with
          | (_, .u8 b) => pure b
          | _ => throw "closure IR: write_all of a view whose slots are not bytes"
        emitBytes fd bs
        pure m
      | _, _, _ => throw "closure IR: write_all on a cell that holds no output stream"
  | .io .readInto, [p] => do
      let (m, v) ← unpair p
      let (_, c) ← cellOf m
      let (base, n) ← unpair v
      match c, base, n with
      | .i32 _, .ptr a, .i32 n => do
        let s ← get
        let bs := s.input.take n.toNat
        set { s with input := s.input.drop n.toNat }
        for (b, i) in bs.zipIdx do setObj (a + i) (.cell (.u8 b))
        let f ← allocObj (.pair (.ptr a) (.i32 n))
        allocObj (.pair m (← allocObj (.pair f (.i32 bs.length.toUInt32))))
      | _, _, _ => throw "closure IR: read_into on a cell that holds no stream"
  | _, _ => throw "closure IR: primitive arity"

mutual
/-- Call the closure `f` on `a`; the call frees `f`'s environment record. -/
def callClos (codes : Array Code) : Nat → CV → CV → IM CV
  | 0, _, _ => throw "closure IR: out of fuel"
  | n + 1, vf, va => do
    match vf with
    | .ptr p =>
      match ← getObj p with
      | .clos c vs => do
        freeObj p
        let some code := codes[c]? | throw "closure IR: bad code index"
        if code.env.length != vs.length then throw "closure IR: environment size"
        let frame := (code.param, va) :: code.env.zip vs
        let (r, rest) ← eval codes n frame code.body
        if !rest.isEmpty then
          throw s!"closure IR: code {c} leaves {rest.map (·.1)} unconsumed"
        pure r
      | _ => throw "closure IR: call of a non-closure"
    | _ => throw "closure IR: call of a non-closure"

/-- `tab`'s fill: cell `a + i` gets `f i`, for `i < k`, each call on a copy of `f`. -/
def tabFill (codes : Array Code) : Nat → CV → Nat → Nat → Nat → IM Unit
  | 0, _, _, _, _ => throw "closure IR: out of fuel"
  | _ + 1, _, _, _, 0 => pure ()
  | n + 1, f, a, i, k + 1 => do
    let fc ← deepCopy objFuel f
    let r ← callClos codes n fc (.i32 (UInt32.ofNat i))
    setObj (a + i) (.cell r)
    tabFill codes n f a (i + 1) k

/-- `count`'s loop: while `i < len(n)`, the state goes to a copy of `f` with the index. -/
def countLoop (codes : Array Code) : Nat → CV → UInt32 → UInt32 → CV → IM CV
  | 0, _, _, _, _ => throw "closure IR: out of fuel"
  | n + 1, f, len, i, s => do
    if i < arrLen len then
      let fc ← deepCopy objFuel f
      let s' ← callClos codes n fc (← allocObj (.pair (.i32 i) s))
      countLoop codes n f len (i + 1) s'
    else pure s

/-- `drop`'s drain: cell `a + i` is freed and its contents handed to a copy of `f`. -/
def dropFill (codes : Array Code) : Nat → CV → Nat → Nat → Nat → IM Unit
  | 0, _, _, _, _ => throw "closure IR: out of fuel"
  | _ + 1, _, _, _, 0 => pure ()
  | n + 1, f, a, i, k + 1 => do
    let (_, c) ← cellOf (.ptr (a + i))
    freeObj (a + i)
    let fc ← deepCopy objFuel f
    let r ← callClos codes n fc c
    deepDrop objFuel r
    dropFill codes n f a (i + 1) k

/-- Evaluate `t` in the frame `env`: its value and what is left of the frame. -/
def eval (codes : Array Code) : Nat → Env → Tm → IM (CV × Env)
  | 0, _, _ => throw "closure IR: out of fuel"
  | n + 1, env, t =>
    match t with
    | .var x => take env x
    | .unit => pure (.unit, env)
    | .lit (.i32 k) => pure (.i32 k, env)
    | .lit (.i64 k) => do pure (← allocObj (.i64 k), env)
    | .lit (.u8 k) => pure (.u8 k, env)
    | .pair a b => do
        let (va, env) ← take env a
        let (vb, env) ← take env b
        pure (← allocObj (.pair va vb), env)
    | .inj r a => do
        let (va, env) ← take env a
        pure (← allocObj (.inj r va), env)
    | .clos c xs => do
        let (vs, env) ← takeAll env xs
        pure (← allocObj (.clos c vs), env)
    | .prim .tab [x] => do
        let (v, env) ← take env x
        let (c, f) ← unpair v
        let .i32 c := c | throw "closure IR: tab of a non-length"
        let len := (arrLen c).toNat
        let base := (← get).next
        for _ in List.range (arrSlots len) do discard (allocObj (.cell .unit))
        tabFill codes n f base 0 len
        deepDrop objFuel f
        pure (← allocObj (.pair (.ptr base) (.i32 (arrLen c))), env)
    | .prim .count [x] => do
        let (v, env) ← take env x
        let (f, r) ← unpair v
        let (len, r) ← unpair r
        let (i, s) ← unpair r
        let .i32 len := len | throw "closure IR: count of a non-length"
        let .i32 i := i | throw "closure IR: count from a non-index"
        let s ← countLoop codes n f len i s
        deepDrop objFuel f
        pure (s, env)
    | .prim .drop [x] => do
        let (v, env) ← take env x
        let (f, arr) ← unpair v
        let (base, len) ← unpair arr
        let .ptr a := base | throw "closure IR: drop of a non-array"
        let .i32 len := len | throw "closure IR: drop of a non-array"
        dropFill codes n f a 0 len.toNat
        deepDrop objFuel f
        if len.toNat = 0 then freeObj a
        pure (.unit, env)
    | .prim op xs => do
        let (vs, env) ← takeAll env xs
        pure (← applyOp op vs, env)
    | .app f a => do
        let (vf, env) ← take env f
        let (va, env) ← take env a
        pure (← callClos codes n vf va, env)
    | .letv x e b => do
        let (v, env) ← eval codes n env e
        eval codes n ((x, v) :: env) b
    | .letpair x y p b => do
        let (vp, env) ← take env p
        match vp with
        | .ptr a =>
          match ← getObj a with
          | .pair va vb => do freeObj a; eval codes n ((x, va) :: (y, vb) :: env) b
          | _ => throw "closure IR: letpair of a non-pair"
        | _ => throw "closure IR: letpair of a non-pair"
    | .case s x b₁ y b₂ => do
        let (vs, env) ← take env s
        match vs with
        | .ptr a =>
          match ← getObj a with
          | .inj false v => do freeObj a; eval codes n ((x, v) :: env) b₁
          | .inj true v => do freeObj a; eval codes n ((y, v) :: env) b₂
          | _ => throw "closure IR: case of a non-injection"
        | _ => throw "closure IR: case of a non-injection"
    | .copy x x' b => do
        let some v := env.lookup x | throw s!"closure IR: copy of consumed variable {x}"
        let v' ← deepCopy objFuel v
        eval codes n ((x', v') :: env) b
    | .drop x b => do
        let (v, env) ← take env x
        deepDrop objFuel v
        eval codes n env b
end

/-- The observable form of a word. -/
def observe : Nat → CV → IM PV
  | 0, _ => throw "closure IR: out of fuel"
  | n + 1, v => do
    match v with
    | .unit => pure .unit
    | .i32 k => pure (.i32 k)
    | .u8 k => pure (.u8 k)
    | .ptr 0 => pure .loc
    | .ptr a =>
      match ← getObj a with
      | .pair x y => do pure (.pair (← observe n x) (← observe n y))
      | .inj r x => do pure (.inj r (← observe n x))
      | .clos _ _ => pure .fn
      | .i64 k => pure (.i64 k)
      | .cell _ => pure .loc

/-- Observe the loop `d` until it finishes: call it on `inl ()`, which answers `inl r` to finish
with `r` or `inr d'` to go on with `d'` (SPEC §11). -/
def drive (codes : Array Code) : Nat → CV → IM CV
  | 0, _ => throw "closure IR: out of fuel"
  | n + 1, d => do
    let t ← allocObj (.inj false .unit)
    let r ← callClos codes n d t
    match r with
    | .ptr a =>
      match ← getObj a with
      | .inj false v => do freeObj a; pure v
      | .inj true d' => do freeObj a; drive codes n d'
      | _ => throw "closure IR: a loop's `next` answered no injection"
    | _ => throw "closure IR: a loop's `next` answered no injection"

/-- Run `main` on the standard input `input` (driving it if it returns a loop), print its value,
drop it, and count the objects left. -/
def interp (fuel : Nat) (p : Prog) (input : List UInt8) : Except String Output := do
  let act : IM String := do
    let (v, rest) ← eval p.codes fuel [] p.main
    if !rest.isEmpty then throw "closure IR: main leaves variables unconsumed"
    let v ← match p.fin with
      | none => pure v
      | some c => do
        let r ← drive p.codes fuel v
        callClos p.codes fuel (← allocObj (.clos c [])) r
    let pv ← observe objFuel v
    deepDrop objFuel v
    pure (report pv (← get).heap.size)
  let (r, s) ← act.run ⟨{}, 1, input, .empty, .empty⟩
  pure (.mk' s.out s.err r)

end Backend.Clos
