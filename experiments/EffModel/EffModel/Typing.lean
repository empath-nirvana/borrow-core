import EffModel.Syntax

/-!
# EffModel — typing

`check Γ M` synthesises `M`'s row and type and how many times it uses each variable. Every rule
that the brief's properties rest on is one of four checks:

- **grades** (`gradeOK`): a variable's uses, an interval over `{0, 1, many}`, must be allowed by
  its type's mode. Branches take the hull, sequencing adds.
- **independence** (`capture`): a thing at mode `m` depends only on hypotheses at modes `≥ m`.
  It is applied, unchanged, at every place something is captured:
  - a thunk at mode `m` captures its free variables (`thunk`);
  - a continuation captured at an operation of a row `ρ` captures what a frame holds while that
    row's operations run: the rest of a `to` (`bind`), an argument waiting on the stack (`app`),
    a handler's clauses (`handle`), a `using` frame (`using`), the algebraic continuation
    (`op`). The mode there is the row's `Bound.req`.
- **scope**: an instance never leaves its binder (types must not mention it), and a borrowed
  place is never captured by a thunk.
- **T1** (`lend`): a lend's body must not perform an operation whose continuation a handler
  outside the lend may suspend (`Bound.susp`).
-/

namespace EffModel

/-! ## Modes of types -/

def VTy.mode : VTy → Mode
  | .unit | .int | .bool | .void => Mode.unr
  | .resD => Mode.unr
  | .ticket => Mode.rel
  | .prod a b => a.mode.meet b.mode
  | .sum a b => a.mode.meet b.mode
  | .thunk m _ _ => m
  | .inst _ _ => Mode.unr
  | .cap _ _ => Mode.lin
  | .stream _ _ => Mode.lin

/-- A type that may be returned from a scope or stored: no instance, no frame-owned handle. -/
def VTy.firstClass : VTy → Bool
  | .inst _ _ | .resD => false
  | .prod a b | .sum a b => a.firstClass && b.firstClass
  | _ => true

/-! ## Rows -/

def rowSub (ρ σ : Row) : Bool := ρ.all (σ.contains ·)
def rowErase (ρ : Row) (x : String) : Row := ρ.filter (· != .i x)

mutual
def VTy.substI (x z : String) : VTy → VTy
  | .prod a b => .prod (a.substI x z) (b.substI x z)
  | .sum a b => .sum (a.substI x z) (b.substI x z)
  | .thunk m ρ c => .thunk m (ρ.map (fun a => if a == .i x then .i z else a)) (c.substI x z)
  | .stream ρ a => .stream (ρ.map (fun a => if a == .i x then .i z else a)) (a.substI x z)
  | t => t
def CTy.substI (x z : String) : CTy → CTy
  | .F a => .F (a.substI x z)
  | .arr y a ρ c =>
      if y == x then .arr y (a.substI x z) ρ c
      else .arr y (a.substI x z) (ρ.map (fun a => if a == .i x then .i z else a)) (c.substI x z)
  | .rcd ρ₁ c₁ ρ₂ c₂ =>
      .rcd (ρ₁.map (fun a => if a == .i x then .i z else a)) (c₁.substI x z)
        (ρ₂.map (fun a => if a == .i x then .i z else a)) (c₂.substI x z)
  | .allR r b ρ c => .allR r b (ρ.map (fun a => if a == .i x then .i z else a)) (c.substI x z)
end

def rowSubstR (r : String) (σ : Row) (ρ : Row) : Row :=
  ρ.flatMap (fun a => if a == .r r then σ else [a])

mutual
def VTy.substR (r : String) (σ : Row) : VTy → VTy
  | .prod a b => .prod (a.substR r σ) (b.substR r σ)
  | .sum a b => .sum (a.substR r σ) (b.substR r σ)
  | .thunk m ρ c => .thunk m (rowSubstR r σ ρ) (c.substR r σ)
  | .stream ρ a => .stream (rowSubstR r σ ρ) (a.substR r σ)
  | t => t
def CTy.substR (r : String) (σ : Row) : CTy → CTy
  | .F a => .F (a.substR r σ)
  | .arr y a ρ c => .arr y (a.substR r σ) (rowSubstR r σ ρ) (c.substR r σ)
  | .rcd ρ₁ c₁ ρ₂ c₂ => .rcd (rowSubstR r σ ρ₁) (c₁.substR r σ) (rowSubstR r σ ρ₂) (c₂.substR r σ)
  | .allR s b ρ c =>
      if s == r then .allR s b ρ c else .allR s b (rowSubstR r σ ρ) (c.substR r σ)
end

-- The instance atoms a type mentions.
mutual
def VTy.atoms : VTy → List Atom
  | .prod a b | .sum a b => a.atoms ++ b.atoms
  | .thunk _ ρ c => ρ ++ c.atoms
  | .stream ρ a => ρ ++ a.atoms
  | _ => []
def CTy.atoms : CTy → List Atom
  | .F a => a.atoms
  | .arr y a ρ c => a.atoms ++ ((ρ ++ c.atoms).filter (· != .i y))
  | .rcd ρ₁ c₁ ρ₂ c₂ => ρ₁ ++ c₁.atoms ++ ρ₂ ++ c₂.atoms
  | .allR r _ ρ c => (ρ ++ c.atoms).filter (· != .r r)
end

/-! ## Subtyping: rows covariant, modes may be forgotten, bounds widened

Recursion is on a depth bound: the contravariant and the renaming cases are not structural. -/

mutual
def vsubN : Nat → VTy → VTy → Bool
  | 0, _, _ => false
  | _ + 1, .unit, .unit | _ + 1, .int, .int | _ + 1, .bool, .bool | _ + 1, .void, .void
  | _ + 1, .resD, .resD | _ + 1, .ticket, .ticket => true
  | n + 1, .prod a b, .prod a' b' => vsubN n a a' && vsubN n b b'
  | n + 1, .sum a b, .sum a' b' => vsubN n a a' && vsubN n b b'
  | n + 1, .thunk m ρ c, .thunk m' ρ' c' => m.ge m' && rowSub ρ ρ' && csubN n c c'
  | _ + 1, .inst e b, .inst e' b' => e == e' && b.le b'
  | n + 1, .cap e s, .cap e' s' => e == e' && vsubN n s s' && vsubN n s' s
  | n + 1, .stream ρ a, .stream ρ' a' => rowSub ρ ρ' && vsubN n a a'
  | n + 1, .thunk _ ρ c, .stream ρ' a => rowSub ρ ρ' && csubN n c (.F (.sum a (.prod .int (.stream ρ' a))))
  | _ + 1, _, _ => false
def csubN : Nat → CTy → CTy → Bool
  | 0, _, _ => false
  | n + 1, .F a, .F a' => vsubN n a a'
  | n + 1, .arr x a ρ c, .arr y a' ρ' c' =>
      vsubN n a' a && rowSub ρ (ρ'.map (fun t => if t == .i y then .i x else t))
        && csubN n c (c'.substI y x)
  | n + 1, .rcd ρ₁ c₁ ρ₂ c₂, .rcd ρ₁' c₁' ρ₂' c₂' =>
      rowSub ρ₁ ρ₁' && csubN n c₁ c₁' && rowSub ρ₂ ρ₂' && csubN n c₂ c₂'
  | n + 1, .allR r b ρ c, .allR s b' ρ' c' =>
      b == b' && rowSub ρ (rowSubstR s [.r r] ρ') && csubN n c (c'.substR s [.r r])
  | _ + 1, _, _ => false
end

def vsub (a b : VTy) : Bool := vsubN 64 a b
def csub (a b : CTy) : Bool := csubN 64 a b

/-! ## Grades: intervals over `{0, 1, many}` -/

structure G where
  lo : Nat
  hi : Nat
deriving DecidableEq, Repr

def G.one : G := ⟨1, 1⟩
def G.add (a b : G) : G := ⟨min 2 (a.lo + b.lo), min 2 (a.hi + b.hi)⟩
def G.hull (a b : G) : G := ⟨min a.lo b.lo, max a.hi b.hi⟩
def G.many : G := ⟨0, 2⟩

/-- A mode allows a grade: never or sometimes used needs weakening, several uses contraction. -/
def gradeOK (m : Mode) (g : G) : Bool := (g.lo ≥ 1 || m.w) && (g.hi ≤ 1 || m.c)

abbrev Uses := List (String × G)

def Uses.get (u : Uses) (x : String) : G := (u.lookup x).getD ⟨0, 0⟩
def Uses.vars (u : Uses) : List String := u.map (·.1)
def Uses.add (u v : Uses) : Uses :=
  (u.vars ++ v.vars).eraseDups.map (fun x => (x, (u.get x).add (v.get x)))
def Uses.hull (u v : Uses) : Uses :=
  (u.vars ++ v.vars).eraseDups.map (fun x => (x, (u.get x).hull (v.get x)))
def Uses.drop (u : Uses) (xs : List String) : Uses := u.filter (fun p => !xs.contains p.1)
def Uses.scale (u : Uses) (g : G) : Uses := u.map (fun p => (p.1, g))

/-! ## Free variables (including instances operated on and places lent) -/

mutual
def Tm.fv : Tm → List String
  | .var x => [x]
  | .unit | .int _ | .bool _ | .ticket _ => []
  | .pair a b => a.fv ++ b.fv
  | .inl a _ | .inr _ a => a.fv
  | .thunk _ M => M.fv
  | .fix f _ _ M => M.fv.filter (· != f)
  | .ret v | .force v | .getcap v | .use v | .punch v | .emit v | .drop v => v.fv
  | .bind M x N => M.fv ++ N.fv.filter (· != x)
  | .lam x _ M => M.fv.filter (· != x)
  | .app M v => M.fv ++ v.fv
  | .rcd M N => M.fv ++ N.fv
  | .prj _ M => M.fv
  | .split v x y M => v.fv ++ M.fv.filter (fun z => z != x && z != y)
  | .case v x M y N => v.fv ++ M.fv.filter (· != x) ++ N.fv.filter (· != y)
  | .ite v M N => v.fv ++ M.fv ++ N.fv
  | .absurd v _ => v.fv
  | .prim _ a b => a.fv ++ b.fv
  | .op x _ v y M => x :: v.fv ++ M.fv.filter (· != y)
  | .handle x _ h _ _ M => h.fv ++ M.fv.filter (· != x)
  | .handleAt x h _ _ M => x :: h.fv ++ M.fv
  | .nu x _ _ M => M.fv.filter (· != x)
  | .ieq x y => [x, y]
  | .newcap _ _ co v => co.fv ++ v.fv
  | .lend c x M => c :: M.fv.filter (· != x)
  | .using x _ M => M.fv.filter (· != x)
  | .rlam _ _ M | .rapp M _ => M.fv
def Hnd.fv : Hnd → List String
  | .ret x M => M.fv.filter (· != x)
  | .cl _ p k M rest => M.fv.filter (fun z => z != p && z != k) ++ rest.fv
end

-- The places a term lends that it does not bind.
mutual
def Tm.lends : Tm → List String
  | .lend c x M => c :: M.lends.filter (· != x)
  | .thunk _ M | .fix _ _ _ M | .ret M | .lam _ _ M | .prj _ M | .rlam _ _ M
  | .rapp M _ | .nu _ _ _ M | .using _ _ M => M.lends
  | .bind M _ N | .rcd M N | .ite _ M N | .case _ _ M _ N => M.lends ++ N.lends
  | .split _ _ _ M | .op _ _ _ _ M | .app M _ => M.lends
  | .handle _ _ h _ _ M | .handleAt _ h _ _ M => h.lends ++ M.lends
  | _ => []
def Hnd.lends : Hnd → List String
  | .ret _ M => M.lends
  | .cl _ _ _ M rest => M.lends ++ rest.lends
end

/-! ## Contexts -/

structure Ctx where
  vars : List (String × VTy) := []
  rvars : List (String × Bound) := []
  sigs : Sigs
  /-- T1 is checked. Off only to show what it prevents. -/
  t1 : Bool := true

def Ctx.push (Γ : Ctx) (x : String) (t : VTy) : Ctx := { Γ with vars := (x, t) :: Γ.vars }
def Ctx.ty (Γ : Ctx) (x : String) : Except String VTy :=
  match Γ.vars.lookup x with
  | some t => pure t
  | none => throw s!"unbound variable {x}"
def Ctx.ops (Γ : Ctx) (e : String) : Except String (List OpSig) :=
  match Γ.sigs.lookup e with
  | some o => pure o
  | none => throw s!"unknown effect {e}"
def Ctx.op (Γ : Ctx) (e o : String) : Except String OpSig := do
  match (← Γ.ops e).find? (·.name == o) with
  | some s => pure s
  | none => throw s!"effect {e} has no operation {o}"

/-- The bound of a row: what a continuation captured at any of its operations may undergo. -/
def Ctx.bound (Γ : Ctx) (ρ : Row) : Except String Bound :=
  ρ.foldlM (fun b a => do
    match a with
    | .i x =>
        match (← Γ.ty x) with
        | .inst _ bi => pure (b.join bi)
        | _ => throw s!"{x} in a row is not an instance"
    | .r r =>
        match Γ.rvars.lookup r with
        | some br => pure (b.join br)
        | none => throw s!"unbound row variable {r}") Bound.none

/-- Independence: every variable of `xs` has a mode `≥ m`. `what` names the capturer. -/
def Ctx.capture (Γ : Ctx) (xs : List String) (m : Mode) (what : String) : Except String Unit :=
  for x in xs.eraseDups do
    let t ← Γ.ty x
    unless t.mode.ge m do
      throw s!"independence: {x}, at mode {t.mode.name}, is captured by {what} at mode {m.name}"

/-- Check a binder's grade and drop it from the uses. -/
def bindVar (u : Uses) (x : String) (t : VTy) : Except String Uses := do
  unless gradeOK t.mode (u.get x) do
    let g := u.get x
    throw s!"grade: {x}, at mode {t.mode.name}, used [{g.lo},{g.hi}] times"
  pure (u.drop [x])

def instVar (Γ : Ctx) (x : String) : Except String (String × Bound) := do
  match (← Γ.ty x) with
  | .inst e b => pure (e, b)
  | _ => throw s!"{x} is not an instance"

def notMention (x : String) (atoms : List Atom) (what : String) : Except String Unit :=
  if atoms.contains (.i x) then throw s!"scope: instance {x} escapes in {what}" else pure ()

/-- The type of two branches. -/
def join (c₁ c₂ : CTy) : Except String CTy :=
  if csub c₁ c₂ then pure c₂ else if csub c₂ c₁ then pure c₁ else throw "branches disagree"

def Hnd.names : Hnd → List String
  | .ret _ _ => []
  | .cl o _ _ _ rest => o :: rest.names

/-- Whether `k` occurs only at the head of a call in tail position: a clause of this shape
resumes before it returns, so it never keeps its continuation. -/
def Tm.tailOnly (k : String) : Tm → Bool
  | .bind M x N => !M.fv.contains k && (x == k || N.tailOnly k)
  | .ite v M N => !v.fv.contains k && M.tailOnly k && N.tailOnly k
  | .case v x M y N => !v.fv.contains k && (x == k || M.tailOnly k) && (y == k || N.tailOnly k)
  | .split v x y M => !v.fv.contains k && (x == k || y == k || M.tailOnly k)
  | .lam x _ M => x == k || M.tailOnly k
  | t@(.app _ _) => tailCall t || !t.fv.contains k
  | t => !t.fv.contains k
where
  tailCall : Tm → Bool
    | .app (.force (.var y)) a => y == k && !a.fv.contains k
    | .app M a => tailCall M && !a.fv.contains k
    | _ => false

def Hnd.clauseFor (o : String) : Hnd → Option (String × Tm)
  | .ret _ _ => none
  | .cl o' _ k M rest => if o' == o then some (k, M) else rest.clauseFor o

/-- The bound of an instance bound by this handler. The rules a continuation may undergo are the
operations' qualifiers. The handler may suspend a continuation when a resuming clause is not
tail-resumptive, or when the clauses perform an operation (of `ρh`) whose handler may. -/
def handlerBound (Γ : Ctx) (ops : List OpSig) (h : Hnd) (ρh : Row) : Except String Bound := do
  let bh ← Γ.bound ρh
  let keeps := ops.any fun o =>
    !o.abortive && match h.clauseFor o.name with
      | some (k, M) => !M.tailOnly k
      | none => true
  pure ⟨(boundOf ops).req, keeps || bh.susp⟩

/-- The checks of a deep handler of `x` once its body and clauses are typed: every operation
has a clause, `x` does not escape, and the clauses, which sit in the handler's frame, may be
captured by a continuation forwarded through it. -/
def finishHandler (Γ : Ctx) (x : String) (ops : List OpSig) (h : Hnd) (ρh : Row) (c : CTy)
    (a : VTy) (ρ : Row) (uM : Uses) (cl : Uses × Uses × Bool) :
    Except String (Row × CTy × Uses) := do
  let (uOnce, uMany, mayEnd) := cl
  notMention x (ρ ++ ρh ++ c.atoms ++ a.atoms) "a handler's type"
  for o in ops do
    unless h.names.contains o.name do throw s!"handle: no clause for {o.name}"
  -- The return clause and the abortive clauses are alternatives; if a clause may drop its
  -- continuation, the return clause may never run.
  let uOnce := if mayEnd then uOnce.hull [] else uOnce
  let b ← Γ.bound ρ
  Γ.capture h.fv b.req s!"a continuation forwarded through the handler of {x}"
  pure (ρ ++ ρh, c, uM.add (uOnce.add uMany))

/-! ## The judgement -/

mutual
/-- Values: their type and uses. -/
def checkV (Γ : Ctx) : Tm → Except String (VTy × Uses)
  | .var x => do pure (← Γ.ty x, [(x, G.one)])
  | .unit => pure (.unit, [])
  | .int _ => pure (.int, [])
  | .bool _ => pure (.bool, [])
  | .pair a b => do
      let (ta, ua) ← checkV Γ a
      let (tb, ub) ← checkV Γ b
      pure (.prod ta tb, ua.add ub)
  | .inl a bt => do
      let (ta, ua) ← checkV Γ a
      pure (.sum ta bt, ua)
  | .inr aty b => do
      let (tb, ub) ← checkV Γ b
      pure (.sum aty tb, ub)
  | .thunk m M => do
      let (ρ, c, u) ← check Γ M
      unless M.lends.isEmpty do throw "scope: a thunk captures a lent place"
      for x in M.fv.eraseDups do
        if let .ok .resD := Γ.ty x then throw s!"scope: a thunk captures the frame-owned {x}"
      Γ.capture M.fv m s!"a thunk"
      pure (.thunk m ρ c, u)
  | .fix f ρ c M => do
      let t := VTy.thunk Mode.unr ρ c
      let (ρ', c', u) ← check (Γ.push f t) M
      unless rowSub ρ' ρ && csub c' c do throw "fix: body does not match its annotation"
      unless M.lends.isEmpty do throw "scope: a thunk captures a lent place"
      Γ.capture (M.fv.filter (· != f)) Mode.unr "a recursive thunk"
      pure (t, u.drop [f])
  | t => throw s!"not a value: {repr t}"

/-- Computations: their row, type and uses. -/
def check (Γ : Ctx) : Tm → Except String (Row × CTy × Uses)
  | .ret v => do
      let (t, u) ← checkV Γ v
      pure ([], .F t, u)
  | .bind M x N => do
      let (ρ₁, c₁, u₁) ← check Γ M
      let .F a := c₁ | throw "bind: not an F computation"
      let (ρ₂, c₂, u₂) ← check (Γ.push x a) N
      let u₂ ← bindVar u₂ x a
      let b ← Γ.bound ρ₁
      Γ.capture (N.fv.filter (· != x)) b.req "the continuation of a `to`"
      pure (ρ₁ ++ ρ₂, c₂, u₁.add u₂)
  | .lam x a M => do
      let (ρ, c, u) ← check (Γ.push x a) M
      let u ← bindVar u x a
      pure ([], .arr x a ρ c, u)
  | .app M v => do
      let (ρ₀, c, u₁) ← check Γ M
      let .arr x a ρ c' := c | throw "app: not a function"
      let (tv, u₂) ← checkV Γ v
      unless vsub tv a do throw s!"app: argument type mismatch"
      let (ρ, c') ← match a, v with
        | .inst _ _, .var z => pure (ρ.map (fun t => if t == .i x then .i z else t), c'.substI x z)
        | .inst _ _, _ => throw "app: an instance argument must be a variable"
        | _, _ => pure (ρ, c')
      let b ← Γ.bound ρ₀
      unless a.mode.ge b.req do
        throw s!"independence: an argument at mode {a.mode.name} waits on the stack while its \
          function performs at mode {b.req.name}"
      pure (ρ₀ ++ ρ, c', u₁.add u₂)
  | .force v => do
      let (t, u) ← checkV Γ v
      match t with
      | .thunk _ ρ c => pure (ρ, c, u)
      | .stream ρ a => pure (ρ, .F (.sum a (.prod .int (.stream ρ a))), u)
      | _ => throw "force: not a thunk"
  | .rcd M N => do
      let (ρ₁, c₁, u₁) ← check Γ M
      let (ρ₂, c₂, u₂) ← check Γ N
      pure ([], .rcd ρ₁ c₁ ρ₂ c₂, u₁.hull u₂)
  | .prj first M => do
      let (ρ₀, c, u) ← check Γ M
      let .rcd ρ₁ c₁ ρ₂ c₂ := c | throw "prj: not a record"
      pure (if first then (ρ₀ ++ ρ₁, c₁, u) else (ρ₀ ++ ρ₂, c₂, u))
  | .split v x y M => do
      let (t, uv) ← checkV Γ v
      let .prod a b := t | throw "split: not a pair"
      let (ρ, c, u) ← check ((Γ.push x a).push y b) M
      let u ← bindVar u x a
      let u ← bindVar u y b
      pure (ρ, c, uv.add u)
  | .case v x M y N => do
      let (t, uv) ← checkV Γ v
      let .sum a b := t | throw "case: not a sum"
      let (ρ₁, c₁, u₁) ← check (Γ.push x a) M
      let (ρ₂, c₂, u₂) ← check (Γ.push y b) N
      let u₁ ← bindVar u₁ x a
      let u₂ ← bindVar u₂ y b
      let c ← join c₁ c₂
      pure (ρ₁ ++ ρ₂, c, uv.add (u₁.hull u₂))
  | .ite v M N => do
      let (t, uv) ← checkV Γ v
      let .bool := t | throw "if: not a bool"
      let (ρ₁, c₁, u₁) ← check Γ M
      let (ρ₂, c₂, u₂) ← check Γ N
      let c ← join c₁ c₂
      pure (ρ₁ ++ ρ₂, c, uv.add (u₁.hull u₂))
  | .absurd v c => do
      let (t, u) ← checkV Γ v
      let .void := t | throw "absurd: not void"
      pure ([], c, u)
  | .prim p a b => do
      let (ta, ua) ← checkV Γ a
      let (tb, ub) ← checkV Γ b
      unless (match ta, tb with | .int, .int => true | _, _ => false) do throw "prim: not ints"
      let r := match p with | .add | .sub => VTy.int | .lt | .eq => VTy.bool
      pure ([], .F r, ua.add ub)
  | .emit v => do
      let (t, u) ← checkV Γ v
      let .int := t | throw "emit: not an int"
      pure ([], .F .unit, u)
  | .op x o v y M => do
      let (e, b) ← instVar Γ x
      let s ← Γ.op e o
      let (tv, uv) ← checkV Γ v
      unless vsub tv s.arg do throw s!"op {o}: argument type mismatch"
      let (ρ, c, u) ← check (Γ.push y s.res) M
      let u ← bindVar u y s.res
      Γ.capture (M.fv.filter (· != y)) b.req s!"the continuation of {x}.{o}"
      pure (.i x :: ρ, c, uv.add u)
  | .handle x e h ρh c M => do
      let ops ← Γ.ops e
      let Γ' := Γ.push x (.inst e (← handlerBound Γ ops h ρh))
      let (ρM, cM, uM) ← check Γ' M
      let .F a := cM | throw "handle: body is not an F computation"
      let ρ := rowErase ρM x
      let cl ← clauses Γ' ops a ρ ρh c h
      let (ρ', c', u) ← finishHandler Γ' x ops h ρh c a ρ uM cl
      pure (ρ', c', u.drop [x])
  | .handleAt x h ρh c M => do
      let (e, bx) ← instVar Γ x
      let ops ← Γ.ops e
      unless (← handlerBound Γ ops h ρh).le bx do
        throw s!"handleAt: the handler exceeds the bound declared for {x}"
      let (ρM, cM, uM) ← check Γ M
      let .F a := cM | throw "handle: body is not an F computation"
      let ρ := rowErase ρM x
      let cl ← clauses Γ ops a ρ ρh c h
      finishHandler Γ x ops h ρh c a ρ uM cl
  | .nu x e b M => do
      let (ρ, c, u) ← check (Γ.push x (.inst e b)) M
      notMention x (ρ ++ c.atoms) "the body of ν: an unhandled instance"
      pure (ρ, c, u.drop [x])
  | .ieq x y => do
      let _ ← instVar Γ x
      let _ ← instVar Γ y
      pure ([], .F .bool, [])
  | .newcap e s co v => do
      let (ts, u) ← checkV Γ v
      unless vsub ts s do throw "newcap: state type mismatch"
      coops Γ e s co
      pure ([], .F (.cap e s), u)
  | .getcap v => do
      let (t, u) ← checkV Γ v
      let .cap _ s := t | throw "getcap: not a capability"
      pure ([], .F s, u)
  | .lend c x M => do
      let .cap e _ ← Γ.ty c | throw s!"lend: {c} is not a capability"
      if M.fv.contains c then throw s!"borrow: {c} is used while it is lent"
      let (ρ, c', u) ← check (Γ.push x (.inst e Bound.none)) M
      let .F a := c' | throw "lend: body is not an F computation"
      let ρ := rowErase ρ x
      notMention x a.atoms "a lend's result"
      unless a.firstClass do throw "scope: a lend's result is not first class"
      let b ← Γ.bound ρ
      if b.susp && Γ.t1 then
        throw "T1: the lend's body performs an operation whose continuation an outer handler \
          may suspend, and that continuation would hold the lend"
      pure (ρ, .F a, u.drop [x])
  | .using x _ M => do
      let (ρ, c, u) ← check (Γ.push x .resD) M
      let .F a := c | throw "using: body is not an F computation"
      unless a.firstClass do throw "scope: a resource handle escapes its frame"
      let b ← Γ.bound ρ
      unless Mode.aff.ge b.req do
        throw s!"independence: a destructor frame (affine) is captured by a continuation at \
          mode {b.req.name}"
      pure (ρ, c, u.drop [x])
  | .use v => do
      let (t, u) ← checkV Γ v
      let .resD := t | throw "use: not a resource"
      pure ([], .F .unit, u)
  | .drop v => do
      let (t, u) ← checkV Γ v
      let .stream _ _ := t | throw "drop: not a stream"
      pure ([], .F .unit, u)
  | .ticket _ => pure ([], .F .ticket, [])
  | .punch v => do
      let (t, u) ← checkV Γ v
      let .ticket := t | throw "punch: not a ticket"
      pure ([], .F .unit, u)
  | .rlam r b M => do
      let (ρ, c, u) ← check { Γ with rvars := (r, b) :: Γ.rvars } M
      pure ([], .allR r b ρ c, u)
  | .rapp M σ => do
      let (ρ₀, c, u) ← check Γ M
      let .allR r b ρ c' := c | throw "rapp: not row-polymorphic"
      let bσ ← Γ.bound σ
      unless bσ.le b do throw "rapp: the row exceeds the variable's bound"
      pure (ρ₀ ++ rowSubstR r σ ρ, c'.substR r σ, u)
  | t => throw s!"not a computation: {repr t}"

/-- Clauses: the uses of the return and abortive clauses (alternatives), the uses of the
resuming clauses (unrestricted: each runs once per operation), and whether a resuming clause may
end the handler without the return clause. -/
def clauses (Γ : Ctx) (ops : List OpSig) (a : VTy) (ρ ρh : Row) (c : CTy) :
    Hnd → Except String (Uses × Uses × Bool)
  | .ret x N => do
      let (ρN, cN, u) ← check (Γ.push x a) N
      unless rowSub ρN (ρ ++ ρh) && csub cN c do throw "handle: return clause does not match"
      let u ← bindVar u x a
      pure (u, [], false)
  | .cl o p k N rest => do
      let s ← match ops.find? (·.name == o) with
        | some s => pure s
        | none => throw s!"handle: no operation {o}"
      let kty := VTy.thunk s.k [] (.arr "_y" s.res (ρ ++ ρh) c)
      let (ρN, cN, u) ← check ((Γ.push p s.arg).push k kty) N
      unless rowSub ρN (ρ ++ ρh) && csub cN c do throw s!"handle: clause {o} does not match"
      let u ← bindVar u p s.arg
      let u ← bindVar u k kty
      let (uOnce, uMany, mayEnd) ← clauses Γ ops a ρ ρh c rest
      if s.abortive then
        pure (uOnce.hull u, uMany, mayEnd)
      else
        Γ.capture (N.fv.filter (fun z => z != p && z != k)) Mode.unr
          s!"the clause of {o}, which runs once per operation"
        pure (uOnce, uMany.add (u.scale G.many), mayEnd || s.k.w)

/-- A capability's co-operations: closed, state-passing, effect-free. -/
def coops (Γ : Ctx) (e : String) (s : VTy) : Hnd → Except String Unit
  | .ret _ _ => pure ()
  | .cl o p _ N rest => do
      let sg ← Γ.op e o
      unless sg.k == Mode.lin && !sg.abortive do
        throw s!"newcap: {o} is not tail-resumptive, so no comodel answers it"
      let Γ₀ : Ctx := { sigs := Γ.sigs }
      let (ρ, c, _) ← check (Γ₀.push p (.prod sg.arg s)) N
      unless ρ.isEmpty && csub c (.F (.prod sg.res s)) do
        throw s!"newcap: co-operation {o} is not a state access `A × S → F (B × S)`"
      coops Γ e s rest

end

/-- Type a closed program: it must be an `F` computation with an empty row. -/
def typecheck (sigs : Sigs) (M : Tm) (t1 : Bool := true) : Except String VTy := do
  let (ρ, c, _) ← check { sigs, t1 } M
  unless ρ.isEmpty do throw "unhandled effects"
  let .F a := c | throw "a program is an F computation"
  pure a

/-- Whether a program is accepted. -/
def accepts (sigs : Sigs) (M : Tm) : Bool := (typecheck sigs M).toBool

/-- Whether a program is accepted when T1 is not checked. -/
def acceptsWithoutT1 (sigs : Sigs) (M : Tm) : Bool := (typecheck sigs M false).toBool

/-- The rejection message, or `""`. -/
def rejection (sigs : Sigs) (M : Tm) : String :=
  match typecheck sigs M with
  | .ok _ => ""
  | .error e => e

end EffModel
