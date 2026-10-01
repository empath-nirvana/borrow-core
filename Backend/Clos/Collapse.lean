import Backend.Clos.Types
import Backend.Clos.Flow

/-!
# Backend — codata thunks built eagerly

A loop, stream or iterator is built by the program as the thunk

    thunkv nu_in ⟨(nu_out (force f s₀)).1, (nu_out (force f s₀)).2⟩

(its erasure `λo. case o {inl _. f s₀ (inl ()) | inr _. f s₀ (inr ())}`, a closure over `f` and
`s₀`), while every later state is the thunk `unfold`'s map builds. The two are different codes
of one type, so every observation would be a dispatched call. Here such a thunk is replaced by
what forcing it computes first, when that is certain to be a value:

- **η.** When both projections observe the same captured variable `t`
  (`⟨(nu_out (force t)).1, (nu_out (force t)).2⟩`), the thunk is `t`.
- **A known pure call.** When both observe `f s₀` for the captured `f` and `s₀`, and the flow
  analysis finds that `f` is always the closure of one code whose body only builds a value (a
  closure, pair, injection or literal, from its variables: `unfold step` is `λs. λo. …`), the
  thunk is the call `f s₀`, made where the thunk is built. It cannot fail and reads or writes no
  memory but the value it builds, so making it early is not observable; the thunk's captures are
  consumed by it, as they would be by either projection.

The replaced codes are no longer built (`Prog.liveCodes`), so they leave their type's union and
the observations become direct calls.
-/

namespace Backend.Clos

/-- `t` computes `f s` from variables: `let x = s; let y = f; y x`, or `f s`. -/
def callOfVars? : Tm → Option (Var × Var)
  | .app f s => some (f, s)
  | .letv x (.var s) (.letv y (.var f) (.app y' x')) =>
    if y == y' && x == x' then some (f, s) else none
  | _ => none

/-- What an arm of a `sel` code applies to its projection: `let a = inl ()/inr (); let h = H; h a`
after the arm's binder is dropped. `H` is a variable (`.inl`) or a call of two (`.inr`). -/
def armHead? (bound : Var) : Tm → Option (Var ⊕ (Var × Var))
  | .drop x b => if x == bound then armHead? bound b else none
  | .letv t (.var x) (.drop t' b) =>
    if x == bound && t == t' then armHead? bound b else none
  | .letv a _ (.letv h H (.app h' a')) =>
    if h != h' || a != a' then none else
    match H with
    | .var y => some (.inl y)
    | .letv y (.var t) (.var y') => if y == y' then some (.inl t) else none
    | H => (callOfVars? H).map .inr
  | _ => none

/-- A term that builds a value from variables and literals, with no call, primitive or case. -/
def Tm.pureValue : Tm → Bool
  | .var _ | .unit | .lit _ | .pair .. | .inj .. | .clos .. => true
  | .letv _ e b => e.pureValue && b.pureValue
  | _ => false

/-- How to build a collapsed thunk from its captured variables' positions. -/
inductive Collapse where
  /-- The captured variable at this position. -/
  | eta (i : Nat)
  /-- The call of the captured variable at `f` on the one at `s`. -/
  | call (f s : Nat)

/-- The thunk code `c`, when it collapses. `flow` gives the codes each call may call. -/
def collapse? (codes : Array Code) (flow : Std.HashMap Var (Array Nat)) (c : Code) :
    Option Collapse := do
  let (_, x, b₁, y, b₂) ← c.selShape?
  let h₁ ← armHead? x b₁
  let h₂ ← armHead? y b₂
  let pos (v : Var) : Option Nat := c.env.idxOf? v
  match h₁, h₂ with
  | .inl t₁, .inl t₂ =>
    let i ← pos t₁
    if pos t₂ == some i && c.env.length == 1 then some (.eta i) else none
  | .inr (f₁, s₁), .inr (f₂, s₂) =>
    let i ← pos f₁
    let j ← pos s₁
    if pos f₂ != some i || pos s₂ != some j || c.env.length != 2 || i == j then none else
    -- The call's function variable: `f` itself, or the variable the arm binds it to.
    let callVar := (findCall b₁).getD f₁
    let fs ← flow[callVar]?
    if fs.size != 1 then none else
    let fc ← codes[fs[0]!]?
    if fc.body.pureValue then some (.call i j) else none
  | _, _ => none
where
  /-- The function variable of the arm's inner call `y x`. -/
  findCall : Tm → Option Var
    | .drop _ b | .letv _ (.var _) (.drop _ b) => findCall b
    | .letv _ _ (.letv _ H _) => match H with
      | .letv _ (.var _) (.letv y (.var _) (.app _ _)) => some y
      | .app f _ => some f
      | _ => none
    | _ => none

/-- Replace every construction of a collapsing code. -/
def Tm.collapse (cs : Std.HashMap Nat Collapse) : Tm → Tm
  | .clos c xs =>
    match cs[c]? with
    | some (.eta i) => .var (xs.getD i 0)
    | some (.call f s) => .app (xs.getD f 0) (xs.getD s 0)
    | none => .clos c xs
  | .letv x e b => .letv x (e.collapse cs) (b.collapse cs)
  | .letpair x y p b => .letpair x y p (b.collapse cs)
  | .case s x b₁ y b₂ => .case s x (b₁.collapse cs) y (b₂.collapse cs)
  | .copy x x' b => .copy x x' (b.collapse cs)
  | .drop x b => .drop x (b.collapse cs)
  | t => t

/-! ### Equal codes

Two λ-terms of the source can be one code: `unfold`'s first state `λo. self g s o` and the
`λo. self g s′ o` its map builds for every later one are the same term once `self` is the fixed
point's code (`Backend/Clos/Convert.lean`). Codes equal up to the names of their variables are
merged, so their closures are one code of their type. -/

abbrev RM := StateM (Std.HashMap Var Nat)

def rn (x : Var) : RM Var := do
  match (← get)[x]? with
  | some y => pure y
  | none => modifyGet fun m => (m.size, m.insert x m.size)

/-- `t` with its variables numbered in order of appearance. -/
def Tm.canon : Tm → RM Tm
  | .var x => return .var (← rn x)
  | .pair a b => return .pair (← rn a) (← rn b)
  | .inj r a => return .inj r (← rn a)
  | .clos c xs => return .clos c (← xs.mapM rn)
  | .prim op xs => return .prim op (← xs.mapM rn)
  | .app f a => return .app (← rn f) (← rn a)
  | .letv x e b => return .letv (← rn x) (← e.canon) (← b.canon)
  | .letpair x y p b => return .letpair (← rn x) (← rn y) (← rn p) (← b.canon)
  | .case s x b₁ y b₂ => return .case (← rn s) (← rn x) (← b₁.canon) (← rn y) (← b₂.canon)
  | .copy x x' b => return .copy (← rn x) (← rn x') (← b.canon)
  | .drop x b => return .drop (← rn x) (← b.canon)
  | t => pure t

/-- A term as a string that determines it (a key for `mergeCodes`), built directly: the derived
`Repr` lays the text out, which dominates the cost on large programs. -/
def Tm.keyStr : Tm → String
  | .var x => s!"v{x}"
  | .unit => "u"
  | .lit c => s!"l({reprStr c})"
  | .pair a b => s!"p({a},{b})"
  | .inj r a => s!"i({r},{a})"
  | .clos c xs => s!"c({c},{xs})"
  | .prim op xs => s!"o({reprStr op},{xs})"
  | .app f a => s!"a({f},{a})"
  | .letv x e b => s!"L({x},{e.keyStr},{b.keyStr})"
  | .letpair x y p b => s!"P({x},{y},{p},{b.keyStr})"
  | .case s x b₁ y b₂ => s!"C({s},{x},{b₁.keyStr},{y},{b₂.keyStr})"
  | .copy x x' b => s!"K({x},{x'},{b.keyStr})"
  | .drop x b => s!"D({x},{b.keyStr})"
  | .raise p => s!"R({p})"
  | .hnd n hr cls b => s!"H({n},{hr},{cls},{b.keyStr})"
  | .ubind nn dd b => s!"U({nn},{dd},{b.keyStr})"

/-- A code's text with its variables numbered in order of appearance. -/
def Code.key (c : Code) : String :=
  let act : RM Code := do
    let env ← c.env.mapM rn
    let param ← rn c.param
    pure ⟨env, param, ← c.body.canon⟩
  let k := act.run' {}
  s!"{k.env}|{k.param}|{k.body.keyStr}"

def Tm.renameCodes (f : Nat → Nat) : Tm → Tm
  | .clos c xs => .clos (f c) xs
  | .letv x e b => .letv x (e.renameCodes f) (b.renameCodes f)
  | .letpair x y p b => .letpair x y p (b.renameCodes f)
  | .case s x b₁ y b₂ => .case s x (b₁.renameCodes f) y (b₂.renameCodes f)
  | .copy x x' b => .copy x x' (b.renameCodes f)
  | .drop x b => .drop x (b.renameCodes f)
  | t => t

/-- Merge equal codes of the same layout type, with captured values of the same layout types,
into the first of them, until none are equal. Layout types are monomorphic, so equal codes at
different types (`λx. x` at two types) stay apart. The layout types of the result, when they were
found: the last round's, in which nothing merges. -/
def Prog.mergeCodesT (p : Prog) : Prog × Option Types := Id.run do
  let mut p := p
  -- The codes merged into another: nothing refers to them any more, so they are not keyed again.
  let mut merged : Std.HashSet Nat := {}
  for _ in [0:p.codes.size + 1] do
    let .ok T := p.types | return (p, none)
    let mut first : Std.HashMap String Nat := {}
    let mut to : Std.HashMap Nat Nat := {}
    for (c, k) in p.codes.toList.zipIdx do
      if merged.contains k then continue
      let key := s!"{T.codeType k} {T.env k} {c.key}"
      match first[key]? with
      | some k₀ => to := to.insert k k₀; merged := merged.insert k
      | none => first := first.insert key k
    if to.isEmpty then return (p, some T)
    let f (c : Nat) : Nat := to.getD c c
    p := { p with
      codes := p.codes.map fun (c : Code) => { c with body := c.body.renameCodes f }
      main := p.main.renameCodes f
      fin := p.fin.map f }
  return (p, none)

def Prog.mergeCodes (p : Prog) : Prog := p.mergeCodesT.1

/-- Build the collapsing codata thunks eagerly; and the result's layout types, when they were
found. -/
def Prog.collapseT (p : Prog) : Prog × Option Types := Id.run do
  let flow := p.flow
  let mut cs : Std.HashMap Nat Collapse := {}
  for (c, k) in p.codes.toList.zipIdx do
    if let some r := collapse? p.codes flow c then cs := cs.insert k r
  if cs.isEmpty then return p.mergeCodesT
  let q : Prog := { p with
    codes := p.codes.map fun (c : Code) => { c with body := c.body.collapse cs }
    main := p.main.collapse cs }
  return q.mergeCodesT

/-- Build the collapsing codata thunks eagerly. -/
def Prog.collapse (p : Prog) : Prog := p.collapseT.1

end Backend.Clos
