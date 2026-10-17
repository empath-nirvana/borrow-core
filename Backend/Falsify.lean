import Paper.S2_Statics.Definitions
import Support.Dynamics.Interpreter
import Backend.Source
import Backend.Clos.Convert

/-!
# Backend — the falsifier: allocators and lend tags  (docs/async-capabilities.md §6.1)

A dynamic check of a run, in `bcc interp`, outside the semantics. It runs the erased term on a
machine of its own: `Support`'s step function (`BoCa.step`) with the memory replaced, the
handler, finaliser and pure primitive steps reused from `Support` (`catchOp`, `effApp?`,
`delta`), and the memory steps checked. Nothing here is a rule of the language, and no theorem
mentions it.

**Allocators.**

- `least`: the least free block, as `Core/Alloc.lean`'s `Alloc.leastFree` and `Core/Run.lean`'s
  `runM`. A freed location is reused by the next allocation, so a use after free reads whatever
  the new cell holds.
- `fresh`: every allocation takes a location never used before, so a use after free is a stuck
  run, reported with the location. `Support`'s interpreter (`Mem.alloc`, the default of
  `bcc interp`) also never reuses a location: its `next` only grows.

**Tags** (`fresh`, and lend tags). A location value carries a tag: the location `c + t·2⁴⁰` is the
cell `c` seen through the tag `t`, and `t = 0` is the owner. Array leaves are `ℓ + i` (`idx`,
`split`), which keeps the tag. Each cell has a stack of the tags lent over it.

The erased term has no mark at a lend: `withbor1`, `withbor2` and `withbor3`, the slice borrows
and the block borrows all erase to `withbor` (`λx.λf. (x, f () x)`), their unwinding forms to
`withborUE d`, and `withload` and `withloadU` to `withload` (`λx.λf. f () (load x)`). Before the
run, `instrument` replaces each occurrence of these closed terms with a form that calls three
interpreter-only markers, written as a literal applied to an argument (a term no typed program
contains, since a literal is not a function):

- `LEND x`: a fresh tag `t` over the cells of `x` (a location, or a family `(ℓ, n)`), pushed on
  each cell's stack; answers `(t, x seen through t)`. The lend's kind is not in the erased term
  (`withbor1` and `withbor2` erase alike): a lend from an owner is `lend`, from a view `mut`
  (only `withbor3` lends a view). Both are exclusive.
- `RETAG c`: `withload`'s loaded contents `c`, each location in it seen through a fresh `imm` tag
  pushed on its cells (a family `(ℓ, n)` inside an array block: its `n` cells).
- `END t e`: a frame around the callback. When `e` answers, `t` ends. When an abortive operation
  passes outward through it, the continuation is discarded, and `t` ends. When a resuming
  operation passes outward through it, `t` is suspended: it stays live, and it is active again
  exactly when the frame is back on the running path, which is when the continuation is
  resumed (or cancelled, so that the borrower's finalisers run with the tag active).

A tag is *active* when its `END` frame is on the path from the term's root to the redex. An
access through a tag `t ≠ 0` is an error when `t` has ended, when it is not active (suspended,
or reached from outside its lend), when it frees, when it writes through an `imm` tag, or when a
live exclusive tag stands above it on the cell's stack (a write also when a live `imm` tag
does). An access through the owner (`t = 0`) is an error while an exclusive tag is live on the
cell, and a write or free while any tag is. A lend is a use of its source. At the end of the run
every tag must have ended. A run that returns a loop is driven one observation at a time; at each
boundary between observations every live tag must be suspended (a resuming operation crossed its
frame, which has not been on the running path since), and once the loop finishes every tag must
have ended.
-/

namespace Backend.Falsify
open BoCa

/-! ### Options -/

inductive AllocMode where
  | least | fresh
  deriving DecidableEq, Repr

structure Opts where
  alloc : AllocMode
  tags : Bool

def Opts.name (o : Opts) : String :=
  if o.tags then "tags" else match o.alloc with
    | .least => "least"
    | .fresh => "fresh"

/-! ### Locations and tags -/

/-- The cells a tag can name: a location is `cell + tag · stride`. -/
def stride : Nat := 1 <<< 40

def cellOf (n : Nat) : Nat := n % stride
def tagOf (n : Nat) : Nat := n / stride
def mkLoc (c t : Nat) : Nat := c + t * stride

inductive Kind where
  /-- A lend from an owner: `withbor1` or `withbor2` (`imm` or `mut`; the erased term does not
  say which). Exclusive. -/
  | lend
  /-- A lend from a view: `withbor3`. Exclusive. -/
  | mut
  /-- `withload`'s contents. Shared. -/
  | imm
  deriving DecidableEq, Repr

def Kind.str : Kind → String
  | .lend => "lend" | .mut => "mut" | .imm => "imm"

def Kind.exclusive : Kind → Bool
  | .imm => false
  | _ => true

structure TagInfo where
  kind : Kind
  live : Bool := true
  /-- A resuming operation crossed the tag's frame outward, and the frame has not been on the
  running path since: the lend is held by a suspended continuation. -/
  suspended : Bool := false
  /-- The cells the tag was pushed on. -/
  cells : Array Nat

structure St where
  cells : Std.HashMap Nat Val := {}
  /-- One past the largest location ever used. -/
  hw : Nat := 0
  /-- `least`: the free locations below `hw`. -/
  holes : Std.TreeSet Nat := {}
  /-- `fresh`: the freed locations. -/
  freed : Std.HashSet Nat := {}
  /-- The blocks `tab` placed: base ↦ length. -/
  blocks : Std.TreeMap Nat Nat := {}
  /-- Each cell's stack of tags, bottom first. -/
  lent : Std.HashMap Nat (Array Nat) := {}
  /-- Tag `t` is `tags[t - 1]`. -/
  tags : Array TagInfo := #[]
  /-- Resuming operations that crossed a live lend. -/
  suspends : Nat := 0

abbrev M := StateM St

def tagInfo (t : Nat) : M (Option TagInfo) := do
  return (← get).tags[t - 1]?

def tagStr (t : Nat) : M String := do
  match ← tagInfo t with
  | some i => return s!"tag {t} ({i.kind.str})"
  | none => return s!"tag {t}"

/-! ### Allocation -/

/-- The least `ℓ` with `ℓ, …, ℓ + n − 1` all free: in the holes below `hw`, or a run of holes
reaching `hw`, or `hw`. -/
def leastBlock (s : St) (n : Nat) : Nat := Id.run do
  if n = 0 then return s.hw
  let mut start := 0
  let mut len := 0
  let mut found : Option Nat := none
  for h in s.holes do
    if found.isNone then
      if len > 0 && h = start + len then len := len + 1
      else
        start := h
        len := 1
      if len ≥ n then found := some start
  match found with
  | some ℓ => return ℓ
  | none => return (if len > 0 && start + len = s.hw then start else s.hw)

/-- `n` cells holding `v`, at the allocator's location. -/
def allocBlock (o : Opts) (n : Nat) (v : Val) : M Nat := do
  let s ← get
  let ℓ := match o.alloc with
    | .least => leastBlock s n
    | .fresh => s.hw
  let mut cells := s.cells
  let mut holes := s.holes
  for i in [0:n] do
    cells := cells.insert (ℓ + i) v
    holes := holes.erase (ℓ + i)
  set { s with cells, holes, hw := max s.hw (ℓ + n) }
  return ℓ

/-! ### Checking an access -/

/-- A use of a location: a lend uses its source as a write does. -/
inductive Access where
  | read | write | free | lend
  deriving DecidableEq

def Access.str : Access → String
  | .read => "read" | .write => "write" | .free => "free" | .lend => "lend"

/-- The live tags of a cell's stack above position `i` (all of it when `i = none`). -/
def liveAbove (stk : Array Nat) (i : Option Nat) : M (Array (Nat × Kind)) := do
  let mut out := #[]
  let from_ := match i with | some k => k + 1 | none => 0
  for j in [from_:stk.size] do
    let t := stk[j]!
    if let some inf ← tagInfo t then
      if inf.live then out := out.push (t, inf.kind)
  return out

/-- Whether the use `a` of cell `c` through tag `t` conflicts with a tag lent over it. -/
def stackConflict (c t : Nat) (a : Access) : M (Option String) := do
  let stk := (← get).lent.getD c #[]
  let pos := if t = 0 then none else stk.findIdx? (· == t)
  if t ≠ 0 && pos.isNone then
    -- A tag not on the cell's stack: an `imm` tag over contents whose extent `RETAG` could not
    -- see. It may read while no exclusive tag is live.
    match ← tagInfo t with
    | some { kind := .imm, .. } =>
      let above ← liveAbove stk none
      if let some (u, _) := above.find? (·.2.exclusive) then
        return some s!"read of location {c} through {← tagStr t} while {← tagStr u} is live on it"
      return none
    | _ => return some s!"{a.str} of location {c} through {← tagStr t}, which was not lent over it"
  let above ← liveAbove stk pos
  let who ← if t = 0 then pure "the owner" else tagStr t
  if let some (u, _) := above.find? (·.2.exclusive) then
    return some s!"{a.str} of location {c} through {who} while {← tagStr u} above it is live"
  if a ≠ .read then
    if let some (u, _) := above[0]? then
      return some s!"{a.str} of location {c} through {who} while {← tagStr u} above it is live"
  return none

/-- The tag rules for the use `a` of the location value `n`, with the active tags `act`. -/
def tagCheck (act : List Nat) (n : Nat) (a : Access) : M (Option String) := do
  let c := cellOf n
  let t := tagOf n
  if t ≠ 0 then
    match ← tagInfo t with
    | none => return some s!"{a.str} of location {c} through an unknown tag {t}"
    | some inf =>
      if !inf.live then
        return some s!"{a.str} of location {c} through {← tagStr t} after its lend ended"
      if !act.contains t then
        return some (s!"{a.str} of location {c} through {← tagStr t} while its lend is " ++
          "suspended: its frame is not on the running path (a stop crossed it, or the view left it)")
      if a = .free then
        return some s!"free of location {c} through a view ({← tagStr t})"
      if a ≠ .read && inf.kind = .imm then
        return some s!"{a.str} of location {c} through an imm tag ({← tagStr t})"
  stackConflict c t a

/-- The memory part of an access: the cell must hold a value. -/
def present (o : Opts) (n : Nat) : M (Except String Val) := do
  let s ← get
  let c := cellOf n
  match s.cells.get? c with
  | some v => return .ok v
  | none =>
    if o.alloc = .fresh && s.freed.contains c then
      return .error s!"use after free of location {c}"
    return .error s!"source interpreter: stuck ({repr Stuck.useAfterFree})"

/-! ### The checked machine -/

inductive R where
  | next (e : Expr)
  | value (v : Val)
  | stuck (msg : String)
  | op (raise : Bool) (K : BoLo.Kont) (p : Val)

def ofStep : BoCa.Step → R
  | .next _ e => .next e
  | .value v => .value v
  | .stuck r => .stuck s!"source interpreter: stuck ({repr r})"
  | .op r K p => .op r K p

/-! #### Markers -/

def markLend : UInt64 := 0x4c454e44_00000001
def markRetag : UInt64 := 0x4c454e44_00000002
def markEnd : UInt64 := 0x4c454e44_00000003

def mk (m : UInt64) : Expr := .prim (.lit (.i64 m))

/-- `withbor` with its lend marked: `λx.λf. let (t, v) = LEND x; (x, END t (f () v))`. -/
def withborT : Expr :=
  .lam (.lam (.letpair (.app (mk markLend) (.var 1))
    (.pair (.var 3) (.app (.app (mk markEnd) (.var 1)) (.app (.app (.var 2) .unit) (.var 0))))))

/-- `withborUE d` with its lend marked:
`λr.λf. let (t, v) = LEND r; (END t (f () v)) then b. (r, b) unwind d r`. -/
def withborUT (d : Expr) : Expr :=
  .lam (.lam (.letpair (.app (mk markLend) (.var 1))
    (.app (.app (.prim .ubind) (.pair (.lam (.pair (.var 4) (.var 0))) (.lam (.app d (.var 4)))))
      (.app (.app (mk markEnd) (.var 1)) (.app (.app (.var 2) .unit) (.var 0))))))

/-- `withload` with its lend marked: `λx.λf. let (t, c) = RETAG (load x); END t (f () c)`. -/
def withloadT : Expr :=
  .lam (.lam (.letpair (.app (mk markRetag) (.app (.prim .load) (.var 1)))
    (.app (.app (mk markEnd) (.var 1)) (.app (.app (.var 2) .unit) (.var 0)))))

/-- The finaliser of `withborUE d`, when the term is one. -/
def withborUD? : Expr → Option Expr
  | .lam (.lam (.app (.app (.prim .ubind) (.pair (.lam (.pair (.var 2) (.var 0)))
      (.lam (.app d (.var 2))))) (.app (.app (.var 0) .unit) (.var 1)))) => some d
  | _ => none

/-- A node whose children are instrumented, marked if it is a lend. -/
def mark (e : Expr) : Expr :=
  if e == BoCa.withbor then withborT
  else if e == BoCa.withload then withloadT
  else match withborUD? e with
    | some d => withborUT d
    | none => e

/-- Mark every lend of `e`. -/
def instrument : Expr → Expr
  | .pair a b => mark (.pair (instrument a) (instrument b))
  | .inj₁ a => mark (.inj₁ (instrument a))
  | .inj₂ a => mark (.inj₂ (instrument a))
  | .lam b => mark (.lam (instrument b))
  | .seq a b => mark (.seq (instrument a) (instrument b))
  | .letpair a b => mark (.letpair (instrument a) (instrument b))
  | .case a b c => mark (.case (instrument a) (instrument b) (instrument c))
  | .app a b => mark (.app (instrument a) (instrument b))
  | e => e

/-- `x` seen through the tag `t` at every location. -/
def retagVal (t : Nat) : Expr → Expr
  | .loc n => .loc (mkLoc (cellOf n) t)
  | .pair a b => .pair (retagVal t a) (retagVal t b)
  | e => e

/-- The cells a lend of `x` covers: a location's cell, or a family's `n` cells. -/
def lendCells : Expr → Option (Nat × Nat × Nat)
  | .loc n => some (cellOf n, 1, tagOf n)
  | .pair (.loc n) (.prim (.lit (.i32 m))) => some (cellOf n, m.toNat, tagOf n)
  | _ => none

def newTag (k : Kind) (cells : Array Nat) : M Nat := do
  let s ← get
  let t := s.tags.size + 1
  let mut lent := s.lent
  for c in cells do
    lent := lent.insert c ((lent.getD c #[]).push t)
  set { s with tags := s.tags.push { kind := k, cells }, lent }
  return t

def endTag (t : Nat) : M Unit := do
  let s ← get
  match s.tags[t - 1]? with
  | none => pure ()
  | some inf =>
    let mut lent := s.lent
    for c in inf.cells do
      lent := lent.insert c ((lent.getD c #[]).filter (· ≠ t))
    set { s with tags := s.tags.set! (t - 1) { inf with live := false }, lent }

def litVal (t : Nat) : Val := .i64 (UInt64.ofNat t)

def pairVal (a b : Expr) : Option Val := valOf? (.pair a b)

/-- `LEND x`: a use of the source over each cell it covers. -/
def lend (o : Opts) (act : List Nat) (x : Val) : M R := do
  let some (c, n, p) := lendCells x.1
    | return .stuck "a lend of a value that is neither a location nor a family"
  for i in [0:n] do
    match ← present o (mkLoc (c + i) p) with
    | .error e => return .stuck s!"lend of location {c + i}: {e}"
    | .ok _ => pure ()
    if let some e ← tagCheck act (mkLoc (c + i) p) .lend then return .stuck e
  if n = 0 && p ≠ 0 then
    if let some e ← tagCheck act (mkLoc c p) .lend then return .stuck e
  let t ← newTag (if p = 0 then .lend else .mut) ((List.range n).toArray.map (c + ·))
  match pairVal (litVal t).1 (retagVal t x.1) with
  | some v => return .next v.1
  | none => return .stuck "internal error: a retagged value is not a value"

/-- The array block a cell is in, if `tab` placed one. -/
def blockOf (s : St) (c : Nat) : Option (Nat × Nat) :=
  match s.blocks.getEntryLE? c with
  | some (b, len) => if c < b + len then some (b, len) else none
  | none => none

/-- Whether the location value `n` may be seen through a new `imm` tag over the cells `cs`: its
tag is live and active, and no exclusive tag is live above it. -/
def retagOk (act : List Nat) (n : Nat) (cs : Array Nat) : M Bool := do
  let p := tagOf n
  if p ≠ 0 then
    match ← tagInfo p with
    | some inf => if !inf.live || !act.contains p then return false
    | none => return false
  for c in cs do
    if (← stackConflict c p .read).isSome then return false
  return true

/-- The contents `e` with each location in it seen through the tag `t`, and the cells covered. -/
def retagGo (act : List Nat) (t : Nat) : Expr → M (Expr × Array Nat)
  | .pair (.loc n) (.prim (.lit (.i32 m))) => do
    let c := cellOf n
    let s ← get
    let fam : Bool := match blockOf s c with
      | some (b, len) => decide (c + m.toNat ≤ b + len)
      | none => false
    if fam then
      let cs := (List.range m.toNat).toArray.map (c + ·)
      if ← retagOk act n cs then
        return (.pair (.loc (mkLoc c t)) (.prim (.lit (.i32 m))), cs)
      return (.pair (.loc n) (.prim (.lit (.i32 m))), #[])
    let (a, cs) ← retagGo act t (.loc n)
    return (.pair a (.prim (.lit (.i32 m))), cs)
  | .loc n => do
    let c := cellOf n
    if (← get).cells.contains c then
      if ← retagOk act n #[c] then return (.loc (mkLoc c t), #[c])
    return (.loc n, #[])
  | .pair a b => do
    let (a', cs₁) ← retagGo act t a
    let (b', cs₂) ← retagGo act t b
    return (.pair a' b', cs₁ ++ cs₂)
  | .inj₁ a => do
    let (a', cs) ← retagGo act t a
    return (.inj₁ a', cs)
  | .inj₂ a => do
    let (a', cs) ← retagGo act t a
    return (.inj₂ a', cs)
  | e => return (e, #[])

/-- `RETAG c`: `withload`'s contents, each location in them seen through a fresh `imm` tag when
`retagOk` allows it. -/
def retag (act : List Nat) (v : Val) : M R := do
  let t := (← get).tags.size + 1
  let (e', cells) ← retagGo act t v.1
  let t' ← newTag .imm cells
  if t' ≠ t then return .stuck "internal error: tag numbering"
  match pairVal (litVal t).1 e' with
  | some w => return .next w.1
  | none => return .stuck "internal error: retagged contents are not a value"

/-- The memory steps, checked; the other primitives are `Support`'s. -/
def delta (o : Opts) (act : List Nat) : Expr → Val → M R
  | .prim .alloc, v => do
    let ℓ ← allocBlock o 1 v
    return .next (.loc ℓ)
  | .prim .free, ⟨.loc n, _⟩ => do
    match ← present o n with
    | .error e => return .stuck e
    | .ok v =>
      if o.tags then
        if let some e ← tagCheck act n .free then return .stuck e
      let c := cellOf n
      modify fun s => { s with
        cells := s.cells.erase c,
        holes := if o.alloc = .least then s.holes.insert c else s.holes,
        freed := if o.alloc = .fresh then s.freed.insert c else s.freed,
        lent := s.lent.erase c }
      return .next v.1
  | .prim .load, ⟨.loc n, _⟩ => do
    match ← present o n with
    | .error e => return .stuck e
    | .ok v =>
      if o.tags then
        if let some e ← tagCheck act n .read then return .stuck e
      return .next v.1
  | .app (.prim .store) (.loc n), v => do
    match ← present o n with
    | .error e => return .stuck e
    | .ok _ =>
      if o.tags then
        if let some e ← tagCheck act n .write then return .stuck e
      modify fun s => { s with cells := s.cells.insert (cellOf n) v }
      return .next .unit
  | .prim .tab, ⟨.pair (.prim (.lit (.i32 c))) f, h⟩ => do
    let n := (arrLen c).toNat
    let ℓ ← allocBlock o n .unit
    modify fun s => { s with blocks := s.blocks.insert ℓ n }
    return .next (tabFill ⟨f, h.pair_right⟩ ℓ (arrLen c) 0 n)
  | f, v => return ofStep (BoCa.delta wasmHost Mem.empty f v)

/-- The frame `END t [·]`, if `f` is one. -/
def endFrame? : Expr → Option Nat
  | .app (.prim (.lit (.i64 m))) (.prim (.lit (.i64 t))) => if m = markEnd then some t.toNat else none
  | _ => none

/-- One step of the checked machine, with the active tags `act`: `BoCa.step`, its memory steps
checked, and the markers. -/
def step (o : Opts) (act : List Nat) : Expr → M R
  | .var _ => return .stuck s!"source interpreter: stuck ({repr Stuck.unboundVar})"
  | .unit => return .value .unit
  | .lam b => return .value (.lam b)
  | .loc ℓ => return .value (.loc ℓ)
  | .prim p => return .value (.prim p)
  | .pair e₁ e₂ => do
    match ← step o act e₁ with
    | .value v₁ =>
      match ← step o act e₂ with
      | .value v₂ => return .value (.pair v₁ v₂)
      | .next e₂' => return .next (.pair e₁ e₂')
      | .stuck r => return .stuck r
      | .op r K p => return .op r (.pairR v₁ K) p
    | .next e₁' => return .next (.pair e₁' e₂)
    | .stuck r => return .stuck r
    | .op r K p => return .op r (.pairL K e₂) p
  | .inj₁ e => do
    match ← step o act e with
    | .value v => return .value (.inj₁ v)
    | .next e' => return .next (.inj₁ e')
    | .stuck r => return .stuck r
    | .op r K p => return .op r (.inj₁ K) p
  | .inj₂ e => do
    match ← step o act e with
    | .value v => return .value (.inj₂ v)
    | .next e' => return .next (.inj₂ e')
    | .stuck r => return .stuck r
    | .op r K p => return .op r (.inj₂ K) p
  | .seq e₁ e₂ => do
    match ← step o act e₁ with
    | .value ⟨.unit, _⟩ => return .next e₂
    | .value _ => return .stuck s!"source interpreter: stuck ({repr Stuck.notAUnit})"
    | .next e₁' => return .next (.seq e₁' e₂)
    | .stuck r => return .stuck r
    | .op r K p => return .op r (.seq K e₂) p
  | .letpair e₁ e₂ => do
    match ← step o act e₁ with
    | .value ⟨.pair a b, h⟩ =>
      return .next ((e₂.subst 0 (Val.shift 1 0 ⟨b, h.pair_right⟩)).subst 0 ⟨a, h.pair_left⟩)
    | .value _ => return .stuck s!"source interpreter: stuck ({repr Stuck.notAPair})"
    | .next e₁' => return .next (.letpair e₁' e₂)
    | .stuck r => return .stuck r
    | .op r K p => return .op r (.letpair K e₂) p
  | .case e e₁ e₂ => do
    match ← step o act e with
    | .value ⟨.inj₁ a, h⟩ => return .next (e₁.subst 0 ⟨a, h.inj₁_inv⟩)
    | .value ⟨.inj₂ a, h⟩ => return .next (e₂.subst 0 ⟨a, h.inj₂_inv⟩)
    | .value _ => return .stuck s!"source interpreter: stuck ({repr Stuck.notASum})"
    | .next e' => return .next (.case e' e₁ e₂)
    | .stuck r => return .stuck r
    | .op r K p => return .op r (.case K e₁ e₂) p
  | .app f a => do
    match endFrame? f with
    | some t =>
      -- The frame is on the running path: its lend is not suspended.
      if (← tagInfo t).any (·.suspended) then
        modify fun s => { s with tags := s.tags.modify (t - 1) ({ · with suspended := false }) }
      match ← step o (t :: act) a with
      | .value v => endTag t; return .next v.1
      | .next a' => return .next (.app f a')
      | .stuck r => return .stuck r
      | .op r K p =>
        if r then endTag t
        else
          if (← tagInfo t).any (·.live) then
            modify fun s => { s with suspends := s.suspends + 1,
                                     tags := s.tags.modify (t - 1) ({ · with suspended := true }) }
        return .op r (.appR f K) p
    | none =>
    match ← step o act a with
    | .value v =>
      match f with
      | .prim (.lit (.i64 m)) =>
        if m = markLend then lend o act v
        else if m = markRetag then retag act v
        else return ofStep (BoCa.delta wasmHost Mem.empty f v)
      | _ =>
      match effApp? Mem.empty f v with
      | some st => return ofStep st
      | none =>
        match ← step o act f with
        | .value w =>
          match w.val with
          | .lam b => return .next (b.subst 0 v)
          | .prim p => delta o act (.prim p) v
          | .app f' a' => delta o act (.app f' a') v
          | _ => return .stuck s!"source interpreter: stuck ({repr Stuck.notAFunction})"
        | .next f' => return .next (.app f' a)
        | .stuck r => return .stuck r
        | .op r K p => return .op r (.appL K v) p
    | .next a' => return .next (.app f a')
    | .stuck r => return .stuck r
    | .op r K p => return ofStep (catchOp Mem.empty f r K p)

/-! ### Runs -/

/-- Run `e` for at most `fuel` steps: the value, and the state. -/
def runFrom (o : Opts) : Nat → St → Expr → Except String Val × St
  | 0, s, _ => (.error "source interpreter: out of fuel", s)
  | n + 1, s, e =>
    match (step o [] e).run s with
    | (.value v, s') => (.ok v, s')
    | (.next e', s') => runFrom o n s' e'
    | (.stuck r, s') => (.error r, s')
    | (.op _ _ _, s') => (.error "source interpreter: an operation no handler catches", s')

/-- The tags still live: a lend that never ended. -/
def liveTags (s : St) : List Nat :=
  (List.range s.tags.size).filterMap fun i =>
    if (s.tags[i]?.map (·.live)).getD false then some (i + 1) else none

/-- The tags live and not suspended: a lend whose frame is neither on the running path nor held by a
suspended continuation. -/
def activeTags (s : St) : List Nat :=
  (List.range s.tags.size).filterMap fun i =>
    if (s.tags[i]?.map fun t => t.live && !t.suspended).getD false then some (i + 1) else none

/-- Run `e` under `o` from `s`, without the check of the lends at its end. -/
def runUnchecked (o : Opts) (fuel : Nat) (s : St) (e : Expr) : Except String (Val × St) :=
  match runFrom o fuel s e with
  | (.error err, _) => .error (if o.tags || o.alloc = .fresh then s!"check {o.name}: {err}" else err)
  | (.ok v, s') => .ok (v, s')

/-- At the end of the run, every lend has ended. -/
def checkEnded (o : Opts) (s : St) : Except String Unit :=
  if o.tags then
    match liveTags s with
    | [] => .ok ()
    | ts => .error s!"check {o.name}: the lends of tags {ts} never ended"
  else .ok ()

/-- At an observation boundary of a loop (between two observations of a `main` that returns a
loop), every live lend is suspended: held by the loop's state, inside a suspended continuation. -/
def checkBoundary (o : Opts) (s : St) : Except String Unit :=
  if o.tags then
    match activeTags s with
    | [] => .ok ()
    | ts => .error s!"check {o.name}: the lends of tags {ts} are active at an observation boundary"
  else .ok ()

/-- Run `e` under `o` from `s`, and check that every lend ended. -/
def runChecked (o : Opts) (fuel : Nat) (s : St) (e : Expr) : Except String (Val × St) := do
  let (v, s') ← runUnchecked o fuel s e
  checkEnded o s'
  pure (v, s')

/-- The term the run starts from: marked when tags are checked. -/
def prepare (o : Opts) (e : Expr) : Expr := if o.tags then instrument e else e

/-- The statistics of a checked run, for `--stats`. -/
def stats (o : Opts) (s : St) : String :=
  s!"check {o.name}: {s.hw} locations used, {s.tags.size} lends, {s.suspends} suspensions crossed a lend"

/-- `interpSource`, checked. -/
def interpSource (o : Opts) (fuel : Nat) (e : Expr) : Except String (Output × String) := do
  let (v, s) ← runChecked o fuel {} (prepare o e)
  pure (.mk' .empty .empty (report (pvOfExpr v.1) s.cells.size), stats o s)

/-- `interpIO`, checked. -/
def interpIO (o : Opts) (fuel : Nat) (e : Expr) (exits : Bool := false) :
    Except String (Output × String) := do
  let (v, s) ← runChecked o fuel {} (prepare o e)
  pure (← ioOutputN v s.cells.size exits, stats o s)

/-- `driveSource`, checked: each observation's run checked, every lend suspended at each boundary
between observations, and every lend ended once the loop finishes. -/
def driveSource (o : Opts) (fuel : Nat) : Nat → St → Val → Except String (Val × St)
  | 0, _, _ => .error "source interpreter: out of fuel"
  | n + 1, s, d => do
    let (w, s') ← runUnchecked o fuel s (.app (.val d) (.val (.inj₁ .unit)))
    match w with
    | ⟨.inj₁ r, h⟩ => checkEnded o s'; pure (⟨r, by cases h; assumption⟩, s')
    | ⟨.inj₂ d', h⟩ =>
      checkBoundary o s'
      driveSource o fuel n s' ⟨d', by cases h; assumption⟩
    | _ => .error "source interpreter: a loop's `next` answered neither `inl` nor `inr`"

/-- A run that returns a loop, then the loop driven: the first boundary is before its first
observation. -/
def runLoop (o : Opts) (fuel : Nat) (e : Expr) : Except String (Val × St) := do
  let (d, s) ← runUnchecked o fuel {} (prepare o e)
  checkBoundary o s
  driveSource o fuel fuel s d

/-- `interpIOLoop`, checked. -/
def interpIOLoop (o : Opts) (fuel : Nat) (e : Expr) (exits : Bool := false) :
    Except String (Output × String) := do
  let (v, s') ← runLoop o fuel e
  pure (← ioOutputN v s'.cells.size exits, stats o s')

/-- A closed term that returns a loop, driven to its end, checked: its value and the cells left. -/
def interpLoop (o : Opts) (fuel : Nat) (e : Expr) : Except String (Output × String) := do
  let (v, s') ← runLoop o fuel e
  pure (.mk' .empty .empty (report (pvOfExpr v.1) s'.cells.size), stats o s')

end Backend.Falsify
