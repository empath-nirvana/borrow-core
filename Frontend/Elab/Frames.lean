import Frontend.Syntax

/-!
# Frontend — Elab — `let mut` as a frame's slots (`BCC_FRAMES=1`, #632, a prototype)  `[spec §47]`

The surface elaboration of `let mut` by the frame rules of `Core/FramesRules.lean`
(`docs/research/frames-with-exits.md`, SPEC §47). A `let mut x = e` of a surface body is a
**slot** of the body's frame: the cell `alloc(e)` (the rule `new`), which the frame owns. Each use
of `x` is the rule `use`, the cell lent for that one use: a load (`*x`), a store or a swap
(`modify &mut x`), a lend to a call or a borrow block (the content swapped out and lent by the
value's own rules, `wrapLends`). Core code never sees a slot, so a read of `x` inside a value is
loaded before the construct that evaluates the value (`slotLoads`), in evaluation order; inside
a borrow block's, a `with`'s or a writing `run`'s body, which is a frame inside the lend (the rule
`lend`), it is loaded where it is. The frame's slots are passed through each construct by its
rule:

- `case`: the arms of an `if`, a `match` or a `case` that mention a slot are frames over the same
  slots, each handing them back at its terminals (`handSlots`), and what follows takes them apart;
- `bind`: a head `x <- M`, `let p = if …` the same;
- `lend`: a callback's body hands back the slots it uses beside its result;
- the loops: §14's and §16's loops thread the cells they use in their state (`Π ⊗ S₀`);
- `new`'s normal exit frees the cell and reads its last content (`slotEnd`); at every other exit
  the cell is a linear value in scope, destroyed by §12's implicit destructor (the drop glue the
  frame rules' `bind` and `catch` carry).

No write set is computed and nothing is handed on by name. For a slot the parser does not run
R2's write sets, R3's hand-on, `mutCap` or `escapingWriter`: a slot is no `let mut` variable to
them.

**Not built** (a prototype gap): a closure that writes a slot is a frame-typed block
(`callBlock`), generic in its slots at its callee (D4); this prototype refuses it.
-/

namespace Frontend.Frames

/-- Fresh names, over the parser's counter. -/
abbrev FM := StateM Nat

def fresh (pre : String) : FM String := modifyGet fun n => (s!"{pre}{n}", n + 1)

/-- The mark of a read of the slot `y`: `*y`, a load (the parser writes it, `slotLoads` binds it
before the construct that evaluates it). -/
def mark (sp : Span) (y : String) : Val := .app sp (.sugar sp .deref) (.var sp y)

/-- The slot a value is the read mark of. -/
def mark? : Val → Option String
  | .app _ (.sugar _ .deref) (.var _ y) => some y
  | _ => none

/-- `modify &mut y { o -> M }`: the slot lent for one swap (the rule `use` with `withswap`). -/
def swapV (sp : Span) (y o : String) (M : Comp) : Val :=
  .app sp (.app sp (.sugar sp (.borrow .modify "")) (.lend sp ⟨y, sp⟩ .mut))
    (.thunkv sp (.lam sp ⟨o, sp⟩ (.name sp "_") M))

/-- The tuple of the variables `xs`. -/
def tuple (sp : Span) : List String → Val
  | [] => .unit sp
  | [x] => .var sp x
  | x :: xs => .pair sp (.var sp x) (tuple sp xs)

/-! ### Reads -/

mutual
/-- Whether `y` occurs in the value, at any depth. -/
def vNames (y : String) : Val → Bool
  | .var _ x | .clone _ x => x == y
  | .lend _ x _ => x.name == y
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => (cNames y M)
  | .pair _ V W | .app _ V W => (vNames y V) || (vNames y W)
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => (vNames y V)
  | _ => false

/-- Whether `y` occurs in the computation, at any depth. -/
def cNames (y : String) : Comp → Bool
  | .ret _ V | .absurd _ V | .perform _ _ _ V | .abort _ _ _ V => (vNames y V)
  | .bind _ _ _ M N _ => (cNames y M) || (cNames y N)
  | .force _ x => x.name == y
  | .lam _ _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M | .nuOut _ M | .ascribe _ M _
  | .proj _ _ M => (cNames y M)
  | .app _ M x => (cNames y M) || x.name == y
  | .with_ _ M N => (cNames y M) || (cNames y N)
  | .letUnit _ V M => (vNames y V) || (cNames y M)
  | .letPair _ _ _ V M => (vNames y V) || (cNames y M)
  | .case _ V _ M _ N => (vNames y V) || (cNames y M) || (cNames y N)
  | .loop _ _ _ V M N => (vNames y V) || (cNames y M) || (cNames y N)
  | .handle _ _ _ hr hc M => (vNames y hr) || (vNames y hc) || (cNames y M)
  | .unwind _ _ _ M D N => (cNames y M) || (cNames y D) || (cNames y N)
  | .withbor2r _ _ _ _ _ _ p m M => p.name == y || m.name == y || (cNames y M)
  | .top _ => false
end

mutual
/-- `V` with the reads of the slot `y` replaced by the variable `o` (a swap's old content, the
last content freed out of the cell), inside closures and `run`s too. -/
def vReads (y o : String) : Val → Val
  | V@(.app sp f W) =>
    if mark? V == some y then .var sp o else .app sp (vReads y o f) (vReads y o W)
  | .pair sp V W => .pair sp (vReads y o V) (vReads y o W)
  | .inl sp V => .inl sp (vReads y o V)
  | .inr sp V => .inr sp (vReads y o V)
  | .unbang sp V => .unbang sp (vReads y o V)
  | .boxed sp l V => .boxed sp l (vReads y o V)
  | .unbox sp V => .unbox sp (vReads y o V)
  | .sub sp V l => .sub sp (vReads y o V) l
  | .roll sp V => .roll sp (vReads y o V)
  | .unroll sp V => .unroll sp (vReads y o V)
  | .inst sp V l => .inst sp (vReads y o V) l
  | .ascribe sp V A => .ascribe sp (vReads y o V) A
  | .shorten sp m σ l V => .shorten sp m σ l (vReads y o V)
  | .mark sp k V => .mark sp k (vReads y o V)
  | .run sp M => .run sp (cReads y o M)
  | .thunk sp M => .thunk sp (cReads y o M)
  | .thunkv sp M => .thunkv sp (cReads y o M)
  | .bangThunk sp M => .bangThunk sp (cReads y o M)
  | .bangThunkv sp M => .bangThunkv sp (cReads y o M)
  | V => V

/-- `vReads` in the values of a computation. -/
def cReads (y o : String) : Comp → Comp
  | .ret sp V => .ret sp (vReads y o V)
  | .absurd sp V => .absurd sp (vReads y o V)
  | .perform sp k i V => .perform sp k i (vReads y o V)
  | .abort sp k i V => .abort sp k i (vReads y o V)
  | .bind sp x A M N lin => .bind sp x A (cReads y o M) (cReads y o N) lin
  | .letUnit sp V M => .letUnit sp (vReads y o V) (cReads y o M)
  | .letPair sp a b V M => .letPair sp a b (vReads y o V) (cReads y o M)
  | .case sp V a M b N => .case sp (vReads y o V) a (cReads y o M) b (cReads y o N)
  | .lam sp x A M => .lam sp x A (cReads y o M)
  | .loop sp ℓ src V M N => .loop sp ℓ src (vReads y o V) (cReads y o M) (cReads y o N)
  | M => M
end

/-- A load of the slot `y` into `v`, made before what follows: `let v = *y;` (`clone(*y)` when
the read is `clone(x)`). -/
structure Load where
  v : String
  cl : Bool
  sp : Span

/-- The loads `ls`, in order, before `M`. -/
def chain (y : String) (ls : List Load) (M : Comp) : Comp :=
  ls.foldr (fun l K =>
    let rd : Val := mark l.sp y
    let rd := if l.cl then .app l.sp (.sugar l.sp (.call "clone")) rd else rd
    .bind l.sp ⟨l.v, l.sp⟩ none (.ret l.sp rd) K false) M

/-- The loads a head begins with, as a context, and the rest of it. -/
def peel : Nat → Comp → (Comp → Comp) × Comp
  | 0, M => (id, M)
  | n + 1, M@(.bind sp d none (.ret rsp V) K false) =>
    if (mark? V).isSome || (match V with
        | .app _ (.sugar _ (.call "clone")) W => (mark? W).isSome
        | _ => false) then
      let (pre, K') := peel n K
      (fun T => .bind sp d none (.ret rsp V) (pre T) false, K')
    else (id, M)
  | _ + 1, M => (id, M)

mutual
/-- `V` with its reads of the slot `y` loaded before it, in the order its evaluation reads them.
A closure's reads are loaded where the closure is made: Core code never sees a slot, and a
closure that captured the cell could not be `!`; it captures the content read there, as a
`let mut` value's closure did. -/
def loadsV (y : String) : Val → StateT (List Load) FM Val
  | .app sp (.sugar csp (.call "clone")) W =>
    if mark? W == some y then do
      let v ← fresh "io_flv"
      modify (· ++ [⟨v, true, sp⟩])
      pure (.var sp v)
    else do pure (.app sp (.sugar csp (.call "clone")) (← loadsV y W))
  -- A borrow block's or a `with`'s body is a frame inside the lend (the rule `lend`): its reads
  -- are loaded where they are, in the body, which hands the slot back.
  | .app sp (.app sp₂ k@(.sugar _ (.borrow ..)) P) (.thunkv tsp (.lam lsp b A M)) => do
    let P' ← loadsV y P
    -- A swap the frame rules wrote (a store, a lend's) is Core code: its reads are the loads
    -- before it.
    if b.name.startsWith "io_f" then
      return .app sp (.app sp₂ k P') (.thunkv tsp (.lam lsp b A (← loadsIn y M)))
    return .app sp (.app sp₂ k P') (.thunkv tsp (.lam lsp b A (← (slotLoads y M : FM Comp))))
  | .app sp (.app sp₂ k@(.sugar _ (.handle ..)) P) (.thunkv tsp (.lam lsp b A M)) => do
    let P' ← loadsV y P
    return .app sp (.app sp₂ k P') (.thunkv tsp (.lam lsp b A (← (slotLoads y M : FM Comp))))
  | V@(.app sp f W) => do
    if mark? V == some y then
      let v ← fresh "io_flv"
      modify (· ++ [⟨v, false, sp⟩])
      return .var sp v
    pure (.app sp (← loadsV y f) (← loadsV y W))
  | .pair sp V W => return .pair sp (← loadsV y V) (← loadsV y W)
  | .inl sp V => return .inl sp (← loadsV y V)
  | .inr sp V => return .inr sp (← loadsV y V)
  | .unbang sp V => return .unbang sp (← loadsV y V)
  | .boxed sp l V => return .boxed sp l (← loadsV y V)
  | .unbox sp V => return .unbox sp (← loadsV y V)
  | .sub sp V l => return .sub sp (← loadsV y V) l
  | .roll sp V => return .roll sp (← loadsV y V)
  | .unroll sp V => return .unroll sp (← loadsV y V)
  | .inst sp V l => return .inst sp (← loadsV y V) l
  | .ascribe sp V A => return .ascribe sp (← loadsV y V) A
  | .shorten sp m σ l V => return .shorten sp m σ l (← loadsV y V)
  | .mark sp k V => return .mark sp k (← loadsV y V)
  | .thunk sp M => return .thunk sp (← loadsIn y M)
  | .thunkv sp M => return .thunkv sp (← loadsIn y M)
  | .bangThunk sp M => return .bangThunk sp (← loadsIn y M)
  | .bangThunkv sp M => return .bangThunkv sp (← loadsIn y M)
  -- `run M` is a frame inside its binding: its reads are loaded where they are when it also
  -- writes or lends the slot. One that only reads it (`a || b`'s operands) reads it where the
  -- expression is evaluated: a load has no effect.
  | .run sp M =>
    if cNames y (cReads y "io_f_" M) then return .run sp (← (slotLoads y M : FM Comp))
    else return .run sp (← loadsIn y M)
  | V => pure V

/-- A closure's or a `run`'s body with its reads of `y` taken out to the loads before it. -/
def loadsIn (y : String) : Comp → StateT (List Load) FM Comp
  | .ret sp V => return .ret sp (← loadsV y V)
  | .absurd sp V => return .absurd sp (← loadsV y V)
  | .perform sp k i V => return .perform sp k i (← loadsV y V)
  | .abort sp k i V => return .abort sp k i (← loadsV y V)
  | .bind sp x A M N lin => return .bind sp x A (← loadsIn y M) (← loadsIn y N) lin
  | .unwind sp x A M D N => return .unwind sp x A (← loadsIn y M) (← loadsIn y D) (← loadsIn y N)
  | .letUnit sp V M => return .letUnit sp (← loadsV y V) (← loadsIn y M)
  | .letPair sp a b V M => return .letPair sp a b (← loadsV y V) (← loadsIn y M)
  | .case sp V a M b N => return .case sp (← loadsV y V) a (← loadsIn y M) b (← loadsIn y N)
  | .loop sp ℓ src V M N => return .loop sp ℓ src (← loadsV y V) (← loadsIn y M) (← loadsIn y N)
  | .handle sp k st hr hc M => return .handle sp k st (← loadsV y hr) (← loadsV y hc) (← loadsIn y M)
  | .lam sp x A M => return .lam sp x A (← loadsIn y M)
  | .lamL sp x b M => return .lamL sp x b (← loadsIn y M)
  | .app sp M x => return .app sp (← loadsIn y M) x
  | .with_ sp M N => return .with_ sp (← loadsIn y M) (← loadsIn y N)
  | .proj sp i M => return .proj sp i (← loadsIn y M)
  | .inst sp M a => return .inst sp (← loadsIn y M) a
  | .nuIn sp M => return .nuIn sp (← loadsIn y M)
  | .nuOut sp M => return .nuOut sp (← loadsIn y M)
  | .ascribe sp M C => return .ascribe sp (← loadsIn y M) C
  | .withbor2r sp x b A B r p m M => return .withbor2r sp x b A B r p m (← loadsIn y M)
  | M@(.force ..) | M@(.top ..) => pure M

/-- The computation `M` with each read of the slot `y` loaded where it is evaluated: before the
construct whose value reads it, and at each turn of a `while` whose condition reads it. -/
def slotLoads (y : String) : Comp → FM Comp
  | .ret sp V => do
    if mark? V == some y then return .ret sp V
    let (V', ls) ← (loadsV y V).run []
    pure (chain y ls (.ret sp V'))
  | .absurd sp V => do
    let (V', ls) ← (loadsV y V).run []
    pure (chain y ls (.absurd sp V'))
  | .perform sp k i V => do
    let (V', ls) ← (loadsV y V).run []
    pure (chain y ls (.perform sp k i V'))
  | .abort sp k i V => do
    let (V', ls) ← (loadsV y V).run []
    pure (chain y ls (.abort sp k i V'))
  | .bind sp x A (.ret rsp V) N lin => do
    let N' ← slotLoads y N
    if mark? V == some y then return .bind sp x A (.ret rsp V) N' lin
    let (V', ls) ← (loadsV y V).run []
    pure (chain y ls (.bind sp x A (.ret rsp V') N' lin))
  | .bind sp x A M N lin => do
    -- The loads a head begins with are made before the binding.
    let (pre, M') := peel 64 (← slotLoads y M)
    return pre (.bind sp x A M' (← slotLoads y N) lin)
  | .unwind sp x A M D N =>
    return .unwind sp x A (← slotLoads y M) (← slotLoads y D) (← slotLoads y N)
  | .letUnit sp V M => do
    let M' ← slotLoads y M
    let (V', ls) ← (loadsV y V).run []
    pure (chain y ls (.letUnit sp V' M'))
  | .letPair sp a b V M => do
    let M' ← slotLoads y M
    let (V', ls) ← (loadsV y V).run []
    pure (chain y ls (.letPair sp a b V' M'))
  | .case sp V a M b N => do
    let M' ← slotLoads y M
    let N' ← slotLoads y N
    let (V', ls) ← (loadsV y V).run []
    pure (chain y ls (.case sp V' a M' b N'))
  | .loop sp ℓ .while_ V M N => do
    let M' ← slotLoads y M
    let N' ← slotLoads y N
    if (vNames y V) then
      -- The condition is read at each turn: `loop { if V { M } else { break } }`.
      let t : Ident := ⟨← fresh "io_fwt", sp⟩
      let f : Ident := ⟨← fresh "io_fwf", sp⟩
      let (V', ls) ← (loadsV y V).run []
      let body := chain y ls (.case sp V' f (.ret sp (.sugar sp .brk)) t M')
      return .loop sp ℓ .forever (.unit sp) body N'
    pure (.loop sp ℓ .while_ V M' N')
  | .loop sp ℓ src V M N => do
    let M' ← slotLoads y M
    let N' ← slotLoads y N
    let (V', ls) ← (loadsV y V).run []
    pure (chain y ls (.loop sp ℓ src V' M' N'))
  | .handle sp k st hr hc M => do
    let M' ← slotLoads y M
    let (hr', l₁) ← (loadsV y hr).run []
    let (hc', l₂) ← (loadsV y hc).run []
    pure (chain y (l₁ ++ l₂) (.handle sp k st hr' hc' M'))
  | .lam sp x A M => return .lam sp x A (← slotLoads y M)
  | .lamL sp x b M => return .lamL sp x b (← slotLoads y M)
  | .app sp M x => return .app sp (← slotLoads y M) x
  | .with_ sp M N => return .with_ sp (← slotLoads y M) (← slotLoads y N)
  | .proj sp i M => return .proj sp i (← slotLoads y M)
  | .inst sp M a => return .inst sp (← slotLoads y M) a
  | .nuIn sp M => return .nuIn sp (← slotLoads y M)
  | .nuOut sp M => return .nuOut sp (← slotLoads y M)
  | .ascribe sp M C => return .ascribe sp (← slotLoads y M) C
  | .withbor2r sp x b A B r p m M => return .withbor2r sp x b A B r p m (← slotLoads y M)
  | M@(.force ..) | M@(.top ..) => pure M

end

/-! ### The slots through a construct -/

/-- The terminals of a computation reached through tail positions. -/
def onTerms (f : Comp → Comp) : Comp → Comp
  | .bind sp x A M N lin => .bind sp x A M (onTerms f N) lin
  | .letUnit sp V M => .letUnit sp V (onTerms f M)
  | .letPair sp x y V M => .letPair sp x y V (onTerms f M)
  | .case sp V x M y N => .case sp V x (onTerms f M) y (onTerms f N)
  | .loop sp ℓ src V M N => .loop sp ℓ src V M (onTerms f N)
  | T => f T

/-- An exit of a loop's body as the parser writes it: `break`, `break e`, `continue`,
`return e`. -/
def isExit : Val → Bool
  | .sugar _ .brk | .sugar _ .cont | .app _ (.sugar _ .brk) _ | .app _ (.sugar _ .retE) _ => true
  | _ => false

/-- **The arms of a frame construct hand back its slots `ps`** (the rules `case` and `bind`): at
each terminal, the value beside the slots, `(V, Π)`; a terminal that is a computation is bound
first. An exit stays a terminal of its own: the loop it leaves takes the slots in its state. -/
def handSlots (t : String) (ps : List String) (M : Comp) : Comp :=
  onTerms (fun T => match T with
    | .ret sp V =>
      match V with
      | .var .. | .unit .. => .ret sp (.pair sp V (tuple sp ps))
      | _ => .bind sp ⟨t, sp⟩ none T (.ret sp (.pair sp (.var sp t) (tuple sp ps))) false
    | T => .bind T.span ⟨t, T.span⟩ none T (.ret T.span (.pair T.span (.var T.span t) (tuple T.span ps)))
      false) M

/-- **The end of a slot's scope** (the rule `new`, its normal exit): at each terminal the cell is
freed and its last content read where the value reads the slot, `let d = free(y); V[d/y]`. -/
def slotEnd (y d : String) (M : Comp) : Comp :=
  onTerms (fun T => match T with
    | .ret sp V =>
      if isExit V then T
      else .bind sp ⟨d, sp⟩ none (.ret sp (.app sp (.sugar sp (.call "free")) (.var sp y)))
        (.ret sp (vReads y d V)) false
    | T =>
      let r := d ++ "r"
      .bind T.span ⟨r, T.span⟩ none T
        (.bind T.span ⟨d, T.span⟩ none (.ret T.span (.app T.span (.sugar T.span (.call "free"))
          (.var T.span y))) (.ret T.span (.var T.span r)) false) false) M

/-! ### Lends of slots -/

/-- The slots among `ps` that a value lends (`&mut y`, `&y`) outside closures, in order. -/
def lentSlots (ps : List String) : Val → List String
  | .lend _ x _ => if ps.contains x.name then [x.name] else []
  | .pair _ V W | .app _ V W => (lentSlots ps V ++ lentSlots ps W).eraseDups
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => lentSlots ps V
  | _ => []

/-- `V` lending the variable `v` where it lends the slot `y`, outside closures. -/
def relend (y v : String) : Val → Val
  | .lend sp x m => if x.name == y then .lend sp ⟨v, x.span⟩ m else .lend sp x m
  | .pair sp V W => .pair sp (relend y v V) (relend y v W)
  | .app sp V W => .app sp (relend y v V) (relend y v W)
  | .inl sp V => .inl sp (relend y v V)
  | .inr sp V => .inr sp (relend y v V)
  | .unbang sp V => .unbang sp (relend y v V)
  | .boxed sp l V => .boxed sp l (relend y v V)
  | .unbox sp V => .unbox sp (relend y v V)
  | .sub sp V l => .sub sp (relend y v V) l
  | .roll sp V => .roll sp (relend y v V)
  | .unroll sp V => .unroll sp (relend y v V)
  | .inst sp V l => .inst sp (relend y v V) l
  | .ascribe sp V A => .ascribe sp (relend y v V) A
  | .shorten sp m σ l V => .shorten sp m σ l (relend y v V)
  | .mark sp k V => .mark sp k (relend y v V)
  | V => V

/-- **A value that lends slots** (the rule `use`): each slot `y` it lends is swapped out of its
cell, its content `v` lent by the value's own rules (a view of an array, a scoped cell of any
other value), and swapped back; `mk` builds the innermost value from `V` lending the contents. -/
def wrapLends (sp : Span) (mk : Val → Val) : List String → Val → FM Val
  | [], V => pure (mk V)
  | y :: ys, V => do
    let v ← fresh "io_flc"
    let r ← fresh "io_flr"
    let inner ← wrapLends sp mk ys (relend y v V)
    pure (swapV sp y v (.bind sp ⟨r, sp⟩ none (.ret sp inner)
      (.ret sp (.pair sp (.var sp v) (.var sp r))) false))

end Frontend.Frames
