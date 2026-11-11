import Std.Data.HashSet
import Frontend.Check.TExpr

/-!
# Backend2 — the types of the low IR  `[spec §3]`

The low IR (LIR) is typed by the checked term's types with what has no run-time content erased:
lifetimes and the lifetime box `[@a] A`. A value type `VTy` becomes an `LTy`, a computation
type `CTy` an `LCTy`, constructor for constructor (`ofV`, `ofC`): no type is inferred here, each is
the image of a type the checker put on a node of the typed term.

* `!A` is kept (`bang`): it has no run-time content (its value is `A`'s), but it is the type's
  statement that the value is persistent, which `Lint` reads at every copy and consume.
* `U C` is a closure, `thunk K`. A closure of `F A` takes no argument (the erasure's `λ_. M`,
  applied to `()`), a closure of `A ⊸ C` takes an `A`, and a closure of `C & D` is observed at one
  of its two components. `νX. C` is its unrolling: `U X` is the type variable `0` of `C`'s value
  types, as in `VTy`.
* `∀'x. C` is `C` (SPEC §44, §63): a `Λ` is its body, a value form (`allI_inst`), so
  `U (∀'x. F A)` is `A` and `U (∀'x. C)` is `U C`; no instantiation has run-time content.
* `Ref A` is an owned cell, `Imm A` and `Mut A` borrows of one, `[L]` a family of leaves `L`
  (an array is `[Ref A]`).
* A row's abortive operations are its computation's way out (SPEC §47): `F_Σ R` answers
  `R ⊕ P`, `P` the payload of `Σ`'s abortive operations (`rowPay`), one summand per operation in
  the row's order; with none, `R`. A non-abortive operation whose clause is called where it is
  performed has no run-time content in the type (`Backend2/Convert.lean`). `Div`'s operations are
  outside the fragment (N4).
* A row's **machine operations** (SPEC §49), the control operations of the program's set `ms`
  (those whose clause at some `handle` node of their name is not called where they are
  performed), make `F_Σ R` an *outcome*: `μY. R ⊕ (P ⊕ S)`, `S` one summand per machine
  operation `A ↠ B` of `Σ`, in the row's order, holding its argument and the suspended
  computation `U((B ⊸ F Y) & F C)`: resumed with the answer, it answers the outcome again;
  cancelled, it answers `C`, the outcome of its cancel row `F_{fin} 1` (`CancelRow`): `()` or the
  first error its finalisers raised, `1 ⊕ P_fin`, and a suspension at each machine operation of
  `fin` (`outcomeTy`).
-/

namespace Backend2
open BoCa BoCa.Fig16.LogRel.Core

deriving instance Hashable for BoCa.Width
deriving instance Hashable for BoCa.Fig16.LogRel.Core.Opaque

mutual
/-- A value type of the LIR. -/
inductive LTy where
  | unit
  | zero
  | int (w : Width)
  | pair (a b : LTy)
  | sum (a b : LTy)
  /-- `μX. A`, binding the type variable `0` in `A`. -/
  | mu (a : LTy)
  | tvar (n : Nat)
  /-- An owned cell holding an `A`. -/
  | ref (a : LTy)
  /-- A shared borrow of a cell holding an `A`. -/
  | imm (a : LTy)
  /-- A unique borrow of a cell holding an `A`. -/
  | mut (a : LTy)
  /-- A family of leaves `L`: `(base, n)`. -/
  | fam (l : LTy)
  | opq (k : Opaque)
  /-- `Unk`: a value of no content. -/
  | unk
  /-- A closure of the computation type `K`. -/
  | thunk (k : LCTy)
  /-- `!A`: a persistent value, represented as an `A`. -/
  | bang (a : LTy)
  deriving Inhabited, DecidableEq, Hashable, Repr

/-- A computation type of the LIR: what a closure answers when it is run. -/
inductive LCTy where
  | ret (a : LTy)
  | arr (a : LTy) (k : LCTy)
  | amp (k₁ k₂ : LCTy)
  | top
  /-- `νX. C`, binding the type variable `0` (standing for `U (νX. C)`) in `C`'s value types. -/
  | nu (k : LCTy)
  /-- **An evidence parameter** [spec §71]: a closure that takes, after its argument,
  the evidence `e` of the static name `n`, then is `k`. -/
  | ev (n : UInt32) (e : LTy) (k : LCTy)
  deriving Inhabited, DecidableEq, Hashable, Repr
end

/-! ### Substitution of type variables

`μX. A` unrolls to `A[μX. A/X]` and `νX. C` to `C[U(νX. C)/X]`; the variables are de Bruijn, as in
`VTy`. -/

mutual
/-- Lift the free type variables at or above `c` by one. -/
def LTy.lift (c : Nat) : LTy → LTy
  | .tvar n => .tvar (if n < c then n else n + 1)
  | .pair a b => .pair (a.lift c) (b.lift c)
  | .sum a b => .sum (a.lift c) (b.lift c)
  | .mu a => .mu (a.lift (c + 1))
  | .ref a => .ref (a.lift c)
  | .imm a => .imm (a.lift c)
  | .mut a => .mut (a.lift c)
  | .fam l => .fam (l.lift c)
  | .thunk k => .thunk (k.lift c)
  | .bang a => .bang (a.lift c)
  | t => t
def LCTy.lift (c : Nat) : LCTy → LCTy
  | .ret a => .ret (a.lift c)
  | .arr a k => .arr (a.lift c) (k.lift c)
  | .amp k₁ k₂ => .amp (k₁.lift c) (k₂.lift c)
  | .top => .top
  | .nu k => .nu (k.lift (c + 1))
  | .ev n e k => .ev n (e.lift c) (k.lift c)
end

mutual
/-- `A[S/X]` at the variable `n` (under binders, `n` and `S` lifted). -/
def LTy.subst (n : Nat) (S : LTy) : LTy → LTy
  | .tvar m => if m == n then S else if m > n then .tvar (m - 1) else .tvar m
  | .pair a b => .pair (LTy.subst n S a) (LTy.subst n S b)
  | .sum a b => .sum (LTy.subst n S a) (LTy.subst n S b)
  | .mu a => .mu (LTy.subst (n + 1) (S.lift 0) a)
  | .ref a => .ref (LTy.subst n S a)
  | .imm a => .imm (LTy.subst n S a)
  | .mut a => .mut (LTy.subst n S a)
  | .fam l => .fam (LTy.subst n S l)
  | .thunk k => .thunk (LCTy.subst n S k)
  | .bang a => .bang (LTy.subst n S a)
  | t => t
def LCTy.subst (n : Nat) (S : LTy) : LCTy → LCTy
  | .ret a => .ret (LTy.subst n S a)
  | .arr a k => .arr (LTy.subst n S a) (LCTy.subst n S k)
  | .amp k₁ k₂ => .amp (LCTy.subst n S k₁) (LCTy.subst n S k₂)
  | .top => .top
  | .nu k => .nu (LCTy.subst (n + 1) (S.lift 0) k)
  | .ev m e k => .ev m (LTy.subst n S e) (LCTy.subst n S k)
end

/-- `A[μX. A/X]`. -/
def LTy.unrollMu (a : LTy) : LTy := LTy.subst 0 (.mu a) a

/-- `C[U(νX. C)/X]`. -/
def LCTy.unrollNu (k : LCTy) : LCTy := LCTy.subst 0 (.thunk (.nu k)) k

/-! ### `!` up to representation

`!A` is represented as `A`. A decision about a value's representation (its layout, its words, which
closure it is) reads its type through `peel`, the top-level `!`s removed; one that compares two
types for a representation compares them with `!` erased throughout (`unbang`, `sameRep`). `Lint`
reads `!` itself, and the conversion's keys keep it (a `use` body's, a consume's: a key fixes
the LIR types of what it converts). -/

/-- The address of a task stack's frame (SPEC §52): one word. -/
def LTy.addr : LTy := .int .w64

/-- The type with its top-level `!`s removed: what the value is represented as. -/
def LTy.peel : LTy → LTy
  | .bang a => a.peel
  | t => t

mutual
/-- The type with every `!` erased. -/
def LTy.unbang : LTy → LTy
  | .pair a b => .pair a.unbang b.unbang
  | .sum a b => .sum a.unbang b.unbang
  | .mu a => .mu a.unbang
  | .ref a => .ref a.unbang
  | .imm a => .imm a.unbang
  | .mut a => .mut a.unbang
  | .fam l => .fam l.unbang
  | .thunk k => .thunk k.unbang
  | .bang a => a.unbang
  | t => t
def LCTy.unbang : LCTy → LCTy
  | .ret a => .ret a.unbang
  | .arr a k => .arr a.unbang k.unbang
  | .amp k₁ k₂ => .amp k₁.unbang k₂.unbang
  | .top => .top
  | .nu k => .nu k.unbang
  | .ev n e k => .ev n e.unbang k.unbang
end

/-- Two types of one representation: equal with every `!` erased. -/
def LTy.sameRep (a b : LTy) : Bool := a.unbang == b.unbang

/-- Two closure types of one representation: equal with every `!` erased. -/
def LCTy.sameRep (a b : LCTy) : Bool := a.unbang == b.unbang

/-- `sameRep` is equality up to `!`: it holds exactly when the two types agree with every `!`
erased. -/
theorem LTy.sameRep_iff (a b : LTy) : a.sameRep b = true ↔ a.unbang = b.unbang := by
  simp [LTy.sameRep]

theorem LCTy.sameRep_iff (a b : LCTy) : a.sameRep b = true ↔ a.unbang = b.unbang := by
  simp [LCTy.sameRep]

/-- What `sameRep` ignores: a `!`, on either side. -/
theorem LTy.sameRep_bang_left (a b : LTy) : (LTy.bang a).sameRep b = a.sameRep b := by
  simp [LTy.sameRep, LTy.unbang]

theorem LTy.sameRep_bang_right (a b : LTy) : a.sameRep (.bang b) = a.sameRep b := by
  simp [LTy.sameRep, LTy.unbang]

/-- Removing the top-level `!`s keeps the representation. -/
theorem LTy.unbang_peel : ∀ a : LTy, a.peel.unbang = a.unbang
  | .bang a => by simp only [LTy.peel, LTy.unbang]; exact LTy.unbang_peel a
  | .unit | .zero | .int _ | .pair .. | .sum .. | .mu _ | .tvar _ | .ref _ | .imm _ | .mut _
  | .fam _ | .opq _ | .unk | .thunk _ => rfl

theorem LTy.sameRep_peel (a : LTy) : a.peel.sameRep a = true := by
  simp [LTy.sameRep, LTy.unbang_peel]

/-- A closure type as its observations see it: `νX. C` unrolled, until it is not a `ν`. -/
def LCTy.whnf : Nat → LCTy → LCTy
  | f + 1, .nu k => LCTy.whnf f k.unrollNu
  | _, k => k

/-- An operation of a row is abortive: answer `0` at a qualifier with weakening (`OpSig.abort`). -/
def abortB (q : Qual) (B : VTy) : Bool := B.isZero && q != .lin

/-- The payload of a row's abortive operations (`ofEff`'s list): each key once, its first, as
`Row.find` reads a row; their argument types a right-nested sum, one summand per operation, in
the row's order; `none` at none.  `[spec §47]` -/
def payOf (ps : List ((UInt32 × UInt32) × LTy)) : Option LTy :=
  let ks := ps.foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []
  ks.reverse.foldl (fun acc p => match acc with
    | none => some p.2
    | some t => some (.sum p.2 t)) none

/-- A payload's list, each key once, its first. -/
def dedupPay (ps : List ((UInt32 × UInt32) × LTy)) : List ((UInt32 × UInt32) × LTy) :=
  ps.foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []

/-- The name of `Div` (SPEC §14). -/
def divName : UInt32 := 0xFFFFFFFF

/-- The program's machine operations (SPEC §49): the control operations `(n, i)` whose clause at
some `handle` node of `n` is not called where it is performed (`Backend2/Driver.lean`,
`machineOps`). -/
abbrev MachSet := Std.HashSet (UInt32 × UInt32)

/-- **A cancel row as a machine operation's `k` reads it** (SPEC §27, §49): the row `fin` of
`F_{fin} 1`, what cancelling a computation suspended at the operation performs. `pay`, its abortive
operations' payload (each key once, its first, `dedupPay`); `ms`, its machine operations (each key
once, its first), each with its argument, its answer and its own cancel row, read as `OpSig.ent`
reads it (`ofFinAt`); `unrs`, its operations at `unr`; `ty`, what the cancel answers:
`outcomeTy 1 pay ms`, the outcome of `F_{fin} 1`. With no machine operation in `fin` that is `()` or
the first error its finalisers raised, `1 ⊕ P_fin` (or `1`). The nesting is the cancel rows' own
(§27), finite. -/
inductive CancelRow where
  | mk (pay : List ((UInt32 × UInt32) × LTy))
      (ms : List ((UInt32 × UInt32) × LTy × LTy × Option CancelRow))
      (unrs : List (UInt32 × UInt32)) (ty : LTy)

instance : Inhabited CancelRow := ⟨.mk [] [] [] .unit⟩

namespace CancelRow
def pay : CancelRow → List ((UInt32 × UInt32) × LTy) | .mk p _ _ _ => p
def ms : CancelRow → List ((UInt32 × UInt32) × LTy × LTy × Option CancelRow) | .mk _ m _ _ => m
def unrs : CancelRow → List (UInt32 × UInt32) | .mk _ _ u _ => u
def ty : CancelRow → LTy | .mk _ _ _ t => t
end CancelRow

/-- What cancelling a computation suspended at an operation answers (SPEC §27, §49): the outcome
of its cancel row (`CancelRow.ty`); `1` at a cancel row `⊤` (an operation that is not capturable,
never cancelled). -/
def cancelResTy (cp : Option CancelRow) : LTy :=
  match cp with
  | none => .unit
  | some cr => cr.ty

/-- **The outcome of a computation** at a row with machine operations  `[spec §49]`: `R`, the
payload `P` of the row's abortive operations (`payOf`), and for each machine operation `A ↠ B`
(each key once, in the row's order) its argument beside the suspended computation,
`U((B ⊸ F Y) & F C)`, `Y` the outcome itself and `C` what its cancel answers (`cancelResTy`, at
the operation's cancel row): `μY. R ⊕ (P ⊕ S)`, or `μY. R ⊕ S` with no abortive operation. With
no machine operation it is `R ⊕ P`, or `R`. `R`'s free type variables (an `X` of a `ν`) are
lifted under the `μ`. -/
def outcomeTy (r : LTy) (aborts : List ((UInt32 × UInt32) × LTy))
    (machs : List ((UInt32 × UInt32) × LTy × LTy × Option CancelRow)) : LTy :=
  let ms := machs.foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []
  match ms with
  | [] => match payOf aborts with
    | none => r
    | some p => .sum r p
  | _ =>
    let pay := payOf aborts
    let kT (b : LTy) (cp : Option CancelRow) : LTy :=
      .thunk (.amp (.arr (b.lift 0) (.ret (.tvar 0))) (.ret ((cancelResTy cp).lift 0)))
    let s := (payOf (ms.map fun (k, a, b, cp) => (k, .pair (a.lift 0) (kT b cp)))).getD .unit
    let x := match pay with
      | none => s
      | some p => .sum (p.lift 0) s
    .mu (.sum (r.lift 0) x)

/-- **The program's evidence** [spec §71]: each static name whose `tail` clause is
called directly with the values it captures (`Backend2/Driver.lean`, `DirectKind.env`), with the
LIR types of its evidence parameters, one per captured slot, in the slots' order. Empty, no type
changes. -/
abbrev EvSet := Std.HashMap UInt32 (List LTy)

/-- The names of a row, in its order (`CTy.effOf`'s layers). -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.effNames : CTy → List UInt32
  | .eff n _ _ _ _ _ _ C => n :: C.effNames
  | _ => []

/-- The evidence parameters a code at a row whose names are `names` takes: each name of `fd`
once, in the row's order, each with its parameters' types. -/
def evLayers (fd : EvSet) (names : List UInt32) : List (UInt32 × LTy) :=
  (names.eraseDups.filter fd.contains).flatMap fun n => (fd.getD n []).map (n, ·)

/-- `k` taking the evidence parameters `es` first. -/
def evWrap (es : List (UInt32 × LTy)) (k : LCTy) : LCTy :=
  es.foldr (fun (n, e) k => .ev n e k) k

/-- A closure type's leading evidence parameters, and what it is after them. -/
def LCTy.stripEv : LCTy → List (UInt32 × LTy) × LCTy
  | .ev n e k => let (es, k') := k.stripEv; ((n, e) :: es, k')
  | k => ([], k)

/-- **Evidence where the first cut builds none**  `[spec §71]`: an internal error. The program's
evidence is chosen before conversion (`Backend2/Driver.lean`, `evNames`), which excludes every
name whose evidence would reach such a place; the conversion never meets one. -/
def evInternal (n : UInt32) (why : String) : String :=
  s!"LIR: internal: the evidence of {n} at {why}, which `evNames` excludes"

mutual
/-- A value type of the LIR: lifetimes, `[@a]` and `∀` erased, `!` kept; `ms` the program's
machine operations. -/
def ofV (ms : MachSet) (fd : EvSet) : VTy → Except String LTy
  | .unit => pure .unit
  | .zero => pure .zero
  | .int w => pure (.int w)
  | .tensor A B => return .pair (← ofV ms fd A) (← ofV ms fd B)
  | .sum A B => return .sum (← ofV ms fd A) (← ofV ms fd B)
  | .mu A => return .mu (← ofV ms fd A)
  | .tvar n => pure (.tvar n)
  | .ref A => return .ref (← ofV ms fd A)
  | .imm _ A => return .imm (← ofV ms fd A)
  | .mut _ A => return .mut (← ofV ms fd A)
  | .box _ A => ofV ms fd A
  | .bang A => return .bang (← ofV ms fd A)
  | .fam L => return .fam (← ofV ms fd L)
  -- `Tok` is a location owning a unit cell, `Ref 1`'s relation (`vCE_tok_eq_ref`), made by
  -- `alloc` and released by `free` (`tokMint`, `tokBurn`); its view is `Unk` (`Imm̲ 'b Tok`), a
  -- pointer read as discarded (`Layout.joinRe`, `Lower.reVals`).
  | .opq .tok => pure (.ref .unit)
  | .opq k => pure (.opq k)
  | .unk => pure .unk
  | .thunk C => ofU ms fd false C
  -- [spec §68] A per-code closure type has no LIR type yet; nothing past `ofV` sees one.
  | .code _ _ _ => throw "LIR: a per-code closure type is not lowered yet (#855 B1, SPEC §68)"

/-- The LIR type of `U C`, under `∀`s when `under`: `U (∀'x. F A)` is `A`. -/
def ofU (ms : MachSet) (fd : EvSet) (under : Bool) : CTy → Except String LTy
  | .all _ _ C => ofU ms fd true C
  | .ret A => if under then ofV ms fd A else return .thunk (.ret (← ofV ms fd A))
  | C => return .thunk (← ofC ms fd C)

/-- The LIR type of a computation type. A `∀` is its body (SPEC §44). -/
def ofC (ms : MachSet) (fd : EvSet) : CTy → Except String LCTy
  | .ret A => return .ret (← ofV ms fd A)
  | .arr A C => return .arr (← ofV ms fd A) (← ofC ms fd C)
  | .amp C D => do
    let c ← ofC ms fd C
    let d ← ofC ms fd D
    if let (n, _) :: _ := c.stripEv.1 ++ d.stripEv.1 then
      throw (evInternal n "a `&` component")
    return .amp c d
  | .top => pure .top
  | .all _ _ C => ofC ms fd C
  | .nu C => do
    let c ← ofC ms fd C
    if let (n, _) :: _ := c.stripEv.1 then
      throw (evInternal n "a `ν`'s observation")
    return .nu c
  | C@(.eff n i q A B fin _ C') => do
    -- `F_Σ R`: `R`, `R ⊕ P` with the payload of `Σ`'s abortive operations (SPEC §47), or the
    -- outcome at its machine operations (SPEC §49); its evidence first [spec §71].
    if n == divName then
      throw s!"an operation ({n}, {i}) in a computation type: outside the pure fragment"
    let (ps, qs, r) ← ofEff ms fd C'
    let es := evLayers fd C.effNames
    let mach := ms.contains (n, i) && !abortB q B
    if let (m, _) :: _ := es then
      if mach || !qs.isEmpty then throw (evInternal m "a machine's row")
    if abortB q B then return evWrap es (.ret (outcomeTy r (((n, i), ← ofV ms fd A) :: ps) qs))
    else if ms.contains (n, i) then
      -- The cancel row read at a capturable operation only (`ofFinAt`).
      let cp ← if capB q B then ofFin ms fd fin else pure none
      return evWrap es (.ret (outcomeTy r ps (((n, i), ← ofV ms fd A, ← ofV ms fd B, cp) :: qs)))
    else return evWrap es (.ret (outcomeTy r ps qs))

/-- The layers of `F_Σ R` (`CTy.effOf`): each abortive operation's key and argument type, each
machine operation's key, argument type, answer type and cancel row, in the row's order, and `R`.
`Div`'s operations are outside the fragment (N4).  [spec §47, §49] -/
def ofEff (ms : MachSet) (fd : EvSet) : CTy →
    Except String (List ((UInt32 × UInt32) × LTy) ×
      List ((UInt32 × UInt32) × LTy × LTy × Option CancelRow) × LTy)
  | .ret R => return ([], [], ← ofV ms fd R)
  | .eff n i q A B fin _ C => do
    if n == divName then
      throw s!"an operation ({n}, {i}) in a computation type: outside the pure fragment"
    let (ps, qs, r) ← ofEff ms fd C
    if abortB q B then return (((n, i), ← ofV ms fd A) :: ps, qs, r)
    else if ms.contains (n, i) then
      -- The cancel row read at a capturable operation only (`ofFinAt`).
      let cp ← if capB q B then ofFin ms fd fin else pure none
      return (ps, ((n, i), ← ofV ms fd A, ← ofV ms fd B, cp) :: qs, r)
    else return (ps, qs, r)
  | _ => throw "a row's layers over a type that is not `F R`"

/-- A cancel row (`CTy.rowOf`) as its `k` reads it (`CancelRow`): `none` at `⊤`. A machine
operation there (a finaliser that may suspend) is a suspension of the cancel, with its own cancel
row, read at a capturable operation only.  [spec §27, §49] -/
def ofFin (ms : MachSet) (fd : EvSet) : CTy → Except String (Option CancelRow)
  | .top => pure none
  | C => do
    let (ps, qs, us) ← ofFinParts ms fd C
    let ps := dedupPay ps
    let qs := qs.foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []
    return some (.mk ps qs us (outcomeTy .unit ps qs))

/-- The layers of a cancel row: its abortive operations' keys and argument types, its machine
operations' keys, argument and answer types and cancel rows (`ofFin`, at a capturable operation),
and its operations at `unr`, in the row's order. -/
def ofFinParts (ms : MachSet) (fd : EvSet) : CTy →
    Except String (List ((UInt32 × UInt32) × LTy) ×
      List ((UInt32 × UInt32) × LTy × LTy × Option CancelRow) × List (UInt32 × UInt32))
  | .ret _ => pure ([], [], [])
  | .eff n i q A B fin _ C => do
    let (ps, qs, us) ← ofFinParts ms fd C
    let us := if q == .unr then (n, i) :: us else us
    if abortB q B then return (((n, i), ← ofV ms fd A) :: ps, qs, us)
    else if ms.contains (n, i) then
      let cp ← if capB q B then ofFin ms fd fin else pure none
      return (ps, ((n, i), ← ofV ms fd A, ← ofV ms fd B, cp) :: qs, us)
    else return (ps, qs, us)
  | _ => throw "a cancel row that is not a row"
end

/-- The cancel row of an operation `A ↠^q B` as its `k` reads it: `ofFin` of its cancel row `fin`
at a capturable operation (`capB`, as the kernel's `OpSig.ent` reads it), and `none` (`⊤`) at a
must-resume one, whose `κ` has the cancel component `⊤` (`kTy`'s `.lin` case) and is never
cancelled (`kappaC_cancel_lin`). `ofC` and `ofEff` read it the same way, inline.
[spec §27, §49] -/
def ofFinAt (ms : MachSet) (fd : EvSet) (q : Qual) (B : VTy) (fin : CTy) : Except String (Option CancelRow) :=
  if capB q B then ofFin ms fd fin else pure none

/-- `ofV` keeps `!`: the LIR type of `!A` is `!` of `A`'s. -/
theorem ofV_bang (ms : MachSet) (fd : EvSet) (A : VTy) : ofV ms fd (.bang A) = (ofV ms fd A).map .bang := by
  simp only [ofV]
  cases ofV ms fd A <;> rfl

/-! ### What `Lint` reads at a copy and a consume

The two predicates are the checker's, on the LIR type: `VTy.persistent` (a slot a split may
duplicate and a leaf may consume, `Ctx.SplitP.dup`, `Ctx.DeadP.weaken`) and `VTy.Consume` (a slot an abort
may consume, `[let]`'s `Ctx.Consumes`). `ofV` keeps both (`ofV_persistent`, `ofV_consumes`): `!` is on the
LIR type, and what `ofV` erases (lifetimes, `[@a]`, `∀`) neither predicate reads. -/

/-- `VTy.persistent` on the LIR type: values that hold no resource. -/
def LTy.persistent : LTy → Bool
  | .unit | .zero | .unk | .int _ | .tvar _ | .bang _ => true
  | .pair a b | .sum a b => a.persistent && b.persistent
  | .mu a => a.persistent
  | .opq _ | .ref _ | .imm _ | .mut _ | .fam _ | .thunk _ => false

/-- The type holds an opaque value (`.opq`) it owns: one no rule but a `[let]`'s abort (`effLet`'s
`hW`, `Ctx.Consumes`), `⊤` (`topI`) or `0` (`zeroE`) discards. -/
def LTy.ownsOpq : LTy → Bool
  | .opq _ => true
  | .pair a b | .sum a b => a.ownsOpq || b.ownsOpq
  | .mu a => a.ownsOpq
  | _ => false

/-- `VTy.Consume` on the LIR type: values that hold no owned cell. -/
def LTy.consumes : LTy → Bool
  | .unit | .zero | .int _ | .unk | .opq _ | .bang _ | .imm _ | .mut _ => true
  | .pair a b | .sum a b => a.consumes && b.consumes
  | .mu _ | .tvar _ | .ref _ | .fam _ | .thunk _ => false

/-- The LIR type of a persistent type is persistent. -/
theorem ofV_persistent {ms : MachSet} {fd : EvSet} : ∀ {A : VTy} {t : LTy}, A.persistent = true →
    ofV ms fd A = .ok t → t.persistent = true
  | .unit, t, _, h | .zero, t, _, h | .unk, t, _, h | .int _, t, _, h | .tvar _, t, _, h => by
      simp only [ofV] at h; cases h; rfl
  | .bang A, t, _, h => by
      rw [ofV_bang] at h
      cases hA : ofV ms fd A <;> rw [hA] at h <;> cases h; rfl
  | .box _ A, t, hp, h => by
      simp only [ofV] at h
      exact ofV_persistent (by simpa [VTy.persistent] using hp) h
  | .mu A, t, hp, h => by
      simp only [ofV] at h
      cases hA : ofV ms fd A <;> rw [hA] at h <;> cases h
      exact by simpa [LTy.persistent] using ofV_persistent (by simpa [VTy.persistent] using hp) hA
  | .tensor A B, t, hp, h => by
      simp only [VTy.persistent, Bool.and_eq_true] at hp
      simp only [ofV] at h
      cases hA : ofV ms fd A <;> cases hB : ofV ms fd B <;> rw [hA, hB] at h <;> cases h
      simp [LTy.persistent, ofV_persistent hp.1 hA, ofV_persistent hp.2 hB]
  | .sum A B, t, hp, h => by
      simp only [VTy.persistent, Bool.and_eq_true] at hp
      simp only [ofV] at h
      cases hA : ofV ms fd A <;> cases hB : ofV ms fd B <;> rw [hA, hB] at h <;> cases h
      simp [LTy.persistent, ofV_persistent hp.1 hA, ofV_persistent hp.2 hB]
  | .opq _, _, hp, _ | .thunk _, _, hp, _ | .ref _, _, hp, _ | .imm _ _, _, hp, _
  | .mut _ _, _, hp, _ | .fam _, _, hp, _ | .code _ _ _, _, hp, _ => by simp [VTy.persistent] at hp

/-- The LIR type of a `VTy.Consume` type consumes. -/
theorem ofV_consumes {ms : MachSet} {fd : EvSet} {A : VTy} (hA : A.OwnFree) : ∀ {t : LTy}, ofV ms fd A = .ok t →
    t.consumes = true := by
  induction hA with
  | opq k hk =>
    intro t h; cases k <;> simp only [ofV] at h <;> cases h <;>
      first | rfl | exact absurd rfl hk
  | unit | zero | int | unk | imm | «mut» =>
      intro t h; simp only [ofV] at h
      first
        | (cases h; rfl)
        | (rename_i A; cases hA : ofV ms fd A <;> rw [hA] at h <;> cases h; rfl)
  | bang A =>
      intro t h; rw [ofV_bang] at h
      cases hA : ofV ms fd A <;> rw [hA] at h <;> cases h; rfl
  | @tensor A B _ _ ihA ihB | @sum A B _ _ ihA ihB =>
      intro t h; simp only [ofV] at h
      cases hA : ofV ms fd A <;> cases hB : ofV ms fd B <;> rw [hA, hB] at h <;> cases h
      simp [LTy.consumes, ihA hA, ihB hB]

/-- The LIR type of a judgment: a value type, or the closure type a computation's value has
(`rep`). -/
def ofJ (ms : MachSet := {}) (fd : EvSet := {}) : Jdg → Except String (Sum LTy LCTy)
  | .val A => return .inl (← ofV ms fd A)
  | .comp C => return .inr (← ofC ms fd C)

/-! ### Printing -/

def widthName : Width → String
  | .w32 => "i32" | .w64 => "i64" | .w8 => "u8" | .f32 => "f32" | .f64 => "f64"
  | .u32 => "u32" | .u64 => "u64"

mutual
def LTy.pp : LTy → String
  | .unit => "1"
  | .zero => "0"
  | .int w => widthName w
  | .pair a b => s!"({a.pp} * {b.pp})"
  | .sum a b => s!"({a.pp} + {b.pp})"
  | .mu a => s!"mu. {a.pp}"
  | .tvar n => s!"#{n}"
  | .ref a => s!"ref {a.pp}"
  | .imm a => s!"imm {a.pp}"
  | .mut a => s!"mut {a.pp}"
  | .fam l => s!"[{l.pp}]"
  | .opq k => match k with
    | .input => "Input" | .output => "Output" | .clock => "Clock" | .args => "Args" | .tok => "Tok"
  | .unk => "Unk"
  | .thunk k => s!"U {k.pp}"
  | .bang a => s!"!{a.pp}"
def LCTy.pp : LCTy → String
  | .ret a => s!"F {a.pp}"
  | .arr a k => s!"({a.pp} -o {k.pp})"
  | .amp k₁ k₂ => s!"({k₁.pp} & {k₂.pp})"
  | .top => "T"
  | .nu k => s!"nu. {k.pp}"
  | .ev n e k => s!"(ev {n} {e.pp} -o {k.pp})"
end

instance : ToString LTy := ⟨LTy.pp⟩
instance : ToString LCTy := ⟨LCTy.pp⟩

end Backend2
