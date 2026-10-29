import Std.Data.HashSet
import Frontend.Check.TExpr

/-!
# Backend2 — the types of the low IR  `[spec §3]`

The low IR (LIR) is typed by the checked term's types with what has no run-time content erased:
lifetimes and the lifetime box `[@a] A`. A value type `VTy` becomes an `LTy`, a computation
type `CTy` an `LCTy`, constructor for constructor (`ofV`, `ofC`): no type is inferred here, each is
the image of a type the checker put on a node of the typed term.

* `!A` is kept (`bang`): it has no run-time content (its value is `A`'s), but it is the type's
  statement that the value is persistent, which `Lint` reads at every copy and drop.
* `U C` is a closure, `thunk K`. A closure of `F A` takes no argument (the erasure's `λ_. M`,
  applied to `()`), a closure of `A ⊸ C` takes an `A`, and a closure of `C & D` is observed at one
  of its two components. `νX. C` is its unrolling: `U X` is the type variable `0` of `C`'s value
  types, as in `VTy`.
* `∀'x. C` is `C` (SPEC §44): a `Λ` is its body, a λ-value (`allI_inst`), so `U (∀'x. F A)` is
  `A` and `U (∀'x. C)` is `U C`; no instantiation has run-time content.
* `Ref A` is an owned cell, `Imm A` and `Mut A` borrows of one, `[L]` a family of leaves `L`
  (an array is `[Ref A]`).
* A row's abortive operations are its computation's way out (SPEC §47): `F_Σ R` answers
  `R ⊕ P`, `P` the payload of `Σ`'s abortive operations (`rowPay`), one summand per operation in
  the row's order; with none, `R`. A non-abortive operation whose clause is called where it is
  performed has no run-time content in the type (`Backend2/Convert.lean`). `Div`'s `tick` is
  linear, so it is not abortive, and it is not a machine operation (no `handle` node handles it):
  it has no run-time content in the type, and its handler, the runtime, answers it where it is
  performed (SPEC §62).
* A row's **machine operations** (SPEC §49), the control operations of the program's set `ms`
  (those whose clause at some `handle` node of their name is not called where they are
  performed), make `F_Σ R` an *outcome*: `μY. R ⊕ (P ⊕ S)`, `S` one summand per machine
  operation `A ↠ B` of `Σ`, in the row's order, holding its argument and the suspended
  computation `U((B ⊸ F Y) & F (1 ⊕ P))`: resumed with the answer, it answers the outcome again;
  cancelled, it answers `()` or the first error its finalisers raised (`outcomeTy`).
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
end

/-- `A[μX. A/X]`. -/
def LTy.unrollMu (a : LTy) : LTy := LTy.subst 0 (.mu a) a

/-- `C[U(νX. C)/X]`. -/
def LCTy.unrollNu (k : LCTy) : LCTy := LCTy.subst 0 (.thunk (.nu k)) k

/-! ### `!` up to representation

`!A` is represented as `A`. A decision about a value's representation (its layout, its words, which
closure it is) reads its type through `peel`, the top-level `!`s removed; one that compares two
types for a representation compares them with `!` erased throughout (`unbang`, `sameRep`). `Lint`
reads `!` itself, and the conversion's keys keep it (a `use` body's, a destructor's: a key fixes
the LIR types of what it converts). -/

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

/-- What cancelling a computation suspended at an operation answers (SPEC §49): `()`, or the first
error its finalisers raised, one of the operation's cancel row's abortive operations (`cp`, its
payload's summands); `1` at a cancel row `⊤` (a linear operation, never cancelled). -/
def cancelResTy (cp : Option (List ((UInt32 × UInt32) × LTy))) : LTy :=
  match cp.bind payOf with
  | none => .unit
  | some p => .sum .unit p

/-- **The outcome of a computation** at a row with machine operations  `[spec §49]`: `R`, the
payload `P` of the row's abortive operations (`payOf`), and for each machine operation `A ↠ B`
(each key once, in the row's order) its argument beside the suspended computation,
`U((B ⊸ F Y) & F C)`, `Y` the outcome itself and `C` what its cancel answers (`cancelResTy`, at
the operation's cancel row): `μY. R ⊕ (P ⊕ S)`, or `μY. R ⊕ S` with no abortive operation. With
no machine operation it is `R ⊕ P`, or `R`. `R`'s free type variables (an `X` of a `ν`) are
lifted under the `μ`. -/
def outcomeTy (r : LTy) (aborts : List ((UInt32 × UInt32) × LTy))
    (machs : List ((UInt32 × UInt32) × LTy × LTy × Option (List ((UInt32 × UInt32) × LTy)))) : LTy :=
  let ms := machs.foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []
  match ms with
  | [] => match payOf aborts with
    | none => r
    | some p => .sum r p
  | _ =>
    let pay := payOf aborts
    let kT (b : LTy) (cp : Option (List ((UInt32 × UInt32) × LTy))) : LTy :=
      .thunk (.amp (.arr (b.lift 0) (.ret (.tvar 0))) (.ret ((cancelResTy cp).lift 0)))
    let s := (payOf (ms.map fun (k, a, b, cp) => (k, .pair (a.lift 0) (kT b cp)))).getD .unit
    let x := match pay with
      | none => s
      | some p => .sum (p.lift 0) s
    .mu (.sum (r.lift 0) x)

mutual
/-- A value type of the LIR: lifetimes, `[@a]` and `∀` erased, `!` kept; `ms` the program's
machine operations. -/
def ofV (ms : MachSet) : VTy → Except String LTy
  | .unit => pure .unit
  | .zero => pure .zero
  | .int w => pure (.int w)
  | .tensor A B => return .pair (← ofV ms A) (← ofV ms B)
  | .sum A B => return .sum (← ofV ms A) (← ofV ms B)
  | .mu A => return .mu (← ofV ms A)
  | .tvar n => pure (.tvar n)
  | .ref A => return .ref (← ofV ms A)
  | .imm _ A => return .imm (← ofV ms A)
  | .mut _ A => return .mut (← ofV ms A)
  | .box _ A => ofV ms A
  | .bang A => return .bang (← ofV ms A)
  | .fam L => return .fam (← ofV ms L)
  | .opq k => pure (.opq k)
  | .unk => pure .unk
  | .thunk C => ofU ms false C

/-- The LIR type of `U C`, under `∀`s when `under`: `U (∀'x. F A)` is `A`. -/
def ofU (ms : MachSet) (under : Bool) : CTy → Except String LTy
  | .all _ _ C => ofU ms true C
  | .ret A => if under then ofV ms A else return .thunk (.ret (← ofV ms A))
  | C => return .thunk (← ofC ms C)

/-- The LIR type of a computation type. A `∀` is its body (SPEC §44). -/
def ofC (ms : MachSet) : CTy → Except String LCTy
  | .ret A => return .ret (← ofV ms A)
  | .arr A C => return .arr (← ofV ms A) (← ofC ms C)
  | .amp C D => return .amp (← ofC ms C) (← ofC ms D)
  | .top => pure .top
  | .all _ _ C => ofC ms C
  | .nu C => return .nu (← ofC ms C)
  | .eff n i q A B fin _ C => do
    -- `F_Σ R`: `R`, `R ⊕ P` with the payload of `Σ`'s abortive operations (SPEC §47), or the
    -- outcome at its machine operations (SPEC §49). `Div`'s `tick` is neither (SPEC §62).
    let (ps, qs, r) ← ofEff ms C
    if abortB q B then return .ret (outcomeTy r (((n, i), ← ofV ms A) :: ps) qs)
    else if ms.contains (n, i) then
      return .ret (outcomeTy r ps (((n, i), ← ofV ms A, ← ofV ms B, ← ofFin ms fin) :: qs))
    else return .ret (outcomeTy r ps qs)

/-- The layers of `F_Σ R` (`CTy.effOf`): each abortive operation's key and argument type, each
machine operation's key, argument type, answer type and cancel row's payload, in the row's order,
and `R`. `Div`'s `tick` is neither, so not a layer (SPEC §62).  [spec §47, §49, §62] -/
def ofEff (ms : MachSet) : CTy →
    Except String (List ((UInt32 × UInt32) × LTy) ×
      List ((UInt32 × UInt32) × LTy × LTy × Option (List ((UInt32 × UInt32) × LTy))) × LTy)
  | .ret R => return ([], [], ← ofV ms R)
  | .eff n i q A B fin _ C => do
    let (ps, qs, r) ← ofEff ms C
    if abortB q B then return (((n, i), ← ofV ms A) :: ps, qs, r)
    else if ms.contains (n, i) then return (ps, ((n, i), ← ofV ms A, ← ofV ms B, ← ofFin ms fin) :: qs, r)
    else return (ps, qs, r)
  | _ => throw "a row's layers over a type that is not `F R`"

/-- A cancel row's abortive operations (`CTy.rowOf`): `none` at `⊤`. A machine operation there (a
finaliser that may suspend) is outside the fragment.  [spec §27, §49] -/
def ofFin (ms : MachSet) : CTy → Except String (Option (List ((UInt32 × UInt32) × LTy)))
  | .top => pure none
  | .ret _ => pure (some [])
  | .eff n i q A B _ _ C => do
    let rest ← ofFin ms C
    if abortB q B then return rest.map (((n, i), ← ofV ms A) :: ·)
    else if ms.contains (n, i) then
      throw s!"a cancel row holding the machine operation ({n}, {i}): outside the fragment"
    else return rest
  | _ => throw "a cancel row that is not a row"
end

/-- `ofV` keeps `!`: the LIR type of `!A` is `!` of `A`'s. -/
theorem ofV_bang (ms : MachSet) (A : VTy) : ofV ms (.bang A) = (ofV ms A).map .bang := by
  simp only [ofV]
  cases ofV ms A <;> rfl

/-! ### What `Lint` reads at a copy and a drop

The two predicates are the checker's, on the LIR type: `VTy.persistent` (a slot a split may
duplicate and a leaf may drop, `Ctx.SplitP.dup`, `Ctx.DeadP.drop`) and `VTy.Drop` (a slot an abort
may drop, `[let]`'s `Ctx.Drops`). `ofV` keeps both (`ofV_persistent`, `ofV_drops`): `!` is on the
LIR type, and what `ofV` erases (lifetimes, `[@a]`, `∀`) neither predicate reads. -/

/-- `VTy.persistent` on the LIR type: values that hold no resource. -/
def LTy.persistent : LTy → Bool
  | .unit | .zero | .unk | .int _ | .tvar _ | .bang _ => true
  | .pair a b | .sum a b => a.persistent && b.persistent
  | .mu a => a.persistent
  | .opq _ | .ref _ | .imm _ | .mut _ | .fam _ | .thunk _ => false

/-- `VTy.Drop` on the LIR type: values that hold no owned cell. -/
def LTy.drops : LTy → Bool
  | .unit | .zero | .int _ | .unk | .opq _ | .bang _ | .imm _ | .mut _ => true
  | .pair a b | .sum a b => a.drops && b.drops
  | .mu _ | .tvar _ | .ref _ | .fam _ | .thunk _ => false

/-- The LIR type of a persistent type is persistent. -/
theorem ofV_persistent {ms : MachSet} : ∀ {A : VTy} {t : LTy}, A.persistent = true →
    ofV ms A = .ok t → t.persistent = true
  | .unit, t, _, h | .zero, t, _, h | .unk, t, _, h | .int _, t, _, h | .tvar _, t, _, h => by
      simp only [ofV] at h; cases h; rfl
  | .bang A, t, _, h => by
      rw [ofV_bang] at h
      cases hA : ofV ms A <;> rw [hA] at h <;> cases h; rfl
  | .box _ A, t, hp, h => by
      simp only [ofV] at h
      exact ofV_persistent (by simpa [VTy.persistent] using hp) h
  | .mu A, t, hp, h => by
      simp only [ofV] at h
      cases hA : ofV ms A <;> rw [hA] at h <;> cases h
      exact by simpa [LTy.persistent] using ofV_persistent (by simpa [VTy.persistent] using hp) hA
  | .tensor A B, t, hp, h => by
      simp only [VTy.persistent, Bool.and_eq_true] at hp
      simp only [ofV] at h
      cases hA : ofV ms A <;> cases hB : ofV ms B <;> rw [hA, hB] at h <;> cases h
      simp [LTy.persistent, ofV_persistent hp.1 hA, ofV_persistent hp.2 hB]
  | .sum A B, t, hp, h => by
      simp only [VTy.persistent, Bool.and_eq_true] at hp
      simp only [ofV] at h
      cases hA : ofV ms A <;> cases hB : ofV ms B <;> rw [hA, hB] at h <;> cases h
      simp [LTy.persistent, ofV_persistent hp.1 hA, ofV_persistent hp.2 hB]
  | .opq _, _, hp, _ | .thunk _, _, hp, _ | .ref _, _, hp, _ | .imm _ _, _, hp, _
  | .mut _ _, _, hp, _ | .fam _, _, hp, _ => by simp [VTy.persistent] at hp

/-- The LIR type of a `VTy.Drop` type drops. -/
theorem ofV_drops {ms : MachSet} {A : VTy} (hA : A.Drop) : ∀ {t : LTy}, ofV ms A = .ok t →
    t.drops = true := by
  induction hA with
  | unit | zero | int | unk | opq | imm | «mut» =>
      intro t h; simp only [ofV] at h
      first
        | (cases h; rfl)
        | (rename_i A; cases hA : ofV ms A <;> rw [hA] at h <;> cases h; rfl)
  | bang A =>
      intro t h; rw [ofV_bang] at h
      cases hA : ofV ms A <;> rw [hA] at h <;> cases h; rfl
  | @tensor A B _ _ ihA ihB | @sum A B _ _ ihA ihB =>
      intro t h; simp only [ofV] at h
      cases hA : ofV ms A <;> cases hB : ofV ms B <;> rw [hA, hB] at h <;> cases h
      simp [LTy.drops, ihA hA, ihB hB]

/-- The LIR type of a judgment: a value type, or the closure type a computation's value has
(`rep`). -/
def ofJ (ms : MachSet := {}) : Jdg → Except String (Sum LTy LCTy)
  | .val A => return .inl (← ofV ms A)
  | .comp C => return .inr (← ofC ms C)

/-! ### Printing -/

def widthName : Width → String
  | .w32 => "i32" | .w64 => "i64" | .w8 => "u8" | .f32 => "f32" | .f64 => "f64"

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
    | .input => "Input" | .output => "Output" | .clock => "Clock" | .args => "Args"
  | .unk => "Unk"
  | .thunk k => s!"U {k.pp}"
  | .bang a => s!"!{a.pp}"
def LCTy.pp : LCTy → String
  | .ret a => s!"F {a.pp}"
  | .arr a k => s!"({a.pp} -o {k.pp})"
  | .amp k₁ k₂ => s!"({k₁.pp} & {k₂.pp})"
  | .top => "T"
  | .nu k => s!"nu. {k.pp}"
end

instance : ToString LTy := ⟨LTy.pp⟩
instance : ToString LCTy := ⟨LCTy.pp⟩

end Backend2
