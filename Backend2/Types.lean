import Frontend.Check.TExpr

/-!
# Backend2 — the types of the low IR  `[spec §3]`

The low IR (LIR) is typed by the checked term's types with what has no run-time content erased:
lifetimes, the lifetime box `[@a] A`, and `!A`. A value type `VTy` becomes an `LTy`, a computation
type `CTy` an `LCTy`, constructor for constructor (`ofV`, `ofC`): no type is inferred here, each is
the image of a type the checker put on a node of the typed term.

* `U C` is a closure, `thunk K`. A closure of `F A` takes no argument (the erasure's `λ_. M`,
  applied to `()`), a closure of `A ⊸ C` takes an `A`, and a closure of `C & D` is observed at one
  of its two components. `νX. C` is its unrolling: `U X` is the type variable `0` of `C`'s value
  types, as in `VTy`.
* `∀'x. C` is `C` (SPEC §44): a `Λ` is its body, a λ-value (`allI_inst`), so `U (∀'x. F A)` is
  `A` and `U (∀'x. C)` is `U C`; no instantiation has run-time content.
* `Ref A` is an owned cell, `Imm A` and `Mut A` borrows of one, `[L]` a family of leaves `L`
  (an array is `[Ref A]`).
* A row's abortive operations are its computation's way out (SPEC §48): `F_Σ R` answers
  `R ⊕ P`, `P` the payload of `Σ`'s abortive operations (`rowPay`), one summand per operation in
  the row's order; with none, `R`. A non-abortive operation has no run-time content in the type:
  its handler's clause is called where it is performed (`Backend2/Convert.lean`). `Div`'s
  `tick` is linear, so it is not abortive: it has no run-time content in the type, and its
  handler, the runtime, answers it where it is performed (SPEC §49).
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
  deriving Inhabited, BEq, Hashable

/-- A computation type of the LIR: what a closure answers when it is run. -/
inductive LCTy where
  | ret (a : LTy)
  | arr (a : LTy) (k : LCTy)
  | amp (k₁ k₂ : LCTy)
  | top
  /-- `νX. C`, binding the type variable `0` (standing for `U (νX. C)`) in `C`'s value types. -/
  | nu (k : LCTy)
  deriving Inhabited, BEq, Hashable
end

/-- An operation of a row is abortive: answer `0` at a qualifier with weakening (`OpSig.abort`). -/
def abortB (q : Qual) (B : VTy) : Bool := B.isZero && q != .lin

/-- The payload of a row's abortive operations (`ofEff`'s list): each key once, its first, as
`Row.find` reads a row; their argument types a right-nested sum, one summand per operation, in
the row's order; `none` at none.  `[spec §48]` -/
def payOf (ps : List ((UInt32 × UInt32) × LTy)) : Option LTy :=
  let ks := ps.foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []
  ks.reverse.foldl (fun acc p => match acc with
    | none => some p.2
    | some t => some (.sum p.2 t)) none

/-- The name of `Div` (SPEC §14). -/
def divName : UInt32 := 0xFFFFFFFF

mutual
/-- The LIR type of a value type: lifetimes, `[@a]`, `!` and `∀` erased. -/
def ofV : VTy → Except String LTy
  | .unit => pure .unit
  | .zero => pure .zero
  | .int w => pure (.int w)
  | .tensor A B => return .pair (← ofV A) (← ofV B)
  | .sum A B => return .sum (← ofV A) (← ofV B)
  | .mu A => return .mu (← ofV A)
  | .tvar n => pure (.tvar n)
  | .ref A => return .ref (← ofV A)
  | .imm _ A => return .imm (← ofV A)
  | .mut _ A => return .mut (← ofV A)
  | .box _ A => ofV A
  | .bang A => ofV A
  | .fam L => return .fam (← ofV L)
  | .opq k => pure (.opq k)
  | .unk => pure .unk
  | .thunk C => ofU false C

/-- The LIR type of `U C`, under `∀`s when `under`: `U (∀'x. F A)` is `A`. -/
def ofU (under : Bool) : CTy → Except String LTy
  | .all _ _ C => ofU true C
  | .ret A => if under then ofV A else return .thunk (.ret (← ofV A))
  | C => return .thunk (← ofC C)

/-- The LIR type of a computation type. A row's operation is outside the pure fragment. A `∀` is
its body (SPEC §44). -/
def ofC : CTy → Except String LCTy
  | .ret A => return .ret (← ofV A)
  | .arr A C => return .arr (← ofV A) (← ofC C)
  | .amp C D => return .amp (← ofC C) (← ofC D)
  | .top => pure .top
  | .all _ _ C => ofC C
  | .nu C => return .nu (← ofC C)
  | .eff n i q A B _ C => do
    -- `F_Σ R`: `R`, or `R ⊕ P` with the payload of `Σ`'s abortive operations.  [spec §48]
    let (ps, r) ← ofEff C
    let ps ← if abortB q B then pure (((n, i), ← ofV A) :: ps) else pure ps
    match payOf ps with
    | none => return .ret r
    | some p => return .ret (.sum r p)

/-- The layers of `F_Σ R` (`CTy.effOf`): each abortive operation's key and argument type, in the
row's order, and `R`. `Div`'s `tick` is linear, so not a layer (SPEC §49).  [spec §48] -/
def ofEff : CTy → Except String (List ((UInt32 × UInt32) × LTy) × LTy)
  | .ret R => return ([], ← ofV R)
  | .eff n i q A B _ C => do
    let (ps, r) ← ofEff C
    if abortB q B then return (((n, i), ← ofV A) :: ps, r) else return (ps, r)
  | _ => throw "a row's layers over a type that is not `F R`"
end

/-- The LIR type of a judgment: a value type, or the closure type a computation's value has
(`rep`). -/
def ofJ : Jdg → Except String (Sum LTy LCTy)
  | .val A => return .inl (← ofV A)
  | .comp C => return .inr (← ofC C)

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

/-- A closure type as its observations see it: `νX. C` unrolled, until it is not a `ν`. -/
def LCTy.whnf : Nat → LCTy → LCTy
  | f + 1, .nu k => LCTy.whnf f k.unrollNu
  | _, k => k

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
