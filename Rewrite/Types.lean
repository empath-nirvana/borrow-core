import Frontend.Check.Program

/-!
# Rewrite — R0's translation of types  `[spec §54]`

R0 (#680, the scope's §R0) eliminates an abortive name `n` (every operation of `n` at the count
`0`) by the exceptions-as-sums translation `⟦−⟧ₙ`. On types it is homomorphic on every former but
the returner chain:

```
⟦F_Σ A⟧ₙ = F_{Σ∖n}(⟦A⟧ₙ ⊕ P_n)     if n ∈ Σ
⟦F_Σ A⟧ₙ = F_Σ ⟦A⟧ₙ               otherwise
```

`P_n` is the name's payload, the sum of its operations' arguments in operation order, nested to
the right (`A₀ ⊕ (A₁ ⊕ …)`); a name of one operation pays its argument. A row is translated
operation by operation, `n`'s removed. Every function type, `def` types included, translates
through its codomain.
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core (VTy CTy OpSig Row Count FShape Shape)

/-- **An abortive name** R0 rewrites: its number and its operations' arguments, in operation order
(the operation `j` is `n.j`). -/
structure AbortName where
  n : UInt32
  args : List VTy
  deriving Inhabited

/-- The payload of a list of arguments: their sum, nested to the right; one argument is itself. -/
def payloadOf : List VTy → VTy
  | [] => .zero
  | [A] => A
  | A :: As => .sum A (payloadOf As)

/-- `P_n`. -/
def AbortName.P (a : AbortName) : VTy := payloadOf a.args

/-- The returner chain `C` holds an operation of `n`. -/
def chainHas (n : UInt32) : CTy → Bool
  | .eff m _ _ _ _ _ _ C => m == n || chainHas n C
  | _ => false

mutual
/-- `⟦A⟧ₙ` at a value type: homomorphic. -/
def trV (a : AbortName) : VTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor (trV a A) (trV a B)
  | .zero => .zero
  | .sum A B => .sum (trV a A) (trV a B)
  | .thunk C => .thunk (trC a C)
  | .ref A => .ref (trV a A)
  | .imm l A => .imm l (trV a A)
  | .mut l A => .mut l (trV a A)
  | .box l A => .box l (trV a A)
  | .bang A => .bang (trV a A)
  | .unk => .unk
  | .tvar k => .tvar k
  | .mu A => .mu (trV a A)
  | .int w => .int w
  | .fam L => .fam (trV a L)
  | .opq k => .opq k
/-- `⟦C⟧ₙ` at a computation type: homomorphic but at a returner chain, whose operations of `n` are
removed and whose answer becomes `⟦A⟧ₙ ⊕ P_n` when it holds one (`trChain`). -/
def trC (a : AbortName) : CTy → CTy
  | .ret A => .ret (trV a A)
  | .arr A C => .arr (trV a A) (trC a C)
  | .amp C D => .amp (trC a C) (trC a D)
  | .top => .top
  | .all x b C => .all x b (trC a C)
  | .nu C => .nu (trC a C)
  | .eff m i c w A B fin C =>
    let has := m == a.n || chainHas a.n C
    if m == a.n then trChain a has C
    else .eff m i c w (trV a A) (trV a B) (trC a fin) (trChain a has C)
/-- The rest of a returner chain, `has` when the whole chain holds an operation of `n`. -/
def trChain (a : AbortName) (has : Bool) : CTy → CTy
  | .eff m i c w A B fin C =>
    if m == a.n then trChain a has C
    else .eff m i c w (trV a A) (trV a B) (trC a fin) (trChain a has C)
  | .ret R => .ret (if has then .sum (trV a R) a.P else trV a R)
  | .arr A C => .arr (trV a A) (trC a C)
  | .amp C D => .amp (trC a C) (trC a D)
  | .top => .top
  | .all x b C => .all x b (trC a C)
  | .nu C => .nu (trC a C)
end

/-- An operation's signature: its argument, answer and cancel row translated. -/
def trOp (a : AbortName) (o : OpSig) : OpSig :=
  { o with A := trV a o.A, B := trV a o.B, fin := trC a o.fin }

/-- `⟦Σ⟧ₙ`: `Σ∖n`, each other operation translated. -/
def trRow (a : AbortName) (S : Row) : Row :=
  (S.filter (·.n != a.n)).map (trOp a)

/-- The row holds an operation of `n`. -/
def rowHas (n : UInt32) (S : Row) : Bool := S.any (·.n == n)

/-- A handler's operations, translated. -/
def trE (a : AbortName) (E : List (Count × VTy × VTy)) : List (Count × VTy × VTy) :=
  E.map fun (q, A, B) => (q, trV a A, trV a B)

/-- A judgment, translated. -/
def trJ (a : AbortName) : BoCa.Fig16.LogRel.Core.Jdg → BoCa.Fig16.LogRel.Core.Jdg
  | .val A => .val (trV a A)
  | .comp C => .comp (trC a C)

/-- A fold's shape, its leaves translated. -/
def trFShape (a : AbortName) : FShape → FShape
  | .leaf A => .leaf (trV a A)
  | .refX => .refX
  | .varX => .varX
  | .tensor F G => .tensor (trFShape a F) (trFShape a G)
  | .sum F G => .sum (trFShape a F) (trFShape a G)

/-- A block's shape, its leaves translated. -/
def trShape (a : AbortName) : Shape → Shape
  | .leaf A => .leaf (trV a A)
  | .node s t => .node (trShape a s) (trShape a t)

/-! ### The translation of a returner chain -/

theorem chainHas_effOf (n : UInt32) : ∀ (S : Row) (A : VTy), chainHas n (CTy.effOf S A) = rowHas n S
  | [], _ => rfl
  | o :: S, A => by
    simp only [CTy.effOf, chainHas, rowHas, List.any_cons, chainHas_effOf n S A]

theorem trChain_effOf (a : AbortName) (has : Bool) : ∀ (S : Row) (A : VTy),
    trChain a has (CTy.effOf S A) =
      CTy.effOf (trRow a S) (if has then .sum (trV a A) a.P else trV a A)
  | [], _ => by simp [CTy.effOf, trChain, trRow]
  | o :: S, A => by
    by_cases h : o.n = a.n
    · simp [CTy.effOf, trChain, trRow, h, trChain_effOf a has S A]
    · simp [CTy.effOf, trChain, trRow, h, trChain_effOf a has S A, trOp]

/-- **The translation of `F_Σ A`**: `F_{⟦Σ⟧ₙ}(⟦A⟧ₙ ⊕ P_n)` at a row holding `n`, `F_{⟦Σ⟧ₙ} ⟦A⟧ₙ`
otherwise. -/
theorem trC_effOf (a : AbortName) (S : Row) (A : VTy) :
    trC a (CTy.effOf S A) =
      CTy.effOf (trRow a S) (if rowHas a.n S then .sum (trV a A) a.P else trV a A) := by
  cases S with
  | nil => simp [CTy.effOf, trC, trRow, rowHas]
  | cons o S =>
    have hc := chainHas_effOf a.n S A
    by_cases h : o.n = a.n
    · simp [CTy.effOf, trC, trRow, rowHas, h, trChain_effOf]
    · simp [CTy.effOf, trC, trRow, rowHas, h, hc, trChain_effOf, trOp]

end Rewrite
