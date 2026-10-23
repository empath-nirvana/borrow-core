import Rewrite.Types
import Frontend.Check.TShift
import Frontend.Check.Reinfo

/-!
# Rewrite — R0, abort  `[spec §54]`

R0 (#680, the scope's §R0) eliminates an abortive name `n`, every operation of which is at the
count `0`, by the exceptions-as-sums translation `⟦−⟧ₙ` over the typed program: a computation's
answer becomes a sum (`Rewrite/Types.lean`), each `raise` the matching injection, each handler of
`n` a `case` on the sum, and a `[then]`'s finaliser runs on the abort path. One rule per
constructor; every constructor not listed is homomorphic (its types translated, its children
rewritten). At a row holding `n`:

```
raise_{n.j} V                    ↦ return (inr (ι_j V))
return V  (a [sub] from n ∉ S)   ↦ M to x. return (inl x)                 (effSub S → S', n ∈ S')
perform_{m.i} V   (m ≠ n)        ↦ perform_{m.i} V to y. return (inl y)
M to x. N                        ↦ ⟦M⟧ to r. case r { inl x → ⟦N⟧ | inr p → return (inr p) }
M then x. N fin D                ↦ ⟦M⟧ to r. case r { inl x → ⟦N⟧ | inr p → ⟦D⟧ to d. return (inr p) }
handle_m e with (h, cs)  (m ≠ n) ↦ handle_m ⟦e⟧ with (λr. case r { inl a → h a | inr p → return (inr p) }, ⟦cs⟧)
handle_n e with (h, cs)          ↦ ⟦e⟧ to r. case r { inl a → h a | inr (ι_j v) → c_j v }
withborkU td r (Λ.λm. M)         ↦ withbork r (Λ.λm. box-lift ⟦M⟧) to (r, s).
                                     case s { inl b → return (inl (r, b)) | inr p → td r; return (inr p) }
```

The rule reads only the checked facts the scope's §2 lists: the node kinds and their rows and
types, the operations' counts, the `[then]`'s finaliser and an unwinding borrow's destructor. It
adds no drop: the `inr` arms' drops are licensed by `[let]`'s `Σ.Weak → Γ.Drops` and `[then]`'s
finaliser, and the kernel's re-check places them (§12) and verifies them. A `[then]` finaliser
`D` the checker inserted (drop glue, not `written`) is read back as the drops it is, which the
re-check places again in the `inr` arm.

**What the rules write where a source node held a type** (the read-back writes no other
annotation). The checker synthesizes neither an injection nor a term a removed node checked, so:
- each injection R0 writes is written at its sum type (`TInfo.asc`);
- the handled computation of a removed handler of `n` is written at the type `[handle]` checked
  it at, translated (`(⟦e⟧ : F_{⟦Σ⟧ₙ}(⟦A⟧ₙ ⊕ P_n))`);
- the binding the `[sub]` rule writes is annotated with the answer the `[sub]` node held, and the
  binding the `[let]`/`[then]` rules write is annotated, with the annotation's translation, where
  the program annotated the source's (`TInfo.ann`).

**Rows `rEffThen` does not write.** A `[then]`'s finaliser is at the empty row (`rEffThen`), so
`⟦D⟧ = D` and the schema's `case` on `D`'s own abort does not arise; a finaliser at a row is a
hard error.
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core (VTy CTy OpSig Row Count Jdg)
open BoCa.Fig16.LogRel.Core.Check (TExpr TInfo Masks)

/-- **A fault planted in R0** for the reject tests (`bcc rewrite --seed`): R0 as written (`none`);
its `[then]` rule with the finaliser missing from the abort arm (`dropFin`); or run twice there
(`dupFin`). The compile plants none. -/
inductive Seed where
  | none
  | dropFin
  | dupFin
  deriving DecidableEq, Repr, Inhabited

/-- What R0's run records for the guard, per node visited (a `def`'s body at each use), and the
fault it plants. -/
structure AbStats where
  seed : Seed := .none
  /-- The `!`-introductions R0 writes: one per forwarding answer clause (`handle_m`, `m ≠ n`). -/
  bangs : Nat := 0
  deriving Inhabited

/-- R0's monad: its statistics, and a hard error. -/
abbrev AbM := StateT AbStats (Except String)

/-- The name R0 gives the binders it writes; the read-back numbers each by its depth
(`Cx.binder`), and no source binder is named so. -/
def r0B : String := "%R0"

/-- A node's information at the span `sp`. -/
def infoAt (sp : Frontend.Span) : TInfo := { sp }

/-- The masks of a node R0 writes: the re-check computes the node's own. -/
def noMasks : Masks := ⟨[]⟩

/-- `t : F_{S₀} A` at the row `S₁ ⊇ S₀`: an inserted `[sub]` (`TInfo.ins`) where the rows differ. -/
def liftTo (sp : Frontend.Span) (S₀ S₁ : Row) (A : VTy) (t : TExpr) : TExpr :=
  if decide (S₀ = S₁) then t else .effSub { sp, ins := true } (.comp (CTy.effOf S₁ A)) S₀ S₁ A t

/-- `M to x. N` at the row `S`, `M : F_S A`, `N : F_S B` under `x : A`: `[let]`, or `[bind]` at
the empty row. `x` is named `nm`, and annotated with `A` when `ann`. -/
def bindAt (sp : Frontend.Span) (nm : String) (S : Row) (A B : VTy) (tM tN : TExpr)
    (ann : Bool := false) : TExpr :=
  let i : TInfo := { sp, binders := [nm], ann }
  if S.isEmpty then .bind i (.comp (.ret B)) A (.ret B) noMasks tM tN
  else .effLet i (.comp (CTy.effOf S B)) A B S noMasks tM tN

/-- The variable `k` at the type `A`. -/
def varAt (sp : Frontend.Span) (k : Nat) (A : VTy) : TExpr := .var (infoAt sp) (.val A) k A

/-- `inl V : A ⊕ B`, written at its type. -/
def inlAt (sp : Frontend.Span) (A B : VTy) (t : TExpr) : TExpr :=
  .sumI₁ { sp, asc := true } (.val (.sum A B)) A B t

/-- `inr V : A ⊕ B`, written at its type. -/
def inrAt (sp : Frontend.Span) (A B : VTy) (t : TExpr) : TExpr :=
  .sumI₂ { sp, asc := true } (.val (.sum A B)) A B t

/-- `return V : F A`. -/
def retAt (sp : Frontend.Span) (A : VTy) (t : TExpr) : TExpr := .ret (infoAt sp) (.comp (.ret A)) A t

/-- `case V { inl x → M | inr y → N }` at `C`, `V : A ⊕ B`; `x` named `nm`. -/
def caseAt (sp : Frontend.Span) (nm : String) (A B : VTy) (C : CTy) (tV t₁ t₂ : TExpr) : TExpr :=
  .sumE { sp, binders := [nm, r0B] } (.comp C) A B C noMasks tV t₁ t₂

/-- **`ι_j V`**, the injection of the operation `j`'s argument into the payload of `args`. -/
def injPay (sp : Frontend.Span) : List VTy → Nat → TExpr → Except String TExpr
  | [], _, _ => throw "R0: an injection into the payload of a name with no operation"
  | [_], 0, t => pure t
  | A :: As, 0, t => pure (inlAt sp A (payloadOf As) t)
  | A :: As, j + 1, t => do pure (inrAt sp A (payloadOf As) (← injPay sp As j t))

/-- `h a`: the answer clause `h : !U(A ⊸ F_S R)` (a value at the context) applied to the variable
`k : A`: `hf <- return (unbang h); (force hf) k`. -/
def applyAt (sp : Frontend.Span) (h : TExpr) (k : Nat) (A : VTy) (C : CTy) : TExpr :=
  let U : VTy := .thunk (.arr A C)
  .bind { sp, binders := [r0B] } (.comp C) U C noMasks (retAt sp U (.bangE (infoAt sp) (.val U) U h))
    (.app (infoAt sp) (.comp C) (k + 1) A C noMasks (.force (infoAt sp) (.comp (.arr A C)) 0 (.arr A C)))

/-- **The clause of the payload's summand**: at the payload variable `pk` (of the payload of
`args`) and the clauses' tuple `cs` (a value at the context, of type `csTy`, each clause
`!U(A_j ⊸ C)`), the clause of the summand the payload is in, applied to it. The tuple is taken
apart once, a clause at a time (`let (c, rest) = cs`), and a `case` down the payload sends each
summand to its clause; the clauses no arm applies are dropped (they are `!`). -/
def dispatch (sp : Frontend.Span) (C : CTy) : List VTy → Nat → TExpr → VTy → Except String TExpr
  | [], _, _, _ => throw "R0: a handler of a name with no operation"
  | A :: As, pk, cs, csTy => do
    let .tensor cTy restTy := csTy | throw "R0: a handler's clauses are not a tuple"
    let .bang (.thunk (.arr A' _)) := cTy | throw "R0: an abortive clause is not `!U(A ⊸ C)`"
    unless decide (A' = A) do throw "R0: an abortive clause's argument is not the operation's"
    -- `let (c, rest) = cs; …` (at `rest :: c :: Γ`, the payload variable at `pk + 2`).
    let body ← match As with
      | [] => pure (applyAt sp (varAt sp 1 cTy) (pk + 2) A C)
      | _ =>
        -- `case p { inl v → c v | inr q → ⟨rest's clause⟩ q }`
        let P' := payloadOf As
        let there ← dispatch sp C As 0 (varAt sp 1 restTy) restTy
        pure (caseAt sp r0B A P' C (varAt sp (pk + 2) (.sum A P'))
          (applyAt sp (varAt sp 2 cTy) 0 A C) there)
    pure (.tensorE { sp, binders := [r0B, r0B] } (.comp C) cTy restTy C noMasks cs body)

/-- The answer clause of a handler's pair `tc` (its first component; the rest is the clauses,
the answering functions, or the works and exits). -/
def pairOf (tc : TExpr) : Except String (TExpr × TExpr) :=
  match tc with
  | .tensorI _ _ _ _ _ tr tcl => pure (tr, tcl)
  | _ => throw "R0: a handler's pair is not a pair"

/-- The value type of a value node. -/
def valTy (t : TExpr) : Except String VTy :=
  match t.jdg with
  | .val A => pure A
  | .comp _ => throw "R0: a computation where a value is expected"

/-- **The forwarding answer clause** of a handler of another name whose outer row holds `n`:
`λr. case r { inl a → h a | inr p → return (inr p) }`, `h : !U(A ⊸ C)` the source's (translated),
`C = F_{⟦Σ⟧ₙ}(⟦R⟧ₙ ⊕ P_n)`. `n`'s payload passes the handler unread (`fwd_abort`). -/
def forwardAns (a : AbortName) (sp : Frontend.Span) (S₁ : Row) (A R : VTy) (h : TExpr) : TExpr :=
  let C := CTy.effOf S₁ (.sum R a.P)
  let arm₁ := applyAt sp (h.shift 2 0) 0 A C
  let arm₂ := liftTo sp [] S₁ (.sum R a.P) (retAt sp (.sum R a.P) (inrAt sp R a.P (varAt sp 0 a.P)))
  let body := caseAt sp r0B A a.P C (varAt sp 0 (.sum A a.P)) arm₁ arm₂
  let lam := TExpr.lam { sp, name := r0B } (.comp (.arr (.sum A a.P) C)) (.sum A a.P) C body
  .bangThunkV (infoAt sp) (.val (.bang (.thunk (.arr (.sum A a.P) C)))) (.arr (.sum A a.P) C) lam

/-- **A handler of `n`**: `⟦e⟧ to r. case r { inl a → h a | inr (ι_j v) → c_j v }`, at the
handler's outer row `S` (`n ∉ S`); `tr` and `tcl` its answer clause and clauses (translated). -/
def handleN (a : AbortName) (sp : Frontend.Span) (S : Row) (A R : VTy) (tr tcl te : TExpr) :
    Except String TExpr := do
  let S₁ := trRow a S
  let A' := trV a A
  let R' := trV a R
  let C := CTy.effOf S₁ R'
  let arm₁ := applyAt sp (tr.shift 2 0) 0 A' C
  let arm₂ ← dispatch sp C a.args 0 (tcl.shift 2 0) (← valTy tcl)
  -- `[handle]` checks its handled computation at `F_{n::Σ} A`; the rule writes `e` at that type's
  -- translation, `F_{⟦Σ⟧ₙ}(⟦A⟧ₙ ⊕ P_n)`, where the node held it.
  let te := te.setInfo { te.info with asc := true }
  pure (bindAt sp r0B S₁ (.sum A' a.P) R' te (caseAt sp r0B A' a.P C (varAt sp 0 (.sum A' a.P)) arm₁ arm₂))

/-- **An unwinding borrow at a row holding `n`** (`withborkU td`, the U-lend rule), as its
η-expansion `λr. λf. withborkU td r f` rewritten:
`λr. λf. withbork r (Λ'x. λm. box-lift (f ['x] m)) to (r, s). case s { inl b → return (inl (r, b)) | inr p → td r; return (inr p) }`,
`withbork` the borrow's non-unwinding form at the answer `⟦B⟧ₙ ⊕ P_n`, and
`box-lift s = case s { inl b → return (boxed['x] (inl (unbox b))) | inr p → return (boxed['x] (inr p)) }`.
`box-lift`'s `boxed['x] (inr p)` needs the payload to outlive `'x`, which the unwinding row gives
(`Row.Unwind`: an argument outlives every lifetime). The borrow's row must hold no other operation:
the non-unwinding form's callback is at the empty row. -/
def uLend (a : AbortName) (t : TExpr) : AbM TExpr := do
  let P := a.P
  let sp := t.info.sp
  let (S, td) : Row × Option TExpr := match t with
    | .withbor1U _ _ _ _ S _ td | .withbor2U _ _ _ _ S _ td | .withbor3U _ _ _ _ _ S _ td
    | .sliceBorrowMU _ _ _ _ S _ td | .sliceBorrowIU _ _ _ _ S _ td => (S, some td)
    | .withloadU _ _ _ _ _ S _ => (S, none)
    | _ => ([], none)
  unless (trRow a S).isEmpty do
    throw "R0: an unwinding borrow whose row holds an operation of another name"
  let .val (.thunk (.arr src (.arr (.thunk (.all x bnd (.arr L Ccb))) Cres))) := t.jdg
    | throw "R0: an unwinding borrow's type is not `U(src ⊸ cb ⊸ F_Σ R)`"
  let some (_, .box _ B) := Frontend.Check.effRow? Ccb
    | throw "R0: an unwinding borrow's callback does not answer `['x] B`"
  let some (_, R) := Frontend.Check.effRow? Cres
    | throw "R0: an unwinding borrow does not answer `F_Σ R`"
  -- Every unwinding borrow but `withload` answers its source with the callback's answer.
  let pair := match t with
    | .withloadU .. => false
    | _ => true
  if pair then
    unless decide (R = .tensor src B) do
      throw "R0: an unwinding borrow does not answer `src ⊗ B`"
  else unless decide (R = B) do throw "R0: `withload` does not answer the callback's `B`"
  let src' := trV a src
  let L' := trV a L
  let B' := trV a B
  let B'' : VTy := .sum B' P
  let bx : VTy := .box (.var x) B'
  -- The callback's type, translated: `U(∀'x ⊏ @bnd. L ⊸ F(['x] B ⊕ P))`.
  let Cf : CTy := .all x bnd (.arr L' (.ret (.sum bx P)))
  let cbU : VTy := .thunk Cf
  -- The non-unwinding callback's type: `∀'x ⊏ @bnd. L ⊸ ['x] (B ⊕ P)`.
  let Cin : CTy := .arr L' (.ret (.box (.var x) B''))
  let Ccb : CTy := .all x bnd (.ret (.thunk Cin))
  let cbT : VTy := .thunk Ccb
  let Rp : VTy := if pair then .tensor src' B'' else B''
  let Rres : VTy := if pair then .sum (.tensor src' B') P else B''
  let plainTy : VTy := .lolli src' (.lolli cbT Rp)
  let plain : TExpr ← match t with
    | .withbor1U i _ A _ _ x _ => pure (.withbor1 i (.val plainTy) (trV a A) B'' x)
    | .withbor2U i _ A _ _ x _ => pure (.withbor2 i (.val plainTy) (trV a A) B'' x)
    | .withbor3U i _ l A _ _ x _ => pure (.withbor3 i (.val plainTy) l (trV a A) B'' x)
    | .withloadU i _ l A _ _ x => pure (.withload i (.val plainTy) l (trV a A) B'' x)
    | .sliceBorrowMU i _ A _ _ x _ => pure (.sliceBorrowM i (.val plainTy) (trV a A) B'' x)
    | .sliceBorrowIU i _ A _ _ x _ => pure (.sliceBorrowI i (.val plainTy) (trV a A) B'' x)
    | _ => throw "R0: not an unwinding borrow"
  -- box-lift (at `m :: u :: f :: r :: Γ`): `ys <- (f ['x]) m; case ys { … }`.
  let Cys : CTy := .ret (.sum bx P)
  let call := TExpr.app (infoAt sp) (.comp Cys) 0 L' Cys noMasks
    (.allE (infoAt sp) (.comp (.arr L' Cys)) x bnd (.var x) (.arr L' Cys)
      (.force (infoAt sp) (.comp Cf) 2 Cf))
  let boxAt (v : TExpr) : TExpr :=
    retAt sp (.box (.var x) B'') (.boxI (infoAt sp) (.val (.box (.var x) B'')) (.var x) B'' v)
  let lift := caseAt sp r0B bx P (.ret (.box (.var x) B'')) (varAt sp 0 (.sum bx P))
    (boxAt (inlAt sp B' P (.boxE (infoAt sp) (.val B') (.var x) B' (varAt sp 0 bx))))
    (boxAt (inrAt sp B' P (varAt sp 0 P)))
  let inner := bindAt sp r0B [] (.sum bx P) (.box (.var x) B'') call lift
  -- The callback (at `f :: r :: Γ`): `thunkv Λ'x. return (thunkv λm. box-lift …)`.
  let cb := TExpr.thunkV (infoAt sp) (.val cbT) Ccb
    (.allI (infoAt sp) (.comp Ccb) x bnd .unit (.ret (.thunk Cin))
      (retAt sp (.thunk Cin) (.thunkV (infoAt sp) (.val (.thunk Cin)) Cin
        (.lam { sp, name := r0B } (.comp Cin) L' (.ret (.box (.var x) B'')) inner))))
  -- `withbork r cb` (at `f :: r :: Γ`).
  let lend := TExpr.lolliE (infoAt sp) (.val Rp) cbT Rp noMasks cb
    (.lolliE (infoAt sp) (.val (.lolli cbT Rp)) src' (.lolli cbT Rp) noMasks (varAt sp 1 src') plain)
  let Cres' : CTy := .ret Rres
  let body ← if pair then do
      -- `let (r, s) = withbork r cb; case s { inl b → return (inl (r, b)) | inr p → td r; return (inr p) }`
      let arm₁ := retAt sp Rres (inlAt sp (.tensor src' B') P
        (.tensorI (infoAt sp) (.val (.tensor src' B')) src' B' noMasks (varAt sp 2 src') (varAt sp 0 B')))
      let ret₂ := retAt sp Rres (inrAt sp (.tensor src' B') P (varAt sp 0 P))
      let arm₂ ← match td with
        | some (.dtor i j A) => pure (TExpr.unitE (infoAt sp) (.comp Cres') Cres' noMasks
            (.lolliE (infoAt sp) (.val .unit) src' .unit noMasks (varAt sp 2 src')
              (.dtor i (trJ a j) (trV a A))) ret₂)
        | some _ => throw "R0: an unwinding borrow whose finaliser is not its source's destructor"
        | none => pure ret₂
      pure (TExpr.tensorE { sp, binders := [r0B, r0B] } (.comp Cres') src' B'' Cres' noMasks lend
        (caseAt sp r0B B' P Cres' (varAt sp 0 B'') arm₁ arm₂))
    else
      -- `case withbork r cb { inl b → return (inl b) | inr p → return (inr p) }`
      pure (caseAt sp r0B B' P Cres' lend
        (retAt sp Rres (inlAt sp B' P (varAt sp 0 B'))) (retAt sp Rres (inrAt sp B' P (varAt sp 0 P))))
  let Cη : CTy := .arr src' (.arr cbU Cres')
  pure (.thunkV (infoAt sp) (.val (.thunk Cη)) Cη
    (.lam { sp, name := r0B } (.comp Cη) src' (.arr cbU Cres')
      (.lam { sp, name := r0B } (.comp (.arr cbU Cres')) cbU Cres' body)))

/-- **R0 over a typed term**, for the name `a`: the rules above at a row holding `n`, homomorphic
on every other node (its types translated, its children rewritten). A node R0 has no rule for at a
row holding `n` is a hard error. -/
def ab (a : AbortName) (t : TExpr) : AbM TExpr := do
  let tV := trV a
  let tC := trC a
  let tJ := trJ a
  let tR := trRow a
  let P := a.P
  let has := rowHas a.n
  match t with
  -- Values and the pure computations: homomorphic.
  | .var i j k A => pure (.var i (tJ j) k (tV A))
  | .unitI i j => pure (.unitI i (tJ j))
  | .tensorI i j A B u t₁ t₂ => return .tensorI i (tJ j) (tV A) (tV B) u (← ab a t₁) (← ab a t₂)
  | .sumI₁ i j A B c => return .sumI₁ i (tJ j) (tV A) (tV B) (← ab a c)
  | .sumI₂ i j A B c => return .sumI₂ i (tJ j) (tV A) (tV B) (← ab a c)
  | .thunkF i j A c => return .thunkF i (tJ j) (tV A) (← ab a c)
  | .thunkV i j C c => return .thunkV i (tJ j) (tC C) (← ab a c)
  | .ret i j A c => return .ret i (tJ j) (tV A) (← ab a c)
  | .bind i j A C u tM tN => return .bind i (tJ j) (tV A) (tC C) u (← ab a tM) (← ab a tN)
  | .force i j k C => pure (.force i (tJ j) k (tC C))
  | .lam i j A C c => return .lam i (tJ j) (tV A) (tC C) (← ab a c)
  | .lamDead i j S B c =>
    let B' := if has S then .sum (tV B) P else tV B
    return .lamDead i (tJ j) (tR S) B' (← ab a c)
  | .app i j k A C u tM => return .app i (tJ j) k (tV A) (tC C) u (← ab a tM)
  | .withI i j C D tM tN => return .withI i (tJ j) (tC C) (tC D) (← ab a tM) (← ab a tN)
  | .proj₁ i j C D c => return .proj₁ i (tJ j) (tC C) (tC D) (← ab a c)
  | .proj₂ i j C D c => return .proj₂ i (tJ j) (tC C) (tC D) (← ab a c)
  | .topI i j => pure (.topI i (tJ j))
  | .unitE i j C u tV' tM => return .unitE i (tJ j) (tC C) u (← ab a tV') (← ab a tM)
  | .tensorE i j A B C u tV' tM => return .tensorE i (tJ j) (tV A) (tV B) (tC C) u (← ab a tV') (← ab a tM)
  | .sumE i j A B C u tV' t₁ t₂ =>
    return .sumE i (tJ j) (tV A) (tV B) (tC C) u (← ab a tV') (← ab a t₁) (← ab a t₂)
  | .zeroE i j C u tV' => return .zeroE i (tJ j) (tC C) u (← ab a tV')
  | .allI i j x b S C c => return .allI i (tJ j) x b (tV S) (tC C) (← ab a c)
  | .allE i j x b l C c => return .allE i (tJ j) x b l (tC C) (← ab a c)
  | .bangThunkF i j A c => return .bangThunkF i (tJ j) (tV A) (← ab a c)
  | .bangThunkV i j C c => return .bangThunkV i (tJ j) (tC C) (← ab a c)
  | .bangE i j A c => return .bangE i (tJ j) (tV A) (← ab a c)
  | .copyBang i j A => pure (.copyBang i (tJ j) (tV A))
  | .forgetBang i j A => pure (.forgetBang i (tJ j) (tV A))
  | .boxI i j l A c => return .boxI i (tJ j) l (tV A) (← ab a c)
  | .boxE i j l A c => return .boxE i (tJ j) l (tV A) (← ab a c)
  | .immSub i j l b A c => return .immSub i (tJ j) l b (tV A) (← ab a c)
  | .mutSub i j l b A c => return .mutSub i (tJ j) l b (tV A) (← ab a c)
  | .alloc i j A => pure (.alloc i (tJ j) (tV A))
  | .free i j A => pure (.free i (tJ j) (tV A))
  | .swap i j A B => pure (.swap i (tJ j) (tV A) (tV B))
  | .copy i j l A => pure (.copy i (tJ j) l (tV A))
  | .forgetImm i j l A => pure (.forgetImm i (tJ j) l (tV A))
  | .forgetMut i j l A => pure (.forgetMut i (tJ j) l (tV A))
  | .forgetUnk i j => pure (.forgetUnk i (tJ j))
  | .lit i j c => pure (.lit i (tJ j) c)
  | .hostOp i j op => pure (.hostOp i (tJ j) op)
  | .arrNew i j A => pure (.arrNew i (tJ j) (tV A))
  | .arrFree i j A => pure (.arrFree i (tJ j) (tV A))
  | .arrSize i j A => pure (.arrSize i (tJ j) (tV A))
  | .arrReplace i j A => pure (.arrReplace i (tJ j) (tV A))
  | .arrLen i j l A => pure (.arrLen i (tJ j) l (tV A))
  | .arrGet i j l A => pure (.arrGet i (tJ j) l (tV A))
  | .arrCopy i j l A => pure (.arrCopy i (tJ j) l (tV A))
  | .arrForget i j l A => pure (.arrForget i (tJ j) l (tV A))
  | .countFold i j S => pure (.countFold i (tJ j) (tV S))
  | .countTry i j S E => pure (.countTry i (tJ j) (tV S) (tV E))
  | .boundedFix i j A C => pure (.boundedFix i (tJ j) (tV A) (tC C))
  | .iterate i j S St B R =>
    if has S then throw "R7: no producer (`iterate` at a row holding an abortive name)"
    else pure (.iterate i (tJ j) (tR S) (tV St) (tV B) (tV R))
  | .divFuel i j S A =>
    if has S then throw "R7: no producer (`divFuel` at a row holding an abortive name)"
    else pure (.divFuel i (tJ j) (tR S) (tV A))
  | .reify i j S B R c =>
    if has S then throw "R7: no producer (`reify` at a row holding an abortive name)"
    else return .reify i (tJ j) (tR S) (tV B) (tV R) (← ab a c)
  | .sliceBorrowM i j A B x => pure (.sliceBorrowM i (tJ j) (tV A) (tV B) x)
  | .sliceBorrowI i j A B x => pure (.sliceBorrowI i (tJ j) (tV A) (tV B) x)
  | .sliceGetM i j l A => pure (.sliceGetM i (tJ j) l (tV A))
  | .sliceLenM i j l A => pure (.sliceLenM i (tJ j) l (tV A))
  | .sliceSplitI i j l A => pure (.sliceSplitI i (tJ j) l (tV A))
  | .sliceSplitM i j l A => pure (.sliceSplitM i (tJ j) l (tV A))
  | .sliceEmptyI i j l A => pure (.sliceEmptyI i (tJ j) l (tV A))
  | .sliceEmptyM i j l A => pure (.sliceEmptyM i (tJ j) l (tV A))
  | .sliceReplaceM i j l A => pure (.sliceReplaceM i (tJ j) l (tV A))
  | .sliceSwapM i j l A => pure (.sliceSwapM i (tJ j) l (tV A))
  | .withbor1 i j A B x => pure (.withbor1 i (tJ j) (tV A) (tV B) x)
  | .withbor2 i j A B x => pure (.withbor2 i (tJ j) (tV A) (tV B) x)
  | .withbor3 i j l A B x => pure (.withbor3 i (tJ j) l (tV A) (tV B) x)
  | .withload i j l A B x => pure (.withload i (tJ j) l (tV A) (tV B) x)
  | .withswap i j l A B => pure (.withswap i (tJ j) l (tV A) (tV B))
  -- The unwinding borrows: R0's U-lend rule at a row holding `n`.
  | .withbor1U i j A B S x td =>
    if has S then uLend a t else return .withbor1U i (tJ j) (tV A) (tV B) (tR S) x (← ab a td)
  | .withbor2U i j A B S x td =>
    if has S then uLend a t else return .withbor2U i (tJ j) (tV A) (tV B) (tR S) x (← ab a td)
  | .withbor3U i j l A B S x td =>
    if has S then uLend a t else return .withbor3U i (tJ j) l (tV A) (tV B) (tR S) x (← ab a td)
  | .withloadU i j l A B S x =>
    if has S then uLend a t else pure (.withloadU i (tJ j) l (tV A) (tV B) (tR S) x)
  | .sliceBorrowMU i j A B S x td =>
    if has S then uLend a t else return .sliceBorrowMU i (tJ j) (tV A) (tV B) (tR S) x (← ab a td)
  | .sliceBorrowIU i j A B S x td =>
    if has S then uLend a t else return .sliceBorrowIU i (tJ j) (tV A) (tV B) (tR S) x (← ab a td)
  | .lolliE i j A B u ta tf => return .lolliE i (tJ j) (tV A) (tV B) u (← ab a ta) (← ab a tf)
  | .allEV i j x b l A c => return .allEV i (tJ j) x b l (tV A) (← ab a c)
  | .ofRet i j A c => return .ofRet i (tJ j) (tV A) (← ab a c)
  | .roll i j A c => return .roll i (tJ j) (tV A) (← ab a c)
  | .unroll i j A c => return .unroll i (tJ j) (tV A) (← ab a c)
  | .foldImm i j F y c R => pure (.foldImm i (tJ j) (trFShape a F) y c (tV R))
  | .foldOwn i j F R => pure (.foldOwn i (tJ j) (trFShape a F) (tV R))
  | .foldReuse i j F R => pure (.foldReuse i (tJ j) (trFShape a F) (tV R))
  | .nuIn i j C c => return .nuIn i (tJ j) (tC C) (← ab a c)
  | .nuOut i j C c => return .nuOut i (tJ j) (tC C) (← ab a c)
  | .unfoldN i j C S => pure (.unfoldN i (tJ j) (tC C) (tV S))
  -- `[sub]`: `return V` reaching a row that holds `n`.
  | .effSub i j S S' A c => do
    let c' ← ab a c
    if has S then pure (.effSub i (tJ j) (tR S) (tR S') (.sum (tV A) P) c')
    else if has S' then
      let sp := i.sp
      let S₁ := tR S'
      let A' := tV A
      -- `[sub]` held `M`'s answer `A`: the binding is written at it (`M` checked, as `[sub]`'s was).
      pure (bindAt sp r0B S₁ A' (.sum A' P) (liftTo sp (tR S) S₁ A' c')
        (liftTo sp [] S₁ (.sum A' P) (retAt sp (.sum A' P) (inlAt sp A' P (varAt sp 0 A'))))
        (ann := true))
    else pure (.effSub i (tJ j) (tR S) (tR S') (tV A) c')
  -- `perform` of another name at a row holding `n`.
  | .effPerform i j S o c => do
    let c' ← ab a c
    if has S then
      let sp := i.sp
      let S₁ := tR S
      let o' := trOp a o
      let B := o'.B
      pure (bindAt sp r0B S₁ B (.sum B P) (.effPerform i (.comp (CTy.effOf S₁ B)) S₁ o' c')
        (liftTo sp [] S₁ (.sum B P) (retAt sp (.sum B P) (inlAt sp B P (varAt sp 0 B)))))
    else pure (.effPerform i (tJ j) (tR S) (trOp a o) c')
  -- `raise`: of `n`, its injection; of another name at a row holding `n`, at the answer `⟦B⟧ ⊕ P`.
  | .effRaise i j S o B c => do
    let c' ← ab a c
    if o.n == a.n then
      let sp := i.sp
      let S₁ := tR S
      let B' := tV B
      let v ← injPay sp a.args o.i.toNat c'
      pure (liftTo sp [] S₁ (.sum B' P) (retAt sp (.sum B' P) (inrAt sp B' P v)))
    else if has S then pure (.effRaise i (tJ j) (tR S) (trOp a o) (.sum (tV B) P) c')
    else pure (.effRaise i (tJ j) (tR S) (trOp a o) (tV B) c')
  -- `[let]` at a row holding `n`: the `inr` arm returns the payload; its drops are `[let]`'s.
  | .effLet i j A B S u tM tN => do
    let tM' ← ab a tM
    let tN' ← ab a tN
    if has S then
      let sp := i.sp
      let S₁ := tR S
      let A' := tV A
      let B' := tV B
      let C := CTy.effOf S₁ (.sum B' P)
      let arm₂ := liftTo sp [] S₁ (.sum B' P) (retAt sp (.sum B' P) (inrAt sp B' P (varAt sp 0 P)))
      let body := caseAt sp (i.binders.head?.getD "") A' P C (varAt sp 0 (.sum A' P))
        (tN'.shift 1 1) arm₂
      pure (bindAt sp r0B S₁ (.sum A' P) (.sum B' P) tM' body (ann := i.ann))
    else pure (.effLet i (tJ j) (tV A) (tV B) (tR S) u tM' tN')
  -- `[then]` at a row holding `n`: the `inr` arm runs the finaliser once, then returns the payload.
  | .effThen i j A B S SM SD u tM tN tD => do
    let tM' ← ab a tM
    let tN' ← ab a tN
    let tD' ← ab a tD
    if has S then
      unless SD.isEmpty do
        throw "R0: a `[then]` whose finaliser is at a row (`rEffThen` writes the empty row)"
      let sp := i.sp
      let S₁ := tR S
      let A' := tV A
      let B' := tV B
      let C := CTy.effOf S₁ (.sum B' P)
      -- `⟦D⟧ to d. return (inr p)`, `D` (at `() :: Γ`) moved to `p :: r :: Γ`.
      let retP (k : Nat) := liftTo sp [] S₁ (.sum B' P) (retAt sp (.sum B' P) (inrAt sp B' P (varAt sp k P)))
      let runD (body : TExpr) :=
        TExpr.bind { sp := tD.info.sp, binders := [r0B] } (.comp C) .unit C noMasks (tD'.shift 1 1) body
      let arm₂ := match (← get).seed with
        | .none => runD (retP 1)
        | .dropFin => retP 0
        | .dupFin => runD (TExpr.bind { sp := tD.info.sp, binders := [r0B] } (.comp C) .unit C noMasks
            ((tD'.shift 1 1).shift 1 0) (retP 2))
      let body := caseAt sp (i.binders.head?.getD "") A' P C (varAt sp 0 (.sum A' P))
        (tN'.shift 1 1) arm₂
      if S₁.isEmpty then pure (bindAt sp r0B [] (.sum A' P) (.sum B' P) tM' body (ann := i.ann))
      else
        -- The `[then]` stays for the abortive names its row keeps, with its finaliser.
        pure (.effThen { i with binders := [r0B], lin := false } (.comp C)
          (.sum A' P) (.sum B' P) S₁ S₁ [] u tM' body tD')
    else pure (.effThen i (tJ j) (tV A) (tV B) (tR S) (tR SM) (tR SD) u tM' tN' tD')
  -- Handlers.
  | .effHandleV i j S E fs nm A R u ks site ins tc@(.tensorI _ _ _ _ _ tr tcl) te => do
    let tr' ← ab a tr
    let tcl' ← ab a tcl
    let te' ← ab a te
    if nm == a.n then
      handleN a i.sp S A R tr' tcl' te'
    else if has S then
      modify fun st => { st with bangs := st.bangs + 1 }
      let ans := forwardAns a i.sp (tR S) (tV A) (tV R) tr'
      let tc' := TExpr.tensorI tc.info (.val (.tensor (← valTy ans) (← valTy tcl'))) (← valTy ans)
        (← valTy tcl') noMasks ans tcl'
      pure (.effHandleV i (tJ j) (tR S) (trE a E) (fun k => tC (fs k)) nm (.sum (tV A) P)
        (.sum (tV R) P) u ks site ins tc' te')
    else
      let tc' := TExpr.tensorI tc.info (tJ tc.jdg) (← valTy tr') (← valTy tcl') noMasks tr' tcl'
      pure (.effHandleV i (tJ j) (tR S) (trE a E) (fun k => tC (fs k)) nm (tV A) (tV R) u ks
        site ins tc' te')
  | .effHandleVB i j S E fs nm A R d u ks site ins tc@(.tensorI _ _ _ _ _ tr tcl) te => do
    let tr' ← ab a tr
    let tcl' ← ab a tcl
    let te' ← ab a te
    if nm == a.n then
      handleN a i.sp S A R tr' tcl' te'
    else if has S then
      modify fun st => { st with bangs := st.bangs + 1 }
      let ans := forwardAns a i.sp (tR S) (tV A) (tV R) tr'
      let tc' := TExpr.tensorI tc.info (.val (.tensor (← valTy ans) (← valTy tcl'))) (← valTy ans)
        (← valTy tcl') noMasks ans tcl'
      pure (.effHandleVB i (tJ j) (tR S) (trE a E) (fun k => tC (fs k)) nm (.sum (tV A) P)
        (.sum (tV R) P) d u ks site ins tc' te')
    else
      let tc' := TExpr.tensorI tc.info (tJ tc.jdg) (← valTy tr') (← valTy tcl') noMasks tr' tcl'
      pure (.effHandleVB i (tJ j) (tR S) (trE a E) (fun k => tC (fs k)) nm (tV A) (tV R) d u ks
        site ins tc' te')
  | .effHandleT i j S SN E fs nm A R u site ins tc@(.tensorI _ _ _ _ _ tr tcl) te => do
    let tr' ← ab a tr
    let tcl' ← ab a tcl
    let te' ← ab a te
    if nm == a.n then
      handleN a i.sp S A R tr' tcl' te'
    else if has S then
      modify fun st => { st with bangs := st.bangs + 1 }
      let ans := forwardAns a i.sp (tR S) (tV A) (tV R) tr'
      let tc' := TExpr.tensorI tc.info (.val (.tensor (← valTy ans) (← valTy tcl'))) (← valTy ans)
        (← valTy tcl') noMasks ans tcl'
      pure (.effHandleT i (tJ j) (tR S) (tR SN) (trE a E) (fun k => tC (fs k)) nm (.sum (tV A) P)
        (.sum (tV R) P) u site ins tc' te')
    else
      let tc' := TExpr.tensorI tc.info (tJ tc.jdg) (← valTy tr') (← valTy tcl') noMasks tr' tcl'
      pure (.effHandleT i (tJ j) (tR S) (tR SN) (trE a E) (fun k => tC (fs k)) nm (tV A) (tV R) u
        site ins tc' te')
  | .effHandleL i j S SW E fs Xs nm A R u site ins tc@(.tensorI _ _ _ _ _ tr tcl) te => do
    if nm == a.n then throw "R0: no rule for `handle_last` of an abortive name"
    if has S then throw "R0: no rule for `handle_last` at a row holding an abortive name"
    let tc' := TExpr.tensorI tc.info (tJ tc.jdg) (tV (← valTy tr)) (tV (← valTy tcl)) noMasks
      (← ab a tr) (← ab a tcl)
    return .effHandleL i (tJ j) (tR S) (tR SW) (trE a E) (fun k => tC (fs k)) (fun k => tV (Xs k))
      nm (tV A) (tV R) u site ins tc' (← ab a te)
  | .effHandleV .. | .effHandleVB .. | .effHandleT .. | .effHandleL .. =>
    throw "R0: a handler's pair is not a pair"
  | .letPoly i j C j' tV' tN => return .letPoly i (tJ j) (tC C) (tJ j') (← ab a tV') (← ab a tN)
  | .lendR i j x b T B S td tM =>
    if has S then throw "R0: an abortive name crossing a `lendR` reached the rule (left: lendR)"
    else return .lendR i (tJ j) x b (tV T) (tV B) (tR S) (← ab a td) (← ab a tM)
  | .lendLoopR i j x A S B R tN tK ts0 =>
    return .lendLoopR i (tJ j) x (tV A) (tV S) (tV B) (tV R) (← ab a tN) (← ab a tK) (← ab a ts0)
  | .nilDead i j j' c => return .nilDead i (tJ j) (tJ j') (← ab a c)
  | .dtor i j A => pure (.dtor i (tJ j) (tV A))
  | .allocS i j σ => pure (.allocS i (tJ j) (trShape a σ))
  | .freeS i j σ => pure (.freeS i (tJ j) (trShape a σ))
  | .withborSM i j σ c T => pure (.withborSM i (tJ j) (trShape a σ) c (tV T))
  | .withborSI i j σ c T => pure (.withborSI i (tJ j) (trShape a σ) c (tV T))
  | .withborF2M i j c x y A B T => pure (.withborF2M i (tJ j) c x y (tV A) (tV B) (tV T))
  | .withborF2I i j c x y A B T => pure (.withborF2I i (tJ j) c x y (tV A) (tV B) (tV T))
  | .litFn i j bs c => return .litFn i (tJ j) bs (← ab a c)
  | .divLit i j op k c => return .divLit i (tJ j) op k (← ab a c)
  | .walk i j m r c => return .walk i (tJ j) m r (← ab a c)
  | .walkGet i j m c => return .walkGet i (tJ j) m (← ab a c)
  | .selfCall i j k n c => return .selfCall i (tJ j) k n (← ab a c)
  | .lendCell i j m c => return .lendCell i (tJ j) m (← ab a c)
  | .nuEta i j f s c => return .nuEta i (tJ j) f s (← ab a c)
  | .use i j nm decl targs ab' c => return .use i (tJ j) nm decl (targs.map tV) ab' (← ab a c)

end Rewrite
