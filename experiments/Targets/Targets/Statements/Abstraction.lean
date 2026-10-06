import Targets.Statements.Handlers

/-!
# Targets — T3, Abstraction (binary) (DESIGN §3 T3, notebook P12)

**World:** [prog], binary; the proof device is a binary world [W₂].  **Out of the first pass**
(OQ-4: binary is optional).  Stated at full strength, over row-polymorphic `f`.

* **Tunnelling** (`Tunnel`, Zhang–Myers Example 1): effect-polymorphic code cannot handle the
  effects of the code it is handed.  In this kernel handlers are found by static site names, so
  the role of tunnelling is played by site freshness (`HndFree`, decision 57 R3) and the row
  typing of `[handle]`.
* **Representation independence** (`RepInd`): T2's `Hiding`, at answering handlers.
* **Encapsulation** (`Encap`): effects handled internally are invisible to every context (the
  survey's B1 corollary).

**The proof device, named-only.**  T3 is a corollary of a binary fundamental lemma, as T1 is of
the unary one.  Its statement needs a binary world `M₂ : SemWorld₂` (a relation on pairs of terms
over pairs of resource worlds) and its judgment `SemW₂`, which this design does not define:

* `FL₂ M₂ J`: every judgment of `J` relates its term to itself in `SemW₂ M₂` (Zhang–Myers Thm 1:
  "∆ | P | Γ | Ξ ⊢ t : [T]e ⇒ ∆ | P | Γ | Ξ ⊢ t ≼log t : [T]e");
* `Adequate₂ M₂ J`: two closed thunks related in `SemW₂ M₂` at `U C` are `CtxApprox J P C`
  (Thm 3: "t1 ≼log t2 … ⇒ t1 ≼ctx t2");
* `AbstractionOfFL₂`: `FL₂ M₂ J → Adequate₂ M₂ J → Abstraction J`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (performE hndE hndVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `f`'s type at the row `S`: `U(U(A ⊸ F_S B) ⊸ F_S R)`. -/
def hofTy (A B R : VTy) (S : Row) : VTy :=
  .thunk (.arr (.thunk (.arr A (CTy.effOf S B))) (CTy.effOf S R))

/-- No `hnd (n, …)` occurs in the term. -/
def _root_.BoCa.Expr.HndFree (n : UInt32) : Expr → Prop
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) r) => m ≠ n ∧ r.HndFree n
  | .pair a b | .seq a b | .letpair a b | .app a b => a.HndFree n ∧ b.HndFree n
  | .inj₁ a | .inj₂ a | .lam a => a.HndFree n
  | .case a b c => a.HndFree n ∧ b.HndFree n ∧ c.HndFree n
  | _ => True

/-- **Tunnelling** (Zhang–Myers, Example 1).  `f` is typed once, polymorphic in its callback's row
`ρ`; the name `n` is fresh for `f`.  Handing `f` the pure `λa. c a` at `ρ := []` is equivalent to
handing it `λa. perform (n, 0) a` at `ρ := {n}` and handling `n` outside by a clause that answers
with `c`: even an `f` that handles effects of its own cannot intercept `n`. -/
def Tunnel (J : TypingJ) (P : Platform) : Prop :=
  ∀ (f c : Val) (ρ : RVar) (k : RowCon) (A B R : VTy) (n : UInt32),
    let op : OpSig := ⟨n, 0, .lin, A, B⟩
    n ≠ 0 → k.cls.Admits [] → k.cls.Admits [op] → k.adm op →
    J [(ρ, k)] LifeCtx.empty (fun _ => []) (.val f) (fun η => .val (hofTy A B R (η ρ))) →
    J.at LifeCtx.empty [] (.val c) (.val (.bang (.thunk (.arr A (.ret B))))) →
    (f.1).HndFree n →
    CtxEquiv (ℍ := ℍ) J P (.ret R)
      (thunkF (.app (.val f) (.val ⟨.lam (.app (.val c) (.var 0)), .lam⟩)))
      (thunkF (hndE (hndVal n ⟨.lam (.var 0), .lam⟩ (Val.pair (tailClause c) .unit))
        (.app (.val f) (.val ⟨.lam (performE (opArgE n 0 (.var 0))), .lam⟩))))

/-- **Representation independence**: T2's `Hiding`, at answering handlers, whose operations are the
only access to their states. -/
abbrev RepInd (J : TypingJ) (P : Platform) : Prop := Hiding (ℍ := ℍ) J P

/-- **Encapsulation**: two closed computations at a data answer, every effect of each handled
inside it, that every platform observes alike, are contextually equivalent. -/
def Encap (J : TypingJ) (P : Platform) : Prop :=
  ∀ e₁ e₂ A, A.Data → J.closed e₁ (.ret A) → J.closed e₂ (.ret A) →
    (∀ P' : Platform, P'.Respects → Obs (ℍ := ℍ) P' A e₁ = Obs (ℍ := ℍ) P' A e₂) →
    CtxEquiv (ℍ := ℍ) J P (.ret A) (thunkF e₁) (thunkF e₂)

/-- **T3.** -/
def Abstraction (J : TypingJ) : Prop :=
  ∀ P : Platform, P.Respects → Tunnel (ℍ := ℍ) J P ∧ RepInd (ℍ := ℍ) J P ∧ Encap (ℍ := ℍ) J P

end Targets

end
