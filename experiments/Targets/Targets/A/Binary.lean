import Targets.A.Expressiveness

/-!
# System A — A₂: the binary laws, stated, out of the first pass (RESTRUCTURE §1.7)

U22: "optional and don't get pursued unless they become necessary for safety".  Nothing is driven
from these.

They are stated over A's contextual approximation.  A has no typing of contexts (`der` types terms,
and `Kont` has none), so a closing context is a term `C` whose variable `0` is the thunk, which the
let law binds: at every value type `T` at which both thunks are typed, every `C` with
`der [T] C (F ε A)` at a data `A`, run under the runner, observes of `lets [lam t₁] C` no more than
of `lets [lam t₂] C`.  This needs no new judgement.

* `HandlerLaws` (T2, Plotkin–Pretnar §1.2, Def. 4.5): return, operation (resuming and abortive),
  forwarding, the tail-resumptive law, algebraicity, capture β and cancel, each as `CtxEquiv`.  A
  term placed under a binder that it does not mention is written as is: a term the instance types
  in a context that does not bind the new variable does not use it, read in good faith.
* `EffDepLaws` (Kammar thesis (11.1), Thm 12.5): Discard at a row with no operation.  With no
  equations in signatures (OQ-22), "op(x, …, x) = x" holds of no operation, so Discard is stated at
  the pure row only.
* `Abstraction` (T3, Zhang–Myers Thm 1, Thm 3): `TunnelBin` (E6's shape, binary: `fwrap g`
  against `g` at every row without `li`) and `Encap`.

**Not stated at A, and why.**  Capture η and Copy/Swap need a renaming of labels or of variables,
and A has no substitution (§1.4); fusion needs a handler of two labels, and A's `handle` has one
(OQ-49); hiding and representation independence need answering implementations, which are our
instance's (`Targets/Instance/Binary.lean` states them over Core).
-/

namespace Targets.A

namespace EffectSystem

variable (S : EffectSystem)

/-- What a complete run shows: its answer and its observable trace. -/
def Observes (R : S.Runner) (e : S.Term) (v : S.Val) (tr : List S.Event) : Prop :=
  ∃ q, S.CompleteFrom R (S.rinit R e) q ∧ S.term (S.lastC (S.rinit R e) q).1 = S.ret v ∧
    S.obs q = tr

/-- `t₁ ≼ t₂` under the runner `R`. -/
def CtxApprox (R : S.Runner) (t₁ t₂ : S.Term) : Prop :=
  ∀ T, S.derV [] (S.lam t₁) T → S.derV [] (S.lam t₂) T →
    ∀ C ε A, S.DataTy A → S.Answers R ε → S.der [T] C (S.F ε A) →
      ∀ v tr, S.Observes R (S.lets [S.lam t₁] C) v tr → S.Observes R (S.lets [S.lam t₂] C) v tr

/-- Contextual equivalence. -/
def CtxEquiv (R : S.Runner) (t₁ t₂ : S.Term) : Prop := S.CtxApprox R t₁ t₂ ∧ S.CtxApprox R t₂ t₁

/-- `λ(a, k). c a to b. k.resume b`: a tail-resumptive clause. -/
def tailCl (c : S.Val) : S.Val :=
  S.lam (S.split (S.var 0) (S.bind (S.app (S.force c) (S.var 1)) (S.resume (S.var 1) (S.var 0))))

/-- **T2**: the handler laws as contextual equivalences. -/
def HandlerLaws : Prop :=
  ∀ R : S.Runner, R.Respects →
    -- return
    (∀ l r cs v, S.CtxEquiv R (S.handle l (S.hnd r cs) (S.ret v)) (S.app (S.force r) v)) ∧
    -- a resuming operation
    (∀ l r cs K i v (o : OpSig S.Ty) cl, S.catches K l = false → (S.sig l)[i]? = some o →
       o.cls ≠ .abortive → cs[i]? = some cl →
       S.CtxEquiv R (S.handle l (S.hnd r cs) (S.plug K (S.perform l i v)))
         (S.app (S.force cl) (S.pair v (S.capture l (S.hnd r cs) K)))) ∧
    -- an abortive operation
    (∀ l r cs K i v (o : OpSig S.Ty) cl, S.catches K l = false → S.unwindClear K →
       (S.sig l)[i]? = some o → o.cls = .abortive → cs[i]? = some cl →
       S.CtxEquiv R (S.handle l (S.hnd r cs) (S.plug K (S.raise l i v))) (S.app (S.force cl) v)) ∧
    -- forwarding: an operation of another label passes the handler
    (∀ l H K m i v, m ≠ l → S.catches K m = false →
       S.CtxEquiv R (S.handle l H (S.plug K (S.perform m i v)))
         (S.bind (S.perform m i v) (S.handle l H (S.plug K (S.ret (S.var 0)))))) ∧
    -- the tail-resumptive law
    (∀ l r cs K i v c, S.catches K l = false → cs[i]? = some (S.tailCl c) →
       S.CtxEquiv R (S.handle l (S.hnd r cs) (S.plug K (S.perform l i v)))
         (S.handle l (S.hnd r cs) (S.plug K (S.app (S.force c) v)))) ∧
    -- algebraicity, at resuming operations
    (∀ l i v (o : OpSig S.Ty) M N, (S.sig l)[i]? = some o → o.cls ≠ .abortive →
       S.CtxEquiv R (S.bind (S.bind (S.perform l i v) M) N) (S.bind (S.perform l i v) (S.bind M N))) ∧
    -- capture β, and cancel
    (∀ l H K w, S.CtxEquiv R (S.resume (S.capture l H K) w) (S.handle l H (S.plug K (S.ret w)))) ∧
    (∀ l H K, S.CtxEquiv R (S.cancel (S.capture l H K)) (S.cancelOf l H K))

/-- **Effect-dependent equations**: Discard at a row with no operation. -/
def EffDepLaws : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ M N ε A C, (∀ l i, ¬ S.has ε l i) →
    S.der [] M (S.F ε A) → S.der [] N C → S.CtxEquiv R (S.bind M N) N

/-- **Tunnelling, binary** (Zhang–Myers Example 1 at E6's shape): `fwrap g` is `g` at every row
without `li`. -/
def TunnelBin (R : S.Runner) : Prop :=
  ∀ li M ε, S.Lacks ε li → S.der [] M (S.F ε S.bool) →
    S.CtxEquiv R (S.call (S.fwrap li) (S.lam M)) (S.app (S.force (S.lam M)) S.unitV)

/-- **Encapsulation**: two closed computations at a data answer on the pure row (every effect
handled inside) that every respecting runner observes alike are contextually equivalent. -/
def Encap (R : S.Runner) : Prop :=
  ∀ e₁ e₂ A, S.DataTy A → S.der [] e₁ (S.F S.EA.unit A) → S.der [] e₂ (S.F S.EA.unit A) →
    (∀ R' : S.Runner, R'.Respects → ∀ v tr, S.Observes R' e₁ v tr ↔ S.Observes R' e₂ v tr) →
    S.CtxEquiv R e₁ e₂

/-- **T3.** -/
def Abstraction : Prop := ∀ R : S.Runner, R.Respects → S.TunnelBin R ∧ S.Encap R

end EffectSystem

end Targets.A
