import Targets.A.Soundness

/-!
# System A — the programs of the (E) properties and of S6's witnesses (RESTRUCTURE §1.5, §1.6)

Each program is written with A's formers, in de Bruijn indices with the innermost binder at `0`:

* `M to x. N` is `bind M N`; `let (x, y) = V in M` is `split V M`, with `y = 0` and `x = 1`;
* a clause `op (v, k) ⇒ N` is `lam (split (var 0) N)`, with `k = 0` and `v = 1` inside `N`;
* `f a` is `call f a`, and `f a b` is `call2 f a b`;
* `let f = V in N` is `bind (ret V) N`, and `lets [v₀, …, vₙ] N` binds `vₙ` outermost and `v₀`
  innermost, so that `var k` in `N` is `vₖ`.

The surface notation of each program is in its docstring.  The signatures: `sigExn` (`1 ↠ 0`,
abortive: an error, decision E1 "error is a control flow effect full stop"), `sigWait` (`1 ↠ 1`,
affine: a suspension), `sigYield` (`bool ↠ 1`, affine), `sigLog` (`bool ↠ 1`, linear),
`sigTick` (`1 ↠ 1`, linear: a platform operation), `sigKube` (`1 ↠ bool`, linear: a platform API
call that may fail).
-/

namespace Targets.A

namespace EffectSystem

variable (S : EffectSystem)

/-! ### Signatures, runners, events -/

def sigExn : List (OpSig S.Ty) := [⟨S.UnitT, S.ZeroT, .abortive⟩]
def sigWait : List (OpSig S.Ty) := [⟨S.UnitT, S.UnitT, .affine⟩]
def sigYield : List (OpSig S.Ty) := [⟨S.bool, S.UnitT, .affine⟩]
def sigLog : List (OpSig S.Ty) := [⟨S.bool, S.UnitT, .linear⟩]
def sigTick : List (OpSig S.Ty) := [⟨S.UnitT, S.UnitT, .linear⟩]
def sigKube : List (OpSig S.Ty) := [⟨S.UnitT, S.bool, .linear⟩]
/-- A linear, resuming operation (S6's witnesses). -/
def sigLin : List (OpSig S.Ty) := [⟨S.UnitT, S.UnitT, .linear⟩]

open Classical in
/-- Answers `lt.0` with `()`. -/
noncomputable def Rtick (lt : S.EA.Lab) : S.Runner :=
  ⟨fun l i => l = lt ∧ i = 0, Unit, (),
   fun _ l i _ => if l = lt ∧ i = 0 then some (S.unitV, ()) else none⟩

open Classical in
/-- Answers `lt.0` and `llog.0` with `()`. -/
noncomputable def Rtl (lt llog : S.EA.Lab) : S.Runner :=
  ⟨fun l i => (l = lt ∨ l = llog) ∧ i = 0, Unit, (),
   fun _ l i _ => if (l = lt ∨ l = llog) ∧ i = 0 then some (S.unitV, ()) else none⟩

open Classical in
/-- Answers `lk.0` alternately `ff` then `tt` (its state is a `Bool`), and `llog.0` with `()`. -/
noncomputable def Rrec (lk llog : S.EA.Lab) : S.Runner :=
  ⟨fun l i => (l = lk ∨ l = llog) ∧ i = 0, Bool, false,
   fun b l i _ => if l = lk ∧ i = 0 then some (if b then S.tt else S.ff, !b)
     else if l = llog ∧ i = 0 then some (S.unitV, b) else none⟩

def tickEv (lt : S.EA.Lab) : S.Event := .io lt 0 S.unitV S.unitV
def logEv (llog : S.EA.Lab) : S.Event := .io llog 0 S.tt S.unitV

/-! ### Shared clauses and handlers -/

/-- `handle le {return x ⇒ inl x; raise _ ⇒ inr ()} M`. -/
def toResult (le : S.EA.Lab) (M : S.Term) : S.Term :=
  S.handle le (S.hnd (S.lam (S.ret (S.inl (S.var 0)))) [S.lam (S.ret (S.inr S.unitV))]) M
/-- `op (_, k) ⇒ resume k ()`. -/
def resumeCl : S.Val := S.lam (S.split (S.var 0) (S.resume (S.var 0) S.unitV))
/-- `handle l {return x ⇒ x; op (_, k) ⇒ resume k ()} M`. -/
def resumer (l : S.EA.Lab) (M : S.Term) : S.Term :=
  S.handle l (S.hnd (S.lam (S.ret (S.var 0))) [S.resumeCl]) M
/-- `wait (_, k) ⇒ cancel k; inr ()`. -/
def timeoutCl : S.Val :=
  S.lam (S.split (S.var 0) (S.bind (S.cancel (S.var 0)) (S.ret (S.inr S.unitV))))
/-- `handle lw {return x ⇒ inl x; wait (_, k) ⇒ cancel k; inr ()} M`. -/
def timeoutH (lw : S.EA.Lab) (M : S.Term) : S.Term :=
  S.handle lw (S.hnd (S.lam (S.ret (S.inl (S.var 0)))) [S.timeoutCl]) M
/-- `op (_, k) ⇒ tick (); resume k ()`. -/
def tickingCl (lt : S.EA.Lab) : S.Val :=
  S.lam (S.split (S.var 0) (S.bind (S.perform lt 0 S.unitV) (S.resume (S.var 1) S.unitV)))
/-- `λ_. return tt`. -/
def pureCb : S.Val := S.lam (S.ret S.tt)
/-- `λ_. raise le ()`. -/
def failCb (le : S.EA.Lab) : S.Val := S.lam (S.raise le 0 S.unitV)
/-- `λ_. wait (); return tt`. -/
def asyncCb (lw : S.EA.Lab) : S.Val := S.lam (S.bind (S.perform lw 0 S.unitV) (S.ret S.tt))

/-! ### S6's rejected programs (the witnesses) -/

/-- `op (v, k) ⇒ return ff`: κ dropped. -/
def dropCl : S.Val := S.lam (S.split (S.var 0) (S.ret S.ff))
/-- `op (v, k) ⇒ resume k () to _. resume k ()`: κ used twice. -/
def twiceCl : S.Val :=
  S.lam (S.split (S.var 0) (S.bind (S.resume (S.var 0) S.unitV) (S.resume (S.var 1) S.unitV)))
/-- `op (v, k) ⇒ cancel k to _. return ff`. -/
def cancelCl : S.Val := S.lam (S.split (S.var 0) (S.bind (S.cancel (S.var 0)) (S.ret S.ff)))
/-- `op (v, k) ⇒ cancel k to _. resume k ()`. -/
def cancelResumeCl : S.Val :=
  S.lam (S.split (S.var 0) (S.bind (S.cancel (S.var 0)) (S.resume (S.var 1) S.unitV)))
/-- `handle l {return x ⇒ x; op (v, k) ⇒ cl} (op () to _. return tt)`.  R1: `withCl l dropCl` at
`l` affine or linear; R2: `withCl l twiceCl`; R3: `withCl ll cancelCl` at `ll` linear; R4:
`withCl lw cancelResumeCl` at `lw` affine. -/
def withCl (l : S.EA.Lab) (cl : S.Val) : S.Term :=
  S.handle l (S.hnd (S.lam (S.ret (S.var 0))) [cl]) (S.bind (S.perform l 0 S.unitV) (S.ret S.tt))

/-! ### E1: no colouring -/

/-- `f = λg. g ()`. -/
def hof : S.Val := S.lam (S.app (S.force (S.var 0)) S.unitV)
/-- `f pure to b₁. handle exn {…} (f fail) to b₂. handle wait {…resume…} (f async) to b₃.
return (b₁, (b₂, b₃))`, `f` is `var 0`. -/
def threeUses (le lw : S.EA.Lab) : S.Term :=
  S.bind (S.call (S.var 0) S.pureCb)
  (S.bind (S.toResult le (S.call (S.var 1) (S.failCb le)))
  (S.bind (S.resumer lw (S.call (S.var 2) (S.asyncCb lw)))
  (S.ret (S.pair (S.var 2) (S.pair (S.var 1) (S.var 0))))))
/-- E1: `let f = f in threeUses`. -/
def noColour (le lw : S.EA.Lab) : S.Term := S.lets [S.hof] (S.threeUses le lw)
/-- `(tt, (inr (), tt))`. -/
def ans1 : S.Val := S.pair S.tt (S.pair (S.inr S.unitV) S.tt)
def ty1 : S.Ty := S.Tensor S.bool (S.Tensor (S.Sum S.bool S.UnitT) S.bool)
/-- `return x ⇒ λ_. return x`. -/
def schedRet : S.Val := S.lam (S.ret (S.lam (S.ret (S.var 1))))
/-- `wait (_, k) ⇒ λ_. resume k () to g. g ()`. -/
def schedCl : S.Val := S.lam (S.split (S.var 0) (S.ret (S.lam
  (S.bind (S.resume (S.var 1) S.unitV) (S.app (S.force (S.var 0)) S.unitV)))))
/-- `sched M = handle wait {return x ⇒ λ_. return x; wait (_, k) ⇒ λ_. resume k () to g. g ()} M`. -/
def sched (lw : S.EA.Lab) (M : S.Term) : S.Term := S.handle lw (S.hnd S.schedRet [S.schedCl]) M
/-- `sched (f async) to g. f pure to b. g () to b₃. return (b, b₃)`, `f` is `var 0`. -/
def usesS (lw : S.EA.Lab) : S.Term :=
  S.bind (S.sched lw (S.call (S.var 0) (S.asyncCb lw)))
  (S.bind (S.call (S.var 1) S.pureCb)
  (S.bind (S.app (S.force (S.var 1)) S.unitV)
  (S.ret (S.pair (S.var 1) (S.var 0)))))
/-- E1′: `let f = f in usesS`. -/
def noColourS (lw : S.EA.Lab) : S.Term := S.lets [S.hof] (S.usesS lw)

/-! ### E2: higher-order polymorphism -/

/-- `twice = λh. λg. h g to x. h g to y. return (x, y)`. -/
def twice : S.Val := S.lam (S.force (S.lam (S.bind (S.app (S.force (S.var 1)) (S.var 0))
  (S.bind (S.app (S.force (S.var 2)) (S.var 1)) (S.ret (S.pair (S.var 1) (S.var 0)))))))
/-- `tw f pure to p₁. handle exn {…} (tw f fail) to p₂. return (p₁, p₂)`, `tw` is `var 0`, `f` is
`var 1`. -/
def body2a (le : S.EA.Lab) : S.Term :=
  S.bind (S.call2 (S.var 0) (S.var 1) S.pureCb)
  (S.bind (S.toResult le (S.call2 (S.var 1) (S.var 2) (S.failCb le)))
    (S.ret (S.pair (S.var 1) (S.var 0))))
def prog2a (le : S.EA.Lab) : S.Term := S.lets [S.twice, S.hof] (S.body2a le)
def ty2a : S.Ty := S.Tensor (S.Tensor S.bool S.bool) (S.Sum (S.Tensor S.bool S.bool) S.UnitT)

/-- `compose = λg₁. λg₂. return (λ_. g₁ () to _. g₂ ())`. -/
def compose : S.Val := S.lam (S.force (S.lam (S.ret (S.lam
  (S.bind (S.app (S.force (S.var 2)) S.unitV) (S.app (S.force (S.var 2)) S.unitV))))))
/-- `c pure pure to k₀. c async pure to k₁. k₀ () to b₀. handle wait {…resume…} (k₁ ()) to b₁.
return (b₀, b₁)`, `c` is `var 0`. -/
def body2b (lw : S.EA.Lab) : S.Term :=
  S.bind (S.call2 (S.var 0) S.pureCb S.pureCb) (S.bind (S.call2 (S.var 1) (S.asyncCb lw) S.pureCb)
  (S.bind (S.call (S.var 1) S.unitV) (S.bind (S.resumer lw (S.call (S.var 1) S.unitV))
  (S.ret (S.pair (S.var 1) (S.var 0))))))
def prog2b (lw : S.EA.Lab) : S.Term := S.lets [S.compose] (S.body2b lw)
def ty2b : S.Ty := S.Tensor S.bool S.bool

/-- `retry = λpol. λbody. handle exn {return x ⇒ x; raise _ ⇒ pol () to b. case b of inl _ ⇒ ff
| inr _ ⇒ tt} (body ())`. -/
def retryP (le : S.EA.Lab) : S.Val := S.lam (S.force (S.lam (S.handle le (S.hnd (S.lam (S.ret (S.var 0)))
  [S.lam (S.bind (S.app (S.force (S.var 2)) S.unitV) (S.case (S.var 0) (S.ret S.ff) (S.ret S.tt)))])
  (S.app (S.force (S.var 0)) S.unitV))))
/-- `λ_. log tt; tt`. -/
def logPol (llog : S.EA.Lab) : S.Val := S.lam (S.bind (S.perform llog 0 S.tt) (S.ret S.tt))
/-- `r (λ_. ff) fail to a₁. handle log {…resume…} (r (λ_. log tt; tt) fail) to a₂. return (a₁, a₂)`,
`r` is `var 0`. -/
def body2c (le llog : S.EA.Lab) : S.Term :=
  S.bind (S.call2 (S.var 0) (S.lam (S.ret S.ff)) (S.failCb le))
  (S.bind (S.resumer llog (S.call2 (S.var 1) (S.logPol llog) (S.failCb le)))
    (S.ret (S.pair (S.var 1) (S.var 0))))
def prog2c (le llog : S.EA.Lab) : S.Term := S.lets [S.retryP le] (S.body2c le llog)

/-- `sumGen = λgen. handle yield {return _ ⇒ ff; yield (x, k) ⇒ resume k () to r. case x of
inl _ ⇒ r | inr _ ⇒ tt} (gen ())`. -/
def sumGen (ly : S.EA.Lab) : S.Val := S.lam (S.handle ly (S.hnd (S.lam (S.ret S.ff))
  [S.lam (S.split (S.var 0) (S.bind (S.resume (S.var 0) S.unitV)
    (S.case (S.var 2) (S.ret (S.var 1)) (S.ret S.tt))))])
  (S.app (S.force (S.var 0)) S.unitV))
/-- `λ_. yield ff; yield tt`. -/
def gen1 (ly : S.EA.Lab) : S.Val := S.lam (S.bind (S.perform ly 0 S.ff) (S.perform ly 0 S.tt))
/-- `λ_. yield ff; raise exn ()`. -/
def gen2 (ly le : S.EA.Lab) : S.Val :=
  S.lam (S.bind (S.perform ly 0 S.ff) (S.raise le 0 S.unitV))
/-- `s gen1 to c₁. handle exn {…} (s gen2) to c₂. return (c₁, c₂)`, `s` is `var 0`. -/
def body2d (ly le : S.EA.Lab) : S.Term :=
  S.bind (S.call (S.var 0) (S.gen1 ly)) (S.bind (S.toResult le (S.call (S.var 1) (S.gen2 ly le)))
  (S.ret (S.pair (S.var 1) (S.var 0))))
def prog2d (ly le : S.EA.Lab) : S.Term := S.lets [S.sumGen ly] (S.body2d ly le)
def ty2d : S.Ty := S.Tensor S.bool (S.Sum S.bool S.UnitT)

/-! ### E3: divergence, an effect any function may have -/

/-- `close`: a data state is dropped. -/
def dropS : S.Val := S.lam (S.ret S.unitV)
/-- `drive (return (inr l))`. -/
def runL (l : S.Val) : S.Term := S.drive (S.ret (S.inr l))
/-- `tickStep s = tick (); return (inr s)`. -/
def tickStep (lt : S.EA.Lab) : S.Val :=
  S.lam (S.bind (S.perform lt 0 S.unitV) (S.ret (S.inr (S.var 1))))
/-- `countStep s = case s of inl _ ⇒ tick (); return (inr (inr ())) | inr _ ⇒ return (inl tt)`. -/
def countStep (lt : S.EA.Lab) : S.Val := S.lam (S.case (S.var 0)
  (S.bind (S.perform lt 0 S.unitV) (S.ret (S.inr (S.inr S.unitV)))) (S.ret (S.inl S.tt)))
/-- `logStep s = log tt; return (inr s)`. -/
def logStep (llog : S.EA.Lab) : S.Val :=
  S.lam (S.bind (S.perform llog 0 S.tt) (S.ret (S.inr (S.var 1))))
def tickL (lt : S.EA.Lab) : S.Val := S.unfold S.UnitT S.UnitT (S.tickStep lt) S.dropS S.unitV
def countL (lt : S.EA.Lab) : S.Val := S.unfold S.bool S.UnitT (S.countStep lt) S.dropS (S.inl S.unitV)
def logL (llog : S.EA.Lab) : S.Val := S.unfold S.UnitT S.UnitT (S.logStep llog) S.dropS S.unitV
/-- A silent loop. -/
def spinL : S.Val := S.unfold S.UnitT S.UnitT (S.lam (S.ret (S.inr (S.var 0)))) S.dropS S.unitV
/-- The delay bind at two loops (SPEC §14's `div_bind`, whose continuation here returns the second
loop): the state is `inl (l₁, l₂)`, in the first loop, or `inr l₂`, in the second.  `A` is the
second loop's answer. -/
def seqStep : S.Val := S.lam (S.case (S.var 0)
  (S.split (S.var 0) (S.bind (S.next (S.var 1)) (S.case (S.var 0)
     (S.ret (S.inr (S.inr (S.var 2))))
     (S.ret (S.inr (S.inl (S.pair (S.var 0) (S.var 2))))))))
  (S.bind (S.next (S.var 0)) (S.case (S.var 0)
     (S.ret (S.inl (S.var 0)))
     (S.ret (S.inr (S.inr (S.var 0)))))))
def seqClose : S.Val := S.lam (S.case (S.var 0)
  (S.split (S.var 0) (S.bind (S.close (S.var 1)) (S.close (S.var 1)))) (S.close (S.var 0)))
def seqL (A : S.Ty) (l₁ l₂ : S.Val) : S.Val :=
  S.unfold A S.UnitT S.seqStep S.seqClose (S.inl (S.pair l₁ l₂))
/-- A handler installed per observation (SPEC §19), its clause performing the platform `tick`:
`unfold (λl. handle log {return x ⇒ x; log (_, k) ⇒ tick (); resume k ()} (next l)) (λl. close l) l`. -/
def handleL (lt llog : S.EA.Lab) (l : S.Val) : S.Val :=
  S.unfold S.UnitT S.UnitT
    (S.lam (S.handle llog (S.hnd (S.lam (S.ret (S.var 0))) [S.tickingCl lt]) (S.next (S.var 0))))
    (S.lam (S.close (S.var 0))) l
/-- `div_fuel`: observe at most `n` times, then close. -/
def fuel : ℕ → S.Val → S.Term
  | 0, l => S.bind (S.close l) (S.ret (S.inr S.unitV))
  | n + 1, l => S.bind (S.next l) (S.case (S.var 0) (S.ret (S.inl (S.var 0))) (fuel n (S.var 0)))
/-- `divF = λs. return (unfold countStep drop s)`: a div function, its result a loop. -/
def divF (lt : S.EA.Lab) : S.Val :=
  S.lam (S.ret (S.unfold S.bool S.UnitT (S.countStep lt) S.dropS (S.var 0)))
/-- `d (inl ()) to l₁. d (inl ()) to l₂. return (inr (seqL l₁ l₂))`, `d` is `var 0`. -/
def e3cBody : S.Term :=
  S.bind (S.call (S.var 0) (S.inl S.unitV)) (S.bind (S.call (S.var 1) (S.inl S.unitV))
  (S.ret (S.inr (S.seqL S.bool (S.var 1) (S.var 0)))))
def e3c (lt : S.EA.Lab) : S.Term := S.drive (S.lets [S.divF lt] S.e3cBody)
/-- `λ_. return tickL`. -/
def divCb (lt : S.EA.Lab) : S.Val := S.lam (S.ret (S.tickL lt))
/-- `f (λ_. return tickL) to l. return (inr l)`, `f` is `var 0`. -/
def e3fBody (lt : S.EA.Lab) : S.Term :=
  S.bind (S.call (S.var 0) (S.divCb lt)) (S.ret (S.inr (S.var 0)))
def e3f (lt : S.EA.Lab) : S.Term := S.drive (S.lets [S.hof] (S.e3fBody lt))

/-! ### E4: deep handlers -/

/-- `handle yield {return _ ⇒ (); yield (_, k) ⇒ tick (); resume k ()} (yield tt; yield ff)`. -/
def deepGen (ly lt : S.EA.Lab) : S.Term :=
  S.handle ly (S.hnd (S.lam (S.ret S.unitV)) [S.tickingCl lt])
    (S.bind (S.perform ly 0 S.tt) (S.perform ly 0 S.ff))

/-! ### E5: nested handlers, in both orders -/

/-- `log tt; raise exn ()`. -/
def body5 (llog le : S.EA.Lab) : S.Term := S.bind (S.perform llog 0 S.tt) (S.raise le 0 S.unitV)
/-- `return x ⇒ λs. (x, s)`. -/
def logRet : S.Val := S.lam (S.ret (S.lam (S.ret (S.pair (S.var 1) (S.var 0)))))
/-- `log (b, k) ⇒ λs. resume k () to g. g b`. -/
def logCl : S.Val := S.lam (S.split (S.var 0) (S.ret (S.lam
  (S.bind (S.resume (S.var 1) S.unitV) (S.app (S.force (S.var 0)) (S.var 3))))))
/-- `withLog M = handle log {return x ⇒ λs. (x, s); log (b, k) ⇒ λs. resume k () to g. g b} M
to g. g ff`: a state-passing handler that keeps the last logged value (decision 59). -/
def withLog (llog : S.EA.Lab) (M : S.Term) : S.Term :=
  S.bind (S.handle llog (S.hnd S.logRet [S.logCl]) M) (S.app (S.force (S.var 0)) S.ff)

/-! ### E6: no accidental handling -/

/-- `fwrap = λg. handle exnᵢ {return x ⇒ x; raise _ ⇒ ff} (g ())`. -/
def fwrap (li : S.EA.Lab) : S.Val := S.lam (S.handle li (S.hnd (S.lam (S.ret (S.var 0)))
  [S.lam (S.ret S.ff)]) (S.app (S.force (S.var 0)) S.unitV))
/-- `handle exnₒ {…inl/inr…} (let w = fwrap in w (λ_. raise exnₒ ()))`. -/
def tunnel (li lo : S.EA.Lab) : S.Term :=
  S.toResult lo (S.lets [S.fwrap li] (S.call (S.var 0) (S.failCb lo)))

/-! ### E7: abandoning a suspension, and the cancel policy -/

/-- `body D = (wait (); return tt) then x. return x unwind D`. -/
def bodyF (lw : S.EA.Lab) (D : S.Term) : S.Term :=
  S.thenT (S.bind (S.perform lw 0 S.unitV) (S.ret S.tt)) (S.ret (S.var 0)) D
/-- `timeout (body ())`. -/
def e7a (lw : S.EA.Lab) : S.Term := S.timeoutH lw (S.bodyF lw (S.ret S.unitV))
/-- `handle exnₒ {…} (timeout (body (raise exnₒ ())))`. -/
def e7b (lw lo : S.EA.Lab) : S.Term :=
  S.toResult lo (S.timeoutH lw (S.bodyF lw (S.raise lo 0 S.unitV)))
/-- `timeout (handle exnᵢ {…} (body (raise exnᵢ ())))`. -/
def e7c (lw li : S.EA.Lab) : S.Term :=
  S.timeoutH lw (S.toResult li (S.bodyF lw (S.raise li 0 S.unitV)))
/-- `handle exn_a {…} (handle exn_b {…} (timeout ((body (raise exn_a ())) then x. return x unwind
raise exn_b ())))`. -/
def e7d (lw la lb : S.EA.Lab) : S.Term := S.toResult la (S.toResult lb (S.timeoutH lw
  (S.thenT (S.bodyF lw (S.raise la 0 S.unitV)) (S.ret (S.var 0)) (S.raise lb 0 S.unitV))))
/-- A finaliser that raises `l` fires and ends with `l`. -/
def finTr (l : S.EA.Lab) : List S.Event :=
  [.fire (S.raise l 0 S.unitV), .finEnd (some (l, 0, S.unitV))]
def ty7 : S.Ty := S.Sum (S.Sum S.bool S.UnitT) S.UnitT
def ty7d : S.Ty := S.Sum (S.Sum (S.Sum S.bool S.UnitT) S.UnitT) S.UnitT

/-! ### E8: unwinding through finalisers -/

/-- `handle exn {…} ((raise exn ()) then x. return x unwind ())`. -/
def e8a (le : S.EA.Lab) : S.Term :=
  S.toResult le (S.thenT (S.raise le 0 S.unitV) (S.ret (S.var 0)) (S.ret S.unitV))
/-- `handle exn_a {…} (handle exn_b {…} ((raise exn_a ()) then x. return x unwind raise exn_b ()))`. -/
def e8b (la lb : S.EA.Lab) : S.Term := S.toResult la (S.toResult lb
  (S.thenT (S.raise la 0 S.unitV) (S.ret (S.var 0)) (S.raise lb 0 S.unitV)))

/-! ### E9: a stored continuation -/

/-- `return _ ⇒ λc. ff`. -/
def stashRet : S.Val := S.lam (S.ret (S.lam (S.ret S.ff)))
/-- `yield (x, k) ⇒ λc. case c of inl _ ⇒ cancel k; x | inr _ ⇒ resume k () to g. g (inr ())`. -/
def stashCl : S.Val := S.lam (S.split (S.var 0) (S.ret (S.lam (S.case (S.var 0)
  (S.bind (S.cancel (S.var 2)) (S.ret (S.var 4)))
  (S.bind (S.resume (S.var 2) S.unitV) (S.app (S.force (S.var 0)) (S.inr S.unitV)))))))
def stash (ly : S.EA.Lab) (M : S.Term) : S.Term := S.handle ly (S.hnd S.stashRet [S.stashCl]) M
/-- `yield tt; yield ff`. -/
def gen9 (ly : S.EA.Lab) : S.Term := S.bind (S.perform ly 0 S.tt) (S.perform ly 0 S.ff)
/-- `stash M to g. g c`. -/
def e9 (ly : S.EA.Lab) (M : S.Term) (c : S.Val) : S.Term :=
  S.bind (S.stash ly M) (S.app (S.force (S.var 0)) c)
/-- `handle exnₒ {…} (stash (gen then x. return x unwind raise exnₒ ()) to g. g (inl ()))`. -/
def e9c (ly lo : S.EA.Lab) : S.Term :=
  S.toResult lo (S.e9 ly (S.thenT (S.gen9 ly) (S.ret (S.var 0)) (S.raise lo 0 S.unitV)) (S.inl S.unitV))

/-! ### E10: the reconciler -/

/-- `timeout = λb. handle wait {return x ⇒ x; wait (_, k) ⇒ cancel k; return ff} (b ())`. -/
def timeoutR (lw : S.EA.Lab) : S.Val := S.lam (S.handle lw (S.hnd (S.lam (S.ret (S.var 0))) [S.cancelCl])
  (S.app (S.force (S.var 0)) S.unitV))
/-- `retry = λb. handle exn {return x ⇒ x; raise _ ⇒ handle exn {return x ⇒ x; raise _ ⇒ ff}
(b ())} (b ())`. -/
def retryR (le : S.EA.Lab) : S.Val := S.lam (S.handle le (S.hnd (S.lam (S.ret (S.var 0)))
  [S.lam (S.handle le (S.hnd (S.lam (S.ret (S.var 0))) [S.lam (S.ret S.ff)])
     (S.app (S.force (S.var 1)) S.unitV))])
  (S.app (S.force (S.var 0)) S.unitV))
/-- `call = λ_. kube () to ok. case ok of inl _ ⇒ raise exn () | inr _ ⇒ tt`. -/
def callK (lk le : S.EA.Lab) : S.Val :=
  S.lam (S.bind (S.perform lk 0 S.unitV) (S.case (S.var 0) (S.raise le 0 S.unitV) (S.ret S.tt)))
/-- `waitCall = λ_. wait (); call ()`. -/
def waitCall (lw lk le : S.EA.Lab) : S.Val :=
  S.lam (S.bind (S.perform lw 0 S.unitV) (S.app (S.force (S.callK lk le)) S.unitV))
/-- The step, with `retry` as `var 1` and `timeout` as `var 2` inside it (the context
`[retry, timeout]` outside it): `retry (λ_. timeout call) to a. timeout (λ_. retry call) to b.
timeout (λ_. retry waitCall) to c. log c; return (inr s)`. -/
def iterOpen (lw le lk llog : S.EA.Lab) : S.Val := S.lam
  (S.bind (S.call (S.var 1) (S.lam (S.call (S.var 3) (S.callK lk le))))
  (S.bind (S.call (S.var 3) (S.lam (S.call (S.var 3) (S.callK lk le))))
  (S.bind (S.call (S.var 4) (S.lam (S.call (S.var 4) (S.waitCall lw lk le))))
  (S.bind (S.perform llog 0 (S.var 0)) (S.ret (S.inr (S.var 4)))))))
def reconBody (lw le lk llog : S.EA.Lab) : S.Term :=
  S.ret (S.inr (S.unfold S.UnitT S.UnitT (S.iterOpen lw le lk llog) S.dropS S.unitV))
/-- `drive (let timeout = timeout; let retry = retry in return (inr (unfold step drop ())))`. -/
def recon (lw le lk llog : S.EA.Lab) : S.Term :=
  S.drive (S.lets [S.retryR le, S.timeoutR lw] (S.reconBody lw le lk llog))
/-- One iteration's observable trace. -/
def iterTrace (lk llog : S.EA.Lab) : List S.Event :=
  [.io lk 0 S.unitV S.ff, .io lk 0 S.unitV S.tt, .io lk 0 S.unitV S.ff, .io lk 0 S.unitV S.tt,
   .io llog 0 S.ff S.unitV]

end EffectSystem

end Targets.A
