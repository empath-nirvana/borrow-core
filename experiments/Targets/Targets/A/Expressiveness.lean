import Targets.A.Programs

/-!
# System A — the expressiveness properties E1–E10 (RESTRUCTURE §1.6)

Each is an **(E)** property: a lower bound, saying what the system **must** accept and run.  It
names its labels and signatures, its runner, its programs, the types the programs must have, and
the behaviour they must show (the answer, and the trace of platform and finaliser events).  Where a
decided feature is needed, it also states a **schema** over every row and every closed callback
body the instance types (effect polymorphism, in Zhang–Myers' shape `f : ∀α. (N → [N]α) → [N]α`,
used as `f [∅] …` and `f [h.lbl] …`).  Each holds at any distinct labels with the stated
signatures, and some such labels exist.

A system that types nothing, or has no effects, fails every one (`Targets/A/NonVacuity.lean`).
The decided features are justified here, not decreed as structure fields:

| property | the decided feature it needs | why |
|---|---|---|
| E1, E2, E6, E10 | row variables (decision 62) | one typing serves a callback at every row (`not_noColouring_of_monoCallback`) |
| E3 | divergence as an effect (decision 35) | a loop is built, sequenced, handled, fuelled and driven; totality fails it (`not_loops_of_total`) |
| E4, E5, E10 | deep handlers, nesting (decision 62; K4, U5) | a handler catches every operation, those after a resume included |
| E7, E8, E9 | linear and affine continuations, explicit cancel (decision 62, SPEC §19) | abandoning a suspension is typable, and its finalisers run |
-/

namespace Targets.A

namespace EffectSystem

variable (S : EffectSystem)

/-- **E1: no colouring (effect polymorphism)**, the lead axis (decisions F1/F2: "one function for
every context").  One higher-order function is typed **once**, and that one typing serves a
callback at **every** row: the pure row, a failing row, a suspending row, and every other row the
instance types a callback body at.  Two concrete programs pin the behaviour: the three uses in one
program (E1), and a use whose callback really suspends, its continuation held after its handler
returned while `f` runs again (E1′). -/
def NoColouring : Prop :=
  S.ForLabels [S.sigExn, S.sigWait] fun ls => ∀ le lw, ls = [le, lw] →
    ∃ A, S.derV [] S.hof A ∧
      -- the schema: this one typing of `f` serves a callback at every row …
      S.PolyUse [A] (fun g => S.call (S.var 0) g) S.bool S.bool ∧
      -- … and `f` calls the callback, catching nothing
      (∀ ε M, S.der [] M (S.F ε S.bool) →
         S.CallsThrough (fun _ => True) (S.lets [S.hof] (S.call (S.var 0) (S.lam M))) M) ∧
      -- the three callbacks' bodies, each at its own row
      S.der [] (S.ret S.tt) (S.F S.EA.unit S.bool) ∧
      S.der [] (S.raise le 0 S.unitV) (S.F (S.EA.lift le) S.bool) ∧
      S.der [] (S.bind (S.perform lw 0 S.unitV) (S.ret S.tt)) (S.F (S.EA.lift lw) S.bool) ∧
      -- E1: one program, three uses; E1′: a real suspension (`LetLaw` types the whole programs)
      S.der [A] (S.threeUses le lw) (S.F S.EA.unit S.ty1) ∧ S.RunsTo S.R₀ (S.noColour le lw) S.ans1 [] ∧
      S.der [A] (S.usesS lw) (S.F S.EA.unit (S.Tensor S.bool S.bool)) ∧
      S.RunsTo S.R₀ (S.noColourS lw) (S.pair S.tt S.tt) []

/-- **E2: higher-order polymorphism** (PR #233's closing comment: "the higher-order cases
(callbacks taking callbacks, stored or returned callbacks, policies as values, effectful codata)
were left pending behind workarounds. The goal was the general form.").  Each program binds its
higher-order function once, uses it at two rows, one of them the pure row, and states its schema.
Each needs only let-bound polymorphism with open rows, at one answer type per function. -/
def HigherOrderPoly : Prop :=
  S.ForLabels [S.sigExn, S.sigWait, S.sigYield, S.sigLog] fun ls =>
    ∀ le lw ly llog, ls = [le, lw, ly, llog] →
    -- E2a: `twice` and `f` typed once; `twice f g` serves `g` at every row, and calls it
    (∃ Af At, S.derV [] S.hof Af ∧ S.derV [] S.twice At ∧
       S.PolyUse [At, Af] (fun g => S.call2 (S.var 0) (S.var 1) g) S.bool (S.Tensor S.bool S.bool) ∧
       (∀ ε M, S.der [] M (S.F ε S.bool) →
          S.CallsThrough (fun _ => True)
            (S.lets [S.twice, S.hof] (S.call2 (S.var 0) (S.var 1) (S.lam M))) M) ∧
       S.der [] (S.ret S.tt) (S.F S.EA.unit S.bool) ∧
       S.der [] (S.raise le 0 S.unitV) (S.F (S.EA.lift le) S.bool) ∧
       S.der [At, Af] (S.body2a le) (S.F S.EA.unit S.ty2a) ∧
       S.RunsTo S.R₀ (S.prog2a le) (S.pair (S.pair S.tt S.tt) (S.inr S.unitV)) []) ∧
    -- E2b: `compose`; the composed callback, stored and called later, serves every row
    (∃ Ac, S.derV [] S.compose Ac ∧
       S.PolyUse [Ac] (fun g => S.bind (S.call2 (S.var 0) g S.pureCb) (S.call (S.var 0) S.unitV))
         S.bool S.bool ∧
       S.der [Ac] (S.body2b lw) (S.F S.EA.unit S.ty2b) ∧
       S.RunsTo S.R₀ (S.prog2b lw) (S.pair S.tt S.tt) []) ∧
    -- E2c: `retry`: the policy at every row without `exn`, the body at every `exn ⊙ ρ`
    (∃ Ar, S.derV [] (S.retryP le) Ar ∧
       S.PolyUseLacks [Ar] le (fun g => S.call2 (S.var 0) g (S.failCb le)) S.bool S.bool ∧
       S.PolyUseOpen [Ar] le (fun g => S.call2 (S.var 0) (S.lam (S.ret S.ff)) g) S.bool S.bool ∧
       S.der [Ar] (S.body2c le llog) (S.F S.EA.unit S.ty2b) ∧
       S.RunsTo S.R₀ (S.prog2c le llog) (S.pair S.ff S.tt) []) ∧
    -- E2d: `sumGen`: the generator at every `yield ⊙ ρ`
    (∃ As, S.derV [] (S.sumGen ly) As ∧
       S.PolyUseOpen [As] ly (fun g => S.call (S.var 0) g) S.UnitT S.bool ∧
       S.der [As] (S.body2d ly le) (S.F S.EA.unit S.ty2d) ∧
       S.RunsTo S.R₀ (S.prog2d ly le) (S.pair S.tt (S.inr S.unitV)) [])

/-- **E3: divergence, an effect any function may have** (decision 35: "Any function may loop
without bound if its type says so; it is not a privilege of `main` … A div function returns a loop
… sequencing loops is the delay bind … running a loop is handling the effect: the runtime drives
`main` forever, and `div_fuel` runs `n` steps"; SPEC §19 *Acceptance* (4): "An infinite loop that
logs").  A loop is built from a step function, a close and a state (`unfold`), observed anywhere
(`next`, `close`), and run without bound by the runtime's driver (`drive`) at the top. -/
def Loops : Prop :=
  S.ForLabels [S.sigTick, S.sigLog] fun ls => ∀ lt llog, ls = [lt, llog] →
    -- E3a, E3b: a loop that never ends, and one that ends
    (∃ ε L, S.Answers (S.Rtick lt) ε ∧ S.der [] (S.runL (S.tickL lt)) (S.F ε (S.Sum S.UnitT L))) ∧
    S.RunsForever (S.Rtick lt) (S.runL (S.tickL lt)) (fun n => List.replicate n (S.tickEv lt)) ∧
    (∃ ε L, S.Answers (S.Rtick lt) ε ∧ S.der [] (S.runL (S.countL lt)) (S.F ε (S.Sum S.bool L))) ∧
    S.RunsTo (S.Rtick lt) (S.runL (S.countL lt)) S.tt [S.tickEv lt] ∧
    -- E3c: a div function, typed once, called twice inside a program that sequences its loops
    (∃ Ad ε L, S.derV [] (S.divF lt) Ad ∧ S.Answers (S.Rtick lt) ε ∧
       S.der [Ad] S.e3cBody (S.F ε (S.Sum S.bool L)) ∧
       S.der [] (S.e3c lt) (S.F ε (S.Sum S.bool L))) ∧
    S.RunsTo (S.Rtick lt) (S.e3c lt) S.tt [S.tickEv lt, S.tickEv lt] ∧
    -- E3d: a loop under a user handler whose clause performs the platform tick
    (∃ ε L, S.Answers (S.Rtick lt) ε ∧
       S.der [] (S.runL (S.handleL lt llog (S.logL llog))) (S.F ε (S.Sum S.UnitT L))) ∧
    S.RunsForever (S.Rtick lt) (S.runL (S.handleL lt llog (S.logL llog)))
      (fun n => List.replicate n (S.tickEv lt)) ∧
    -- E3e: two loops sequenced, the first ending and the second not
    (∃ ε L, S.Answers (S.Rtl lt llog) ε ∧
       S.der [] (S.runL (S.seqL S.UnitT (S.countL lt) (S.logL llog))) (S.F ε (S.Sum S.UnitT L))) ∧
    S.RunsForever (S.Rtl lt llog) (S.runL (S.seqL S.UnitT (S.countL lt) (S.logL llog)))
      (fun n => S.tickEv lt :: List.replicate n (S.logEv llog)) ∧
    -- E3f: the no-colouring function applied to a div callback
    (∃ A' ε L, S.derV [] S.hof A' ∧ S.Answers (S.Rtick lt) ε ∧
       S.der [A'] (S.e3fBody lt) (S.F ε (S.Sum S.UnitT L)) ∧
       S.der [] (S.e3f lt) (S.F ε (S.Sum S.UnitT L))) ∧
    S.RunsForever (S.Rtick lt) (S.e3f lt) (fun n => List.replicate n (S.tickEv lt)) ∧
    -- E3g: fuel makes a silent loop total at a data answer of the pure row; the driver runs it
    -- forever
    S.der [] (S.fuel 3 S.spinL) (S.F S.EA.unit S.bool) ∧
    S.RunsTo S.R₀ (S.fuel 3 S.spinL) (S.inr S.unitV) [] ∧
    (∃ L, S.der [] (S.runL S.spinL) (S.F S.EA.unit (S.Sum S.UnitT L))) ∧
    S.RunsForever S.R₀ (S.runL S.spinL) (fun _ => [])

/-- **E4: deep handlers** (decision 62, "Handlers are deep").  One handler, written once, catches
every yield of the computation, including those performed after a resume.  Its clause performs a
platform `tick`, so the trace counts the catches. -/
def DeepHandler : Prop :=
  S.ForLabels [S.sigYield, S.sigTick] fun ls => ∀ ly lt, ls = [ly, lt] →
    S.der [] (S.deepGen ly lt) (S.F (S.EA.lift lt) S.UnitT) ∧
    S.RunsTo (S.Rtick lt) (S.deepGen ly lt) S.unitV [S.tickEv lt, S.tickEv lt]

/-- **E5: nested handlers, in both orders** (K4: the reconciler chain must "work, full stop"; SPEC
§19 *Acceptance* (1), "in both nesting orders, with each order's observable result").  The first
program forwards a resuming operation through `exn`'s handler, and the resume reinstalls it; the
second forwards a raise through `log`'s handler, which the unwind drops with its state. -/
def NestedHandlers : Prop :=
  S.ForLabels [S.sigLog, S.sigExn] fun ls => ∀ llog le, ls = [llog, le] →
    S.der [] (S.withLog llog (S.toResult le (S.body5 llog le)))
      (S.F S.EA.unit (S.Tensor (S.Sum S.UnitT S.UnitT) S.bool)) ∧
    S.RunsTo S.R₀ (S.withLog llog (S.toResult le (S.body5 llog le))) (S.pair (S.inr S.unitV) S.tt) [] ∧
    S.der [] (S.toResult le (S.withLog llog (S.body5 llog le)))
      (S.F S.EA.unit (S.Sum (S.Tensor S.UnitT S.bool) S.UnitT)) ∧
    S.RunsTo S.R₀ (S.toResult le (S.withLog llog (S.body5 llog le))) (S.inr S.unitV) []

/-- **E6: no accidental handling** (survey #10; Zhang–Myers' abstract: "it is impossible for
higher-order, effect-polymorphic code to accidentally handle effects raised by functions passed in;
such effects tunnel through the higher-order, calling procedures polymorphic to them").  `fwrap`
handles its own instance of an effect and is typed once, its callback and its use at the **same**
row, every row without its own label (Zhang–Myers' `f : ∀α. (N → [N]α) → [N]α`, used as
`f [∅] …` and `f [h.lbl] (g h)`); a callback raising another instance tunnels through. -/
def Tunnel : Prop :=
  S.ForLabels [S.sigExn, S.sigExn] fun ls => ∀ li lo, ls = [li, lo] →
    ∃ Af, S.derV [] (S.fwrap li) Af ∧
      -- one typing of `fwrap`: the callback and the use at the same row ε, every ε without `li`
      S.PolyUseLacks [Af] li (fun g => S.call (S.var 0) g) S.bool S.bool ∧
      (∀ ε M, S.Lacks ε li → S.der [] M (S.F ε S.bool) →
         S.CallsThrough (· ≠ li) (S.lets [S.fwrap li] (S.call (S.var 0) (S.lam M))) M) ∧
      S.der [] (S.ret S.tt) (S.F S.EA.unit S.bool) ∧
      S.der [] (S.raise lo 0 S.unitV) (S.F (S.EA.lift lo) S.bool) ∧
      S.der [] (S.tunnel li lo) (S.F S.EA.unit (S.Sum S.bool S.UnitT)) ∧
      S.RunsTo S.R₀ (S.tunnel li lo) (S.inr S.unitV) []

/-- **E7: abandoning a suspension, and the cancel policy as built** (SPEC §19 *Cancels*;
*Acceptance* (5), (6)).  A timer cancels a suspended body whose frame holds a finaliser.  E7a: the
canceller proceeds and the frozen finaliser runs once; E7b: its error is re-raised at the
canceller; E7c: the error of a label the cancelled region handles is suppressed, and the region's
dying handler does not catch it; E7d: innermost first, and the first error is kept. -/
def CancelPolicy : Prop :=
  S.ForLabels [S.sigWait, S.sigExn, S.sigExn] fun ls => ∀ lw la lb, ls = [lw, la, lb] →
    S.der [] (S.e7a lw) (S.F S.EA.unit (S.Sum S.bool S.UnitT)) ∧
    S.RunsTo S.R₀ (S.e7a lw) (S.inr S.unitV) [.fire (S.ret S.unitV), .finEnd none] ∧
    S.der [] (S.e7b lw la) (S.F S.EA.unit S.ty7) ∧
    S.RunsTo S.R₀ (S.e7b lw la) (S.inr S.unitV) (S.finTr la) ∧
    S.der [] (S.e7c lw la) (S.F S.EA.unit S.ty7) ∧
    S.RunsTo S.R₀ (S.e7c lw la) (S.inr S.unitV) (S.finTr la) ∧
    S.der [] (S.e7d lw la lb) (S.F S.EA.unit S.ty7d) ∧
    S.RunsTo S.R₀ (S.e7d lw la lb) (S.inr S.unitV) (S.finTr la ++ S.finTr lb)

/-- **E8: unwinding through finalisers** (survey #9, "Each destructor runs exactly once, via
unwinding"; SPEC [finalise], with supersession).  An unwind fires a finaliser with no `finEnd`: it
runs in place, and in E8b its raise supersedes the pending one. -/
def UnwindPolicy : Prop :=
  S.ForLabels [S.sigExn, S.sigExn] fun ls => ∀ la lb, ls = [la, lb] →
    S.der [] (S.e8a la) (S.F S.EA.unit (S.Sum S.UnitT S.UnitT)) ∧
    S.RunsTo S.R₀ (S.e8a la) (S.inr S.unitV) [.fire (S.ret S.unitV)] ∧
    S.der [] (S.e8b la lb) (S.F S.EA.unit (S.Sum (S.Sum S.UnitT S.UnitT) S.UnitT)) ∧
    S.RunsTo S.R₀ (S.e8b la lb) (S.inl (S.inr S.unitV)) [.fire (S.raise lb 0 S.unitV)]

/-- **E9: a stored continuation** (SPEC §19 *Acceptance* (6): "A stored continuation is unwound";
the survey's "Stores it and resumes it elsewhere" (A4)).  The handler returns a closure that holds
`κ`; the closure is applied after the handler has returned, and resumes (E9a) or cancels (E9b) it
there; a stored `κ`'s cancel finalises (E9c). -/
def StoredK : Prop :=
  S.ForLabels [S.sigYield, S.sigExn] fun ls => ∀ ly lo, ls = [ly, lo] →
    S.der [] (S.e9 ly (S.gen9 ly) (S.inr S.unitV)) (S.F S.EA.unit S.bool) ∧
    S.RunsTo S.R₀ (S.e9 ly (S.gen9 ly) (S.inr S.unitV)) S.ff [] ∧
    S.der [] (S.e9 ly (S.gen9 ly) (S.inl S.unitV)) (S.F S.EA.unit S.bool) ∧
    S.RunsTo S.R₀ (S.e9 ly (S.gen9 ly) (S.inl S.unitV)) S.tt [] ∧
    S.der [] (S.e9c ly lo) (S.F S.EA.unit (S.Sum S.bool S.UnitT)) ∧
    S.RunsTo S.R₀ (S.e9c ly lo) (S.inr S.unitV) (S.finTr lo)

/-- **E10: the reconciler** (K4, U5: "need to work, full stop"; OQ-13: the reconciler chain's
`timeout` and `retry` "are generic over rows"; the operator: "`call`, which is `retry` of
`timeout` of the call").  A driven loop: each iteration retries a call under a timeout, times out
a retried call, and times out a retried body that waits, cancelled while suspended under the
retry's handler; then it logs to the platform.  `timeout` and `retry` are bound once, each serves
a body at every row with its own label added, and each is used at two rows, at `bool`
throughout. -/
def Reconciler : Prop :=
  S.ForLabels [S.sigWait, S.sigExn, S.sigKube, S.sigLog] fun ls =>
    ∀ lw le lk llog, ls = [lw, le, lk, llog] →
    ∃ At Ar ε L, S.derV [] (S.timeoutR lw) At ∧ S.derV [] (S.retryR le) Ar ∧
      -- the schemas: one typing of each serves a body at every row with its own label added
      S.PolyUseOpen [At] lw (fun g => S.call (S.var 0) g) S.bool S.bool ∧
      (∀ ε M, S.Lacks ε lw → S.der [] M (S.F ε S.bool) →
         S.CallsThrough (· ≠ lw) (S.lets [S.timeoutR lw] (S.call (S.var 0) (S.lam M))) M) ∧
      S.PolyUseOpen [Ar] le (fun g => S.call (S.var 0) g) S.bool S.bool ∧
      S.der [] (S.ret S.tt) (S.F S.EA.unit S.bool) ∧
      S.der [] (S.raise le 0 S.unitV) (S.F (S.EA.lift le) S.bool) ∧
      -- the loop: both bound once, each used at two rows, at `bool` throughout
      S.der [Ar, At] (S.reconBody lw le lk llog) (S.F ε (S.Sum S.UnitT L)) ∧
      S.der [] (S.recon lw le lk llog) (S.F ε (S.Sum S.UnitT L)) ∧ S.Answers (S.Rrec lk llog) ε ∧
      S.RunsForever (S.Rrec lk llog) (S.recon lw le lk llog)
        (fun n => (List.replicate n (S.iterTrace lk llog)).flatten)

/-- **The expressiveness properties of A.** -/
def EProps : Prop :=
  S.NoColouring ∧ S.HigherOrderPoly ∧ S.Loops ∧ S.DeepHandler ∧ S.NestedHandlers ∧ S.Tunnel ∧
    S.CancelPolicy ∧ S.UnwindPolicy ∧ S.StoredK ∧ S.Reconciler

/-- **System A, first pass**: the soundness and the expressiveness properties. -/
def Props : Prop := S.SProps ∧ S.EProps

end EffectSystem

end Targets.A
