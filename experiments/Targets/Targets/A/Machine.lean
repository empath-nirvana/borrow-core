import Targets.A.System

/-!
# System A — S0: the shape of the machine, and the let law (RESTRUCTURE §1.4)

The laws that make the formers mean what they are called.  They are upper bounds on the semantics,
except the let law, which is a lower bound on typing.

* **Evaluation contexts.**  The handler laws, `OpStuck` and `StopsIn` hold in every context, binds
  and applications included, as Yoshioka's `E_Eval` has them: `bind (perform l i v) N` is
  `plug (bindF N) (perform l i v)`, so it is stuck when no handler of `l` encloses it.
* **`appF` up to administrative steps.**  `AppLaw` asks that `M V` *reach* `plug (appF V) M`.
* **The formers are constructors** (`DataInj`): answers are told apart, and an operation or a
  driven term is no answer.  **`OpStuck`** says that the machine does not answer operations, the
  platform does; that is what gives effect safety (S3) its content.
* **An answer is a returned value at which nothing steps** (`IsVal`).  The driver acts on a value
  at the top, with `top` steps, and those are the only steps `Congr` excepts.
* **Inside a driven program.**  `drive M` is `plug driveF M`, so a driven program is a term in a
  context like any other: a non-`top` step of `M` is a step of `drive M` (`Congr` at `driveF`),
  the runner answers an operation a driven loop performs (`RStep.io` at `kcomp driveF K`), and
  S3–S6 hold in a driven loop's contexts.
* **Plugging need not be injective**, and no property reads injectivity.
* **The let law and substitution.**  The schemas type a use with the higher-order value's type in
  the context, and `LetLaw` ties that to the program that binds the value.  A has no substitution
  operation: where a property needs a β-behaviour, it states it per program (`CallsThrough`) or as
  a law of the former (`LoopLaws`).
-/

namespace Targets.A

namespace EffectSystem

variable (S : EffectSystem)

/-- The configuration laws: `init` puts a term in, `setT` replaces it. -/
def ConfLaws : Prop :=
  (∀ e, S.term (S.init e) = e) ∧ (∀ c t, S.term (S.setT c t) = t) ∧
  (∀ c, S.setT c (S.term c) = c) ∧ (∀ c t t', S.setT (S.setT c t) t' = S.setT c t')

/-- Plugging composes.  The five named frames plug as their formers.  A handler frame of `l`
catches `l` and nothing else, a finaliser frame stops a raise and holds its finaliser, the driver
catches nothing and stops nothing, and `catches`, `unwindClear`, `fins` and `acts` are computed
frame by frame; the finalisers a cancel fires are the context's finalisers, and a context no frame
of which stops a raise holds no action.  Forwarding is structural.  The instance's other frames
are its own. -/
def KontLaws : Prop :=
  (∀ t, S.plug S.hole t = t) ∧
  (∀ K₁ K₂ t, S.plug (S.kcomp K₁ K₂) t = S.plug K₁ (S.plug K₂ t)) ∧
  (∀ N M, S.plug (S.bindF N) M = S.bind M N) ∧
  (∀ l H t, S.plug (S.handleF l H) t = S.handle l H t) ∧
  (∀ N D M, S.plug (S.thenF N D) M = S.thenT M N D) ∧
  (∀ M, S.plug S.driveF M = S.drive M) ∧
  (∀ m, S.catches S.hole m = false) ∧ (∀ N m, S.catches (S.bindF N) m = false) ∧
  (∀ V m, S.catches (S.appF V) m = false) ∧
  (∀ l H m, S.catches (S.handleF l H) m = true ↔ m = l) ∧
  (∀ N D m, S.catches (S.thenF N D) m = false) ∧ (∀ m, S.catches S.driveF m = false) ∧
  (∀ K₁ K₂ m, S.catches (S.kcomp K₁ K₂) m = (S.catches K₁ m || S.catches K₂ m)) ∧
  S.unwindClear S.hole ∧ (∀ N, S.unwindClear (S.bindF N)) ∧ (∀ V, S.unwindClear (S.appF V)) ∧
  (∀ l H, S.unwindClear (S.handleF l H)) ∧ (∀ N D, ¬ S.unwindClear (S.thenF N D)) ∧
  S.unwindClear S.driveF ∧
  (∀ K₁ K₂, S.unwindClear (S.kcomp K₁ K₂) ↔ S.unwindClear K₁ ∧ S.unwindClear K₂) ∧
  S.fins S.hole = [] ∧ (∀ N, S.fins (S.bindF N) = []) ∧ (∀ V, S.fins (S.appF V) = []) ∧
  (∀ l H, S.fins (S.handleF l H) = []) ∧ (∀ N D, S.fins (S.thenF N D) = [D]) ∧
  S.fins S.driveF = [] ∧
  (∀ K₁ K₂, S.fins (S.kcomp K₁ K₂) = S.fins K₂ ++ S.fins K₁) ∧
  (∀ K, S.unwindClear K → S.fins K = []) ∧
  S.acts S.hole = [] ∧ (∀ N, S.acts (S.bindF N) = []) ∧ (∀ V, S.acts (S.appF V) = []) ∧
  (∀ l H, S.acts (S.handleF l H) = []) ∧ (∀ N D, S.acts (S.thenF N D) = [.fire D]) ∧
  S.acts S.driveF = [] ∧
  (∀ K₁ K₂, S.acts (S.kcomp K₁ K₂) = S.acts K₂ ++ S.acts K₁) ∧
  (∀ K, S.unwindClear K → S.acts K = []) ∧
  (∀ K, (S.acts K).filterMap Act.fire? = S.fins K)

/-- `c` arises from a typed closed program, under a runner that keeps its protocol.  The laws that
assert a step (`AppLaw`, `LoopLaws`, `DriveLaws`, and S4's `HandlerSem`) are about such
configurations: A's values include variables (`var`), and a calculus steps on closed values only,
as the literature's reduction rules are stated for closed terms. -/
def Live (c : S.Conf) : Prop :=
  ∃ (P : S.Term) (C : S.CTy) (R : S.Runner) (s : R.St),
    R.Respects ∧ S.der [] P C ∧ S.RReach R (S.rinit R P) (c, s)

/-- An application reaches its function's evaluation position by administrative steps: `M V` is
`□ V` around `M` after them.  (Our instance's `[app]` takes a variable argument, so its `M V` binds
`V` first.) -/
def AppLaw : Prop :=
  ∀ c M V, S.Live (S.setT c (S.app M V)) →
    S.PureSteps (S.setT c (S.app M V)) (S.setT c (S.plug (S.appF V) M))

/-- A step of a term is its step in every context (Yoshioka `E_Eval`), the driver's frame
included.  The driver's own steps are excepted: they act on a whole program only. -/
def Congr : Prop :=
  ∀ c t ev c' K, ev ≠ .top → S.step (S.setT c t) ev c' →
    S.step (S.setT c (S.plug K t)) ev (S.setT c' (S.plug K (S.term c')))

/-- The machine never answers an operation: io comes from the runner only. -/
def NoIO : Prop := ∀ c l i v w c', ¬ S.step c (.io l i v w) c'

/-- An operation no handler catches takes no step; nor does a raise no frame stops. -/
def OpStuck : Prop :=
  (∀ c K l i v, S.term c = S.plug K (S.perform l i v) → S.catches K l = false →
     ∀ ev c', ¬ S.step c ev c') ∧
  (∀ c K l i v, S.term c = S.plug K (S.raise l i v) → S.catches K l = false → S.unwindClear K →
     ∀ ev c', ¬ S.step c ev c')

/-- Answers are told apart: `ret` and the data formers are injective, `inl` and `inr` disjoint,
and a term stopped at an operation, or being driven, is no answer. -/
def DataInj : Prop :=
  Function.Injective S.ret ∧ (∀ a b a' b', S.pair a b = S.pair a' b' → a = a' ∧ b = b') ∧
  Function.Injective S.inl ∧ Function.Injective S.inr ∧ (∀ a b, S.inl a ≠ S.inr b) ∧
  (∀ a b, S.unitV ≠ S.pair a b) ∧ (∀ a, S.unitV ≠ S.inl a ∧ S.unitV ≠ S.inr a) ∧
  (∀ a b c, S.pair a b ≠ S.inl c ∧ S.pair a b ≠ S.inr c) ∧
  (∀ K l i v w, S.plug K (S.perform l i v) ≠ S.ret w ∧ S.plug K (S.raise l i v) ≠ S.ret w) ∧
  (∀ M w, S.drive M ≠ S.ret w)

/-- **A loop value's observations** (decision 35; SPEC §14: "`next` in the first loop observes
it").  `next (unfold A B f g s)` runs `f s` under a context that catches nothing and holds no
finaliser, and answers `inl a` when `f s` does, and `inr (unfold f g s')` when `f s` answers
`inr s'`.  `close` runs `g s` the same way and answers what it answers. -/
def LoopLaws : Prop :=
  (∀ c A B f g s, S.Live (S.setT c (S.next (S.unfold A B f g s))) →
   ∃ K', (∀ m, S.catches K' m = false) ∧ S.unwindClear K' ∧
     S.PureSteps (S.setT c (S.next (S.unfold A B f g s)))
       (S.setT c (S.plug K' (S.app (S.force f) s))) ∧
     (∀ a, S.Live (S.setT c (S.plug K' (S.ret (S.inl a)))) →
        S.PureSteps (S.setT c (S.plug K' (S.ret (S.inl a)))) (S.setT c (S.ret (S.inl a)))) ∧
     (∀ s', S.Live (S.setT c (S.plug K' (S.ret (S.inr s')))) →
        S.PureSteps (S.setT c (S.plug K' (S.ret (S.inr s'))))
          (S.setT c (S.ret (S.inr (S.unfold A B f g s')))))) ∧
  (∀ c A B f g s, S.Live (S.setT c (S.close (S.unfold A B f g s))) →
   ∃ K', (∀ m, S.catches K' m = false) ∧ S.unwindClear K' ∧
     S.PureSteps (S.setT c (S.close (S.unfold A B f g s)))
       (S.setT c (S.plug K' (S.app (S.force g) s))) ∧
     ∀ v, S.Live (S.setT c (S.plug K' (S.ret v))) →
       S.PureSteps (S.setT c (S.plug K' (S.ret v))) (S.setT c (S.ret v)))

/-- **The driver** ("the runtime drives `main` forever"): `drive M` runs `M` (that is `Congr` at
`driveF`); at `inr l` it drives `next l`, at `inl a` it answers `a`.  Each of those transitions is
one `top` step and the only step there, and the driver's are the only `top` steps. -/
def DriveLaws : Prop :=
  (∀ c l ev c', S.Live c → S.term c = S.drive (S.ret (S.inr l)) →
     (S.step c ev c' ↔ ev = .top ∧ c' = S.setT c (S.drive (S.next l)))) ∧
  (∀ c a ev c', S.Live c → S.term c = S.drive (S.ret (S.inl a)) →
     (S.step c ev c' ↔ ev = .top ∧ c' = S.setT c (S.ret a))) ∧
  (∀ c c', S.step c .top c' → ∃ v, S.term c = S.drive (S.ret v))

/-- **S0**: the shape of the machine. -/
def MachShape : Prop :=
  S.ConfLaws ∧ S.KontLaws ∧ S.AppLaw ∧ S.Congr ∧ S.NoIO ∧ S.OpStuck ∧ S.DataInj ∧ S.LoopLaws ∧
    S.DriveLaws

/-- **The let law** (CBPV's `[let]` at a returned value), in every context: a closed value typed
at `A` and a body typed with `A` in front give the let. -/
def LetLaw : Prop :=
  ∀ Γ V A N C, S.derV [] V A → S.der (A :: Γ) N C → S.der Γ (S.bind (S.ret V) N) C

end EffectSystem

end Targets.A
