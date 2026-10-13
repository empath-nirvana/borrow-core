import Targets.A.Machine

/-!
# System A — the soundness properties S1–S6 (RESTRUCTURE §1.5)

Each is an **(S)** property: an upper bound, saying that nothing goes wrong.  A system that types
nothing meets every one; the lower bounds are the (E) properties (`Targets/A/Expressiveness.lean`).

* **S1** (`RowAlgebra`): the rows form a safe effect algebra over one signature object (Kammar:
  "annotation effects can be identified with the effect operations"), and typing is closed under
  its subeffecting.  Yoshioka's Def. 7.1 (masking) and Def. 7.6 (erasure with type-argument
  dispatch) apply only to instances with masking or with labels whose type arguments dispatch.
* **S2** (`Safety`): Bauer–Pretnar Thm 4.1, Cor. 4.2 ("A terminating computation of type A ! ∆
  returns a value of type A, or calls an operation in ∆"); Affect Thm 2.1; [CONF] 415:18.  Under
  every platform that keeps its protocol, at every row it answers.  Termination is claimed at the
  div-free types; `DataDiv` makes the pure row's data answers div-free (decision 35: "code without
  [div] is total"), which is weaker than decision 35 at other rows (RESTRUCTURE §1.5, §7 Q3).
* **S3** (`EffSafe`): Yoshioka Lemma 5.7, Thm 5.8; Bauer–Pretnar Cor. 4.2; Tang Thm 3.2.  At the
  pure row `RowSig` makes `StopsIn` empty, so no operation goes unhandled; `K` ranges over every
  context, the driver's frame included.
* **S4** (`HandlerSem`): Plotkin–Pretnar's equations as reductions, in every context `K₀`, up to
  steps that change no store (`PureJoin`), at the configurations typed closed programs reach
  (`Live`).  With no equations in signatures (OQ-22), "If the
  effect theory is empty, then any handler is correct" (after Def. 4.5), so handler correctness is
  exactly these equations.  The deep-resume conjunct is Yoshioka's
  "v_cont = λz.handle_l S E[z] with h".  S4 states Core's continuation as built (`capture` a
  value, the catch, resume and cancel laws store-keeping), which excludes OQ-50 (b) (§7 Q9).
* **S5** (`Cancellation`): SPEC §19 as built (decision 62): a cancel is not interceptable, fires
  the frozen finalisers innermost first, keeps the first error outside the region, suppresses the
  region's own, and re-raises the kept error at the canceller; an unwind fires each finaliser in
  place, a finaliser's raise superseding the pending one.  Ahman–Bauer Thm 7 and
  Voigt–Schuster–Brachthäuser Thm 3.6 are possible proof routes, not the statements' shape.
* **S6** (`ContUse`): Tang et al. Thm 3.6 ("tagged linear values are not duplicated or discarded
  during evaluation"); Affect ("continuations corresponding to one-shot effects are resumed at most
  once").  On every run no continuation is used more often than it was caught, and one caught at
  a linear operation is never cancelled; on every complete run at a data answer each is used
  exactly as often as it was caught.
-/

namespace Targets.A

namespace EffectSystem

variable (S : EffectSystem)

/-! ### S1: the row algebra (T0) -/

/-- **One signature object**: `(l)↑` admits exactly `sig l`'s operations, `⊙` unions, `0` admits
nothing, `∼` preserves what is admitted, substitution adds the substituted row's operations and
nothing else, and no signature is empty. -/
def RowSig : Prop :=
  (∀ l m i, S.has (S.EA.lift l) m i ↔ m = l ∧ i < (S.sig l).length) ∧
  (∀ l i, ¬ S.has S.EA.unit l i) ∧
  (∀ ε₁ ε₂ ε l i, S.EA.comp ε₁ ε₂ = some ε → (S.has ε l i ↔ S.has ε₁ l i ∨ S.has ε₂ l i)) ∧
  (∀ ε₁ ε₂ l i, S.EA.eqv ε₁ ε₂ → (S.has ε₁ l i ↔ S.has ε₂ l i)) ∧
  (∀ α ε' ε l i, S.has ε l i → S.has (S.EA.subst α ε' ε) l i) ∧
  (∀ α ε' ε l i, S.has (S.EA.subst α ε' ε) l i → S.has ε l i ∨ S.has ε' l i) ∧
  (∀ l, S.sig l ≠ [])

/-- Subeffecting is a typing rule: what the algebra's `<` relates, the typing relates.  This gives
Def. 5.1 (1) its teeth: an algebra with `(l)↑ < 0` would type an unhandled operation at `0`. -/
def SubClosed : Prop :=
  ∀ Γ e ε₁ ε₂ A, S.der Γ e (S.F ε₁ A) → S.EA.Sub ε₁ ε₂ → S.der Γ e (S.F ε₂ A)

/-- **S1.** -/
def RowAlgebra : Prop := S.EA.Laws ∧ S.EA.Safe ∧ S.RowSig ∧ S.SubClosed

/-! ### S2: safety, and termination where claimed -/

/-- Every program at a data answer on the pure row is claimed to terminate (decision 35: "code
without [div] is total").  The instance may claim more. -/
def DataDiv : Prop := ∀ A, S.DataTy A → S.DivFree (S.F S.EA.unit A)

/-- **S2.**  Under every platform that keeps its protocol, at every row it answers: a program at a
data answer has every run never stuck, terminates where the type is div-free, and every complete
run ends at a value of the answer type; a driven program whose current step answers `A ⊕ L`, `A`
data, has every run never stuck, and every complete run ends at a value of `A`. -/
def Safety : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ ε, S.Answers R ε →
    (∀ e A, S.DataTy A → S.der [] e (S.F ε A) →
       S.SafeRuns R e ∧ (S.DivFree (S.F ε A) → S.Terminates R e) ∧
       ∀ q, S.CompleteFrom R (S.rinit R e) q →
         ∃ v, S.term (S.lastC (S.rinit R e) q).1 = S.ret v ∧ S.DataVal A v) ∧
    (∀ M A L, S.DataTy A → S.der [] (S.drive M) (S.F ε (S.Sum A L)) →
       S.SafeRuns R (S.drive M) ∧
       ∀ q, S.CompleteFrom R (S.rinit R (S.drive M)) q →
         ∃ a, S.term (S.lastC (S.rinit R (S.drive M)) q).1 = S.ret a ∧ S.DataVal A a)

/-! ### S3: effect safety -/

/-- Stopped at an operation of the row: a resuming `perform` no handler catches, or an abortive
`raise` no frame stops. -/
def StopsIn (ε : S.EA.Eff) (c : S.Conf) : Prop :=
  ∃ K l i v o, (S.sig l)[i]? = some o ∧ S.has ε l i ∧ S.catches K l = false ∧
    ((S.term c = S.plug K (S.perform l i v) ∧ o.cls ≠ .abortive) ∨
     (S.term c = S.plug K (S.raise l i v) ∧ o.cls = .abortive ∧ S.unwindClear K))

/-- **S3.** -/
def EffSafe : Prop :=
  ∀ e ε A, S.der [] e (S.F ε A) → ∀ c, S.Reach (S.init e) c →
    S.IsVal c ∨ (∃ ev c', S.step c ev c') ∨ S.StopsIn ε c

/-! ### S4: the handler laws, unary -/

/-- **S4.** -/
def HandlerSem : Prop :=
  -- return: "return V handled with … to x : A. N(x) = N(V)"
  (∀ c K₀ l r cs v, S.Live c → S.term c = S.plug K₀ (S.handle l (S.hnd r cs) (S.ret v)) →
     S.PureJoin c (S.setT c (S.plug K₀ (S.app (S.force r) v)))) ∧
  -- a resuming operation caught: the clause gets the argument and κ
  (∀ c K₀ l r cs K i v (o : OpSig S.Ty) cl,
     S.Live c → S.term c = S.plug K₀ (S.handle l (S.hnd r cs) (S.plug K (S.perform l i v))) →
     S.catches K l = false → (S.sig l)[i]? = some o → o.cls ≠ .abortive → cs[i]? = some cl →
     S.PureJoin c (S.setT c (S.plug K₀ (S.app (S.force cl) (S.pair v (S.capture l (S.hnd r cs) K)))))) ∧
  -- an abortive operation caught: the clause gets the argument only, and κ is never reified
  (∀ c K₀ l r cs K i v (o : OpSig S.Ty) cl,
     S.Live c → S.term c = S.plug K₀ (S.handle l (S.hnd r cs) (S.plug K (S.raise l i v))) →
     S.catches K l = false → S.unwindClear K → (S.sig l)[i]? = some o → o.cls = .abortive →
     cs[i]? = some cl → S.PureJoin c (S.setT c (S.plug K₀ (S.app (S.force cl) v)))) ∧
  -- deep resume: resuming κ runs the frozen context under the same handler again
  (∀ c K₀ l H K w, S.Live c → S.term c = S.plug K₀ (S.resume (S.capture l H K) w) →
     S.PureJoin c (S.setT c (S.plug K₀ (S.handle l H (S.plug K (S.ret w)))))) ∧
  -- cancel starts κ's cancel run, in the canceller's context
  (∀ c K₀ l H K, S.Live c → S.term c = S.plug K₀ (S.cancel (S.capture l H K)) →
     S.PureJoin c (S.setT c (S.plug K₀ (S.cancelOf l H K)))) ∧
  -- a finaliser frame whose body returned continues with `N`
  (∀ c K₀ v N D, S.Live c → S.term c = S.plug K₀ (S.thenT (S.ret v) N D) →
     S.PureJoin c (S.setT c (S.plug K₀ (S.bind (S.ret v) N)))) ∧
  -- an unwind that reaches a finaliser frame fires the finaliser and runs it where the frame was,
  -- inside a context `Kp` of the instance's that catches nothing; once it returns `()`, the raise
  -- goes on (SPEC [finalise])
  (∀ c K₀ N D K m j w, S.Live c → S.term c = S.plug K₀ (S.thenT (S.plug K (S.raise m j w)) N D) →
     S.catches K m = false → S.unwindClear K →
     ∃ c₁ Kp, S.step c (.fire D) c₁ ∧ (∀ m', S.catches Kp m' = false) ∧ S.unwindClear Kp ∧
       S.PureSteps c₁ (S.setT c (S.plug (S.kcomp K₀ Kp) D)) ∧
       S.PureSteps (S.setT c (S.plug (S.kcomp K₀ Kp) (S.ret S.unitV)))
         (S.setT c (S.plug K₀ (S.raise m j w))))

/-! ### S5: cancellation, as built (SPEC §19; decision 62) -/

/-- An error a cancel keeps: a raise's label, operation and argument. -/
abbrev Err : Type := Option (S.EA.Lab × ℕ × S.Val)

open Classical in
/-- [cfin-raise]: "err′ = err if err ≠ none; none if m ∈ N; (m, v) otherwise". -/
noncomputable def keep (N : S.EA.Lab → Prop) : S.Err → S.Err → S.Err
  | some e, _ => some e
  | none, none => none
  | none, some (m, j, w) => if N m then none else some (m, j, w)

/-- The region a cancel of `capture l H K` tears down: `l` and every label a handler frame of `K`
catches. -/
def Region (l : S.EA.Lab) (K : S.Kont) (m : S.EA.Lab) : Prop := m = l ∨ S.catches K m = true

/-- The canceller is answered ([cancel], [cancel-raise]): `()`, or the kept error raised at it. -/
def Answered (K₀ : S.Kont) : S.Err → S.Term → Prop
  | none, t => t = S.plug K₀ (S.ret S.unitV)
  | some (m, j, w), t => t = S.plug K₀ (S.raise m j w)

/-- Along `q` from `c`, the term inside the context `Kf` runs alone. -/
inductive Alone (R : S.Runner) (Kf : S.Kont) :
    S.RConf R → List (S.Event × S.RConf R) → S.RConf R → Prop
  | nil {c : S.RConf R} : Alone R Kf c [] c
  | cons {c : S.RConf R} {ev : S.Event} {c' : S.RConf R} {t t' : S.Term}
      {q : List (S.Event × S.RConf R)} {c'' : S.RConf R} :
      S.term c.1 = S.plug Kf t → S.term c'.1 = S.plug Kf t' →
      S.RStep R c ev c' → S.RStep R (S.setR c t) ev (S.setR c' t') → Alone R Kf c' q c'' →
      Alone R Kf c ((ev, c') :: q) c''

/-- At `c` the term inside `Kf` has ended: it returned, or a raise escaped it. -/
def Ended {R : S.Runner} (Kf : S.Kont) (c : S.RConf R) : S.Err → Prop
  | none => ∃ v, S.term c.1 = S.plug Kf (S.ret v)
  | some (m, j, w) => ∃ K, S.term c.1 = S.plug Kf (S.plug K (S.raise m j w)) ∧
      S.catches K m = false ∧ S.unwindClear K

mutual
/-- **A cancel trace**: `fs` are the frozen finalisers not yet fired, and `err` is the error kept
so far.  Each finaliser fires, innermost first, then runs alone to its end, and its end updates the
kept error.  Last, the canceller is answered.  A trace may stop anywhere, and after the answer
anything may follow. -/
inductive CancelTrace (R : S.Runner) (N : S.EA.Lab → Prop) (K₀ : S.Kont) :
    S.RConf R → List S.Term → S.Err → List (S.Event × S.RConf R) → Prop
  | stop {c : S.RConf R} {fs : List S.Term} {err : S.Err} : CancelTrace R N K₀ c fs err []
  | answer {c c' : S.RConf R} {err : S.Err} {q : List (S.Event × S.RConf R)} :
      S.RStep R c .tau c' → S.Answered K₀ err (S.term c'.1) →
      CancelTrace R N K₀ c [] err ((.tau, c') :: q)
  | fire {c c₁ c₂ : S.RConf R} {D : S.Term} {fs : List S.Term} {err : S.Err} {Kf : S.Kont}
      {q₀ q : List (S.Event × S.RConf R)} :
      S.RStep R c (.fire D) c₁ → S.PurePath R c₁ q₀ c₂ → S.term c₂.1 = S.plug Kf D →
      FinTrace R N K₀ Kf c₂ fs err q → CancelTrace R N K₀ c (D :: fs) err ((.fire D, c₁) :: q₀ ++ q)
/-- A cancel trace while a finaliser runs alone in `Kf`. -/
inductive FinTrace (R : S.Runner) (N : S.EA.Lab → Prop) (K₀ : S.Kont) :
    S.Kont → S.RConf R → List S.Term → S.Err → List (S.Event × S.RConf R) → Prop
  | running {Kf : S.Kont} {c : S.RConf R} {fs : List S.Term} {err : S.Err}
      {q : List (S.Event × S.RConf R)} {c' : S.RConf R} :
      S.Alone R Kf c q c' → FinTrace R N K₀ Kf c fs err q
  | ended {Kf : S.Kont} {c : S.RConf R} {fs : List S.Term} {err : S.Err}
      {q : List (S.Event × S.RConf R)} {c' : S.RConf R} {r : S.Err} {c'' : S.RConf R}
      {q' : List (S.Event × S.RConf R)} :
      S.Alone R Kf c q c' → S.Ended Kf c' r →
      S.RStep R c' (.finEnd r) c'' → CancelTrace R N K₀ c'' fs (S.keep N err r) q' →
      FinTrace R N K₀ Kf c fs err (q ++ (.finEnd r, c'') :: q')
end

/-- **Not interceptable, in order, with the error policy**: every run of a typed program from the
start of a cancel of `capture l H K` follows a cancel trace of `fins K` with nothing kept. -/
def NoIntercept : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ (c₀ c : S.RConf R) K₀ l H K q, S.RReach R (S.rinit R e) c₀ →
      S.term c₀.1 = S.plug K₀ (S.cancel (S.capture l H K)) →
      S.PureSteps c₀.1 c.1 → c.2 = c₀.2 → S.term c.1 = S.plug K₀ (S.cancelOf l H K) →
      S.RPath R c q → S.CancelTrace R (S.Region l K) K₀ c (S.fins K) none q

/-- The frames of `K` that stop a raise are handler frames and finaliser frames. -/
inductive Std : S.Kont → Prop
  | clear {K : S.Kont} : S.unwindClear K → Std K
  | frame {K₁ K₂ F : S.Kont} : S.unwindClear K₁ →
      ((∃ l H, F = S.handleF l H) ∨ (∃ N D, F = S.thenF N D)) →
      Std K₂ → Std (S.kcomp K₂ (S.kcomp F K₁))

mutual
/-- **An unwind trace**: a raise is pending under `K`, inside the fixed context `K₀`, and the first
frame of `K` that stops it decides.  If that frame is a handler of its label, the trace ends there
(S4's abortive law says what follows).  If it is a finaliser frame, its finaliser fires and runs
alone.  If the finaliser returns, the pending raise goes on through the rest of `K`.  If a raise
escapes the finaliser, that raise supersedes the pending one.  Once the pending raise has left
`K`, the trace is over. -/
inductive UnwindTrace (R : S.Runner) (K₀ : S.Kont) :
    S.RConf R → S.Kont → List (S.Event × S.RConf R) → Prop
  | stop {c : S.RConf R} {K : S.Kont} : UnwindTrace R K₀ c K []
  | out {c : S.RConf R} {K : S.Kont} {m : S.EA.Lab} {j : ℕ} {w : S.Val}
      {q : List (S.Event × S.RConf R)} :
      S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.catches K m = false →
      S.unwindClear K → UnwindTrace R K₀ c K q
  | caught {c : S.RConf R} {K K₁ K₂ : S.Kont} {H : S.Hnd} {m : S.EA.Lab} {j : ℕ} {w : S.Val}
      {q : List (S.Event × S.RConf R)} :
      K = S.kcomp K₂ (S.kcomp (S.handleF m H) K₁) → S.catches K₁ m = false →
      S.unwindClear K₁ → S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) →
      UnwindTrace R K₀ c K q
  | fire {c c₁ c₂ : S.RConf R} {K K₁ K₂ : S.Kont} {N D : S.Term} {Kp : S.Kont} {m : S.EA.Lab}
      {j : ℕ} {w : S.Val} {q₀ q : List (S.Event × S.RConf R)} :
      K = S.kcomp K₂ (S.kcomp (S.thenF N D) K₁) →
      S.catches K₁ m = false → S.unwindClear K₁ → S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) →
      S.RStep R c (.fire D) c₁ → S.PurePath R c₁ q₀ c₂ → (∀ m', S.catches Kp m' = false) →
      S.unwindClear Kp →
      S.term c₂.1 = S.plug (S.kcomp (S.kcomp K₀ K₂) Kp) D → PendTrace R K₀ K₂ Kp (m, j, w) c₂ q →
      UnwindTrace R K₀ c K ((.fire D, c₁) :: q₀ ++ q)
/-- An unwind trace while a finaliser runs, the raise `p` pending. -/
inductive PendTrace (R : S.Runner) (K₀ : S.Kont) :
    S.Kont → S.Kont → S.EA.Lab × ℕ × S.Val → S.RConf R → List (S.Event × S.RConf R) → Prop
  | running {K₂ Kp : S.Kont} {p : S.EA.Lab × ℕ × S.Val} {c : S.RConf R}
      {q : List (S.Event × S.RConf R)} {c' : S.RConf R} :
      S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' → PendTrace R K₀ K₂ Kp p c q
  | returned {K₂ Kp : S.Kont} {p : S.EA.Lab × ℕ × S.Val} {c : S.RConf R}
      {q : List (S.Event × S.RConf R)} {c' : S.RConf R}
      {q₁ : List (S.Event × S.RConf R)} {c'' : S.RConf R} {q₂ : List (S.Event × S.RConf R)} :
      S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' →
      S.Ended (S.kcomp (S.kcomp K₀ K₂) Kp) c' none → S.PurePath R c' q₁ c'' →
      S.term c''.1 = S.plug K₀ (S.plug K₂ (S.raise p.1 p.2.1 p.2.2)) → UnwindTrace R K₀ c'' K₂ q₂ →
      PendTrace R K₀ K₂ Kp p c (q ++ q₁ ++ q₂)
  | superseded {K₂ Kp : S.Kont} {p : S.EA.Lab × ℕ × S.Val} {c : S.RConf R}
      {q : List (S.Event × S.RConf R)} {c' : S.RConf R} {K' : S.Kont}
      {m' : S.EA.Lab} {j' : ℕ} {w' : S.Val} {q₂ : List (S.Event × S.RConf R)} :
      S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' →
      S.term c'.1 = S.plug (S.kcomp (S.kcomp K₀ K₂) Kp) (S.plug K' (S.raise m' j' w')) →
      S.catches K' m' = false → S.unwindClear K' →
      UnwindTrace R K₀ c' (S.kcomp K₂ (S.kcomp Kp K')) q₂ →
      PendTrace R K₀ K₂ Kp p c (q ++ q₂)
end

/-- **The unwind**, in order, with supersession. -/
def UnwindOrder : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ (c : S.RConf R) K₀ K m j w q, S.RReach R (S.rinit R e) c → S.Std K →
      S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.catches K m = false →
      S.RPath R c q → S.UnwindTrace R K₀ c K q

/-- **S5.** -/
def Cancellation : Prop := S.NoIntercept ∧ S.UnwindOrder

/-! ### S6: the linear and affine use of continuations -/

/-- Step `j` of the path `q` from `c₀` catches `κ` at an operation of class `k`: the configuration
before it is stopped at a resuming operation that a handler catches, and `κ` is the continuation
the catch hands its clause. -/
def CatchAt {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R)) (j : ℕ) (κ : S.Val)
    (k : OpClass) : Prop :=
  j < q.length ∧ ∃ K₀ l r cs K i v, ∃ o : OpSig S.Ty,
    S.term (S.cfgAt c₀ q j).1 = S.plug K₀ (S.handle l (S.hnd r cs) (S.plug K (S.perform l i v))) ∧
    S.catches K l = false ∧ (S.sig l)[i]? = some o ∧ o.cls = k ∧ k ≠ .abortive ∧
    κ = S.capture l (S.hnd r cs) K

/-- Step `j` resumes `κ`. -/
def ResumeAt {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R)) (j : ℕ) (κ : S.Val) :
    Prop :=
  j < q.length ∧ ∃ K₀ w, S.term (S.cfgAt c₀ q j).1 = S.plug K₀ (S.resume κ w)

/-- Step `j` cancels `κ`. -/
def CancelAt {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R)) (j : ℕ) (κ : S.Val) :
    Prop :=
  j < q.length ∧ ∃ K₀, S.term (S.cfgAt c₀ q j).1 = S.plug K₀ (S.cancel κ)

open Classical in
/-- The catches of `κ` at a linear operation along `q`. -/
noncomputable def caughtLin {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  (List.range q.length).countP (fun j => decide (S.CatchAt c₀ q j κ .linear))

open Classical in
/-- The catches of `κ` at an affine operation along `q`. -/
noncomputable def caughtAff {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  (List.range q.length).countP (fun j => decide (S.CatchAt c₀ q j κ .affine))

open Classical in
/-- The resumes of `κ` along `q`. -/
noncomputable def resumes {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  (List.range q.length).countP (fun j => decide (S.ResumeAt c₀ q j κ))

open Classical in
/-- The cancels of `κ` along `q`. -/
noncomputable def cancels {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  (List.range q.length).countP (fun j => decide (S.CancelAt c₀ q j κ))

/-- The uses of `κ`: resumes and cancels. -/
noncomputable def uses {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  S.resumes c₀ q κ + S.cancels c₀ q κ

/-- The catches of `κ`. -/
noncomputable def caught {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  S.caughtLin c₀ q κ + S.caughtAff c₀ q κ

/-- **S6.** -/
def ContUse : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ q, S.RPath R (S.rinit R e) q → ∀ κ,
      S.uses (S.rinit R e) q κ ≤ S.caught (S.rinit R e) q κ ∧
      S.cancels (S.rinit R e) q κ ≤ S.caughtAff (S.rinit R e) q κ ∧
      (S.DataTy A → S.IsVal (S.lastC (S.rinit R e) q).1 →
        S.uses (S.rinit R e) q κ = S.caught (S.rinit R e) q κ)

/-! ### The (S) properties together -/

/-- **The soundness properties of A.** -/
def SProps : Prop :=
  S.MachShape ∧ S.LetLaw ∧ S.RowAlgebra ∧ S.DataDiv ∧ S.Safety ∧ S.EffSafe ∧ S.HandlerSem ∧
    S.Cancellation ∧ S.ContUse

/-- `SProps` without `ContUse` (OPEN at our instance, §7 Q9): the restricted tier-1 reduction's
A conjunct. -/
def SPropsNoUse : Prop :=
  S.MachShape ∧ S.LetLaw ∧ S.RowAlgebra ∧ S.DataDiv ∧ S.Safety ∧ S.EffSafe ∧ S.HandlerSem ∧
    S.Cancellation

end EffectSystem

end Targets.A
