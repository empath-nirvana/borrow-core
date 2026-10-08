import Targets.A.Machine

/-!
# System A — the soundness properties S1–S6 (RESTRUCTURE §1.5)

Each is an **(S)** property: an upper bound, saying that nothing goes wrong.  A system that types
nothing meets every one; the lower bounds are the (E) properties (`Targets/A/Expressiveness.lean`).

* **S1** (`RowAlgebra`): the rows form a safe effect algebra over one signature object (Kammar:
  "annotation effects can be identified with the effect operations"), and typing is closed under
  its subeffecting at well-formed target rows (Yoshioka's `[sub]`, whose premise `Γ ⊢ ε₂ : Eff`
  `SubClosed` carries).  Yoshioka's Def. 7.1 (masking) and Def. 7.6 (erasure with type-argument
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
  "v_cont = λz.handle_l S E[z] with h".  A continuation may own a cell of the store (OQ-50 (b),
  decision S6; the one-shot continuation object of Affect §3.1): the catch then allocates one fresh
  cell and hands `κ` at it, and `κ`'s resume and an affine `κ`'s cancel release it, each law
  otherwise store-keeping (`JoinAcross`).  A continuation with no cell is `capture l H K`, a value
  computed from the handler and the context.  `HandlerSemNoCell` is S4 with no cell, every
  continuation `capture l H K`; at an instance with no cells the two agree (`handlerSem_iff_noCell`).
* **S5** (`Cancellation FR`): SPEC §19 as built (decision 62): a cancel is not interceptable, fires
  the frozen finalisers innermost first, keeps the first error outside the region, suppresses the
  region's own, and re-raises the kept error at the canceller; an unwind fires each finaliser in
  place, a finaliser's raise superseding the pending one.  Its set of endings is parameterised by
  `FR`, the labels whose raises a finaliser may let escape (decision D3); the target reads it at
  `noFinRaise`, option A, where a finaliser handles its raises itself.  Each statement carries the
  no-interception condition explicitly (decision D4, `FinRow`): the finalisers that fire are closed
  computations typed at a row of abortive operations of `FR`'s labels.  Each reads a run
  prefix-closed, as a safety property is read (Alpern–Schneider): every run from the start is a
  prefix of a trace, that is, some continuation of it, itself a run, follows the trace.  So a run
  may stop anywhere, inside a fire step's administrative steps (the steps that start the fired
  finaliser, at our instance the β-step of `D ()`) among other places, and every step it takes is a
  trace's.  Ahman–Bauer Thm 7 and Voigt–Schuster–Brachthäuser Thm 3.6 are possible proof routes,
  not the statements' shape.
* **S6** (`ContUseEv`): Tang et al. Thm 3.6 ("tagged linear values are not duplicated or discarded
  during evaluation"); Affect ("continuations corresponding to one-shot effects are resumed at most
  once").  A use of a continuation is a step that applies it to a data value (decision D4: a
  clause's direct application of `κ` counts, and the instance's `resume` and `cancel` apply it).
  Per capture event, on complete runs (decision S6): the continuation a catch hands is read off the
  run, and on every complete run at a data answer each continuation a capture event hands is used
  exactly as often as it was handed, a linear one never cancelled.  `ContUse` is D4's form, which
  counts catches at `capture` and uses of every value.
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

/-- Subeffecting is a typing rule: what the algebra's `<` relates, the typing relates, at a
well-formed target row.  Yoshioka's `[sub]` carries the premise `Γ ⊢ ε₂ : Eff`; `der` has no
row-variable context, so the premise is that `ε₂` is well formed under some row variables in scope.
This gives Def. 5.1 (1) its teeth: an algebra with `(l)↑ < 0` would type an unhandled operation at
`0`, which is well formed (`unit_wf`). -/
def SubClosed : Prop :=
  ∀ Γ e ε₁ ε₂ A, S.der Γ e (S.F ε₁ A) → S.EA.Sub ε₁ ε₂ → (∃ Δ, S.EA.WF Δ ε₂) →
    S.der Γ e (S.F ε₂ A)

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

/-- **A common reduct across one change of store**: `c` reaches it by steps that keep the store
but one, which leaves the store of `c'`; at the store of `c'` the term `t` reaches it by steps that
keep the store.  At `c' = withCell c ℓ` the one step allocates the cell `ℓ`; at
`c = withCell c' ℓ` it releases it. -/
def JoinAcross (c c' : S.Conf) (t : S.Term) : Prop :=
  ∃ c₁ ev t₂ d, S.PureSteps c c₁ ∧ S.step c₁ ev (S.setT c' t₂) ∧ S.PureSteps (S.setT c' t₂) d ∧
    S.PureSteps (S.setT c' t) d

/-- The return law: "return V handled with … to x : A. N(x) = N(V)". -/
def RetLaw : Prop :=
  ∀ c K₀ l r cs v, S.Live c → S.term c = S.plug K₀ (S.handle l (S.hnd r cs) (S.ret v)) →
    S.PureJoin c (S.setT c (S.plug K₀ (S.app (S.force r) v)))

/-- **The catch law**: a resuming operation caught, the clause gets the argument and `κ`.  Either
`κ` is `capture l H K` and the store is kept, or `κ` owns a cell: the store gains one fresh cell
`ℓ`, holding the unit value, and `κ` is the continuation at `ℓ` — the one-shot continuation object
of Affect §3.1 and of SPEC §25 (decision S6).  Each side is otherwise store-keeping. -/
def CatchLaw : Prop :=
  ∀ c K₀ l r cs K i v (o : OpSig S.Ty) cl,
    S.Live c → S.term c = S.plug K₀ (S.handle l (S.hnd r cs) (S.plug K (S.perform l i v))) →
    S.catches K l = false → (S.sig l)[i]? = some o → o.cls ≠ .abortive → cs[i]? = some cl →
    S.PureJoin c (S.setT c (S.plug K₀ (S.app (S.force cl) (S.pair v (S.capture l (S.hnd r cs) K))))) ∨
    ∃ ℓ, S.cellFree c ℓ ∧ S.JoinAcross c (S.withCell c ℓ)
      (S.plug K₀ (S.app (S.force cl) (S.pair v (S.captureAt o.cls l (S.hnd r cs) K ℓ))))

/-- The catch law with no cell: the clause gets the argument and `capture l H K`, and the store is
kept. -/
def CatchKeep : Prop :=
  ∀ c K₀ l r cs K i v (o : OpSig S.Ty) cl,
    S.Live c → S.term c = S.plug K₀ (S.handle l (S.hnd r cs) (S.plug K (S.perform l i v))) →
    S.catches K l = false → (S.sig l)[i]? = some o → o.cls ≠ .abortive → cs[i]? = some cl →
    S.PureJoin c (S.setT c (S.plug K₀ (S.app (S.force cl) (S.pair v (S.capture l (S.hnd r cs) K)))))

/-- An abortive operation caught: the clause gets the argument only, and `κ` is never reified. -/
def AbortLaw : Prop :=
  ∀ c K₀ l r cs K i v (o : OpSig S.Ty) cl,
    S.Live c → S.term c = S.plug K₀ (S.handle l (S.hnd r cs) (S.plug K (S.raise l i v))) →
    S.catches K l = false → S.unwindClear K → (S.sig l)[i]? = some o → o.cls = .abortive →
    cs[i]? = some cl → S.PureJoin c (S.setT c (S.plug K₀ (S.app (S.force cl) v)))

/-- Deep resume: resuming `κ` runs the frozen context under the same handler again (Yoshioka's
"v_cont = λz.handle_l S E[z] with h"). -/
def ResumeLaw : Prop :=
  ∀ c K₀ l H K w, S.Live c → S.term c = S.plug K₀ (S.resume (S.capture l H K) w) →
    S.PureJoin c (S.setT c (S.plug K₀ (S.handle l H (S.plug K (S.ret w)))))

/-- Deep resume at a cell: resuming `κ` at its cell `ℓ`, in a store that holds `ℓ`, releases `ℓ`
and runs the frozen context under the same handler again. -/
def ResumeCellLaw : Prop :=
  ∀ c K₀ k l H K ℓ w, S.cellFree c ℓ → S.Live (S.withCell c ℓ) →
    S.term (S.withCell c ℓ) = S.plug K₀ (S.resume (S.captureAt k l H K ℓ) w) →
    S.JoinAcross (S.withCell c ℓ) c (S.plug K₀ (S.handle l H (S.plug K (S.ret w))))

/-- Cancel starts `κ`'s cancel run, in the canceller's context. -/
def CancelLaw : Prop :=
  ∀ c K₀ l H K, S.Live c → S.term c = S.plug K₀ (S.cancel (S.capture l H K)) →
    S.PureJoin c (S.setT c (S.plug K₀ (S.cancelOf l H K)))

/-- Cancel at a cell: cancelling an affine `κ` at its cell `ℓ`, in a store that holds `ℓ`, releases
`ℓ` and starts `κ`'s cancel run.  (A linear `κ` is never cancelled; S6.) -/
def CancelCellLaw : Prop :=
  ∀ c K₀ l H K ℓ, S.cellFree c ℓ → S.Live (S.withCell c ℓ) →
    S.term (S.withCell c ℓ) = S.plug K₀ (S.cancel (S.captureAt .affine l H K ℓ)) →
    S.JoinAcross (S.withCell c ℓ) c (S.plug K₀ (S.cancelOf l H K))

/-- A finaliser frame whose body returned continues with `N`. -/
def ThenLaw : Prop :=
  ∀ c K₀ v N D, S.Live c → S.term c = S.plug K₀ (S.thenT (S.ret v) N D) →
    S.PureJoin c (S.setT c (S.plug K₀ (S.bind (S.ret v) N)))

/-- An unwind that reaches a finaliser frame fires the finaliser and runs it where the frame was,
inside a context `Kp` of the instance's that catches nothing; once it returns `()`, the raise goes
on (SPEC [finalise]). -/
def FinLaw : Prop :=
  ∀ c K₀ N D K m j w, S.Live c → S.term c = S.plug K₀ (S.thenT (S.plug K (S.raise m j w)) N D) →
    S.catches K m = false → S.unwindClear K →
    ∃ c₁ Kp, S.step c (.fire D) c₁ ∧ (∀ m', S.catches Kp m' = false) ∧ S.unwindClear Kp ∧
      S.PureSteps c₁ (S.setT c (S.plug (S.kcomp K₀ Kp) D)) ∧
      S.PureSteps (S.setT c (S.plug (S.kcomp K₀ Kp) (S.ret S.unitV)))
        (S.setT c (S.plug K₀ (S.raise m j w)))

/-- **S4.** -/
def HandlerSem : Prop :=
  S.RetLaw ∧ S.CatchLaw ∧ S.AbortLaw ∧ S.ResumeLaw ∧ S.ResumeCellLaw ∧ S.CancelLaw ∧
    S.CancelCellLaw ∧ S.ThenLaw ∧ S.FinLaw

/-- **S4 with no cell**: every catch hands `capture l H K` and keeps the store.  At an instance with
no cells it is S4 (`handlerSem_iff_noCell`); at ours it fails at `J₁`, where the catch of a linear or
affine operation allocates `κ`'s cell (`Targets/Instance/HandlerCell.lean`). -/
def HandlerSemNoCell : Prop :=
  S.RetLaw ∧ S.CatchKeep ∧ S.AbortLaw ∧ S.ResumeLaw ∧ S.CancelLaw ∧ S.ThenLaw ∧ S.FinLaw

/-- The catch law with no cell gives the catch law. -/
theorem catchLaw_of_keep (h : S.CatchKeep) : S.CatchLaw :=
  fun c K₀ l r cs K i v o cl hl ht hK hs ho hc => .inl (h c K₀ l r cs K i v o cl hl ht hK hs ho hc)

/-- **At an instance with no cells, S4 is S4 with no cell**: the catch law's cell alternative
needs a cell, and the laws at a cell are about none.  So every refutation of S4 with no cell at
such an instance refutes S4. -/
theorem handlerSem_iff_noCell (hC : IsEmpty S.Cell) : S.HandlerSem ↔ S.HandlerSemNoCell := by
  constructor
  · rintro ⟨h1, h2, h3, h4, -, h6, -, h8, h9⟩
    refine ⟨h1, fun c K₀ l r cs K i v o cl hl ht hK hs ho hc => ?_, h3, h4, h6, h8, h9⟩
    rcases h2 c K₀ l r cs K i v o cl hl ht hK hs ho hc with h | ⟨ℓ, -⟩
    · exact h
    · exact hC.elim ℓ
  · rintro ⟨h1, h2, h3, h4, h6, h8, h9⟩
    exact ⟨h1, S.catchLaw_of_keep h2, h3, h4, fun _ _ _ _ _ _ ℓ => hC.elim ℓ, h6,
      fun _ _ _ _ _ ℓ => hC.elim ℓ, h8, h9⟩

/-- A refutation of S4 with no cell, at an instance with no cells, refutes S4. -/
theorem not_handlerSem_of_noCell (hC : IsEmpty S.Cell) (h : ¬ S.HandlerSemNoCell) :
    ¬ S.HandlerSem :=
  fun h' => h ((S.handlerSem_iff_noCell hC).1 h')

/-! ### S5: cancellation, as built (SPEC §19; decision 62) -/

/-- **Option A** (decision D3): a finaliser lets no raise escape; its raises are handled inside
it.  The set of labels whose raises a finaliser may let escape is `S5`'s parameter, and this is
the empty instance, which the target reads.  OQ-7 (finalisers that resume, or clean up
asynchronously) is a separate question. -/
def noFinRaise : S.EA.Lab → Prop := fun _ => False

/-- **The no-interception condition** (SPEC §19: "its handlers are dying, so they catch
nothing"; decision D4 makes it explicit): the finaliser `D` is a closed computation typed at a row
whose operations are abortive operations of labels in `FR`.  A finaliser performs no resuming
operation, so nothing it does is caught by a handler of the region a cancel tears down; at
`noFinRaise` it is typed at the pure row. -/
def FinRow (FR : S.EA.Lab → Prop) (D : S.Term) : Prop :=
  ∃ ε, (∀ l i, S.has ε l i → FR l ∧ ∃ o : OpSig S.Ty, (S.sig l)[i]? = some o ∧ o.cls = .abortive) ∧
    S.der [] D (S.F ε S.UnitT)

/-- A finaliser's end that `FR` allows: it returned, or a raise of a label in `FR` escaped it. -/
def FinEnd (FR : S.EA.Lab → Prop) : Option (S.EA.Lab × ℕ × S.Val) → Prop
  | none => True
  | some (m, _, _) => FR m

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
so far.  Each finaliser fires, innermost first: the fire step, the administrative steps that start
the finaliser (`q₀`), then its run alone to an end `FR` allows, which updates the kept error.  Last,
the canceller is answered, and after the answer anything may follow.  A trace stops before a fire
step or the answer (`stop`) and while a finaliser runs alone (`FinTrace.running`); S5 reads a run
as a prefix of a trace (`NoIntercept`), so a run may stop anywhere. -/
inductive CancelTrace (R : S.Runner) (FR N : S.EA.Lab → Prop) (K₀ : S.Kont) :
    S.RConf R → List S.Term → S.Err → List (S.Event × S.RConf R) → Prop
  | stop {c : S.RConf R} {fs : List S.Term} {err : S.Err} : CancelTrace R FR N K₀ c fs err []
  | answer {c c' : S.RConf R} {err : S.Err} {q : List (S.Event × S.RConf R)} :
      S.RStep R c .tau c' → S.Answered K₀ err (S.term c'.1) →
      CancelTrace R FR N K₀ c [] err ((.tau, c') :: q)
  | fire {c c₁ c₂ : S.RConf R} {D : S.Term} {fs : List S.Term} {err : S.Err} {Kf : S.Kont}
      {q₀ q : List (S.Event × S.RConf R)} :
      S.RStep R c (.fire D) c₁ → S.PurePath R c₁ q₀ c₂ → S.term c₂.1 = S.plug Kf D →
      FinTrace R FR N K₀ Kf c₂ fs err q →
      CancelTrace R FR N K₀ c (D :: fs) err ((.fire D, c₁) :: q₀ ++ q)
/-- A cancel trace while a finaliser runs alone in `Kf`. -/
inductive FinTrace (R : S.Runner) (FR N : S.EA.Lab → Prop) (K₀ : S.Kont) :
    S.Kont → S.RConf R → List S.Term → S.Err → List (S.Event × S.RConf R) → Prop
  | running {Kf : S.Kont} {c : S.RConf R} {fs : List S.Term} {err : S.Err}
      {q : List (S.Event × S.RConf R)} {c' : S.RConf R} :
      S.Alone R Kf c q c' → FinTrace R FR N K₀ Kf c fs err q
  | ended {Kf : S.Kont} {c : S.RConf R} {fs : List S.Term} {err : S.Err}
      {q : List (S.Event × S.RConf R)} {c' : S.RConf R} {r : S.Err} {c'' : S.RConf R}
      {q' : List (S.Event × S.RConf R)} :
      S.Alone R Kf c q c' → S.Ended Kf c' r → S.FinEnd FR r →
      S.RStep R c' (.finEnd r) c'' → CancelTrace R FR N K₀ c'' fs (S.keep N err r) q' →
      FinTrace R FR N K₀ Kf c fs err (q ++ (.finEnd r, c'') :: q')
end

/-- **Not interceptable, in order, with the error policy**: every run of a typed program from the
start of a cancel of `capture l H K`, whose finalisers meet the no-interception condition, is a
prefix of a cancel trace of `fins K` with nothing kept: some continuation of it, itself a run,
follows the trace. -/
def NoIntercept (FR : S.EA.Lab → Prop) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ (c₀ c : S.RConf R) K₀ l H K q, S.RReach R (S.rinit R e) c₀ →
      S.term c₀.1 = S.plug K₀ (S.cancel (S.capture l H K)) →
      S.PureSteps c₀.1 c.1 → c.2 = c₀.2 → S.term c.1 = S.plug K₀ (S.cancelOf l H K) →
      (∀ D ∈ S.fins K, S.FinRow FR D) →
      S.RPath R c q → ∃ q', S.RPath R c (q ++ q') ∧
        S.CancelTrace R FR (S.Region l K) K₀ c (S.fins K) none (q ++ q')

/-- The frames of `K` that stop a raise are handler frames and finaliser frames. -/
inductive Std : S.Kont → Prop
  | clear {K : S.Kont} : S.unwindClear K → Std K
  | frame {K₁ K₂ F : S.Kont} : S.unwindClear K₁ →
      ((∃ l H, F = S.handleF l H) ∨ (∃ N D, F = S.thenF N D)) →
      Std K₂ → Std (S.kcomp K₂ (S.kcomp F K₁))

mutual
/-- **An unwind trace**: a raise is pending under `K`, inside the fixed context `K₀`, and the first
frame of `K` that stops it decides.  If that frame is a handler of its label, the trace ends there
(S4's abortive law says what follows).  If it is a finaliser frame, its finaliser fires: the fire
step, the administrative steps that start the finaliser (`q₀`), then its run alone.  If the
finaliser returns, the pending raise goes on through the rest of `K`.  If a raise of a label in
`FR` escapes the finaliser, that raise supersedes the pending one.  Once the pending raise has left
`K`, the trace is over.  A trace stops before a fire step (`stop`) and while a finaliser runs alone
(`PendTrace.running`); S5 reads a run as a prefix of a trace (`UnwindOrder`), so a run may stop
anywhere. -/
inductive UnwindTrace (R : S.Runner) (FR : S.EA.Lab → Prop) (K₀ : S.Kont) :
    S.RConf R → S.Kont → List (S.Event × S.RConf R) → Prop
  | stop {c : S.RConf R} {K : S.Kont} : UnwindTrace R FR K₀ c K []
  | out {c : S.RConf R} {K : S.Kont} {m : S.EA.Lab} {j : ℕ} {w : S.Val}
      {q : List (S.Event × S.RConf R)} :
      S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.catches K m = false →
      S.unwindClear K → UnwindTrace R FR K₀ c K q
  | caught {c : S.RConf R} {K K₁ K₂ : S.Kont} {H : S.Hnd} {m : S.EA.Lab} {j : ℕ} {w : S.Val}
      {q : List (S.Event × S.RConf R)} :
      K = S.kcomp K₂ (S.kcomp (S.handleF m H) K₁) → S.catches K₁ m = false →
      S.unwindClear K₁ → S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) →
      UnwindTrace R FR K₀ c K q
  | fire {c c₁ c₂ : S.RConf R} {K K₁ K₂ : S.Kont} {N D : S.Term} {Kp : S.Kont} {m : S.EA.Lab}
      {j : ℕ} {w : S.Val} {q₀ q : List (S.Event × S.RConf R)} :
      K = S.kcomp K₂ (S.kcomp (S.thenF N D) K₁) →
      S.catches K₁ m = false → S.unwindClear K₁ → S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) →
      S.RStep R c (.fire D) c₁ → S.PurePath R c₁ q₀ c₂ → (∀ m', S.catches Kp m' = false) →
      S.unwindClear Kp →
      S.term c₂.1 = S.plug (S.kcomp (S.kcomp K₀ K₂) Kp) D → PendTrace R FR K₀ K₂ Kp (m, j, w) c₂ q →
      UnwindTrace R FR K₀ c K ((.fire D, c₁) :: q₀ ++ q)
/-- An unwind trace while a finaliser runs, the raise `p` pending. -/
inductive PendTrace (R : S.Runner) (FR : S.EA.Lab → Prop) (K₀ : S.Kont) :
    S.Kont → S.Kont → S.EA.Lab × ℕ × S.Val → S.RConf R → List (S.Event × S.RConf R) → Prop
  | running {K₂ Kp : S.Kont} {p : S.EA.Lab × ℕ × S.Val} {c : S.RConf R}
      {q : List (S.Event × S.RConf R)} {c' : S.RConf R} :
      S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' → PendTrace R FR K₀ K₂ Kp p c q
  | returned {K₂ Kp : S.Kont} {p : S.EA.Lab × ℕ × S.Val} {c : S.RConf R}
      {q : List (S.Event × S.RConf R)} {c' : S.RConf R}
      {q₁ : List (S.Event × S.RConf R)} {c'' : S.RConf R} {q₂ : List (S.Event × S.RConf R)} :
      S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' →
      S.Ended (S.kcomp (S.kcomp K₀ K₂) Kp) c' none → S.PurePath R c' q₁ c'' →
      S.term c''.1 = S.plug K₀ (S.plug K₂ (S.raise p.1 p.2.1 p.2.2)) →
      UnwindTrace R FR K₀ c'' K₂ q₂ → PendTrace R FR K₀ K₂ Kp p c (q ++ q₁ ++ q₂)
  | superseded {K₂ Kp : S.Kont} {p : S.EA.Lab × ℕ × S.Val} {c : S.RConf R}
      {q : List (S.Event × S.RConf R)} {c' : S.RConf R} {K' : S.Kont}
      {m' : S.EA.Lab} {j' : ℕ} {w' : S.Val} {q₂ : List (S.Event × S.RConf R)} :
      S.Alone R (S.kcomp (S.kcomp K₀ K₂) Kp) c q c' →
      S.term c'.1 = S.plug (S.kcomp (S.kcomp K₀ K₂) Kp) (S.plug K' (S.raise m' j' w')) →
      S.catches K' m' = false → S.unwindClear K' → FR m' →
      UnwindTrace R FR K₀ c' (S.kcomp K₂ (S.kcomp Kp K')) q₂ →
      PendTrace R FR K₀ K₂ Kp p c (q ++ q₂)
end

/-- **The unwind**, in order, with supersession, through frames whose finalisers meet the
no-interception condition: every run from the raise is a prefix of an unwind trace. -/
def UnwindOrder (FR : S.EA.Lab → Prop) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ (c : S.RConf R) K₀ K m j w q, S.RReach R (S.rinit R e) c → S.Std K →
      S.term c.1 = S.plug K₀ (S.plug K (S.raise m j w)) → S.catches K m = false →
      (∀ D ∈ S.fins K, S.FinRow FR D) →
      S.RPath R c q → ∃ q', S.RPath R c (q ++ q') ∧ S.UnwindTrace R FR K₀ c K (q ++ q')

/-- **S5**, its endings parameterised by what a finaliser may raise (decision D3). -/
def Cancellation (FR : S.EA.Lab → Prop) : Prop := S.NoIntercept FR ∧ S.UnwindOrder FR

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

/-- Step `j` uses `κ`: it applies `κ` to a data value at the evaluation position.  The instance's
`resume` and `cancel` apply `κ` (ours: `resume κ w` binds `w` and applies `κ` to `inl ()`, and
`cancel κ` is `κ (inr ())`), and so does a clause that applies `κ` itself, as Core's clauses do
(decision D4: a direct application of `κ` counts as a use). -/
def UseAt {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R)) (j : ℕ) (κ : S.Val) :
    Prop :=
  j < q.length ∧ ∃ K₀ w T, S.DataVal T w ∧
    S.term (S.cfgAt c₀ q j).1 = S.plug K₀ (S.plug (S.appF w) (S.force κ))

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
/-- The cancels of `κ` along `q`. -/
noncomputable def cancels {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  (List.range q.length).countP (fun j => decide (S.CancelAt c₀ q j κ))

open Classical in
/-- The uses of `κ` along `q`: the steps that apply it. -/
noncomputable def uses {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  (List.range q.length).countP (fun j => decide (S.UseAt c₀ q j κ))

/-- The catches of `κ`. -/
noncomputable def caught {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  S.caughtLin c₀ q κ + S.caughtAff c₀ q κ

/-- **S6, read at `capture`** (decision D4's form).  A catch is counted at `capture l H K`, and a
use is any application of a value to a data value.  Two things make it the wrong reading: a
machine whose catch gives `κ` a resource of its own hands a `κ` that no function of the handler and
the context names (our instance's capture cell, SPEC §25); and every application of a value that is
not a continuation, a handler's return clause at a data answer among them, counts as a use of a
value never caught.  `ContUseEv` is S6. -/
def ContUse : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) →
    ∀ q, S.RPath R (S.rinit R e) q → ∀ κ,
      S.uses (S.rinit R e) q κ ≤ S.caught (S.rinit R e) q κ ∧
      S.cancels (S.rinit R e) q κ ≤ S.caughtAff (S.rinit R e) q κ ∧
      (S.DataTy A → S.IsVal (S.lastC (S.rinit R e) q).1 →
        S.uses (S.rinit R e) q κ = S.caught (S.rinit R e) q κ)

/-! ### S6 per capture event (the user's decision S6, 2026-10-08) -/

/-- **A capture event**: step `j` of the path `q` from `c₀` catches a resuming operation of class
`k`, the clause `cl`, and `κ` is the continuation the catch hands the clause, read off the run: at
the first configuration after step `j` whose term is the clause applied to the operation's argument
and a value, `κ` is that value.  The hand-off is an application (`appF` of the pair is a frame), so
no open junk matches it. -/
def CatchEvAt {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R)) (j : ℕ) (κ : S.Val)
    (k : OpClass) : Prop :=
  j < q.length ∧ ∃ K₀ l r cs K i v, ∃ o : OpSig S.Ty, ∃ cl,
    S.term (S.cfgAt c₀ q j).1 = S.plug K₀ (S.handle l (S.hnd r cs) (S.plug K (S.perform l i v))) ∧
    S.catches K l = false ∧ (S.sig l)[i]? = some o ∧ o.cls = k ∧ k ≠ .abortive ∧ cs[i]? = some cl ∧
    S.appF (S.pair v κ) ≠ S.hole ∧
    ∃ j', j < j' ∧ j' ≤ q.length ∧
      S.term (S.cfgAt c₀ q j').1 = S.plug K₀ (S.plug (S.appF (S.pair v κ)) (S.force cl)) ∧
      ∀ j'' κ', j < j'' → j'' < j' → S.appF (S.pair v κ') ≠ S.hole →
        S.term (S.cfgAt c₀ q j'').1 ≠ S.plug K₀ (S.plug (S.appF (S.pair v κ')) (S.force cl))

open Classical in
/-- The capture events handing `κ` at a linear operation along `q`. -/
noncomputable def caughtEvLin {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  (List.range q.length).countP (fun j => decide (S.CatchEvAt c₀ q j κ .linear))

open Classical in
/-- The capture events handing `κ` at an affine operation along `q`. -/
noncomputable def caughtEvAff {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  (List.range q.length).countP (fun j => decide (S.CatchEvAt c₀ q j κ .affine))

/-- The capture events handing `κ`. -/
noncomputable def caughtEv {R : S.Runner} (c₀ : S.RConf R) (q : List (S.Event × S.RConf R))
    (κ : S.Val) : ℕ :=
  S.caughtEvLin c₀ q κ + S.caughtEvAff c₀ q κ

/-- **S6, per capture event, on complete runs** (decision S6).  On every complete run of a typed
program at a data answer, each continuation a capture event hands is used exactly as often as it
was handed (a use is a step that applies it to a data value, decision D4), and cancelled no more
often than an affine event handed it: a linear one is never cancelled.  Counts are per
continuation value, over the values capture events hand. -/
def ContUseEv : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ e ε A, S.Answers R ε → S.der [] e (S.F ε A) → S.DataTy A →
    ∀ q, S.CompleteFrom R (S.rinit R e) q → ∀ κ, (∃ j k, S.CatchEvAt (S.rinit R e) q j κ k) →
      S.uses (S.rinit R e) q κ = S.caughtEv (S.rinit R e) q κ ∧
      S.cancels (S.rinit R e) q κ ≤ S.caughtEvAff (S.rinit R e) q κ

/-! ### The (S) properties together -/

/-- **The soundness properties of A**, S5 at option A (`noFinRaise`, decision D3), S6 per capture
event (decision S6). -/
def SProps : Prop :=
  S.MachShape ∧ S.LetLaw ∧ S.RowAlgebra ∧ S.DataDiv ∧ S.Safety ∧ S.EffSafe ∧ S.HandlerSem ∧
    S.Cancellation S.noFinRaise ∧ S.ContUseEv

/-- `SProps` without S6 (OPEN at our instance): the restricted tier-1 reduction's A conjunct. -/
def SPropsNoUse : Prop :=
  S.MachShape ∧ S.LetLaw ∧ S.RowAlgebra ∧ S.DataDiv ∧ S.Safety ∧ S.EffSafe ∧ S.HandlerSem ∧
    S.Cancellation S.noFinRaise

end EffectSystem

end Targets.A
