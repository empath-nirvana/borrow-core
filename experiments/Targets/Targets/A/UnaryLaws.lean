import Targets.A.Binary

/-!
# System A — the unary laws beside done: tail-resumption, algebraicity, η (stated, not proved)

The P11 chapter lists the tail-resumptive law, algebraicity and η among the unary laws of handler
correctness.  S4 (`HandlerSem`) has none of the three: its conjuncts are reductions up to
store-keeping steps (`PureJoin`, form F.1 of the P11/I5 menu), and the two sides of each of these
laws are not joinable in general (the tail-resumptive clause runs outside `K` on one side and inside
it on the other; η relates a handler to no handler).  Their only statements were binary: A₂'s
`HandlerLaws` (tail, algebraicity) and Core's `Laws` (`LawTail`, `LawAlg`, `CapEta`).

Here each is stated **unary, at the run level** (the menu's F.3): at a configuration that a typed
closed program reaches under a runner that keeps its protocol, with the law's left side in the
evaluation context `K₀`, the complete runs from that configuration and from the same configuration
with the right side in `K₀` have the same answers and observable traces.  Each side is read only
through its own runs; there is no context quantifier beyond the evaluation context and no binary
relation.  As A₂'s `Observes`, this reads complete runs only.

* `TailLaw`: Xie, Brachthäuser, Hillerström, Schuster & Leijen, *Effect Handlers, Evidently*
  (ICFP 2020) §6.2, a clause `λx k. k e` with `k ∉ fv(e)` run in place ("since f has already
  captured its evidence w, it can still perform operations itself"); Kammar–Lindley–Oury's
  handle.op with a clause that resumes in tail position.  Its hygiene is explicit hypotheses.
* `AlgLaw`: Plotkin–Power algebraicity in Core `LawAlg`'s form, graded by continuation class as
  `LawAlg` is (resuming operations only).
* `EtaHold`, `EtaLin`: effects TR §13 T13.8, `handleAt x with Fwd_x in M ≡ M`, at the same label
  (P13.10 refutes the fresh-label form).  `EtaHold` writes the clause at an affine operation with a
  frame that holds the continuation (D13.7); `EtaLin` is the typing-restricted alternative
  (L13.5).

`UnaryLaws` bundles `TailLaw`, `AlgLaw` and `EtaHold`.  It is **beside done**, not a conjunct of S4
or of done: whether these laws belong in done is a menu choice (P11/I5 menu axes H, F and K), for
the user.

`not_tailLaw_toy`, `not_algLaw_toy`, `not_etaHold_toy` and `not_etaLin_toy` show that each fails at
an instance (`toy`) whose handler or bind ignores its clauses.
-/

namespace Targets.A

namespace EffectSystem

variable (S : EffectSystem)

/-! ### Runs from a configuration -/

/-- A complete run from `c` answers `v` with the observable trace `tr`. -/
def ObsFrom (R : S.Runner) (c : S.RConf R) (v : S.Val) (tr : List S.Event) : Prop :=
  ∃ q, S.CompleteFrom R c q ∧ S.term (S.lastC c q).1 = S.ret v ∧ S.obs q = tr

/-- **`t₁` and `t₂` run alike in every evaluation context**: under every runner that keeps its
protocol, at every configuration a typed closed program reaches whose term is `t₁` in `K₀`, the
complete runs from it and from the same configuration with `t₂` in `K₀` show the same answers and
traces. -/
def RunsAlike (t₁ t₂ : S.Term) : Prop :=
  ∀ R : S.Runner, R.Respects → ∀ (P : S.Term) (C : S.CTy) (c : S.RConf R) (K₀ : S.Kont),
    S.der [] P C → S.RReach R (S.rinit R P) c → S.term c.1 = S.plug K₀ t₁ →
    ∀ v tr, S.ObsFrom R c v tr ↔ S.ObsFrom R (S.setR c (S.plug K₀ t₂)) v tr

/-! ### The tail-resumptive law -/

/-- **The tail-resumptive law, unary.**  A resuming operation `i` of `l` whose clause is
`tailCl c` (`λ(a, k). c a to b. k.resume b`) runs `c v` in place:
`handle l H (K[perform l i v])` runs as `handle l H (K[c v])`.

Xie et al. §6.2: "almost all important effects are tail-resumptive"; the clause runs with the
handler's evidence, so its operations go where the handler's would.  The hygiene condition is three
hypotheses, over the row `εc` at which `c v` is typed (the operations of `c v` are those its row
admits):
* **not caught by `K`**: no label `εc` admits is caught by a frame of `K` (on the left `c v` runs
  outside `K`, on the right inside it);
* **not caught by the handler**: `εc` does not admit `l`.  At our instance this is what `[handle]`'s
  premise appears to supply, read with the clause typed at the outer row (SPEC §19: "`n` not in
  `Σ`"); that reading is not checked here;
* **no finaliser between**: `K` holds no finaliser, or every operation `εc` admits is linear.  On
  the left a raise or a cancel from `c v` passes no frame of `K`, on the right it passes all of
  them; a linear operation is never cancelled and is not a raise.

A₂'s conjunct and Core's `LawTail` carry only `catches K l = false` (the handler catches the
operation); the first and third hypotheses are not in either. -/
def TailLaw : Prop :=
  ∀ l r cs K i v (o : OpSig S.Ty) c εc B,
    S.catches K l = false → (S.sig l)[i]? = some o → o.cls ≠ .abortive →
    cs[i]? = some (S.tailCl c) →
    S.der [] (S.app (S.force c) v) (S.F εc B) →
    (∀ m j, S.has εc m j → S.catches K m = false) →
    S.Lacks εc l →
    (S.unwindClear K ∨ ∀ m j (o' : OpSig S.Ty), S.has εc m j → (S.sig m)[j]? = some o' →
       o'.cls = .linear) →
    S.RunsAlike (S.handle l (S.hnd r cs) (S.plug K (S.perform l i v)))
      (S.handle l (S.hnd r cs) (S.plug K (S.app (S.force c) v)))

/-! ### Algebraicity -/

/-- **Algebraicity, unary, graded by continuation class**: a resuming operation commutes with the
`let` it is sequenced in, `(op v to x. M) to y. N` runs as `op v to x. (M to y. N)`.  Plotkin–Power
algebraicity; the grading is Core `LawAlg`'s (`o.abort = false`, `o.q ≠ .unr`).  A has no `unr`
class, so the grading here is `o.cls ≠ .abortive`.  The abortive case is S4's: a raise passes bind
frames (`unwindClear`, `KontLaws`), and the frames it does not pass are finaliser frames, whose
laws are S4's finaliser conjuncts.  `N` is written under the binder of `x`, which it does not
mention, as A₂ writes it. -/
def AlgLaw : Prop :=
  ∀ l i v (o : OpSig S.Ty) M N, (S.sig l)[i]? = some o → o.cls ≠ .abortive →
    S.RunsAlike (S.bind (S.bind (S.perform l i v) M) N) (S.bind (S.perform l i v) (S.bind M N))

/-! ### η: the forwarding handler -/

/-- The forwarding handler's return clause, `λz. ret z`. -/
def retCl : S.Val := S.lam (S.ret (S.var 0))

/-- `λ(a, k). perform l i a to y. k.resume y`: TR D13.4's clause `op x.o(p; y. resume k y)`.  The
clause runs outside the handler's frame, so its `perform l` reaches the next handler of `l`
outward. -/
def fwdCl (l : S.EA.Lab) (i : ℕ) : S.Val :=
  S.lam (S.split (S.var 0) (S.bind (S.perform l i (S.var 1)) (S.resume (S.var 1) (S.var 0))))

/-- `λ(a, k). perform l i a then y. k.resume y unwind k.cancel`: TR D13.7's
`(op x.o(p; y. ret y)) to^k y. resume k y`, a frame that holds `k` and cancels it when unwound,
written with A's finaliser former. -/
def holdCl (l : S.EA.Lab) (i : ℕ) : S.Val :=
  S.lam (S.split (S.var 0)
    (S.thenT (S.perform l i (S.var 1)) (S.resume (S.var 1) (S.var 0)) (S.cancel (S.var 0))))

/-- `λa. raise l i a`: TR D13.4's abortive clause `ab x.a(p)`. -/
def abCl (l : S.EA.Lab) (i : ℕ) : S.Val := S.lam (S.raise l i (S.var 0))

/-- The forwarding clause of operation `i` at its class; `hold` selects D13.7's clause at an affine
operation. -/
def fwdClause (hold : Bool) (l : S.EA.Lab) (i : ℕ) (o : OpSig S.Ty) : S.Val :=
  match o.cls with
  | .abortive => S.abCl l i
  | .linear => S.fwdCl l i
  | .affine => if hold then S.holdCl l i else S.fwdCl l i

/-- `Fwd_l`: TR D13.4's forwarding handler, a clause for each operation of `l`. -/
def fwdH (hold : Bool) (l : S.EA.Lab) : S.Hnd :=
  S.hnd S.retCl ((S.sig l).mapIdx (fun i o => S.fwdClause hold l i o))

/-- **η, unary, with a frame that holds the continuation**: the forwarding handler, its affine
clauses written with D13.7's frame, runs as no handler.  TR T13.8 (b): "the clause at each `o` with
`W ∈ q_o` is written with D13.7 … This holds for every `M`"; (a) linear and (c) abortive operations
use D13.4's clauses.  The plain clause at an affine operation loses the frozen finalisers when an
outer handler cancels (TR P13.6; EffModelRel `etaAff_leaks`); the held `k`'s cancel runs them.
Whether an instance types `holdCl` (it uses `k` in both the continuation and the finaliser) is the
instance's: D13.7's rule [to-hold] is the typing that would.  At an instance that types no
`fwdH true l` for an affine `l`, no configuration of the law arises there, and the law says what
`EtaLin` says (`etaLin_of_etaHold`). -/
def EtaHold : Prop :=
  ∀ l M, S.RunsAlike (S.handle l (S.fwdH true l) M) M

/-- **η, unary, under a typing restriction** (the alternative to `EtaHold`): at a label with no
affine operation, D13.4's forwarding handler runs as no handler.  TR L13.5: `Fwd_x` "types when
every resuming operation of `E` is linear and `E` has no abortive operation" and "never types when
some resuming `o` has `W ∈ q_o` and `C ∉ q_o`"; its remark: a premise at `q_o` would type it at the
linear operations of an effect that also has abortive ones, which T13.8 (c) covers.  The hypothesis
here is that semantic condition, no affine operation.  T13.8 (a)'s second hypothesis (each
operation crosses no `using` or `lend` frame) is not carried: its counterexample P13.9 needs an
unhandled operation whose stack unwinds, and A's runs do not unwind an unhandled operation
(`OpStuck`, `RStep.io`).  Whether the run-level law needs it is not checked. -/
def EtaLin : Prop :=
  ∀ l M, (∀ o ∈ S.sig l, o.cls ≠ .affine) → S.RunsAlike (S.handle l (S.fwdH false l) M) M

/-! ### The bundle -/

/-- **The unary laws, beside done**: STATED, not proved, at no instance.  Not a conjunct of S4 or of
done; membership is a menu choice (P11/I5 menu axes H, F and K). -/
def UnaryLaws : Prop := S.TailLaw ∧ S.AlgLaw ∧ S.EtaHold

/-- The two forwarding handlers agree at a label with no affine operation. -/
theorem fwdH_hold_eq {l : S.EA.Lab} (h : ∀ o ∈ S.sig l, o.cls ≠ .affine) :
    S.fwdH true l = S.fwdH false l := by
  unfold fwdH
  congr 1
  apply List.ext_getElem (by simp)
  intro n h₁ h₂
  simp only [List.getElem_mapIdx]
  have ho := h _ (List.getElem_mem (by simpa using h₁))
  unfold fwdClause
  split <;> simp_all

/-- `EtaHold` gives `EtaLin`. -/
theorem etaLin_of_etaHold (h : S.EtaHold) : S.EtaLin := fun l M hl => by
  rw [← S.fwdH_hold_eq hl]
  exact h l M

end EffectSystem

/-! ### Non-vacuity: an instance whose handler or bind ignores its clauses -/

/-- One label, one linear operation; nothing steps; a term is `true` (stopped) or `false`
(returned).  `perform` and `raise` are `true`, `ret`, `app` and `force` are `false`, contexts plug
as the identity and catch nothing.  `handle` is `hd` of its body and `bind` is `bd`.  A witness that
each law can fail, and nothing more: `toy` is not claimed to meet S0–S6. -/
def toy (hd : Bool → Bool) (bd : Bool → Bool → Bool) : EffectSystem where
  EA := ⟨Unit, Unit, Unit, fun _ _ => True, fun _ _ => True, fun _ _ => some (), (), fun _ => (),
    fun _ _ => True, fun _ _ _ => ()⟩
  Ty := Unit
  CTy := Unit
  sig := fun _ => [⟨(), (), .linear⟩]
  has := fun _ _ _ => False
  UnitT := ()
  ZeroT := ()
  Tensor := fun _ _ => ()
  Sum := fun _ _ => ()
  F := fun _ _ => ()
  DivFree := fun _ => True
  Val := Unit
  Term := Bool
  Hnd := Unit
  Kont := Unit
  Conf := Bool
  var := fun _ => ()
  unitV := ()
  pair := fun _ _ => ()
  inl := fun _ => ()
  inr := fun _ => ()
  lam := fun _ => ()
  force := fun _ => false
  app := fun _ _ => false
  ret := fun _ => false
  bind := bd
  split := fun _ _ => false
  case := fun _ _ _ => false
  perform := fun _ _ _ => true
  raise := fun _ _ _ => true
  hnd := fun _ _ => ()
  handle := fun _ _ M => hd M
  resume := fun _ _ => false
  cancel := fun _ => false
  thenT := fun _ _ _ => false
  unfold := fun _ _ _ _ _ => ()
  next := fun _ => false
  close := fun _ => false
  drive := fun _ => false
  hole := ()
  kcomp := fun _ _ => ()
  bindF := fun _ => ()
  appF := fun _ => ()
  handleF := fun _ _ => ()
  thenF := fun _ _ => ()
  driveF := ()
  plug := fun _ t => t
  catches := fun _ _ => false
  unwindClear := fun _ => True
  fins := fun _ => []
  capture := fun _ _ _ => ()
  cancelOf := fun _ _ _ => false
  init := id
  term := id
  setT := fun _ t => t
  step := fun _ _ _ => False
  derV := fun _ _ _ => True
  der := fun _ _ _ => True

namespace EffectSystem

variable {hd : Bool → Bool} {bd : Bool → Bool → Bool}

/-- At `toy`, the returned configuration completes with no event. -/
theorem toy_obs_false : (toy hd bd).ObsFrom (toy hd bd).R₀ (false, ()) () [] :=
  ⟨[], ⟨.nil, ⟨⟨(), rfl⟩, fun _ _ h => h⟩⟩, rfl, rfl⟩

/-- At `toy`, the stopped configuration has no complete run. -/
theorem toy_not_obs_true (v : Unit) (tr : List (toy hd bd).Event) :
    ¬ (toy hd bd).ObsFrom (toy hd bd).R₀ (true, ()) v tr := by
  rintro ⟨q, ⟨hp, hv⟩, -, -⟩
  cases hp with
  | nil => obtain ⟨⟨_, h⟩, -⟩ := hv; cases h
  | cons hs _ =>
      cases hs with
      | mach h => exact h
      | io _ _ ha _ => exact ha

theorem toy_r₀_respects : (toy hd bd).R₀.Respects := fun _ _ _ h => h.elim

/-- `RunsAlike` fails at `toy` when the left side is stopped and the right side returned. -/
theorem toy_not_runsAlike {t₁ t₂ : Bool} (h₁ : t₁ = true) (h₂ : t₂ = false) :
    ¬ (toy hd bd).RunsAlike t₁ t₂ := fun h => by
  subst h₁ h₂
  have := (h (toy hd bd).R₀ toy_r₀_respects true () (true, ()) () trivial
    Relation.ReflTransGen.refl rfl () []).2 toy_obs_false
  exact toy_not_obs_true () [] this

/-- **The tail-resumptive law is not trivially true**: it fails where `handle` ignores its clauses
(`hd = id`), with the hygiene hypotheses met. -/
theorem not_tailLaw_toy : ¬ (toy id bd).TailLaw := fun h =>
  toy_not_runsAlike rfl rfl (h () () [(toy id bd).tailCl ()] () 0 () ⟨(), (), .linear⟩ () () ()
    rfl rfl (fun h => nomatch h) rfl trivial (fun _ _ h => h.elim) (fun _ h => h) (Or.inl trivial))

/-- **Algebraicity is not trivially true**: it fails where `bind` does not associate with
`perform` (`bd M _ = !M`). -/
theorem not_algLaw_toy : ¬ (toy hd (fun M _ => !M)).AlgLaw := fun h =>
  toy_not_runsAlike rfl rfl (h () 0 () ⟨(), (), .linear⟩ false false rfl (fun h => nomatch h))

/-- **η with a holding frame is not trivially true**: it fails where `handle` never returns
(`hd = fun _ => true`). -/
theorem not_etaHold_toy : ¬ (toy (fun _ => true) bd).EtaHold := fun h =>
  toy_not_runsAlike rfl rfl (h () false)

/-- **η under the typing restriction is not trivially true**: the same instance, whose one
operation is linear. -/
theorem not_etaLin_toy : ¬ (toy (fun _ => true) bd).EtaLin := fun h =>
  toy_not_runsAlike rfl rfl (h () false (fun o ho => by
    simp only [toy] at ho; rw [List.mem_singleton.mp ho]; exact fun h => nomatch h))

end EffectSystem

end Targets.A
