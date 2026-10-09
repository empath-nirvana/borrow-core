import Targets.A.EffAlg
import Mathlib.Data.List.Infix

/-!
# System A — an effect system, abstractly (RESTRUCTURE §1.3)

**An effect system** is any calculus with effects, read as call-by-push-value with an effect
index: a signature of operations with arities and a control class, rows over it (an effect algebra,
`EffAlg`), a typing judgement at a row closed under binding a value, handlers given by a return
clause and a clause per operation, continuations resumed or cancelled (a continuation may own a
cell of the store, which its use releases), a labelled small-step
semantics whose evaluation contexts include `□ to x. N` and `□ V`, and a platform (a runner,
Ahman–Bauer Def. 1) that answers the operations left at the top.

A has only the formers that its (S) properties and its (E) programs need.  On the type side that is
the data types of the answers and the returner `F_ε A`: A has no function type, thunk type,
continuation type, row binder or loop type, which are the instance's own.  The loop formers
(`unfold`, `next`, `close`, `drive`) are vocabulary for writing the loop programs: A has no loop
type and no typing rule for them, and `LoopLaws`/`DriveLaws` (`Targets/A/Machine.lean`) say only
what they do.  `unfold`, `next` and `close` are definable in any calculus with general recursion;
`drive` is the runtime's primitive driver (decision 35: "the runtime drives `main` forever"), and
A treats it as a context (`driveF`), so that every law stated in every context holds inside a
driven program.

Nothing here mentions BoLo or Core.  Our calculus is one instance (`Targets/Instance/Core.lean`).
-/

namespace Targets.A

/-- Never resumed (a raise); resumed exactly once; resumed or cancelled exactly once. -/
inductive OpClass
  | abortive
  | linear
  | affine
  deriving DecidableEq, Repr

/-- `op : A ↠ B` at a class.  Arities are value types: operations are algebraic (higher-order
operations: not now). -/
structure OpSig (Ty : Type) where
  arg : Ty
  ans : Ty
  cls : OpClass

/-- What a step shows.  `fire` and `finEnd` mark a finaliser's start and end (the cancellation
traces and the behaviours read them); `io` is the platform's answer, emitted only by the runner's
steps; `top` is a step of the runtime's driver, which acts only on a whole program. -/
inductive Ev (Lab Val Term : Type)
  | tau
  | fire (D : Term)
  | finEnd (r : Option (Lab × ℕ × Val))
  | io (l : Lab) (i : ℕ) (v w : Val)
  | top

/-- What a cancel meets at a frame of the region it tears down: a finaliser, which it fires; or a
running finaliser of an earlier cancel, whose continuation is the one being cancelled (a finaliser
performed an operation and its handler cancels it), holding the error that earlier cancel has kept
so far. -/
inductive Act (Lab Val Term : Type)
  | fire (D : Term)
  | pend (e : Option (Lab × ℕ × Val))

/-- The finaliser a cancel fires at an action, if it fires one. -/
def Act.fire? {Lab Val Term : Type} : Act Lab Val Term → Option Term
  | .fire D => some D
  | .pend _ => none

/-- **An effect system**: any calculus with effects, read as call-by-push-value with an effect
index. -/
structure EffectSystem where
  /-- Rows: an effect algebra over labels. -/
  EA      : EffAlg
  Ty      : Type
  CTy     : Type
  /-- The one signature object: each label's operations. -/
  sig     : EA.Lab → List (OpSig Ty)
  /-- The row admits operation `i` of label `l`. -/
  has     : EA.Eff → EA.Lab → ℕ → Prop
  UnitT   : Ty
  ZeroT   : Ty
  Tensor  : Ty → Ty → Ty
  Sum     : Ty → Ty → Ty
  /-- The returner at a row (Bauer–Pretnar's `A ! ∆`). -/
  F       : EA.Eff → Ty → CTy
  /-- The types whose programs the instance claims terminate. -/
  DivFree : CTy → Prop
  Val     : Type
  Term    : Type
  Hnd     : Type
  Kont    : Type
  Conf    : Type
  var     : ℕ → Val
  unitV   : Val
  pair    : Val → Val → Val
  inl     : Val → Val
  inr     : Val → Val
  /-- The thunk of `λx. M`. -/
  lam     : Term → Val
  force   : Val → Term
  /-- `M V`. -/
  app     : Term → Val → Term
  ret     : Val → Term
  /-- `M to x. N`. -/
  bind    : Term → Term → Term
  /-- `let (x, y) = V in M`. -/
  split   : Val → Term → Term
  case    : Val → Term → Term → Term
  perform : EA.Lab → ℕ → Val → Term
  raise   : EA.Lab → ℕ → Val → Term
  /-- A return clause, and a clause per operation. -/
  hnd     : Val → List Val → Hnd
  handle  : EA.Lab → Hnd → Term → Term
  resume  : Val → Val → Term
  cancel  : Val → Term
  /-- `M then x. N unwind D`. -/
  thenT   : Term → Term → Term → Term
  /-- `unfold A B f g s`: the loop that answers `A` when it finishes and `B` when closed; `next`
  runs `f s`, `close` runs `g s`.  The two answer types are annotations (a calculus whose codata
  constant is type-directed, as Core's `unfoldV C` is, needs them to build the loop). -/
  unfold  : Ty → Ty → Val → Val → Val → Val
  next    : Val → Term
  close   : Val → Term
  /-- Runs `M`, which answers `inl a` (done) or `inr l` (drive `l`). -/
  drive   : Term → Term
  /-- Evaluation contexts: all of the instance's. -/
  hole    : Kont
  /-- `kcomp K₁ K₂`: `K₂` plugged into `K₁`. -/
  kcomp   : Kont → Kont → Kont
  /-- `□ to x. N`. -/
  bindF   : Term → Kont
  /-- `□ V`. -/
  appF    : Val → Kont
  handleF : EA.Lab → Hnd → Kont
  /-- `□ then x. N unwind D`. -/
  thenF   : Term → Term → Kont
  /-- The runtime's driver around a program: `drive □`. -/
  driveF  : Kont
  plug    : Kont → Term → Term
  /-- Has a handler frame of the label. -/
  catches : Kont → EA.Lab → Bool
  /-- No frame of it stops a raise, other than a handler of the raise's label. -/
  unwindClear : Kont → Prop
  /-- Its finalisers, innermost first. -/
  fins    : Kont → List Term
  /-- What a cancel meets at its frames, innermost first: its finalisers, and the running
  finalisers of earlier cancels with the errors those cancels have kept. -/
  acts    : Kont → List (Act EA.Lab Val Term)
  /-- `κ`, handed to the clause of a caught operation. -/
  capture : EA.Lab → Hnd → Kont → Val
  /-- The start of `κ`'s cancel run. -/
  cancelOf : EA.Lab → Hnd → Kont → Term
  /-- A continuation's cell: a location of the store.  A one-shot continuation can be a store
  object at a fresh location, which its use releases (Affect §3.1; Hazel; SPEC §25's capture
  cell). -/
  Cell    : Type
  /-- `κ` at its cell: the continuation of a caught operation of class `k`, owning the cell. -/
  captureAt : OpClass → EA.Lab → Hnd → Kont → Cell → Val
  /-- The store holds nothing at the location. -/
  cellFree : Conf → Cell → Prop
  /-- The store with a cell at the location, holding the unit value; the term is kept. -/
  withCell : Conf → Cell → Conf
  init    : Term → Conf
  term    : Conf → Term
  /-- The same store, another term. -/
  setT    : Conf → Term → Conf
  step    : Conf → Ev EA.Lab Val Term → Conf → Prop
  /-- Typing: values and computations in a context of value types. -/
  derV    : List Ty → Val → Ty → Prop
  der     : List Ty → Term → CTy → Prop

/-- **The platform**: a runner (Ahman–Bauer Def. 1) for the operations it answers. -/
structure EffectSystem.Runner (S : EffectSystem) where
  answers : S.EA.Lab → ℕ → Prop
  St      : Type
  s₀      : St
  co      : St → S.EA.Lab → ℕ → S.Val → Option (S.Val × St)

namespace EffectSystem

variable (S : EffectSystem)

/-- The events of `S`'s steps. -/
abbrev Event : Type := Ev S.EA.Lab S.Val S.Term

/-! ### Runs -/

/-- Returned, and done. -/
def IsVal (c : S.Conf) : Prop := (∃ v, S.term c = S.ret v) ∧ ∀ ev c', ¬ S.step c ev c'

/-- A step that keeps the store. -/
def PureStep (c : S.Conf) (ev : S.Event) (c' : S.Conf) : Prop :=
  S.step c ev c' ∧ c' = S.setT c (S.term c')

def PureSteps : S.Conf → S.Conf → Prop :=
  Relation.ReflTransGen (fun c c' => ∃ ev, S.PureStep c ev c')

/-- A common reduct by steps that keep the store. -/
def PureJoin (c c' : S.Conf) : Prop := ∃ d, S.PureSteps c d ∧ S.PureSteps c' d

def Reach : S.Conf → S.Conf → Prop := Relation.ReflTransGen (fun c c' => ∃ ev, S.step c ev c')

/-- A configuration under a runner: the machine's and the runner's state. -/
abbrev RConf (R : S.Runner) : Type := S.Conf × R.St

def rinit (R : S.Runner) (e : S.Term) : S.RConf R := (S.init e, R.s₀)

def setR {R : S.Runner} (c : S.RConf R) (t : S.Term) : S.RConf R := (S.setT c.1 t, c.2)

/-- A step under a runner: a machine step, or the runner answering an operation no handler of the
program catches. -/
inductive RStep (R : S.Runner) : S.RConf R → S.Event → S.RConf R → Prop
  | mach {c : S.Conf} {ev : S.Event} {c' : S.Conf} {s : R.St} :
      S.step c ev c' → RStep R (c, s) ev (c', s)
  | io {c : S.Conf} {s s' : R.St} {K : S.Kont} {l : S.EA.Lab} {i : ℕ} {v w : S.Val} :
      S.term c = S.plug K (S.perform l i v) → S.catches K l = false →
      R.answers l i → R.co s l i v = some (w, s') →
      RStep R (c, s) (.io l i v w) (S.setT c (S.plug K (S.ret w)), s')

/-- A run, step by step. -/
inductive RPath (R : S.Runner) : S.RConf R → List (S.Event × S.RConf R) → Prop
  | nil {c : S.RConf R} : RPath R c []
  | cons {c : S.RConf R} {ev : S.Event} {c' : S.RConf R} {q : List (S.Event × S.RConf R)} :
      S.RStep R c ev c' → RPath R c' q → RPath R c ((ev, c') :: q)

/-- The configuration before step `j` of the path `q` from `c` (`c` itself at `0`). -/
def cfgAt {R : S.Runner} (c : S.RConf R) (q : List (S.Event × S.RConf R)) (j : ℕ) : S.RConf R :=
  ((c :: q.map Prod.snd)[j]?).getD c

/-- The last configuration of the path `q` from `c`. -/
def lastC {R : S.Runner} (c : S.RConf R) (q : List (S.Event × S.RConf R)) : S.RConf R :=
  S.cfgAt c q q.length

def RReach (R : S.Runner) : S.RConf R → S.RConf R → Prop :=
  Relation.ReflTransGen (fun c c' => ∃ ev, S.RStep R c ev c')

/-- A path of store-keeping machine steps, the runner's state unchanged. -/
inductive PurePath (R : S.Runner) : S.RConf R → List (S.Event × S.RConf R) → S.RConf R → Prop
  | nil {c : S.RConf R} : PurePath R c [] c
  | cons {c : S.RConf R} {ev : S.Event} {c' : S.RConf R} {q : List (S.Event × S.RConf R)}
      {c'' : S.RConf R} :
      S.PureStep c.1 ev c'.1 → c'.2 = c.2 → PurePath R c' q c'' → PurePath R c ((ev, c') :: q) c''

/-- The observable events: the platform's answers and the finaliser events. -/
def _root_.Targets.A.Ev.Obs {Lab Val Term : Type} : Ev Lab Val Term → Bool
  | .io .. => true
  | .fire _ => true
  | .finEnd _ => true
  | _ => false

/-- The observable events of a path, in order. -/
def obs {R : S.Runner} (q : List (S.Event × S.RConf R)) : List S.Event :=
  (q.map Prod.fst).filter Ev.Obs

/-- A complete run: a path that ends at an answer. -/
def CompleteFrom (R : S.Runner) (c : S.RConf R) (q : List (S.Event × S.RConf R)) : Prop :=
  S.RPath R c q ∧ S.IsVal (S.lastC c q).1

/-- Every run is never stuck. -/
def SafeRuns (R : S.Runner) (e : S.Term) : Prop :=
  ∀ c, S.RReach R (S.rinit R e) c → S.IsVal c.1 ∨ ∃ ev c', S.RStep R c ev c'

/-- Every run continues to an answer, and no run is infinite. -/
def Terminates (R : S.Runner) (e : S.Term) : Prop :=
  (∀ c, S.RReach R (S.rinit R e) c → ∃ c', S.RReach R c c' ∧ S.IsVal c'.1) ∧
  ¬ ∃ f : ℕ → S.RConf R, f 0 = S.rinit R e ∧ ∀ n, ∃ ev, S.RStep R (f n) ev (f (n + 1))

/-- The runner answers every operation the row admits. -/
def Answers (R : S.Runner) (ε : S.EA.Eff) : Prop := ∀ l i, S.has ε l i → R.answers l i

/-! ### Data -/

/-- The least types built by the data formers. -/
inductive DataTy : S.Ty → Prop
  | unit : DataTy S.UnitT
  | zero : DataTy S.ZeroT
  | tensor {A B : S.Ty} : DataTy A → DataTy B → DataTy (S.Tensor A B)
  | sum {A B : S.Ty} : DataTy A → DataTy B → DataTy (S.Sum A B)

/-- The values of the data types. -/
inductive DataVal : S.Ty → S.Val → Prop
  | unit : DataVal S.UnitT S.unitV
  | pair {A B : S.Ty} {a b : S.Val} : DataVal A a → DataVal B b → DataVal (S.Tensor A B) (S.pair a b)
  | inl {A B : S.Ty} {a : S.Val} : DataVal A a → DataVal (S.Sum A B) (S.inl a)
  | inr {A B : S.Ty} {b : S.Val} : DataVal B b → DataVal (S.Sum A B) (S.inr b)

/-- The runner keeps its protocol: it answers only linear operations at data types, every request
at the argument type, at the answer type. -/
def Runner.Respects {S : EffectSystem} (R : S.Runner) : Prop :=
  ∀ l i (o : OpSig S.Ty), R.answers l i → (S.sig l)[i]? = some o →
    o.cls = .linear ∧ S.DataTy o.arg ∧ S.DataTy o.ans ∧
    ∀ s v, S.DataVal o.arg v → ∃ w s', R.co s l i v = some (w, s') ∧ S.DataVal o.ans w

/-- The runner that answers nothing. -/
def R₀ : S.Runner := ⟨fun _ _ => False, Unit, (), fun _ _ _ _ => none⟩

/-! ### Behaviours -/

/-- **A behaviour**: every complete run answers `v` with the observable trace `tr`, and there is
one. -/
def RunsTo (R : S.Runner) (e : S.Term) (v : S.Val) (tr : List S.Event) : Prop :=
  (∃ q, S.CompleteFrom R (S.rinit R e) q ∧ S.term (S.lastC (S.rinit R e) q).1 = S.ret v ∧
    S.obs q = tr) ∧
  ∀ q, S.CompleteFrom R (S.rinit R e) q →
    S.term (S.lastC (S.rinit R e) q).1 = S.ret v ∧ S.obs q = tr

/-- **A run that never completes**: every run is safe, none completes, every prefix of `tr` is
shown, and every run shows a prefix of `tr`. -/
def RunsForever (R : S.Runner) (e : S.Term) (tr : ℕ → List S.Event) : Prop :=
  S.SafeRuns R e ∧ (∀ q, ¬ S.CompleteFrom R (S.rinit R e) q) ∧
  (∀ n, ∃ q, S.RPath R (S.rinit R e) q ∧ S.obs q = tr n) ∧
  ∀ q, S.RPath R (S.rinit R e) q → ∃ n, S.obs q <+: tr n

/-! ### Labels -/

/-- A program's labels have the stated signatures and are distinct. -/
def LabelsAt (sigs : List (List (OpSig S.Ty))) (ls : List S.EA.Lab) : Prop :=
  ls.length = sigs.length ∧ ls.Nodup ∧
    ∀ k (h₁ : k < ls.length) (h₂ : k < sigs.length), S.sig ls[k] = sigs[k]

/-- Some labels with the stated signatures exist, and every such choice works. -/
def ForLabels (sigs : List (List (OpSig S.Ty))) (P : List S.EA.Lab → Prop) : Prop :=
  (∃ ls, S.LabelsAt sigs ls) ∧ ∀ ls, S.LabelsAt sigs ls → P ls

/-! ### Term vocabulary -/

/-- `apps f [a₁, …, aₙ]` is `f a₁ … aₙ`. -/
def apps (f : S.Val) (as : List S.Val) : S.Term := as.foldl S.app (S.force f)

def call (f a : S.Val) : S.Term := S.apps f [a]

def call2 (f a b : S.Val) : S.Term := S.apps f [a, b]

/-- `lets [v₀, …, vₙ] N`: `vₙ` bound outermost, `v₀` innermost (`var 0` in `N`). -/
def lets : List S.Val → S.Term → S.Term
  | [], N => N
  | v :: vs, N => lets vs (S.bind (S.ret v) N)

def bool : S.Ty := S.Sum S.UnitT S.UnitT

def tt : S.Val := S.inr S.unitV

def ff : S.Val := S.inl S.unitV

/-! ### The schemas' vocabulary -/

/-- `P` calls `M` without catching a label of `L`: it reaches `M` by administrative steps, under a
context that catches no label of `L` and holds no finaliser. -/
def CallsThrough (L : S.EA.Lab → Prop) (P M : S.Term) : Prop :=
  ∃ K, (∀ m, L m → S.catches K m = false) ∧ S.unwindClear K ∧
    S.PureSteps (S.init P) (S.setT (S.init P) (S.plug K M))

/-- `ε` does not admit `l`. -/
def Lacks (ε : S.EA.Eff) (l : S.EA.Lab) : Prop := ∀ i, ¬ S.has ε l i

/-- **A polymorphic use** (schematic).  In the context `Γ`, the use `use g` serves a callback at
every row: for every row `ε` and every closed callback body `M` at `F ε B`, the use is typed at
`F ε B'`. -/
def PolyUse (Γ : List S.Ty) (use : S.Val → S.Term) (B B' : S.Ty) : Prop :=
  ∀ ε M, S.der [] M (S.F ε B) → S.der Γ (use (S.lam M)) (S.F ε B')

/-- The same at every row that does not admit `l`: for a higher-order value that handles `l` itself
somewhere, since a handler's label is not in its outer row (SPEC §19's `[handle]`: "`n` not in
`Σ`"). -/
def PolyUseLacks (Γ : List S.Ty) (l : S.EA.Lab) (use : S.Val → S.Term) (B B' : S.Ty) : Prop :=
  ∀ ε M, S.Lacks ε l → S.der [] M (S.F ε B) → S.der Γ (use (S.lam M)) (S.F ε B')

/-- For a higher-order value that handles its own label `l` around the callback: the body is at
`l ⊙ ε`, the use at `ε`, for every row `ε` that does not admit `l`. -/
def PolyUseOpen (Γ : List S.Ty) (l : S.EA.Lab) (use : S.Val → S.Term) (B B' : S.Ty) : Prop :=
  ∀ ε ε' M, S.Lacks ε l → S.EA.comp (S.EA.lift l) ε = some ε' →
    S.der [] M (S.F ε' B) → S.der Γ (use (S.lam M)) (S.F ε B')

end EffectSystem

end Targets.A
