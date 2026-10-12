import Targets.A.Expressiveness

/-!
# System A — A₃: the erased lowering, against a fixed target, stated, out of the first pass
(RESTRUCTURE §1.7; finding #4)

L1: "Part of 18 needs to be effect handling is erased", and, as relayed, "The criterion is cost
parity. A handler never adds cost of its own"; L2; L3.  OQ-23 (is lowering correctness a theorem?)
needs the user.

* **The fixed target** `Tgt`: a first-order machine, defined here and not supplied by the instance.
  Functions over words with numbered locals; a heap of word blocks with `alloc` and `free`; direct
  calls and tail calls; structured branches (`switch`); and `dispatch`, a switch on a code tag
  followed by direct calls, which is the only indirect call.  Platform calls are io events.  No
  instruction captures, saves, restores or searches a stack, so **erasure is structural**: every
  correct lowering into `Tgt` has erased handling.  It is modelled on the backend's flat IR
  (`Backend/Flat/Syntax.lean`).
* **The baseline is the hand-written equivalents** (`refCost`), fixed here: for each terminating
  (E) program, the cost of its hand-written, handler-free equivalent.  Each allocates nothing and
  makes no indirect call: callbacks are called directly, failure is a branch per call, and a
  suspension is a state machine whose state lives in the caller's frame.  So `ZeroCost` says that a
  lowered corpus program allocates nothing and dispatches nothing.
* **What the instance supplies** is the lowering and the label numbering, nothing else.  A target
  platform is related to a runner by `PlatformSim`, through the numbering and the data encoding.
* **The driven programs are not in the corpus** (`ZeroCost` reads complete runs): E3a, E3d–f and
  E10 are left out; when A₃ is taken up, each loop gets a per-iteration statement.

The hand-written reference programs themselves (the `Tgt` code whose run would check each
`refCost` entry) are not written in this pass; RESTRUCTURE §Unresolved records it.
-/

namespace Targets.A

namespace Tgt

/-- Expressions over words: a local, a literal, a load from a block, a binary primitive. -/
inductive Exp
  | loc (i : ℕ)
  | lit (n : ℕ)
  | load (a : Exp) (k : ℕ)
  | prim (o : ℕ) (a b : Exp)

/-- Statements. -/
inductive Stmt
  | set (i : ℕ) (e : Exp)
  | store (a : Exp) (k : ℕ) (v : Exp)
  | alloc (i n : ℕ)
  | free (a : Exp)
  | switch (e : Exp) (cs : List (List Stmt))
  | call (ds : List ℕ) (f : ℕ) (as : List Exp)
  | dispatch (ds : List ℕ) (tag : Exp) (fs : List ℕ) (as : List Exp)
  | tail (f : ℕ) (as : List Exp)
  | ret (es : List Exp)
  | io (ds : List ℕ) (lab op : ℕ) (args : List Exp)

structure Fn where
  params : ℕ
  body   : List Stmt

structure Prog where
  fns  : List Fn
  main : ℕ

/-- A target platform: a word-level runner, `(label, op, argument words) ↦ (answer words, state)`. -/
structure Platform where
  St : Type
  s₀ : St
  co : St → ℕ → ℕ → List ℕ → Option (List ℕ × St)

/-- An io event of the target. -/
structure IoEv where
  lab : ℕ
  op  : ℕ
  arg : List ℕ
  ans : List ℕ

/-- The fixed primitives: addition, truncated subtraction, equality, multiplication. -/
def primOp : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => a + b
  | 1, a, b => a - b
  | 2, a, b => if a = b then 1 else 0
  | 3, a, b => a * b
  | _, _, _ => 0

abbrev Heap := ℕ → Option (List ℕ)
abbrev Locals := ℕ → ℕ

/-- Expression evaluation. -/
inductive EvalE (h : Heap) (L : Locals) : Exp → ℕ → Prop
  | loc (i : ℕ) : EvalE h L (.loc i) (L i)
  | lit (n : ℕ) : EvalE h L (.lit n) n
  | load {a : Exp} {k p : ℕ} {b : List ℕ} {w : ℕ} :
      EvalE h L a p → h p = some b → b[k]? = some w → EvalE h L (.load a k) w
  | prim {o : ℕ} {a b : Exp} {x y : ℕ} :
      EvalE h L a x → EvalE h L b y → EvalE h L (.prim o a b) (primOp o x y)

/-- A list of expressions evaluated in order. -/
def EvalEs (h : Heap) (L : Locals) (es : List Exp) (ws : List ℕ) : Prop :=
  List.Forall₂ (EvalE h L) es ws

/-- `L` with the locals `ds` set to the words `ws`. -/
def assign (L : Locals) : List ℕ → List ℕ → Locals
  | d :: ds, w :: ws => assign (fun i => if i = d then w else L i) ds ws
  | _, _ => L

/-- The locals of a call: its arguments, then zeros. -/
def initLocals (ws : List ℕ) : Locals := fun i => ws.getD i 0

/-- A machine configuration: the heap, the platform's state, the io trace so far, and the counters
(allocations, dispatches). -/
structure Cfg (ρ : Platform) where
  heap : Heap
  ps   : ρ.St
  tr   : List IoEv
  allocs : ℕ
  dispatches : ℕ

/-- How a statement ends: it falls through with new locals, or it returns. -/
inductive Outcome
  | next (L : Locals)
  | done (ws : List ℕ)

mutual
/-- One statement. -/
inductive ExecS (ρ : Platform) (p : Prog) : Locals → Cfg ρ → Stmt → Outcome → Cfg ρ → Prop
  | set {L c i e n} : EvalE c.heap L e n →
      ExecS ρ p L c (.set i e) (.next (fun j => if j = i then n else L j)) c
  | store {L c a k v q b w} : EvalE c.heap L a q → EvalE c.heap L v w → c.heap q = some b →
      k < b.length →
      ExecS ρ p L c (.store a k v) (.next L)
        { c with heap := fun r => if r = q then some (b.set k w) else c.heap r }
  | alloc {L c i n q} : c.heap q = none →
      ExecS ρ p L c (.alloc i n) (.next (fun j => if j = i then q else L j))
        { c with heap := fun r => if r = q then some (List.replicate n 0) else c.heap r,
                 allocs := c.allocs + 1 }
  | free {L c a q b} : EvalE c.heap L a q → c.heap q = some b →
      ExecS ρ p L c (.free a) (.next L) { c with heap := fun r => if r = q then none else c.heap r }
  | switch {L c e n cs ss o c'} : EvalE c.heap L e n → cs[n]? = some ss → ExecL ρ p L c ss o c' →
      ExecS ρ p L c (.switch e cs) o c'
  | call {L c ds f as ws rs c'} : EvalEs c.heap L as ws → Call ρ p f ws c rs c' →
      ExecS ρ p L c (.call ds f as) (.next (assign L ds rs)) c'
  | dispatch {L c ds tag fs as n f ws rs c'} : EvalE c.heap L tag n → fs[n]? = some f →
      EvalEs c.heap L as ws → Call ρ p f ws { c with dispatches := c.dispatches + 1 } rs c' →
      ExecS ρ p L c (.dispatch ds tag fs as) (.next (assign L ds rs)) c'
  | tail {L c f as ws rs c'} : EvalEs c.heap L as ws → Call ρ p f ws c rs c' →
      ExecS ρ p L c (.tail f as) (.done rs) c'
  | ret {L c es ws} : EvalEs c.heap L es ws → ExecS ρ p L c (.ret es) (.done ws) c
  | io {L c ds lab op args ws rs s'} : EvalEs c.heap L args ws → ρ.co c.ps lab op ws = some (rs, s') →
      ExecS ρ p L c (.io ds lab op args) (.next (assign L ds rs))
        { c with ps := s', tr := c.tr ++ [⟨lab, op, ws, rs⟩] }
/-- A list of statements. -/
inductive ExecL (ρ : Platform) (p : Prog) : Locals → Cfg ρ → List Stmt → Outcome → Cfg ρ → Prop
  | nil {L c} : ExecL ρ p L c [] (.next L) c
  | next {L c s ss L' c' o c''} : ExecS ρ p L c s (.next L') c' → ExecL ρ p L' c' ss o c'' →
      ExecL ρ p L c (s :: ss) o c''
  | done {L c s ss ws c'} : ExecS ρ p L c s (.done ws) c' → ExecL ρ p L c (s :: ss) (.done ws) c'
/-- A call of function `f` at the argument words, returning the words `rs`. -/
inductive Call (ρ : Platform) (p : Prog) : ℕ → List ℕ → Cfg ρ → List ℕ → Cfg ρ → Prop
  | mk {f ws c fn rs c'} : p.fns[f]? = some fn → ws.length = fn.params →
      ExecL ρ p (initLocals ws) c fn.body (.done rs) c' → Call ρ p f ws c rs c'
end

/-- `Run ρ p ws tr k`: a complete run of `p` under `ρ` answers the words `ws` with the io trace
`tr`, having made `k.1` allocations and `k.2` dispatches. -/
def Run (ρ : Platform) (p : Prog) (ws : List ℕ) (tr : List IoEv) (k : ℕ × ℕ) : Prop :=
  ∃ c' : Cfg ρ, Call ρ p p.main [] ⟨fun _ => none, ρ.s₀, [], 0, 0⟩ ws c' ∧ tr = c'.tr ∧
    k = (c'.allocs, c'.dispatches)

/-- The terminating (E) programs, the corpus of `ZeroCost`. -/
inductive CorpusId
  | e1 | e1' | e2a | e2b | e2c | e2d | e3b | e3c | e3g | e4 | e5log | e5fail | e6
  | e7a | e7b | e7d | e8a | e8b | e9a | e9b | e9c
  deriving DecidableEq, Repr

/-- **The hand-written equivalents' costs** (allocations, dispatches).  E1: the pure call, a
sum-returning copy of the failing callback (a branch per call) and a direct call for the
asynchronous one, whose handler resumes at once.  E1′, E9: the suspended computation's state is a
state machine in the caller's frame, resumed by a branch.  E2: callbacks and composed callbacks are
called directly.  E3b, E3c, E3g: loops.  E4, E5: direct calls for answering operations, branches for
raises.  E6: a branch.  E7, E8: the finalisers called on the exit paths.  None allocates, and none
makes an indirect call. -/
def refCost : CorpusId → ℕ × ℕ
  | .e1 | .e1' | .e2a | .e2b | .e2c | .e2d | .e3b | .e3c | .e3g | .e4 | .e5log | .e5fail | .e6
  | .e7a | .e7b | .e7d | .e8a | .e8b | .e9a | .e9b | .e9c => (0, 0)

end Tgt

namespace EffectSystem

variable (S : EffectSystem)

/-- An entry of the corpus: a terminating (E) program at its labels, its runner, and its
signatures. -/
structure CorpusEntry where
  id     : Tgt.CorpusId
  term   : List S.EA.Lab → S.Term
  runner : List S.EA.Lab → S.Runner
  sigs   : List (List (OpSig S.Ty))

/-- A program of two labels. -/
def at2 (f : S.EA.Lab → S.EA.Lab → S.Term) : List S.EA.Lab → S.Term
  | [a, b] => f a b
  | _ => S.ret S.unitV

/-- A program of three labels. -/
def at3 (f : S.EA.Lab → S.EA.Lab → S.EA.Lab → S.Term) : List S.EA.Lab → S.Term
  | [a, b, c] => f a b c
  | _ => S.ret S.unitV

/-- `Rtick` at the second label. -/
noncomputable def rtick2 : List S.EA.Lab → S.Runner
  | [_, b] => S.Rtick b
  | [a] => S.Rtick a
  | _ => S.R₀

/-- **The corpus**: E1, E1′, E2a–d, E3b, E3c, E3g, E4, E5 (both orders), E6, E7a, E7b, E7d,
E8a–b, E9a–c, at the labels of their (E) properties.  E7c is the program E7 rejects. -/
noncomputable def corpus : List S.CorpusEntry :=
  [⟨.e1, S.at2 S.noColour, fun _ => S.R₀, [S.sigExn, S.sigWait]⟩,
   ⟨.e1', S.at2 fun _ lw => S.noColourS lw, fun _ => S.R₀, [S.sigExn, S.sigWait]⟩,
   ⟨.e2a, S.at2 fun le _ => S.prog2a le, fun _ => S.R₀, [S.sigExn, S.sigWait]⟩,
   ⟨.e2b, S.at2 fun _ lw => S.prog2b lw, fun _ => S.R₀, [S.sigExn, S.sigWait]⟩,
   ⟨.e2c, S.at2 S.prog2c, fun _ => S.R₀, [S.sigExn, S.sigLog]⟩,
   ⟨.e2d, S.at2 S.prog2d, fun _ => S.R₀, [S.sigYield, S.sigExn]⟩,
   ⟨.e3b, S.at2 fun lt _ => S.runL (S.countL lt), fun ls => S.rtick2 (ls.take 1),
     [S.sigTick, S.sigLog]⟩,
   ⟨.e3c, S.at2 fun lt _ => S.e3c lt, fun ls => S.rtick2 (ls.take 1), [S.sigTick, S.sigLog]⟩,
   ⟨.e3g, fun _ => S.fuel 3 S.spinL, fun _ => S.R₀, []⟩,
   ⟨.e4, S.at2 S.deepGen, S.rtick2, [S.sigYield, S.sigTick]⟩,
   ⟨.e5log, S.at2 fun llog le => S.withLog llog (S.toResult le (S.body5 llog le)), fun _ => S.R₀,
     [S.sigLog, S.sigExn]⟩,
   ⟨.e5fail, S.at2 fun llog le => S.toResult le (S.withLog llog (S.body5 llog le)), fun _ => S.R₀,
     [S.sigLog, S.sigExn]⟩,
   ⟨.e6, S.at2 S.tunnel, fun _ => S.R₀, [S.sigExn, S.sigExn]⟩,
   ⟨.e7a, S.at3 fun lw _ _ => S.e7a lw, fun _ => S.R₀, [S.sigWait, S.sigExn, S.sigExn]⟩,
   ⟨.e7b, S.at3 fun lw la _ => S.e7b lw la, fun _ => S.R₀, [S.sigWait, S.sigExn, S.sigExn]⟩,
   ⟨.e7d, S.at3 S.e7d, fun _ => S.R₀, [S.sigWait, S.sigExn, S.sigExn]⟩,
   ⟨.e8a, S.at2 fun la _ => S.e8a la, fun _ => S.R₀, [S.sigExn, S.sigExn]⟩,
   ⟨.e8b, S.at2 S.e8b, fun _ => S.R₀, [S.sigExn, S.sigExn]⟩,
   ⟨.e9a, S.at2 fun ly _ => S.e9 ly (S.gen9 ly) (S.inr S.unitV), fun _ => S.R₀,
     [S.sigYield, S.sigExn]⟩,
   ⟨.e9b, S.at2 fun ly _ => S.e9 ly (S.gen9 ly) (S.inl S.unitV), fun _ => S.R₀,
     [S.sigYield, S.sigExn]⟩,
   ⟨.e9c, S.at2 S.e9c, fun _ => S.R₀, [S.sigYield, S.sigExn]⟩]

/-- What the instance supplies: the lowering and the label numbering. -/
structure Lowering where
  lower : S.Term → Tgt.Prog
  labNum : S.EA.Lab → ℕ
  labNum_inj : Function.Injective labNum

/-- The data encoding, A-defined on the data formers: `unitV ↦ []`, `pair a b ↦ enc a ++ enc b`,
`inl a ↦ 0 :: enc a`, `inr a ↦ 1 :: enc a`. -/
inductive DataEnc : S.Val → List ℕ → Prop
  | unit : DataEnc S.unitV []
  | pair {a b : S.Val} {wa wb : List ℕ} : DataEnc a wa → DataEnc b wb → DataEnc (S.pair a b) (wa ++ wb)
  | inl {a : S.Val} {wa : List ℕ} : DataEnc a wa → DataEnc (S.inl a) (0 :: wa)
  | inr {a : S.Val} {wa : List ℕ} : DataEnc a wa → DataEnc (S.inr a) (1 :: wa)

/-- A source io event and a target io event agree, through the numbering and the encoding. -/
def IoEvEnc (L : S.Lowering) : S.Event → Tgt.IoEv → Prop
  | .io l i v w, t => t.lab = L.labNum l ∧ t.op = i ∧ S.DataEnc v t.arg ∧ S.DataEnc w t.ans
  | _, _ => False

/-- Keeps a trace's io events. -/
def isIo : S.Event → Bool
  | .io .. => true
  | _ => false

/-- The io events of a source trace, encoded, are the target's trace. -/
def IoEnc (L : S.Lowering) (tr : List S.Event) (trT : List Tgt.IoEv) : Prop :=
  List.Forall₂ (S.IoEvEnc L) (tr.filter S.isIo) trT

/-- The target platform `ρ` answers as the runner `R` does, through the numbering and the encoding,
their states related, and answers nothing else. -/
def PlatformSim (L : S.Lowering) (R : S.Runner) (ρ : Tgt.Platform) : Prop :=
  ∃ rel : R.St → ρ.St → Prop, rel R.s₀ ρ.s₀ ∧
    (∀ s σ l i v ws w s', rel s σ → S.DataEnc v ws → R.co s l i v = some (w, s') →
       ∃ ws' σ', ρ.co σ (L.labNum l) i ws = some (ws', σ') ∧ S.DataEnc w ws' ∧ rel s' σ') ∧
    (∀ σ lab i ws ws' σ', ρ.co σ lab i ws = some (ws', σ') →
       ∃ s l v w s', rel s σ ∧ L.labNum l = lab ∧ S.DataEnc v ws ∧ R.co s l i v = some (w, s') ∧
         S.DataEnc w ws' ∧ rel s' σ')

/-- **Lowering correctness**: the target observes exactly what the source does. -/
def LoweringCorrect (L : S.Lowering) : Prop :=
  ∀ (R : S.Runner) (ρ : Tgt.Platform) e ε A, R.Respects → S.Answers R ε → S.DataTy A →
    S.der [] e (S.F ε A) → S.PlatformSim L R ρ →
    (∀ v tr, S.RunsTo R e v tr →
       ∃ ws trT k, S.DataEnc v ws ∧ S.IoEnc L tr trT ∧ Tgt.Run ρ (L.lower e) ws trT k) ∧
    (∀ ws trT k, Tgt.Run ρ (L.lower e) ws trT k →
       ∃ v tr, S.RunsTo R e v tr ∧ S.DataEnc v ws ∧ S.IoEnc L tr trT)

/-- **Zero cost**: on the corpus, each lowered program costs no more than the hand-written
equivalent. -/
def ZeroCost (L : S.Lowering) : Prop :=
  ∀ P ∈ S.corpus, ∀ ls, S.LabelsAt P.sigs ls → ∀ ρ, S.PlatformSim L (P.runner ls) ρ →
    ∀ ws trT k, Tgt.Run ρ (L.lower (P.term ls)) ws trT k →
      k.1 ≤ (Tgt.refCost P.id).1 ∧ k.2 ≤ (Tgt.refCost P.id).2

end EffectSystem

end Targets.A
