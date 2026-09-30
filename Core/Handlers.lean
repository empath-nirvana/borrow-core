import Core.Fix
import Core.Steps
import Support.Dynamics.Completeness

/-!
# Core — the laws of the handler schemas  `[spec §18]`

A handler is defined by its elaboration into core terms (SPEC §18, decision 48), so there is no
separate handler semantics for the elaboration to agree with. What can still be wrong is what a
handler *means*, and that is checked here: each class of clause has an algebraic law, stated
about the machine's runs of the terms the elaboration emits, as `experiments/CoeffectsStrict`'s
`Handler.lean` states the homomorphism equations of a deep handler as runs of `foldOwn`.

**Answering, tail-resumptive (`op_tail`, `op_answer`).** An operation call `op(v)` on the
capability `ℓ` is `withswap ℓ (λs. g (s, v))`, `g` the clause's code over the state and the
argument. Its law is `handle E[op v] = handle E[clause v]`: in any evaluation context `K` (the
rest of the handled body, the continuation) and at every memory whose cell `ℓ` holds the state
`s`, the call reduces, with no change to memory, to the clause run on `s` (`op_tail`); and when
the clause answers the new state `s'` and the result `r`, the call reaches `K[(ℓ, r)]` with `s'`
in the cell (`op_answer`). The continuation is resumed once, in place, with the answer: nothing
is captured or allocated, and `K` is never inspected.

**Handling is the fold of the clauses (`handle_fold`).** A handled body that performs the
operations `(g₁, v₁), …, (gₙ, vₙ)` and goes on with `k` runs the clauses one after the other on the
threaded state, and then `k`: the tail-resumptive handler is the state-passing fold of its clauses
over the operations performed, as a deep handler is the fold of its free model.

**Abort (`abort_passes`, `return_resumes`, `loop_abort`).** A call that can raise is followed by the branch
`case t { inl x -> K | inr e -> inr e }`: the rest of the body `K` on a value, the error handed on.
An abort `inr e` passes every such branch around it and reaches the handler unchanged, running
none of their continuations (`abort_passes`); this is `handle E[raise e] = handler(e)` for the
`try` handler, whose answer is the sum. A value `inl v` runs the innermost continuation with it
(`return_resumes`), which is `handle (return v) = return v`. Inside a loop's body the abort is the
loop's own exit: a step that answers `inr e` ends `count_try` with `inr e` at once
(`countTry_exit`, SPEC §16), after which the loop is such a branch.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Handlers
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-! ### The answering class -/

/-- The callback a clause runs under `withswap`: `λs. g (s, v)`. -/
def clauseCb (g v : Val) : Val := .lam (.app (.val g) (.pair (.var 0) (.val v)))

/-- An operation call on the capability `ℓ` (SPEC §18): `withswap ℓ (λs. g (s, v))`, with `g`
the clause's code and `v` the argument. -/
def opCall (ℓ : Loc) (g v : Val) : Expr :=
  .app (.app withswap (.val (.loc ℓ))) (.val (clauseCb g v))

/-- What an operation call reduces to on the state `s`: the clause run on `(s, v)`, its new
state stored in the cell, and its answer handed back beside the capability. -/
def clauseRun (ℓ : Loc) (g s v : Val) : Expr :=
  .letpair (.app (.val g) (.val (.pair s v)))
    (.seq (.app (.app store' (.val (.loc ℓ))) (.var 1)) (.pair (.val (.loc ℓ)) (.var 0)))

/-- One head step in an evaluation context, as a run. -/
theorem steps_head_in (K : Kont) {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a') :
    Steps (ℍ := ℍ) μ (K.plug a) μ' (K.plug a') :=
  .more ((Step1.head h).plug K) (.refl _ _)

/-- The rest of `withswap`'s body after its callback answers: the new state stored and the
answer handed back beside the capability. -/
def swapRest (ℓ : Loc) : Expr :=
  .seq (.app (.app store' (.val (.loc ℓ))) (.var 1)) (.pair (.val (.loc ℓ)) (.var 0))

/-- **The tail-resumptive law, the call.** In any continuation `K`, at a memory whose cell `ℓ`
holds `s`, the operation call reduces to its clause run on `s`, with no change to memory. -/
theorem op_tail (K : Kont) {μ : Heap} {ℓ : Loc} {s : Val} (hs : μ ℓ = some s) (g v : Val)
    (hg : closedAt 0 g.1 = true) (hv : closedAt 0 v.1 = true) :
    Steps (ℍ := ℍ) μ (K.plug (opCall ℓ g v)) μ (K.plug (clauseRun ℓ g s v)) := by
  refine Steps.plug K ?_
  -- `withswap ℓ` ↦ `λf. body[ℓ/x]`.
  have h₁ : Steps (ℍ := ℍ) μ (opCall ℓ g v) μ
      (.app (.val (.lam (.letpair (.app (.var 0) (.app load' (.val (.loc ℓ)))) (swapRest ℓ))))
        (.val (clauseCb g v))) :=
    steps_head_in (Kont.appL .hole (clauseCb g v)) (Head.beta μ _ (Val.loc ℓ))
  -- `(λf. body[ℓ/x]) cb` ↦ `body[ℓ/x, cb/f]`.
  have h₂ : Steps (ℍ := ℍ) μ
      (.app (.val (.lam (.letpair (.app (.var 0) (.app load' (.val (.loc ℓ)))) (swapRest ℓ))))
        (.val (clauseCb g v))) μ
      (.letpair (.app (.val (clauseCb g v)) (.app load' (.val (.loc ℓ)))) (swapRest ℓ)) :=
    steps_head_in .hole (Head.beta μ _ (clauseCb g v))
  -- `load ℓ` ↦ `s`, in the argument of the callback.
  have h₃ : Steps (ℍ := ℍ) μ
      (.letpair (.app (.val (clauseCb g v)) (.app load' (.val (.loc ℓ)))) (swapRest ℓ)) μ
      (.letpair (.app (.val (clauseCb g v)) (.val s)) (swapRest ℓ)) :=
    steps_head_in (Kont.letpair (Kont.appR (.val (clauseCb g v)) .hole) (swapRest ℓ))
      (Head.load μ ℓ s hs)
  -- `cb s` ↦ `g (s, v)`.
  have h₄ : Steps (ℍ := ℍ) μ (.letpair (.app (.val (clauseCb g v)) (.val s)) (swapRest ℓ)) μ
      (clauseRun ℓ g s v) := by
    have := steps_head_in (ℍ := ℍ) (Kont.letpair .hole (swapRest ℓ))
      (Head.beta μ (.app (.val g) (.pair (.var 0) (.val v))) s)
    simpa [Kont.plug, Expr.subst, val_subst_closed hg, val_subst_closed hv, clauseRun, swapRest,
      clauseCb, Expr.val]
      using this
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- The clause's answer stored and handed back: when the clause's run on `(s, v)` answers the new
state `s'` and the result `r`, the rest of `withswap` puts `s'` in the cell and answers `(ℓ, r)`. -/
theorem clauseRun_answers {μ μ₁ : Heap} {ℓ : Loc} {g s v s' r w : Val}
    (hrun : Steps (ℍ := ℍ) μ (.app (.val g) (.val (.pair s v))) μ₁ (.val (.pair s' r)))
    (hw : μ₁ ℓ = some w) (hr : closedAt 0 r.1 = true) :
    Steps (ℍ := ℍ) μ (clauseRun ℓ g s v) (μ₁.upd ℓ s') (.val (.pair (.loc ℓ) r)) := by
  have h₁ : Steps (ℍ := ℍ) μ (clauseRun ℓ g s v) μ₁ (.letpair (.val (.pair s' r)) (swapRest ℓ)) :=
    hrun.plug (Kont.letpair .hole (swapRest ℓ))
  have h₂ : Steps (ℍ := ℍ) μ₁ (.letpair (.val (.pair s' r)) (swapRest ℓ)) μ₁
      (.seq (.app (.app store' (.val (.loc ℓ))) (.val s')) (.val (.pair (.loc ℓ) r))) := by
    have := steps_head_in (ℍ := ℍ) .hole (Head.letpair μ₁ s' r (swapRest ℓ))
    simpa [Kont.plug, Expr.subst, swapRest, val_shift_closed hr, val_subst_closed hr, Expr.val, store']
      using this
  have h₃ : Steps (ℍ := ℍ) μ₁
      (.seq (.app (.app store' (.val (.loc ℓ))) (.val s')) (.val (.pair (.loc ℓ) r))) (μ₁.upd ℓ s')
      (.seq (.val .unit) (.val (.pair (.loc ℓ) r))) :=
    steps_head_in (Kont.seq .hole _) (Head.store μ₁ ℓ s' w hw)
  have h₄ : Steps (ℍ := ℍ) (μ₁.upd ℓ s') (.seq (.val .unit) (.val (.pair (.loc ℓ) r))) (μ₁.upd ℓ s')
      (.val (.pair (.loc ℓ) r)) :=
    steps_head_in .hole (Head.seq _ _)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- **The tail-resumptive law.** `handle K[op v] ↦* handle K[r]`: in any continuation `K`, at a
memory whose cell `ℓ` holds the state `s`, when the clause run on `(s, v)` answers the new state
`s'` and the result `r`, the operation call reaches `K[(ℓ, r)]`, the continuation resumed once with
the answer and the capability, with `s'` in the cell. -/
theorem op_answer (K : Kont) {μ μ₁ : Heap} {ℓ : Loc} {g s v s' r w : Val} (hs : μ ℓ = some s)
    (hg : closedAt 0 g.1 = true) (hv : closedAt 0 v.1 = true) (hr : closedAt 0 r.1 = true)
    (hrun : Steps (ℍ := ℍ) μ (.app (.val g) (.val (.pair s v))) μ₁ (.val (.pair s' r)))
    (hw : μ₁ ℓ = some w) :
    Steps (ℍ := ℍ) μ (K.plug (opCall ℓ g v)) (μ₁.upd ℓ s') (K.plug (.val (.pair (.loc ℓ) r))) :=
  (op_tail K hs g v hg hv).trans ((clauseRun_answers hrun hw hr).plug K)

/-! ### The abort class -/

/-- The error arm of the branch after a call that can raise: `inr e`, handed on. -/
def abortArm : Expr := .inj₂ (.var 0)

/-- The branches around an abort point, outermost first: each `case [·] { inl x -> K | inr e ->
inr e }`, the continuation `K` still to run above it. -/
def branches : List Expr → Kont
  | [] => .hole
  | K :: Ks => .case (branches Ks) K abortArm

/-- **The abort law.** An abort `inr e` passes every branch around it, running none of their
continuations, and reaches the handler as `inr e`: `try { E[raise e] } ↦* inr e`. -/
theorem abort_passes (Ks : List Expr) (μ : Heap) (e : Val) :
    Steps (ℍ := ℍ) μ ((branches Ks).plug (.val (.inj₂ e))) μ (.val (.inj₂ e)) := by
  induction Ks with
  | nil => exact .refl _ _
  | cons K Ks ih =>
    have h₁ : Steps (ℍ := ℍ) μ ((branches (K :: Ks)).plug (.val (.inj₂ e))) μ
        (.case (.val (.inj₂ e)) K abortArm) :=
      ih.plug (Kont.case .hole K abortArm)
    have h₂ : Steps (ℍ := ℍ) μ (.case (.val (.inj₂ e)) K abortArm) μ (.val (.inj₂ e)) :=
      steps_head_in .hole (Head.case₂ μ e K abortArm)
    exact h₁.trans h₂

/-- **The return law.** A value `inl v` runs the innermost continuation with it: the branch
`case (inl v) { inl x -> K | inr e -> inr e }` reduces to `K[v/x]`. -/
theorem return_resumes (K : Expr) (μ : Heap) (v : Val) :
    Steps (ℍ := ℍ) μ (.case (.val (.inj₁ v)) K abortArm) μ (K.subst 0 v) :=
  steps_head_in .hole (Head.case₁ μ v K abortArm)

/-! ### Handling is the fold of the clauses -/

/-- A straight run of operation calls on the capability `ℓ`, then `k`: each call's answer
`(ℓ, r)` bound, and the next call made. The elaborated form of a handled body that performs the
operations `(g₁, v₁), …, (gₙ, vₙ)` in order and goes on with `k`. -/
def seqCalls (ℓ : Loc) : List (Val × Val) → Expr → Expr
  | [], k => k
  | (g, v) :: cs, k => .letpair (opCall ℓ g v) (seqCalls ℓ cs k)

/-- The clauses run one after the other on the state in `ℓ`, each on the state the one before it
left, from `μ` to `μ'`: the fold of the handler's clauses over the operations performed, into
the state it threads. -/
inductive ClauseRuns (ℓ : Loc) : List (Val × Val) → Heap → Heap → Prop
  | nil (μ : Heap) : ClauseRuns ℓ [] μ μ
  | cons {g v s s' r w : Val} {μ μ₁ μ' : Heap} {cs : List (Val × Val)} (hs : μ ℓ = some s)
      (hrun : Steps (ℍ := ℍ) μ (.app (.val g) (.val (.pair s v))) μ₁ (.val (.pair s' r)))
      (hw : μ₁ ℓ = some w) (hr : closedAt 0 r.1 = true)
      (rest : ClauseRuns ℓ cs (μ₁.upd ℓ s') μ') : ClauseRuns ℓ ((g, v) :: cs) μ μ'

theorem opCall_closed (ℓ : Loc) {g v : Val} (hg : closedAt 0 g.1 = true)
    (hv : closedAt 0 v.1 = true) : closedAt 0 (opCall ℓ g v) = true := by
  simp [opCall, clauseCb, withswap, lam2, closedAt, v0, v1, v3, load', store',
    closedAt_mono _ hg (Nat.zero_le 1), closedAt_mono _ hv (Nat.zero_le 1)]

theorem seqCalls_closed (ℓ : Loc) (k : Expr) (hk : closedAt 0 k = true) :
    ∀ cs : List (Val × Val), (∀ p ∈ cs, closedAt 0 p.1.1 = true ∧ closedAt 0 p.2.1 = true) →
      closedAt 0 (seqCalls ℓ cs k) = true
  | [], _ => hk
  | (g, v) :: cs, h => by
    have hgv := h (g, v) (List.mem_cons_self ..)
    simp only [seqCalls, closedAt, Bool.and_eq_true]
    exact ⟨opCall_closed ℓ hgv.1 hgv.2,
      closedAt_mono _ (seqCalls_closed ℓ k hk cs fun p hp => h p (List.mem_cons_of_mem _ hp))
        (Nat.zero_le 2)⟩

/-- **Handling is the fold of the clauses.** A handled body that performs the operations
`(g₁, v₁), …, (gₙ, vₙ)` and goes on with `k` runs, when the clauses run one after the other on
the threaded state (`ClauseRuns`), to `k` at the memory the last one left: the tail-resumptive
handler is the state-passing fold of its clauses over the operations, as a deep handler is the
fold of its free model (`experiments/CoeffectsStrict`'s `Handler.lean`). -/
theorem handle_fold {ℓ : Loc} {k : Expr} (hk : closedAt 0 k = true) {cs : List (Val × Val)}
    (hcs : ∀ p ∈ cs, closedAt 0 p.1.1 = true ∧ closedAt 0 p.2.1 = true) {μ μ' : Heap}
    (h : ClauseRuns (ℍ := ℍ) ℓ cs μ μ') : Steps (ℍ := ℍ) μ (seqCalls ℓ cs k) μ' k := by
  induction h with
  | nil => exact .refl _ _
  | @cons g v s s' r w μ μ₁ μ' cs hs hrun hw hr rest ih =>
    have hgv := hcs (g, v) (List.mem_cons_self ..)
    have hrest := seqCalls_closed ℓ k hk cs fun p hp => hcs p (List.mem_cons_of_mem _ hp)
    have h₁ := op_answer (ℍ := ℍ) (Kont.letpair .hole (seqCalls ℓ cs k)) hs hgv.1 hgv.2 hr hrun hw
    have h₂ : Steps (ℍ := ℍ) (μ₁.upd ℓ s') (.letpair (.val (.pair (.loc ℓ) r)) (seqCalls ℓ cs k))
        (μ₁.upd ℓ s') (seqCalls ℓ cs k) := by
      have := steps_head_in (ℍ := ℍ) .hole (Head.letpair (μ₁.upd ℓ s') (.loc ℓ) r (seqCalls ℓ cs k))
      simpa [Kont.plug, subst_closedAt _ _ hrest (Nat.zero_le _)] using this
    exact (h₁.trans h₂).trans (ih fun p hp => hcs p (List.mem_cons_of_mem _ hp))

/-- **The abort law in a loop.** A step of `count_try` that answers `inr e` ends the loop with
`inr e` (`countTry_exit`), and the branches after it hand the error on: an abort in a loop's body
reaches the handler, running none of the rest. -/
theorem loop_abort (Ks : List Expr) (f : Val) (n i : UInt32) (s e : Val) (μ μ' : Heap)
    (hi : i < arrLen n)
    (hf : Steps (ℍ := ℍ) μ (.app (.val f) (.val (Val.pair (Val.i32 i) s))) μ' (.val (Val.inj₂ e))) :
    Steps (ℍ := ℍ) μ ((branches Ks).plug (BoCa.BoLo.countTryE f n i s)) μ' (.val (.inj₂ e)) :=
  ((BoCa.BoLo.countTry_exit f n i s e μ μ' hi hf).plug (branches Ks)).trans (abort_passes Ks μ' e)

end BoCa.Fig16.LogRel.Core.Handlers

end
