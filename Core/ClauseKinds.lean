import Core.Handlers
import Core.EffRules
import Core.DivHandleLast

/-!
# Core — the premises of the clause kinds  `[spec §19]`

A control clause of `[handle]` is `λp. let (x, κ) = p; M` (`clauseTy`): it takes the operation's
argument and the continuation `κ : U((B ⊸ F_Σ R) & C)`, whose resume is `κ.1` and whose cancel
is `κ.2`. Erased, the resume of `κ` in the slot `k` is `k (inl ())` applied to the answer, and the
cancel is `k (inr ())` (`resumeAt`, `cancelAt`). What the effect-erasure pass may do at an
operation depends on how `M` uses `κ` on its paths, through the arms of `case`s, the bodies of
`let`s and sequences, and the alias `let k' = κ in M'` (`OnPaths`). Each kind of clause is a
property of `M`, the premise of the handler law that kind's rewrite applies:

* **tail-resumptive** (`TailResumesAt`): every path ends in one resume of `κ` in tail position,
  or that resume under the right unit `let x = κ.1 N in return x`, and uses `κ` nowhere else.
  Closing `κ` makes it `TailResumes`, the premise of `tail_resumes`
  (`TailResumesAt.subst_kappa`), and the clause without its resumes does not mention `κ`
  (`TailResumesAt.kappa_free`);
* **tail-resumptive with handler state** (`StateLeaf`): the clause answers the state-passing
  function `λs. S` (§21's encoding of a handler with a state), and every path of `S` resumes
  `κ`, then applies the function it answers to the new state in tail position (`AppliesAt`);
* **resume or cancel** (`CancelLeaf`): each path either resumes `κ` in tail position or cancels
  it and goes on without it (`kappa_cancel_steps`, `cancel_prefix`), with or without state;
* **resume once** (`Once`): each path uses `κ` once, by a resume or a cancel in evaluation
  position, and never under a `λ` (so `κ` is not stored), with or without state.

What a path that matches none of these does with `κ` is not described here: such a clause may
keep `κ`, and is left to the state machines.
-/

namespace BoCa.Fig16.LogRel.Core.ClauseKinds
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Handlers

/-- Whether the variable `k` occurs free in `e`. -/
def mentions : Nat → Expr → Bool
  | k, .var i => i == k
  | _, .unit => false
  | k, .pair a b => mentions k a || mentions k b
  | k, .inj₁ a => mentions k a
  | k, .inj₂ a => mentions k a
  | k, .lam b => mentions (k + 1) b
  | _, .loc _ => false
  | _, .prim _ => false
  | k, .seq a b => mentions k a || mentions k b
  | k, .letpair a b => mentions k a || mentions (k + 2) b
  | k, .case e a b => mentions k e || mentions (k + 1) a || mentions (k + 1) b
  | k, .app a b => mentions k a || mentions k b

/-- The resume projection of the continuation in the slot `k`: `κ.1`, erased. -/
def resumeAt (k : Nat) : Expr := .app (.var k) (.val (.inj₁ .unit))

/-- The cancel of the continuation in the slot `k`: `κ.2`, erased. -/
def cancelAt (k : Nat) : Expr := .app (.var k) (.val (.inj₂ .unit))

/-- The resume projection of a continuation value `κ`. -/
def resumeOf (κ : Val) : Expr := .app (.val κ) (.val (.inj₁ .unit))

theorem closedAt_resumeOf {κ : Val} (h : closedAt 0 κ.1 = true) :
    closedAt 0 (resumeOf κ) = true := by
  simp [resumeOf, closedAt, h, Expr.val, Val.inj₁, Val.unit]

/-! ### Paths -/

/-- Every path of `e` from its root, through the arms of `case`s, the bodies of `let (x, y)`s,
sequences and `let x = M` (`(λx. B) M`), ends in a leaf `L` at the slot `κ` has there, and `κ`
is not used on the way. An alias `let k' = κ in B`, `(λk'. B) κ`, moves `κ` to the slot of `k'`,
`B` not using the old one. -/
inductive OnPaths (L : Nat → Expr → Prop) : Nat → Expr → Prop where
  | leaf {k : Nat} {e : Expr} : L k e → OnPaths L k e
  | case {k : Nat} {e B₁ B₂ : Expr} : mentions k e = false → OnPaths L (k + 1) B₁ →
      OnPaths L (k + 1) B₂ → OnPaths L k (.case e B₁ B₂)
  | letpair {k : Nat} {e B : Expr} : mentions k e = false → OnPaths L (k + 2) B →
      OnPaths L k (.letpair e B)
  | seq {k : Nat} {e B : Expr} : mentions k e = false → OnPaths L k B → OnPaths L k (.seq e B)
  | bind {k : Nat} {e B : Expr} : mentions k e = false → OnPaths L (k + 1) B →
      OnPaths L k (.app (.val (.lam B)) e)
  | rebind {k : Nat} {B : Expr} : mentions (k + 1) B = false → OnPaths L 0 B →
      OnPaths L k (.app (.val (.lam B)) (.var k))

theorem OnPaths.mono {L L' : Nat → Expr → Prop} (hL : ∀ k e, L k e → L' k e) {k : Nat} {e : Expr}
    (h : OnPaths L k e) : OnPaths L' k e := by
  induction h with
  | leaf h => exact .leaf (hL _ _ h)
  | case he _ _ ih₁ ih₂ => exact .case he ih₁ ih₂
  | letpair he _ ih => exact .letpair he ih
  | seq he _ ih => exact .seq he ih
  | bind he _ ih => exact .bind he ih
  | rebind hB _ ih => exact .rebind hB ih

/-! ### Leaves -/

/-- A resume of `κ` in tail position, `κ.1 N`, its answer `N` computed without `κ`; or such a
resume under the right unit, `let x = κ.1 N in return x` (`Returns0`). -/
inductive TailLeaf : Nat → Expr → Prop where
  | resume {k : Nat} {N : Expr} : mentions k N = false → TailLeaf k (.app (resumeAt k) N)
  | ret {k : Nat} {X R₀ : Expr} : TailLeaf k X → Returns0 R₀ →
      TailLeaf k (.app (.val (.lam R₀)) X)

/-- A cancel of `κ`, then the rest `N` without `κ`: `let _ = κ.2 in N`. -/
def CancelLeaf (k : Nat) (e : Expr) : Prop :=
  ∃ N, e = .app (.val (.lam N)) (cancelAt k) ∧ mentions (k + 1) N = false

/-- `T` applies the state function in the slot `g` to the new state, in tail position: after
work that uses neither it nor `κ` (the slot `k`), the call `g s`, then its answer returned
(`Returns0`). -/
inductive AppliesAt : Nat → Nat → Expr → Prop where
  | apply {g k : Nat} {s : Expr} : mentions g s = false → mentions k s = false →
      AppliesAt g k (.app (.var g) s)
  | bind {g k : Nat} {e T : Expr} : mentions g e = false → mentions k e = false →
      AppliesAt (g + 1) (k + 1) T → AppliesAt g k (.app (.val (.lam T)) e)
  | ret {g k : Nat} {X R : Expr} : AppliesAt g k X → Returns0 R →
      AppliesAt g k (.app (.val (.lam R)) X)

/-- The state-passing resume in tail position: `let g = κ.1 N in T`, `T` applying `g` to the new
state (`AppliesAt`), `N` without `κ`. -/
def StateLeaf (k : Nat) (e : Expr) : Prop :=
  ∃ N T, e = .app (.val (.lam T)) (.app (resumeAt k) N) ∧ mentions k N = false ∧
    AppliesAt 0 (k + 1) T

/-- The clause answers the state-passing function `λs. S`, whose paths end in `L`. -/
def StateFn (L : Nat → Expr → Prop) (k : Nat) (e : Expr) : Prop :=
  ∃ S, e = .val (.lam S) ∧ OnPaths L (k + 1) S

/-- `κ` used once, by a resume or a cancel in evaluation position, never under a `λ`: the resume
or the cancel itself, or the bound computation of a `let` whose body does not use `κ`. -/
inductive Once : Nat → Expr → Prop where
  | resume {k : Nat} {N : Expr} : mentions k N = false → Once k (.app (resumeAt k) N)
  | cancel {k : Nat} : Once k (cancelAt k)
  | head {k : Nat} {M N : Expr} : Once k M → mentions (k + 1) N = false →
      Once k (.app (.val (.lam N)) M)

/-! ### Tail-resumptive -/

/-- A term that answers its variable `0` mentions no other. -/
theorem Returns0.mentions_succ {R : Expr} (h : Returns0 R) : ∀ j, mentions (j + 1) R = false := by
  induction h with
  | var => intro j; simp [mentions]
  | bind _ ih => intro j; simp [mentions, ih]

/-- A closed value mentions no variable. -/
theorem mentions_closed : ∀ (e : Expr) {c : Nat}, closedAt c e = true → ∀ j, c ≤ j →
    mentions j e = false
  | .var i, _, h, j, hj => by simp only [closedAt, decide_eq_true_eq] at h; simp [mentions]; omega
  | .unit, _, _, _, _ | .loc _, _, _, _, _ | .prim _, _, _, _, _ => rfl
  | .pair a b, _, h, j, hj | .seq a b, _, h, j, hj | .app a b, _, h, j, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp [mentions, mentions_closed a h.1 j hj, mentions_closed b h.2 j hj]
  | .inj₁ a, _, h, j, hj | .inj₂ a, _, h, j, hj => mentions_closed a h j hj
  | .lam b, _, h, j, hj => mentions_closed b h (j + 1) (by omega)
  | .letpair a b, _, h, j, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp [mentions, mentions_closed a h.1 j hj, mentions_closed b h.2 (j + 2) (by omega)]
  | .case e a b, _, h, j, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp [mentions, mentions_closed e h.1.1 j hj, mentions_closed a h.1.2 (j + 1) (by omega),
        mentions_closed b h.2 (j + 1) (by omega)]

/-- A substitution of a closed value below `j` takes the mentions of `j + 1` to `j`. -/
theorem mentions_subst_closed {v : Val} (hv : closedAt 0 v.1 = true) :
    ∀ (e : Expr) (c j : Nat), c ≤ j → mentions (j + 1) e = false → mentions j (e.subst c v) = false
  | .var i, c, j, hj, h => by
      simp only [mentions, beq_eq_false_iff_ne, ne_eq] at h
      simp only [Expr.subst]
      split
      · exact mentions_closed v.1 hv j (Nat.zero_le _)
      · split <;> simp [mentions] <;> omega
  | .unit, _, _, _, _ | .loc _, _, _, _, _ | .prim _, _, _, _, _ => rfl
  | .pair a b, c, j, hj, h | .seq a b, c, j, hj, h | .app a b, c, j, hj, h => by
      simp only [mentions, Bool.or_eq_false_iff] at h
      simp [Expr.subst, mentions, mentions_subst_closed hv a c j hj h.1,
        mentions_subst_closed hv b c j hj h.2]
  | .inj₁ a, c, j, hj, h | .inj₂ a, c, j, hj, h => by
      simp only [mentions] at h
      simp [Expr.subst, mentions, mentions_subst_closed hv a c j hj h]
  | .lam b, c, j, hj, h => by
      simp only [mentions] at h
      simp only [Expr.subst, mentions, val_shift_closed hv]
      exact mentions_subst_closed hv b (c + 1) (j + 1) (by omega) h
  | .letpair a b, c, j, hj, h => by
      simp only [mentions, Bool.or_eq_false_iff] at h
      simp only [Expr.subst, mentions, val_shift_closed hv, Bool.or_eq_false_iff]
      exact ⟨mentions_subst_closed hv a c j hj h.1,
        mentions_subst_closed hv b (c + 2) (j + 2) (by omega) h.2⟩
  | .case e a b, c, j, hj, h => by
      simp only [mentions, Bool.or_eq_false_iff] at h
      simp only [Expr.subst, mentions, val_shift_closed hv, Bool.or_eq_false_iff]
      exact ⟨⟨mentions_subst_closed hv e c j hj h.1.1,
        mentions_subst_closed hv a (c + 1) (j + 1) (by omega) h.1.2⟩,
        mentions_subst_closed hv b (c + 1) (j + 1) (by omega) h.2⟩

/-- A substitution for a variable a term does not mention does not depend on the value. -/
theorem subst_unmentioned : ∀ (e : Expr) (j : Nat) (v w : Val), mentions j e = false →
    e.subst j v = e.subst j w
  | .var i, j, v, w, h => by
      simp only [mentions, beq_eq_false_iff_ne, ne_eq] at h
      simp [Expr.subst, h]
  | .unit, _, _, _, _ | .loc _, _, _, _, _ | .prim _, _, _, _, _ => rfl
  | .pair a b, j, v, w, h | .seq a b, j, v, w, h | .app a b, j, v, w, h => by
      simp only [mentions, Bool.or_eq_false_iff] at h
      simp [Expr.subst, subst_unmentioned a j v w h.1, subst_unmentioned b j v w h.2]
  | .inj₁ a, j, v, w, h | .inj₂ a, j, v, w, h => by
      simp only [mentions] at h
      simp [Expr.subst, subst_unmentioned a j v w h]
  | .lam b, j, v, w, h => by
      simp only [mentions] at h
      simp [Expr.subst, subst_unmentioned b (j + 1) (v.shift 1 0) (w.shift 1 0) h]
  | .letpair a b, j, v, w, h => by
      simp only [mentions, Bool.or_eq_false_iff] at h
      simp [Expr.subst, subst_unmentioned a j v w h.1,
        subst_unmentioned b (j + 2) (v.shift 2 0) (w.shift 2 0) h.2]
  | .case e a b, j, v, w, h => by
      simp only [mentions, Bool.or_eq_false_iff] at h
      simp [Expr.subst, subst_unmentioned e j v w h.1.1,
        subst_unmentioned a (j + 1) (v.shift 1 0) (w.shift 1 0) h.1.2,
        subst_unmentioned b (j + 1) (v.shift 1 0) (w.shift 1 0) h.2]

/-- `B` resumes `κ`, in the slot `k`, on every path, in tail position, and uses it nowhere else;
`B'` is `B` with each resume `κ.1 N` replaced by its answer `N`. On the way: the arms of a `case`,
the body of a `let (x, y)`, a sequence, a `let x = e` with `e` not using `κ`, the right unit
`(λx. R₀) X`, `R₀` answering `x`, whose frame `B'` drops, and an alias `(λk'. B) κ`, `B` resuming
`k'` and not using `κ`, whose binding `B'` drops. -/
inductive TailResumesAt : Nat → Expr → Expr → Prop where
  | resume {k : Nat} {N : Expr} : mentions k N = false →
      TailResumesAt k (.app (resumeAt k) N) N
  | case {k : Nat} {e B₁ B₂ B₁' B₂' : Expr} : mentions k e = false →
      TailResumesAt (k + 1) B₁ B₁' → TailResumesAt (k + 1) B₂ B₂' →
      TailResumesAt k (.case e B₁ B₂) (.case e B₁' B₂')
  | letpair {k : Nat} {e B B' : Expr} : mentions k e = false → TailResumesAt (k + 2) B B' →
      TailResumesAt k (.letpair e B) (.letpair e B')
  | seq {k : Nat} {e B B' : Expr} : mentions k e = false → TailResumesAt k B B' →
      TailResumesAt k (.seq e B) (.seq e B')
  | bind {k : Nat} {e B B' : Expr} : mentions k e = false → TailResumesAt (k + 1) B B' →
      TailResumesAt k (.app (.val (.lam B)) e) (.app (.val (.lam B')) e)
  | ret {k : Nat} {X X' R₀ : Expr} : TailResumesAt k X X' → Returns0 R₀ →
      TailResumesAt k (.app (.val (.lam R₀)) X) X'
  | rebind {k : Nat} {B B' : Expr} : mentions (k + 1) B = false → TailResumesAt 0 B B' →
      TailResumesAt k (.app (.val (.lam B)) (.var k)) (B'.subst 0 .unit)

/-- A tail leaf is tail-resumptive, with its answer. -/
theorem TailLeaf.tailResumes {k : Nat} {e : Expr} (h : TailLeaf k e) : ∃ e', TailResumesAt k e e' := by
  induction h with
  | resume hN => exact ⟨_, .resume hN⟩
  | ret _ h₀ ih => obtain ⟨X', h⟩ := ih; exact ⟨X', .ret h h₀⟩

/-- Every path ending in a tail resume is a `TailResumesAt`, with the clause without its
resumes. -/
theorem OnPaths.tailResumes {k : Nat} {B : Expr} (h : OnPaths TailLeaf k B) :
    ∃ B', TailResumesAt k B B' := by
  induction h with
  | leaf h => exact h.tailResumes
  | case he _ _ ih₁ ih₂ =>
      obtain ⟨B₁', h₁⟩ := ih₁; obtain ⟨B₂', h₂⟩ := ih₂; exact ⟨_, .case he h₁ h₂⟩
  | letpair he _ ih => obtain ⟨B', h⟩ := ih; exact ⟨_, .letpair he h⟩
  | seq he _ ih => obtain ⟨B', h⟩ := ih; exact ⟨_, .seq he h⟩
  | bind he _ ih => obtain ⟨B', h⟩ := ih; exact ⟨_, .bind he h⟩
  | rebind hB _ ih => obtain ⟨B', h⟩ := ih; exact ⟨_, .rebind hB h⟩

/-- The clause without its resumes mentions no variable the clause does not. -/
theorem TailResumesAt.mentions_le {k : Nat} {B B' : Expr} (h : TailResumesAt k B B') :
    ∀ j, mentions j B = false → mentions j B' = false := by
  induction h with
  | resume _ =>
      intro j hj; simp only [mentions, Bool.or_eq_false_iff] at hj; exact hj.2
  | case _ _ _ ih₁ ih₂ =>
      intro j hj; simp only [mentions, Bool.or_eq_false_iff] at hj ⊢
      exact ⟨⟨hj.1.1, ih₁ _ hj.1.2⟩, ih₂ _ hj.2⟩
  | letpair _ _ ih =>
      intro j hj; simp only [mentions, Bool.or_eq_false_iff] at hj ⊢; exact ⟨hj.1, ih _ hj.2⟩
  | seq _ _ ih =>
      intro j hj; simp only [mentions, Bool.or_eq_false_iff] at hj ⊢; exact ⟨hj.1, ih _ hj.2⟩
  | bind _ _ ih =>
      intro j hj
      simp only [mentions, Expr.val, Val.lam, Bool.or_eq_false_iff] at hj ⊢
      exact ⟨ih _ hj.1, hj.2⟩
  | ret _ _ ih =>
      intro j hj
      simp only [mentions, Expr.val, Val.lam, Bool.or_eq_false_iff] at hj
      exact ih _ hj.2
  | rebind _ _ ih =>
      intro j hj
      simp only [mentions, Expr.val, Val.lam, Bool.or_eq_false_iff] at hj
      exact mentions_subst_closed (v := .unit) rfl _ 0 j (Nat.zero_le _) (ih _ hj.1)

/-- **The clause without its resumes does not use `κ`.** -/
theorem TailResumesAt.kappa_free {k : Nat} {B B' : Expr} (h : TailResumesAt k B B') :
    mentions k B' = false := by
  induction h with
  | resume hN => exact hN
  | case he _ _ ih₁ ih₂ => simp [mentions, he, ih₁, ih₂]
  | letpair he _ ih => simp [mentions, he, ih]
  | seq he _ ih => simp [mentions, he, ih]
  | bind he _ ih => simp [mentions, he, ih, Expr.val, Val.lam]
  | ret _ _ ih => exact ih
  | rebind hB h _ =>
      exact mentions_subst_closed (v := .unit) rfl _ 0 _ (Nat.zero_le _) (h.mentions_le _ hB)

/-- **Closing `κ` gives the premise of `tail_resumes`.** With the continuation `κ`, a closed
value, for its slot, the clause resumes with `κ.1` on every path, in tail position. -/
theorem TailResumesAt.subst_kappa {k : Nat} {B B' : Expr} (h : TailResumesAt k B B') {κ : Val}
    (hκ : closedAt 0 κ.1 = true) : TailResumes (resumeOf κ) (B.subst k κ) (B'.subst k κ) := by
  have hR : closedAt 0 (resumeOf κ) = true := closedAt_resumeOf hκ
  induction h with
  | @resume k N _ =>
      have : (Expr.app (resumeAt k) N).subst k κ = .app (resumeOf κ) (N.subst k κ) := by
        simp [resumeAt, resumeOf, Expr.subst, Expr.val, Val.inj₁, Val.unit]
      rw [this]; exact .resume _
  | case _ _ _ ih₁ ih₂ =>
      simp only [Expr.subst, val_shift_closed hκ]; exact .case _ ih₁ ih₂
  | letpair _ _ ih => simp only [Expr.subst, val_shift_closed hκ]; exact .letpair _ ih
  | seq _ _ ih => simp only [Expr.subst]; exact .seq _ ih
  | bind _ _ ih =>
      simp only [Expr.subst, Expr.val, Val.lam, val_shift_closed hκ]; exact .bind _ ih
  | ret _ h₀ ih =>
      have := TailResumes.ret ih h₀
      simpa only [Expr.subst, Expr.val, Val.lam, h₀.subst_succ] using this
  | @rebind k B B' _ hBB ih =>
      -- `(λk'. B) κ` is the `β`-step to `B[κ/k'][κ/κ]`, whose resumes are those of `B[κ/k']`.
      have h₁ := (ih.subst hR k κ)
      have hc := subst_comm_closed hκ B 0 k κ
      simp only [Nat.add_zero, val_shift_closed hκ] at hc
      rw [← hc, subst_unmentioned B' 0 κ .unit hBB.kappa_free] at h₁
      have := TailResumes.beta (R := resumeOf κ) κ hκ h₁
      simpa only [Expr.subst, Expr.val, Val.lam, val_shift_closed hκ, if_true] using this

/-! ### The kinds -/

/-- The kind of an operation's clause at a handler, as the checker classifies it at `[handle]`
from the clause's typed term (`Frontend/Check/Kinds.lean`). Each kind but the last names the
premise of the law its rewrite applies (`Premise`); a clause that matches none of them may keep
`κ`, and is left to the state machines.  `[spec §19]` -/
inductive ClauseKind where
  /-- An abortive operation: the clause takes the argument alone, with no `κ`. -/
  | abortive
  /-- Tail-resumptive on every path (`TailResumesAt`). -/
  | tail
  /-- Tail-resumptive with handler state: the clause answers `λs. S`, every path of `S` resuming
  and applying the answer to the new state in tail position (`StateLeaf`). -/
  | tailState
  /-- Each path resumes in tail position or cancels `κ` and goes on without it. -/
  | resumeOrCancel (state : Bool)
  /-- Each path resumes or cancels `κ` once, not all in tail position, and never stores it. -/
  | resumeOnce (state : Bool)
  /-- Anything else: `κ` may be kept. -/
  | stored
  /-- `[handle-last]`'s clause (§51), written by its rule: the work, then a resume of `κ` in tail
  position or `κ`'s cancel and the exit, `κ`'s cancel the work's finaliser (`lastClause`). -/
  | last
  deriving DecidableEq, Repr, Inhabited

/-- An operation's clause at a handler: the operation's qualifier and the clause's kind. -/
structure HKind where
  q : Qual
  kind : ClauseKind
  deriving DecidableEq, Repr

instance : Inhabited HKind := ⟨⟨.lin, .stored⟩⟩

/-- The kind's premise on the body `M` of the clause `λp. let (x, κ) = p; M`, `κ` in the slot
`0` of `M`. -/
def ClauseKind.BodyPremise : ClauseKind → Expr → Prop
  | .abortive, _ => True
  | .tail, M => ∃ M', TailResumesAt 0 M M'
  | .tailState, M => OnPaths (StateFn StateLeaf) 0 M
  | .resumeOrCancel false, M => OnPaths (fun k e => TailLeaf k e ∨ CancelLeaf k e) 0 M
  | .resumeOrCancel true, M =>
      OnPaths (StateFn (fun k e => StateLeaf k e ∨ CancelLeaf k e)) 0 M
  | .resumeOnce false, M => OnPaths Once 0 M
  | .resumeOnce true, M => OnPaths (StateFn Once) 0 M
  | .stored, _ => True
  | .last, M => ∃ j Hw Hn, Expr.lam (.letpair (.var 0) M) = lastClause j false Hw Hn

/-- Whether the operation `o = A ↠^q B` is abortive: its clause takes no `κ` (`clauseTy`). -/
def isAbortive (o : Qual × VTy × VTy) : Bool := o.2.2.isZero && o.1 != .lin

/-- **The premise of the kind's law**, for the operation `o` and its clause `c` (erased). An
abortive operation's clause takes its argument alone (`clauseTy_abortive`); a control clause is
`λp. let (x, κ) = p; M` with `M`'s premise. -/
def ClauseKind.Premise : ClauseKind → (Qual × VTy × VTy) → Expr → Prop
  | .abortive, o, _ => isAbortive o = true
  | .stored, _, _ => True
  | k, o, c => isAbortive o = false ∧
      ∃ M, c = .val (.lam (.letpair (.var 0) M)) ∧ k.BodyPremise M

/-- An abortive operation's clause type has no `κ`: `!U(A ⊸ F_Σ R)`. -/
theorem clauseTy_abortive {S : Row} {R : VTy} {o : Qual × VTy × VTy} {F : CTy}
    (h : isAbortive o = true) : clauseTy S R o F = .bang (.thunk (.arr o.2.1 (CTy.effOf S R))) := by
  obtain ⟨q, A, B⟩ := o
  simp only [isAbortive] at h
  simp [clauseTy, h]

/-- A control operation's clause type takes `κ`: `!U(A ⊗ K ⊸ F_Σ R)`. -/
theorem clauseTy_control {S : Row} {R : VTy} {o : Qual × VTy × VTy} {F : CTy}
    (h : isAbortive o = false) :
    clauseTy S R o F = .bang (.thunk (.arr (.tensor o.2.1 (kTy S R o.1 o.2.2 F)) (CTy.effOf S R))) := by
  obtain ⟨q, A, B⟩ := o
  simp only [isAbortive] at h
  simp [clauseTy, h]

/-! ### The clauses of `effHandleT` -/

/-- The kind `effHandleT` gives an operation by its rule (§14, decision 68): its clauses are
written out from answering functions (`tailClause`), each resuming `κ` in tail position. -/
def tailKind (o : Qual × VTy × VTy) : HKind :=
  ⟨o.1, if isAbortive o then .abortive else .tail⟩

theorem mentions_shift {d c k : Nat} (hk : c ≤ k) (hd : k < c + d) :
    ∀ e : Expr, mentions k (e.shift d c) = false := by
  intro e
  induction e generalizing c k with
  | var i =>
      simp only [Expr.shift]
      split <;> simp [mentions] <;> omega
  | lam b ih => simp only [Expr.shift, mentions]; exact ih (c := c + 1) (k := k + 1) (by omega) (by omega)
  | letpair a b iha ihb =>
      simp only [Expr.shift, mentions, iha hk hd, ihb (c := c + 2) (k := k + 2) (by omega) (by omega)]; rfl
  | case e a b ihe iha ihb =>
      simp only [Expr.shift, mentions, ihe hk hd, iha (c := c + 1) (k := k + 1) (by omega) (by omega),
        ihb (c := c + 1) (k := k + 1) (by omega) (by omega)]; rfl
  | pair a b iha ihb | seq a b iha ihb | app a b iha ihb =>
      simp only [Expr.shift, mentions, iha hk hd, ihb hk hd]; rfl
  | inj₁ a ih | inj₂ a ih => simp only [Expr.shift, mentions, ih hk hd]
  | unit | loc _ | prim _ => rfl

theorem mentions_pickE : ∀ (j : Nat) {k : Nat} {t : Expr}, mentions k t = false →
    mentions k (pickE j t) = false
  | 0, k, t, h => by simp [pickE, mentions, h]
  | j + 1, k, t, h => by
      simp only [pickE, mentions, h, Bool.false_or]
      exact mentions_pickE j (by simp [mentions])

/-- **`effHandleT`'s clauses are tail-resumptive**: the clause of a control operation written
out from an answering function, `λ(x, κ). (λw. κ.1 w) (g x)`, meets the `tail` kind's premise,
and an abortive one the `abortive` kind's. So the rule's class is an instance of `tail`, the one
definition of tail-resumptive.  `[spec §14, §19]` -/
theorem tailClause_premise (o : Qual × VTy × VTy) (j : Nat) (Hc : Expr) :
    (tailKind o).kind.Premise o (tailClause j (isAbortive o) Hc) := by
  unfold tailKind
  cases ha : isAbortive o
  · simp only [Bool.false_eq_true, if_false]
    refine ⟨ha, _, rfl, _, .bind ?_ (.resume (by simp [mentions]))⟩
    simp only [mentions, Bool.or_eq_false_iff]
    exact ⟨mentions_pickE j (mentions_shift (by omega) (by omega) Hc), by simp⟩
  · simp only [if_true]; exact ha

/-! ### The clauses of `effHandleL` -/

/-- The kind `effHandleL` gives an operation by its rule (§51): its clauses are written out from
works and exits (`lastClause`). -/
def lastKind (o : Qual × VTy × VTy) : HKind :=
  ⟨o.1, if isAbortive o then .abortive else .last⟩

/-- **`effHandleL`'s clauses are of the `last` kind**: the clause of a control operation is the
rule's `lastClause`, and an abortive one's is `effHandleT`'s, of the `abortive` kind.
`[spec §51, §64]` -/
theorem lastClause_premise (o : Qual × VTy × VTy) (j : Nat) (Hw Hn : Expr) :
    (lastKind o).kind.Premise o (lastClause j (isAbortive o) Hw Hn) := by
  unfold lastKind
  cases ha : isAbortive o
  · simp only [Bool.false_eq_true, if_false]
    exact ⟨ha, _, rfl, j, Hw, Hn, rfl⟩
  · simp only [if_true]; exact ha

end BoCa.Fig16.LogRel.Core.ClauseKinds
