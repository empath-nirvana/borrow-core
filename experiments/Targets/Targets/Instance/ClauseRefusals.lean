import Targets.Instance.ContUse

/-!
# The Instance — today's clause typing refuses R1–R4's clauses

RESTRUCTURE §6.1 names the reason today's kernel refuses S6's witnesses: `κ`'s type `kTy` at
`lin` and `aff` is a thunk, neither droppable nor persistent, and a linear `κ`'s cancel branch is
at `⊤`.  Today's kernel types no A-level handler (`refuses_R_tier1Open`), so that reason is read
here at the clauses themselves: `[handle]` types a clause at `clauseTy`, and at a resuming
operation that is `!U(A ⊗ kTy ⊸ F_Σ R)`.

* R1's clause drops `κ`, R2's and R4's use it twice: refused at every resuming `lin` or `aff`
  operation, since a live slot of `kTy` is neither dropped nor duplicated (`refuses_dropClause`,
  `refuses_twiceClause`, `refuses_cancelResumeClause`).
* R3's clause cancels `κ`: refused at every `lin` operation, since `κ (inj₂ ())` is at `⊤`, which
  no bind takes (`refuses_cancelClause_lin`).

The inversions, each one induction over `CDerivesNU` (CLAUDE.md asks for the cost):

* `der_free_live`: a variable that occurs free in a typed term is a live slot of its context;
* `der_lam_arr`: a λ read as a function of `P` into `C` has its body typed under a live slot of
  `P`, at `C` up to `ν`;
* `der_letpair_split`, `der_var_tensor`: `let (x, y) = z in X` splits the context, and `z`, read
  at a tensor, has its slot's tensor;
* `der_unit_dead`: `()` and `inj₁ ()` at a judgement that is not `⊤`'s consume their context;
* `der_appLam_split`: `M to x. N` splits the context between `M` and `N`;
* `der_cancel_lin`: `k (inj₂ ())` at a live slot of a linear `kTy` is at `⊤` only.

**The refusals pin `κ`'s use** (`clauseRefusals_pinned`): at the clause type of a linear `1 ↠ 1`,
where all four clauses are refused, a clause that resumes `κ` once is typed, and `cancelCl`, which
cancels `κ`, is typed at `aff` and refused at `lin`.

**Scope.**  `unr` is outside: there `kTy` is `!`, persistent, and the argument does not apply
(multi-shot is not considered).  `clsOf` reads a resuming `unr` operation as affine.
-/

noncomputable section

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx)
open Targets (CDerivesNU)

/-! ### Free variables -/

/-- The variable `i` occurs free in `e`. -/
def _root_.BoCa.Expr.FreeIn : Expr → ℕ → Prop
  | .var j, i => j = i
  | .unit, _ | .loc _, _ | .prim _, _ => False
  | .pair a b, i | .seq a b, i | .app a b, i => a.FreeIn i ∨ b.FreeIn i
  | .inj₁ a, i | .inj₂ a, i => a.FreeIn i
  | .lam b, i => b.FreeIn (i + 1)
  | .letpair a b, i => a.FreeIn i ∨ b.FreeIn (i + 2)
  | .case a b c, i => a.FreeIn i ∨ b.FreeIn (i + 1) ∨ c.FreeIn (i + 1)

theorem not_freeIn_of_closedAt : ∀ (e : Expr) {k i : ℕ}, closedAt k e = true → k ≤ i →
    ¬ e.FreeIn i
  | .var j, k, i, h, hk => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [Expr.FreeIn]
      omega
  | .unit, _, _, _, _ | .loc _, _, _, _, _ | .prim _, _, _, _, _ => by simp [Expr.FreeIn]
  | .pair a b, k, i, h, hk | .seq a b, k, i, h, hk | .app a b, k, i, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.FreeIn, not_or]
      exact ⟨not_freeIn_of_closedAt a h.1 hk, not_freeIn_of_closedAt b h.2 hk⟩
  | .inj₁ a, k, i, h, hk | .inj₂ a, k, i, h, hk => by
      simp only [closedAt] at h
      exact not_freeIn_of_closedAt a h hk
  | .lam b, k, i, h, hk => by
      simp only [closedAt] at h
      exact not_freeIn_of_closedAt b h (by omega)
  | .letpair a b, k, i, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.FreeIn, not_or]
      exact ⟨not_freeIn_of_closedAt a h.1 hk, not_freeIn_of_closedAt b h.2 (by omega)⟩
  | .case a b c, k, i, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.FreeIn, not_or]
      exact ⟨not_freeIn_of_closedAt a h.1.1 hk, not_freeIn_of_closedAt b h.1.2 (by omega),
        not_freeIn_of_closedAt c h.2 (by omega)⟩

/-- Live slots of a context. -/
abbrev LiveAt (Γ : Ctx VTy) (i : ℕ) : Prop := ∃ T, Γ[i]? = some ⟨T, true⟩

theorem liveAt_of_split_left {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) {i : ℕ}
    (hi : LiveAt Γ₁ i) : LiveAt Γ i := by
  obtain ⟨T, hT⟩ := hi
  exact ⟨T, splitP_live_left h hT⟩

theorem liveAt_of_split_right {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) {i : ℕ}
    (hi : LiveAt Γ₂ i) : LiveAt Γ i := by
  obtain ⟨T, hT⟩ := hi
  exact ⟨T, splitP_live_right h hT⟩

theorem liveAt_cons {s : Slot VTy} {Γ : Ctx VTy} {i : ℕ} (h : LiveAt (s :: Γ) (i + 1)) :
    LiveAt Γ i := by
  simpa [LiveAt] using h

theorem liveAt_of_soloP {Γ : Ctx VTy} {j : ℕ} {A : VTy} (h : Ctx.SoloP Γ j A) : LiveAt Γ j :=
  ⟨A, soloP_slot h⟩

theorem not_liveAt_deadP {Γ : Ctx VTy} (h : Ctx.DeadP Γ) {i : ℕ} {T : VTy}
    (hi : Γ[i]? = some ⟨T, true⟩) : T.Persistent := by
  induction h generalizing i with
  | nil => simp at hi
  | cons _ ih =>
      cases i with
      | zero => simp at hi
      | succ i => exact ih (by simpa using hi)
  | drop hT _ ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hi
          obtain ⟨rfl, -⟩ := hi
          exact hT
      | succ i => exact ih (by simpa using hi)

theorem freeIn_val_lam {b : Expr} {i : ℕ} : (Expr.val (Val.lam b)).FreeIn i ↔ b.FreeIn (i + 1) :=
  Iff.rfl

/-- A closed term has no free variable. -/
theorem not_freeIn_closed {e : Expr} (h : closedAt 0 e = true) (i : ℕ) : ¬ e.FreeIn i :=
  not_freeIn_of_closedAt e h (Nat.zero_le i)

/-- **A variable that occurs free in a typed term is a live slot of its context.**  One induction
over `CDerivesNU`: a rule's context goes to its premises through splits, which only turn
liveness off, and binders, which shift it; a constant's term is closed. -/
theorem der_free_live {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ i, e.FreeIn i → LiveAt Γ i := by
  induction h with
  | var h =>
      intro i hi
      simp only [Expr.FreeIn] at hi
      subst hi
      exact liveAt_of_soloP h
  | tensorI hs _ _ ih₁ ih₂ =>
      intro i hi
      rcases hi with hi | hi
      · exact liveAt_of_split_left hs (ih₁ i hi)
      · exact liveAt_of_split_right hs (ih₂ i hi)
  | sumI₁ _ ih | sumI₂ _ ih => exact ih
  | thunkF _ ih | lam _ ih | allI _ _ _ _ ih | bangThunkF _ _ ih =>
      intro i hi
      exact liveAt_cons (ih (i + 1) hi)
  | thunkV _ _ ih | ret _ ih | bangThunkV _ _ _ ih | bangE _ ih | boxI _ _ ih | boxE _ ih
  | immSub _ _ ih | mutSub _ _ ih | ofRet _ ih | roll _ _ _ ih | unroll _ ih | nuIn _ _ ih
  | nuOut _ _ ih | effSub _ _ _ ih => exact ih
  | bind hs _ _ ihM ihN | effLet _ hs _ _ _ _ ihM ihN =>
      intro i hi
      rcases hi with hi | hi
      · exact liveAt_of_split_right hs (liveAt_cons (ihN (i + 1) hi))
      · exact liveAt_of_split_left hs (ihM i hi)
  | force h =>
      rename_i i' C
      intro i hi
      rcases forceE_cases C (.var i') with he | he <;> rw [he] at hi
      · simp only [Expr.FreeIn] at hi; subst hi; exact liveAt_of_soloP h
      · rcases hi with hi | hi
        · simp only [Expr.FreeIn] at hi; subst hi; exact liveAt_of_soloP h
        · simp [Expr.FreeIn, Expr.val, Val.unit] at hi
  | app hs _ hx ihM =>
      intro i hi
      rcases hi with hi | hi
      · exact liveAt_of_split_left hs (ihM i hi)
      · simp only [Expr.FreeIn] at hi; subst hi; exact liveAt_of_split_right hs (liveAt_of_soloP hx)
  | withI _ _ ihM ihN =>
      intro i hi
      simp only [withPair, Expr.val, Val.lam, Expr.FreeIn] at hi
      rcases hi with hi | (hi | hi) | (hi | hi)
      · omega
      · omega
      · exact liveAt_cons (liveAt_cons (ihM (i + 2) (by simpa [Nat.add_assoc] using hi)))
      · omega
      · exact liveAt_cons (liveAt_cons (ihN (i + 2) (by simpa [Nat.add_assoc] using hi)))
  | proj₁ _ ih | proj₂ _ ih | allE _ _ ih | allEV _ _ ih =>
      intro i hi
      rcases hi with hi | hi
      · exact ih i hi
      · simp [Expr.FreeIn, Expr.val, Val.inj₁, Val.inj₂, Val.unit] at hi
  | unitE hs _ _ ihV ihM =>
      intro i hi
      rcases hi with hi | hi
      · exact liveAt_of_split_left hs (ihV i hi)
      · exact liveAt_of_split_right hs (ihM i hi)
  | tensorE hs _ _ ihV ihM =>
      intro i hi
      rcases hi with hi | hi
      · exact liveAt_of_split_left hs (ihV i hi)
      · exact liveAt_of_split_right hs (liveAt_cons (liveAt_cons (ihM (i + 2) hi)))
  | sumE hs _ _ _ ihV ih₁ ih₂ =>
      intro i hi
      rcases hi with hi | hi | hi
      · exact liveAt_of_split_left hs (ihV i hi)
      · exact liveAt_of_split_right hs (liveAt_cons (ih₁ (i + 1) hi))
      · exact liveAt_of_split_right hs (liveAt_cons (ih₂ (i + 1) hi))
  | zeroE hs _ ihV =>
      intro i hi
      simp only [absurdE, Expr.FreeIn] at hi
      rcases hi with hi | hi | hi
      · exact liveAt_of_split_left hs (ihV i hi)
      · omega
      · omega
  | lolliE hs _ _ iha ihf =>
      intro i hi
      rcases hi with hi | hi
      · exact liveAt_of_split_right hs (ihf i hi)
      · exact liveAt_of_split_left hs (iha i hi)
  | effPerform _ _ _ _ ih | effRaise _ _ _ _ ih =>
      intro i hi
      simp only [BoCa.BoLo.performE, BoCa.BoLo.raiseE, opArgE, Expr.FreeIn, Expr.val, Val.prim,
        Val.i32, false_or] at hi
      exact ih i hi
  | effThen _ hs _ _ _ _ _ _ ihM ihN ihD =>
      intro i hi
      simp only [thenE, Expr.FreeIn, Expr.val, Val.prim, Val.lam, false_or] at hi
      rcases hi with (hi | hi) | hi
      · exact liveAt_of_split_right hs (liveAt_cons (ihN (i + 1) hi))
      · exact liveAt_of_split_right hs (liveAt_cons (ihD (i + 1) hi))
      · exact liveAt_of_split_left hs (ihM i hi)
  | effHandle _ hs hs₁ hr hc _ _ _ _ ihe =>
      intro i hi
      simp only [hndTerm, Expr.FreeIn, Expr.val, Val.prim, Val.i32, false_or] at hi
      rcases hi with (hi | hi) | hi
      · subst hi
        exact liveAt_of_split_left hs (liveAt_of_split_left hs₁ (liveAt_of_soloP hr))
      · subst hi
        exact liveAt_of_split_left hs (liveAt_of_split_right hs₁ (liveAt_of_soloP hc))
      · exact liveAt_of_split_right hs (ihe i hi)
  | withbor1U _ _ _ _ _ _ _ hdc _ _ | withbor2U _ _ _ _ _ _ _ hdc _ _
  | withbor3U _ _ _ _ _ _ hdc _ _ | sliceBorrowMU _ _ _ _ _ _ _ hdc _ _
  | sliceBorrowIU _ _ _ _ _ _ _ _ hdc _ _ =>
      intro i hi
      exact absurd hi (not_freeIn_closed (withborUE_closed hdc) i)
  | foldImm F => intro i hi; exact absurd hi (not_freeIn_closed (foldImmV_closed F) i)
  | foldOwn F => intro i hi; exact absurd hi (not_freeIn_closed (foldOwnV_closed F) i)
  | foldReuse F => intro i hi; exact absurd hi (not_freeIn_closed (foldReuseV_closed F) i)
  | unfoldN C => intro i hi; exact absurd hi (not_freeIn_closed (unfoldV_closed C) i)
  | lit c _ => intro i hi; simp [Expr.FreeIn] at hi
  | hostOp op _ => intro i hi; simp [Expr.FreeIn, Expr.val, Val.prim] at hi
  | _ =>
      intro i hi
      exact absurd hi (not_freeIn_closed (by decide) i)

/-! ### Closed data consumes its context -/

/-- A judgement that is no view of `⊤`: a value judgement, or a computation one that unrolls to a
returner. -/
def NotTopJ : Jdg → Prop
  | .val _ => True
  | .comp D => NuUp (fun D' => ∃ S Y, D' = CTy.effOf S Y) D

theorem notTopJ_nu {C : CTy} (h : NotTopJ (.comp (.nu C))) : NotTopJ (.comp C.unroll) :=
  NuUp.of_nu (fun _ ⟨S, Y, he⟩ => effOf_ne_nu S Y _ he.symm) h

/-- **`()` and `inj₁ ()`, at a judgement that is no view of `⊤`, consume their context**: only
`[1I]` types `()` there, and it asks the context to be consumed; `⟨⟩ : ⊤` is excluded. -/
theorem der_unit_dead {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : (e = .unit ∨ e = .inj₁ .unit) → NotTopJ j → Ctx.DeadP Γ := by
  induction h
  case unitI hΓ => intro _ _; exact hΓ
  case topI =>
    intro _ hj
    have := NuUp.base_of (fun _ h => by cases h) hj
    obtain ⟨S, Y, h⟩ := this
    cases S <;> simp [CTy.effOf] at h
  case sumI₁ ih =>
    intro he _
    rcases he with he | he
    · cases he
    · simp only [Expr.inj₁.injEq] at he
      exact ih (.inl he) trivial
  case sumI₂ =>
    intro he _
    rcases he with he | he <;> cases he
  case ret ih => intro he _; exact ih he trivial
  case ofRet ih => intro he _; exact ih he (.base ⟨[], _, rfl⟩)
  case effSub ih => intro he _; exact ih he (.base ⟨_, _, rfl⟩)
  case nuIn ih => intro he hj; exact ih he (notTopJ_nu hj)
  case nuOut ih => intro he hj; exact ih he (.nu hj)
  case bangE ih => intro he _; exact ih he trivial
  case boxI ih => intro he _; exact ih he trivial
  case boxE ih => intro he _; exact ih he trivial
  case immSub ih => intro he _; exact ih he trivial
  case mutSub ih => intro he _; exact ih he trivial
  case roll ih => intro he _; exact ih he trivial
  case unroll ih => intro he _; exact ih he trivial
  case force =>
    rename_i i C _
    intro he _
    rcases forceE_cases C (.var i) with hf | hf <;> rw [hf] at he <;> simp at he
  all_goals
    intro he _
    rcases he with he | he <;> cdnu_terms

/-! ### A clause's λ -/

/-- The judgements at which a λ-value is read as a function of `P` into `C`: a thunk of `P ⊸ C`
(through `!`, `[a]` and `μ`), the arrow itself up to `ν`, or a returner of such a thunk. -/
def ArrView (P : VTy) (C : CTy) : Jdg → Prop
  | .val Y => ThunkOf Y (.arr P C)
  | .comp D => NuEq D (.arr P C) ∨
      NuUp (fun D' => ∃ S Y, D' = CTy.effOf S Y ∧ ThunkOf Y (.arr P C)) D

/-- The tails of `let (x, y) = z in X` that no constant's λ has: `arrLenV`, `sizeV`, `swapV` and
`replaceV` are λs of `let (x, y) = z in` a variable, a pair or another `let`. -/
def PlainTail (X : Expr) : Prop := (X ≠ .var 0) ∧ (∀ a c, X ≠ .pair a c) ∧ (∀ a c, X ≠ .letpair a c)

theorem arr_ne_nu (P : VTy) (C : CTy) (C' : CTy) : CTy.arr P C ≠ .nu C' := by simp

/-- **A λ read as a function of `P` into `C` has its body typed under a live slot of `P`**, at
`C` up to `ν`, in the same context.  The rules whose premise has the λ itself (`thunkV`,
`bangThunkV`, `ret`, `ofRet`, `[sub]`, `ν`'s two rules, and `!`, `[a]`, `μ`) carry the view; `[⊸I]`
gives the body; every other rule's λ has another body or another type. -/
theorem der_lam_arr {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesNU Δ Γ e j) :
    ∀ (X : Expr) (P : VTy) (C : CTy), e = .lam (.letpair (.var 0) X) → PlainTail X →
      ArrView P C j →
      ∃ C', NuEq C' C ∧ CDerivesNU Δ (⟨P, true⟩ :: Γ) (.letpair (.var 0) X) (.comp C') := by
  induction h
  case lam hM _ =>
    rename_i A₀ C₀
    intro X P C he _ hv
    simp only [Expr.val, Val.lam, Expr.lam.injEq] at he
    subst he
    rcases hv with hv | hv
    · have := NuEq.eq hv (fun _ h => by cases h) (fun _ h => by cases h)
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨_, .refl _, hM⟩
    · obtain ⟨S, Y, h', -⟩ := NuUp.base_of (fun _ h => by cases h) hv
      cases S <;> simp [CTy.effOf] at h'
  case thunkF =>
    intro X P C he _ hv
    cases hv
  case thunkV ih =>
    intro X P C he hX hv
    cases hv
    exact ih X P C he hX (.inl (.refl _))
  case bangThunkF =>
    intro X P C he _ hv
    cases hv with | bang hv => cases hv
  case bangThunkV ih =>
    intro X P C he hX hv
    cases hv with | bang hv => cases hv; exact ih X P C he hX (.inl (.refl _))
  case allI =>
    intro X P C he _ hv
    rcases hv with hv | hv
    · exact absurd (NuEq.eq hv (fun _ h => by cases h) (fun _ h => by cases h)) (by simp)
    · obtain ⟨S, Y, h', -⟩ := NuUp.base_of (fun _ h => by cases h) hv
      cases S <;> simp [CTy.effOf] at h'
  case withI =>
    intro X P C he _ _
    simp [withPair] at he
  case ret ih =>
    intro X P C he hX hv
    rcases hv with hv | hv
    · exact absurd (NuEq.eq hv (fun _ h => by cases h) (fun _ h => by cases h)) (by simp)
    · obtain ⟨S, Y, h', hY⟩ := NuUp.base_of (fun _ h => by cases h) hv
      cases S with
      | nil =>
          simp only [CTy.effOf, CTy.ret.injEq] at h'
          subst h'
          exact ih X P C he hX hY
      | cons o S => simp [CTy.effOf] at h'
  case ofRet ih =>
    intro X P C he hX hv
    exact ih X P C he hX (.inr (.base ⟨[], _, rfl, hv⟩))
  case effSub ih =>
    rename_i S S' A _ _ _
    intro X P C he hX hv
    rcases hv with hv | hv
    · exact absurd (NuEq.eq hv (effOf_ne_nu S' A) (fun _ h => by cases h)) (by
        cases S' <;> simp [CTy.effOf])
    · obtain ⟨S₀, Y, h', hY⟩ := NuUp.base_of (effOf_ne_nu S' A) hv
      obtain ⟨-, rfl⟩ := effOf_inj h'
      exact ih X P C he hX (.inr (.base ⟨S, _, rfl, hY⟩))
  case nuIn ih =>
    rename_i C₀ _ _
    intro X P C he hX hv
    rcases hv with hv | hv
    · exact ih X P C he hX (.inl (.trans _ _ _ (.symm _ _ (NuEq.unroll C₀)) hv))
    · exact ih X P C he hX (.inr (NuUp.of_nu (fun _ ⟨S, Y, h', _⟩ => effOf_ne_nu S Y _ h'.symm) hv))
  case nuOut ih =>
    rename_i C₀ _ _
    intro X P C he hX hv
    rcases hv with hv | hv
    · exact ih X P C he hX (.inl (.trans _ _ _ (NuEq.unroll C₀) hv))
    · exact ih X P C he hX (.inr (.nu hv))
  case bangE ih =>
    intro X P C he hX hv
    exact ih X P C he hX (ThunkOf.bang hv)
  case boxI ih =>
    intro X P C he hX hv
    cases hv with | box hv => exact ih X P C he hX hv
  case boxE ih =>
    intro X P C he hX hv
    exact ih X P C he hX (ThunkOf.box hv)
  case immSub => intro X P C he _ hv; cases hv
  case mutSub => intro X P C he _ hv; cases hv
  case roll ih =>
    intro X P C he hX hv
    cases hv with | mu hv => exact ih X P C he hX hv
  case unroll ih =>
    intro X P C he hX hv
    exact ih X P C he hX (ThunkOf.mu hv)
  case force =>
    rename_i i C₀ _
    intro X P C he _ _
    rcases forceE_cases C₀ (.var i) with hf | hf <;> rw [hf] at he <;> simp at he
  all_goals
    intro X P C he hX _
    obtain ⟨h₁, h₂, h₃⟩ := hX
    cdnu_terms
  all_goals first
    | exact absurd he.symm h₁ | exact absurd he.symm (h₂ _ _) | exact absurd he.symm (h₃ _ _)
    | simp [unit'] at he

/-! ### A clause's `let` -/

theorem notTopJ_of_nuEq {C : CTy} {S : Row} {R : VTy} (h : NuEq C (CTy.effOf S R)) :
    NotTopJ (.comp C) := by
  have hr : NuRoot C (CTy.effOf S R) := (h.root _).mpr (.base (effOf_ne_nu S R))
  clear h
  generalize hE : CTy.effOf S R = E at hr
  induction hr with
  | base _ => exact .base ⟨S, R, hE.symm⟩
  | nu _ ih => exact .nu (ih hE)

/-- **`let (x, y) = z in X` splits the context**: `z` is read in one part, at a tensor, and `X` is
typed in the other under the tensor's two components, at a judgement that is no view of `⊤` when
the `let`'s is not. -/
theorem der_letpair_split {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ (V X : Expr), e = .letpair V X →
      ∃ (Γp Γb : Ctx VTy) (A B : VTy) (C : CTy), Ctx.SplitP Γ Γp Γb ∧
        CDerivesNU Δ Γp V (.val (.tensor A B)) ∧
        CDerivesNU Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) X (.comp C) ∧
        (NotTopJ j → NotTopJ (.comp C)) := by
  induction h
  case tensorE hs hV hM _ _ =>
    intro V X he
    simp only [Expr.letpair.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, _, _, _, _, hs, hV, hM, id⟩
  case ret ih =>
    intro V X he
    obtain ⟨Γp, Γb, A, B, C, hs, hV, hM, hT⟩ := ih V X he
    exact ⟨Γp, Γb, A, B, C, hs, hV, hM, fun _ => hT trivial⟩
  case ofRet ih =>
    intro V X he
    obtain ⟨Γp, Γb, A, B, C, hs, hV, hM, hT⟩ := ih V X he
    exact ⟨Γp, Γb, A, B, C, hs, hV, hM, fun _ => hT (.base ⟨[], _, rfl⟩)⟩
  case effSub ih =>
    intro V X he
    obtain ⟨Γp, Γb, A, B, C, hs, hV, hM, hT⟩ := ih V X he
    exact ⟨Γp, Γb, A, B, C, hs, hV, hM, fun _ => hT (.base ⟨_, _, rfl⟩)⟩
  case nuIn ih =>
    intro V X he
    obtain ⟨Γp, Γb, A, B, C, hs, hV, hM, hT⟩ := ih V X he
    exact ⟨Γp, Γb, A, B, C, hs, hV, hM, fun hj => hT (notTopJ_nu hj)⟩
  case nuOut ih =>
    intro V X he
    obtain ⟨Γp, Γb, A, B, C, hs, hV, hM, hT⟩ := ih V X he
    exact ⟨Γp, Γb, A, B, C, hs, hV, hM, fun hj => hT (.nu hj)⟩
  case bangE ih | boxI ih | boxE ih | immSub ih | mutSub ih | roll ih | unroll ih =>
    intro V X he
    obtain ⟨Γp, Γb, A, B, C, hs, hV, hM, hT⟩ := ih V X he
    exact ⟨Γp, Γb, A, B, C, hs, hV, hM, fun _ => hT trivial⟩
  case force =>
    rename_i i C₀ _
    intro V X he
    rcases forceE_cases C₀ (.var i) with hf | hf <;> rw [hf] at he <;> simp at he
  all_goals intro V X he; cdnu_terms

/-- The views of a slot's type `T` at which a variable is read, when `T` is no thunk, `!`, `Imm`
or `Mut`: `T` itself, boxed, and folded into a `μ`. -/
inductive IsViewOf (T : VTy) : VTy → Prop
  | refl : IsViewOf T T
  | box {a : Lifetime.Life} {Y : VTy} : IsViewOf T Y → IsViewOf T (.box a Y)
  | mu {Z : VTy} : IsViewOf T (VTy.inst (.mu Z) Z) → IsViewOf T (.mu Z)

/-- **A variable whose slot is a tensor is read at that tensor's views.** -/
theorem der_var_tensor {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ (i : ℕ) (P Q : VTy), e = .var i →
      Γ[i]? = some ⟨.tensor P Q, true⟩ →
      match j with
      | .val Y => IsViewOf (.tensor P Q) Y
      | .comp D => NuUp (fun D' => ∃ S Y, D' = CTy.effOf S Y ∧ IsViewOf (.tensor P Q) Y) D := by
  induction h
  case var hs =>
    intro i P Q he hi
    cases he
    rw [soloP_slot hs] at hi
    cases hi
    exact .refl
  case force =>
    rename_i i' C hs
    intro i P Q he hi
    rcases forceE_cases C (.var i') with hf | hf <;> rw [hf] at he
    · cases he
      rw [soloP_slot hs] at hi
      cases hi
    · cases he
  case ret ih => intro i P Q he hi; exact .base ⟨[], _, rfl, ih i P Q he hi⟩
  case ofRet ih =>
    intro i P Q he hi
    have := ih i P Q he hi
    obtain ⟨S, Y, h', hY⟩ := NuUp.base_of (fun _ h => by cases h) this
    obtain ⟨-, rfl⟩ := effOf_inj (S := []) h'
    exact hY
  case effSub ih =>
    rename_i S S' A _ _ _
    intro i P Q he hi
    have := ih i P Q he hi
    obtain ⟨S₀, Y, h', hY⟩ := NuUp.base_of (effOf_ne_nu S A) this
    obtain ⟨-, rfl⟩ := effOf_inj h'
    exact .base ⟨S', _, rfl, hY⟩
  case nuIn ih => intro i P Q he hi; exact .nu (ih i P Q he hi)
  case nuOut ih =>
    intro i P Q he hi
    exact NuUp.of_nu (fun _ ⟨S, Y, h', _⟩ => effOf_ne_nu S Y _ h'.symm) (ih i P Q he hi)
  case bangE ih =>
    intro i P Q he hi
    have := ih i P Q he hi
    cases this
  case boxI ih => intro i P Q he hi; exact .box (ih i P Q he hi)
  case boxE ih =>
    intro i P Q he hi
    have := ih i P Q he hi
    cases this with | box h => exact h
  case immSub ih => intro i P Q he hi; have := ih i P Q he hi; cases this
  case mutSub ih => intro i P Q he hi; have := ih i P Q he hi; cases this
  case roll ih => intro i P Q he hi; exact .mu (ih i P Q he hi)
  case unroll ih =>
    intro i P Q he hi
    have := ih i P Q he hi
    cases this with | mu h => exact h
  all_goals intro i P Q he hi; cdnu_terms

theorem isViewOf_tensor {P Q A B : VTy} (h : IsViewOf (.tensor P Q) (.tensor A B)) :
    A = P ∧ B = Q := by
  cases h
  exact ⟨rfl, rfl⟩

/-! ### A clause's bind -/

/-- An argument that no rule other than `[bind]`, `[let]` and `[⊸E]` reads at an application of
a λ: not a variable (`[app]`), nor `inj₁ ()`, `inj₂ ()` (`&`'s projections), nor `()` (`∀E`). -/
def PlainArg (M : Expr) : Prop :=
  (∀ i, M ≠ .var i) ∧ M ≠ .inj₁ .unit ∧ M ≠ .inj₂ .unit ∧ M ≠ .unit

/-- **`M to x. N` splits the context between `M` and `N`**: `M` is typed in one part at a
judgement that is no view of `⊤`, and `N` in the other under one more slot (`[bind]`, `[let]`),
or the λ itself there (`[⊸E]`). -/
theorem der_appLam_split {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ (N M : Expr), e = .app (.lam N) M → PlainArg M →
      ∃ Γ₁ Γ₂ : Ctx VTy, Ctx.SplitP Γ Γ₁ Γ₂ ∧ (∃ jM, CDerivesNU Δ Γ₁ M jM ∧ NotTopJ jM) ∧
        ((∃ s j', CDerivesNU Δ (s :: Γ₂) N j') ∨ ∃ j', CDerivesNU Δ Γ₂ (.lam N) j') := by
  induction h
  case bind hs hM hN _ _ =>
    intro N M he _
    simp only [Expr.val, Val.lam, Expr.app.injEq, Expr.lam.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, _, hs, ⟨_, hM, .base ⟨[], _, rfl⟩⟩, .inl ⟨_, _, hN⟩⟩
  case effLet hs _ _ hM hN _ _ =>
    intro N M he _
    simp only [Expr.val, Val.lam, Expr.app.injEq, Expr.lam.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, _, hs, ⟨_, hM, .base ⟨_, _, rfl⟩⟩, .inl ⟨_, _, hN⟩⟩
  case lolliE hs ha hf _ _ =>
    intro N M he _
    simp only [Expr.app.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, _, hs, ⟨_, ha, trivial⟩, .inr ⟨_, hf⟩⟩
  case app =>
    intro N M he hM
    simp only [Expr.app.injEq] at he
    exact absurd he.2.symm (hM.1 _)
  case proj₁ =>
    intro N M he hM
    simp only [Expr.app.injEq] at he
    exact absurd he.2.symm hM.2.1
  case proj₂ =>
    intro N M he hM
    simp only [Expr.app.injEq] at he
    exact absurd he.2.symm hM.2.2.1
  case allE | allEV =>
    intro N M he hM
    simp only [Expr.app.injEq] at he
    exact absurd he.2.symm hM.2.2.2
  case ret ih | ofRet ih | effSub ih | nuIn ih | nuOut ih | bangE ih | boxI ih | boxE ih
    | immSub ih | mutSub ih | roll ih | unroll ih | thunkV ih | bangThunkV ih => exact ih
  case force =>
    rename_i i C _
    intro N M he _
    rcases forceE_cases C (.var i) with hf | hf <;> rw [hf] at he <;> simp at he
  all_goals intro N M he _; cdnu_terms

/-- A slot live on both sides of a split is persistent. -/
theorem splitP_both_live {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) :
    ∀ {i : ℕ}, LiveAt Γ₁ i → LiveAt Γ₂ i → ∃ T, Γ[i]? = some ⟨T, true⟩ ∧ T.Persistent := by
  induction h with
  | nil => intro i h₁; obtain ⟨T, hT⟩ := h₁; simp at hT
  | left _ ih | right _ ih | dead _ ih =>
      intro i h₁ h₂
      cases i with
      | zero =>
          obtain ⟨T₁, hT₁⟩ := h₁; obtain ⟨T₂, hT₂⟩ := h₂
          simp at hT₁ hT₂
      | succ i => simpa using ih (liveAt_cons h₁) (liveAt_cons h₂)
  | dup hT _ ih =>
      intro i h₁ h₂
      cases i with
      | zero => exact ⟨_, rfl, hT⟩
      | succ i => simpa using ih (liveAt_cons h₁) (liveAt_cons h₂)

/-! ### A linear `κ`'s cancel -/

/-- **A linear `κ` is not cancelled at a returner**: `κ (inj₂ ())` projects `κ`'s `&` onto `⊤`, so
it is typed only at `⊤`'s views, and `κ` is no function of `⊸`. -/
theorem der_cancel_lin {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ (i : ℕ) (S : Row) (R B : VTy),
      e = .app (.var i) (.inj₂ .unit) → Γ[i]? = some ⟨kTy S R .lin B, true⟩ → NotTopJ j → False := by
  induction h
  case proj₂ hM _ =>
    rename_i C D
    intro i S R B he hi hj
    simp only [Expr.app.injEq] at he
    obtain ⟨rfl, -⟩ := he
    obtain ⟨A, hA, hI⟩ := der_var_inv hM i rfl
    rw [hi] at hA
    cases hA
    rcases hI with hI | ⟨C₀, hC₀, hN⟩
    · have := NuUp.base_of (fun _ h => by cases h) hI
      obtain ⟨S', Y, h', -⟩ := this
      cases S' <;> simp [CTy.effOf] at h'
    · simp only [kTy, VTy.thunk.injEq] at hC₀
      subst hC₀
      have := NuEq.eq hN (fun _ h => by cases h) (fun _ h => by cases h)
      simp only [CTy.amp.injEq] at this
      obtain ⟨-, rfl⟩ := this
      have := NuUp.base_of (fun _ h => by cases h) hj
      obtain ⟨S', Y, h'⟩ := this
      cases S' <;> simp [CTy.effOf] at h'
  case lolliE hs _ hf _ _ =>
    intro i S R B he hi _
    simp only [Expr.app.injEq] at he
    obtain ⟨rfl, -⟩ := he
    obtain ⟨A, hA, hI⟩ := der_var_inv hf i rfl
    have hA' := splitP_live_right hs hA
    rw [hi] at hA'
    cases hA'
    rcases hI with hI | ⟨C, S', X, hA, hC, -⟩
    · have h2 := (hI _).mp (ThunkOf.thunk _)
      have h3 : ThunkOf (kTy S R .lin B) (.amp (.arr B (CTy.effOf S R)) .top) := .thunk _
      have := ThunkOf.unique h2 h3
      cases this
    · simp only [kTy, VTy.thunk.injEq] at hA
      subst hA
      have := NuEq.eq hC (fun _ h => by cases h) (effOf_ne_nu S' X)
      exact absurd this.symm (effOf_ne_amp S' X _ _)
  case app =>
    intro i S R B he _ _
    simp at he
  case proj₁ =>
    intro i S R B he _ _
    simp [Expr.val, Val.inj₁, Val.unit] at he
  case allE | allEV =>
    intro i S R B he _ _
    simp [Expr.val, Val.unit] at he
  case ret ih => intro i S R B he hi _; exact ih i S R B he hi trivial
  case ofRet ih => intro i S R B he hi _; exact ih i S R B he hi (.base ⟨[], _, rfl⟩)
  case effSub ih => intro i S R B he hi _; exact ih i S R B he hi (.base ⟨_, _, rfl⟩)
  case nuIn ih => intro i S R B he hi hj; exact ih i S R B he hi (notTopJ_nu hj)
  case nuOut ih => intro i S R B he hi hj; exact ih i S R B he hi (.nu hj)
  case bangE ih | boxI ih | boxE ih | immSub ih | mutSub ih | roll ih | unroll ih =>
    intro i S R B he hi _; exact ih i S R B he hi trivial
  case force =>
    rename_i i' C _
    intro i S R B he _ _
    rcases forceE_cases C (.var i') with hf | hf <;> rw [hf] at he <;>
      simp [Expr.val, Val.unit] at he
  all_goals intro i S R B he _ _; cdnu_terms

/-! ### The four clauses -/

theorem clauseTy_resuming {S : Row} {R : VTy} {q : Qual} {A B : VTy}
    (h : (B.isZero && q != .lin) = false) :
    clauseTy S R (q, A, B) = .bang (.thunk (.arr (.tensor A (kTy S R q B)) (CTy.effOf S R))) := by
  simp [clauseTy, h]

theorem kTy_not_persistent {S : Row} {R : VTy} {q : Qual} {B : VTy} (hq : q ≠ .unr) :
    ¬ (kTy S R q B).Persistent := by
  cases q <;> simp_all [kTy, VTy.Persistent, VTy.persistent]

/-- **A clause `λp. let (v, k) = p in X` at a resuming operation's clause type** types `X` with
`k : kTy` live in slot `0` and `v : A` in slot `1`, at a judgement that is no view of `⊤`. -/
theorem der_clause_body {Δ : LifeCtx} {Γ : Ctx VTy} {X : Expr} {S : Row} {R : VTy} {q : Qual}
    {A B : VTy} (hX : PlainTail X) (hres : (B.isZero && q != .lin) = false)
    (h : CDerivesNU Δ Γ (.lam (.letpair (.var 0) X)) (.val (clauseTy S R (q, A, B)))) :
    ∃ (Γb : Ctx VTy) (C : CTy), CDerivesNU Δ (⟨kTy S R q B, true⟩ :: ⟨A, true⟩ :: Γb) X (.comp C) ∧
      NotTopJ (.comp C) := by
  rw [clauseTy_resuming hres] at h
  obtain ⟨C', hC', hb⟩ := der_lam_arr h X (.tensor A (kTy S R q B)) (CTy.effOf S R) rfl hX
    (ThunkOf.bang (.thunk _))
  obtain ⟨Γp, Γb, A', B', C'', hs, hV, hM, hT⟩ := der_letpair_split hb (.var 0) X rfl
  obtain ⟨T, hT0⟩ := der_free_live hV 0 rfl
  have hT0' := splitP_live_left hs hT0
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hT0'
  obtain ⟨rfl, -⟩ := hT0'
  have hview := der_var_tensor hV 0 A (kTy S R q B) rfl hT0
  obtain ⟨rfl, rfl⟩ := isViewOf_tensor hview
  exact ⟨Γb, C'', hM, hT (notTopJ_of_nuEq hC')⟩

/-- **R1's clause is refused at a resuming linear or affine operation**: `return ff` leaves the
slot of `k : kTy` live, and `kTy` is neither dropped nor persistent. -/
theorem refuses_dropClause {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {q : Qual}
    {A B : VTy} (hq : q ≠ .unr) (hres : (B.isZero && q != .lin) = false) :
    ¬ CDerivesNU Δ Γ dropV.1 (.val (clauseTy S R (q, A, B))) := by
  intro h
  obtain ⟨Γb, C, hX, hT⟩ := der_clause_body (X := .inj₁ .unit) ⟨by simp, by simp, by simp⟩ hres h
  exact kTy_not_persistent hq (not_liveAt_deadP (der_unit_dead hX (.inr rfl) hT) (i := 0) rfl)

/-- `k` used on both sides of `M to x. N` is a persistent slot. -/
theorem k_twice {Δ : LifeCtx} {Γb : Ctx VTy} {K A : VTy} {N M : Expr} {j : Jdg}
    (h : CDerivesNU Δ (⟨K, true⟩ :: ⟨A, true⟩ :: Γb) (.app (.lam N) M) j) (hM : PlainArg M)
    (hM0 : M.FreeIn 0) (hN1 : N.FreeIn 1) : K.Persistent := by
  obtain ⟨Γ₁, Γ₂, hs, ⟨jM, hdM, -⟩, hN⟩ := der_appLam_split h N M rfl hM
  have h₁ := der_free_live hdM 0 hM0
  have h₂ : LiveAt Γ₂ 0 := by
    rcases hN with ⟨s, j', hdN⟩ | ⟨j', hdN⟩
    · exact liveAt_cons (der_free_live hdN 1 hN1)
    · exact der_free_live hdN 0 hN1
  obtain ⟨T, hT, hP⟩ := splitP_both_live hs h₁ h₂
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hT
  obtain ⟨rfl, -⟩ := hT
  exact hP

/-- **R2's clause is refused at a resuming linear or affine operation**: `resume k () to _.
resume k ()` reads `k` on both sides of a bind, so its slot would be persistent. -/
theorem refuses_twiceClause {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {q : Qual}
    {A B : VTy} (hq : q ≠ .unr) (hres : (B.isZero && q != .lin) = false) :
    ¬ CDerivesNU Δ Γ twiceV.1 (.val (clauseTy S R (q, A, B))) := by
  intro h
  obtain ⟨Γb, C, hX, -⟩ := der_clause_body (X := twBody)
    ⟨by simp [twBody, bindE], by simp [twBody, bindE], by simp [twBody, bindE]⟩ hres h
  exact kTy_not_persistent hq (k_twice hX ⟨by simp [resumeE], by simp [resumeE], by simp [resumeE],
    by simp [resumeE]⟩ (by simp [resumeE, Expr.FreeIn, Expr.shift]) (by simp [resumeE, Expr.FreeIn, Expr.shift]))

/-- **R4's clause is refused at a resuming linear or affine operation**: `cancel k to _.
resume k ()` reads `k` on both sides of a bind. -/
theorem refuses_cancelResumeClause {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {q : Qual}
    {A B : VTy} (hq : q ≠ .unr) (hres : (B.isZero && q != .lin) = false) :
    ¬ CDerivesNU Δ Γ cancelResumeV.1 (.val (clauseTy S R (q, A, B))) := by
  intro h
  obtain ⟨Γb, C, hX, -⟩ := der_clause_body (X := crBody)
    ⟨by simp [crBody, bindE], by simp [crBody, bindE], by simp [crBody, bindE]⟩ hres h
  exact kTy_not_persistent hq (k_twice hX ⟨by simp [cancelE], by simp [cancelE], by simp [cancelE],
    by simp [cancelE]⟩ (by simp [cancelE, Expr.FreeIn]) (by simp [resumeE, Expr.FreeIn, Expr.shift]))

/-- **R3's clause is refused at a linear operation**: a linear `κ`'s cancel branch is at `⊤`, which
no bind takes. -/
theorem refuses_cancelClause_lin {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {A B : VTy} :
    ¬ CDerivesNU Δ Γ cancelV.1 (.val (clauseTy S R (.lin, A, B))) := by
  intro h
  obtain ⟨Γb, C, hX, -⟩ := der_clause_body (X := cBody)
    ⟨by simp [cBody, bindE], by simp [cBody, bindE], by simp [cBody, bindE]⟩ (by simp) h
  obtain ⟨Γ₁, Γ₂, hs, ⟨jM, hdM, hjM⟩, -⟩ := der_appLam_split hX (.inj₁ .unit) (cancelE (.var 0)) rfl
    ⟨by simp [cancelE], by simp [cancelE], by simp [cancelE], by simp [cancelE]⟩
  obtain ⟨T, hT⟩ := der_free_live hdM 0 (by simp [cancelE, Expr.FreeIn])
  have hT' := splitP_live_left hs hT
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hT'
  obtain ⟨rfl, -⟩ := hT'
  exact der_cancel_lin hdM 0 S R B rfl hT hjM

/-- **Today's clause typing refuses R1–R4's clauses** at the classes S6's witnesses name: R1, R2
and R4 at every resuming linear or affine operation, R3 at every linear one. -/
theorem refuses_R_clauses {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {q : Qual} {A B : VTy}
    (hq : q ≠ .unr) (hres : (B.isZero && q != .lin) = false) :
    ¬ CDerivesNU Δ Γ dropV.1 (.val (clauseTy S R (q, A, B))) ∧
    ¬ CDerivesNU Δ Γ twiceV.1 (.val (clauseTy S R (q, A, B))) ∧
    ¬ CDerivesNU Δ Γ cancelV.1 (.val (clauseTy S R (.lin, A, B))) ∧
    ¬ CDerivesNU Δ Γ cancelResumeV.1 (.val (clauseTy S R (q, A, B))) :=
  ⟨refuses_dropClause hq hres, refuses_twiceClause hq hres, refuses_cancelClause_lin,
    refuses_cancelResumeClause hq hres⟩

/-! ### The refusals pin `κ`'s use -/

/-- **R3's refusal is the class.**  `cancelCl`, `λ(x, k). k (inj₂ ())`, is typed at an affine
operation (`d_cancelClNU`) and refused at a linear one. -/
theorem refuses_cancelCl_lin {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {A B : VTy} :
    ¬ CDerivesNU Δ Γ cancelCl (.val (clauseTy S R (.lin, A, B))) := by
  intro h
  obtain ⟨Γb, C, hX, hT⟩ := der_clause_body (X := .app (.var 0) (.inj₂ .unit))
    ⟨by simp, by simp, by simp⟩ (by simp) h
  exact der_cancel_lin hX 0 S R B rfl rfl hT

/-- **The refusals pin `κ`'s use, not the clauses' form.**  At a linear operation `1 ↠ 1` a clause
that resumes `κ` once is typed (`d_tailClNU`) and R1–R4's clauses are not; `cancelCl` is typed at
an affine operation and refused at a linear one. -/
theorem clauseRefusals_pinned {Δ : LifeCtx} :
    (CDerivesNU Δ [] tailClE (.val (clauseTy S₁₁ .unit (.lin, .unit, .unit))) ∧
      ¬ CDerivesNU Δ [] dropV.1 (.val (clauseTy S₁₁ .unit (.lin, .unit, .unit))) ∧
      ¬ CDerivesNU Δ [] twiceV.1 (.val (clauseTy S₁₁ .unit (.lin, .unit, .unit))) ∧
      ¬ CDerivesNU Δ [] cancelV.1 (.val (clauseTy S₁₁ .unit (.lin, .unit, .unit))) ∧
      ¬ CDerivesNU Δ [] cancelResumeV.1 (.val (clauseTy S₁₁ .unit (.lin, .unit, .unit)))) ∧
    (CDerivesNU Δ [] cancelCl (.val (clauseTy [] .unit (.aff, .unit, .unit))) ∧
      ¬ CDerivesNU Δ [] cancelCl (.val (clauseTy [] .unit (.lin, .unit, .unit)))) :=
  ⟨⟨d_tailClNU .nil, refuses_dropClause (by simp) (by simp),
      refuses_twiceClause (by simp) (by simp), refuses_cancelClause_lin,
      refuses_cancelResumeClause (by simp) (by simp)⟩,
    d_cancelClNU .nil, refuses_cancelCl_lin⟩

end Targets.Inst

end
