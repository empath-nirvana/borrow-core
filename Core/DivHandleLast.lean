import Core.DivHandle

/-!
# Core — `[handle-last]`: a clause that uses `κ` once, last  `[spec §14, §19, §27, §51]`

`hnd_m H e`, `e` at a row that may hold `Div`, `m ≠ Div`, at clauses of one class: the clause
works on the operation's argument, then resumes `κ` in tail position or cancels it and leaves,
and while it works `κ`'s cancel is its unwind finaliser.

    λ(x, κ). (w x) then r. case r { inl y → κ.1 y | inr z → κ.2 (); nf z } unwind κ.2 ()

**The rule** (`effHandleL`): the clauses are written out from a tuple of works `w` and a tuple of
exits `nf` (`lastTuple`), as `effHandleT`'s are from its answering functions.  A work
`w : !U(A ⊸ F_{Σ_W}(B ⊕ X))` runs at a row `Σ_W ≤ Σ`, and may tick, raise and perform cancellable
operations of the rows outside; an exit `nf : !U(X ⊸ F_Σ R)`.  The handler's operations are
cancellable or abortive; an abortive operation's clause is its work `w : !U(A ⊸ F_Σ R)` itself.  `κ`'s
type never appears in a program, so its cancel branch is given the table of the operation's own
cancel row `fs j` (`ewp_handle_or`'s `hTc` asks only that it be above the entry's obligation).

**The proof** (`cwp_handle_last`), at a row holding `Div`, is `cwp_handle_tail`'s: the greatest
fixed point of the handled computations together with the finaliser frame around a work, `κ` in
the frame resumed into one segment of the candidate.  The candidate is a least fixed point
(`lastY`).  The frame is `cwpF_frame_then` from the work's row to the outer one; its finaliser
`κ.2 ()` runs at the cancel row's table; the frame's answer resumes `κ` (`inl`) or cancels it and
runs the exit (`inr`, `last_cont`).  The Fundamental Property is applied to the works and the
exits, never to a term that mentions `κ`.  `Closing` is `ewp_handle` at the closing tables.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal
  kappa kappaC kappaCell kappaAt clauseAt capTag)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### The clauses -/

/-- The clause of the `j`-th operation, from the tuples `Hw` of works and `Hn` of exits: at a
non-abortive operation
`λ(x, κ). (w_j x) then r. case r {inl y → κ.1 y | inr z → κ.2 (); nf_j z} unwind κ.2 ()`,
at an abortive one `λx. w_j x`.  `[spec §51]` -/
def lastClause (j : Nat) (abort : Bool) (Hw Hn : Expr) : Expr :=
  if abort then .lam (.app (pickE j (Hw.shift 1 0)) (.var 0))
  else .lam (.letpair (.var 0)
    (thenE
      -- `N`, under `r` (0), `κ` (1), `x` (2)
      (.case (.var 0)
        (.app (.app (.var 2) (.val (Val.inj₁ .unit))) (.var 0))
        (.app (.val (.lam (.app (pickE j (Hn.shift 6 0)) (.var 1))))
          (.app (.var 2) (.val (Val.inj₂ .unit)))))
      -- `D`, under `_` (0), `κ` (1)
      (.app (.var 1) (.val (Val.inj₂ .unit)))
      -- `M`
      (.app (pickE j (Hw.shift 3 0)) (.var 1))))

/-- The clauses, from the `j`-th on.  `[spec §51]` -/
def lastTuple : List (Qual × VTy × VTy) → Nat → Expr → Expr → Expr
  | [], _, _, _ => .val .unit
  | (q, _, B) :: E, j, Hw, Hn =>
      .pair (lastClause j (B.isZero && q != .lin) Hw Hn) (lastTuple E (j + 1) Hw Hn)

/-- A work's type: `!U(A ⊸ F_{Σ_W}(B ⊕ X))`, or the clause's `!U(A ⊸ F_Σ R)` at an abortive
operation.  `[spec §51]` -/
def workTy (S SW : Row) (R X : VTy) : Qual × VTy × VTy → VTy
  | (q, A, B) => if (B.isZero && q != .lin) then .bang (.thunk (.arr A (CTy.effOf S R)))
      else .bang (.thunk (.arr A (CTy.effOf SW (.sum B X))))

/-- The works' tuple's type, the `j`-th exit's argument at `Xs j`.  `[spec §51]` -/
def worksTy (S SW : Row) (R : VTy) (Xs : Nat → VTy) : List (Qual × VTy × VTy) → Nat → VTy
  | [], _ => .unit
  | o :: E, j => .tensor (workTy S SW R (Xs j) o) (worksTy S SW R Xs E (j + 1))

/-- An exit's type, `!U(X ⊸ F_Σ R)`.  `[spec §51]` -/
def exitTy (S : Row) (R X : VTy) : VTy := .bang (.thunk (.arr X (CTy.effOf S R)))

/-- The exits' tuple's type.  `[spec §51]` -/
def exitsTy (S : Row) (R : VTy) (Xs : Nat → VTy) : List (Qual × VTy × VTy) → Nat → VTy
  | [], _ => .unit
  | _ :: E, j => .tensor (exitTy S R (Xs j)) (exitsTy S R Xs E (j + 1))

theorem workTy_persistent (S SW : Row) (R X : VTy) (o : Qual × VTy × VTy) :
    (workTy S SW R X o).Persistent := by
  obtain ⟨q, A, B⟩ := o
  simp only [workTy]; split <;> rfl

theorem worksTy_persistent (S SW : Row) (R : VTy) (Xs : Nat → VTy) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat), (worksTy S SW R Xs E j).Persistent
  | [], _ => rfl
  | o :: E, j => by
      simp only [VTy.Persistent, VTy.persistent, worksTy, Bool.and_eq_true]
      exact ⟨workTy_persistent S SW R (Xs j) o, worksTy_persistent S SW R Xs E (j + 1)⟩

theorem exitsTy_persistent (S : Row) (R : VTy) (Xs : Nat → VTy) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat), (exitsTy S R Xs E j).Persistent
  | [], _ => rfl
  | _ :: E, j => by
      simp only [VTy.Persistent, VTy.persistent, exitsTy, Bool.and_eq_true]
      exact ⟨rfl, exitsTy_persistent S R Xs E (j + 1)⟩

/-- An abortive operation's clause is `effHandleT`'s. -/
theorem lastClause_abort (j : Nat) (Hw Hn : Expr) : lastClause j true Hw Hn = tailClause j true Hw :=
  rfl

/-! ### Substitution and shifts -/

theorem lastClause_psub (j : Nat) (b : Bool) (γ : List Val) (Hw Hn : Expr) :
    Expr.psub 0 γ (lastClause j b Hw Hn) = lastClause j b (Expr.psub 0 γ Hw) (Expr.psub 0 γ Hn) := by
  cases b
  · have e₃ := Expr.psub_shift 3 γ Hw 0
    have e₆ := Expr.psub_shift 6 γ Hn 0
    simp only [Nat.zero_add] at e₃ e₆
    simp only [lastClause, Bool.false_eq_true, if_false, thenE, Expr.psub, pickE_psub, e₃, e₆,
      Expr.val, Val.lam]
    simp [Val.inj₁, Val.inj₂, Val.unit, Val.prim, Expr.psub]
  · have e := Expr.psub_shift 1 γ Hw 0
    simp only [Nat.zero_add] at e
    simp only [lastClause, if_true, Expr.psub, pickE_psub, e]
    simp

theorem lastTuple_psub (γ : List Val) (Hw Hn : Expr) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat),
      Expr.psub 0 γ (lastTuple E j Hw Hn) = lastTuple E j (Expr.psub 0 γ Hw) (Expr.psub 0 γ Hn)
  | [], _ => by simp [lastTuple, Expr.psub, Val.unit]
  | _ :: E, j => by
      simp only [lastTuple, Expr.psub, lastClause_psub, lastTuple_psub γ Hw Hn E (j + 1)]

theorem lastClause_shift (j : Nat) (b : Bool) (d c : Nat) (Hw Hn : Expr) :
    Expr.shift d c (lastClause j b Hw Hn) = lastClause j b (Hw.shift d c) (Hn.shift d c) := by
  cases b
  · have e₃ := Expr.shift_shift_comm 3 d c Hw 0
    have e₆ := Expr.shift_shift_comm 6 d c Hn 0
    simp only [Nat.zero_add] at e₃ e₆
    simp only [lastClause, Bool.false_eq_true, if_false, thenE, Expr.shift, pickE_shift, Val.lam,
      Val.prim, Val.inj₁, Val.inj₂, Val.unit, Expr.val]
    simp [Nat.add_assoc, e₃, e₆]
  · have e := Expr.shift_shift_comm 1 d c Hw 0
    simp only [Nat.zero_add] at e
    simp only [lastClause, if_true, Expr.shift, pickE_shift]
    rw [e]
    simp

theorem lastTuple_shift (d c : Nat) (Hw Hn : Expr) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat),
      Expr.shift d c (lastTuple E j Hw Hn) = lastTuple E j (Hw.shift d c) (Hn.shift d c)
  | [], _ => by simp [lastTuple, Expr.shift, Val.unit]
  | _ :: E, j => by
      simp only [lastTuple, Expr.shift, lastClause_shift, lastTuple_shift d c Hw Hn E (j + 1)]

theorem closedAt_lastTuple {k : Nat} {Hw Hn : Expr} (hw : closedAt k Hw = true)
    (hn : closedAt k Hn = true) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat), closedAt k (lastTuple E j Hw Hn) = true
  | [], _ => rfl
  | (q, _, B) :: E, j => by
      simp only [lastTuple, closedAt, closedAt_lastTuple hw hn E (j + 1), Bool.and_true]
      unfold lastClause
      split
      · have := closedAt_pickE j (closedAt_shift_add 1 Hw k 0 hw)
        simp [closedAt, this]
      · have h₃ := closedAt_pickE j (closedAt_shift_add 3 Hw k 0 hw)
        have h₆ := closedAt_pickE j (closedAt_shift_add 6 Hn k 0 hn)
        simp [closedAt, thenE, h₃, h₆, Val.lam, Val.inj₁, Val.inj₂, Val.unit, Val.prim]

/-- A clause is a value. -/
theorem isVal_lastClause (j : Nat) (b : Bool) (Hw Hn : Expr) : IsVal (lastClause j b Hw Hn) := by
  cases b <;> simp only [lastClause, Bool.false_eq_true, if_false, if_true] <;> exact .lam

theorem isVal_lastTuple (Hw Hn : Expr) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat), IsVal (lastTuple E j Hw Hn)
  | [], _ => .unit
  | _ :: E, j => .pair (isVal_lastClause _ _ _ _) (isVal_lastTuple Hw Hn E (j + 1))

/-- The `j`-th clause of the tuple. -/
theorem clauseAt_lastTuple (Hw Hn : Expr) :
    ∀ (E : List (Qual × VTy × VTy)) (k j : Nat) (hj : j < E.length),
      clauseAt (lastTuple E k Hw Hn) j =
        some ⟨lastClause (k + j) (E[j].2.2.isZero && E[j].1 != .lin) Hw Hn,
          isVal_lastClause _ _ _ _⟩
  | [], _, _, hj => by simp at hj
  | (q, A, B) :: E, k, 0, _ => by
      simp only [lastTuple, clauseAt, Nat.add_zero, dif_pos (isVal_lastClause k _ Hw Hn)]
      rfl
  | (q, A, B) :: E, k, j + 1, hj => by
      simp only [lastTuple, clauseAt]
      rw [clauseAt_lastTuple Hw Hn E (k + 1) j (by simpa using hj)]
      simp only [List.getElem_cons_succ]
      rw [show k + 1 + j = k + (j + 1) by omega]

/-! ### The works and the exits -/

/-- **The works**: a tuple of the works' type holds, at each operation, the function `pickE j`
steps to, at the empty resource. -/
theorem worksTy_at {S SW : Row} {R : VTy} {Xs : Nat → VTy} {ls : List SRec} {δ : LSub} :
    ∀ (E : List (Qual × VTy × VTy)) (k : Nat) {vc : Val} {ρ : WRes},
      vC true (worksTy S SW R Xs E k) ls δ vc ρ →
      ∀ j (h : j < E.length), ∃ g, PureSteps (pickE j (.val vc)) (.val g) ∧
        vC true (workTy S SW R (Xs (k + j)) E[j]) ls δ g PMap.empty
  | [], _, _, _, _, j, h => by simp at h
  | o :: E, k, vc, ρ, h, j, hj => by
      obtain ⟨g, rest, h⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, hg, hr⟩ := pure_sep_iff.mp h
      have he : ρ₁ = PMap.empty := vP_empty_of_persistent (workTy_persistent S SW R _ o) hg
      cases j with
      | zero =>
          exact ⟨g, pickE_steps 0 g rest _ rfl g (fun _ => rfl) (fun _ h => by cases h),
            by simpa using he ▸ hg⟩
      | succ j =>
          obtain ⟨g', hs, hg'⟩ := worksTy_at E (k + 1) hr j (by simpa using hj)
          refine ⟨g', pickE_steps (j + 1) g rest _ rfl g' (fun h => by cases h)
            (fun j' h => by cases h; exact hs), ?_⟩
          rw [show k + (j + 1) = k + 1 + j by omega]
          simpa using hg'

/-- **The exits**, as the works. -/
theorem exitsTy_at {S : Row} {R : VTy} {Xs : Nat → VTy} {ls : List SRec} {δ : LSub} :
    ∀ (E : List (Qual × VTy × VTy)) (k : Nat) {vc : Val} {ρ : WRes},
      vC true (exitsTy S R Xs E k) ls δ vc ρ →
      ∀ j, j < E.length → ∃ g, PureSteps (pickE j (.val vc)) (.val g) ∧
        vC true (exitTy S R (Xs (k + j))) ls δ g PMap.empty
  | [], _, _, _, _, j, h => by simp at h
  | o :: E, k, vc, ρ, h, j, hj => by
      obtain ⟨g, rest, h⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, hg, hr⟩ := pure_sep_iff.mp h
      have he : ρ₁ = PMap.empty := vP_empty_of_persistent (A := exitTy S R (Xs k)) rfl hg
      cases j with
      | zero =>
          exact ⟨g, pickE_steps 0 g rest _ rfl g (fun _ => rfl) (fun _ h => by cases h),
            by simpa using he ▸ hg⟩
      | succ j =>
          obtain ⟨g', hs, hg'⟩ := exitsTy_at E (k + 1) hr j (by simpa using hj)
          refine ⟨g', pickE_steps (j + 1) g rest _ rfl g' (fun h => by cases h)
            (fun j' h => by cases h; exact hs), ?_⟩
          rw [show k + (j + 1) = k + 1 + j by omega]
          simpa using hg'

/-! ### Steps -/

/-- The clause's answer function `λr. case r {inl y → κ.1 y | inr z → κ.2 (); nf_j z}`, at `κ`
and the exits' tuple `vn`. -/
def lastN (j : Nat) (κ vn : Val) : Val :=
  Val.lam (.case (.var 0)
    (.app (.app (.val (κ.shift 2 0)) (.val (Val.inj₁ .unit))) (.var 0))
    (.app (.val (.lam (.app (pickE j ((Expr.val vn).shift 3 0)) (.var 1))))
      (.app (.val (κ.shift 2 0)) (.val (Val.inj₂ .unit)))))

/-- The clause's finaliser `λ_. κ.2 ()`. -/
def lastD (κ : Val) : Val := Val.lam (.app (.val (κ.shift 1 0)) (.val (Val.inj₂ .unit)))

/-- The exit's frame after `κ`'s cancel: `(λ_. nf_j z) [·]`. -/
def exitK (j : Nat) (vn z : Val) : Kont :=
  .appR (.val (Val.lam (.app (pickE j ((Expr.val vn).shift 1 0)) (.val (z.shift 1 0))))) .hole

theorem exitK_plain (j : Nat) (vn z : Val) :
    (∀ n, (exitK j vn z).HasHnd n = false) ∧ (∀ n, (exitK j vn z).Catches n = false) :=
  ⟨fun n => by simp [exitK, Kont.HasHnd], fun n => by simp [exitK, Kont.Catches]⟩

/-- A clause at `(v, κ)` runs its work under the finaliser frame. -/
theorem lastClause_steps (j : Nat) (vc vn g v κ : Val)
    (hg : PureSteps (pickE j (.val vc)) (.val g)) :
    PureSteps (.app (lastClause j false (.val vc) (.val vn)) (.val (Val.pair v κ)))
      ((ubindK (lastN j κ vn) (lastD κ)).plug (.app (.val g) (.val v))) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.letpair μ v κ _) rfl).trans ?_
  have e : ((Expr.subst 2 ((Val.pair v κ).shift 2 0) (thenE
      (.case (.var 0)
        (.app (.app (.var 2) (.val (Val.inj₁ .unit))) (.var 0))
        (.app (.val (.lam (.app (pickE j ((Expr.val vn).shift 6 0)) (.var 1))))
          (.app (.var 2) (.val (Val.inj₂ .unit)))))
      (.app (.var 1) (.val (Val.inj₂ .unit)))
      (.app (pickE j ((Expr.val vc).shift 3 0)) (.var 1)))).subst 0 (κ.shift 1 0)).subst 0 v =
      (ubindK (lastN j κ vn) (lastD κ)).plug (.app (pickE j (.val vc)) (.val v)) := by
    simp [thenE, pickE_subst, lastN, lastD, Kont.plug, subst_shift_succ, Val.pair, Val.lam,
      Val.inj₁, Val.inj₂, Val.unit, Val.prim]
  rw [e]
  have := PureSteps.plug ((ubindK (lastN j κ vn) (lastD κ)).comp (.appL .hole v)) hg
  rw [Kont.plug_comp, Kont.plug_comp] at this
  exact this

/-- The frame's answer `inl y` resumes `κ` at `y`. -/
theorem lastN_inl (j : Nat) (κ vn y : Val) :
    PureSteps ((ubindK (lastN j κ vn) (lastD κ)).plug (.val (Val.inj₁ y)))
      (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val y)) := by
  refine (PureSteps.head (fun μ => Head.uthen μ _ _ _) rfl).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ y _ _) rfl).trans ?_
  simp [subst_shift_succ, Val.inj₁, Val.unit]
  exact .refl

/-- The frame's answer `inr z` cancels `κ` under the exit's frame. -/
theorem lastN_inr (j : Nat) (κ vn z : Val) :
    PureSteps ((ubindK (lastN j κ vn) (lastD κ)).plug (.val (Val.inj₂ z)))
      ((exitK j vn z).plug (.app (.val κ) (.val (Val.inj₂ .unit)))) := by
  refine (PureSteps.head (fun μ => Head.uthen μ _ _ _) rfl).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ z _ _) rfl).trans ?_
  simp [subst_shift_succ, pickE_subst, exitK, Kont.plug, Val.inj₂, Val.unit, Val.lam]
  exact .refl

/-- After `κ`'s cancel the exit runs at `z`. -/
theorem exitK_steps (j : Nat) (vn z g : Val) (hg : PureSteps (pickE j (.val vn)) (.val g)) :
    PureSteps ((exitK j vn z).plug (.val .unit)) (.app (.val g) (.val z)) := by
  refine (PureSteps.beta _ _).trans ?_
  have e : Expr.subst 0 Val.unit (.app (pickE j ((Expr.val vn).shift 1 0)) (.val (z.shift 1 0))) =
      (Kont.appL .hole z).plug (pickE j (.val vn)) := by
    simp [pickE_subst, Kont.plug, subst_shift_succ]
  rw [e]
  exact PureSteps.plug (.appL .hole z) hg

/-- The finaliser cancels `κ`. -/
theorem lastD_steps (κ : Val) :
    PureSteps (.app (.val (lastD κ)) (.val .unit)) (.app (.val κ) (.val (Val.inj₂ .unit))) := by
  refine (PureSteps.beta _ _).trans ?_
  simp [subst_shift_succ, Val.inj₂, Val.unit]
  exact .refl

/-! ### `κ`'s own type as a finaliser -/

/-- **`κ.2 ()` at its own type, as a finaliser**: a `[then]` whose finaliser is `κ.2 ()`, typed at
`cancelTy Σ F = F_{F ⊕ Σ} 1`, around a capturable operation `o` of `Σ` asks, through `[then]`'s
`hfin` (`ThenLe o.fin (F ⊕ Σ) o.fin`), that `o`'s cancel row be `⊤` or find `o`'s own key: the
finaliser's row holds `o` itself.  `[handle-last]` writes its clauses and gives `κ`'s cancel the
table of the operation's own cancel row instead, so this does not arise there.  `[spec §51]` -/
def KappaFinSelf : Prop :=
  ∀ (F : CTy) (S : Row) (o : OpSig), o ∈ S → Row.find S o.n o.i = some o →
    capB o.q o.B = true → ThenLe o.fin (F.rowOf ++ S) o.fin →
    o.fin.isTop = true ∨ ∃ o', Row.find o.fin.rowOf o.n o.i = some o'

theorem kappaFinSelf : KappaFinSelf := by
  intro F S o _ hf _ h
  rw [ThenLe] at h
  rcases h with h | ⟨-, -, hE⟩
  · exact .inl h
  · obtain ⟨o₁, h₁⟩ : ∃ o₁, Row.find (F.rowOf ++ S) o.n o.i = some o₁ := by
      rw [Row.find_append]
      cases h' : Row.find F.rowOf o.n o.i with
      | none => exact ⟨o, by simp [hf]⟩
      | some o₁ => exact ⟨o₁, rfl⟩
    obtain ⟨o', h', -⟩ := hE _ _ _ h₁
    exact .inr ⟨o', h'⟩

/-! ### The cancel rows -/

/-- What the rule asks of the `j`-th operation's cancel row `F`, at the work's row `Σ_W`, the
outer row `Σ` and the exit's argument `X`: `F` is not `⊤`, it is below `Σ` (D3) and free of `Div`
(decision 69), each capturable operation of `Σ_W` has a cancel row above its own `⋈ F` (`[then]`'s
`hfin`, `κ.2 ()` being the finaliser), the errors pending at the finaliser are persistent where
`F` has an unrestricted operation (`[then]`'s `hP`), and `X` drops where `F` has an operation
with weakening: `z : X` is held across `κ.2 ()`, which may raise or be captured and cancelled
(`[let]`'s `hW`).  `[spec §27, §51]` -/
def LastFinOK (S SW : Row) (F : CTy) (X : VTy) : Prop :=
  F.isTop = false ∧ RowLe F.rowOf S ∧ Row.divB F.rowOf = false ∧
  (∀ m i o o', Row.find SW m i = some o → Row.find S m i = some o' →
    capB o.q o.B = true → ThenLe o.fin F.rowOf o'.fin) ∧
  (Row.UnrD F.rowOf → SW.PendPers) ∧ (Row.Cancels F.rowOf → X.OwnFree)

/-- **At the empty cancel row**, the one the checker emits, `LastFinOK` is `[then]`'s `hfin` at
the empty finaliser row.  `[spec §27, §51]` -/
theorem lastFinOK_nil {S SW : Row} {X : VTy}
    (h : ∀ m i o o', Row.find SW m i = some o → Row.find S m i = some o' →
      capB o.q o.B = true → ThenLe o.fin [] o'.fin) :
    LastFinOK S SW (.ret .unit) X :=
  ⟨rfl, RowLe.nil S, rfl, h, fun ⟨_, h, _⟩ => by simp [CTy.rowOf] at h,
    fun ⟨_, h, _⟩ => by simp [CTy.rowOf] at h⟩

/-- `LastFinOK` at the empty cancel row, where `Σ_W` finds what `Σ` finds (`Σ_W = Σ`, or a part of
`Σ` ahead of the rest): every operation's cancel row is its own, `ThenLe.nil`.  `[spec §51]` -/
theorem lastFinOK_nil_of_find {S SW : Row} {X : VTy}
    (h : ∀ m i o, Row.find SW m i = some o → Row.find S m i = some o) :
    LastFinOK S SW (.ret .unit) X :=
  lastFinOK_nil fun m i o o' hf hf' _ => by
    rw [h m i o hf] at hf'; cases hf'; exact ThenLe.nil o.fin

/-- A row below `Σ` that does not hold `Div` has no entry at `Div`'s key. -/
theorem tab_le_erase0 {δ : LSub} {G S : Row} (hGS : RowLe G S) (hSd : Row.divB S = true)
    (hGd : Row.divB G = false) : (Row.tab G δ).Le (Row.tab S δ).erase0 := by
  intro m i en hT
  obtain ⟨en', hT', hle⟩ := Row.tab_le δ hGS m i en hT
  refine ⟨en', ?_, hle⟩
  have hk : ¬ (m = divEff ∧ i = 0) := by
    rintro ⟨rfl, rfl⟩
    obtain ⟨o, hf, -⟩ := Row.tab_some hT
    rw [Row.find_key_none hGS hSd hGd] at hf; cases hf
  rw [OpTab.erase0_ne hk]; exact hT'

theorem tab_le_closeAt {δ : LSub} {G S : Row} (hGS : RowLe G S) (hSd : Row.divB S = true)
    (hGd : Row.divB G = false) : (Row.tab G δ).Le (Row.tab S δ).closeAt := by
  intro m i en hT
  obtain ⟨en', hT', hle⟩ := Row.tab_le δ hGS m i en hT
  refine ⟨en', ?_, hle⟩
  have hk : ¬ (m = divEff ∧ i = 0) := by
    rintro ⟨rfl, rfl⟩
    obtain ⟨o, hf, -⟩ := Row.tab_some hT
    rw [Row.find_key_none hGS hSd hGd] at hf; cases hf
  rw [OpTab.closeAt_ne hk]; exact hT'

/-- A row below one with no unrestricted operation finds none. -/
theorem find_not_unr {G S : Row} (hGS : RowLe G S) (hSu : ¬ S.UnrD) {n i : UInt32} {o : OpSig}
    (hf : Row.find G n i = some o) : o.q ≠ .unr := by
  intro hq
  obtain ⟨o', hf', hle⟩ := hGS n i o hf
  exact hSu ⟨o', (Row.find_mem hf').1, Or.inl (hle.1.2.2.1 ▸ hq)⟩

/-! ### The frame's answer -/

/-- **The finaliser frame's answer**: `inl y` resumes `κ` at `y`; `inr z` cancels `κ`, at the
table of its cancel row `G`, beside `z`, which the cancel leaves held (left behind where `G` may
raise or be captured, so `X` drops there), and then runs the exit at `z`.  `[spec §51]` -/
theorem last_cont {δ : LSub} {T' : OpTab} {Px' : Table} (hPx' : Px'.Mono) {G : Row}
    (hGT : (Row.tab G δ).Le T') (hGu : ∀ n i o, Row.find G n i = some o → o.q ≠ .unr)
    {X : VTy} (hXd : G.Cancels → X.OwnFree) {Qout : List SRec → Val → WProp} {en : OpEnt}
    (hq : en.q ≠ .lin) {B : VTy} (hPB : ∀ ls w ρ, vC true B ls δ w ρ → en.PB ls w ρ)
    {j : Nat} {vn nfv : Val} (hnf : PureSteps (pickE j (.val vn)) (.val nfv))
    (hX : ∀ ls z σ, vC true X ls δ z σ →
      ewpTS ls (.app (.val nfv) (.val z)) (orTab (opTable T') Px') Qout σ)
    {κ : Val} {ls : List SRec} {v : Val} {ρ : WRes}
    (h : (vC true (.sum B X) ls δ v ⋆
      KapRelT (orTab (opTable T') Px') Qout en (some (Row.tab G δ)) ls κ) ρ) :
    ewpTS ls ((ubindK (lastN j κ vn) (lastD κ)).plug (.val v)) (orTab (opTable T') Px') Qout ρ := by
  have hM := orTab_mono (opTable_mono T') hPx'
  obtain ⟨σ₁, σ₂, hc, hv, hk⟩ := h
  rcases hv with ⟨y, τ₁, τ₂, hcy, hp, hy⟩ | ⟨z, τ₁, τ₂, hcz, hp, hz⟩
  · obtain ⟨rfl, rfl⟩ := hp
    rw [eq_of_compS_empty_left hcy] at hc
    exact ewp_pureSteps hM (lastN_inl j κ vn y) _ _ ρ
      ((hk.2 ls (Ext.refl ls σ₂)).1 y τ₂ ρ (hPB _ _ _ hy) (ResU.CompS.comm hc))
  · obtain ⟨rfl, rfl⟩ := hp
    rw [eq_of_compS_empty_left hcz] at hc
    refine ewp_pureSteps hM (lastN_inr j κ vn z) _ _ ρ ?_
    have hcan := (hk.2 ls (Ext.refl ls σ₂)).2 hq _ rfl
    refine ewp_frame_plain_or (Row.tab G δ) T' hGT Table.bot Px' hPx' (exitK j vn z)
      (exitK_plain j vn z).1 (exitK_plain j vn z).2 (fun ls => vC true X ls δ z)
      (fun _ _ hs σ h => vC_same hs h) (fun _ _ _ he h => vC_local true X he h) ?_ ?_ ?_
      (fun _ _ _ _ _ _ _ h => h.elim) (fun _ v => ⌜v = Val.unit⌝) Qout ?_
      ((ewp_orBot (opTable_mono _)).mpr hcan) hz (ResU.CompS.comm hc)
    · intro m i en' hT ha ls' σ h
      obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
      exact vC_noOwn_of_ownFree (hXd ⟨o, (Row.find_mem hf).1, OpSig.cancels_of_ent (Or.inr ha)⟩) h
    · intro m i en' hT hq'
      obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
      exact absurd hq' (hGu m i o hf)
    · intro m i en' hT ha hq' ls' K₁ ρ' σ ρ'' hcan' hσ hc'
      obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
      exact ent_plain δ _ (exitK_plain j vn z).1 ((exitK_plain j vn z).2 0)
        (vC_noOwn_of_ownFree (hXd ⟨o, (Row.find_mem hf).1, OpSig.cancels_of_ent (Or.inl hq')⟩) hσ) o
        hcan' hc'
    · rintro ls' w τ ⟨τa, τb, hcab, hw, hz'⟩
      obtain ⟨rfl, rfl⟩ := hw
      rw [eq_of_compS_empty_left hcab]
      exact ewp_pureSteps hM (exitK_steps j vn z nfv hnf) _ _ τb (hX ls' z τb hz')

/-- `[then]`'s premises at the finaliser `κ.2 ()`: `κ`'s relation is carried along the list, and
the finaliser cancels `κ` at its cancel row's table. -/
theorem lastD_run {Tb : Table} {Qout : List SRec → Val → WProp} {en : OpEnt} (hq : en.q ≠ .lin)
    {Tk : OpTab} {κ : Val} (ls : List SRec) :
    Entails (KapRelT Tb Qout en (some Tk) ls κ)
      (ewpTS ls (.app (.val (lastD κ)) (.val .unit)) (opTable Tk) (fun _ v => ⌜v = Val.unit⌝)) :=
  fun σ h => ewp_pureSteps (opTable_mono _) (lastD_steps κ) _ _ σ
    ((h.2 ls (Ext.refl ls σ)).2 hq _ rfl)

theorem lastD_post : ∀ (ls : List SRec) (v : Val) (ρ : WRes),
    (fun (_ : List SRec) (v : Val) => (⌜v = Val.unit⌝ : WProp)) ls v ρ → v = .unit ∧ NoOwn ρ :=
  fun _ _ _ h => ⟨h.2, h.1 ▸ noOwn_empty⟩

/-! ### The handler -/

/-- The handler value of a `[handle-last]` handler: the clauses written out from the works and the
exits. -/
def lastH (n : UInt32) (E : List (Qual × VTy × VTy)) (vr vw vn : Val) : Val :=
  hndVal n (qualsVal (E.map Prod.fst)) vr ⟨lastTuple E 0 (.val vw) (.val vn), isVal_lastTuple _ _ E 0⟩

/-- `κ`'s cancel branch at the operation `i`: the table of its own cancel row. -/
def lastTc (fs : Nat → CTy) (δ : LSub) (i : UInt32) : Option OpTab :=
  some (Row.tab (fs i.toNat).rowOf δ)

section
variable {δ : LSub} {S SW : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {Xs : Nat → VTy}
  {n : UInt32} {A R : VTy} (hnd : n ≠ divEff) (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
  (hlen : E.length ≤ 2 ^ 32) (hNZ : S.NZ) (hSW : RowLe SW S) (hSu : ¬ S.UnrD)
  (hCancel : ∀ o ∈ E, o.1 = .cancel ∨ (o.2.2.isZero && o.1 != .lin) = true)
  (hFin : ∀ j, j < E.length → LastFinOK S SW (fs j) (Xs j))
  {vr vw vn : Val} {ls₀ : List SRec}
  (hVr : vC true (retTy S A R) ls₀ δ vr PMap.empty)
  (hVw : vC true (worksTy S SW R Xs E 0) ls₀ δ vw PMap.empty)
  (hVn : vC true (exitsTy S R Xs E 0) ls₀ δ vn PMap.empty)

include hnS hlen hVw hVn in
/-- The clause of an operation of the handler, from its entry. -/
theorem last_clause_of {i : UInt32} {en : OpEnt}
    (hT : Row.tab (Row.ofEff n E 0 fs ++ S) δ n i = some en) :
    ∃ j, ∃ hj : j < E.length, i.toNat = j ∧
      en = OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), E[j].1, E[j].2.1, E[j].2.2, fs j⟩ ∧
      clauseAt (lastTuple E 0 (.val vw) (.val vn)) i.toNat =
        some ⟨lastClause j en.abort (.val vw) (.val vn), isVal_lastClause _ _ _ _⟩ ∧
      (∃ g, PureSteps (pickE j (.val vw)) (.val g) ∧
        vC true (workTy S SW R (Xs j) E[j]) ls₀ δ g PMap.empty) ∧
      ∃ g, PureSteps (pickE j (.val vn)) (.val g) ∧ vC true (exitTy S R (Xs j)) ls₀ δ g PMap.empty := by
  obtain ⟨j, hj, hji, -, rfl⟩ := Row.tab_ofEff_self hnS hlen hT
  obtain ⟨g, hg, hVg⟩ := worksTy_at E 0 hVw j hj
  obtain ⟨g', hg', hVg'⟩ := exitsTy_at E 0 hVn j hj
  rw [Nat.zero_add] at hVg hVg'
  refine ⟨j, hj, hji, rfl, ?_, ⟨g, hg, hVg⟩, g', hg', hVg'⟩
  rw [hji, clauseAt_lastTuple _ _ E 0 j hj]
  simp [OpSig.ent, OpSig.abort]

include hnS hlen hFin in
/-- `κ`'s cancel branch is above the entry's cancel obligation. -/
theorem last_hTc {T : OpTab} (hT₀ : ∀ i en, T n i = some en →
      Row.tab (Row.ofEff n E 0 fs ++ S) δ n i = some en) :
    ∀ i en, T n i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, lastTc fs δ i = some Tk →
      ∃ T₁, en.fin = some (cancelObl T₁) ∧ T₁.Le Tk := by
  intro i en hT ha hq Tk hTk
  obtain ⟨j, hj, hji, -, rfl⟩ := Row.tab_ofEff_self hnS hlen (hT₀ i en hT)
  have hcap := capB_of_ent ha hq
  simp only [lastTc, hji, Option.some.injEq] at hTk
  subst hTk
  refine ⟨Row.tab (fs j).rowOf δ, ?_, OpTab.Le.refl _⟩
  rw [OpSig.ent_fin, if_pos hcap, finObl_eq, if_neg (by simp [(hFin j hj).1])]

/-- A non-abortive operation of the handler is cancellable. -/
theorem last_cancel (hCancel : ∀ o ∈ E, o.1 = .cancel ∨ (o.2.2.isZero && o.1 != .lin) = true) {j : Nat}
    (hj : j < E.length) (ha : (E[j].2.2.isZero && E[j].1 != .lin) = false) : E[j].1 ≠ .lin := by
  rcases hCancel E[j] (List.getElem_mem hj) with h | h
  · rw [h]; decide
  · rw [ha] at h; cases h

include hnd hn0 hnS hlen hNZ hSW hSu hCancel hFin hVr hVw hVn in
/-- **`Closing` under a `[handle-last]` handler**: Core's `ewp_handle` at the closing tables; a
clause's work is in `Closing` at its row, under the finaliser frame (`closing_then`), whose answer
is `last_cont` at the closing table. -/
theorem last_closing (hSd : Row.divB S = true) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Closing (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (fun ls v => vC true A ls δ v) ls e ρ) :
    Closing (Row.tab S δ) (fun ls v => vC true R ls δ v) ls (hndE (lastH n E vr vw vn) e) ρ := by
  have hb := fun {T : OpTab} {ls e Q ρ} => @ewp_orBot _ _ (opTable T) (opTable_mono T) ls e Q ρ
  refine ewp_handle _ _ n hn0 ?_ (qualsVal (E.map Prod.fst)) vr _ _ _ (lastTc fs δ) ?_ ?_ ?_ ?_ h
  · intro m i hm
    unfold OpTab.closeAt
    rw [Row.tab_ofEff_ne δ hm]
  · intro i en hT ha
    have hk : ¬ (n = divEff ∧ i = 0) := fun h => hnd h.1
    rw [OpTab.closeAt_ne hk] at hT
    rw [capTag_ofEff hnS hlen i en hT]
  · refine last_hTc hnS hlen hFin fun i en hT => ?_
    have hk : ¬ (n = divEff ∧ i = 0) := fun h => hnd h.1
    rwa [OpTab.closeAt_ne hk] at hT
  · intro ls' v σ hv
    have hf := (hVr.2 ls' (ext_empty' ls₀ ls')) v σ σ hv (compS_empty_left σ)
    have := (cC_effOf_wp S R ls' δ _ σ).mp hf
    rw [hSd] at this
    exact closing_of_cwp this
  · intro i en hT
    have hk : ¬ (n = divEff ∧ i = 0) := fun h => hnd h.1
    rw [OpTab.closeAt_ne hk] at hT
    obtain ⟨j, hj, hji, rfl, hcl, ⟨g, hg, hVg⟩, nfv, hnf, hVnf⟩ :=
      last_clause_of hnS hlen hVw hVn hT
    refine ⟨_, hcl, fun ha ls' v κ σ hσ => ?_, fun ha ls' v σ hσ => ?_⟩
    · -- the work, under the finaliser frame
      show ewpTS ls' (.app (lastClause j (OpSig.ent δ _).abort (.val vw) (.val vn))
        (.pair (.val v) κ.1)) _ _ σ
      rw [ha]
      have hq := last_cancel hCancel hj ha
      obtain ⟨hFt, hFS, hFd, hFth, hFP, hFX⟩ := hFin j hj
      have hTcj : lastTc fs δ i = some (Row.tab (fs j).rowOf δ) := by simp [lastTc, hji]
      rw [hTcj] at hσ
      generalize hEj : E[j] = t at hVg ha hσ hq
      obtain ⟨q, A', B'⟩ := t
      have ha' : (B'.isZero && q != .lin) = false := ha
      simp only [workTy, ha'] at hVg
      obtain ⟨σa, σk, hck, hA', hK⟩ := hσ
      refine ewp_pureSteps (opTable_mono _) (lastClause_steps j vw vn g v κ hg) _ _ σ ?_
      have hy := (hVg.2 ls' (ext_empty' ls₀ ls')) v σa σa hA' (compS_empty_left σa)
      have hy' := (cC_effOf_wp SW (.sum B' (Xs j)) ls' δ _ σa).mp hy
      have hyc : Closing (Row.tab SW δ) (fun ls w => vC true (.sum B' (Xs j)) ls δ w) ls'
          (.app (.val g) (.val v)) σa := by
        cases hbw : Row.divB SW <;> rw [hbw] at hy'
        · exact closing_of_ewp hy'
        · exact closing_of_cwp hy'
      refine closing_then hSd hFd hNZ hSW hFS hFth hFP (lastN j κ vn) (lastD κ)
        (fun ls => KapRel (Row.tab S δ).closeAt (fun ls v => vC true R ls δ v)
          (OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), q, A', B', fs j⟩) (some (Row.tab (fs j).rowOf δ))
          ls κ)
        KapRelT.same KapRelT.ext (fun hu => absurd hu hSu) lastD_post
        (fun ls => lastD_run hq ls) _ _ (fun ls w τ hτ => ?_) hyc hK hck
      refine hb.mp (last_cont (T' := (Row.tab S δ).closeAt) (B := B')
        (en := OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), q, A', B', fs j⟩) Table.bot_const.mono
        (tab_le_closeAt hFS hSd hFd) (fun _ _ _ hf => find_not_unr hFS hSu hf) hFX hq
        (fun _ _ _ h => h) hnf (fun ls z τ hz => hb.mpr ?_) ?_)
      · have hf := (hVnf.2 ls (ext_empty' ls₀ ls)) z τ τ hz (compS_empty_left τ)
        have := (cC_effOf_wp S R ls δ _ τ).mp hf
        rw [hSd] at this
        exact closing_of_cwp this
      · obtain ⟨τ₁, τ₂, hcτ, hw, hk'⟩ := hτ
        exact ⟨τ₁, τ₂, hcτ, hw, KapRelT.mono (fun _ _ _ h => hb.mpr h) hk'⟩
    · -- an abortive operation's clause runs its work, at the outer row
      show ewpTS ls' (.app (lastClause j (OpSig.ent δ _).abort (.val vw) (.val vn)) (.val v)) _ _ σ
      rw [ha]
      generalize hEj : E[j] = t at hVg ha hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at ha hσ
      simp only [workTy, ha] at hVg
      rw [lastClause_abort]
      refine ewp_pureSteps (opTable_mono _) (tailClauseA_steps j vw g v hg) _ _ σ ?_
      have hy := (hVg.2 ls' (ext_empty' ls₀ ls')) v σ σ hσ (compS_empty_left σ)
      have hy' := (cC_effOf_wp S R ls' δ _ σ).mp hy
      rw [hSd] at hy'
      exact closing_of_cwp hy'

end

/-! ### The candidate -/

/-- The finaliser frame around a work, `κ` in the frame resumed into one segment of `Z`.  `P` is
what the frame's answer function and finaliser are, and the rest of what the proof reads of the
operation, none of it about `Z`. -/
def lastW₂ (TW To : OpTab) (Qout : List SRec → Val → WProp)
    (P : Val → OpEnt → OpTab → (List SRec → Val → WProp) → Val → Val → Prop) (Z : CPred) : CPred :=
  fun ls x ρ => ∃ (κ : Val) (y : Expr) (en : OpEnt) (Tk : OpTab) (Q₁ : List SRec → Val → WProp)
    (Nv Dv : Val) (ρy ρk : WRes), P κ en Tk Q₁ Nv Dv ∧ x = (ubindK Nv Dv).plug y ∧
    cwp TW Q₁ ls y ρy ∧ KapRelT (divTab To Qout Z) Qout en (some Tk) ls κ ρk ∧ ResU.CompS ρy ρk ρ

/-- One step of the candidate. -/
def lastG (Ti TW To : OpTab) (Qin Qout : List SRec → Val → WProp) (H : Val)
    (P : Val → OpEnt → OpTab → (List SRec → Val → WProp) → Val → Val → Prop) (Z : CPred) : CPred :=
  fun ls x ρ => tailW₁ Ti Qin H ls x ρ ∨ lastW₂ TW To Qout P Z ls x ρ ∨ cwp To Qout ls x ρ

/-- **The candidate**: the least fixed point of `lastG`. -/
def lastY (Ti TW To : OpTab) (Qin Qout : List SRec → Val → WProp) (H : Val)
    (P : Val → OpEnt → OpTab → (List SRec → Val → WProp) → Val → Val → Prop) : CPred :=
  fun ls x ρ => ∀ Z : CPred, (∀ ls x ρ, lastG Ti TW To Qin Qout H P Z ls x ρ → Z ls x ρ) → Z ls x ρ

section candidate
variable {Ti TW To : OpTab} {Qin Qout : List SRec → Val → WProp} {H : Val}
  {P : Val → OpEnt → OpTab → (List SRec → Val → WProp) → Val → Val → Prop}

theorem lastG_mono {Z Z' : CPred} (h : ∀ ls x ρ, Z ls x ρ → Z' ls x ρ) {ls : List SRec} {x : Expr}
    {ρ : WRes} (hg : lastG Ti TW To Qin Qout H P Z ls x ρ) : lastG Ti TW To Qin Qout H P Z' ls x ρ := by
  rcases hg with hg | ⟨κ, y, en, Tk, Q₁, Nv, Dv, ρy, ρk, hP, rfl, hy, hk, hc⟩ | hg
  · exact Or.inl hg
  · refine Or.inr (Or.inl ⟨κ, y, en, Tk, Q₁, Nv, Dv, ρy, ρk, hP, rfl, hy,
      KapRelT.mono (fun _ _ _ h' => ?_) hk, hc⟩)
    exact ewp_mono (divTab_mono _ _ _) (fun _ _ _ _ hd => divTab_le h (fun _ _ _ h => h) hd)
      (fun _ _ _ h => h) h'
  · exact Or.inr (Or.inr hg)

theorem lastY_fold {ls : List SRec} {x : Expr} {ρ : WRes}
    (h : lastG Ti TW To Qin Qout H P (lastY Ti TW To Qin Qout H P) ls x ρ) :
    lastY Ti TW To Qin Qout H P ls x ρ :=
  fun Z hZ => hZ _ _ _ (lastG_mono (fun _ _ _ hy => hy Z hZ) h)

theorem lastY_unfold {ls : List SRec} {x : Expr} {ρ : WRes} (h : lastY Ti TW To Qin Qout H P ls x ρ) :
    lastG Ti TW To Qin Qout H P (lastY Ti TW To Qin Qout H P) ls x ρ :=
  h _ fun _ _ _ hg => lastG_mono (fun _ _ _ h => lastY_fold h) hg

end candidate

section
variable {δ : LSub} {S SW : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {Xs : Nat → VTy}
  {n : UInt32} {A R : VTy} (hnd : n ≠ divEff) (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
  (hlen : E.length ≤ 2 ^ 32) (hNZ : S.NZ) (hSW : RowLe SW S) (hSu : ¬ S.UnrD)
  (hCancel : ∀ o ∈ E, o.1 = .cancel ∨ (o.2.2.isZero && o.1 != .lin) = true)
  (hFin : ∀ j, j < E.length → LastFinOK S SW (fs j) (Xs j))
  {vr vw vn : Val} {ls₀ : List SRec}
  (hVr : vC true (retTy S A R) ls₀ δ vr PMap.empty)
  (hVw : vC true (worksTy S SW R Xs E 0) ls₀ δ vw PMap.empty)
  (hVn : vC true (exitsTy S R Xs E 0) ls₀ δ vn PMap.empty)

/-- What the candidate's frame reads of the `j`-th operation. -/
def lastP (δ : LSub) (S : Row) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) (Xs : Nat → VTy)
    (n : UInt32) (R : VTy) (vn : Val) (ls₀ : List SRec) :
    Val → OpEnt → OpTab → (List SRec → Val → WProp) → Val → Val → Prop :=
  fun κ en Tk Q₁ Nv Dv => ∃ j, ∃ hj : j < E.length, ∃ nfv : Val,
    (E[j].2.2.isZero && E[j].1 != .lin) = false ∧
    en = OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), E[j].1, E[j].2.1, E[j].2.2, fs j⟩ ∧
    Tk = Row.tab (fs j).rowOf δ ∧ Q₁ = (fun ls v => vC true (.sum E[j].2.2 (Xs j)) ls δ v) ∧
    Nv = lastN j κ vn ∧ Dv = lastD κ ∧ PureSteps (pickE j (.val vn)) (.val nfv) ∧
    vC true (exitTy S R (Xs j)) ls₀ δ nfv PMap.empty

include hnd hn0 hnS hlen hNZ hSW hSu hCancel hFin hVr hVw hVn in
/-- **`[handle-last]` at a row holding `Div`**, by coinduction with the candidate `lastY`: the
handled computations under the handler (`ewp_handle_or`, the inner tick passing the handler),
and the finaliser frame around a work, one segment each (`cwpF_frame_then`), `κ` resumed or
cancelled by the frame's answer (`last_cont`).  `[spec §14, §19, §27, §51]` -/
theorem cwp_handle_last (hSd : Row.divB S = true) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cwp (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (fun ls v => vC true A ls δ v) ls e ρ) :
    cwp (Row.tab S δ) (fun ls v => vC true R ls δ v) ls (hndE (lastH n E vr vw vn) e) ρ := by
  have hSbd : Row.divB (Row.ofEff n E 0 fs ++ S) = true := by rw [Row.divB_ofEff_eq hnd]; exact hSd
  have hTi := Row.divOK_of_divB hSbd δ
  have hTo := Row.divOK_of_divB hSd δ
  have hTW := Row.divOK_of_le hSW hSd δ
  obtain ⟨o, hfo, hto⟩ := Row.divB_find hSd
  have hTo0 : Row.tab S δ divEff 0 = some (o.ent δ) := Row.tab_find hfo
  have hTo0' := OpSig.isTick_ent δ hto
  -- the candidate
  let Y := lastY (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (Row.tab SW δ) (Row.tab S δ)
    (fun ls v => vC true A ls δ v) (fun ls v => vC true R ls δ v) (lastH n E vr vw vn)
    (lastP δ S E fs Xs n R vn ls₀)
  -- the parts of the candidate, one segment each
  have hc : ∀ ls x ρ, cwp (Row.tab S δ) (fun ls v => vC true R ls δ v) ls x ρ →
      cwpF (Row.tab S δ) (fun ls v => vC true R ls δ v) Y ls x ρ :=
    fun _ _ _ h => cwpF_mono (fun _ _ _ h => lastY_fold (Or.inr (Or.inr h))) (cwp_out h)
  have hW₂ : ∀ ls x ρ, lastW₂ (Row.tab SW δ) (Row.tab S δ) (fun ls v => vC true R ls δ v)
      (lastP δ S E fs Xs n R vn ls₀) Y ls x ρ →
      cwpF (Row.tab S δ) (fun ls v => vC true R ls δ v) Y ls x ρ := by
    rintro ls x ρ ⟨κ, y, en, Tk, Q₁, Nv, Dv, ρy, ρk,
      ⟨j, hj, nfv, ha, rfl, rfl, rfl, rfl, rfl, hnf, hVnf⟩, rfl, hy, hk, hcy⟩
    have hq := last_cancel hCancel hj ha
    obtain ⟨-, hFS, hFd, hFth, hFP, hFX⟩ := hFin j hj
    refine cwpF_frame_then hSd hFd hNZ hSW hFS hFth hFP (lastN j κ vn) (lastD κ)
      (fun ls => KapRelT (divTab (Row.tab S δ) (fun ls v => vC true R ls δ v) Y)
        (fun ls v => vC true R ls δ v)
        (OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), E[j].1, E[j].2.1, E[j].2.2, fs j⟩)
        (some (Row.tab (fs j).rowOf δ)) ls κ)
      KapRelT.same KapRelT.ext (fun hu => absurd hu hSu) lastD_post (fun ls => lastD_run hq ls) _ _
      Y (fun ls y' ρ' ρ₂ ρ'' hy' hF hc' => lastY_fold (Or.inr (Or.inl ⟨κ, y', _, _, _, _, _, ρ',
        ρ₂, ⟨j, hj, nfv, ha, rfl, rfl, rfl, rfl, rfl, hnf, hVnf⟩, rfl, hy', hF, hc'⟩)))
      ?_ ?_ hy hk hcy
    · intro ls w τ hτ
      refine last_cont (T' := (Row.tab S δ).erase0) (B := E[j].2.2)
        (en := OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), E[j].1, E[j].2.1, E[j].2.2, fs j⟩)
        (Table.Const.mono fun _ _ _ _ _ h => h) (tab_le_erase0 hFS hSd hFd)
        (fun _ _ _ hf => find_not_unr hFS hSu hf) hFX hq (fun _ _ _ h => h) hnf
        (fun ls z τ hz => ?_) hτ
      have hf := (hVnf.2 ls (ext_empty' ls₀ ls)) z τ τ hz (compS_empty_left τ)
      have := (cC_effOf_wp S R ls δ _ τ).mp hf
      rw [hSd] at this
      exact hc _ _ _ this
    · intro ls w τ hτ
      refine closing_of_cwpF (last_cont (T' := (Row.tab S δ).erase0) (B := E[j].2.2)
        (en := OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), E[j].1, E[j].2.1, E[j].2.2, fs j⟩)
        (Table.Const.mono fun _ _ _ _ _ h => h) (tab_le_erase0 hFS hSd hFd)
        (fun _ _ _ hf => find_not_unr hFS hSu hf) hFX hq (fun _ _ _ h => h) hnf
        (fun ls z τ hz => ?_) hτ)
      have hf := (hVnf.2 ls (ext_empty' ls₀ ls)) z τ τ hz (compS_empty_left τ)
      have := (cC_effOf_wp S R ls δ _ τ).mp hf
      rw [hSd] at this
      exact hc _ _ _ this
  have hW₁ : ∀ ls x ρ, tailW₁ (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (fun ls v => vC true A ls δ v)
      (lastH n E vr vw vn) ls x ρ →
      cwpF (Row.tab S δ) (fun ls v => vC true R ls δ v) Y ls x ρ := by
    rintro ls x ρ ⟨e, rfl, he⟩
    refine ewp_handle_or _ _ _ _ (Table.Const.mono fun _ _ _ _ _ h => h) n hn0 ?_
      (qualsVal (E.map Prod.fst)) vr _ _ _ (lastTc fs δ) ?_ ?_ ?_ ?_ ?_ (cwp_out he)
    · intro m i hm
      unfold OpTab.erase0
      rw [Row.tab_ofEff_ne δ hm]
    · intro i en hT ha
      have hk : ¬ (n = divEff ∧ i = 0) := fun h => hnd h.1
      rw [OpTab.erase0_ne hk] at hT
      rw [capTag_ofEff hnS hlen i en hT]
    · refine last_hTc hnS hlen hFin fun i en hT => ?_
      have hk : ¬ (n = divEff ∧ i = 0) := fun h => hnd h.1
      rwa [OpTab.erase0_ne hk] at hT
    · -- a tick passes the handler
      intro ls' t Φ Φ' σ hp
      obtain ⟨K₁, en, rfl, hK₁, hT0, ht, hcont⟩ := tickStop_inv hTi hp
      rw [← Kont.plug_comp]
      refine tickStop_mk hTo0 hTo0' ((hndK (lastH n E vr vw vn)).comp K₁)
        (by rw [hasHnd_comp, hK₁]; simp [lastH, hndK_hasHnd]; exact hnd) fun ls'' he w hw => ?_
      have ho := hcont ls'' he w hw
      rw [Kont.plug_comp]
      exact ⟨lastY_fold (Or.inl ⟨_, rfl, ho.1⟩),
        last_closing hnd hn0 hnS hlen hNZ hSW hSu hCancel hFin hVr hVw hVn hSd ho.2⟩
    · intro ls' v σ hv
      have hf := (hVr.2 ls' (ext_empty' ls₀ ls')) v σ σ hv (compS_empty_left σ)
      have := (cC_effOf_wp S R ls' δ _ σ).mp hf
      rw [hSd] at this
      exact hc _ _ _ this
    · intro i en hT
      have hk : ¬ (n = divEff ∧ i = 0) := fun h => hnd h.1
      rw [OpTab.erase0_ne hk] at hT
      obtain ⟨j, hj, hji, rfl, hcl, ⟨g, hg, hVg⟩, nfv, hnf, hVnf⟩ :=
        last_clause_of hnS hlen hVw hVn hT
      refine ⟨_, hcl, fun ha ls' v κ σ hσ => ?_, fun ha ls' v σ hσ => ?_⟩
      · show ewpTS ls' (.app (lastClause j (OpSig.ent δ _).abort (.val vw) (.val vn))
          (.pair (.val v) κ.1)) _ _ σ
        rw [ha]
        have hTcj : lastTc fs δ i = some (Row.tab (fs j).rowOf δ) := by simp [lastTc, hji]
        rw [hTcj] at hσ
        have ha' : (E[j].2.2.isZero && E[j].1 != .lin) = false := ha
        have hVg' := hVg
        simp only [workTy, ha'] at hVg'
        obtain ⟨σa, σk, hck, hA', hK⟩ := hσ
        refine ewp_pureSteps (divTab_mono _ _ _) (lastClause_steps j vw vn g v κ hg) _ _ σ ?_
        have hy := (hVg'.2 ls' (ext_empty' ls₀ ls')) v σa σa hA' (compS_empty_left σa)
        have hy' := (cC_effOf_wp SW (.sum E[j].2.2 (Xs j)) ls' δ _ σa).mp hy
        have hyc : cwp (Row.tab SW δ) (fun ls w => vC true (.sum E[j].2.2 (Xs j)) ls δ w) ls'
            (.app (.val g) (.val v)) σa := by
          cases hb : Row.divB SW <;> rw [hb] at hy'
          · exact cwp_of_ewp hTW.keyNA hy'
          · exact hy'
        exact hW₂ _ _ _ ⟨κ, _, _, _, _, _, _, σa, σk,
          ⟨j, hj, nfv, ha', rfl, rfl, rfl, rfl, rfl, hnf, hVnf⟩, rfl, hyc, hK, hck⟩
      · show ewpTS ls' (.app (lastClause j (OpSig.ent δ _).abort (.val vw) (.val vn)) (.val v)) _ _ σ
        rw [ha]
        generalize hEj : E[j] = t at hVg ha hσ
        obtain ⟨q, A', B'⟩ := t
        simp only [OpSig.ent, OpSig.abort] at ha hσ
        simp only [workTy, ha] at hVg
        rw [lastClause_abort]
        refine ewp_pureSteps (divTab_mono _ _ _) (tailClauseA_steps j vw g v hg) _ _ σ ?_
        have hy := (hVg.2 ls' (ext_empty' ls₀ ls')) v σ σ hσ (compS_empty_left σ)
        have hy' := (cC_effOf_wp S R ls' δ _ σ).mp hy
        rw [hSd] at hy'
        exact hc _ _ _ hy'
  refine cwp_coind (W := Y) (fun ls x ρ hy => ?_) (lastY_fold (Or.inl ⟨e, rfl, h⟩))
  rcases lastY_unfold hy with hx | hx | hx
  · exact hW₁ _ _ _ hx
  · exact hW₂ _ _ _ hx
  · exact hc _ _ _ hx

end

section
variable {δ : LSub} {S SW : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {Xs : Nat → VTy}
  {n : UInt32} {A R : VTy} (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
  (hlen : E.length ≤ 2 ^ 32) (hNZ : S.NZ) (hSW : RowLe SW S) (hSu : ¬ S.UnrD)
  (hCancel : ∀ o ∈ E, o.1 = .cancel ∨ (o.2.2.isZero && o.1 != .lin) = true)
  (hFin : ∀ j, j < E.length → LastFinOK S SW (fs j) (Xs j))
  {vr vw vn : Val} {ls₀ : List SRec}
  (hVr : vC true (retTy S A R) ls₀ δ vr PMap.empty)
  (hVw : vC true (worksTy S SW R Xs E 0) ls₀ δ vw PMap.empty)
  (hVn : vC true (exitsTy S R Xs E 0) ls₀ δ vn PMap.empty)

include hn0 hnS hlen hNZ hSW hSu hCancel hFin hVr hVw hVn in
/-- **A `[handle-last]` handler at a row that does not hold `Div`**: Core's `ewp_handle`; a
clause's work runs at its row under the finaliser frame (`ewp_frame_then`), whose answer is
`last_cont`.  `[spec §19, §27, §51]` -/
theorem ewp_handle_last (hSd : Row.divB S = false) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e (opTable (Row.tab (Row.ofEff n E 0 fs ++ S) δ)) (fun ls v => vC true A ls δ v) ρ) :
    ewpTS ls (hndE (lastH n E vr vw vn) e) (opTable (Row.tab S δ)) (fun ls v => vC true R ls δ v) ρ := by
  have hb := fun {T : OpTab} {ls e Q ρ} => @ewp_orBot _ _ (opTable T) (opTable_mono T) ls e Q ρ
  have hSWd : Row.divB SW = false := by
    cases hbw : Row.divB SW
    · rfl
    · rw [Row.divB_le hSW hbw] at hSd; cases hSd
  refine ewp_handle _ _ n hn0 (fun m i hm => Row.tab_ofEff_ne δ hm) (qualsVal (E.map Prod.fst)) vr
    _ _ _ (lastTc fs δ) (fun i en hT _ => capTag_ofEff hnS hlen i en hT)
    (last_hTc hnS hlen hFin fun _ _ h => h) ?_ ?_ h
  · intro ls' v σ hv
    have hf := (hVr.2 ls' (ext_empty' ls₀ ls')) v σ σ hv (compS_empty_left σ)
    exact (cC_effOf S R ls' δ _ σ hSd).mp hf
  · intro i en hT
    obtain ⟨j, hj, hji, rfl, hcl, ⟨g, hg, hVg⟩, nfv, hnf, hVnf⟩ := last_clause_of hnS hlen hVw hVn hT
    refine ⟨_, hcl, fun ha ls' v κ σ hσ => ?_, fun ha ls' v σ hσ => ?_⟩
    · show ewpTS ls' (.app (lastClause j (OpSig.ent δ _).abort (.val vw) (.val vn))
        (.pair (.val v) κ.1)) _ _ σ
      rw [ha]
      have hq := last_cancel hCancel hj ha
      obtain ⟨-, hFS, -, hFth, hFP, hFX⟩ := hFin j hj
      have hTcj : lastTc fs δ i = some (Row.tab (fs j).rowOf δ) := by simp [lastTc, hji]
      rw [hTcj] at hσ
      have ha' : (E[j].2.2.isZero && E[j].1 != .lin) = false := ha
      have hVg' := hVg
      simp only [workTy, ha'] at hVg'
      obtain ⟨σa, σk, hck, hA', hK⟩ := hσ
      refine ewp_pureSteps (opTable_mono _) (lastClause_steps j vw vn g v κ hg) _ _ σ ?_
      have hy := (hVg'.2 ls' (ext_empty' ls₀ ls')) v σa σa hA' (compS_empty_left σa)
      have hy' := (cC_effOf SW (.sum E[j].2.2 (Xs j)) ls' δ _ σa hSWd).mp hy
      refine ewp_frame_then δ S SW (fs j).rowOf hNZ hSW hFS hFth hFP (lastN j κ vn) (lastD κ)
        (fun ls => KapRel (Row.tab S δ) (fun ls v => vC true R ls δ v)
          (OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), E[j].1, E[j].2.1, E[j].2.2, fs j⟩)
          (some (Row.tab (fs j).rowOf δ)) ls κ)
        KapRelT.same KapRelT.ext (fun hu => absurd hu hSu) lastD_post
        (fun ls => lastD_run hq ls) _ _ (fun ls w τ hτ => ?_) hy' hK hck
      refine hb.mp (last_cont (T' := Row.tab S δ) (B := E[j].2.2)
        (en := OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), E[j].1, E[j].2.1, E[j].2.2, fs j⟩)
        Table.bot_const.mono (Row.tab_le δ hFS) (fun _ _ _ hf => find_not_unr hFS hSu hf) hFX hq
        (fun _ _ _ h => h) hnf (fun ls z τ hz => hb.mpr ?_) ?_)
      · have hf := (hVnf.2 ls (ext_empty' ls₀ ls)) z τ τ hz (compS_empty_left τ)
        exact (cC_effOf S R ls δ _ τ hSd).mp hf
      · obtain ⟨τ₁, τ₂, hcτ, hw, hk'⟩ := hτ
        exact ⟨τ₁, τ₂, hcτ, hw, KapRelT.mono (fun _ _ _ h => hb.mpr h) hk'⟩
    · show ewpTS ls' (.app (lastClause j (OpSig.ent δ _).abort (.val vw) (.val vn)) (.val v)) _ _ σ
      rw [ha]
      generalize hEj : E[j] = t at hVg ha hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at ha hσ
      simp only [workTy, ha] at hVg
      rw [lastClause_abort]
      refine ewp_pureSteps (opTable_mono _) (tailClauseA_steps j vw g v hg) _ _ σ ?_
      have hy := (hVg.2 ls' (ext_empty' ls₀ ls')) v σ σ hσ (compS_empty_left σ)
      exact (cC_effOf S R ls' δ _ σ hSd).mp hy

end

/-- **`[handle-last]`** (T-A): `handle_n e with (h_ret, ws, nfs)`, the clauses written out from the
works `ws` and the exits `nfs` (`lastTuple`).  The handler's operations are cancellable or abortive,
the work's row `Σ_W ≤ Σ`, `Σ` with no unrestricted operation at any depth (`κ` is not
persistent), and each operation's cancel row as `LastFinOK` says.  At a row holding `Div` the
handled computation's ticks pass the handler (`cwp_handle_last`); elsewhere it is Core's handler
(`ewp_handle_last`).  The Fundamental Property is applied to `h_ret`, the works, the exits and
`e`; no term the rule reads mentions `κ`.  `[spec §14, §19, §27, §51]` -/
theorem handleL_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Hr Hw Hn e : Expr} {S SW : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {Xs : Nat → VTy} {n : UInt32} {A R : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hHr : Hr.ValFormIn Γ₁)
    (hHw : Hw.ValFormIn Γ₁) (hHn : Hn.ValFormIn Γ₁)
    (hc : SemV Δ Γ₁ (.pair Hr (.pair Hw Hn))
      (.tensor (retTy S A R) (.tensor (worksTy S SW R Xs E 0) (exitsTy S R Xs E 0))))
    (hn0 : n ≠ 0) (hnd : n ≠ divEff) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hNZ : S.NZ) (hCancel : ∀ o ∈ E, o.1 = .cancel ∨ (o.2.2.isZero && o.1 != .lin) = true)
    (hSW : RowLe SW S) (hSu : ¬ S.UnrD)
    (hFin : ∀ j, j < E.length → LastFinOK S SW (fs j) (Xs j))
    (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) :
    SemC Δ Γ (hndExpr n (E.map Prod.fst) (.pair Hr (lastTuple E 0 Hw Hn)) e) (CTy.effOf S R) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨hlw₁, hs₁⟩ := gDenC_iff.mp hg₁
  have hρ₁ : ρ₁ = PMap.empty := gSepC_deadP hd hs₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ (.pair Hr (.pair Hw Hn))) :=
    isVal_psub_valFormIn hlw₁ (.pair hHr (.pair hHw hHn))
  have hH' := hc δ γ ls PMap.empty hδ hg₁
  have hE' := (cC_effOf_wp _ A ls δ _ ρ₂).mp (he δ γ ls ρ₂ hδ hg₂)
  rw [Row.divB_ofEff_eq hnd] at hE'
  show cC _ ls δ (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) (.pair Hr (lastTuple E 0 Hw Hn)) e)) ρ₂
  rw [psub_hndExpr]
  simp only [Expr.psub]
  rw [show Expr.psub 0 γ (lastTuple E 0 Hw Hn) = lastTuple E 0 (substAll γ Hw) (substAll γ Hn) from
    lastTuple_psub γ Hw Hn E 0]
  refine (cC_effOf_wp S R ls δ _ ρ₂).mpr ?_
  have hT₀ : (VTy.tensor (retTy S A R)
      (.tensor (worksTy S SW R Xs E 0) (exitsTy S R Xs E 0))).Persistent := by
    simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true]
    exact ⟨retTy_persistent S A R, worksTy_persistent S SW R Xs E 0, exitsTy_persistent S R Xs E 0⟩
  -- the handler's values, read off `wpTS` at the run's start
  have key : ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ₂ → ResU.CompS ρf ρ₂ fρ →
      TW fρ ps (rsOf ls) → Tagged fρ ps ls → ∃ ls' vr vw vn,
        Expr.psub 0 γ Hr = vr.1 ∧ substAll γ Hw = vw.1 ∧ substAll γ Hn = vn.1 ∧
        vC true (retTy S A R) ls' δ vr PMap.empty ∧
        vC true (worksTy S SW R Xs E 0) ls' δ vw PMap.empty ∧
        vC true (exitsTy S R Xs E 0) ls' δ vn PMap.empty := by
    intro ρf fρ ps hf hcf hT htg
    obtain ⟨ls', ρ', -, hv⟩ := wpTS_val_post (v := ⟨substAll γ (.pair Hr (.pair Hw Hn)), hval⟩) hH'
      (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg
    have hρ' : ρ' = PMap.empty := vP_empty_of_persistent hT₀ hv
    subst hρ'
    obtain ⟨vr, vwn, h⟩ := hv
    obtain ⟨hpair, σ₁, σ₂, -, hVr, hVwn⟩ := pure_sep_iff.mp h
    have hσ₁ : σ₁ = PMap.empty := vP_empty_of_persistent (retTy_persistent S A R) hVr
    subst hσ₁
    obtain ⟨vw, vn, h'⟩ := hVwn
    obtain ⟨hpair', τ₁, τ₂, -, hVw, hVn⟩ := pure_sep_iff.mp h'
    have hτ₁ : τ₁ = PMap.empty := vP_empty_of_persistent (worksTy_persistent S SW R Xs E 0) hVw
    have hτ₂ : τ₂ = PMap.empty := vP_empty_of_persistent (exitsTy_persistent S R Xs E 0) hVn
    subst hτ₁ hτ₂
    have hHe : substAll γ (.pair Hr (.pair Hw Hn)) = (Val.pair vr vwn).1 := congrArg Subtype.val hpair
    rw [hpair'] at hHe
    simp only [substAll, Expr.psub, Val.pair] at hHe
    obtain ⟨h₁, h₂⟩ := Expr.pair.inj hHe
    obtain ⟨h₃, h₄⟩ := Expr.pair.inj h₂
    exact ⟨ls', vr, vw, vn, h₁, h₃, h₄, hVr, hVw, hVn⟩
  cases hSd : Row.divB S <;> rw [hSd] at hE'
  · refine ewp_fold (opTable_mono _) ?_
    intro ρf fρ ps hf hcf hT htg Al k
    obtain ⟨ls', vr, vw, vn, h₁, h₂, h₃, hVr, hVw, hVn⟩ := key ρf fρ ps hf hcf hT htg
    rw [h₁, h₂, h₃]
    exact ewp_unfold (opTable_mono _) (ewp_handle_last (fs := fs) hn0 hnS hlen hNZ hSW hSu hCancel hFin
      hVr hVw hVn hSd hE') ρf fρ ps hf hcf hT htg Al k
  · refine cwp_roll (ewp_fold (divTab_mono _ _ _) ?_)
    intro ρf fρ ps hf hcf hT htg Al k
    obtain ⟨ls', vr, vw, vn, h₁, h₂, h₃, hVr, hVw, hVn⟩ := key ρf fρ ps hf hcf hT htg
    rw [h₁, h₂, h₃]
    exact ewp_unfold (divTab_mono _ _ _) (cwp_out (cwp_handle_last (fs := fs) hnd hn0 hnS hlen hNZ
      hSW hSu hCancel hFin hVr hVw hVn hSd hE')) ρf fρ ps hf hcf hT htg Al k

end BoCa.Fig16.LogRel.Core

end
