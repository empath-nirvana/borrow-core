import Frontend.Check.Kinds

/-!
# Frontend — Check — the clause kinds give their laws' premises  `[spec §19]`

`classify_sound`: the kind the checker records for an operation's clause (`classifyClause`) gives
the premise of that kind's law (`ClauseKind.Premise`, `Core/ClauseKinds.lean`) at the clause's
erasure, the term the handler runs. Each decision of the classifier on the typed term is matched
by a constructor of the premise on the erasure: `onPaths` by `OnPaths`, `resumeB` by
`TailLeaf` (`tailLeafB`, with the right unit), `cancelB` by `CancelLeaf`, `stateLeafB` by `StateLeaf`, `onceB` by `Once`.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.ClauseKinds
open BoCa.Fig16.LogRel.Core.Handlers (Returns0)

theorem TExpr.unSub_erase (t : TExpr) : t.unSub.erase = t.erase := by
  fun_induction TExpr.unSub t <;> simp_all [TExpr.erase]
theorem TExpr.unUse_erase (t : TExpr) : t.unUse.erase = t.erase := by
  fun_induction TExpr.unUse t <;> simp_all [TExpr.erase]
theorem returns0B_isVar0 {t : TExpr} (h : returns0B.isVar0 t = true) : t.erase = .var 0 := by
  unfold returns0B.isVar0 at h; split at h <;> simp_all [TExpr.erase]
theorem returns0B_sound {t : TExpr} (h : returns0B t = true) : Returns0 t.erase := by
  fun_induction returns0B t
  all_goals simp_all [TExpr.erase]
  all_goals first
    | exact .var
    | (have := returns0B_isVar0 h.1; rw [TExpr.unSub_erase] at this; rw [this]; exact .bind (by assumption))

theorem resumeB_sound' {k : Nat} {t : TExpr} (h : resumeB k t = true) :
    ∃ N, t.erase = .app (resumeAt k) N ∧ mentions k N = false := by
  rw [← TExpr.unSub_erase]
  unfold resumeB at h
  split at h
  next =>
    rename_i heq
    rw [heq]
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨rfl, hy⟩ := h
    exact ⟨_, rfl, by simpa [mentions] using hy⟩
  next => exact absurd h (by simp)

theorem resumeB_sound {k : Nat} {t : TExpr} (h : resumeB k t = true) : TailLeaf k t.erase := by
  obtain ⟨N, hN, hm⟩ := resumeB_sound' h
  rw [hN]; exact .resume hm

theorem tailLeafB_sound {k : Nat} {t : TExpr} (h : tailLeafB k t = true) : TailLeaf k t.erase := by
  fun_induction tailLeafB k t
  case case1 ih =>
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h₁, h₂⟩
    · exact resumeB_sound h
    · simp only [TExpr.erase]; exact .ret (ih h₁) (returns0B_sound h₂)
  case case2 ih =>
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h₁, h₂⟩
    · exact resumeB_sound h
    · simp only [TExpr.erase]; exact .ret (ih h₁) (returns0B_sound h₂)
  case case3 => exact resumeB_sound h

theorem isVarB_sound {k : Nat} {e : Expr} (h : isVarB k e = true) : e = .var k := by
  unfold isVarB at h; split at h <;> simp_all

theorem cancelHeadB_sound {k : Nat} {t : TExpr} (h : cancelHeadB k t = true) :
    t.erase = cancelAt k := by
  rw [← TExpr.unSub_erase]
  unfold cancelHeadB at h
  split at h
  next =>
    rename_i heq
    rw [heq]; simp only [beq_iff_eq] at h; subst h
    rfl
  next => exact absurd h (by simp)

theorem cancelB_sound {k : Nat} {t : TExpr} (h : cancelB k t = true) : CancelLeaf k t.erase := by
  unfold cancelB at h
  split at h
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨_, by simp [TExpr.erase, cancelHeadB_sound h.1], h.2⟩
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨_, by simp [TExpr.erase, cancelHeadB_sound h.1], h.2⟩
  · exact absurd h (by simp)

theorem forceArrB_sound {g : Nat} {t : TExpr} (h : forceArrB g t = true) : t.erase = .var g := by
  rw [← TExpr.unSub_erase]
  unfold forceArrB at h
  split at h
  next =>
    rename_i heq
    rw [heq]; simp only [beq_iff_eq] at h; subst h; rfl
  next => exact absurd h (by simp)

theorem appliesB_sound {g k : Nat} {t : TExpr} (h : appliesB g k t = true) :
    AppliesAt g k t.erase := by
  fun_induction appliesB g k t
  case case1 =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hf, hg⟩, hk⟩ := h
    simp only [TExpr.erase, forceArrB_sound hf]
    exact .apply (by simp [mentions]; omega) (by simp [mentions]; omega)
  case case2 => simp only [TExpr.erase]; simp_all
  case case3 ih₁ ih₂ =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [TExpr.erase]
    rcases h with ⟨⟨h₁, h₂⟩, h₃⟩ | ⟨h₁, h₂⟩
    · exact .bind h₁ h₂ (ih₁ h₃)
    · exact .ret (ih₂ h₁) (returns0B_sound h₂)
  case case4 ih₁ ih₂ =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [TExpr.erase]
    rcases h with ⟨⟨h₁, h₂⟩, h₃⟩ | ⟨h₁, h₂⟩
    · exact .bind h₁ h₂ (ih₁ h₃)
    · exact .ret (ih₂ h₁) (returns0B_sound h₂)
  all_goals simp_all

theorem stateLeafB_sound {k : Nat} {t : TExpr} (h : stateLeafB k t = true) :
    StateLeaf k t.erase := by
  unfold stateLeafB at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨N, hN, hm⟩ := resumeB_sound' h.1
    exact ⟨N, _, by simp [TExpr.erase, hN], hm, appliesB_sound h.2⟩
  · simp only [Bool.and_eq_true] at h
    obtain ⟨N, hN, hm⟩ := resumeB_sound' h.1
    exact ⟨N, _, by simp [TExpr.erase, hN], hm, appliesB_sound h.2⟩
  · exact absurd h (by simp)

theorem onceB_sound {k : Nat} {t : TExpr} (h : onceB k t = true) : Once k t.erase := by
  fun_induction onceB k t
  case case1 ih =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [TExpr.erase]; exact .head (ih h.1) h.2
  case case2 ih =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [TExpr.erase]; exact .head (ih h.1) h.2
  case case3 ih => simp only [TExpr.erase]; exact ih h
  case case4 =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨N, hN, hm⟩ := resumeB_sound' h; rw [hN]; exact .resume hm
    · rw [cancelHeadB_sound h]; exact .cancel

theorem onPaths_sound {leaf : Nat → TExpr → Bool} {L : Nat → Expr → Prop}
    (hl : ∀ k t, leaf k t = true → L k t.erase) {k : Nat} {t : TExpr}
    (h : onPaths leaf k t = true) : OnPaths L k t.erase := by
  fun_induction onPaths leaf k t
  case case1 ih₁ ih₂ =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with h | ⟨⟨h₀, h₁⟩, h₂⟩
    · exact .leaf (hl _ _ h)
    · simp only [TExpr.erase]; exact .case h₀ (ih₁ h₁) (ih₂ h₂)
  case case2 ih =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with h | ⟨h₀, h₁⟩
    · exact .leaf (hl _ _ h)
    · simp only [TExpr.erase]; exact .letpair h₀ (ih h₁)
  case case3 ih =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with h | ⟨h₀, h₁⟩
    · exact .leaf (hl _ _ h)
    · simp only [TExpr.erase]; exact .seq h₀ (ih h₁)
  case case4 ih ih' =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with (h | ⟨h₀, h₁⟩) | ⟨⟨h₀, h₁⟩, h₂⟩
    · exact .leaf (hl _ _ h)
    · simp only [TExpr.erase]; exact .bind h₀ (ih h₁)
    · simp only [TExpr.erase, isVarB_sound h₀]; exact .rebind h₁ (ih' h₂)
  case case5 ih ih' =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with (h | ⟨h₀, h₁⟩) | ⟨⟨h₀, h₁⟩, h₂⟩
    · exact .leaf (hl _ _ h)
    · simp only [TExpr.erase]; exact .bind h₀ (ih h₁)
    · simp only [TExpr.erase, isVarB_sound h₀]; exact .rebind h₁ (ih' h₂)
  case case6 ih =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact .leaf (hl _ _ h)
    · simp only [TExpr.erase]; exact ih h
  case case7 ih =>
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact .leaf (hl _ _ h)
    · simp only [TExpr.erase]; exact ih h
  case case8 => exact .leaf (hl _ _ h)

theorem stateFnB_sound {leaf : Nat → TExpr → Bool} {L : Nat → Expr → Prop}
    (hl : ∀ k t, leaf k t = true → L k t.erase) {k : Nat} {t : TExpr}
    (h : stateFnB leaf k t = true) : StateFn L k t.erase := by
  unfold stateFnB at h
  split at h
  · exact ⟨_, rfl, onPaths_sound hl h⟩
  · exact absurd h (by simp)

theorem classifyBody_sound (tM : TExpr) : (classifyBody tM).BodyPremise tM.erase := by
  unfold classifyBody
  split
  · next h => exact (onPaths_sound (fun _ _ h => tailLeafB_sound h) h).tailResumes
  split
  · next h => exact onPaths_sound (fun _ _ h => stateFnB_sound (fun _ _ h => stateLeafB_sound h) h) h
  split
  · next h =>
      refine onPaths_sound (fun _ _ h => ?_) h
      simp only [Bool.or_eq_true] at h
      exact h.elim (fun h => .inl (tailLeafB_sound h)) (fun h => .inr (cancelB_sound h))
  split
  · next h =>
      refine onPaths_sound (fun _ _ h => stateFnB_sound (fun _ _ h => ?_) h) h
      simp only [Bool.or_eq_true] at h
      exact h.elim (fun h => .inl (stateLeafB_sound h)) (fun h => .inr (cancelB_sound h))
  split
  · next h => exact onPaths_sound (fun _ _ h => onceB_sound h) h
  split
  · next h => exact onPaths_sound (fun _ _ h => stateFnB_sound (fun _ _ h => onceB_sound h) h) h
  trivial

/-- **The kind the checker records gives its law's premise** at the clause the handler runs: an
abortive operation's clause takes no `κ`; a control clause is `λp. let (x, κ) = p; M` and `M`
meets the kind's premise (`ClauseKind.Premise`).  `[spec §19]` -/
theorem classify_sound (o : Qual × VTy × VTy) (c : TExpr) :
    (classifyClause o (some c)).kind.Premise o c.erase := by
  unfold classifyClause
  by_cases ha : isAbortive o = true
  · simp only [ha, if_true]; exact ha
  · have ha' : isAbortive o = false := by simpa using ha
    simp only [ha', if_false, Bool.false_eq_true]
    split
    · rename_i tM heq
      have hP := classifyBody_sound tM
      have he : c.erase = .val (.lam (.letpair (.var 0) tM.erase)) := by
        rw [← TExpr.unUse_erase c]
        simp only [Option.map_some, Option.some.injEq] at heq
        rw [heq]; rfl
      have hne : classifyBody tM ≠ .abortive := by
        unfold classifyBody; split_ifs <;> simp
      revert hP hne
      generalize classifyBody tM = k
      intro hP hne
      cases k with
      | abortive => exact absurd rfl hne
      | stored => trivial
      | tail => exact ⟨ha', _, he, hP⟩
      | tailState => exact ⟨ha', _, he, hP⟩
      | resumeOrCancel s => cases s <;> exact ⟨ha', _, he, hP⟩
      | resumeOnce s => cases s <;> exact ⟨ha', _, he, hP⟩
    · simp [ClauseKind.Premise]

/-- The `j`-th component of a tuple `(e₀, (e₁, …))`. -/
def tupleAt : Nat → Expr → Option Expr
  | 0, .pair a _ => some a
  | j + 1, .pair _ b => tupleAt j b
  | _, _ => none

/-- The clause of the operation `j` in a handler's pair `(h_ret, (c₀, (c₁, …)))`. -/
def clauseAt (j : Nat) : Expr → Option Expr
  | .pair _ cs => tupleAt j cs
  | _ => none

theorem getElem?_replicate_none {α : Type} {n j : Nat} {c : α} :
    (List.replicate n (none : Option α))[j]? ≠ some (some c) := by
  rw [List.getElem?_replicate]; split <;> simp

/-- A component `clauseParts` reads is the tuple's component in the erasure. -/
theorem clauseParts_erase : ∀ (n : Nat) (t : TExpr) (j : Nat) (c : TExpr),
    (clauseParts n t)[j]? = some (some c) → tupleAt j t.erase = some c.erase
  | 0, _, _, _, h => by simp [clauseParts] at h
  | n + 1, t, j, c, h => by
    unfold clauseParts at h
    rw [← TExpr.unUse_erase t]
    split at h
    · rename_i c' t' heq
      rw [heq]
      cases j with
      | zero => simp at h; subst h; rfl
      | succ j => simpa [TExpr.erase, tupleAt] using clauseParts_erase n t' j c (by simpa using h)
    · exact absurd h getElem?_replicate_none

/-- **The kinds a `handle` node records give their laws' premises at the clauses the node
holds**: the kind of the operation `j` gives that kind's premise (`ClauseKind.Premise`) at the
`j`-th clause of the erasure of the node's own pair `tH`, the clause the handler runs for it.
`[spec §19]` -/
theorem classifyHandler_sound (E : List (Qual × VTy × VTy)) (tH : TExpr) {j : Nat}
    {o : Qual × VTy × VTy} {k : HKind} {e : Expr} (ho : E[j]? = some o)
    (hk : (classifyHandler E tH)[j]? = some k) (he : clauseAt j tH.erase = some e) :
    k.kind.Premise o e := by
  unfold classifyHandler at hk
  rw [List.getElem?_zipWith, ho] at hk
  generalize hp : (_ : List (Option TExpr))[j]? = p at hk
  cases p with
  | none => simp at hk
  | some p =>
    simp only [Option.some.injEq] at hk
    subst hk
    by_cases ha : isAbortive o = true
    · simp [classifyClause, ha, ClauseKind.Premise]
    · cases p with
      | none => simp [classifyClause, ha, ClauseKind.Premise]
      | some c =>
        have hc : clauseAt j tH.erase = some c.erase := by
          split at hp
          · rename_i tc
            rw [List.getElem?_append] at hp
            split at hp
            · simp only [TExpr.erase, clauseAt]
              exact clauseParts_erase _ _ _ _ hp
            · exact absurd hp getElem?_replicate_none
          · rw [List.getElem?_append] at hp
            split at hp <;> exact absurd hp getElem?_replicate_none
        rw [he, Option.some.injEq] at hc
        subst hc
        exact classify_sound o c

theorem zipWith_fst_append {α β : Type} (E : List α) (f : α → β → HKind) (g : α → Qual)
    (hf : ∀ a b, (f a b).q = g a) : ∀ (xs ys : List β), E.length ≤ ys.length →
    (E.zipWith f (xs ++ ys)).map (·.q) = E.map g := by
  induction E with
  | nil => intros; simp
  | cons a E ih =>
    intro xs ys hl
    cases xs with
    | nil =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
        simp only [List.nil_append, List.zipWith_cons_cons, List.map_cons, hf]
        have := ih [] ys (by simp at hl; omega)
        simpa using this
    | cons x xs =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.map_cons, hf]
      rw [ih xs ys (by simp at hl; omega)]

/-- **The qualifiers travel with the kinds**: the `handle` node's `ks` has one entry per
operation, carrying that operation's qualifier, the one `E` gives it.  `[spec §19, §25]` -/
theorem classifyHandler_quals (E : List (Qual × VTy × VTy)) (tH : TExpr) :
    (classifyHandler E tH).map (·.q) = E.map Prod.fst := by
  unfold classifyHandler
  exact zipWith_fst_append E _ Prod.fst (fun _ _ => rfl) _ _ (by simp)

end BoCa.Fig16.LogRel.Core.Check
