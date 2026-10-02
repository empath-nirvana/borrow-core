import GhostEnd.Branch

/-!
# GhostEnd — a borrower that loops around its yields

The kernel's loop is `bounded_fix (s, (k, a))` (`Core/BoundedFix.lean`): the step `s` runs on
its self-reference at the budget `k` and the argument, and the self-reference at `k` calls the
loop at `k − 1`. The budget is a number of the term. `open_boundedFix` is induction on it: the
loop is a borrower piece at every budget, given one step's behaviour on a self-reference whose
calls are pieces at the budget below. That measure does not mention a lifetime, and each
re-lend inside the step is covered by `Open`'s own unfolding (`Body.lean`).

The instance: the borrower holds `m` through every iteration and yields once per iteration.

    withbor ℓ (Λ. λm. bounded_fix (s, (K, m)))
    s = λ(self, m′). case self { inj₁ z. z; N_f m′ | inj₂ f. perform yield 1; f m′ }

`loop_spans_yields` holds at every budget `K`: the lend is open across all `K` yields. `N_f` is
derived from its typing (`d_nfAt`), as in `Branch.lean`; the iteration itself is reasoned about
directly, by `open_yield` and the machine's steps.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **A loop around yields, by induction on its budget.** -/
theorem open_boundedFix {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {T : VTy} {δ : LSub}
    {β : Life} {Vw : Life → List SRec → WProp} {Q : Life → List SRec → Val → WProp}
    (s a : Val) (P : List SRec → WProp)
    (hstep : ∀ k : UInt32,
      (k ≠ 0 → ∀ ls ρ, P ls ρ → Open Tb l T δ β Vw Q ls (boundedFixE s (k - 1) a) ρ) →
      ∀ ls ρ, P ls ρ → Open Tb l T δ β Vw Q ls (boundedFixNext s k a) ρ) :
    ∀ (n : Nat) (k : UInt32), k.toNat = n → ∀ ls ρ, P ls ρ →
      Open Tb l T δ β Vw Q ls (boundedFixE s k a) ρ := by
  intro n
  induction n with
  | zero =>
      intro k hk ls ρ hP
      refine open_step hTb (fun μ => Step1N.head (Head.boundedFix μ s k a) rfl)
        (hstep k (fun h0 => absurd (UInt32.toNat_inj.mp (by simpa using hk)) h0) ls ρ hP)
  | succ j ih =>
      intro k hk ls ρ hP
      have hkj : (k - 1).toNat = j := by
        have hk0 : k ≠ 0 := fun h => by subst h; simp at hk
        have : (k - 1).toNat = k.toNat - 1 := by
          rw [UInt32.toNat_sub_of_le]
          · rfl
          · rw [UInt32.le_iff_toNat_le]; simp; omega
        omega
      exact open_step hTb (fun μ => Step1N.head (Head.boundedFix μ s k a) rfl)
        (hstep k (fun _ ls' ρ' hP' => ih (k - 1) hkj ls' ρ' hP') ls ρ hP)

namespace Loop
open GhostEnd.Instance (yieldOp)
open GhostEnd.Branch (nfAt d_nfAt deadOf hbx hΔx hS hT hf)

/-- The step: `λ(self, m′). case self { inj₁ z. z; N_f m′ | inj₂ f. perform yield 1; f m′ }`. -/
def stepBody : Expr :=
  .letpair (.var 0) (.case (.var 1) (.seq (.var 0) (nfAt 1))
    (yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.app (.var 0) (.var 1))))

def sLoop : Val := Val.lam stepBody

/-- The borrower's body: `bounded_fix (s, (K, m))`. -/
def loopBody (K : UInt32) : Expr :=
  .app (.val (.prim .boundedFix)) (.pair (.val sLoop) (.pair (.val (Val.i32 K)) (.var 0)))

theorem sLoop_closed : closedAt 0 sLoop.1 = true := by decide

theorem loopBody_closed (K : UInt32) : closedAt 1 (loopBody K) = true := by
  simp [loopBody, closedAt, Expr.val, Val.i32]
  exact closedAt_mono _ sLoop_closed (Nat.zero_le _)

theorem loopBody_subst (K : UInt32) (l : BoCa.Loc) :
    substAll [Val.loc l] (loopBody K) = boundedFixE sLoop K (Val.loc l) := by
  rw [substAll_one]
  simp only [loopBody, Expr.subst, Expr.val, Val.i32, if_pos]
  rw [subst_closedAt _ _ sLoop_closed (Nat.zero_le _)]
  rfl

/-- `s (self, ℓ)` takes the β-step and the `let (self, m′)` step: `self` and `m′ := ℓ` bound. -/
theorem step_bind (fs : Val) (l : BoCa.Loc) (μ : Heap) :
    Step1N μ (Expr.subst 0 (Val.pair fs (Val.loc l)) stepBody) μ
      (.case (.val fs) (.seq (.var 0) (substAll [Val.loc l] (nfAt 0)))
        (yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.app (.var 0) (.val (Val.loc l))))) := by
  have := Step1N.head (ℍ := ℍ) (Head.letpair μ fs (Val.loc l)
    (.case (.var 1) (.seq (.var 0) (nfAt 1))
      (yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.app (.var 0) (.var 1))))) rfl
  convert this using 2
  all_goals simp [Expr.subst, stepBody, substAll_one, nfAt, bindE, yieldSeq, BoCa.BoLo.performE,
    opPayload, Expr.val, Val.loc, Val.i32, Val.pair, forget, Val.shift, Expr.shift, unit']

theorem nf0_closed : closedAt 0 (substAll [Val.loc l] (nfAt 0)) = true := by
  rw [substAll_one]
  simp [nfAt, bindE, Expr.subst, closedAt, forget, Expr.val, Val.loc, unit', Val.shift, Expr.shift]

/-- **The loop, at every budget.** -/
theorem loop_open {δ : LSub} (hδ : LifeCtx.empty.Models δ) {β : Life}
    (hβ : LifeCtx.empty.meetOfDom.interp δ = some β) (l : BoCa.Loc) :
    ∀ (n : Nat) (k : UInt32), k.toNat = n → ∀ ls ρ, ρ = PMap.empty →
      Open (opTable (Row.tab [yieldOp] δ)) l .unit δ β (viewP l .unit δ)
        (ansR 0 δ (.box (.var 0) .unit)) ls (boundedFixE sLoop k (Val.loc l)) ρ := by
  have hTb := opTable_mono (Row.tab [yieldOp] δ)
  refine open_boundedFix hTb sLoop (Val.loc l) (fun _ ρ => ρ = PMap.empty) ?_
  intro k ih ls ρ hρ
  refine open_step hTb (fun μ => Step1N.head (Head.beta μ stepBody _) rfl)
    (open_step hTb (fun μ => step_bind _ l μ) ?_)
  by_cases hk : k = 0
  · -- the budget is spent: `N_f` on `ℓ`, from its typing
    have hfs : fixSelf sLoop k = Val.inj₁ Val.unit := by unfold fixSelf; rw [if_pos hk]
    rw [hfs]
    refine open_step hTb (fun μ => Step1N.head (Head.case₁ μ Val.unit _ _) rfl) ?_
    refine open_step hTb (e' := substAll [Val.loc l] (nfAt 0)) (fun μ => ?_) ?_
    · have h := Step1N.head (ℍ := ℍ) (Head.seq μ (substAll [Val.loc l] (nfAt 0))) rfl
      convert h using 2
      simp [Expr.subst, subst_closedAt _ _ nf0_closed (Nat.zero_le _), Expr.val, Val.unit]
    · subst hρ
      exact open_of_rbody hT hδ hβ (GhostEnd.Branch.rb_nf []) l ls
  · -- one more yield, then the loop at the budget below
    have hfs : fixSelf sLoop k = Val.inj₂ (Val.lam (.app (.val (.prim .boundedFix))
        (.pair (.val (sLoop.shift 1 0)) (.pair (.val (.i32 (k - 1))) (.var 0))))) := by
      unfold fixSelf; rw [if_neg hk]
    rw [hfs]
    refine open_step hTb (fun μ => Step1N.head (Head.case₂ μ _ _ _) rfl) ?_
    have hy : ∀ ls, (yieldOp.ent δ).PA ls (Val.i32 1) PMap.empty := fun _ => ⟨rfl, 1, rfl⟩
    have e : Expr.subst 0 (Val.lam (.app (.val (.prim .boundedFix))
        (.pair (.val (sLoop.shift 1 0)) (.pair (.val (.i32 (k - 1))) (.var 0)))))
          (yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.app (.var 0) (.val (Val.loc l))))
        = yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.app (.val (Val.lam (.app
            (.val (.prim .boundedFix)) (.pair (.val (sLoop.shift 1 0))
              (.pair (.val (.i32 (k - 1))) (.var 0)))))) (.val (Val.loc l))) := by
      simp [Expr.subst, yieldSeq, BoCa.BoLo.performE, opPayload, Expr.val, Val.loc, Val.i32,
        Val.pair, Val.lam]
    rw [e]
    refine open_yield ((hS).linResume δ) (en := yieldOp.ent δ) (by simp [Row.tab, hf])
      (fun ls w ρ h => by simp only [OpSig.ent, yieldOp] at h; exact ⟨h.2, h.1⟩)
      (fun _ _ _ hv => noOwn_ptoMutS hv) (fun _ ρ => ρ = PMap.empty)
      (fun _ _ _ _ h => h) (fun _ _ h _ _ => by rw [h]; exact ResU.inStratum_empty _) hy
      ?_ ls ρ hρ
    intro ls' ρ' hρ'
    refine open_step hTb (fun μ => Step1N.head (Head.beta μ _ (Val.loc l)) rfl) ?_
    rw [fixSelf_body_subst]
    exact ih hk ls' ρ' hρ'

/-- **A borrower that loops around its yields**, at every budget `K`: from `ℓ ↦ v ⋆ 𝒱⟦1⟧(v)`,
`withbor ℓ (Λ. λm. bounded_fix (s, (K, m)))` is in `𝒞⟦F_{yield} (Ref 1 ⊗ 1)⟧`. -/
theorem loop_spans_yields (K : UInt32) (δ : LSub) (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true .unit ls δ v)
      (cC (CTy.effOf [yieldOp] (.tensor (.ref .unit) .unit)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam (loopBody K)), .lam⟩))) := by
  have hδ : LifeCtx.empty.Models δ := fun x u h => by
    simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  obtain ⟨β, hβ⟩ : ∃ β, LifeCtx.empty.meetOfDom.interp δ = some β :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf LifeCtx.empty.entries)
  intro ρ hρ
  refine (cC_effOf [yieldOp] _ ls δ _ ρ).mpr ?_
  refine withbor_relend (Row.tab [yieldOp] δ) (βP := ⊤) ?_ _ v
    (relend_lam2 (opTable_mono _) (loopBody_closed K) ?_) ρ hρ
  · intro ls w σ h
    rw [h.1]; exact ResU.inStratum_empty _
  · rw [loopBody_subst]
    exact relend_of_open_box (opTable_mono _) (by simp [VFree])
      (loop_open hδ hβ l _ K rfl ls _ rfl)

end Loop

end GhostEnd
