import Core.AffTy

/-!
# Core — `[gen]`: a generator whose suspended rest is a bounded affine closure  `[spec §24]`

`docs/effects-tr` §15 (D14.3–D14.7, L14.3, T14.4, T14.6), transcribed.  A body `M` performs one
affine, resuming operation `yield : B_y ↠ A` of the name `n`.  `gen M` handles it with

    H_gen ≜ (h_ret, [h_yield])
      h_ret   ≜ λ_. done to d. return (inj₂ (), d)        (the body returned)
      h_yield ≜ λ(b, κ). return (inj₁ b, κ)                (the clause returns the continuation)

so `gen M` answers `(inj₁ b, κ)` at the body's first `yield`, and `(inj₂ (), done)` when the
body returns.  The rule `[gen]` (D14.7) types that answer at

    F((B_y ⊕ 1) ⊗ [@c] U(Aff^c A (B_y ⊕ 1)))

when the body's context and `A` outlive `@c`: the continuation is a bounded affine closure
(SPEC §22), whose `call` resumes it and whose `close` cancels it.  `κ : U(…)` has no outlives
rule, so `[]I` cannot box it; that is why `[gen]` is a rule.

The proof, in the TR's order:

- `Qgen` is D14.4's postcondition: the greatest fixed point of `genF`, monotone in its argument
  because `Q` occurs only as an `ewpTS` postcondition (`genF_mono`).
- `ewp_gen` is L14.3: one application of `ewp_handle` at `Tin = T_y`, `Tout = ∅`.
- `affBox_of_kapRel` is T14.4: a continuation whose resource lies in `Res_{δ(c)}` and that is in
  `KapRel ∅ Qgen` is in `𝒱⟦[@c] U(Aff^c A B)⟧`, by `aff_coind` at the candidate `R_κ ∪ nuRel`.
- `gen_compatC` is T14.6 followed by T14.4: 6.62 puts the body's resource in `Res_{δ(c)}`, L14.2
  (`wpTS_box`, [TR] 6.147) keeps every suspension there, and T14.4 reads the continuation off.

The hypothesis T14.6 does not need, "no lend open at a suspension", is the kernel's T1: a
borrow's callback performs only abortive operations (SPEC §19, `Row.Unwind`).

**`done`.** D14.3 builds `done` by `d_mkBox` at the state `1`, "so `fundamentalC` puts it in
`vC (affBox c A B)`".  `fundamentalC`'s induction cannot reach a derivation that is not a premise,
so the rule takes `done`'s derivation as a premise on the fixed closed term `genDoneE`, as the
unwinding borrows take their finaliser's (`withbor1U`'s `hd`).  `d_genDone` (`GenRules.lean`)
derives it whenever `A` is persistent.  Only `done`'s relation is used (T14.4's right disjunct),
so `Qgen`'s right disjunct names the closure by its relation.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Step1N Head Kont performE raiseE opPayload cancelVal hndE
  ccatchE hndVal kappa clauseAt)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The operation, the types and the terms -/

/-- `yield : B_y ↠ A`, affine, the operation `0` of the name `n`.  (D14.3's `en_y`.) -/
def genOp (n : UInt32) (By A : VTy) : OpSig := ⟨n, 0, .aff, By, A⟩

/-- `B = B_y ⊕ 1`: an element, or the end. -/
abbrev genB (By : VTy) : VTy := .sum By .unit

/-- The answer of `[gen]`: `(B_y ⊕ 1) ⊗ [@c] U(Aff^c A (B_y ⊕ 1))`. -/
abbrev genTy (c : Lifetime.Life) (A By : VTy) : VTy := .tensor (genB By) (affBox c A (genB By))

/-- `done`'s step, at the state `s : 1`: `λs. ⟨λa. return (inj₂ (), s), ()⟩`.  Every call answers
the end and hands the state back; `close` answers `()`. -/
def doneStep : Val :=
  .lam (withPair (.val (.lam (.pair (.val (.inj₂ .unit)) (.var 3)))) (.val .unit))

/-- `done`: the finished generator, `mkE` at the state `()` with `doneStep` (D14.3). -/
def genDoneE (c : Lifetime.Life) (A By : VTy) : Expr :=
  mkE c A (genB By) (.val .unit) doneStep (.var 0)

/-- `h_ret ≜ λ_. done to d. return (inj₂ (), d)`. -/
def genHr (c : Lifetime.Life) (A By : VTy) : Val :=
  .lam (bindE (genDoneE c A By) (.pair (.val (.inj₂ .unit)) (.var 0)))

/-- `h_yield ≜ λp. let (b, κ) = p in return (inj₁ b, κ)`. -/
def genClause : Val := .lam (.letpair (.var 0) (.pair (.inj₁ (.var 1)) (.var 0)))

/-- The clauses' tuple, `(h_yield, ())`. -/
def genHs : Val := .pair genClause .unit

/-- `H_gen`. -/
def genH (n : UInt32) (c : Lifetime.Life) (A By : VTy) : Val := hndVal n (genHr c A By) genHs

/-- `gen M ≜ hnd H_gen M`.  `[spec §24]` -/
def genE (n : UInt32) (c : Lifetime.Life) (A By : VTy) (M : Expr) : Expr := hndE (genH n c A By) M

/-! ### Closed terms -/

theorem genDoneE_closed (c : Lifetime.Life) (A By : VTy) : closedAt 0 (genDoneE c A By) = true := by
  have hu : ∀ k, closedAt k (affUnfoldV c A (genB By)).1 = true :=
    fun k => closedAt_mono _ (unfoldV_closed _) (Nat.zero_le k)
  simp [genDoneE, mkE, bindE, packE, withPair, doneStep, closedAt, hu]

theorem genHr_closed (c : Lifetime.Life) (A By : VTy) : closedAt 0 (genHr c A By).1 = true := by
  have h := closedAt_mono _ (genDoneE_closed c A By) (Nat.zero_le 1)
  simp [genHr, bindE, closedAt, h]

theorem genH_closed (n : UInt32) (c : Lifetime.Life) (A By : VTy) :
    closedAt 0 (genH n c A By).1 = true := by
  have h := genHr_closed c A By
  simp [genH, hndVal, genHs, genClause, Val.pair, closedAt] at h ⊢
  exact ⟨rfl, h⟩

/-- A closing substitution passes the closed handler. -/
theorem substAll_genE (n : UInt32) (c : Lifetime.Life) (A By : VTy) (γ : List Val) (M : Expr) :
    substAll γ (genE n c A By M) = genE n c A By (substAll γ M) := by
  show Expr.psub 0 γ (hndE _ M) = hndE _ (Expr.psub 0 γ M)
  simp only [hndE, Expr.psub]
  rw [psub_closedAt _ γ (genH_closed n c A By) (Nat.le_refl 0)]
  rfl

theorem clauseAt_genHs : clauseAt genHs.1 0 = some genClause := by
  simp [clauseAt, genHs, Val.pair, genClause]

/-! ### `Q_gen` (D14.4) -/

/-- `yield`'s entry at `δ`: affine, resuming at a nonzero `A`, `PA = 𝒱⟦B_y⟧`, `PB = 𝒱⟦A⟧`. -/
abbrev genEnt (δ : LSub) (n : UInt32) (By A : VTy) : OpEnt := (genOp n By A).ent δ

/-- `KapRel` is monotone in its postcondition (`ewp_mono`). -/
theorem KapRel.mono {T : OpTab} {Q Q' : List SRec → Val → WProp}
    (hQ : ∀ ls v ρ, Q ls v ρ → Q' ls v ρ) {en : OpEnt} {ls : List SRec} {κ : Val} {ρ : WRes}
    (h : KapRel T Q en ls κ ρ) : KapRel T Q' en ls κ ρ :=
  ⟨h.1, fun ls' he => ⟨fun w ρ₁ ρ₂ hB hc =>
    ewp_mono (opTable_mono T) (fun _ _ _ _ h => h) hQ ((h.2 ls' he).1 w ρ₁ ρ₂ hB hc),
    (h.2 ls' he).2⟩⟩

/-- `KapRel` is Kripke along `Ext`. -/
theorem KapRel.ext {T : OpTab} {Q : List SRec → Val → WProp} {en : OpEnt} {ls ls' : List SRec}
    {κ : Val} {ρ : WRes} (h : KapRel T Q en ls κ ρ) (he : Ext ls ls' ρ) :
    KapRel T Q en ls' κ ρ :=
  ⟨h.1, fun ls'' he' => h.2 ls'' (Ext.trans he he')⟩

/-- D14.4's operator: an element `b` beside a continuation in `KapRel ∅ Q`, or the end beside
the finished closure.  `[spec §24]` -/
def genF (c : Lifetime.Life) (A By : VTy) (δ : LSub) (n : UInt32)
    (Q : List SRec → Val → WProp) : List SRec → Val → WProp := fun ls v =>
  BoLo.or
    (ex fun b : Val => ex fun κ : Val => ⌜v = .pair (.inj₁ b) κ⌝ ⋆
      (vC true By ls δ b ⋆ KapRel OpTab.empty Q (genEnt δ n By A) ls κ))
    (ex fun d : Val => ⌜v = .pair (.inj₂ .unit) d⌝ ⋆ vC true (affBox c A (genB By)) ls δ d)

/-- `genF` is monotone: `Q` occurs only as an `ewpTS` postcondition. -/
theorem genF_mono {c : Lifetime.Life} {A By : VTy} {δ : LSub} {n : UInt32}
    {Q Q' : List SRec → Val → WProp} (hQ : ∀ ls v ρ, Q ls v ρ → Q' ls v ρ) :
    ∀ ls v ρ, genF c A By δ n Q ls v ρ → genF c A By δ n Q' ls v ρ := by
  rintro ls v ρ (⟨b, κ, h⟩ | h)
  · obtain ⟨hv, ρb, ρk, hc, hb, hk⟩ := pure_sep_iff.mp h
    exact Or.inl ⟨b, κ, pure_sep_mk hv ⟨ρb, ρk, hc, hb, KapRel.mono hQ hk⟩⟩
  · exact Or.inr h

/-- `Q_gen`: the greatest fixed point of `genF`, written in `Prop` as `nuRel` is.
`[spec §24]` -/
def Qgen (c : Lifetime.Life) (A By : VTy) (δ : LSub) (n : UInt32) :
    List SRec → Val → WProp := fun ls v ρ =>
  ∃ Q : List SRec → Val → WProp, (∀ ls v ρ, Q ls v ρ → genF c A By δ n Q ls v ρ) ∧ Q ls v ρ

theorem Qgen_out {c : Lifetime.Life} {A By : VTy} {δ : LSub} {n : UInt32} :
    ∀ ls v ρ, Qgen c A By δ n ls v ρ → genF c A By δ n (Qgen c A By δ n) ls v ρ := by
  rintro ls v ρ ⟨Q, hQ, h⟩
  exact genF_mono (fun ls v ρ h => ⟨Q, hQ, h⟩) ls v ρ (hQ ls v ρ h)

theorem Qgen_roll {c : Lifetime.Life} {A By : VTy} {δ : LSub} {n : UInt32} :
    ∀ ls v ρ, genF c A By δ n (Qgen c A By δ n) ls v ρ → Qgen c A By δ n ls v ρ :=
  fun ls v ρ h => ⟨genF c A By δ n (Qgen c A By δ n),
    fun _ _ _ h' => genF_mono Qgen_out _ _ _ h', h⟩

/-! ### L14.3: the generator handler -/

/-- `ewpTS` at the empty operation table is `wpTS`. -/
theorem wp_of_ewp_empty {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls e (opTable OpTab.empty) Q ρ) : wpTS ls e Q ρ :=
  ewp_bot.mp (ewp_mono (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ h => (opTable_empty h).elim)
    (fun _ _ _ h => h) h)

/-- `h_ret ()` steps to `done to d. return (inj₂ (), d)`. -/
theorem genHr_subst (c : Lifetime.Life) (A By : VTy) (v : Val) :
    Expr.subst 0 v (bindE (genDoneE c A By) (.pair (.val (.inj₂ .unit)) (.var 0))) =
      bindE (genDoneE c A By) (.pair (.val (.inj₂ .unit)) (.var 0)) := by
  simp only [bindE, Expr.subst, subst_closedAt _ v (genDoneE_closed c A By) (Nat.le_refl 0)]
  rfl

/-- `h_yield (b, κ)` steps to `(inj₁ b, κ)`. -/
theorem genClause_letpair (b κ : Val) :
    Expr.subst 0 b (Expr.subst 0 (κ.shift 1 0)
      (Expr.subst (0 + 2) ((Val.pair b κ).shift 2 0) (.pair (.inj₁ (.var 1)) (.var 0)))) =
      (Val.pair (Val.inj₁ b) κ).1 := by
  show Expr.pair (Expr.inj₁ b.1) (Expr.subst 0 b (Expr.shift (0 + 1) 0 κ.1)) = _
  rw [Expr.subst_shift 0 0 0 b κ.1 (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  rfl

/-- **L14.3 (the generator handler).**  A body that answers `()` or stops at `yield` is handled
by `H_gen` into `Q_gen`, at the empty table: `ewp_handle` at `Tin = T_y`, `Tout = ∅`.
`[spec §24]` -/
theorem ewp_gen {n : UInt32} (hn0 : n ≠ 0) {c : Lifetime.Life} {A By : VTy} {δ : LSub}
    (hna : A.isZero = false)
    (hdone : ∀ ls, wpTS ls (genDoneE c A By)
      (fun ls' => vC true (affBox c A (genB By)) ls' δ) PMap.empty)
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e (opTable (Row.tab [genOp n By A] δ)) (fun ls v => vC true .unit ls δ v) ρ) :
    ewpTS ls (genE n c A By e) (opTable OpTab.empty) (Qgen c A By δ n) ρ := by
  refine ewp_handle (Row.tab [genOp n By A] δ) OpTab.empty n hn0 ?_ (genHr c A By) genHs _ _
    ?_ ?_ h
  · intro m i hm
    simp [Row.tab, Row.find, genOp, OpTab.empty, hm]
  · -- `[ret]`: `h_ret` builds `done` and answers the end
    intro ls' v σ hv
    obtain ⟨rfl, rfl⟩ := hv
    refine ewp_of_wp (opTable_mono _) ?_
    refine wpTS_step (fun μ => Step1N.head (Head.beta μ _ _) rfl) ls' _ PMap.empty ?_
    rw [genHr_subst]
    refine wpTS_bind (.appR (.val (.lam (.pair (.val (.inj₂ .unit)) (.var 0)))) .hole)
      (genDoneE c A By) ls' _ PMap.empty ?_
    refine wpTS_mono (fun ls'' d τ hd => ?_) PMap.empty (hdone ls')
    refine wpTS_step (fun μ => Step1N.head (Head.beta μ _ d) rfl) ls'' _ τ ?_
    exact wpTS_val ls'' (Val.pair (.inj₂ .unit) d) _ τ
      (Qgen_roll _ _ _ (Or.inr ⟨d, pure_sep_mk rfl hd⟩))
  · -- `[op]` at `yield`: the clause returns the element and the continuation
    intro i en hT
    have hi : i = 0 ∧ en = genEnt δ n By A := by
      by_cases h0 : i = 0
      · subst h0
        simp [Row.tab, Row.find, genOp] at hT
        exact ⟨rfl, hT.symm⟩
      · simp [Row.tab, Row.find, genOp, h0] at hT
    obtain ⟨rfl, rfl⟩ := hi
    refine ⟨genClause, clauseAt_genHs, fun _ ls' v κ σ hσ => ?_, fun ha => ?_⟩
    · refine ewp_step (opTable_mono _)
        (fun μ => Step1N.head (Head.beta μ _ (Val.pair v κ)) rfl) ls' _ σ ?_
      refine ewp_step (opTable_mono _)
        (fun μ => Step1N.head (Head.letpair μ v κ _) rfl) ls' _ σ ?_
      rw [genClause_letpair]
      exact ewp_val (opTable_mono _) (Qgen_roll _ _ _ (Or.inl ⟨v, κ, pure_sep_mk rfl hσ⟩))
    · simp [genEnt, OpSig.ent, OpSig.abort, genOp, hna] at ha

end BoCa.Fig16.LogRel.Core

end
