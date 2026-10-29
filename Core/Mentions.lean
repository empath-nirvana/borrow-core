import Core.PinDerives
import Core.ClauseKinds
import Core.Closed

/-!
# Core — a typed term mentions only live slots  `[spec §55]`

`CDerivesP.mentions_live`: a term `CDerivesP` types at `Γ` mentions only slots live in `Γ`. A dead
slot (a binder typed dead, a slot a split gives the other part, a slot a consumed context holds)
is never read. Induction on `CDerivesP`, as `closedAt_of_derives`: a leaf reads its slot, which
`Ctx.SoloP` makes live; a split's part's live slots are the whole's (`Ctx.SplitP.live_left`,
`live_right`); a binder's slot is the head of its premise's context; the constants are closed;
`[let-poly]`'s body mentions what its filled premise term does (`mentions_fill`); the relaxed rules
conclude at `r : Ref T` and read `r` alone.

This is what makes a split's use masks cover its parts (`Masks.Covers`, SPEC §55): a family of
derivations at every liveness between its uses and its absorption (`Fam`) has one at its uses
alone, where every slot it does not use is dead.
-/

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core.ClauseKinds (mentions mentions_closed)
open BoCa.Lifetime (LifeCtx)

/-- Slot `k` of `Γ` is live. -/
def Ctx.LiveAt (Γ : Ctx VTy) (k : Nat) : Prop := ∃ s, Γ[k]? = some s ∧ s.live = true

theorem Ctx.liveAt_cons_succ {s : Slot VTy} {Γ : Ctx VTy} {k : Nat} :
    Ctx.LiveAt (s :: Γ) (k + 1) ↔ Ctx.LiveAt Γ k := by
  simp [Ctx.LiveAt]

theorem Ctx.not_liveAt_dead {T : VTy} {Γ : Ctx VTy} : ¬ Ctx.LiveAt (⟨T, false⟩ :: Γ) 0 := by
  simp [Ctx.LiveAt]

theorem Ctx.liveAt_nil (k : Nat) : ¬ Ctx.LiveAt [] k := by simp [Ctx.LiveAt]

theorem Ctx.SplitP.liveAt_left {Γ Γ₁ Γ₂ : Ctx VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂) {k : Nat}
    (h : Ctx.LiveAt Γ₁ k) : Ctx.LiveAt Γ k := by
  obtain ⟨s, hs', hl⟩ := h; exact hs.live_left hs' hl

theorem Ctx.SplitP.liveAt_right {Γ Γ₁ Γ₂ : Ctx VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂) {k : Nat}
    (h : Ctx.LiveAt Γ₂ k) : Ctx.LiveAt Γ k := by
  obtain ⟨s, hs', hl⟩ := h; exact hs.live_right hs' hl

/-- A slot of a consumed context, up to persistent slots, that is live is so persistently; a
consumed context (`Ctx.Dead`) has none. -/
theorem Ctx.Dead.not_liveAt : ∀ {Γ : Ctx VTy}, BoCa.Ctx.Dead Γ → ∀ k, ¬ Ctx.LiveAt Γ k
  | [], _, k => Ctx.liveAt_nil k
  | _ :: _, .cons _, 0 => Ctx.not_liveAt_dead
  | _ :: _, .cons h, k + 1 => fun hl => Ctx.Dead.not_liveAt h k (Ctx.liveAt_cons_succ.mp hl)

/-! ### Mentions under the term builders -/

/-- A closed term mentions nothing. -/
theorem mentions_of_closed {e : Expr} (h : closedAt 0 e = true) (k : Nat) : mentions k e = false :=
  mentions_closed e h k (Nat.zero_le k)

theorem mentions_shift_lt {d : Nat} : ∀ (e : Expr) {c k : Nat}, k < c →
    mentions k (e.shift d c) = mentions k e
  | .var i, c, k, hk => by
      simp only [Expr.shift]; split <;> simp [mentions] <;> omega
  | .unit, _, _, _ | .loc _, _, _, _ | .prim _, _, _, _ => rfl
  | .pair a b, c, k, hk | .seq a b, c, k, hk | .app a b, c, k, hk => by
      simp only [Expr.shift, mentions, mentions_shift_lt a hk, mentions_shift_lt b hk]
  | .inj₁ a, c, k, hk | .inj₂ a, c, k, hk => by
      simp only [Expr.shift, mentions, mentions_shift_lt a hk]
  | .lam b, c, k, hk => by
      simp only [Expr.shift, mentions, mentions_shift_lt b (c := c + 1) (k := k + 1) (by omega)]
  | .letpair a b, c, k, hk => by
      simp only [Expr.shift, mentions, mentions_shift_lt a hk,
        mentions_shift_lt b (c := c + 2) (k := k + 2) (by omega)]
  | .case s a b, c, k, hk => by
      simp only [Expr.shift, mentions, mentions_shift_lt s hk,
        mentions_shift_lt a (c := c + 1) (k := k + 1) (by omega),
        mentions_shift_lt b (c := c + 1) (k := k + 1) (by omega)]

theorem mentions_shift_ge {d : Nat} : ∀ (e : Expr) {c k : Nat}, c ≤ k →
    mentions (k + d) (e.shift d c) = mentions k e
  | .var i, c, k, hk => by
      simp only [Expr.shift]; split <;> simp [mentions] <;> omega
  | .unit, _, _, _ | .loc _, _, _, _ | .prim _, _, _, _ => rfl
  | .pair a b, c, k, hk | .seq a b, c, k, hk | .app a b, c, k, hk => by
      simp only [Expr.shift, mentions, mentions_shift_ge a hk, mentions_shift_ge b hk]
  | .inj₁ a, c, k, hk | .inj₂ a, c, k, hk => by
      simp only [Expr.shift, mentions, mentions_shift_ge a hk]
  | .lam b, c, k, hk => by
      have := mentions_shift_ge (d := d) b (c := c + 1) (k := k + 1) (by omega)
      simp only [Expr.shift, mentions]; rw [show k + d + 1 = k + 1 + d by omega, this]
  | .letpair a b, c, k, hk => by
      have := mentions_shift_ge (d := d) b (c := c + 2) (k := k + 2) (by omega)
      simp only [Expr.shift, mentions, mentions_shift_ge a hk]
      rw [show k + d + 2 = k + 2 + d by omega, this]
  | .case s a b, c, k, hk => by
      have ha := mentions_shift_ge (d := d) a (c := c + 1) (k := k + 1) (by omega)
      have hb := mentions_shift_ge (d := d) b (c := c + 1) (k := k + 1) (by omega)
      simp only [Expr.shift, mentions, mentions_shift_ge s hk]
      rw [show k + d + 1 = k + 1 + d by omega, ha, hb]

/-- A term shifted at `0` mentions `k + d` where the term mentions `k`. -/
theorem mentions_shift0 (e : Expr) (d k : Nat) : mentions (k + d) (e.shift d 0) = mentions k e :=
  mentions_shift_ge e (Nat.zero_le k)

theorem mentions_pickE_eq : ∀ (j : Nat) (k : Nat) (t : Expr),
    mentions k (BoCa.Fig16.LogRel.Core.pickE j t) = mentions k t
  | 0, k, t => by simp [pickE, mentions]
  | j + 1, k, t => by
      simp only [pickE, mentions, mentions_pickE_eq j, Bool.or_eq_left_iff_imp]
      simp

theorem mentions_shift0_iff (e : Expr) (d m : Nat) :
    mentions m (e.shift d 0) = (decide (d ≤ m) && mentions (m - d) e) := by
  by_cases h : d ≤ m
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + d := ⟨m - d, by omega⟩
    rw [mentions_shift0]; simp
  · have := ClauseKinds.mentions_shift (d := d) (c := 0) (k := m) (Nat.zero_le m) (by omega) e
    rw [this]; simp [h]

theorem mentions_tailTuple {Hc : Expr} {k : Nat} : ∀ (E : List (Qual × VTy × VTy)) (j : Nat),
    mentions k (tailTuple E j Hc) = true → mentions k Hc = true
  | [], _, h => by simp [tailTuple, mentions, Expr.val, Val.unit] at h
  | (q, _, B) :: E, j, h => by
      simp only [tailTuple, mentions, Bool.or_eq_true] at h
      rcases h with h | h
      · by_contra hc
        simp only [Bool.not_eq_true] at hc
        unfold tailClause at h
        split at h <;>
          simp [mentions, mentions_pickE_eq, mentions_shift0_iff, resumeB, Expr.val, Val.lam,
            Val.inj₁, Val.unit, hc] at h
      · exact mentions_tailTuple E (j + 1) h

theorem mentions_lastTuple {Hw Hn : Expr} {k : Nat} : ∀ (E : List (Qual × VTy × VTy)) (j : Nat),
    mentions k (lastTuple E j Hw Hn) = true → mentions k Hw = true ∨ mentions k Hn = true
  | [], _, h => by simp [lastTuple, mentions, Expr.val, Val.unit] at h
  | (q, _, B) :: E, j, h => by
      simp only [lastTuple, mentions, Bool.or_eq_true] at h
      rcases h with h | h
      · by_contra hc
        simp only [not_or, Bool.not_eq_true] at hc
        unfold lastClause at h
        split at h <;>
          simp [thenE, mentions, mentions_pickE_eq, mentions_shift0_iff, Expr.val, Val.lam,
            Val.inj₁, Val.inj₂, Val.unit, Val.prim, hc.1, hc.2] at h
      · exact mentions_lastTuple E (j + 1) h

/-- **`N` mentions what its filling does**, above the filled variable: `(N.subst j V).shift 1 j`,
for a closed `V`. -/
theorem mentions_fill {V : Val} (hV : closedAt 0 V.1 = true) :
    ∀ (N : Expr) (j k : Nat), j < k →
      mentions k ((N.subst j V).shift 1 j) = mentions k N
  | .var i, j, k, hjk => by
      by_cases h2 : i = j
      · simp only [Expr.subst, if_pos h2]
        rw [shift_closedAt V.1 1 hV (Nat.zero_le j), mentions_of_closed hV]
        simp [mentions]; omega
      · by_cases h3 : i > j
        · have h4 : ¬ (i - 1 < j) := by omega
          simp only [Expr.subst, if_neg h2, if_pos h3, Expr.shift, if_neg h4, mentions]
          rw [show i - 1 + 1 = i by omega]
        · have h4 : i < j := by omega
          simp only [Expr.subst, if_neg h2, if_neg h3, Expr.shift, if_pos h4, mentions]
  | .unit, _, _, _ | .loc _, _, _, _ | .prim _, _, _, _ => rfl
  | .pair a b, j, k, hjk | .seq a b, j, k, hjk | .app a b, j, k, hjk => by
      simp only [Expr.subst, Expr.shift, mentions, mentions_fill hV a j k hjk,
        mentions_fill hV b j k hjk]
  | .inj₁ a, j, k, hjk | .inj₂ a, j, k, hjk => by
      simp only [Expr.subst, Expr.shift, mentions, mentions_fill hV a j k hjk]
  | .lam b, j, k, hjk => by
      simp only [Expr.subst, Expr.shift, mentions, val_shift_closed hV]
      exact mentions_fill hV b (j + 1) (k + 1) (by omega)
  | .letpair a b, j, k, hjk => by
      simp only [Expr.subst, Expr.shift, mentions, val_shift_closed hV,
        mentions_fill hV a j k hjk, mentions_fill hV b (j + 2) (k + 2) (by omega)]
  | .case s a b, j, k, hjk => by
      simp only [Expr.subst, Expr.shift, mentions, val_shift_closed hV,
        mentions_fill hV s j k hjk, mentions_fill hV a (j + 1) (k + 1) (by omega),
        mentions_fill hV b (j + 1) (k + 1) (by omega)]

/-! ### The theorem -/

/-- **A typed term mentions only live slots** of its context.  `[spec §55]` -/
theorem CDerivesP.mentions_live {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesP Δ Γ e j) : ∀ k, mentions k e = true → Ctx.LiveAt Γ k := by
  induction h with
  | var h =>
      intro k hk; simp only [mentions, beq_iff_eq] at hk; subst hk; exact h.live
  | @force _ _ i C h =>
      intro k hk
      have : mentions k (Expr.var i) = true := by
        cases C <;> simpa [forceE, mentions, Expr.val, Val.unit] using hk
      simp only [mentions, beq_iff_eq] at this; subst this; exact h.live
  | tensorI hs _ _ ih₁ ih₂ | unitE hs _ _ ih₁ ih₂ =>
      intro k hk; simp only [mentions, Bool.or_eq_true] at hk
      rcases hk with hk | hk
      · exact hs.liveAt_left (ih₁ k hk)
      · exact hs.liveAt_right (ih₂ k hk)
  | lolliE hs _ _ iha ihf =>
      intro k hk; simp only [mentions, Bool.or_eq_true] at hk
      rcases hk with hk | hk
      · exact hs.liveAt_right (ihf k hk)
      · exact hs.liveAt_left (iha k hk)
  | sumI₁ _ ih | sumI₂ _ ih => intro k hk; exact ih k (by simpa [mentions] using hk)
  | thunkV _ _ ih | ret _ ih | bangE _ ih | boxI _ _ ih | boxE _ ih | immSub _ _ ih
  | mutSub _ _ ih | ofRet _ ih | roll _ _ _ ih | unroll _ ih | nuIn _ _ ih | nuOut _ _ ih
  | effSub _ _ ih | bangThunkV _ _ _ ih => exact ih
  | thunkF _ ih | lamDead _ ih | allI _ _ _ _ ih | bangThunkF _ _ ih =>
      intro k hk
      exact Ctx.liveAt_cons_succ.mp (ih (k + 1) (by simpa [mentions, Expr.val, Val.lam] using hk))
  | lam _ ih =>
      intro k hk
      exact Ctx.liveAt_cons_succ.mp (ih (k + 1) (by simpa [mentions, Expr.val, Val.lam] using hk))
  | bind hs _ _ ihM ihN | effLet hs _ _ _ _ ihM ihN =>
      intro k hk
      simp only [mentions, Expr.val, Val.lam, Bool.or_eq_true] at hk
      rcases hk with hk | hk
      · exact hs.liveAt_right (Ctx.liveAt_cons_succ.mp (ihN _ hk))
      · exact hs.liveAt_left (ihM k hk)
  | app hs _ hx ihM =>
      intro k hk
      simp only [mentions, Bool.or_eq_true, beq_iff_eq] at hk
      rcases hk with hk | hk
      · exact hs.liveAt_left (ihM k hk)
      · subst hk; exact hs.liveAt_right hx.live
  | withI _ _ ihM ihN =>
      intro k hk
      simp only [withPair, mentions, Expr.val, Val.lam, Bool.or_eq_true, beq_iff_eq] at hk
      rcases hk with (hk | hk | hk) | hk | hk
      · omega
      · omega
      · exact Ctx.liveAt_cons_succ.mp (Ctx.liveAt_cons_succ.mp (ihM _ hk))
      · omega
      · exact Ctx.liveAt_cons_succ.mp (Ctx.liveAt_cons_succ.mp (ihN _ hk))
  | proj₁ _ ih | proj₂ _ ih | allE _ _ ih | allEV _ _ ih =>
      intro k hk
      simp only [mentions, Expr.val, Val.inj₁, Val.inj₂, Val.unit, Bool.or_false] at hk
      exact ih k hk
  | tensorE hs _ _ ihV ihM =>
      intro k hk
      simp only [mentions, Bool.or_eq_true] at hk
      rcases hk with hk | hk
      · exact hs.liveAt_left (ihV k hk)
      · exact hs.liveAt_right (Ctx.liveAt_cons_succ.mp (Ctx.liveAt_cons_succ.mp (ihM _ hk)))
  | sumE hs _ _ _ ihV ih₁ ih₂ =>
      intro k hk
      simp only [mentions, Bool.or_eq_true] at hk
      rcases hk with (hk | hk) | hk
      · exact hs.liveAt_left (ihV k hk)
      · exact hs.liveAt_right (Ctx.liveAt_cons_succ.mp (ih₁ _ hk))
      · exact hs.liveAt_right (Ctx.liveAt_cons_succ.mp (ih₂ _ hk))
  | zeroE hs _ ihV =>
      intro k hk
      simp only [absurdE, mentions, Bool.or_eq_true, beq_iff_eq] at hk
      rcases hk with (hk | hk) | hk
      · exact hs.liveAt_left (ihV k hk)
      · omega
      · omega
  | withbor1U _ _ _ _ _ _ _ hdc _ _ | withbor2U _ _ _ _ _ _ _ hdc _ _
  | withbor3U _ _ _ _ _ _ hdc _ _ | sliceBorrowMU _ _ _ _ _ _ _ hdc _ _
  | sliceBorrowIU _ _ _ _ _ _ _ _ hdc _ _ =>
      intro k hk; rw [mentions_of_closed (withborUE_closed hdc)] at hk; cases hk
  | foldImm => intro k hk; rw [mentions_of_closed (foldImmV_closed _)] at hk; cases hk
  | foldOwn => intro k hk; rw [mentions_of_closed (foldOwnV_closed _)] at hk; cases hk
  | foldOwnG => intro k hk; rw [mentions_of_closed (FoldP.foldOwnGV_closed _)] at hk; cases hk
  | foldReuse => intro k hk; rw [mentions_of_closed (foldReuseV_closed _)] at hk; cases hk
  | unfoldN => intro k hk; rw [mentions_of_closed (unfoldV_closed _)] at hk; cases hk
  | divFuel => intro k hk; rw [mentions_of_closed divFuelV_closed] at hk; cases hk
  | reify _ _ _ _ _ hcl => intro k hk; rw [mentions_of_closed (reifyV_closed hcl)] at hk; cases hk
  | effPerform _ _ _ ih | effRaise _ _ _ _ ih =>
      intro k hk
      simp [BoCa.BoLo.performE, BoCa.BoLo.raiseE, opArgE, mentions, Expr.val, Val.prim, Val.i32] at hk
      exact ih k hk
  | effThen hs _ _ _ _ _ _ _ _ _ _ _ ihM ihN ihD =>
      intro k hk
      simp only [thenE, mentions, Expr.val, Val.prim, Val.lam, Bool.false_or,
        Bool.or_eq_true] at hk
      rcases hk with (hk | hk) | hk
      · exact hs.liveAt_right (Ctx.liveAt_cons_succ.mp (ihN _ hk))
      · exact hs.liveAt_right (Ctx.liveAt_cons_succ.mp (ihD _ hk))
      · exact hs.liveAt_left (ihM k hk)
  | effHandleV hs _ _ _ _ _ _ _ _ ihc ihe | effHandleVB hs _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      intro k hk
      simp only [hndExpr, mentions, Expr.val, Val.prim, Val.i32, Bool.false_or,
        Bool.or_eq_true, mentions_of_closed (closedAt_qualsVal 0 _)] at hk
      rcases hk with hk | hk
      · exact hs.liveAt_left (ihc k hk)
      · exact hs.liveAt_right (ihe k hk)
  | effHandleT hs _ _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      intro k hk
      simp only [hndExpr, mentions, Expr.val, Val.prim, Val.i32, Bool.false_or,
        Bool.or_eq_true, mentions_of_closed (closedAt_qualsVal 0 _)] at hk
      rcases hk with (hk | hk) | hk
      · exact hs.liveAt_left (ihc k (by simp [mentions, hk]))
      · exact hs.liveAt_left (ihc k (by simp [mentions, mentions_tailTuple _ _ hk]))
      · exact hs.liveAt_right (ihe k hk)
  | effHandleL hs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      intro k hk
      simp only [hndExpr, mentions, Expr.val, Val.prim, Val.i32, Bool.false_or,
        Bool.or_eq_true, mentions_of_closed (closedAt_qualsVal 0 _)] at hk
      rcases hk with (hk | hk) | hk
      · exact hs.liveAt_left (ihc k (by simp [mentions, hk]))
      · rcases mentions_lastTuple _ _ hk with h | h
        · exact hs.liveAt_left (ihc k (by simp [mentions, h]))
        · exact hs.liveAt_left (ihc k (by simp [mentions, h]))
      · exact hs.liveAt_right (ihe k hk)
  | @letPoly _ Γ' N _ _ b hcl _ _ _ ihN =>
      intro k hk
      simp only [mentions, Expr.val, Val.lam, Bool.or_eq_true] at hk
      rcases hk with hk | hk
      · have := ihN (k + 1) (by rw [mentions_fill hcl N 0 (k + 1) (Nat.succ_pos k)]; exact hk)
        exact Ctx.liveAt_cons_succ.mp this
      · have hb := mentions_of_closed hcl k
        simp only [mentions, Val.lam] at hb
        rw [hb] at hk; cases hk
  | lendR _ _ _ _ _ _ _ _ _ _ hcb hdc =>
      intro k hk
      simp only [mentions, Expr.val, Bool.or_eq_true, beq_iff_eq] at hk
      rcases hk with (hk | hk) | hk
      · have hw : closedAt 0 (withborUV _).1 = true := withborUE_closed hdc
        rw [mentions_of_closed hw] at hk; cases hk
      · subst hk; exact ⟨_, rfl, rfl⟩
      · rw [mentions_of_closed hcb] at hk; cases hk
  | @lendLoopR _ _ A _ B R N K s0 _ _ _ _ _ _ _ _ _ hN1 hK1 hs0c _ _ _ _ _ _ =>
      intro k hk
      have hcN : closedAt 0 (lendCb N).1 = true := by
        simpa [lendCb, closedAt] using closedAt_mono N hN1 (by omega : 1 ≤ 2)
      have hcK : closedAt 0 (lendCb K).1 = true := by
        simpa [lendCb, closedAt] using closedAt_mono K hK1 (by omega : 1 ≤ 2)
      have hL : closedAt 0 (lendLoopE (lendLoopBody A B R)) = true := by
        have h1 := closedAt_of_zero (unfoldV_closed (lendLoopBody A B R)) 3
        have h2 : closedAt 3 lendStepE = true := by decide
        simp [lendLoopE, closedAt, h1, h2]
      cases k with
      | zero => exact ⟨_, rfl, rfl⟩
      | succ k =>
        have h1 := mentions_of_closed hL (k + 1)
        have h2 := mentions_of_closed hcN (k + 1)
        have h3 := mentions_of_closed hcK (k + 1)
        have h4 := mentions_of_closed hs0c (k + 1 + 1)
        simp only [lendLoopApp, bindE, mentions, Expr.val, Val.lam] at hk h2 h3
        simp [h1, h2, h3, h4] at hk
  | nilDead _ _ ih => intro k hk; exact absurd (ih k hk) (Ctx.liveAt_nil k)
  | _ =>
      intro k hk
      rw [mentions_of_closed rfl] at hk; cases hk

end BoCa.Fig16.LogRel.Core
