import Frames.Rules

/-!
# Frames — each rule's elaboration is a `CDerives` derivation

One lemma per frame rule: from the derivations of its premises' elaborations (the induction
hypotheses of `FDerives.elab`), the rule's elaborated term is a `CDerives` derivation at its
frame type. Each lemma names one rule and Core's own rules; none mentions another frame rule.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Frames
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- O1: a derivation stays one under a new dead binder at the front, its term shifted. -/
theorem shift_dead {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (T : VTy)
    (h : CDerives Δ Γ e j) : CDerives Δ (⟨T, false⟩ :: Γ) (e.shift 1 0) j :=
  Core.CDerives.insert_dead (Γd := [⟨T, false⟩]) (.cons .nil) h [] Γ rfl

/-- O1 at `k` dead binders. -/
theorem shift_deadN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (Γd : Ctx VTy)
    (hd : Ctx.Dead Γd) (h : CDerives Δ Γ e j) :
    CDerives Δ (Γd ++ Γ) (e.shift Γd.length 0) j := by
  simpa using Core.CDerives.insert_dead hd h [] Γ rfl

theorem elab_core {Δ : LifeCtx} {Γ : Ctx VTy} {Ps : List VTy} {N : Expr} {S : Row} {E : ExitRow}
    {A : VTy} (hS : FRow S) (hP : SlotsOk Ps)
    (hN : CDerives Δ Γ N (.comp (CTy.effOf S A))) :
    CDerives Δ Γ (coreE Ps N) (.comp (frTy S Ps E A)) := by
  refine .lam (CDerives.effThenA (.right (splitP_left_all Γ)) hS.1 hS.2.1
    (fun h => absurd h hS.2.2) (shift_dead _ hN) ?_ ?_)
  · refine .effSub (RowLe.nil S) (.ret (.tensorI (.right (.left (deadSplit (kill_dead Γ))))
      (.var (.there (.here (kill_dead Γ).toP))) (.sumI₁ (.var (.here (.cons (kill_dead Γ).toP))))))
  · exact .ret (.lolliE (.dead (.left (deadSplit (kill_dead Γ))))
      (.var (.there (.here (kill_dead Γ).toP))) (dtor_wf (SlotsOk.hasDtor hP) (.cons (.cons (kill_dead Γ)))))

/-- The injection at position `k` of the exit row is typed at `⊕E`. -/
theorem injAt_derives {Δ : LifeCtx} {Γ : Ctx VTy} {v : Expr} :
    ∀ {E : ExitRow} {k l : Nat} {B : VTy}, E[k]? = some (l, B) →
    CDerives Δ Γ v (.val B) → CDerives Δ Γ (injAt k v) (.val E.sumTy)
  | [], _, _, _, h, _ => by simp at h
  | (l', B') :: E, 0, l, B, h, hv => by
      simp at h; obtain ⟨-, rfl⟩ := h; exact .sumI₁ hv
  | _ :: E, k + 1, l, B, h, hv => by
      simp at h; exact .sumI₂ (injAt_derives h hv)

theorem elab_exit {Δ : LifeCtx} {Γ : Ctx VTy} {Ps : List VTy} {V : Expr} {S : Row} {E : ExitRow}
    {A : VTy} {k l : Nat} {B : VTy} (hk : E[k]? = some (l, B))
    (hV : CDerives Δ Γ V (.val B)) :
    CDerives Δ Γ (exitE k V) (.comp (frTy S Ps E A)) :=
  .lam (.effSub (RowLe.nil S) (.ret (.tensorI (.left (splitP_right_all Γ))
    (.var (.here (kill_dead Γ).toP)) (.sumI₂ (injAt_derives hk (shift_dead _ hV))))))

theorem elab_sub {Δ : LifeCtx} {Γ : Ctx VTy} {Ps : List VTy} {e : Expr} {S S' : Row}
    {E : ExitRow} {A : VTy} (hle : RowLe S S')
    (h : CDerives Δ Γ e (.comp (frTy S Ps E A))) :
    CDerives Δ Γ (subE e) (.comp (frTy S' Ps E A)) :=
  .lam (.effSub hle (.app (.right (splitP_left_all Γ)) (shift_dead _ h) (.here (kill_dead Γ).toP)))

theorem elab_case {Δ : LifeCtx} {Γ Γs Γb : Ctx VTy} {Ps : List VTy} {V e₁ e₂ : Expr} {S : Row}
    {E : ExitRow} {A B C : VTy} (hs : Ctx.SplitP Γ Γs Γb)
    (hV : CDerives Δ Γs V (.val (.sum A B)))
    (h₁ : CDerives Δ (⟨A, true⟩ :: Γb) e₁ (.comp (frTy S Ps E C)))
    (h₂ : CDerives Δ (⟨B, true⟩ :: Γb) e₂ (.comp (frTy S Ps E C))) :
    CDerives Δ Γ (caseE V e₁ e₂) (.comp (frTy S Ps E C)) := by
  refine .lam (.sumE (.right hs) (shift_dead _ hV) ?_ ?_)
  · refine .app (.left (.right (splitP_left_all Γb))) ?_ (.there (.here (kill_dead Γb).toP))
    refine .app (.right (.dead (splitP_left_all Γb)))
      (shift_deadN [⟨A, false⟩, ⟨slotsTy Ps, false⟩] (.cons (.cons .nil)) (.lam h₁))
      (.here (.cons (kill_dead Γb).toP))
  · refine .app (.left (.right (splitP_left_all Γb))) ?_ (.there (.here (kill_dead Γb).toP))
    refine .app (.right (.dead (splitP_left_all Γb)))
      (shift_deadN [⟨B, false⟩, ⟨slotsTy Ps, false⟩] (.cons (.cons .nil)) (.lam h₂))
      (.here (.cons (kill_dead Γb).toP))

/-! ### Drop glue -/

theorem kill_append : ∀ (a b : Ctx VTy), kill (a ++ b) = kill a ++ kill b
  | [], _ => rfl
  | _ :: a, b => by simp [kill]

theorem kill_kill (Γ : Ctx VTy) : kill (kill Γ) = kill Γ := by simp [kill]

theorem splitP_app {a a₁ a₂ b b₁ b₂ : Ctx VTy} (ha : Ctx.SplitP a a₁ a₂)
    (hb : Ctx.SplitP b b₁ b₂) : Ctx.SplitP (a ++ b) (a₁ ++ b₁) (a₂ ++ b₂) := by
  induction ha with
  | nil => exact hb
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | dead _ ih => exact .dead ih
  | dup hT _ ih => exact .dup hT ih

theorem soloP_killPre {T : VTy} {b : Ctx VTy} (hb : Ctx.DeadP b) :
    ∀ a : Ctx VTy, Ctx.SoloP (kill a ++ ⟨T, true⟩ :: b) a.length T
  | [] => .here hb
  | _ :: a => .there (soloP_killPre hb a)

theorem dropCtx_derives {Δ : LifeCtx} {k : Expr} {C : CTy} :
    ∀ (Γ Γpre : Ctx VTy), CtxDtor Γ → CDerives Δ (Γpre ++ kill Γ) k (.comp C) →
      CDerives Δ (Γpre ++ Γ) (dropCtxE Γ Γpre.length k) (.comp C)
  | [], Γpre, _, h => by simpa [dropCtxE, kill] using h
  | ⟨T, true⟩ :: Γ, Γpre, hD, h => by
      have hT : HasDtor T := hD ⟨T, true⟩ (by simp) rfl
      have ih := dropCtx_derives Γ (Γpre ++ [⟨T, false⟩]) (fun s hs => hD s (by simp [hs]))
        (by simpa [kill] using h)
      simp only [List.append_assoc, List.singleton_append, List.length_append,
        List.length_singleton] at ih
      refine drop_derives (splitP_app (splitP_right_all Γpre) (.left (splitP_right_all Γ)))
        (soloP_killPre (kill_dead Γ).toP Γpre) hT ih
  | ⟨T, false⟩ :: Γ, Γpre, hD, h => by
      have ih := dropCtx_derives Γ (Γpre ++ [⟨T, false⟩]) (fun s hs => hD s (by simp [hs]))
        (by simpa [kill] using h)
      simpa [dropCtxE] using ih

/-- The exit arm: at an empty row, `(π', inr (absurd e))`; else the drop glue. -/
theorem exitArm_derives {Δ : LifeCtx} {Γ : Ctx VTy} {E : ExitRow} {i : Nat} {d : Expr} {C : CTy}
    {T : Slot VTy}
    (h₀ : E = [] → CDerives Δ (T :: Γ) (.pair (.var i) (.inj₂ (absurdE (.var 0)))) (.comp C))
    (hd : E ≠ [] → CDerives Δ (T :: Γ) d (.comp C)) :
    CDerives Δ (T :: Γ) (exitArmE E i d) (.comp C) := by
  cases E with
  | nil => exact h₀ rfl
  | cons _ _ => exact hd (by simp)

theorem drops_consDead {Γ : Ctx VTy} {T : VTy} (h : Γ.Drops) : Ctx.Drops (⟨T, false⟩ :: Γ) := by
  intro s hs hl
  cases hs with
  | head => cases hl
  | tail _ hs => exact h s hs hl

theorem persistent_consDead {Γ : Ctx VTy} {T : VTy} (h : Persistent Γ) :
    Persistent (⟨T, false⟩ :: Γ) := by
  intro s hs hl
  cases hs with
  | head => cases hl
  | tail _ hs => exact h s hs hl

theorem elab_bind {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Ps : List VTy} {eM eN : Expr} {S : Row}
    {E : ExitRow} {A B : VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂) (hX : E = [] ∨ CtxDtor Γ₂)
    (hM : CDerives Δ Γ₁ eM (.comp (frTy S Ps E A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) eN (.comp (frTy S Ps E B))) :
    CDerives Δ Γ (bindE E Γ₂ eM eN) (.comp (frTy S Ps E B)) := by
  have kd := kill_dead Γ₂
  refine .lam (.effLet (.left hs) (fun h => drops_consDead (hW h))
    (fun h => persistent_consDead (hU h))
    (.app (.right (splitP_left_all Γ₁)) (shift_dead _ hM) (.here (kill_dead Γ₁).toP)) ?_)
  refine .tensorE (.left (.dead (splitP_right_all Γ₂))) (.var (.here (.cons kd.toP))) ?_
  refine .sumE (.left (.right (.dead (.dead (splitP_right_all Γ₂)))))
    (.var (.here (.cons (.cons (.cons kd.toP))))) ?_ ?_
  · refine .app (.left (.dead (.right (.dead (.dead (splitP_left_all Γ₂)))))) ?_
      (.there (.there (.here (.cons (.cons kd.toP)))))
    exact .app (.right (.dead (.dead (.dead (.dead (splitP_left_all Γ₂))))))
      (shift_deadN [⟨A, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩]
        (.cons (.cons (.cons (.cons (.cons .nil))))) (.lam hN))
      (.here (.cons (.cons (.cons (.cons kd.toP)))))
  · refine exitArm_derives (fun hE => ?_) (fun hE => ?_)
    · subst hE
      exact .effSub (RowLe.nil S) (.ret (.tensorI
        (.right (.dead (.left (.dead (.dead (splitP_right_all Γ₂))))))
        (.var (.there (.there (.here (.cons (.cons kd.toP))))))
        (.sumI₂ (.ofRet (.zeroE (.left (.dead (.dead (.dead (.dead (splitP_right_all Γ₂))))))
          (.var (.here (.cons (.cons (.cons (.cons kd.toP)))))))))))
    have hD : CtxDtor Γ₂ := hX.resolve_left hE
    refine dropCtx_derives Γ₂ [⟨_, true⟩, ⟨_, false⟩, ⟨_, true⟩, ⟨_, false⟩, ⟨_, false⟩] hD ?_
    exact .effSub (RowLe.nil S) (.ret (.tensorI
      (.right (.dead (.left (.dead (.dead (deadSplit kd))))))
      (.var (.there (.there (.here (.cons (.cons kd.toP))))))
      (.sumI₂ (.var (.here (.cons (.cons (.cons (.cons kd.toP)))))))))

theorem elab_catch {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Ps : List VTy} {eM eH : Expr} {S : Row}
    {E : ExitRow} {A : VTy} {l : Nat} {B : VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂) (hX : CtxDtor Γ₂)
    (hM : CDerives Δ Γ₁ eM (.comp (frTy S Ps ((l, B) :: E) A)))
    (hH : CDerives Δ (⟨B, true⟩ :: Γ₂) eH (.comp (frTy S Ps E A))) :
    CDerives Δ Γ (catchE Γ₂ eM eH) (.comp (frTy S Ps E A)) := by
  have kd := kill_dead Γ₂
  refine .lam (.effLet (.left hs) (fun h => drops_consDead (hW h))
    (fun h => persistent_consDead (hU h))
    (.app (.right (splitP_left_all Γ₁)) (shift_dead _ hM) (.here (kill_dead Γ₁).toP)) ?_)
  refine .tensorE (.left (.dead (splitP_right_all Γ₂))) (.var (.here (.cons kd.toP))) ?_
  refine .sumE (.left (.right (.dead (.dead (splitP_right_all Γ₂)))))
    (.var (.here (.cons (.cons (.cons kd.toP))))) ?_ ?_
  · refine dropCtx_derives Γ₂ [⟨_, true⟩, ⟨_, false⟩, ⟨_, true⟩, ⟨_, false⟩, ⟨_, false⟩] hX ?_
    exact .effSub (RowLe.nil S) (.ret (.tensorI
      (.right (.dead (.left (.dead (.dead (deadSplit kd))))))
      (.var (.there (.there (.here (.cons (.cons kd.toP))))))
      (.sumI₁ (.var (.here (.cons (.cons (.cons (.cons kd.toP)))))))))
  · refine .sumE (.left (.dead (.right (.dead (.dead (splitP_right_all Γ₂))))))
      (.var (.here (.cons (.cons (.cons (.cons kd.toP)))))) ?_ ?_
    · refine .app (.left (.dead (.dead (.right (.dead (.dead (splitP_left_all Γ₂))))))) ?_
        (.there (.there (.there (.here (.cons (.cons kd.toP))))))
      exact .app (.right (.dead (.dead (.dead (.dead (.dead (splitP_left_all Γ₂)))))))
        (shift_deadN [⟨B, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩]
          (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))) (.lam hH))
        (.here (.cons (.cons (.cons (.cons (.cons kd.toP))))))
    · refine dropCtx_derives Γ₂
        [⟨_, true⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, true⟩, ⟨_, false⟩, ⟨_, false⟩] hX ?_
      exact .effSub (RowLe.nil S) (.ret (.tensorI
        (.right (.dead (.dead (.left (.dead (.dead (deadSplit kd)))))))
        (.var (.there (.there (.there (.here (.cons (.cons kd.toP)))))))
        (.sumI₂ (.var (.here (.cons (.cons (.cons (.cons (.cons kd.toP))))))))))

theorem elab_under {Δ : LifeCtx} {Γ : Ctx VTy} {Ps : List VTy} {eM : Expr} {S : Row}
    {E : ExitRow} {A : VTy} {Q : VTy} (hS : FRow S) (hQ : SlotOk Q)
    (hM : CDerives Δ Γ eM (.comp (frTy S Ps E A))) :
    CDerives Δ Γ (underE Q eM) (.comp (frTy S (Q :: Ps) E A)) := by
  have kd := kill_dead Γ
  refine .lam (.tensorE (.left (splitP_right_all Γ)) (.var (.here kd.toP)) ?_)
  refine CDerives.effThenA (A := .tensor (slotsTy Ps) (exitsTy A E))
    (.left (.right (.dead (splitP_left_all Γ)))) hS.1 hS.2.1
    (fun h => absurd h hS.2.2) ?_ ?_ ?_
  · exact .app (.right (.dead (.dead (splitP_left_all Γ))))
      (shift_deadN [⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩] (.cons (.cons (.cons .nil))) hM)
      (.here (.cons (.cons kd.toP)))
  · refine .tensorE (.left (.dead (.right (.dead (deadSplit kd)))))
      (.var (.here (.cons (.cons (.cons kd.toP))))) ?_
    exact .effSub (RowLe.nil S) (.ret (.tensorI
      (.right (.left (.dead (.dead (.left (.dead (deadSplit kd)))))))
      (.tensorI (.dead (.right (.dead (.dead (.left (.dead (deadSplit kd)))))))
        (.var (.there (.there (.there (.there (.here (.cons kd.toP)))))))
        (.var (.there (.here (.cons (.cons (.cons (.cons kd.toP))))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons kd.toP)))))))))
  · exact .ret (.lolliE (.dead (.dead (.left (.dead (deadSplit kd)))))
      (.var (.there (.there (.here (.cons kd.toP)))))
      (dtor_wf hQ.hasDtor (.cons (.cons (.cons (.cons kd))))))

/-! ### The destructors are closed -/

theorem dtorAt_closed : ∀ (b : Bool) (T : VTy), closedAt 0 (dtorAt b T) = true
  | b, .tensor A B => by
      have h₁ := dtorAt_closed b A; have h₂ := dtorAt_closed b B
      simp [dtorAt, closedAt, closedAt_mono _ h₁ (Nat.zero_le _), closedAt_mono _ h₂ (Nat.zero_le _)]
  | b, .sum A B => by
      have h₁ := dtorAt_closed b A; have h₂ := dtorAt_closed b B
      simp [dtorAt, closedAt, closedAt_mono _ h₁ (Nat.zero_le _), closedAt_mono _ h₂ (Nat.zero_le _)]
  | b, .ref A => by
      have h₁ := dtorAt_closed false A
      unfold dtorAt
      split
      · simp [forget, closedAt, unit', Expr.val, Val.lam, Val.unit]
      · simp [Core.bindE, closedAt, closedAt_mono _ h₁ (Nat.zero_le _), Expr.val, Val.prim, Val.lam]
  | b, .box _ A => by
      have h₁ := dtorAt_closed false A
      simp [dtorAt, closedAt, closedAt_mono _ h₁ (Nat.zero_le _)]
  | b, .mu A => by
      have h₁ := dtorAt_closed true A
      simp [dtorAt, closedAt, closedAt_mono _ h₁ (Nat.zero_le _),
        closedAt_mono _ (foldOwnV_closed (toFShape A)) (Nat.zero_le _)]
  | b, .thunk C => by
      rw [dtorAt_thunk]
      match C with
      | .nu (.amp _ (.ret R)) =>
          have h₁ := dtorAt_closed false R
          simp [dtorAt, closedAt, Core.bindE, Expr.val, Val.lam, Val.unit, Val.inj₂,
            closedAt_mono _ h₁ (Nat.zero_le _)]
      | .nu (.amp _ (.arr _ _)) | .nu (.amp _ (.amp _ _)) | .nu (.amp _ .top)
      | .nu (.amp _ (.all _ _ _)) | .nu (.amp _ (.nu _)) | .nu (.amp _ (.eff _ _ _ _ _ _ _))
      | .nu (.eff _ _ _ _ _ _ _) | .eff _ _ _ _ _ _ _ | .nu (.ret _) | .nu (.arr _ _) | .nu .top
      | .nu (.all _ _ _) | .nu (.nu _) | .ret _ | .arr _ _ | .amp _ _ | .top | .all _ _ _ =>
          simp [dtorAt, closedAt, Expr.val, Val.lam, Val.unit, Val.inj₂]
  | b, .fam L => by
      cases L <;> simp [dtorAt, forget, closedAt, unit', Expr.val, Val.lam, Val.unit, Val.prim,
        Val.i32, elet, closedAt_mono _ (dtorAt_closed false _) (Nat.zero_le _)]
  | b, .unit | b, .zero | b, .int _ | b, .imm _ _ | b, .mut _ _ | b, .bang _ | b, .unk
  | b, .opq _ | b, .tvar _ => by
      simp [dtorAt, forget, closedAt, unit', Expr.val, Val.lam, Val.unit]

/-! ### Lending a slot -/

/-- The unwinding borrow constant at a slot's source: `U(src ⊸ cb ⊸ F_Σ(src ⊗ B))`. -/
theorem withborU_src {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {x : LifeVar} {B : VTy}
    (src : LendSrc) (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none) (hS : S.Unwind x)
    (hsrc : LendOk Δ x src) (hsrcD : SlotOk src.ty) (hB : ¬ VFree x B) :
    CDerives Δ Γ (withborUE src.fin)
      (.val (withborUTy src.ty (cbUTy x Δ.meetOfDom (.mut (.var x) src.payload) B S) S
        (.tensor src.ty B))) := by
  cases src with
  | ref A =>
      exact .withbor2U x hΓ.toP hx hsrc.2 hsrc.1 hB hS (dtorAt_closed false _)
        (dtor_wf hsrcD.hasDtor hΓ)
  | «mut» a A =>
      exact .withbor3U x hΓ.toP hx hsrc hB hS (dtorAt_closed false _) (dtor_wf hsrcD.hasDtor hΓ)

theorem elab_use {Δ : LifeCtx} {Γ : Ctx VTy} {Ps : List VTy} {N : Expr} {S : Row} {E : ExitRow}
    {B : VTy} (src : LendSrc) (x : LifeVar) (hx : Δ.find? x = none)
    (hS : S.Unwind x) (hS' : FRow S) (hP : SlotsOk Ps) (hsrc : LendOk Δ x src)
    (hsrcD : SlotOk src.ty) (hB : ¬ VFree x B)
    (hN : CDerives Δ Γ N (.val (cbUTy x Δ.meetOfDom (.mut (.var x) src.payload) B S))) :
    CDerives Δ Γ (useE src Ps N) (.comp (frTy S (src.ty :: Ps) E B)) := by
  have kd := kill_dead Γ
  refine .lam (.tensorE (.left (splitP_right_all Γ)) (.var (.here kd.toP)) ?_)
  refine .bind (.right (.right (.dead (splitP_left_all Γ))))
    (.ret (shift_deadN [⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩] (.cons (.cons (.cons .nil))) hN)) ?_
  refine .bind (splitP_right_all _)
    (.ret (withborU_src (B := B) src (kill_dead _) hx hS hsrc hsrcD hB)) ?_
  refine CDerives.effThenA (A := .tensor src.ty B)
    (.left (.left (.right (.left (.dead (deadSplit kd)))))) hS'.1 hS'.2.1
    (fun h => absurd h hS'.2.2) ?_ ?_ ?_
  · refine .app (.left (.right (.dead (.left (.dead (deadSplit kd))))))
      ?_ (.there (.here (.cons (.cons (.cons kd.toP)))))
    exact .app (.left (.dead (.dead (.right (.dead (deadSplit kd))))))
      (.force (C := .arr src.ty (.arr _ _)) (.here (.cons (.cons (.cons (.cons kd.toP))))))
      (.there (.there (.there (.here (.cons kd.toP)))))
  · refine .tensorE (.left (.dead (.dead (.right (.dead (.dead (deadSplit kd)))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons kd.toP))))))) ?_
    exact .effSub (RowLe.nil S) (.ret (.tensorI
      (.right (.left (.dead (.dead (.dead (.left (.dead (.dead (deadSplit kd)))))))))
      (.tensorI (.dead (.left (.dead (.dead (.dead (.right (.dead (.dead (deadSplit kd)))))))))
        (.var (by csoloP)) (.var (by csoloP)))
      (.sumI₁ (.var (by csoloP)))))
  · exact .ret (.lolliE (.dead (.dead (.dead (.left (.dead (.dead (deadSplit kd)))))))
      (.var (.there (.there (.there (.here (.cons (.cons kd.toP)))))))
      (dtor_wf (SlotsOk.hasDtor hP) (.cons (.cons (.cons (.cons (.cons (.cons kd))))))))

theorem drops_dead {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Γ.Drops :=
  fun s hs hl => by rw [dead_not_live h s hs] at hl; cases hl

theorem persistent_dead {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Persistent Γ :=
  fun s hs hl => by rw [dead_not_live h s hs] at hl; cases hl

theorem elab_new {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Ps : List VTy} {V eM : Expr} {S : Row}
    {E : ExitRow} {A B : VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hA : HasDtor A)
    (hV : CDerives Δ Γ₁ V (.val A))
    (hM : CDerives Δ Γ₂ eM (.comp (frTy S (.ref A :: Ps) E B))) :
    CDerives Δ Γ (newE A V eM) (.comp (frTy S Ps E (.tensor B A))) := by
  have kd := kill_dead Γ₂
  refine .lam (.bind (A := .ref A) (.right hs)
    (.ret (.lolliE (.dead (splitP_left_all Γ₁)) (shift_dead _ hV) (.alloc (A := A) (.cons (kill_dead Γ₁).toP)))) ?_)
  refine .bind (A := .tensor (.ref A) (slotsTy Ps)) (.left (.left (splitP_right_all Γ₂)))
    (.ret (.tensorI (.left (.right (deadSplit kd))) (.var (by csoloP)) (.var (by csoloP)))) ?_
  refine .effLet (splitP_left_all _) (fun _ => drops_dead (kill_dead _))
    (fun _ => persistent_dead (kill_dead _))
    (.app (.right (.dead (.dead (splitP_left_all Γ₂))))
      (shift_deadN [⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩] (.cons (.cons (.cons .nil))) hM)
      (.here (.cons (.cons kd.toP)))) ?_
  have kd₂ := kill_dead (⟨slotsTy (.ref A :: Ps), true⟩ :: ⟨.ref A, false⟩ :: ⟨slotsTy Ps, false⟩ :: Γ₂)
  refine .tensorE (.left (deadSplit kd₂)) (.var (by csoloP)) ?_
  refine .tensorE (.right (.left (.dead (deadSplit kd₂)))) (.var (by csoloP)) ?_
  refine .sumE (.right (.right (.left (.dead (.dead (deadSplit kd₂)))))) (.var (by csoloP)) ?_ ?_
  · refine .bind (.right (.right (.left (deadSplit (.cons (.cons (.cons kd₂)))))))
      (.ret (.lolliE (splitP_left_all _) (.var (by csoloP)) (.free (A := A) (kill_dead _).toP))) ?_
    exact .effSub (RowLe.nil S) (.ret (.tensorI
      (.right (.right (.left (deadSplit (.cons (.cons (.cons (.cons kd₂)))))))) (.var (by csoloP))
      (.sumI₁ (.tensorI (.right (.left (.dead (deadSplit (.cons (.cons (.cons (.cons kd₂))))))))
        (.var (by csoloP)) (.var (by csoloP))))))
  · refine drop_derives (.right (.right (.left (deadSplit (.cons (.cons (.cons kd₂)))))))
      (by csoloP) (.ref hA) ?_
    exact .effSub (RowLe.nil S) (.ret (.tensorI
      (.right (.left (.dead (deadSplit (.cons (.cons (.cons kd₂))))))) (.var (by csoloP))
      (.sumI₂ (.var (by csoloP)))))

theorem elab_callBlock {Δ : LifeCtx} {Γ : Ctx VTy} {j : Nat} {b : FBlock} (hb : b.Wf Δ)
    (hj : Ctx.SoloP Γ j b.B) :
    CDerives Δ Γ (callE b.v j) (.comp (frTy b.S b.Ps b.E b.A)) := by
  have kd := kill_dead Γ
  have hv : CDerives Δ (kill (⟨slotsTy b.Ps, true⟩ :: Γ)) (.val b.v)
      (.val (blockTy b.B b.S b.Ps b.E b.A)) := by
    have h := shift_deadN _ (kill_dead (⟨slotsTy b.Ps, true⟩ :: Γ)) hb.2
    rwa [List.append_nil, shift_closed0 hb.1] at h
  refine .lam (.bind (A := .thunk (.arr b.B (frTy b.S b.Ps b.E b.A))) (splitP_right_all _)
    (.ret (.bangE hv)) ?_)
  refine .app (.left (.right (splitP_left_all Γ))) ?_ (.there (.here kd.toP))
  exact .app (.left (.dead (splitP_right_all Γ)))
    (.force (C := .arr b.B (frTy b.S b.Ps b.E b.A)) (.here (.cons kd.toP))) (.there (.there hj))

theorem splitP_symm {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) : Ctx.SplitP Γ Γ₂ Γ₁ := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih
  | dead _ ih => exact .dead ih
  | dup hT _ ih => exact .dup hT ih

/-- The counted loop's step `λ(i, (π, s)). M[i, s] π to (π', r). …` over the persistent context of
the turn. -/
theorem countStep_derives {Δ : LifeCtx} {Γ₂ : Ctx VTy} {Ps : List VTy} {eM : Expr}
    {E : ExitRow} {l : Nat} {S₀ B : VTy} (hp : Persistent Γ₂)
    (hM : CDerives Δ (⟨S₀, true⟩ :: ⟨.int .w32, true⟩ :: Γ₂) eM
      (.comp (frTy [] Ps ((l, B) :: E) S₀))) :
    CDerives Δ Γ₂ (countStepE eM)
      (.val (.bang (.lolli (.tensor (.int .w32) (.tensor (slotsTy Ps) S₀))
        (.sum (.tensor (slotsTy Ps) S₀) (.tensor (slotsTy Ps) (exitsTy B E)))))) := by
  have kd := kill_dead Γ₂
  refine .bangThunkV hp rfl (.lam ?_)
  refine .tensorE (.left (splitP_right_all Γ₂)) (.var (.here kd.toP)) ?_
  refine .tensorE (.left (.right (.dead (splitP_right_all Γ₂)))) (.var (.here (.cons (.cons kd.toP)))) ?_
  refine .bind (A := .tensor (slotsTy Ps) (exitsTy S₀ ((l, B) :: E))) (splitP_left_all _) ?_ ?_
  · refine .app (A := slotsTy Ps) (.left (.right (.dead (.left (.dead (splitP_left_all Γ₂)))))) ?_ ?_
    · refine .app (A := S₀) (.right (.dead (.dead (.left (.dead (splitP_left_all Γ₂)))))) ?_ ?_
      · refine .app (A := .int .w32) (.dead (.dead (.dead (.right (.dead (splitP_left_all Γ₂))))))
          (shift_deadN [⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩]
            (.cons (.cons (.cons (.cons (.cons .nil))))) (.lam (.lam hM))) ?_
        csoloP
      · csoloP
    · csoloP
  · have kd' := kill_dead (⟨S₀, true⟩ :: ⟨slotsTy Ps, true⟩ :: ⟨.tensor (slotsTy Ps) S₀, false⟩ ::
      ⟨.int .w32, true⟩ :: ⟨.tensor (.int .w32) (.tensor (slotsTy Ps) S₀), false⟩ :: Γ₂)
    refine .tensorE (.left (deadSplit kd')) (.var (.here kd'.toP)) ?_
    refine .sumE (.left (.right (.dead (deadSplit kd')))) (.var (by csoloP)) ?_ ?_
    · exact .ret (.sumI₁ (.tensorI (.right (.dead (.left (.dead (deadSplit kd')))))
        (.var (by csoloP)) (.var (by csoloP))))
    · exact .ret (.sumI₂ (.tensorI (.right (.dead (.left (.dead (deadSplit kd')))))
        (.var (by csoloP)) (.var (by csoloP))))

theorem elab_loopCount {Δ : LifeCtx} {Γ Γ₁ Γn Γs Γ₂ : Ctx VTy} {Ps : List VTy} {n s₀ eM : Expr}
    {E : ExitRow} {l : Nat} {S₀ B : VTy}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γn Γs) (hp : Persistent Γ₂)
    (hn : CDerives Δ Γn n (.val (.int .w32))) (hs0 : CDerives Δ Γs s₀ (.val S₀))
    (hM : CDerives Δ (⟨S₀, true⟩ :: ⟨.int .w32, true⟩ :: Γ₂) eM
      (.comp (frTy [] Ps ((l, B) :: E) S₀))) :
    CDerives Δ Γ (loopCountE n s₀ eM) (.comp (frTy [] Ps E (.sum S₀ B))) := by
  refine .lam (.bind (A := .sum (.tensor (slotsTy Ps) S₀) (.tensor (slotsTy Ps) (exitsTy B E)))
    (splitP_left_all _) ?_ ?_)
  · refine .ret (.lolliE (splitP_left_all _) ?_ (.bangE (.countTry _ _ (kill_dead _).toP)))
    refine .tensorI (.right (splitP_symm hs)) (shift_dead _ (countStep_derives hp hM)) ?_
    refine .tensorI (.right hs₁) (shift_dead _ hn) ?_
    refine .tensorI (splitP_right_all _) (.lit (.i32 0) (kill_dead _).toP) ?_
    exact .tensorI (.left (splitP_right_all Γs)) (.var (.here (kill_dead Γs).toP)) (shift_dead _ hs0)
  · have kd := kill_dead (⟨slotsTy Ps, true⟩ :: Γ)
    refine .sumE (.left (deadSplit kd)) (.var (.here kd.toP)) ?_ ?_
    · refine .tensorE (.left (.dead (deadSplit kd))) (.var (by csoloP)) ?_
      exact .ret (.tensorI (.right (.left (.dead (.dead (deadSplit kd))))) (.var (by csoloP))
        (.sumI₁ (.sumI₁ (.var (by csoloP)))))
    · refine .tensorE (.left (.dead (deadSplit kd))) (.var (by csoloP)) ?_
      refine .sumE (.left (.right (.dead (.dead (deadSplit kd))))) (.var (by csoloP)) ?_ ?_
      · exact .ret (.tensorI (.right (.dead (.left (.dead (.dead (deadSplit kd)))))) (.var (by csoloP))
          (.sumI₁ (.sumI₂ (.var (by csoloP)))))
      · exact .ret (.tensorI (.right (.dead (.left (.dead (.dead (deadSplit kd)))))) (.var (by csoloP))
          (.sumI₂ (.var (by csoloP))))

theorem deadP_of_persistent : ∀ {Γ : Ctx VTy}, Persistent Γ → Ctx.DeadP Γ
  | [], _ => .nil
  | ⟨T, false⟩ :: Γ, h => .cons (deadP_of_persistent fun s hs hl => h s (by simp [hs]) hl)
  | ⟨T, true⟩ :: Γ, h => by
      obtain ⟨A, hA⟩ := h ⟨T, true⟩ (by simp) rfl
      simp only at hA
      subst hA
      exact .drop rfl (deadP_of_persistent fun s hs hl => h s (by simp [hs]) hl)

/-- The div loop's step `λst. let (π, s) = st; ⟨turn, close⟩` over the persistent context of the
turn. -/
theorem iterStep_derives {Δ : LifeCtx} {Γ₂ : Ctx VTy} {Ps : List VTy} {eM : Expr} {S : Row}
    {E : ExitRow} {l : Nat} {S₀ B : VTy} (hp : Persistent Γ₂) (hS₀ : HasDtor S₀)
    (hM : CDerives Δ (⟨S₀, true⟩ :: Γ₂) eM (.comp (frTy S Ps ((l, B) :: E) S₀))) :
    CDerives Δ Γ₂ (iterStepE S₀ eM)
      (.val (iterStepTy S (.tensor (slotsTy Ps) S₀) (.tensor (slotsTy Ps) (exitsTy B E))
        (.tensor (slotsTy Ps) .unit))) := by
  have kd := kill_dead Γ₂
  refine .bangThunkV hp rfl (.lam ?_)
  refine .tensorE (.left (splitP_right_all Γ₂)) (.var (.here kd.toP)) ?_
  refine .withI ?_ ?_
  · refine .effLet (A := .tensor (slotsTy Ps) (exitsTy S₀ ((l, B) :: E))) (splitP_left_all _)
      (fun _ => drops_dead (kill_dead _)) (fun _ => persistent_dead (kill_dead _)) ?_ ?_
    · refine .app (A := slotsTy Ps) (.dead (.dead (.left (.right (.dead (splitP_left_all Γ₂))))))
        ?_ (by csoloP)
      exact .app (A := S₀) (.dead (.dead (.right (.dead (.dead (splitP_left_all Γ₂))))))
        (shift_deadN [⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩]
          (.cons (.cons (.cons (.cons (.cons .nil))))) (.lam hM)) (by csoloP)
    · have kd' := kill_dead (withCtx (⟨S₀, true⟩ :: ⟨slotsTy Ps, true⟩ ::
        ⟨.tensor (slotsTy Ps) S₀, false⟩ :: Γ₂))
      refine .tensorE (.left (deadSplit kd')) (.var (.here kd'.toP)) ?_
      refine .sumE (.left (.right (.dead (deadSplit kd')))) (.var (by csoloP)) ?_ ?_
      · exact .effSub (RowLe.nil S) (.ret (.sumI₂ (.tensorI (.right (.dead (.left (.dead (deadSplit kd')))))
          (.var (by csoloP)) (.var (by csoloP)))))
      · exact .effSub (RowLe.nil S) (.ret (.sumI₁ (.tensorI (.right (.dead (.left (.dead (deadSplit kd')))))
          (.var (by csoloP)) (.var (by csoloP)))))
  · refine drop_derives (.dead (.dead (.left (.right (.dead (splitP_right_all Γ₂))))))
      (by csoloP) hS₀ ?_
    exact .effSub (RowLe.nil S) (.ret (.tensorI
      (.dead (.dead (.dead (.left (.dead (splitP_right_all Γ₂))))))
      (.var (by csoloP)) (.unitI (.cons (.cons (.cons (.cons (.cons (deadP_of_persistent hp)))))))))

theorem elab_loopIter {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Ps : List VTy} {s₀ eM : Expr} {S : Row}
    {E : ExitRow} {l : Nat} {S₀ B : VTy} (hdiv : Row.divB S = true) (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hp : Persistent Γ₂) (hS₀ : HasDtor S₀) (hs0 : CDerives Δ Γ₁ s₀ (.val S₀))
    (hM : CDerives Δ (⟨S₀, true⟩ :: Γ₂) eM (.comp (frTy S Ps ((l, B) :: E) S₀))) :
    CDerives Δ Γ (loopIterE S₀ s₀ eM) (.comp (frTy S Ps E (.sum B .unit))) := by
  refine .lam (.bind (.right (splitP_symm hs)) (.ret (shift_dead _ (iterStep_derives hp hS₀ hM))) ?_)
  refine .bind (splitP_right_all _)
    (.ret (.bangE (.iterate S (.tensor (slotsTy Ps) S₀) (.tensor (slotsTy Ps) (exitsTy B E))
      (.tensor (slotsTy Ps) .unit) hdiv (kill_dead _).toP))) ?_
  refine .bind (A := .tensor (iterStepTy S (.tensor (slotsTy Ps) S₀)
      (.tensor (slotsTy Ps) (exitsTy B E)) (.tensor (slotsTy Ps) .unit)) (.tensor (slotsTy Ps) S₀))
    (.right (.left (.left (splitP_left_all Γ₁))))
    (.ret (.tensorI (.dead (.left (.right (splitP_right_all Γ₁))))
      (.var (.there (.here (.cons (kill_dead Γ₁).toP))))
      (.tensorI (.dead (.dead (.left (splitP_right_all Γ₁))))
        (.var (.there (.there (.here (kill_dead Γ₁).toP))))
        (shift_deadN [⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩] (.cons (.cons (.cons .nil))) hs0)))) ?_
  refine .effLet (A := .sum (.tensor (slotsTy Ps) (exitsTy B E)) (.tensor (slotsTy Ps) .unit))
    (splitP_left_all _) (fun _ => drops_dead (kill_dead _))
    (fun _ => persistent_dead (kill_dead _))
    (.app (.right (.left (deadSplit (.cons (.cons (kill_dead Γ₁))))))
      (.force (C := .arr (.tensor (iterStepTy S (.tensor (slotsTy Ps) S₀)
        (.tensor (slotsTy Ps) (exitsTy B E)) (.tensor (slotsTy Ps) .unit)) (.tensor (slotsTy Ps) S₀))
        (CTy.effOf S (.sum (.tensor (slotsTy Ps) (exitsTy B E)) (.tensor (slotsTy Ps) .unit))))
        (.there (.here (.cons (.cons (kill_dead Γ₁).toP)))))
      (.here (.cons (.cons (.cons (kill_dead Γ₁).toP))))) ?_
  have kd := kill_dead (⟨.tensor (iterStepTy S (.tensor (slotsTy Ps) S₀)
      (.tensor (slotsTy Ps) (exitsTy B E)) (.tensor (slotsTy Ps) .unit)) (.tensor (slotsTy Ps) S₀), true⟩ ::
    ⟨.thunk (.arr (.tensor (iterStepTy S (.tensor (slotsTy Ps) S₀)
        (.tensor (slotsTy Ps) (exitsTy B E)) (.tensor (slotsTy Ps) .unit)) (.tensor (slotsTy Ps) S₀))
        (CTy.effOf S (.sum (.tensor (slotsTy Ps) (exitsTy B E)) (.tensor (slotsTy Ps) .unit)))), true⟩ ::
    ⟨iterStepTy S (.tensor (slotsTy Ps) S₀) (.tensor (slotsTy Ps) (exitsTy B E))
      (.tensor (slotsTy Ps) .unit), false⟩ :: ⟨slotsTy Ps, false⟩ :: kill Γ₁)
  refine .sumE (.left (deadSplit kd)) (.var (.here kd.toP)) ?_ ?_
  · refine .tensorE (.left (.dead (deadSplit kd))) (.var (by csoloP)) ?_
    refine .sumE (.left (.right (.dead (.dead (deadSplit kd))))) (.var (by csoloP)) ?_ ?_
    · exact .effSub (RowLe.nil S) (.ret (.tensorI (.right (.dead (.left (.dead (.dead (deadSplit kd))))))
        (.var (by csoloP)) (.sumI₁ (.sumI₁ (.var (by csoloP))))))
    · exact .effSub (RowLe.nil S) (.ret (.tensorI (.right (.dead (.left (.dead (.dead (deadSplit kd))))))
        (.var (by csoloP)) (.sumI₂ (.var (by csoloP)))))
  · refine .tensorE (.left (.dead (deadSplit kd))) (.var (by csoloP)) ?_
    exact .effSub (RowLe.nil S) (.ret (.tensorI (.right (.left (.dead (.dead (deadSplit kd)))))
      (.var (by csoloP)) (.sumI₁ (.sumI₂ (.unitI (.drop rfl (.cons (.cons (.cons kd.toP)))))))))

theorem elab_lend {Δ : LifeCtx} {Γ : Ctx VTy} {Ps : List VTy} {eM : Expr} {S : Row}
    {E : ExitRow} {A : VTy} (src : LendSrc) (x : LifeVar) (hΔ : Δ.Ok) (hx : Δ.find? x = none)
    (hS : S.Unwind x) (hsrc : LendOk Δ x src) (hsrcD : SlotOk src.ty)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (hfree : ¬ VFree x (.tensor (slotsTy Ps) (exitsTy A E)))
    (hout : VOutlives (Δ.extend x Δ.meetOfDom) (.var x) (slotsTy Ps) ∧
      VOutlives (Δ.extend x Δ.meetOfDom) (.var x) (exitsTy A E))
    (hM : CDerives (Δ.extend x Δ.meetOfDom) Γ eM
      (.comp (frTy S (.mut (.var x) src.payload :: Ps) E A))) :
    CDerives Δ Γ (lendE src eM) (.comp (frTy S (src.ty :: Ps) E A)) := by
  have kd := kill_dead Γ
  have hP : ¬ VFree x (slotsTy Ps) := fun h => hfree (Or.inl h)
  -- the callback, at `Δ, 'x`
  have hcb : CDerives Δ (⟨slotsTy Ps, true⟩ :: ⟨src.ty, false⟩ :: ⟨slotsTy (src.ty :: Ps), false⟩ :: Γ)
      (.val (.lam (.val (.lam (.app (.val (.lam (.app (.val (.lam
          (.letpair (.var 0) (.letpair (.var 1)
            (.seq (.app forget (.var 1)) (.pair (.var 0) (.var 2)))))))
          (.app (sh 6 eM) (.var 0)))))
        (.pair (.var 0) (.var 2)))))))
      (.val (cbUTy x Δ.meetOfDom (.mut (.var x) src.payload) (.tensor (slotsTy Ps) (exitsTy A E)) S)) := by
    refine .thunkV rfl (.allI (S := .unit)
      (Lifetime.Life.mentions_false_of_wf hx (Lifetime.meetOfDomL_wf Δ.entries))
      (fun _ _ h => hΔ.bound_mentions_false hx h) ?_ (.lam ?_))
    · intro s hs hl
      simp only [List.mem_cons] at hs
      rcases hs with rfl | rfl | rfl | hs
      · exact hP
      · cases hl
      · cases hl
      · exact hΓx s hs hl
    refine .bind (A := slotsTy (.mut (.var x) src.payload :: Ps))
      (.left (.dead (.left (.dead (.dead (splitP_right_all Γ))))))
      (.ret (.tensorI (.left (.dead (.right (.dead (.dead (deadSplit kd))))))
        (.var (.here (.cons (.cons (.cons (.cons kd.toP))))))
        (.var (.there (.there (.here (.cons (.cons kd.toP)))))))) ?_
    refine .effLet (A := .tensor (slotsTy (.mut (.var x) src.payload :: Ps)) (exitsTy A E))
      (splitP_left_all _) (fun _ => drops_dead (kill_dead _))
      (fun _ => persistent_dead (kill_dead _))
      (.app (A := slotsTy (.mut (.var x) src.payload :: Ps))
        (.right (.dead (.dead (.dead (.dead (.dead (splitP_left_all Γ)))))))
        (shift_deadN [⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩]
          (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))) hM)
        (.here (.cons (.cons (.cons (.cons (.cons kd.toP))))))) ?_
    have kd₂ := kill_dead (⟨slotsTy (.mut (.var x) src.payload :: Ps), true⟩ ::
      ⟨.mut (.var x) src.payload, false⟩ :: ⟨.unit, false⟩ :: ⟨slotsTy Ps, false⟩ ::
      ⟨src.ty, false⟩ :: ⟨slotsTy (src.ty :: Ps), false⟩ :: Γ)
    refine .tensorE (.left (deadSplit kd₂)) (.var (.here kd₂.toP)) ?_
    refine .tensorE (.right (.left (.dead (deadSplit kd₂)))) (.var (.there (.here (.cons kd₂.toP)))) ?_
    refine .unitE (.right (.left (.right (deadSplit (.cons (.cons kd₂))))))
      (.lolliE (splitP_left_all _) (.var (.there (.here (.cons (.cons (.cons kd₂.toP))))))
        (.forgetMut (kill_dead _).toP)) ?_
    refine .effSub (RowLe.nil S) (.ret (.boxI (.tensorI
      (.left (.dead (.right (deadSplit (.cons (.cons kd₂))))))
      (.var (.here (.cons (.cons (.cons (.cons kd₂.toP))))))
      (.var (.there (.there (.here (.cons (.cons kd₂.toP))))))) ?_))
    have hdef : (Δ.extend x Δ.meetOfDom).Defines (.var x) :=
      LifeCtx.defines_of_wf (wf_var_self _ _ _)
    exact .consLive hout.1 (.consDead (.consLive hout.2 (.consDead (.consDead
      (ctxOutlives_dead hdef kd₂)))))
  refine .lam (.tensorE (.left (splitP_right_all Γ)) (.var (.here kd.toP)) ?_)
  refine .bind (.left (.right (.dead (splitP_left_all Γ)))) (.ret hcb) ?_
  refine .bind (splitP_right_all _)
    (.ret (withborU_src (B := .tensor (slotsTy Ps) (exitsTy A E)) src (kill_dead _) hx hS hsrc
      hsrcD hfree)) ?_
  have kd₃ := kill_dead Γ
  refine .effLet (A := .tensor src.ty (.tensor (slotsTy Ps) (exitsTy A E))) (splitP_left_all _)
    (fun _ => drops_dead (kill_dead _)) (fun _ => persistent_dead (kill_dead _)) ?_ ?_
  · refine .app (.left (.right (.dead (.left (.dead (deadSplit kd₃))))))
      ?_ (.there (.here (.cons (.cons (.cons kd₃.toP)))))
    exact .app (.left (.dead (.dead (.right (.dead (deadSplit kd₃))))))
      (.force (C := .arr src.ty (.arr _ _)) (.here (.cons (.cons (.cons (.cons kd₃.toP))))))
      (.there (.there (.there (.here (.cons kd₃.toP)))))
  · have kd₄ := kill_dead (⟨withborUTy src.ty (cbUTy x Δ.meetOfDom (.mut (.var x) src.payload)
        (.tensor (slotsTy Ps) (exitsTy A E)) S) S (.tensor src.ty (.tensor (slotsTy Ps) (exitsTy A E))),
        true⟩ :: ⟨cbUTy x Δ.meetOfDom (.mut (.var x) src.payload) (.tensor (slotsTy Ps) (exitsTy A E)) S,
        true⟩ :: ⟨slotsTy Ps, false⟩ :: ⟨src.ty, true⟩ :: ⟨slotsTy (src.ty :: Ps), false⟩ :: kill Γ)
    refine .tensorE (.left (deadSplit kd₄)) (.var (.here kd₄.toP)) ?_
    refine .tensorE (.left (.right (.dead (deadSplit kd₄)))) (.var (.here (.cons (.cons kd₄.toP)))) ?_
    exact .effSub (RowLe.nil S) (.ret (.tensorI
      (.right (.left (.dead (.left (.dead (deadSplit kd₄))))))
      (.tensorI (.dead (.right (.dead (.left (.dead (deadSplit kd₄))))))
        (.var (.there (.there (.there (.here (.cons kd₄.toP))))))
        (.var (.there (.here (.cons (.cons (.cons kd₄.toP)))))))
      (.var (.here (.cons (.cons (.cons (.cons kd₄.toP))))))))

end BoCa.Fig16.LogRel.Core.Frames

end
