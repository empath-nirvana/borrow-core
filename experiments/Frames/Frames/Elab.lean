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

/-- The exit arm: at an empty row, `absurd` of the payload; else the drop glue. -/
theorem exitArm_derives {Δ : LifeCtx} {Γ : Ctx VTy} {E : ExitRow} {d : Expr} {C : CTy}
    {T : Slot VTy} (hE : T = ⟨E.sumTy, true⟩)
    (hd : E ≠ [] → CDerives Δ (T :: Γ) d (.comp C)) :
    CDerives Δ (T :: Γ) (exitArmE E d) (.comp C) := by
  cases E with
  | nil =>
      subst hE
      exact .zeroE (.left (splitP_right_all Γ)) (.var (.here (kill_dead Γ).toP))
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
  · refine exitArm_derives rfl (fun hE => ?_)
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

end BoCa.Fig16.LogRel.Core.Frames

end
