import Law2.FragInstances
import Law2.Rules

/-!
# Law2 — pure code answering a view, or a closure over one, held across a stop

Two borrowers at the depth-2 stack `[s@'x₂ reborrow, s@'x₁]` of `Law2/FragInstances.lean`, at the
row `{yield : I32 ↠ 1}`, each with every hypothesis discharged and its piece judgment built from
the rule lemmas of `Law2/Piece.lean` and `Law2/Rules.lean` (no open step):

* `view_call_spans`: `id = λz. return z; r = id m; yield 1; use r` — a pure call answers the view,
  and the answer, not frozen (its type `Mut 'x₂ _` reads the stack's variable), is held across the
  stop and used after it;
* `closure_call_spans`: `mk = λz. return (λ_. use z); f = mk m; u = yield 1; f u` — a pure call
  answers a closure over the view, held across the stop and called after it.

The pure closures are read re-lendably (`RSlot` at `U(A ⊸ F B)` is the piece at the empty row), so
the call answers a re-lendable value (`pj_call` at `F B`) and the frame of the bind across the stop
holds it (`pj_let`, `rctx_relendable`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N performE opPayload)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd GhostEnd.Instance
open Law2

/-- **Law 2 at the stack `[s@'x₂ reborrow, s@'x₁]`, for every borrower whose piece judgment
holds**, holding the reborrow's view and answering `()`: `law2_of_pj` with every hypothesis
discharged once. -/
theorem law2_A_pj (s : BoCa.Loc) {M : Expr}
    (hpj : PJ (ℍ := ℍ) δA [e₂ s, e₁ s] [yieldOp] ΔA [⟨TM, true⟩] M (CTy.effOf [yieldOp] .unit))
    (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (substAll [Val.loc s] M) (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) := by
  intro ρ ho
  have hσ : MixedStack [e₂ s, e₁ s] :=
    .reborrow rfl rfl rfl rfl (.mutOther rfl (by simp) .nil)
  have hx : AllCross [e₂ s, e₁ s] (Row.tab [yieldOp] δA) := fun n i en _ e he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  have ho' : ownersM (ℍ := ℍ) δA [e₂ s, e₁ s] ls ρ := by
    refine ⟨PMap.empty, ρ, compS_empty_left ρ, ?_, ρ, PMap.empty, ResU.comp_empty_right ρ, ?_,
      ⟨rfl, trivial⟩⟩
    · rw [if_pos (Reb_e₂ s)]; exact ⟨rfl, trivial⟩
    · rw [if_neg (not_Reb_e₁ s)]; exact ho
  have h := law2_of_pj (S := [yieldOp]) (yield_linResume δA) (yield_local δA)
    (β := OrderDual.toDual 2) hσ hx
    (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact TA_stratum)
    (fun e he v hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> cases hk)
    (Qa := fun _ v => ⌜v = Val.unit⌝) (fun _ _ _ _ _ h => h) (ds := [true, true])
    (bs := [OrderDual.toDual 4, OrderDual.toDual 3]) rfl rfl
    (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> decide)
    hpj trivial (γ := [Val.loc s])
    (fun αs hlt hch => hΔ_A (hlt.imp fun _ _ => le_of_lt) hch s)
    (fun αs ls ρv hlt hch hv => hctx_view αs ls ρv hlt hch hv)
    (fun αs ls v ρ _ _ h => ⟨h, fun a _ => by rw [h.1]; exact ResU.inStratum_empty a⟩) ls ρ ho'
  have hw : withOwnersM (ℍ := ℍ) δA [e₂ s, e₁ s] (fun _ v => ⌜v = Val.unit⌝) =
      fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝ := by
    simp only [withOwnersM, if_pos (Reb_e₂ s), if_neg (not_Reb_e₁ s)]; rfl
  rw [hw] at h
  exact h

/-! ### A pure call answering the view -/

/-- `id`'s type, `U(Mut 'x₂ _ ⊸ F (Mut 'x₂ _))`. -/
abbrev idTy : VTy := .thunk (.arr TM (.ret TM))

/-- **The program.** `id = λz. return z; r = id m; yield 1; use r`, `m` at index `0`. -/
abbrev viewCallE : Expr :=
  bindE (.val (.lam (.var 0))) (bindE (.app (.var 0) (.var 1)) (bindE (yE 1) (tailE 1)))

/-- `use r` at a context of a unit, `r`, and two dead slots. -/
theorem d_tailV {Δ : LifeCtx} {S₁ S₂ : VTy} :
    CDerives Δ [⟨.unit, true⟩, ⟨TM, true⟩, ⟨S₁, false⟩, ⟨S₂, false⟩] (tailE 1)
      (.comp (.ret .unit)) :=
  .bind (.right (.right (.dead (.dead .nil))))
    (.ret (.forgetMut (a := .var 2) (A := TA) (.cons (.cons (.cons (.cons .nil))))))
    (.bind (.left (.right (.left (.dead (.dead .nil)))))
      (.app (.left (.dead (.right (.dead (.dead .nil)))))
        (.force (.here (.cons (.cons (.cons (.cons .nil))))))
        (.there (.there (.here (.cons (.cons .nil))))))
      (.ret (.unitI (.drop pu (.cons (.drop pu (.cons (.cons (.cons .nil)))))))))

/-- The row `{yield}` is linear: no frame of a `let` at it drops or is copied. -/
theorem lin_yield : ∀ o ∈ [yieldOp], o.q = .lin := by simp [yieldOp]

/-- **The program is typed**: Core's typing derives it at `F_{yield} 1`, over the reborrow's
view. -/
theorem d_viewCall {Δ : LifeCtx} :
    CDerives Δ [⟨TM, true⟩] viewCallE (.comp (CTy.effOf [yieldOp] .unit)) :=
  .effLet (.right .nil) (fun ⟨o, ho, hq⟩ => absurd (lin_yield o ho) hq)
    (fun ⟨o, ho, hq⟩ => absurd (hq.symm.trans (lin_yield o ho)) (by decide))
    (.effSub (RowLe.nil _) (.ret (.thunkV rfl (.lam (.ret (.var (.here (.cons .nil))))))))
    (.effLet (.left (.left .nil)) (fun ⟨o, ho, hq⟩ => absurd (lin_yield o ho) hq)
      (fun ⟨o, ho, hq⟩ => absurd (hq.symm.trans (lin_yield o ho)) (by decide))
      (.effSub (RowLe.nil _)
        (.app (.left (.right .nil)) (.force (.here (.cons .nil))) (.there (.here .nil))))
      (.effLet (.right (.dead (.dead .nil))) (fun ⟨o, ho, hq⟩ => absurd (lin_yield o ho) hq)
        (fun ⟨o, ho, hq⟩ => absurd (hq.symm.trans (lin_yield o ho)) (by decide))
        (.effPerform (o := yieldOp) (by simp [Row.find, yieldOp]) rfl
          (.lit (.i32 1) (.cons (.cons (.cons .nil)))))
        (.effSub (RowLe.nil _) d_tailV)))

/-- The yield, its argument a literal, at a consumed context. -/
theorem pj_yield {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) (n : UInt32) {s : BoCa.Loc} :
    PJ (ℍ := ℍ) δA [e₂ s, e₁ s] [yieldOp] ΔA Γ (yE n) (CTy.effOf [yieldOp] .unit) :=
  pj_perform (o := yieldOp) (by simp [Row.find, yieldOp]) (by simp [outN, yieldOp]) rfl rfl rfl
    (fun _ _ h => by simp [VFree, yieldOp] at h) (fun _ _ => .int) trivial
    (pv_lit (IntLit.i32 n) hΓ)

/-- **The piece judgment of the program**, from the rule lemmas: the pure call's answer, the view,
is re-lendable (`pj_call` at `F (Mut 'x₂ _)`), and the bind across the yield holds it in its
frame. -/
theorem pj_viewCall (s : BoCa.Loc) :
    PJ (ℍ := ℍ) δA [e₂ s, e₁ s] [yieldOp] ΔA [⟨TM, true⟩] viewCallE
      (CTy.effOf [yieldOp] .unit) := by
  have hL : RowLin [yieldOp] [yieldOp] := rowLin_self (yield_linResume δA)
  refine pj_let (A := idTy) hL (.right .nil)
    (pj_of_pv (pv_lam (pj_ret (pv_var (.here (.cons .nil)))))) ?_
  refine pj_let (A := TM) hL (.left (.left .nil))
    (pj_effSub (RowLe.nil [yieldOp])
      (pj_call (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil)))) ?_
  refine pj_let (A := .unit) hL (.right (.dead (.dead .nil)))
    (pj_yield (.cons (.cons (.cons .nil))) 1) ?_
  exact pj_pure d_tailV
    (fun sl hs hl => by
      simp at hs; rcases hs with rfl | rfl | rfl | rfl <;> simp_all [NoThunkT])
    trivial (fun _ _ h => by simp [VFree] at h) (aboveAll_of_persistent rfl)

/-- **Pure code answering the view, held across a stop.** The generator lends `s` at `'x₁` and
reborrows it at `'x₂`; it calls the pure `id` on the reborrow's view, yields with the answer in its
frame, and uses the answer after. -/
theorem view_call_spans (s : BoCa.Loc) (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (substAll [Val.loc s] viewCallE) (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) :=
  law2_A_pj s (pj_viewCall s) ls

/-! ### A pure call answering a closure over the view -/

/-- The answer's type, `U(1 ⊸ F 1)`. -/
abbrev gTy : VTy := .thunk (.arr .unit (.ret .unit))

/-- `mk`'s type, `U(Mut 'x₂ _ ⊸ F (U(1 ⊸ F 1)))`. -/
abbrev mkTy : VTy := .thunk (.arr TM (.ret gTy))

/-- **The program.** `mk = λz. return (λ_. use z); f = mk m; u = yield 1; f u`, `m` at index
`0`. -/
abbrev closureCallE : Expr :=
  bindE (.val (.lam (.val (.lam (tailE 1)))))
    (bindE (.app (.var 0) (.var 1)) (bindE (yE 1) (.app (.var 1) (.var 0))))

/-- `use z` inside the closure: a unit argument, `z`, and a dead slot. -/
theorem d_body {Δ : LifeCtx} {S₁ : VTy} :
    CDerives Δ [⟨.unit, true⟩, ⟨TM, true⟩, ⟨S₁, false⟩] (tailE 1) (.comp (.ret .unit)) :=
  .bind (.right (.right (.dead .nil)))
    (.ret (.forgetMut (a := .var 2) (A := TA) (.cons (.cons (.cons .nil)))))
    (.bind (.left (.right (.left (.dead .nil))))
      (.app (.left (.dead (.right (.dead .nil))))
        (.force (.here (.cons (.cons (.cons .nil)))))
        (.there (.there (.here (.cons .nil)))))
      (.ret (.unitI (.drop pu (.cons (.drop pu (.cons (.cons .nil))))))))

/-- **The program is typed**: Core's typing derives it at `F_{yield} 1`, over the reborrow's
view. -/
theorem d_closureCall {Δ : LifeCtx} :
    CDerives Δ [⟨TM, true⟩] closureCallE (.comp (CTy.effOf [yieldOp] .unit)) :=
  .effLet (.right .nil) (fun ⟨o, ho, hq⟩ => absurd (lin_yield o ho) hq)
    (fun ⟨o, ho, hq⟩ => absurd (hq.symm.trans (lin_yield o ho)) (by decide))
    (.effSub (RowLe.nil _) (.ret (.thunkV rfl (.lam (.ret (.thunkV rfl (.lam d_body)))))))
    (.effLet (.left (.left .nil)) (fun ⟨o, ho, hq⟩ => absurd (lin_yield o ho) hq)
      (fun ⟨o, ho, hq⟩ => absurd (hq.symm.trans (lin_yield o ho)) (by decide))
      (.effSub (RowLe.nil _)
        (.app (.left (.right .nil)) (.force (.here (.cons .nil))) (.there (.here .nil))))
      (.effLet (.right (.dead (.dead .nil))) (fun ⟨o, ho, hq⟩ => absurd (lin_yield o ho) hq)
        (fun ⟨o, ho, hq⟩ => absurd (hq.symm.trans (lin_yield o ho)) (by decide))
        (.effPerform (o := yieldOp) (by simp [Row.find, yieldOp]) rfl
          (.lit (.i32 1) (.cons (.cons (.cons .nil)))))
        (.effSub (RowLe.nil _)
          (.app (.right (.left (.dead (.dead .nil)))) (.force (.there (.here (.cons (.cons .nil)))))
            (.here (.cons (.cons (.cons .nil))))))))

/-- **The piece judgment of the program**, from the rule lemmas: the pure call's answer is a
closure over the view, re-lendable with its environment (`rslot_lam`), held in the frame of the
bind across the yield and called after it. -/
theorem pj_closureCall (s : BoCa.Loc) :
    PJ (ℍ := ℍ) δA [e₂ s, e₁ s] [yieldOp] ΔA [⟨TM, true⟩] closureCallE
      (CTy.effOf [yieldOp] .unit) := by
  have hL : RowLin [yieldOp] [yieldOp] := rowLin_self (yield_linResume δA)
  have hbody : PJ (ℍ := ℍ) δA [e₂ s, e₁ s] [yieldOp] ΔA
      [⟨.unit, true⟩, ⟨TM, true⟩, ⟨TM, false⟩] (tailE 1) (.ret .unit) :=
    pj_pure (S := []) d_body
      (fun sl hs hl => by simp at hs; rcases hs with rfl | rfl | rfl <;> simp_all [NoThunkT])
      trivial (fun _ _ h => by simp [VFree] at h) (aboveAll_of_persistent rfl)
  refine pj_let (A := mkTy) hL (.right .nil)
    (pj_of_pv (pv_lam (pj_ret (pv_lam hbody)))) ?_
  refine pj_let (A := gTy) hL (.left (.left .nil))
    (pj_effSub (RowLe.nil [yieldOp])
      (pj_call (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil)))) ?_
  refine pj_let (A := .unit) hL (.right (.dead (.dead .nil)))
    (pj_yield (.cons (.cons (.cons .nil))) 1) ?_
  exact pj_effSub (RowLe.nil [yieldOp])
    (pj_call (.right (.left (.dead (.dead .nil)))) (.there (.here (.cons (.cons .nil))))
      (.here (.cons (.cons (.cons .nil)))))

/-- **Pure code answering a closure over the view, held across a stop.** The generator calls the
pure `mk` on the reborrow's view, yields with the closure it answers in its frame, and calls the
closure after, which uses the view. -/
theorem closure_call_spans (s : BoCa.Loc) (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (substAll [Val.loc s] closureCallE) (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) :=
  law2_A_pj s (pj_closureCall s) ls

end Law2.Inst

end
