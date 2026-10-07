import Core.Weaken
import Targets.Base.Typing
import Targets.Base.Programs

/-!
# Base — shifting and context lemmas (RESTRUCTURE §4.5)

Shifting a term under binders, splitting and killing slots,
and `CDerives.insert_dead`.  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free')

/-- The index a variable has after `d` slots are inserted at position `c`. -/
def sIdx (d c i : Nat) : Nat := if i < c then i else i + d

theorem sIdx_zero_succ (d c : Nat) : sIdx d (c + 1) 0 = 0 := by simp [sIdx]

theorem sIdx_succ (d c i : Nat) : sIdx d (c + 1) (i + 1) = sIdx d c i + 1 := by
  unfold sIdx; split_ifs <;> omega

theorem sIdx_at_zero (d i : Nat) : sIdx d 0 i = i + d := by simp [sIdx]

theorem var_shift (d c i : Nat) : (Expr.var i).shift d c = .var (sIdx d c i) := by
  unfold sIdx Expr.shift; split <;> rfl

theorem shift_closed0 {e : Expr} (h : closedAt 0 e = true) (d c : Nat) : e.shift d c = e :=
  shift_closedAt e d h (Nat.zero_le c)

theorem forceE_var_shift (C : CTy) (d c i : Nat) :
    (forceE C (.var i)).shift d c = forceE C (.var (sIdx d c i)) := by
  cases C <;> first
    | exact var_shift d c i
    | (show Expr.app ((Expr.var i).shift d c) ((Expr.val Val.unit).shift d c) = _
       rw [var_shift]; rfl)

theorem absurdE_shift (V : Expr) (d c : Nat) : (absurdE V).shift d c = absurdE (V.shift d c) := by
  simp [absurdE, Expr.shift]

theorem withPair_shift (M N : Expr) (d c : Nat) :
    (withPair M N).shift d c = withPair (M.shift d (c + 1 + 1)) (N.shift d (c + 1 + 1)) := by
  simp [withPair, Expr.shift]

theorem hndTerm_shift (n : UInt32) (ir ic : Nat) (e : Expr) (d c : Nat) :
    (hndTerm n ir ic e).shift d c = hndTerm n (sIdx d c ir) (sIdx d c ic) (e.shift d c) := by
  show Expr.app (Expr.app (.prim .hnd) (.pair (.prim (.lit (.i32 n)))
      (.pair ((Expr.var ir).shift d c) ((Expr.var ic).shift d c)))) (e.shift d c) = _
  rw [var_shift, var_shift]; rfl

variable {Γd : Ctx VTy}

theorem deadP_prepend (hd : Ctx.Dead Γd) {Γ : Ctx VTy} (h : Ctx.DeadP Γ) :
    Ctx.DeadP (Γd ++ Γ) := by
  induction hd with
  | nil => exact h
  | cons _ ih => exact .cons ih

theorem deadP_insert (hd : Ctx.Dead Γd) : ∀ (Γa : Ctx VTy) {Γb : Ctx VTy},
    Ctx.DeadP (Γa ++ Γb) → Ctx.DeadP (Γa ++ Γd ++ Γb)
  | [], _, h => deadP_prepend hd h
  | _ :: Γa, _, h => by
      rw [List.cons_append] at h
      cases h with
      | cons h => exact .cons (deadP_insert hd Γa h)
      | drop hT h => exact .drop hT (deadP_insert hd Γa h)

theorem splitP_prepend (hd : Ctx.Dead Γd) {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) :
    Ctx.SplitP (Γd ++ Γ) (Γd ++ Γ₁) (Γd ++ Γ₂) := by
  induction hd with
  | nil => exact h
  | cons _ ih => exact .dead ih

theorem splitP_insert (hd : Ctx.Dead Γd) : ∀ (Γa : Ctx VTy) {Γb Γ₁ Γ₂ : Ctx VTy},
    Ctx.SplitP (Γa ++ Γb) Γ₁ Γ₂ →
    ∃ Γa₁ Γb₁ Γa₂ Γb₂, Γ₁ = Γa₁ ++ Γb₁ ∧ Γ₂ = Γa₂ ++ Γb₂ ∧ Γa₁.length = Γa.length ∧
      Γa₂.length = Γa.length ∧ Ctx.SplitP (Γa ++ Γd ++ Γb) (Γa₁ ++ Γd ++ Γb₁) (Γa₂ ++ Γd ++ Γb₂)
  | [], _, Γ₁, Γ₂, h => ⟨[], Γ₁, [], Γ₂, rfl, rfl, rfl, rfl, splitP_prepend hd h⟩
  | _ :: Γa, _, _, _, h => by
      rw [List.cons_append] at h
      cases h with
      | left h =>
          obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs⟩ := splitP_insert hd Γa h
          exact ⟨_ :: Γa₁, Γb₁, _ :: Γa₂, Γb₂, rfl, rfl, by simp [h₁], by simp [h₂], .left hs⟩
      | right h =>
          obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs⟩ := splitP_insert hd Γa h
          exact ⟨_ :: Γa₁, Γb₁, _ :: Γa₂, Γb₂, rfl, rfl, by simp [h₁], by simp [h₂], .right hs⟩
      | dead h =>
          obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs⟩ := splitP_insert hd Γa h
          exact ⟨_ :: Γa₁, Γb₁, _ :: Γa₂, Γb₂, rfl, rfl, by simp [h₁], by simp [h₂], .dead hs⟩
      | dup hT h =>
          obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs⟩ := splitP_insert hd Γa h
          exact ⟨_ :: Γa₁, Γb₁, _ :: Γa₂, Γb₂, rfl, rfl, by simp [h₁], by simp [h₂], .dup hT hs⟩

theorem soloP_prepend (hd : Ctx.Dead Γd) {Γ : Ctx VTy} {i : Nat} {A : VTy}
    (h : Ctx.SoloP Γ i A) : Ctx.SoloP (Γd ++ Γ) (i + Γd.length) A := by
  induction hd with
  | nil => exact h
  | cons _ ih => exact .there ih

theorem soloP_insert (hd : Ctx.Dead Γd) : ∀ (Γa : Ctx VTy) {Γb : Ctx VTy} {i : Nat} {A : VTy},
    Ctx.SoloP (Γa ++ Γb) i A → Ctx.SoloP (Γa ++ Γd ++ Γb) (sIdx Γd.length Γa.length i) A
  | [], _, _, _, h => by
      rw [List.length_nil, sIdx_at_zero]; exact soloP_prepend hd h
  | _ :: Γa, _, _, _, h => by
      rw [List.cons_append] at h
      cases h with
      | here h => rw [List.length_cons, sIdx_zero_succ]; exact .here (deadP_insert hd Γa h)
      | there h => rw [List.length_cons, sIdx_succ]; exact .there (soloP_insert hd Γa h)
      | skip hS h => rw [List.length_cons, sIdx_succ]; exact .skip hS (soloP_insert hd Γa h)

theorem live_insert (hd : Ctx.Dead Γd) {P : Slot VTy → Prop} {Γa Γb : Ctx VTy}
    (h : ∀ s ∈ Γa ++ Γb, s.live = true → P s) : ∀ s ∈ Γa ++ Γd ++ Γb, s.live = true → P s := by
  intro s hs hl
  simp only [List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · exact h s (List.mem_append_left _ hs) hl
  · rw [dead_not_live hd s hs] at hl; cases hl
  · exact h s (List.mem_append_right _ hs) hl

/-- A derivation at `Γa ++ Γb` is one at `Γa ++ Γd ++ Γb` for dead `Γd`, the term's variables
past `Γa` shifted past `Γd`. -/
theorem CDerives.insert_dead (hd : Ctx.Dead Γd) {Δ : LifeCtx} {Γ₀ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ₀ e j) : ∀ (Γa Γb : Ctx VTy), Γ₀ = Γa ++ Γb →
    CDerives Δ (Γa ++ Γd ++ Γb) (e.shift Γd.length Γa.length) j := by
  induction h with
  | var hs =>
      intro Γa Γb hΓ; subst hΓ
      rw [var_shift]; exact .var (soloP_insert hd Γa hs)
  | unitI hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      exact .unitI (deadP_insert hd Γa hΓ)
  | tensorI hs _ _ ih₁ ih₂ =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have e₁ := ih₁ Γa₁ Γb₁ rfl
      have e₂ := ih₂ Γa₂ Γb₂ rfl
      rw [h₁] at e₁; rw [h₂] at e₂
      exact .tensorI hs' e₁ e₂
  | sumI₁ _ ih => intro Γa Γb hΓ; exact .sumI₁ (ih Γa Γb hΓ)
  | sumI₂ _ ih => intro Γa Γb hΓ; exact .sumI₂ (ih Γa Γb hΓ)
  | thunkF _ ih =>
      intro Γa Γb hΓ; subst hΓ
      have e' := ih (_ :: Γa) Γb rfl
      rw [List.length_cons] at e'
      exact .thunkF e'
  | thunkV hC _ ih => intro Γa Γb hΓ; exact .thunkV hC (ih Γa Γb hΓ)
  | ret _ ih => intro Γa Γb hΓ; exact .ret (ih Γa Γb hΓ)
  | bind hs _ _ ihM ihN =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ihM Γa₁ Γb₁ rfl
      have eN := ihN (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eM; rw [List.length_cons, h₂] at eN
      exact .bind hs' eM eN
  | force hs =>
      intro Γa Γb hΓ; subst hΓ
      rw [forceE_var_shift]; exact .force (soloP_insert hd Γa hs)
  | lam _ ih =>
      intro Γa Γb hΓ; subst hΓ
      have e' := ih (_ :: Γa) Γb rfl
      rw [List.length_cons] at e'
      exact .lam e'
  | app hs _ hx ih =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ih Γa₁ Γb₁ rfl
      have hx' := soloP_insert hd Γa₂ hx
      rw [h₁] at eM; rw [h₂] at hx'
      show CDerives _ _ (.app _ ((Expr.var _).shift _ _)) _
      rw [var_shift]; exact .app hs' eM hx'
  | withI _ _ ihM ihN =>
      intro Γa Γb hΓ; subst hΓ
      have eM := ihM (_ :: _ :: Γa) Γb rfl
      have eN := ihN (_ :: _ :: Γa) Γb rfl
      simp only [List.length_cons] at eM eN
      rw [withPair_shift]; exact .withI eM eN
  | proj₁ _ ih => intro Γa Γb hΓ; exact .proj₁ (ih Γa Γb hΓ)
  | proj₂ _ ih => intro Γa Γb hΓ; exact .proj₂ (ih Γa Γb hΓ)
  | topI => intro Γa Γb _; exact .topI
  | unitE hs _ _ ihV ihM =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eV := ihV Γa₁ Γb₁ rfl
      have eM := ihM Γa₂ Γb₂ rfl
      rw [h₁] at eV; rw [h₂] at eM
      exact .unitE hs' eV eM
  | tensorE hs _ _ ihV ihM =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eV := ihV Γa₁ Γb₁ rfl
      have eM := ihM (_ :: _ :: Γa₂) Γb₂ rfl
      rw [h₁] at eV; simp only [List.length_cons, h₂] at eM
      exact .tensorE hs' eV eM
  | sumE hs _ _ _ ihV ih₁ ih₂ =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eV := ihV Γa₁ Γb₁ rfl
      have e₁ := ih₁ (_ :: Γa₂) Γb₂ rfl
      have e₂ := ih₂ (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eV; rw [List.length_cons, h₂] at e₁ e₂
      exact .sumE hs' eV e₁ e₂
  | zeroE hs _ ihV =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eV := ihV Γa₁ Γb₁ rfl
      rw [h₁] at eV
      rw [absurdE_shift]; exact .zeroE hs' eV
  | allI hbx hΔx hΓx _ ih =>
      intro Γa Γb hΓ; subst hΓ
      have e' := ih (_ :: Γa) Γb rfl
      rw [List.length_cons] at e'
      exact .allI hbx hΔx (live_insert hd hΓx) e'
  | allE _ hlt ih => intro Γa Γb hΓ; exact .allE (ih Γa Γb hΓ) hlt
  | bangThunkF hp _ ih =>
      intro Γa Γb hΓ; subst hΓ
      have e' := ih (_ :: Γa) Γb rfl
      rw [List.length_cons] at e'
      exact .bangThunkF (live_insert hd hp) e'
  | bangThunkV hp hC _ ih =>
      intro Γa Γb hΓ; subst hΓ
      exact .bangThunkV (live_insert hd hp) hC (ih Γa Γb rfl)
  | bangE _ ih => intro Γa Γb hΓ; exact .bangE (ih Γa Γb hΓ)
  | copyBang hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := copy) (by rfl)]; exact .copyBang (deadP_insert hd Γa hΓ)
  | forgetBang hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := forget) (by rfl)]; exact .forgetBang (deadP_insert hd Γa hΓ)
  | boxI _ hΓ ih =>
      intro Γa Γb hΓ'; subst hΓ'
      exact .boxI (ih Γa Γb rfl) ⟨hΓ.1, live_insert hd hΓ.2⟩
  | boxE _ ih => intro Γa Γb hΓ; exact .boxE (ih Γa Γb hΓ)
  | immSub _ hle ih => intro Γa Γb hΓ; exact .immSub (ih Γa Γb hΓ) hle
  | mutSub _ hle ih => intro Γa Γb hΓ; exact .mutSub (ih Γa Γb hΓ) hle
  | alloc hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .alloc (deadP_insert hd Γa hΓ)
  | free hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .free (deadP_insert hd Γa hΓ)
  | swap hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := swap) (by rfl)]; exact .swap (deadP_insert hd Γa hΓ)
  | copy hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := copy) (by rfl)]; exact .copy (deadP_insert hd Γa hΓ)
  | forgetImm hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := forget) (by rfl)]; exact .forgetImm (deadP_insert hd Γa hΓ)
  | forgetMut hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := forget) (by rfl)]; exact .forgetMut (deadP_insert hd Γa hΓ)
  | forgetUnk hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := forget) (by rfl)]; exact .forgetUnk (deadP_insert hd Γa hΓ)
  | lit c hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .lit c (deadP_insert hd Γa hΓ)
  | hostOp op hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .hostOp op (deadP_insert hd Γa hΓ)
  | arrNew A hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .arrNew A (deadP_insert hd Γa hΓ)
  | arrFree A hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .arrFree A (deadP_insert hd Γa hΓ)
  | arrSize A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := sizeV.1) (by rfl)]; exact .arrSize A (deadP_insert hd Γa hΓ)
  | arrReplace A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := replaceV.1) (by rfl)]; exact .arrReplace A (deadP_insert hd Γa hΓ)
  | arrLen a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := arrLenV.1) (by rfl)]; exact .arrLen a A (deadP_insert hd Γa hΓ)
  | arrGet a A hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .arrGet a A (deadP_insert hd Γa hΓ)
  | arrCopy a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := copyV.1) (by rfl)]; exact .arrCopy a A (deadP_insert hd Γa hΓ)
  | arrForget a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := forgetV.1) (by rfl)]; exact .arrForget a A (deadP_insert hd Γa hΓ)
  | countFold S hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .countFold S (deadP_insert hd Γa hΓ)
  | countTry S E hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .countTry S E (deadP_insert hd Γa hΓ)
  | boundedFix A C hΓ =>
      intro Γa Γb hΓ'; subst hΓ'; exact .boundedFix A C (deadP_insert hd Γa hΓ)
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := withbor) (by rfl)]
      exact .sliceBorrowM x (deadP_insert hd Γa hΓ) hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := withbor) (by rfl)]
      exact .sliceBorrowI x (deadP_insert hd Γa hΓ) hsc hA hB hf₁ hf₂
  | sliceGetM a A hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .sliceGetM a A (deadP_insert hd Γa hΓ)
  | sliceLenM a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := sizeV.1) (by rfl)]; exact .sliceLenM a A (deadP_insert hd Γa hΓ)
  | sliceSplitI a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'; exact .sliceSplitI a A (deadP_insert hd Γa hΓ)
  | sliceSplitM a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'; exact .sliceSplitM a A (deadP_insert hd Γa hΓ)
  | sliceEmptyI a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := emptyFamV.1) (by rfl)]; exact .sliceEmptyI a A (deadP_insert hd Γa hΓ)
  | sliceEmptyM a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := emptyFamV.1) (by rfl)]; exact .sliceEmptyM a A (deadP_insert hd Γa hΓ)
  | sliceReplaceM a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := replaceV.1) (by rfl)]
      exact .sliceReplaceM a A (deadP_insert hd Γa hΓ)
  | sliceSwapM a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := swapV.1) (by rfl)]; exact .sliceSwapM a A (deadP_insert hd Γa hΓ)
  | withbor1 x hΓ hx hsc hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := withbor) (by rfl)]
      exact .withbor1 x (deadP_insert hd Γa hΓ) hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := withbor) (by rfl)]
      exact .withbor2 x (deadP_insert hd Γa hΓ) hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := withbor) (by rfl)]
      exact .withbor3 x (deadP_insert hd Γa hΓ) hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := withload) (by rfl)]
      exact .withload x (deadP_insert hd Γa hΓ) hx hf₁ hf₂
  | withswap hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := withswap) (by rfl)]; exact .withswap (deadP_insert hd Γa hΓ)
  | withbor1U x hΓ hx hsc hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb hΓ'; subst hΓ'
      have ed := ihd Γa Γb rfl
      rw [shift_closed0 hdc] at ed
      rw [shift_closed0 (withborUE_closed hdc)]
      exact .withbor1U x (deadP_insert hd Γa hΓ) hx hsc hf₁ hf₂ hS hdc ed
  | withbor2U x hΓ hx hside hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb hΓ'; subst hΓ'
      have ed := ihd Γa Γb rfl
      rw [shift_closed0 hdc] at ed
      rw [shift_closed0 (withborUE_closed hdc)]
      exact .withbor2U x (deadP_insert hd Γa hΓ) hx hside hf₁ hf₂ hS hdc ed
  | withbor3U x hΓ hx hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb hΓ'; subst hΓ'
      have ed := ihd Γa Γb rfl
      rw [shift_closed0 hdc] at ed
      rw [shift_closed0 (withborUE_closed hdc)]
      exact .withbor3U x (deadP_insert hd Γa hΓ) hx hf₁ hf₂ hS hdc ed
  | withloadU x hΓ hx hf₁ hf₂ hS =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := withload) (by rfl)]
      exact .withloadU x (deadP_insert hd Γa hΓ) hx hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb hΓ'; subst hΓ'
      have ed := ihd Γa Γb rfl
      rw [shift_closed0 hdc] at ed
      rw [shift_closed0 (withborUE_closed hdc)]
      exact .sliceBorrowMU x (deadP_insert hd Γa hΓ) hA hB hf₁ hf₂ hS hdc ed
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb hΓ'; subst hΓ'
      have ed := ihd Γa Γb rfl
      rw [shift_closed0 hdc] at ed
      rw [shift_closed0 (withborUE_closed hdc)]
      exact .sliceBorrowIU x (deadP_insert hd Γa hΓ) hsc hA hB hf₁ hf₂ hS hdc ed
  | lolliE hs _ _ iha ihf =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have ea := iha Γa₁ Γb₁ rfl
      have ef := ihf Γa₂ Γb₂ rfl
      rw [h₁] at ea; rw [h₂] at ef
      exact .lolliE hs' ea ef
  | allEV _ hlt ih => intro Γa Γb hΓ; exact .allEV (ih Γa Γb hΓ) hlt
  | ofRet _ ih => intro Γa Γb hΓ; exact .ofRet (ih Γa Γb hΓ)
  | roll hA hc _ ih => intro Γa Γb hΓ; exact .roll hA hc (ih Γa Γb hΓ)
  | unroll _ ih => intro Γa Γb hΓ; exact .unroll (ih Γa Γb hΓ)
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (foldImmV_closed F)]
      exact .foldImm F y c R (deadP_insert hd Γa hΓ) hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (foldOwnV_closed F)]
      exact .foldOwn F R (deadP_insert hd Γa hΓ) hF hG
  | foldReuse F R hΓ hF hG =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (foldReuseV_closed F)]
      exact .foldReuse F R (deadP_insert hd Γa hΓ) hF hG
  | nuIn hC _ ih => intro Γa Γb hΓ; exact .nuIn hC (ih Γa Γb hΓ)
  | nuOut hC _ ih => intro Γa Γb hΓ; exact .nuOut hC (ih Γa Γb hΓ)
  | unfoldN C S hC hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (unfoldV_closed C)]
      exact .unfoldN C S hC (deadP_insert hd Γa hΓ)
  | effSub hle _ ih => intro Γa Γb hΓ; exact .effSub hle (ih Γa Γb hΓ)
  | effPerform hf hna _ ih => intro Γa Γb hΓ; exact .effPerform hf hna (ih Γa Γb hΓ)
  | effRaise hf ha hdr _ ih => intro Γa Γb hΓ; exact .effRaise hf ha hdr (ih Γa Γb hΓ)
  | effLet hs hW hU _ _ ihM ihN =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ihM Γa₁ Γb₁ rfl
      have eN := ihN (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eM; rw [List.length_cons, h₂] at eN
      exact .effLet hs' (fun hw => live_insert hd (P := fun s => s.ty.Drop) (hW hw))
        (fun hu => live_insert hd (hU hu)) eM eN
  | effThen hs hNZ hUq hU _ _ _ ihM ihN ihD =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ihM Γa₁ Γb₁ rfl
      have eN := ihN (_ :: Γa₂) Γb₂ rfl
      have eD := ihD (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eM; rw [List.length_cons, h₂] at eN eD
      exact .effThen hs' hNZ hUq (fun hu => live_insert hd (hU hu)) eM eN eD
  | effHandle hs hs₁ hr hc hn0 hnS hlen _ ih =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      obtain ⟨Γar, Γbr, Γac, Γbc, rfl, rfl, hr₁, hc₁, hs₁'⟩ := splitP_insert hd Γa₁ hs₁
      have e' := ih Γa₂ Γb₂ rfl
      have hr' := soloP_insert hd Γar hr
      have hc' := soloP_insert hd Γac hc
      rw [h₂] at e'; rw [hr₁, h₁] at hr'; rw [hc₁, h₁] at hc'
      rw [hndTerm_shift]
      exact .effHandle hs' hs₁' hr' hc' hn0 hnS hlen e'

/-- `CDerives.insert_dead` at the unr-free rules: a derivation at `Γa ++ Γb` is one at
`Γa ++ Γd ++ Γb` for dead `Γd`, the term's variables past `Γa` shifted past `Γd`. -/
theorem CDerivesNU.insert_dead (hd : Ctx.Dead Γd) {Δ : LifeCtx} {Γ₀ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ₀ e j) : ∀ (Γa Γb : Ctx VTy), Γ₀ = Γa ++ Γb →
    CDerivesNU Δ (Γa ++ Γd ++ Γb) (e.shift Γd.length Γa.length) j := by
  induction h with
  | var hs =>
      intro Γa Γb hΓ; subst hΓ
      rw [var_shift]; exact .var (soloP_insert hd Γa hs)
  | unitI hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      exact .unitI (deadP_insert hd Γa hΓ)
  | tensorI hs _ _ ih₁ ih₂ =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have e₁ := ih₁ Γa₁ Γb₁ rfl
      have e₂ := ih₂ Γa₂ Γb₂ rfl
      rw [h₁] at e₁; rw [h₂] at e₂
      exact .tensorI hs' e₁ e₂
  | sumI₁ _ ih => intro Γa Γb hΓ; exact .sumI₁ (ih Γa Γb hΓ)
  | sumI₂ _ ih => intro Γa Γb hΓ; exact .sumI₂ (ih Γa Γb hΓ)
  | thunkF _ ih =>
      intro Γa Γb hΓ; subst hΓ
      have e' := ih (_ :: Γa) Γb rfl
      rw [List.length_cons] at e'
      exact .thunkF e'
  | thunkV hC _ ih => intro Γa Γb hΓ; exact .thunkV hC (ih Γa Γb hΓ)
  | ret _ ih => intro Γa Γb hΓ; exact .ret (ih Γa Γb hΓ)
  | bind hs _ _ ihM ihN =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ihM Γa₁ Γb₁ rfl
      have eN := ihN (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eM; rw [List.length_cons, h₂] at eN
      exact .bind hs' eM eN
  | force hs =>
      intro Γa Γb hΓ; subst hΓ
      rw [forceE_var_shift]; exact .force (soloP_insert hd Γa hs)
  | lam _ ih =>
      intro Γa Γb hΓ; subst hΓ
      have e' := ih (_ :: Γa) Γb rfl
      rw [List.length_cons] at e'
      exact .lam e'
  | app hs _ hx ih =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ih Γa₁ Γb₁ rfl
      have hx' := soloP_insert hd Γa₂ hx
      rw [h₁] at eM; rw [h₂] at hx'
      show CDerivesNU _ _ (.app _ ((Expr.var _).shift _ _)) _
      rw [var_shift]; exact .app hs' eM hx'
  | withI _ _ ihM ihN =>
      intro Γa Γb hΓ; subst hΓ
      have eM := ihM (_ :: _ :: Γa) Γb rfl
      have eN := ihN (_ :: _ :: Γa) Γb rfl
      simp only [List.length_cons] at eM eN
      rw [withPair_shift]; exact .withI eM eN
  | proj₁ _ ih => intro Γa Γb hΓ; exact .proj₁ (ih Γa Γb hΓ)
  | proj₂ _ ih => intro Γa Γb hΓ; exact .proj₂ (ih Γa Γb hΓ)
  | topI => intro Γa Γb _; exact .topI
  | unitE hs _ _ ihV ihM =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eV := ihV Γa₁ Γb₁ rfl
      have eM := ihM Γa₂ Γb₂ rfl
      rw [h₁] at eV; rw [h₂] at eM
      exact .unitE hs' eV eM
  | tensorE hs _ _ ihV ihM =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eV := ihV Γa₁ Γb₁ rfl
      have eM := ihM (_ :: _ :: Γa₂) Γb₂ rfl
      rw [h₁] at eV; simp only [List.length_cons, h₂] at eM
      exact .tensorE hs' eV eM
  | sumE hs _ _ _ ihV ih₁ ih₂ =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eV := ihV Γa₁ Γb₁ rfl
      have e₁ := ih₁ (_ :: Γa₂) Γb₂ rfl
      have e₂ := ih₂ (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eV; rw [List.length_cons, h₂] at e₁ e₂
      exact .sumE hs' eV e₁ e₂
  | zeroE hs _ ihV =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eV := ihV Γa₁ Γb₁ rfl
      rw [h₁] at eV
      rw [absurdE_shift]; exact .zeroE hs' eV
  | allI hbx hΔx hΓx _ ih =>
      intro Γa Γb hΓ; subst hΓ
      have e' := ih (_ :: Γa) Γb rfl
      rw [List.length_cons] at e'
      exact .allI hbx hΔx (live_insert hd hΓx) e'
  | allE _ hlt ih => intro Γa Γb hΓ; exact .allE (ih Γa Γb hΓ) hlt
  | bangThunkF hp _ ih =>
      intro Γa Γb hΓ; subst hΓ
      have e' := ih (_ :: Γa) Γb rfl
      rw [List.length_cons] at e'
      exact .bangThunkF (live_insert hd hp) e'
  | bangThunkV hp hC _ ih =>
      intro Γa Γb hΓ; subst hΓ
      exact .bangThunkV (live_insert hd hp) hC (ih Γa Γb rfl)
  | bangE _ ih => intro Γa Γb hΓ; exact .bangE (ih Γa Γb hΓ)
  | copyBang hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.copy) (by rfl)]; exact .copyBang (deadP_insert hd Γa hΓ)
  | forgetBang hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.forget) (by rfl)]; exact .forgetBang (deadP_insert hd Γa hΓ)
  | boxI _ hΓ ih =>
      intro Γa Γb hΓ'; subst hΓ'
      exact .boxI (ih Γa Γb rfl) ⟨hΓ.1, live_insert hd hΓ.2⟩
  | boxE _ ih => intro Γa Γb hΓ; exact .boxE (ih Γa Γb hΓ)
  | immSub _ hle ih => intro Γa Γb hΓ; exact .immSub (ih Γa Γb hΓ) hle
  | mutSub _ hle ih => intro Γa Γb hΓ; exact .mutSub (ih Γa Γb hΓ) hle
  | alloc hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .alloc (deadP_insert hd Γa hΓ)
  | free hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .free (deadP_insert hd Γa hΓ)
  | swap hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.swap) (by rfl)]; exact .swap (deadP_insert hd Γa hΓ)
  | copy hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.copy) (by rfl)]; exact .copy (deadP_insert hd Γa hΓ)
  | forgetImm hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.forget) (by rfl)]; exact .forgetImm (deadP_insert hd Γa hΓ)
  | forgetMut hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.forget) (by rfl)]; exact .forgetMut (deadP_insert hd Γa hΓ)
  | forgetUnk hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.forget) (by rfl)]; exact .forgetUnk (deadP_insert hd Γa hΓ)
  | lit c hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .lit c (deadP_insert hd Γa hΓ)
  | hostOp op hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .hostOp op (deadP_insert hd Γa hΓ)
  | arrNew A hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .arrNew A (deadP_insert hd Γa hΓ)
  | arrFree A hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .arrFree A (deadP_insert hd Γa hΓ)
  | arrSize A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := sizeV.1) (by rfl)]; exact .arrSize A (deadP_insert hd Γa hΓ)
  | arrReplace A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := replaceV.1) (by rfl)]; exact .arrReplace A (deadP_insert hd Γa hΓ)
  | arrLen a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := arrLenV.1) (by rfl)]; exact .arrLen a A (deadP_insert hd Γa hΓ)
  | arrGet a A hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .arrGet a A (deadP_insert hd Γa hΓ)
  | arrCopy a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := copyV.1) (by rfl)]; exact .arrCopy a A (deadP_insert hd Γa hΓ)
  | arrForget a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := forgetV.1) (by rfl)]; exact .arrForget a A (deadP_insert hd Γa hΓ)
  | countFold S hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .countFold S (deadP_insert hd Γa hΓ)
  | countTry S E hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .countTry S E (deadP_insert hd Γa hΓ)
  | boundedFix A C hΓ =>
      intro Γa Γb hΓ'; subst hΓ'; exact .boundedFix A C (deadP_insert hd Γa hΓ)
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.withbor) (by rfl)]
      exact .sliceBorrowM x (deadP_insert hd Γa hΓ) hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.withbor) (by rfl)]
      exact .sliceBorrowI x (deadP_insert hd Γa hΓ) hsc hA hB hf₁ hf₂
  | sliceGetM a A hΓ => intro Γa Γb hΓ'; subst hΓ'; exact .sliceGetM a A (deadP_insert hd Γa hΓ)
  | sliceLenM a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := sizeV.1) (by rfl)]; exact .sliceLenM a A (deadP_insert hd Γa hΓ)
  | sliceSplitI a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'; exact .sliceSplitI a A (deadP_insert hd Γa hΓ)
  | sliceSplitM a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'; exact .sliceSplitM a A (deadP_insert hd Γa hΓ)
  | sliceEmptyI a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := emptyFamV.1) (by rfl)]; exact .sliceEmptyI a A (deadP_insert hd Γa hΓ)
  | sliceEmptyM a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := emptyFamV.1) (by rfl)]; exact .sliceEmptyM a A (deadP_insert hd Γa hΓ)
  | sliceReplaceM a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := replaceV.1) (by rfl)]
      exact .sliceReplaceM a A (deadP_insert hd Γa hΓ)
  | sliceSwapM a A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := swapV.1) (by rfl)]; exact .sliceSwapM a A (deadP_insert hd Γa hΓ)
  | withbor1 x hΓ hx hsc hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.withbor) (by rfl)]
      exact .withbor1 x (deadP_insert hd Γa hΓ) hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.withbor) (by rfl)]
      exact .withbor2 x (deadP_insert hd Γa hΓ) hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.withbor) (by rfl)]
      exact .withbor3 x (deadP_insert hd Γa hΓ) hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.withload) (by rfl)]
      exact .withload x (deadP_insert hd Γa hΓ) hx hf₁ hf₂
  | withswap hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.withswap) (by rfl)]; exact .withswap (deadP_insert hd Γa hΓ)
  | withbor1U x hΓ hx hsc hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb hΓ'; subst hΓ'
      have ed := ihd Γa Γb rfl
      rw [shift_closed0 hdc] at ed
      rw [shift_closed0 (withborUE_closed hdc)]
      exact .withbor1U x (deadP_insert hd Γa hΓ) hx hsc hf₁ hf₂ hS hdc ed
  | withbor2U x hΓ hx hside hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb hΓ'; subst hΓ'
      have ed := ihd Γa Γb rfl
      rw [shift_closed0 hdc] at ed
      rw [shift_closed0 (withborUE_closed hdc)]
      exact .withbor2U x (deadP_insert hd Γa hΓ) hx hside hf₁ hf₂ hS hdc ed
  | withbor3U x hΓ hx hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb hΓ'; subst hΓ'
      have ed := ihd Γa Γb rfl
      rw [shift_closed0 hdc] at ed
      rw [shift_closed0 (withborUE_closed hdc)]
      exact .withbor3U x (deadP_insert hd Γa hΓ) hx hf₁ hf₂ hS hdc ed
  | withloadU x hΓ hx hf₁ hf₂ hS =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.withload) (by rfl)]
      exact .withloadU x (deadP_insert hd Γa hΓ) hx hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb hΓ'; subst hΓ'
      have ed := ihd Γa Γb rfl
      rw [shift_closed0 hdc] at ed
      rw [shift_closed0 (withborUE_closed hdc)]
      exact .sliceBorrowMU x (deadP_insert hd Γa hΓ) hA hB hf₁ hf₂ hS hdc ed
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb hΓ'; subst hΓ'
      have ed := ihd Γa Γb rfl
      rw [shift_closed0 hdc] at ed
      rw [shift_closed0 (withborUE_closed hdc)]
      exact .sliceBorrowIU x (deadP_insert hd Γa hΓ) hsc hA hB hf₁ hf₂ hS hdc ed
  | lolliE hs _ _ iha ihf =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have ea := iha Γa₁ Γb₁ rfl
      have ef := ihf Γa₂ Γb₂ rfl
      rw [h₁] at ea; rw [h₂] at ef
      exact .lolliE hs' ea ef
  | allEV _ hlt ih => intro Γa Γb hΓ; exact .allEV (ih Γa Γb hΓ) hlt
  | ofRet _ ih => intro Γa Γb hΓ; exact .ofRet (ih Γa Γb hΓ)
  | roll hA hc _ ih => intro Γa Γb hΓ; exact .roll hA hc (ih Γa Γb hΓ)
  | unroll _ ih => intro Γa Γb hΓ; exact .unroll (ih Γa Γb hΓ)
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (foldImmV_closed F)]
      exact .foldImm F y c R (deadP_insert hd Γa hΓ) hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (foldOwnV_closed F)]
      exact .foldOwn F R (deadP_insert hd Γa hΓ) hF hG
  | foldReuse F R hΓ hF hG =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (foldReuseV_closed F)]
      exact .foldReuse F R (deadP_insert hd Γa hΓ) hF hG
  | nuIn hC _ ih => intro Γa Γb hΓ; exact .nuIn hC (ih Γa Γb hΓ)
  | nuOut hC _ ih => intro Γa Γb hΓ; exact .nuOut hC (ih Γa Γb hΓ)
  | unfoldN C S hC hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (unfoldV_closed C)]
      exact .unfoldN C S hC (deadP_insert hd Γa hΓ)
  | effSub hNU hle _ ih => intro Γa Γb hΓ; exact .effSub hNU hle (ih Γa Γb hΓ)
  | effPerform hNU hf hna _ ih => intro Γa Γb hΓ; exact .effPerform hNU hf hna (ih Γa Γb hΓ)
  | effRaise hf ha hdr _ ih => intro Γa Γb hΓ; exact .effRaise hf ha hdr (ih Γa Γb hΓ)
  | effLet hNU hs hW hU _ _ ihM ihN =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ihM Γa₁ Γb₁ rfl
      have eN := ihN (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eM; rw [List.length_cons, h₂] at eN
      exact .effLet hNU hs' (fun hw => live_insert hd (P := fun s => s.ty.Drop) (hW hw))
        (fun hu => live_insert hd (hU hu)) eM eN
  | effThen hNU hs hNZ hUq hU _ _ _ ihM ihN ihD =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ihM Γa₁ Γb₁ rfl
      have eN := ihN (_ :: Γa₂) Γb₂ rfl
      have eD := ihD (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eM; rw [List.length_cons, h₂] at eN eD
      exact .effThen hNU hs' hNZ hUq (fun hu => live_insert hd (hU hu)) eM eN eD
  | effHandle hNU hs hs₁ hr hc hn0 hnS hlen _ ih =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      obtain ⟨Γar, Γbr, Γac, Γbc, rfl, rfl, hr₁, hc₁, hs₁'⟩ := splitP_insert hd Γa₁ hs₁
      have e' := ih Γa₂ Γb₂ rfl
      have hr' := soloP_insert hd Γar hr
      have hc' := soloP_insert hd Γac hc
      rw [h₂] at e'; rw [hr₁, h₁] at hr'; rw [hc₁, h₁] at hc'
      rw [hndTerm_shift]
      exact .effHandle hNU hs' hs₁' hr' hc' hn0 hnS hlen e'

/-! ### Dead slots at the end of a context -/

section AppendDead

theorem splitP_dead_self (hd : Ctx.Dead Γd) : Ctx.SplitP Γd Γd Γd := by
  induction hd with
  | nil => exact .nil
  | cons _ ih => exact .dead ih

theorem splitP_append_dead (hd : Ctx.Dead Γd) {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) :
    Ctx.SplitP (Γ ++ Γd) (Γ₁ ++ Γd) (Γ₂ ++ Γd) := by
  induction h with
  | nil => exact splitP_dead_self hd
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | dead _ ih => exact .dead ih
  | dup hT _ ih => exact .dup hT ih

theorem deadP_append_dead (hd : Ctx.Dead Γd) {Γ : Ctx VTy} (h : Ctx.DeadP Γ) :
    Ctx.DeadP (Γ ++ Γd) := by
  induction h with
  | nil => exact hd.toP
  | cons _ ih => exact .cons ih
  | drop hT _ ih => exact .drop hT ih

theorem soloP_append_dead (hd : Ctx.Dead Γd) {Γ : Ctx VTy} {i : Nat} {A : VTy}
    (h : Ctx.SoloP Γ i A) : Ctx.SoloP (Γ ++ Γd) i A := by
  induction h with
  | here h => exact .here (deadP_append_dead hd h)
  | there _ ih => exact .there ih
  | skip hS _ ih => exact .skip hS ih

theorem live_append_dead (hd : Ctx.Dead Γd) {Γ : Ctx VTy} {P : Slot VTy → Prop}
    (h : ∀ s ∈ Γ, s.live = true → P s) : ∀ s ∈ Γ ++ Γd, s.live = true → P s := by
  intro s hs hl
  rcases List.mem_append.mp hs with hs | hs
  · exact h s hs hl
  · rw [dead_not_live hd s hs] at hl; cases hl

/-- **Dead slots appended to a context**: a derivation at `Γ` is one at `Γ ++ Γd`, on the same
term, since no index below `Γ`'s length moves. -/
theorem CDerivesNU.append_dead (hd : Ctx.Dead Γd) {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : CDerivesNU Δ (Γ ++ Γd) e j := by
  induction h with
  | var hs => exact .var (soloP_append_dead hd hs)
  | unitI h => exact .unitI (deadP_append_dead hd h)
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI (splitP_append_dead hd hs) ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | thunkF _ ih => exact .thunkF ih
  | thunkV hC _ ih => exact .thunkV hC ih
  | ret _ ih => exact .ret ih
  | bind hs _ _ ihM ihN => exact .bind (splitP_append_dead hd hs) ihM ihN
  | force h => exact .force (soloP_append_dead hd h)
  | lam _ ih => exact .lam ih
  | app hs _ hx ih => exact .app (splitP_append_dead hd hs) ih (soloP_append_dead hd hx)
  | withI _ _ ihM ihN => exact .withI ihM ihN
  | proj₁ _ ih => exact .proj₁ ih
  | proj₂ _ ih => exact .proj₂ ih
  | topI => exact .topI
  | unitE hs _ _ ihV ihM => exact .unitE (splitP_append_dead hd hs) ihV ihM
  | tensorE hs _ _ ihV ihM => exact .tensorE (splitP_append_dead hd hs) ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact .sumE (splitP_append_dead hd hs) ihV ih₁ ih₂
  | zeroE hs _ ihV => exact .zeroE (splitP_append_dead hd hs) ihV
  | allI hbx hΔx hΓx _ ih => exact .allI hbx hΔx (live_append_dead hd hΓx) ih
  | allE _ hlt ih => exact .allE ih hlt
  | bangThunkF hp _ ih => exact .bangThunkF (live_append_dead hd hp) ih
  | bangThunkV hp hC _ ih => exact .bangThunkV (live_append_dead hd hp) hC ih
  | bangE _ ih => exact .bangE ih
  | copyBang hΓ => exact .copyBang (deadP_append_dead hd hΓ)
  | forgetBang hΓ => exact .forgetBang (deadP_append_dead hd hΓ)
  | boxI _ hΓ ih => exact .boxI ih ⟨hΓ.1, live_append_dead hd hΓ.2⟩
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | alloc hΓ => exact .alloc (deadP_append_dead hd hΓ)
  | free hΓ => exact .free (deadP_append_dead hd hΓ)
  | swap hΓ => exact .swap (deadP_append_dead hd hΓ)
  | copy hΓ => exact .copy (deadP_append_dead hd hΓ)
  | forgetImm hΓ => exact .forgetImm (deadP_append_dead hd hΓ)
  | forgetMut hΓ => exact .forgetMut (deadP_append_dead hd hΓ)
  | forgetUnk hΓ => exact .forgetUnk (deadP_append_dead hd hΓ)
  | lit c hΓ => exact .lit c (deadP_append_dead hd hΓ)
  | hostOp op hΓ => exact .hostOp op (deadP_append_dead hd hΓ)
  | arrNew A hΓ => exact .arrNew A (deadP_append_dead hd hΓ)
  | arrFree A hΓ => exact .arrFree A (deadP_append_dead hd hΓ)
  | arrSize A hΓ => exact .arrSize A (deadP_append_dead hd hΓ)
  | arrReplace A hΓ => exact .arrReplace A (deadP_append_dead hd hΓ)
  | arrLen a A hΓ => exact .arrLen a A (deadP_append_dead hd hΓ)
  | arrGet a A hΓ => exact .arrGet a A (deadP_append_dead hd hΓ)
  | arrCopy a A hΓ => exact .arrCopy a A (deadP_append_dead hd hΓ)
  | arrForget a A hΓ => exact .arrForget a A (deadP_append_dead hd hΓ)
  | countFold S hΓ => exact .countFold S (deadP_append_dead hd hΓ)
  | countTry S E hΓ => exact .countTry S E (deadP_append_dead hd hΓ)
  | boundedFix A C hΓ => exact .boundedFix A C (deadP_append_dead hd hΓ)
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ =>
      exact .sliceBorrowM x (deadP_append_dead hd hΓ) hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ =>
      exact .sliceBorrowI x (deadP_append_dead hd hΓ) hsc hA hB hf₁ hf₂
  | sliceGetM a A hΓ => exact .sliceGetM a A (deadP_append_dead hd hΓ)
  | sliceLenM a A hΓ => exact .sliceLenM a A (deadP_append_dead hd hΓ)
  | sliceSplitI a A hΓ => exact .sliceSplitI a A (deadP_append_dead hd hΓ)
  | sliceSplitM a A hΓ => exact .sliceSplitM a A (deadP_append_dead hd hΓ)
  | sliceEmptyI a A hΓ => exact .sliceEmptyI a A (deadP_append_dead hd hΓ)
  | sliceEmptyM a A hΓ => exact .sliceEmptyM a A (deadP_append_dead hd hΓ)
  | sliceReplaceM a A hΓ => exact .sliceReplaceM a A (deadP_append_dead hd hΓ)
  | sliceSwapM a A hΓ => exact .sliceSwapM a A (deadP_append_dead hd hΓ)
  | withbor1 x hΓ hx hsc hf₁ hf₂ => exact .withbor1 x (deadP_append_dead hd hΓ) hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ =>
      exact .withbor2 x (deadP_append_dead hd hΓ) hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact .withbor3 x (deadP_append_dead hd hΓ) hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact .withload x (deadP_append_dead hd hΓ) hx hf₁ hf₂
  | withswap hΓ => exact .withswap (deadP_append_dead hd hΓ)
  | withbor1U x hΓ hx hsc hf₁ hf₂ hS hdc _ ihd =>
      exact .withbor1U x (deadP_append_dead hd hΓ) hx hsc hf₁ hf₂ hS hdc ihd
  | withbor2U x hΓ hx hside hf₁ hf₂ hS hdc _ ihd =>
      exact .withbor2U x (deadP_append_dead hd hΓ) hx hside hf₁ hf₂ hS hdc ihd
  | withbor3U x hΓ hx hf₁ hf₂ hS hdc _ ihd =>
      exact .withbor3U x (deadP_append_dead hd hΓ) hx hf₁ hf₂ hS hdc ihd
  | withloadU x hΓ hx hf₁ hf₂ hS => exact .withloadU x (deadP_append_dead hd hΓ) hx hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact .sliceBorrowMU x (deadP_append_dead hd hΓ) hA hB hf₁ hf₂ hS hdc ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact .sliceBorrowIU x (deadP_append_dead hd hΓ) hsc hA hB hf₁ hf₂ hS hdc ihd
  | lolliE hs _ _ iha ihf => exact .lolliE (splitP_append_dead hd hs) iha ihf
  | allEV _ hlt ih => exact .allEV ih hlt
  | ofRet _ ih => exact .ofRet ih
  | roll hA hc _ ih => exact .roll hA hc ih
  | unroll _ ih => exact .unroll ih
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      exact .foldImm F y c R (deadP_append_dead hd hΓ) hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R (deadP_append_dead hd hΓ) hF hG
  | foldReuse F R hΓ hF hG => exact .foldReuse F R (deadP_append_dead hd hΓ) hF hG
  | nuIn hC _ ih => exact .nuIn hC ih
  | nuOut hC _ ih => exact .nuOut hC ih
  | unfoldN C S hC hΓ => exact .unfoldN C S hC (deadP_append_dead hd hΓ)
  | effSub hNU hle _ ih => exact .effSub hNU hle ih
  | effPerform hNU hf hna _ ih => exact .effPerform hNU hf hna ih
  | effRaise hf ha hdr _ ih => exact .effRaise hf ha hdr ih
  | effLet hNU hs hW hU _ _ ihM ihN =>
      exact .effLet hNU (splitP_append_dead hd hs)
        (fun hw => live_append_dead hd (P := fun s => s.ty.Drop) (hW hw))
        (fun hu => live_append_dead hd (hU hu)) ihM ihN
  | effThen hNU hs hNZ hUq hU _ _ _ ihM ihN ihD =>
      exact .effThen hNU (splitP_append_dead hd hs) hNZ hUq
        (fun hu => live_append_dead hd (hU hu)) ihM ihN ihD
  | effHandle hNU hs hs₁ hr hc hn0 hnS hlen _ ih =>
      exact .effHandle hNU (splitP_append_dead hd hs) (splitP_append_dead hd hs₁)
        (soloP_append_dead hd hr) (soloP_append_dead hd hc) hn0 hnS hlen ih

end AppendDead

/-- A consumed context splits into itself twice: each live slot is persistent. -/
theorem deadP_selfSplit : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ → Ctx.SplitP Γ Γ Γ
  | _, .nil => .nil
  | _, .cons h => .dead (deadP_selfSplit h)
  | _, .drop hT h => .dup hT (deadP_selfSplit h)

/-- A consumed context splits into itself and its killed copy (`kill`, `Core/Records.lean`). -/
theorem deadP_splitKill : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ → Ctx.SplitP Γ Γ (kill Γ)
  | _, .nil => .nil
  | _, .cons h => .dead (deadP_splitKill h)
  | _, .drop _ h => .left (deadP_splitKill h)

/-- `⊓Δ` does not mention a variable `Δ` does not bind. -/
theorem meetOfDomL_not_mentions {x : LifeVar} : ∀ t : List (LifeVar × Lifetime.Life),
    Lifetime.assocFind x t = none → (Lifetime.meetOfDomL t).mentions x = false
  | [], _ => rfl
  | (y, u) :: t, h => by
      simp only [Lifetime.assocFind] at h
      split_ifs at h with hy
      simp [Lifetime.meetOfDomL, Lifetime.Life.mentions, meetOfDomL_not_mentions t h, Ne.symm hy]

end Targets

end
