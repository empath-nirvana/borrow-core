import Core.Weaken
import Targets.Restricted.CoreLaws

/-!
# Targets — I4.a at tier 1 (DESIGN §9 item 14)

`i4a_tier1 : I4a tier1 admClosedOp .abortive`: the borrow form `ansRun d s₀ body` of a typed
answering body is typed by Core's rules at every row a lend may span under `admClosedOp` that is
abortive.  The derivation: `alloc` the cell; the callback `Λ. λm. body` by `∀I` and `λ`; the
unwinding borrow `withbor2U`; the call `w c f` at the row by `[let]`; `free` the cell.  `[prog]`

The callback holds `body` under the `Λ`'s slot and the cell, so its derivation is weakened by two
dead slots inserted after `m`: `CDerives.insert_dead`, the inner-position form of Core's
`CDerives.append_dead` (`Core/Weaken.lean`), which reuses its `dead_not_live`.
-/

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free')

/-! ### Indices and terms under an insertion -/

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

/-! ### Contexts under an insertion of dead slots -/

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

/-! ### Weakening by dead slots at an inner position -/

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

/-! ### Consumed contexts -/

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

/-! ### I4.a at tier 1 -/

/-- **`I4a tier1 admClosedOp .abortive`.** -/
theorem i4a_tier1 : I4a tier1 admClosedOp .abortive := by
  intro impl Δ Γ x S d s₀ body B _ hΓ hx hΔx hΓx hxS hxB hside hspan hcls hdc hs₀ hd hbody η hη
  set A := impl.S with hA
  set bnd := Δ.meetOfDom with hbnd
  have hs₀' : CDerives Δ Γ s₀ (.val A) := hs₀ η hη
  have hd' : CDerives Δ Γ d (.val (.lolli (.ref A) .unit)) := hd η hη
  have hbody' : CDerives (Δ.extend x bnd) (⟨.mut (.var x) A, true⟩ :: Γ) body
      (.comp (CTy.effOf S (.box (.var x) B))) := hbody η hη
  have hS : S.Unwind x := rowSpan_abortive_iff_unwind.mp ⟨hspan, hcls⟩
  have hsplit := deadP_selfSplit hΓ
  -- the callback `Λ. λm. body`, under the cell
  let cbT : VTy := cbUTy x bnd (.mut (.var x) A) B S
  have hcb : CDerives Δ (⟨.ref A, false⟩ :: Γ) (.val (.lam (.val (.lam (body.shift 2 1)))))
      (.val cbT) := by
    have hdd : Ctx.Dead [(⟨.unit, false⟩ : Slot VTy), ⟨.ref A, false⟩] := .cons (.cons .nil)
    have hb := CDerives.insert_dead hdd hbody' [⟨.mut (.var x) A, true⟩] Γ rfl
    refine .thunkV rfl (.allI (S := .unit) ?_ ?_ ?_ (.lam hb))
    · exact meetOfDomL_not_mentions _ hx
    · exact hΔx
    · intro s hs hl
      rcases List.mem_cons.mp hs with rfl | hs
      · cases hl
      · exact hΓx s hs hl
  -- the unwinding borrow `withborU d`
  let wT : VTy := withbor2UTy x bnd A B S
  have hw : CDerives Δ (⟨cbT, false⟩ :: ⟨.ref A, false⟩ :: Γ) (withborUE d) (.val wT) := by
    have hdd : Ctx.Dead [(⟨cbT, false⟩ : Slot VTy), ⟨.ref A, false⟩] := .cons (.cons .nil)
    have hd2 := CDerives.insert_dead hdd hd' [] Γ rfl
    rw [shift_closed0 hdc] at hd2
    exact .withbor2U x (.cons (.cons hΓ)) hx hside hxS hxB hS hdc hd2
  -- after the call: free the cell, answer the result
  have hK : Ctx.Dead (kill Γ) := kill_dead Γ
  let Γ₂ : Ctx VTy := ⟨wT, false⟩ :: ⟨cbT, false⟩ :: ⟨.ref A, false⟩ :: kill Γ
  have hΓ₂ : Ctx.Dead Γ₂ := .cons (.cons (.cons hK))
  have hR : Ctx.Dead ((⟨.tensor (.ref A) B, false⟩ : Slot VTy) :: Γ₂) := .cons hΓ₂
  have hpair : CDerives Δ (⟨B, true⟩ :: ⟨.ref A, true⟩ :: ⟨.tensor (.ref A) B, false⟩ :: Γ₂)
      (.pair (.app free' (.var 1)) (.var 0)) (.comp (CTy.effOf S (.tensor A B))) := by
    refine .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h) (.ret (.tensorI
      (.right (.left (deadSplit hR))) ?_ (.var (.here (.cons hR.toP)))))
    exact .lolliE (.dead (.left (deadSplit hR))) (.var (.there (.here hR.toP)))
      (.free (.cons (.cons hR.toP)))
  have hN₄ : CDerives Δ (⟨.tensor (.ref A) B, true⟩ :: Γ₂)
      (.letpair (.var 0) (.pair (.app free' (.var 1)) (.var 0)))
      (.comp (CTy.effOf S (.tensor A B))) :=
    .tensorE (.left (deadSplit hΓ₂)) (.var (.here hΓ₂.toP)) hpair
  -- the call `w c f`
  have hM₃ : CDerives Δ (⟨wT, true⟩ :: ⟨cbT, true⟩ :: ⟨.ref A, true⟩ :: Γ)
      (.app (.app (.var 0) (.var 2)) (.var 1)) (.comp (CTy.effOf S (.tensor (.ref A) B))) := by
    have hf : CDerives Δ (⟨wT, true⟩ :: ⟨cbT, false⟩ :: ⟨.ref A, false⟩ :: Γ) (.var 0)
        (.comp (.arr (.ref A) (.arr cbT (CTy.effOf S (.tensor (.ref A) B))))) :=
      .force (C := .arr (.ref A) (.arr cbT (CTy.effOf S (.tensor (.ref A) B))))
        (.here (.cons (.cons hΓ)))
    have hfc : CDerives Δ (⟨wT, true⟩ :: ⟨cbT, false⟩ :: ⟨.ref A, true⟩ :: Γ)
        (.app (.var 0) (.var 2)) (.comp (.arr cbT (CTy.effOf S (.tensor (.ref A) B)))) :=
      .app (.left (.dead (.right (deadP_splitKill hΓ)))) hf (.there (.there (.here hK.toP)))
    exact .app (.left (.right (.left (deadP_splitKill hΓ)))) hfc (.there (.here (.cons hK.toP)))
  have hN₃ : CDerives Δ (⟨wT, true⟩ :: ⟨cbT, true⟩ :: ⟨.ref A, true⟩ :: Γ)
      (.app (.val (.lam (.letpair (.var 0) (.pair (.app free' (.var 1)) (.var 0)))))
        (.app (.app (.var 0) (.var 2)) (.var 1)))
      (.comp (CTy.effOf S (.tensor A B))) :=
    .effLet (.left (.left (.left (deadP_splitKill hΓ))))
      (fun _ s hs hl => by rw [dead_not_live hΓ₂ s hs] at hl; cases hl)
      (fun _ s hs hl => by rw [dead_not_live hΓ₂ s hs] at hl; cases hl) hM₃ hN₄
  -- the three bindings
  have hN₂ := CDerives.bind (.right (.right hsplit)) (.ret hw) hN₃
  have hN₁ := CDerives.bind (.right hsplit) (.ret hcb) hN₂
  exact CDerives.bind hsplit (.ret (.lolliE hsplit hs₀' (.alloc hΓ))) hN₁

end Targets
