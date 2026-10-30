import Core.Weaken
import Core.Tied

/-!
# Core — weakening by dead slots inside a context  `[spec §3, §24]`

A derivation at `Γa ++ Γb` is one at `Γa ++ Γd ++ Γb` when every slot of `Γd` is consumed, the
term's variables past `Γa` shifted past `Γd` (`CDerives.insert_dead`; `CDerivesAt.insert_dead` for
a tied derivation).  Every rule's context premise holds of the context with `Γd` inserted
(`deadP_insert`, `splitP_insert`, `soloP_insert`, `live_insert`, `valFormIn_insert`), and the terms
the rules build commute with the shift (`var_shift`, `forceE_var_shift`, `absurdE_shift`,
`withPair_shift`, `shift_hndExpr`).  `[let-poly]`'s premise term commutes with a shift above the
filled variable (`fill_shift`), so that case is the rule again.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Shifting the terms the rules build -/

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

/-- **Filling a variable commutes with a shift above it**: `[let-poly]`'s premise term, shifted
past slots inserted above the filled variable, is the premise term of the shifted body. -/
theorem fill_shift {V : Val} (hV : closedAt 0 V.1 = true) (d : Nat) :
    ∀ (N : Expr) (j c : Nat), j ≤ c →
      ((N.shift d (c + 1)).subst j V).shift 1 j = ((N.subst j V).shift 1 j).shift d (c + 1)
  | .var i, j, c, hjc => by
      have hs : ∀ (d' c' : Nat), V.1.shift d' c' = V.1 :=
        fun d' c' => shift_closedAt V.1 d' hV (Nat.zero_le c')
      by_cases h1 : i < c + 1
      · by_cases h2 : i = j
        · subst h2
          simp only [Expr.shift, if_pos h1, Expr.subst]
          rw [if_pos trivial, hs, hs]
        · by_cases h3 : i > j
          · have h4 : ¬ (i - 1 < j) := by omega
            have h5 : i - 1 + 1 < c + 1 := by omega
            simp only [Expr.shift, if_pos h1, Expr.subst, if_neg h2, if_pos h3, if_neg h4,
              if_pos h5]
          · have h4 : i < j := by omega
            simp only [Expr.shift, if_pos h1, Expr.subst, if_neg h2, if_neg h3, if_pos h4]
      · have h2 : ¬ (i + d = j) := by omega
        have h3 : i + d > j := by omega
        have h4 : ¬ (i = j) := by omega
        have h5 : i > j := by omega
        have h6 : ¬ (i + d - 1 < j) := by omega
        have h7 : ¬ (i - 1 < j) := by omega
        have h8 : ¬ (i - 1 + 1 < c + 1) := by omega
        simp only [Expr.shift, if_neg h1, Expr.subst, if_neg h2, if_pos h3, if_neg h4, if_pos h5,
          if_neg h6, if_neg h7, if_neg h8]
        congr 1; omega
  | .unit, _, _, _ => rfl
  | .pair a b, j, c, h => by
      simp only [Expr.shift, Expr.subst, fill_shift hV d a j c h, fill_shift hV d b j c h]
  | .inj₁ a, j, c, h => by simp only [Expr.shift, Expr.subst, fill_shift hV d a j c h]
  | .inj₂ a, j, c, h => by simp only [Expr.shift, Expr.subst, fill_shift hV d a j c h]
  | .lam b, j, c, h => by
      simp only [Expr.shift, Expr.subst, val_shift_closed hV,
        fill_shift hV d b (j + 1) (c + 1) (by omega)]
  | .loc _, _, _, _ => rfl
  | .prim _, _, _, _ => rfl
  | .seq a b, j, c, h => by
      simp only [Expr.shift, Expr.subst, fill_shift hV d a j c h, fill_shift hV d b j c h]
  | .letpair a b, j, c, h => by
      simp only [Expr.shift, Expr.subst, val_shift_closed hV, fill_shift hV d a j c h,
        fill_shift hV d b (j + 2) (c + 2) (by omega)]
  | .case a b e, j, c, h => by
      simp only [Expr.shift, Expr.subst, val_shift_closed hV, fill_shift hV d a j c h,
        fill_shift hV d b (j + 1) (c + 1) (by omega), fill_shift hV d e (j + 1) (c + 1) (by omega)]
  | .app f a, j, c, h => by
      simp only [Expr.shift, Expr.subst, fill_shift hV d f j c h, fill_shift hV d a j c h]

/-! ### The context premises with consumed slots inserted -/

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

/-- A value form over `Γa ++ Γb` is one over `Γa ++ Γd ++ Γb`, its variables past `Γa` shifted. -/
theorem valFormIn_insert (Γa : Ctx VTy) {Γb : Ctx VTy} {H : Expr} (h : H.ValFormIn (Γa ++ Γb)) :
    (H.shift Γd.length Γa.length).ValFormIn (Γa ++ Γd ++ Γb) := by
  induction h with
  | @var i s hs hl =>
      rw [var_shift]
      refine .var (s := s) ?_ hl
      unfold sIdx
      by_cases hi : i < Γa.length
      · rw [if_pos hi, List.append_assoc, List.getElem?_append_left hi]
        rwa [List.getElem?_append_left hi] at hs
      · rw [if_neg hi, List.getElem?_append_right (by simp; omega)]
        rw [List.getElem?_append_right (by omega)] at hs
        simp only [List.length_append]
        rw [show i + Γd.length - (Γa.length + Γd.length) = i - Γa.length by omega]
        exact hs
  | val v => exact .val (v.shift Γd.length Γa.length)
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih

theorem live_insert (hd : Ctx.Dead Γd) {P : Slot VTy → Prop} {Γa Γb : Ctx VTy}
    (h : ∀ s ∈ Γa ++ Γb, s.live = true → P s) : ∀ s ∈ Γa ++ Γd ++ Γb, s.live = true → P s := by
  intro s hs hl
  simp only [List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · exact h s (List.mem_append_left _ hs) hl
  · rw [dead_not_live hd s hs] at hl; cases hl
  · exact h s (List.mem_append_right _ hs) hl

/-! ### Weakening -/

/-- **Weakening by consumed slots inside a context**: a derivation at `Γa ++ Γb` is one at
`Γa ++ Γd ++ Γb` for dead `Γd`, the term's variables past `Γa` shifted past `Γd`.  `[spec §3]` -/
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
  | lamDead _ ih =>
      intro Γa Γb hΓ; subst hΓ
      have e' := ih (_ :: Γa) Γb rfl
      rw [List.length_cons] at e'
      exact .lamDead e'
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
      rw [shift_closed0 (e := BoCa.copy) (by rfl)]; exact .copyBang (deadP_insert hd Γa hΓ)
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
      rw [shift_closed0 (e := BoCa.swap) (by rfl)]; exact .swap (deadP_insert hd Γa hΓ)
  | copy hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.copy) (by rfl)]; exact .copy (deadP_insert hd Γa hΓ)
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
  | iterate S St B R hS hΓ =>
      intro Γa Γb hΓ'; subst hΓ'; exact .iterate S St B R hS (deadP_insert hd Γa hΓ)
  | divFuel S A hS hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 divFuelV_closed]
      exact .divFuel S A hS (deadP_insert hd Γa hΓ)
  | reify S B R res hS hcl hres hΓ _ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (reifyV_closed hcl)]
      exact .reify S B R res hS hcl hres (deadP_insert hd Γa hΓ)
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
  | arrEmpty A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := emptyFamV.1) (by rfl)]; exact .arrEmpty A (deadP_insert hd Γa hΓ)
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
  | foldOwnG B₀ Rs hΓ hB =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (FoldP.foldOwnGV_closed B₀)]
      exact .foldOwnG B₀ Rs (deadP_insert hd Γa hΓ) hB
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
      exact .effLet hs' (fun hw => live_insert hd (P := fun s => s.ty.OwnFree) (hW hw))
        (fun hu => live_insert hd (hU hu)) eM eN
  | effThen hs hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ihM Γa₁ Γb₁ rfl
      have eN := ihN (_ :: Γa₂) Γb₂ rfl
      have eD := ihD (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eM; rw [List.length_cons, h₂] at eN eD
      exact .effThen hs' hNZ hUq (fun hu => live_insert hd (hU hu)) hMS hDS hfin hP hSD eM eN eD
  | effHandleV hs hdd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have ec := ihc Γa₁ Γb₁ rfl
      have ee := ihe Γa₂ Γb₂ rfl
      have hH' := valFormIn_insert (Γd := Γd) Γa₁ hH
      rw [h₁] at ec hH'; rw [h₂] at ee
      rw [shift_hndExpr]
      exact .effHandleV hs' (deadP_insert hd Γa₁ hdd) hH' ec hn0 hnS hlen hdv ee
  | effHandleVB hs hdd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have ec := ihc Γa₁ Γb₁ rfl
      have ee := ihe Γa₂ Γb₂ rfl
      have hH' := valFormIn_insert (Γd := Γd) Γa₁ hH
      rw [h₁] at ec hH'; rw [h₂] at ee
      rw [shift_hndExpr]
      exact .effHandleVB hs' (deadP_insert hd Γa₁ hdd) hH' ec hn0 hnS hlen hdv ee
        ⟨hΓd.1, live_insert hd hΓd.2⟩ hSd
  | effHandleT hs hdd hHr hHc _ hn0 hnd hnS hlen hSN hLin _ ihc ihe =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have ec := ihc Γa₁ Γb₁ rfl
      have ee := ihe Γa₂ Γb₂ rfl
      have hHr' := valFormIn_insert (Γd := Γd) Γa₁ hHr
      have hHc' := valFormIn_insert (Γd := Γd) Γa₁ hHc
      rw [h₁] at ec hHr' hHc'; rw [h₂] at ee
      rw [shift_hndExpr]
      simp only [Expr.shift, tailTuple_shift]
      exact .effHandleT hs' (deadP_insert hd Γa₁ hdd) hHr' hHc' ec hn0 hnd hnS hlen hSN hLin ee
  | effHandleL hs hdd hHr hHw hHn _ hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin _ ihc ihe =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have ec := ihc Γa₁ Γb₁ rfl
      have ee := ihe Γa₂ Γb₂ rfl
      have hHr' := valFormIn_insert (Γd := Γd) Γa₁ hHr
      have hHw' := valFormIn_insert (Γd := Γd) Γa₁ hHw
      have hHn' := valFormIn_insert (Γd := Γd) Γa₁ hHn
      rw [h₁] at ec hHr' hHw' hHn'; rw [h₂] at ee
      rw [shift_hndExpr]
      simp only [Expr.shift, lastTuple_shift]
      exact .effHandleL hs' (deadP_insert hd Γa₁ hdd) hHr' hHw' hHn' ec hn0 hnd hnS hlen hNZ hCancel
        hSW hSu hFin ee
  | @letPoly _ _ N _ _ b hcl hV _ _ ihN =>
      intro Γa Γb hΓ; subst hΓ
      have eN := ihN (⟨.unit, false⟩ :: Γa) Γb rfl
      rw [List.length_cons, ← fill_shift hcl Γd.length N 0 Γa.length (Nat.zero_le _)] at eN
      have hb : (Expr.lam b).shift Γd.length Γa.length = .lam b := shift_closed0 hcl _ _
      show CDerives _ _ (Expr.app (Expr.lam (N.shift _ (Γa.length + 1))) ((Expr.lam b).shift _ _)) _
      rw [hb]
      exact .letPoly b hcl hV eN

/-- **Weakening of a tied derivation** by consumed slots inside its context, as
`CDerives.insert_dead`: the tie is on rows, which the shift leaves alone.  `[spec §3, §19]` -/
theorem CDerivesAt.insert_dead {Ξ : EffCtx} (hd : Ctx.Dead Γd) {Δ : LifeCtx} {Γ₀ : Ctx VTy}
    {e : Expr} {j : Jdg} (h : CDerivesAt Ξ Δ Γ₀ e j) : ∀ (Γa Γb : Ctx VTy), Γ₀ = Γa ++ Γb →
    CDerivesAt Ξ Δ (Γa ++ Γd ++ Γb) (e.shift Γd.length Γa.length) j := by
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
  | lamDead _ ih =>
      intro Γa Γb hΓ; subst hΓ
      have e' := ih (_ :: Γa) Γb rfl
      rw [List.length_cons] at e'
      exact .lamDead e'
  | app hs _ hx ih =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ih Γa₁ Γb₁ rfl
      have hx' := soloP_insert hd Γa₂ hx
      rw [h₁] at eM; rw [h₂] at hx'
      show CDerivesAt _ _ _ (.app _ ((Expr.var _).shift _ _)) _
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
      rw [shift_closed0 (e := BoCa.swap) (by rfl)]; exact .swap (deadP_insert hd Γa hΓ)
  | copy hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := BoCa.copy) (by rfl)]; exact .copy (deadP_insert hd Γa hΓ)
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
  | iterate S St B R hAt hS hΓ =>
      intro Γa Γb hΓ'; subst hΓ'; exact .iterate S St B R hAt hS (deadP_insert hd Γa hΓ)
  | divFuel S A hAt hS hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 divFuelV_closed]
      exact .divFuel S A hAt hS (deadP_insert hd Γa hΓ)
  | reify S B R res hAt hS hcl hres hΓ _ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (reifyV_closed hcl)]
      exact .reify S B R res hAt hS hcl hres (deadP_insert hd Γa hΓ)
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
  | arrEmpty A hΓ =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (e := emptyFamV.1) (by rfl)]; exact .arrEmpty A (deadP_insert hd Γa hΓ)
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
  | foldOwnG B₀ Rs hΓ hB =>
      intro Γa Γb hΓ'; subst hΓ'
      rw [shift_closed0 (FoldP.foldOwnGV_closed B₀)]
      exact .foldOwnG B₀ Rs (deadP_insert hd Γa hΓ) hB
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
  | effPerform hAt hf hna _ ih => intro Γa Γb hΓ; exact .effPerform hAt hf hna (ih Γa Γb hΓ)
  | effRaise hAt hf ha hdr _ ih => intro Γa Γb hΓ; exact .effRaise hAt hf ha hdr (ih Γa Γb hΓ)
  | effLet hs hW hU _ _ ihM ihN =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ihM Γa₁ Γb₁ rfl
      have eN := ihN (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eM; rw [List.length_cons, h₂] at eN
      exact .effLet hs' (fun hw => live_insert hd (P := fun s => s.ty.OwnFree) (hW hw))
        (fun hu => live_insert hd (hU hu)) eM eN
  | effThen hs hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have eM := ihM Γa₁ Γb₁ rfl
      have eN := ihN (_ :: Γa₂) Γb₂ rfl
      have eD := ihD (_ :: Γa₂) Γb₂ rfl
      rw [h₁] at eM; rw [List.length_cons, h₂] at eN eD
      exact .effThen hs' hNZ hUq (fun hu => live_insert hd (hU hu)) hMS hDS hfin hP hSD eM eN eD
  | effHandleV hAt hs hdd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have ec := ihc Γa₁ Γb₁ rfl
      have ee := ihe Γa₂ Γb₂ rfl
      have hH' := valFormIn_insert (Γd := Γd) Γa₁ hH
      rw [h₁] at ec hH'; rw [h₂] at ee
      rw [shift_hndExpr]
      exact .effHandleV hAt hs' (deadP_insert hd Γa₁ hdd) hH' ec hn0 hnS hlen hdv ee
  | effHandleVB hAt hs hdd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have ec := ihc Γa₁ Γb₁ rfl
      have ee := ihe Γa₂ Γb₂ rfl
      have hH' := valFormIn_insert (Γd := Γd) Γa₁ hH
      rw [h₁] at ec hH'; rw [h₂] at ee
      rw [shift_hndExpr]
      exact .effHandleVB hAt hs' (deadP_insert hd Γa₁ hdd) hH' ec hn0 hnS hlen hdv ee
        ⟨hΓd.1, live_insert hd hΓd.2⟩ hSd
  | effHandleT hAt hs hdd hHr hHc _ hn0 hnd hnS hlen hSN hLin _ ihc ihe =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have ec := ihc Γa₁ Γb₁ rfl
      have ee := ihe Γa₂ Γb₂ rfl
      have hHr' := valFormIn_insert (Γd := Γd) Γa₁ hHr
      have hHc' := valFormIn_insert (Γd := Γd) Γa₁ hHc
      rw [h₁] at ec hHr' hHc'; rw [h₂] at ee
      rw [shift_hndExpr]
      simp only [Expr.shift, tailTuple_shift]
      exact .effHandleT hAt hs' (deadP_insert hd Γa₁ hdd) hHr' hHc' ec hn0 hnd hnS hlen hSN hLin
        ee
  | effHandleL hAt hs hdd hHr hHw hHn _ hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin _ ihc ihe =>
      intro Γa Γb hΓ; subst hΓ
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, rfl, rfl, h₁, h₂, hs'⟩ := splitP_insert hd Γa hs
      have ec := ihc Γa₁ Γb₁ rfl
      have ee := ihe Γa₂ Γb₂ rfl
      have hHr' := valFormIn_insert (Γd := Γd) Γa₁ hHr
      have hHw' := valFormIn_insert (Γd := Γd) Γa₁ hHw
      have hHn' := valFormIn_insert (Γd := Γd) Γa₁ hHn
      rw [h₁] at ec hHr' hHw' hHn'; rw [h₂] at ee
      rw [shift_hndExpr]
      simp only [Expr.shift, lastTuple_shift]
      exact .effHandleL hAt hs' (deadP_insert hd Γa₁ hdd) hHr' hHw' hHn' ec hn0 hnd hnS hlen hNZ
        hCancel hSW hSu hFin ee
  | @letPoly _ _ N _ _ b hcl hV _ _ ihN =>
      intro Γa Γb hΓ; subst hΓ
      have eN := ihN (⟨.unit, false⟩ :: Γa) Γb rfl
      rw [List.length_cons, ← fill_shift hcl Γd.length N 0 Γa.length (Nat.zero_le _)] at eN
      have hb : (Expr.lam b).shift Γd.length Γa.length = .lam b := shift_closed0 hcl _ _
      show CDerivesAt _ _ _
        (Expr.app (Expr.lam (N.shift _ (Γa.length + 1))) ((Expr.lam b).shift _ _)) _
      rw [hb]
      exact .letPoly b hcl hV eN

end BoCa.Fig16.LogRel.Core

end
