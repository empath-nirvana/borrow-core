import Frontend.Check.TDerives
import Core.InsertDead

/-!
# Frontend — Check — weakening a typed derivation  `[spec §3, §10]`

**The lemma a `use` node rests on.** A typed derivation at `Γa ++ Γb` is one at `Γa ++ Γp ++ Γb`
of the shifted term (`TExpr.shift`, `Frontend/Check/TShift.lean`), when every live slot of `Γp`
satisfies the term's absorption (`TExpr.absF`); and the shifted term's erasure is the erasure
shifted (`TDerivesP.weaken`, `TDerivesAt.weaken`). A `def`'s body is checked once, at the
persistent externs, and this places it at each use (`TTied.weaken`): the slots bound between the
externs and the use are `Γp`, its live ones those the enclosing rules give the use.

`Core`'s weakening lemmas insert dead slots only (`CDerives.insert_dead`, `CDerives.append_dead`).
A use may be given live ones: the checker lets a `def`'s body absorb an unused live slot of the
use's context wherever its rules can, as the slot's leaf drops it (a persistent slot at `DeadP`)
or `⟨⟩` takes it. The absorption is that set of slots, read off the typed term, so the use is
given exactly the slots its body's derivation takes.

The premises on the context are moved past the inserted slots by `deadP_ins`, `soloP_ins`,
`splitP_route` (a live inserted slot goes to the part whose absorption it satisfies) and `live_ins`
(a premise on every live slot: `Ctx.Banged`, `CtxOutlives`, `∀I`'s freshness, `Ctx.OwnFree`).
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx LifeVar)

/-- Every live slot of `Γ` is at a type `p` holds of. -/
def LiveP (p : VTy → Bool) (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → p s.ty = true

theorem LiveP.imp {p q : VTy → Bool} (hq : ∀ A, p A = true → q A = true) {Γ : Ctx VTy}
    (h : LiveP p Γ) : LiveP q Γ := fun s hs hl => hq _ (h s hs hl)

theorem LiveP.tail {p : VTy → Bool} {s : Slot VTy} {Γ : Ctx VTy} (h : LiveP p (s :: Γ)) :
    LiveP p Γ := fun s' hs hl => h s' (List.mem_cons_of_mem _ hs) hl

theorem LiveP.head {p : VTy → Bool} {A : VTy} {l : Bool} {Γ : Ctx VTy} (h : LiveP p (⟨A, l⟩ :: Γ))
    (hl : l = true) : p A = true := h _ List.mem_cons_self hl

/-- No slot live where nothing holds: a consumed context. -/
theorem LiveP.dead : ∀ {Γ : Ctx VTy}, LiveP (fun _ => false) Γ → BoCa.Ctx.Dead Γ
  | [], _ => .nil
  | ⟨A, l⟩ :: Γ, h => by
      cases l with
      | false => exact .cons (LiveP.dead h.tail)
      | true => exact absurd (h.head rfl) (by simp)

/-! ### The absorption, decomposed -/

theorem live_eval_atom {a : Atom} {f : AbsF} {Γ : Ctx VTy} (hf : some (AbsF.atom a) = some f)
    (h : LiveP f.eval Γ) : LiveP a.eval Γ := by
  cases hf; exact h.imp fun A hA => by rwa [AbsF.eval_atom] at hA

theorem live_eval_ff {f : AbsF} {Γ : Ctx VTy} (hf : some AbsF.ff = some f) (h : LiveP f.eval Γ) :
    BoCa.Ctx.Dead Γ := by
  cases hf; exact LiveP.dead (h.imp fun A hA => by rwa [AbsF.eval_ff] at hA)

theorem live_orO {a b : Option AbsF} {f : AbsF} {Γ : Ctx VTy} (hf : AbsF.orO a b = some f)
    (h : LiveP f.eval Γ) : ∃ f₁ f₂, a = some f₁ ∧ b = some f₂ ∧
      LiveP (fun A => f₁.eval A || f₂.eval A) Γ := by
  match a, b, hf with
  | some f₁, some f₂, hf =>
      cases hf
      exact ⟨f₁, f₂, rfl, rfl, h.imp fun A hA => by rwa [AbsF.eval_or] at hA⟩

theorem live_andO {a b : Option AbsF} {f : AbsF} {Γ : Ctx VTy} (hf : AbsF.andO a b = some f)
    (h : LiveP f.eval Γ) : ∃ f₁ f₂, a = some f₁ ∧ b = some f₂ ∧ LiveP f₁.eval Γ ∧
      LiveP f₂.eval Γ := by
  match a, b, hf with
  | some f₁, some f₂, hf =>
      cases hf
      refine ⟨f₁, f₂, rfl, rfl, h.imp fun A hA => ?_, h.imp fun A hA => ?_⟩ <;>
        simp only [AbsF.eval_and, Bool.and_eq_true] at hA
      · exact hA.1
      · exact hA.2

theorem live_withO {g : AbsF} {a : Option AbsF} {f : AbsF} {Γ : Ctx VTy}
    (hf : AbsF.withO g a = some f) (h : LiveP f.eval Γ) :
    ∃ f', a = some f' ∧ LiveP g.eval Γ ∧ LiveP f'.eval Γ := by
  match a, hf with
  | some f', hf =>
      cases hf
      refine ⟨f', rfl, h.imp fun A hA => ?_, h.imp fun A hA => ?_⟩ <;>
        simp only [AbsF.eval_and, Bool.and_eq_true] at hA
      · exact hA.1
      · exact hA.2

theorem live_atom {a : Atom} {Γ : Ctx VTy} (h : LiveP (AbsF.atom a).eval Γ) : LiveP a.eval Γ :=
  h.imp fun A hA => by rwa [AbsF.eval_atom] at hA

/-! ### The context premises with slots inserted -/

variable {Γp : Ctx VTy}

theorem deadP_prep (hp : LiveP VTy.persistent Γp) {Γ : Ctx VTy} (h : Ctx.DeadP Γ) :
    Ctx.DeadP (Γp ++ Γ) := by
  induction Γp with
  | nil => exact h
  | cons s Γp ih =>
      obtain ⟨A, l⟩ := s
      cases l with
      | false => exact .cons (ih hp.tail)
      | true => exact .drop (hp.head rfl) (ih hp.tail)

theorem deadP_ins (hp : LiveP VTy.persistent Γp) : ∀ (Γa : Ctx VTy) {Γb : Ctx VTy},
    Ctx.DeadP (Γa ++ Γb) → Ctx.DeadP (Γa ++ Γp ++ Γb)
  | [], _, h => deadP_prep hp h
  | _ :: Γa, _, h => by
      rw [List.cons_append] at h
      cases h with
      | cons h => exact .cons (deadP_ins hp Γa h)
      | drop hT h => exact .drop hT (deadP_ins hp Γa h)

theorem dead_ins (hp : BoCa.Ctx.Dead Γp) : ∀ (Γa : Ctx VTy) {Γb : Ctx VTy},
    BoCa.Ctx.Dead (Γa ++ Γb) → BoCa.Ctx.Dead (Γa ++ Γp ++ Γb)
  | [], _, h => by
      induction hp with
      | nil => exact h
      | cons _ ih => exact .cons ih
  | _ :: Γa, _, h => by
      rw [List.cons_append] at h
      cases h with
      | cons h => exact .cons (dead_ins hp Γa h)

theorem soloP_prep (hp : LiveP VTy.persistent Γp) {Γ : Ctx VTy} {i : Nat} {A : VTy}
    (h : Ctx.SoloP Γ i A) : Ctx.SoloP (Γp ++ Γ) (i + Γp.length) A := by
  induction Γp with
  | nil => exact h
  | cons s Γp ih =>
      obtain ⟨B, l⟩ := s
      rw [List.length_cons, ← Nat.add_assoc]
      cases l with
      | false => exact .there (ih hp.tail)
      | true => exact .skip (hp.head rfl) (ih hp.tail)

theorem soloP_ins (hp : LiveP VTy.persistent Γp) : ∀ (Γa : Ctx VTy) {Γb : Ctx VTy} {i : Nat}
    {A : VTy}, Ctx.SoloP (Γa ++ Γb) i A → Ctx.SoloP (Γa ++ Γp ++ Γb) (sIdx Γp.length Γa.length i) A
  | [], _, _, _, h => by
      rw [List.length_nil, sIdx_at_zero]; exact soloP_prep hp h
  | _ :: Γa, _, _, _, h => by
      rw [List.cons_append] at h
      cases h with
      | here h => rw [List.length_cons, sIdx_zero_succ]; exact .here (deadP_ins hp Γa h)
      | there h => rw [List.length_cons, sIdx_succ]; exact .there (soloP_ins hp Γa h)
      | skip hS h => rw [List.length_cons, sIdx_succ]; exact .skip hS (soloP_ins hp Γa h)

/-- The slots of `Γp` live where `p` holds, the others dead. -/
def routeL (p : VTy → Bool) (Γp : Ctx VTy) : Ctx VTy := Γp.map fun s => ⟨s.ty, s.live && p s.ty⟩

/-- The slots of `Γp` live where `p` fails, the others dead. -/
def routeR (p : VTy → Bool) (Γp : Ctx VTy) : Ctx VTy := Γp.map fun s => ⟨s.ty, s.live && !p s.ty⟩

/-- The routed slots go to one part each. -/
theorem route_masks (p : VTy → Bool) : ∀ (Γp : Ctx VTy),
    SplitMasks (routeL p Γp) (routeR p Γp) (List.replicate Γp.length false)
      (List.replicate Γp.length false)
  | [] => .nil
  | ⟨A, l⟩ :: Γp => by
      simp only [routeL, routeR, List.map_cons, List.length_cons, List.replicate_succ]
      exact .cons (by simp) (by simp) (fun h₁ h₂ => by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h₁ h₂; simp_all) (route_masks p Γp)

theorem splitP_prep (p : VTy → Bool) : ∀ (Γp : Ctx VTy) {Γ Γ₁ Γ₂ : Ctx VTy},
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.SplitP (Γp ++ Γ) (routeL p Γp ++ Γ₁) (routeR p Γp ++ Γ₂)
  | [], _, _, _, h => h
  | ⟨A, l⟩ :: Γp, _, _, _, h => by
      have ih := splitP_prep p Γp h
      simp only [routeL, routeR, List.map_cons, List.cons_append] at ih ⊢
      cases l <;> cases hA : p A <;> simp only [Bool.false_and, Bool.true_and, Bool.not_true,
        Bool.not_false]
      · exact .dead ih
      · exact .dead ih
      · exact .right ih
      · exact .left ih

/-- **A split with slots inserted**: each live inserted slot goes to the left part where `p₁`
holds, else to the right, where `p₂` holds. -/
theorem splitP_route {p₁ p₂ : VTy → Bool} (hp : LiveP (fun A => p₁ A || p₂ A) Γp) :
    ∀ (Γa : Ctx VTy) {Γb Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP (Γa ++ Γb) Γ₁ Γ₂ →
    ∃ Γa₁ Γb₁ Γa₂ Γb₂ Γp₁ Γp₂, Γ₁ = Γa₁ ++ Γb₁ ∧ Γ₂ = Γa₂ ++ Γb₂ ∧ Γa₁.length = Γa.length ∧
      Γa₂.length = Γa.length ∧ Γp₁.length = Γp.length ∧ Γp₂.length = Γp.length ∧ LiveP p₁ Γp₁ ∧
      LiveP p₂ Γp₂ ∧ Ctx.SplitP (Γa ++ Γp ++ Γb) (Γa₁ ++ Γp₁ ++ Γb₁) (Γa₂ ++ Γp₂ ++ Γb₂) ∧
      SplitMasks Γp₁ Γp₂ (List.replicate Γp.length false) (List.replicate Γp.length false)
  | [], _, Γ₁, Γ₂, h => by
      refine ⟨[], Γ₁, [], Γ₂, routeL p₁ Γp, routeR p₁ Γp, rfl, rfl, rfl, rfl, by simp [routeL],
        by simp [routeR], ?_, ?_, splitP_prep p₁ Γp h, route_masks p₁ Γp⟩
      · intro s hs hl
        obtain ⟨s', _, rfl⟩ := List.mem_map.mp hs
        simp only [Bool.and_eq_true] at hl
        exact hl.2
      · intro s hs hl
        obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hl
        have := hp s' hs' hl.1
        simpa [hl.2] using this
  | _ :: Γa, _, _, _, h => by
      rw [List.cons_append] at h
      cases h with
      | left h =>
          obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, h₁, h₂, l₁, l₂, q₁, q₂, hs, pm⟩ :=
            splitP_route hp Γa h
          exact ⟨_ :: Γa₁, Γb₁, _ :: Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, by simp [h₁], by simp [h₂],
            l₁, l₂, q₁, q₂, .left hs, pm⟩
      | right h =>
          obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, h₁, h₂, l₁, l₂, q₁, q₂, hs, pm⟩ :=
            splitP_route hp Γa h
          exact ⟨_ :: Γa₁, Γb₁, _ :: Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, by simp [h₁], by simp [h₂],
            l₁, l₂, q₁, q₂, .right hs, pm⟩
      | dead h =>
          obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, h₁, h₂, l₁, l₂, q₁, q₂, hs, pm⟩ :=
            splitP_route hp Γa h
          exact ⟨_ :: Γa₁, Γb₁, _ :: Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, by simp [h₁], by simp [h₂],
            l₁, l₂, q₁, q₂, .dead hs, pm⟩
      | dup hT h =>
          obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, h₁, h₂, l₁, l₂, q₁, q₂, hs, pm⟩ :=
            splitP_route hp Γa h
          exact ⟨_ :: Γa₁, Γb₁, _ :: Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, by simp [h₁], by simp [h₂],
            l₁, l₂, q₁, q₂, .dup hT hs, pm⟩

/-- A premise on every live slot, past inserted slots that satisfy it. -/
theorem live_ins {P : Slot VTy → Prop} {Γa Γb : Ctx VTy} (hp : ∀ s ∈ Γp, s.live = true → P s)
    (h : ∀ s ∈ Γa ++ Γb, s.live = true → P s) : ∀ s ∈ Γa ++ Γp ++ Γb, s.live = true → P s := by
  intro s hs hl
  simp only [List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · exact h s (List.mem_append_left _ hs) hl
  · exact hp s hs hl
  · exact h s (List.mem_append_right _ hs) hl

theorem banged_ins {Γa Γb : Ctx VTy} (hp : LiveP Atom.bang.eval Γp)
    (h : Ctx.Banged (Γa ++ Γb)) : Ctx.Banged (Γa ++ Γp ++ Γb) :=
  live_ins (fun s hs hl => isBangB_sound (hp s hs hl)) h

theorem ctxOutlives_ins {Δ : LifeCtx} {a : Lifetime.Life} {Γa Γb : Ctx VTy}
    (hp : LiveP (Atom.outl Δ a).eval Γp) (h : CtxOutlives Δ (Γa ++ Γb) a) :
    CtxOutlives Δ (Γa ++ Γp ++ Γb) a :=
  ⟨h.1, live_ins (fun s hs hl => outlivesB_sound Δ a s.ty (hp s hs hl)) h.2⟩

theorem fresh_ins {x : LifeVar} {Γa Γb : Ctx VTy} (hp : LiveP (Atom.nfree x).eval Γp)
    (h : ∀ s ∈ Γa ++ Γb, s.live = true → ¬ VFree x s.ty) :
    ∀ s ∈ Γa ++ Γp ++ Γb, s.live = true → ¬ VFree x s.ty :=
  live_ins (fun s hs hl => not_vfree_of_vfreeB (by simpa [Atom.eval] using hp s hs hl)) h

theorem cancels_of_unr {S : Row} (h : S.Unr) : S.Cancels := by
  obtain ⟨o, ho, hq⟩ := h
  exact ⟨o, ho, by rw [hq]; decide⟩

/-- `[let]`'s premises on the rest's context, past inserted slots that satisfy its condition. -/
theorem letCond_ins {S : Row} {Γa Γb : Ctx VTy} (hp : LiveP (TExpr.absF.letCond S).eval Γp)
    (hW : S.Cancels → (Γa ++ Γb).OwnFree) (hU : S.Unr → Ctx.Banged (Γa ++ Γb)) :
    (S.Cancels → (Γa ++ Γp ++ Γb).OwnFree) ∧ (S.Unr → Ctx.Banged (Γa ++ Γp ++ Γb)) := by
  unfold TExpr.absF.letCond at hp
  by_cases hw : Row.cancelsB S = true
  · rw [if_pos hw] at hp
    have hd : LiveP dropB Γp := hp.imp fun A hA => by
      simp only [AbsF.eval_and, AbsF.eval_atom, Bool.and_eq_true] at hA; exact hA.1
    refine ⟨fun h => live_ins (fun s hs hl => dropB_sound _ (hd s hs hl)) (hW h),
      fun h => live_ins (fun s hs hl => isBangB_sound ?_) (hU h)⟩
    have hu : Row.unrB S = true := Row.unrB_iff.mpr h
    have := hp s hs hl
    simp only [hu, if_true, AbsF.eval_and, AbsF.eval_atom, Atom.eval, Bool.and_eq_true] at this
    exact this.2
  · refine ⟨fun h => absurd (Row.cancelsB_iff.mpr h) hw,
      fun h => absurd (Row.cancelsB_iff.mpr (cancels_of_unr h)) hw⟩

/-! ### Weakening -/

/-- **Weakening of a typed derivation** by slots inserted inside its context, every live one at a
type the term's absorption holds of: the shifted term, at the context with the slots inserted;
and the shifted term's erasure is the erasure shifted.  `[spec §3, §29]` -/
theorem TDerivesP.weaken {Δ : LifeCtx} {Γ₀ : Ctx VTy} {t : TExpr} {j : Jdg}
    (h : TDerivesP Δ Γ₀ t j) : ∀ (Γa Γb Γp : Ctx VTy) (f : AbsF), Γ₀ = Γa ++ Γb →
    t.absF Δ = some f → LiveP f.eval Γp →
    TDerivesP Δ (Γa ++ Γp ++ Γb) (t.shift Γp.length Γa.length) j ∧
      (t.shift Γp.length Γa.length).erase = t.erase.shift Γp.length Γa.length := by
  induction h with
  | var hs =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      exact ⟨.var (soloP_ins (live_eval_atom hf hp) Γa hs), (var_shift _ _ _).symm⟩
  | unitI hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.unitI (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | tensorI hs hm hcv _ _ ih₁ ih₂ =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨d₁, e₁⟩ := ih₁ Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨d₂, e₂⟩ := ih₂ Γa₂ Γb₂ Γp₂ f₂ rfl hf₂ q₂
      rw [ha₁, hl₁] at d₁ e₁; rw [ha₂, hl₂] at d₂ e₂
      exact ⟨.tensorI hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [e₁]; rfl), hcv.2.ins₂ (by rw [e₂]; rfl)⟩ d₁ d₂, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e₁, e₂]⟩
  | sumI₁ _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.sumI₁ d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]⟩
  | sumI₂ _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.sumI₂ d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]⟩
  | thunkF _ ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨d, e⟩ := ih (_ :: Γa) Γb Γp f rfl hf hp
      rw [List.length_cons] at d e
      exact ⟨.thunkF d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, e]⟩
  | thunkV hC _ q ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.thunkV hC d (by rw [e, q]; rfl), e⟩
  | ret _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.ret d, e⟩
  | bind hs hm hcv _ _ ihM ihN =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨dM, eM⟩ := ihM Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨dN, eN⟩ := ihN (_ :: Γa₂) Γb₂ Γp₂ f₂ rfl hf₂ q₂
      rw [ha₁, hl₁] at dM eM; rw [List.length_cons, ha₂, hl₂] at dN eN
      exact ⟨.bind hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eM]; rfl), hcv.2.ins₂ (by rw [eN])⟩ dM dN, by
        simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, eM, eN]⟩
  | force hs =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      exact ⟨.force (soloP_ins (live_eval_atom hf hp) Γa hs), (forceE_var_shift _ _ _ _).symm⟩
  | lam _ ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨d, e⟩ := ih (_ :: Γa) Γb Γp f rfl hf hp
      rw [List.length_cons] at d e
      exact ⟨.lam d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, e]⟩
  | lamDead _ ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨d, e⟩ := ih (_ :: Γa) Γb Γp f rfl hf hp
      rw [List.length_cons] at d e
      exact ⟨.lamDead d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, e]⟩
  | app hs hm hcv _ hx ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨dM, eM⟩ := ih Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      have hx' := soloP_ins (live_eval_atom hf₂ q₂) Γa₂ hx
      rw [ha₁, hl₁] at dM eM; rw [ha₂, hl₂] at hx'
      exact ⟨.app hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eM]; rfl), hcv.2.ins₂ (by rw [var_shift]; rfl)⟩ dM hx', by
        simp only [TExpr.shift, TExpr.erase, eM]; rw [Expr.shift, var_shift]⟩
  | withI _ _ ihM ihN =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, q₁, q₂⟩ := live_andO hf hp
      obtain ⟨dM, eM⟩ := ihM (_ :: _ :: Γa) Γb Γp f₁ rfl hf₁ q₁
      obtain ⟨dN, eN⟩ := ihN (_ :: _ :: Γa) Γb Γp f₂ rfl hf₂ q₂
      simp only [List.length_cons] at dM eM dN eN
      exact ⟨.withI dM dN, by rw [TExpr.erase, withPair_shift, ← eM, ← eN]; rfl⟩
  | proj₁ _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.proj₁ d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]; rfl⟩
  | proj₂ _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.proj₂ d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]; rfl⟩
  | topI => intro Γa Γb Γp f _ _ _; exact ⟨.topI, rfl⟩
  | unitE hs hm hcv _ _ ihV ihM =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨dV, eV⟩ := ihV Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨dM, eM⟩ := ihM Γa₂ Γb₂ Γp₂ f₂ rfl hf₂ q₂
      rw [ha₁, hl₁] at dV eV; rw [ha₂, hl₂] at dM eM
      exact ⟨.unitE hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eV]; rfl), hcv.2.ins₂ (by rw [eM]; rfl)⟩ dV dM, by simp only [TExpr.shift, TExpr.erase, Expr.shift, eV, eM]⟩
  | tensorE hs hm hcv _ _ ihV ihM =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨dV, eV⟩ := ihV Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨dM, eM⟩ := ihM (_ :: _ :: Γa₂) Γb₂ Γp₂ f₂ rfl hf₂ q₂
      rw [ha₁, hl₁] at dV eV; simp only [List.length_cons, ha₂, hl₂] at dM eM
      exact ⟨.tensorE hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eV]; rfl), hcv.2.ins₂ (by rw [eM])⟩ dV dM, by simp only [TExpr.shift, TExpr.erase, Expr.shift, eV, eM]⟩
  | sumE hs hm hcv _ _ _ ihV ih₁ ih₂ =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨k₁, k₂, hk₁, hk₂, w₁, w₂⟩ := live_andO hf₂ q₂
      obtain ⟨dV, eV⟩ := ihV Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨d₁, e₁⟩ := ih₁ (_ :: Γa₂) Γb₂ Γp₂ k₁ rfl hk₁ w₁
      obtain ⟨d₂, e₂⟩ := ih₂ (_ :: Γa₂) Γb₂ Γp₂ k₂ rfl hk₂ w₂
      rw [ha₁, hl₁] at dV eV; rw [List.length_cons, ha₂, hl₂] at d₁ e₁ d₂ e₂
      exact ⟨.sumE hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eV]; rfl), hcv.2.1.ins₂ (by rw [e₁]), hcv.2.2.ins₂ (by rw [e₂])⟩ dV d₁ d₂, by simp only [TExpr.shift, TExpr.erase, Expr.shift, eV, e₁, e₂]⟩
  | zeroE hs hm hcv _ ihV =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨dV, eV⟩ := ihV Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      rw [ha₁, hl₁] at dV eV
      exact ⟨.zeroE hs' (hm.ins ha₁ ha₂ pm) (hcv.ins₁ (by rw [eV]; rfl)) dV, by rw [TExpr.erase, absurdE_shift, ← eV]; rfl⟩
  | allI hbx hΔx hΓx _ ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f', hf', hx, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ih (_ :: Γa) Γb Γp f' rfl hf' hp'
      rw [List.length_cons] at d e
      exact ⟨.allI hbx hΔx (fresh_ins (live_atom hx) hΓx) d, by
        simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, e]⟩
  | allE _ hlt ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.allE d hlt, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]; rfl⟩
  | bangThunkF hpΓ _ ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f', hf', hb, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ih (_ :: Γa) Γb Γp f' rfl hf' hp'
      rw [List.length_cons] at d e
      exact ⟨.bangThunkF (banged_ins (live_atom hb) hpΓ) d, by
        simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, e]⟩
  | bangThunkV hpΓ hC _ q ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f', hf', hb, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f' rfl hf' hp'
      exact ⟨.bangThunkV (banged_ins (live_atom hb) hpΓ) hC d (by rw [e, q]; rfl), e⟩
  | bangE _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.bangE d, e⟩
  | copyBang hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.copyBang (deadP_ins (live_eval_atom hf hp) Γa hΓ), (shift_closed0 (by rfl) _ _).symm⟩
  | forgetBang hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.forgetBang (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | boxI _ hΓ ih =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', ho, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f' rfl hf' hp'
      exact ⟨.boxI d (ctxOutlives_ins (live_atom ho) hΓ), e⟩
  | boxE _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.boxE d, e⟩
  | immSub _ hle ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.immSub d hle, e⟩
  | mutSub _ hle ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.mutSub d hle, e⟩
  | alloc hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.alloc (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | free hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.free (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | swap hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.swap (deadP_ins (live_eval_atom hf hp) Γa hΓ), (shift_closed0 (by rfl) _ _).symm⟩
  | copy hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.copy (deadP_ins (live_eval_atom hf hp) Γa hΓ), (shift_closed0 (by rfl) _ _).symm⟩
  | forgetImm hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.forgetImm (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | forgetMut hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.forgetMut (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | forgetUnk hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.forgetUnk (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | lit c hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.lit c (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | hostOp op hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.hostOp op (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | arrNew A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrNew A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | arrFree A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrFree A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | arrSize A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrSize A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | arrReplace A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrReplace A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | arrLen a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrLen a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | arrGet a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrGet a A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | arrCopy a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrCopy a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | arrForget a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrForget a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | countFold S hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.countFold S (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | countTry S E hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.countTry S E (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | boundedFix A C hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.boundedFix A C (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceBorrowM x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hA hB hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceBorrowI x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hsc hA hB hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceGetM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceGetM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | sliceLenM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceLenM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceSplitI a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceSplitI a A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | sliceSplitM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceSplitM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | sliceEmptyI a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceEmptyI a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceEmptyM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceEmptyM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | arrEmpty A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrEmpty A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceReplaceM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceReplaceM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceSwapM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceSwapM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | withbor1 x hΓ hx hsc hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withbor1 x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hx hsc hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | withbor2 x hΓ hx hside hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withbor2 x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hx hside hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | withbor3 x hΓ hx hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withbor3 x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hx hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | withload x hΓ hx hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withload x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hx hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | withswap hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withswap (deadP_ins (live_eval_atom hf hp) Γa hΓ), (shift_closed0 (by rfl) _ _).symm⟩
  | withbor1U x hΓ hx hsc hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', hpe, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ihd Γa Γb Γp f' rfl hf' hp'
      rw [shift_closed0 hdc] at e
      exact ⟨.withbor1U x (deadP_ins (live_atom hpe) Γa hΓ) hx hsc hf₁ hf₂ hS (by rw [e]; exact hdc)
        d, by rw [TExpr.shift, TExpr.erase, TExpr.erase, e, shift_closed0 (withborUE_closed hdc)]⟩
  | withbor2U x hΓ hx hside hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', hpe, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ihd Γa Γb Γp f' rfl hf' hp'
      rw [shift_closed0 hdc] at e
      exact ⟨.withbor2U x (deadP_ins (live_atom hpe) Γa hΓ) hx hside hf₁ hf₂ hS
        (by rw [e]; exact hdc) d,
        by rw [TExpr.shift, TExpr.erase, TExpr.erase, e, shift_closed0 (withborUE_closed hdc)]⟩
  | withbor3U x hΓ hx hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', hpe, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ihd Γa Γb Γp f' rfl hf' hp'
      rw [shift_closed0 hdc] at e
      exact ⟨.withbor3U x (deadP_ins (live_atom hpe) Γa hΓ) hx hf₁ hf₂ hS (by rw [e]; exact hdc) d,
        by rw [TExpr.shift, TExpr.erase, TExpr.erase, e, shift_closed0 (withborUE_closed hdc)]⟩
  | withloadU x hΓ hx hf₁ hf₂ hS =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withloadU x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hx hf₁ hf₂ hS,
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', hpe, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ihd Γa Γb Γp f' rfl hf' hp'
      rw [shift_closed0 hdc] at e
      exact ⟨.sliceBorrowMU x (deadP_ins (live_atom hpe) Γa hΓ) hA hB hf₁ hf₂ hS
        (by rw [e]; exact hdc) d,
        by rw [TExpr.shift, TExpr.erase, TExpr.erase, e, shift_closed0 (withborUE_closed hdc)]⟩
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', hpe, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ihd Γa Γb Γp f' rfl hf' hp'
      rw [shift_closed0 hdc] at e
      exact ⟨.sliceBorrowIU x (deadP_ins (live_atom hpe) Γa hΓ) hsc hA hB hf₁ hf₂ hS
        (by rw [e]; exact hdc) d,
        by rw [TExpr.shift, TExpr.erase, TExpr.erase, e, shift_closed0 (withborUE_closed hdc)]⟩
  | lolliE hs hm hcv _ _ iha ihf =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨da, ea⟩ := iha Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨df, ef⟩ := ihf Γa₂ Γb₂ Γp₂ f₂ rfl hf₂ q₂
      rw [ha₁, hl₁] at da ea; rw [ha₂, hl₂] at df ef
      exact ⟨.lolliE hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [ea]; rfl), hcv.2.ins₂ (by rw [ef]; rfl)⟩ da df, by simp only [TExpr.shift, TExpr.erase, Expr.shift, ea, ef]⟩
  | allEV _ hlt ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.allEV d hlt, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]; rfl⟩
  | ofRet _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.ofRet d, e⟩
  | roll hA hc _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.roll hA hc d, e⟩
  | unroll _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.unroll d, e⟩
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.foldImm F y c R (deadP_ins (live_eval_atom hf hp) Γa hΓ) hF hG hyM hyR hR,
        (shift_closed0 (foldImmV_closed F) _ _).symm⟩
  | foldOwn F R hΓ hF hG =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.foldOwn F R (deadP_ins (live_eval_atom hf hp) Γa hΓ) hF hG,
        (shift_closed0 (foldOwnV_closed F) _ _).symm⟩
  | foldOwnG B₀ Rs hΓ hB =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.foldOwnG B₀ Rs (deadP_ins (live_eval_atom hf hp) Γa hΓ) hB,
        (shift_closed0 (FoldP.foldOwnGV_closed B₀) _ _).symm⟩
  | foldReuse F R hΓ hF hG =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.foldReuse F R (deadP_ins (live_eval_atom hf hp) Γa hΓ) hF hG,
        (shift_closed0 (foldReuseV_closed F) _ _).symm⟩
  | nuIn hC _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.nuIn hC d, e⟩
  | nuOut hC _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.nuOut hC d, e⟩
  | unfoldN C S hC hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.unfoldN C S hC (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (unfoldV_closed C) _ _).symm⟩
  | effSub hle _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.effSub hle d, e⟩
  | effPerform hf₀ hna _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.effPerform hf₀ hna d, by
        simp only [TExpr.shift, TExpr.erase, BoCa.BoLo.performE, opArgE, Expr.shift, e]; rfl⟩
  | effRaise hf₀ ha hd _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.effRaise hf₀ ha hd d, by
        simp only [TExpr.shift, TExpr.erase, BoCa.BoLo.raiseE, opArgE, Expr.shift, e]; rfl⟩
  | effLet hs hm hcv hW hU _ _ ihM ihN =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨f', hf', hc, q₂'⟩ := live_withO hf₂ q₂
      obtain ⟨dM, eM⟩ := ihM Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨dN, eN⟩ := ihN (_ :: Γa₂) Γb₂ Γp₂ f' rfl hf' q₂'
      rw [ha₁, hl₁] at dM eM; rw [List.length_cons, ha₂, hl₂] at dN eN
      obtain ⟨hW', hU'⟩ := letCond_ins hc hW hU
      exact ⟨.effLet hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eM]; rfl), hcv.2.ins₂ (by rw [eN])⟩ hW' hU' dM dN, by
        simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, eM, eN]⟩
  | effThen hs hm hcv hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨f', hf', hc, q₂'⟩ := live_withO hf₂ q₂
      obtain ⟨k₁, k₂, hk₁, hk₂, w₁, w₂⟩ := live_andO hf' q₂'
      obtain ⟨dM, eM⟩ := ihM Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨dN, eN⟩ := ihN (_ :: Γa₂) Γb₂ Γp₂ k₁ rfl hk₁ w₁
      obtain ⟨dD, eD⟩ := ihD (_ :: Γa₂) Γb₂ Γp₂ k₂ rfl hk₂ w₂
      rw [ha₁, hl₁] at dM eM; rw [List.length_cons, ha₂, hl₂] at dN eN dD eD
      exact ⟨.effThen hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eM]; rfl), hcv.2.1.ins₂ (by rw [eN]), hcv.2.2.ins₂ (by rw [eD])⟩ hNZ hUq (fun hu => banged_ins (hc.imp fun A hA => by
          rw [if_pos (Row.unrDB_iff.mpr hu), AbsF.eval_atom] at hA; exact hA) (hU hu))
          hMS hDS hfin hP hSD dM dN dD, by
        simp only [TExpr.shift, TExpr.erase, thenE, Expr.shift, Expr.val, Val.lam, Val.prim, eM,
          eN, eD]⟩
  | effHandleV hs hm hcv hdd hH _ hn0 hnS hlen hdv _ hins ihc ihe =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨f', hf', hpe, q₁'⟩ := live_withO hf₁ q₁
      obtain ⟨dc, ec⟩ := ihc Γa₁ Γb₁ Γp₁ f' rfl hf' q₁'
      obtain ⟨de, ee⟩ := ihe Γa₂ Γb₂ Γp₂ f₂ rfl hf₂ q₂
      have hH' := valFormIn_insert (Γd := Γp₁) Γa₁ hH
      rw [← ec] at hH'
      rw [ha₁, hl₁] at dc ec hH'; rw [ha₂, hl₂] at de ee
      exact ⟨.effHandleV hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [ec]; rfl), hcv.2.ins₂ (by rw [ee]; rfl)⟩ (deadP_ins (live_atom hpe) Γa₁ hdd) hH' dc hn0 hnS hlen hdv de
        (by rw [ee, ClauseKinds.hin_shift]; exact hins), by
        rw [TExpr.shift, TExpr.erase, TExpr.erase, shift_hndExpr, ec, ee]⟩
  | effHandleVB hs hm hcv hdd hH _ hn0 hnS hlen hdv _ hΓd hSd hins ihc ihe =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨f', hf', hpe, q₁'⟩ := live_withO hf₁ q₁
      obtain ⟨g', hg', ho, q₂'⟩ := live_withO hf₂ q₂
      obtain ⟨dc, ec⟩ := ihc Γa₁ Γb₁ Γp₁ f' rfl hf' q₁'
      obtain ⟨de, ee⟩ := ihe Γa₂ Γb₂ Γp₂ g' rfl hg' q₂'
      have hH' := valFormIn_insert (Γd := Γp₁) Γa₁ hH
      rw [← ec] at hH'
      rw [ha₁, hl₁] at dc ec hH'; rw [ha₂, hl₂] at de ee
      exact ⟨.effHandleVB hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [ec]; rfl), hcv.2.ins₂ (by rw [ee]; rfl)⟩ (deadP_ins (live_atom hpe) Γa₁ hdd) hH' dc hn0 hnS hlen hdv de
        (ctxOutlives_ins (live_atom ho) hΓd) hSd (by rw [ee, ClauseKinds.hin_shift]; exact hins), by
        rw [TExpr.shift, TExpr.erase, TExpr.erase, shift_hndExpr, ec, ee]⟩
  | iterate S St B R hS hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.iterate S St B R hS (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | divFuel S A hS hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.divFuel S A hS (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 divFuelV_closed _ _).symm⟩
  | reify S B R res hS hcl hres qres hΓ _ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.reify S B R res hS hcl hres qres (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        by simp only [TExpr.shift, TExpr.erase, qres, Expr.toVal_val]
           exact (shift_closed0 (reifyV_closed hcl) _ _).symm⟩
  | effHandleT => intro _ _ _ _ _ hf _; cases hf
  | effHandleL => intro _ _ _ _ _ hf _; cases hf
  | letPoly => intro _ _ _ _ _ hf _; cases hf
  | lendR => intro _ _ _ _ _ hf _; cases hf
  | lendLoopR => intro _ _ _ _ _ hf _; cases hf
  | nilDead => intro _ _ _ _ _ hf _; cases hf
  | dtor hA hc he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.dtor hA hc he (dead_ins (live_eval_ff hf hp) Γa hΓ), (shift_closed0 hc _ _).symm⟩
  | allocS σ he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.allocS σ he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 (allocS_closed σ) _ _).symm⟩
  | freeS σ he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.freeS σ he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 (freeS_closed σ) _ _).symm⟩
  | withborSM σ c T hσ hT hΔ hc hcl he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withborSM σ c T hσ hT hΔ hc hcl he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 hcl _ _).symm⟩
  | withborSI σ c T hσ hT hΔ hc hcl he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withborSI σ c T hσ hT hΔ hc hcl he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 hcl _ _).symm⟩
  | withborF2M s hA hBo hTo he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withborF2M s hA hBo hTo he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | withborF2I s hA hB hBo hTo he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withborF2I s hA hB hBo hTo he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | litFn _ hb hcl ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.litFn d (by rw [e, hb, shift_closed0 hcl]) hcl, e⟩
  | divLit _ hb hs ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.divLit d (by rw [e]; exact divLitB_shift hb _ _) hs, e⟩
  | walk _ hb hr ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.walk d (by rw [e]; exact walkB_shift hb _ _)
        (fun h => by rw [e]; exact walkReadB_shift (hr h) _ _), e⟩
  | walkGet _ hb ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.walkGet d (by rw [e]; exact walkGetB_shift hb _ _), e⟩
  | selfCall _ hb ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.selfCall d (by rw [e]; exact selfCallB_shift hb _ _), e⟩
  | lendCell _ hb hm ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.lendCell d (by rw [e]; exact lendCellB_shift hb _ _) (by rw [lendKindB_shift]; exact hm), e⟩
  | lendScope _ hs hr ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.lendScope d (by rw [lendScopeT_shift]; exact hs) (by rw [lendRelT_shift]; exact hr), e⟩
  | litView _ hb ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.litView d (by rw [litViewT_shift]; exact hb), e⟩
  | unfoldStep _ hb ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.unfoldStep d (by rw [unfoldAppT_shift]; exact hb), e⟩
  | nuEta _ hb ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.nuEta d (by rw [e]; exact nuEtaB_shift hb _ _), e⟩
  | use _ hab ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ (hab ▸ hf) hp
      exact ⟨.use d (hab.trans (TExpr.absF_shift _ _ _ _).symm), e⟩

/-- **Weakening of a tied typed derivation**, as `TDerivesP.weaken`: the tie is on rows, which the
shift leaves alone.  `[spec §3, §19]` -/
theorem TDerivesAt.weaken {Ξ : EffCtx} {Δ : LifeCtx} {Γ₀ : Ctx VTy} {t : TExpr} {j : Jdg}
    (h : TDerivesAt Ξ Δ Γ₀ t j) : ∀ (Γa Γb Γp : Ctx VTy) (f : AbsF), Γ₀ = Γa ++ Γb →
    t.absF Δ = some f → LiveP f.eval Γp →
    TDerivesAt Ξ Δ (Γa ++ Γp ++ Γb) (t.shift Γp.length Γa.length) j ∧
      (t.shift Γp.length Γa.length).erase = t.erase.shift Γp.length Γa.length := by
  induction h with
  | var hs =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      exact ⟨.var (soloP_ins (live_eval_atom hf hp) Γa hs), (var_shift _ _ _).symm⟩
  | unitI hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.unitI (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | tensorI hs hm hcv _ _ ih₁ ih₂ =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨d₁, e₁⟩ := ih₁ Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨d₂, e₂⟩ := ih₂ Γa₂ Γb₂ Γp₂ f₂ rfl hf₂ q₂
      rw [ha₁, hl₁] at d₁ e₁; rw [ha₂, hl₂] at d₂ e₂
      exact ⟨.tensorI hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [e₁]; rfl), hcv.2.ins₂ (by rw [e₂]; rfl)⟩ d₁ d₂, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e₁, e₂]⟩
  | sumI₁ _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.sumI₁ d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]⟩
  | sumI₂ _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.sumI₂ d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]⟩
  | thunkF _ ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨d, e⟩ := ih (_ :: Γa) Γb Γp f rfl hf hp
      rw [List.length_cons] at d e
      exact ⟨.thunkF d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, e]⟩
  | thunkV hC _ q ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.thunkV hC d (by rw [e, q]; rfl), e⟩
  | ret _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.ret d, e⟩
  | bind hs hm hcv _ _ ihM ihN =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨dM, eM⟩ := ihM Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨dN, eN⟩ := ihN (_ :: Γa₂) Γb₂ Γp₂ f₂ rfl hf₂ q₂
      rw [ha₁, hl₁] at dM eM; rw [List.length_cons, ha₂, hl₂] at dN eN
      exact ⟨.bind hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eM]; rfl), hcv.2.ins₂ (by rw [eN])⟩ dM dN, by
        simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, eM, eN]⟩
  | force hs =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      exact ⟨.force (soloP_ins (live_eval_atom hf hp) Γa hs), (forceE_var_shift _ _ _ _).symm⟩
  | lam _ ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨d, e⟩ := ih (_ :: Γa) Γb Γp f rfl hf hp
      rw [List.length_cons] at d e
      exact ⟨.lam d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, e]⟩
  | lamDead _ ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨d, e⟩ := ih (_ :: Γa) Γb Γp f rfl hf hp
      rw [List.length_cons] at d e
      exact ⟨.lamDead d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, e]⟩
  | app hs hm hcv _ hx ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨dM, eM⟩ := ih Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      have hx' := soloP_ins (live_eval_atom hf₂ q₂) Γa₂ hx
      rw [ha₁, hl₁] at dM eM; rw [ha₂, hl₂] at hx'
      exact ⟨.app hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eM]; rfl), hcv.2.ins₂ (by rw [var_shift]; rfl)⟩ dM hx', by
        simp only [TExpr.shift, TExpr.erase, eM]; rw [Expr.shift, var_shift]⟩
  | withI _ _ ihM ihN =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, q₁, q₂⟩ := live_andO hf hp
      obtain ⟨dM, eM⟩ := ihM (_ :: _ :: Γa) Γb Γp f₁ rfl hf₁ q₁
      obtain ⟨dN, eN⟩ := ihN (_ :: _ :: Γa) Γb Γp f₂ rfl hf₂ q₂
      simp only [List.length_cons] at dM eM dN eN
      exact ⟨.withI dM dN, by rw [TExpr.erase, withPair_shift, ← eM, ← eN]; rfl⟩
  | proj₁ _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.proj₁ d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]; rfl⟩
  | proj₂ _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.proj₂ d, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]; rfl⟩
  | topI => intro Γa Γb Γp f _ _ _; exact ⟨.topI, rfl⟩
  | unitE hs hm hcv _ _ ihV ihM =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨dV, eV⟩ := ihV Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨dM, eM⟩ := ihM Γa₂ Γb₂ Γp₂ f₂ rfl hf₂ q₂
      rw [ha₁, hl₁] at dV eV; rw [ha₂, hl₂] at dM eM
      exact ⟨.unitE hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eV]; rfl), hcv.2.ins₂ (by rw [eM]; rfl)⟩ dV dM, by simp only [TExpr.shift, TExpr.erase, Expr.shift, eV, eM]⟩
  | tensorE hs hm hcv _ _ ihV ihM =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨dV, eV⟩ := ihV Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨dM, eM⟩ := ihM (_ :: _ :: Γa₂) Γb₂ Γp₂ f₂ rfl hf₂ q₂
      rw [ha₁, hl₁] at dV eV; simp only [List.length_cons, ha₂, hl₂] at dM eM
      exact ⟨.tensorE hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eV]; rfl), hcv.2.ins₂ (by rw [eM])⟩ dV dM, by simp only [TExpr.shift, TExpr.erase, Expr.shift, eV, eM]⟩
  | sumE hs hm hcv _ _ _ ihV ih₁ ih₂ =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨k₁, k₂, hk₁, hk₂, w₁, w₂⟩ := live_andO hf₂ q₂
      obtain ⟨dV, eV⟩ := ihV Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨d₁, e₁⟩ := ih₁ (_ :: Γa₂) Γb₂ Γp₂ k₁ rfl hk₁ w₁
      obtain ⟨d₂, e₂⟩ := ih₂ (_ :: Γa₂) Γb₂ Γp₂ k₂ rfl hk₂ w₂
      rw [ha₁, hl₁] at dV eV; rw [List.length_cons, ha₂, hl₂] at d₁ e₁ d₂ e₂
      exact ⟨.sumE hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eV]; rfl), hcv.2.1.ins₂ (by rw [e₁]), hcv.2.2.ins₂ (by rw [e₂])⟩ dV d₁ d₂, by simp only [TExpr.shift, TExpr.erase, Expr.shift, eV, e₁, e₂]⟩
  | zeroE hs hm hcv _ ihV =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨dV, eV⟩ := ihV Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      rw [ha₁, hl₁] at dV eV
      exact ⟨.zeroE hs' (hm.ins ha₁ ha₂ pm) (hcv.ins₁ (by rw [eV]; rfl)) dV, by rw [TExpr.erase, absurdE_shift, ← eV]; rfl⟩
  | allI hbx hΔx hΓx _ ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f', hf', hx, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ih (_ :: Γa) Γb Γp f' rfl hf' hp'
      rw [List.length_cons] at d e
      exact ⟨.allI hbx hΔx (fresh_ins (live_atom hx) hΓx) d, by
        simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, e]⟩
  | allE _ hlt ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.allE d hlt, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]; rfl⟩
  | bangThunkF hpΓ _ ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f', hf', hb, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ih (_ :: Γa) Γb Γp f' rfl hf' hp'
      rw [List.length_cons] at d e
      exact ⟨.bangThunkF (banged_ins (live_atom hb) hpΓ) d, by
        simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, e]⟩
  | bangThunkV hpΓ hC _ q ih =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f', hf', hb, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f' rfl hf' hp'
      exact ⟨.bangThunkV (banged_ins (live_atom hb) hpΓ) hC d (by rw [e, q]; rfl), e⟩
  | bangE _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.bangE d, e⟩
  | copyBang hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.copyBang (deadP_ins (live_eval_atom hf hp) Γa hΓ), (shift_closed0 (by rfl) _ _).symm⟩
  | forgetBang hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.forgetBang (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | boxI _ hΓ ih =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', ho, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f' rfl hf' hp'
      exact ⟨.boxI d (ctxOutlives_ins (live_atom ho) hΓ), e⟩
  | boxE _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.boxE d, e⟩
  | immSub _ hle ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.immSub d hle, e⟩
  | mutSub _ hle ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.mutSub d hle, e⟩
  | alloc hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.alloc (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | free hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.free (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | swap hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.swap (deadP_ins (live_eval_atom hf hp) Γa hΓ), (shift_closed0 (by rfl) _ _).symm⟩
  | copy hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.copy (deadP_ins (live_eval_atom hf hp) Γa hΓ), (shift_closed0 (by rfl) _ _).symm⟩
  | forgetImm hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.forgetImm (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | forgetMut hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.forgetMut (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | forgetUnk hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.forgetUnk (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | lit c hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.lit c (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | hostOp op hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.hostOp op (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | arrNew A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrNew A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | arrFree A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrFree A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | arrSize A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrSize A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | arrReplace A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrReplace A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | arrLen a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrLen a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | arrGet a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrGet a A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | arrCopy a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrCopy a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | arrForget a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrForget a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | countFold S hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.countFold S (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | countTry S E hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.countTry S E (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | boundedFix A C hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.boundedFix A C (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceBorrowM x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hA hB hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceBorrowI x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hsc hA hB hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceGetM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceGetM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | sliceLenM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceLenM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceSplitI a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceSplitI a A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | sliceSplitM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceSplitM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | sliceEmptyI a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceEmptyI a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceEmptyM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceEmptyM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | arrEmpty A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.arrEmpty A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceReplaceM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceReplaceM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceSwapM a A hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.sliceSwapM a A (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | withbor1 x hΓ hx hsc hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withbor1 x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hx hsc hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | withbor2 x hΓ hx hside hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withbor2 x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hx hside hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | withbor3 x hΓ hx hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withbor3 x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hx hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | withload x hΓ hx hf₁ hf₂ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withload x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hx hf₁ hf₂,
        (shift_closed0 (by rfl) _ _).symm⟩
  | withswap hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withswap (deadP_ins (live_eval_atom hf hp) Γa hΓ), (shift_closed0 (by rfl) _ _).symm⟩
  | withbor1U x hΓ hx hsc hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', hpe, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ihd Γa Γb Γp f' rfl hf' hp'
      rw [shift_closed0 hdc] at e
      exact ⟨.withbor1U x (deadP_ins (live_atom hpe) Γa hΓ) hx hsc hf₁ hf₂ hS (by rw [e]; exact hdc)
        d, by rw [TExpr.shift, TExpr.erase, TExpr.erase, e, shift_closed0 (withborUE_closed hdc)]⟩
  | withbor2U x hΓ hx hside hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', hpe, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ihd Γa Γb Γp f' rfl hf' hp'
      rw [shift_closed0 hdc] at e
      exact ⟨.withbor2U x (deadP_ins (live_atom hpe) Γa hΓ) hx hside hf₁ hf₂ hS
        (by rw [e]; exact hdc) d,
        by rw [TExpr.shift, TExpr.erase, TExpr.erase, e, shift_closed0 (withborUE_closed hdc)]⟩
  | withbor3U x hΓ hx hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', hpe, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ihd Γa Γb Γp f' rfl hf' hp'
      rw [shift_closed0 hdc] at e
      exact ⟨.withbor3U x (deadP_ins (live_atom hpe) Γa hΓ) hx hf₁ hf₂ hS (by rw [e]; exact hdc) d,
        by rw [TExpr.shift, TExpr.erase, TExpr.erase, e, shift_closed0 (withborUE_closed hdc)]⟩
  | withloadU x hΓ hx hf₁ hf₂ hS =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withloadU x (deadP_ins (live_eval_atom hf hp) Γa hΓ) hx hf₁ hf₂ hS,
        (shift_closed0 (by rfl) _ _).symm⟩
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', hpe, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ihd Γa Γb Γp f' rfl hf' hp'
      rw [shift_closed0 hdc] at e
      exact ⟨.sliceBorrowMU x (deadP_ins (live_atom hpe) Γa hΓ) hA hB hf₁ hf₂ hS
        (by rw [e]; exact hdc) d,
        by rw [TExpr.shift, TExpr.erase, TExpr.erase, e, shift_closed0 (withborUE_closed hdc)]⟩
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      obtain ⟨f', hf', hpe, hp'⟩ := live_withO hf hp
      obtain ⟨d, e⟩ := ihd Γa Γb Γp f' rfl hf' hp'
      rw [shift_closed0 hdc] at e
      exact ⟨.sliceBorrowIU x (deadP_ins (live_atom hpe) Γa hΓ) hsc hA hB hf₁ hf₂ hS
        (by rw [e]; exact hdc) d,
        by rw [TExpr.shift, TExpr.erase, TExpr.erase, e, shift_closed0 (withborUE_closed hdc)]⟩
  | lolliE hs hm hcv _ _ iha ihf =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨da, ea⟩ := iha Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨df, ef⟩ := ihf Γa₂ Γb₂ Γp₂ f₂ rfl hf₂ q₂
      rw [ha₁, hl₁] at da ea; rw [ha₂, hl₂] at df ef
      exact ⟨.lolliE hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [ea]; rfl), hcv.2.ins₂ (by rw [ef]; rfl)⟩ da df, by simp only [TExpr.shift, TExpr.erase, Expr.shift, ea, ef]⟩
  | allEV _ hlt ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.allEV d hlt, by simp only [TExpr.shift, TExpr.erase, Expr.shift, e]; rfl⟩
  | ofRet _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.ofRet d, e⟩
  | roll hA hc _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.roll hA hc d, e⟩
  | unroll _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.unroll d, e⟩
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.foldImm F y c R (deadP_ins (live_eval_atom hf hp) Γa hΓ) hF hG hyM hyR hR,
        (shift_closed0 (foldImmV_closed F) _ _).symm⟩
  | foldOwn F R hΓ hF hG =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.foldOwn F R (deadP_ins (live_eval_atom hf hp) Γa hΓ) hF hG,
        (shift_closed0 (foldOwnV_closed F) _ _).symm⟩
  | foldOwnG B₀ Rs hΓ hB =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.foldOwnG B₀ Rs (deadP_ins (live_eval_atom hf hp) Γa hΓ) hB,
        (shift_closed0 (FoldP.foldOwnGV_closed B₀) _ _).symm⟩
  | foldReuse F R hΓ hF hG =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.foldReuse F R (deadP_ins (live_eval_atom hf hp) Γa hΓ) hF hG,
        (shift_closed0 (foldReuseV_closed F) _ _).symm⟩
  | nuIn hC _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.nuIn hC d, e⟩
  | nuOut hC _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.nuOut hC d, e⟩
  | unfoldN C S hC hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.unfoldN C S hC (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 (unfoldV_closed C) _ _).symm⟩
  | effSub hle _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.effSub hle d, e⟩
  | effPerform hAt hf₀ hna _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.effPerform hAt hf₀ hna d, by
        simp only [TExpr.shift, TExpr.erase, BoCa.BoLo.performE, opArgE, Expr.shift, e]; rfl⟩
  | effRaise hAt hf₀ ha hd _ ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.effRaise hAt hf₀ ha hd d, by
        simp only [TExpr.shift, TExpr.erase, BoCa.BoLo.raiseE, opArgE, Expr.shift, e]; rfl⟩
  | effLet hs hm hcv hW hU _ _ ihM ihN =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨f', hf', hc, q₂'⟩ := live_withO hf₂ q₂
      obtain ⟨dM, eM⟩ := ihM Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨dN, eN⟩ := ihN (_ :: Γa₂) Γb₂ Γp₂ f' rfl hf' q₂'
      rw [ha₁, hl₁] at dM eM; rw [List.length_cons, ha₂, hl₂] at dN eN
      obtain ⟨hW', hU'⟩ := letCond_ins hc hW hU
      exact ⟨.effLet hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eM]; rfl), hcv.2.ins₂ (by rw [eN])⟩ hW' hU' dM dN, by
        simp only [TExpr.shift, TExpr.erase, Expr.shift, Expr.val, Val.lam, eM, eN]⟩
  | effThen hs hm hcv hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨f', hf', hc, q₂'⟩ := live_withO hf₂ q₂
      obtain ⟨k₁, k₂, hk₁, hk₂, w₁, w₂⟩ := live_andO hf' q₂'
      obtain ⟨dM, eM⟩ := ihM Γa₁ Γb₁ Γp₁ f₁ rfl hf₁ q₁
      obtain ⟨dN, eN⟩ := ihN (_ :: Γa₂) Γb₂ Γp₂ k₁ rfl hk₁ w₁
      obtain ⟨dD, eD⟩ := ihD (_ :: Γa₂) Γb₂ Γp₂ k₂ rfl hk₂ w₂
      rw [ha₁, hl₁] at dM eM; rw [List.length_cons, ha₂, hl₂] at dN eN dD eD
      exact ⟨.effThen hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [eM]; rfl), hcv.2.1.ins₂ (by rw [eN]), hcv.2.2.ins₂ (by rw [eD])⟩ hNZ hUq (fun hu => banged_ins (hc.imp fun A hA => by
          rw [if_pos (Row.unrDB_iff.mpr hu), AbsF.eval_atom] at hA; exact hA) (hU hu))
          hMS hDS hfin hP hSD dM dN dD, by
        simp only [TExpr.shift, TExpr.erase, thenE, Expr.shift, Expr.val, Val.lam, Val.prim, eM,
          eN, eD]⟩
  | effHandleV hAt hs hm hcv hdd hH _ hn0 hnS hlen hdv _ hins ihc ihe =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨f', hf', hpe, q₁'⟩ := live_withO hf₁ q₁
      obtain ⟨dc, ec⟩ := ihc Γa₁ Γb₁ Γp₁ f' rfl hf' q₁'
      obtain ⟨de, ee⟩ := ihe Γa₂ Γb₂ Γp₂ f₂ rfl hf₂ q₂
      have hH' := valFormIn_insert (Γd := Γp₁) Γa₁ hH
      rw [← ec] at hH'
      rw [ha₁, hl₁] at dc ec hH'; rw [ha₂, hl₂] at de ee
      exact ⟨.effHandleV hAt hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [ec]; rfl), hcv.2.ins₂ (by rw [ee]; rfl)⟩ (deadP_ins (live_atom hpe) Γa₁ hdd) hH' dc hn0 hnS hlen hdv de
        (by rw [ee, ClauseKinds.hin_shift]; exact hins), by
        rw [TExpr.shift, TExpr.erase, TExpr.erase, shift_hndExpr, ec, ee]⟩
  | effHandleVB hAt hs hm hcv hdd hH _ hn0 hnS hlen hdv _ hΓd hSd hins ihc ihe =>
      intro Γa Γb Γp f hΓ hf hp; subst hΓ
      obtain ⟨f₁, f₂, hf₁, hf₂, hp'⟩ := live_orO hf hp
      obtain ⟨Γa₁, Γb₁, Γa₂, Γb₂, Γp₁, Γp₂, rfl, rfl, ha₁, ha₂, hl₁, hl₂, q₁, q₂, hs', pm⟩ :=
        splitP_route hp' Γa hs
      obtain ⟨f', hf', hpe, q₁'⟩ := live_withO hf₁ q₁
      obtain ⟨g', hg', ho, q₂'⟩ := live_withO hf₂ q₂
      obtain ⟨dc, ec⟩ := ihc Γa₁ Γb₁ Γp₁ f' rfl hf' q₁'
      obtain ⟨de, ee⟩ := ihe Γa₂ Γb₂ Γp₂ g' rfl hg' q₂'
      have hH' := valFormIn_insert (Γd := Γp₁) Γa₁ hH
      rw [← ec] at hH'
      rw [ha₁, hl₁] at dc ec hH'; rw [ha₂, hl₂] at de ee
      exact ⟨.effHandleVB hAt hs' (hm.ins ha₁ ha₂ pm) ⟨hcv.1.ins₁ (by rw [ec]; rfl), hcv.2.ins₂ (by rw [ee]; rfl)⟩ (deadP_ins (live_atom hpe) Γa₁ hdd) hH' dc hn0 hnS hlen hdv de
        (ctxOutlives_ins (live_atom ho) hΓd) hSd (by rw [ee, ClauseKinds.hin_shift]; exact hins), by
        rw [TExpr.shift, TExpr.erase, TExpr.erase, shift_hndExpr, ec, ee]⟩
  | iterate S St B R hAt hS hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.iterate S St B R hAt hS (deadP_ins (live_eval_atom hf hp) Γa hΓ), rfl⟩
  | divFuel S A hAt hS hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.divFuel S A hAt hS (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        (shift_closed0 divFuelV_closed _ _).symm⟩
  | reify S B R res hAt hS hcl hres qres hΓ _ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.reify S B R res hAt hS hcl hres qres (deadP_ins (live_eval_atom hf hp) Γa hΓ),
        by simp only [TExpr.shift, TExpr.erase, qres, Expr.toVal_val]
           exact (shift_closed0 (reifyV_closed hcl) _ _).symm⟩
  | effHandleT => intro _ _ _ _ _ hf _; cases hf
  | effHandleL => intro _ _ _ _ _ hf _; cases hf
  | letPoly => intro _ _ _ _ _ hf _; cases hf
  | dtor hA hc he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.dtor hA hc he (dead_ins (live_eval_ff hf hp) Γa hΓ), (shift_closed0 hc _ _).symm⟩
  | allocS σ he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.allocS σ he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 (allocS_closed σ) _ _).symm⟩
  | freeS σ he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.freeS σ he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 (freeS_closed σ) _ _).symm⟩
  | withborSM σ c T hσ hT hΔ hc hcl he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withborSM σ c T hσ hT hΔ hc hcl he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 hcl _ _).symm⟩
  | withborSI σ c T hσ hT hΔ hc hcl he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withborSI σ c T hσ hT hΔ hc hcl he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 hcl _ _).symm⟩
  | withborF2M s hA hBo hTo he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withborF2M s hA hBo hTo he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | withborF2I s hA hB hBo hTo he hΓ =>
      intro Γa Γb Γp f hΓ' hf hp; subst hΓ'
      exact ⟨.withborF2I s hA hB hBo hTo he (dead_ins (live_eval_ff hf hp) Γa hΓ),
        (shift_closed0 (by rfl) _ _).symm⟩
  | litFn _ hb hcl ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.litFn d (by rw [e, hb, shift_closed0 hcl]) hcl, e⟩
  | divLit _ hb hs ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.divLit d (by rw [e]; exact divLitB_shift hb _ _) hs, e⟩
  | walk _ hb hr ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.walk d (by rw [e]; exact walkB_shift hb _ _)
        (fun h => by rw [e]; exact walkReadB_shift (hr h) _ _), e⟩
  | walkGet _ hb ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.walkGet d (by rw [e]; exact walkGetB_shift hb _ _), e⟩
  | selfCall _ hb ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.selfCall d (by rw [e]; exact selfCallB_shift hb _ _), e⟩
  | lendCell _ hb hm ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.lendCell d (by rw [e]; exact lendCellB_shift hb _ _) (by rw [lendKindB_shift]; exact hm), e⟩
  | lendScope _ hs hr ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.lendScope d (by rw [lendScopeT_shift]; exact hs) (by rw [lendRelT_shift]; exact hr), e⟩
  | litView _ hb ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.litView d (by rw [litViewT_shift]; exact hb), e⟩
  | unfoldStep _ hb ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.unfoldStep d (by rw [unfoldAppT_shift]; exact hb), e⟩
  | nuEta _ hb ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ hf hp
      exact ⟨.nuEta d (by rw [e]; exact nuEtaB_shift hb _ _), e⟩
  | use _ hab ih =>
      intro Γa Γb Γp f hΓ hf hp
      obtain ⟨d, e⟩ := ih Γa Γb Γp f hΓ (hab ▸ hf) hp
      exact ⟨.use d (hab.trans (TExpr.absF_shift _ _ _ _).symm), e⟩

/-! ### A `use` node projects to the inlined body -/

/-- **A `use` node projects to the derivation the inlining gave.** A `def`'s body `t`, typed at
`Γ`, placed at a use whose context has the slots `Γp` before `Γ` (`rUse`), is a `use` node typed at
the use's context; it erases to the body's erasure with its free variables moved past `Γp`, which
is the term a check of the body at the use's own context gives; and its derivation projects to
one of that term there.  `[spec §10, §19]` -/
theorem TDerivesAt.use_projects {Ξ : EffCtx} {Δ : LifeCtx} {Γ Γp : Ctx VTy} {t : TExpr} {j : Jdg}
    {f : AbsF} (i : TInfo) (name : String) (decl : Nat) (targs : List VTy)
    (h : TDerivesAt Ξ Δ Γ t j) (hf : t.absF Δ = some f) (hp : LiveP f.eval Γp) :
    TDerivesAt Ξ Δ (Γp ++ Γ) (.use i j name decl targs (some f) (t.shift Γp.length 0)) j ∧
      (TExpr.use i j name decl targs (some f) (t.shift Γp.length 0)).erase =
        t.erase.shift Γp.length 0 ∧
      CDerivesAt Ξ Δ (Γp ++ Γ) (t.erase.shift Γp.length 0) j := by
  obtain ⟨d, e⟩ := h.weaken [] Γ Γp f rfl hf hp
  simp only [List.nil_append, List.length_nil] at d e
  have du : TDerivesAt Ξ Δ (Γp ++ Γ) (.use i j name decl targs (some f) (t.shift Γp.length 0)) j :=
    .use d (by rw [TExpr.absF_shift, hf])
  exact ⟨du, e, e ▸ d.erase⟩

/-- **A `use` node projects to the derivation the inlining gave**, in `CDerivesP`.  `[spec §29]` -/
theorem TDerivesP.use_projects {Δ : LifeCtx} {Γ Γp : Ctx VTy} {t : TExpr} {j : Jdg} {f : AbsF}
    (i : TInfo) (name : String) (decl : Nat) (targs : List VTy) (h : TDerivesP Δ Γ t j)
    (hf : t.absF Δ = some f) (hp : LiveP f.eval Γp) :
    TDerivesP Δ (Γp ++ Γ) (.use i j name decl targs (some f) (t.shift Γp.length 0)) j ∧
      (TExpr.use i j name decl targs (some f) (t.shift Γp.length 0)).erase =
        t.erase.shift Γp.length 0 ∧
      CDerivesP Δ (Γp ++ Γ) (t.erase.shift Γp.length 0) j := by
  obtain ⟨d, e⟩ := h.weaken [] Γ Γp f rfl hf hp
  simp only [List.nil_append, List.length_nil] at d e
  have du : TDerivesP Δ (Γp ++ Γ) (.use i j name decl targs (some f) (t.shift Γp.length 0)) j :=
    .use d (by rw [TExpr.absF_shift, hf])
  exact ⟨du, e, e ▸ d.erase⟩

end BoCa.Fig16.LogRel.Core.Check
