import ProbeD1.R1Stmt0

/-!
# ProbeD1 — `[allI]` at `binder0`: what the row reads beside monotonicity (`R1MONO.md` §2.6)

`AllIRowMOfMonoOwnGM` (`R1.lean`) plans the row from `MonoOwnGM` alone. Carrying the premise to the
two places the `∀` clause asks it shows two more facts the row reads, each about the context's
reading, and one class of index where its first conjunct does not reach the premise:

* **The first conjunct reads the premise at the reading extended at the binder** (`δ.extend x α`),
  so the context must move there (`CtxExtendMAt`). At a `U` slot `vRLM` reads the reading as a
  whole: the `∀` clause's own lend is fresh below every value of the reading (`SubFresh δ α`), so
  a binding new to the stack strengthens that hypothesis, and a `U` slot whose argument type holds
  a `∀` is read at the extended reading over more arguments. Not derived at a `U` slot; no
  obstruction verified.
* **The own-lend conjunct reads it at the pushed stack and the reading extended at the pushed
  variable**, so after the push (`MonoOwnGMAt`) the context must move to that reading, which the
  stack shadows at the pushed variable (`CtxShadowMAt`). Not derived at a `U` slot; no obstruction
  verified.
* **At an index whose stack holds an entry named by the binder** (`StackJ`'s third kind) the first
  conjunct's premise needs `SubOutside` at the extended reading, which `subOutsideExtend` gives
  only for a binder new to the stack, and which fails in general (`not_subOutsideExtendAny`).

`allIRowMNKAt0_of` proves the row at `binder0` at one context from the three transports at that
context, at every index whose stack does not name the binder (`AllIRowMNKAt`): the premise at the
two places, every index fact carried (`StackJ` to the extended `Δ`, the models, `SubOutside` by
`subOutsideExtend` and `subOutsidePush`), and the β step in front of every computation type
(`cRLM_step`). At a context whose live slots reach no `U` the three transports hold
(`monoOwnGMAt_uFree`, `ctxExtendMAt_uFree`, `ctxShadowMAt_uFree`), so the row holds there
(`allIRowMNKUFree0`), the empty context among them (`allIRowMNKNil0`).

At `gd`, whose context is a `U` slot, the row's conclusion holds at a derivable body that hands
`gdF` a thunk holding the argument and forces what comes back (`gdMtDerivable`,
`gdAllIHoldsAtMt`), at the own lend's pushed stack included, where `MonoOwnGM` fails
(`notMonoOwnGM0`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty innerView rowTab
  bodyS OpenS)
open BoCa.BoLo (Step1N Head Heap Kont)

/-! ### The statements -/

/-- **`MonoOwnGM` at one context**, the pushed variable read in no entry's payload type
(`StackPayAvoids`; the row has it at every index it reads, `stackPayAvoids_of_stackJ`). -/
def MonoOwnGMAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (C : CTy) (e : LEnt) (a : Life),
    StackPayAvoids e.x σ →
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    RecsOutside (a :: αs) ls → SubFresh δ a →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ

/-- **The context at the reading extended at a variable new to the stack and the reading**, free
and bound in no live slot, read in no entry's payload type. -/
def CtxExtendMAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (x : LifeVar) (α : Life),
    x ∉ σ.map LEnt.x → δ.find? x = none → StackPayAvoids x σ →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty ∧ x ∉ VTy.binders s.ty) →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ (δ.extend x α) αs ls Γ γ ρ

/-- `CtxExtendMAt` at every context. -/
def CtxExtendM (p : Placement) : Prop := ∀ Γ, CtxExtendMAt (ℍ := ℍ) p Γ

/-- **The context after the own lend's push, at the reading extended at the pushed variable at the
pushed lifetime**: the stack reads the variable at that lifetime already. -/
def CtxShadowMAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (e : LEnt) (α : Life),
    δ.find? e.x = none → (∀ s ∈ Γ, s.live = true → ¬ VFree e.x s.ty ∧ e.x ∉ VTy.binders s.ty) →
    gRLM (ℍ := ℍ) p (e :: σ) δ (α :: αs) ls Γ γ ρ →
      gRLM (ℍ := ℍ) p (e :: σ) (δ.extend e.x α) (α :: αs) ls Γ γ ρ

/-- `CtxShadowMAt` at every context. -/
def CtxShadowM (p : Placement) : Prop := ∀ Γ, CtxShadowMAt (ℍ := ℍ) p Γ

/-- `SemSM` at the indices whose stack does not name the variable `x`. -/
def SemSMNK (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) (x : LifeVar) :
    Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    x ∉ σ.map LEnt.x →
    StackOK σ αs → OuterBelowTop αs → StackJ σ αs δ Δ Γ (jdgCty j) → SubDom δ Δ →
    Δ.Models (extS δ σ αs) → RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ →
    cRLM (ℍ := ℍ) p σ δ (jdgCty j) αs ls (substAll γ e) ρ

/-- **`[allI]` at `SemSM` at one context, its conclusion at the indices whose stack does not name
the binder.** -/
def AllIRowMNKAt (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (M : Expr) (S : VTy) (C : CTy),
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → Δ.find? x = none →
    (∀ s ∈ Γ, s.live = true → x ∉ VTy.binders s.ty) →
    SemSM (ℍ := ℍ) p (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C) →
    SemSMNK (ℍ := ℍ) p Δ Γ (.val (.lam M)) (.comp (.all x b C)) x

/-- `AllIRowMNKAt` at every context. -/
def AllIRowMNK (p : Placement) : Prop := ∀ Γ, AllIRowMNKAt (ℍ := ℍ) p Γ

/-- **`SubOutside` along a binding is not kept in general**: an entry named by the bound variable
has every binding of the old reading before it. Only for a variable new to the stack
(`subOutsideExtend`). -/
theorem not_subOutsideExtendAny :
    ¬ ∀ (σ : LStack) (αs : List Life) (δ : LSub) (x : LifeVar) (α : Life),
      SubOutside σ αs δ → SubOutside σ αs (δ.extend x α) := by
  intro h
  have h₀ : SubOutside [⟨0, 0, .unit, .mut, fun _ => true⟩] [lifeN 5] ⟨[(1, 9)]⟩ := by
    intro e a he p hp
    obtain ⟨rfl, rfl⟩ : e = ⟨0, 0, .unit, .mut, fun _ => true⟩ ∧ a = lifeN 5 := by
      simpa using he
    simp [boundBefore] at hp
  have := h _ _ _ 0 (lifeN 3) h₀ ⟨0, 0, .unit, .mut, fun _ => true⟩ (lifeN 5)
    (List.mem_singleton_self _) (1, 9) (by simp [boundBefore, LSub.extend])
  exact absurd this (by decide)

/-! ### A pure step in front of every computation type -/

/-- **`cRLM` is closed under a pure step in front**, at every computation type: `wpTS_step` at `F`,
`wpG_step` at a row, Core's `cC_step` at `ν`, the step under the application at `⊸`, `&` and
`∀`. -/
theorem cRLM_step (p : Placement) : ∀ (C : CTy) {e e' : Expr}, (∀ μ : Heap, Step1N μ e μ e') →
    ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec),
      Entails (cRLM (ℍ := ℍ) p σ δ C αs ls e') (cRLM (ℍ := ℍ) p σ δ C αs ls e)
  | .ret _, _, _, h, _, _, _, ls => wpTS_step h ls _
  | .eff _ _ _ _ _ _, _, _, h, σ, δ, αs, ls => by
      intro ρ h'
      unfold cRLM at h' ⊢
      split at h' <;> rename_i hsf <;> simp only [hsf, if_true] <;>
        exact wpG_step h ls _ ρ h'
  | .arr _ D, _, _, h, σ, δ, αs, ls => fun ρ h' ls' σ' αs' he hf hav v ρ₁ ρ₂ hv hc ht hpv =>
      cRLM_step p D (fun μ => (h μ).plug (Kont.appL .hole v)) σ' δ αs' ls' ρ₂
        (h' ls' σ' αs' he hf hav v ρ₁ ρ₂ hv hc ht hpv)
  | .amp C D, _, _, h, σ, δ, αs, ls => fun ρ ⟨h₁, h₂⟩ =>
      ⟨cRLM_step p C (fun μ => (h μ).plug (Kont.appL .hole _)) σ δ αs ls ρ h₁,
       cRLM_step p D (fun μ => (h μ).plug (Kont.appL .hole _)) σ δ αs ls ρ h₂⟩
  | .top, _, _, _, _, _, _, _ => fun _ _ => trivial
  | .all x c C, _, _, h, σ, δ, αs, ls => fun ρ h' ls' σ' αs' he hf hav => by
      obtain ⟨h₁, h₂⟩ := h' ls' σ' αs' he hf hav
      refine ⟨fun α ρ₁ ρ₂ hp hc ht hpv => ?_, fun hown en α hpush hro hsf ht hpv => ?_⟩
      · exact cRLM_step p C (fun μ => (h μ).plug (Kont.appL .hole _)) σ' (δ.extend x α) αs' ls' ρ₂
          (h₁ α ρ₁ ρ₂ hp hc ht hpv)
      · exact cRLM_step p C (fun μ => (h μ).plug (Kont.appL .hole _)) (en :: σ') (δ.extend x α)
          (α :: αs') ls' ρ (h₂ hown en α hpush hro hsf ht hpv)
  | .nu C, _, _, h, σ, δ, αs, ls => cC_step (.nu C) h ls (extS δ σ αs)


/-! ### The index facts at the premise's two indices -/

theorem bindersLow_allBody {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life} {C : CTy} {S : VTy}
    (h : BindersLow Γ (.all x b C)) : BindersLow (⟨S, false⟩ :: Γ) C := by
  refine ⟨fun y hy => h.1 y (by simp [CTy.binders, hy]), fun s hs hl => ?_⟩
  rcases List.mem_cons.mp hs with rfl | hs
  · simp at hl
  · exact h.2 s hs hl

theorem lifeCtx_find?_extend_some {Δ : LifeCtx} {y : LifeVar} {u : Lifetime.Life}
    (h : Δ.find? y = some u) (x : LifeVar) (b : Lifetime.Life) :
    ∃ u', (Δ.extend x b).find? y = some u' := by
  rw [LifeCtx.find?_extend]
  split
  · exact ⟨b, rfl⟩
  · exact ⟨u, h⟩

theorem scoped_allBody {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life} {C : CTy}
    {S : VTy} (h : Scoped Δ Γ (.all x b C)) : Scoped (Δ.extend x b) (⟨S, false⟩ :: Γ) C := by
  refine ⟨fun y hy => ?_, fun s hs hl => ?_⟩
  · by_cases hyx : x = y
    · subst hyx; exact ⟨b, by rw [LifeCtx.find?_extend, if_pos rfl]⟩
    · obtain ⟨u, hu⟩ := h.1 y (Or.inr ⟨Ne.symm hyx, hy⟩)
      exact lifeCtx_find?_extend_some hu x b
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · intro y hy
      obtain ⟨u, hu⟩ := h.2 s hs hl y hy
      exact lifeCtx_find?_extend_some hu x b

theorem subDom_extend {δ : LSub} {Δ : LifeCtx} (h : SubDom δ Δ) (x : LifeVar) (α : Life)
    (b : Lifetime.Life) : SubDom (δ.extend x α) (Δ.extend x b) := by
  intro y hy
  by_cases hyx : x = y
  · subst hyx; exact ⟨b, by rw [LifeCtx.find?_extend, if_pos rfl]⟩
  · rw [find?_extend_ne δ α hyx] at hy
    obtain ⟨u, hu⟩ := h y hy
    exact lifeCtx_find?_extend_some hu x b

/-- The stack's entries at the binder's body: `Δ`'s or names no program binds, at the extended
`Δ`, when the binder is new to the stack. -/
theorem stackJ_kinds_allBody {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx} {Γ : Ctx VTy}
    {x : LifeVar} {b : Lifetime.Life} {C : CTy} {S : VTy} (h : StackJ σ αs δ Δ Γ (.all x b C))
    (hxσ : x ∉ σ.map LEnt.x) : ∀ e ∈ σ,
      (∃ u, (Δ.extend x b).find? e.x = some u) ∨
      (NsVar e.x ∧ (Δ.extend x b).find? e.x = none ∧ ¬ CFree e.x C ∧
        CtxAvoids e.x (⟨S, false⟩ :: Γ)) := by
  intro e he
  have hex : e.x ≠ x := fun h' => hxσ (h' ▸ List.mem_map_of_mem he)
  rcases h.2.2 e he with ⟨u, hu⟩ | ⟨hns, hΔ, hCe, hctx⟩ | ⟨-, -, -, c, D, hall, -⟩
  · exact Or.inl (lifeCtx_find?_extend_some hu x b)
  · refine Or.inr ⟨hns, ?_, fun hc => hCe (Or.inr ⟨hex, hc⟩), ctxAvoids_dead hctx⟩
    rw [LifeCtx.find?_extend, if_neg (Ne.symm hex)]; exact hΔ
  · obtain ⟨rfl, -, -⟩ : x = e.x ∧ b = c ∧ C = D := by simpa using hall
    exact absurd rfl hex

/-- **`StackJ` at the first conjunct's premise**, the binder new to the stack. -/
theorem stackJ_allExtend {σ : LStack} {αs : List Life} {δ δ' : LSub} {Δ : LifeCtx} {Γ : Ctx VTy}
    {x : LifeVar} {b : Lifetime.Life} {C : CTy} {S : VTy} (h : StackJ σ αs δ Δ Γ (.all x b C))
    (hxσ : x ∉ σ.map LEnt.x) :
    StackJ σ αs δ' (Δ.extend x b) (⟨S, false⟩ :: Γ) C := by
  refine ⟨h.1, fun e he y hy => ?_, fun e he => ?_⟩
  · rcases h.2.1 e he y hy with ⟨u, hu⟩ | hm
    · exact Or.inl (lifeCtx_find?_extend_some hu x b)
    · exact Or.inr hm
  · rcases stackJ_kinds_allBody (S := S) h hxσ e he with h₁ | h₂
    · exact Or.inl h₁
    · exact Or.inr (Or.inl h₂)

/-- **`StackJ` at the own-lend conjunct's premise**: the pushed entry is named by the binder, now
`Δ`'s; the old entries as at the first conjunct. -/
theorem stackJ_allPush {σ : LStack} {αs : List Life} {δ δ' : LSub} {Δ : LifeCtx} {Γ : Ctx VTy}
    {x : LifeVar} {b : Lifetime.Life} {C : CTy} {S : VTy} {en : LEnt} {α : Life} {ρ : WRes}
    (h : StackJ σ αs δ Δ Γ (.all x b C)) (hSD : SubDom δ Δ) (hex : en.x = x)
    (hoi : OwnOKI δ σ αs en α ρ) :
    StackJ (en :: σ) (α :: αs) δ' (Δ.extend x b) (⟨S, false⟩ :: Γ) C := by
  have hxσ : x ∉ σ.map LEnt.x := hex ▸ hoi.var
  refine ⟨by rw [List.map_cons]; exact List.nodup_cons.mpr ⟨hoi.var, h.1⟩,
    fun e he y hy => ?_, fun e he => ?_⟩
  · rcases List.mem_cons.mp he with rfl | he
    · have hb := hoi.pay y hy
      by_cases hyx : e.x = y
      · exact Or.inr (by rw [← hyx]; exact List.mem_cons_self)
      · rw [extS_push_find _ e σ α αs hyx] at hb
        by_cases hyσ : y ∈ σ.map LEnt.x
        · exact Or.inr (List.mem_cons_of_mem _ hyσ)
        · rw [extS_find_not_mem _ σ αs y hyσ] at hb
          obtain ⟨u, hu⟩ := hSD y hb
          exact Or.inl (lifeCtx_find?_extend_some hu x b)
    · rcases h.2.1 e he y hy with ⟨u, hu⟩ | h₁
      · exact Or.inl (lifeCtx_find?_extend_some hu x b)
      · exact Or.inr (List.mem_cons_of_mem _ h₁)
  · rcases List.mem_cons.mp he with rfl | he
    · exact Or.inl ⟨b, by rw [hex, LifeCtx.find?_extend, if_pos rfl]⟩
    · rcases stackJ_kinds_allBody (S := S) h hxσ e he with h₁ | h₂
      · exact Or.inl h₁
      · exact Or.inr (Or.inl h₂)

/-- **The extended `Δ`'s models at the first conjunct's premise**: `'x ↦ α` below `b`, the other
bounds read alike (none mentions `'x`). -/
theorem models_allExtend {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life} {x : LifeVar}
    {b : Lifetime.Life} {α : Life} (hMod : Δ.Models (extS δ σ αs)) (hxσ : x ∉ σ.map LEnt.x)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hlt : LtLife (extS δ σ αs) b α) :
    (Δ.extend x b).Models (extS (δ.extend x α) σ αs) := by
  have hagree : ∀ y, x ≠ y → (extS (δ.extend x α) σ αs).find? y = (extS δ σ αs).find? y :=
    fun y hyx => extS_find_base (find?_extend_ne δ α hyx) σ αs
  have hint : ∀ (u : Lifetime.Life), u.mentions x = false →
      u.interp (extS (δ.extend x α) σ αs) = u.interp (extS δ σ αs) :=
    fun u hu => interp_congr u (fun y hy => hagree y (fun he => by rw [he] at hu; simp [hu] at hy))
  intro y u hy
  rw [LifeCtx.find?_extend] at hy
  split at hy
  · rename_i hyx
    subst hyx
    have hub : b = u := Option.some.inj hy
    subst hub
    obtain ⟨β, hβ, hαβ⟩ := hlt
    refine ⟨α, β, ?_, by rw [hint b hbx]; exact hβ, hαβ⟩
    rw [extS_find_not_mem _ σ αs x hxσ, find?_extend_self]; rfl
  · rename_i hyx
    obtain ⟨m, n, hm, hn, hl⟩ := hMod y u hy
    exact ⟨m, n, by rw [hagree y hyx]; exact hm, by rw [hint u (hΔx y u hy)]; exact hn, hl⟩

/-- **The extended `Δ`'s models at the own-lend conjunct's premise**: the pushed entry reads `'x`
at its lifetime, below `b`. -/
theorem models_allPush {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life} {x : LifeVar}
    {b : Lifetime.Life} {en : LEnt} {α : Life} (hMod : Δ.Models (extS δ σ αs)) (hex : en.x = x)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hlt : LtLife (extS δ σ αs) b α) :
    (Δ.extend x b).Models (extS (δ.extend x α) (en :: σ) (α :: αs)) := by
  have hagree : ∀ y, x ≠ y →
      (extS (δ.extend x α) (en :: σ) (α :: αs)).find? y = (extS δ σ αs).find? y := by
    intro y hyx
    rw [extS_push_find _ en σ α αs (by rw [hex]; exact hyx)]
    exact extS_find_base (find?_extend_ne δ α hyx) σ αs
  have hint : ∀ (u : Lifetime.Life), u.mentions x = false →
      u.interp (extS (δ.extend x α) (en :: σ) (α :: αs)) = u.interp (extS δ σ αs) :=
    fun u hu => interp_congr u (fun y hy => hagree y (fun he => by rw [he] at hu; simp [hu] at hy))
  intro y u hy
  rw [LifeCtx.find?_extend] at hy
  split at hy
  · rename_i hyx
    subst hyx
    have hub : b = u := Option.some.inj hy
    subst hub
    obtain ⟨β, hβ, hαβ⟩ := hlt
    refine ⟨α, β, ?_, by rw [hint b hbx]; exact hβ, hαβ⟩
    show ((extS (δ.extend x α) σ αs).extend en.x α).find? x = some α
    rw [hex, find?_extend_self]
  · rename_i hyx
    obtain ⟨m, n, hm, hn, hl⟩ := hMod y u hy
    exact ⟨m, n, by rw [hagree y hyx]; exact hm, by rw [hint u (hΔx y u hy)]; exact hn, hl⟩


/-! ### The row at `binder0` at one context, from the three transports -/

/-- **`[allI]` at `binder0` at one context, at every index whose stack does not name the binder,
from the three transports at that context**: the `∀` clause's first conjunct by the premise at
the reading extended at the binder, the context moved there by `CtxExtendMAt`; its own-lend
conjunct by the premise at the pushed stack and the reading extended at the pushed variable, the
context carried across the push by `MonoOwnGMAt` and to that reading by `CtxShadowMAt`; the
index's facts by `stackJ_allExtend`, `stackJ_allPush`, `models_allExtend`, `models_allPush`,
`subOutsideExtend`, `subOutsidePush`, `outerBelowTopPush`; the β step by `cRLM_step`. -/
theorem allIRowMNKAt0_of (Γ : Ctx VTy) (hMono : MonoOwnGMAt (ℍ := ℍ) .binder0 Γ)
    (hExt : CtxExtendMAt (ℍ := ℍ) .binder0 Γ) (hSh : CtxShadowMAt (ℍ := ℍ) .binder0 Γ) :
    AllIRowMNKAt (ℍ := ℍ) .binder0 Γ := by
  intro Δ x b M S C hbx hΔx hΓx hΔ hΓb hM hBL hSc δ σ αs ls γ ρ hxσ hok hob hJ hSD hMod hro hso
    ht hpv hg
  have hδx : δ.find? x = none := by
    cases h : δ.find? x with
    | none => rfl
    | some m =>
        obtain ⟨u, hu⟩ := hSD x (by rw [h]; simp)
        rw [hΔ] at hu; exact absurd hu (by simp)
  have hσx : StackPayAvoids x σ := stackPayAvoids_of_stackJ hJ hΔ hxσ
  have hslots : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty ∧ x ∉ VTy.binders s.ty :=
    fun s hs hl => ⟨hΓx s hs hl, hΓb s hs hl⟩
  have hBL' := bindersLow_allBody (S := S) hBL
  have hSc' := scoped_allBody (S := S) hSc
  show cRLM .binder0 σ δ (.all x b C) αs ls (.val (.lam (Expr.psub 1 γ M))) ρ
  intro ls' σ' αs' hE hF _
  have hE' : ls' = ls := by simpa [ExtQ, Placement.bindFut] using hE
  have hF' : σ' = σ ∧ αs' = αs := by simpa [FutQI, Placement.bindFut] using hF
  obtain ⟨rfl, rfl⟩ := hF'
  subst hE'
  refine ⟨fun α ρ₁ ρ₂ hp hc ht' hpv' => ?_, fun _ en α hpush hro' hsf ht' hpv' => ?_⟩
  · -- the first conjunct: the premise at the reading extended at the binder
    obtain ⟨rfl, hlt⟩ := hp
    rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ)] at ht' hpv' ⊢
    refine cRLM_step .binder0 C (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) σ'
      (δ.extend x α) αs' ls' ρ ?_
    rw [← GhostEnd.substAll_cons_l]
    exact hM hBL' hSc' (δ.extend x α) σ' αs' ls' (Val.unit :: γ) ρ hok hob
      (stackJ_allExtend hJ hxσ) (subDom_extend hSD x α b)
      (models_allExtend hMod hxσ hbx hΔx hlt) hro (subOutsideExtend σ' αs' δ x α hxσ hso) ht'
      hpv' (gRLM_dead_cons (hExt σ' δ γ αs' ls' ρ x α hxσ hδx hσx hslots hg))
  · -- the own-lend conjunct: the premise at the pushed stack
    obtain ⟨x', c', C', hall, hex, hbind, hoi, hlt, hview⟩ := hpush
    obtain ⟨rfl, rfl, rfl⟩ : x = x' ∧ b = c' ∧ C = C' := by simpa using hall
    have hpush : OwnPushI δ (.all x b C) ρ (σ', αs') en α :=
      ⟨x, b, C, rfl, hex, hbind, hoi, hlt, hview⟩
    have hδen : δ.find? en.x = none := by rw [hex]; exact hδx
    have hfr : CtxFresh en.x Γ := fun s hs hl => by rw [hex]; exact hslots s hs hl
    have hσen : StackPayAvoids en.x σ' := by rw [hex]; exact hσx
    have hg₁ := hMono σ' δ γ αs' ls' ρ (.all x b C) en α hσen hok hob hro hso hpush hδen hfr hro'
      hsf ht hpv hg
    have hg₂ := hSh σ' δ γ αs' ls' ρ en α hδen (fun s hs hl => hfr s hs hl) hg₁
    rw [hex] at hg₂
    refine cRLM_step .binder0 C (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) (en :: σ')
      (δ.extend x α) (α :: αs') ls' ρ ?_
    rw [← GhostEnd.substAll_cons_l]
    have hokP : StackOK (en :: σ') (α :: αs') :=
      ⟨by simp [hok.1], hoi.chain, by rw [List.map_cons]; exact List.nodup_cons.mpr ⟨hoi.var, hok.2.2⟩⟩
    exact hM hBL' hSc' (δ.extend x α) (en :: σ') (α :: αs') ls' (Val.unit :: γ) ρ hokP
      (outerBelowTopPush αs' α _ b hob hlt) (stackJ_allPush hJ hSD hex hoi)
      (subDom_extend hSD x α b) (models_allPush hMod hex hbx hΔx hlt) hro'
      (by rw [← hex]; exact subOutsidePush σ' αs' δ en α hoi.var hso hsf) ht' hpv'
      (gRLM_dead_cons hg₂)

/-! ### The three transports at a context whose live slots reach no `U`

At such a context `vRLM` reads the reading only through the stack's (`extS`), and there only at
the free variables of the slot's type, of the environment's types and of the entries' payload
types: Core's leaf by `vC_congr`, `CohS`'s `TyEq` by `TyEq.of_agree`, `RetainedPay` and a box's
bound at their variables. `MonoOwnGM` itself is refuted at `binder0` (`notMonoOwnGM0`), at a `U`
slot; at a context reaching no `U` the push is `monoOwnGUFreeMA`. -/

/-- **A value reaching no `U` at two readings that agree wherever it, the environment's types or
the entries' payload types read.** -/
theorem vRLM_reading_uFree (p : Placement) : ∀ (A : VTy) (η : Option (Nat → WEnt))
    (σ : LStack) (δ₁ δ₂ : LSub) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    UFreeM A →
    (∀ y, (VFree y A ∨ ∃ n, VFree y (wEnv η n).ty) →
      (extS δ₁ σ αs).find? y = (extS δ₂ σ αs).find? y) →
    (∀ e ∈ σ, ∀ y, VFree y e.T → (extS δ₁ σ αs).find? y = (extS δ₂ σ αs).find? y) →
    vRLM (ℍ := ℍ) p η σ δ₁ A αs ls v ρ → vRLM (ℍ := ℍ) p η σ δ₂ A αs ls v ρ := by
  intro A
  induction A using VTy.recV with
  | thunk C => intro _ _ _ _ _ _ _ _ hu; exact hu.elim
  | tensor A B ihA ihB =>
      intro η σ δ₁ δ₂ αs ls v ρ hu hag hagE h
      obtain ⟨v₁, v₂, hsep⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hsep
      exact ⟨v₁, v₂, pure_sep_mk rfl ⟨ρ₁, ρ₂, hc,
        ihA η σ δ₁ δ₂ αs ls v₁ ρ₁ hu.1
          (fun y hy => hag y (hy.imp (fun h' => Or.inl h') id)) hagE h₁,
        ihB η σ δ₁ δ₂ αs ls v₂ ρ₂ hu.2
          (fun y hy => hag y (hy.imp (fun h' => Or.inr h') id)) hagE h₂⟩⟩
  | sum A B ihA ihB =>
      intro η σ δ₁ δ₂ αs ls v ρ hu hag hagE h
      rcases h with ⟨v₁, hsep⟩ | ⟨v₂, hsep⟩
      · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hsep
        exact Or.inl ⟨v₁, pure_sep_mk rfl (ihA η σ δ₁ δ₂ αs ls v₁ ρ hu.1
          (fun y hy => hag y (hy.imp (fun h' => Or.inl h') id)) hagE h₁)⟩
      · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hsep
        exact Or.inr ⟨v₂, pure_sep_mk rfl (ihB η σ δ₁ δ₂ αs ls v₂ ρ hu.2
          (fun y hy => hag y (hy.imp (fun h' => Or.inr h') id)) hagE h₂)⟩
  | bang A ih =>
      intro η σ δ₁ δ₂ αs ls v ρ hu hag hagE h
      exact ⟨h.1, ih η σ δ₁ δ₂ αs ls v ρ hu hag hagE h.2⟩
  | box b A ih =>
      intro η σ δ₁ δ₂ αs ls v ρ hu hag hagE h
      obtain ⟨α, hα, hv, hout⟩ := h
      refine ⟨α, ?_, ih η σ δ₁ δ₂ αs ls v ρ hu
        (fun y hy => hag y (hy.imp (fun h' => Or.inr h') id)) hagE hv, hout⟩
      rw [← interp_congr b (fun y hy => hag y (Or.inl (Or.inl hy)))]
      exact hα
  | ref A ih =>
      intro η σ δ₁ δ₂ αs ls v ρ hu hag hagE h
      obtain ⟨ℓ, v', hsep⟩ := h
      obtain ⟨rfl, ρo, ρa, hc, hown, ha⟩ := pure_sep_iff.mp hsep
      exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρo, ρa, hc, hown,
        ih η σ δ₁ δ₂ αs ls v' ρa hu hag hagE ha⟩⟩
  | «mut» b T _ =>
      intro η σ δ₁ δ₂ αs ls v ρ _ hag hagE h
      rw [vRLM_mut_eq, vRLJ_mut_eq] at h ⊢
      obtain ⟨hvc, hcoh, hpay⟩ := h
      have hagT : ∀ y, VFree y (.mut b (wClose η T)) →
          (extS δ₁ σ αs).find? y = (extS δ₂ σ αs).find? y := by
        rintro y (hm | hT)
        · exact hag y (Or.inl (Or.inl hm))
        · rw [wClose_eq] at hT
          rcases vFree_subst T _ hT with hT | ⟨n, hn⟩
          · exact hag y (Or.inl (Or.inr hT))
          · exact hag y (Or.inr ⟨n, hn⟩)
      refine ⟨by rw [← vC_congr _ hagT]; exact hvc, fun l e α hl hi => ?_,
        fun l hl hi y hy m hm => hpay l hl hi y hy m (by rw [hagT y (Or.inr hy)]; exact hm)⟩
      obtain ⟨hk, hat⟩ := hcoh l e α hl hi
      have he : e ∈ σ := (List.of_mem_zip (innerAt_mem hi).1).1
      exact ⟨⟨hk.1, (TyEq.of_agree _ (fun y hy => (hagT y (Or.inr hy)).symm)).trans
        (hk.2.trans (TyEq.of_agree e.T (fun y hy => hagE e he y hy)))⟩, hat⟩
  | imm b T _ =>
      intro η σ δ₁ δ₂ αs ls v ρ _ hag hagE h
      rw [vRLM_imm_eq, vRLJ_imm_eq] at h ⊢
      obtain ⟨hvc, hcoh, hpay⟩ := h
      have hagT : ∀ y, VFree y (.imm b (wClose η T)) →
          (extS δ₁ σ αs).find? y = (extS δ₂ σ αs).find? y := by
        rintro y (hm | hT)
        · exact hag y (Or.inl (Or.inl hm))
        · rw [wClose_eq] at hT
          rcases vFree_subst T _ hT with hT | ⟨n, hn⟩
          · exact hag y (Or.inl (Or.inr hT))
          · exact hag y (Or.inr ⟨n, hn⟩)
      refine ⟨by rw [← vC_congr _ hagT]; exact hvc, fun l e α hl hi => ?_,
        fun l hl hi y hy m hm => hpay l hl hi y hy m (by rw [hagT y (Or.inr hy)]; exact hm)⟩
      obtain ⟨hk, hat⟩ := hcoh l e α hl hi
      have he : e ∈ σ := (List.of_mem_zip (innerAt_mem hi).1).1
      exact ⟨⟨hk.1, (TyEq.of_agree _ (fun y hy => (hagT y (Or.inr hy)).symm)).trans
        (hk.2.trans (TyEq.of_agree e.T (fun y hy => hagE e he y hy)))⟩, hat⟩
  | unit =>
      intro η σ δ₁ δ₂ αs ls v ρ _ _ _ h
      show vC true .unit ls (extS δ₂ σ αs) v ρ
      rw [vC_congr .unit (δ₂ := extS δ₁ σ αs) (fun y hy => hy.elim)]; exact h
  | int w =>
      intro η σ δ₁ δ₂ αs ls v ρ _ _ _ h
      show vC true (.int w) ls (extS δ₂ σ αs) v ρ
      rw [vC_congr (.int w) (δ₂ := extS δ₁ σ αs) (fun y hy => hy.elim)]; exact h
  | opq k =>
      intro η σ δ₁ δ₂ αs ls v ρ _ _ _ h
      show vC true (.opq k) ls (extS δ₂ σ αs) v ρ
      rw [vC_congr (.opq k) (δ₂ := extS δ₁ σ αs) (fun y hy => hy.elim)]; exact h
  | unk =>
      intro η σ δ₁ δ₂ αs ls v ρ _ _ _ h
      show vC true .unk ls (extS δ₂ σ αs) v ρ
      rw [vC_congr .unk (δ₂ := extS δ₁ σ αs) (fun y hy => hy.elim)]; exact h
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ h; exact h.elim
  | tvar n => intro _ _ _ _ _ _ _ _ _ _ _ h; exact h
  | fam L ih =>
      intro η σ δ₁ δ₂ αs ls v ρ hu hag hagE h
      obtain ⟨ℓ, c, hsep⟩ := h
      obtain ⟨⟨rfl, hcn⟩, hs⟩ := pure_sep_iff.mp hsep
      exact ⟨ℓ, c, pure_sep_mk ⟨rfl, hcn⟩
        (sepRange_mono' (fun m τ hm => ih η σ δ₁ δ₂ αs ls (.loc m) τ hu hag hagE hm) hs)⟩
  | mu A ih =>
      intro η σ δ₁ δ₂ αs ls v ρ hu hag hagE h
      obtain ⟨hnm, hcl, hlfp⟩ := h
      refine ⟨hnm, hcl, fun P hP => hlfp P (fun v' ρ' h' => hP v' ρ' ?_)⟩
      refine ih _ σ δ₁ δ₂ αs ls v' ρ' hu (fun y hy => ?_) hagE h'
      rcases hy with hy | ⟨n, hn⟩
      · exact hag y (Or.inl hy)
      · cases n with
        | zero =>
            change VFree y (wClose η (.mu A)) at hn
            rw [wClose_eq] at hn
            rcases vFree_subst (.mu A) _ hn with hn | ⟨m, hm⟩
            · exact hag y (Or.inl hn)
            · exact hag y (Or.inr ⟨m, hm⟩)
        | succ n => exact hag y (Or.inr ⟨n, hn⟩)

/-- **A context reaching no `U` at two readings that agree wherever its live slots or the entries'
payload types read.** -/
theorem gRLM_reading_uFree (p : Placement) {σ : LStack} {δ₁ δ₂ : LSub} {αs : List Life}
    {ls : List SRec} : ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes},
    (∀ s ∈ Γ, s.live = true → UFreeM s.ty) →
    (∀ s ∈ Γ, s.live = true → ∀ y, VFree y s.ty →
      (extS δ₁ σ αs).find? y = (extS δ₂ σ αs).find? y) →
    (∀ e ∈ σ, ∀ y, VFree y e.T → (extS δ₁ σ αs).find? y = (extS δ₂ σ αs).find? y) →
    gRLM (ℍ := ℍ) p σ δ₁ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ δ₂ αs ls Γ γ ρ := by
  intro Γ γ ρ hU hag hagE hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  refine pure_sep_mk hlw ?_
  clear hlw hg
  induction Γ generalizing γ ρ with
  | nil => cases γ <;> exact hgs
  | cons s Γ ih =>
      cases γ with
      | nil => exact hgs
      | cons v γ =>
          have hU' : ∀ s' ∈ Γ, s'.live = true → UFreeM s'.ty :=
            fun s' hs' hl => hU s' (List.mem_cons_of_mem _ hs') hl
          have hag' : ∀ s' ∈ Γ, s'.live = true → ∀ y, VFree y s'.ty →
              (extS δ₁ σ αs).find? y = (extS δ₂ σ αs).find? y :=
            fun s' hs' hl => hag s' (List.mem_cons_of_mem _ hs') hl
          by_cases hl : s.live = true
          · simp only [gSepRLM, hl, if_true] at hgs ⊢
            obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := hgs
            refine ⟨ρ₁, ρ₂, hc, vRLM_reading_uFree p s.ty none σ δ₁ δ₂ αs ls v ρ₁
              (hU s List.mem_cons_self hl) (fun y hy => ?_) hagE h₁, ih hU' hag' h₂⟩
            rcases hy with hy | ⟨n, hn⟩
            · exact hag s List.mem_cons_self hl y hy
            · exact hn.elim
          · simp only [gSepRLM, hl] at hgs ⊢
            exact ih hU' hag' hgs

/-- **`CtxExtendMAt` at a context reaching no `U`**: the extended reading agrees with the old one
off the new variable, which no live slot and no entry's payload type reads. -/
theorem ctxExtendMAt_uFree (p : Placement) (Γ : Ctx VTy)
    (hU : ∀ s ∈ Γ, s.live = true → UFreeM s.ty) : CtxExtendMAt (ℍ := ℍ) p Γ := by
  intro σ δ γ αs ls ρ x α _ _ hσx hslots hg
  have hag : ∀ y, x ≠ y → (extS δ σ αs).find? y = (extS (δ.extend x α) σ αs).find? y :=
    fun y hyx => (extS_find_base (find?_extend_ne δ α hyx) σ αs).symm
  exact gRLM_reading_uFree p hU
    (fun s hs hl y hy => hag y (fun he => (hslots s hs hl).1 (he ▸ hy)))
    (fun e he y hy => hag y (fun hxy => hσx e he (hxy ▸ hy))) hg

/-- **`CtxShadowMAt` at a context reaching no `U`**: the stack reads the pushed variable at the
pushed lifetime, so the two readings agree everywhere. -/
theorem ctxShadowMAt_uFree (p : Placement) (Γ : Ctx VTy)
    (hU : ∀ s ∈ Γ, s.live = true → UFreeM s.ty) : CtxShadowMAt (ℍ := ℍ) p Γ := by
  intro σ δ γ αs ls ρ e α _ _ hg
  have hag : ∀ y, (extS δ (e :: σ) (α :: αs)).find? y =
      (extS (δ.extend e.x α) (e :: σ) (α :: αs)).find? y := by
    intro y
    by_cases hxy : e.x = y
    · subst hxy
      show ((extS δ σ αs).extend e.x α).find? e.x = ((extS (δ.extend e.x α) σ αs).extend e.x α).find? e.x
      rw [find?_extend_self, find?_extend_self]
    · rw [extS_push_find _ e σ α αs hxy, extS_push_find _ e σ α αs hxy]
      exact (extS_find_base (find?_extend_ne δ α hxy) σ αs).symm
  exact gRLM_reading_uFree p hU (fun _ _ _ y _ => hag y) (fun _ _ y _ => hag y) hg

/-- **`MonoOwnGMAt` at a context reaching no `U`**: `monoOwnGUFreeMA`. -/
theorem monoOwnGMAt_uFree (p : Placement) (Γ : Ctx VTy)
    (hU : ∀ s ∈ Γ, s.live = true → UFreeM s.ty) : MonoOwnGMAt (ℍ := ℍ) p Γ :=
  fun σ δ γ αs ls ρ C e a hσ hok hob hro hso hpush hδ hfr hro' hsf ht hpv hg =>
    monoOwnGUFreeMA p σ δ Γ γ αs ls ρ C e a hσ hU hok hob hro hso hpush hδ hfr hro' hsf ht hpv hg

/-- **`[allI]` at `binder0` at every context whose live slots reach no `U`**, at every index whose
stack does not name the binder: `allIRowMNKAt0_of` with the three transports at such a context. -/
theorem allIRowMNKUFree0 (Γ : Ctx VTy) (hU : ∀ s ∈ Γ, s.live = true → UFreeM s.ty) :
    AllIRowMNKAt (ℍ := ℍ) .binder0 Γ :=
  allIRowMNKAt0_of Γ (monoOwnGMAt_uFree .binder0 Γ hU) (ctxExtendMAt_uFree .binder0 Γ hU)
    (ctxShadowMAt_uFree .binder0 Γ hU)

/-- **`[allI]` at `binder0` at the empty context**, at every index whose stack does not name the
binder. -/
theorem allIRowMNKNil0 : AllIRowMNKAt (ℍ := ℍ) .binder0 [] :=
  allIRowMNKUFree0 [] (fun _ hs => absurd hs List.not_mem_nil)

/-! ### The row's conclusion at `gd`, at a derivable body that exercises the closure

`gdM` (`R1.lean`) applies `f` to a thunk literal, which `app` does not take (it takes a variable),
so `GdMDerivable` is not proved. `gdMt` binds the thunk first and is derived from `CDerivesNU`'s
rules (`gdMtDerivable`). At `gd`'s index the row's conclusion holds at it (`gdAllIHoldsAtMt`): at
both conjuncts of the `∀` clause, the argument at `Imm '2 1` is a single `imm` cell, `gdF` hands the
thunk holding it back, the thunk forgets it, and `()` holds nothing; the cell goes to the garbage
(`wpTS_frame_noOwn`, as 6.149). The run never reads `gdF`'s relation, so the box at `'1` that
`GdNotPushed` turns on is never asked. -/

/-- **A derivable body that hands `gdF` a thunk holding the argument**:
`λr. let t = thunk (forget r) in let g = f t in let h = return g in force h`, at the premise's
context `_ : 1, f : gdTy` (under `λr`: `r` is `0`, the dead slot `1`, `f` is `2`). -/
abbrev gdMt : Expr :=
  .val (.lam (elet (.val (.lam (.app forget (.var 1))))
    (elet (.app (.var 3) (.var 0))
      (elet (.var 0) (.app (.var 0) (.val .unit))))))

/-- `gdMt` after `gd`'s closing substitution and the `∀`'s β step: `f` is `gdF`. -/
abbrev gdMtS : Expr :=
  .val (.lam (elet (.val (.lam (.app forget (.var 1))))
    (elet (.app (.val gdF) (.var 0))
      (elet (.var 0) (.app (.var 0) (.val .unit))))))

/-- A judgement of `CDerivesNU` is one of the probe's rule set (`Tier1SubNU`). -/
theorem probeRules_of_nu {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : Targets.CDerivesNU Δ Γ e j) : ProbeRules Δ Γ e j :=
  fun _ _ hE _ _ _ => hE.1 [] Δ (fun _ => Γ) e (fun _ => j) (fun _ _ => h)

/-- **`gdMt` is derivable at the premise's judgement**: `forget` at `Imm '2 1` under the thunk's
dead binder, the thunk bound, `f` forced (`forceE` at an `⊸` type is the variable itself) and
applied to it, the answer unboxed (`boxE`) and bound, and forced. -/
theorem gdMtDerivable :
    ProbeRules (gdΔ.extend 2 (.var 1)) (⟨.unit, false⟩ :: gdΓ) gdMt (.comp gdCyBody) := by
  refine probeRules_of_nu (.lam ?_)
  refine .bind (A := gdArg) (.left (.dead (.right .nil))) (.ret (.thunkF (A := .unit) (.ret ?_))) ?_
  · exact .lolliE (.dead (.left (.dead (.dead .nil))))
      (.var (.there (.here (.cons (.cons .nil))))) (.forgetImm (.cons (.cons (.cons (.cons .nil)))))
  · refine .bind (A := .box (.var 1) gdArg) (.left (.dead (.dead (.left .nil))))
      (.app (.right (.dead (.dead (.left .nil))))
        (.force (C := gdC) (.there (.there (.there (.here .nil)))))
        (.here (.cons (.cons (.cons .nil))))) ?_
    exact .bind (A := gdArg) (.left (.dead (.dead (.dead (.dead .nil)))))
      (.ret (.boxE (.var (.here (.cons (.cons (.cons (.cons .nil))))))))
      (.force (C := .ret .unit) (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))

/-- **The run of `gdMtS` at a location over a resource with no `own` cell**: five β steps, `gdF`
handing the thunk back in argument position, then `forget`; the resource goes to the garbage. -/
theorem gdMtS_run {ls : List SRec} {Q : List SRec → Val → WProp} {l : BoCa.Loc} {ρ : WRes}
    (hρ : NoOwn ρ) (hQ : Q ls .unit PMap.empty) :
    wpTS (ℍ := ℍ) ls (.app gdMtS (.val (.loc l))) Q ρ := by
  let t : Val := Val.lam (.app forget (.val (.loc l)))
  let B₄ : Expr := .app (.var 0) (.val .unit)
  let B₃ : Expr := elet (.var 0) B₄
  let B₂ : Expr := elet (.app (.val gdF) (.var 0)) B₃
  refine wpTS_lolli ls (elet (.val (.lam (.app forget (.var 1)))) B₂) (.loc l) Q ρ ?_
  refine wpTS_lolli ls B₂ t Q ρ ?_
  show wpTS ls (Kont.plug (.appR (.val (.lam B₃)) .hole) (.app (.val gdF) (.val t))) Q ρ
  refine wpTS_bind _ _ ls Q ρ ?_
  refine wpTS_lolli ls (.var 0) t _ ρ ?_
  refine wpTS_val ls t _ ρ ?_
  refine wpTS_lolli ls B₃ t Q ρ ?_
  refine wpTS_lolli ls B₄ t Q ρ ?_
  refine wpTS_lolli ls (.app forget (.val (.loc l))) .unit Q ρ ?_
  refine wpTS_lolli ls unit' (.loc l) Q ρ ?_
  exact wpTS_frame_noOwn (R := fun ρ' => ρ' = ρ) (fun _ h => h ▸ hρ) ls _ Q ρ
    ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, rfl, wpTS_val ls .unit Q PMap.empty hQ⟩

/-- **`gdMtS` is related at `gdCyBody` at every index, over nothing**: every argument at `Imm 'v 1`
is a location over a single `imm` cell, and the run answers `()` over nothing. -/
theorem gdMtS_cRLM (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    cRLM (ℍ := ℍ) .binder0 σ δ gdCyBody αs ls gdMtS PMap.empty := by
  intro ls' σ' αs' _ _ _ v ρa ρb hv hc _ _
  rw [eq_of_compS_empty_left hc]
  rw [vRLM_imm_eq, vRLJ_imm_eq] at hv
  obtain ⟨hvc, -, -⟩ := hv
  obtain ⟨α, -, ℓ, hsep⟩ := hvc
  obtain ⟨⟨rfl, -⟩, S, u, χ, hχ, ls₀, hρ, -⟩ := pure_sep_iff.mp hsep
  exact gdMtS_run (by rw [hρ]; exact ResU.restrict_single_other (by simp)) ⟨rfl, rfl⟩

/-- **At `gd`'s index the `∀I` row's conclusion holds at `gdMt`**: both conjuncts of the `∀`
clause reduce to `gdMtS` at `gdCyBody` (`gdMtS_cRLM`), at `gdσ` and at the pushed stack alike. -/
theorem gdAllIHoldsAtMt : GdAllIConclAt (ℍ := ℍ) gdMt := by
  show cRLM .binder0 gdσ gdδ gdCy gdαs gdls (.val (.lam (Expr.psub 1 gdγ gdMt))) PMap.empty
  intro ls' σ' αs' hE hF _
  have hE' : ls' = gdls := by simpa [ExtQ, Placement.bindFut] using hE
  have hF' : σ' = gdσ ∧ αs' = gdαs := by simpa [FutQI, Placement.bindFut] using hF
  obtain ⟨rfl, rfl⟩ := hF'
  subst hE'
  refine ⟨fun α ρ₁ ρ₂ hp hc _ _ => ?_, fun _ en α _ _ _ _ _ => ?_⟩
  · obtain ⟨rfl, -⟩ := hp
    rw [ResU.CompS.functional hc (ResU.comp_empty_right _)]
    exact cRLM_step .binder0 gdCyBody (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) _ _ _ _
      _ (gdMtS_cRLM _ _ _ _)
  · exact cRLM_step .binder0 gdCyBody (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) _ _ _ _
      _ (gdMtS_cRLM _ _ _ _)

end ProbeD1

end
