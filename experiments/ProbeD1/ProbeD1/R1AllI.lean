import ProbeD1.R1Stmt0

/-!
# ProbeD1 — `[allI]` at `binder0`: what the row reads beside monotonicity (`R1MONO.md` §2.6)

`AllIRowMOfMonoOwnGM` (`R1.lean`) plans the row from `MonoOwnGM` alone. Carrying the premise to the
two places the `∀` clause asks it shows two more facts the row reads, each about the context's
reading:

* **The first conjunct reads the premise at the reading extended at the binder** (`δ.extend x α`),
  so the context must move there (`CtxExtendM`). `vRLM` reads the reading as a whole at one
  place: the `∀` clause's own lend is fresh below every value of the reading (`SubFresh δ α`,
  `BinderJ.lean`'s own-lend conjunct), so a binding new to the stack strengthens that hypothesis,
  and a `U` slot whose argument type holds a `∀` is read at the extended reading over more
  arguments. Not derived; no obstruction verified.
* **The own-lend conjunct reads it at the pushed stack and the reading extended at the pushed
  variable** (`δ.extend x α` with `x` the pushed entry's), so after `MonoOwnGM` the context must
  move to that reading, which the stack shadows at `x` (`CtxShadowM`). Not derived; no obstruction
  verified.
* **At an index whose stack holds an entry named by the binder** (`StackJ`'s third kind) the first
  conjunct's premise needs `SubOutside` at the extended reading, which `subOutsideExtend` gives
  only for a binder new to the stack, and which fails in general (`not_subOutsideExtendAny`).

`allIRowMNK0_of` proves the row at `binder0` from `MonoOwnGM`, `CtxExtendM` and `CtxShadowM`, at
every index whose stack does not name the binder (`AllIRowMNK`). Its proof is the row's: the
premise at the two places, every index fact carried (`StackJ` to the extended `Δ`, the models,
`SubOutside` by `subOutsideExtend` and `subOutsidePush`), and the β step in front of every
computation type (`cRLM_step`).
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

/-- **The context at the reading extended at a variable new to the stack and the reading**, free
and bound in no live slot, read in no entry's payload type. -/
def CtxExtendM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (x : LifeVar) (α : Life),
    x ∉ σ.map LEnt.x → δ.find? x = none → StackPayAvoids x σ →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty ∧ x ∉ VTy.binders s.ty) →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ (δ.extend x α) αs ls Γ γ ρ

/-- **The context after the own lend's push, at the reading extended at the pushed variable at the
pushed lifetime**: the stack reads the variable at that lifetime already. -/
def CtxShadowM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (e : LEnt) (α : Life),
    δ.find? e.x = none → (∀ s ∈ Γ, s.live = true → ¬ VFree e.x s.ty ∧ e.x ∉ VTy.binders s.ty) →
    gRLM (ℍ := ℍ) p (e :: σ) δ (α :: αs) ls Γ γ ρ →
      gRLM (ℍ := ℍ) p (e :: σ) (δ.extend e.x α) (α :: αs) ls Γ γ ρ

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

/-- **`[allI]` at `SemSM`, its conclusion at the indices whose stack does not name the binder.** -/
def AllIRowMNK (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (b : Lifetime.Life) (M : Expr) (S : VTy) (C : CTy),
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → Δ.find? x = none →
    (∀ s ∈ Γ, s.live = true → x ∉ VTy.binders s.ty) →
    SemSM (ℍ := ℍ) p (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C) →
    SemSMNK (ℍ := ℍ) p Δ Γ (.val (.lam M)) (.comp (.all x b C)) x

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


/-! ### The row at `binder0`, from the three transports -/

/-- **`[allI]` at `binder0`, at every index whose stack does not name the binder, from
`MonoOwnGM`, `CtxExtendM` and `CtxShadowM`**: the `∀` clause's first conjunct by the premise at
the reading extended at the binder, the context moved there by `CtxExtendM`; its own-lend
conjunct by the premise at the pushed stack and the reading extended at the pushed variable, the
context carried across the push by `MonoOwnGM` and to that reading by `CtxShadowM`; the index's
facts by `stackJ_allExtend`, `stackJ_allPush`, `models_allExtend`, `models_allPush`,
`subOutsideExtend`, `subOutsidePush`, `outerBelowTopPush`; the β step by `cRLM_step`. -/
theorem allIRowMNK0_of (hMono : MonoOwnGM (ℍ := ℍ) .binder0) (hExt : CtxExtendM (ℍ := ℍ) .binder0)
    (hSh : CtxShadowM (ℍ := ℍ) .binder0) : AllIRowMNK (ℍ := ℍ) .binder0 := by
  intro Δ Γ x b M S C hbx hΔx hΓx hΔ hΓb hM hBL hSc δ σ αs ls γ ρ hxσ hok hob hJ hSD hMod hro hso
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
      hpv' (gRLM_dead_cons (hExt σ' δ Γ γ αs' ls' ρ x α hxσ hδx hσx hslots hg))
  · -- the own-lend conjunct: the premise at the pushed stack
    obtain ⟨x', c', C', hall, hex, hbind, hoi, hlt, hview⟩ := hpush
    obtain ⟨rfl, rfl, rfl⟩ : x = x' ∧ b = c' ∧ C = C' := by simpa using hall
    have hpush : OwnPushI δ (.all x b C) ρ (σ', αs') en α :=
      ⟨x, b, C, rfl, hex, hbind, hoi, hlt, hview⟩
    have hδen : δ.find? en.x = none := by rw [hex]; exact hδx
    have hfr : CtxFresh en.x Γ := fun s hs hl => by rw [hex]; exact hslots s hs hl
    have hg₁ := hMono σ' δ Γ γ αs' ls' ρ (.all x b C) en α hok hob hro hso hpush hδen hfr hro' hsf
      ht hpv hg
    have hg₂ := hSh σ' δ Γ γ αs' ls' ρ en α hδen (fun s hs hl => hfr s hs hl) hg₁
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

end ProbeD1

end
