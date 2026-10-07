import ProbeD1.Mono

/-!
# ProbeD1 — the callback's own lend: `MonoOwnG` (statement 0, the first per-placement fact)

`MonoOwnG p` carries a context across the stack the callback's own lend pushes (DESIGN §4.1). The
push is named by the type's binder, not by a future's name, so it is no future of the stack
(DESIGN §2.2, *The own lend*).

* **What holds at every placement** (`monoOwnV_uFree`, `monoOwnG_uFree`): at a slot whose type
  reaches no `U` through the formers W reads componentwise, the transport is the leaves' reading at
  the pushed stack, which agrees with the old one at the slot's free variables (`CtxFresh`,
  `vC_extend_of_not_free`, `interp_extend_of_not_mentions`).
* **What holds at a push named by a future's name** (`ownPush_futStep`, `monoOwnGNs_of_monoG`):
  when the pushed variable is `NsVar` and new to the reading substitution, the push is the one-step
  future at depth `0` (`OwnOK` gives `FutOK`'s fields), and the transport is `MonoG`'s instance
  there. So at `cbpv` and `binder` the transport holds at such a push (`monoOwnGNs_cbpv`,
  `monoOwnGNs_binder`).
* **What is not derived.** At a thunk slot `g : U C₁` and a push named by a program binder, `g`'s
  `U` clause owes `g`'s body at every future of the pushed stack, the pushed stack itself
  included. No such stack is a future of the old one (the pushed variable is not `NsVar`), and
  `g`'s clause gives its body only at the old stack's futures and, at `cbpv`, at `C₁`'s own pushes,
  which are named by `C₁`'s binder, not by the context's. The transport would need `g`'s forced
  body carried along the push itself (`MonoC` along a non-future insertion). At `⊸` that reads the
  argument back at the old stack, under the old stack's guard, which is stronger than the pushed
  stack's (`TabAtS σ` fails at a resource holding a cell at the pushed place). This holds at every
  placement, for the one reason the design names (DESIGN §4.3, §12.3): our `Fut` has no step for a
  binder-named entry. I have not derived it and have not verified that any obstruction is real.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS)

/-! ### At a slot whose type reaches no `U` -/

/-- A value type reaches no `U` through the formers W's relation reads componentwise (`⊗`, `⊕`,
`!`, `[@a]`, `Ref`); its other formers are leaves read by the kernel's `vC`. -/
def UFree : VTy → Prop
  | .thunk _ => False
  | .tensor A B => UFree A ∧ UFree B
  | .sum A B => UFree A ∧ UFree B
  | .bang A => UFree A
  | .box _ A => UFree A
  | .ref A => UFree A
  | _ => True

/-- The pushed stack's substitution reads every variable but the pushed one as the stack's does. -/
theorem extS_push_find (δ : LSub) (e : LEnt) (σ : LStack) (a : Life) (αs : List Life) {y : LifeVar}
    (hy : e.x ≠ y) : (extS δ (e :: σ) (a :: αs)).find? y = (extS δ σ αs).find? y :=
  find?_extend_ne _ _ hy

/-- **The transport across the own push at a slot reaching no `U`**, at every placement. -/
theorem monoOwnV_uFree (p : Placement) (e : LEnt) (a : Life) : ∀ (A : VTy), UFree A →
    ¬ VFree e.x A → ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (v : Val)
    (ρ : WRes), vRL p σ δ A αs ls v ρ → vRL p (e :: σ) δ A (a :: αs) ls v ρ
  | .tensor A B, hu, hx, σ, δ, αs, ls, v, ρ, h => by
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      exact ⟨v₁, v₂, pure_sep_mk rfl ⟨ρ₁, ρ₂, hc,
        monoOwnV_uFree p e a A hu.1 (fun h' => hx (Or.inl h')) σ δ αs ls v₁ ρ₁ h₁,
        monoOwnV_uFree p e a B hu.2 (fun h' => hx (Or.inr h')) σ δ αs ls v₂ ρ₂ h₂⟩⟩
  | .sum A B, hu, hx, σ, δ, αs, ls, v, ρ, h => by
      rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
      · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hs
        exact Or.inl ⟨v₁, pure_sep_mk rfl
          (monoOwnV_uFree p e a A hu.1 (fun h' => hx (Or.inl h')) σ δ αs ls v₁ ρ h₁)⟩
      · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hs
        exact Or.inr ⟨v₂, pure_sep_mk rfl
          (monoOwnV_uFree p e a B hu.2 (fun h' => hx (Or.inr h')) σ δ αs ls v₂ ρ h₂)⟩
  | .bang A, hu, hx, σ, δ, αs, ls, v, ρ, h => by
      obtain ⟨rfl, h₁⟩ := h
      exact ⟨rfl, monoOwnV_uFree p e a A hu hx σ δ αs ls v _ h₁⟩
  | .box b A, hu, hx, σ, δ, αs, ls, v, ρ, h => by
      obtain ⟨α, hα, hP, hO⟩ := h
      have hint : b.interp (extS δ (e :: σ) (a :: αs)) = b.interp (extS δ σ αs) := by
        show b.interp ((extS δ σ αs).extend e.x a) = _
        exact interp_extend_of_not_mentions (by
          cases hb : b.mentions e.x
          · rfl
          · exact absurd (Or.inl hb) hx)
      exact ⟨α, hint.trans hα, monoOwnV_uFree p e a A hu (fun h' => hx (Or.inr h')) σ δ αs ls v ρ hP,
        hO⟩
  | .ref A, hu, hx, σ, δ, αs, ls, v, ρ, h => by
      obtain ⟨ℓ, v', hs⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρ₁, ρ₂, hc, h₁,
        monoOwnV_uFree p e a A hu hx σ δ αs ls v' ρ₂ h₂⟩⟩
  | .unit, _, hx, σ, δ, αs, ls, v, ρ, h => by
      show vC true _ ls ((extS δ σ αs).extend e.x a) v ρ
      rw [vC_extend_of_not_free hx]; exact h
  | .zero, _, hx, σ, δ, αs, ls, v, ρ, h => by
      show vC true _ ls ((extS δ σ αs).extend e.x a) v ρ
      rw [vC_extend_of_not_free hx]; exact h
  | .imm _ _, _, hx, σ, δ, αs, ls, v, ρ, h => by
      show vC true _ ls ((extS δ σ αs).extend e.x a) v ρ
      rw [vC_extend_of_not_free hx]; exact h
  | .mut _ _, _, hx, σ, δ, αs, ls, v, ρ, h => by
      show vC true _ ls ((extS δ σ αs).extend e.x a) v ρ
      rw [vC_extend_of_not_free hx]; exact h
  | .unk, _, hx, σ, δ, αs, ls, v, ρ, h => by
      show vC true _ ls ((extS δ σ αs).extend e.x a) v ρ
      rw [vC_extend_of_not_free hx]; exact h
  | .tvar _, _, hx, σ, δ, αs, ls, v, ρ, h => by
      show vC true _ ls ((extS δ σ αs).extend e.x a) v ρ
      rw [vC_extend_of_not_free hx]; exact h
  | .mu _, _, hx, σ, δ, αs, ls, v, ρ, h => by
      show vC true _ ls ((extS δ σ αs).extend e.x a) v ρ
      rw [vC_extend_of_not_free hx]; exact h
  | .int _, _, hx, σ, δ, αs, ls, v, ρ, h => by
      show vC true _ ls ((extS δ σ αs).extend e.x a) v ρ
      rw [vC_extend_of_not_free hx]; exact h
  | .fam _, _, hx, σ, δ, αs, ls, v, ρ, h => by
      show vC true _ ls ((extS δ σ αs).extend e.x a) v ρ
      rw [vC_extend_of_not_free hx]; exact h
  | .opq _, _, hx, σ, δ, αs, ls, v, ρ, h => by
      show vC true _ ls ((extS δ σ αs).extend e.x a) v ρ
      rw [vC_extend_of_not_free hx]; exact h

/-- **`MonoOwnG` at a context whose live slots reach no `U`**, at every placement. -/
theorem monoOwnG_uFree (p : Placement) {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec}
    (e : LEnt) (a : Life) : ∀ (Γ : Ctx VTy) (γ : List Val) (ρ : WRes),
    (∀ s ∈ Γ, s.live = true → UFree s.ty) → CtxFresh e.x Γ →
    gRL p σ δ αs ls Γ γ ρ → gRL p (e :: σ) δ (a :: αs) ls Γ γ ρ := by
  intro Γ γ ρ hu hfr hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  refine pure_sep_mk hlw ?_
  clear hlw hg
  induction Γ generalizing γ ρ with
  | nil => exact hgs
  | cons s Γ ih =>
      cases γ with
      | nil => exact hgs
      | cons v γ =>
          have hu' : ∀ s' ∈ Γ, s'.live = true → UFree s'.ty :=
            fun s' hs' hl => hu s' (List.mem_cons_of_mem _ hs') hl
          have hfr' : CtxFresh e.x Γ := fun s' hs' hl => hfr s' (List.mem_cons_of_mem _ hs') hl
          by_cases hl : s.live = true
          · simp only [gSepRL, hl, if_true] at hgs ⊢
            obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := hgs
            exact ⟨ρ₁, ρ₂, hc, monoOwnV_uFree p e a s.ty (hu s List.mem_cons_self hl)
              (hfr s List.mem_cons_self hl).1 σ δ αs ls v ρ₁ h₁, ih γ ρ₂ hu' hfr' h₂⟩
          · simp only [gSepRL, hl] at hgs ⊢
            exact ih γ ρ hu' hfr' hgs

/-! ### At a push named by a future's name -/

/-- **The own push at a future's name is a one-step future**: its entry, named by an `NsVar` new to
the reading substitution, meets `FutOK` at depth `0` from `OwnOK`. -/
theorem ownPush_futStep {δ : LSub} {C : CTy} {ρ : WRes} {σ : LStack} {αs : List Life} {e : LEnt}
    {a : Life} (hpush : OwnPush δ C ρ (σ, αs) e a) (hns : NsVar e.x) (hδ : δ.find? e.x = none) :
    FutStep δ ρ (σ, αs) (e :: σ, a :: αs) := by
  obtain ⟨x, c, C', -, -, -, hown, -⟩ := hpush
  refine ⟨0, [e], [a], none, ?_, fun e' he' => by rw [List.mem_singleton.mp he']; exact hns, ?_, ?_⟩
  · exact
      { len := rfl
        depth_le := Nat.zero_le _
        chain := by simpa [futL] using hown.chain
        below := fun b hb => by rw [List.mem_singleton.mp hb]; exact hown.below
        vars_stack := fun e' he' => by rw [List.mem_singleton.mp he']; exact hown.var
        vars_sub := fun e' he' => by
          rw [List.mem_singleton.mp he']
          rw [extS_find_not_mem δ σ αs e.x hown.var]; exact hδ
        nodup := List.nodup_singleton _
        places := fun e' he' => by rw [List.mem_singleton.mp he']; exact hown.place
        pay := fun e' he' y hy => by
          rw [List.mem_singleton.mp he'] at hy
          simpa [futL] using hown.pay y hy }
  · show e :: σ = σ.take 0 ++ [e] ++ σ.drop 0
    simp
  · show a :: αs = futL 0 [a] αs
    simp [futL]

/-- **`MonoOwnG` at a push named by a future's name**: `MonoOwnG` with the pushed variable `NsVar`
and new to the reading substitution. -/
def MonoOwnGNs (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    StackOK σ αs → OwnPush δ C ρ (σ, αs) e a → NsVar e.x → δ.find? e.x = none →
    CtxFresh e.x Γ → TabAtS σ αs ρ →
    gRL p σ δ αs ls Γ γ ρ → gRL p (e :: σ) δ (a :: αs) ls Γ γ ρ

/-- **At a push named by a future's name the transport is `MonoG`'s instance.** -/
theorem monoOwnGNs_of_monoG (p : Placement) (hG : MonoG (ℍ := ℍ) p) : MonoOwnGNs (ℍ := ℍ) p := by
  intro σ δ Γ γ αs ls ρ C e a hok hpush hns hδ hfr ht hg
  have hvar : e.x ∉ σ.map LEnt.x := by
    obtain ⟨_, _, _, -, -, -, hown, -⟩ := hpush; exact hown.var
  refine hG σ δ Γ γ αs ls ls ρ (e :: σ) (a :: αs) hok (Ext.refl ls ρ)
    (Relation.ReflTransGen.single (ownPush_futStep hpush hns hδ)) ?_ ht hg
  intro s hs hl e' he' hx
  rcases List.mem_cons.mp he' with rfl | he'
  · exact hfr s hs hl
  · exact absurd (List.mem_map_of_mem he') hx

theorem monoOwnGNs_cbpv : MonoOwnGNs (ℍ := ℍ) .cbpv := monoOwnGNs_of_monoG .cbpv monoG_cbpv

theorem monoOwnGNs_binder : MonoOwnGNs (ℍ := ℍ) .binder := monoOwnGNs_of_monoG .binder monoG_binder

end ProbeD1

end
