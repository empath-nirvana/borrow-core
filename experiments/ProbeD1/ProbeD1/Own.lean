import ProbeD1.Mono

/-!
# ProbeD1 — the callback's own lend: `MonoOwnG` (statement 0, the first per-placement fact)

`MonoOwnG p` carries a context across the stack the callback's own lend pushes (DESIGN §4.1). The
push is named by the type's binder.

* **The push is a future** (`ownPush_futStep`). A step's inserted variables are any new to the
  stack and to the reading substitution (`FutStep`), so the push of an entry whose variable is new
  to `δ` is the one-step future at depth `0`: `OwnOK` gives `FutOK`'s fields. `MonoOwnG` is
  `MonoG`'s instance there (`monoOwnG_of_monoG`), and holds at `cbpv` and `binder`
  (`monoOwnG_cbpv`, `monoOwnG_binder`). It takes `δ.find? e.x = none`, which is `FutOK.vars_sub`
  at the push (DESIGN §4.3: "`vars_sub` follows from `SubDom` and the binder new to `Δ`").
* **Why the futures' names are not restricted to `NsVar`.** With every inserted variable a name no
  program binds, a binder-named push is no future. At a thunk slot `g : U C₁`, `g`'s `U` clause
  owes `g`'s body at every future of the pushed stack, the pushed stack itself included, and gives
  it only at the old stack's futures (and, at `cbpv`, at `C₁`'s own pushes, named by `C₁`'s
  binder). The transport would then need `g`'s forced body carried along the push itself (`MonoC`
  along a non-future insertion), which at `⊸` reads the argument back at the old stack under the
  old stack's stronger guard. That is the case DESIGN §13 step 2 admits such names for.
* **At `binder0`** the `U` clause ranges over the stack itself, so the transport at a thunk slot
  needs `MonoG binder0`, hence `MonoC binder0` along the push. Not derived.
* **At every placement**, at a context reaching no `U` (`monoOwnG_uFree`): the leaves' reading at
  the pushed stack agrees with the old one at the slot's free variables (`CtxFresh`).
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

/-! ### The push as a future: `MonoOwnG` at `cbpv` and `binder` -/

/-- **The own push is a one-step future**: its entry, its variable new to the reading
substitution, meets `FutOK` at depth `0` from `OwnOK`. -/
theorem ownPush_futStep {δ : LSub} {C : CTy} {ρ : WRes} {σ : LStack} {αs : List Life} {e : LEnt}
    {a : Life} (hpush : OwnPush δ C ρ (σ, αs) e a) (hδ : δ.find? e.x = none) :
    FutStep δ ρ (σ, αs) (e :: σ, a :: αs) := by
  obtain ⟨x, c, C', -, -, -, hown, -⟩ := hpush
  refine ⟨0, [e], [a], none, ?_, ?_, ?_⟩
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

/-- **`MonoOwnG` is `MonoG`'s instance at the one-step future the push is.** -/
theorem monoOwnG_of_monoG (p : Placement) (hG : MonoG (ℍ := ℍ) p) : MonoOwnG (ℍ := ℍ) p := by
  intro σ δ Γ γ αs ls ρ C e a hok hpush hδ hfr ht hg
  refine hG σ δ Γ γ αs ls ls ρ (e :: σ) (a :: αs) hok (Ext.refl ls ρ)
    (Relation.ReflTransGen.single (ownPush_futStep hpush hδ)) ?_ ht hg
  intro s hs hl e' he' hx
  rcases List.mem_cons.mp he' with rfl | he'
  · exact hfr s hs hl
  · exact absurd (List.mem_map_of_mem he') hx

/-- **`MonoOwnG` at `cbpv`.** -/
theorem monoOwnG_cbpv : MonoOwnG (ℍ := ℍ) .cbpv := monoOwnG_of_monoG .cbpv monoG_cbpv

/-- **`MonoOwnG` at `binder`.** -/
theorem monoOwnG_binder : MonoOwnG (ℍ := ℍ) .binder := monoOwnG_of_monoG .binder monoG_binder

end ProbeD1

end
