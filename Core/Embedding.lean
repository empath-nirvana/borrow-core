import Core.Fundamental
import Support.Statics.Presupposed

/-!
# Core — the call-by-value embedding of BoLo  `[spec §3]`

`cbv : Ty → VTy` is the call-by-value translation of BoLo types: `T₁ ⊸ T₂ ↦ U (T₁⁺ ⊸ F T₂⁺)`
(`VTy.lolli`), `∀'x ⊏ @b. T ↦ U (∀'x ⊏ @b. F T⁺)` (`VTy.all`), every other former to its
namesake.  `cbvCtx` translates a context slot by slot.

`embed` sends a derivation of BoLo's `DerivesWf Δ Γ e T` to a derivation of
`CDerives Δ (cbvCtx Γ) e (.val (cbv T))` on the same term, under `Δ.Ok` and `Ctx.ScopedB Δ Γ`
(the hypotheses of the typed world's Fundamental Property, `Typed.fundamental`).
`adequacy_of_derivesWf` runs every closed BoLo program of type `1` to `()` from the empty
memory, through `adequacyC`.

The facts along `cbv`: it keeps free lifetime variables (`lFree_iff_vFree`), `lifeBound`
(`cbv_lifeBound`), substitution (`cbv_applyLSub`, `cbv_instLife`), `Imm̲` (`cbv_immReborrow`),
the axiom types (`cbv_axSwapTy`, …), outlives (`vOutlives_cbv`) and scoping (`vScoped_cbv`);
`cbvCtx` keeps `Ctx.Dead`, `Ctx.Solo`, `Ctx.Split`, `!Γ` and `Δ ⊨ Γ ⊐ @a`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar LSubst)

/-- The call-by-value translation of BoLo types.  `[spec §3]` -/
def cbv : Ty → VTy
  | .unit => .unit
  | .unk => .unk
  | .sum T₁ T₂ => .sum (cbv T₁) (cbv T₂)
  | .tensor T₁ T₂ => .tensor (cbv T₁) (cbv T₂)
  | .lolli T₁ T₂ => .lolli (cbv T₁) (cbv T₂)
  | .ref T => .ref (cbv T)
  | .bang T => .bang (cbv T)
  | .imm a T => .imm a (cbv T)
  | .mut a T => .mut a (cbv T)
  | .box a T => .box a (cbv T)
  | .all x b T => .all x b (cbv T)

/-- The call-by-value translation of a context, slot by slot. -/
def cbvCtx (Γ : Ctx Ty) : Ctx VTy := Γ.map fun s => ⟨cbv s.ty, s.live⟩

/-! ### Types -/

/-- The translation keeps the free lifetime variables. -/
theorem lFree_iff_vFree (x : LifeVar) : ∀ T : Ty, LFree x T ↔ VFree x (cbv T)
  | .unit => Iff.rfl
  | .unk => Iff.rfl
  | .sum A B => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A, lFree_iff_vFree x B]
  | .tensor A B => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A, lFree_iff_vFree x B]
  | .lolli A B => by
      simp only [LFree, VFree, CFree, cbv, VTy.lolli, lFree_iff_vFree x A, lFree_iff_vFree x B]
  | .ref A => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A]
  | .bang A => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A]
  | .imm a A => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A]
  | .mut a A => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A]
  | .box a A => by simp only [LFree, VFree, cbv, lFree_iff_vFree x A]
  | .all y b A => by simp only [LFree, VFree, CFree, cbv, VTy.all, lFree_iff_vFree x A]

theorem cbv_lifeBound : ∀ T : Ty, (cbv T).lifeBound = T.lifeBound
  | .unit => rfl
  | .unk => rfl
  | .sum A B => by simp only [cbv, VTy.lifeBound, Ty.lifeBound, cbv_lifeBound A, cbv_lifeBound B]
  | .tensor A B => by
      simp only [cbv, VTy.lifeBound, Ty.lifeBound, cbv_lifeBound A, cbv_lifeBound B]
  | .lolli A B => by
      simp only [cbv, VTy.lolli, VTy.lifeBound, CTy.lifeBound, Ty.lifeBound, cbv_lifeBound A,
        cbv_lifeBound B]
  | .ref A => by simp only [cbv, VTy.lifeBound, Ty.lifeBound, cbv_lifeBound A]
  | .bang A => by simp only [cbv, VTy.lifeBound, Ty.lifeBound, cbv_lifeBound A]
  | .imm a A => by simp only [cbv, VTy.lifeBound, Ty.lifeBound, cbv_lifeBound A]
  | .mut a A => by simp only [cbv, VTy.lifeBound, Ty.lifeBound, cbv_lifeBound A]
  | .box a A => by simp only [cbv, VTy.lifeBound, Ty.lifeBound, cbv_lifeBound A]
  | .all y b A => by
      simp only [cbv, VTy.all, VTy.lifeBound, CTy.lifeBound, Ty.lifeBound, cbv_lifeBound A]

/-- The translation commutes with capture-avoiding lifetime substitution: both rename a `∀`
binder under the same condition, to the same variable (`cbv_lifeBound`). -/
theorem cbv_applyLSub : ∀ (T : Ty) (σ : LSubst), cbv (T.applyLSub σ) = (cbv T).applyLSub σ
  | .unit, _ => rfl
  | .unk, _ => rfl
  | .sum A B, σ => by
      simp only [Ty.applyLSub, cbv, VTy.applyLSub, cbv_applyLSub A, cbv_applyLSub B]
  | .tensor A B, σ => by
      simp only [Ty.applyLSub, cbv, VTy.applyLSub, cbv_applyLSub A, cbv_applyLSub B]
  | .lolli A B, σ => by
      simp only [Ty.applyLSub, cbv, VTy.lolli, VTy.applyLSub, CTy.applyLSub, cbv_applyLSub A,
        cbv_applyLSub B]
  | .ref A, σ => by simp only [Ty.applyLSub, cbv, VTy.applyLSub, cbv_applyLSub A]
  | .bang A, σ => by simp only [Ty.applyLSub, cbv, VTy.applyLSub, cbv_applyLSub A]
  | .imm a A, σ => by simp only [Ty.applyLSub, cbv, VTy.applyLSub, cbv_applyLSub A]
  | .mut a A, σ => by simp only [Ty.applyLSub, cbv, VTy.applyLSub, cbv_applyLSub A]
  | .box a A, σ => by simp only [Ty.applyLSub, cbv, VTy.applyLSub, cbv_applyLSub A]
  | .all y b A, σ => by
      show cbv (Ty.applyLSub σ (.all y b A)) = .thunk ((CTy.all y b (.ret (cbv A))).applyLSub σ)
      cases h : lsubCaptures (lsubDrop σ y) y
      · rw [CTy.applyLSub_all_not_captures h]
        simp only [Ty.applyLSub, h, Bool.false_eq_true, if_false, cbv, VTy.all, CTy.applyLSub,
          cbv_applyLSub A]
      · rw [CTy.applyLSub_all_captures h]
        simp only [Ty.applyLSub, h, if_true, cbv, VTy.all, CTy.applyLSub, CTy.lifeBound,
          cbv_lifeBound A, cbv_applyLSub A]

theorem cbv_instLife (x : LifeVar) (a : Lifetime.Life) (T : Ty) :
    cbv (Ty.instLife x a T) = (cbv T).instLife x a :=
  cbv_applyLSub T [(x, a)]

theorem cbv_immReborrow (b : Lifetime.Life) : ∀ T : Ty,
    cbv (T.immReborrow b) = (cbv T).immReborrow b
  | .unit => rfl
  | .unk => rfl
  | .sum A B => by
      simp only [Ty.immReborrow, cbv, VTy.immReborrow, cbv_immReborrow b A, cbv_immReborrow b B]
  | .tensor A B => by
      simp only [Ty.immReborrow, cbv, VTy.immReborrow, cbv_immReborrow b A, cbv_immReborrow b B]
  | .lolli _ _ => rfl
  | .ref _ => rfl
  | .bang _ => rfl
  | .imm _ _ => rfl
  | .mut _ _ => rfl
  | .box _ A => by simp only [Ty.immReborrow, cbv, VTy.immReborrow, cbv_immReborrow b A]
  | .all _ _ _ => rfl

/-! ### The axiom types -/

theorem cbv_axSwapTy (T₁ T₂ : Ty) : cbv (BoCa.axSwapTy T₁ T₂) = axSwapTy (cbv T₁) (cbv T₂) := rfl
theorem cbv_axCopyTy (a : Lifetime.Life) (T : Ty) :
    cbv (BoCa.axCopyTy a T) = axCopyTy a (cbv T) := rfl
theorem cbv_axForgetImmTy (a : Lifetime.Life) (T : Ty) :
    cbv (BoCa.axForgetImmTy a T) = axForgetImmTy a (cbv T) := rfl
theorem cbv_axForgetMutTy (a : Lifetime.Life) (T : Ty) :
    cbv (BoCa.axForgetMutTy a T) = axForgetMutTy a (cbv T) := rfl
theorem cbv_axForgetUnkTy : cbv BoCa.axForgetUnkTy = axForgetUnkTy := rfl
theorem cbv_axWithbor1Ty (x : LifeVar) (bnd : Lifetime.Life) (T₁ T₂ : Ty) :
    cbv (BoCa.axWithbor1Ty x bnd T₁ T₂) = axWithbor1Ty x bnd (cbv T₁) (cbv T₂) := rfl
theorem cbv_axWithbor2Ty (x : LifeVar) (bnd : Lifetime.Life) (T₁ T₂ : Ty) :
    cbv (BoCa.axWithbor2Ty x bnd T₁ T₂) = axWithbor2Ty x bnd (cbv T₁) (cbv T₂) := rfl
theorem cbv_axWithbor3Ty (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (T₁ T₂ : Ty) :
    cbv (BoCa.axWithbor3Ty a x bnd T₁ T₂) = axWithbor3Ty a x bnd (cbv T₁) (cbv T₂) := rfl
theorem cbv_axWithloadTy (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (T₁ T₂ : Ty) :
    cbv (BoCa.axWithloadTy a x bnd T₁ T₂) = axWithloadTy a x bnd (cbv T₁) (cbv T₂) := by
  simp only [BoCa.axWithloadTy, axWithloadTy, cbv, cbv_immReborrow]
theorem cbv_axWithswapTy (a : Lifetime.Life) (T₁ T₂ : Ty) :
    cbv (BoCa.axWithswapTy a T₁ T₂) = axWithswapTy a (cbv T₁) (cbv T₂) := rfl

/-! ### Outlives and scoping -/

theorem vOutlives_cbv {Δ : LifeCtx} {a : Lifetime.Life} {T : Ty} (h : OutlivesRules Δ a T) :
    VOutlives Δ a (cbv T) := by
  induction h with
  | unit => exact .unit
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  | ref _ ih => exact .ref ih
  | bang => exact .bang
  -- 2.35's strict premise gives the non-strict one of `VOutlives.box`.  `[spec §23]`
  | box h => exact .box (entailsLe_of_entailsLt h)
  | imm h => exact .imm h
  | «mut» h => exact .mut h

/-- `Δ ⊢ T` (its scoping half) scopes `T⁺`: a variable free in `T⁺` is free in `T`, and a
variable free in a type scoped in `Δ` is in `dom(Δ)` (`not_lfree_of_scopedB`). -/
theorem vScoped_cbv {Δ : LifeCtx} {T : Ty} (h : T.scopedB Δ = true) : VScoped Δ (cbv T) := by
  intro y hy
  cases hΔ : Δ.find? y with
  | none => exact absurd ((lFree_iff_vFree y T).mpr hy) (not_lfree_of_scopedB hΔ h)
  | some u => exact ⟨u, rfl⟩

/-! ### Contexts -/

theorem mem_cbvCtx {Γ : Ctx Ty} {s : Slot VTy} (h : s ∈ cbvCtx Γ) :
    ∃ t ∈ Γ, s = ⟨cbv t.ty, t.live⟩ := by
  unfold cbvCtx at h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
  exact ⟨t, ht, rfl⟩

theorem dead_cbvCtx {Γ : Ctx Ty} (h : Ctx.Dead Γ) : Ctx.Dead (cbvCtx Γ) := by
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

theorem solo_cbvCtx {Γ : Ctx Ty} {i : Nat} {T : Ty} (h : Ctx.Solo Γ i T) :
    Ctx.Solo (cbvCtx Γ) i (cbv T) := by
  induction h with
  | here hd => exact .here (dead_cbvCtx hd)
  | there _ ih => exact .there ih

theorem split_cbvCtx {Γ Γ₁ Γ₂ : Ctx Ty} (h : Ctx.Split Γ Γ₁ Γ₂) :
    Ctx.Split (cbvCtx Γ) (cbvCtx Γ₁) (cbvCtx Γ₂) := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | dead _ ih => exact .dead ih

theorem persistent_cbv {Γ : Ctx Ty} (h : Ctx.Persistent Γ) : Persistent (cbvCtx Γ) := by
  intro s hs hl
  obtain ⟨t, ht, rfl⟩ := mem_cbvCtx hs
  obtain ⟨T, hT⟩ := h t ht hl
  exact ⟨cbv T, by simp only [hT, cbv]⟩

theorem ctxOutlives_cbv {Δ : LifeCtx} {Γ : Ctx Ty} {a : Lifetime.Life}
    (h : Ctx.Outlives Δ Γ a) : CtxOutlives Δ (cbvCtx Γ) a := by
  refine ⟨h.1, fun s hs hl => ?_⟩
  obtain ⟨t, ht, rfl⟩ := mem_cbvCtx hs
  exact vOutlives_cbv (h.2 t ht hl)

theorem not_vFree_cbvCtx {Γ : Ctx Ty} {x : LifeVar}
    (h : ∀ s ∈ Γ, s.live = true → ¬ LFree x s.ty) :
    ∀ s ∈ cbvCtx Γ, s.live = true → ¬ VFree x s.ty := by
  intro s hs hl hv
  obtain ⟨t, ht, rfl⟩ := mem_cbvCtx hs
  exact h t ht hl ((lFree_iff_vFree x t.ty).mpr hv)

theorem not_vFree_cbv {Δ : LifeCtx} {x : LifeVar} {T : Ty} (hx : Δ.find? x = none)
    (h : T.scopedB Δ = true) : ¬ VFree x (cbv T) :=
  fun hv => not_lfree_of_scopedB hx h ((lFree_iff_vFree x T).mpr hv)

/-! ### The embedding -/

/-- **The call-by-value embedding.**  A BoLo derivation `Δ; Γ ⊢ e : T` is a CBPV derivation
`Δ; Γ⁺ ⊢ e : T⁺` of the same term, at the value judgment.  The hypotheses are those of the
typed world's Fundamental Property (`Typed.fundamental`): `Δ.Ok` and `Δ ⊢ Γ`.

* `1E`, `⊗E`, `⊕E` are CBPV's eliminators at `F T⁺`, read back at `T⁺` (`ofRet`).
* `⊸I` is `thunk (λx. return b)`; `∀I` is `thunk (Λ. return e)`; `!I` promotes either.
* `⊸E` and `∀E` are the call-by-value forms `lolliE` and `allEV`.
* Each axiom is `CDerives`' constant at the translated payloads.  `[spec §3]` -/
theorem embed {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} (h : DerivesWf Δ Γ e T) :
    Δ.Ok → Ctx.ScopedB Δ Γ → CDerives Δ (cbvCtx Γ) e (.val (cbv T)) := by
  induction h with
  | var h => intro _ _; exact .var (solo_cbvCtx h)
  | unitI h => intro _ _; exact .unitI (dead_cbvCtx h)
  | unitE hs _ _ ih₁ ih₂ =>
      intro hΔ hΓ
      exact .ofRet (.unitE (split_cbvCtx hs) (ih₁ hΔ (hΓ.split_left hs))
        (.ret (ih₂ hΔ (hΓ.split_right hs))))
  | tensorI hs _ _ ih₁ ih₂ =>
      intro hΔ hΓ
      exact .tensorI (split_cbvCtx hs) (ih₁ hΔ (hΓ.split_left hs)) (ih₂ hΔ (hΓ.split_right hs))
  | tensorE hs hwf _ _ ihp ihb =>
      intro hΔ hΓ
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ |>.mp hwf
      exact .ofRet (.tensorE (split_cbvCtx hs).toP (ihp hΔ (hΓ.split_left hs))
        (.ret (ihb hΔ (Ctx.ScopedB.cons (fun _ => h₂)
          (Ctx.ScopedB.cons (fun _ => h₁) (hΓ.split_right hs))))))
  | sumI₁ _ ih => intro hΔ hΓ; exact .sumI₁ (ih hΔ hΓ)
  | sumI₂ _ ih => intro hΔ hΓ; exact .sumI₂ (ih hΔ hΓ)
  | sumE hs hwf _ _ _ ih₀ ih₁ ih₂ =>
      intro hΔ hΓ
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ |>.mp hwf
      exact .ofRet (.sumE (split_cbvCtx hs).toP (ih₀ hΔ (hΓ.split_left hs))
        (.ret (ih₁ hΔ (Ctx.ScopedB.cons (fun _ => h₁) (hΓ.split_right hs))))
        (.ret (ih₂ hΔ (Ctx.ScopedB.cons (fun _ => h₂) (hΓ.split_right hs)))))
  | lolliI hwf _ ih =>
      intro hΔ hΓ
      exact .thunkV rfl (.lam (.ret (ih hΔ (Ctx.ScopedB.cons (fun _ => hwf) hΓ))))
  | lolliE hs _ _ iha ihf =>
      intro hΔ hΓ
      exact .lolliE (split_cbvCtx hs) (iha hΔ (hΓ.split_left hs)) (ihf hΔ (hΓ.split_right hs))
  | allI hx hb hnb _ ih =>
      intro hΔ hΓ
      have hside := allISide_of_scopedB hΔ hx hb hΓ
      exact .thunkV rfl (.allI hside.1 hside.2.1 (not_vFree_cbvCtx hside.2.2)
        (.ret (ih (hΔ.extend hx hb) (Ctx.ScopedB.allI hnb hΓ))))
  | allE _ hlt ih =>
      intro hΔ hΓ
      rw [cbv_instLife]
      exact .allEV (ih hΔ hΓ) hlt
  | boxIctx _ hΓo ih => intro hΔ hΓ; exact .boxI (ih hΔ hΓ) (ctxOutlives_cbv hΓo)
  | boxE _ ih => intro hΔ hΓ; exact .boxE (ih hΔ hΓ)
  | immSub _ hle ih => intro hΔ hΓ; exact .immSub (ih hΔ hΓ) hle
  | mutSub _ hle ih => intro hΔ hΓ; exact .mutSub (ih hΔ hΓ) hle
  | allocAx hΓd => intro _ _; exact .alloc (dead_cbvCtx hΓd)
  | freeAx hΓd => intro _ _; exact .free (dead_cbvCtx hΓd)
  | swapAx hΓd => intro _ _; rw [cbv_axSwapTy]; exact .swap (dead_cbvCtx hΓd)
  | copyAx hΓd => intro _ _; rw [cbv_axCopyTy]; exact .copy (dead_cbvCtx hΓd)
  | forgetImmAx hΓd => intro _ _; rw [cbv_axForgetImmTy]; exact .forgetImm (dead_cbvCtx hΓd)
  | forgetMutAx hΓd => intro _ _; rw [cbv_axForgetMutTy]; exact .forgetMut (dead_cbvCtx hΓd)
  | forgetUnkAx hΓd => intro _ _; rw [cbv_axForgetUnkTy]; exact .forgetUnk (dead_cbvCtx hΓd)
  | withbor1Ax hΓd x hx hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithbor1Ty hwf
      rw [cbv_axWithbor1Ty]
      exact .withbor1 x (dead_cbvCtx hΓd) hx (vScoped_cbv h₁) (not_vFree_cbv hx h₁)
        (not_vFree_cbv hx h₂)
  | withbor2Ax hΓd x hx hs hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithbor2Ty hwf
      obtain ⟨b, hb, ho⟩ := hs
      rw [cbv_axWithbor2Ty]
      exact .withbor2 x (dead_cbvCtx hΓd) hx ⟨b, hb, (vOutlives_cbv ho).toLe⟩ (not_vFree_cbv hx h₁)
        (not_vFree_cbv hx h₂)
  | withbor3Ax hΓd x hx hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithbor3Ty hwf
      rw [cbv_axWithbor3Ty]
      exact .withbor3 x (dead_cbvCtx hΓd) hx (not_vFree_cbv hx h₁) (not_vFree_cbv hx h₂)
  | withloadAx hΓd x hx hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithloadTy hwf
      rw [cbv_axWithloadTy]
      exact .withload x (dead_cbvCtx hΓd) hx (not_vFree_cbv hx h₁) (not_vFree_cbv hx h₂)
  | withswapAx hΓd => intro _ _; rw [cbv_axWithswapTy]; exact .withswap (dead_cbvCtx hΓd)
  | bangLamI hΓp hwf _ ih =>
      intro hΔ hΓ
      exact .bangThunkV (persistent_cbv hΓp) rfl
        (.lam (.ret (ih hΔ (Ctx.ScopedB.cons (fun _ => hwf) hΓ))))
  | bangAllI hΓp hx hb hnb _ ih =>
      intro hΔ hΓ
      have hside := allISide_of_scopedB hΔ hx hb hΓ
      exact .bangThunkV (persistent_cbv hΓp) rfl (.allI hside.1 hside.2.1
        (not_vFree_cbvCtx hside.2.2) (.ret (ih (hΔ.extend hx hb) (Ctx.ScopedB.allI hnb hΓ))))
  | bangE _ ih => intro hΔ hΓ; exact .bangE (ih hΔ hΓ)
  | copyBangAx hΓd => intro _ _; exact .copyBang (dead_cbvCtx hΓd)
  | forgetBangAx hΓd => intro _ _; exact .forgetBang (dead_cbvCtx hΓd)

/-- **Adequacy of BoLo through the CBPV core.**  A closed BoLo program of type `1` runs from
the empty memory to `()` and the empty memory: `embed`, then `adequacyC`.  `[spec §3]` -/
theorem adequacy_of_derivesWf {e : Expr} (h : DerivesWf LifeCtx.empty [] e .unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret (embed h ok_empty (fun _ hs => by cases hs)))

end BoCa.Fig16.LogRel.Core

end
