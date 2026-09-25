import Paper.S6_8_FundamentalProperty.Lemmas
/-!
# Experiment: does the typed world factor through CBPV?

Value types `VTy` and computation types `CTy`, with `U` (`thunk`), `→` (`arr`), `F` (`ret`)
and a lifetime `∀` on computations, and `!A` on values.  `Ty.cbv` is the call-by-value
translation: `T₁ ⊸ T₂ ↦ U (T₁⁺ → F T₂⁺)`, `∀'x ⊏ @b. T ↦ U (∀'x ⊏ @b. F T⁺)` and
`!T ↦ !T⁺`.

`vC`/`cC` interpret value and computation types over the typed world, with the Kripke
quantifier over `Ext` only at `U`, the tagged `wp` only at `F`, and `→`/`∀` plain.
`vX_eq_vC`: at every BoLo type, `vX` is `vC` at the translation.  So BoLo's Fundamental
Property is a statement about the CBV fragment of this relation (`fundamentalPropertyC`).

Computations are interpreted on BoLo expressions; there is no CBPV syntax or machine.
-/

namespace Experiments.CBPVSplit
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LSub LifeCtx LifeVar)
noncomputable section

mutual
/-- Value types. -/
inductive VTy where
  | unit
  | sum (A B : VTy)
  | tensor (A B : VTy)
  | ref (A : VTy)
  | imm (a : Lifetime.Life) (A : VTy)
  | mut (a : Lifetime.Life) (A : VTy)
  | box (a : Lifetime.Life) (A : VTy)
  | unk
  /-- `!A`: resource `∅` and `A`'s full relation, in both modes. -/
  | bang (A : VTy)
  /-- `U C`. -/
  | thunk (C : CTy)
/-- Computation types. -/
inductive CTy where
  /-- `A → C`. -/
  | arr (A : VTy) (C : CTy)
  /-- `F A`. -/
  | ret (A : VTy)
  /-- `∀'x ⊏ @b. C`. -/
  | all (x : LifeVar) (b : Lifetime.Life) (C : CTy)
end

/-- The call-by-value translation of BoLo types. -/
def cbv : Ty → VTy
  | .unit => .unit
  | .sum T₁ T₂ => .sum (cbv T₁) (cbv T₂)
  | .tensor T₁ T₂ => .tensor (cbv T₁) (cbv T₂)
  | .lolli T₁ T₂ => .thunk (.arr (cbv T₁) (.ret (cbv T₂)))
  | .ref T => .ref (cbv T)
  | .imm a T => .imm a (cbv T)
  | .mut a T => .mut a (cbv T)
  | .box a T => .box a (cbv T)
  | .all x b T => .thunk (.all x b (.ret (cbv T)))
  | .bang T => .bang (cbv T)
  | .unk => .unk

theorem cbv_injective : ∀ {S T : Ty}, cbv S = cbv T → S = T
  | .unit, T, h => by cases T <;> simp_all [cbv]
  | .unk, T, h => by cases T <;> simp_all [cbv]
  | .sum S₁ S₂, T, h => by
      cases T <;> simp [cbv] at h
      exact congrArg₂ _ (cbv_injective h.1) (cbv_injective h.2)
  | .tensor S₁ S₂, T, h => by
      cases T <;> simp [cbv] at h
      exact congrArg₂ _ (cbv_injective h.1) (cbv_injective h.2)
  | .lolli S₁ S₂, T, h => by
      cases T <;> simp [cbv] at h
      exact congrArg₂ _ (cbv_injective h.1) (cbv_injective h.2)
  | .ref S, T, h => by
      cases T <;> simp [cbv] at h
      exact congrArg _ (cbv_injective h)
  | .bang S, T, h => by
      cases T <;> simp [cbv] at h
      exact congrArg _ (cbv_injective h)
  | .imm a S, T, h => by
      cases T <;> simp [cbv] at h
      rw [h.1, cbv_injective h.2]
  | .mut a S, T, h => by
      cases T <;> simp [cbv] at h
      rw [h.1, cbv_injective h.2]
  | .box a S, T, h => by
      cases T <;> simp [cbv] at h
      rw [h.1, cbv_injective h.2]
  | .all x b S, T, h => by
      cases T <;> simp [cbv] at h
      rw [h.1, h.2.1, cbv_injective h.2.2]

mutual
/-- `𝒱⟦A⟧(ls)δ(v)`; `full = false` is the observable view (`U` relaxed to `True`). -/
def vC (wpX : WpOp) : Bool → VTy → List SRec → LSub → Val → WProp
  | _, .unit, _, _, v => ⌜v = .unit⌝
  | b, .tensor A B, ls, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vC wpX b A ls δ v₁ ⋆ vC wpX b B ls δ v₂
  | b, .sum A B, ls, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vC wpX b A ls δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vC wpX b B ls δ v₂)
  | true, .thunk C, ls, δ, v => fun ρ =>
      ∀ ls', Ext ls ls' ρ → cC wpX C ls' δ (.val v) ρ
  | false, .thunk _, _, _, _ => fun _ => True
  | _, .bang A, ls, δ, v => fun ρ => ρ = PMap.empty ∧ vC wpX true A ls δ v ρ
  | b, .box a A, ls, δ, v => atLife δ a fun α => box α (vC wpX b A ls δ v)
  | b, .ref A, ls, δ, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vC wpX b A ls δ v'
  | _, .imm a A, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ =>
        ⌜v = .loc ℓ ∧ ∃ T, cbv T = A ∧ CohE (rsOf ls) ℓ T δ⌝ ⋆
        ptoImmS ℓ α ls (fun ls₀ => vC wpX false A ls₀ δ)
  | _, .mut a A, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
        ptoMutS ℓ α ls (fun ls₀ => vC wpX true A ls₀ δ)
  | _, .unk, _, _, _ => emp
/-- `𝒞⟦C⟧(ls)δ(e)`: `F` runs `e` at the tagged `wp`; `→` and `∀` supply an argument. -/
def cC (wpX : WpOp) : CTy → List SRec → LSub → Expr → WProp
  | .ret A, ls, δ, e => wpX ls e (fun ls'' => vC wpX true A ls'' δ)
  | .arr A C, ls, δ, e => fun ρ =>
      ∀ v', (vC wpX true A ls δ v' ─⋆ cC wpX C ls δ (.app e (.val v'))) ρ
  | .all x c C, ls, δ, e => fun ρ =>
      ∀ α, (⌜LtLife δ c α⌝ ─⋆ cC wpX C ls (δ.extend x α) (.app e (.val .unit))) ρ
end

/-- At every BoLo type, `vX` is `vC` at the CBV translation. -/
theorem vX_eq_vC_fun (wpX : WpOp) :
    ∀ (b : Bool) (T : Ty), vX wpX b T = vC wpX b (cbv T) := by
  intro b T
  induction T generalizing b with
  | unit => rfl
  | sum T₁ T₂ ih₁ ih₂ => funext ls δ v; simp only [vX, vC, cbv, ih₁, ih₂]
  | tensor T₁ T₂ ih₁ ih₂ => funext ls δ v; simp only [vX, vC, cbv, ih₁, ih₂]
  | lolli T₁ T₂ ih₁ ih₂ =>
      cases b
      · rfl
      · funext ls δ v; simp only [vX, vC, cC, cbv, ih₁, ih₂]
  | ref T ih => funext ls δ v; simp only [vX, vC, cbv, ih]
  | imm a T ih =>
      funext ls δ v
      have hc : ∀ (ℓ : Loc) (rs : List FrameRec) (δ : LSub),
          (∃ S, cbv S = cbv T ∧ CohE rs ℓ S δ) ↔ CohE rs ℓ T δ :=
        fun ℓ rs δ => ⟨fun ⟨S, hS, h⟩ => cbv_injective hS ▸ h, fun h => ⟨T, rfl, h⟩⟩
      simp only [vX, vC, cbv, ih, hc]
  | «mut» a T ih => funext ls δ v; simp only [vX, vC, cbv, ih]
  | bang T ih => funext ls δ v; simp only [vX, vC, cbv, ih]
  | box a T ih => funext ls δ v; simp only [vX, vC, cbv, ih]
  | all x c T ih =>
      cases b
      · rfl
      · funext ls δ v; simp only [vX, vC, cC, cbv, ih]
  | unk => rfl

theorem vX_eq_vC (wpX : WpOp) (b : Bool) (T : Ty) (ls : List SRec) (δ : LSub) (v : Val) :
    vX wpX b T ls δ v = vC wpX b (cbv T) ls δ v := by
  rw [vX_eq_vC_fun]

/-- **`𝒱⟦A⟧` is stable along `Ext`** at every CBPV value type, including those that are no
BoLo type's translation: the Kripke quantifier sits at `U`, and nothing else reads the list
except through the records a cell keeps. -/
theorem vC_local {wpX : WpOp} : ∀ (b : Bool) (T : VTy) {ls ls' : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    Ext ls ls' ρ → vC wpX b T ls δ v ρ → vC wpX b T ls' δ v ρ
  | _, .unit, _, _, _, _, _, _, h => h
  | b, .tensor T₁ T₂, _, _, _, _, _, hk, h => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      have hk' := hk.right hc
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
        vC_local b T₁ (hk'.left hc') h₁, vC_local b T₂ (hk'.right hc') h₂⟩
  | b, .sum T₁ T₂, _, _, _, _, _, hk, h => by
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, vC_local b T₁ (hk.right hc) h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, vC_local b T₂ (hk.right hc) h₂⟩
  | true, .thunk C, _, _, _, _, _, hk, h => fun ls'' hk' => h ls'' (hk.trans hk')
  | false, .thunk _, _, _, _, _, _, _, h => h
  | _, .bang T, _, _, _, _, _, hk, h => ⟨h.1, vC_local true T hk h.2⟩
  | b, .box a T, _, _, _, _, _, hk, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, vC_local b T hk hb, ho⟩
  | b, .ref T, _, _, _, _, _, hk, h => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho,
        vC_local b T ((hk.right hc).right hc') h₂⟩
  | _, .imm a T, ls, ls', _, _, _, hk, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, T₀, hT₀, hcoh⟩, s, u, σ, hs, ls₀, hρ₁, hP, hαs, hls₀⟩ := h
      subst hρ₀
      have hρ₁' := eq_of_compS_empty_left hc
      subst hρ₁'
      subst hρ₁
      have hk₁ : Keeps (rsOf _) (rsOf _) _ := hk.1
      have hcell : CellIn (ResU.single ℓ (CellU.immOf s u σ hs)) s.meet :=
        CellIn.single (by simp)
      refine ⟨α, hα, ℓ, _, _, hc, ⟨rfl, hv, T₀, hT₀, cohE_keeps hk₁ (CellU.kind_immOf _ _ _ _) hcoh⟩,
        s, u, σ, hs, ls₀, rfl, hP, hαs, fun x => ?_⟩
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mpr hx, hb⟩⟩
  | _, .mut a T, ls, ls', _, _, _, hk, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, hls₀,
        hunif⟩ := h
      subst hρ₀
      have hk₁ := hk.right hc
      have hmut : CellIn ρ₁ b :=
        ⟨ℓ, _, by rw [hρ₁]; exact ResU.single_get_self _ _, by simp, le_rfl⟩
      refine ⟨α, hα, ℓ, _, _, hc, ⟨rfl, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, ?_, hunif⟩
      intro x
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mpr hx, hb⟩⟩
  | _, .unk, _, _, _, _, _, _, h => h

/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⁺⟧(ls)δ(γ(x))`. -/
def gSepC (ls : List SRec) (δ : LSub) : Ctx Ty → List Val → WProp
  | [],     _      => emp
  | _ :: _, []     => emp
  | s :: Γ, v :: γ =>
      if s.live then vC wpTS true (cbv s.ty) ls δ v ⋆ gSepC ls δ Γ γ else gSepC ls δ Γ γ

theorem gSepX_eq_gSepC (ls : List SRec) (δ : LSub) :
    ∀ (Γ : Ctx Ty) (γ : List Val), gSepX ls δ Γ γ = gSepC ls δ Γ γ
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: Γ, v :: γ => by
      simp only [gSepX, gSepC, vP, gSepX_eq_gSepC ls δ Γ γ]
      rw [vX_eq_vC]

/-- The judgment at a computation type: `Γ⁺ ⊨ e : C`. -/
def SemC (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (C : CTy) : Prop :=
  ∀ δ γ (ls : List SRec) ρ, Δ.Models δ →
    (⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepC ls δ Γ γ) ρ → cC wpTS C ls δ (substAll γ e) ρ

/-- `SemX` is `SemC` at `F T⁺`. -/
theorem semX_iff_semC (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) :
    SemX Δ Γ e T ↔ SemC Δ Γ e (.ret (cbv T)) := by
  have hg : ∀ ls δ γ, gDenX ls δ Γ γ = (⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepC ls δ Γ γ) :=
    fun ls δ γ => by simp only [gDenX, gSepX_eq_gSepC]
  have hv : ∀ δ, (fun ls' => vP T ls' δ) = (fun ls' => vC wpTS true (cbv T) ls' δ) :=
    fun δ => funext fun ls' => funext fun v => vX_eq_vC wpTS true T ls' δ v
  simp only [SemX, SemC, cC, hg, hv]

/-- BoLo's Fundamental Property, read on the CBV fragment. -/
theorem fundamentalPropertyC (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty)
    (hD : DerivesWf Δ Γ e T) (hΔ : Δ.Ok) (hΓ : Ctx.ScopedB Δ Γ) :
    SemC Δ Γ e (.ret (cbv T)) :=
  (semX_iff_semC Δ Γ e T).mp (fundamentalProperty Δ Γ e T hD hΔ hΓ)

end

end Experiments.CBPVSplit
