import Core.Chain.TyEq834N
import Core.Alpha
import Core.Compat

/-!
# The rules L1 and L2 make mechanical, at `SemJN₀`  `[spec §62]`

`docs/new-core/scope-831-interface.md` §3. Each rule's chain proof is Core's compatibility lemma
(`Core/Compat.lean`, `Core/Compatibility.lean`, `Core/Integers.lean`, `Core/Alpha.lean`,
`Core/Fundamental.lean`), line by line, against the interface of `Core/Chain/Iface834N.lean` and
`Core/Chain/TyEq834N.lean`: `gDenC_split ↦ gN_split₀`/`gN_splitC₀`, `wpTS_bind_frame ↦
erwp_bind_frame`, `cC_bind ↦ cN_bind₀`, `gDenC_local ↦ gN_extR₀`, `cC_tyEq ↦ cN_tyEq₀`.

The chain's judgment carries a world, a view consistent with the resource and a step index
(`SemJN₀`'s `Θ`, `c`, `n`); Core's has none. They enter at the same places in every rule:
* a premise is read at the view, which a context split's part is consistent with where the
  resource is valid (`gN_splitC₀`): at `F`/`F_Σ` by `erwp_of_valid`, elsewhere by `cN_of_valid₀`,
  at every conclusion;
* a premise read after a run is read at the index the run leaves (`gN_le₀`, `vN_le₀`);
* a thunk moves its context along `ExtR` to the world it is forced at (`gN_extR₀`), as Core's
  `gDenC_local`; `⊸` is a plain wand and moves nothing.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head)

private theorem substAll_cons₂ (w₂ w₁ : Val) (γ : List Val) (e : Expr) :
    substAll (w₂ :: w₁ :: γ) e = Expr.subst 0 w₁ (Expr.subst 0 (w₂.shift 1 0) (Expr.psub 2 γ e)) := by
  show Expr.psub 0 (w₂ :: w₁ :: γ) e = _
  rw [Expr.psub_cons₂ 0 w₂ w₁ γ e, Val.shift_zero]

private theorem substAll_forceE {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v)
    (C : CTy) : substAll γ (forceE C (.var i)) = forceE C (.val v) := by
  cases C with
  | ret A =>
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, substAll_var_some hv]; rfl
  | eff n j q A B C =>
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, substAll_var_some hv]; rfl
  | _ => exact substAll_var_some hv

/-! ### The context relation at a slot -/

/-- A dead slot contributes nothing (Core's `gDenC_dead_cons`). -/
theorem gN_dead_cons₀ {δ : LSub} {Θ : LocTy} {n : Nat} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (A : VTy) (v : Val) (hg : gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ) :
    gN₀ (ℍ := ℍ) δ Θ (⟨A, false⟩ :: Γ) (v :: γ) n ρ := by
  simpa [gN₀] using hg

/-- A live slot beside the rest (Core's `gDenC_mk` at a cons). -/
theorem gN_live_cons₀ {δ : LSub} {Θ : LocTy} {n : Nat} {Γ : Ctx VTy} {A : VTy} {v : Val}
    {γ : List Val} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : vN₀ (ℍ := ℍ) A δ Θ n v ρ₁)
    (hg : gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ₂) : gN₀ (ℍ := ℍ) δ Θ (⟨A, true⟩ :: Γ) (v :: γ) n ρ :=
  by simp only [gN₀, if_true]; exact ⟨ρ₁, ρ₂, hc, hv, hg⟩

/-- A live slot of `1` gives the context relation with the slot dead (Core's
`gDenC_unit_dead`): a value of `1` holds only `∅`. -/
theorem gN_unit_dead₀ {δ : LSub} {Θ : LocTy} {n : Nat} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (h : gN₀ (ℍ := ℍ) δ Θ (⟨.unit, true⟩ :: Γ) γ n ρ) :
    gN₀ (ℍ := ℍ) δ Θ (⟨.unit, false⟩ :: Γ) γ n ρ := by
  cases γ with
  | nil => exact h
  | cons v γ => exact gN_dead_cons₀ .unit v (gN_cons_persistent₀ (T := .unit) rfl h).2

/-- A live slot's liveness bit turned off keeps `LiveWithin`. -/
theorem liveWithin_dead {A : VTy} {Γ : Ctx VTy} {γ : List Val}
    (h : Ctx.LiveWithin (⟨A, true⟩ :: Γ) γ) : Ctx.LiveWithin (⟨A, false⟩ :: Γ) γ := by
  cases γ with
  | nil => exact absurd h.1 (by simp)
  | cons _ _ => exact h

/-! ### Values -/

/-- **`ID` at `SemJN₀`** (Core's `var_compatC`). -/
theorem var_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {A : VTy} (h : Ctx.SoloP Γ i A) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.var i) (.val A) := by
  intro δ γ Θ c n ls ρ _ _ _ hlw hg
  obtain ⟨v, hv, hval⟩ := gN_soloP₀ h (h.lt_of_liveWithin hlw) hg
  show erwp (ℍ := ℍ) _ _ _ n ls (substAll γ (.var i)) ρ
  rw [substAll_var_some hv]
  exact erwp_val hval

/-- **`⊗I` at `SemJN₀`** (Core's `tensorI_compatC`): the split with its parts' consistency
(`gN_splitC₀`), then `erwp_bind_frame` twice, each later premise read at the index the run
leaves. -/
theorem tensorI_compatN₀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e₁ e₂ : Expr} {A B : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (h₁ : SemJN₀ (ℍ := ℍ) Δ Γ₁ e₁ (.val A))
    (h₂ : SemJN₀ (ℍ := ℍ) Δ Γ₂ e₂ (.val B)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.pair e₁ e₂) (.val (.tensor A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  have hΦ := LocTy.view_down hΘ.1 c
  refine erwp_of_valid fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, -⟩ := gN_splitC₀ hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine erwp_bind_frame hΦ (opTableN_local _) (.pairL .hole (substAll γ e₂))
    (fun σ => gN₀ (ℍ := ℍ) δ Θ Γ₂ γ n σ) hcρ hc (h₁ δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁) hg₂ ?_
  intro k hk ls' v₁ σ₁ σ₂ σ hcσ hv₁ hg₂' hcσ' hvσ
  refine erwp_bind_frame hΦ (opTableN_local _) (.pairR v₁ .hole)
    (fun τ => vN₀ (ℍ := ℍ) A δ Θ k v₁ τ) (ResU.CompS.comm hcσ) hcσ'
    (h₂ δ γ Θ c k ls' σ₂ hδ hΘ (consistentX_right hcσ hcσ' hvσ) hlw₂ (gN_le₀ hk hg₂')) hv₁ ?_
  intro k' hk' ls'' v₂ τ₁ τ₂ τ hcτ hv₂ hv₁' _ _
  exact erwp_val (v := Val.pair v₁ v₂)
    ⟨v₁, v₂, τ₂, τ₁, rfl, ResU.CompS.comm hcτ, vN_le₀ hk' hv₁', hv₂⟩

/-- The thunk `λ_. M` of `thunk M : U (F A)` is a value of `U (F A)`: the closure runs at every
extension along `ExtR`, its environment moved there by `gN_extR₀` (Core's `gDenC_local`). -/
theorem thunkF_sem₀ {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (h : SemJN₀ (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) {δ : LSub} {γ : List Val}
    {Θ : LocTy} {n : Nat} {ρ : WRes} (hδ : Δ.Models δ) (hlw : Ctx.LiveWithin Γ γ)
    (hg : gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ) :
    vN₀ (ℍ := ℍ) (.thunk (.ret A)) δ Θ n (Val.lam (Expr.psub 1 γ M)) ρ := by
  intro Θ' hE hΘ' c' hc' ls'
  refine cN_head₀ (.ret A) δ Θ' hΘ'.1 c' n ls' ρ .hole _ _
    (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) rfl ?_
  rw [show Kont.hole.plug (Expr.subst 0 Val.unit (Expr.psub 1 γ M)) = substAll (Val.unit :: γ) M
    from (substAll_cons_psub Val.unit γ M).symm]
  exact h δ (Val.unit :: γ) Θ' c' n ls' ρ hδ hΘ' hc' hlw (gN_dead_cons₀ _ _ (gN_extR₀ hE hg))

/-- **`thunk M : U (F A)` at `SemJN₀`** (Core's `thunkF_compatC`). -/
theorem thunkF_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (h : SemJN₀ (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.lam M)) (.val (.thunk (.ret A))) := by
  intro δ γ Θ c n ls ρ hδ _ _ hlw hg
  show erwp (ℍ := ℍ) _ _ _ n ls (.val (.lam (Expr.psub 1 γ M))) ρ
  exact erwp_val (v := Val.lam (Expr.psub 1 γ M)) (thunkF_sem₀ h hδ hlw hg)

/-- The λ-value `V : C`, `C` not an `F`, is a value of `U C`: it runs at every extension along
`ExtR`, its environment moved there by `gN_extR₀`. -/
theorem thunkV_sem₀ {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hC : C.isRet = false)
    (h : SemJN₀ (ℍ := ℍ) Δ Γ (.val (.lam N)) (.comp C)) {δ : LSub} {γ : List Val}
    {Θ : LocTy} {n : Nat} {ρ : WRes} (hδ : Δ.Models δ) (hlw : Ctx.LiveWithin Γ γ)
    (hg : gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ) :
    vN₀ (ℍ := ℍ) (.thunk C) δ Θ n (Val.lam (Expr.psub 1 γ N)) ρ := by
  intro Θ' hE hΘ' c' hc' ls'
  rw [forceE_of_not_ret hC]
  exact h δ γ Θ' c' n ls' ρ hδ hΘ' hc' hlw (gN_extR₀ hE hg)

/-- **`thunk V : U C`, `C` not an `F`, at `SemJN₀`** (Core's `thunkV_compatC`). -/
theorem thunkV_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hC : C.isRet = false)
    (h : SemJN₀ (ℍ := ℍ) Δ Γ (.val (.lam N)) (.comp C)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.lam N)) (.val (.thunk C)) := by
  intro δ γ Θ c n ls ρ hδ _ _ hlw hg
  show erwp (ℍ := ℍ) _ _ _ n ls (.val (.lam (Expr.psub 1 γ N))) ρ
  exact erwp_val (v := Val.lam (Expr.psub 1 γ N)) (thunkV_sem₀ hC h hδ hlw hg)

/-! ### Computations -/

/-- **`force x : C` at `SemJN₀`** (Core's `force_compatC`): the thunk at its own world. -/
theorem force_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {C : CTy}
    (h : Ctx.SoloP Γ i (.thunk C)) : SemJN₀ (ℍ := ℍ) Δ Γ (forceE C (.var i)) (.comp C) := by
  intro δ γ Θ c n ls ρ _ hΘ hc hlw hg
  obtain ⟨v, hv, hval⟩ := gN_soloP₀ h (h.lt_of_liveWithin hlw) hg
  show cN₀ (ℍ := ℍ) C δ Θ c n ls (substAll γ (forceE C (.var i))) ρ
  rw [substAll_forceE hv]
  exact hval Θ (LocTy.extR_refl Θ ρ) hΘ c hc ls

/-- **`λx. M : A ⊸ C` at `SemJN₀`** (Core's `lam_compatC`): the arrow runs at the world and the
view it is applied at; its context is read at the application's index (`gN_le₀`). -/
theorem lam_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {C : CTy}
    (h : SemJN₀ (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.lam M)) (.comp (.arr A C)) := by
  intro δ γ Θ c n ls ρ hδ hΘ _ hlw hg c' k hk v ρv ρ' hcomp hv hcon
  refine cN_head₀ C δ Θ hΘ.1 c' k ls ρ' .hole _ _ (fun μ => Head.beta μ (Expr.psub 1 γ M) v) rfl ?_
  rw [show Kont.hole.plug (Expr.subst 0 v (Expr.psub 1 γ M)) = substAll (v :: γ) M
    from (substAll_cons_psub v γ M).symm]
  exact h δ (v :: γ) Θ c' k ls ρ' hδ hΘ hcon hlw
    (gN_live_cons₀ (ResU.CompS.comm hcomp) hv (gN_le₀ hk hg))

/-- **`[λ-dead]` at `SemJN₀`** (Core's `lamDead_compatC`): `[λ]` at the context with `x : 1` live,
whose relation gives the one with `x` dead (`gN_unit_dead₀`). -/
theorem lamDead_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy}
    (h : SemJN₀ (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) M (.comp C)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.lam M)) (.comp (.arr .unit C)) :=
  lam_compatN₀ fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg =>
    h δ γ Θ c n ls ρ hδ hΘ hc (liveWithin_dead hlw) (gN_unit_dead₀ hg)

/-- **`M x : C` at `SemJN₀`** (Core's `app_compatC`): the function's part of the split is
consistent with the view (`gN_splitC₀` at a valid resource, `cN_of_valid₀` at `C`). -/
theorem app_compatN₀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M : Expr} {i : Nat} {A : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hM : SemJN₀ (ℍ := ℍ) Δ Γ₁ M (.comp (.arr A C)))
    (hx : Ctx.SoloP Γ₂ i A) : SemJN₀ (ℍ := ℍ) Δ Γ (.app M (.var i)) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_of_valid₀ C δ Θ c n ls _ ρ fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, -⟩ := gN_splitC₀ hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  obtain ⟨v, hvγ, hval⟩ := gN_soloP₀ hx (hx.lt_of_liveWithin hlw₂) hg₂
  have he : substAll γ (.app M (.var i)) = .app (substAll γ M) (.val v) := by
    show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ (.var i)) = _
    rw [← substAll, ← substAll, substAll_var_some hvγ]
  rw [he]
  exact hM δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁ c n le_rfl v ρ₂ ρ hcρ hval hc

/-- **`M to x. N : C` at `SemJN₀`** (Core's `bind_compatC`): the context `N` needs is framed
through `M`'s run, together with the stack `C` is eliminated by (`cN_bind₀`). -/
theorem bind_compatN₀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hM : SemJN₀ (ℍ := ℍ) Δ Γ₁ M (.comp (.ret A)))
    (hN : SemJN₀ (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.app (.val (.lam N)) M) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂⟩ := gN_split₀ hsp hg
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine cN_bind₀ C δ Θ hΘ.1 (.appR (.val (.lam (Expr.psub 1 γ N))) .hole) (substAll γ M)
    (fun k _ v ρ => vN₀ (ℍ := ℍ) A δ Θ k v ρ) (fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h)
    (fun k σ => gN₀ (ℍ := ℍ) δ Θ Γ₂ γ k σ) (fun _ _ _ hk h => gN_le₀ hk h) ?_ c n ls ρ₁ ρ₂ ρ hcρ
    (fun c' hc' => hM δ γ Θ c' n ls ρ₁ hδ hΘ hc' hlw₁ hg₁) hg₂ hc
  intro c' k ls' v σ₁ σ₂ σ hcσ hv hg₂' hcσ'
  refine cN_head₀ C δ Θ hΘ.1 c' k ls' σ .hole _ _ (fun μ => Head.beta μ (Expr.psub 1 γ N) v) rfl ?_
  rw [show Kont.hole.plug (Expr.subst 0 v (Expr.psub 1 γ N)) = substAll (v :: γ) N
    from (substAll_cons_psub v γ N).symm]
  exact hN δ (v :: γ) Θ c' k ls' σ hδ hΘ hcσ' hlw₂ (gN_live_cons₀ hcσ hv hg₂')

/-! ### Eliminations of values into computations -/

/-- **`V; M : C` at `SemJN₀`** (Core's `unitE_compatC`). -/
theorem unitE_compatN₀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {V M : Expr} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hV : SemJN₀ (ℍ := ℍ) Δ Γ₁ V (.val .unit))
    (hM : SemJN₀ (ℍ := ℍ) Δ Γ₂ M (.comp C)) : SemJN₀ (ℍ := ℍ) Δ Γ (.seq V M) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂⟩ := gN_split₀ hsp hg
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine cN_bind₀ C δ Θ hΘ.1 (.seq .hole (substAll γ M)) (substAll γ V)
    (fun k _ v ρ => vN₀ (ℍ := ℍ) .unit δ Θ k v ρ) (fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h)
    (fun k σ => gN₀ (ℍ := ℍ) δ Θ Γ₂ γ k σ) (fun _ _ _ hk h => gN_le₀ hk h) ?_ c n ls ρ₁ ρ₂ ρ hcρ
    (fun c' hc' => hV δ γ Θ c' n ls ρ₁ hδ hΘ hc' hlw₁ hg₁) hg₂ hc
  rintro c' k ls' v σ₁ σ₂ σ hcσ ⟨rfl, rfl⟩ hg₂' hcσ'
  rw [eq_of_compS_empty_left hcσ] at hcσ' ⊢
  exact cN_head₀ C δ Θ hΘ.1 c' k ls' σ₂ .hole _ _ (fun μ => Head.seq μ _) rfl
    (hM δ γ Θ c' k ls' σ₂ hδ hΘ hcσ' hlw₂ hg₂')

/-- **`let (x, y) = V in M : C` at `SemJN₀`** (Core's `tensorE_compatC`). -/
theorem tensorE_compatN₀ {Δ : LifeCtx} {Γ Γp Γb : Ctx VTy} {V M : Expr} {A B : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γp Γb)
    (hV : SemJN₀ (ℍ := ℍ) Δ Γp V (.val (.tensor A B)))
    (hM : SemJN₀ (ℍ := ℍ) Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.letpair V M) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂⟩ := gN_split₀ hsp hg
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine cN_bind₀ C δ Θ hΘ.1 (.letpair .hole (Expr.psub 2 γ M)) (substAll γ V)
    (fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor A B) δ Θ k v ρ) (fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h)
    (fun k σ => gN₀ (ℍ := ℍ) δ Θ Γb γ k σ) (fun _ _ _ hk h => gN_le₀ hk h) ?_ c n ls ρ₁ ρ₂ ρ hcρ
    (fun c' hc' => hV δ γ Θ c' n ls ρ₁ hδ hΘ hc' hlw₁ hg₁) hg₂ hc
  rintro c' k ls' v σ₁ σ₂ σ hcσ ⟨w₁, w₂, b₁, b₂, rfl, hcb, hw₁, hw₂⟩ hg₂' hcσ'
  refine cN_head₀ C δ Θ hΘ.1 c' k ls' σ .hole _ _ (fun μ => Head.letpair μ w₁ w₂ _) rfl ?_
  rw [← substAll_cons₂]
  obtain ⟨x, hx, hxσ⟩ := compS_reassoc hcb hcσ
  obtain ⟨y, hy, hyσ⟩ := compS_lcomm hx hxσ
  exact hM δ (w₂ :: w₁ :: γ) Θ c' k ls' σ hδ hΘ hcσ' hlw₂
    (gN_live_cons₀ hyσ hw₂ (gN_live_cons₀ hy hw₁ hg₂'))

/-- **`case V {inj₁ x. M₁ | inj₂ y. M₂} : C` at `SemJN₀`** (Core's `sumE_compatC`). -/
theorem sumE_compatN₀ {Δ : LifeCtx} {Γ Γs Γb : Ctx VTy} {V M₁ M₂ : Expr} {A B : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γs Γb) (hV : SemJN₀ (ℍ := ℍ) Δ Γs V (.val (.sum A B)))
    (h₁ : SemJN₀ (ℍ := ℍ) Δ (⟨A, true⟩ :: Γb) M₁ (.comp C))
    (h₂ : SemJN₀ (ℍ := ℍ) Δ (⟨B, true⟩ :: Γb) M₂ (.comp C)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.case V M₁ M₂) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂⟩ := gN_split₀ hsp hg
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine cN_bind₀ C δ Θ hΘ.1 (.case .hole (Expr.psub 1 γ M₁) (Expr.psub 1 γ M₂)) (substAll γ V)
    (fun k _ v ρ => vN₀ (ℍ := ℍ) (.sum A B) δ Θ k v ρ) (fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h)
    (fun k σ => gN₀ (ℍ := ℍ) δ Θ Γb γ k σ) (fun _ _ _ hk h => gN_le₀ hk h) ?_ c n ls ρ₁ ρ₂ ρ hcρ
    (fun c' hc' => hV δ γ Θ c' n ls ρ₁ hδ hΘ hc' hlw₁ hg₁) hg₂ hc
  rintro c' k ls' v σ₁ σ₂ σ hcσ hsum hg₂' hcσ'
  rcases hsum with ⟨w, rfl, hw⟩ | ⟨w, rfl, hw⟩
  · refine cN_head₀ C δ Θ hΘ.1 c' k ls' σ .hole _ _ (fun μ => Head.case₁ μ w _ _) rfl ?_
    rw [show Kont.hole.plug (Expr.subst 0 w (Expr.psub 1 γ M₁)) = substAll (w :: γ) M₁
      from (substAll_cons_psub w γ M₁).symm]
    exact h₁ δ (w :: γ) Θ c' k ls' σ hδ hΘ hcσ' hlw₂ (gN_live_cons₀ hcσ hw hg₂')
  · refine cN_head₀ C δ Θ hΘ.1 c' k ls' σ .hole _ _ (fun μ => Head.case₂ μ w _ _) rfl ?_
    rw [show Kont.hole.plug (Expr.subst 0 w (Expr.psub 1 γ M₂)) = substAll (w :: γ) M₂
      from (substAll_cons_psub w γ M₂).symm]
    exact h₂ δ (w :: γ) Θ c' k ls' σ hδ hΘ hcσ' hlw₂ (gN_live_cons₀ hcσ hw hg₂')

/-- **`absurd V : C` at `SemJN₀`** (Core's `zeroE_compatC`): no arm runs. -/
theorem zeroE_compatN₀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {V : Expr} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hV : SemJN₀ (ℍ := ℍ) Δ Γ₁ V (.val .zero)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (absurdE V) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂⟩ := gN_split₀ hsp hg
  obtain ⟨hlw₁, -⟩ := hsp.liveWithin hlw
  refine cN_bind₀ C δ Θ hΘ.1 (.case .hole (.var 0) (.var 0)) (substAll γ V)
    (fun k _ v ρ => vN₀ (ℍ := ℍ) .zero δ Θ k v ρ) (fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h)
    (fun k σ => gN₀ (ℍ := ℍ) δ Θ Γ₂ γ k σ) (fun _ _ _ hk h => gN_le₀ hk h) ?_ c n ls ρ₁ ρ₂ ρ hcρ
    (fun c' hc' => hV δ γ Θ c' n ls ρ₁ hδ hΘ hc' hlw₁ hg₁) hg₂ hc
  rintro c' k ls' v σ₁ σ₂ σ - hv - -
  exact hv.elim

/-! ### `!` and `[@a]` -/

/-- **Promotion of `thunk M : U (F A)` over `!Γ` at `SemJN₀`** (Core's `bangThunkF_compatC`):
`!Γ` holds nothing (`gN_persistent₀`). -/
theorem bangThunkF_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} (hp : Ctx.Banged Γ)
    (h : SemJN₀ (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A)))) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  show erwp (ℍ := ℍ) _ _ _ n ls (.val (.lam (Expr.psub 1 γ M))) ρ
  exact erwp_val (v := Val.lam (Expr.psub 1 γ M)) ⟨gN_persistent₀ hp hg, thunkF_sem₀ h hδ hlw hg⟩

/-- **Promotion of a λ-value `V : C` over `!Γ` at `SemJN₀`** (Core's `bangThunkV_compatC`). -/
theorem bangThunkV_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hp : Ctx.Banged Γ)
    (hC : C.isRet = false) (h : SemJN₀ (ℍ := ℍ) Δ Γ (.val (.lam N)) (.comp C)) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.lam N)) (.val (.bang (.thunk C))) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  show erwp (ℍ := ℍ) _ _ _ n ls (.val (.lam (Expr.psub 1 γ N))) ρ
  exact erwp_val (v := Val.lam (Expr.psub 1 γ N)) ⟨gN_persistent₀ hp hg, thunkV_sem₀ hC h hδ hlw hg⟩

/-- **`[]I` at `SemJN₀`** (Core's `boxI_compatC`, `boxI_compatX`): `[TR]` 6.62 at the context
(`gN_outlives₀`), `wp-[]` at the run (`erwp_box`). -/
theorem boxI_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} {a : Lifetime.Life}
    (h : SemJN₀ (ℍ := ℍ) Δ Γ e (.val A)) (hΓ : CtxOutlives Δ Γ a) :
    SemJN₀ (ℍ := ℍ) Δ Γ e (.val (.box a A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, ha⟩ := hΓ.1 δ hδ
  exact erwp_mono (fun _ _ _ _ ⟨hv, hst⟩ => ⟨α, ha, hv, hst⟩) (opTableN_local _) n ls _ ρ
    (erwp_box (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg) (gN_outlives₀ hδ ha hΓ.2 hg))

/-! ### Literals and host operations -/

/-- **An integer literal at `SemJN₀`** (Core's `lit_compatX`, `vP_lit`). -/
theorem lit_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} (c : IntLit) (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val ⟨.prim (.lit c), .prim⟩) (.val (.int c.width)) := by
  intro δ γ Θ c' n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP₀ hΓ hg
  exact erwp_val (v := ⟨.prim (.lit c), .prim⟩) ((vN_iff_vP₀ (ls := []) rfl).mpr (vP_lit c))

/-- **Every host operation at `SemJN₀`** (Core's `hostOp_compatX`): one host step, which changes
no memory, answers in the relation at `∅` (`host_call_sound₀`). -/
theorem hostOp_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} (op : HostOp) (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim (.host op))) (.val (.bang (hostSig op))) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP₀ hΓ hg
  refine erwp_val (v := Val.prim (.host op)) ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv _
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨rfl, r, hr, hres⟩ := host_call_sound₀ op (Θ' := Θ') (n' := k) hv
  exact erwp_det (LocTy.view_down hΘ'.1 c'') (opTableN_down OpTabN.empty_down)
    (fun k _ v ρ h => vN_down₀ _ _ _ k v ρ h)
    (fun μ => step1Only_plug (Head.host μ op v r hr) rfl .hole) (erwp_val hres)

/-! ### Call-by-value application -/

/-- **`f a` at `VTy.lolli` at `SemJN₀`** (Core's `lolliE_compatX`): `erwp_bind_frame` at the
argument, then at the function, then the function's `U` clause at its own world and the plain
`⊸` at the argument. -/
theorem lolliE_compatN₀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {f arg : Expr} {T₁ T₂ : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (ha : SemJN₀ (ℍ := ℍ) Δ Γ₁ arg (.val T₁))
    (hf : SemJN₀ (ℍ := ℍ) Δ Γ₂ f (.val (.lolli T₁ T₂))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.app f arg) (.val T₂) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  have hΦ := LocTy.view_down hΘ.1 c
  refine erwp_of_valid fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, -⟩ := gN_splitC₀ hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine erwp_bind_frame hΦ (opTableN_local _) (.appR (substAll γ f) .hole)
    (fun σ => gN₀ (ℍ := ℍ) δ Θ Γ₂ γ n σ) hcρ hc (ha δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁) hg₂ ?_
  intro k hk ls' v₁ σ₁ σ₂ σ hcσ hv₁ hg₂' hcσ' hvσ
  refine erwp_bind_frame hΦ (opTableN_local _) (.appL .hole v₁)
    (fun τ => vN₀ (ℍ := ℍ) T₁ δ Θ k v₁ τ) (ResU.CompS.comm hcσ) hcσ'
    (hf δ γ Θ c k ls' σ₂ hδ hΘ (consistentX_right hcσ hcσ' hvσ) hlw₂ (gN_le₀ hk hg₂')) hv₁ ?_
  intro k' hk' ls'' v₂ τ₁ τ₂ τ hcτ hv₂ hv₁' hcτ' hvτ
  exact hv₂ Θ (LocTy.extR_refl _ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'' c k' le_rfl v₁ τ₂ τ
    hcτ (vN_le₀ hk' hv₁') hcτ'

/-! ### `∀E` and `[α]` (L2) -/

/-- **`M [] : C[@a/'x]` at `SemJN₀`** (Core's `allE_compatC`): `CTyEq.instLife` reads `C[@a/'x]`
at `δ` as `C` at `δ['x ↦ @aδ]`, and `cN_tyEq₀` carries the relation across. -/
theorem allE_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {x : LifeVar} {b a : Lifetime.Life}
    {C : CTy} (h : SemJN₀ (ℍ := ℍ) Δ Γ M (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.app M (.val .unit)) (.comp (C.instLife x a)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, β, ha, hb, hab⟩ := hlt δ hδ
  have he : substAll γ (.app M (.val .unit)) = .app (substAll γ M) (.val .unit) := by
    show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ (.val .unit)) = _
    simp [Expr.psub, substAll]
  show cN₀ (ℍ := ℍ) (C.instLife x a) δ Θ c n ls (substAll γ (.app M (.val .unit))) ρ
  rw [he, cN_tyEq₀ _ (CTyEq.instLife x a C ha)]
  exact h δ γ Θ c n ls ρ hδ hΘ hc hlw hg α ⟨β, hb, hab⟩

/-- **Call-by-value `∀E` at `SemJN₀`** (Core's `allE_compatX`): bind the run, then the thunk's
`U` clause at its own world, the `∀` at `@aδ`, and `vN_tyEq₀` at `TyEq.instLife`. -/
theorem allEV_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {x : LifeVar} {b a : Lifetime.Life}
    {A : VTy} (h : SemJN₀ (ℍ := ℍ) Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.app e (.val .unit)) (.val (VTy.instLife x a A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, β, ha, hb, hab⟩ := hlt δ hδ
  have hΦ := LocTy.view_down hΘ.1 c
  have hsub : vN₀ (ℍ := ℍ) (VTy.instLife x a A) δ = vN₀ (ℍ := ℍ) A (δ.extend x α) :=
    vN_tyEq₀ _ (TyEq.instLife x a A ha)
  show erwp (ℍ := ℍ) _ _ _ n ls ((Kont.appL .hole .unit).plug (substAll γ e)) ρ
  refine erwp_bindR hΦ (opTableN_local _) (.appL .hole .unit) ?_
  refine rwp_mono_le (fun k _ ls' v σ hv => ?_)
    (rwp_consistentXV (rwp_of_erwp_empty (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)) hc)
  obtain ⟨hv, hcσ, -⟩ := hv
  rw [hsub]
  exact hv Θ (LocTy.extR_refl _ _) hΘ c hcσ ls' α ⟨β, hb, hab⟩

/-- **`[α]` at `SemJN₀`** (Core's `alpha_compatJ`, `alpha_compatC`): α-equivalent types are one
type (`CTy.alphaB_sound`), and the relation reads a type up to `CTyEq` (`cN_tyEq₀`). -/
theorem alpha_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} :
    ∀ {j j' : Jdg}, j.alphaB j' = true → SemJN₀ (ℍ := ℍ) Δ Γ e j → SemJN₀ (ℍ := ℍ) Δ Γ e j'
  | .val A, .val A', hα, h => fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg => by
      have e := cN_tyEq₀ (ℍ := ℍ) (.ret A) (C' := .ret A')
        (CTy.alphaB_sound (.ret A) (.ret A') (alphaAgree_nil δ) hα)
      show cN₀ (ℍ := ℍ) (.ret A') δ Θ c n ls _ ρ
      rw [← e]
      exact h δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  | .comp C, .comp C', hα, h => fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg => by
      have e := cN_tyEq₀ (ℍ := ℍ) C (C' := C') (CTy.alphaB_sound C C' (alphaAgree_nil δ) hα)
      show cN₀ (ℍ := ℍ) C' δ Θ c n ls _ ρ
      rw [← e]
      exact h δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  | .val _, .comp _, hα, _ | .comp _, .val _, hα, _ => by simp [Jdg.alphaB] at hα

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
