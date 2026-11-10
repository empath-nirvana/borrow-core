import Core.Chain.RulesKW835N
import Core.Chain.CodeNuKW835N
import Core.CodeRules

/-!
# The code rules at the chain's relation  `[spec §68]`

Core's `Core/CodeRules.lean` at `SemJN`, the relation `goal791N` reads.

* `gN_capTy`: under `Ctx.CapOK`, the captured values' tuple is in `𝒱⟦Γ.capTy e⟧` at the context's
  whole resource, the uncaptured live slots being persistent and so at `∅`
  (`vN_empty_of_persistent`, through `gN_cons_persistent`).
* `vN_thunk_of_cN`: a value whose `F (U C)` reading holds at every extension of the world is in
  `𝒱⟦U C⟧`: forcing it is a bind at its own run (`cN_bind`).
* `codeI_compatN`, `codeIB_compatN`, `codeErase_compatN`, `codeEraseB_compatN`: the four rules' lemmas.
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
open BoCa.BoLo (Kont)

/-! ### The captured values compose to the environment -/

/-- **The captured slots' values compose to the environment tuple** at the chain's relation
(Core's `gSepC_capTyOf`).  `[spec §68]` -/
theorem gN_capTyOf {δ : LSub} {Θ : LocTy} {n : Nat} : ∀ (Γ : Ctx VTy) (γ : List Val)
    (L : List Nat) (ρ : WRes), L.Pairwise (· < ·) →
    (∀ i ∈ L, ∃ s, Γ[i]? = some s ∧ s.live = true) →
    (∀ i s, Γ[i]? = some s → s.live = true → i ∉ L → s.ty.Persistent) →
    Ctx.LiveWithin Γ γ → gN (ℍ := ℍ) δ Θ Γ γ n ρ →
    vN (ℍ := ℍ) (Ctx.capTyOf Γ L) δ Θ n (tupleV (L.map fun i => γ.getD i Val.unit)) ρ
  | [], γ, L, ρ, _, hc, _, _, hg => by
      have hL : L = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
        obtain ⟨s, hs, -⟩ := hc i hi; simp at hs
      subst hL
      have hρ : ρ = PMap.empty := by cases γ <;> exact hg
      exact ⟨rfl, hρ⟩
  | s :: Γ, [], L, ρ, _, hc, _, hw, hg => by
      have hL : L = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
        obtain ⟨s', hs, hl⟩ := hc i hi
        exact absurd (Ctx.LiveWithin.lt hw hs hl) (Nat.not_lt_zero _)
      subst hL
      exact ⟨rfl, hg⟩
  | ⟨T, l⟩ :: Γ, v :: γ, L, ρ, hp, hc, hper, hw, hg => by
      by_cases h0 : 0 ∈ L
      · obtain ⟨L', rfl⟩ : ∃ L', L = 0 :: L' := by
          cases L with
          | nil => simp at h0
          | cons a L' =>
              rcases List.mem_cons.mp h0 with h | h
              · exact ⟨L', by rw [h]⟩
              · exact absurd (List.rel_of_pairwise_cons hp h) (Nat.not_lt_zero _)
        have hpos : ∀ i ∈ L', 0 < i := fun i hi => List.rel_of_pairwise_cons hp hi
        obtain ⟨s₀, hs₀, hl₀⟩ := hc 0 List.mem_cons_self
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hs₀
        subst hs₀
        simp only at hl₀
        subst hl₀
        simp only [gN, if_true] at hg
        obtain ⟨ρ₁, ρ₂, hcρ, hv, hrest⟩ := hg
        have ih := gN_capTyOf Γ γ (L'.map (· - 1)) ρ₂ (pairwise_pred hp.of_cons hpos)
          (fun j hj => by
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
            obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := hpos i hi; omega⟩
            simpa using hc (k + 1) (List.mem_cons_of_mem _ hi))
          (fun j s hs hl hn => hper (j + 1) s (by simpa using hs) hl (by
            intro hm
            rcases List.mem_cons.mp hm with h | h
            · omega
            · exact hn (List.mem_map.mpr ⟨j + 1, h, by simp⟩)))
          hw hrest
        rw [← Ctx.capTyOf_tail L' hpos, ← capVals_tail L' hpos] at ih
        refine ⟨v, _, ρ₁, ρ₂, rfl, hcρ, ?_, ih⟩
        simpa [Ctx.capTyOf, Ctx.slotTy] using hv
      · have hpos : ∀ i ∈ L, 0 < i := fun i hi => Nat.pos_of_ne_zero (fun h => h0 (h ▸ hi))
        have hrest : gN (ℍ := ℍ) δ Θ Γ γ n ρ := by
          cases l with
          | false => simpa [gN] using hg
          | true => exact (gN_cons_persistent (hper 0 ⟨T, true⟩ rfl rfl h0) hg).2
        have ih := gN_capTyOf Γ γ (L.map (· - 1)) ρ (pairwise_pred hp hpos)
          (fun j hj => by
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
            obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := hpos i hi; omega⟩
            simpa using hc (k + 1) hi)
          (fun j s hs hl hn => hper (j + 1) s (by simpa using hs) hl (by
            intro hm
            exact hn (List.mem_map.mpr ⟨j + 1, hm, by simp⟩)))
          hw hrest
        rwa [← Ctx.capTyOf_tail L hpos, ← capVals_tail L hpos] at ih

/-- **`codeI`'s semantic step at the chain's relation**: under `Ctx.CapOK`, the captured values
`capEnv e γ` are in `𝒱⟦Γ.capTy e⟧` at the context's whole resource.  `[spec §68]` -/
theorem gN_capTy {δ : LSub} {Θ : LocTy} {n : Nat} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    {e : Expr} (hok : Ctx.CapOK Γ e) (hw : Ctx.LiveWithin Γ γ) (hg : gN (ℍ := ℍ) δ Θ Γ γ n ρ) :
    vN (ℍ := ℍ) (Ctx.capTy Γ e) δ Θ n (tupleV (Expr.capEnv e γ)) ρ :=
  gN_capTyOf Γ γ _ ρ (Expr.capVars_pairwise e) hok.live
    (fun i s hs hl hn => hok.persistent i s hs hl hn) hw hg

/-! ### A value at `U C`, at its own resource -/

/-- **A value whose `F (U C)` reading holds at every extension of the world is in `𝒱⟦U C⟧`**:
forcing it is a bind at its own run (`cN_bind`). -/
theorem vN_thunk_of_cN {δ : LSub} {Θ : LocTy} {n : Nat} {C : CTy} {w : Val} {ρ : WRes}
    {A : VTy} (hA : ∀ Θ k v σ, vN (ℍ := ℍ) A δ Θ k v σ → vN (ℍ := ℍ) (.thunk C) δ Θ k v σ)
    (h : ∀ Θ', Θ.ExtR Θ' ρ → Θ'.OK → ∀ c', ConsistentX c' ρ → ∀ ls',
      cN (ℍ := ℍ) (.ret A) δ Θ' c' n ls' (.val w) ρ) :
    vN (ℍ := ℍ) (.thunk C) δ Θ n w ρ := by
  intro Θ' hE hΘ' c' hc' ls'
  obtain ⟨K, hK⟩ := forceE_plug C
  rw [hK]
  refine cN_bind C δ Θ' hΘ'.1 K (.val w) (fun k _ v σ => vN (ℍ := ℍ) A δ Θ' k v σ)
    (fun k _ v σ hv => vN_down _ δ Θ' k v σ hv) (fun _ σ => σ = PMap.empty)
    (fun _ _ _ _ h => h) ?_ c' n ls' ρ PMap.empty ρ (ResU.comp_empty_right ρ)
    (fun c'' hc'' => erwp_of_cN_ret (h Θ' hE hΘ' c'' hc'' ls')) rfl hc'
  intro c'' k ls'' v σ₁ σ₂ σ hcσ hv hσ₂ hcons
  subst hσ₂
  rw [ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)] at hcons ⊢
  have := hA Θ' k v σ₁ hv Θ' (LocTy.extR_refl Θ' σ₁) hΘ' c'' hcons ls''
  rw [hK] at this
  exact this

/-! ### The compatibility lemmas -/

/-- **`codeI` at `SemJN`** (Core's `codeI_compatC`).  `[spec §68]` -/
theorem codeI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy}
    (h : SemJN (ℍ := ℍ) Δ Γ (.val (.lam M)) (.val (.thunk C))) (hok : Ctx.CapOK Γ (.lam M)) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.lam M))
      (.val (.code (Expr.capNorm (.lam M)) (Ctx.capTy Γ (.lam M)) C)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) _ _ _ n ls (.val (.lam (Expr.psub 1 γ M))) ρ
  refine erwp_val (v := Val.lam (Expr.psub 1 γ M))
    ⟨⟨Expr.capEnv (.lam M) γ, Expr.lam_psub_capNorm M γ (hok.occs_lt hlw), gN_capTy hok hlw hg⟩,
      vN_thunk_of_cN (fun _ _ _ _ h => h) fun Θ' hE hΘ' c' hc' ls' => ?_⟩
  exact h δ γ Θ' c' n ls' ρ hδ hΘ' hc' hlw (gN_extR hE hg)

/-- **`codeIB` at `SemJN`** (Core's `codeIB_compatC`): over `!Γ`, at `∅` (`gN_persistent`).
`[spec §68]` -/
theorem codeIB_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy} (hp : Ctx.Banged Γ)
    (h : SemJN (ℍ := ℍ) Δ Γ (.val (.lam M)) (.val (.bang (.thunk C))))
    (hok : Ctx.CapOK Γ (.lam M)) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.lam M))
      (.val (.bang (.code (Expr.capNorm (.lam M)) (Ctx.capTy Γ (.lam M)) C))) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) _ _ _ n ls (.val (.lam (Expr.psub 1 γ M))) ρ
  refine erwp_val (v := Val.lam (Expr.psub 1 γ M)) ⟨gN_persistent hp hg,
    ⟨Expr.capEnv (.lam M) γ, Expr.lam_psub_capNorm M γ (hok.occs_lt hlw), gN_capTy hok hlw hg⟩,
      vN_thunk_of_cN (A := .bang (.thunk C)) (fun _ _ _ _ h => h.2)
        fun Θ' hE hΘ' c' hc' ls' => ?_⟩
  exact h δ γ Θ' c' n ls' ρ hδ hΘ' hc' hlw (gN_extR hE hg)

/-- **`codeErase` at `SemJN`** (Core's `codeErase_compatC`): the `U C` conjunct.  `[spec §68]` -/
theorem codeErase_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {N : Expr} {E : VTy} {C : CTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val (.code N E C))) :
    SemJN (ℍ := ℍ) Δ Γ e (.val (.thunk C)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_ret_of ?_
  exact erwp_mono (fun _ _ _ _ hv => hv.2) (opTableN_local _) n ls _ ρ
    (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg))

/-- **`codeEraseB` at `SemJN`** (Core's `codeEraseB_compatC`).  `[spec §68]` -/
theorem codeEraseB_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {N : Expr} {E : VTy} {C : CTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val (.bang (.code N E C)))) :
    SemJN (ℍ := ℍ) Δ Γ e (.val (.bang (.thunk C))) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_ret_of ?_
  exact erwp_mono (fun _ _ _ _ hv => ⟨hv.1, hv.2.2⟩) (opTableN_local _) n ls _ ρ
    (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg))

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
