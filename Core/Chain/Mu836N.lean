import Core.Chain.Rules834N
import Core.Chain.ImmLend833N
import Core.Chain.Fuel835N
import Core.FoldReuse

/-!
# The `μ` rows at `SemJN`  `[spec §6]`

`docs/new-core/scope-831-interface.md` §13. `vN` reads `μX. A` at Core's least fixed point
(`vNE`'s `μ` clause), the candidate joint over the mode, the world and the index; unfolding costs
no step, as in Core, where the machine has no `roll`/`unroll` step.

* `roll_compatN`, `unroll_compatN`: Core's `roll_compatX`, `unroll_compatX`, with `vN_roll` and
  `vN_unfold` under `erwp_mono`.
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
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-- **`roll` at `SemJN`** (Core's `roll_compatX`): a value of `A[μX. A/X]` is a value of
`μX. A`, at the same index. -/
theorem roll_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} (hA : A.NoMut 0)
    (hc : (VTy.mu A).Cl 0) (h : SemJN (ℍ := ℍ) Δ Γ e (.val (VTy.inst (.mu A) A))) :
    SemJN (ℍ := ℍ) Δ Γ e (.val (.mu A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hcρ hlw hg
  exact erwp_mono (fun _ _ _ _ hv => vN_roll hA hc hv) (opTableN_local _) n ls _ ρ
    (h δ γ Θ c n ls ρ hδ hΘ hcρ hlw hg)

/-- **`unroll` at `SemJN`** (Core's `unroll_compatX`): a value of `μX. A` is a value of
`A[μX. A/X]`, at the same index. -/
theorem unroll_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val (.mu A))) :
    SemJN (ℍ := ℍ) Δ Γ e (.val (VTy.inst (.mu A) A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hcρ hlw hg
  exact erwp_mono (fun _ _ _ _ hv => (vN_unfold hv).2.2) (opTableN_local _) n ls _ ρ
    (h δ γ Θ c n ls ρ hδ hΘ hcρ hlw hg)

/-! ### `foldOwn` (Core's `Core/FoldOwn.lean`)

The term is Core's (`foldOwnV`, `travO`, `selfO`, `hO`) and so are its reductions; each pure step is
`erwp_det` at the same index, a `free` costs one (`erwp_free`). The induction is Core's: on a
bound of the owned resource's size (`dsize`), then on the size of the value. The run is at one
world and one view; the algebra is read at that world (`vN_extR` at its empty resource), at
every index below the fold's. -/

section FoldOwn

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-- `travO G h w` steps to its body (Core's `travO_app`). -/
theorem travO_appN {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) (G : FShape) (h w : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (((tO G).subst 1 (h.shift 1 0)).subst 0 w) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (.app (.app (.val (travO G)) (.val h)) (.val w)) ρ := by
  rw [travO_eq]
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ h) rfl (.appL .hole w)) ?_
  exact erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) hw

/-- `h w` for `h = λw. self g w` reaches `travO T h w to r. g r` (Core's `hO_app`). -/
theorem hO_appN {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) (F : FShape) (g w : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      ((Kont.appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole).plug
        (.app (.app (.val (travO F)) (.val (hO F g))) (.val w))) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.val (hO F g)) (.val w)) ρ := by
  have hT := opTableN_down OpTabN.empty_down
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  have e₁ : Expr.subst 0 w (.app (.app (.val (selfO F)) (.val (g.shift 1 0))) (.var 0))
      = .app (.app (.val (selfO F)) (.val g)) (.val w) := by
    simp [closed_subst (selfO_closed F), subst_shift_succ]
  rw [e₁]
  refine erwp_pureSteps hΦ hT hQ (selfV_steps_in (fBO_closed F) (.appL .hole w) g) ?_
  rw [fixV_eq (fBO_closed F)]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ g) rfl (.appL .hole w)) ?_
  rw [fBO_subst F (selfO_closed F)]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [fBO_body F (selfO_closed F)]
  exact hw

/-- The post of a run at `𝒱⟦R⟧`. -/
abbrev vPostN (R : VTy) (δ : LSub) (Θ : LocTy) : PostN := fun k _ v ρ => vN (ℍ := ℍ) R δ Θ k v ρ

theorem vPostN_down (R : VTy) (δ : LSub) (Θ : LocTy) : (vPostN (ℍ := ℍ) R δ Θ).Down :=
  fun k _ v ρ h => vN_down R δ Θ k v ρ h

/-- The recursive call on a value of `M` whose resource has at most `n` cells, smaller than `K`,
at every index up to `N` (Core's `HOSpec`). -/
def HOSpecN (M R : VTy) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (N n K : Nat) (h : Val) :
    Prop :=
  ∀ w χ k ls, k ≤ N → sizeOf w.1 < K → vN (ℍ := ℍ) M δ Θ k w χ → dsize χ ≤ n → ConsistentX c χ →
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) k ls (.app (.val h) (.val w)) χ

/-- **The owned traversal** (Core's `travO_spec`): at a sub-shape `G`, `travO G h w` takes
`w : G[M/X]` to a value of `G.resO R`, given the recursive call on a value of fewer cells (`hP`,
through a freed `Ref`) and on a smaller value (`hH`, at a head `X`). -/
theorem travO_specN {M R : VTy} {δ : LSub} {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life}
    {N n K : Nat} {h : Val}
    (hP : ∀ w ρ k ls, k ≤ N → vN (ℍ := ℍ) M δ Θ k w ρ → dsize ρ < n → ConsistentX c ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) k ls
        (.app (.val h) (.val w)) ρ)
    (hH : HOSpecN (ℍ := ℍ) M R δ Θ c N n K h) :
    ∀ (G : FShape), G.WF → ∀ w χ k ls, k ≤ N → sizeOf w.1 ≤ K → (G = .varX → sizeOf w.1 < K) →
      vN (ℍ := ℍ) (VTy.inst M G.ty) δ Θ k w χ → dsize χ ≤ n → ConsistentX c χ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN (G.resO R) δ Θ) k ls
        (.app (.app (.val (travO G)) (.val h)) (.val w)) χ
  | .leaf A, hA, w, χ, k, ls, _, _, _, hv, _, _ => by
      refine travO_appN (LocTy.view_down hΘ c) (vPostN_down _ δ Θ) _ h w ?_
      rw [tO_leaf]
      have e : VTy.inst M A = A := VTy.subst_closed0 hA _
      simp only [FShape.ty, e] at hv
      exact erwp_val hv
  | .refX, _, w, χ, k, ls, hkN, _, _, hv, hn, hcχ => by
      refine travO_appN (LocTy.view_down hΘ c) (vPostN_down _ δ Θ) _ h w ?_
      rw [tO_refX]
      change vN (ℍ := ℍ) (.ref M) δ Θ k w χ at hv
      obtain ⟨ℓ, v', σ, rfl, hc, hM⟩ := hv
      refine erwp_of_valid fun hvχ => ?_
      refine erwp_free (LocTy.view_down hΘ c) (opTableN_local _) (.appR (.val h) .hole) ℓ v'
        ⟨_, σ, hc, rfl, ?_⟩
      exact hP v' σ (k - 1) ls (le_trans (Nat.sub_le k 1) hkN) (vN_le (Nat.sub_le k 1) hM)
        (lt_of_lt_of_le (dsize_tail_lt hc ⟨PMap.empty, ResU.comp_empty_right _⟩) hn)
        (consistentX_right hc hcχ hvχ)
  | .varX, _, w, χ, k, ls, hkN, _, hlt, hv, hn, hcχ => by
      refine travO_appN (LocTy.view_down hΘ c) (vPostN_down _ δ Θ) _ h w ?_
      rw [tO_varX]
      exact hH w χ k ls hkN (hlt rfl) hv hn hcχ
  | .tensor F G, hFG, w, χ, k, ls, hkN, hK, _, hv, hn, hcχ => by
      obtain ⟨v₁, v₂, χ₁, χ₂, rfl, hc, h₁, h₂⟩ := hv
      have hs₁ : sizeOf v₁.1 < K := by rw [sizeOf_pair] at hK; omega
      have hs₂ : sizeOf v₂.1 < K := by rw [sizeOf_pair] at hK; omega
      have hΦ := LocTy.view_down hΘ c
      have hT := opTableN_down OpTabN.empty_down
      refine travO_appN hΦ (vPostN_down _ δ Θ) _ h _ ?_
      rw [tO_tensor]
      refine erwp_det hΦ hT (vPostN_down _ δ Θ)
        (fun μ => step1Only_plug (Head.letpair μ v₁ v₂ _) rfl .hole) ?_
      rw [tensorO_body]
      refine erwp_of_valid fun hvχ => ?_
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.lam (bindE (.app (.app (.val (travO G)) (.val (h.shift 1 0)))
          (.val (v₂.shift 1 0))) (.pair (.var 1) (.var 0))))) .hole)
        (fun ρ => vN (ℍ := ℍ) (VTy.inst M G.ty) δ Θ k v₂ ρ ∧ dsize ρ ≤ n) hc hcχ
        (travO_specN hΘ hP hH F hFG.1 v₁ χ₁ k ls hkN (le_of_lt hs₁) (fun _ => hs₁) h₁
          (le_trans (dsize_le_left hc) hn) (consistentX_left hc hcχ hvχ))
        ⟨h₂, le_trans (dsize_le_right hc) hn⟩ ?_
      intro k' hk' ls' r₁ σ₁ σ₂ σ hcσ hr₁ ⟨hv₂, hn₂⟩ hcσ' hvσ
      simp only [Kont.plug]
      refine erwp_det hΦ hT (vPostN_down _ δ Θ)
        (fun μ => step1Only_plug (Head.beta μ _ r₁) rfl .hole) ?_
      rw [tensorO_body₂]
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.lam (.pair (.val (r₁.shift 1 0)) (.var 0)))) .hole)
        (fun ρ => vN (ℍ := ℍ) (F.resO R) δ Θ k' r₁ ρ)
        (ResU.CompS.comm hcσ) hcσ'
        (travO_specN hΘ hP hH G hFG.2 v₂ σ₂ k' ls' (le_trans hk' hkN) (le_of_lt hs₂) (fun _ => hs₂)
          (vN_le hk' hv₂) hn₂ (consistentX_right hcσ hcσ' hvσ)) hr₁ ?_
      intro k'' hk'' ls'' r₂ τ₁ τ₂ τ hcτ hr₂ hr₁' _ _
      simp only [Kont.plug]
      refine erwp_det hΦ hT (vPostN_down _ δ Θ)
        (fun μ => step1Only_plug (Head.beta μ _ r₂) rfl .hole) ?_
      rw [tensor_body₃]
      exact erwp_val ⟨r₁, r₂, τ₂, τ₁, rfl, ResU.CompS.comm hcτ, vN_le hk'' hr₁', hr₂⟩
  | .sum F G, hFG, w, χ, k, ls, hkN, hK, _, hv, hn, hcχ => by
      have hΦ := LocTy.view_down hΘ c
      have hT := opTableN_down OpTabN.empty_down
      rcases hv with ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
      · have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₁ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travO_appN hΦ (vPostN_down _ δ Θ) _ h _ ?_
        rw [tO_sum]
        refine erwp_det hΦ hT (vPostN_down _ δ Θ)
          (fun μ => step1Only_plug (Head.case₁ μ v _ _) rfl .hole) ?_
        rw [sumO_branch F h v Expr.inj₁ (fun _ _ _ => rfl)]
        refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam (Expr.inj₁ (.var 0)))) .hole)
          (fun ρ => ρ = PMap.empty)
          (ResU.comp_empty_right χ) hcχ
          (travO_specN hΘ hP hH F hFG.1 v χ k ls hkN (le_of_lt hsz) (fun _ => hsz) hv hn hcχ) rfl ?_
        intro k' _ ls' r σ₁ σ₂ σ hcσ hr hσ₂ _ _
        subst hσ₂
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_det hΦ hT (vPostN_down _ δ Θ)
          (fun μ => step1Only_plug (Head.beta μ _ r) rfl .hole) ?_
        exact erwp_val (v := Val.inj₁ r) (.inl ⟨r, rfl, hr⟩)
      · have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₂ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travO_appN hΦ (vPostN_down _ δ Θ) _ h _ ?_
        rw [tO_sum]
        refine erwp_det hΦ hT (vPostN_down _ δ Θ)
          (fun μ => step1Only_plug (Head.case₂ μ v _ _) rfl .hole) ?_
        rw [sumO_branch G h v Expr.inj₂ (fun _ _ _ => rfl)]
        refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam (Expr.inj₂ (.var 0)))) .hole)
          (fun ρ => ρ = PMap.empty)
          (ResU.comp_empty_right χ) hcχ
          (travO_specN hΘ hP hH G hFG.2 v χ k ls hkN (le_of_lt hsz) (fun _ => hsz) hv hn hcχ) rfl ?_
        intro k' _ ls' r σ₁ σ₂ σ hcσ hr hσ₂ _ _
        subst hσ₂
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_det hΦ hT (vPostN_down _ δ Θ)
          (fun μ => step1Only_plug (Head.beta μ _ r) rfl .hole) ?_
        exact erwp_val (v := Val.inj₂ r) (.inr ⟨r, rfl, hr⟩)

/-- **The recursive call**, at every resource bound `n` and value bound `K` (Core's
`hOSpec_all`): strong induction on `n`, then induction on `K`. -/
theorem hOSpecN_all {F : FShape} (hF : F.WF) (hG : F.Guarded) {R : VTy} {δ : LSub} {Θ : LocTy}
    (hΘ : Θ.Down) {c : Loc → Option Life} {N : Nat} {g : Val}
    (hg : ∀ k ls r σ, k ≤ N → vN (ℍ := ℍ) (F.resO R) δ Θ k r σ → ConsistentX c σ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) k ls
        (.app (.val g) (.val r)) σ) :
    ∀ n K, HOSpecN (ℍ := ℍ) (.mu F.ty) R δ Θ c N n K (hO F g) := by
  have hΦ := LocTy.view_down hΘ c
  have hT := opTableN_down OpTabN.empty_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    have hP : ∀ w ρ k ls, k ≤ N → vN (ℍ := ℍ) (.mu F.ty) δ Θ k w ρ → dsize ρ < n →
        ConsistentX c ρ → erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) k ls
          (.app (.val (hO F g)) (.val w)) ρ :=
      fun w ρ k ls hkN hv hlt hcρ =>
        ihn (dsize ρ) hlt (sizeOf w.1 + 1) w ρ k ls hkN (Nat.lt_succ_self _) hv le_rfl hcρ
    intro K
    induction K with
    | zero => intro w χ k ls _ hlt; exact absurd hlt (Nat.not_lt_zero _)
    | succ K ihK =>
        intro w χ k ls hkN hlt hv hn hcχ
        refine hO_appN hΦ (vPostN_down _ δ Θ) F g w ?_
        refine erwp_bind_frame hΦ (opTableN_local _)
          (.appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole) (fun ρ => ρ = PMap.empty)
          (ResU.comp_empty_right χ) hcχ
          (travO_specN hΘ hP ihK F hF w χ k ls hkN (Nat.lt_succ_iff.mp hlt)
            (fun e => by subst e; exact hG.elim) (vN_unfold hv).2.2 hn hcχ) rfl ?_
        intro k' hk' ls' r σ₁ σ₂ σ hcσ hr hσ₂ hcσ' _
        subst hσ₂
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_det hΦ hT (vPostN_down _ δ Θ)
          (fun μ => step1Only_plug (Head.beta μ _ r) rfl .hole) ?_
        rw [algO_subst]
        exact hg k' ls' r _ (le_trans hk' hkN) hr hcσ'

/-- **The owned fold at `SemJN`** (Core's `foldOwn_compatX`): `foldOwn : !U(A′_R ⊸ F R) ⊸
!U(μX. T ⊸ F R)` at every `T` of the class `FShape` and every `R`. -/
theorem foldOwn_compatN {Δ : LifeCtx} {Γ : Ctx VTy} (F : FShape) (hF : F.WF) (hG : F.Guarded)
    (R : VTy) (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (foldOwnV F)) (.val (.lolli (algOTy F R) (foldOTy F R))) := by
  intro δ γ Θ c n ls ρ _ hΘ _ _ hg₀
  have hρ : ρ = PMap.empty := gN_deadP hΓ hg₀
  subst hρ
  show erwp (ℍ := ℍ) _ _ _ n ls (substAll γ (.val (foldOwnV F))) _
  rw [substAll_closed (foldOwnV_closed F)]
  refine erwp_val ?_
  intro Θ₁ hE₁ hOK₁ c₁ _ ls₁ c₂ k₁ hk₁ g ρv ρ' hcomp hv₁ _
  have hρv : ρv = PMap.empty := hv₁.1
  subst hρv
  obtain rfl := eq_of_compS_empty_left hcomp
  have hΦ := LocTy.view_down hOK₁.1 c₂
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (vPostN_down _ δ Θ₁)
    (fun μ => step1Only_plug (Head.beta μ _ g) rfl .hole) ?_
  rw [foldOwnV_subst]
  refine erwp_val ⟨rfl, ?_⟩
  intro Θ₂ hE₂ hOK₂ c₃ _ ls₂ c₄ k₂ hk₂ w ρw ρ'' hcomp' hw hc₄
  obtain rfl := eq_of_compS_empty_left hcomp'
  have hg₂ : vN (ℍ := ℍ) (algOTy F R) δ Θ₂ k₁ g PMap.empty := vN_extR _ δ k₁ g _ hE₂ hv₁
  have hgA : ∀ k ls r σ, k ≤ k₂ → vN (ℍ := ℍ) (F.resO R) δ Θ₂ k r σ → ConsistentX c₄ σ →
      erwp (ℍ := ℍ) (Θ₂.view c₄) (opTableN OpTabN.empty) (vPostN R δ Θ₂) k ls
        (.app (.val g) (.val r)) σ :=
    fun k ls r σ hk hr hcσ => hg₂.2 Θ₂ (LocTy.extR_refl _ _) hOK₂ c₄ (consistentX_empty c₄) ls c₄ k
      (le_trans hk hk₂) r σ σ (compS_empty_left σ) hr hcσ
  exact hOSpecN_all hF hG hOK₂.1 hgA (dsize ρ'') (sizeOf w.1 + 1) w ρ'' k₂ ls₂ le_rfl
    (Nat.lt_succ_self _) hw le_rfl hc₄

end FoldOwn

/-! ### `foldReuse` (Core's `Core/FoldReuse.lean`)

`foldOwn`'s port with the `Ref X` clause replaced: the cell is emptied by `swap w ()` (`erwp_swapN`,
Core's `wpTS_swap`: a load and a store, one step each), and the emptied cell goes to the algebra
beside the recursive result. -/

section FoldReuse

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-- **`swap ℓ v`** at `ℓ ↦ w` returns `(ℓ, w)` with `ℓ ↦ v` (Core's `wpTS_swap`): the load and the
store cost one step each. -/
theorem erwp_swapN {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) (ℓ : Loc) (w v : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : (sep (ptoOwn ℓ w) (wand (ptoOwn ℓ v) (Q (n - 1 - 1) ls (.pair (.loc ℓ) w)))) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.app swap (.val (.loc ℓ))) (.val v)) ρ := by
  obtain ⟨ρo, ρR, hc, rfl, hR⟩ := h
  have hT := opTableN_down OpTabN.empty_down
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (elet (.app load' BoCa.v1)
          (.seq (.app (.app store' BoCa.v2) BoCa.v1) (.pair BoCa.v2 BoCa.v0)))))
      = Expr.val (Val.lam (elet (eLoad ℓ)
          (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                (.pair (.val (.loc ℓ)) BoCa.v0)))) := by
    simp [elet, eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, BoCa.v2, load', store']
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc ℓ)) rfl (.appL .hole v)) ?_
  rw [hβ₁]
  simp only [Kont.plug]
  have hβ₂ : Expr.subst 0 v
        (elet (eLoad ℓ) (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                              (.pair (.val (.loc ℓ)) BoCa.v0)))
      = elet (eLoad ℓ) (.seq (eStore ℓ (v.shift 1 0)) (.pair (.val (.loc ℓ)) BoCa.v0)) := by
    simp [elet, eLoad, eStore, Expr.subst, BoCa.v0, BoCa.v1, store']
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  rw [hβ₂]
  refine erwp_bindR hΦ (opTableN_local _) (.appR (.val (.lam _)) .hole) ?_
  refine rwp_load ls ℓ w _ ⟨_, ρR, hc, rfl, fun c₁ p₁ hc₁ hp₁ => ?_⟩
  obtain rfl := hc₁
  simp only [Kont.plug]
  have hβ₃ : Expr.subst 0 w
        (Expr.seq (eStore ℓ (v.shift 1 0)) (.pair (.val (.loc ℓ)) BoCa.v0))
      = Expr.seq (eStore ℓ v) (.pair (.val (.loc ℓ)) (.val w)) := by
    simp [eStore, Expr.subst, BoCa.v0,
      Expr.subst_shift 0 0 0 w v.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [hβ₃, show eStore ℓ v = .app (.val (Val.storeV (Val.loc ℓ))) (.val v) from rfl]
  refine erwp_bindR hΦ (opTableN_local _) (.seq .hole (.pair (.val (.loc ℓ)) (.val w))) ?_
  refine rwp_store ls ℓ w v _ ⟨_, ρR, ResU.CompS.comm hp₁, rfl, fun c₃ p₃ hc₃ hp₃ => ?_⟩
  simp only [Kont.plug]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  exact erwp_val (v := Val.pair (.loc ℓ) w) (hR c₃ p₃ hc₃ hp₃)

theorem travR_appN {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) (G : FShape) (h w : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (((tR G).subst 1 (h.shift 1 0)).subst 0 w) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (.app (.app (.val (travR G)) (.val h)) (.val w)) ρ := by
  rw [travR_eq]
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ h) rfl (.appL .hole w)) ?_
  exact erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) hw

theorem hR_appN {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) (F : FShape) (g w : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      ((Kont.appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole).plug
        (.app (.app (.val (travR F)) (.val (hR F g))) (.val w))) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.val (hR F g)) (.val w)) ρ := by
  have hT := opTableN_down OpTabN.empty_down
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  have e₁ : Expr.subst 0 w (.app (.app (.val (selfR F)) (.val (g.shift 1 0))) (.var 0))
      = .app (.app (.val (selfR F)) (.val g)) (.val w) := by
    simp [closed_subst (selfR_closed F), subst_shift_succ]
  rw [e₁]
  refine erwp_pureSteps hΦ hT hQ (selfV_steps_in (fBR_closed F) (.appL .hole w) g) ?_
  rw [fixV_eq (fBR_closed F)]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ g) rfl (.appL .hole w)) ?_
  rw [fBR_subst F (selfR_closed F)]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [fBR_body F (selfR_closed F)]
  exact hw

/-- The recursive call (Core's `HRSpec`). -/
def HRSpecN (M R : VTy) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (N n K : Nat) (h : Val) :
    Prop :=
  ∀ w χ k ls, k ≤ N → sizeOf w.1 < K → vN (ℍ := ℍ) M δ Θ k w χ → dsize χ ≤ n → ConsistentX c χ →
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) k ls (.app (.val h) (.val w)) χ

/-- **The owned traversal with reuse** (Core's `travR_spec`). -/
theorem travR_specN {M R : VTy} {δ : LSub} {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life}
    {N n K : Nat} {h : Val}
    (hP : ∀ w ρ k ls, k ≤ N → vN (ℍ := ℍ) M δ Θ k w ρ → dsize ρ < n → ConsistentX c ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) k ls
        (.app (.val h) (.val w)) ρ)
    (hH : HRSpecN (ℍ := ℍ) M R δ Θ c N n K h) :
    ∀ (G : FShape), G.WF → ∀ w χ k ls, k ≤ N → sizeOf w.1 ≤ K → (G = .varX → sizeOf w.1 < K) →
      vN (ℍ := ℍ) (VTy.inst M G.ty) δ Θ k w χ → dsize χ ≤ n → ConsistentX c χ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN (G.resR R) δ Θ) k ls
        (.app (.app (.val (travR G)) (.val h)) (.val w)) χ
  | .leaf A, hA, w, χ, k, ls, _, _, _, hv, _, _ => by
      refine travR_appN (LocTy.view_down hΘ c) (vPostN_down _ δ Θ) _ h w ?_
      rw [tR_leaf]
      have e : VTy.inst M A = A := VTy.subst_closed0 hA _
      simp only [FShape.ty, e] at hv
      exact erwp_val hv
  | .refX, _, w, χ, k, ls, hkN, _, _, hv, hn, hcχ => by
      have hΦ := LocTy.view_down hΘ c
      have hT := opTableN_down OpTabN.empty_down
      refine travR_appN hΦ (vPostN_down _ δ Θ) _ h w ?_
      rw [tR_refX]
      change vN (ℍ := ℍ) (.ref M) δ Θ k w χ at hv
      obtain ⟨ℓ, v', ρb, rfl, hc, hM⟩ := hv
      have hlt : dsize ρb < n :=
        lt_of_lt_of_le (dsize_tail_lt hc ⟨PMap.empty, ResU.comp_empty_right _⟩) hn
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.lam (.letpair (.var 0) (bindE (.app (.val (h.shift 3 0)) (.var 0))
          (.pair (.var 2) (.var 0)))))) .hole)
        (P := fun _ _ q σ => q = Val.pair (.loc ℓ) v' ∧ σ = ResU.single ℓ (CellU.ownOf .unit))
        (fun σ => vN (ℍ := ℍ) M δ Θ k v' σ ∧ dsize σ < n) hc hcχ
        (erwp_swapN hΦ (fun _ _ _ _ h => h) ℓ v' .unit
          ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, fun σa σ hσa hcσ => ⟨rfl, by
            rw [ResU.CompS.functional hcσ (compS_empty_left σa)]; exact hσa⟩⟩) ⟨hM, hlt⟩ ?_
      rintro k' hk' ls' q σ₁ σ₂ σ hcσ ⟨rfl, rfl⟩ ⟨hM', hlt'⟩ hcσ' hvσ
      simp only [Kont.plug]
      refine erwp_det hΦ hT (vPostN_down _ δ Θ)
        (fun μ => step1Only_plug (Head.beta μ _ (Val.pair (.loc ℓ) v')) rfl .hole) ?_
      refine erwp_det hΦ hT (vPostN_down _ δ Θ)
        (fun μ => step1Only_plug (Head.letpair μ (.loc ℓ) v' _) rfl .hole) ?_
      rw [refR_body]
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.lam (.pair (.val (.loc ℓ)) (.var 0)))) .hole)
        (fun τ => τ = ResU.single ℓ (CellU.ownOf .unit)) (ResU.CompS.comm hcσ) hcσ'
        (hP v' σ₂ k' ls' (le_trans hk' hkN) (vN_le hk' hM') hlt'
          (consistentX_right hcσ hcσ' hvσ)) rfl ?_
      intro k'' hk'' ls'' r τ₁ τ₂ τ hcτ hr hτ₂ _ _
      subst hτ₂
      simp only [Kont.plug]
      refine erwp_det hΦ hT (vPostN_down _ δ Θ)
        (fun μ => step1Only_plug (Head.beta μ _ r) rfl .hole) ?_
      have e : (Expr.pair (.val (Val.loc ℓ)) (.var 0)).subst 0 r = .val (Val.pair (.loc ℓ) r) := by
        simp
      rw [e]
      exact erwp_val ⟨.loc ℓ, r, _, τ₁, rfl, ResU.CompS.comm hcτ,
        ⟨ℓ, .unit, PMap.empty, rfl, ResU.comp_empty_right _, rfl, rfl⟩, hr⟩
  | .varX, _, w, χ, k, ls, hkN, _, hlt, hv, hn, hcχ => by
      refine travR_appN (LocTy.view_down hΘ c) (vPostN_down _ δ Θ) _ h w ?_
      rw [tR_varX]
      exact hH w χ k ls hkN (hlt rfl) hv hn hcχ
  | .tensor F G, hFG, w, χ, k, ls, hkN, hK, _, hv, hn, hcχ => by
      obtain ⟨v₁, v₂, χ₁, χ₂, rfl, hc, h₁, h₂⟩ := hv
      have hs₁ : sizeOf v₁.1 < K := by rw [sizeOf_pair] at hK; omega
      have hs₂ : sizeOf v₂.1 < K := by rw [sizeOf_pair] at hK; omega
      have hΦ := LocTy.view_down hΘ c
      have hT := opTableN_down OpTabN.empty_down
      refine travR_appN hΦ (vPostN_down _ δ Θ) _ h _ ?_
      rw [tR_tensor]
      refine erwp_det hΦ hT (vPostN_down _ δ Θ)
        (fun μ => step1Only_plug (Head.letpair μ v₁ v₂ _) rfl .hole) ?_
      rw [tensorR_body]
      refine erwp_of_valid fun hvχ => ?_
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.lam (bindE (.app (.app (.val (travR G)) (.val (h.shift 1 0)))
          (.val (v₂.shift 1 0))) (.pair (.var 1) (.var 0))))) .hole)
        (fun ρ => vN (ℍ := ℍ) (VTy.inst M G.ty) δ Θ k v₂ ρ ∧ dsize ρ ≤ n) hc hcχ
        (travR_specN hΘ hP hH F hFG.1 v₁ χ₁ k ls hkN (le_of_lt hs₁) (fun _ => hs₁) h₁
          (le_trans (dsize_le_left hc) hn) (consistentX_left hc hcχ hvχ))
        ⟨h₂, le_trans (dsize_le_right hc) hn⟩ ?_
      intro k' hk' ls' r₁ σ₁ σ₂ σ hcσ hr₁ ⟨hv₂, hn₂⟩ hcσ' hvσ
      simp only [Kont.plug]
      refine erwp_det hΦ hT (vPostN_down _ δ Θ)
        (fun μ => step1Only_plug (Head.beta μ _ r₁) rfl .hole) ?_
      rw [tensorR_body₂]
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.lam (.pair (.val (r₁.shift 1 0)) (.var 0)))) .hole)
        (fun ρ => vN (ℍ := ℍ) (F.resR R) δ Θ k' r₁ ρ)
        (ResU.CompS.comm hcσ) hcσ'
        (travR_specN hΘ hP hH G hFG.2 v₂ σ₂ k' ls' (le_trans hk' hkN) (le_of_lt hs₂) (fun _ => hs₂)
          (vN_le hk' hv₂) hn₂ (consistentX_right hcσ hcσ' hvσ)) hr₁ ?_
      intro k'' hk'' ls'' r₂ τ₁ τ₂ τ hcτ hr₂ hr₁' _ _
      simp only [Kont.plug]
      refine erwp_det hΦ hT (vPostN_down _ δ Θ)
        (fun μ => step1Only_plug (Head.beta μ _ r₂) rfl .hole) ?_
      rw [tensor_body₃]
      exact erwp_val ⟨r₁, r₂, τ₂, τ₁, rfl, ResU.CompS.comm hcτ, vN_le hk'' hr₁', hr₂⟩
  | .sum F G, hFG, w, χ, k, ls, hkN, hK, _, hv, hn, hcχ => by
      have hΦ := LocTy.view_down hΘ c
      have hT := opTableN_down OpTabN.empty_down
      rcases hv with ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
      · have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₁ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travR_appN hΦ (vPostN_down _ δ Θ) _ h _ ?_
        rw [tR_sum]
        refine erwp_det hΦ hT (vPostN_down _ δ Θ)
          (fun μ => step1Only_plug (Head.case₁ μ v _ _) rfl .hole) ?_
        rw [sumR_branch F h v Expr.inj₁ (fun _ _ _ => rfl)]
        refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam (Expr.inj₁ (.var 0)))) .hole)
          (fun ρ => ρ = PMap.empty) (ResU.comp_empty_right χ) hcχ
          (travR_specN hΘ hP hH F hFG.1 v χ k ls hkN (le_of_lt hsz) (fun _ => hsz) hv hn hcχ) rfl ?_
        intro k' _ ls' r σ₁ σ₂ σ hcσ hr hσ₂ _ _
        subst hσ₂
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_det hΦ hT (vPostN_down _ δ Θ)
          (fun μ => step1Only_plug (Head.beta μ _ r) rfl .hole) ?_
        exact erwp_val (v := Val.inj₁ r) (.inl ⟨r, rfl, hr⟩)
      · have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₂ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine travR_appN hΦ (vPostN_down _ δ Θ) _ h _ ?_
        rw [tR_sum]
        refine erwp_det hΦ hT (vPostN_down _ δ Θ)
          (fun μ => step1Only_plug (Head.case₂ μ v _ _) rfl .hole) ?_
        rw [sumR_branch G h v Expr.inj₂ (fun _ _ _ => rfl)]
        refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam (Expr.inj₂ (.var 0)))) .hole)
          (fun ρ => ρ = PMap.empty) (ResU.comp_empty_right χ) hcχ
          (travR_specN hΘ hP hH G hFG.2 v χ k ls hkN (le_of_lt hsz) (fun _ => hsz) hv hn hcχ) rfl ?_
        intro k' _ ls' r σ₁ σ₂ σ hcσ hr hσ₂ _ _
        subst hσ₂
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_det hΦ hT (vPostN_down _ δ Θ)
          (fun μ => step1Only_plug (Head.beta μ _ r) rfl .hole) ?_
        exact erwp_val (v := Val.inj₂ r) (.inr ⟨r, rfl, hr⟩)

/-- **The recursive call** (Core's `hRSpec_all`). -/
theorem hRSpecN_all {F : FShape} (hF : F.WF) (hG : F.Guarded) {R : VTy} {δ : LSub} {Θ : LocTy}
    (hΘ : Θ.Down) {c : Loc → Option Life} {N : Nat} {g : Val}
    (hg : ∀ k ls r σ, k ≤ N → vN (ℍ := ℍ) (F.resR R) δ Θ k r σ → ConsistentX c σ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) k ls
        (.app (.val g) (.val r)) σ) :
    ∀ n K, HRSpecN (ℍ := ℍ) (.mu F.ty) R δ Θ c N n K (hR F g) := by
  have hΦ := LocTy.view_down hΘ c
  have hT := opTableN_down OpTabN.empty_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    have hP : ∀ w ρ k ls, k ≤ N → vN (ℍ := ℍ) (.mu F.ty) δ Θ k w ρ → dsize ρ < n →
        ConsistentX c ρ → erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN R δ Θ) k ls
          (.app (.val (hR F g)) (.val w)) ρ :=
      fun w ρ k ls hkN hv hlt hcρ =>
        ihn (dsize ρ) hlt (sizeOf w.1 + 1) w ρ k ls hkN (Nat.lt_succ_self _) hv le_rfl hcρ
    intro K
    induction K with
    | zero => intro w χ k ls _ hlt; exact absurd hlt (Nat.not_lt_zero _)
    | succ K ihK =>
        intro w χ k ls hkN hlt hv hn hcχ
        refine hR_appN hΦ (vPostN_down _ δ Θ) F g w ?_
        refine erwp_bind_frame hΦ (opTableN_local _)
          (.appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole) (fun ρ => ρ = PMap.empty)
          (ResU.comp_empty_right χ) hcχ
          (travR_specN hΘ hP ihK F hF w χ k ls hkN (Nat.lt_succ_iff.mp hlt)
            (fun e => by subst e; exact hG.elim) (vN_unfold hv).2.2 hn hcχ) rfl ?_
        intro k' hk' ls' r σ₁ σ₂ σ hcσ hr hσ₂ hcσ' _
        subst hσ₂
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_det hΦ hT (vPostN_down _ δ Θ)
          (fun μ => step1Only_plug (Head.beta μ _ r) rfl .hole) ?_
        rw [algR_subst]
        exact hg k' ls' r _ (le_trans hk' hkN) hr hcσ'

/-- **The owned fold with reuse at `SemJN`** (Core's `foldReuse_compatX`). -/
theorem foldReuse_compatN {Δ : LifeCtx} {Γ : Ctx VTy} (F : FShape) (hF : F.WF) (hG : F.Guarded)
    (R : VTy) (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (foldReuseV F)) (.val (.lolli (algRTy F R) (foldOTy F R))) := by
  intro δ γ Θ c n ls ρ _ hΘ _ _ hg₀
  have hρ : ρ = PMap.empty := gN_deadP hΓ hg₀
  subst hρ
  show erwp (ℍ := ℍ) _ _ _ n ls (substAll γ (.val (foldReuseV F))) _
  rw [substAll_closed (foldReuseV_closed F)]
  refine erwp_val ?_
  intro Θ₁ hE₁ hOK₁ c₁ _ ls₁ c₂ k₁ hk₁ g ρv ρ' hcomp hv₁ _
  have hρv : ρv = PMap.empty := hv₁.1
  subst hρv
  obtain rfl := eq_of_compS_empty_left hcomp
  have hΦ := LocTy.view_down hOK₁.1 c₂
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (vPostN_down _ δ Θ₁)
    (fun μ => step1Only_plug (Head.beta μ _ g) rfl .hole) ?_
  rw [foldReuseV_subst]
  refine erwp_val ⟨rfl, ?_⟩
  intro Θ₂ hE₂ hOK₂ c₃ _ ls₂ c₄ k₂ hk₂ w ρw ρ'' hcomp' hw hc₄
  obtain rfl := eq_of_compS_empty_left hcomp'
  have hg₂ : vN (ℍ := ℍ) (algRTy F R) δ Θ₂ k₁ g PMap.empty := vN_extR _ δ k₁ g _ hE₂ hv₁
  have hgA : ∀ k ls r σ, k ≤ k₂ → vN (ℍ := ℍ) (F.resR R) δ Θ₂ k r σ → ConsistentX c₄ σ →
      erwp (ℍ := ℍ) (Θ₂.view c₄) (opTableN OpTabN.empty) (vPostN R δ Θ₂) k ls
        (.app (.val g) (.val r)) σ :=
    fun k ls r σ hk hr hcσ => hg₂.2 Θ₂ (LocTy.extR_refl _ _) hOK₂ c₄ (consistentX_empty c₄) ls c₄ k
      (le_trans hk hk₂) r σ σ (compS_empty_left σ) hr hcσ
  exact hRSpecN_all hF hG hOK₂.1 hgA (dsize ρ'') (sizeOf w.1 + 1) w ρ'' k₂ ls₂ le_rfl
    (Nat.lt_succ_self _) hw le_rfl hc₄

end FoldReuse

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
