import Core.Computation

/-!
# Core — Compatibility of the CBPV rules  `[spec §3]`

The compatibility lemmas at `SemC`, one per CBPV rule.  Terms are BoLo expressions:

* `return V` is `V`; `M to x. N` is `(λx. N) M` (the argument runs first);
* `thunk M : U (F A)` is `λ_. M`, `M` typed under an extra dead binder, and forcing it is `x ()`;
  a thunk of a λ-value `V : C` at any other `C` is `V`, and forcing it is `x`;
* `Λ. M` is `λ_. M`, `M` under a dead binder, and `M []` is `M ()`;
* `λx. M` is `λx. M`; `M x` is `M x`;
* `⟨M, N⟩` is `λs. case s {inj₁ u. u; M | inj₂ u. u; N}`, `M` and `N` typed in the same context
  extended by the two dead binders `u : 1`, `s : 1 ⊕ 1`; the projections are `M (inj₁ ())` and
  `M (inj₂ ())`;
* `⊤` is `()` at any context.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

private theorem substAll_cons (v : Val) (γ : List Val) (e : Expr) :
    substAll (v :: γ) e = Expr.subst 0 v (Expr.psub 1 γ e) := by
  show Expr.psub 0 (v :: γ) e = _
  rw [Expr.psub_cons 0 v γ e, Val.shift_zero]

private theorem substAll_cons₂ (w₂ w₁ : Val) (γ : List Val) (e : Expr) :
    substAll (w₂ :: w₁ :: γ) e = Expr.subst 0 w₁ (Expr.subst 0 (w₂.shift 1 0) (Expr.psub 2 γ e)) := by
  show Expr.psub 0 (w₂ :: w₁ :: γ) e = _
  rw [Expr.psub_cons₂ 0 w₂ w₁ γ e, Val.shift_zero]

private theorem substAll_var {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v) :
    substAll γ (.var i) = .val v := by
  show Expr.psub 0 γ (.var i) = _
  simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv, Val.shift_zero]

/-! ### Values -/

theorem var_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {A : VTy}
    (h : Ctx.SoloP Γ i A) : SemV Δ Γ (.var i) A := by
  intro δ γ ls ρ _ hg
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp hg
  obtain ⟨v, hv, hval⟩ := gSepC_soloP h (h.lt_of_liveWithin hlen) hs
  show wpTS ls _ _ ρ
  rw [substAll_var hv]
  exact wpTS_val ls v _ ρ hval

theorem unitI_compatC {Δ : LifeCtx} {Γ : Ctx VTy} (h : Ctx.DeadP Γ) :
    SemV Δ Γ (.val .unit) .unit := by
  intro δ γ ls ρ _ hg
  obtain ⟨-, hs⟩ := gDenC_iff.mp hg
  rw [gSepC_deadP h hs]
  exact wpTS_val ls Val.unit _ _ ⟨rfl, rfl⟩

theorem tensorI_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e₁ e₂ : Expr} {A B : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (h₁ : SemV Δ Γ₁ e₁ A) (h₂ : SemV Δ Γ₂ e₂ B) :
    SemV Δ Γ (.pair e₁ e₂) (.tensor A B) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine wpTS_bind_frame (.pairL .hole (substAll γ e₂)) (substAll γ e₁) ls
    (fun ls' => vC true A ls' δ) (fun ls' => gDenC ls' δ Γ₂ γ) (fun ls' => vC true (.tensor A B) ls' δ)
    (fun ls' hls ρ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, h₁ δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v₁ σ ⟨σ₁, σ₂, hcσ, hv₁, hg₂'⟩
  refine wpTS_bind_frame (.pairR v₁ .hole) (substAll γ e₂) ls'
    (fun ls'' => vC true B ls'' δ) (fun ls'' => vC true A ls'' δ v₁) (fun ls'' => vC true (.tensor A B) ls'' δ)
    (fun ls'' hls ρ h => vC_same hls h) ?_ σ
    ⟨σ₂, σ₁, ResU.CompS.comm hcσ, h₂ δ γ ls' σ₂ hδ hg₂', hv₁⟩
  rintro ls'' - v₂ τ ⟨τ₁, τ₂, hcτ, hv₂, hv₁'⟩
  exact wpTS_val ls'' (.pair v₁ v₂) _ τ
    ⟨v₁, v₂, pure_sep_mk rfl ⟨τ₂, τ₁, ResU.CompS.comm hcτ, hv₁', hv₂⟩⟩

theorem sumI₁_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A B : VTy}
    (h : SemV Δ Γ e A) : SemV Δ Γ (.inj₁ e) (.sum A B) := by
  intro δ γ ls ρ hδ hg
  refine wpTS_bind (.inj₁ .hole) (substAll γ e) ls _ ρ
    (wpTS_mono (fun ls' v σ hv => ?_) ρ (h δ γ ls ρ hδ hg))
  exact wpTS_val ls' (.inj₁ v) _ σ (Or.inl ⟨v, pure_sep_mk rfl hv⟩)

theorem sumI₂_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A B : VTy}
    (h : SemV Δ Γ e B) : SemV Δ Γ (.inj₂ e) (.sum A B) := by
  intro δ γ ls ρ hδ hg
  refine wpTS_bind (.inj₂ .hole) (substAll γ e) ls _ ρ
    (wpTS_mono (fun ls' v σ hv => ?_) ρ (h δ γ ls ρ hδ hg))
  exact wpTS_val ls' (.inj₂ v) _ σ (Or.inr ⟨v, pure_sep_mk rfl hv⟩)

/-- `C` is an `F A`. -/
def CTy.isRet : CTy → Bool
  | .ret _ => true
  | _ => false

theorem forceE_of_not_ret {C : CTy} (h : C.isRet = false) (e : Expr) : forceE C e = e := by
  cases C <;> first | rfl | exact absurd h (by simp [CTy.isRet])

/-- `thunk M : U (F A)`, written `λ_. M` with `M` under a dead binder.  The closure runs at any
list `Ext`-above the one it was made at, and its environment moves there by `gSepC_local` —
`lolliI_compatX`'s argument, at `U`. -/
theorem thunkF_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (h : SemC Δ (⟨.unit, false⟩ :: Γ) M (.ret A)) :
    SemV Δ Γ (.val (.lam M)) (.thunk (.ret A)) := by
  intro δ γ ls ρ hδ hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ ?_
  intro ls' hext
  refine cC_head (.ret A) (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) ls' δ ρ ?_
  rw [← substAll_cons]
  exact h δ (Val.unit :: γ) ls' ρ hδ (gDenC_dead_cons _ _ (gDenC_local hext hg))

/-- `thunk V : U C` for a λ-value `V : C` at a computation type other than `F`: the thunk is
`V` itself. -/
theorem thunkV_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hC : C.isRet = false)
    (h : SemC Δ Γ (.val (.lam N)) C) : SemV Δ Γ (.val (.lam N)) (.thunk C) := by
  intro δ γ ls ρ hδ hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  refine wpTS_val _ _ _ _ ?_
  intro ls' hext
  rw [forceE_of_not_ret hC]
  exact h δ γ ls' ρ hδ (gDenC_local hext hg)

/-! ### Computations -/

/-- `return V : F A`. -/
theorem ret_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemV Δ Γ e A) : SemC Δ Γ e (.ret A) := h

private theorem substAll_forceE {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v)
    (C : CTy) : substAll γ (forceE C (.var i)) = forceE C (.val v) := by
  cases C with
  | ret A =>
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, substAll_var hv]; rfl
  | _ => exact substAll_var hv

/-- `force x : C` for `x : U C`, written `forceE C x`. -/
theorem force_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {C : CTy}
    (h : Ctx.SoloP Γ i (.thunk C)) : SemC Δ Γ (forceE C (.var i)) C := by
  intro δ γ ls ρ _ hg
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp hg
  obtain ⟨v, hv, hval⟩ := gSepC_soloP h (h.lt_of_liveWithin hlen) hs
  rw [substAll_forceE hv]
  exact hval ls (Ext.refl _ _)

/-- `λx. M : A ⊸ C`.  No Kripke quantifier: the arrow runs at the list it is applied at. -/
theorem lam_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {C : CTy}
    (h : SemC Δ (⟨A, true⟩ :: Γ) M C) : SemC Δ Γ (.val (.lam M)) (.arr A C) := by
  intro δ γ ls ρ hδ hg v ρ₁ ρ₂ hv hc
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg
  refine cC_head C (fun μ => Head.beta μ (Expr.psub 1 γ M) v) ls δ ρ₂ ?_
  rw [← substAll_cons]
  exact h δ (v :: γ) ls ρ₂ hδ
    (gDenC_mk (by simpa using hlen) ⟨ρ₁, ρ, ResU.CompS.comm hc, hv, hgs⟩)

/-- `M x : C` for `M : A ⊸ C`, `x : A`. -/
theorem app_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M : Expr} {i : Nat} {A : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hM : SemC Δ Γ₁ M (.arr A C)) (hx : Ctx.SoloP Γ₂ i A) :
    SemC Δ Γ (.app M (.var i)) C := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp hg₂
  obtain ⟨v, hv, hval⟩ := gSepC_soloP hx (hx.lt_of_liveWithin hlen) hs
  have he : substAll γ (.app M (.var i)) = .app (substAll γ M) (.val v) := by
    show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ (.var i)) = _
    rw [← substAll, ← substAll, substAll_var hv]
  rw [he]
  exact hM δ γ ls ρ₁ hδ hg₁ v ρ₂ ρ hval hc

/-- `M to x. N : C`.  The context `N` needs is framed through `M`'s run, together with the stack
`C` is eliminated by, and used at the list `M` returns (`cC_bind`). -/
theorem bind_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hM : SemC Δ Γ₁ M (.ret A))
    (hN : SemC Δ (⟨A, true⟩ :: Γ₂) N C) :
    SemC Δ Γ (.app (.val (.lam N)) M) C := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine cC_bind C (.appR (.val (.lam (Expr.psub 1 γ N))) .hole) (substAll γ M) ls δ
    (fun ls' => vC true A ls' δ) (fun ls' => gDenC ls' δ Γ₂ γ)
    (fun ls' hls σ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, hM δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, hv, hg₂'⟩
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
  refine cC_head C (fun μ => Head.beta μ (Expr.psub 1 γ N) v) ls' δ σ ?_
  rw [← substAll_cons]
  exact hN δ (v :: γ) ls' σ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hv, hgs⟩)

/-- The `&` pair: `λs. case s {inj₁ u. u; M | inj₂ u. u; N}`. -/
def withPair (M N : Expr) : Expr :=
  .val (.lam (.case (.var 0) (.seq (.var 0) M) (.seq (.var 0) N)))

/-- The branch context of `⟨M, N⟩`: the two dead binders `u : 1`, `s : 1 ⊕ 1`. -/
abbrev withCtx (Γ : Ctx VTy) : Ctx VTy :=
  ⟨.unit, false⟩ :: ⟨.sum .unit .unit, false⟩ :: Γ

private theorem substAll_withPair (γ : List Val) (M N : Expr) :
    substAll γ (withPair M N) =
      .val (.lam (.case (.var 0) (.seq (.var 0) (Expr.psub 2 γ M))
        (.seq (.var 0) (Expr.psub 2 γ N)))) := by
  show Expr.psub 0 γ (.lam _) = _
  simp [Expr.psub]

private theorem withBody_subst (γ : List Val) (M N : Expr) (s : Val) :
    (Expr.case (.var 0) (.seq (.var 0) (Expr.psub 2 γ M)) (.seq (.var 0) (Expr.psub 2 γ N))).subst 0 s
      = .case (.val s) (.seq (.var 0) (Expr.psub 1 (s :: γ) M))
          (.seq (.var 0) (Expr.psub 1 (s :: γ) N)) := by
  simp [Expr.subst, Expr.psub_cons 1 s γ]

private theorem seq_subst_unit (e : Expr) :
    (Expr.seq (.var 0) e).subst 0 Val.unit = .seq (.val .unit) (e.subst 0 Val.unit) := by
  simp [Expr.subst]

/-- `⟨M, N⟩ : C & D`.  Additive: `M` and `N` are typed in the same context, and each projection
hands the whole context resource to its branch.  A projection runs three head steps (β, `case`,
`;`) to the branch at `() :: inj ᵢ () :: γ`. -/
theorem withI_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M N : Expr} {C D : CTy}
    (hM : SemC Δ (withCtx Γ) M C) (hN : SemC Δ (withCtx Γ) N D) :
    SemC Δ Γ (withPair M N) (.amp C D) := by
  intro δ γ ls ρ hδ hg
  rw [substAll_withPair]
  refine ⟨?_, ?_⟩
  · refine cC_head C (fun μ => Head.beta μ _ (Val.inj₁ Val.unit)) ls δ ρ ?_
    rw [withBody_subst]
    refine cC_head C (fun μ => Head.case₁ μ Val.unit _ _) ls δ ρ ?_
    rw [seq_subst_unit]
    refine cC_head C (fun μ => Head.seq μ _) ls δ ρ ?_
    rw [← substAll_cons]
    exact hM δ _ ls ρ hδ (gDenC_dead_cons _ _ (gDenC_dead_cons _ _ hg))
  · refine cC_head D (fun μ => Head.beta μ _ (Val.inj₂ Val.unit)) ls δ ρ ?_
    rw [withBody_subst]
    refine cC_head D (fun μ => Head.case₂ μ Val.unit _ _) ls δ ρ ?_
    rw [seq_subst_unit]
    refine cC_head D (fun μ => Head.seq μ _) ls δ ρ ?_
    rw [← substAll_cons]
    exact hN δ _ ls ρ hδ (gDenC_dead_cons _ _ (gDenC_dead_cons _ _ hg))

private theorem substAll_app_val (γ : List Val) (M : Expr) (w : Val) (hw : ∀ k, Expr.psub k γ w.val = w.val) :
    substAll γ (.app M (.val w)) = .app (substAll γ M) (.val w) := by
  show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ w.val) = _
  rw [hw]; rfl

/-- `π₁ M : C` for `M : C & D`. -/
theorem proj₁_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C D : CTy}
    (h : SemC Δ Γ M (.amp C D)) : SemC Δ Γ (.app M (.val (.inj₁ .unit))) C := by
  intro δ γ ls ρ hδ hg
  rw [substAll_app_val γ M _ (fun k => by simp [Expr.psub])]
  exact (h δ γ ls ρ hδ hg).1

/-- `π₂ M : D` for `M : C & D`. -/
theorem proj₂_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C D : CTy}
    (h : SemC Δ Γ M (.amp C D)) : SemC Δ Γ (.app M (.val (.inj₂ .unit))) D := by
  intro δ γ ls ρ hδ hg
  rw [substAll_app_val γ M _ (fun k => by simp [Expr.psub])]
  exact (h δ γ ls ρ hδ hg).2

/-- `⟨⟩ : ⊤` at any context: `⊤` has no stacks, so its context resource is never consumed. -/
theorem topI_compatC {Δ : LifeCtx} {Γ : Ctx VTy} : SemC Δ Γ (.val .unit) .top :=
  fun _ _ _ _ _ _ => trivial

/-! ### Eliminations of values into computations -/

/-- `V; M : C` for `V : 1`. -/
theorem unitE_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {V M : Expr} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hV : SemV Δ Γ₁ V .unit) (hM : SemC Δ Γ₂ M C) :
    SemC Δ Γ (.seq V M) C := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine cC_bind C (.seq .hole (substAll γ M)) (substAll γ V) ls δ
    (fun ls' => vC true .unit ls' δ) (fun ls' => gDenC ls' δ Γ₂ γ)
    (fun ls' hls σ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, hV δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, ⟨rfl, rfl⟩, hg₂'⟩
  rw [eq_of_compS_empty_left hcσ]
  exact cC_head C (fun μ => Head.seq μ _) ls' δ σ₂ (hM δ γ ls' σ₂ hδ hg₂')

/-- `let (x, y) = V in M : C` for `V : A ⊗ B`. -/
theorem tensorE_compatC {Δ : LifeCtx} {Γ Γp Γb : Ctx VTy} {V M : Expr} {A B : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γp Γb) (hV : SemV Δ Γp V (.tensor A B))
    (hM : SemC Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M C) :
    SemC Δ Γ (.letpair V M) C := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine cC_bind C (.letpair .hole (Expr.psub 2 γ M)) (substAll γ V) ls δ
    (fun ls' => vC true (.tensor A B) ls' δ) (fun ls' => gDenC ls' δ Γb γ)
    (fun ls' hls σ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, hV δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, hpair, hg₂'⟩
  obtain ⟨w₁, w₂, hs⟩ := hpair
  obtain ⟨rfl, b₁, b₂, hcb, hw₁, hw₂⟩ := pure_sep_iff.mp hs
  refine cC_head C (fun μ => Head.letpair μ w₁ w₂ _) ls' δ σ ?_
  rw [← substAll_cons₂]
  obtain ⟨x, hx, hxσ⟩ := compS_reassoc hcb hcσ
  obtain ⟨y, hy, hyσ⟩ := compS_lcomm hx hxσ
  refine hM δ (w₂ :: w₁ :: γ) ls' _ hδ (gDenC_mk ?_ ?_)
  · have := (gDenC_iff.mp hg₂').1
    simpa using this
  · exact ⟨b₂, y, hyσ, hw₂, ⟨b₁, σ₂, hy, hw₁, (gDenC_iff.mp hg₂').2⟩⟩

/-- `case V {inj₁ x. M₁ | inj₂ y. M₂} : C` for `V : A ⊕ B`. -/
theorem sumE_compatC {Δ : LifeCtx} {Γ Γs Γb : Ctx VTy} {V M₁ M₂ : Expr} {A B : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γs Γb) (hV : SemV Δ Γs V (.sum A B))
    (h₁ : SemC Δ (⟨A, true⟩ :: Γb) M₁ C) (h₂ : SemC Δ (⟨B, true⟩ :: Γb) M₂ C) :
    SemC Δ Γ (.case V M₁ M₂) C := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine cC_bind C (.case .hole (Expr.psub 1 γ M₁) (Expr.psub 1 γ M₂)) (substAll γ V) ls δ
    (fun ls' => vC true (.sum A B) ls' δ) (fun ls' => gDenC ls' δ Γb γ)
    (fun ls' hls σ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, hV δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, hsum, hg₂'⟩
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
  rcases hsum with ⟨w, hs⟩ | ⟨w, hs⟩
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hs
    refine cC_head C (fun μ => Head.case₁ μ w _ _) ls' δ σ ?_
    rw [← substAll_cons]
    exact h₁ δ (w :: γ) ls' _ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hw, hgs⟩)
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hs
    refine cC_head C (fun μ => Head.case₂ μ w _ _) ls' δ σ ?_
    rw [← substAll_cons]
    exact h₂ δ (w :: γ) ls' _ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hw, hgs⟩)

/-- `absurd V : C` for `V : 0`, written `case V {inj₁ _. () | inj₂ _. ()}`; the rest of the
context is absorbed. -/
def absurdE (V : Expr) : Expr := .case V (.val .unit) (.val .unit)

theorem zeroE_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {V : Expr} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hV : SemV Δ Γ₁ V .zero) : SemC Δ Γ (absurdE V) C := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine cC_bind C (.case .hole (.val .unit) (.val .unit)) (substAll γ V) ls δ
    (fun ls' => vC true .zero ls' δ) (fun ls' => gDenC ls' δ Γ₂ γ)
    (fun ls' hls σ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, hV δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, -, hv, -⟩
  exact hv.elim

/-! ### The lifetime `∀` -/

/-- `Λ. M : ∀'x ⊏ @b. C`, written `λ_. M`, `M` under a dead binder at `Δ, 'x ⊏ @b` (`allI_compatX`).
`'x` is fresh for `@b`, for the bounds in `Δ`, and for the live slots of `Γ`, so the context's
relation is the same at `δ` and `δ['x ↦ α]` (`vC_extend_of_not_free`). -/
theorem allI_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life} {M : Expr}
    {C : CTy} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : SemC (Δ.extend x b) (⟨.unit, false⟩ :: Γ) M C) :
    SemC Δ Γ (.val (.lam M)) (.all x b C) := by
  intro δ γ ls ρ hδ hg α ρ₁ ρ₂ hpure hcomp
  obtain ⟨rfl, β, hβ, hlt⟩ := hpure
  have hρ₂ : ρ₂ = ρ := eq_of_compS_empty_left (ResU.CompS.comm hcomp)
  subst ρ₂
  have hδ' : (Δ.extend x b).Models (δ.extend x α) := by
    intro y u hy
    rw [LifeCtx.find?_extend] at hy
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl] at hy
      obtain rfl := Option.some.inj hy
      exact ⟨α, β, find?_extend_self δ x α,
        by rw [interp_extend_of_not_mentions hbx]; exact hβ, hlt⟩
    · rw [if_neg hxy] at hy
      obtain ⟨m, k, hm, hk, hlk⟩ := hδ y u hy
      exact ⟨m, k, by rw [find?_extend_ne δ α hxy]; exact hm,
        by rw [interp_extend_of_not_mentions (hΔx y u hy)]; exact hk, hlk⟩
  show cC C ls (δ.extend x α) (.app (.val (.lam (Expr.psub 1 γ M))) (.val .unit)) ρ
  refine cC_head C (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) ls (δ.extend x α) ρ ?_
  rw [← substAll_cons]
  refine h (δ.extend x α) (Val.unit :: γ) ls ρ hδ' (gDenC_dead_cons _ _ ?_)
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg
  refine gDenC_mk hlen ?_
  rw [gSepC_congr (δ₂ := δ) (fun s hs hl => vC_extend_of_not_free (hΓx s hs hl) true ls δ α)]
  exact hgs

/-! ### `!` -/

/-- Promotion of `thunk M : U (F A)` over `!Γ`. -/
theorem bangThunkF_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} (hp : Persistent Γ)
    (h : SemC Δ (⟨.unit, false⟩ :: Γ) M (.ret A)) :
    SemV Δ Γ (.val (.lam M)) (.bang (.thunk (.ret A))) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨-, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ ⟨gSepC_persistent hp hgs, ?_⟩
  intro ls' hext
  refine cC_head (.ret A) (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) ls' δ ρ ?_
  rw [← substAll_cons]
  exact h δ (Val.unit :: γ) ls' ρ hδ (gDenC_dead_cons _ _ (gDenC_local hext hg))

/-- Promotion of a λ-value `V : C` (`C` not an `F`) over `!Γ`: `bangLamI_compatX` at
`C = A ⊸ F B`, `bangAllI_compatX` at `C = ∀'x ⊏ @b. F B`. -/
theorem bangThunkV_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hp : Persistent Γ)
    (hC : C.isRet = false) (h : SemC Δ Γ (.val (.lam N)) C) :
    SemV Δ Γ (.val (.lam N)) (.bang (.thunk C)) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨-, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  refine wpTS_val _ _ _ _ ⟨gSepC_persistent hp hgs, ?_⟩
  intro ls' hext
  rw [forceE_of_not_ret hC]
  exact h δ γ ls' ρ hδ (gDenC_local hext hg)

/-- Dereliction: forget the `ρ = ∅` (`bangE_compatX`). -/
theorem bangE_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemV Δ Γ e (.bang A)) : SemV Δ Γ e A := by
  intro δ γ ls ρ hδ hg
  exact wpTS_mono (fun _ _ _ hb => hb.2) ρ (h δ γ ls ρ hδ hg)

/-- `copy : U (!A ⊸ F (!A ⊗ !A))`: both copies are the original, at `∅` (`copyBang_compatX`). -/
theorem copyBang_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ copy (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A))))) := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls copy _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_lolli ls' (.pair BoCa.v0 BoCa.v0) v _ _ ?_
  have hb : Expr.subst 0 v (.pair BoCa.v0 BoCa.v0) = Expr.pair (.val v) (.val v) := by
    simp [BoCa.v0, Expr.subst]
  rw [hb]
  refine wpTS_val ls' (.pair v v) _ _ ?_
  have hσ : σ = PMap.empty := hv.1
  subst hσ
  exact ⟨v, v, pure_sep_mk rfl ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, hv, hv⟩⟩

/-- `forget : U (!A ⊸ F 1)`: nothing to release (`forgetBang_compatX`). -/
theorem forgetBang_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ forget (.thunk (.arr (.bang A) (.ret .unit))) := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls forget _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_lolli ls' unit' v _ _ ?_
  have hb : Expr.subst 0 v unit' = unit' := by simp [unit', Expr.subst]
  rw [hb]
  have hσ : σ = PMap.empty := hv.1
  subst hσ
  exact wpTS_val ls' .unit _ _ ⟨rfl, rfl⟩

/-! ### `[@a]`, and the lifetime index of `Imm`/`Mut` -/

/-- `[]E` (`boxE_compatX`). -/
theorem boxE_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a : Lifetime.Life} {A : VTy}
    (h : SemV Δ Γ e (.box a A)) : SemV Δ Γ e A := by
  intro δ γ ls ρ hδ hg
  exact wpTS_mono (fun _ _ _ ⟨_, _, hb, _⟩ => hb) ρ (h δ γ ls ρ hδ hg)

/-- `⊑imm` (`immSub_compatX`). -/
theorem immSub_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {A : VTy}
    (h : SemV Δ Γ e (.imm b A)) (hle : Δ.EntailsLe a b) : SemV Δ Γ e (.imm a A) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, β, ha, hb, hle'⟩ := hle δ hδ
  refine wpTS_mono (fun ls' v => ?_) ρ (h δ γ ls ρ hδ hg)
  rintro σ ⟨β', hβ', ℓ, hs⟩
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  obtain ⟨hvl, himm⟩ := pure_sep_iff.mp hs
  exact ⟨α, ha, ℓ, pure_sep_mk hvl (ptoImmS_antitone hle' himm)⟩

/-- `⊑mut` (`mutSub_compatX`). -/
theorem mutSub_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {A : VTy}
    (h : SemV Δ Γ e (.mut b A)) (hle : Δ.EntailsLe a b) : SemV Δ Γ e (.mut a A) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, β, ha, hb, hle'⟩ := hle δ hδ
  refine wpTS_mono (fun ls' v => ?_) ρ (h δ γ ls ρ hδ hg)
  rintro σ ⟨β', hβ', ℓ, hs⟩
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  obtain ⟨hvl, hmut⟩ := pure_sep_iff.mp hs
  exact ⟨α, ha, ℓ, pure_sep_mk hvl (ptoMutS_antitone hle' hmut)⟩

/-! ### `∀E`, and `[]I` -/

/-- `M [] : C[@a/'x]` for `M : ∀'x ⊏ @b. C` and `Δ ⊨ @a ⊏ @b`, at every `C`: `CTyEq.instLife`
reads `C[@a/'x]` at `δ` as `C` at `δ['x ↦ @aδ]`, and `cC_tyEq` carries the relation across. -/
theorem allE_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {x : LifeVar} {b a : Lifetime.Life}
    {C : CTy} (h : SemC Δ Γ M (.all x b C)) (hlt : Δ.EntailsLt a b) :
    SemC Δ Γ (.app M (.val .unit)) (C.instLife x a) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, β, ha, hb, hab⟩ := hlt δ hδ
  have he : substAll γ (.app M (.val .unit)) = .app (substAll γ M) (.val .unit) := by
    show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ (.val .unit)) = _
    simp [Expr.psub, substAll]
  rw [he, cC_tyEq (CTyEq.instLife x a C ha) ls]
  exact h δ γ ls ρ hδ hg α PMap.empty ρ ⟨rfl, β, hb, hab⟩ (ResU.comp_empty_right ρ)

/-- `[]I` at every value type: `boxI_compatX`, whose premise `Δ ⊨ Γ ⊐ @a` is 6.60 at `vC`
(`vC_outlives`) folded over the context. -/
theorem boxI_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} {a : Lifetime.Life}
    (h : SemV Δ Γ e A) (hΓ : CtxOutlives Δ Γ a) : SemV Δ Γ e (.box a A) :=
  boxI_compatX h hΓ

end BoCa.Fig16.LogRel.Core

end
