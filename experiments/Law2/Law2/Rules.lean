import Law2.Fragment

/-!
# Law2 — the piece judgment, rule by rule

One lemma per rule of Core's typing (`CDerives`), at the motive `Law2/Fundamental.lean` inducts
with: a value judgment `V : A` is `PV` (from a re-lendable context, a run to a re-lendable value),
a computation judgment `M : C` is `PJ` (from a re-lendable context, `RC C`). Each lemma takes the
premises' piece judgments and the rule's side conditions.

This file holds the structural rules, closures and calls, the eliminations, `!`, `[@a]` at a type
that outlives its lifetime, the sub-lifetime rules, the effect rules at linear operations, the
polymorphic let, the borrow axioms on `Ref`, `Imm`, `Mut` and `Unk`, the family constants and the
counted loops. The family operations are in `Law2/Families.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N performE opPayload eLoad eStore)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

section unfold
variable {δ : LSub} {σ : LStack} {S₀ : Row}

theorem rslot_thunk_eq (C : CTy) (αs : List Life) (ls : List SRec) (f : Val) :
    RSlot (ℍ := ℍ) δ σ S₀ (.thunk C) αs ls f =
      RelendableS δ [] σ (fun αs' ls' => RC (ℍ := ℍ) δ σ S₀ C αs' ls' (forceE C (.val f)))
        αs ls := by
  rw [RSlot]

theorem rc_arr_eq (A : VTy) (C : CTy) (αs : List Life) (ls : List SRec) (e : Expr) :
    RC (ℍ := ℍ) δ σ S₀ (.arr A C) αs ls e = fun ρ =>
      ∀ v, (RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ─⋆ RC (ℍ := ℍ) δ σ S₀ C αs ls (.app e (.val v))) ρ := by
  rw [RC]

theorem rc_amp_eq (C D : CTy) (αs : List Life) (ls : List SRec) (e : Expr) :
    RC (ℍ := ℍ) δ σ S₀ (.amp C D) αs ls e = fun ρ =>
      RC (ℍ := ℍ) δ σ S₀ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
        RC (ℍ := ℍ) δ σ S₀ D αs ls (.app e (.val (.inj₂ .unit))) ρ := by
  rw [RC]

theorem rc_all_eq (x : LifeVar) (b : Lifetime.Life) (C : CTy) (αs : List Life) (ls : List SRec)
    (e : Expr) :
    RC (ℍ := ℍ) δ σ S₀ (.all x b C) αs ls e = cC (ℍ := ℍ) (.all x b C) ls (extS δ σ αs) e := by
  rw [RC]

theorem rc_nu_eq (C : CTy) (αs : List Life) (ls : List SRec) (e : Expr) :
    RC (ℍ := ℍ) δ σ S₀ (.nu C) αs ls e = cC (ℍ := ℍ) (.nu C) ls (extS δ σ αs) e := by
  rw [RC]

theorem rslot_box_eq (a : Lifetime.Life) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) :
    RSlot (ℍ := ℍ) δ σ S₀ (.box a A) αs ls v =
      RelendableS δ [] σ (fun αs' ls' =>
        atLife (extS δ σ αs') a fun α => box α (RSlot (ℍ := ℍ) δ σ S₀ A αs' ls' v)) αs ls := by
  rw [RSlot]

/-- A dead slot of a context holds nothing. -/
theorem rctx_dead_cons {αs : List Life} {ls : List SRec} {A : VTy} {Γ : Ctx VTy} {v : Val}
    {γ : List Val} {ρ : WRes} :
    RCtx (ℍ := ℍ) δ σ S₀ αs ls (⟨A, false⟩ :: Γ) (v :: γ) ρ ↔
      RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ := by
  simp only [RCtx, rSep, Bool.false_eq_true, if_false, Ctx.liveWithin_cons]

end unfold

/-! ### Substitution -/

theorem substAll_forceE' {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v)
    (C : CTy) : substAll γ (forceE C (.var i)) = forceE C (.val v) := by
  cases C with
  | ret A =>
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, substAll_var' hv]; rfl
  | eff n j q A B C =>
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, substAll_var' hv]; rfl
  | _ => exact substAll_var' hv

theorem substAll_withPair' (γ : List Val) (M N : Expr) :
    substAll γ (withPair M N) =
      .val (.lam (.case (.var 0) (.seq (.var 0) (Expr.psub 2 γ M))
        (.seq (.var 0) (Expr.psub 2 γ N)))) := by
  show Expr.psub 0 γ (.lam _) = _
  simp [Expr.psub]

theorem withBody_subst' (γ : List Val) (M N : Expr) (s : Val) :
    (Expr.case (.var 0) (.seq (.var 0) (Expr.psub 2 γ M)) (.seq (.var 0) (Expr.psub 2 γ N))).subst 0 s
      = .case (.val s) (.seq (.var 0) (Expr.psub 1 (s :: γ) M))
          (.seq (.var 0) (Expr.psub 1 (s :: γ) N)) := by
  simp [Expr.subst, Expr.psub_cons 1 s γ]

theorem seq_subst_unit' (e : Expr) :
    (Expr.seq (.var 0) e).subst 0 Val.unit = .seq (.val .unit) (e.subst 0 Val.unit) := by
  simp [Expr.subst]

theorem substAll_app_val' (γ : List Val) (M : Expr) (w : Val)
    (hw : ∀ k, Expr.psub k γ w.val = w.val) :
    substAll γ (.app M (.val w)) = .app (substAll γ M) (.val w) := by
  show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ w.val) = _
  rw [hw]; rfl

section rules
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-! ### Values and their eliminations -/

/-- **`return V : F A`**: a value is a run that does not stop. -/
theorem pj_ret {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {A : VTy}
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ V A) : PJ (ℍ := ℍ) δ σ S₀ Δ Γ V (.ret A) :=
  pj_of_pv (S := []) h

/-- **`F A` read as a value** (`ofRet`): the run at `F A` stops nowhere. -/
theorem pv_ofRet {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : PJ (ℍ := ℍ) δ σ S₀ Δ Γ e (.ret A)) : PV (ℍ := ℍ) δ σ S₀ Δ Γ e A :=
  pv_iff_pj.mpr h

/-- **`thunk M : U (F A)`**, `M` under a dead binder: its environment, re-lendable, is its frozen
share; forced at a re-lend, the β-step hands the body its re-lendable context. -/
theorem rslot_thunkF {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨.unit, false⟩ :: Γ) M (.ret A))
    {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes} (hlen : αs.length = σ.length)
    (hΔ : ∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs'))
    (hg : RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ) :
    RSlot (ℍ := ℍ) δ σ S₀ (.thunk (.ret A)) αs ls ⟨.lam (Expr.psub 1 γ M), .lam⟩ ρ := by
  rw [rslot_thunk_eq]
  refine relendableS_mono_rel ?_ ρ (rctx_relendable hlen hg)
  intro αs' ls' hr' τ hτ
  show RC δ σ S₀ (.ret A) αs' ls' (.app (.val ⟨.lam (Expr.psub 1 γ M), .lam⟩) (.val .unit)) τ
  refine rc_head (.ret A) (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) rfl αs' ls' τ ?_
  rw [← substAll_cons_psub]
  exact hM αs' ls' (Val.unit :: γ) τ ((List.Forall₂.length_eq hr'.1).trans hlen) hr'.2
    (fun αs'' h'' => hΔ αs'' (reLend_trans h'' hr')) (rctx_dead_cons.mpr hτ)

theorem pv_thunkF {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨.unit, false⟩ :: Γ) M (.ret A)) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam M)) (.thunk (.ret A)) := by
  intro αs ls γ ρ hlen _ hΔ hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  exact wpTS_val ls _ _ ρ (rslot_thunkF hM hlen hΔ hg)

/-- **`thunk V : U C`** for a λ-value `V : C`, `C` not an `F`: forced it is `V`, re-read at every
re-lend from the re-lent environment. -/
theorem rslot_thunkV {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hC : C.isRet = false)
    (hN : PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam N)) C)
    {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes} (hlen : αs.length = σ.length)
    (hΔ : ∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs'))
    (hg : RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ) :
    RSlot (ℍ := ℍ) δ σ S₀ (.thunk C) αs ls ⟨.lam (Expr.psub 1 γ N), .lam⟩ ρ := by
  rw [rslot_thunk_eq]
  refine relendableS_mono_rel ?_ ρ (rctx_relendable hlen hg)
  intro αs' ls' hr' τ hτ
  rw [forceE_of_not_ret hC]
  exact hN αs' ls' γ τ ((List.Forall₂.length_eq hr'.1).trans hlen) hr'.2
    (fun αs'' h'' => hΔ αs'' (reLend_trans h'' hr')) hτ

theorem pv_thunkV {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hC : C.isRet = false)
    (hN : PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam N)) C) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam N)) (.thunk C) := by
  intro αs ls γ ρ hlen _ hΔ hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  exact wpTS_val ls _ _ ρ (rslot_thunkV hC hN hlen hΔ hg)

/-- **`!thunk M : !U (F A)`** over `!Γ`: the environment holds nothing. -/
theorem pv_bangThunkF {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} (hp : Persistent Γ)
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨.unit, false⟩ :: Γ) M (.ret A)) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam M)) (.bang (.thunk (.ret A))) := by
  intro αs ls γ ρ hlen hch hΔ hg
  have hρ : ρ = PMap.empty := rSep_persistent_empty Γ γ hp (pure_sep_iff.mp hg).2
  subst hρ
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ PMap.empty
  exact wpTS_val ls _ _ PMap.empty ⟨rfl, rslot_thunkF hM hlen hΔ hg⟩

/-- **`!thunk V : !U C`** over `!Γ`, `C` not an `F`. -/
theorem pv_bangThunkV {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hp : Persistent Γ)
    (hC : C.isRet = false) (hN : PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam N)) C) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam N)) (.bang (.thunk C)) := by
  intro αs ls γ ρ hlen hch hΔ hg
  have hρ : ρ = PMap.empty := rSep_persistent_empty Γ γ hp (pure_sep_iff.mp hg).2
  subst hρ
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ PMap.empty
  exact wpTS_val ls _ _ PMap.empty ⟨rfl, rslot_thunkV hC hN hlen hΔ hg⟩

/-- **`M to x. N`** for a pure `M`: `M` runs to a re-lendable answer without stopping, `N`'s
context its frame (`rc_bind`), and the β-step hands `N` its re-lendable context, at every `C`. -/
theorem pj_bind {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hM : PJ (ℍ := ℍ) δ σ S₀ Δ Γ₁ M (.ret A))
    (hN : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ₂) N C) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app (.val (.lam N)) M) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  refine rc_bind C (.appR (.val (.lam (Expr.psub 1 γ N))) .hole) (substAll γ M) αs ls
    (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ A αs ls' v)
    (fun ls' => RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γ₂ γ)
    (fun ls' hls τ h => rctx_local (ext_of_same hls τ) h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, wpTS_of_rc_ret (hM αs ls γ ρ₁ hlen hch hΔ hg₁), hg₂⟩
  rintro ls' - v τ ⟨τ₁, τ₂, hcτ, hv, hg₂'⟩
  refine rc_head C (fun μ => Head.beta μ (Expr.psub 1 γ N) v) rfl αs ls' τ ?_
  rw [← substAll_cons_psub]
  obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg₂'
  exact hN αs ls' (v :: γ) τ hlen hch hΔ (pure_sep_mk hl ⟨τ₁, τ₂, hcτ, hv, hs⟩)

/-- **`force x : C`** for `x : U C`: the closure's re-lendable reading at the current
lifetimes. -/
theorem pj_force {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {C : CTy}
    (h : Ctx.SoloP Γ i (.thunk C)) : PJ (ℍ := ℍ) δ σ S₀ Δ Γ (forceE C (.var i)) C := by
  intro αs ls γ ρ _ hch _ hg
  obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg
  obtain ⟨v, hv, hval⟩ := rSep_soloP hch h (h.lt_of_liveWithin hl) hs
  rw [substAll_forceE' hv]
  rw [rslot_thunk_eq] at hval
  exact relendableS_now hch hval

/-- **`λx. M : A ⊸ C`**: applied to a re-lendable argument, the β-step hands the body its
re-lendable context. -/
theorem pj_lam {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {C : CTy}
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ) M C) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam M)) (.arr A C) := by
  intro αs ls γ ρ hlen hch hΔ hg
  show RC δ σ S₀ (.arr A C) αs ls (.val ⟨.lam (Expr.psub 1 γ M), .lam⟩) ρ
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  refine rc_head C (fun μ => Head.beta μ (Expr.psub 1 γ M) v) rfl αs ls ρ₂ ?_
  rw [← substAll_cons_psub]
  obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg
  exact hM αs ls (v :: γ) ρ₂ hlen hch hΔ (pure_sep_mk hl ⟨ρ₁, ρ, ResU.CompS.comm hc, hv, hs⟩)

/-- **`λ_. M : 1 ⊸ C`** with the binder dead: the unit argument holds nothing. -/
theorem pj_lamDead {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy}
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨.unit, false⟩ :: Γ) M C) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam M)) (.arr .unit C) := by
  intro αs ls γ ρ hlen hch hΔ hg
  show RC δ σ S₀ (.arr .unit C) αs ls (.val ⟨.lam (Expr.psub 1 γ M), .lam⟩) ρ
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  obtain ⟨rfl, rfl⟩ := relendableS_now hch hv
  rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ)]
  refine rc_head C (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) rfl αs ls ρ ?_
  rw [← substAll_cons_psub]
  exact hM αs ls (Val.unit :: γ) ρ hlen hch hΔ (rctx_dead_cons.mpr hg)

/-- **`M x : C`** for `M : A ⊸ C`, `x : A`. -/
theorem pj_app {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M : Expr} {i : Nat} {A : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hM : PJ (ℍ := ℍ) δ σ S₀ Δ Γ₁ M (.arr A C))
    (hx : Ctx.SoloP Γ₂ i A) : PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app M (.var i)) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  obtain ⟨hl₂, hs₂⟩ := pure_sep_iff.mp hg₂
  obtain ⟨v, hv, hval⟩ := rSep_soloP hch hx (hx.lt_of_liveWithin hl₂) hs₂
  have he : substAll γ (.app M (.var i)) = .app (substAll γ M) (.val v) := by
    show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ (.var i)) = _
    rw [← substAll, ← substAll, substAll_var' hv]
  rw [he]
  have h := hM αs ls γ ρ₁ hlen hch hΔ hg₁
  rw [rc_arr_eq] at h
  exact h v ρ₂ ρ hval hc

/-- **`⟨M, N⟩ : C & D`**: each projection hands the whole context to its branch. -/
theorem pj_withI {Δ : LifeCtx} {Γ : Ctx VTy} {M N : Expr} {C D : CTy}
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (withCtx Γ) M C) (hN : PJ (ℍ := ℍ) δ σ S₀ Δ (withCtx Γ) N D) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (withPair M N) (.amp C D) := by
  intro αs ls γ ρ hlen hch hΔ hg
  rw [substAll_withPair', rc_amp_eq]
  refine ⟨?_, ?_⟩
  · refine rc_head C (fun μ => Head.beta μ _ (Val.inj₁ Val.unit)) rfl αs ls ρ ?_
    rw [withBody_subst']
    refine rc_head C (fun μ => Head.case₁ μ Val.unit _ _) rfl αs ls ρ ?_
    rw [seq_subst_unit']
    refine rc_head C (fun μ => Head.seq μ _) rfl αs ls ρ ?_
    rw [← substAll_cons_psub]
    exact hM αs ls _ ρ hlen hch hΔ (rctx_dead_cons.mpr (rctx_dead_cons.mpr hg))
  · refine rc_head D (fun μ => Head.beta μ _ (Val.inj₂ Val.unit)) rfl αs ls ρ ?_
    rw [withBody_subst']
    refine rc_head D (fun μ => Head.case₂ μ Val.unit _ _) rfl αs ls ρ ?_
    rw [seq_subst_unit']
    refine rc_head D (fun μ => Head.seq μ _) rfl αs ls ρ ?_
    rw [← substAll_cons_psub]
    exact hN αs ls _ ρ hlen hch hΔ (rctx_dead_cons.mpr (rctx_dead_cons.mpr hg))

theorem pj_proj₁ {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C D : CTy}
    (h : PJ (ℍ := ℍ) δ σ S₀ Δ Γ M (.amp C D)) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app M (.val (.inj₁ .unit))) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  rw [substAll_app_val' γ M _ (fun k => by simp [Expr.psub])]
  have h' := h αs ls γ ρ hlen hch hΔ hg
  rw [rc_amp_eq] at h'
  exact h'.1

theorem pj_proj₂ {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C D : CTy}
    (h : PJ (ℍ := ℍ) δ σ S₀ Δ Γ M (.amp C D)) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app M (.val (.inj₂ .unit))) D := by
  intro αs ls γ ρ hlen hch hΔ hg
  rw [substAll_app_val' γ M _ (fun k => by simp [Expr.psub])]
  have h' := h αs ls γ ρ hlen hch hΔ hg
  rw [rc_amp_eq] at h'
  exact h'.2

theorem pj_topI {Δ : LifeCtx} {Γ : Ctx VTy} :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.val .unit) .top := fun _ _ _ _ _ _ _ _ => by rw [RC]; trivial

/-- **`absurd V : C`** for `V : 0`: no value of `0` is re-lendable. -/
theorem pj_zeroE {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {V : Expr} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hV : PV (ℍ := ℍ) δ σ S₀ Δ Γ₁ V .zero) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (absurdE V) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  refine rc_bind C (.case .hole (.var 0) (.var 0)) (substAll γ V) αs ls
    (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ .zero αs ls' v)
    (fun ls' => RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γ₂ γ)
    (fun ls' hls τ h => rctx_local (ext_of_same hls τ) h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, hV αs ls γ ρ₁ hlen hch hΔ hg₁, hg₂⟩
  rintro ls' - v τ ⟨τ₁, τ₂, -, hv, -⟩
  exact (relendableS_now hch hv).elim

/-! ### `!` -/

/-- A value at `F A`: a run of no steps to its answer. -/
theorem rc_ret_val {A : VTy} {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes}
    (h : RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ) : RC (ℍ := ℍ) δ σ S₀ (.ret A) αs ls (.val v) ρ := by
  rw [RC]; exact wpG_here _ _ _ ρ (Or.inl ⟨v, rfl, h⟩)

/-- A closed constant holding nothing is re-lendable at `U C` when its reading at every re-lend
holds at `∅`. -/
theorem rslot_const {C : CTy} {f : Val} {αs : List Life} (hlen : αs.length = σ.length)
    (ls : List SRec)
    (h : ∀ αs' ls', ReLend αs' αs → RC (ℍ := ℍ) δ σ S₀ C αs' ls' (forceE C (.val f)) PMap.empty) :
    RSlot (ℍ := ℍ) δ σ S₀ (.thunk C) αs ls f PMap.empty := by
  rw [rslot_thunk_eq]
  exact relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a) fun ls' _ αs' hr => h αs' ls' hr

/-- A constant typed at a consumed context: its value expression, holding nothing. -/
theorem pv_const {Δ : LifeCtx} {Γ : Ctx VTy} {c : Val} {T : VTy} (hΓ : Ctx.DeadP Γ)
    (hc : ∀ k (γ : List Val), Expr.psub k γ c.1 = c.1)
    (h : ∀ αs ls, αs.length = σ.length → List.IsChain (· < ·) αs →
      RSlot (ℍ := ℍ) δ σ S₀ T αs ls c PMap.empty) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val c) T := by
  intro αs ls γ ρ hlen hch _ hg
  obtain rfl := rSep_deadP hch hΓ (pure_sep_iff.mp hg).2
  show wpTS ls (Expr.psub 0 γ c.1) _ PMap.empty
  rw [hc]
  exact wpTS_val ls c _ PMap.empty (h αs ls hlen hch)

/-- **`copy : U (!A ⊸ F (!A ⊗ !A))`**: both copies are the original, at `∅`. -/
theorem pv_copyBang {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ copy (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A))))) := by
  refine pv_const (c := ⟨.lam (.pair BoCa.v0 BoCa.v0), .lam⟩) hΓ
    (fun k γ => by simp [Expr.psub, BoCa.v0]) fun αs ls hlen _ => ?_
  refine rslot_const hlen ls fun αs' ls' _ => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val _) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  refine rc_head _ (fun μ => Head.beta μ (.pair BoCa.v0 BoCa.v0) v) rfl αs' ls' ρ₁ ?_
  have hb : Expr.subst 0 v (.pair BoCa.v0 BoCa.v0) = Expr.pair (.val v) (.val v) := by
    simp [BoCa.v0, Expr.subst]
  rw [hb]
  obtain ⟨rfl, hv'⟩ := hv
  exact rc_ret_val (v := Val.pair v v) ⟨v, v, pure_sep_mk rfl ⟨PMap.empty, PMap.empty,
    ResU.comp_empty_right _, ⟨rfl, hv'⟩, ⟨rfl, hv'⟩⟩⟩

/-- **`forget : U (!A ⊸ F 1)`**: nothing to release. -/
theorem pv_forgetBang {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ forget (.thunk (.arr (.bang A) (.ret .unit))) := by
  refine pv_const (c := ⟨.lam unit', .lam⟩) hΓ (fun k γ => by simp [Expr.psub, unit'])
    fun αs ls hlen _ => ?_
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val _) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  obtain ⟨rfl, -⟩ := hv
  refine rc_head _ (fun μ => Head.beta μ unit' v) rfl αs' ls' PMap.empty ?_
  have hb : Expr.subst 0 v unit' = unit' := by simp [unit', Expr.subst]
  rw [hb]
  exact rc_ret_val (v := Val.unit)
    (rslot_unit ((List.Forall₂.length_eq hr.1).trans hlen) ls')

/-! ### `[@a]`, and the lifetime index of `Imm` and `Mut` -/

/-- The types `RSlot` reads at the kernel's relation, named. -/
macro "leafR" : term => `(⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h),
    (fun _ h => nomatch h)⟩)

/-- **6.60 at the re-lendable reading**: a re-lendable value of a type outliving `@a` lies in
`Res_{@a}` at the current lifetimes. -/
theorem rslot_outlives {Δ : LifeCtx} {a : Lifetime.Life} {α : Life} {αs : List Life}
    (hδ : Δ.Models (extS δ σ αs)) (ha : a.interp (extS δ σ αs) = some α)
    (hch : List.IsChain (· < ·) αs) (A : VTy) (hA : VOutlives Δ a A) :
    ∀ {ls : List SRec} {v : Val} {ρ : WRes}, RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ →
      ρ.InStratum α := by
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨C, rfl⟩ | ⟨A', rfl⟩ | ⟨A', rfl⟩ |
    ⟨b, A', rfl⟩ | ⟨L, rfl⟩ | hL
  · cases hA with
    | tensor h₁ h₂ =>
        intro ls v ρ h
        obtain ⟨v₁, v₂, hq⟩ := h
        obtain ⟨-, ρ₁, ρ₂, hc, g₁, g₂⟩ := pure_sep_iff.mp hq
        exact (outlives_comp hc α).mpr
          ⟨rslot_outlives hδ ha hch A₁ h₁ g₁, rslot_outlives hδ ha hch A₂ h₂ g₂⟩
  · cases hA with
    | sum h₁ h₂ =>
        intro ls v ρ h
        rcases h with ⟨v₁, hq⟩ | ⟨v₂, hq⟩
        · exact rslot_outlives hδ ha hch A₁ h₁ (pure_sep_iff.mp hq).2
        · exact rslot_outlives hδ ha hch A₂ h₂ (pure_sep_iff.mp hq).2
  · cases hA
  · intro ls v ρ h
    rw [h.1]; exact ResU.inStratum_empty α
  · cases hA with
    | ref h₁ =>
        intro ls v ρ h
        obtain ⟨ℓ, w, hq⟩ := h
        obtain ⟨-, ρ₁, ρ₂, hc, ho, hp⟩ := pure_sep_iff.mp hq
        exact (outlives_comp hc α).mpr ⟨by rw [ho]; exact ResU.inStratum_single_own α ℓ w,
          rslot_outlives hδ ha hch A' h₁ hp⟩
  · cases hA with
    | box hle =>
        intro ls v ρ h
        rw [rslot_box_eq] at h
        obtain ⟨β, hb, -, ho⟩ := relendableS_now hch h
        obtain ⟨α', β', ha', hb', hle'⟩ := hle _ hδ
        rw [ha] at ha'; cases Option.some.inj ha'
        rw [hb] at hb'; cases Option.some.inj hb'
        exact ho.mono (show (α : Life) ≤ β from hle')
  · cases hA with
    | fam hL =>
        intro ls v ρ h
        obtain ⟨ℓ, n, hq⟩ := h
        obtain ⟨-, hs⟩ := pure_sep_iff.mp hq
        exact sepRange_closed (ResU.inStratum_empty α)
          (fun _ _ _ hc g₁ g₂ => (outlives_comp hc α).mpr ⟨g₁, g₂⟩)
          (fun m τ hτ => rslot_outlives hδ ha hch L hL hτ) hs
  · intro ls v ρ h
    rw [rslot_leaf hL] at h
    exact vC_outlives hδ ha hA true ls v ρ (relendableS_now hch h)
termination_by sizeOf A

/-- **`[]I` at a type outliving the lifetime**: at every re-lend, the re-lent value is in
`Res_{@a}` (`rslot_outlives`, `Δ` modelled there). -/
theorem pv_boxI_outlives {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} {a : Lifetime.Life}
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ e A) (hdef : Δ.Defines a) (hA : VOutlives Δ a A) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.box a A) := by
  intro αs ls γ ρ hlen hch hΔ hg
  refine wpTS_mono (fun ls' v τ hv => ?_) ρ (h αs ls γ ρ hlen hch hΔ hg)
  rw [rslot_box_eq]
  refine relendableS_mono_rel (fun αs' ls'' hr τ' hτ => ?_) τ (rslot_relendable A hlen hv)
  obtain ⟨α', ha'⟩ := hdef _ (hΔ αs' hr)
  exact ⟨α', ha', hτ, rslot_outlives (hΔ αs' hr) ha' hr.2 A hA hτ⟩

/-- **`[]E`**: the boxed value at the current lifetimes. -/
theorem pv_boxE {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} {a : Lifetime.Life}
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.box a A)) : PV (ℍ := ℍ) δ σ S₀ Δ Γ e A :=
  fun αs ls γ ρ hlen hch hΔ hg => wpTS_mono (fun ls' v τ hv => by
    rw [rslot_box_eq] at hv
    obtain ⟨_, -, hb, -⟩ := relendableS_now hch hv
    exact hb) ρ (h αs ls γ ρ hlen hch hΔ hg)

/-- **`⊑imm`**: at every re-lend, `Δ` modelled there, the shorter lifetime. -/
theorem pv_immSub {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {A : VTy}
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.imm b A)) (hle : Δ.EntailsLe a b) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.imm a A) := by
  intro αs ls γ ρ hlen hch hΔ hg
  refine wpTS_mono (fun ls' v τ hv => ?_) ρ (h αs ls γ ρ hlen hch hΔ hg)
  rw [rslot_leaf (A := .imm b A) leafR] at hv
  rw [rslot_leaf (A := .imm a A) leafR]
  refine relendableS_mono_rel (fun αs' ls'' hr τ' hτ => ?_) τ hv
  obtain ⟨α, β, ha, hb, hle'⟩ := hle _ (hΔ αs' hr)
  obtain ⟨β', hβ', ℓ, hs⟩ := hτ
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  obtain ⟨hvl, himm⟩ := pure_sep_iff.mp hs
  exact ⟨α, ha, ℓ, pure_sep_mk hvl (ptoImmS_antitone hle' himm)⟩

/-- **`⊑mut`**: at every re-lend, `Δ` modelled there, the shorter lifetime (M Vary). -/
theorem pv_mutSub {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {A : VTy}
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.mut b A)) (hle : Δ.EntailsLe a b) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.mut a A) := by
  intro αs ls γ ρ hlen hch hΔ hg
  refine wpTS_mono (fun ls' v τ hv => ?_) ρ (h αs ls γ ρ hlen hch hΔ hg)
  rw [rslot_leaf (A := .mut b A) leafR] at hv
  rw [rslot_leaf (A := .mut a A) leafR]
  refine relendableS_mono_rel (fun αs' ls'' hr τ' hτ => ?_) τ hv
  obtain ⟨α, β, ha, hb, hle'⟩ := hle _ (hΔ αs' hr)
  obtain ⟨β', hβ', ℓ, hs⟩ := hτ
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  obtain ⟨hvl, hmut⟩ := pure_sep_iff.mp hs
  exact ⟨α, ha, ℓ, pure_sep_mk hvl (ptoMutS_antitone hle' hmut)⟩

/-! ### The borrow axioms on `Ref`, `Imm`, `Mut`, `Unk`, and the integer constants -/

/-- A run to a re-lendable answer is the piece at `F A`. -/
theorem rc_ret_of_wpTS {A : VTy} {αs : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : wpTS ls e (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ A αs ls' v) ρ) :
    RC (ℍ := ℍ) δ σ S₀ (.ret A) αs ls e ρ := by
  rw [RC]
  exact wpG_mono (fun ls' t τ hq => Or.inl hq) ((wpTS_iff_wpG _ _ _ _).mp h)

/-- **`alloc : A ⊸ Ref A`**: the cell, owned, frozen beside its re-lendable payload. -/
theorem pv_alloc {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .alloc)) (.lolli A (.ref A)) := by
  refine pv_const (c := Val.prim .alloc) hΓ (fun k γ => rfl) fun αs ls hlen _ => ?_
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr A (.ret (.ref A))) αs' ls' (.val (Val.prim .alloc)) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  refine rc_ret_of_wpTS (wpTS_alloc ls' v _ ρ₁ ?_)
  intro ℓ σ' τ hcell hc'
  exact ⟨ℓ, v, pure_sep_mk rfl ⟨σ', ρ₁, ResU.CompS.comm hc', hcell, hv⟩⟩

/-- **`free : Ref A ⊸ A`**: the payload, re-lendable as it was. -/
theorem pv_free {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .free)) (.lolli (.ref A) A) := by
  refine pv_const (c := Val.prim .free) hΓ (fun k γ => rfl) fun αs ls hlen _ => ?_
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr (.ref A) (.ret A)) αs' ls' (.val (Val.prim .free)) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  obtain ⟨ℓ, w, hs⟩ := hv
  obtain ⟨rfl, hsep⟩ := pure_sep_iff.mp hs
  exact rc_ret_of_wpTS (wpTS_free ls' ℓ w _ _ hsep)

/-- An `imm` cell composes with itself to itself. -/
theorem ptoImmS_idem {l : BoCa.Loc} {α : Life} {ls : List SRec} {P : List SRec → Val → WProp}
    {ρ : WRes} (hp : ptoImmS l α ls P ρ) : ResU.CompS ρ ρ ρ := by
  obtain ⟨s, v, σ, hs, ls₀, rfl, -, -, -⟩ := hp
  have h₃ : σ.InStratum (s ∪ s).join := ResU.InStratum.sup hs hs
  have e : CellU.immOf (s ∪ s) v σ h₃ = CellU.immOf s v σ hs :=
    CellU.immOf_congr (LSet.union_self s) rfl rfl h₃ hs
  have hcomp := ResU.compS_single_imm l s s v σ hs hs h₃
  rw [e] at hcomp
  exact hcomp

/-- **`copy : Imm @a A ⊸ Imm @a A ⊗ Imm @a A`**: the `imm` cell is duplicated, each copy the
original's re-lendable reading. -/
theorem pv_copy {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ copy (axCopyTy a A) := by
  refine pv_const (c := ⟨.lam (.pair BoCa.v0 BoCa.v0), .lam⟩) hΓ
    (fun k γ => by simp [Expr.psub, BoCa.v0]) fun αs ls hlen _ => ?_
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val _) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  refine rc_head _ (fun μ => Head.beta μ (.pair BoCa.v0 BoCa.v0) v) rfl αs' ls' ρ₁ ?_
  have hb : Expr.subst 0 v (.pair BoCa.v0 BoCa.v0) = Expr.pair (.val v) (.val v) := by
    simp [BoCa.v0, Expr.subst]
  rw [hb]
  have hk := hv
  rw [rslot_leaf (A := .imm a A) leafR] at hk
  obtain ⟨α, -, ℓ, hs⟩ := relendableS_now hr.2 hk
  obtain ⟨-, himm⟩ := pure_sep_iff.mp hs
  exact rc_ret_val (v := Val.pair v v) ⟨v, v, pure_sep_mk rfl ⟨ρ₁, ρ₁, ptoImmS_idem himm, hv, hv⟩⟩

/-- **`forget : Imm @a A ⊸ 1`**: the `imm` cell is released. -/
theorem pv_forgetImm {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ forget (axForgetImmTy a A) := by
  refine pv_const (c := ⟨.lam unit', .lam⟩) hΓ (fun k γ => by simp [Expr.psub, unit'])
    fun αs ls hlen _ => ?_
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val _) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  refine rc_head _ (fun μ => Head.beta μ unit' v) rfl αs' ls' ρ₁ ?_
  have hb : Expr.subst 0 v unit' = unit' := by simp [unit', Expr.subst]
  rw [hb]
  rw [rslot_leaf (A := .imm a A) leafR] at hv
  obtain ⟨α, -, ℓ, hs⟩ := relendableS_now hr.2 hv
  obtain ⟨-, himm⟩ := pure_sep_iff.mp hs
  exact rc_ret_of_wpTS (wpTS_I_forget ls' ℓ α _ _ _ _
    ⟨_, PMap.empty, ResU.comp_empty_right _, ptoImmS_ptoImm himm,
      wpTS_val ls' .unit _ _ (rslot_unit ((List.Forall₂.length_eq hr.1).trans hlen) ls')⟩)

/-- **`forget : Mut @a A ⊸ 1`**: the `mut` cell is released. -/
theorem pv_forgetMut {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ forget (axForgetMutTy a A) := by
  refine pv_const (c := ⟨.lam unit', .lam⟩) hΓ (fun k γ => by simp [Expr.psub, unit'])
    fun αs ls hlen _ => ?_
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val _) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  refine rc_head _ (fun μ => Head.beta μ unit' v) rfl αs' ls' ρ₁ ?_
  have hb : Expr.subst 0 v unit' = unit' := by simp [unit', Expr.subst]
  rw [hb]
  rw [rslot_leaf (A := .mut a A) leafR] at hv
  obtain ⟨α, -, ℓ, hs⟩ := relendableS_now hr.2 hv
  obtain ⟨-, hmut⟩ := pure_sep_iff.mp hs
  obtain ⟨P', hmut'⟩ := ptoMutS_ptoMut hmut
  exact rc_ret_of_wpTS (wpTS_M_forget ls' ℓ α P' _ _ _
    ⟨_, PMap.empty, ResU.comp_empty_right _, hmut',
      wpTS_val ls' .unit _ _ (rslot_unit ((List.Forall₂.length_eq hr.1).trans hlen) ls')⟩)

/-- **`forget : Unk ⊸ 1`**: an `Unk` value holds nothing. -/
theorem pv_forgetUnk {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ forget axForgetUnkTy := by
  refine pv_const (c := ⟨.lam unit', .lam⟩) hΓ (fun k γ => by simp [Expr.psub, unit'])
    fun αs ls hlen _ => ?_
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val _) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  refine rc_head _ (fun μ => Head.beta μ unit' v) rfl αs' ls' ρ₁ ?_
  have hb : Expr.subst 0 v unit' = unit' := by simp [unit', Expr.subst]
  rw [hb]
  rw [rslot_leaf (A := .unk) leafR] at hv
  obtain ⟨rfl, -⟩ := relendableS_now hr.2 hv
  exact rc_ret_val (rslot_unit ((List.Forall₂.length_eq hr.1).trans hlen) ls')

/-- **An integer literal**, frozen. -/
theorem pv_lit {Δ : LifeCtx} {Γ : Ctx VTy} (c : IntLit) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val ⟨.prim (.lit c), .prim⟩) (.int c.width) := by
  refine pv_const hΓ (fun k γ => rfl) fun αs ls hlen _ => ?_
  rw [rslot_leaf (A := .int c.width) leafR]
  exact relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a) fun ls' _ αs' _ => vP_lit c

theorem noThunkT_hostArg (op : HostOp) : NoThunkT (hostArg op) := by
  cases op <;> first | trivial | (rename_i w _; cases w <;> exact ⟨trivial, trivial⟩) |
    (rename_i w; cases w <;> trivial) | (rename_i w _; cases w <;> trivial)

theorem noThunkT_hostRes (op : HostOp) : NoThunkT (hostRes op) := by
  cases op <;> simp [hostRes, NoThunkT, VTy.boolT]

theorem hostRes_free (op : HostOp) (x : LifeVar) : ¬ VFree x (hostRes op) := by
  cases op <;> simp [hostRes, VFree, VTy.boolT]

/-- **A host operation** at `!(hostArg ⊸ F hostRes)`: its argument, data, at the kernel's
relation; its answer, data reading no lifetime, frozen. -/
theorem pv_hostOp {Δ : LifeCtx} {Γ : Ctx VTy} (op : HostOp) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim (.host op))) (.bang (hostSig op)) := by
  refine pv_const hΓ (fun k γ => rfl) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr (hostArg op) (.ret (hostRes op))) αs' ls' (.val _) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  have hv' := rslot_vC (hostArg op) (noThunkT_hostArg op) hr.2 hv
  obtain ⟨rfl, r, hr', hres⟩ := host_call_sound ℍ op (ls' := ls') hv'
  refine rc_head _ (fun μ => Head.host μ op v r hr') rfl αs' ls' PMap.empty ?_
  exact rc_ret_val (rslot_of_frozen (hostRes op) (noThunkT_hostRes op)
    (fun e _ => hostRes_free op e.x) ((List.Forall₂.length_eq hr.1).trans hlen) hres
    (fun a _ => ResU.inStratum_empty a))

/-- **`f a`, call by value** at `A ⊸ B`: the argument, then the closure, then the call, each run
holding the earlier answers in its frame. -/
theorem pv_lolliE {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {f a : Expr} {A B : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (ha : PV (ℍ := ℍ) δ σ S₀ Δ Γ₁ a A)
    (hf : PV (ℍ := ℍ) δ σ S₀ Δ Γ₂ f (.lolli A B)) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.app f a) B := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  show wpTS ls (.app (substAll γ f) (substAll γ a)) _ ρ
  refine wpTS_bind_frame (.appR (substAll γ f) .hole) (substAll γ a) ls
    (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ A αs ls' v) (fun ls' => RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γ₂ γ) _
    (fun ls' hls τ h => rctx_local (ext_of_same hls τ) h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, ha αs ls γ ρ₁ hlen hch hΔ hg₁, hg₂⟩
  rintro ls' - v₁ τ ⟨τ₁, τ₂, hcτ, hv₁, hg₂'⟩
  refine wpTS_bind_frame (.appL .hole v₁) (substAll γ f) ls'
    (fun ls'' v => RSlot (ℍ := ℍ) δ σ S₀ (.lolli A B) αs ls'' v)
    (fun ls'' => RSlot (ℍ := ℍ) δ σ S₀ A αs ls'' v₁) _
    (fun ls'' hls τ h => rslot_local A (ext_of_same hls τ) h) ?_ τ
    ⟨τ₂, τ₁, ResU.CompS.comm hcτ, hf αs ls' γ τ₂ hlen hch hΔ hg₂', hv₁⟩
  rintro ls'' - v₂ υ ⟨υ₁, υ₂, hcυ, hv₂, hv₁'⟩
  rw [rslot_thunk_eq] at hv₂
  have h₁ := relendableS_now hch hv₂
  simp only [forceE] at h₁
  rw [rc_arr_eq] at h₁
  exact wpTS_of_rc_ret (h₁ v₁ υ₂ υ hv₁' hcυ)

/-- **`roll`** at a `μ` type whose unrolling holds no `U`: at every re-lend the unrolled value is
in the kernel's relation, which rolls. -/
theorem pv_roll {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} (hA : A.NoMut 0)
    (hc : (VTy.mu A).Cl 0) (hN : NoThunkT (VTy.inst (.mu A) A))
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ e (VTy.inst (.mu A) A)) : PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.mu A) := by
  intro αs ls γ ρ hlen hch hΔ hg
  refine wpTS_mono (fun ls' v τ hv => ?_) ρ (h αs ls γ ρ hlen hch hΔ hg)
  rw [rslot_leaf (A := .mu A) leafR]
  exact relendableS_mono_rel (fun αs' ls'' hr τ' hτ => vC_roll hA hc (rslot_vC _ hN hr.2 hτ)) τ
    (rslot_relendable _ hlen hv)

/-- **`Λ. M : ∀'x ⊏ @b. C`** at a context free of `U`: `∀` is read at the kernel's relation, which
the body's own derivation gives (`fundamentalC`, `allI_compatC`), the context read at the kernel's
relation at the current lifetimes. -/
theorem pj_allI_kernel {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life} {M : Expr}
    {S : VTy} {C : CTy} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (hd : CDerives (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) (hΓ : CtxNoThunk Γ) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam M)) (.all x b C) := by
  intro αs ls γ ρ _ hch hΔ hg
  rw [rc_all_eq]
  have hsem : SemC Δ Γ (.val (.lam M)) (.all x b C) :=
    allI_compatC hbx hΔx hΓx ((semC_liveEq (.dead (LiveEq.refl _))).mp (fundamentalC (ℍ := ℍ) hd))
  exact hsem (extS δ σ αs) γ ls ρ (hΔ αs (reLend_refl hch)) (rctx_gDenC hch hΓ hg)

/-! ### The effect rules -/

/-- **The piece grows with its table and with what it catches inside**: `[sub]` at one run. -/
theorem bodyH_tab_mono {To To' : OpTab} {RI RI' : UInt32 → UInt32 → Option InRel}
    {Q : List Life → List SRec → Val → WProp} {X X' : XT} {αs : List Life}
    (hT : To.Le To') (hR : ∀ n i P, RI n i = some P → RI' n i = some P)
    (hX : ∀ k ds αi αo ls e ρ, X k ds αi αo ls e ρ → X' k ds αi αo ls e ρ) {ls : List SRec}
    {e : Expr} : Entails (bodyH δ σ To RI Q X αs ls e) (bodyH δ σ To' RI' Q X' αs ls e) :=
  fun _ h => wpG_mono (fun _ _ _ hq => hq.imp id (Or.imp
    (fun ⟨ds, ρ₁, ρ₂, hc, hd, hb, hs⟩ =>
      ⟨ds, ρ₁, ρ₂, hc, hd, opTable_le hT (opTable_mono _ _ _ _ _ _
        (fun _ _ _ h => hX _ _ _ _ _ _ _ h) hb), hs⟩)
    (fun ⟨K, n, i, v, P, hp⟩ => by
      obtain ⟨⟨ht, hK, hP⟩, ρa, ρk, hc, hA, hk⟩ := pure_sep_iff.mp hp
      exact ⟨K, n, i, v, P, pure_sep_mk ⟨ht, hK, hR n i P hP⟩ ⟨ρa, ρk, hc, hA,
        relendableS_mono' (P' := fun αs' ls' ρ => ∀ w,
            (P.2 αs' ls' w ─⋆ X' 0 [] [] αs' ls' (K.plug (.val w))) ρ)
          (fun αs' ls' τ hτ w => wand_mono_right
            (fun _ h => hX _ _ _ _ _ _ _ h) τ (hτ w)) ρk hk⟩⟩))) h

/-- **The piece grows with its table and with what it catches inside**, at every
continuation. -/
theorem openH_tab_mono {To To' : OpTab} {RI RI' : UInt32 → UInt32 → Option InRel}
    {Q : List Life → List SRec → Val → WProp} (hT : To.Le To')
    (hR : ∀ n i P, RI n i = some P → RI' n i = some P) {k : Nat} {ds : List Bool}
    {αi αo : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenH δ σ To RI Q k ds αi αo ls e ρ) : OpenH δ σ To' RI' Q k ds αi αo ls e ρ := by
  refine h (OpenH δ σ To' RI' Q) (fun k ds αi αo ls e ρ hF => openH_fold ?_)
  exact fun αi' hlt hch => boxTop_mono (wand_mono_right (bodyH_tab_mono hT hR
    (fun _ _ _ _ _ _ _ h => h))) ρ (hF αi' hlt hch)

/-- `RTab` grows with the row. -/
theorem rTab_le {S S' : Row} (hle : RowLe S S') (A : VTy) :
    (RTab (ℍ := ℍ) δ S₀ (CTy.effOf S A)).Le (RTab (ℍ := ℍ) δ S₀ (CTy.effOf S' A)) := by
  intro m j en hT
  rw [rTab_effOf] at hT ⊢
  dsimp only at hT ⊢
  by_cases ho : outN S₀ m = true
  · rw [if_pos ho] at hT ⊢
    exact Row.tab_le δ hle m j en hT
  · rw [if_neg ho] at hT; cases hT

/-- `RIn` grows with the row: an operation it catches keeps its signature. -/
theorem rIn_le {S S' : Row} (hle : RowLe S S') (A : VTy) :
    ∀ n i P, RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S A) n i = some P →
      RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S' A) n i = some P := by
  intro n i P hP
  obtain ⟨o, hf, hout, rfl⟩ := rIn_effOf_some S hP
  obtain ⟨o', hf', hLe⟩ := hle n i o hf
  rw [rIn_effOf_find A S' hf' hout, hLe.1.2.2.2.1, hLe.1.2.2.2.2]

/-- **`[sub]`**: `F_Σ A ≤ F_Σ′ A`. The piece at `Σ` is the piece at `Σ′`: its table and what it
catches inside grow, its answers are the same. -/
theorem pj_effSub {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {S S' : Row} {A : VTy}
    (hle : RowLe S S') (h : PJ (ℍ := ℍ) δ σ S₀ Δ Γ e (CTy.effOf S A)) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ e (CTy.effOf S' A) := by
  refine pj_effOf_iff.mpr fun αs ls γ ρ hlen hch hΔ hg => ?_
  have hb := pj_effOf_iff.mp h αs ls γ ρ hlen hch hΔ hg
  have hQ : QA (ℍ := ℍ) δ σ S₀ (CTy.effOf S A) = QA (ℍ := ℍ) δ σ S₀ (CTy.effOf S' A) := by
    funext αs' ls' v; simp only [QA, rAns_effOf]
  simp only [BHC, OHC] at hb ⊢
  rw [hQ] at hb
  exact bodyH_tab_mono (rTab_le hle A) (rIn_le hle A)
    (fun _ _ _ _ _ _ _ hO => openH_tab_mono (rTab_le hle A) (rIn_le hle A) hO) ρ hb

/-- **An operation a borrower may stop at with its lends open**: non-abortive, linear, answered at
`1`, its argument data reading none of the stack's variables, outliving every lifetime, holding no
`U`. -/
def ResumeOp (σ : LStack) (o : OpSig) : Prop :=
  o.abort = false ∧ o.q = .lin ∧ o.B = .unit ∧ (∀ e ∈ σ, ¬ VFree e.x o.A) ∧
    (∀ Δ a, VOutlives Δ a o.A) ∧ NoThunkT o.A

/-- **`[perform]` at a lenders' name, at a resuming operation**: the stop crosses every lend. -/
theorem pj_effPerform_resume {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig}
    (hf : Row.find S o.n o.i = some o) (hout : outN S₀ o.n = true) (hR : ResumeOp σ o)
    (hV : PV (ℍ := ℍ) δ σ S₀ Δ Γ V o.A) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (performE (opArgE o.n o.i V)) (CTy.effOf S o.B) :=
  pj_perform hf hout hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 hR.2.2.2.2.1 hR.2.2.2.2.2 hV

/-- **The polymorphic let** (`[let-poly]`): the closed λ-value substituted, its slot dead. -/
theorem pj_letPoly {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (V : Val)
    (hV : closedAt 0 V.1 = true)
    (hN : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨.unit, false⟩ :: Γ) ((N.subst 0 V).shift 1 0) C) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app (.val (.lam N)) (.val V)) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  have h := hN αs ls (V :: γ) ρ hlen hch hΔ (rctx_dead_cons.mpr hg)
  have e₁ : substAll (V :: γ) ((N.subst 0 V).shift 1 0) = (Expr.psub 1 γ N).subst 0 V := by
    show Expr.psub 0 (V :: γ) _ = _
    rw [psub_fill hV γ N 0, Expr.psub_cons 0 V γ N, Val.shift_zero]
  rw [e₁] at h
  show RC δ σ S₀ C αs ls (Expr.psub 0 γ (.app (.val (.lam N)) (.val V))) ρ
  simp only [Expr.psub]
  rw [psub_closedAt V.1 γ hV (Nat.zero_le 0)]
  exact rc_head C (fun μ => Head.beta μ (Expr.psub 1 γ N) V) rfl αs ls ρ h

/-- **`swap : Ref A ⊸ B ⊸ Ref B ⊗ A`**: the partial application holds the reference, re-lendable
with it; called at a re-lend it loads the old payload, stores the new one, and answers both. -/
theorem pv_swap {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ swap (axSwapTy A B) := by
  intro αs ls γ ρ hlen hch _ hg
  obtain rfl := rSep_deadP hch hΓ (pure_sep_iff.mp hg).2
  have hcl : Expr.psub 0 γ swap = swap := psub_closedAt swap γ rfl (Nat.zero_le 0)
  show wpTS ls (Expr.psub 0 γ swap) _ _
  rw [hcl]
  refine wpTS_val ls ⟨_, .lam⟩ _ _ ?_
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val _) PMap.empty
  rw [rc_arr_eq]
  intro v₁ ρ₁ ρ₂ hv₁ hc
  rw [eq_of_compS_empty_left hc]
  have hlen' : αs'.length = σ.length := (List.Forall₂.length_eq hr.1).trans hlen
  have hr₁ := rslot_relendable (.ref A) hlen' hv₁
  obtain ⟨ℓ, w, hs₁⟩ := hv₁
  obtain ⟨rfl, -, -, -, -, -⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (elet (.app load' BoCa.v1)
          (.seq (.app (.app store' BoCa.v2) BoCa.v1) (.pair BoCa.v2 BoCa.v0)))))
      = Expr.val (Val.lam (elet (eLoad ℓ)
          (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                (.pair (.val (.loc ℓ)) BoCa.v0)))) := by
    simp [elet, eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, BoCa.v2, load', store']
  refine rc_head _ (fun μ => Head.beta μ _ (Val.loc ℓ)) rfl αs' ls' ρ₁ ?_
  rw [hβ₁]
  refine rc_ret_val (v := ⟨_, .lam⟩) ?_
  rw [rslot_thunk_eq]
  refine relendableS_mono_rel (fun αs'' ls'' hr' τ hτ => ?_) ρ₁ hr₁
  show RC δ σ S₀ (.arr _ _) αs'' ls'' (.val _) τ
  rw [rc_arr_eq]
  intro v₂ ρ₂ τ' hv₂ hc₂
  obtain ⟨ℓ', w', hs⟩ := hτ
  obtain ⟨hℓ, b₁, b₂, hcb, rfl, hA⟩ := pure_sep_iff.mp hs
  obtain rfl : ℓ = ℓ' := Val.loc_inj.mp hℓ
  have hβ₂ : Expr.subst 0 v₂
        (elet (eLoad ℓ) (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                              (.pair (.val (.loc ℓ)) BoCa.v0)))
      = elet (eLoad ℓ) (.seq (eStore ℓ (v₂.shift 1 0)) (.pair (.val (.loc ℓ)) BoCa.v0)) := by
    simp [elet, eLoad, eStore, Expr.subst, BoCa.v0, BoCa.v1, store']
  refine rc_head _ (fun μ => Head.beta μ _ v₂) rfl αs'' ls'' τ' ?_
  rw [hβ₂]
  refine rc_ret_of_wpTS ?_
  obtain ⟨u, hu, hτu⟩ := compS_reassoc hcb hc₂
  refine wpTS_bind (.appR (.val (.lam _)) .hole) (eLoad ℓ) ls'' _ τ' ?_
  refine wpTS_load ls'' ℓ w' _ τ' ⟨_, u, hτu, rfl, ?_⟩
  intro ρ' σ' hp' hc'
  subst hp'
  simp only [Kont.plug]
  have hβ₃ : Expr.subst 0 w'
        (Expr.seq (eStore ℓ (v₂.shift 1 0)) (.pair (.val (.loc ℓ)) BoCa.v0))
      = Expr.seq (eStore ℓ v₂) (.pair (.val (.loc ℓ)) (.val w')) := by
    simp [eStore, Expr.subst, BoCa.v0,
      Expr.subst_shift 0 0 0 w' v₂.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  refine wpTS_lolli _ _ w' _ _ ?_
  rw [hβ₃]
  refine wpTS_bind (.seq .hole (.pair (.val (.loc ℓ)) (.val w'))) (eStore ℓ v₂) ls'' _ _ ?_
  refine wpTS_store ls'' ℓ w' v₂ _ _ ⟨_, u, ResU.CompS.comm hc', rfl, ?_⟩
  intro ρ₃ σ₃ hp₃ hc₃
  subst hp₃
  simp only [Kont.plug]
  refine wpTS_1 _ _ _ _ ?_
  refine wpTS_val ls'' (.pair (.loc ℓ) w') _ _ ?_
  obtain ⟨R, hR, hb₂R⟩ := compS_reassoc hu hc₃
  exact ⟨.loc ℓ, w', pure_sep_mk rfl
    ⟨R, b₂, ResU.CompS.comm hb₂R,
      ⟨ℓ, v₂, pure_sep_mk rfl ⟨_, ρ₂, ResU.CompS.comm hR, rfl, hv₂⟩⟩, hA⟩⟩

/-! ### Families: the size, the length, forgetting, the empty family, copying -/

/-- A family's shape: a location and a length. -/
theorem rslot_fam_shape {L : VTy} {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes}
    (h : RSlot (ℍ := ℍ) δ σ S₀ (.fam L) αs ls v ρ) : ∃ ℓ n, v = Val.arr ℓ n := by
  obtain ⟨ℓ, n, hq⟩ := h
  exact ⟨ℓ, n, (pure_sep_iff.mp hq).1.1⟩

/-- A family of `imm` leaves, at the current lifetimes: the kernel's. -/
theorem rslot_arrayImm_now {a : Lifetime.Life} {A : VTy} {αs : List Life} {ls : List SRec}
    {v : Val} {ρ : WRes} (hch : List.IsChain (· < ·) αs)
    (h : RSlot (ℍ := ℍ) δ σ S₀ (.arrayImm a A) αs ls v ρ) :
    vCE (ℍ := ℍ) none true (.arrayImm a A) ls (extS δ σ αs) v ρ :=
  rslot_vC (.fam (.imm a A)) trivial hch h

/-- An `I32`, frozen. -/
theorem rslot_i32 {αs : List Life} (hlen : αs.length = σ.length) (ls : List SRec) (n : UInt32) :
    RSlot (ℍ := ℍ) δ σ S₀ (.int .w32) αs ls (Val.i32 n) PMap.empty := by
  rw [rslot_leaf (A := .int .w32) leafR]
  exact relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a) fun _ _ _ _ => vP_i32 n

/-- **The size of a family** (`array_size`, `slice_len_mut`): the family answered as it came, its
re-lendable reading unchanged, beside its length, frozen. -/
theorem pv_famSize {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val sizeV) (.bang (.lolli (.fam L) (.tensor (.fam L) (.int .w32)))) := by
  refine pv_const hΓ (fun k γ => by simp [sizeV, Expr.psub]) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val sizeV) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  obtain ⟨ℓ, n, rfl⟩ := rslot_fam_shape hv
  refine rc_ret_of_wpTS (wpTS_lolli ls' _ _ _ _ ?_)
  show wpTS ls' (.letpair (.val (Val.arr ℓ n)) (.pair (.pair (.var 1) (.var 0)) (.var 0))) _ _
  refine wpTS_tensor ls' (Val.loc ℓ) (Val.i32 n) _ _ _ ?_
  refine wpTS_val ls' (Val.pair (Val.arr ℓ n) (Val.i32 n)) _ _ ?_
  exact ⟨_, _, pure_sep_mk rfl ⟨ρ₁, PMap.empty, ResU.comp_empty_right ρ₁, hv,
    rslot_i32 ((List.Forall₂.length_eq hr.1).trans hlen) ls' n⟩⟩

theorem pv_arrSize {Δ : LifeCtx} {Γ : Ctx VTy} (A : VTy) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val sizeV) (arrSizeTy A) := pv_famSize hΓ

theorem pv_sliceLenM {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val sizeV) (sliceLenMTy a A) := pv_famSize hΓ

/-- **`array_len`**: the family, holding no `own` cell, dropped; its length, frozen. -/
theorem pv_arrLen {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val arrLenV) (arrLenTy a A) := by
  refine pv_const hΓ (fun k γ => by simp [arrLenV, Expr.psub]) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val arrLenV) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  have hk := rslot_arrayImm_now hr.2 hv
  obtain ⟨ℓ, n, rfl, -, -⟩ := vP_fam_iff.mp hk
  refine rc_ret_of_wpTS (wpTS_drop (noOwn_arrayImm hk) (ResU.comp_empty_right ρ₁) ?_)
  refine wpTS_lolli ls' _ _ _ _ ?_
  show wpTS ls' (.letpair (.val (Val.arr ℓ n)) (.var 0)) _ _
  refine wpTS_tensor ls' (Val.loc ℓ) (Val.i32 n) (.var 0) _ _ ?_
  exact wpTS_val ls' (Val.i32 n) _ _ (rslot_i32 ((List.Forall₂.length_eq hr.1).trans hlen) ls' n)

/-- **`array_forget`**: the family, holding no `own` cell, dropped. -/
theorem pv_arrForget {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val forgetV) (arrForgetTy a A) := by
  refine pv_const hΓ (fun k γ => by simp [forgetV, Expr.psub]) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val forgetV) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  have hk := rslot_arrayImm_now hr.2 hv
  refine rc_ret_of_wpTS (wpTS_drop (noOwn_arrayImm hk) (ResU.comp_empty_right ρ₁) ?_)
  refine wpTS_lolli ls' _ _ _ _ ?_
  exact wpTS_val ls' .unit _ _ (rslot_unit ((List.Forall₂.length_eq hr.1).trans hlen) ls')

/-- **The empty family** (`slice_empty_imm`, `slice_empty_mut`): no leaves, nothing held. -/
theorem pv_famEmpty {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val emptyFamV) (.fam L) := by
  refine pv_const hΓ (fun k γ => by simp [emptyFamV, Val.arr, Val.i32, Expr.psub])
    fun αs ls _ _ => ?_
  exact ⟨0, 0, pure_sep_mk ⟨rfl, by decide⟩ ⟨rfl, trivial⟩⟩

theorem pv_sliceEmptyI {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val emptyFamV) (.arrayImm a A) := pv_famEmpty hΓ

theorem pv_sliceEmptyM {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val emptyFamV) (.sliceMut a A) := pv_famEmpty hΓ

/-- A family of `imm` leaves holds only `imm` cells: it composes with itself to itself. -/
theorem compS_self_arrayImm {a : Lifetime.Life} {A : VTy} {ls : List SRec} {δ' : LSub} {v : Val}
    {ρ : WRes} (h : vCE (ℍ := ℍ) none true (.arrayImm a A) ls δ' v ρ) : ResU.CompS ρ ρ ρ := by
  obtain ⟨ℓ, n, -, -, hs⟩ := vP_fam_iff.mp h
  have hleaf : ∀ k, k ≠ Kind.imm → ∀ m τ, vCE (ℍ := ℍ) none true (.imm a A) ls δ' (.loc m) τ →
      Free k τ := by
    intro k hk m τ hτ
    obtain ⟨α, -, ℓ', hs'⟩ := hτ
    obtain ⟨-, s', u, σ', hσ', ls₀, rfl, -⟩ := pure_sep_iff.mp hs'
    exact free_single (by rw [CellU.kind_immOf]; exact fun e => hk e.symm)
  have hfree : ∀ k, k ≠ Kind.imm → Free k ρ := fun k hk =>
    sepRange_closed (free_empty k) (fun _ _ _ hc h₁ h₂ => free_compS hk hc h₁ h₂)
      (hleaf k hk) hs
  exact compS_self_of_imm (hfree _ (by decide)) (hfree _ (by decide))

/-- **`array_copy`**: a family of `imm` leaves is duplicated, each copy the original's
re-lendable reading. -/
theorem pv_arrCopy {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val copyV) (arrCopyTy a A) := by
  refine pv_const hΓ (fun k γ => by simp [copyV, Expr.psub]) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val copyV) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  have hk := rslot_arrayImm_now hr.2 hv
  refine rc_ret_of_wpTS (wpTS_lolli ls' _ _ _ _ ?_)
  show wpTS ls' (.pair (.val v) (.val v)) _ _
  refine wpTS_val ls' (Val.pair v v) _ _ ?_
  exact ⟨v, v, pure_sep_mk rfl ⟨ρ₁, ρ₁, compS_self_arrayImm hk, hv, hv⟩⟩

/-! ### The counted loops -/

/-- A step held at `!`: applied at the current lifetimes to a re-lendable argument, a run to a
re-lendable answer. -/
theorem bang_app_rs {A B : VTy} {αs : List Life} (hch : List.IsChain (· < ·) αs) {ls₀ ls : List SRec}
    (hls : ∀ x, x ∈ ls ↔ x ∈ ls₀) {f : Val}
    (hf : RSlot (ℍ := ℍ) δ σ S₀ (.bang (.lolli A B)) αs ls₀ f PMap.empty) {a : Val} {ρ : WRes}
    (ha : RSlot (ℍ := ℍ) δ σ S₀ A αs ls a ρ) :
    wpTS ls (.app (.val f) (.val a)) (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ B αs ls' v) ρ := by
  have hf' := rslot_local (.bang (.lolli A B)) (ext_of_same hls PMap.empty) hf
  have h₁ := hf'.2
  rw [rslot_thunk_eq] at h₁
  have h₂ := relendableS_now hch h₁
  simp only [forceE] at h₂
  rw [rc_arr_eq] at h₂
  exact wpTS_of_rc_ret (h₂ a ρ ρ ha (compS_empty_left ρ))

/-- **The counted loop**, from `i`, the state re-lendable: by induction on `len(n) − i`, each step
the re-lendable step on the re-lendable state. -/
theorem countLoop_rs {S : VTy} {αs : List Life} (hch : List.IsChain (· < ·) αs)
    (hlen : αs.length = σ.length) {ls₀ : List SRec} (f : Val) (n : UInt32)
    (hf : RSlot (ℍ := ℍ) δ σ S₀ (.bang (.lolli (.tensor (.int .w32) S) S)) αs ls₀ f PMap.empty) :
    ∀ (k : Nat) (i : UInt32) (ls : List SRec) (s : Val) (ρ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      (arrLen n).toNat - i.toNat = k → RSlot (ℍ := ℍ) δ σ S₀ S αs ls s ρ →
      wpTS ls (.app (.val (.prim .count))
        (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)))))
        (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ S αs ls' v) ρ := by
  intro k
  induction k with
  | zero =>
      intro i ls s ρ _ hk hs
      refine wpTS_count ls f n i s _ ρ ?_
      have hi : ¬ i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      unfold countNext
      rw [if_neg hi]
      exact wpTS_val ls s _ ρ hs
  | succ k ih =>
      intro i ls s ρ hls hk hs
      refine wpTS_count ls f n i s _ ρ ?_
      have hi : i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      have hb := arrLen_bound n
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i.toNat < (arrLen n).toNat := UInt32.lt_iff_toNat_lt.mp hi
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      unfold countNext
      rw [if_pos hi]
      refine wpTS_bind_frame
        (.appR (.val (.prim .count)) (.pairR f (.pairR (Val.i32 n) (.pairR (Val.i32 (i + 1)) .hole))))
        (.app (.val f) (.val (Val.pair (Val.i32 i) s))) ls
        (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ S αs ls' v) (fun _ => emp) _
        (fun _ _ _ h => h) ?_ ρ
        ⟨ρ, PMap.empty, ResU.comp_empty_right ρ,
          bang_app_rs hch hls hf ⟨Val.i32 i, s, pure_sep_mk rfl
            ⟨PMap.empty, ρ, compS_empty_left ρ, rslot_i32 hlen ls i, hs⟩⟩, ⟨rfl, trivial⟩⟩
      rintro ls' hls' v τ ⟨τ₁, τ₂, hc, hv, ⟨rfl, -⟩⟩
      rw [ResU.CompS.functional hc (ResU.comp_empty_right τ₁)]
      exact ih (i + 1) ls' v τ₁ (fun x => (hls' x).trans (hls x)) (by omega) hv

/-- The argument of a counted loop, taken apart: the step, held at `!`, the bound and the start,
integers, and the state. -/
theorem countArg_rs {T S : VTy} {αs : List Life} (hch : List.IsChain (· < ·) αs) {ls : List SRec}
    {v : Val} {ρ : WRes}
    (hv : RSlot (ℍ := ℍ) δ σ S₀ (.tensor (.bang T) (.tensor (.int .w32) (.tensor (.int .w32) S)))
      αs ls v ρ) :
    ∃ f n i s, v = Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)) ∧
      RSlot (ℍ := ℍ) δ σ S₀ (.bang T) αs ls f PMap.empty ∧ RSlot (ℍ := ℍ) δ σ S₀ S αs ls s ρ := by
  obtain ⟨f, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, hf, h₂⟩ := pure_sep_iff.mp hk
  have e₁ : σ₁ = PMap.empty := hf.1
  subst e₁
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨vn, v₃, hk₂⟩ := h₂
  obtain ⟨rfl, ρn, ρ₃, hc₂, hn, h₃⟩ := pure_sep_iff.mp hk₂
  obtain ⟨rfl, n, rfl⟩ := relendableS_now hch hn
  obtain rfl := eq_of_compS_empty_left hc₂
  obtain ⟨vi, s, hk₃⟩ := h₃
  obtain ⟨rfl, ρi, ρs, hc₃, hi, hs⟩ := pure_sep_iff.mp hk₃
  obtain ⟨rfl, i, rfl⟩ := relendableS_now hch hi
  obtain rfl := eq_of_compS_empty_left hc₃
  exact ⟨f, n, i, s, rfl, hf, hs⟩

/-- **`count_fold`**: the counted loop at the re-lendable reading. -/
theorem pv_countFold {Δ : LifeCtx} {Γ : Ctx VTy} (S : VTy) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .count)) (countFoldTy S) := by
  refine pv_const (c := Val.prim .count) hΓ (fun k γ => rfl) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val (Val.prim .count)) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  obtain ⟨f, n, i, s, rfl, hf, hs⟩ := countArg_rs hr.2 hv
  exact rc_ret_of_wpTS (countLoop_rs hr.2 ((List.Forall₂.length_eq hr.1).trans hlen) f n hf _ i
    ls' s ρ₁ (fun _ => Iff.rfl) rfl hs)

/-- **The counted loop with an exit**, from `i`: by induction on `len(n) − i`. -/
theorem countTryLoop_rs {S E : VTy} {αs : List Life} (hch : List.IsChain (· < ·) αs)
    (hlen : αs.length = σ.length) {ls₀ : List SRec} (f : Val) (n : UInt32)
    (hf : RSlot (ℍ := ℍ) δ σ S₀ (.bang (.lolli (.tensor (.int .w32) S) (.sum S E))) αs ls₀ f
      PMap.empty) :
    ∀ (k : Nat) (i : UInt32) (ls : List SRec) (s : Val) (ρ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      (arrLen n).toNat - i.toNat = k → RSlot (ℍ := ℍ) δ σ S₀ S αs ls s ρ →
      wpTS ls (.app (.val (.prim .countTry))
        (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)))))
        (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ (.sum S E) αs ls' v) ρ := by
  intro k
  induction k with
  | zero =>
      intro i ls s ρ _ hk hs
      refine wpTS_countTry ls f n i s _ ρ ?_
      have hi : ¬ i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      unfold countTryNext
      rw [if_neg hi]
      exact wpTS_val ls (Val.inj₁ s) _ ρ (Or.inl ⟨s, pure_sep_mk rfl hs⟩)
  | succ k ih =>
      intro i ls s ρ hls hk hs
      refine wpTS_countTry ls f n i s _ ρ ?_
      have hi : i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      have hb := arrLen_bound n
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i.toNat < (arrLen n).toNat := UInt32.lt_iff_toNat_lt.mp hi
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      unfold countTryNext
      rw [if_pos hi]
      let e₁ : Expr := .app (.val (.prim .countTry)) (.pair (.val (f.shift 1 0))
        (.pair (.val (.i32 n)) (.pair (.val (.i32 (i + 1))) (.var 0))))
      let e₂ : Expr := .inj₂ (.var 0)
      refine wpTS_bind_frame (.case .hole e₁ e₂)
        (.app (.val f) (.val (Val.pair (Val.i32 i) s))) ls
        (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ (.sum S E) αs ls' v)
        (fun _ => emp) _ (fun _ _ _ h => h) ?_ ρ
        ⟨ρ, PMap.empty, ResU.comp_empty_right ρ,
          bang_app_rs hch hls hf ⟨Val.i32 i, s, pure_sep_mk rfl
            ⟨PMap.empty, ρ, compS_empty_left ρ, rslot_i32 hlen ls i, hs⟩⟩, ⟨rfl, trivial⟩⟩
      rintro ls' hls' v τ ⟨τ₁, τ₂, hc, hv, ⟨rfl, -⟩⟩
      rw [ResU.CompS.functional hc (ResU.comp_empty_right τ₁)]
      rcases hv with ⟨s', hs'⟩ | ⟨e, he⟩
      · obtain ⟨rfl, hs₁⟩ := pure_sep_iff.mp hs'
        refine wpTS_sum₁ ls' s' e₁ e₂ _ τ₁ ?_
        show wpTS ls' (Expr.subst 0 s' e₁) _ τ₁
        rw [countTry_cont_subst]
        exact ih (i + 1) ls' s' τ₁ (fun x => (hls' x).trans (hls x)) (by omega) hs₁
      · obtain ⟨rfl, he₁⟩ := pure_sep_iff.mp he
        refine wpTS_sum₂ ls' e e₁ e₂ _ τ₁ ?_
        exact wpTS_val ls' (Val.inj₂ e) _ τ₁ (Or.inr ⟨e, pure_sep_mk rfl he₁⟩)

/-- **`count_try`**: the counted loop with an exit, at the re-lendable reading. -/
theorem pv_countTry {Δ : LifeCtx} {Γ : Ctx VTy} (S E : VTy) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .countTry)) (countTryTy S E) := by
  refine pv_const (c := Val.prim .countTry) hΓ (fun k γ => rfl) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val (Val.prim .countTry)) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  obtain ⟨f, n, i, s, rfl, hf, hs⟩ := countArg_rs hr.2 hv
  exact rc_ret_of_wpTS (countTryLoop_rs hr.2 ((List.Forall₂.length_eq hr.1).trans hlen) f n hf _ i
    ls' s ρ₁ (fun _ => Iff.rfl) rfl hs)

end rules

end Law2

end
