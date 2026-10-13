import DenseCarrier.Faithful
import Core.Compat
import Support.Statics.Presupposed

/-!
# DenseCarrier — the `∀` rules of the fundamental property over `L`

`Core/Compat.lean`'s `allI_compatC` and `allE_compatC`, re-proved over the relation of
`Relation.lean` at every lifetime order `L`, with Core's typing premises:

* `allI_compatD`: `Λ. M : ∀'x ⊏ @b. C` from `M : C` at `Δ, 'x ⊏ @b`. Core's proof, step for
  step: the β-step (`cD_head`), `δ['x ↦ α] ∈ ⟦Δ, 'x ⊏ @b⟧`, and the context's relation unchanged
  at `δ['x ↦ α]` (`vD_extend_of_not_free`).
* `allE_compatD`: `M [] : C[@a/'x]` from `M : ∀'x ⊏ @b. C` and `Δ ⊨ @a ⊏ @b`. Core's proof: the
  clause at `α = @aδ`, and `C[@a/'x]` at `δ` is `C` at `δ['x ↦ @aδ]` (`CTyEqD.instLife`, Core's
  `CTyEq.instLife` with `interpD`, through `cD_tyEq`). The premise is Core's own
  `LifeCtx.EntailsLt`, over `ℕ`; it carries to `L` (`entailsLtD_of_entailsLt`) because the
  lifetimes a reading takes are finitely many and their order is all `@aδ` sees: they are
  re-read in `ℕᵒᵈ` by their rank (`rankIn`), which keeps `⊤`, `⊔`, `⊓` and the strict order on
  them.

Neither proof uses a fact about `L` beyond its being a linear order with a top.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont Step1N)
open BoCa.Lifetime (LifeVar LifeCtx LSubst)

variable {L : Type} [LinearOrder L] [OrderTop L]

/-! ### Head expansion -/

/-- `𝒞⟦C⟧` is closed under a pure step in front (`cC_step`). -/
theorem cD_step (ι : Slots L) : ∀ (C : CTy) {e e' : Expr}, (∀ μ : Heap, Step1N (ℍ := ℍ) μ e μ e') →
    ∀ (ls : List SRec) (δ : LSubD L), Entails (cD (ℍ := ℍ) ι C ls δ e') (cD (ℍ := ℍ) ι C ls δ e)
  | .ret _, _, _, h, ls, _ => wpTS_step h ls _
  | .arr _ C, _, _, h, ls, δ => fun _ h' v ρ₁ ρ₂ hv hc =>
      cD_step ι C (fun μ => (h μ).plug (Kont.appL .hole v)) ls δ _ (h' v ρ₁ ρ₂ hv hc)
  | .top, _, _, _, _, _ => fun _ _ => trivial
  | .all x _ C, _, _, h, ls, δ => fun _ h' α ρ₁ ρ₂ hp hc =>
      cD_step ι C (fun μ => (h μ).plug (Kont.appL .hole _)) ls (δ.extend x α) _
        (h' α ρ₁ ρ₂ hp hc)
  | .amp _ _, _, _, _, _, _ | .nu _, _, _, _, _, _ | .eff _ _ _ _ _ _, _, _, _, _, _ =>
      fun _ h => h

/-- One head step in front of `𝒞⟦C⟧` (`cC_head`). -/
theorem cD_head (ι : Slots L) (C : CTy) {e e' : Expr} (h : ∀ μ : Heap, Head (ℍ := ℍ) μ e μ e')
    (hn : e.allocs = false) (ls : List SRec) (δ : LSubD L) :
    Entails (cD (ℍ := ℍ) ι C ls δ e') (cD (ℍ := ℍ) ι C ls δ e) :=
  cD_step ι C (fun μ => Step1N.head (h μ) hn) ls δ

/-! ### The context -/

theorem atLifeD_congr {δ₁ δ₂ : LSubD L} {a a' : Lifetime.Life} (h : interpD δ₁ a = interpD δ₂ a') :
    atLifeD δ₁ a = atLifeD δ₂ a' := by
  funext F ρ
  unfold atLifeD
  rw [h]

/-- `𝒱⟦A⟧` reads `δ` only at the variables free in `A` (`vC_congr`). -/
theorem vD_congr (ι : Slots L) : ∀ (A : VTy) {δ₁ δ₂ : LSubD L},
    (∀ y, VFree y A → δ₁.find? y = δ₂.find? y) → ∀ ls, vD ι A ls δ₁ = vD ι A ls δ₂
  | .unit, _, _, _, _ => rfl
  | .box a A, δ₁, δ₂, h, ls => by
      funext v
      show atLifeD δ₁ a (fun α => boxD ι α (vD ι A ls δ₁ v)) =
        atLifeD δ₂ a (fun α => boxD ι α (vD ι A ls δ₂ v))
      have ha : interpD δ₁ a = interpD δ₂ a := interpD_congr a (fun y hy => h y (Or.inl hy))
      rw [vD_congr ι A (fun y hy => h y (Or.inr hy)) ls, atLifeD_congr ha]
  | .mut a A, δ₁, δ₂, h, ls => by
      funext v
      show atLifeD δ₁ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutD ι ℓ α ls (fun ls₀ => vD ι A ls₀ δ₁)) =
        atLifeD δ₂ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutD ι ℓ α ls (fun ls₀ => vD ι A ls₀ δ₂))
      have ha : interpD δ₁ a = interpD δ₂ a := interpD_congr a (fun y hy => h y (Or.inl hy))
      simp only [vD_congr ι A (fun y hy => h y (Or.inr hy))]
      rw [atLifeD_congr ha]
  | .tensor _ _, _, _, _, _ | .zero, _, _, _, _ | .sum _ _, _, _, _, _ | .thunk _, _, _, _, _
  | .ref _, _, _, _, _ | .imm _ _, _, _, _, _ | .bang _, _, _, _, _ | .unk, _, _, _, _
  | .tvar _, _, _, _, _ | .mu _, _, _, _, _ | .int _, _, _, _, _ | .fam _, _, _, _, _
  | .opq _, _, _, _, _ => rfl

theorem vD_extend_of_not_free (ι : Slots L) {x : LifeVar} {T : VTy} (h : ¬ VFree x T)
    (ls : List SRec) (δ : LSubD L) (α : L) : vD ι T ls (δ.extend x α) = vD ι T ls δ :=
  vD_congr ι T (fun y hy => LSubD.find?_extend_ne δ α (fun e => by subst e; exact h hy)) ls

theorem gSepD_congr (ι : Slots L) {ls : List SRec} {δ₁ δ₂ : LSubD L} :
    ∀ {Γ : Ctx VTy} {γ : List Val},
    (∀ s ∈ Γ, s.live = true → vD ι s.ty ls δ₁ = vD ι s.ty ls δ₂) →
    gSepD ι ls δ₁ Γ γ = gSepD ι ls δ₂ Γ γ := by
  intro Γ
  induction Γ with
  | nil => intro γ _; cases γ <;> rfl
  | cons s Γ' ih =>
      intro γ h
      cases γ with
      | nil => rfl
      | cons v γ' =>
          have htail : ∀ t ∈ Γ', t.live = true → vD ι t.ty ls δ₁ = vD ι t.ty ls δ₂ :=
            fun t ht => h t (List.mem_cons_of_mem _ ht)
          by_cases hl : s.live
          · simp only [gSepD, if_pos hl, ih htail, h s (List.mem_cons_self ..) hl]
          · simp only [gSepD, if_neg hl, ih htail]

theorem gDenD_iff (ι : Slots L) {ls : List SRec} {δ : LSubD L} {Γ : Ctx VTy} {γ : List Val}
    {ρ : WRes} : gDenD ι ls δ Γ γ ρ ↔ (Ctx.LiveWithin Γ γ ∧ gSepD ι ls δ Γ γ ρ) := pure_sep_iff

theorem gDenD_mk (ι : Slots L) {ls : List SRec} {δ : LSubD L} {Γ : Ctx VTy} {γ : List Val}
    {ρ : WRes} (hlen : Ctx.LiveWithin Γ γ) (hg : gSepD ι ls δ Γ γ ρ) : gDenD ι ls δ Γ γ ρ :=
  (gDenD_iff ι).mpr ⟨hlen, hg⟩

/-- A dead slot contributes nothing (`gDenC_dead_cons`). -/
theorem gDenD_dead_cons (ι : Slots L) {ls : List SRec} {δ : LSubD L} {Γ : Ctx VTy}
    {γ : List Val} {ρ : WRes} (A : VTy) (v : Val) (hg : gDenD ι ls δ Γ γ ρ) :
    gDenD ι ls δ (⟨A, false⟩ :: Γ) (v :: γ) ρ := by
  obtain ⟨hlen, hs⟩ := (gDenD_iff ι).mp hg
  exact gDenD_mk ι (by simpa using hlen) (by simpa [gSepD] using hs)

theorem substAll_cons' (v : Val) (γ : List Val) (e : Expr) :
    substAll (v :: γ) e = Expr.subst 0 v (Expr.psub 1 γ e) := by
  show Expr.psub 0 (v :: γ) e = _
  rw [Expr.psub_cons 0 v γ e, Val.shift_zero]

/-! ### `∀I` -/

/-- **`∀I` over `L`** (`allI_compatC`). -/
theorem allI_compatD (ι : Slots L) {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life}
    {M : Expr} {C : CTy} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : SemD (ℍ := ℍ) ι (Δ.extend x b) (⟨.unit, false⟩ :: Γ) M C) :
    SemD (ℍ := ℍ) ι Δ Γ (.val (.lam M)) (.all x b C) := by
  intro δ γ ls ρ hδ hg α ρ₁ ρ₂ hpure hcomp
  obtain ⟨rfl, β, hβ, hlt⟩ := hpure
  have hρ₂ : ρ₂ = ρ := eq_of_compS_empty_left (ResU.CompS.comm hcomp)
  subst ρ₂
  have hδ' : ModelsD (Δ.extend x b) (δ.extend x α) := by
    intro y u hy
    rw [LifeCtx.find?_extend] at hy
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl] at hy
      obtain rfl := Option.some.inj hy
      exact ⟨α, β, LSubD.find?_extend_self δ x α,
        by rw [interpD_extend_of_not_mentions hbx]; exact hβ, hlt⟩
    · rw [if_neg hxy] at hy
      obtain ⟨m, k, hm, hk, hlk⟩ := hδ y u hy
      exact ⟨m, k, by rw [LSubD.find?_extend_ne δ α hxy]; exact hm,
        by rw [interpD_extend_of_not_mentions (hΔx y u hy)]; exact hk, hlk⟩
  show cD ι C ls (δ.extend x α) (.app (.val (.lam (Expr.psub 1 γ M))) (.val .unit)) ρ
  refine cD_head ι C (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) rfl ls (δ.extend x α) ρ ?_
  rw [← substAll_cons']
  refine h (δ.extend x α) (Val.unit :: γ) ls ρ hδ' (gDenD_dead_cons ι _ _ ?_)
  obtain ⟨hlen, hgs⟩ := (gDenD_iff ι).mp hg
  refine gDenD_mk ι hlen ?_
  rw [gSepD_congr ι (δ₂ := δ) (fun s hs hl => vD_extend_of_not_free ι (hΓx s hs hl) ls δ α)]
  exact hgs

/-! ### Types up to the reading -/

mutual
/-- `S` at `δ` and `S'` at `δ'` are one value type (`TyEq` with `interpD`). -/
def TyEqD : VTy → LSubD L → VTy → LSubD L → Prop
  | .unit, _, .unit, _ => True
  | .zero, _, .zero, _ => True
  | .unk, _, .unk, _ => True
  | .int w, _, .int w', _ => w = w'
  | .opq k, _, .opq k', _ => k = k'
  | .tensor A B, δ, .tensor A' B', δ' => TyEqD A δ A' δ' ∧ TyEqD B δ B' δ'
  | .sum A B, δ, .sum A' B', δ' => TyEqD A δ A' δ' ∧ TyEqD B δ B' δ'
  | .thunk C, δ, .thunk C', δ' => CTyEqD C δ C' δ'
  | .ref A, δ, .ref A', δ' => TyEqD A δ A' δ'
  | .bang A, δ, .bang A', δ' => TyEqD A δ A' δ'
  | .box a A, δ, .box a' A', δ' => interpD δ a = interpD δ' a' ∧ TyEqD A δ A' δ'
  | .imm a A, δ, .imm a' A', δ' => interpD δ a = interpD δ' a' ∧ TyEqD A δ A' δ'
  | .mut a A, δ, .mut a' A', δ' => interpD δ a = interpD δ' a' ∧ TyEqD A δ A' δ'
  | .tvar n, _, .tvar n', _ => n = n'
  | .mu A, δ, .mu A', δ' => TyEqD A δ A' δ'
  | .fam A, δ, .fam A', δ' => TyEqD A δ A' δ'
  | _, _, _, _ => False
/-- `C` at `δ` and `C'` at `δ'` are one computation type (`CTyEq` with `interpD`). -/
def CTyEqD : CTy → LSubD L → CTy → LSubD L → Prop
  | .ret A, δ, .ret A', δ' => TyEqD A δ A' δ'
  | .arr A C, δ, .arr A' C', δ' => TyEqD A δ A' δ' ∧ CTyEqD C δ C' δ'
  | .amp C D, δ, .amp C' D', δ' => CTyEqD C δ C' δ' ∧ CTyEqD D δ D' δ'
  | .top, _, .top, _ => True
  | .all x b C, δ, .all x' b' C', δ' =>
      interpD δ b = interpD δ' b' ∧ ∀ α : L, CTyEqD C (δ.extend x α) C' (δ'.extend x' α)
  | .nu C, δ, .nu C', δ' => CTyEqD C δ C' δ'
  | .eff n i q A B C, δ, .eff n' i' q' A' B' C', δ' =>
      n = n' ∧ i = i' ∧ q = q' ∧ TyEqD A δ A' δ' ∧ TyEqD B δ B' δ' ∧ CTyEqD C δ C' δ'
  | _, _, _, _ => False
end

mutual
/-- `Δ-subst` at `TyEqD` (`TyEq.applyLSub`). -/
theorem TyEqD.applyLSub : ∀ (T : VTy) (σ : LSubst) (δ δ' : LSubD L),
    (∀ y, VFree y T → interpD δ ((Lifetime.Life.var y).applySub σ) = δ'.find? y) →
      TyEqD (T.applyLSub σ) δ T δ'
  | .unit, _, _, _, _ => trivial
  | .int _, _, _, _, _ => rfl
  | .opq _, _, _, _, _ => rfl
  | .zero, _, _, _, _ => trivial
  | .unk, _, _, _, _ => trivial
  | .ref T, σ, δ, δ', h => TyEqD.applyLSub T σ δ δ' h
  | .bang T, σ, δ, δ', h => TyEqD.applyLSub T σ δ δ' h
  | .fam T, σ, δ, δ', h => TyEqD.applyLSub T σ δ δ' h
  | .thunk C, σ, δ, δ', h => CTyEqD.applyLSub C σ δ δ' h
  | .sum T₁ T₂, σ, δ, δ', h =>
      ⟨TyEqD.applyLSub T₁ σ δ δ' (fun y hy => h y (Or.inl hy)),
       TyEqD.applyLSub T₂ σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .tensor T₁ T₂, σ, δ, δ', h =>
      ⟨TyEqD.applyLSub T₁ σ δ δ' (fun y hy => h y (Or.inl hy)),
       TyEqD.applyLSub T₂ σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .imm a T, σ, δ, δ', h =>
      ⟨interpD_applySub a (fun y hy => h y (Or.inl hy)),
       TyEqD.applyLSub T σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .mut a T, σ, δ, δ', h =>
      ⟨interpD_applySub a (fun y hy => h y (Or.inl hy)),
       TyEqD.applyLSub T σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .box a T, σ, δ, δ', h =>
      ⟨interpD_applySub a (fun y hy => h y (Or.inl hy)),
       TyEqD.applyLSub T σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .tvar _, _, _, _, _ => rfl
  | .mu T, σ, δ, δ', h => TyEqD.applyLSub T σ δ δ' h
/-- `Δ-subst` at `CTyEqD` (`CTyEq.applyLSub`), with its two branches at `∀`. -/
theorem CTyEqD.applyLSub : ∀ (C : CTy) (σ : LSubst) (δ δ' : LSubD L),
    (∀ y, CFree y C → interpD δ ((Lifetime.Life.var y).applySub σ) = δ'.find? y) →
      CTyEqD (C.applyLSub σ) δ C δ'
  | .ret A, σ, δ, δ', h => TyEqD.applyLSub A σ δ δ' h
  | .arr A C, σ, δ, δ', h =>
      ⟨TyEqD.applyLSub A σ δ δ' (fun y hy => h y (Or.inl hy)),
       CTyEqD.applyLSub C σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .amp C D, σ, δ, δ', h =>
      ⟨CTyEqD.applyLSub C σ δ δ' (fun y hy => h y (Or.inl hy)),
       CTyEqD.applyLSub D σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .top, _, _, _, _ => trivial
  | .nu C, σ, δ, δ', h => CTyEqD.applyLSub C σ δ δ' h
  | .eff _ _ _ A B C, σ, δ, δ', h =>
      ⟨rfl, rfl, rfl, TyEqD.applyLSub A σ δ δ' (fun y hy => h y (Or.inl hy)),
       TyEqD.applyLSub B σ δ δ' (fun y hy => h y (Or.inr (Or.inl hy))),
       CTyEqD.applyLSub C σ δ δ' (fun y hy => h y (Or.inr (Or.inr hy)))⟩
  | .all y b S, σ, δ, δ', h => by
      have hb : interpD δ (b.applySub σ) = interpD δ' b :=
        interpD_applySub b (fun w hw => h w (Or.inl hw))
      cases hcap : lsubCaptures (lsubDrop σ y) y with
      | false =>
          rw [CTy.applyLSub_all_not_captures hcap]
          refine ⟨hb, fun α => ?_⟩
          refine CTyEqD.applyLSub S _ _ _ (fun w hw => ?_)
          by_cases hwy : w = y
          · subst hwy
            rw [applySub_var_none (assocFind_lsubDrop_self w σ)]
            show (δ.extend w α).find? w = (δ'.extend w α).find? w
            rw [LSubD.find?_extend_self, LSubD.find?_extend_self]
          · have hvar : (Lifetime.Life.var w).applySub (lsubDrop σ y)
                = (Lifetime.Life.var w).applySub σ := by
              simp only [Lifetime.Life.applySub, assocFind_lsubDrop_ne hwy σ]
            have hcm : ((Lifetime.Life.var w).applySub σ).mentions y = false := by
              cases hf : Lifetime.assocFind w (lsubDrop σ y) with
              | none =>
                  rw [← hvar, applySub_var_none hf]
                  simp only [Lifetime.Life.mentions, beq_eq_false_iff_ne, ne_eq]
                  exact Ne.symm hwy
              | some d =>
                  rw [← hvar, applySub_var_some hf]
                  exact not_mentions_of_lsubCaptures hcap hf
            rw [hvar, interpD_extend_of_not_mentions hcm, h w (Or.inr ⟨hwy, hw⟩),
              LSubD.find?_extend_ne δ' α (Ne.symm hwy)]
      | true =>
          obtain ⟨z, hzy, hzr, hzS, hty⟩ :
              ∃ z, y < z ∧ lsubRangeBound (lsubDrop σ y) ≤ z ∧ S.lifeBound ≤ z ∧
                (CTy.all y b S).applyLSub σ
                  = CTy.all z (b.applySub σ)
                      (S.applyLSub ((y, Lifetime.Life.var z) :: lsubDrop σ y)) :=
            ⟨_, Nat.lt_of_lt_of_le (Nat.lt_succ_self y) (Nat.le_max_left _ _),
              Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
              Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _),
              CTy.applyLSub_all_captures hcap⟩
          rw [hty]
          refine ⟨hb, fun α => ?_⟩
          refine CTyEqD.applyLSub S _ _ _ (fun w hw => ?_)
          by_cases hwy : w = y
          · subst hwy
            rw [applySub_var_some
              (show Lifetime.assocFind w ((w, Lifetime.Life.var z) :: lsubDrop σ w)
                  = some (Lifetime.Life.var z) from by simp [Lifetime.assocFind])]
            show (δ.extend z α).find? z = (δ'.extend w α).find? w
            rw [LSubD.find?_extend_self, LSubD.find?_extend_self]
          · have hvar : (Lifetime.Life.var w).applySub
                  ((y, Lifetime.Life.var z) :: lsubDrop σ y)
                = (Lifetime.Life.var w).applySub σ := by
              simp only [Lifetime.Life.applySub, Lifetime.assocFind,
                if_neg (Ne.symm hwy), assocFind_lsubDrop_ne hwy σ]
            have hcm : ((Lifetime.Life.var w).applySub σ).mentions z = false := by
              cases hf : Lifetime.assocFind w (lsubDrop σ y) with
              | none =>
                  have hfσ : Lifetime.assocFind w σ = none := by
                    rw [← assocFind_lsubDrop_ne hwy σ]; exact hf
                  rw [applySub_var_none hfσ]
                  exact not_mentions_of_varBound_le
                    (Nat.lt_of_lt_of_le (lt_cLifeBound hw) hzS)
              | some d =>
                  have hfσ : Lifetime.assocFind w σ = some d := by
                    rw [← assocFind_lsubDrop_ne hwy σ]; exact hf
                  rw [applySub_var_some hfσ]
                  exact not_mentions_of_varBound_le
                    (Nat.le_trans (varBound_le_lsubRangeBound hf) hzr)
            rw [hvar, interpD_extend_of_not_mentions hcm, h w (Or.inr ⟨hwy, hw⟩),
              LSubD.find?_extend_ne δ' α (Ne.symm hwy)]
end

/-- The substitution `[@a/'x]` at `δ` is `δ['x↦@aδ]`, variable by variable (`instLife_var`). -/
theorem instLifeD_var (x : LifeVar) (a : Lifetime.Life) {δ : LSubD L} {α : L}
    (ha : interpD δ a = some α) (y : LifeVar) :
    interpD δ ((Lifetime.Life.var y).applySub [(x, a)]) = (δ.extend x α).find? y := by
  by_cases hxy : x = y
  · subst hxy
    rw [applySub_var_some
      (show Lifetime.assocFind x [(x, a)] = some a from by simp [Lifetime.assocFind])]
    rw [ha, LSubD.find?_extend_self]
  · rw [applySub_var_none
      (show Lifetime.assocFind y [(x, a)] = none from by
        simp only [Lifetime.assocFind, if_neg hxy])]
    show δ.find? y = _
    rw [LSubD.find?_extend_ne δ α hxy]

/-- `C[@a/'x]` at `δ` is `C` at `δ['x↦@aδ]` (`CTyEq.instLife`). -/
theorem CTyEqD.instLife (x : LifeVar) (a : Lifetime.Life) (C : CTy) {δ : LSubD L} {α : L}
    (ha : interpD δ a = some α) : CTyEqD (CTy.instLife x a C) δ C (δ.extend x α) :=
  CTyEqD.applyLSub C [(x, a)] δ (δ.extend x α) (fun y _ => instLifeD_var x a ha y)

/-- `𝒱⟦S⟧` reads a type only up to `TyEqD` (`vC_tyEq`). -/
theorem vD_tyEq (ι : Slots L) : ∀ (A A' : VTy) (δ δ' : LSubD L), TyEqD A δ A' δ' →
    ∀ ls, vD ι A ls δ = vD ι A' ls δ' := by
  intro A
  induction A using VTy.recV with
  | unit => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | box a A ih =>
      intro A' δ δ' h ls
      cases A' <;> simp only [TyEqD] at h
      rename_i a' A'
      funext v
      show atLifeD δ a (fun α => boxD ι α (vD ι A ls δ v)) =
        atLifeD δ' a' (fun α => boxD ι α (vD ι A' ls δ' v))
      rw [ih A' δ δ' h.2 ls, atLifeD_congr h.1]
  | «mut» a A ih =>
      intro A' δ δ' h ls
      cases A' <;> simp only [TyEqD] at h
      rename_i a' A'
      funext v
      show atLifeD δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutD ι ℓ α ls (fun ls₀ => vD ι A ls₀ δ)) =
        atLifeD δ' a' (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutD ι ℓ α ls (fun ls₀ => vD ι A' ls₀ δ'))
      simp only [ih A' δ δ' h.2]
      rw [atLifeD_congr h.1]
  | tensor A B _ _ => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | zero => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | sum A B _ _ => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | thunk C => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | ref A _ => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | imm a A _ => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | bang A _ => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | unk => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | tvar n => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | mu A _ => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | int w => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | fam L _ => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl
  | opq k => intro A' δ δ' h ls; cases A' <;> simp only [TyEqD] at h; rfl

/-- `𝒞⟦C⟧` reads a type only up to `CTyEqD` (`cC_tyEq`). -/
theorem cD_tyEq (ι : Slots L) : ∀ (C C' : CTy) (δ δ' : LSubD L), CTyEqD C δ C' δ' →
    ∀ ls e, cD (ℍ := ℍ) ι C ls δ e = cD (ℍ := ℍ) ι C' ls δ' e
  | .ret A, C', δ, δ', h, ls, e => by
      cases C' <;> simp only [CTyEqD] at h
      rename_i A'
      show wpTS ls e (fun ls'' => vD ι A ls'' δ) = wpTS ls e (fun ls'' => vD ι A' ls'' δ')
      simp only [vD_tyEq ι A A' δ δ' h]
  | .arr A C, C', δ, δ', h, ls, e => by
      cases C' <;> simp only [CTyEqD] at h
      rename_i A' C'
      funext ρ
      show (∀ v, (vD ι A ls δ v ─⋆ cD ι C ls δ (.app e (.val v))) ρ) =
        (∀ v, (vD ι A' ls δ' v ─⋆ cD ι C' ls δ' (.app e (.val v))) ρ)
      simp only [vD_tyEq ι A A' δ δ' h.1, cD_tyEq ι C C' δ δ' h.2]
  | .top, C', δ, δ', h, ls, e => by cases C' <;> simp only [CTyEqD] at h; rfl
  | .all x b C, C', δ, δ', h, ls, e => by
      cases C' <;> simp only [CTyEqD] at h
      rename_i x' b' C'
      funext ρ
      show (∀ α : L, (⌜LtLifeD δ b α⌝ ─⋆ cD ι C ls (δ.extend x α) (.app e (.val .unit))) ρ) =
        (∀ α : L, (⌜LtLifeD δ' b' α⌝ ─⋆ cD ι C' ls (δ'.extend x' α) (.app e (.val .unit))) ρ)
      simp only [LtLifeD, h.1, cD_tyEq ι C C' _ _ (h.2 _)]
  | .amp C D, C', δ, δ', h, ls, e => by cases C' <;> simp only [CTyEqD] at h; rfl
  | .nu C, C', δ, δ', h, ls, e => by cases C' <;> simp only [CTyEqD] at h; rfl
  | .eff _ _ _ _ _ _, C', δ, δ', h, ls, e => by cases C' <;> simp only [CTyEqD] at h; rfl

/-! ### The typing's lifetime premise, read in `L` -/

/-- How many of the lifetimes `S` lie strictly above `x`, as a lifetime of `ℕᵒᵈ`. -/
def rankIn (S : Finset L) (x : L) : Life := OrderDual.toDual (S.filter (fun s => x < s)).card

omit [OrderTop L] in
theorem rankIn_mono (S : Finset L) : Monotone (rankIn S) := by
  intro x y hxy
  show (S.filter (fun s => y < s)).card ≤ (S.filter (fun s => x < s)).card
  refine Finset.card_le_card ?_
  intro s hs
  simp only [Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, lt_of_le_of_lt hxy hs.2⟩

theorem rankIn_top (S : Finset L) : rankIn S ⊤ = ⊤ := by
  show OrderDual.toDual (S.filter (fun s => (⊤ : L) < s)).card = OrderDual.toDual 0
  congr 1
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun s _ => not_lt.mpr le_top

omit [OrderTop L] in
theorem rankIn_strict (S : Finset L) {x y : L} (hy : y ∈ S) (h : x < y) :
    rankIn S x < rankIn S y := by
  show (S.filter (fun s => y < s)).card < (S.filter (fun s => x < s)).card
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_filter] at hs ⊢
    exact ⟨hs.1, lt_trans h hs.2⟩
  intro hsub
  have := hsub (Finset.mem_filter.mpr ⟨hy, h⟩)
  exact lt_irrefl _ (Finset.mem_filter.mp this).2

/-- The values a reading takes, and `⊤`. -/
def valsD (δ : LSubD L) : Finset L := insert ⊤ (δ.entries.map Prod.snd).toFinset

theorem find?_mem_valsD (δ : LSubD L) {x : LifeVar} {v : L} (h : δ.find? x = some v) :
    v ∈ valsD δ := by
  have : ∀ es : List (LifeVar × L), Lifetime.assocFind x es = some v → v ∈ es.map Prod.snd := by
    intro es
    induction es with
    | nil => intro h; simp [Lifetime.assocFind] at h
    | cons p t ih =>
        intro h
        obtain ⟨y, w⟩ := p
        simp only [Lifetime.assocFind] at h
        split_ifs at h with hy
        · cases h; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h)
  exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (this _ h))

/-- `@aδ` is one of the reading's values or `⊤`. -/
theorem interpD_mem_valsD (δ : LSubD L) : ∀ (a : Lifetime.Life) {v : L},
    interpD δ a = some v → v ∈ valsD δ := by
  intro a
  induction a with
  | var y => intro v h; exact find?_mem_valsD δ h
  | top => intro v h; cases h; exact Finset.mem_insert_self _ _
  | join p q ihp ihq =>
      intro v h
      simp only [interpD] at h
      cases hp : interpD δ p with
      | none => simp [hp] at h
      | some m =>
          cases hq : interpD δ q with
          | none => simp [hp, hq] at h
          | some n =>
              simp only [hp, hq, Option.bind_some, Option.some.injEq] at h
              subst h
              rcases le_total m n with hle | hle
              · rw [max_eq_right hle]; exact ihq hq
              · rw [max_eq_left hle]; exact ihp hp
  | meet p q ihp ihq =>
      intro v h
      simp only [interpD] at h
      cases hp : interpD δ p with
      | none => simp [hp] at h
      | some m =>
          cases hq : interpD δ q with
          | none => simp [hp, hq] at h
          | some n =>
              simp only [hp, hq, Option.bind_some, Option.some.injEq] at h
              subst h
              rcases le_total m n with hle | hle
              · rw [min_eq_left hle]; exact ihp hp
              · rw [min_eq_right hle]; exact ihq hq

/-- **Core's `Δ ⊨ @a ⊏ @b` holds over every lifetime order `L`.** A reading over `L` is re-read
in `ℕᵒᵈ` by rank among its finitely many values; the rank keeps `⊤`, `⊔`, `⊓`, and the strict
order on those values, so a counter-reading over `L` would be one over `ℕ`. -/
theorem entailsLtD_of_entailsLt {Δ : LifeCtx} {a b : Lifetime.Life} (h : Δ.EntailsLt a b) :
    EntailsLtD L Δ a b := by
  intro δ hδ
  set f := rankIn (valsD δ) with hf
  have hfm : Monotone f := rankIn_mono _
  have hft : f ⊤ = ⊤ := rankIn_top _
  have hint : ∀ c : Lifetime.Life,
      c.interp (toLSub (δ.map f)) = (interpD δ c).map (fun v => OrderDual.ofDual (f v)) := by
    intro c
    rw [interp_toLSub, interpD_map hfm hft]
    cases interpD δ c <;> rfl
  have hmod : Δ.Models (toLSub (δ.map f)) := by
    intro x u hu
    obtain ⟨m, n, hm, hn, hlt⟩ := hδ x u hu
    refine ⟨OrderDual.ofDual (f m), OrderDual.ofDual (f n), ?_, ?_, ?_⟩
    · rw [toLSub_find?, LSubD.find?_map, hm]; rfl
    · rw [hint, hn]; rfl
    · exact rankIn_strict _ (interpD_mem_valsD δ u hn) hlt
  obtain ⟨m, n, hm, hn, hlt⟩ := h _ hmod
  rw [hint] at hm hn
  obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.mp hm
  obtain ⟨n', hn', rfl⟩ := Option.map_eq_some_iff.mp hn
  refine ⟨m', n', hm', hn', ?_⟩
  by_contra hle
  have : f n' ≤ f m' := hfm (not_lt.mp hle)
  exact absurd hlt (not_lt.mpr this)

/-- `Δ ⊨ @a ⊑ @b` over `L` (`LifeCtx.EntailsLe` over `L`). -/
def EntailsLeD (L : Type) [LinearOrder L] [OrderTop L] (Δ : LifeCtx) (a b : Lifetime.Life) :
    Prop :=
  ∀ δ : LSubD L, ModelsD Δ δ → ∃ m n, interpD δ a = some m ∧ interpD δ b = some n ∧ m ≤ n

/-- **Core's `Δ ⊨ @a ⊑ @b` holds over every lifetime order `L`**, by the same re-reading. -/
theorem entailsLeD_of_entailsLe {Δ : LifeCtx} {a b : Lifetime.Life} (h : Δ.EntailsLe a b) :
    EntailsLeD L Δ a b := by
  intro δ hδ
  set f := rankIn (valsD δ) with hf
  have hfm : Monotone f := rankIn_mono _
  have hft : f ⊤ = ⊤ := rankIn_top _
  have hint : ∀ c : Lifetime.Life,
      c.interp (toLSub (δ.map f)) = (interpD δ c).map (fun v => OrderDual.ofDual (f v)) := by
    intro c
    rw [interp_toLSub, interpD_map hfm hft]
    cases interpD δ c <;> rfl
  have hmod : Δ.Models (toLSub (δ.map f)) := by
    intro x u hu
    obtain ⟨m, n, hm, hn, hlt⟩ := hδ x u hu
    refine ⟨OrderDual.ofDual (f m), OrderDual.ofDual (f n), ?_, ?_, ?_⟩
    · rw [toLSub_find?, LSubD.find?_map, hm]; rfl
    · rw [hint, hn]; rfl
    · exact rankIn_strict _ (interpD_mem_valsD δ u hn) hlt
  obtain ⟨m, n, hm, hn, hle⟩ := h _ hmod
  rw [hint] at hm hn
  obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.mp hm
  obtain ⟨n', hn', rfl⟩ := Option.map_eq_some_iff.mp hn
  refine ⟨m', n', hm', hn', ?_⟩
  by_contra hlt
  have : f n' < f m' := rankIn_strict _ (interpD_mem_valsD δ a hm') (not_le.mp hlt)
  exact absurd hle (not_le.mpr this)

/-! ### `∀E` -/

/-- **`∀E` over `L`** (`allE_compatC`), at Core's own premise `Δ ⊨ @a ⊏ @b`. -/
theorem allE_compatD (ι : Slots L) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {x : LifeVar}
    {b a : Lifetime.Life} {C : CTy} (h : SemD (ℍ := ℍ) ι Δ Γ M (.all x b C))
    (hlt : Δ.EntailsLt a b) : SemD (ℍ := ℍ) ι Δ Γ (.app M (.val .unit)) (C.instLife x a) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, β, ha, hb, hab⟩ := entailsLtD_of_entailsLt (L := L) hlt δ hδ
  have he : substAll γ (.app M (.val .unit)) = .app (substAll γ M) (.val .unit) := by
    show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ (.val .unit)) = _
    simp [Expr.psub, substAll]
  rw [he, cD_tyEq ι _ _ _ _ (CTyEqD.instLife x a C ha) ls]
  exact h δ γ ls ρ hδ hg α PMap.empty ρ ⟨rfl, β, hb, hab⟩ (ResU.comp_empty_right ρ)

end DenseCarrier

end
