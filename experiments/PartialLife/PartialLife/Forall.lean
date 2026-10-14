import PartialLife.Relation
import Core.Compat
import Support.Statics.Presupposed

/-!
# PartialLife — the `∀` rules of the fundamental property over a partial order

`Core/Compat.lean`'s `allI_compatC` and `allE_compatC`, proved again over the relation of
`Relation.lean`, with the lifetimes read in a partial order `L` with a top. The proofs are
`DenseCarrier/FL.lean`'s, which were Core's step for step; none of them compares two lifetimes:

* `allI_compatP`: `Λ. M : ∀'x ⊏ @b. C` from `M : C` at `Δ, 'x ⊏ @b`: the β-step (`cP_head`),
  `δ['x ↦ α] ∈ ⟦Δ, 'x ⊏ @b⟧`, and the context's relation unchanged at `δ['x ↦ α]`
  (`vP_extend_of_not_free`).
* `allE_compatP`: `M [] : C[@a/'x]` from `M : ∀'x ⊏ @b. C` and `Δ ⊨ @a ⊏ @b` **read on `L`**
  (`EntailsLtP`): the clause at `α = @aδ`, and `C[@a/'x]` at `δ` is `C` at `δ['x ↦ @aδ]`
  (`CTyEqP.instLife`, through `cP_tyEq`). Core's premise is entailment over `ℕ`, a chain;
  `DenseCarrier` carried it to a chain `L` (`entailsLtD_of_entailsLt`), and on a partial order it
  does not carry (`Statics.lean`), so the premise is taken on `L`.

The relation is `False` outside the fragment (`FragV`, `FragC`), so these lemmas are statements
about Core's rules only when every type in them is in the fragment.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace PartialLife
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont Step1N)
open BoCa.Lifetime (LifeVar LifeCtx LSubst)
open DenseCarrier (LSubD)

variable {L : Type} [PartialOrder L] [OrderTop L]

/-! ### The reading of a term, up to the variables it mentions -/

theorem interpP_congr {δ₁ δ₂ : LSubD L} : ∀ (a : Lifetime.Life),
    (∀ x, a.mentions x = true → δ₁.find? x = δ₂.find? x) → interpP δ₁ a = interpP δ₂ a := by
  intro a
  induction a with
  | var y => intro h; exact h y (by simp [Lifetime.Life.mentions])
  | top => intro _; rfl
  | join p q ihp ihq =>
      intro h
      simp only [interpP,
        ihp (fun x hx => h x (by simp [Lifetime.Life.mentions, hx])),
        ihq (fun x hx => h x (by simp [Lifetime.Life.mentions, hx]))]
  | meet p q ihp ihq =>
      intro h
      simp only [interpP,
        ihp (fun x hx => h x (by simp [Lifetime.Life.mentions, hx])),
        ihq (fun x hx => h x (by simp [Lifetime.Life.mentions, hx]))]

theorem interpP_extend_of_not_mentions {δ : LSubD L} {z : LifeVar} {α : L}
    {c : Lifetime.Life} (h : c.mentions z = false) :
    interpP (δ.extend z α) c = interpP δ c := by
  refine interpP_congr c (fun w hw => ?_)
  by_cases hzw : z = w
  · subst hzw; simp [h] at hw
  · exact LSubD.find?_extend_ne δ α hzw

/-- `@(a[σ])δ = @a δ′` whenever `δ′` reads each variable of `@a` the way `δ` reads what `σ` sends
it to. -/
theorem interpP_applySub {σ : LSubst} {δ δ' : LSubD L} : ∀ (c : Lifetime.Life),
    (∀ y, c.mentions y = true → interpP δ ((Lifetime.Life.var y).applySub σ) = δ'.find? y) →
      interpP δ (c.applySub σ) = interpP δ' c := by
  intro c
  induction c with
  | var y => intro h; exact h y (by simp [Lifetime.Life.mentions])
  | top => intro _; rfl
  | join p q ihp ihq =>
      intro h
      simp only [Lifetime.Life.applySub, interpP,
        ihp (fun y hy => h y (by simp [Lifetime.Life.mentions, hy])),
        ihq (fun y hy => h y (by simp [Lifetime.Life.mentions, hy]))]
  | meet p q ihp ihq =>
      intro h
      simp only [Lifetime.Life.applySub, interpP,
        ihp (fun y hy => h y (by simp [Lifetime.Life.mentions, hy])),
        ihq (fun y hy => h y (by simp [Lifetime.Life.mentions, hy]))]

/-! ### Head expansion -/

/-- `𝒞⟦C⟧` is closed under a pure step in front (`cC_step`). -/
theorem cP_step (ι : Reading L) : ∀ (C : CTy) {e e' : Expr}, (∀ μ : Heap, Step1N (ℍ := ℍ) μ e μ e') →
    ∀ (ls : List SRec) (δ : LSubD L), Entails (cP (ℍ := ℍ) ι C ls δ e') (cP (ℍ := ℍ) ι C ls δ e)
  | .ret _, _, _, h, ls, _ => wpTS_step h ls _
  | .arr _ C, _, _, h, ls, δ => fun _ h' v ρ₁ ρ₂ hv hc =>
      cP_step ι C (fun μ => (h μ).plug (Kont.appL .hole v)) ls δ _ (h' v ρ₁ ρ₂ hv hc)
  | .top, _, _, _, _, _ => fun _ _ => trivial
  | .all x _ C, _, _, h, ls, δ => fun _ h' α ρ₁ ρ₂ hp hc =>
      cP_step ι C (fun μ => (h μ).plug (Kont.appL .hole _)) ls (δ.extend x α) _
        (h' α ρ₁ ρ₂ hp hc)
  | .amp _ _, _, _, _, _, _ | .nu _, _, _, _, _, _ | .eff _ _ _ _ _ _ _, _, _, _, _, _ =>
      fun _ h => h

/-- One head step in front of `𝒞⟦C⟧` (`cC_head`). -/
theorem cP_head (ι : Reading L) (C : CTy) {e e' : Expr} (h : ∀ μ : Heap, Head (ℍ := ℍ) μ e μ e')
    (hn : e.allocs = false) (ls : List SRec) (δ : LSubD L) :
    Entails (cP (ℍ := ℍ) ι C ls δ e') (cP (ℍ := ℍ) ι C ls δ e) :=
  cP_step ι C (fun μ => Step1N.head (h μ) hn) ls δ

/-! ### The context -/

theorem atLifeP_congr {δ₁ δ₂ : LSubD L} {a a' : Lifetime.Life} (h : interpP δ₁ a = interpP δ₂ a') :
    atLifeP δ₁ a = atLifeP δ₂ a' := by
  funext F ρ
  unfold atLifeP
  rw [h]

mutual
/-- `𝒱⟦A⟧` reads `δ` only at the variables free in `A` (`vC_congr`). -/
theorem vP_congr (ι : Reading L) : ∀ (A : VTy) {δ₁ δ₂ : LSubD L},
    (∀ y, VFree y A → δ₁.find? y = δ₂.find? y) → ∀ ls, vP (ℍ := ℍ) ι A ls δ₁ = vP (ℍ := ℍ) ι A ls δ₂
  | .unit, _, _, _, _ => rfl
  | .tensor A B, δ₁, δ₂, h, ls => by
      funext v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vP (ℍ := ℍ) ι A ls δ₁ v₁ ⋆ vP (ℍ := ℍ) ι B ls δ₁ v₂) =
        (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vP (ℍ := ℍ) ι A ls δ₂ v₁ ⋆ vP (ℍ := ℍ) ι B ls δ₂ v₂)
      simp only [vP_congr ι A (fun y hy => h y (Or.inl hy)) ls,
        vP_congr ι B (fun y hy => h y (Or.inr hy)) ls]
  | .thunk C, δ₁, δ₂, h, ls => by
      funext v ρ
      show (∀ ls', Ext ls ls' ρ → cP (ℍ := ℍ) ι C ls' δ₁ (forceE C (.val v)) ρ) =
        (∀ ls', Ext ls ls' ρ → cP (ℍ := ℍ) ι C ls' δ₂ (forceE C (.val v)) ρ)
      simp only [cP_congr ι C h]
  | .ref A, δ₁, δ₂, h, ls => by
      funext v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vP (ℍ := ℍ) ι A ls δ₁ v') =
        (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vP (ℍ := ℍ) ι A ls δ₂ v')
      simp only [vP_congr ι A h ls]
  | .box a A, δ₁, δ₂, h, ls => by
      funext v
      show atLifeP δ₁ a (fun α => boxP ι α (vP (ℍ := ℍ) ι A ls δ₁ v)) =
        atLifeP δ₂ a (fun α => boxP ι α (vP (ℍ := ℍ) ι A ls δ₂ v))
      have ha : interpP δ₁ a = interpP δ₂ a := interpP_congr a (fun y hy => h y (Or.inl hy))
      rw [vP_congr ι A (fun y hy => h y (Or.inr hy)) ls, atLifeP_congr ha]
  | .mut a A, δ₁, δ₂, h, ls => by
      funext v
      show atLifeP δ₁ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutP ι ℓ α ls (fun ls₀ => vP (ℍ := ℍ) ι A ls₀ δ₁)) =
        atLifeP δ₂ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutP ι ℓ α ls (fun ls₀ => vP (ℍ := ℍ) ι A ls₀ δ₂))
      have ha : interpP δ₁ a = interpP δ₂ a := interpP_congr a (fun y hy => h y (Or.inl hy))
      simp only [vP_congr ι A (fun y hy => h y (Or.inr hy))]
      rw [atLifeP_congr ha]
  | .zero, _, _, _, _ | .sum _ _, _, _, _, _ | .imm _ _, _, _, _, _ | .bang _, _, _, _, _
  | .unk, _, _, _, _ | .tvar _, _, _, _, _ | .mu _, _, _, _, _ | .int _, _, _, _, _
  | .fam _, _, _, _, _ | .opq _, _, _, _, _ => rfl

/-- `𝒞⟦C⟧` reads `δ` only at the variables free in `C`. -/
theorem cP_congr (ι : Reading L) : ∀ (C : CTy) {δ₁ δ₂ : LSubD L},
    (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) →
      ∀ ls e, cP (ℍ := ℍ) ι C ls δ₁ e = cP (ℍ := ℍ) ι C ls δ₂ e
  | .ret A, δ₁, δ₂, h, ls, e => by
      show wpTS ls e (fun ls'' => vP (ℍ := ℍ) ι A ls'' δ₁) =
        wpTS ls e (fun ls'' => vP (ℍ := ℍ) ι A ls'' δ₂)
      simp only [vP_congr ι A h]
  | .arr A C, δ₁, δ₂, h, ls, e => by
      funext ρ
      show (∀ v, (vP (ℍ := ℍ) ι A ls δ₁ v ─⋆ cP (ℍ := ℍ) ι C ls δ₁ (.app e (.val v))) ρ) =
        (∀ v, (vP (ℍ := ℍ) ι A ls δ₂ v ─⋆ cP (ℍ := ℍ) ι C ls δ₂ (.app e (.val v))) ρ)
      simp only [vP_congr ι A (fun y hy => h y (Or.inl hy)),
        cP_congr ι C (fun y hy => h y (Or.inr hy))]
  | .top, _, _, _, _, _ => rfl
  | .all x c C, δ₁, δ₂, h, ls, e => by
      funext ρ
      show (∀ α : L, (⌜LtLifeP δ₁ c α⌝ ─⋆
          cP (ℍ := ℍ) ι C ls (δ₁.extend x α) (.app e (.val .unit))) ρ) =
        (∀ α : L, (⌜LtLifeP δ₂ c α⌝ ─⋆
          cP (ℍ := ℍ) ι C ls (δ₂.extend x α) (.app e (.val .unit))) ρ)
      have hc : interpP δ₁ c = interpP δ₂ c := interpP_congr c (fun y hy => h y (Or.inl hy))
      have hC : ∀ α : L, cP (ℍ := ℍ) ι C ls (δ₁.extend x α) (.app e (.val .unit)) =
          cP (ℍ := ℍ) ι C ls (δ₂.extend x α) (.app e (.val .unit)) := by
        intro α
        refine cP_congr ι C (fun y hy => ?_) ls _
        by_cases hxy : x = y
        · subst hxy; rw [LSubD.find?_extend_self, LSubD.find?_extend_self]
        · rw [LSubD.find?_extend_ne δ₁ α hxy, LSubD.find?_extend_ne δ₂ α hxy]
          exact h y (Or.inr ⟨Ne.symm hxy, hy⟩)
      simp only [LtLifeP, hc, hC]
  | .amp _ _, _, _, _, _, _ | .nu _, _, _, _, _, _ | .eff _ _ _ _ _ _ _, _, _, _, _, _ => rfl
end

theorem vP_extend_of_not_free (ι : Reading L) {x : LifeVar} {T : VTy} (h : ¬ VFree x T)
    (ls : List SRec) (δ : LSubD L) (α : L) : vP ι T ls (δ.extend x α) = vP ι T ls δ :=
  vP_congr ι T (fun y hy => LSubD.find?_extend_ne δ α (fun e => by subst e; exact h hy)) ls

theorem gSepP_congr (ι : Reading L) {ls : List SRec} {δ₁ δ₂ : LSubD L} :
    ∀ {Γ : Ctx VTy} {γ : List Val},
    (∀ s ∈ Γ, s.live = true → vP ι s.ty ls δ₁ = vP ι s.ty ls δ₂) →
    gSepP ι ls δ₁ Γ γ = gSepP ι ls δ₂ Γ γ := by
  intro Γ
  induction Γ with
  | nil => intro γ _; cases γ <;> rfl
  | cons s Γ' ih =>
      intro γ h
      cases γ with
      | nil => rfl
      | cons v γ' =>
          have htail : ∀ t ∈ Γ', t.live = true → vP ι t.ty ls δ₁ = vP ι t.ty ls δ₂ :=
            fun t ht => h t (List.mem_cons_of_mem _ ht)
          by_cases hl : s.live
          · simp only [gSepP, if_pos hl, ih htail, h s (List.mem_cons_self ..) hl]
          · simp only [gSepP, if_neg hl, ih htail]

theorem gDenP_iff (ι : Reading L) {ls : List SRec} {δ : LSubD L} {Γ : Ctx VTy} {γ : List Val}
    {ρ : WRes} : gDenP ι ls δ Γ γ ρ ↔ (Ctx.LiveWithin Γ γ ∧ gSepP ι ls δ Γ γ ρ) := pure_sep_iff

theorem gDenP_mk (ι : Reading L) {ls : List SRec} {δ : LSubD L} {Γ : Ctx VTy} {γ : List Val}
    {ρ : WRes} (hlen : Ctx.LiveWithin Γ γ) (hg : gSepP ι ls δ Γ γ ρ) : gDenP ι ls δ Γ γ ρ :=
  (gDenP_iff ι).mpr ⟨hlen, hg⟩

/-- A dead slot contributes nothing (`gDenC_dead_cons`). -/
theorem gDenP_dead_cons (ι : Reading L) {ls : List SRec} {δ : LSubD L} {Γ : Ctx VTy}
    {γ : List Val} {ρ : WRes} (A : VTy) (v : Val) (hg : gDenP ι ls δ Γ γ ρ) :
    gDenP ι ls δ (⟨A, false⟩ :: Γ) (v :: γ) ρ := by
  obtain ⟨hlen, hs⟩ := (gDenP_iff ι).mp hg
  exact gDenP_mk ι (by simpa using hlen) (by simpa [gSepP] using hs)

theorem substAll_cons' (v : Val) (γ : List Val) (e : Expr) :
    substAll (v :: γ) e = Expr.subst 0 v (Expr.psub 1 γ e) := by
  show Expr.psub 0 (v :: γ) e = _
  rw [Expr.psub_cons 0 v γ e, Val.shift_zero]

/-! ### `∀I` -/

/-- **`∀I` over a partial order** (`allI_compatC`). -/
theorem allI_compatP (ι : Reading L) {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life}
    {M : Expr} {C : CTy} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : SemP (ℍ := ℍ) ι (Δ.extend x b) (⟨.unit, false⟩ :: Γ) M C) :
    SemP (ℍ := ℍ) ι Δ Γ (.val (.lam M)) (.all x b C) := by
  intro δ γ ls ρ hδ hg α ρ₁ ρ₂ hpure hcomp
  obtain ⟨rfl, β, hβ, hlt⟩ := hpure
  have hρ₂ : ρ₂ = ρ := eq_of_compS_empty_left (ResU.CompS.comm hcomp)
  subst ρ₂
  have hδ' : ModelsP (Δ.extend x b) (δ.extend x α) := by
    intro y u hy
    rw [LifeCtx.find?_extend] at hy
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl] at hy
      obtain rfl := Option.some.inj hy
      exact ⟨α, β, LSubD.find?_extend_self δ x α,
        by rw [interpP_extend_of_not_mentions hbx]; exact hβ, hlt⟩
    · rw [if_neg hxy] at hy
      obtain ⟨m, k, hm, hk, hlk⟩ := hδ y u hy
      exact ⟨m, k, by rw [LSubD.find?_extend_ne δ α hxy]; exact hm,
        by rw [interpP_extend_of_not_mentions (hΔx y u hy)]; exact hk, hlk⟩
  show cP ι C ls (δ.extend x α) (.app (.val (.lam (Expr.psub 1 γ M))) (.val .unit)) ρ
  refine cP_head ι C (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) rfl ls (δ.extend x α) ρ ?_
  rw [← substAll_cons']
  refine h (δ.extend x α) (Val.unit :: γ) ls ρ hδ' (gDenP_dead_cons ι _ _ ?_)
  obtain ⟨hlen, hgs⟩ := (gDenP_iff ι).mp hg
  refine gDenP_mk ι hlen ?_
  rw [gSepP_congr ι (δ₂ := δ) (fun s hs hl => vP_extend_of_not_free ι (hΓx s hs hl) ls δ α)]
  exact hgs

/-! ### Types up to the reading -/

mutual
/-- `S` at `δ` and `S'` at `δ'` are one value type (`TyEq` with `interpP`). -/
def TyEqP : VTy → LSubD L → VTy → LSubD L → Prop
  | .unit, _, .unit, _ => True
  | .zero, _, .zero, _ => True
  | .unk, _, .unk, _ => True
  | .int w, _, .int w', _ => w = w'
  | .opq k, _, .opq k', _ => k = k'
  | .tensor A B, δ, .tensor A' B', δ' => TyEqP A δ A' δ' ∧ TyEqP B δ B' δ'
  | .sum A B, δ, .sum A' B', δ' => TyEqP A δ A' δ' ∧ TyEqP B δ B' δ'
  | .thunk C, δ, .thunk C', δ' => CTyEqP C δ C' δ'
  | .ref A, δ, .ref A', δ' => TyEqP A δ A' δ'
  | .bang A, δ, .bang A', δ' => TyEqP A δ A' δ'
  | .box a A, δ, .box a' A', δ' => interpP δ a = interpP δ' a' ∧ TyEqP A δ A' δ'
  | .imm a A, δ, .imm a' A', δ' => interpP δ a = interpP δ' a' ∧ TyEqP A δ A' δ'
  | .mut a A, δ, .mut a' A', δ' => interpP δ a = interpP δ' a' ∧ TyEqP A δ A' δ'
  | .tvar n, _, .tvar n', _ => n = n'
  | .mu A, δ, .mu A', δ' => TyEqP A δ A' δ'
  | .fam A, δ, .fam A', δ' => TyEqP A δ A' δ'
  | _, _, _, _ => False
/-- `C` at `δ` and `C'` at `δ'` are one computation type (`CTyEq` with `interpP`). -/
def CTyEqP : CTy → LSubD L → CTy → LSubD L → Prop
  | .ret A, δ, .ret A', δ' => TyEqP A δ A' δ'
  | .arr A C, δ, .arr A' C', δ' => TyEqP A δ A' δ' ∧ CTyEqP C δ C' δ'
  | .amp C D, δ, .amp C' D', δ' => CTyEqP C δ C' δ' ∧ CTyEqP D δ D' δ'
  | .top, _, .top, _ => True
  | .all x b C, δ, .all x' b' C', δ' =>
      interpP δ b = interpP δ' b' ∧ ∀ α : L, CTyEqP C (δ.extend x α) C' (δ'.extend x' α)
  | .nu C, δ, .nu C', δ' => CTyEqP C δ C' δ'
  | .eff n i q A B fin C, δ, .eff n' i' q' A' B' fin' C', δ' =>
      n = n' ∧ i = i' ∧ q = q' ∧ TyEqP A δ A' δ' ∧ TyEqP B δ B' δ' ∧ CTyEqP fin δ fin' δ' ∧
        CTyEqP C δ C' δ'
  | _, _, _, _ => False
end

mutual
/-- `Δ-subst` at `TyEqP` (`TyEq.applyLSub`). -/
theorem TyEqP.applyLSub : ∀ (T : VTy) (σ : LSubst) (δ δ' : LSubD L),
    (∀ y, VFree y T → interpP δ ((Lifetime.Life.var y).applySub σ) = δ'.find? y) →
      TyEqP (T.applyLSub σ) δ T δ'
  | .unit, _, _, _, _ => trivial
  | .int _, _, _, _, _ => rfl
  | .opq _, _, _, _, _ => rfl
  | .zero, _, _, _, _ => trivial
  | .unk, _, _, _, _ => trivial
  | .ref T, σ, δ, δ', h => TyEqP.applyLSub T σ δ δ' h
  | .bang T, σ, δ, δ', h => TyEqP.applyLSub T σ δ δ' h
  | .fam T, σ, δ, δ', h => TyEqP.applyLSub T σ δ δ' h
  | .thunk C, σ, δ, δ', h => CTyEqP.applyLSub C σ δ δ' h
  | .sum T₁ T₂, σ, δ, δ', h =>
      ⟨TyEqP.applyLSub T₁ σ δ δ' (fun y hy => h y (Or.inl hy)),
       TyEqP.applyLSub T₂ σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .tensor T₁ T₂, σ, δ, δ', h =>
      ⟨TyEqP.applyLSub T₁ σ δ δ' (fun y hy => h y (Or.inl hy)),
       TyEqP.applyLSub T₂ σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .imm a T, σ, δ, δ', h =>
      ⟨interpP_applySub a (fun y hy => h y (Or.inl hy)),
       TyEqP.applyLSub T σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .mut a T, σ, δ, δ', h =>
      ⟨interpP_applySub a (fun y hy => h y (Or.inl hy)),
       TyEqP.applyLSub T σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .box a T, σ, δ, δ', h =>
      ⟨interpP_applySub a (fun y hy => h y (Or.inl hy)),
       TyEqP.applyLSub T σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .tvar _, _, _, _, _ => rfl
  | .mu T, σ, δ, δ', h => TyEqP.applyLSub T σ δ δ' h
/-- `Δ-subst` at `CTyEqP` (`CTyEq.applyLSub`), with its two branches at `∀`. -/
theorem CTyEqP.applyLSub : ∀ (C : CTy) (σ : LSubst) (δ δ' : LSubD L),
    (∀ y, CFree y C → interpP δ ((Lifetime.Life.var y).applySub σ) = δ'.find? y) →
      CTyEqP (C.applyLSub σ) δ C δ'
  | .ret A, σ, δ, δ', h => TyEqP.applyLSub A σ δ δ' h
  | .arr A C, σ, δ, δ', h =>
      ⟨TyEqP.applyLSub A σ δ δ' (fun y hy => h y (Or.inl hy)),
       CTyEqP.applyLSub C σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .amp C D, σ, δ, δ', h =>
      ⟨CTyEqP.applyLSub C σ δ δ' (fun y hy => h y (Or.inl hy)),
       CTyEqP.applyLSub D σ δ δ' (fun y hy => h y (Or.inr hy))⟩
  | .top, _, _, _, _ => trivial
  | .nu C, σ, δ, δ', h => CTyEqP.applyLSub C σ δ δ' h
  | .eff _ _ _ A B fin C, σ, δ, δ', h =>
      ⟨rfl, rfl, rfl, TyEqP.applyLSub A σ δ δ' (fun y hy => h y (Or.inl hy)),
       TyEqP.applyLSub B σ δ δ' (fun y hy => h y (Or.inr (Or.inl hy))),
       CTyEqP.applyLSub fin σ δ δ' (fun y hy => h y (Or.inr (Or.inr (Or.inl hy)))),
       CTyEqP.applyLSub C σ δ δ' (fun y hy => h y (Or.inr (Or.inr (Or.inr hy))))⟩
  | .all y b S, σ, δ, δ', h => by
      have hb : interpP δ (b.applySub σ) = interpP δ' b :=
        interpP_applySub b (fun w hw => h w (Or.inl hw))
      cases hcap : lsubCaptures (lsubDrop σ y) y with
      | false =>
          rw [CTy.applyLSub_all_not_captures hcap]
          refine ⟨hb, fun α => ?_⟩
          refine CTyEqP.applyLSub S _ _ _ (fun w hw => ?_)
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
            rw [hvar, interpP_extend_of_not_mentions hcm, h w (Or.inr ⟨hwy, hw⟩),
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
          refine CTyEqP.applyLSub S _ _ _ (fun w hw => ?_)
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
            rw [hvar, interpP_extend_of_not_mentions hcm, h w (Or.inr ⟨hwy, hw⟩),
              LSubD.find?_extend_ne δ' α (Ne.symm hwy)]
end

/-- The substitution `[@a/'x]` at `δ` is `δ['x↦@aδ]`, variable by variable (`instLife_var`). -/
theorem instLifeP_var (x : LifeVar) (a : Lifetime.Life) {δ : LSubD L} {α : L}
    (ha : interpP δ a = some α) (y : LifeVar) :
    interpP δ ((Lifetime.Life.var y).applySub [(x, a)]) = (δ.extend x α).find? y := by
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
theorem CTyEqP.instLife (x : LifeVar) (a : Lifetime.Life) (C : CTy) {δ : LSubD L} {α : L}
    (ha : interpP δ a = some α) : CTyEqP (CTy.instLife x a C) δ C (δ.extend x α) :=
  CTyEqP.applyLSub C [(x, a)] δ (δ.extend x α) (fun y _ => instLifeP_var x a ha y)

/-- One computation type at two readings is forced the same way (`forceE_of_cTyEq`). -/
theorem forceE_of_cTyEqP {C C' : CTy} {δ δ' : LSubD L} (h : CTyEqP C δ C' δ') :
    forceE C = forceE C' := by
  cases C <;> cases C' <;> first | rfl | simp_all [CTyEqP]

mutual
/-- `𝒱⟦S⟧` reads a type only up to `TyEqP` (`vC_tyEq`). -/
theorem vP_tyEq (ι : Reading L) : ∀ (A A' : VTy) (δ δ' : LSubD L), TyEqP A δ A' δ' →
    ∀ ls, vP (ℍ := ℍ) ι A ls δ = vP (ℍ := ℍ) ι A' ls δ'
  | .unit, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl
  | .tensor A B, A', δ, δ', h, ls => by
      cases A' <;> simp only [TyEqP] at h
      rename_i A' B'
      funext v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vP (ℍ := ℍ) ι A ls δ v₁ ⋆ vP (ℍ := ℍ) ι B ls δ v₂) =
        (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vP (ℍ := ℍ) ι A' ls δ' v₁ ⋆ vP (ℍ := ℍ) ι B' ls δ' v₂)
      simp only [vP_tyEq ι A A' δ δ' h.1 ls, vP_tyEq ι B B' δ δ' h.2 ls]
  | .thunk C, A', δ, δ', h, ls => by
      cases A' <;> simp only [TyEqP] at h
      rename_i C'
      funext v ρ
      show (∀ ls', Ext ls ls' ρ → cP (ℍ := ℍ) ι C ls' δ (forceE C (.val v)) ρ) =
        (∀ ls', Ext ls ls' ρ → cP (ℍ := ℍ) ι C' ls' δ' (forceE C' (.val v)) ρ)
      rw [forceE_of_cTyEqP h]
      simp only [cP_tyEq ι C C' δ δ' h]
  | .ref A, A', δ, δ', h, ls => by
      cases A' <;> simp only [TyEqP] at h
      rename_i A'
      funext v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vP (ℍ := ℍ) ι A ls δ v') =
        (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vP (ℍ := ℍ) ι A' ls δ' v')
      simp only [vP_tyEq ι A A' δ δ' h ls]
  | .box a A, A', δ, δ', h, ls => by
      cases A' <;> simp only [TyEqP] at h
      rename_i a' A'
      funext v
      show atLifeP δ a (fun α => boxP ι α (vP (ℍ := ℍ) ι A ls δ v)) =
        atLifeP δ' a' (fun α => boxP ι α (vP (ℍ := ℍ) ι A' ls δ' v))
      rw [vP_tyEq ι A A' δ δ' h.2 ls, atLifeP_congr h.1]
  | .mut a A, A', δ, δ', h, ls => by
      cases A' <;> simp only [TyEqP] at h
      rename_i a' A'
      funext v
      show atLifeP δ a (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutP ι ℓ α ls (fun ls₀ => vP (ℍ := ℍ) ι A ls₀ δ)) =
        atLifeP δ' a' (fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
          ptoMutP ι ℓ α ls (fun ls₀ => vP (ℍ := ℍ) ι A' ls₀ δ'))
      simp only [vP_tyEq ι A A' δ δ' h.2]
      rw [atLifeP_congr h.1]
  | .zero, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl
  | .sum _ _, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl
  | .imm _ _, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl
  | .bang _, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl
  | .unk, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl
  | .tvar _, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl
  | .mu _, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl
  | .int _, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl
  | .fam _, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl
  | .opq _, A', δ, δ', h, ls => by cases A' <;> simp only [TyEqP] at h; rfl

/-- `𝒞⟦C⟧` reads a type only up to `CTyEqP` (`cC_tyEq`). -/
theorem cP_tyEq (ι : Reading L) : ∀ (C C' : CTy) (δ δ' : LSubD L), CTyEqP C δ C' δ' →
    ∀ ls e, cP (ℍ := ℍ) ι C ls δ e = cP (ℍ := ℍ) ι C' ls δ' e
  | .ret A, C', δ, δ', h, ls, e => by
      cases C' <;> simp only [CTyEqP] at h
      rename_i A'
      show wpTS ls e (fun ls'' => vP (ℍ := ℍ) ι A ls'' δ) =
        wpTS ls e (fun ls'' => vP (ℍ := ℍ) ι A' ls'' δ')
      simp only [vP_tyEq ι A A' δ δ' h]
  | .arr A C, C', δ, δ', h, ls, e => by
      cases C' <;> simp only [CTyEqP] at h
      rename_i A' C'
      funext ρ
      show (∀ v, (vP (ℍ := ℍ) ι A ls δ v ─⋆ cP (ℍ := ℍ) ι C ls δ (.app e (.val v))) ρ) =
        (∀ v, (vP (ℍ := ℍ) ι A' ls δ' v ─⋆ cP (ℍ := ℍ) ι C' ls δ' (.app e (.val v))) ρ)
      simp only [vP_tyEq ι A A' δ δ' h.1, cP_tyEq ι C C' δ δ' h.2]
  | .top, C', δ, δ', h, ls, e => by cases C' <;> simp only [CTyEqP] at h; rfl
  | .all x b C, C', δ, δ', h, ls, e => by
      cases C' <;> simp only [CTyEqP] at h
      rename_i x' b' C'
      funext ρ
      show (∀ α : L, (⌜LtLifeP δ b α⌝ ─⋆
          cP (ℍ := ℍ) ι C ls (δ.extend x α) (.app e (.val .unit))) ρ) =
        (∀ α : L, (⌜LtLifeP δ' b' α⌝ ─⋆
          cP (ℍ := ℍ) ι C' ls (δ'.extend x' α) (.app e (.val .unit))) ρ)
      simp only [LtLifeP, h.1, cP_tyEq ι C C' _ _ (h.2 _)]
  | .amp _ _, C', δ, δ', h, ls, e => by cases C' <;> simp only [CTyEqP] at h; rfl
  | .nu _, C', δ, δ', h, ls, e => by cases C' <;> simp only [CTyEqP] at h; rfl
  | .eff _ _ _ _ _ _ _, C', δ, δ', h, ls, e => by cases C' <;> simp only [CTyEqP] at h; rfl
end

/-! ### `∀E` -/

/-- **`∀E` over a partial order** (`allE_compatC`), with `Δ ⊨ @a ⊏ @b` read on `L`. -/
theorem allE_compatP (ι : Reading L) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {x : LifeVar}
    {b a : Lifetime.Life} {C : CTy} (h : SemP (ℍ := ℍ) ι Δ Γ M (.all x b C))
    (hlt : EntailsLtP L Δ a b) : SemP (ℍ := ℍ) ι Δ Γ (.app M (.val .unit)) (C.instLife x a) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, β, ha, hb, hab⟩ := hlt δ hδ
  have he : substAll γ (.app M (.val .unit)) = .app (substAll γ M) (.val .unit) := by
    show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ (.val .unit)) = _
    simp [Expr.psub, substAll]
  rw [he, cP_tyEq ι _ _ _ _ (CTyEqP.instLife x a C ha) ls]
  exact h δ γ ls ρ hδ hg α PMap.empty ρ ⟨rfl, β, hb, hab⟩ (ResU.comp_empty_right ρ)

end PartialLife

end
