import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Lifetimes.Interpretation
import Support.Lifetimes.Substitution
import Support.Lifetimes.Terms
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Notation
import Support.Model.Propositions
import Support.Statics.Contexts
import Support.Statics.Presupposed

/-!
# Support — LogicalRelation — Facts

`[about ours]`.  `⌜p⌝ ⋆ P` and the context relation read pointwise.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

theorem atLife_eq {δ : LSub} {a : Lifetime.Life} {α : Life} (h : a.interp δ = some α)
    (F : Life → WProp) : atLife δ a F = F α := by
  funext ρ
  exact propext ⟨fun ⟨β, hβ, k⟩ => by rw [h] at hβ; cases Option.some.inj hβ; exact k,
                 fun k => ⟨α, h, k⟩⟩

/-- `(⌜p⌝ ⋆ P)(ρ) ⟺ p ∧ P(ρ)`.
`[about ours: `⋆` at `[TR]` p. 6's own `⌜⌝` row, read at the graph]` -/
theorem pure_sep_iff {p : Prop} {P : WProp} {ρ : WRes} : (⌜p⌝ ⋆ P) ρ ↔ (p ∧ P ρ) := by
  constructor
  · rintro ⟨ρ₁, ρ₂, hc, ⟨rfl, hp⟩, hP⟩
    rw [eq_of_compS_empty_left hc]
    exact ⟨hp, hP⟩
  · rintro ⟨hp, hP⟩
    exact ⟨PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, hp⟩, hP⟩

theorem pure_sep_mk {p : Prop} {P : WProp} {ρ : WRes} (hp : p) (hP : P ρ) :
    (⌜p⌝ ⋆ P) ρ := pure_sep_iff.mpr ⟨hp, hP⟩

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
variable (δ : LSub) (v : Val) (b : Lifetime.Life)

/-- `Imm̲ 'b 1 ≜ 1` — clause (1). -/
theorem vDen_immReborrow_unit : vDen (Ty.unit.immReborrow b) δ v = ⌜v = .unit⌝ := rfl

/-- `Imm̲ 'b (T₁ ⊕ T₂) ≜ Imm̲ 'b T₁ ⊕ Imm̲ 'b T₂` — clause (2). -/
theorem vDen_immReborrow_sum (T₁ T₂ : Ty) :
    vDen ((Ty.sum T₁ T₂).immReborrow b) δ v =
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vDen (T₁.immReborrow b) δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vDen (T₂.immReborrow b) δ v₂) := rfl

/-- `Imm̲ 'b (T₁ ⊗ T₂) ≜ Imm̲ 'b T₁ ⊗ Imm̲ 'b T₂` — clause (3). -/
theorem vDen_immReborrow_tensor (T₁ T₂ : Ty) :
    vDen ((Ty.tensor T₁ T₂).immReborrow b) δ v =
      ex (fun v₁ => ex fun v₂ =>
        ⌜v = .pair v₁ v₂⌝ ⋆ vDen (T₁.immReborrow b) δ v₁ ⋆ vDen (T₂.immReborrow b) δ v₂) :=
  rfl

/-- `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk` — clause (4), and `𝒱⟦Unk⟧δ(v) ≜ emp`. -/
theorem vDen_immReborrow_lolli (T₁ T₂ : Ty) :
    vDen ((Ty.lolli T₁ T₂).immReborrow b) δ v = emp := rfl

/-- `Imm̲ 'b (Ref T) ≜ Imm 'b T`, the constructor — clause (5). -/
theorem vDen_immReborrow_ref (T : Ty) :
    vDen ((Ty.ref T).immReborrow b) δ v =
      atLife δ b (fun β => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ β (vDen T δ)) := rfl

/-- `Imm̲ 'b (Imm @a T) ≜ Imm @a T` — clause (6).  The metafunction is the
identity here, which is what 6.131's `Imm` bullet reads off its goal line. -/
theorem vDen_immReborrow_imm (a : Lifetime.Life) (T : Ty) :
    vDen ((Ty.imm a T).immReborrow b) δ v = vDen (.imm a T) δ v := rfl

/-- `Imm̲ 'b ([@a] T) ≜ Imm̲ 'b T` — clause (7), the one recursive clause whose
right-hand side is underlined. -/
theorem vDen_immReborrow_box (a : Lifetime.Life) (T : Ty) :
    vDen ((Ty.box a T).immReborrow b) δ v = vDen (T.immReborrow b) δ v := rfl

/-- `Imm̲ 'b (∀ 'a ⊏ @c. T) ≜ Unk` — clause (8). -/
theorem vDen_immReborrow_all (x : LifeVar) (c : Lifetime.Life) (T : Ty) :
    vDen ((Ty.all x c T).immReborrow b) δ v = emp := rfl

/-- `Imm̲ 'b (Mut @a T) ≜ Imm 'b T` — clause (9), [CONF] Fig. 9's.  The index
is the load's `'b`, as in 6.131's `Mut` bullet's goal `↺_α 𝒱⟦Imm α T′⟧δ(v)`.
`[about ours: clause (9) of `Ty.immReborrow` read through `𝒱⟦−⟧`]` -/
theorem vDen_immReborrow_mut (a : Lifetime.Life) (T : Ty) :
    vDen ((Ty.mut a T).immReborrow b) δ v =
      atLife δ b (fun β => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ β (vDen T δ)) := rfl

/-- `Imm̲ 'b Unk ≜ Unk` — §12.11's clause, ours. -/
theorem vDen_immReborrow_unk : vDen (Ty.unk.immReborrow b) δ v = emp := rfl

/-- Clause (5) with `@bδ` eliminated — "fold the definition of
`𝒱⟦Imm α T′⟧`" at a lifetime variable whose `δ`-image is `β`. -/
theorem vDen_immReborrow_ref_at {β : Life} (h : b.interp δ = some β) (T : Ty) :
    vDen ((Ty.ref T).immReborrow b) δ v =
      ex (fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ β (vDen T δ)) := by
  rw [vDen_immReborrow_ref, atLife_eq h]

/-- Clause (9) with `@bδ` eliminated — the `Mut` bullet's last line. -/
theorem vDen_immReborrow_mut_at {β : Life} (h : b.interp δ = some β)
    (a : Lifetime.Life) (T : Ty) :
    vDen ((Ty.mut a T).immReborrow b) δ v =
      ex (fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ β (vDen T δ)) := by
  rw [vDen_immReborrow_mut, atLife_eq h]

/-- Clause (6) with `@aδ` eliminated — the `Imm` bullet's last line, where
the index that survives is the borrow's own `@a`. -/
theorem vDen_immReborrow_imm_at {γ : Life} (a : Lifetime.Life) (h : a.interp δ = some γ)
    (T : Ty) :
    vDen ((Ty.imm a T).immReborrow b) δ v =
      ex (fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ γ (vDen T δ)) := by
  rw [vDen_immReborrow_imm, vDen_imm, atLife_eq h]

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

theorem gDen_iff {δ : LSub} {Γ : Ctx Ty} {γ : List Val} {ρ : WRes} :
    gDen δ Γ γ ρ ↔ (Ctx.LiveWithin Γ γ ∧ gSep δ Γ γ ρ) := pure_sep_iff

theorem find?_extend_life (δ : LSub) (x : LifeVar) (α : Life) (y : LifeVar) :
    (δ.extend x α).find? y = if x = y then some α else δ.find? y :=
  LSub.find?_extend δ x α y

theorem find?_extend_self (δ : LSub) (x : LifeVar) (α : Life) :
    (δ.extend x α).find? x = some α :=
  (find?_extend_life δ x α x).trans (if_pos rfl)

theorem find?_extend_ne (δ : LSub) {x y : LifeVar} (α : Life) (h : x ≠ y) :
    (δ.extend x α).find? y = δ.find? y :=
  (find?_extend_life δ x α y).trans (if_neg h)

theorem lt_varBound {x : LifeVar} :
    ∀ {a : Lifetime.Life}, a.mentions x = true → x < a.varBound := by
  intro a
  induction a with
  | var y =>
      intro h
      simp only [Lifetime.Life.mentions, beq_iff_eq] at h
      subst h
      exact Nat.lt_succ_self _
  | top => intro h; simp [Lifetime.Life.mentions] at h
  | join p q ihp ihq =>
      intro h
      simp only [Lifetime.Life.mentions, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (ihp h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ihq h) (Nat.le_max_right _ _)
  | meet p q ihp ihq =>
      intro h
      simp only [Lifetime.Life.mentions, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (ihp h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ihq h) (Nat.le_max_right _ _)

theorem not_mentions_of_varBound_le {x : LifeVar} {a : Lifetime.Life}
    (h : a.varBound ≤ x) : a.mentions x = false := by
  cases hm : a.mentions x with
  | false => rfl
  | true => exact absurd (lt_varBound hm) (Nat.not_lt.mpr h)

/-- A variable free in `T` is below `T.lifeBound`, so the renamed binder — which
`Ty.applyLSub` takes at or above that bound — is fresh for the body. -/
theorem lt_lifeBound {x : LifeVar} : ∀ {T : Ty}, LFree x T → x < T.lifeBound := by
  intro T
  induction T with
  | unit => intro h; exact h.elim
  | unk => intro h; exact h.elim
  | ref T ih => exact ih
  | bang T ih => exact ih
  | imm a T ih =>
      rintro (h | h)
      · exact Nat.lt_of_lt_of_le (lt_varBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih h) (Nat.le_max_right _ _)
  | «mut» a T ih =>
      rintro (h | h)
      · exact Nat.lt_of_lt_of_le (lt_varBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih h) (Nat.le_max_right _ _)
  | box a T ih =>
      rintro (h | h)
      · exact Nat.lt_of_lt_of_le (lt_varBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih h) (Nat.le_max_right _ _)
  | sum T₁ T₂ ih₁ ih₂ =>
      rintro (h | h)
      · exact Nat.lt_of_lt_of_le (ih₁ h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih₂ h) (Nat.le_max_right _ _)
  | tensor T₁ T₂ ih₁ ih₂ =>
      rintro (h | h)
      · exact Nat.lt_of_lt_of_le (ih₁ h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih₂ h) (Nat.le_max_right _ _)
  | lolli T₁ T₂ ih₁ ih₂ =>
      rintro (h | h)
      · exact Nat.lt_of_lt_of_le (ih₁ h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih₂ h) (Nat.le_max_right _ _)
  | all y b T ih =>
      rintro (h | ⟨-, h⟩)
      · exact Nat.lt_of_lt_of_le (lt_varBound h)
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      · exact Nat.lt_of_lt_of_le (ih h)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- The dropped variable is unbound: under the binder, `'y` stands for itself. -/
theorem assocFind_lsubDrop_self (y : LifeVar) : ∀ (σ : Lifetime.LSubst),
    Lifetime.assocFind y (lsubDrop σ y) = none := by
  intro σ
  induction σ with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨k, c⟩ := p
      by_cases hk : k = y
      · have hd : lsubDrop ((k, c) :: t) y = lsubDrop t y := by
          simp [lsubDrop, hk]
        rw [hd]; exact ih
      · have hd : lsubDrop ((k, c) :: t) y = (k, c) :: lsubDrop t y := by
          simp [lsubDrop, hk]
        rw [hd]
        simp only [Lifetime.assocFind, if_neg hk]
        exact ih

/-- …and every other variable keeps its binding. -/
theorem assocFind_lsubDrop_ne {w y : LifeVar} (h : w ≠ y) : ∀ (σ : Lifetime.LSubst),
    Lifetime.assocFind w (lsubDrop σ y) = Lifetime.assocFind w σ := by
  intro σ
  induction σ with
  | nil => rfl
  | cons p t ih =>
      obtain ⟨k, c⟩ := p
      by_cases hk : k = y
      · have hd : lsubDrop ((k, c) :: t) y = lsubDrop t y := by
          simp [lsubDrop, hk]
        have hkw : ¬ (k = w) := by rintro rfl; exact h hk
        rw [hd, ih]
        simp only [Lifetime.assocFind, if_neg hkw]
      · have hd : lsubDrop ((k, c) :: t) y = (k, c) :: lsubDrop t y := by
          simp [lsubDrop, hk]
        rw [hd]
        by_cases hkw : k = w
        · simp only [Lifetime.assocFind, if_pos hkw]
        · simp only [Lifetime.assocFind, if_neg hkw]; exact ih

/-- `lsubCaptures σ 'y = false` is a statement about every value in `σ`, and this
is it at the one the lookup returns — the branch where the binder stands. -/
theorem not_mentions_of_lsubCaptures {y w : LifeVar} {c : Lifetime.Life} :
    ∀ {σ : Lifetime.LSubst}, lsubCaptures σ y = false →
      Lifetime.assocFind w σ = some c → c.mentions y = false := by
  intro σ
  induction σ with
  | nil => intro _ h; simp [Lifetime.assocFind] at h
  | cons p t ih =>
      obtain ⟨k, d⟩ := p
      intro hcap hfind
      simp only [lsubCaptures, List.any_cons, Bool.or_eq_false_iff] at hcap
      by_cases hk : k = w
      · simp only [Lifetime.assocFind, if_pos hk] at hfind
        cases hfind
        exact hcap.1
      · simp only [Lifetime.assocFind, if_neg hk] at hfind
        exact ih (by simpa only [lsubCaptures] using hcap.2) hfind

/-- …and the same for `lsubRangeBound`, which is what the renamed binder is
chosen past — so no substituend mentions it. -/
theorem varBound_le_lsubRangeBound {w : LifeVar} {c : Lifetime.Life} :
    ∀ {σ : Lifetime.LSubst}, Lifetime.assocFind w σ = some c →
      c.varBound ≤ lsubRangeBound σ := by
  intro σ
  induction σ with
  | nil => intro h; simp [Lifetime.assocFind] at h
  | cons p t ih =>
      obtain ⟨k, d⟩ := p
      intro hfind
      have hstep : lsubRangeBound ((k, d) :: t)
          = max (max (k + 1) d.varBound) (lsubRangeBound t) := rfl
      rw [hstep]
      by_cases hk : k = w
      · simp only [Lifetime.assocFind, if_pos hk] at hfind
        cases hfind
        exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
      · simp only [Lifetime.assocFind, if_neg hk] at hfind
        exact Nat.le_trans (ih hfind) (Nat.le_max_right _ _)

theorem applySub_var_some {σ : Lifetime.LSubst} {w : LifeVar} {c : Lifetime.Life}
    (h : Lifetime.assocFind w σ = some c) : (Lifetime.Life.var w).applySub σ = c := by
  simp only [Lifetime.Life.applySub, h]

theorem applySub_var_none {σ : Lifetime.LSubst} {w : LifeVar}
    (h : Lifetime.assocFind w σ = none) : (Lifetime.Life.var w).applySub σ = .var w := by
  simp only [Lifetime.Life.applySub, h]

/-- `@aδ` depends on `δ` only through the variables `@a` mentions. -/
theorem interp_congr {δ₁ δ₂ : LSub} : ∀ (a : Lifetime.Life),
    (∀ x, a.mentions x = true → δ₁.find? x = δ₂.find? x) →
      a.interp δ₁ = a.interp δ₂ := by
  intro a
  induction a with
  | var y => intro h; exact h y (by simp [Lifetime.Life.mentions])
  | top => intro _; rfl
  | join p q ihp ihq =>
      intro h
      simp only [Lifetime.Life.interp,
        ihp (fun x hx => h x (by simp [Lifetime.Life.mentions, hx])),
        ihq (fun x hx => h x (by simp [Lifetime.Life.mentions, hx]))]
  | meet p q ihp ihq =>
      intro h
      simp only [Lifetime.Life.interp,
        ihp (fun x hx => h x (by simp [Lifetime.Life.mentions, hx])),
        ihq (fun x hx => h x (by simp [Lifetime.Life.mentions, hx]))]

/-- Extending `δ` at a variable `@a` does not mention leaves `@aδ` alone. -/
theorem interp_extend_of_not_mentions {δ : LSub} {z : LifeVar} {α : Life}
    {c : Lifetime.Life} (h : c.mentions z = false) :
    c.interp (δ.extend z α) = c.interp δ := by
  refine interp_congr c (fun w hw => ?_)
  by_cases hzw : z = w
  · subst hzw; simp [h] at hw
  · exact find?_extend_ne δ α hzw

/-- `@(a[σ])δ = @a δ′` whenever `δ′` reads each variable of `@a` the way `δ`
reads what `σ` sends it to. -/
theorem interp_applySub {σ : Lifetime.LSubst} {δ δ' : LSub} : ∀ (c : Lifetime.Life),
    (∀ y, c.mentions y = true →
        ((Lifetime.Life.var y).applySub σ).interp δ = δ'.find? y) →
      (c.applySub σ).interp δ = c.interp δ' := by
  intro c
  induction c with
  | var y => intro h; exact h y (by simp [Lifetime.Life.mentions])
  | top => intro _; rfl
  | join p q ihp ihq =>
      intro h
      simp only [Lifetime.Life.applySub, Lifetime.Life.interp,
        ihp (fun y hy => h y (by simp [Lifetime.Life.mentions, hy])),
        ihq (fun y hy => h y (by simp [Lifetime.Life.mentions, hy]))]
  | meet p q ihp ihq =>
      intro h
      simp only [Lifetime.Life.applySub, Lifetime.Life.interp,
        ihp (fun y hy => h y (by simp [Lifetime.Life.mentions, hy])),
        ihq (fun y hy => h y (by simp [Lifetime.Life.mentions, hy]))]

/-- `[@aδ]`, `↦ I @aδ` and `↦ M @aδ` depend on `@a` and `δ` only through `@aδ`. -/
theorem atLife_congr {δ₁ δ₂ : LSub} {a₁ a₂ : Lifetime.Life}
    {F G : Life → SPropU BoCa.Loc BoCa.Val}
    (ha : a₁.interp δ₁ = a₂.interp δ₂) (hF : F = G) :
    atLife δ₁ a₁ F = atLife δ₂ a₂ G := by
  funext ρ
  show atLife δ₁ a₁ F ρ = atLife δ₂ a₂ G ρ
  simp only [atLife, ha, hF]

/-- …and so does the `∀` clause's bound `α ⊏ @bδ`. -/
theorem ltLife_congr {δ₁ δ₂ : LSub} {b₁ b₂ : Lifetime.Life}
    (hb : b₁.interp δ₁ = b₂.interp δ₂) : LtLife δ₁ b₁ = LtLife δ₂ b₂ := by
  funext α; simp only [LtLife, hb]

theorem applyLSub_all_captures {σ : Lifetime.LSubst} {y : LifeVar}
    {b : Lifetime.Life} {S : Ty} (h : lsubCaptures (lsubDrop σ y) y = true) :
    (Ty.all y b S).applyLSub σ
      = Ty.all (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) S.lifeBound))
          (b.applySub σ)
          (S.applyLSub ((y, Lifetime.Life.var
            (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) S.lifeBound)))
              :: lsubDrop σ y)) := by
  simp [Ty.applyLSub, h]

theorem applyLSub_all_not_captures {σ : Lifetime.LSubst} {y : LifeVar}
    {b : Lifetime.Life} {S : Ty} (h : lsubCaptures (lsubDrop σ y) y = false) :
    (Ty.all y b S).applyLSub σ
      = Ty.all y (b.applySub σ) (S.applyLSub (lsubDrop σ y)) := by
  simp [Ty.applyLSub, h]

/-- `𝒱⟦T[σ]⟧δ = 𝒱⟦T⟧δ′`, whenever `δ′` reads each variable free in `T` the
way `δ` reads what `σ` sends it to.
`[variant: `[TR]` names `Δ-subst` at 6.162 and states no lemma for it; this is
the equality that step uses, generalised from `[@a/'a]` to a simultaneous `σ` so
that the capture-avoiding branch of `Ty.applyLSub` is inside the induction]`

Structural on `T`.  At `∀` the binder is either kept — `σ` acts on the body as
`lsubDrop σ 'y`, whose values do not mention `'y` — or renamed to a `'z` past
`lsubRangeBound` and `T.lifeBound`, and then the body is substituted by
`('y,'z) :: lsubDrop σ 'y` and read at `δ['z↦α]` against `δ′['y↦α]`. -/
theorem vDen_applyLSub : ∀ (T : Ty) (σ : Lifetime.LSubst) (δ δ' : LSub),
    (∀ y, LFree y T → ((Lifetime.Life.var y).applySub σ).interp δ = δ'.find? y) →
      vDen (T.applyLSub σ) δ = vDen T δ' := by
  intro T
  induction T with
  | unit => intro _ _ _ _; rfl
  | unk => intro _ _ _ _; rfl
  | ref T ih =>
      intro σ δ δ' h; funext v
      simp only [Ty.applyLSub]
      rw [vDen_ref, vDen_ref, ih σ δ δ' h]
  | bang T ih =>
      intro σ δ δ' h; funext v
      simp only [Ty.applyLSub]
      rw [vDen_bang, vDen_bang, ih σ δ δ' h]
  | sum T₁ T₂ ih₁ ih₂ =>
      intro σ δ δ' h; funext v
      simp only [Ty.applyLSub]
      rw [vDen_sum, vDen_sum, ih₁ σ δ δ' (fun y hy => h y (Or.inl hy)),
        ih₂ σ δ δ' (fun y hy => h y (Or.inr hy))]
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro σ δ δ' h; funext v
      simp only [Ty.applyLSub]
      rw [vDen_tensor, vDen_tensor, ih₁ σ δ δ' (fun y hy => h y (Or.inl hy)),
        ih₂ σ δ δ' (fun y hy => h y (Or.inr hy))]
  | lolli T₁ T₂ ih₁ ih₂ =>
      intro σ δ δ' h; funext v
      simp only [Ty.applyLSub]
      rw [vDen_lolli, vDen_lolli, ih₁ σ δ δ' (fun y hy => h y (Or.inl hy)),
        ih₂ σ δ δ' (fun y hy => h y (Or.inr hy))]
  | imm a T ih =>
      intro σ δ δ' h; funext v
      simp only [Ty.applyLSub]
      rw [vDen_imm, vDen_imm]
      exact atLife_congr (interp_applySub a (fun y hy => h y (Or.inl hy)))
        (by rw [ih σ δ δ' (fun y hy => h y (Or.inr hy))])
  | «mut» a T ih =>
      -- The printed cell holds `𝒱⟦T⟧δ`, so the payload has to be reproduced only
      -- denotationally.
      intro σ δ δ' h; funext v
      simp only [Ty.applyLSub]
      rw [vDen_mut, vDen_mut]
      exact atLife_congr (interp_applySub a (fun y hy => h y (Or.inl hy)))
        (by rw [ih σ δ δ' (fun y hy => h y (Or.inr hy))])
  | box a T ih =>
      intro σ δ δ' h; funext v
      simp only [Ty.applyLSub]
      rw [vDen_box, vDen_box]
      exact atLife_congr (interp_applySub a (fun y hy => h y (Or.inl hy)))
        (by rw [ih σ δ δ' (fun y hy => h y (Or.inr hy))])
  | all y b S ih =>
      intro σ δ δ' h; funext v
      have hb : (b.applySub σ).interp δ = b.interp δ' :=
        interp_applySub b (fun w hw => h w (Or.inl hw))
      cases hcap : lsubCaptures (lsubDrop σ y) y with
      | false =>
          rw [applyLSub_all_not_captures hcap, vDen_all, vDen_all, ltLife_congr hb]
          have hbody : ∀ α : Life,
              vDen (S.applyLSub (lsubDrop σ y)) (δ.extend y α)
                = vDen S (δ'.extend y α) := by
            intro α
            refine ih _ _ _ (fun w hw => ?_)
            by_cases hwy : w = y
            · subst hwy
              rw [applySub_var_none (assocFind_lsubDrop_self w σ)]
              show (δ.extend w α).find? w = (δ'.extend w α).find? w
              rw [find?_extend_self, find?_extend_self]
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
              rw [hvar, interp_extend_of_not_mentions hcm, h w (Or.inr ⟨hwy, hw⟩),
                find?_extend_ne δ' α (Ne.symm hwy)]
          simp only [hbody]
      | true =>
          -- The renamed binder, together with the three facts about it that the
          -- body's case needs; `Ty.applyLSub` picks it as this `max`.
          obtain ⟨z, hzy, hzr, hzS, hty⟩ :
              ∃ z, y < z ∧ lsubRangeBound (lsubDrop σ y) ≤ z ∧ S.lifeBound ≤ z ∧
                (Ty.all y b S).applyLSub σ
                  = Ty.all z (b.applySub σ)
                      (S.applyLSub ((y, Lifetime.Life.var z) :: lsubDrop σ y)) :=
            ⟨_, Nat.lt_of_lt_of_le (Nat.lt_succ_self y) (Nat.le_max_left _ _),
              Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _),
              Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _),
              applyLSub_all_captures hcap⟩
          rw [hty, vDen_all, vDen_all, ltLife_congr hb]
          have hbody : ∀ α : Life,
              vDen (S.applyLSub ((y, Lifetime.Life.var z) :: lsubDrop σ y))
                  (δ.extend z α)
                = vDen S (δ'.extend y α) := by
            intro α
            refine ih _ _ _ (fun w hw => ?_)
            by_cases hwy : w = y
            · subst hwy
              rw [applySub_var_some
                (show Lifetime.assocFind w ((w, Lifetime.Life.var z) :: lsubDrop σ w)
                    = some (Lifetime.Life.var z) from by simp [Lifetime.assocFind])]
              show (δ.extend z α).find? z = (δ'.extend w α).find? w
              rw [find?_extend_self, find?_extend_self]
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
                      (Nat.lt_of_lt_of_le (lt_lifeBound hw) hzS)
                | some d =>
                    have hfσ : Lifetime.assocFind w σ = some d := by
                      rw [← assocFind_lsubDrop_ne hwy σ]; exact hf
                    rw [applySub_var_some hfσ]
                    exact not_mentions_of_varBound_le
                      (Nat.le_trans (varBound_le_lsubRangeBound hf) hzr)
              rw [hvar, interp_extend_of_not_mentions hcm, h w (Or.inr ⟨hwy, hw⟩),
                find?_extend_ne δ' α (Ne.symm hwy)]
          simp only [hbody]

/-- `𝒱⟦T⟧δ` depends on `δ` only at the variables free in `T`.
`[about ours: `vDen_applyLSub` at the empty substitution]` -/
theorem vDen_congr (T : Ty) {δ₁ δ₂ : LSub}
    (h : ∀ y, LFree y T → δ₁.find? y = δ₂.find? y) :
    vDen T δ₁ = vDen T δ₂ := by
  have hid : ∀ y, ((Lifetime.Life.var y).applySub []).interp δ₁ = δ₁.find? y := by
    intro y
    simp only [applySub_var_none (show Lifetime.assocFind y [] = none from rfl),
      Lifetime.Life.interp_var]
  have h₁ : vDen (T.applyLSub []) δ₁ = vDen T δ₁ :=
    vDen_applyLSub T [] δ₁ δ₁ (fun y _ => hid y)
  have h₂ : vDen (T.applyLSub []) δ₁ = vDen T δ₂ :=
    vDen_applyLSub T [] δ₁ δ₂ (fun y hy => (hid y).trans (h y hy))
  exact h₁.symm.trans h₂

/-- `δ['x↦α]` is invisible to a type `'x` is not free in.  Two printed
steps are this equation: `[TR]` p. 46's "Fold and simplify, using that `'b` does
not occur free in `T₁` or `T₂`" — the bound variable of `∀'a ⊏ ⊓Δ. …`, which the
axiom-table constructors take as a schematic `x` — and the third row of the
`↺V₂` table on p. 35, "Have `𝒱⟦T⟧δ = 𝒱⟦T⟧δ['a↦α]` because `'a` not free in
`T`". -/
theorem vDen_extend_of_not_free {x : LifeVar} {T : Ty} (h : ¬ LFree x T)
    (δ : LSub) (α : Life) : vDen T (δ.extend x α) = vDen T δ :=
  vDen_congr T (fun _ hy => find?_extend_ne δ α (fun e => h (e ▸ hy)))

/-- `⨅δ` — the meet of the lifetimes `δ` assigns, as a right fold of
`Fig16.Life.meet` with `⨅∅ = ⊤`.  `[TR]` p. 35 writes it in the first row of
the `↺V₂` table, "fix `α ⊏ ⨅δ` arbitrary".  The fold is over `cod(δ)` and lands
in the carrier.
`[about ours: a realisation of `[TR]` p. 35's `⨅δ` for a finite `δ`]` -/
def meetOfCod (δ : LSub) : Life :=
  δ.entries.foldr (fun e a => Life.meet e.2 a) Life.top

end BoCa.Fig16.LogRel

end
