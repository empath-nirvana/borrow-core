import GhostEnd.TypedD

/-!
# GhostEnd — closures carrying the lend: re-derived, not transported (#262, item 3)

A closure that captures `m` holds the lend's cell inside its environment, and its type need not
mention `'x`: `λ_. (m := 1)` is a `U(F 1)`. So `𝒱⟦U C⟧_{δ[x ↦ α]}` alone cannot be thawed: the
relation at `U` reads the closure only through its behaviour, and does not say which part of
its resource is the cell to drop and re-lend.

A closure *made by the borrower* is a typed term with a closing substitution: `λ_. M` with
`Δ, x ⊏ b; ·, Γ_f ⊢ M : F A`, or a λ-value `V` with `Δ, x ⊏ b; Γ_f ⊢ V : C`, at the values
`γ_f`. That is the kernel invariant (#262, item 4) at the values the borrower builds. `TV`
records it: a typed value is an atom in the relation (`Mut 'x T`, or data free of `'x`
outliving it), a pair or injection of typed values, a closure typed by its derivation over a
typed environment `TVG`, or a fixed axiomatic constant, closed and in the relation at every
lend. `TV true` is the same with each atom frozen (`fzAtom`).

The lemmas are inductions over typed values. `Mut` is case 2 and closures recurse into their
environments:

* `tv_sound`: a typed value is in the relation at `δ[x ↦ α]`. A closure is re-derived there by
  `fundamentalC` at its own derivation, from its environment's relation (`thunkF_compatC`'s and
  `thunkV_compatC`'s argument);
* `tv_freeze`: at a stop, the lend's cell is dropped wherever it sits, in a pair or inside a
  closure's environment;
* `tv_thaw`: at a later lend the handed view goes back where the cell was dropped, and the value
  is typed again at `α′`. With `tv_sound`, a closure that captured `m` is re-derived at
  `δ[x ↦ α′]` from its typing.

No naturality is used, and `mut_not_natural` is never asked: nothing is moved from one lend to
the next. The re-lent closure is a new instance of its typing.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- An atom a typed value may hold across a stop: the borrow, or data free of `'x` that outlives
it. -/
def AtomOk (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T A : VTy) : Prop :=
  A = .mut (.var x) T ∨ (¬ VFree x A ∧ VOutlives (Δ.extend x b) (.var x) A)

mutual
/-- **A typed value** at the lend `α`. `fz = false`: live, each atom in the relation at
`δ[x ↦ α]`, the drop flag `false`. `fz = true`: frozen, each atom as `fzAtom` records it, the flag
saying whether the lend's cell was dropped. -/
inductive TV (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (δ : LSub)
    (l : BoCa.Loc) : Bool → Life → VTy → List SRec → Val → Bool → WRes → Prop where
  | atomL {α A ls v ρ} (hA : AtomOk Δ x b T A) (h : vC true A ls (δ.extend x α) v ρ) :
      TV Δ x b T δ l false α A ls v false ρ
  | atomF {α A ls v d ρ} (hA : AtomOk Δ x b T A) (h : fzAtom x T δ l α A ls v d ρ) :
      TV Δ x b T δ l true α A ls v d ρ
  | pair {fz α A B ls v₁ v₂ d₁ d₂ ρ₁ ρ₂ ρ} (h₁ : TV Δ x b T δ l fz α A ls v₁ d₁ ρ₁)
      (h₂ : TV Δ x b T δ l fz α B ls v₂ d₂ ρ₂) (hd : ¬ (d₁ = true ∧ d₂ = true))
      (hc : ResU.CompS ρ₁ ρ₂ ρ) :
      TV Δ x b T δ l fz α (.tensor A B) ls (.pair v₁ v₂) (d₁ || d₂) ρ
  | inl {fz α A B ls v d ρ} (h : TV Δ x b T δ l fz α A ls v d ρ) :
      TV Δ x b T δ l fz α (.sum A B) ls (.inj₁ v) d ρ
  | inr {fz α A B ls v d ρ} (h : TV Δ x b T δ l fz α B ls v d ρ) :
      TV Δ x b T δ l fz α (.sum A B) ls (.inj₂ v) d ρ
  /-- `thunk M : U(F A)` over the environment `γ_f`, typed by its derivation. -/
  | cloF {fz α Γf γf M A ls d ρ}
      (hD : CDerives (Δ.extend x b) (⟨.unit, false⟩ :: Γf) M (.comp (.ret A)))
      (h : TVG Δ x b T δ l fz α Γf γf ls d ρ) :
      TV Δ x b T δ l fz α (.thunk (.ret A)) ls (Val.lam (Expr.psub 1 γf M)) d ρ
  /-- A λ-value `V : C`, `C` not an `F`, as a thunk `U C` over `γ_f`, typed by its derivation. -/
  | cloV {fz α Γf γf N C ls d ρ} (hC : C.isRet = false)
      (hD : CDerives (Δ.extend x b) Γf (.val (.lam N)) (.comp C))
      (h : TVG Δ x b T δ l fz α Γf γf ls d ρ) :
      TV Δ x b T δ l fz α (.thunk C) ls (Val.lam (Expr.psub 1 γf N)) d ρ
  /-- A fixed axiomatic constant at a thunk type: closed, holding nothing, and in the relation
  at every lend (its compatibility lemma at `δ[x ↦ α′]`). -/
  | const {fz α C ls v}
      (h : ∀ α', (Δ.extend x b).Models (δ.extend x α') → ∀ ls',
        vC true (.thunk C) ls' (δ.extend x α') v PMap.empty) :
      TV Δ x b T δ l fz α (.thunk C) ls v false PMap.empty
/-- A typed environment, slot by slot as `gSepC` reads it. -/
inductive TVG (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (δ : LSub)
    (l : BoCa.Loc) : Bool → Life → Ctx VTy → List Val → List SRec → Bool → WRes → Prop where
  | nil {fz α ls} : TVG Δ x b T δ l fz α [] [] ls false PMap.empty
  | dead {fz α A Γ v γ ls d ρ} (h : TVG Δ x b T δ l fz α Γ γ ls d ρ) :
      TVG Δ x b T δ l fz α (⟨A, false⟩ :: Γ) (v :: γ) ls d ρ
  | live {fz α A Γ v γ ls d₁ d₂ ρ₁ ρ₂ ρ} (h₁ : TV Δ x b T δ l fz α A ls v d₁ ρ₁)
      (h₂ : TVG Δ x b T δ l fz α Γ γ ls d₂ ρ₂) (hd : ¬ (d₁ = true ∧ d₂ = true))
      (hc : ResU.CompS ρ₁ ρ₂ ρ) :
      TVG Δ x b T δ l fz α (⟨A, true⟩ :: Γ) (v :: γ) ls (d₁ || d₂) ρ
end

section
variable {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {δ : LSub} {l : BoCa.Loc}

/-- **Soundness**: a live typed value is in the relation at `δ[x ↦ α]`. A closure is re-derived
there by `fundamentalC` at its own derivation. -/
theorem tv_sound {α : Life} (hδα : (Δ.extend x b).Models (δ.extend x α)) :
    (∀ {fz α' A ls v d ρ}, TV Δ x b T δ l fz α' A ls v d ρ → fz = false → α' = α →
      vC true A ls (δ.extend x α) v ρ) ∧
    (∀ {fz α' Γ γ ls d ρ}, TVG Δ x b T δ l fz α' Γ γ ls d ρ → fz = false → α' = α →
      gDenC ls (δ.extend x α) Γ γ ρ) := by
  constructor
  · intro fz α' A ls v d ρ h
    exact TV.rec
      (motive_1 := fun fz α' A ls v d ρ _ => fz = false → α' = α →
        vC true A ls (δ.extend x α) v ρ)
      (motive_2 := fun fz α' Γ γ ls d ρ _ => fz = false → α' = α →
        gDenC ls (δ.extend x α) Γ γ ρ)
      (fun _ h _ e => e ▸ h)
      (fun _ _ hf _ => absurd hf (by decide))
      (fun _ _ _ hc ih₁ ih₂ hf e => ⟨_, _, pure_sep_mk rfl ⟨_, _, hc, ih₁ hf e, ih₂ hf e⟩⟩)
      (fun _ ih hf e => Or.inl ⟨_, pure_sep_mk rfl (ih hf e)⟩)
      (fun _ ih hf e => Or.inr ⟨_, pure_sep_mk rfl (ih hf e)⟩)
      (fun {_ _ Γf γf M A ls _ ρ} hD _ ih hf e => by
        intro ls' hext
        refine cC_head (.ret A) (fun μ => Head.beta μ (Expr.psub 1 γf M) Val.unit) rfl ls' _ ρ ?_
        rw [← substAll_cons_l]
        exact (fundamentalC hD) _ (Val.unit :: γf) ls' ρ hδα
          (gDenC_dead_cons _ _ (gDenC_local hext (ih hf e))))
      (fun {_ _ Γf γf N C ls _ ρ} hC hD _ ih hf e => by
        intro ls' hext
        rw [forceE_of_not_ret hC]
        exact (fundamentalC hD) _ γf ls' ρ hδα (gDenC_local hext (ih hf e)))
      (fun {_ _ _ ls _} h _ _ => h α hδα ls)
      (fun _ _ => gDenC_mk trivial ⟨rfl, trivial⟩)
      (fun {_ _ A Γ v γ ls _ ρ} _ ih hf e => gDenC_dead_cons A v (ih hf e))
      (fun {_ _ A Γ v γ ls _ _ ρ₁ ρ₂ ρ} _ _ _ hc ih₁ ih₂ hf e => by
        obtain ⟨hlw, hg⟩ := gDenC_iff.mp (ih₂ hf e)
        exact gDenC_mk hlw ⟨ρ₁, ρ₂, hc, ih₁ hf e, hg⟩)
      h
  · intro fz α' Γ γ ls d ρ h
    exact TVG.rec
      (motive_1 := fun fz α' A ls v d ρ _ => fz = false → α' = α →
        vC true A ls (δ.extend x α) v ρ)
      (motive_2 := fun fz α' Γ γ ls d ρ _ => fz = false → α' = α →
        gDenC ls (δ.extend x α) Γ γ ρ)
      (fun _ h _ e => e ▸ h)
      (fun _ _ hf _ => absurd hf (by decide))
      (fun _ _ _ hc ih₁ ih₂ hf e => ⟨_, _, pure_sep_mk rfl ⟨_, _, hc, ih₁ hf e, ih₂ hf e⟩⟩)
      (fun _ ih hf e => Or.inl ⟨_, pure_sep_mk rfl (ih hf e)⟩)
      (fun _ ih hf e => Or.inr ⟨_, pure_sep_mk rfl (ih hf e)⟩)
      (fun {_ _ Γf γf M A ls _ ρ} hD _ ih hf e => by
        intro ls' hext
        refine cC_head (.ret A) (fun μ => Head.beta μ (Expr.psub 1 γf M) Val.unit) rfl ls' _ ρ ?_
        rw [← substAll_cons_l]
        exact (fundamentalC hD) _ (Val.unit :: γf) ls' ρ hδα
          (gDenC_dead_cons _ _ (gDenC_local hext (ih hf e))))
      (fun {_ _ Γf γf N C ls _ ρ} hC hD _ ih hf e => by
        intro ls' hext
        rw [forceE_of_not_ret hC]
        exact (fundamentalC hD) _ γf ls' ρ hδα (gDenC_local hext (ih hf e)))
      (fun {_ _ _ ls _} h _ _ => h α hδα ls)
      (fun _ _ => gDenC_mk trivial ⟨rfl, trivial⟩)
      (fun {_ _ A Γ v γ ls _ ρ} _ ih hf e => gDenC_dead_cons A v (ih hf e))
      (fun {_ _ A Γ v γ ls _ _ ρ₁ ρ₂ ρ} _ _ _ hc ih₁ ih₂ hf e => by
        obtain ⟨hlw, hg⟩ := gDenC_iff.mp (ih₂ hf e)
        exact gDenC_mk hlw ⟨ρ₁, ρ₂, hc, ih₁ hf e, hg⟩)
      h

end

section
variable {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {δ : LSub} {l : BoCa.Loc}

mutual
/-- A typed value is Kripke along `Ext`. -/
theorem tv_local : ∀ {fz α A ls ls' v d ρ}, Ext ls ls' ρ → TV Δ x b T δ l fz α A ls v d ρ →
    TV Δ x b T δ l fz α A ls' v d ρ
  | _, _, _, _, _, _, _, _, he, .atomL hA h => .atomL hA (vC_local true _ he h)
  | _, _, _, _, _, _, _, _, he, .atomF hA h => .atomF hA (by
      rcases h with h | ⟨hd, hv, hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨hd, vC_local true _ he hv, hs⟩)
  | _, _, _, _, _, _, _, _, he, .pair h₁ h₂ hd hc =>
      .pair (tv_local (he.left hc) h₁) (tv_local (he.right hc) h₂) hd hc
  | _, _, _, _, _, _, _, _, he, .inl h => .inl (tv_local he h)
  | _, _, _, _, _, _, _, _, he, .inr h => .inr (tv_local he h)
  | _, _, _, _, _, _, _, _, he, .cloF hD h => .cloF hD (tvg_local he h)
  | _, _, _, _, _, _, _, _, he, .cloV hC hD h => .cloV hC hD (tvg_local he h)
  | _, _, _, _, _, _, _, _, _, .const h => .const h
theorem tvg_local : ∀ {fz α Γ γ ls ls' d ρ}, Ext ls ls' ρ → TVG Δ x b T δ l fz α Γ γ ls d ρ →
    TVG Δ x b T δ l fz α Γ γ ls' d ρ
  | _, _, _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, _, he, .dead h => .dead (tvg_local he h)
  | _, _, _, _, _, _, _, _, he, .live h₁ h₂ hd hc =>
      .live (tv_local (he.left hc) h₁) (tvg_local (he.right hc) h₂) hd hc
end

mutual
/-- A frozen typed value is in `Res_α`. -/
theorem tv_inStratum : ∀ {fz α A ls v d ρ}, TV Δ x b T δ l fz α A ls v d ρ → fz = true →
    ρ.InStratum α
  | _, _, _, _, _, _, _, .atomL _ _, hf => absurd hf (by decide)
  | _, _, _, _, _, _, _, .atomF _ h, _ => fzAtom_inStratum h
  | _, _, _, _, _, _, _, .pair h₁ h₂ _ hc, hf =>
      (outlives_comp hc _).mpr ⟨tv_inStratum h₁ hf, tv_inStratum h₂ hf⟩
  | _, _, _, _, _, _, _, .inl h, hf => tv_inStratum h hf
  | _, _, _, _, _, _, _, .inr h, hf => tv_inStratum h hf
  | _, _, _, _, _, _, _, .cloF _ h, hf => tvg_inStratum h hf
  | _, _, _, _, _, _, _, .cloV _ _ h, hf => tvg_inStratum h hf
  | _, α, _, _, _, _, _, .const _, _ => ResU.inStratum_empty α
theorem tvg_inStratum : ∀ {fz α Γ γ ls d ρ}, TVG Δ x b T δ l fz α Γ γ ls d ρ → fz = true →
    ρ.InStratum α
  | _, α, _, _, _, _, _, .nil, _ => ResU.inStratum_empty α
  | _, _, _, _, _, _, _, .dead h, hf => tvg_inStratum h hf
  | _, _, _, _, _, _, _, .live h₁ h₂ _ hc, hf =>
      (outlives_comp hc _).mpr ⟨tv_inStratum h₁ hf, tvg_inStratum h₂ hf⟩
end


/-- A view handed is a dropped cell. -/
theorem dropC_of_vwD {d : Bool} {α : Life} {ls : List SRec} {ρ : WRes}
    (h : vwD l T δ d α ls ρ) : dropC l d ρ := by
  cases d with
  | false => exact h
  | true => exact dropC_of_view h

/-- The two views of a stop under a frame, joined: at most one is a cell. -/
theorem vwD_join {d₁ d₂ : Bool} (hd : ¬ (d₁ = true ∧ d₂ = true)) {α : Life} {ls : List SRec}
    {ρa ρb ρ : WRes} (ha : vwD l T δ d₁ α ls ρa) (hb : vwD l T δ d₂ α ls ρb)
    (hc : ResU.CompS ρa ρb ρ) : vwD l T δ (d₁ || d₂) α ls ρ := by
  cases d₁ <;> cases d₂
  · obtain ⟨rfl, -⟩ := ha; obtain ⟨rfl, -⟩ := hb
    exact ⟨eq_of_compS_empty_left hc, trivial⟩
  · obtain ⟨rfl, -⟩ := ha; rw [eq_of_compS_empty_left hc]; exact hb
  · obtain ⟨rfl, -⟩ := hb
    rw [ResU.CompS.functional hc (ResU.comp_empty_right ρa)]; exact ha
  · exact absurd ⟨rfl, rfl⟩ hd

/-- **Freeze an atom**, the dropped cell read as the view at `α`. -/
theorem fzAtom_freeze_view (hT : ¬ VFree x T) {α : Life}
    (hδα : (Δ.extend x b).Models (δ.extend x α)) {A : VTy} (hA : AtomOk Δ x b T A)
    {ls : List SRec} {v : Val} {ρ : WRes} (hv : vC true A ls (δ.extend x α) v ρ)
    (ht : TabAt l α ρ) :
    ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ fzAtom x T δ l α A ls v d ρz ∧ vwD l T δ d α ls ρn := by
  obtain ⟨d, ρz, ρn, hc, hz, hn⟩ := fzAtom_freeze hδα hA hv ht
  cases d with
  | false => exact ⟨false, ρz, ρn, hc, hz, hn⟩
  | true =>
      rcases hz with ⟨-, rfl, rfl, rfl⟩ | ⟨h, -⟩
      · obtain rfl := eq_of_compS_empty_left hc
        exact ⟨true, PMap.empty, ρ, hc, Or.inl ⟨rfl, rfl, rfl, rfl⟩, view_of_vC hT hv⟩
      · exact absurd h (by decide)

mutual
/-- **Freeze a typed value** at the lend `α`: the lend's cell is dropped wherever it sits, in a
pair or inside a closure's environment. -/
theorem tv_freeze (hT : ¬ VFree x T) {α : Life} (hδα : (Δ.extend x b).Models (δ.extend x α)) :
    ∀ {fz α' A ls v d ρ}, TV Δ x b T δ l fz α' A ls v d ρ → fz = false → α' = α → TabAt l α ρ →
      ∃ d' ρz ρn, ResU.CompS ρz ρn ρ ∧ TV Δ x b T δ l true α A ls v d' ρz ∧ vwD l T δ d' α ls ρn
  | _, _, _, _, _, _, _, .atomF _ _, hf, _, _ => absurd hf (by decide)
  | _, _, _, _, _, _, _, .atomL hA h, _, rfl, ht => by
      obtain ⟨d', ρz, ρn, hc, hz, hn⟩ := fzAtom_freeze_view hT hδα hA h ht
      exact ⟨d', ρz, ρn, hc, .atomF hA hz, hn⟩
  | _, _, _, _, _, _, _, .pair h₁ h₂ _ hc, hf, e, ht => by
      obtain ⟨ht₁, ht₂⟩ := (tabAt_comp hc).mp ht
      obtain ⟨d₁, ρz₁, ρn₁, hc₁, hz₁, hn₁⟩ := tv_freeze hT hδα h₁ hf e ht₁
      obtain ⟨d₂, ρz₂, ρn₂, hc₂, hz₂, hn₂⟩ := tv_freeze hT hδα h₂ hf e ht₂
      have hnd : ¬ (d₁ = true ∧ d₂ = true) := by
        rintro ⟨rfl, rfl⟩
        exact dropC_disj (dropC_of_vwD hn₁) (dropC_of_vwD hn₂) (ResU.CompS.comm hc₁)
          (ResU.CompS.comm hc₂) hc
      obtain ⟨ρz, ρn, hcz, hcn, hcρ⟩ := compS_four hc₁ hc₂ hc
      exact ⟨d₁ || d₂, ρz, ρn, hcρ, .pair hz₁ hz₂ hnd hcz, vwD_join hnd hn₁ hn₂ hcn⟩
  | _, _, _, _, _, _, _, .inl h, hf, e, ht => by
      obtain ⟨d', ρz, ρn, hc, hz, hn⟩ := tv_freeze hT hδα h hf e ht
      exact ⟨d', ρz, ρn, hc, .inl hz, hn⟩
  | _, _, _, _, _, _, _, .inr h, hf, e, ht => by
      obtain ⟨d', ρz, ρn, hc, hz, hn⟩ := tv_freeze hT hδα h hf e ht
      exact ⟨d', ρz, ρn, hc, .inr hz, hn⟩
  | _, _, _, _, _, _, _, .cloF hD h, hf, e, ht => by
      obtain ⟨d', ρz, ρn, hc, hz, hn⟩ := tvg_freeze hT hδα h hf e ht
      exact ⟨d', ρz, ρn, hc, .cloF hD hz, hn⟩
  | _, _, _, _, _, _, _, .cloV hC hD h, hf, e, ht => by
      obtain ⟨d', ρz, ρn, hc, hz, hn⟩ := tvg_freeze hT hδα h hf e ht
      exact ⟨d', ρz, ρn, hc, .cloV hC hD hz, hn⟩
  | _, _, _, _, _, _, _, .const h, _, rfl, _ =>
      ⟨false, PMap.empty, PMap.empty, compS_empty_left _, .const h, rfl, trivial⟩
/-- **Freeze a typed environment.** -/
theorem tvg_freeze (hT : ¬ VFree x T) {α : Life} (hδα : (Δ.extend x b).Models (δ.extend x α)) :
    ∀ {fz α' Γ γ ls d ρ}, TVG Δ x b T δ l fz α' Γ γ ls d ρ → fz = false → α' = α →
      TabAt l α ρ →
      ∃ d' ρz ρn, ResU.CompS ρz ρn ρ ∧ TVG Δ x b T δ l true α Γ γ ls d' ρz ∧ vwD l T δ d' α ls ρn
  | _, _, _, _, _, _, _, .nil, _, _, _ =>
      ⟨false, PMap.empty, PMap.empty, compS_empty_left _, .nil, rfl, trivial⟩
  | _, _, _, _, _, _, _, .dead h, hf, e, ht => by
      obtain ⟨d', ρz, ρn, hc, hz, hn⟩ := tvg_freeze hT hδα h hf e ht
      exact ⟨d', ρz, ρn, hc, .dead hz, hn⟩
  | _, _, _, _, _, _, _, .live h₁ h₂ _ hc, hf, e, ht => by
      obtain ⟨ht₁, ht₂⟩ := (tabAt_comp hc).mp ht
      obtain ⟨d₁, ρz₁, ρn₁, hc₁, hz₁, hn₁⟩ := tv_freeze hT hδα h₁ hf e ht₁
      obtain ⟨d₂, ρz₂, ρn₂, hc₂, hz₂, hn₂⟩ := tvg_freeze hT hδα h₂ hf e ht₂
      have hnd : ¬ (d₁ = true ∧ d₂ = true) := by
        rintro ⟨rfl, rfl⟩
        exact dropC_disj (dropC_of_vwD hn₁) (dropC_of_vwD hn₂) (ResU.CompS.comm hc₁)
          (ResU.CompS.comm hc₂) hc
      obtain ⟨ρz, ρn, hcz, hcn, hcρ⟩ := compS_four hc₁ hc₂ hc
      exact ⟨d₁ || d₂, ρz, ρn, hcρ, .live hz₁ hz₂ hnd hcz, vwD_join hnd hn₁ hn₂ hcn⟩
end

mutual
/-- **Thaw a typed value** at a later lend `α′ ⊑ α`: the view goes back where the cell was
dropped, and every closure is typed again over its thawed environment. -/
theorem tv_thaw (hT : ¬ VFree x T) {α α' : Life} (hle : α' ≤ α) :
    ∀ {fz α₀ A ls v d ρz}, TV Δ x b T δ l fz α₀ A ls v d ρz → fz = true → α₀ = α →
      ∀ (ρv ρ : WRes), vwD l T δ d α' ls ρv → ResU.CompS ρz ρv ρ →
      TV Δ x b T δ l false α' A ls v false ρ ∧ TabAt l α' ρ
  | _, _, _, _, _, _, _, .atomL _ _, hf, _, _, _, _, _ => absurd hf (by decide)
  | _, _, _, _, _, _, _, .atomF hA h, _, rfl, _, _, hv, hc => by
      obtain ⟨h', ht⟩ := fzAtom_thaw (Δ := Δ) (b := b) hT hle hA h hv hc
      exact ⟨.atomL hA h', ht⟩
  | _, _, _, _, _, _, _, .pair (A := A) (B := B) (ls := ls) (v₁ := v₁) (v₂ := v₂) (d₁ := d₁)
      (d₂ := d₂) (ρ₁ := ρz₁) (ρ₂ := ρz₂) h₁ h₂ hnd hcz, hf, e, _, ρ, hv, hc => by
      have ih₁ := tv_thaw hT hle h₁ hf e
      have ih₂ := tv_thaw hT hle h₂ hf e
      have key : ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧
          (TV Δ x b T δ l false α' A ls v₁ false ρ₁ ∧ TabAt l α' ρ₁) ∧
          (TV Δ x b T δ l false α' B ls v₂ false ρ₂ ∧ TabAt l α' ρ₂) := by
        cases d₁ with
        | true =>
            obtain rfl : d₂ = false := by
              cases d₂
              · rfl
              · exact absurd ⟨rfl, rfl⟩ hnd
            obtain ⟨y, hy, hcy⟩ := compS_exch hcz hc
            exact ⟨y, ρz₂, hcy, ih₁ _ _ hv hy, ih₂ _ _ ⟨rfl, trivial⟩ (ResU.comp_empty_right ρz₂)⟩
        | false =>
            obtain ⟨y, hy, hcy⟩ := compS_reassoc hcz hc
            exact ⟨ρz₁, y, hcy, ih₁ _ _ ⟨rfl, trivial⟩ (ResU.comp_empty_right ρz₁), ih₂ _ _ hv hy⟩
      obtain ⟨ρ₁, ρ₂, hc', ⟨h₁', ht₁⟩, ⟨h₂', ht₂⟩⟩ := key
      exact ⟨.pair h₁' h₂' (fun h => absurd h.1 (by decide)) hc', (tabAt_comp hc').mpr ⟨ht₁, ht₂⟩⟩
  | _, _, _, _, _, _, _, .inl h, hf, e, _, _, hv, hc => by
      obtain ⟨h', ht⟩ := tv_thaw hT hle h hf e _ _ hv hc
      exact ⟨.inl h', ht⟩
  | _, _, _, _, _, _, _, .inr h, hf, e, _, _, hv, hc => by
      obtain ⟨h', ht⟩ := tv_thaw hT hle h hf e _ _ hv hc
      exact ⟨.inr h', ht⟩
  | _, _, _, _, _, _, _, .cloF hD h, hf, e, _, _, hv, hc => by
      obtain ⟨h', ht⟩ := tvg_thaw hT hle h hf e _ _ hv hc
      exact ⟨.cloF hD h', ht⟩
  | _, _, _, _, _, _, _, .cloV hC hD h, hf, e, _, _, hv, hc => by
      obtain ⟨h', ht⟩ := tvg_thaw hT hle h hf e _ _ hv hc
      exact ⟨.cloV hC hD h', ht⟩
  | _, _, _, _, _, _, _, .const h, _, _, _, _, hv, hc => by
      obtain ⟨rfl, -⟩ := hv
      obtain rfl := eq_of_compS_empty_left hc
      exact ⟨.const h, tabAt_empty l α'⟩
/-- **Thaw a typed environment.** -/
theorem tvg_thaw (hT : ¬ VFree x T) {α α' : Life} (hle : α' ≤ α) :
    ∀ {fz α₀ Γ γ ls d ρz}, TVG Δ x b T δ l fz α₀ Γ γ ls d ρz → fz = true → α₀ = α →
      ∀ (ρv ρ : WRes), vwD l T δ d α' ls ρv → ResU.CompS ρz ρv ρ →
      TVG Δ x b T δ l false α' Γ γ ls false ρ ∧ TabAt l α' ρ
  | _, _, _, _, _, _, _, .nil, _, _, _, _, hv, hc => by
      obtain ⟨rfl, -⟩ := hv
      obtain rfl := eq_of_compS_empty_left hc
      exact ⟨.nil, tabAt_empty l α'⟩
  | _, _, _, _, _, _, _, .dead h, hf, e, _, _, hv, hc => by
      obtain ⟨h', ht⟩ := tvg_thaw hT hle h hf e _ _ hv hc
      exact ⟨.dead h', ht⟩
  | _, _, _, _, _, _, _, .live (A := A) (Γ := Γ) (v := v) (γ := γ) (ls := ls) (d₁ := d₁)
      (d₂ := d₂) (ρ₁ := ρz₁) (ρ₂ := ρz₂) h₁ h₂ hnd hcz, hf, e, _, ρ, hv, hc => by
      have ih₁ := tv_thaw hT hle h₁ hf e
      have ih₂ := tvg_thaw hT hle h₂ hf e
      have key : ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧
          (TV Δ x b T δ l false α' A ls v false ρ₁ ∧ TabAt l α' ρ₁) ∧
          (TVG Δ x b T δ l false α' Γ γ ls false ρ₂ ∧ TabAt l α' ρ₂) := by
        cases d₁ with
        | true =>
            obtain rfl : d₂ = false := by
              cases d₂
              · rfl
              · exact absurd ⟨rfl, rfl⟩ hnd
            obtain ⟨y, hy, hcy⟩ := compS_exch hcz hc
            exact ⟨y, ρz₂, hcy, ih₁ _ _ hv hy, ih₂ _ _ ⟨rfl, trivial⟩ (ResU.comp_empty_right ρz₂)⟩
        | false =>
            obtain ⟨y, hy, hcy⟩ := compS_reassoc hcz hc
            exact ⟨ρz₁, y, hcy, ih₁ _ _ ⟨rfl, trivial⟩ (ResU.comp_empty_right ρz₁), ih₂ _ _ hv hy⟩
      obtain ⟨ρ₁, ρ₂, hc', ⟨h₁', ht₁⟩, ⟨h₂', ht₂⟩⟩ := key
      exact ⟨.live h₁' h₂' (fun h => absurd h.1 (by decide)) hc', (tabAt_comp hc').mpr ⟨ht₁, ht₂⟩⟩
end

end

end GhostEnd
