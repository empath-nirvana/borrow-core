import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_4_StandardEntailments.Lemmas
import Paper.S6_7_WeakestPreconditionRules.Lemmas
import Support.Dynamics.Machine
import Support.Dynamics.PrintedWp
import Support.Lifetimes.Interpretation
import Support.Lifetimes.Substitution
import Support.Lifetimes.Terms
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts
import Support.Model.Algebra
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.Notation
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.Reborrow
import Support.Model.ReborrowRule
import Support.Model.Singletons
import Support.Model.UpdateFrame
import Support.Statics.Contexts
import Support.Statics.Presupposed

/-!
# Support — LogicalRelation — Compatibility

`[about ours]`.  What the compatibility lemmas share at the literal judgment: `𝒢⟦Γ⟧` split along the context, `wp` monotone and bound with a frame, `𝒱⟦−⟧` under substitution and instantiation, the members of a lifetime, the hypotheses 6.172–6.175 add (`…Side`) and the derivations that carry them (`DerivesIn`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

theorem gDen_mk {δ : LSub} {Γ : Ctx Ty} {γ : List Val} {ρ : WRes}
    (hlen : Ctx.LiveWithin Γ γ) (hg : gSep δ Γ γ ρ) : gDen δ Γ γ ρ :=
  gDen_iff.mpr ⟨hlen, hg⟩

/-- A context with no live slot contributes nothing: `⊛_{x∈∅} … = emp`. -/
theorem gSep_dead {δ : LSub} : ∀ {Γ : Ctx Ty}, Ctx.Dead Γ →
    ∀ {γ : List Val} {ρ : WRes}, gSep δ Γ γ ρ → ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ h; exact h.1
  | cons _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' => exact ih (γ := γ') h

/-- `ID`'s context: the one live slot's value is at its own index, and it
carries the whole resource. -/
theorem gSep_solo {δ : LSub} : ∀ {Γ : Ctx Ty} {i : Nat} {T : Ty}, Ctx.Solo Γ i T →
    ∀ {γ : List Val} {ρ : WRes}, i < γ.length → gSep δ Γ γ ρ →
      ∃ v, γ[i]? = some v ∧ vDen T δ v ρ := by
  intro Γ i T hs
  induction hs with
  | @here T Γ' hdead =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
          rw [gSep_dead hdead hrest] at hc
          rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
          exact ⟨v, rfl, hv⟩
  | @there S T Γ' i' _ ih =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨w, hw, hv⟩ := ih (γ := γ') (by simpa using hlen) hg
          exact ⟨w, by simpa using hw, hv⟩

/-- `Γ = Γ₁, Γ₂` splits the resource.  The value list is the same on both sides:
a `Ctx.Split` keeps every position and only turns liveness bits off. -/
theorem gSep_split {δ : LSub} : ∀ {Γ Γ₁ Γ₂ : Ctx Ty}, Ctx.Split Γ Γ₁ Γ₂ →
    ∀ {γ : List Val} {ρ : WRes}, gSep δ Γ γ ρ →
      (gSep δ Γ₁ γ ⋆ gSep δ Γ₂ γ) ρ := by
  intro Γ Γ₁ Γ₂ hsp
  induction hsp with
  | nil =>
      intro γ ρ h
      refine ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ?_⟩
      cases γ <;> exact ⟨rfl, trivial⟩
  | @left Γ' Γ₁' Γ₂' T _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_reassoc' hcσ hc
          exact ⟨x, σ₂, hxρ, ⟨ρ₁, σ₁, hx, hv, h₁⟩, h₂⟩
  | @right Γ' Γ₁' Γ₂' T _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_lcomm hcσ hc
          exact ⟨σ₁, x, hxρ, h₁, ⟨ρ₁, σ₂, hx, hv, h₂⟩⟩
  | @dead Γ' Γ₁' Γ₂' T _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' => exact ih (γ := γ') h

/-- The split, at `𝒢` rather than at `⊛`. -/
theorem gDen_split {δ : LSub} {Γ Γ₁ Γ₂ : Ctx Ty} (hsp : Ctx.Split Γ Γ₁ Γ₂)
    {γ : List Val} {ρ : WRes} (hg : gDen δ Γ γ ρ) :
    (gDen δ Γ₁ γ ⋆ gDen δ Γ₂ γ) ρ := by
  obtain ⟨hlen, hs⟩ := gDen_iff.mp hg
  obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := gSep_split hsp hs
  exact ⟨ρ₁, ρ₂, hc,
    gDen_mk (hsp.liveWithin hlen).1 h₁,
    gDen_mk (hsp.liveWithin hlen).2 h₂⟩

/-- `wp` is monotone in its postcondition — `[TR]` 6.146 at the empty
frame.  `[about ours: 6.146 with `∅` for the framed resource]` -/
theorem wp_mono {P Q : Val → WProp} (h : ∀ v, Entails (P v) (Q v)) (e : Expr) :
    Entails (wp e P) (wp e Q) := by
  intro ρ hw
  refine wp_ramify e P Q ρ ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, hw, ?_⟩
  intro v ρ₁ ρ₂ hP hc
  rw [eq_of_compS_empty_left hc]
  exact h v ρ₁ hP

/-- Bind on the sub-expression, frame the rest of the context through the run,
then weaken — `[TR]` 6.135 and 6.146 in one, and the move `[TR]` §6.8 makes at
every rule with a context split.
`[about ours: 6.135 and 6.146 composed, at the shape §6.8 uses them in]` -/
theorem wp_bind_frame (K : Kont) (e : Expr) (P : Val → WProp) (R : WProp)
    (Q : Val → WProp) (h : ∀ v, Entails ((P v) ⋆ R) (wp (K.plug (.val v)) Q)) :
    Entails ((wp e P) ⋆ R) (wp (K.plug e) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, hwp, hR⟩
  refine wp_bind K e Q ρ (wp_ramify e P (fun v => wp (K.plug (.val v)) Q) ρ ?_)
  refine ⟨ρ₁, ρ₂, hc, hwp, ?_⟩
  intro v σ₁ σ₂ hP hcs
  exact h v σ₂ ⟨σ₁, ρ₂, ResU.CompS.comm hcs, hP, hR⟩

/-- The same without a frame — the shape `⊕I` uses, where the rule has one
premise and does not split the context.
`[about ours: 6.135 and 6.146 composed at an empty frame]` -/
theorem wp_bind_mono (K : Kont) (e : Expr) (P Q : Val → WProp)
    (h : ∀ v, Entails (P v) (wp (K.plug (.val v)) Q)) :
    Entails (wp e P) (wp (K.plug e) Q) :=
  Entails.trans (wp_mono h e) (wp_bind K e Q)

/-- `wp(v₁,v₂){Q̂} ⊨ wp((v₁,v₂)){Q̂}` — reflexivity: the two sides are one term.
`[about ours: `[TR]` p. 1's `(v₁,v₂)`, at the two derivations its grammar
identifies]` -/
theorem wp_pair (v₁ v₂ : Val) (Q : Val → WProp) :
    Entails (wp (.val (.pair v₁ v₂)) Q) (wp (.pair (.val v₁) (.val v₂)) Q) :=
  Entails.refl _

/-- …and for the first injection.
`[about ours: `[TR]` p. 1's `inj₁ v`, at the two derivations its grammar
identifies]` -/
theorem wp_inj₁ (v : Val) (Q : Val → WProp) :
    Entails (wp (.val (.inj₁ v)) Q) (wp (.inj₁ (.val v)) Q) :=
  Entails.refl _

/-- …and the second.
`[about ours: `[TR]` p. 1's `inj₂ v`, at the two derivations its grammar
identifies]` -/
theorem wp_inj₂ (v : Val) (Q : Val → WProp) :
    Entails (wp (.val (.inj₂ v)) Q) (wp (.inj₂ (.val v)) Q) :=
  Entails.refl _

/-- `𝒱⟦Mut @a T⟧δ` depends on `T` only through `𝒱⟦T⟧δ`, because the printed
`mut` cell stores the payload predicate.
`[about ours: the substitutivity of the printed `mut` clause]` -/
theorem vDen_mut_congr {δ₁ δ₂ : LSub} {a₁ a₂ : Lifetime.Life} {T₁ T₂ : Ty}
    (ha : a₁.interp δ₁ = a₂.interp δ₂) (hT : vDen T₁ δ₁ = vDen T₂ δ₂) :
    vDen (.mut a₁ T₁) δ₁ = vDen (.mut a₂ T₂) δ₂ := by
  funext v ρ
  show atLife δ₁ a₁ _ ρ = atLife δ₂ a₂ _ ρ
  simp only [atLife, ha, hT]

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel.MutPayloadSubst
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

theorem interp_congr (δ : LSub) :
    (Lifetime.Life.var 0).interp (δ.extend 0 Life.top)
      = (Lifetime.Life.top).interp δ := by
  simp [Lifetime.Life.interp, LSub.find?_extend, Life.top, Lifetime.SLife.top]
  rfl

/-- The payload's two readings agree: `𝒱⟦Imm 'x 1⟧_{δ['x↦⊤]} = 𝒱⟦Imm ⊤ 1⟧δ`. -/
theorem imm_eq (δ : LSub) :
    vDen (.imm (.var 0) .unit) (δ.extend 0 Life.top)
      = vDen (.imm .top .unit) δ := by
  have hu : vDen .unit (δ.extend 0 Life.top) = vDen .unit δ := by funext w; rfl
  funext v ρ
  show atLife _ _ _ ρ = atLife _ _ _ ρ
  simp only [atLife, interp_congr δ, hu]

end BoCa.Fig16.LogRel.MutPayloadSubst

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- …and at `Ty.scopedB`, which differs from `Ty.wfB` only at `Unk`, where
`LFree x Unk` is `False`.
`[about ours: `not_lfree_of_wfB` at the scoping half]` -/
theorem not_lfree_of_scopedB {x : LifeVar} :
    ∀ {T : Ty} {Δ : LifeCtx}, Δ.find? x = none → T.scopedB Δ = true → ¬ LFree x T := by
  intro T
  induction T with
  | unit => intro _ _ _ h; exact h
  | unk => intro _ _ _ h; exact h
  | ref T ih => intro Δ hx h; exact ih hx h
  | bang T ih => intro Δ hx h; exact ih hx h
  | sum T₁ T₂ ih₁ ih₂ =>
      intro Δ hx h
      simp only [Ty.scopedB, Bool.and_eq_true] at h
      rintro (k | k)
      · exact ih₁ hx h.1 k
      · exact ih₂ hx h.2 k
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro Δ hx h
      simp only [Ty.scopedB, Bool.and_eq_true] at h
      rintro (k | k)
      · exact ih₁ hx h.1 k
      · exact ih₂ hx h.2 k
  | lolli T₁ T₂ ih₁ ih₂ =>
      intro Δ hx h
      simp only [Ty.scopedB, Bool.and_eq_true] at h
      rintro (k | k)
      · exact ih₁ hx h.1 k
      · exact ih₂ hx h.2 k
  | box a T ih =>
      intro Δ hx h
      simp only [Ty.scopedB, Bool.and_eq_true] at h
      rintro (k | k)
      · rw [Lifetime.Life.mentions_false_of_wf hx h.1] at k; exact Bool.noConfusion k
      · exact ih hx h.2 k
  | imm a T ih =>
      intro Δ hx h
      simp only [Ty.scopedB, Bool.and_eq_true] at h
      rintro (k | k)
      · rw [Lifetime.Life.mentions_false_of_wf hx h.1] at k; exact Bool.noConfusion k
      · exact ih hx h.2 k
  | «mut» a T ih =>
      intro Δ hx h
      simp only [Ty.scopedB, Bool.and_eq_true] at h
      rintro (k | k)
      · rw [Lifetime.Life.mentions_false_of_wf hx h.1] at k; exact Bool.noConfusion k
      · exact ih hx h.2 k
  | all y b T ih =>
      intro Δ hx h
      simp only [Ty.scopedB, Bool.and_eq_true] at h
      rintro (k | ⟨hne, k⟩)
      · rw [Lifetime.Life.mentions_false_of_wf hx h.1.2] at k; exact Bool.noConfusion k
      · refine ih ?_ h.2 k
        rw [LifeCtx.find?_extend, if_neg (fun e => hne e.symm)]
        exact hx

/-- `𝒱⟦T[@a/'x]⟧δ = 𝒱⟦T⟧_{δ['x↦@aδ]}` — `Δ-subst` at the substitution `∀E`
performs.
`[variant: the single-variable instance of `vDen_applyLSub`; `[TR]` states no
lemma for the step 6.162 calls `Δ-subst`]` -/
theorem vDen_instLife (x : LifeVar) (a : Lifetime.Life) (T : Ty) {δ : LSub} {α : Life}
    (ha : a.interp δ = some α) :
    vDen (Ty.instLife x a T) δ = vDen T (δ.extend x α) := by
  refine vDen_applyLSub T [(x, a)] δ (δ.extend x α) (fun y _ => ?_)
  by_cases hxy : x = y
  · subst hxy
    rw [applySub_var_some
      (show Lifetime.assocFind x [(x, a)] = some a from by simp [Lifetime.assocFind])]
    rw [ha, find?_extend_self]
  · rw [applySub_var_none
      (show Lifetime.assocFind y [(x, a)] = none from by
        simp only [Lifetime.assocFind, if_neg hxy])]
    show δ.find? y = _
    rw [find?_extend_ne δ α hxy]

/-- `⊛_{x∈dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))` depends on `δ` only through the live slots: a
consumed slot contributes no conjunct (convention L4), so its type is never
read. -/
theorem gSep_congr {δ₁ δ₂ : LSub} : ∀ {Γ : Ctx Ty} {γ : List Val},
    (∀ s ∈ Γ, s.live = true → vDen s.ty δ₁ = vDen s.ty δ₂) →
    gSep δ₁ Γ γ = gSep δ₂ Γ γ := by
  intro Γ
  induction Γ with
  | nil => intro γ _; cases γ <;> rfl
  | cons s Γ' ih =>
      intro γ h
      cases γ with
      | nil => rfl
      | cons v γ' =>
          have htail : ∀ t ∈ Γ', t.live = true → vDen t.ty δ₁ = vDen t.ty δ₂ :=
            fun t ht => h t (List.mem_cons_of_mem _ ht)
          by_cases hl : s.live
          · simp only [gSep, if_pos hl, ih htail, h s (List.mem_cons_self ..) hl]
          · simp only [gSep, if_neg hl, ih htail]

/-- `✓∅`, by `[TR]` Lemma 6.10 splitting the validity of an owned cell.
`[about ours: `✓∅` is not a printed result; this is 6.10's instance at it]` -/
theorem valid_empty : ResU.Valid (Loc := BoCa.Loc) (Val := BoCa.Val) PMap.empty :=
  (ResU.Valid.split
    (compS_empty_left (ResU.single (0 : BoCa.Loc) (CellU.ownOf (Val.unit))))
    (ResU.valid_single_own 0 Val.unit)).1

/-- `∅ # ∅`. -/
theorem hash_empty : ResU.Hash (Loc := BoCa.Loc) (Val := BoCa.Val)
    PMap.empty PMap.empty :=
  ResU.hash_empty_right valid_empty

/-- `ℰ⟦1⟧δ(free (alloc ()))` holds on the printed machine: `[TR]` p. 2's `⊸E`
types it at `1` (`TR3.derives_wFreeAlloc`), and the printed `alloc↦`, `free↦`
and frame `e K` run it to `()`.
`[about ours: `[TR]` p. 4's `ℰ⟦1⟧` over `TR3.Steps`, the printed machine]` -/
theorem tr3_eDen_freeAlloc (δ : LSub) :
    TR3.wp TR3.wFreeAlloc (vDen .unit δ) PMap.empty := by
  have hb := TR3.wp_bind (.appR (.val (.prim .free)) .hole) TR3.wAlloc
    (vDen .unit δ) PMap.empty
  refine hb ?_
  refine TR3.wp_alloc .unit _ PMap.empty ?_
  intro l σ τ hσ hc
  cases hσ
  rw [eq_of_compS_empty_left hc]
  exact TR3.wp_free l .unit (vDen .unit δ) _
    ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, ⟨rfl, rfl⟩⟩

/-- Every lifetime recorded in an `imm` cell of `ρ` is one `L` licenses. -/
def LifeMembers (L : Life → Prop) (ρ : WRes) : Prop :=
  ∀ l (i : ImmU BoCa.Loc BoCa.Val), ρ.get l = some (.imm i) → ∀ x, i.ls.mem x → L x

theorem lifeMembers_empty {L : Life → Prop} : LifeMembers L (PMap.empty : WRes) :=
  fun _ _ e => absurd e (by simp)

/-- `●` unions the sets at a shared location, so a licence covering both
operands covers the composite. -/
theorem lifeMembers_compS {L : Life → Prop} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : LifeMembers L ρ₁) (h₂ : LifeMembers L ρ₂) : LifeMembers L ρ := by
  intro l i e x hx
  rcases ResU.Comp.get hc l with ⟨-, -, a3⟩ | ⟨ζ, b1, -, b3⟩ | ⟨ζ, -, c2, c3⟩ |
      ⟨ζ₁, ζ₂, ζ, d1, d2, d3, hC⟩
  · rw [a3] at e; exact absurd e (by simp)
  · rw [b3] at e; cases Option.some.inj e; exact h₁ l i b1 x hx
  · rw [c3] at e; cases Option.some.inj e; exact h₂ l i c2 x hx
  · obtain ⟨s₁, s₂, v, σ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := hC
    subst e₁; subst e₂; subst e₃
    rw [d3] at e
    cases Option.some.inj e
    rcases hx with hx | hx
    · exact h₁ l _ d1 x hx
    · exact h₂ l _ d2 x hx

/-- `reb_α` establishes it.  It mints `{α}` at the cells it creates and
keeps a subset of each source `imm` cell's lifetime set, so a licence holding
of the source and of `α` holds of the image. -/
theorem lifeMembers_reb {L : Life → Prop} {α : Life} {src img : WRes}
    (h : ResU.Reb α src img) (hs : LifeMembers L src) (hα : L α) :
    LifeMembers L img := by
  intro l i e x hx
  obtain ⟨φ, hφ⟩ := ResU.reb_dom_subset h e
  by_cases hk : φ.kind = Kind.imm
  · rcases CellU.rep φ with ⟨w, rfl⟩ | ⟨s, w, χ, hsχ, rfl⟩ | ⟨b, w, χ, hb, P, hw, rfl⟩
    · exact absurd hk (by simp)
    · obtain ⟨t, ht, hts, he⟩ := ResU.reb_imm_cell_sub h e hφ
      have hls : i.ls = t := congrArg ImmU.ls (CellU.imm.inj he)
      rw [hls] at hx
      exact hs l _ hφ x (hts x hx)
    · exact absurd hk (by simp)
  · obtain ⟨v, χ, hχ, hψ, -, -⟩ := ResU.reb_src h e hφ hk
    have hls : i.ls = LSet.singleton α := congrArg ImmU.ls (CellU.imm.inj hψ)
    rw [hls] at hx
    exact hx ▸ hα

/-- …and it splits.  At a shared location `●` unions the sets, so an
operand's members are among the composite's. -/
theorem lifeMembers_compS_left {L : Life → Prop} {ρ₁ ρ₂ ρ : WRes}
    (hc : ResU.CompS ρ₁ ρ₂ ρ) (h : LifeMembers L ρ) : LifeMembers L ρ₁ := by
  intro l i e x hx
  rcases ResU.Comp.get hc l with ⟨a1, -, -⟩ | ⟨ζ, b1, -, b3⟩ | ⟨ζ, c1, -, -⟩ |
      ⟨ζ₁, ζ₂, ζ, d1, d2, d3, hC⟩
  · rw [e] at a1; exact absurd a1 (by simp)
  · rw [e] at b1; cases Option.some.inj b1; exact h l i b3 x hx
  · rw [e] at c1; exact absurd c1 (by simp)
  · obtain ⟨s₁, s₂, v, σ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := hC
    subst e₁; subst e₂; subst e₃
    rw [e] at d1
    cases Option.some.inj d1
    exact h l _ d3 x (Or.inl hx)

/-- `α ⊑ ⊓β̄` at each `imm` cell — `LifeMembers` at the licence `(α ⊑ ·)`,
`⊓β̄` is a member of `β̄` (`Fig16.LSet.meet_mem`) bounded by every other
(`Fig16.LSet.meet_least`), so bounding the meet and bounding every member
agree.
`[about ours: the slot condition, as `LifeMembers` at one licence]` -/
def ImmAt (α : Life) (ρ : WRes) : Prop := LifeMembers (fun x => α ⊑ x) ρ

/-- The shortest lifetime `T` itself declares, following `OutlivesRules`'
own clauses: the borrow formers contribute their index and do not recurse
(neither does the judgment), the structural ones take the meet. -/
def tyLifeMeet (δ : LSub) : Ty → Option Life
  | .unit           => none
  | .lolli _ _      => none
  | .all _ _ _      => none
  | .unk            => none
  | .ref T          => tyLifeMeet δ T
  | .bang _          => none
  | .imm b _        => b.interp δ
  | .mut b _        => b.interp δ
  | .box b _        => b.interp δ
  | .sum T₁ T₂      => match tyLifeMeet δ T₁, tyLifeMeet δ T₂ with
      | some x, some y => some (x ⊓ y)
      | some x, none   => some x
      | none,   some y => some y
      | none,   none   => none
  | .tensor T₁ T₂   => match tyLifeMeet δ T₁, tyLifeMeet δ T₂ with
      | some x, some y => some (x ⊓ y)
      | some x, none   => some x
      | none,   some y => some y
      | none,   none   => none

/-- The three readings of "what lifetime does `T` declare", kept apart. -/
inductive TyLife where
  /-- `T` declares `β`, the shortest lifetime any of its borrow formers names. -/
  | bounded (β : Life) : TyLife
  /-- `Δ ⊢ T ⊐ @a` reaches `T` and `T` names no lifetime. -/
  | free : TyLife
  /-- `Δ ⊢ T ⊐ @a` has no rule for `T`. -/
  | unreached : TyLife

/-- `OutlivesRules.tensor` and `OutlivesRules.sum` need both sides derivable,
so a side the judgment does not reach makes the whole type unreached; two
declared lifetimes meet, and a side declaring nothing constrains nothing. -/
def TyLife.combine : TyLife → TyLife → TyLife
  | .unreached, _           => .unreached
  | _,          .unreached  => .unreached
  | .bounded x, .bounded y  => .bounded (x ⊓ y)
  | .bounded x, .free       => .bounded x
  | .free,      .bounded y  => .bounded y
  | .free,      .free       => .free

/-- The index `OutlivesRules` itself induces: the borrow formers contribute
their index and do not recurse (neither does the judgment), the structural
formers combine, and the three formers the judgment has no rule for are
`unreached`.  A borrow former whose lifetime does not interpret is `unreached`
too — `Δ.Models δ` makes that case vacuous under the judgment. -/
def tyLife (δ : LSub) : Ty → TyLife
  | .unit           => .free
  | .lolli _ _      => .unreached
  | .all _ _ _      => .unreached
  | .unk            => .unreached
  | .ref T          => tyLife δ T
  | .bang _          => .free
  | .imm b _        => match b.interp δ with
      | some β => .bounded β
      | none   => .unreached
  | .mut b _        => match b.interp δ with
      | some β => .bounded β
      | none   => .unreached
  | .box b _        => match b.interp δ with
      | some β => .bounded β
      | none   => .unreached
  | .sum T₁ T₂      => TyLife.combine (tyLife δ T₁) (tyLife δ T₂)
  | .tensor T₁ T₂   => TyLife.combine (tyLife δ T₁) (tyLife δ T₂)

/-- The non-circular slot condition, at the three-valued index.  `ImmAt` at
the lifetime `T` declares, which `reb_α` establishes inside its own
definition.  A type the judgment reaches and which
declares nothing carries no `imm` cell at all.  A type the judgment does not
reach is asked nothing. -/
def TyAt (δ : LSub) (T : Ty) (ρ : WRes) : Prop :=
  match tyLife δ T with
  | .bounded β => ImmAt β ρ
  | .free      => ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ Kind.imm
  | .unreached => True

/-- `⊛_{x∈dom(Γ)}` again, with each live slot's denotation conjoined with
`TyAt` at that slot's own type.  Same `⋆`-structure as `gSep`, so it
splits the same way. -/
noncomputable def gSepB (Δ : LifeCtx) (δ : LSub) : Ctx Ty → List Val → WProp
  | [],     _      => emp
  | _ :: _, []     => emp
  | s :: Γ, v :: γ =>
      if s.live then
        (fun ρ => vDen s.ty δ v ρ ∧ TyAt δ s.ty ρ) ⋆ gSepB Δ δ Γ γ
      else gSepB Δ δ Γ γ

/-- `𝒢⟦Γ⟧δ(γ)` carrying the slot conditions. -/
noncomputable def gDenB (Δ : LifeCtx) (δ : LSub) (Γ : Ctx Ty) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepB Δ δ Γ γ

/-- What `∀I` asks beyond `Derives.allI`.  `[TR]` Lemma 6.161's proof
(p. 42) says "By Δ-extend, δ['a↦α] ∈ ⟦Δ, ('a ⊏ @b)⟧" and "Extend 𝒢⟦Γ⟧δ with
δ['a↦α]"; each holds only if the extension changes no lookup its object makes.
So: `@b` does not mention `'a` (the first sentence at `'a` itself, where the
bound read is `@bδ['a↦α]`); no bound of `Δ` mentions `'a` (the same sentence at
each `'y ∈ dom(Δ)`); and `'a` is free in no live type of `Γ` (the second
sentence).  `[TR]`'s named binder gives all three by convention.
`[about ours: the freshness `allI_compat` takes as hypotheses, at one `∀I` node]` -/
def AllISide (Δ : LifeCtx) (Γ : Ctx Ty) (x : LifeVar) (b : Lifetime.Life) : Prop :=
  b.mentions x = false ∧
    (∀ y u, Δ.find? y = some u → u.mentions x = false) ∧
    (∀ s ∈ Γ, s.live = true → ¬ LFree x s.ty)

/-- What `withbor`'s first form asks beyond `Derives.withbor1Ax`.  `[TR]`
Lemma 6.172's proof (pp. 45–46) applies `ImmFrame` where 6.173 applies
`MutFrame`, and `ImmFrame` (`[TR]` 6.64, p. 22) carries no premise
`𝒱⟦T₁⟧δ ⊨ [@bδ] 𝒱⟦T₁⟧δ`, so this form asks no side condition on `T₁` — only the
folding sentence "using that 'b does not occur free in T₁ or T₂", the binder's
freshness for both, which the page's convention gives and the schematic `x`
does not.  `Δ` is not read, so it is no parameter.
`[about ours: the hypotheses `withbor1_compat` adds, at one `withbor1Ax` node]` -/
def Withbor1Side (x : LifeVar) (T₁ T₂ : Ty) : Prop :=
  ¬ LFree x T₁ ∧ ¬ LFree x T₂

/-- What `withbor`'s second form asks beyond `Derives.withbor2Ax`.  `[TR]`
Lemma 6.173's proof (p. 46) says "Fold and simplify, using that 'b does not
occur free in T₁ or T₂" — the binder's freshness for both, which the page's
convention gives and the schematic `x` does not.  Its "Since Δ ⊢ T₁ ⊐ @b,
theorem 6.60 gives 𝒱⟦T₁⟧δ ⊨ [@bδ] 𝒱⟦T₁⟧δ" is the node's own premise through
`vDen_outlives`, so it asks nothing here.
`[about ours: the hypotheses `withbor2_compat` adds, at one `withbor2Ax` node]` -/
def Withbor2Side (x : LifeVar) (T₁ T₂ : Ty) : Prop :=
  ¬ LFree x T₁ ∧ ¬ LFree x T₂

/-- What `withbor`'s third form asks beyond `Derives.withbor3Ax`.  `[TR]`
Lemma 6.174 inherits 6.172's "'b does not occur free in T₁ or T₂", the
binder's freshness for both, which the page's convention gives and the
schematic `x` does not.  The entailment `MutFrame` consumes is read off the
borrow in hand (`withbor3_compat`), so it asks nothing here.
`[about ours: the hypotheses `withbor3_compat` adds, at one `withbor3Ax` node]` -/
def Withbor3Side (x : LifeVar) (T₁ T₂ : Ty) : Prop :=
  ¬ LFree x T₁ ∧ ¬ LFree x T₂

/-- What `withload` asks beyond `Derives.withloadAx`, from `[TR]` Lemma 6.175's
proof (p. 48): `hesc`, `Fig16.BoLo.RebEscrow` — what `[TR]` 6.150 inherits from
6.55 — at the `P̂` this proof builds; and the binder's freshness for `T₁` and
`T₂`, from *"because `'b` does not occur free in `T₂`"* (p. 48) and `↺V₂`'s
*"if `'a` not free in `T`"* (p. 35).  `[TR]` 6.125 (`↺⋆`) names no part of the
node and stays a parameter of the induction.
`[about ours: the hypotheses `withload_compat` adds that name the node, at one
`withloadAx` node]` -/
def WithloadSide (x : LifeVar) (T₁ T₂ : Ty) : Prop :=
  (∀ (δ : LSub) (vℓ : Val), RebEscrow
      (fun β v' => ⌜vℓ = v'⌝ ⋆ vDen (T₁.immReborrow (.var x)) (δ.extend x β) vℓ)) ∧
    ¬ LFree x T₁ ∧ ¬ LFree x T₂

/-- `Δ; Γ ⊢ e : T` by a derivation in the regime: `BoCa.Derives` with
`AllISide`, `Withbor1Side`, `Withbor2Side`, `Withbor3Side` and `WithloadSide`
premises of `allI`, `withbor1Ax`, `withbor2Ax`, `withbor3Ax` and `withloadAx`.
`[about ours: `BoCa.Derives`, with a premise added at five constructors]` -/
inductive DerivesIn : LifeCtx → Ctx Ty → Expr → Ty → Prop where
  | var {Δ Γ i T} (h : Ctx.Solo Γ i T) : DerivesIn Δ Γ (.var i) T
  | unitI {Δ Γ} (h : Ctx.Dead Γ) : DerivesIn Δ Γ (.val .unit) .unit
  | unitE {Δ Γ Γ₁ Γ₂ e₁ e₂ T} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (h₁ : DerivesIn Δ Γ₁ e₁ .unit) (h₂ : DerivesIn Δ Γ₂ e₂ T) :
      DerivesIn Δ Γ (.seq e₁ e₂) T
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (h₁ : DerivesIn Δ Γ₁ e₁ T₁) (h₂ : DerivesIn Δ Γ₂ e₂ T₂) :
      DerivesIn Δ Γ (.pair e₁ e₂) (.tensor T₁ T₂)
  | tensorE {Δ Γ Γp Γb ep eb T₁ T₂ T} (hs : Ctx.Split Γ Γp Γb)
      (hp : DerivesIn Δ Γp ep (.tensor T₁ T₂))
      (hb : DerivesIn Δ (⟨T₂, true⟩ :: ⟨T₁, true⟩ :: Γb) eb T) :
      DerivesIn Δ Γ (.letpair ep eb) T
  | sumI₁ {Δ Γ e T₁ T₂} (h : DerivesIn Δ Γ e T₁) :
      DerivesIn Δ Γ (.inj₁ e) (.sum T₁ T₂)
  | sumI₂ {Δ Γ e T₁ T₂} (h : DerivesIn Δ Γ e T₂) :
      DerivesIn Δ Γ (.inj₂ e) (.sum T₁ T₂)
  | sumE {Δ Γ Γs Γb es e₁ e₂ T₁ T₂ T} (hs : Ctx.Split Γ Γs Γb)
      (h₀ : DerivesIn Δ Γs es (.sum T₁ T₂))
      (h₁ : DerivesIn Δ (⟨T₁, true⟩ :: Γb) e₁ T)
      (h₂ : DerivesIn Δ (⟨T₂, true⟩ :: Γb) e₂ T) :
      DerivesIn Δ Γ (.case es e₁ e₂) T
  | lolliI {Δ Γ b T₁ T₂} (h : DerivesIn Δ (⟨T₁, true⟩ :: Γ) b T₂) :
      DerivesIn Δ Γ (.val (.lam b)) (.lolli T₁ T₂)
  | lolliE {Δ Γ Γ₁ Γ₂ f a T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (ha : DerivesIn Δ Γ₁ a T₁) (hf : DerivesIn Δ Γ₂ f (.lolli T₁ T₂)) :
      DerivesIn Δ Γ (.app f a) T₂
  /-- `∀I`, under `AllISide`. -/
  | allI {Δ Γ x b S e T} (hx : Δ.find? x = none)
      (h : DerivesIn (Δ.extend x b) (⟨S, false⟩ :: Γ) e T) (hside : AllISide Δ Γ x b) :
      DerivesIn Δ Γ (.val (.lam e)) (.all x b T)
  | allE {Δ Γ e x b T a} (h : DerivesIn Δ Γ e (.all x b T)) (hlt : Δ.EntailsLt a b) :
      DerivesIn Δ Γ (.app e (.val .unit)) (Ty.instLife x a T)
  | boxIctx {Δ Γ e T a} (h : DerivesIn Δ Γ e T) (hΓ : Ctx.Outlives Δ Γ a) :
      DerivesIn Δ Γ e (.box a T)
  | boxE {Δ Γ e T a} (h : DerivesIn Δ Γ e (.box a T)) : DerivesIn Δ Γ e T
  | immSub {Δ Γ e a b T} (h : DerivesIn Δ Γ e (.imm b T)) (hle : Δ.EntailsLe a b) :
      DerivesIn Δ Γ e (.imm a T)
  | mutSub {Δ Γ e a b T} (h : DerivesIn Δ Γ e (.mut b T)) (hle : Δ.EntailsLe a b) :
      DerivesIn Δ Γ e (.mut a T)
  | allocAx {Δ Γ T} (hΓ : Ctx.Dead Γ) :
      DerivesIn Δ Γ (.val (.prim .alloc)) (.lolli T (.ref T))
  | freeAx {Δ Γ T} (hΓ : Ctx.Dead Γ) :
      DerivesIn Δ Γ (.val (.prim .free)) (.lolli (.ref T) T)
  | swapAx {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) : DerivesIn Δ Γ swap (axSwapTy T₁ T₂)
  | copyAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) : DerivesIn Δ Γ copy (axCopyTy a T)
  | forgetImmAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) : DerivesIn Δ Γ forget (axForgetImmTy a T)
  | forgetMutAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) : DerivesIn Δ Γ forget (axForgetMutTy a T)
  | forgetUnkAx {Δ Γ} (hΓ : Ctx.Dead Γ) : DerivesIn Δ Γ forget axForgetUnkTy
  /-- `withbor`'s first form, under `Withbor1Side`. -/
  | withbor1Ax {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hside : Withbor1Side x T₁ T₂) :
      DerivesIn Δ Γ withbor (axWithbor1Ty x Δ.meetOfDom T₁ T₂)
  /-- `withbor`'s second form, under `Withbor2Side`. -/
  | withbor2Ax {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hs : ∃ b, Δ.Defines b ∧ BoCa.Outlives Δ T₁ b) (hside : Withbor2Side x T₁ T₂) :
      DerivesIn Δ Γ withbor (axWithbor2Ty x Δ.meetOfDom T₁ T₂)
  /-- `withbor`'s third form, under `Withbor3Side`. -/
  | withbor3Ax {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hside : Withbor3Side x T₁ T₂) :
      DerivesIn Δ Γ withbor (axWithbor3Ty a x Δ.meetOfDom T₁ T₂)
  /-- `withload`, under `WithloadSide`. -/
  | withloadAx {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hside : WithloadSide x T₁ T₂) :
      DerivesIn Δ Γ withload (axWithloadTy a x Δ.meetOfDom T₁ T₂)
  | withswapAx {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) :
      DerivesIn Δ Γ withswap (axWithswapTy a T₁ T₂)

/-- `AllISide` off `Δ ⊢ @b`, `Δ ⊢ Γ` and a well-scoped `Δ`.
`[about ours: the `∀I` side, from [TR] p. 2's `Δ ⊢ T`]` -/
theorem allISide_of_scopedB {Δ : LifeCtx} {Γ : Ctx Ty} {x : LifeVar} {b : Lifetime.Life}
    (hΔ : Δ.Ok) (hx : Δ.find? x = none) (hb : b.wf Δ = true)
    (hΓ : Ctx.ScopedB Δ Γ) : AllISide Δ Γ x b :=
  ⟨Lifetime.Life.mentions_false_of_wf hx hb,
    fun _ _ hy => hΔ.bound_mentions_false hx hy,
    fun s hs hl => not_lfree_of_scopedB hx (hΓ s hs hl)⟩

/-- `Withbor1Side` off `Δ ⊢ T₁` and `Δ ⊢ T₂`; the form asks nothing else.
`[about ours: the `withbor1` side, from [TR] p. 2's `Δ ⊢ T`]` -/
theorem withbor1Side_of_scopedB {Δ : LifeCtx} {x : LifeVar} {T₁ T₂ : Ty}
    (hx : Δ.find? x = none) (h₁ : T₁.scopedB Δ = true) (h₂ : T₂.scopedB Δ = true) :
    Withbor1Side x T₁ T₂ :=
  ⟨not_lfree_of_scopedB hx h₁, not_lfree_of_scopedB hx h₂⟩

/-- `Withbor2Side` off `Δ ⊢ T₁` and `Δ ⊢ T₂`.
`[about ours: the `withbor2` side, from [TR] p. 2's `Δ ⊢ T`]` -/
theorem withbor2Side_of_scopedB {Δ : LifeCtx} {x : LifeVar} {T₁ T₂ : Ty}
    (hx : Δ.find? x = none) (h₁ : T₁.scopedB Δ = true) (h₂ : T₂.scopedB Δ = true) :
    Withbor2Side x T₁ T₂ :=
  ⟨not_lfree_of_scopedB hx h₁, not_lfree_of_scopedB hx h₂⟩

/-- `Withbor3Side`, the same two conditions as `Withbor2Side`.
`[about ours: the `withbor3` side, from [TR] p. 2's `Δ ⊢ T`]` -/
theorem withbor3Side_of_scopedB {Δ : LifeCtx} {x : LifeVar} {T₁ T₂ : Ty}
    (hx : Δ.find? x = none) (h₁ : T₁.scopedB Δ = true) (h₂ : T₂.scopedB Δ = true) :
    Withbor3Side x T₁ T₂ :=
  ⟨not_lfree_of_scopedB hx h₁, not_lfree_of_scopedB hx h₂⟩

/-- `WithloadSide` off `Δ ⊢ T₁`, `Δ ⊢ T₂` and 6.150's escrow, which is not one
of these.
`[about ours: the `withload` side, with its freshness from [TR] p. 2]` -/
theorem withloadSide_of_scopedB {Δ : LifeCtx} {x : LifeVar} {T₁ T₂ : Ty}
    (hesc : ∀ (δ : LSub) (vℓ : Val), RebEscrow
      (fun β v' => ⌜vℓ = v'⌝ ⋆ vDen (T₁.immReborrow (.var x)) (δ.extend x β) vℓ))
    (hx : Δ.find? x = none) (h₁ : T₁.scopedB Δ = true) (h₂ : T₂.scopedB Δ = true) :
    WithloadSide x T₁ T₂ :=
  ⟨hesc, not_lfree_of_scopedB hx h₁, not_lfree_of_scopedB hx h₂⟩

/-- Every derivation is in the regime — what `FundamentalPropertyOverRules` is
reduced to.

* The freshness half — `AllISide`'s three conjuncts and the `¬ LFree`
  conjuncts of the other four sides — is [TR] p. 2's `Δ ⊢ T` at a binder
  outside `dom(Δ)`: `allISide_of_scopedB` and the four beside it derive them
  from `Ty.scopedB` and `Lifetime.LifeCtx.Ok`.  `Derives` consumes that judgment
  at no constructor (definition row 2.19); `not_everyDerivationWf` is a
  `Derives.allI` node whose bound mentions its own binder.
* `WithloadSide`'s escrow is [TR] 6.150's inheritance from 6.55.

Not derived here, and no obstruction to it verified.
`[about ours: the residual of `Fig16.LogRel.FundamentalPropertyOverRules`
over `fundamental_in`]` -/
def EveryDerivationInRegime : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), Derives Δ Γ e T → DerivesIn Δ Γ e T

/-- Peel the `[@a]` modalities off the head of a type. -/
def stripBox : Ty → Ty
  | .box _ T => stripBox T
  | .bang T => stripBox T
  | T => T

theorem aux : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}, DerivesIn Δ Γ e T →
    e = .val (.lam (.val .unit)) → stripBox T ≠ .all 0 (.var 0) .unit := by
  intro Δ Γ e T h
  induction h with
  | var _ => intro he; cases he
  | unitI _ => intro he; cases he
  | unitE _ _ _ _ _ => intro he; cases he
  | tensorI _ _ _ _ _ => intro he; cases he
  | tensorE _ _ _ _ _ => intro he; cases he
  | sumI₁ _ _ => intro he; cases he
  | sumI₂ _ _ => intro he; cases he
  | sumE _ _ _ _ _ _ _ => intro he; cases he
  | lolliI _ _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | lolliE _ _ _ _ _ => intro he; cases he
  | @allI Δ' Γ' x b S e' T' hx hd hside ih =>
      intro _ hT
      have hT' : Ty.all x b T' = Ty.all 0 (Lifetime.Life.var 0) Ty.unit := hT
      cases hT'
      exact absurd hside.1 (by decide)
  | allE _ _ _ => intro he; cases he
  | boxIctx _ _ ih => intro he hT; exact ih he (by simpa [stripBox] using hT)
  | boxE _ ih => intro he hT; exact ih he (by simpa [stripBox] using hT)
  | immSub _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | mutSub _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | allocAx _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | freeAx _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | swapAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axSwapTy])
  | copyAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axCopyTy])
  | forgetImmAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axForgetImmTy])
  | forgetMutAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axForgetMutTy])
  | forgetUnkAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axForgetUnkTy])
  | withbor1Ax _ _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox, axWithbor1Ty])
  | withbor2Ax _ _ _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox, axWithbor2Ty])
  | withbor3Ax _ _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox, axWithbor3Ty])
  | withloadAx _ _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox, axWithloadTy])
  | withswapAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axWithswapTy])

/-- The witness `Derives` derivation: `∅; • ⊢ λ().() : ∀('a ⊏ 'a). 1`. -/
theorem witness : Derives ⟨[]⟩ [] (.val (.lam (.val .unit)))
    (.all 0 (.var 0) .unit) :=
  Derives.allI (S := .unit) rfl (Derives.unitI (.cons .nil))

/-- What `FundamentalPropertyOverRules` needs beyond `fundamental`, which
concludes at a `DerivesWf` node under the hypotheses `⊧ Δ` (`Δ.Ok`) and `Δ ⊢ Γ`
(`Ctx.ScopedB`); `FundamentalPropertyOverRules` quantifies over `Derives` and
every `Δ` and `Γ` (`docs/adjudications.md` §C.26).
`[about ours: the residual of `Fig16.LogRel.FundamentalPropertyOverRules` over
`fundamental`]` -/
def EveryDerivationWf : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), Derives Δ Γ e T → DerivesWf Δ Γ e T

/-- No `DerivesWf` derivation gives `λ().()` a `∀`-type under any stack of
`[@a]`s whose binder is its own bound: `∀I` asks `Δ ⊧ @b` beside
`'a ∉ dom(Δ)`, and `@b = 'a` cannot have both. -/
theorem auxWf : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}, DerivesWf Δ Γ e T →
    e = .val (.lam (.val .unit)) → stripBox T ≠ .all 0 (.var 0) .unit := by
  intro Δ Γ e T h
  induction h with
  | var _ => intro he; cases he
  | unitI _ => intro he; cases he
  | unitE _ _ _ _ _ => intro he; cases he
  | tensorI _ _ _ _ _ => intro he; cases he
  | tensorE _ _ _ _ _ _ => intro he; cases he
  | sumI₁ _ _ => intro he; cases he
  | sumI₂ _ _ => intro he; cases he
  | sumE _ _ _ _ _ _ _ _ => intro he; cases he
  | lolliI _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | lolliE _ _ _ _ _ => intro he; cases he
  | bangLamI _ _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | bangE _ ih => intro he hT; exact ih he hT
  | copyBangAx _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | forgetBangAx _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | @bangAllI Δ' Γ' x b S e' T' _ hx hb _ _ _ =>
      intro _ hT
      have hT' : Ty.all x b T' = Ty.all 0 (Lifetime.Life.var 0) Ty.unit := hT
      cases hT'
      rw [show (Lifetime.Life.var 0).wf Δ' = (Δ'.find? 0).isSome from rfl, hx] at hb
      exact absurd hb (by decide)
  | @allI Δ' Γ' x b S e' T' hx hb _ _ _ =>
      intro _ hT
      have hT' : Ty.all x b T' = Ty.all 0 (Lifetime.Life.var 0) Ty.unit := hT
      cases hT'
      rw [show (Lifetime.Life.var 0).wf Δ' = (Δ'.find? 0).isSome from rfl, hx] at hb
      exact absurd hb (by decide)
  | allE _ _ _ => intro he; cases he
  | boxIctx _ _ ih => intro he hT; exact ih he (by simpa [stripBox] using hT)
  | boxE _ ih => intro he hT; exact ih he (by simpa [stripBox] using hT)
  | immSub _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | mutSub _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | allocAx _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | freeAx _ => intro _ hT; exact absurd hT (by simp [stripBox])
  | swapAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axSwapTy])
  | copyAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axCopyTy])
  | forgetImmAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axForgetImmTy])
  | forgetMutAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axForgetMutTy])
  | forgetUnkAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axForgetUnkTy])
  | withbor1Ax _ _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox, axWithbor1Ty])
  | withbor2Ax _ _ _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox, axWithbor2Ty])
  | withbor3Ax _ _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox, axWithbor3Ty])
  | withloadAx _ _ _ _ => intro _ hT; exact absurd hT (by simp [stripBox, axWithloadTy])
  | withswapAx _ => intro _ hT; exact absurd hT (by simp [stripBox, axWithswapTy])

end BoCa.Fig16.LogRel

end
