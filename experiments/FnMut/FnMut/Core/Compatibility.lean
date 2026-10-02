import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.S6_5_NonStandardEntailments.Lemmas
import Support.Dynamics.Machine
import Support.Lifetimes.Interpretation
import Support.Lifetimes.Substitution
import Support.Lifetimes.Terms
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Compatibility
import Support.LogicalRelation.Facts
import Support.Model.Composition
import Support.Model.Lifetimes
import Support.Model.Notation
import Support.Model.Propositions
import Support.Model.ReborrowFrame
import Support.Model.Singletons
import Support.Model.Strata
import Support.Model.UpdateFrame
import Support.Statics.Contexts
import Support.Statics.Presupposed
import Support.Syntax.Terms
import FnMut.Core.FrameRules
import FnMut.Core.Images
import FnMut.Core.Reborrow
import FnMut.Core.ReborrowShapes
import FnMut.Core.FrameRecords
import FnMut.Core.Relation
import FnMut.Core.RelationFacts
import FnMut.Core.World
import FnMut.Core.Wp
import FnMut.Core.Persistent

/-!
# Core — Compatibility  `[spec §3]`

`Support/TypedWorld`'s layer `Compatibility`, with records typed at `VTy`.  The compatibility lemmas at `SemV`: `𝒢X⟦Γ⟧` split along the context, `wpTS` monotone and bound with a frame, the stratified connectives, and 6.152–6.176 as `_compatX`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem gSepC_local {ls ls' : List SRec} {δ : LSub} :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}, Ext ls ls' ρ →
      gSepC ls δ Γ γ ρ → gSepC ls' δ Γ γ ρ
  | [], _, _, _, h => h
  | _ :: _, [], _, _, h => h
  | s :: Γ, v :: γ, ρ, hk, h => by
      unfold gSepC at h ⊢
      split
      · rename_i hl
        rw [if_pos hl] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact ⟨ρ₁, ρ₂, hc, vC_local true s.ty (hk.left hc) h₁, gSepC_local (hk.right hc) h₂⟩
      · rename_i hl
        rw [if_neg hl] at h
        exact gSepC_local hk h

theorem gDenC_local {ls ls' : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val}
    {ρ : WRes} (hk : Ext ls ls' ρ) (h : gDenC ls δ Γ γ ρ) : gDenC ls' δ Γ γ ρ := by
  obtain ⟨ρ₁, ρ₂, hc, hp, h₂⟩ := h
  exact ⟨ρ₁, ρ₂, hc, hp, gSepC_local (hk.right hc) h₂⟩

theorem gDenC_iff {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes} :
    gDenC ls δ Γ γ ρ ↔ (Ctx.LiveWithin Γ γ ∧ gSepC ls δ Γ γ ρ) := pure_sep_iff

theorem gDenC_mk {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (hlen : Ctx.LiveWithin Γ γ) (hg : gSepC ls δ Γ γ ρ) : gDenC ls δ Γ γ ρ :=
  gDenC_iff.mpr ⟨hlen, hg⟩

/-- `Γ = Γ₁, Γ₂` splits the context relation; a persistent slot goes to both halves.  `[spec §10]` -/
theorem gDenC_split {ls : List SRec} {δ : LSub} {Γ Γ₁ Γ₂ : Ctx VTy} (hsp : Ctx.SplitP Γ Γ₁ Γ₂)
    {γ : List Val} {ρ : WRes} (hg : gDenC ls δ Γ γ ρ) :
    (gDenC ls δ Γ₁ γ ⋆ gDenC ls δ Γ₂ γ) ρ := by
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp hg
  obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := gSepC_splitP hsp hs
  exact ⟨ρ₁, ρ₂, hc, gDenC_mk (hsp.liveWithin hlen).1 h₁, gDenC_mk (hsp.liveWithin hlen).2 h₂⟩

/-- `wpTS` is monotone in its postcondition. -/
theorem wpTS_mono {ls : List SRec} {e : Expr} {P Q : List SRec → Val → WProp}
    (h : ∀ ls' v, Entails (P ls' v) (Q ls' v)) : Entails (wpTS ls e P) (wpTS ls e Q) := by
  intro ρ hw ρf fρ ps hf hc hT htg A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉, hA, hB,
    hT', htg', hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, h₈, h₉, hA, hB,
    hT', htg', hps, hls, h ls' v ρ' hC⟩

/-- Bind on the sub-expression, frame the rest through the run, then weaken — 6.135 and
6.146 at `wpTS`, the move `[TR]` §6.8 makes at every rule with a context split.  The frame is
carried to the returned list by `hR`. -/
theorem wpTS_bind_frame (K : Kont) (e : Expr) (ls : List SRec) (P : List SRec → Val → WProp)
    (R : List SRec → WProp) (Q : List SRec → Val → WProp)
    (hR : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (R ls) (R ls'))
    (h : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ v,
      Entails ((P ls' v) ⋆ R ls') (wpTS ls' (K.plug (.val v)) Q)) :
    Entails ((wpTS ls e P) ⋆ R ls) (wpTS ls (K.plug e) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, hwp, hRρ⟩
  refine wpTS_bind K e ls Q ρ (wpTS_ramify ls e P (fun ls' v => wpTS ls' (K.plug (.val v)) Q) ρ ?_)
  refine ⟨ρ₁, ρ₂, hc, hwp, ?_⟩
  intro ls' hls v σ₁ σ₂ hP hcs
  exact h ls' hls v σ₂ ⟨σ₁, ρ₂, ResU.CompS.comm hcs, hP, hR ls' hls ρ₂ hRρ⟩

/-- A frame valid at `vC` is carried to a list with the same members. -/
theorem vP_same {T : VTy} {ls ls' : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : ∀ x, x ∈ ls' ↔ x ∈ ls) (hv : vP T ls δ v ρ) : vP T ls' δ v ρ :=
  vC_local true T (ext_of_same h ρ) hv

theorem gDenC_same {ls ls' : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (h : ∀ x, x ∈ ls' ↔ x ∈ ls) (hg : gDenC ls δ Γ γ ρ) : gDenC ls' δ Γ γ ρ :=
  gDenC_local (ext_of_same h ρ) hg

/-- An `imm` cell at the observable view is an `imm` cell whose payload is observable at the
current list (`ptoImmO_read`). -/
theorem ptoImmO_toImm {l : Loc} {α : Life} {ls : List SRec} {S : VTy} {δ : LSub} {ρ : WRes}
    (h : ptoImmS l α ls (fun ls₀ => vC false S ls₀ δ) ρ) :
    ptoImm l α (fun u => vC false S ls δ u) ρ := by
  obtain ⟨s, u, σ, hs, hρ, hαs, hP⟩ := ptoImmO_read h
  exact ⟨s, u, σ, hs, hρ, hP, hαs⟩

/-- The chooser with the loaded value pinned — 6.134's `⌜x = y⌝` carried through the
chooser. -/
theorem rebChooseTW_pin {ls : List SRec} {l : Loc} {R : Val → WRes → Prop}
    {P₀ P : Life → Val → WProp} (c : Val) (h : RebChooseTW ls l R P₀ P) :
    RebChooseTW ls l (fun w σ => w = c ∧ R w σ) P₀ (fun β w χ => (⌜c = w⌝ ⋆ P β w) χ) := by
  intro W F χ₀ σ ps β w s hs hT htag hβ hW hR hreb₀ hP₀
  obtain ⟨hwc, hR'⟩ := hR
  obtain ⟨χ, hreb, hPχ, hag, hEF, hEI, hen, hex⟩ := h W F χ₀ σ ps β w s hs hT htag hβ hW hR' hreb₀ hP₀
  exact ⟨χ, hreb, pure_sep_mk hwc.symm hPχ, hag, hEF, hEI, hen, hex⟩

/-- `[TR]` 6.114 (`I ⊒`) at `ptoImmS`. -/
theorem ptoImmS_antitone {l : Loc} {α β : Life} (h : β ⊑ α) {ls : List SRec}
    {P : List SRec → Val → WProp} {ρ : WRes} (hp : ptoImmS l α ls P ρ) : ptoImmS l β ls P ρ := by
  obtain ⟨s, u, σ, hs, ls₀, hρ, hP, hα, hls₀⟩ := hp
  exact ⟨s, u, σ, hs, ls₀, hρ, hP, le_trans h hα, hls₀⟩

/-- `[TR]` 6.118 (`M ⊒`) at `ptoMutS`. -/
theorem ptoMutS_antitone {l : Loc} {α β : Life} (h : β ⊑ α) {ls : List SRec}
    {P : List SRec → Val → WProp} {ρ : WRes} (hp : ptoMutS l α ls P ρ) : ptoMutS l β ls P ρ := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, hab, hρ, hQ, hls₀, hunif⟩ := hp
  exact ⟨b, u, σ, hσ, Q, hw, ls₀, le_trans h hab, hρ, hQ, hls₀, hunif⟩

/-- `[TR]` 6.116 (`I-dup`) at `ptoImmS`: the composite is the same cell (6.43), so each
copy carries the same stratified payload. -/
theorem ptoImmS_dup {l : Loc} {α : Life} {ls : List SRec} {P : List SRec → Val → WProp}
    {ρ : WRes} (hp : ptoImmS l α ls P ρ) :
    ∃ τ₁ τ₂, ResU.CompS τ₁ τ₂ ρ ∧ ptoImmS l α ls P τ₁ ∧ ptoImmS l α ls P τ₂ := by
  obtain ⟨s, v, σ, hs, ls₀, rfl, hP, hα, hls₀⟩ := hp
  have h₃ : σ.InStratum (s ∪ s).join := ResU.InStratum.sup hs hs
  have e : CellU.immOf (s ∪ s) v σ h₃ = CellU.immOf s v σ hs :=
    CellU.immOf_congr (LSet.union_self s) rfl rfl h₃ hs
  have hcomp := ResU.compS_single_imm l s s v σ hs hs h₃
  rw [e] at hcomp
  exact ⟨_, _, hcomp, ⟨s, v, σ, hs, ls₀, rfl, hP, hα, hls₀⟩, ⟨s, v, σ, hs, ls₀, rfl, hP, hα, hls₀⟩⟩

/-- A stratified `imm` cell is an `imm` cell (for `wp-I-forget`). -/
theorem ptoImmS_ptoImm {l : Loc} {α : Life} {ls : List SRec} {P : List SRec → Val → WProp}
    {ρ : WRes} (hp : ptoImmS l α ls P ρ) : ptoImm l α (fun _ _ => True) ρ := by
  obtain ⟨s, v, σ, hs, ls₀, hρ, -, hα, -⟩ := hp
  exact ⟨s, v, σ, hs, hρ, trivial, hα⟩

/-- A stratified `mut` cell is a `mut` cell (for `wp-M-forget`). -/
theorem ptoMutS_ptoMut {l : Loc} {α : Life} {ls : List SRec} {P : List SRec → Val → WProp}
    {ρ : WRes} (hp : ptoMutS l α ls P ρ) : ∃ P', ptoMut l α P' ρ := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, hab, hρ, -, -, -⟩ := hp
  exact ⟨ofS Q, b, u, σ, hσ, Q, hw, hab, hρ, rfl⟩

theorem gSepC_congr {ls : List SRec} {δ₁ δ₂ : LSub} : ∀ {Γ : Ctx VTy} {γ : List Val},
    (∀ s ∈ Γ, s.live = true → vP s.ty ls δ₁ = vP s.ty ls δ₂) →
    gSepC ls δ₁ Γ γ = gSepC ls δ₂ Γ γ := by
  intro Γ
  induction Γ with
  | nil => intro γ _; cases γ <;> rfl
  | cons s Γ' ih =>
      intro γ h
      cases γ with
      | nil => rfl
      | cons v γ' =>
          have htail : ∀ t ∈ Γ', t.live = true → vP t.ty ls δ₁ = vP t.ty ls δ₂ :=
            fun t ht => h t (List.mem_cons_of_mem _ ht)
          by_cases hl : s.live
          · simp only [gSepC, if_pos hl, ih htail, h s (List.mem_cons_self ..) hl]
          · simp only [gSepC, if_neg hl, ih htail]

/-- 6.62's fold over `⊛_{x∈dom(Γ)}` at `vC`: `[]⋆` at each live slot and 6.60
(`vC_outlives`) at its clause. -/
theorem gSepC_outlives {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life} {ls : List SRec}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes},
      (∀ s ∈ Γ, s.live = true → VOutlives Δ a s.ty) →
      gSepC ls δ Γ γ ρ → BoLo.Outlives ρ α := by
  intro Γ
  induction Γ with
  | nil =>
      rintro γ ρ - ⟨rfl, -⟩
      exact ResU.inStratum_empty α
  | cons s Γ ih =>
      intro γ ρ hT hg
      cases γ with
      | nil =>
          obtain ⟨rfl, -⟩ := hg
          exact ResU.inStratum_empty α
      | cons v γ =>
          have hT' : ∀ t ∈ Γ, t.live = true → VOutlives Δ a t.ty :=
            fun t ht => hT t (List.mem_cons.mpr (Or.inr ht))
          by_cases hl : s.live = true
          · rw [gSepC, if_pos hl] at hg
            obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
            exact (outlives_comp hc α).mpr
              ⟨vC_outlives hδ ha (hT s (List.mem_cons.mpr (Or.inl rfl)) hl) true ls v ρ₁ hv,
               ih hT' hrest⟩
          · rw [gSepC, if_neg hl] at hg
            exact ih hT' hg

/-- `Δ ⊢ T` gives `AdmWf T δ` at `δ ⊨ Δ`: every variable free in a scoped type is in
`dom(Δ)`, and `δ ⊨ Δ` interprets it.  `[about ours: [TR] p. 2's `Δ ⊢ T` at the record
premise `TW.immFrame` reads]` -/
theorem admWf_of_vScoped {Δ : LifeCtx} {δ : LSub} {T : VTy} (hsc : VScoped Δ T)
    (hδ : Δ.Models δ) : AdmWf T δ := by
  intro y hy
  obtain ⟨u, hu⟩ := hsc y hy
  obtain ⟨m, k, hm, -⟩ := hδ y u hu
  exact ⟨m, hm⟩

/-- `𝒢X⟦∅⟧(ls)δ([])` holds of `∅`. -/
theorem gDenC_nil (ls : List SRec) (δ : LSub) : gDenC ls δ [] [] (PMap.empty : WRes) :=
  gDenC_iff.mpr ⟨by simp [Ctx.LiveWithin], by simp only [gSepC]; exact ⟨rfl, trivial⟩⟩

/-- `∅` is well scoped. -/
theorem ok_empty : LifeCtx.empty.Ok := rfl

/-! ### Lemma 6.175 (withload-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.175 (`withload-compat`, pp. 47–48) at the stratified judgment:

        Δ ⊨X withload : Imm @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b] T₂) ⊸ T₂

The library's `withload_compat`, step for step, with no `hesc`.  "Apply theorem 6.150" is
`wpTS_reborrow`, whose chooser is read off the `Coh` the program's own `vC⟦Imm @a T₁⟧` carries
at the loaded cell.  `[restricted: `hfree₁` (6.132's *"if `'a` not free in `T`"*) and `hfree₂`
(p. 48's *"because `'b` does not occur free in `T₂`"*), as `withload_compat`]` -/
theorem withload_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {T₁ T₂ : VTy}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none)
    (hfree₁ : ¬ VFree x T₁) (hfree₂ : ¬ VFree x T₂) :
    SemV Δ Γ withload (axWithloadTy a x Δ.meetOfDom T₁ T₂) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls withload _ _
  refine wpTS_val _ _ _ _ ?_
  -- "Unfold 𝒱⟦⊸⟧.  Let `v` be arbitrary.  Apply `wp⊸` and `wp-val`."
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  -- "Unfold 𝒱⟦Imm⟧.  There exists some `ℓ` such that `v = ℓ`."
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, v₁ = Val.loc ℓ := by
    obtain ⟨α₀, -, ℓ, hs₁⟩ := hv₁
    exact ⟨ℓ, (pure_sep_iff.mp hs₁).1.1⟩
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.app (.app BoCa.v0 unit') (.app load' BoCa.v1))))
      = Expr.val (Val.lam (.app (.app BoCa.v0 unit') (eLoad ℓ))) := by
    simp [eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit', load']
  refine wpTS_lolli _ _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  -- "Unfold 𝒱⟦⊸⟧.  Let `v_f` be arbitrary.  Apply `wp⊸`."
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf (Expr.app (.app BoCa.v0 unit') (eLoad ℓ))
      = Expr.app (.app (.val vf) (.val .unit)) (eLoad ℓ) := by
    simp [eLoad, Expr.subst, BoCa.v0, unit']
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  -- the borrow, carried to the callback's list
  have hv₂ : vP (.imm a T₁) ls₂ δ (Val.loc ℓ) ρ₁ := vC_local true _ hext₂ hv₁
  obtain ⟨α₀, ha, ℓ', hs₂⟩ := hv₂
  obtain ⟨⟨hℓ', hcoh⟩, himm⟩ := pure_sep_iff.mp hs₂
  have hℓℓ : ℓ' = ℓ := by
    have := congrArg Subtype.val hℓ'; simpa using this.symm
  subst hℓℓ
  -- "Apply `wp-bind`", with continuation `v_ℓ. v_f () v_ℓ`
  refine wpTS_bind (.appR (.app (.val vf) (.val .unit)) .hole) (eLoad ℓ') ls₂ _ τ ?_
  -- "Apply `wp-load-I`.  Let `v_ℓ` be arbitrary."
  refine wpTS_load_I ls₂ ℓ' α₀ (fun u => vC false T₁ ls₂ δ u) _ τ
    ⟨ρ₁, ρ₂, hc₂, ptoImmO_toImm himm, ?_⟩
  intro vℓ ρc ρcomp hcell hccomp
  simp only [Kont.plug]
  -- The chooser, read off the program's `Coh` at `ℓ`.
  have hesc : RebChooseTW ls₂ ℓ'
      (fun w σ => w = vℓ ∧ vC false T₁ ls₂ δ w σ)
      (fun β w χ => vShape (T₁.immReborrow (.var x)) (δ.extend x β) w χ)
      (fun β w χ => (⌜vℓ = w⌝ ⋆ vC true (T₁.immReborrow (.var x)) ls₂ (δ.extend x β) w) χ) := by
    -- `Coh` up to `TyEq`: the record's type `S₀` at its `δ₀`, read against `T₁` at `δ`
    obtain ⟨S₀, δ₀, he, hc⟩ := hcoh
    have hx₀ : ¬ VFree S₀.lifeBound S₀ := fun h => lt_irrefl _ (lt_vLifeBound h)
    have heβ : ∀ β : Life, TyEq (T₁.immReborrow (.var x)) (δ.extend x β)
        (S₀.immReborrow (.var S₀.lifeBound)) (δ₀.extend S₀.lifeBound β) := fun β =>
      TyEq.immReborrow (by rw [interp_ext_self, interp_ext_self])
        (TyEq.extend_left hx₀ β (TyEq.extend_left hfree₁ β he).symm).symm
    have eR : vC false T₁ ls₂ δ = vC false S₀ ls₂ δ₀ := vC_tyEq he false ls₂
    have eP₀ : ∀ β : Life, vShape (T₁.immReborrow (.var x)) (δ.extend x β)
        = vShape (S₀.immReborrow (.var S₀.lifeBound)) (δ₀.extend S₀.lifeBound β) :=
      fun β => vShape_tyEq (heβ β)
    have eP : ∀ β : Life, vC true (T₁.immReborrow (.var x)) ls₂ (δ.extend x β)
        = vC true (S₀.immReborrow (.var S₀.lifeBound)) ls₂ (δ₀.extend S₀.lifeBound β) :=
      fun β => vC_tyEq (heβ β) true ls₂
    simp only [eR, eP₀, eP]
    rcases hc with ⟨r, hr, rfl, rfl, hag⟩ | ⟨r, hr, p, u, hch, hag⟩
    · exact rebChooseTW_pin vℓ (rebChooseTW_top hr hag hx₀)
    · exact rebChooseTW_pin vℓ (rebChooseTW_deep hr hch hag hx₀)
  -- "Apply `↺V₂`" (at the shape relation, on the observable payload) and "Apply theorem 6.134":
  -- the cell family 6.150 asks for.
  have hcell' : ptoImm ℓ' α₀ (fun v σ => (v = vℓ ∧ vC false T₁ ls₂ δ v σ) ∧
      fresh (fun b => reborrow b (vShape (T₁.immReborrow (.var x)) (δ.extend x b) v)) σ) ρc := by
    refine ptoImm_mono (fun u σ h => ?_) ρc hcell
    obtain ⟨he, hobs⟩ := pure_sep_iff.mp h
    subst he
    exact ⟨⟨rfl, hobs⟩, six132_shape_fresh hfree₁ δ vℓ σ (vC_vShape false T₁ hobs)⟩
  -- "Apply theorem 6.150"
  refine wpTS_reborrow ls₂ ℓ' α₀ _ _ _ _ (fun ls' => vP T₂ ls' δ) hesc ρcomp
    ⟨ρc, ρ₂, ResU.CompS.comm hccomp, hcell', ?_⟩
  -- "Apply `ИR` on the left-hand side.  By `И-mono`, let `β ⊏ ⨅δ` be arbitrary."
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨g₂, hg₂⟩ := ResU.exists_stratum ρ₂
  refine ⟨m ⊓ g₂, fun β hβ => ⟨?_, hg₂.mono (le_of_lt (lt_of_lt_of_le hβ inf_le_right))⟩⟩
  -- "Apply `─⋆R`"; "Substitute `v_ℓ` for `v′`", which the pin does
  intro v σ ρpc hP hpc
  obtain ⟨hvv, hreb⟩ := pure_sep_iff.mp hP
  subst hvv
  -- the callback's `𝒱⟦∀⟧` at `β ⊏ ⊓Δδ`: the thunk `v_f ()` runs at `δ['x↦β]`
  have hlt : LtLife δ Δ.meetOfDom β := ⟨m, hm, lt_of_lt_of_le hβ inf_le_left⟩
  have hwpf := hvf ls₂ (Ext.refl _ _) β PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  -- "Fold ℰ⟦−⟧": `wp-bind` on the thunk, framing the reborrow through
  refine wpTS_bind_frame (.appL .hole vℓ) (.app (.val vf) (.val .unit)) ls₂
    (fun ls' => vP (.lolli (VTy.immReborrow (.var x) T₁) (.box (.var x) T₂)) ls' (δ.extend x β))
    (fun ls' => vP (VTy.immReborrow (.var x) T₁) ls' (δ.extend x β) vℓ) _
    (fun ls' hls ρ h => vP_same hls h) ?_ ρpc ⟨ρ₂, σ, hpc, hwpf, hreb⟩
  rintro ls' - vg σ' ⟨σ₁, σ₂, hcσ, hvg, hR⟩
  simp only [Kont.plug]
  -- "Follows from `∀E-compat` and `⊸E-compat`": the callback's `⊸` at the reborrow, then
  -- `wp-mono` on its postcondition
  refine wpTS_mono (fun ls'' v' ρ' hb => ?_) σ' (hvg ls' (Ext.refl _ _) vℓ σ₂ σ' hR hcσ)
  obtain ⟨α', hα', hbox⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  -- "Have `𝒱⟦T₂⟧δ = 𝒱⟦T₂⟧δ['b↦β]` because `'b` does not occur free in `T₂`."
  rw [vC_extend_of_not_free hfree₂] at hbox
  exact hbox

/-! ### Lemma 6.152 (id-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.152 (`id-compat`) at `SemV`.  `[as printed]`. -/
theorem id_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {T : VTy}
    (h : Ctx.SoloP Γ i T) : SemV Δ Γ (.var i) T := by
  intro δ γ ls ρ _ hg
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp hg
  obtain ⟨v, hv, hval⟩ := gSepC_soloP h (h.lt_of_liveWithin hlen) hs
  have he : substAll γ (.var i) = .val v := by
    show Expr.psub 0 γ (.var i) = _
    simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv, Val.shift_zero]
  rw [he]
  exact wpTS_val ls v _ ρ hval

/-! ### Lemma 6.153 (1I-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.153 (`1I-compat`) at `SemV`.  `[as printed]`. -/
theorem unitI_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (h : Ctx.DeadP Γ) :
    SemV Δ Γ (.val .unit) .unit := by
  intro δ γ ls ρ _ hg
  obtain ⟨-, hs⟩ := gDenC_iff.mp hg
  rw [gSepC_deadP h hs]
  exact wpTS_val ls Val.unit _ _ ⟨rfl, rfl⟩

/-! ### Lemma 6.154 (1E-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.154 (`1E-compat`) at `SemV`.  `[as printed]`. -/
theorem unitE_compatX {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e₁ e₂ : Expr} {T : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (h₁ : SemV Δ Γ₁ e₁ .unit) (h₂ : SemV Δ Γ₂ e₂ T) :
    SemV Δ Γ (.seq e₁ e₂) T := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine wpTS_bind_frame (.seq .hole (substAll γ e₂)) (substAll γ e₁) ls
    (fun ls' => vP .unit ls' δ) (fun ls' => gDenC ls' δ Γ₂ γ) (fun ls' => vP T ls' δ)
    (fun ls' hls ρ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, h₁ δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, ⟨rfl, rfl⟩, hg₂'⟩
  rw [eq_of_compS_empty_left hcσ]
  exact wpTS_1 ls' _ _ σ₂ (h₂ δ γ ls' σ₂ hδ hg₂')

/-! ### Lemma 6.155 (⊗I-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.155 (`⊗I-compat`) at `SemV`.  `[as printed]`. -/
theorem tensorI_compatX {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e₁ e₂ : Expr} {T₁ T₂ : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (h₁ : SemV Δ Γ₁ e₁ T₁) (h₂ : SemV Δ Γ₂ e₂ T₂) :
    SemV Δ Γ (.pair e₁ e₂) (.tensor T₁ T₂) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine wpTS_bind_frame (.pairL .hole (substAll γ e₂)) (substAll γ e₁) ls
    (fun ls' => vP T₁ ls' δ) (fun ls' => gDenC ls' δ Γ₂ γ) (fun ls' => vP (.tensor T₁ T₂) ls' δ)
    (fun ls' hls ρ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, h₁ δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v₁ σ ⟨σ₁, σ₂, hcσ, hv₁, hg₂'⟩
  refine wpTS_bind_frame (.pairR v₁ .hole) (substAll γ e₂) ls'
    (fun ls'' => vP T₂ ls'' δ) (fun ls'' => vP T₁ ls'' δ v₁) (fun ls'' => vP (.tensor T₁ T₂) ls'' δ)
    (fun ls'' hls ρ h => vP_same hls h) ?_ σ
    ⟨σ₂, σ₁, ResU.CompS.comm hcσ, h₂ δ γ ls' σ₂ hδ hg₂', hv₁⟩
  rintro ls'' - v₂ τ ⟨τ₁, τ₂, hcτ, hv₂, hv₁'⟩
  exact wpTS_val ls'' (.pair v₁ v₂) _ τ
    ⟨v₁, v₂, pure_sep_mk rfl ⟨τ₂, τ₁, ResU.CompS.comm hcτ, hv₁', hv₂⟩⟩

/-! ### Lemma 6.156 (⊗E-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.156 (`⊗E-compat`) at `SemV`.  `[as printed]`. -/
theorem tensorE_compatX {Δ : LifeCtx} {Γ Γp Γb : Ctx VTy} {ep eb : Expr}
    {T₁ T₂ T : VTy} (hsp : Ctx.SplitP Γ Γp Γb)
    (h₁ : SemV Δ Γp ep (.tensor T₁ T₂))
    (h₂ : SemV Δ (⟨T₂, true⟩ :: ⟨T₁, true⟩ :: Γb) eb T) :
    SemV Δ Γ (.letpair ep eb) T := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine wpTS_bind_frame (.letpair .hole (Expr.psub 2 γ eb)) (substAll γ ep) ls
    (fun ls' => vP (.tensor T₁ T₂) ls' δ) (fun ls' => gDenC ls' δ Γb γ) (fun ls' => vP T ls' δ)
    (fun ls' hls ρ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, h₁ δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, hpair, hg₂'⟩
  obtain ⟨w₁, w₂, hs⟩ := hpair
  obtain ⟨rfl, b₁, b₂, hcb, hw₁, hw₂⟩ := pure_sep_iff.mp hs
  have hsub : substAll (w₂ :: w₁ :: γ) eb
      = Expr.subst 0 w₁ (Expr.subst 0 (w₂.shift 1 0) (Expr.psub 2 γ eb)) := by
    show Expr.psub 0 (w₂ :: w₁ :: γ) eb = _
    rw [Expr.psub_cons₂ 0 w₂ w₁ γ eb, Val.shift_zero]
  refine wpTS_tensor ls' w₁ w₂ (Expr.psub 2 γ eb) _ _ ?_
  rw [← hsub]
  obtain ⟨x, hx, hxσ⟩ := compS_reassoc hcb hcσ
  obtain ⟨y, hy, hyσ⟩ := compS_lcomm hx hxσ
  refine h₂ δ (w₂ :: w₁ :: γ) ls' _ hδ (gDenC_mk ?_ ?_)
  · have := (gDenC_iff.mp hg₂').1
    simpa using this
  · exact ⟨b₂, y, hyσ, hw₂, ⟨b₁, σ₂, hy, hw₁, (gDenC_iff.mp hg₂').2⟩⟩

/-! ### Lemma 6.157 (⊕I-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.157 (`⊕I-compat`) at `SemV`, `i = 1`.  `[as printed]`. -/
theorem sumI₁_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {T₁ T₂ : VTy}
    (h : SemV Δ Γ e T₁) : SemV Δ Γ (.inj₁ e) (.sum T₁ T₂) := by
  intro δ γ ls ρ hδ hg
  refine wpTS_bind (.inj₁ .hole) (substAll γ e) ls _ ρ
    (wpTS_mono (fun ls' v σ hv => ?_) ρ (h δ γ ls ρ hδ hg))
  exact wpTS_val ls' (.inj₁ v) _ σ (Or.inl ⟨v, pure_sep_mk rfl hv⟩)

/-- `[TR]` Lemma 6.157 (`⊕I-compat`) at `SemV`, `i = 2`.  `[as printed]`. -/
theorem sumI₂_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {T₁ T₂ : VTy}
    (h : SemV Δ Γ e T₂) : SemV Δ Γ (.inj₂ e) (.sum T₁ T₂) := by
  intro δ γ ls ρ hδ hg
  refine wpTS_bind (.inj₂ .hole) (substAll γ e) ls _ ρ
    (wpTS_mono (fun ls' v σ hv => ?_) ρ (h δ γ ls ρ hδ hg))
  exact wpTS_val ls' (.inj₂ v) _ σ (Or.inr ⟨v, pure_sep_mk rfl hv⟩)

/-! ### Lemma 6.158 (⊕E-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.158 (`⊕E-compat`) at `SemV`.  `[as printed]`. -/
theorem sumE_compatX {Δ : LifeCtx} {Γ Γs Γb : Ctx VTy} {es e₁ e₂ : Expr}
    {T₁ T₂ T : VTy} (hsp : Ctx.SplitP Γ Γs Γb)
    (h₀ : SemV Δ Γs es (.sum T₁ T₂))
    (hb₁ : SemV Δ (⟨T₁, true⟩ :: Γb) e₁ T)
    (hb₂ : SemV Δ (⟨T₂, true⟩ :: Γb) e₂ T) :
    SemV Δ Γ (.case es e₁ e₂) T := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine wpTS_bind_frame (.case .hole (Expr.psub 1 γ e₁) (Expr.psub 1 γ e₂))
    (substAll γ es) ls (fun ls' => vP (.sum T₁ T₂) ls' δ) (fun ls' => gDenC ls' δ Γb γ)
    (fun ls' => vP T ls' δ) (fun ls' hls ρ h => gDenC_same hls h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, h₀ δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, hsum, hg₂'⟩
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
  rcases hsum with ⟨w, hs⟩ | ⟨w, hs⟩
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hs
    have hsub : substAll (w :: γ) e₁ = Expr.subst 0 w (Expr.psub 1 γ e₁) := by
      show Expr.psub 0 (w :: γ) e₁ = _
      rw [Expr.psub_cons 0 w γ e₁, Val.shift_zero]
    refine wpTS_sum₁ ls' w (Expr.psub 1 γ e₁) (Expr.psub 1 γ e₂) _ _ ?_
    rw [← hsub]
    exact hb₁ δ (w :: γ) ls' _ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hw, hgs⟩)
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hs
    have hsub : substAll (w :: γ) e₂ = Expr.subst 0 w (Expr.psub 1 γ e₂) := by
      show Expr.psub 0 (w :: γ) e₂ = _
      rw [Expr.psub_cons 0 w γ e₂, Val.shift_zero]
    refine wpTS_sum₂ ls' w (Expr.psub 1 γ e₁) (Expr.psub 1 γ e₂) _ _ ?_
    rw [← hsub]
    exact hb₂ δ (w :: γ) ls' _ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hw, hgs⟩)

/-! ### Lemma 6.159 (⊸I-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.159 (`⊸I-compat`) at `SemV`: the closure runs at any list `Ext`-above
the one it was made at, and its environment moves there by `gSepC_local`.  `[as printed]`. -/
theorem lolliI_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {body : Expr} {T₁ T₂ : VTy}
    (h : SemV Δ (⟨T₁, true⟩ :: Γ) body T₂) :
    SemV Δ Γ (.val (.lam body)) (.lolli T₁ T₂) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ body))) _ ρ
  refine wpTS_val _ _ _ _ ?_
  intro ls' hext v' ρ₁ ρ₂ hv' hcomp
  have hsub : substAll (v' :: γ) body = Expr.subst 0 v' (Expr.psub 1 γ body) := by
    show Expr.psub 0 (v' :: γ) body = _
    rw [Expr.psub_cons 0 v' γ body, Val.shift_zero]
  refine wpTS_lolli ls' (Expr.psub 1 γ body) v' _ _ ?_
  rw [← hsub]
  exact h δ (v' :: γ) ls' _ hδ
    (gDenC_mk (by simpa using hlen) ⟨ρ₁, ρ, ResU.CompS.comm hcomp, hv', gSepC_local hext hgs⟩)

/-! ### Lemma 6.160 (⊸E-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.160 (`⊸E-compat`) at `SemV`.  `[as printed]`. -/
theorem lolliE_compatX {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {f arg : Expr} {T₁ T₂ : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (ha : SemV Δ Γ₁ arg T₁) (hf : SemV Δ Γ₂ f (.lolli T₁ T₂)) :
    SemV Δ Γ (.app f arg) T₂ := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine wpTS_bind_frame (.appR (substAll γ f) .hole) (substAll γ arg) ls
    (fun ls' => vP T₁ ls' δ) (fun ls' => gDenC ls' δ Γ₂ γ) (fun ls' => vP T₂ ls' δ)
    (fun ls' hls ρ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, ha δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v₁ σ ⟨σ₁, σ₂, hcσ, hv₁, hg₂'⟩
  refine wpTS_bind_frame (.appL .hole v₁) (substAll γ f) ls'
    (fun ls'' => vP (.lolli T₁ T₂) ls'' δ) (fun ls'' => vP T₁ ls'' δ v₁) (fun ls'' => vP T₂ ls'' δ)
    (fun ls'' hls ρ h => vP_same hls h) ?_ σ
    ⟨σ₂, σ₁, ResU.CompS.comm hcσ, hf δ γ ls' σ₂ hδ hg₂', hv₁⟩
  rintro ls'' - v₂ τ ⟨τ₁, τ₂, hcτ, hv₂, hv₁'⟩
  exact hv₂ ls'' (Ext.refl _ _) v₁ τ₂ τ hv₁' hcτ

/-! ### Lemma 6.164 ([]E-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.164 (`[]E-compat`) at `SemV`.  `[as printed]`. -/
theorem boxE_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a : Lifetime.Life} {T : VTy}
    (h : SemV Δ Γ e (.box a T)) : SemV Δ Γ e T := by
  intro δ γ ls ρ hδ hg
  refine wpTS_mono (fun ls' v => ?_) ρ (h δ γ ls ρ hδ hg)
  rintro σ ⟨-, -, hP, -⟩
  exact hP

/-! ### Lemma 6.166 (free-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.166 (`free-compat`) at `SemV`.  `[as printed]`. -/
theorem free_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {T : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .free)) (.lolli (.ref T) T) := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  refine wpTS_val ls (Val.prim .free) _ _ ?_
  intro ls' _ v ρ₁ ρ₂ hv hcomp
  obtain ⟨ℓ, w, hs⟩ := hv
  obtain ⟨rfl, hsep⟩ := pure_sep_iff.mp hs
  rw [eq_of_compS_empty_left hcomp]
  exact wpTS_free ls' ℓ w _ _ hsep

/-! ### Lemma 6.167 (⊑imm-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.167 (`⊑imm-compat`) at `SemV`.  `CohE` does not read the index.  `[as printed]`. -/
theorem immSub_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {T : VTy}
    (h : SemV Δ Γ e (.imm b T)) (hle : Δ.EntailsLe a b) : SemV Δ Γ e (.imm a T) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, β, ha, hb, hle'⟩ := hle δ hδ
  refine wpTS_mono (fun ls' v => ?_) ρ (h δ γ ls ρ hδ hg)
  rintro σ ⟨β', hβ', ℓ, hs⟩
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  obtain ⟨hvl, himm⟩ := pure_sep_iff.mp hs
  exact ⟨α, ha, ℓ, pure_sep_mk hvl (ptoImmS_antitone hle' himm)⟩

/-! ### Lemma 6.168 (⊑mut-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.168 (`⊑mut-compat`) at `SemV`.  `[as printed]`. -/
theorem mutSub_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {T : VTy}
    (h : SemV Δ Γ e (.mut b T)) (hle : Δ.EntailsLe a b) : SemV Δ Γ e (.mut a T) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, β, ha, hb, hle'⟩ := hle δ hδ
  refine wpTS_mono (fun ls' v => ?_) ρ (h δ γ ls ρ hδ hg)
  rintro σ ⟨β', hβ', ℓ, hs⟩
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  obtain ⟨hvl, hmut⟩ := pure_sep_iff.mp hs
  exact ⟨α, ha, ℓ, pure_sep_mk hvl (ptoMutS_antitone hle' hmut)⟩

/-! ### Lemma 6.165 (alloc-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.165 (`alloc-compat`) at `SemV`.  `[as printed]`. -/
theorem alloc_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {T : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .alloc)) (.lolli T (.ref T)) := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  refine wpTS_val ls (Val.prim .alloc) _ _ ?_
  intro ls' _ v ρ₁ ρ₂ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_alloc ls' v _ _ ?_
  intro ℓ σ τ hcell hc
  exact ⟨ℓ, v, pure_sep_mk rfl ⟨σ, ρ₁, ResU.CompS.comm hc, hcell, hv⟩⟩

/-! ### Lemma 6.169 (swap-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.169 (`swap-compat`) at `SemV`: the library's `swap_compat`, step for
step.  `[as printed]`. -/
theorem swap_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {T₁ T₂ : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ swap (axSwapTy T₁ T₂) := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls swap _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, w, hs₁⟩ := hv₁
  obtain ⟨rfl, b₁, b₂, hcb, rfl, hT₁⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (elet (.app load' BoCa.v1)
          (.seq (.app (.app store' BoCa.v2) BoCa.v1) (.pair BoCa.v2 BoCa.v0)))))
      = Expr.val (Val.lam (elet (eLoad ℓ)
          (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                (.pair (.val (.loc ℓ)) BoCa.v0)))) := by
    simp [elet, eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, BoCa.v2, load', store']
  refine wpTS_lolli _ _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ v₂ ρ₂ τ hv₂ hc₂
  have hβ₂ : Expr.subst 0 v₂
        (elet (eLoad ℓ) (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                              (.pair (.val (.loc ℓ)) BoCa.v0)))
      = elet (eLoad ℓ) (.seq (eStore ℓ (v₂.shift 1 0)) (.pair (.val (.loc ℓ)) BoCa.v0)) := by
    simp [elet, eLoad, eStore, Expr.subst, BoCa.v0, BoCa.v1, store']
  refine wpTS_lolli _ _ v₂ _ _ ?_
  rw [hβ₂]
  -- the old payload, carried to the callback's list
  have hT₁' : vP T₁ ls₂ δ w b₂ := vC_local true T₁ (hext₂.right hcb) hT₁
  obtain ⟨s, hs, hτ⟩ := compS_reassoc hcb hc₂
  refine wpTS_bind (.appR (.val (.lam _)) .hole) (eLoad ℓ) ls₂ _ τ ?_
  refine wpTS_load ls₂ ℓ w _ τ ⟨_, s, hτ, rfl, ?_⟩
  intro ρ' σ' hp' hc'
  subst hp'
  simp only [Kont.plug]
  have hβ₃ : Expr.subst 0 w
        (Expr.seq (eStore ℓ (v₂.shift 1 0)) (.pair (.val (.loc ℓ)) BoCa.v0))
      = Expr.seq (eStore ℓ v₂) (.pair (.val (.loc ℓ)) (.val w)) := by
    simp [eStore, Expr.subst, BoCa.v0,
      Expr.subst_shift 0 0 0 w v₂.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  refine wpTS_lolli _ _ w _ _ ?_
  rw [hβ₃]
  refine wpTS_bind (.seq .hole (.pair (.val (.loc ℓ)) (.val w))) (eStore ℓ v₂) ls₂ _ _ ?_
  refine wpTS_store ls₂ ℓ w v₂ _ _ ⟨_, s, ResU.CompS.comm hc', rfl, ?_⟩
  intro ρ₃ σ₃ hp₃ hc₃
  subst hp₃
  simp only [Kont.plug]
  refine wpTS_1 _ _ _ _ ?_
  refine wpTS_val ls₂ (.pair (.loc ℓ) w) _ _ ?_
  obtain ⟨R, hR, hb₂R⟩ := compS_reassoc hs hc₃
  exact ⟨.loc ℓ, w, pure_sep_mk rfl
    ⟨R, b₂, ResU.CompS.comm hb₂R,
      ⟨ℓ, v₂, pure_sep_mk rfl ⟨_, ρ₂, ResU.CompS.comm hR, rfl, hv₂⟩⟩, hT₁'⟩⟩

/-! ### Lemma 6.170 (copy-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.170 (`copy-compat`) at `SemV`: `I-Dup` at the stratified cell, and
`CohE` copied with the value.  `[as printed]`. -/
theorem copy_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {T : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ copy (axCopyTy a T) := by
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
  obtain ⟨α, ha, ℓ, hs⟩ := hv
  obtain ⟨hvl, himm⟩ := pure_sep_iff.mp hs
  obtain ⟨τ₁, τ₂, hc, h₁, h₂⟩ := ptoImmS_dup himm
  exact ⟨v, v, pure_sep_mk rfl
    ⟨τ₁, τ₂, hc, ⟨α, ha, ℓ, pure_sep_mk hvl h₁⟩, ⟨α, ha, ℓ, pure_sep_mk hvl h₂⟩⟩⟩

/-! ### Lemma 6.171 (forget-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.171 (`forget-compat`) at `SemV`, `B = Imm @a T`.  `[as printed]`. -/
theorem forgetImm_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {T : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ forget (axForgetImmTy a T) := by
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
  obtain ⟨α, -, ℓ, hs⟩ := hv
  obtain ⟨-, himm⟩ := pure_sep_iff.mp hs
  exact wpTS_I_forget ls' ℓ α _ _ _ _
    ⟨_, PMap.empty, ResU.comp_empty_right _, ptoImmS_ptoImm himm,
      wpTS_val ls' .unit _ _ ⟨rfl, rfl⟩⟩

/-- `[TR]` Lemma 6.171 (`forget-compat`) at `SemV`, `B = Mut @a T`.  `[as printed]`. -/
theorem forgetMut_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {T : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ forget (axForgetMutTy a T) := by
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
  obtain ⟨α, -, ℓ, hs⟩ := hv
  obtain ⟨-, hmut⟩ := pure_sep_iff.mp hs
  obtain ⟨P', hmut'⟩ := ptoMutS_ptoMut hmut
  exact wpTS_M_forget ls' ℓ α P' _ _ _
    ⟨_, PMap.empty, ResU.comp_empty_right _, hmut', wpTS_val ls' .unit _ _ ⟨rfl, rfl⟩⟩

/-- `[TR]` Lemma 6.171 (`forget-compat`) at `SemV`, `B = Unk`.  `[as printed]`. -/
theorem forgetUnk_compatX {Δ : LifeCtx} {Γ : Ctx VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ forget axForgetUnkTy := by
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
  obtain ⟨rfl, -⟩ := hv
  exact wpTS_val ls' .unit _ _ ⟨rfl, rfl⟩

/-! ### Lemma 6.162 (∀E-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.162 (`∀E-compat`) at `SemV`: `Δ-subst` is `vC_tyEq` at
`TyEq.instLife`.  `[as printed]`. -/
theorem allE_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {x : LifeVar}
    {b : Lifetime.Life} {T : VTy} {a : Lifetime.Life}
    (h : SemV Δ Γ e (.all x b T)) (hlt : Δ.EntailsLt a b) :
    SemV Δ Γ (.app e (.val .unit)) (VTy.instLife x a T) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, β, ha, hb, hab⟩ := hlt δ hδ
  have hsub : (fun ls'' => vP (VTy.instLife x a T) ls'' δ)
      = (fun ls'' => vP T ls'' (δ.extend x α)) :=
    funext fun ls'' => vC_tyEq (TyEq.instLife x a T ha) true ls''
  refine wpTS_bind (.appL .hole .unit) (substAll γ e) ls _ ρ
    (wpTS_mono (fun ls' v σ hv => ?_) ρ (h δ γ ls ρ hδ hg))
  simp only [Kont.plug]
  rw [hsub]
  exact hv ls' (Ext.refl _ _) α PMap.empty σ ⟨rfl, β, hb, hab⟩ (ResU.comp_empty_right σ)

/-! ### Lemma 6.161 (∀I-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.161 (`∀I-compat`) at `SemV`, with the library's three freshness
hypotheses (`allI_compat`).
`[variant: at `SemV`, with `allI_compat`'s added freshness hypotheses]` -/
theorem allI_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life}
    {S : VTy} {e : Expr} {T : VTy} (_hx : Δ.find? x = none)
    (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : SemV (Δ.extend x b) (⟨S, false⟩ :: Γ) e T) :
    SemV Δ Γ (.val (.lam e)) (.all x b T) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ e))) _ ρ
  refine wpTS_val _ _ _ _ ?_
  intro ls' hext α ρ₁ ρ₂ hpure hcomp
  obtain ⟨rfl, β, hβ, hlt⟩ := hpure
  have hρ₂ : ρ₂ = ρ := eq_of_compS_empty_left (ResU.CompS.comm hcomp)
  subst ρ₂
  have hfind : ∀ z, z ≠ x → (δ.extend x α).find? z = δ.find? z :=
    fun z hz => find?_extend_ne δ α (Ne.symm hz)
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
  have hsub : substAll (Val.unit :: γ) e = Expr.subst 0 Val.unit (Expr.psub 1 γ e) := by
    show Expr.psub 0 (Val.unit :: γ) e = _
    rw [Expr.psub_cons 0 Val.unit γ e, Val.shift_zero]
  refine wpTS_lolli ls' (Expr.psub 1 γ e) Val.unit _ _ ?_
  rw [← hsub]
  refine h (δ.extend x α) (Val.unit :: γ) ls' ρ hδ' (gDenC_mk (by simpa using hlen) ?_)
  show gSepC ls' (δ.extend x α) Γ γ ρ
  have heq : gSepC ls' δ Γ γ = gSepC ls' (δ.extend x α) Γ γ :=
    gSepC_congr (fun s hs hl => vC_congr s.ty (fun z hz =>
      (hfind z (by rintro rfl; exact hΓx s hs hl hz)).symm) true ls')
  rw [← heq]
  exact gSepC_local hext hgs

/-! ### Lemma 6.163 ([]I-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/

/-- `!Γ` holds no resource. -/
theorem gSepC_persistent {ls : List SRec} {δ : LSub} :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}, Persistent Γ → gSepC ls δ Γ γ ρ → ρ = PMap.empty
  | [], _, _, _, h => h.1
  | _ :: _, [], _, _, h => h.1
  | s :: Γ, v :: γ, ρ, hp, h => by
      have hp' : Persistent Γ := fun t ht hl => hp t (List.mem_cons_of_mem _ ht) hl
      unfold gSepC at h
      split at h
      · rename_i hl
        obtain ⟨T, hT⟩ := hp s List.mem_cons_self hl
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        have e₁ : ρ₁ = PMap.empty := by rw [hT] at h₁; exact h₁.1
        have e₂ := gSepC_persistent hp' h₂
        subst e₁; subst e₂
        first | exact eq_of_compS_empty_left hc | exact (eq_of_compS_empty_left hc).symm
      · exact gSepC_persistent hp' h

theorem bangLamI_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {body : Expr} {T₁ T₂ : VTy}
    (hΓp : Persistent Γ) (h : SemV Δ (⟨T₁, true⟩ :: Γ) body T₂) :
    SemV Δ Γ (.val (.lam body)) (.bang (.lolli T₁ T₂)) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ body))) _ ρ
  refine wpTS_val _ _ _ _ ⟨gSepC_persistent hΓp hgs, ?_⟩
  intro ls' hext v' ρ₁ ρ₂ hv' hcomp
  have hsub : substAll (v' :: γ) body = Expr.subst 0 v' (Expr.psub 1 γ body) := by
    show Expr.psub 0 (v' :: γ) body = _
    rw [Expr.psub_cons 0 v' γ body, Val.shift_zero]
  refine wpTS_lolli ls' (Expr.psub 1 γ body) v' _ _ ?_
  rw [← hsub]
  exact h δ (v' :: γ) ls' _ hδ
    (gDenC_mk (by simpa using hlen) ⟨ρ₁, ρ, ResU.CompS.comm hcomp, hv', gSepC_local hext hgs⟩)

/-! ### Lemma 6.160 (⊸E-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/

theorem bangAllI_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life}
    {S : VTy} {e : Expr} {T : VTy} (hΓp : Persistent Γ) (_hx : Δ.find? x = none)
    (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : SemV (Δ.extend x b) (⟨S, false⟩ :: Γ) e T) :
    SemV Δ Γ (.val (.lam e)) (.bang (.all x b T)) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ e))) _ ρ
  refine wpTS_val _ _ _ _ ⟨gSepC_persistent hΓp hgs, ?_⟩
  intro ls' hext α ρ₁ ρ₂ hpure hcomp
  obtain ⟨rfl, β, hβ, hlt⟩ := hpure
  have hρ₂ : ρ₂ = ρ := eq_of_compS_empty_left (ResU.CompS.comm hcomp)
  subst ρ₂
  have hfind : ∀ z, z ≠ x → (δ.extend x α).find? z = δ.find? z :=
    fun z hz => find?_extend_ne δ α (Ne.symm hz)
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
  have hsub : substAll (Val.unit :: γ) e = Expr.subst 0 Val.unit (Expr.psub 1 γ e) := by
    show Expr.psub 0 (Val.unit :: γ) e = _
    rw [Expr.psub_cons 0 Val.unit γ e, Val.shift_zero]
  refine wpTS_lolli ls' (Expr.psub 1 γ e) Val.unit _ _ ?_
  rw [← hsub]
  refine h (δ.extend x α) (Val.unit :: γ) ls' ρ hδ' (gDenC_mk (by simpa using hlen) ?_)
  show gSepC ls' (δ.extend x α) Γ γ ρ
  have heq : gSepC ls' δ Γ γ = gSepC ls' (δ.extend x α) Γ γ :=
    gSepC_congr (fun s hs hl => vC_congr s.ty (fun z hz =>
      (hfind z (by rintro rfl; exact hΓx s hs hl hz)).symm) true ls')
  rw [← heq]
  exact gSepC_local hext hgs

/-! ### Lemma 6.163 ([]I-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/

/-- `!E` at `SemV`: forget the `ρ = ∅`. -/
theorem bangE_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {T : VTy}
    (h : SemV Δ Γ e (.bang T)) : SemV Δ Γ e T := by
  intro δ γ ls ρ hδ hg
  exact wpTS_mono (fun _ _ _ hb => hb.2) ρ (h δ γ ls ρ hδ hg)

/-- `copy` at `!T`: both copies are the original, at `∅`. -/
theorem copyBang_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {T : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ copy (.lolli (.bang T) (.tensor (.bang T) (.bang T))) := by
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

/-- `forget` at `!T`: nothing to release. -/
theorem forgetBang_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {T : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ forget (.lolli (.bang T) .unit) := by
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

/-- `[TR]` Lemma 6.163 (`[]I-compat`) at `SemV`: 6.62 is `gSepC_outlives` (6.60 at `vC`),
`wp-[]` is `wpTS_box`.  `[as printed]`. -/
theorem boxI_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {T : VTy} {a : Lifetime.Life}
    (h : SemV Δ Γ e T) (hΓ : CtxOutlives Δ Γ a) :
    SemV Δ Γ e (.box a T) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, ha⟩ := hΓ.1 δ hδ
  show wpTS ls (substAll γ e) (fun ls' => vP (.box a T) ls' δ) ρ
  have hv : (fun ls' => vP (.box a T) ls' δ) = fun ls' v => box α (vP T ls' δ v) := by
    funext ls' v
    exact atLife_eq ha _
  rw [hv]
  exact wpTS_box ls α _ _ ρ
    ⟨h δ γ ls ρ hδ hg, gSepC_outlives hδ ha hΓ.2 (gDenC_iff.mp hg).2⟩

/-! ### Lemma 6.172 (withbor-compat1) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.172 (`withbor-compat1`, p. 45) at `SemV`.
`[restricted: `hfree₁`/`hfree₂`, as `withbor1_compat`; `hsc₁`, `[TR]` p. 2's `Δ ⊢ T₁`,
which `TW.immFrame` reads as `AdmWf`]` -/
theorem withbor1_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {T₁ T₂ : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none) (hsc₁ : VScoped Δ T₁)
    (hfree₁ : ¬ VFree x T₁) (hfree₂ : ¬ VFree x T₂) :
    SemV Δ Γ withbor (axWithbor1Ty x Δ.meetOfDom T₁ T₂) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls withbor _ _
  refine wpTS_val _ _ _ _ ?_
  -- unfold 𝒱⟦⊸⟧, let `v` be arbitrary, apply `wp-⊸`
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  -- unfold 𝒱⟦Ref T₁⟧: `v = ℓ`, and the resource is `ℓ ↦ vℓ ⋆ 𝒱⟦T₁⟧δ(vℓ)`
  obtain ⟨ℓ, vℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, ρℓ, ρP, hcℓ, hown, hP⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))))
      = Expr.val (Val.lam (.pair (.val (.loc ℓ))
          (.app (.app BoCa.v0 unit') (.val (.loc ℓ))))) := by
    simp [Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit']
  refine wpTS_lolli _ _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  -- `wp-val`; unfold 𝒱⟦⊸⟧ again, let `vf` be arbitrary, apply `wp-⊸`
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (.loc ℓ)) (.app (.app BoCa.v0 unit') (.val (.loc ℓ))))
      = Expr.pair (.val (.loc ℓ))
          (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) := by
    simp [Expr.subst, BoCa.v0, unit']
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  -- the payload, at the callback's list
  have hP₂ : vP T₁ ls₂ δ vℓ ρP := vC_local true T₁ (hext₂.right hcℓ) hP
  -- `ImmFrame` at `ℓ ↦ vℓ ⋆ 𝒱⟦T₁⟧δ(vℓ)`, with the callback's resource `ρ₂` under the `⋔α`
  obtain ⟨σ, hcσ, hcτ⟩ := compS_reassoc hcℓ hc₂
  refine wpTS_I_frameX ℓ T₁ δ (admWf_of_vScoped hsc₁ hδ) vℓ _ ls₂
    (fun ls' => vP (.tensor (.ref T₁) T₂) ls' δ) (fun _ _ _ _ hk h => vC_local true _ hk h) τ
    ⟨ρℓ, σ, hcτ, hown, ρP, ρ₂, hcσ, hP₂, ?_⟩
  -- `⋔r` at `@ρ₂` and `⋔-mono` down to `⊓Δδ`: the bound is `@ρ₂ ⊓ ⊓Δδ`
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  have hout₂ : ρ₂.InStratum α := outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)
  -- `─⋆R`: take the borrow `ℓ ↦ I α 𝒱⟦T₁⟧δ`, at the list with the frame's record
  intro ls' hadd hrec ρm σ' hm' hcm
  -- the borrow at the callback's type `Imm 'x T₁`, at `δ['x↦α]`
  have himm' : vP (.imm (.var x) T₁) ls' (δ.extend x α) (.loc ℓ) ρm := by
    obtain ⟨r, hr, hle, hT, hδr⟩ := hrec
    refine ⟨α, interp_ext_self δ x α, ℓ, pure_sep_mk ⟨rfl, cohE_of_coh
      (Or.inl ⟨r, hr, hle.symm, hT.symm, fun y hy => ?_⟩)⟩ ?_⟩
    · rw [hδr]
      rw [hT] at hy
      exact find?_extend_ne δ α (fun e => by subst e; exact hfree₁ hy)
    · exact ptoImmS_mono (fun ls₀ u σ h => by
        rw [vC_extend_of_not_free hfree₁]; exact vO_obs T₁ h) hm'
  -- `wp-bind` at `vf () ℓ` under `(ℓ, −)`
  refine wpTS_bind (.pairR (.loc ℓ) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) ls' _ σ' ?_
  -- unfold 𝒱⟦∀⟧ at `α ⊏ ⊓Δδ`, at `ls′` (`Ext`-above `ls₂` at `ρ₂ ∈ Res_α`)
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf ls' (ext_add hadd hout₂) α PMap.empty ρ₂ ⟨rfl, hlt⟩
    (ResU.comp_empty_right ρ₂)
  refine wpTS_bind_frame (.appL .hole (.loc ℓ)) (.app (.val vf) (.val .unit)) ls'
    (fun ls'' => vP (.lolli (.imm (.var x) T₁) (.box (.var x) T₂)) ls'' (δ.extend x α))
    (fun ls'' => vP (.imm (.var x) T₁) ls'' (δ.extend x α) (.loc ℓ)) _
    (fun ls'' hls ρ h => vP_same hls h) ?_ σ' ⟨ρ₂, ρm, hcm, hwpf, himm'⟩
  rintro ls'' - vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, himm''⟩
  simp only [Kont.plug]
  -- the callback's own 𝒱⟦⊸⟧ at that borrow, then `wp-mono` at its result `v″`
  refine wpTS_mono (fun ls''' v'' ρ'' hb => ?_) σ''
    (hvg ls'' (Ext.refl _ _) (.loc ℓ) σ₂ σ'' himm'' hcσ'')
  -- unfold 𝒱⟦['x] T₂⟧_{δ['x↦α]}, which is `[α] 𝒱⟦T₂⟧δ(v″)` since `'x` is not free in `T₂`
  obtain ⟨α', hα', hT₂δ', hout⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  have hT₂' : vP T₂ ls''' δ v'' ρ'' := by
    rw [vC_extend_of_not_free hfree₂] at hT₂δ'; exact hT₂δ'
  -- `wp-ret`, and the cell ImmFrame gets back, at the same `vℓ`
  refine wpTS_val ls''' (.pair (.loc ℓ) v'') _ ρ'' ?_
  refine ⟨fun c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
  exact ⟨.loc ℓ, v'', pure_sep_mk rfl
    ⟨s, ρ'', ResU.CompS.comm hρs, ⟨ℓ, vℓ, pure_sep_mk rfl ⟨c₁, p₁, hs, hc₁, hp⟩⟩, hT₂'⟩⟩

/-! ### Lemma 6.173 (withbor-compat2) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.173 (`withbor-compat2`, p. 46) at `SemV`: `MutFrame`'s premise is 6.60
at `vC` at the side condition's `@bδ`, as printed.
`[restricted: `hfree₁`/`hfree₂`, as `withbor2_compat`]` -/
theorem withbor2_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {T₁ T₂ : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none)
    (hside : ∃ b, Δ.Defines b ∧ VOutlives Δ b T₁)
    (hfree₁ : ¬ VFree x T₁) (hfree₂ : ¬ VFree x T₂) :
    SemV Δ Γ withbor (axWithbor2Ty x Δ.meetOfDom T₁ T₂) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls withbor _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, vℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, ρℓ, ρP, hcℓ, hown, hP⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))))
      = Expr.val (Val.lam (.pair (.val (.loc ℓ))
          (.app (.app BoCa.v0 unit') (.val (.loc ℓ))))) := by
    simp [Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit']
  refine wpTS_lolli _ _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (.loc ℓ)) (.app (.app BoCa.v0 unit') (.val (.loc ℓ))))
      = Expr.pair (.val (.loc ℓ))
          (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) := by
    simp [Expr.subst, BoCa.v0, unit']
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  have hP₂ : vP T₁ ls₂ δ vℓ ρP := vC_local true T₁ (hext₂.right hcℓ) hP
  -- "Since `Δ ⊢ T₁ ⊐ @b`, theorem 6.60 gives `𝒱⟦T₁⟧δ ⊧ [@bδ] 𝒱⟦T₁⟧δ`, so MutFrame applies"
  obtain ⟨b, hdef, hO⟩ := hside
  obtain ⟨β, hb⟩ := hdef δ hδ
  have hβ := vC_outlives hδ hb hO true
  obtain ⟨σ, hcσ, hcτ⟩ := compS_reassoc hcℓ hc₂
  refine wpTS_M_frameX ℓ T₁ δ β (fun ls' w σ' h => hβ ls' w σ' h) vℓ _ ls₂
    (fun ls' => vP (.tensor (.ref T₁) T₂) ls' δ) τ
    ⟨ρℓ, σ, hcτ, hown, ρP, ρ₂, hcσ, hP₂, ?_⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  -- `─⋆R`: take the borrow `ℓ ↦ M α 𝒱⟦T₁⟧δ`
  intro ρm σ' hm' hcm
  have hmut' : vP (.mut (.var x) T₁) ls₂ (δ.extend x α) (.loc ℓ) ρm := by
    have e : (fun ls₀ => vC true T₁ ls₀ (δ.extend x α)) = (fun ls₀ => vC true T₁ ls₀ δ) :=
      funext fun ls₀ => vC_extend_of_not_free hfree₁ true ls₀ δ α
    refine ⟨α, interp_ext_self δ x α, ℓ, pure_sep_mk rfl ?_⟩
    show ptoMutS ℓ α ls₂ (fun ls₀ => vC true T₁ ls₀ (δ.extend x α)) ρm
    rw [e]; exact hm'
  refine wpTS_bind (.pairR (.loc ℓ) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) ls₂ _ σ' ?_
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf ls₂ (Ext.refl _ _) α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wpTS_bind_frame (.appL .hole (.loc ℓ)) (.app (.val vf) (.val .unit)) ls₂
    (fun ls'' => vP (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)) ls'' (δ.extend x α))
    (fun ls'' => vP (.mut (.var x) T₁) ls'' (δ.extend x α) (.loc ℓ)) _
    (fun ls'' hls ρ h => vP_same hls h) ?_ σ' ⟨ρ₂, ρm, hcm, hwpf, hmut'⟩
  rintro ls'' - vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, hmut''⟩
  simp only [Kont.plug]
  refine wpTS_mono (fun ls''' v'' ρ'' hb => ?_) σ''
    (hvg ls'' (Ext.refl _ _) (.loc ℓ) σ₂ σ'' hmut'' hcσ'')
  obtain ⟨α', hα', hT₂δ', hout⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  have hT₂' : vP T₂ ls''' δ v'' ρ'' := by
    rw [vC_extend_of_not_free hfree₂] at hT₂δ'; exact hT₂δ'
  -- `wp-ret`, and the `∀v′` that pays `MutFrame` back
  refine wpTS_val ls''' (.pair (.loc ℓ) v'') _ ρ'' ?_
  refine ⟨fun w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
  exact ⟨.loc ℓ, v'', pure_sep_mk rfl
    ⟨s, ρ'', ResU.CompS.comm hρs, ⟨ℓ, w, pure_sep_mk rfl ⟨c₁, p₁, hs, hc₁, hp⟩⟩, hT₂'⟩⟩

/-! ### Lemma 6.174 (withbor-compat3) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.174 (`withbor-compat3`, p. 47) at `SemV`: `AntiFrame`, then `MutFrame`
with its premise read off the borrow in hand.
`[restricted: `hfree₁`/`hfree₂`, as `withbor3_compat`]` -/
theorem withbor3_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life}
    {T₁ T₂ : VTy} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none)
    (hfree₁ : ¬ VFree x T₁) (hfree₂ : ¬ VFree x T₂) :
    SemV Δ Γ withbor (axWithbor3Ty a x Δ.meetOfDom T₁ T₂) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls withbor _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, v₁ = Val.loc ℓ := by
    obtain ⟨α₀, -, ℓ, hs₁⟩ := hv₁
    exact ⟨ℓ, (pure_sep_iff.mp hs₁).1⟩
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))))
      = Expr.val (Val.lam (.pair (.val (.loc ℓ))
          (.app (.app BoCa.v0 unit') (.val (.loc ℓ))))) := by
    simp [Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit']
  refine wpTS_lolli _ _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (.loc ℓ)) (.app (.app BoCa.v0 unit') (.val (.loc ℓ))))
      = Expr.pair (.val (.loc ℓ))
          (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) := by
    simp [Expr.subst, BoCa.v0, unit']
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  -- the `Mut` value at the callback's list: `ℓ ↦ M α₀ 𝒱⟦T₁⟧δ`
  have hv₂ : vP (.mut a T₁) ls₂ δ (Val.loc ℓ) ρ₁ := vC_local true _ hext₂ hv₁
  obtain ⟨α₀, ha, ℓ', hs₂⟩ := hv₂
  obtain ⟨hℓ', hmut⟩ := pure_sep_iff.mp hs₂
  have hℓℓ : ℓ' = ℓ := by
    have := congrArg Subtype.val hℓ'; simpa using this.symm
  subst hℓℓ
  -- `MutFrame`'s premise, read off the borrow in hand
  obtain ⟨β, hβ⟩ : ∃ β, ∀ ls' w σ, vC true T₁ ls' δ w σ → σ.InStratum β := by
    obtain ⟨b, -, -, -, -, -, -, -, -, -, -, hunif⟩ := hmut
    exact ⟨b, hunif⟩
  -- `AntiFrame` at `ℓ ↦ M α₀ 𝒱⟦T₁⟧δ`, the callback's resource `ρ₂` the second conjunct
  refine wpTS_M_antiFrameX ℓ' α₀ T₁ δ _ ls₂ _ τ ⟨ρ₁, ρ₂, hc₂, hmut, ?_⟩
  intro v₂ c₁ c₂ hc hcc p₁ p₂ hp hcp
  obtain ⟨σ, hcσ, hmid⟩ := compS_reassoc' hcc (ResU.CompS.comm hcp)
  refine wpTS_M_frameX ℓ' T₁ δ β hβ v₂ _ ls₂ _ p₂
    ⟨c₁, σ, ResU.CompS.comm hmid, hc, p₁, ρ₂, hcσ, hp, ?_⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  intro ρm σ' hm' hcm
  have hmut' : vP (.mut (.var x) T₁) ls₂ (δ.extend x α) (.loc ℓ') ρm := by
    have e : (fun ls₀ => vC true T₁ ls₀ (δ.extend x α)) = (fun ls₀ => vC true T₁ ls₀ δ) :=
      funext fun ls₀ => vC_extend_of_not_free hfree₁ true ls₀ δ α
    refine ⟨α, interp_ext_self δ x α, ℓ', pure_sep_mk rfl ?_⟩
    show ptoMutS ℓ' α ls₂ (fun ls₀ => vC true T₁ ls₀ (δ.extend x α)) ρm
    rw [e]; exact hm'
  refine wpTS_bind (.pairR (.loc ℓ') .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ'))) ls₂ _ σ' ?_
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf ls₂ (Ext.refl _ _) α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wpTS_bind_frame (.appL .hole (.loc ℓ')) (.app (.val vf) (.val .unit)) ls₂
    (fun ls'' => vP (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)) ls'' (δ.extend x α))
    (fun ls'' => vP (.mut (.var x) T₁) ls'' (δ.extend x α) (.loc ℓ')) _
    (fun ls'' hls ρ h => vP_same hls h) ?_ σ' ⟨ρ₂, ρm, hcm, hwpf, hmut'⟩
  rintro ls'' - vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, hmut''⟩
  simp only [Kont.plug]
  refine wpTS_mono (fun ls''' v'' ρ'' hb => ?_) σ''
    (hvg ls'' (Ext.refl _ _) (.loc ℓ') σ₂ σ'' hmut'' hcσ'')
  obtain ⟨α', hα', hT₂δ', hout⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  have hT₂' : vP T₂ ls''' δ v'' ρ'' := by
    rw [vC_extend_of_not_free hfree₂] at hT₂δ'; exact hT₂δ'
  refine wpTS_val ls''' (.pair (.loc ℓ') v'') _ ρ'' ?_
  refine ⟨fun w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
  obtain ⟨W, hcWi, hcW⟩ := compS_reassoc hs (ResU.CompS.comm hρs)
  exact ⟨w, c₁, W, hcW, hc₁, p₁, ρ'', hcWi, hp,
    fun m₁ m₂ hm hcm => ⟨.loc ℓ', v'', pure_sep_mk rfl
      ⟨m₁, ρ'', ResU.CompS.comm hcm, ⟨α₀, ha, ℓ', pure_sep_mk rfl hm⟩, hT₂'⟩⟩⟩

/-! ### Lemma 6.176 (withswap-compat) at the typed world; record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` -/
/-- `[TR]` Lemma 6.176 (`withswap-compat`, pp. 48–49) at `SemV`.  `[as printed]`. -/
theorem withswap_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life}
    {T₁ T₂ : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ withswap (axWithswapTy a T₁ T₂) := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls withswap _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, v₁ = Val.loc ℓ := by
    obtain ⟨α₀, -, ℓ, hs₁⟩ := hv₁
    exact ⟨ℓ, (pure_sep_iff.mp hs₁).1⟩
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.letpair (.app BoCa.v0 (.app load' BoCa.v1))
          (.seq (.app (.app store' BoCa.v3) BoCa.v1) (.pair BoCa.v3 BoCa.v0)))))
      = Expr.val (Val.lam (.letpair (.app BoCa.v0 (eLoad ℓ))
          (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                (.pair (.val (.loc ℓ)) BoCa.v0)))) := by
    simp [eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, BoCa.v3, load', store']
  refine wpTS_lolli _ _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.letpair (.app BoCa.v0 (eLoad ℓ))
          (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                (.pair (.val (.loc ℓ)) BoCa.v0)))
      = Expr.letpair (.app (.val vf) (eLoad ℓ))
          (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                (.pair (.val (.loc ℓ)) BoCa.v0)) := by
    simp [eLoad, Expr.subst, BoCa.v0, BoCa.v1, store']
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  have hv₂ : vP (.mut a T₁) ls₂ δ (Val.loc ℓ) ρ₁ := vC_local true _ hext₂ hv₁
  obtain ⟨α, ha, ℓ', hs₂⟩ := hv₂
  obtain ⟨hℓ', hmut⟩ := pure_sep_iff.mp hs₂
  have hℓℓ : ℓ' = ℓ := by
    have := congrArg Subtype.val hℓ'; simpa using this.symm
  subst hℓℓ
  -- `wp-m-anti-frame`; let `v₂` be the payload it hands over
  refine wpTS_M_antiFrameX ℓ' α T₁ δ _ ls₂ _ τ ⟨ρ₁, ρ₂, hc₂, hmut, ?_⟩
  intro v₂ c₁ c₂ hc hcc p₁ p₂ hp hcp
  obtain ⟨s, hs, hsp⟩ := compS_exch hcc hcp
  -- `wp-bind` at the argument `load ℓ`, then `wp-load`
  refine wpTS_bind (.letpair (.appR (.val vf) .hole) _) (eLoad ℓ') ls₂ _ _ ?_
  refine wpTS_load ls₂ ℓ' v₂ _ _ ⟨c₁, s, ResU.CompS.comm hsp, hc, ?_⟩
  intro r₁ r₂ hr hcr
  simp only [Kont.plug]
  -- the callback's 𝒱⟦⊸⟧ at 𝒱⟦T₁⟧δ(v₂); `wp-bind` at `vf v₂`, framing the cell through
  refine wpTS_bind_frame (.letpair .hole _) (.app (.val vf) (.val v₂)) ls₂
    (fun ls' => vP (.tensor T₁ T₂) ls' δ) (fun _ => ptoOwn ℓ' v₂) _
    (fun _ _ _ h => h) ?_ r₂
    ⟨s, r₁, hcr, hvf ls₂ (Ext.refl _ _) v₂ p₁ s hp hs, hr⟩
  rintro ls' - w σ ⟨σ₁, σ₂, hcσ, hw, hown⟩
  obtain ⟨v₃, v₄, hs₂'⟩ := hw
  obtain ⟨rfl, ρ₃, ρ₄, hc34, h₃, h₄⟩ := pure_sep_iff.mp hs₂'
  simp only [Kont.plug]
  have hβ₃ : Expr.subst 0 v₃ (Expr.subst 0 (v₄.shift 1 0)
        (Expr.seq (.app (.app store' (.val (.loc ℓ'))) BoCa.v1) (.pair (.val (.loc ℓ')) BoCa.v0)))
      = Expr.seq (eStore ℓ' v₃) (.pair (.val (.loc ℓ')) (.val v₄)) := by
    simp [eStore, Expr.subst, BoCa.v0, BoCa.v1, store',
      Expr.subst_shift 0 0 0 v₃ v₄.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  refine wpTS_tensor ls' v₃ v₄ _ _ _ ?_
  rw [hβ₃]
  refine wpTS_bind (.seq .hole (.pair (.val (.loc ℓ')) (.val v₄))) (eStore ℓ' v₃) ls' _ _ ?_
  refine wpTS_store ls' ℓ' v₂ v₃ _ _ ⟨σ₂, σ₁, ResU.CompS.comm hcσ, hown, ?_⟩
  intro t₁ t₂ ht hct
  simp only [Kont.plug]
  refine wpTS_1 _ _ _ _ ?_
  refine wpTS_val ls' (.pair (.loc ℓ') v₄) _ _ ?_
  -- choose `∃v` to be `v₃`, and give the borrow back
  refine ⟨v₃, t₁, σ₁, ResU.CompS.comm hct, ht, ρ₃, ρ₄, hc34, h₃, ?_⟩
  intro m₁ m₂ hm hcm
  exact ⟨.loc ℓ', v₄, pure_sep_mk rfl
    ⟨m₁, ρ₄, ResU.CompS.comm hcm, ⟨α, ha, ℓ', pure_sep_mk rfl hm⟩, h₄⟩⟩

end BoCa.Fig16.LogRel.Core

end
