import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S4_LogicalRelation.Remarks
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.S6_3_FrameAndAntiFrame.Lemmas
import Paper.S6_4_StandardEntailments.Lemmas
import Paper.S6_5_NonStandardEntailments.Lemmas
import Paper.S6_6_ReborrowingEntailments.Lemmas
import Paper.S6_7_WeakestPreconditionRules.Lemmas
import Support.Dynamics.Machine
import Support.Lifetimes.Interpretation
import Support.Lifetimes.Substitution
import Support.Lifetimes.Terms
import Support.LogicalRelation.ClosedJudgment
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Compatibility
import Support.LogicalRelation.Facts
import Support.Model.Notation
import Support.Model.Propositions
import Support.Model.ReborrowRule
import Support.Model.UpdateFrame
import Support.Statics.Contexts
import Support.Statics.Presupposed
import Support.Syntax.Terms
import Support.TypedWorld.Compatibility
import Support.TypedWorld.Relation

/-!
# [TR] §6.8 Fundamental Property  (physical pp. 40–49), Lemmas 6.151–6.176

The Fundamental Property (6.151) and its compatibility lemmas, one per typing rule
of `[TR]` p. 2 and per row of its axiom table (6.152–6.176).  Records as in §6.1's
file.

Each compatibility lemma is declared at the printed definitions read literally
(`Sem`); its record names the same proof at the repaired judgment `SemX` under
*Typed-world version* (`Support/TypedWorld/Compatibility.lean`; §12.69–§12.72).
6.151 is stated and proved at `SemX`.  `Fig16.LogRel.fundamentalProperty`, at the end of
this file, runs the printed induction at `Sem` with `WithloadEscrow` as a hypothesis at
the `withload` case; it is not among the results.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `[TR]` Lemma 6.151's printed proof at `SemX`: induction on the derivation, each
node closed by its `_compatX` compatibility lemma.  `[restricted: `⊧ Δ` carried as `Δ.Ok`; at the definition repairs
of docs/adjudications.md §12.69–§12.72]` -/
theorem fundamental :
    ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty),
      DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → SemX Δ Γ e T := by
  intro Δ Γ e T hD
  induction hD with
  | var h => intro _ _; exact id_compatX h
  | unitI h => intro _ _; exact unitI_compatX h
  | unitE hs _ _ ih₁ ih₂ =>
      intro hΔ hΓ
      exact unitE_compatX hs (ih₁ hΔ (hΓ.split_left hs)) (ih₂ hΔ (hΓ.split_right hs))
  | tensorI hs _ _ ih₁ ih₂ =>
      intro hΔ hΓ
      exact tensorI_compatX hs (ih₁ hΔ (hΓ.split_left hs)) (ih₂ hΔ (hΓ.split_right hs))
  | tensorE hs hwf _ _ ihp ihb =>
      intro hΔ hΓ
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ |>.mp hwf
      exact tensorE_compatX hs (ihp hΔ (hΓ.split_left hs))
        (ihb hΔ (Ctx.ScopedB.cons (fun _ => h₂)
          (Ctx.ScopedB.cons (fun _ => h₁) (hΓ.split_right hs))))
  | sumI₁ _ ih => intro hΔ hΓ; exact sumI₁_compatX (ih hΔ hΓ)
  | sumI₂ _ ih => intro hΔ hΓ; exact sumI₂_compatX (ih hΔ hΓ)
  | sumE hs hwf _ _ _ ih₀ ih₁ ih₂ =>
      intro hΔ hΓ
      obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ |>.mp hwf
      exact sumE_compatX hs (ih₀ hΔ (hΓ.split_left hs))
        (ih₁ hΔ (Ctx.ScopedB.cons (fun _ => h₁) (hΓ.split_right hs)))
        (ih₂ hΔ (Ctx.ScopedB.cons (fun _ => h₂) (hΓ.split_right hs)))
  | lolliI hwf _ ih =>
      intro hΔ hΓ
      exact lolliI_compatX (ih hΔ (Ctx.ScopedB.cons (fun _ => hwf) hΓ))
  | lolliE hs _ _ iha ihf =>
      intro hΔ hΓ
      exact lolliE_compatX hs (iha hΔ (hΓ.split_left hs)) (ihf hΔ (hΓ.split_right hs))
  | bangLamI hΓp hwf _ ih =>
      intro hΔ hΓ
      exact bangLamI_compatX hΓp (ih hΔ (Ctx.ScopedB.cons (fun _ => hwf) hΓ))
  | bangAllI hΓp hx hb hnb _ ih =>
      intro hΔ hΓ
      have hside := allISide_of_scopedB hΔ hx hb hΓ
      exact bangAllI_compatX hΓp hx hside.1 hside.2.1 hside.2.2
        (ih (hΔ.extend hx hb) (Ctx.ScopedB.allI hnb hΓ))
  | bangE _ ih => intro hΔ hΓ; exact bangE_compatX (ih hΔ hΓ)
  | copyBangAx hΓd => intro _ _; exact copyBang_compatX hΓd
  | forgetBangAx hΓd => intro _ _; exact forgetBang_compatX hΓd
  | allI hx hb hnb _ ih =>
      intro hΔ hΓ
      have hside := allISide_of_scopedB hΔ hx hb hΓ
      exact allI_compatX hx hside.1 hside.2.1 hside.2.2
        (ih (hΔ.extend hx hb) (Ctx.ScopedB.allI hnb hΓ))
  | allE _ hlt ih => intro hΔ hΓ; exact allE_compatX (ih hΔ hΓ) hlt
  | boxIctx _ hΓo ih =>
      intro hΔ hΓ
      exact boxI_compatX (ih hΔ hΓ) hΓo
  | boxE _ ih => intro hΔ hΓ; exact boxE_compatX (ih hΔ hΓ)
  | immSub _ hle ih => intro hΔ hΓ; exact immSub_compatX (ih hΔ hΓ) hle
  | mutSub _ hle ih => intro hΔ hΓ; exact mutSub_compatX (ih hΔ hΓ) hle
  | allocAx hΓd => intro _ _; exact alloc_compatX hΓd
  | freeAx hΓd => intro _ _; exact free_compatX hΓd
  | swapAx hΓd => intro _ _; exact swap_compatX hΓd
  | copyAx hΓd => intro _ _; exact copy_compatX hΓd
  | forgetImmAx hΓd => intro _ _; exact forgetImm_compatX hΓd
  | forgetMutAx hΓd => intro _ _; exact forgetMut_compatX hΓd
  | forgetUnkAx hΓd => intro _ _; exact forgetUnk_compatX hΓd
  | withbor1Ax hΓd x hx hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithbor1Ty hwf
      have hside := withbor1Side_of_scopedB hx h₁ h₂
      exact withbor1_compatX x hΓd hx h₁ hside.1 hside.2
  | withbor2Ax hΓd x hx hs hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithbor2Ty hwf
      have hside := withbor2Side_of_scopedB hx h₁ h₂
      exact withbor2_compatX x hΓd hx hs hside.1 hside.2
  | withbor3Ax hΓd x hx hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithbor3Ty hwf
      have hside := withbor3Side_of_scopedB hx h₁ h₂
      exact withbor3_compatX x hΓd hx hside.1 hside.2
  | withloadAx hΓd x hx hwf =>
      intro _ _
      obtain ⟨h₁, h₂⟩ := BoCa.scopedB_axWithloadTy hwf
      exact withload_compatX x hΓd hx (not_lfree_of_scopedB hx h₁) (not_lfree_of_scopedB hx h₂)
  | withswapAx hΓd => intro _ _; exact withswap_compatX hΓd

/-- The statement of `[TR]` Lemma 6.151 (Fundamental Property, p. 40) at `SemX`.
`[variant: at `SemX`, p. 4's judgment at the definition repairs of docs/adjudications.md §12.69–§12.72; `⊧ Δ` carried as `Δ.Ok`]` -/
def FundamentalProperty : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty),
    DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → SemX Δ Γ e T

/-!
## Lemma 6.151 (Fundamental Property) · `[TR]` p. 40 · `variant`

> If Δ; Γ ⊢ e : T then Δ; Γ ⊨ e : T.

**Printed proof, transcribed.** By induction on the typing derivation and appealing to the appropriate compatibility lemma (Lemmas 6.152–6.176) in each case.

**Lean.** `BoCa.Fig16.LogRel.Typed.fundamentalProperty` (statement `FundamentalProperty`, proof `fundamental`), aliases `TR.lemma_6_151`, `TR.«Fundamental Property»`, tag `[variant: at `SemX`, p. 4's judgment at the definition repairs of docs/adjudications.md §12.69–§12.72; `⊧ Δ` carried as `Δ.Ok`]`.

**Note.** `DerivesWf` is p. 2's typing rules with the scoping half of p. 2's `Δ ⊢ T` (`Ty.scopedB`, which also admits `Unk`) consulted at binders and eliminated types, and `∀I` carrying a Barendregt premise (C14); the Fundamental Property takes `⊧ Δ` (as `Δ.Ok`, sufficient: `Lifetime.LifeCtx.sat_of_ok`) and `Δ ⊢ Γ` (`Ctx.ScopedB`) as hypotheses, which p. 2's typing box does not print (`docs/adjudications.md` §C.26).  The conclusion `SemX` is p. 4's judgment at the repaired definitions (§12.69–§12.72), a different relation from the literal `Sem`; the result is a statement about `SemX`.  There is no other hypothesis.

**Literal reading.** `Fig16.LogRel.fundamentalProperty`, below, runs the printed induction at `Sem` with `WithloadEscrow` as a hypothesis at the `withload` case; it is not among the results.  `Paper/LiteralReadings/S6_8_FundamentalProperty.lean` holds the `withload` configuration at `Sem` (`ViewWitness`, §12.68), the check that it is not a typed world (`ViewWitness.excluded`, §12.73), and the antecedent read as the rule figures alone (`FundamentalPropertyOverRules`).
-/
theorem fundamentalProperty : FundamentalProperty := fundamental

end BoCa.Fig16.LogRel.Typed

alias TR.lemma_6_151 := BoCa.Fig16.LogRel.Typed.fundamentalProperty
alias TR.«Fundamental Property» := BoCa.Fig16.LogRel.Typed.fundamentalProperty

namespace BoCa.Lifetime

/-- `⊨ Δ` for every well-scoped `Δ`, witnessed by the canonical substitution. -/
theorem LifeCtx.sat_of_ok {Δ : LifeCtx} (h : Δ.Ok) : Δ.Sat :=
  ⟨Δ.canonical, canonList_models h⟩

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-- `Δ ⊢ Γ` holds of a context whose slots are all consumed (the axiom table's `∅`). -/
theorem Ctx.ScopedB.of_dead {Δ : LifeCtx} : ∀ {Γ : Ctx Ty}, Ctx.Dead Γ → Ctx.ScopedB Δ Γ := by
  intro Γ h
  induction h with
  | nil => intro s hm; exact absurd hm (by simp)
  | cons _ ih =>
      intro s hm hl
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact absurd hl (by simp)
      · exact ih s hm' hl

end BoCa

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.152 (id-compat) · `[TR]` p. 40 · `proved`

> ─────────────── id
> Δ; x : T ⊨ x : T

**Printed proof, transcribed.** By unfolding and `wp-val`.

**Lean.** `BoCa.Fig16.LogRel.id_compat`, aliases `TR.lemma_6_152`, `TR.«id-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.id_compatX`.
-/
/-- `[TR]` Lemma 6.152 (`id-compat`, p. 40).  `x : T` is `Ctx.Solo Γ i T`.
`[as printed]` -/
theorem id_compat {Δ : LifeCtx} {Γ : Ctx Ty} {i : Nat} {T : Ty}
    (h : Ctx.Solo Γ i T) : Sem Δ Γ (.var i) T := by
  refine sem_iff.mpr fun δ γ ρ _ hg => ?_
  obtain ⟨hlen, hs⟩ := gDen_iff.mp hg
  obtain ⟨v, hv, hval⟩ := gSep_solo h (h.lt_of_liveWithin hlen) hs
  have he : substAll γ (.var i) = .val v := by
    show Expr.psub 0 γ (.var i) = _
    simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv, Val.shift_zero]
  rw [he]
  exact wp_val v _ ρ hval

end BoCa.Fig16.LogRel

alias TR.lemma_6_152 := BoCa.Fig16.LogRel.id_compat
alias TR.«id-compat» := BoCa.Fig16.LogRel.id_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.153 (1I-compat) · `[TR]` p. 40 · `proved`

> ─────────────── 1I
> Δ; ∅ ⊨ () : 1

**Printed proof, transcribed.** By unfolding and `wp-val`.

**Lean.** `BoCa.Fig16.LogRel.unitI_compat`, aliases `TR.lemma_6_153`, `TR.«1I-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.unitI_compatX`.
-/
/-- `[TR]` Lemma 6.153 (`1I-compat`, p. 40).  `∅` is `Ctx.Dead Γ`: every slot
already consumed.  `[as printed]` -/
theorem unitI_compat {Δ : LifeCtx} {Γ : Ctx Ty} (h : Ctx.Dead Γ) :
    Sem Δ Γ (.val .unit) .unit := by
  refine sem_iff.mpr fun δ γ ρ _ hg => ?_
  obtain ⟨-, hs⟩ := gDen_iff.mp hg
  rw [gSep_dead h hs]
  refine wp_val Val.unit _ _ ?_
  exact ⟨rfl, rfl⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_153 := BoCa.Fig16.LogRel.unitI_compat
alias TR.«1I-compat» := BoCa.Fig16.LogRel.unitI_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.154 (1E-compat) · `[TR]` p. 40 · `proved`

> Δ; Γ₁ ⊨ e₁ : 1    Δ; Γ₂ ⊨ e₂ : T
> ───────────────────────────────── 1E
> Δ; Γ₁, Γ₂ ⊨ e₁; e₂ : T

**Printed proof, transcribed.** Suppose H1 and H2 (the premises); let `δ ∈ ⟦Δ⟧` and `γ`, split into `γ₁, γ₂`.  Apply `wp-bind`; the goal is `𝒢⟦Γ₁⟧δ(γ₁) ⋆ 𝒢⟦Γ₂⟧δ(γ₂) ⊨ wp(e₁γ₁){v₁. wp(v₁; e₂γ₂){𝒱⟦T⟧δ}}`.  Apply H1, `wp-frame` and `wp-mono` at an arbitrary `v₁`: `𝒱⟦1⟧δ(v₁) ⋆ 𝒢⟦Γ₂⟧δ(γ₂) ⊨ wp(v₁; e₂γ₂){𝒱⟦T⟧δ}`.  Unfolding `𝒱⟦1⟧`, `v₁ = ()`; follows from `wp-1` and H2.

**Lean.** `BoCa.Fig16.LogRel.unitE_compat`, aliases `TR.lemma_6_154`, `TR.«1E-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.unitE_compatX`.

**Literal reading.** `BoCa.Fig16.LogRel.unitE_refused_on_TR3`; `BoCa.TR3.derives_wSeq` (`Paper/LiteralReadings/S6_8_FundamentalProperty.lean`).

**Note.** Over `[TR]` §3's printed machine, which has no frame `K; e`, the conclusion is refused at `e₁ = free (alloc ())`, `e₂ = ()`, `T = 1`, a closed instance p. 2's `1E` types (§12.42, D6).
-/
/-- `[TR]` Lemma 6.154 (`1E-compat`, p. 40).  The split of `γ` into `γ₁`, `γ₂` is
positional, so the closing substitution is the same list on both premises.
`[as printed]` -/
theorem unitE_compat {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx Ty} {e₁ e₂ : Expr} {T : Ty}
    (hsp : Ctx.Split Γ Γ₁ Γ₂)
    (h₁ : Sem Δ Γ₁ e₁ .unit) (h₂ : Sem Δ Γ₂ e₂ T) :
    Sem Δ Γ (.seq e₁ e₂) T := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDen_split hsp hg
  refine wp_bind_frame (.seq .hole (substAll γ e₂)) (substAll γ e₁)
    (vDen .unit δ) (gDen δ Γ₂ γ) (vDen T δ) ?_ _
    ⟨ρ₁, ρ₂, hc, sem_iff.mp h₁ δ γ ρ₁ hδ hg₁, hg₂⟩
  rintro v σ ⟨σ₁, σ₂, hcσ, ⟨rfl, rfl⟩, hg₂'⟩
  rw [eq_of_compS_empty_left hcσ]
  exact wp_1 _ _ _ (sem_iff.mp h₂ δ γ σ₂ hδ hg₂')

end BoCa.Fig16.LogRel

alias TR.lemma_6_154 := BoCa.Fig16.LogRel.unitE_compat
alias TR.«1E-compat» := BoCa.Fig16.LogRel.unitE_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.155 (⊗I-compat) · `[TR]` p. 41 · `proved`

> Δ; Γ₁ ⊨ e₁ : T₁    Δ; Γ₂ ⊨ e₂ : T₂
> ─────────────────────────────────── ⊗I
> Δ; Γ₁, Γ₂ ⊨ (e₁, e₂) : T₁ ⊗ T₂

**Printed proof, transcribed.** Suppose H1, H2; let `δ ∈ ⟦Δ⟧`, `γ` split into `γ₁, γ₂`.  Apply `wp-bind`: `𝒢⟦Γ₁⟧δ(γ₁) ⋆ 𝒢⟦Γ₂⟧δ(γ₂) ⊨ wp(e₁γ₁){v₁. wp((v₁, e₂γ₂)){𝒱⟦T₁ ⊗ T₂⟧}}`.  Apply H1, `wp-frame` and `wp-mono` at an arbitrary `v₁`; apply `wp-bind`; repeat with H2 at some `v₂`: `𝒱⟦T₁⟧δ(v₁) ⋆ 𝒱⟦T₂⟧δ(v₂) ⊨ wp((v₁, v₂)){𝒱⟦T₁ ⊗ T₂⟧}`.  Fold `𝒱⟦⊗⟧`; follows from `wp-val`.

**Lean.** `BoCa.Fig16.LogRel.tensorI_compat`, aliases `TR.lemma_6_155`, `TR.«⊗I-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.tensorI_compatX`.

**Literal reading.** `BoCa.Fig16.LogRel.tensorI_step_on_TR3` (`Paper/LiteralReadings/S6_8_FundamentalProperty.lean`).

**Note.** `wp-val` at the expression `(v₁,v₂)` is `wp_pair`, reflexivity: `Expr` identifies the two derivations of `(v₁,v₂)` (§12.43).
-/
/-- `[TR]` Lemma 6.155 (`⊗I-compat`, p. 41).  `[as printed]` -/
theorem tensorI_compat {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx Ty} {e₁ e₂ : Expr} {T₁ T₂ : Ty}
    (hsp : Ctx.Split Γ Γ₁ Γ₂)
    (h₁ : Sem Δ Γ₁ e₁ T₁) (h₂ : Sem Δ Γ₂ e₂ T₂) :
    Sem Δ Γ (.pair e₁ e₂) (.tensor T₁ T₂) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDen_split hsp hg
  refine wp_bind_frame (.pairL .hole (substAll γ e₂)) (substAll γ e₁)
    (vDen T₁ δ) (gDen δ Γ₂ γ) (vDen (.tensor T₁ T₂) δ) ?_ _
    ⟨ρ₁, ρ₂, hc, sem_iff.mp h₁ δ γ ρ₁ hδ hg₁, hg₂⟩
  rintro v₁ σ ⟨σ₁, σ₂, hcσ, hv₁, hg₂'⟩
  refine wp_bind_frame (.pairR v₁ .hole) (substAll γ e₂)
    (vDen T₂ δ) (vDen T₁ δ v₁) (vDen (.tensor T₁ T₂) δ) ?_ _
    ⟨σ₂, σ₁, ResU.CompS.comm hcσ, sem_iff.mp h₂ δ γ σ₂ hδ hg₂', hv₁⟩
  rintro v₂ τ ⟨τ₁, τ₂, hcτ, hv₂, hv₁'⟩
  refine wp_pair v₁ v₂ _ _ (wp_val (.pair v₁ v₂) _ _ ?_)
  exact ⟨v₁, v₂, pure_sep_mk rfl ⟨τ₂, τ₁, ResU.CompS.comm hcτ, hv₁', hv₂⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_155 := BoCa.Fig16.LogRel.tensorI_compat
alias TR.«⊗I-compat» := BoCa.Fig16.LogRel.tensorI_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.156 (⊗E-compat) · `[TR]` p. 41 · `proved`

> Δ; Γ₁ ⊨ e₁ : T₁₁ ⊗ T₁₂    Δ; Γ₂, x₁ : T₁₁, x₂ : T₁₂ ⊨ e₂ : T₂
> ──────────────────────────────────────────────────────────── ⊗E
> Δ; Γ₁, Γ₂ ⊨ let (x₁, x₂) = e₁; e₂ : T₂

**Printed proof, transcribed.** Suppose H1, H2; let `δ ∈ ⟦Δ⟧`, `γ` split into `γ₁, γ₂`.  Apply `wp-bind`: `𝒢⟦Γ₁⟧δ(γ₁) ⋆ 𝒢⟦Γ₂⟧δ(γ₂) ⊨ wp(e₁γ₁){v₁. wp(let (x₁, x₂) = v₁; e₂γ₂){𝒱⟦T₂⟧δ}}`.  Apply H1, `wp-frame` and `wp-mono` at an arbitrary `v₁`.  Unfolding `𝒱⟦⊗⟧`, `v₁ = (v₁₁, v₁₂)`: `𝒱⟦T₁₁⟧δ(v₁₁) ⋆ 𝒱⟦T₁₂⟧(v₁₂) ⋆ 𝒢⟦Γ₂⟧δ(γ₂) ⊨ wp(let (x₁, x₂) = (v₁₁, v₁₂); e₂γ₂){𝒱⟦T₂⟧δ}`.  Follows from `wp-⊗` and H2 with `γ₂[x₁ ↦ v₁₁, x₂ ↦ v₁₂]`.

**Lean.** `BoCa.Fig16.LogRel.tensorE_compat`, aliases `TR.lemma_6_156`, `TR.«⊗E-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.tensorE_compatX`.
-/
/-- `[TR]` Lemma 6.156 (`⊗E-compat`, p. 41).  De Bruijn: `x₂` is index 0 and `x₁`
index 1, so `[TR]`'s `γ₂[x₁↦v₁¹, x₂↦v₁²]` is the list `v₁² :: v₁¹ :: γ`, and
`Expr.psub_cons₂` crosses the two binders.  `[as printed]` -/
theorem tensorE_compat {Δ : LifeCtx} {Γ Γp Γb : Ctx Ty} {ep eb : Expr}
    {T₁ T₂ T : Ty} (hsp : Ctx.Split Γ Γp Γb)
    (h₁ : Sem Δ Γp ep (.tensor T₁ T₂))
    (h₂ : Sem Δ (⟨T₂, true⟩ :: ⟨T₁, true⟩ :: Γb) eb T) :
    Sem Δ Γ (.letpair ep eb) T := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDen_split hsp hg
  refine wp_bind_frame (.letpair .hole (Expr.psub 2 γ eb)) (substAll γ ep)
    (vDen (.tensor T₁ T₂) δ) (gDen δ Γb γ) (vDen T δ) ?_ _
    ⟨ρ₁, ρ₂, hc, sem_iff.mp h₁ δ γ ρ₁ hδ hg₁, hg₂⟩
  rintro v σ ⟨σ₁, σ₂, hcσ, hpair, hg₂'⟩
  obtain ⟨w₁, w₂, hs⟩ := hpair
  obtain ⟨rfl, b₁, b₂, hcb, hw₁, hw₂⟩ := pure_sep_iff.mp hs
  have hsub : substAll (w₂ :: w₁ :: γ) eb
      = Expr.subst 0 w₁ (Expr.subst 0 (w₂.shift 1 0) (Expr.psub 2 γ eb)) := by
    show Expr.psub 0 (w₂ :: w₁ :: γ) eb = _
    rw [Expr.psub_cons₂ 0 w₂ w₁ γ eb, Val.shift_zero]
  refine wp_tensor w₁ w₂ (Expr.psub 2 γ eb) _ _ ?_
  rw [← hsub]
  obtain ⟨x, hx, hxσ⟩ := compS_reassoc hcb hcσ
  obtain ⟨y, hy, hyσ⟩ := compS_lcomm hx hxσ
  refine sem_iff.mp h₂ δ (w₂ :: w₁ :: γ) _ hδ (gDen_mk ?_ ?_)
  · have := (gDen_iff.mp hg₂').1
    simpa using this
  · exact ⟨b₂, y, hyσ, hw₂,
      ⟨b₁, σ₂, hy, hw₁, (gDen_iff.mp hg₂').2⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_156 := BoCa.Fig16.LogRel.tensorE_compat
alias TR.«⊗E-compat» := BoCa.Fig16.LogRel.tensorE_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.157 (⊕I-compat) · `[TR]` p. 41 · `proved`

> Δ; Γ ⊨ e : Tᵢ
> ─────────────────────── ⊕I
> Δ; Γ ⊨ i e : T₁ ⊕ T₂

**Printed proof, transcribed.** Suppose H1; let `δ ∈ ⟦Δ⟧`, `γ`.  Apply `wp-bind`: `𝒢⟦Γ⟧δ(γ) ⊨ wp(eγ){v. wp(i v){𝒱⟦T₁ ⊕ T₂⟧δ}}`.  Apply H1 and `wp-mono`.  Fold `𝒱⟦⊕⟧`; follows from `wp-val`.

Schematic in `i`, as Lemma 6.72: one declaration per `i`.

**Lean.** `BoCa.Fig16.LogRel.sumI₁_compat`, aliases `TR.lemma_6_157_1`, `TR.«⊕I-compat₁»`, tag `[as printed]`; `BoCa.Fig16.LogRel.sumI₂_compat`, aliases `TR.lemma_6_157_2`, `TR.«⊕I-compat₂»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.sumI₁_compatX`; `BoCa.Fig16.LogRel.Typed.sumI₂_compatX`.

**Literal reading.** `BoCa.Fig16.LogRel.sumI₁_refused_on_TR3`; `BoCa.TR3.derives_wInj` (`Paper/LiteralReadings/S6_8_FundamentalProperty.lean`).

**Note.** Over `[TR]` §3's printed machine, which has no frame `injᵢ K`, the conclusion is refused at `e = free (alloc ())`, a closed instance p. 2's `⊕I` types (§12.42, D6).
-/
/-- `[TR]` Lemma 6.157 (`⊕I-compat`, p. 41) at `i = 1`.  `[as printed]` -/
theorem sumI₁_compat {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T₁ T₂ : Ty}
    (h : Sem Δ Γ e T₁) : Sem Δ Γ (.inj₁ e) (.sum T₁ T₂) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  refine wp_bind_mono (.inj₁ .hole) (substAll γ e) (vDen T₁ δ)
    (vDen (.sum T₁ T₂) δ) ?_ _ (sem_iff.mp h δ γ ρ hδ hg)
  intro v σ hv
  exact wp_inj₁ v _ _ (wp_val (.inj₁ v) _ _ (Or.inl ⟨v, pure_sep_mk rfl hv⟩))

end BoCa.Fig16.LogRel

alias TR.lemma_6_157_1 := BoCa.Fig16.LogRel.sumI₁_compat
alias TR.«⊕I-compat₁» := BoCa.Fig16.LogRel.sumI₁_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- `[TR]` Lemma 6.157 (`⊕I-compat`, p. 41) at `i = 2`.  `[as printed]` -/
theorem sumI₂_compat {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T₁ T₂ : Ty}
    (h : Sem Δ Γ e T₂) : Sem Δ Γ (.inj₂ e) (.sum T₁ T₂) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  refine wp_bind_mono (.inj₂ .hole) (substAll γ e) (vDen T₂ δ)
    (vDen (.sum T₁ T₂) δ) ?_ _ (sem_iff.mp h δ γ ρ hδ hg)
  intro v σ hv
  exact wp_inj₂ v _ _ (wp_val (.inj₂ v) _ _ (Or.inr ⟨v, pure_sep_mk rfl hv⟩))

end BoCa.Fig16.LogRel

alias TR.lemma_6_157_2 := BoCa.Fig16.LogRel.sumI₂_compat
alias TR.«⊕I-compat₂» := BoCa.Fig16.LogRel.sumI₂_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.158 (⊕E-compat) · `[TR]` p. 41 · `proved`

> Δ; Γ₁ ⊨ e₁ : T₁₁ ⊕ T₁₂    Δ; Γ₂, xᵢ : T₁ᵢ ⊨ eᵢ₂ : T₂    i ∈ {1, 2}
> ─────────────────────────────────────────────────────────────── ⊕E
> Δ; Γ₁, Γ₂ ⊨ match e₁ {x₁ ⇒ e₁₂, x₂ ⇒ e₂₂} : T₂

**Printed proof, transcribed.** Suppose H1 and, for each `i`, H2; let `δ ∈ ⟦Δ⟧`, `γ` split into `γ₁, γ₂`.  Apply `wp-bind`: `𝒢⟦Γ₁⟧δ(γ₁) ⋆ 𝒢⟦Γ₂⟧δ(γ₂) ⊨ wp(e₁γ₁){v₁. wp(match v₁ {…}){𝒱⟦T₂⟧δ}}`.  Apply H1, `wp-frame` and `wp-mono` at an arbitrary `v₁`.  Unfolding `𝒱⟦⊕⟧` gives `i` and `v′₁`: `𝒱⟦T₁ᵢ⟧δ(v′₁) ⋆ 𝒢⟦Γ₂⟧δ(γ₂) ⊨ wp(match i v′₁ {…}){𝒱⟦T₂⟧δ}`.  Follows from `wp-⊕` and H2 with `γ₂[xᵢ ↦ v′₁]`.

**Lean.** `BoCa.Fig16.LogRel.sumE_compat`, aliases `TR.lemma_6_158`, `TR.«⊕E-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.sumE_compatX`.
-/
/-- `[TR]` Lemma 6.158 (`⊕E-compat`, p. 41).  `γ₂[xᵢ ↦ v₁′]` is `v₁′ :: γ`.
`[as printed]` -/
theorem sumE_compat {Δ : LifeCtx} {Γ Γs Γb : Ctx Ty} {es e₁ e₂ : Expr}
    {T₁ T₂ T : Ty} (hsp : Ctx.Split Γ Γs Γb)
    (h₀ : Sem Δ Γs es (.sum T₁ T₂))
    (hb₁ : Sem Δ (⟨T₁, true⟩ :: Γb) e₁ T)
    (hb₂ : Sem Δ (⟨T₂, true⟩ :: Γb) e₂ T) :
    Sem Δ Γ (.case es e₁ e₂) T := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDen_split hsp hg
  refine wp_bind_frame (.case .hole (Expr.psub 1 γ e₁) (Expr.psub 1 γ e₂))
    (substAll γ es) (vDen (.sum T₁ T₂) δ) (gDen δ Γb γ) (vDen T δ) ?_ _
    ⟨ρ₁, ρ₂, hc, sem_iff.mp h₀ δ γ ρ₁ hδ hg₁, hg₂⟩
  rintro v σ ⟨σ₁, σ₂, hcσ, hsum, hg₂'⟩
  obtain ⟨hlen, hgs⟩ := gDen_iff.mp hg₂'
  rcases hsum with ⟨w, hs⟩ | ⟨w, hs⟩
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hs
    have hsub : substAll (w :: γ) e₁ = Expr.subst 0 w (Expr.psub 1 γ e₁) := by
      show Expr.psub 0 (w :: γ) e₁ = _
      rw [Expr.psub_cons 0 w γ e₁, Val.shift_zero]
    refine wp_sum₁ w (Expr.psub 1 γ e₁) (Expr.psub 1 γ e₂) _ _ ?_
    rw [← hsub]
    exact sem_iff.mp hb₁ δ (w :: γ) _ hδ
      (gDen_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hw, hgs⟩)
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hs
    have hsub : substAll (w :: γ) e₂ = Expr.subst 0 w (Expr.psub 1 γ e₂) := by
      show Expr.psub 0 (w :: γ) e₂ = _
      rw [Expr.psub_cons 0 w γ e₂, Val.shift_zero]
    refine wp_sum₂ w (Expr.psub 1 γ e₁) (Expr.psub 1 γ e₂) _ _ ?_
    rw [← hsub]
    exact sem_iff.mp hb₂ δ (w :: γ) _ hδ
      (gDen_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hw, hgs⟩)

end BoCa.Fig16.LogRel

alias TR.lemma_6_158 := BoCa.Fig16.LogRel.sumE_compat
alias TR.«⊕E-compat» := BoCa.Fig16.LogRel.sumE_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.159 (⊸I-compat) · `[TR]` p. 41 · `proved`

> Δ; Γ, x : T₁ ⊨ e : T₂
> ──────────────────────── ⊸I
> Δ; Γ ⊨ λx.e : T₁ ⊸ T₂

**Printed proof, transcribed.** Suppose H1; let `δ ∈ ⟦Δ⟧`, `γ`.  Apply `wp-val`; unfold `𝒱⟦⊸⟧` and let `v′` be arbitrary: `𝒢⟦Γ⟧δ(γ) ⋆ 𝒱⟦T₁⟧δ(v′) ⊨ wp((λx.eγ) v′){𝒱⟦T₂⟧δ}`.  Follows from `wp-⊸` and H1.

**Lean.** `BoCa.Fig16.LogRel.lolliI_compat`, aliases `TR.lemma_6_159`, `TR.«⊸I-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.lolliI_compatX`.
-/
/-- `[TR]` Lemma 6.159 (`⊸I-compat`, p. 41).  `[as printed]` -/
theorem lolliI_compat {Δ : LifeCtx} {Γ : Ctx Ty} {body : Expr} {T₁ T₂ : Ty}
    (h : Sem Δ (⟨T₁, true⟩ :: Γ) body T₂) :
    Sem Δ Γ (.val (.lam body)) (.lolli T₁ T₂) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  obtain ⟨hlen, hgs⟩ := gDen_iff.mp hg
  show wp (.val (.lam (Expr.psub 1 γ body))) _ ρ
  refine wp_val _ _ _ ?_
  intro v' ρ₁ ρ₂ hv' hcomp
  have hsub : substAll (v' :: γ) body = Expr.subst 0 v' (Expr.psub 1 γ body) := by
    show Expr.psub 0 (v' :: γ) body = _
    rw [Expr.psub_cons 0 v' γ body, Val.shift_zero]
  refine wp_lolli (Expr.psub 1 γ body) v' _ _ ?_
  rw [← hsub]
  exact sem_iff.mp h δ (v' :: γ) _ hδ
    (gDen_mk (by simpa using hlen) ⟨ρ₁, ρ, ResU.CompS.comm hcomp, hv', hgs⟩)

end BoCa.Fig16.LogRel

alias TR.lemma_6_159 := BoCa.Fig16.LogRel.lolliI_compat
alias TR.«⊸I-compat» := BoCa.Fig16.LogRel.lolliI_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.160 (⊸E-compat) · `[TR]` p. 42 · `proved`

> Δ; Γ₁ ⊨ e₁ : T₁    Δ; Γ₂ ⊨ e₂ : T₁ ⊸ T₂
> ──────────────────────────────────────── ⊸E
> Δ; Γ₁, Γ₂ ⊨ e₂ e₁ : T₂

**Printed proof, transcribed.** Suppose H1, H2; let `δ ∈ ⟦Δ⟧`, `γ` split into `γ₁, γ₂`.  Apply `wp-bind`: `𝒢⟦Γ₁⟧δ(γ₁) ⋆ 𝒢⟦Γ₂⟧δ(γ₂) ⊨ wp(e₁γ₁){v₁. wp(e₂γ₂ v₁){𝒱⟦T₂⟧δ}}`.  Apply H1, `wp-frame` and `wp-mono` at an arbitrary `v₁`; apply `wp-bind`: `𝒱⟦T₁⟧δ(v₁) ⋆ 𝒢⟦Γ₂⟧δ(γ₂) ⊨ wp(e₂γ₂){v₂. wp(v₂ v₁){𝒱⟦T₂⟧δ}}`.  Apply H2, `wp-frame` and `wp-mono` at an arbitrary `v₂`: `𝒱⟦T₁⟧δ(v₁) ⋆ 𝒱⟦T₁ ⊸ T₂⟧(v₂) ⊨ wp(v₂ v₁){𝒱⟦T₂⟧δ}`.  Follows from unfolding `𝒱⟦⊸⟧`.

**Lean.** `BoCa.Fig16.LogRel.lolliE_compat`, aliases `TR.lemma_6_160`, `TR.«⊸E-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.lolliE_compatX`.
-/
/-- `[TR]` Lemma 6.160 (`⊸E-compat`, p. 42).  `e₁` is the argument and `e₂` the
function (§12.2); `Γ₁`, the argument's half, is framed off first, because
`Kont`'s `e K` comes before `K v`.  `[as printed]` -/
theorem lolliE_compat {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx Ty} {f arg : Expr} {T₁ T₂ : Ty}
    (hsp : Ctx.Split Γ Γ₁ Γ₂)
    (ha : Sem Δ Γ₁ arg T₁) (hf : Sem Δ Γ₂ f (.lolli T₁ T₂)) :
    Sem Δ Γ (.app f arg) T₂ := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDen_split hsp hg
  refine wp_bind_frame (.appR (substAll γ f) .hole) (substAll γ arg)
    (vDen T₁ δ) (gDen δ Γ₂ γ) (vDen T₂ δ) ?_ _
    ⟨ρ₁, ρ₂, hc, sem_iff.mp ha δ γ ρ₁ hδ hg₁, hg₂⟩
  rintro v₁ σ ⟨σ₁, σ₂, hcσ, hv₁, hg₂'⟩
  refine wp_bind_frame (.appL .hole v₁) (substAll γ f)
    (vDen (.lolli T₁ T₂) δ) (vDen T₁ δ v₁) (vDen T₂ δ) ?_ _
    ⟨σ₂, σ₁, ResU.CompS.comm hcσ, sem_iff.mp hf δ γ σ₂ hδ hg₂', hv₁⟩
  rintro v₂ τ ⟨τ₁, τ₂, hcτ, hv₂, hv₁'⟩
  exact hv₂ v₁ τ₂ τ hv₁' hcτ

end BoCa.Fig16.LogRel

alias TR.lemma_6_160 := BoCa.Fig16.LogRel.lolliE_compat
alias TR.«⊸E-compat» := BoCa.Fig16.LogRel.lolliE_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.161 (∀I-compat) · `[TR]` p. 42 · `variant`

> Δ, ('a ⊏ @b); Γ ⊨ e : T
> ───────────────────────────── ∀I
> Δ; Γ ⊨ λe : ∀('a ⊏ @b). T

**Printed proof, transcribed.** Suppose H1; let `δ ∈ ⟦Δ⟧`, `γ`.  Apply `wp-val`: `𝒢⟦Γ⟧δ(γ) ⊨ 𝒱⟦∀('a ⊏ @b). T⟧δ(λ_.eγ)`.  Unfold `𝒱⟦∀⟧` and let `α ⊏ @bδ` be arbitrary.  By `Δ-extend`, `δ['a ↦ α] ∈ ⟦Δ, ('a ⊏ @b)⟧`.  Extend `𝒢⟦Γ⟧δ` with `δ['a ↦ α]`: `𝒢⟦Γ⟧δ['a↦α](γ) ⊨ wp((λ_.eγ) ()){𝒱⟦T⟧δ['a↦α]}`.  Follows from `wp-⊸` and H1.

**Lean.** `BoCa.Fig16.LogRel.allI_compat`, aliases `TR.lemma_6_161`, `TR.«∀I-compat»`, tag `[variant: adds the freshness of `'a` for `@b`, for the bounds of `Δ` and for
the live types of `Γ`, which the printed proof takes from its named binder and
does not state]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.allI_compatX`.

**Note.** `allISide_of_scopedB` reads the three freshnesses off `DerivesWf.allI` (§12.44, C14).
-/
/-- `[TR]` Lemma 6.161 (`∀I-compat`, p. 42).
`[variant: adds the freshness of `'a` for `@b`, for the bounds of `Δ` and for
the live types of `Γ`, which the printed proof takes from its named binder and
does not state]`

`Λ.e ≜ λ_.e` (§12.14), so the premise's context gains a dead slot and the closing
substitution a `()` at it.  `Δ ⊨ @b` is not a hypothesis: the `∀` clause's bound
is a proposition about `@bδ` (L3), so the arbitrary `α ⊏ @bδ` carries `@bδ`
defined. -/
theorem allI_compat {Δ : LifeCtx} {Γ : Ctx Ty} {x : LifeVar} {b : Lifetime.Life}
    {S : Ty} {e : Expr} {T : Ty} (hx : Δ.find? x = none)
    /- "By Δ-extend, δ['a↦α] ∈ ⟦Δ, ('a ⊏ @b)⟧", at `'a` itself: the bound read
       there is `@bδ['a↦α]`, and it is `@bδ` — the one `α ⊏ @bδ` was taken
       against — only if `@b` does not mention `'a`. -/
    (hbx : b.mentions x = false)
    /- The same sentence at every `'y ∈ dom(Δ)`: `δ('y) ⊏ Δ('y)δ` is what
       `δ ∈ ⟦Δ⟧` gives, and it carries over to `δ['a↦α]` only if `Δ('y)` does
       not mention `'a`. -/
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    /- "Extend 𝒢⟦Γ⟧δ with δ['a↦α]": `𝒱⟦Γ(x)⟧δ['a↦α]` is `𝒱⟦Γ(x)⟧δ` at each live
       slot only if `'a` is free in none of their types. -/
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ LFree x s.ty)
    (h : Sem (Δ.extend x b) (⟨S, false⟩ :: Γ) e T) :
    Sem Δ Γ (.val (.lam e)) (.all x b T) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  obtain ⟨hlen, hgs⟩ := gDen_iff.mp hg
  show wp (.val (.lam (Expr.psub 1 γ e))) _ ρ
  refine wp_val _ _ _ ?_
  -- unfold 𝒱⟦∀⟧, let `α ⊏ @bδ` be arbitrary; the wand composes `ρ ● ∅`, so what
  -- it hands back is `ρ` itself
  intro α ρ₁ ρ₂ hpure hcomp
  obtain ⟨rfl, β, hβ, hlt⟩ := hpure
  have hρ₂ : ρ₂ = ρ := eq_of_compS_empty_left (ResU.CompS.comm hcomp)
  subst ρ₂
  -- `δ['a↦α]` leaves every lookup but `'a` alone
  have hfind : ∀ z, z ≠ x → (δ.extend x α).find? z = δ.find? z :=
    fun z hz => find?_extend_ne δ α (Ne.symm hz)
  -- "By Δ-extend, δ['a↦α] ∈ ⟦Δ, ('a ⊏ @b)⟧"
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
  -- "Follows from wp-⊸ and H1": the closing substitution gains `()` at the
  -- dead slot
  have hsub : substAll (Val.unit :: γ) e = Expr.subst 0 Val.unit (Expr.psub 1 γ e) := by
    show Expr.psub 0 (Val.unit :: γ) e = _
    rw [Expr.psub_cons 0 Val.unit γ e, Val.shift_zero]
  refine wp_lolli (Expr.psub 1 γ e) Val.unit _ _ ?_
  rw [← hsub]
  refine sem_iff.mp h (δ.extend x α) (Val.unit :: γ) ρ hδ'
    (gDen_mk (by simpa using hlen) ?_)
  -- "Extend 𝒢⟦Γ⟧δ with δ['a↦α]"
  show gSep (δ.extend x α) Γ γ ρ
  have heq : gSep δ Γ γ = gSep (δ.extend x α) Γ γ :=
    gSep_congr (fun s hs hl => vDen_congr s.ty (fun z hz =>
      (hfind z (by rintro rfl; exact hΓx s hs hl hz)).symm))
  rw [← heq]
  exact hgs

end BoCa.Fig16.LogRel

alias TR.lemma_6_161 := BoCa.Fig16.LogRel.allI_compat
alias TR.«∀I-compat» := BoCa.Fig16.LogRel.allI_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.162 (∀E-compat) · `[TR]` p. 42 · `proved`

> Δ; Γ ⊨ e : ∀('a ⊏ @b). T    Δ ⊨ @a ⊏ @b
> ───────────────────────────────────────── ∀E
> Δ; Γ ⊨ e () : T[@a/'a]

**Printed proof, transcribed.** Suppose H1 and `Δ ⊨ @a ⊏ @b` (H2); let `δ ∈ ⟦Δ⟧`, `γ`.  Apply `wp-bind`: `𝒢⟦Γ⟧δ(γ) ⊨ wp(eγ){v. wp(v ()){𝒱⟦T[@a/'a]⟧δ}}`.  Apply H1 and `wp-mono` at an arbitrary `v`: `𝒱⟦∀('a ⊏ @b). T⟧δ(v) ⊨ wp(v ()){𝒱⟦T[@a/'a]⟧δ}`.  Unfold `𝒱⟦∀⟧` and instantiate with `@aδ`, which is `⊏ @bδ` by H2.  Apply `wp-mono` at an arbitrary `v′`: `𝒱⟦T⟧δ['a↦@aδ](v′) ⊨ 𝒱⟦T[@a/'a]⟧δ(v′)`.  Follows from `Δ-subst`.

**Lean.** `BoCa.Fig16.LogRel.allE_compat`, aliases `TR.lemma_6_162`, `TR.«∀E-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.allE_compatX`.

**Literal reading.** `BoCa.Fig16.LogRel.MutPayloadSubst.subst_eq` (`Paper/LiteralReadings/S6_8_FundamentalProperty.lean`).
-/
/-- `[TR]` Lemma 6.162 (`∀E-compat`, p. 42).  `e[] ≜ e ()` (§12.14), `T[@a/'a]` is
`Ty.instLife`, and `Δ-subst` is `vDen_instLife`.  `[as printed]` -/
theorem allE_compat {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {x : LifeVar}
    {b : Lifetime.Life} {T : Ty} {a : Lifetime.Life}
    (h : Sem Δ Γ e (.all x b T)) (hlt : Δ.EntailsLt a b) :
    Sem Δ Γ (.app e (.val .unit)) (Ty.instLife x a T) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  obtain ⟨α, β, ha, hb, hab⟩ := hlt δ hδ
  refine wp_bind_mono (.appL .hole .unit) (substAll γ e)
    (vDen (.all x b T) δ) (vDen (Ty.instLife x a T) δ) ?_ _
    (sem_iff.mp h δ γ ρ hδ hg)
  intro v σ hv
  rw [vDen_instLife x a T ha]
  exact hv α PMap.empty σ ⟨rfl, β, hb, hab⟩ (ResU.comp_empty_right σ)

end BoCa.Fig16.LogRel

alias TR.lemma_6_162 := BoCa.Fig16.LogRel.allE_compat
alias TR.«∀E-compat» := BoCa.Fig16.LogRel.allE_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.163 ([]I-compat) · `[TR]` p. 42 · `proved`

> Δ; Γ ⊨ e : T    Δ ⊨ Γ ⊐ @a
> ──────────────────────────── []I
> Δ; Γ ⊨ e : [@a] T

**Printed proof, transcribed.** Suppose H1 and `Δ ⊢ Γ ⊐ @a` (H2); let `δ ∈ ⟦Δ⟧`, `γ`.  The goal is `𝒢⟦Γ⟧δ(γ) ⊨ wp(e){𝒱⟦[@a] T⟧δ}`.  Apply Lemma 6.62 with H2; unfold `𝒱⟦[]⟧`: `[@aδ]𝒢⟦Γ⟧δ(γ) ⊨ wp(e){[@aδ]𝒱⟦T⟧δ}`.  Follows from `wp-[]`, `[]-mono` and H1.

**Lean.** `BoCa.Fig16.LogRel.boxI_compat`, aliases `TR.lemma_6_163`, `TR.«[]I-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.boxI_compatX`.

**Note.** `@aδ` has only to be defined, which is `Ctx.Outlives`'s presupposition, p. 2's `Δ ⊨ @a` (§12.67(a)).
-/
/-- `[TR]` Lemma 6.163 (`[]I-compat`, p. 42).  6.62 is `gDen_box` and `wp-[]` is
`Fig16.BoLo.wp_box`.  `[as printed]` -/
theorem boxI_compat {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} {a : Lifetime.Life}
    (h : Sem Δ Γ e T) (hΓ : Ctx.Outlives Δ Γ a) :
    Sem Δ Γ e (.box a T) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  -- `@aδ` is defined: `[TR]` p. 2's `Δ ⊨ @a`, which `Ctx.Outlives` carries
  obtain ⟨α, ha⟩ := hΓ.1 δ hδ
  -- unfold 𝒱⟦[]⟧ at the defined `@aδ`
  have hv : vDen (.box a T) δ = fun v => box α (vDen T δ v) := by
    funext v
    exact atLife_eq ha _
  rw [hv]
  -- `wp-[]` at `[@aδ] wp(e){𝒱⟦T⟧δ}`, whose two conjuncts are H1 and 6.62
  exact wp_box α _ _ ρ
    ⟨sem_iff.mp h δ γ ρ hδ hg, (gDen_box hδ ha hΓ γ ρ hg).2⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_163 := BoCa.Fig16.LogRel.boxI_compat
alias TR.«[]I-compat» := BoCa.Fig16.LogRel.boxI_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.164 ([]E-compat) · `[TR]` p. 43 · `proved`

> Δ; Γ ⊨ e : [@a] T
> ─────────────────── []E
> Δ; Γ ⊨ e : T

**Printed proof, transcribed.** Suppose H1; let `δ ∈ ⟦Δ⟧`, `γ`.  Follows from H1, `wp-mono`, unfolding `𝒱⟦[]⟧`, and `[]l`.

**Lean.** `BoCa.Fig16.LogRel.boxE_compat`, aliases `TR.lemma_6_164`, `TR.«[]E-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.boxE_compatX`.
-/
/-- `[TR]` Lemma 6.164 (`[]E-compat`, p. 43).  `[]l` is `Fig16.BoLo.box_L`.
`[as printed]` -/
theorem boxE_compat {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {a : Lifetime.Life} {T : Ty}
    (h : Sem Δ Γ e (.box a T)) : Sem Δ Γ e T := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  refine wp_mono (fun v => ?_) _ _ (sem_iff.mp h δ γ ρ hδ hg)
  rintro σ ⟨-, -, hP, -⟩
  exact hP

end BoCa.Fig16.LogRel

alias TR.lemma_6_164 := BoCa.Fig16.LogRel.boxE_compat
alias TR.«[]E-compat» := BoCa.Fig16.LogRel.boxE_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.165 (alloc-compat) · `[TR]` p. 43 · `proved`

> ───────────────────────── alloc
> Δ; ∅ ⊨ alloc : T ⊸ Ref T

**Printed proof, transcribed.** Let `δ ∈ ⟦∅⟧`, `γ`.  Apply `wp-val` and unfold `𝒱⟦⊸⟧` at an arbitrary `v`: `𝒱⟦T⟧δ(v) ⊨ wp(alloc v){𝒱⟦Ref T⟧δ}`.  Follows from `wp-alloc` and unfolding `𝒱⟦Ref⟧`.

**Lean.** `BoCa.Fig16.LogRel.alloc_compat`, aliases `TR.lemma_6_165`, `TR.«alloc-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.alloc_compatX`.
-/
/-- `[TR]` Lemma 6.165 (`alloc-compat`, p. 43).  `wp-alloc` is 6.141, its wand
instantiated at the location `PMap.exists_fresh` picks.  `[as printed]` -/
theorem alloc_compat {Δ : LifeCtx} {Γ : Ctx Ty} {T : Ty} (hΓ : Ctx.Dead Γ) :
    Sem Δ Γ (.val (.prim .alloc)) (.lolli T (.ref T)) := by
  refine sem_iff.mpr fun δ γ ρ _ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  refine wp_val (Val.prim .alloc) _ _ ?_
  -- unfold 𝒱⟦⊸⟧, let `v` be arbitrary; the wand composes `∅ ● ρ₁`, so what it
  -- hands back is the argument's own resource
  intro v ρ₁ ρ₂ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  -- `wp-alloc`; what is left is its premise `∀ℓ. ℓ ↦ v ─⋆ 𝒱⟦Ref T⟧δ(ℓ)`
  refine wp_alloc v _ _ ?_
  intro ℓ σ τ hcell hc
  -- fold 𝒱⟦Ref T⟧ at `v′ = v`: the new cell, then the argument's own resource
  exact ⟨ℓ, v, pure_sep_mk rfl ⟨σ, ρ₁, ResU.CompS.comm hc, hcell, hv⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_165 := BoCa.Fig16.LogRel.alloc_compat
alias TR.«alloc-compat» := BoCa.Fig16.LogRel.alloc_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.166 (free-compat) · `[TR]` p. 43 · `proved`

> ───────────────────────── free
> Δ; ∅ ⊨ free : Ref T ⊸ T

**Printed proof, transcribed.** Let `δ ∈ ⟦∅⟧`, `γ`.  Apply `wp-val` and unfold `𝒱⟦⊸⟧` at an arbitrary `v`: `𝒱⟦Ref T⟧δ(v) ⊨ wp(free v){𝒱⟦T⟧δ}`.  Follows from unfolding `𝒱⟦Ref⟧` and `wp-free`.

**Lean.** `BoCa.Fig16.LogRel.free_compat`, aliases `TR.lemma_6_166`, `TR.«free-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.free_compatX`.
-/
/-- `[TR]` Lemma 6.166 (`free-compat`, p. 43).  `[as printed]` -/
theorem free_compat {Δ : LifeCtx} {Γ : Ctx Ty} {T : Ty} (hΓ : Ctx.Dead Γ) :
    Sem Δ Γ (.val (.prim .free)) (.lolli (.ref T) T) := by
  refine sem_iff.mpr fun δ γ ρ _ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  refine wp_val (Val.prim .free) _ _ ?_
  intro v ρ₁ ρ₂ hv hcomp
  obtain ⟨ℓ, w, hs⟩ := hv
  obtain ⟨rfl, hsep⟩ := pure_sep_iff.mp hs
  have hρ₂ : ρ₂ = ρ₁ := eq_of_compS_empty_left hcomp
  subst hρ₂
  exact wp_free ℓ w _ _ hsep

end BoCa.Fig16.LogRel

alias TR.lemma_6_166 := BoCa.Fig16.LogRel.free_compat
alias TR.«free-compat» := BoCa.Fig16.LogRel.free_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.167 (⊑imm-compat) · `[TR]` p. 43 · `proved`

> Δ; Γ ⊨ e : Imm @b T    Δ ⊨ @a ⊑ @b
> ─────────────────────────────────── ⊑imm
> Δ; Γ ⊨ e : Imm @a T

**Printed proof, transcribed.** Suppose H1 and `Δ ⊨ @a ⊑ @b` (H2); let `δ ∈ ⟦Δ⟧`, `γ`.  Apply H1 to `𝒢⟦Γ⟧δ(γ)`, then `wp-mono` at an arbitrary `v`: `𝒱⟦Imm @b T⟧δ(v) ⊨ 𝒱⟦Imm @a T⟧δ(v)`.  Unfold `𝒱⟦Imm⟧δ`, with `v = ℓ`: `ℓ ↦I_{@bδ} 𝒱⟦T⟧δ ⊨ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦I_{@aδ} 𝒱⟦T⟧δ`.  Apply `I⊒` with H2; choose `ℓ`.

**Lean.** `BoCa.Fig16.LogRel.immSub_compat`, aliases `TR.lemma_6_167`, `TR.«⊑imm-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.immSub_compatX`.
-/
/-- `[TR]` Lemma 6.167 (`⊑imm-compat`, p. 43).  `I ⊒` is
`Fig16.BoLo.ptoImm_antitone` (6.114).  `[as printed]` -/
theorem immSub_compat {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr}
    {a b : Lifetime.Life} {T : Ty}
    (h : Sem Δ Γ e (.imm b T)) (hle : Δ.EntailsLe a b) :
    Sem Δ Γ e (.imm a T) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  obtain ⟨α, β, ha, hb, hle'⟩ := hle δ hδ
  refine wp_mono (fun v => ?_) _ _ (sem_iff.mp h δ γ ρ hδ hg)
  rintro σ ⟨β', hβ', ℓ, hs⟩
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  obtain ⟨hvl, himm⟩ := pure_sep_iff.mp hs
  exact ⟨α, ha, ℓ, pure_sep_mk hvl (ptoImm_antitone hle' _ _ himm)⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_167 := BoCa.Fig16.LogRel.immSub_compat
alias TR.«⊑imm-compat» := BoCa.Fig16.LogRel.immSub_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.168 (⊑mut-compat) · `[TR]` p. 43 · `proved`

> Δ; Γ ⊨ e : Mut @b T    Δ ⊨ @a ⊑ @b
> ─────────────────────────────────── ⊑mut
> Δ; Γ ⊨ e : Mut @a T

**Printed proof, transcribed.** As Lemma 6.167, at `Mut`: apply H1 and `wp-mono`; unfold `𝒱⟦Mut⟧δ` with `v = ℓ`: `ℓ ↦M_{@bδ} 𝒱⟦T⟧δ ⊨ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦M_{@aδ} 𝒱⟦T⟧δ`.  Apply `M⊒` with H2; choose `ℓ`.

**Lean.** `BoCa.Fig16.LogRel.mutSub_compat`, aliases `TR.lemma_6_168`, `TR.«⊑mut-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.mutSub_compatX`.
-/
/-- `[TR]` Lemma 6.168 (`⊑mut-compat`, p. 43).  `M ⊒` is
`Fig16.BoLo.ptoMut_antitone` (6.118).  `[as printed]` -/
theorem mutSub_compat {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr}
    {a b : Lifetime.Life} {T : Ty}
    (h : Sem Δ Γ e (.mut b T)) (hle : Δ.EntailsLe a b) :
    Sem Δ Γ e (.mut a T) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  obtain ⟨α, β, ha, hb, hle'⟩ := hle δ hδ
  refine wp_mono (fun v => ?_) _ _ (sem_iff.mp h δ γ ρ hδ hg)
  rintro σ ⟨β', hβ', ℓ, hs⟩
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  obtain ⟨hvl, hmut⟩ := pure_sep_iff.mp hs
  exact ⟨α, ha, ℓ, pure_sep_mk hvl (ptoMut_antitone hle' _ _ hmut)⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_168 := BoCa.Fig16.LogRel.mutSub_compat
alias TR.«⊑mut-compat» := BoCa.Fig16.LogRel.mutSub_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.169 (swap-compat) · `[TR]` p. 44 · `proved`

> ────────────────────────────────────────── swap
> Δ; ∅ ⊨ swap : Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁

**Printed proof, transcribed.** Let `δ ∈ ⟦∅⟧`, `γ`.  Apply `wp-val`; unfold `𝒱⟦⊸⟧` at `v₁` and apply `wp-⊸`; apply `wp-val`, unfold `𝒱⟦⊸⟧` at `v₂` and apply `wp-⊸`: `𝒱⟦Ref T₁⟧δ(v₁) ⋆ 𝒱⟦T₂⟧δ(v₂) ⊨ wp(let z = load v₁; store v₁ v₂; (v₁, z)){𝒱⟦Ref T₂ ⊗ T₁⟧δ}`.  Unfold `let` to `(λz. store v₁ v₂; (v₁, z)) (load v₁)` and apply `wp-bind`.  Unfold `𝒱⟦Ref⟧`: `v₁ = ℓ`, `ℓ ↦ v′₁ ⋆ 𝒱⟦T₁⟧δ(v′₁) ⋆ 𝒱⟦T₂⟧δ(v₂)`.  Apply `wp-load`, `wp-⊸` and `wp-bind`; then `wp-store` and `wp-val`: `ℓ ↦ v₂ ⋆ 𝒱⟦T₁⟧δ(v′₁) ⋆ 𝒱⟦T₂⟧δ(v₂) ⊨ 𝒱⟦Ref T₂ ⊗ T₁⟧δ((ℓ, v′₁))`, which follows by folding and unfolding the `𝒱` definitions.

**Lean.** `BoCa.Fig16.LogRel.swap_compat`, aliases `TR.lemma_6_169`, `TR.«swap-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.swap_compatX`.

**Literal reading.** `BoCa.Fig16.LogRel.swap_step_blocked_on_TR3` (`Paper/LiteralReadings/S6_8_FundamentalProperty.lean`).

**Note.** `[TR]`'s proof runs `[CONF]` Fig. 3b's body, which returns the old payload (§12.20).  Over `[TR]` §3's printed machine, which has no frame `K; e`, `wp` is refused at the step `store ℓ v₂; (ℓ, w)` (§12.42, D6).
-/
/-- `[TR]` Lemma 6.169 (`swap-compat`, p. 44).  `[as printed]` -/
theorem swap_compat {Δ : LifeCtx} {Γ : Ctx Ty} {T₁ T₂ : Ty} (hΓ : Ctx.Dead Γ) :
    Sem Δ Γ swap (axSwapTy T₁ T₂) := by
  refine sem_iff.mpr fun δ γ ρ _ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  show wp swap _ _
  refine wp_val _ _ _ ?_
  -- unfold 𝒱⟦⊸⟧, let `v₁` be arbitrary, apply `wp-⊸`
  intro v₁ ρ₁ τ₀ hv₁ hcomp
  have hτ₀ : τ₀ = ρ₁ := eq_of_compS_empty_left hcomp
  subst hτ₀
  -- unfold 𝒱⟦Ref⟧: `v₁ = ℓ`, and the resource is `ℓ ↦ w ⋆ 𝒱⟦T₁⟧δ(w)`
  obtain ⟨ℓ, w, hs₁⟩ := hv₁
  obtain ⟨rfl, b₁, b₂, hcb, rfl, hT₁⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (elet (.app load' v1)
          (.seq (.app (.app store' v2) v1) (.pair v2 v0)))))
      = Expr.val (Val.lam (elet (eLoad ℓ)
          (.seq (.app (.app store' (.val (.loc ℓ))) v1)
                (.pair (.val (.loc ℓ)) v0)))) := by
    simp [elet, eLoad, Expr.subst, Expr.shift, v0, v1, v2, load', store']
  refine wp_lolli _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  -- `wp-val`; unfold 𝒱⟦⊸⟧ again, let `v₂` be arbitrary, apply `wp-⊸`
  refine wp_val _ _ _ ?_
  intro v₂ ρ₂ τ hv₂ hc₂
  have hβ₂ : Expr.subst 0 v₂
        (elet (eLoad ℓ) (.seq (.app (.app store' (.val (.loc ℓ))) v1)
                              (.pair (.val (.loc ℓ)) v0)))
      = elet (eLoad ℓ) (.seq (eStore ℓ (v₂.shift 1 0)) (.pair (.val (.loc ℓ)) v0)) := by
    simp [elet, eLoad, eStore, Expr.subst, v0, v1, store']
  refine wp_lolli _ v₂ _ _ ?_
  rw [hβ₂]
  -- `(ℓ↦w ● b₂) ● ρ₂` regrouped as `ℓ↦w ● (b₂ ● ρ₂)`
  obtain ⟨s, hs, hτ⟩ := compS_reassoc hcb hc₂
  -- `wp-bind` at the argument `load ℓ`, then `wp-load`
  refine wp_bind (.appR (.val (.lam _)) .hole) (eLoad ℓ) _ _ ?_
  refine wp_load ℓ w _ _ ⟨_, s, hτ, rfl, ?_⟩
  intro ρ' σ' hp' hc'
  subst hp'
  simp only [Kont.plug]
  have hβ₃ : Expr.subst 0 w
        (Expr.seq (eStore ℓ (v₂.shift 1 0)) (.pair (.val (.loc ℓ)) v0))
      = Expr.seq (eStore ℓ v₂) (.pair (.val (.loc ℓ)) (.val w)) := by
    simp [eStore, Expr.subst, v0,
      Expr.subst_shift 0 0 0 w v₂.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  refine wp_lolli _ w _ _ ?_
  rw [hβ₃]
  -- `wp-bind` at `store ℓ v₂`, then `wp-store`
  refine wp_bind (.seq .hole (.pair (.val (.loc ℓ)) (.val w))) (eStore ℓ v₂) _ _ ?_
  -- `[TR]` p. 4's `store↦` box takes `store ℓ v₂` in one step, and so does this
  -- machine: the partially applied `store ℓ` is `[TR]` p. 1's value `store v`
  -- and the application `(store) ℓ`, one term either way, so 6.145's redex is
  -- `eStore ℓ v₂` itself
  refine wp_store ℓ w v₂ _ _ ⟨_, s, ResU.CompS.comm hc', rfl, ?_⟩
  intro ρ₃ σ₃ hp₃ hc₃
  subst hp₃
  simp only [Kont.plug]
  -- `wp-1`, the pair, `wp-val`
  refine wp_1 _ _ _ ?_
  refine wp_pair (.loc ℓ) w _ _ (wp_val (.pair (.loc ℓ) w) _ _ ?_)
  -- fold 𝒱⟦Ref T₂ ⊗ T₁⟧: the reference now holds `v₂`, and `w` is the old payload
  obtain ⟨R, hR, hb₂R⟩ := compS_reassoc hs hc₃
  exact ⟨.loc ℓ, w, pure_sep_mk rfl
    ⟨R, b₂, ResU.CompS.comm hb₂R,
      ⟨ℓ, v₂, pure_sep_mk rfl ⟨_, ρ₂, ResU.CompS.comm hR, rfl, hv₂⟩⟩, hT₁⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_169 := BoCa.Fig16.LogRel.swap_compat
alias TR.«swap-compat» := BoCa.Fig16.LogRel.swap_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.170 (copy-compat) · `[TR]` p. 44 · `proved`

> Δ ⊨ copy : Imm @a T ⊸ (Imm @a T ⊗ Imm @a T)

**Printed proof, transcribed.** A table of steps.  Let `δ ∈ ⟦Δ⟧`; apply `wp-val`; let `v` be arbitrary; apply `wp⊸`: `𝒱⟦Imm @a T⟧δ(v) ⊨ 𝒱⟦Imm @a T ⊗ Imm @a T⟧δ(v, v)`.  Unfold, and choose `v₁ = v₂ = v`: `𝒱⟦Imm @a T⟧δ(v) ⊨ 𝒱⟦Imm @a T⟧δ(v) ⋆ 𝒱⟦Imm @a T⟧δ(v)`.  Unfold, substitute `v = ℓ`, unfold and simplify: `ℓ ↦I_{@aδ} 𝒱⟦T⟧ ⊨ (ℓ ↦I_{@aδ} 𝒱⟦T⟧) ⋆ (ℓ ↦I_{@aδ} 𝒱⟦T⟧)`.  Apply `I-Dup`.

**Lean.** `BoCa.Fig16.LogRel.copy_compat`, aliases `TR.lemma_6_170`, `TR.«copy-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.copy_compatX`.

**Literal reading.** `BoCa.Fig16.LogRel.copy_step_on_TR3` (`Paper/LiteralReadings/S6_8_FundamentalProperty.lean`).
-/
/-- `[TR]` Lemma 6.170 (`copy-compat`, p. 44).  `I-Dup` is `Fig16.BoLo.ptoImm_dup`
(6.116).  `[as printed]` -/
theorem copy_compat {Δ : LifeCtx} {Γ : Ctx Ty} {a : Lifetime.Life} {T : Ty}
    (hΓ : Ctx.Dead Γ) : Sem Δ Γ copy (axCopyTy a T) := by
  refine sem_iff.mpr fun δ γ ρ _ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  show wp copy _ _
  refine wp_val _ _ _ ?_
  intro v σ τ hv hcomp
  have hτ : τ = σ := eq_of_compS_empty_left hcomp
  subst hτ
  refine wp_lolli (.pair v0 v0) v _ _ ?_
  have hb : Expr.subst 0 v (.pair v0 v0) = Expr.pair (.val v) (.val v) := by
    simp [v0, Expr.subst]
  rw [hb]
  refine wp_pair v v _ _ (wp_val (.pair v v) _ _ ?_)
  -- unfold 𝒱⟦Imm⟧, then `I-Dup`
  obtain ⟨α, ha, ℓ, hs⟩ := hv
  obtain ⟨hvl, himm⟩ := pure_sep_iff.mp hs
  obtain ⟨τ₁, τ₂, hc, h₁, h₂⟩ := ptoImm_dup ℓ α (vDen T δ) _ himm
  exact ⟨v, v, pure_sep_mk rfl
    ⟨τ₁, τ₂, hc, ⟨α, ha, ℓ, pure_sep_mk hvl h₁⟩, ⟨α, ha, ℓ, pure_sep_mk hvl h₂⟩⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_170 := BoCa.Fig16.LogRel.copy_compat
alias TR.«copy-compat» := BoCa.Fig16.LogRel.copy_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.171 (forget-compat) · `[TR]` p. 44 · `proved`

> Δ ⊨ forget : B ⊸ 1 for all B ∈ {Imm @a T, Mut @a T, Unk}.

**Printed proof, transcribed.** A table of steps.  Let `δ ∈ ⟦Δ⟧`; apply `wp-val`; let `v` be arbitrary; apply `wp⊸`: `𝒱⟦B⟧δ(v) ⊨ wp(()){𝒱⟦1⟧δ}`.  Three cases.  `B = Imm @a T`: unfold, substitute `v = ℓ`; apply `wp-I-forget`, giving `ℓ ↦I 𝒱⟦T⟧ ⊨ ℓ ↦I 𝒱⟦T⟧ ⋆ wp(()){𝒱⟦1⟧δ}`; cancel `ℓ ↦I 𝒱⟦T⟧`: `emp ⊨ wp(()){𝒱⟦1⟧δ}`; apply `wp-val` and unfold: `emp ⊨ ⌜() = ()⌝`.  `B = Mut @a T`: the same with `wp-M-forget` and `ℓ ↦M 𝒱⟦T⟧`.  `B = Unk`: unfold to `emp ⊨ wp(()){𝒱⟦1⟧δ}`; apply `wp-val` and unfold.

One lemma with three cases; Lean states one declaration per case, aliased `TR.lemma_6_171_1` (`Imm`), `_2` (`Mut`), `_3` (`Unk`).

**Lean.** `BoCa.Fig16.LogRel.forgetImm_compat`, aliases `TR.lemma_6_171_1`, `TR.«forget-compat₁»`, tag `[as printed]`; `BoCa.Fig16.LogRel.forgetMut_compat`, aliases `TR.lemma_6_171_2`, `TR.«forget-compat₂»`, tag `[as printed]`; `BoCa.Fig16.LogRel.forgetUnk_compat`, aliases `TR.lemma_6_171_3`, `TR.«forget-compat₃»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.forgetImm_compatX`; `BoCa.Fig16.LogRel.Typed.forgetMut_compatX`; `BoCa.Fig16.LogRel.Typed.forgetUnk_compatX`.
-/
/-- `[TR]` Lemma 6.171 (`forget-compat`, pp. 44–45) at `B = Imm @a T`.
`[as printed]` -/
theorem forgetImm_compat {Δ : LifeCtx} {Γ : Ctx Ty} {a : Lifetime.Life} {T : Ty}
    (hΓ : Ctx.Dead Γ) : Sem Δ Γ forget (axForgetImmTy a T) := by
  refine sem_iff.mpr fun δ γ ρ _ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  show wp forget _ _
  refine wp_val _ _ _ ?_
  intro v σ τ hv hcomp
  have hτ : τ = σ := eq_of_compS_empty_left hcomp
  subst hτ
  refine wp_lolli unit' v _ _ ?_
  have hb : Expr.subst 0 v unit' = unit' := by simp [unit', Expr.subst]
  rw [hb]
  obtain ⟨α, -, ℓ, hs⟩ := hv
  obtain ⟨-, himm⟩ := pure_sep_iff.mp hs
  exact wp_I_forget ℓ α _ _ _ _
    ⟨_, PMap.empty, ResU.comp_empty_right _, himm, wp_val .unit _ _ ⟨rfl, rfl⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_171_1 := BoCa.Fig16.LogRel.forgetImm_compat
alias TR.«forget-compat₁» := BoCa.Fig16.LogRel.forgetImm_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- `[TR]` Lemma 6.171 (`forget-compat`, pp. 44–45) at `B = Mut @a T`, by
`wp-M-forget` (6.148), which applies to the clause `ℓ ↦ M @aδ 𝒱⟦T⟧δ` directly.
`[as printed]` -/
theorem forgetMut_compat {Δ : LifeCtx} {Γ : Ctx Ty} {a : Lifetime.Life} {T : Ty}
    (hΓ : Ctx.Dead Γ) : Sem Δ Γ forget (axForgetMutTy a T) := by
  refine sem_iff.mpr fun δ γ ρ _ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  show wp forget _ _
  refine wp_val _ _ _ ?_
  intro v σ τ hv hcomp
  have hτ : τ = σ := eq_of_compS_empty_left hcomp
  subst hτ
  refine wp_lolli unit' v _ _ ?_
  have hb : Expr.subst 0 v unit' = unit' := by simp [unit', Expr.subst]
  rw [hb]
  obtain ⟨α, -, ℓ, hs⟩ := hv
  obtain ⟨-, hmut⟩ := pure_sep_iff.mp hs
  exact wp_M_forget ℓ α _ _ _ _
    ⟨_, PMap.empty, ResU.comp_empty_right _, hmut, wp_val .unit _ _ ⟨rfl, rfl⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_171_2 := BoCa.Fig16.LogRel.forgetMut_compat
alias TR.«forget-compat₂» := BoCa.Fig16.LogRel.forgetMut_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- `[TR]` Lemma 6.171 (`forget-compat`, pp. 44–45) at `B = Unk`.  `𝒱⟦Unk⟧δ = emp`,
so there is no `wp-forget` step.  `[as printed]` -/
theorem forgetUnk_compat {Δ : LifeCtx} {Γ : Ctx Ty}
    (hΓ : Ctx.Dead Γ) : Sem Δ Γ forget axForgetUnkTy := by
  refine sem_iff.mpr fun δ γ ρ _ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  show wp forget _ _
  refine wp_val _ _ _ ?_
  intro v σ τ hv hcomp
  have hτ : τ = σ := eq_of_compS_empty_left hcomp
  subst hτ
  refine wp_lolli unit' v _ _ ?_
  have hb : Expr.subst 0 v unit' = unit' := by simp [unit', Expr.subst]
  rw [hb]
  obtain ⟨rfl, -⟩ := hv
  exact wp_val .unit _ _ ⟨rfl, rfl⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_171_3 := BoCa.Fig16.LogRel.forgetUnk_compat
alias TR.«forget-compat₃» := BoCa.Fig16.LogRel.forgetUnk_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
## Lemma 6.172 (withbor-compat1) · `[TR]` p. 45 · `variant`

> Δ ⊨ withbor : Ref T₁ ⊸ (∀'a ⊏ ⨅Δ. Imm 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂

**Printed proof, transcribed.** Let `T_f ≔ ∀'a ⊏ ⨅Δ. Imm 'a T₁ ⊸ ['a]T₂` and fix `δ ∈ ⟦Δ⟧`.  Apply `wp-val`, `wp⊸` and fix `v, v_f`: `𝒱⟦Ref T₁⟧δ(v) ⋆ 𝒱⟦T_f⟧δ(v_f) ⊨ wp(v, v_f () v){𝒱⟦Ref T₁ ⊗ T₂⟧δ}`.  Unfold and substitute `v = ℓ`: `ℓ ↦ v_ℓ ⋆ 𝒱⟦T₁⟧δ(v_ℓ) ⋆ 𝒱⟦T_f⟧δ(v_f) ⊨ wp(ℓ, v_f () ℓ){…}`.  Apply ImmFrame (6.64): `𝒱⟦T_f⟧(v_f) ⊨ Иα. ℓ ↦I_α 𝒱⟦T₁⟧δ(v_ℓ) –⋆ wp(ℓ, v_f () ℓ){[α](ℓ ↦ v_ℓ –⋆ 𝒱⟦T₁⟧δ(v_ℓ) –⋆ 𝒱⟦Ref T₁ ⊗ T₂⟧δ)}`.  Unfold `𝒱⟦Ref T₁ ⊗ T₂⟧δ` to `P̂`; apply `wp-bind`; choose `v₁ ≔ ℓ`, `v₂ ≔ v₂`; unfold `𝒱⟦Ref T₁⟧δ`; choose `v_ℓ ≔ v_ℓ` and cancel `ℓ ↦ v_ℓ`, `𝒱⟦T₁⟧δ(v_ℓ)`; apply `wp-val`: `𝒱⟦T_f⟧δ(v_f) ⊨ Иα. ℓ ↦I_α 𝒱⟦T₁⟧δ(v_ℓ) –⋆ wp(v_f () ℓ){v₂. [α]𝒱⟦T₂⟧δ(v₂)}`.  Unfold `T_f`.  Apply `ИR` on the left; fix `α ⊏ ⨅δ` by `И-mono`; apply `–⋆R`.  Fold and simplify, using that `'b` does not occur free in `T₁` or `T₂`: `𝒱⟦T_f⟧δ(v_f) ⋆ 𝒱⟦Imm 'a T₁⟧δ['a↦α](ℓ) ⊨ wp(v_f () ℓ){v₂. 𝒱⟦['a]T₂⟧δ['a↦α](v₂)}`.  Follows from `∀E-compat` and `⊸E-compat`.

**Lean.** `BoCa.Fig16.LogRel.withbor1_compat`, aliases `TR.lemma_6_172`, `TR.«withbor-compat1»`, tag `[variant: the printed statement is kept and two hypotheses are added, each the
content of one sentence of the printed proof — `hfree₁`/`hfree₂`, the binder
convention its last step folds by]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.withbor1_compatX`.

**Note.** `⊓Δ` is `Lifetime.LifeCtx.meetOfDom` (§12.15) and the schematic binder a parameter `x` (§12.44).  `hfree₁`/`hfree₂` are p. 46's *"Fold and simplify, using that `'b` does not occur free in `T₁` or `T₂`"*; `withbor1Side_unit` inhabits them.  The printed `Δ.find? x = none` is carried; the proof instantiates `𝒱⟦∀⟧` at `α` where `[TR]` cites `∀E-compat`, and does not use it (§12.32).
-/
/-- `[TR]` Lemma 6.172 (`withbor-compat1`, p. 45).
`[variant: the printed statement is kept and two hypotheses are added, each the
content of one sentence of the printed proof — `hfree₁`/`hfree₂`, the binder
convention its last step folds by]`

The bound handed to `ImmFrame` is `@ρ₂ ⊓ ⊓Δδ` (`⋔r` at `@ρ₂`, then `⋔-mono`);
`⊓Δδ` is defined at every `δ ⊨ Δ` (`Lifetime.meetOfDomL_wf`). -/
theorem withbor1_compat {Δ : LifeCtx} {Γ : Ctx Ty} {T₁ T₂ : Ty} (x : LifeVar)
    (hΓ : Ctx.Dead Γ) (_hx : Δ.find? x = none)
    /- p. 46: "Fold and simplify, using that 'b does not occur free in T₁ or T₂"
       — the bound variable of `∀'a ⊏ ⊓Δ. …`, which is `x` here. -/
    (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
    Sem Δ Γ withbor (axWithbor1Ty x Δ.meetOfDom T₁ T₂) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  show wp withbor _ _
  refine wp_val _ _ _ ?_
  -- unfold 𝒱⟦⊸⟧, let `v` be arbitrary, apply `wp-⊸`
  intro v₁ ρ₁ τ₀ hv₁ hcomp
  have hτ₀ : τ₀ = ρ₁ := eq_of_compS_empty_left hcomp
  subst hτ₀
  -- unfold 𝒱⟦Ref T₁⟧: `v = ℓ`, and the resource is `ℓ ↦ vℓ ⋆ 𝒱⟦T₁⟧δ(vℓ)`
  obtain ⟨ℓ, vℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, ρℓ, ρP, hcℓ, hown, hP⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.pair v1 (.app (.app v0 unit') v1))))
      = Expr.val (Val.lam (.pair (.val (.loc ℓ))
          (.app (.app v0 unit') (.val (.loc ℓ))))) := by
    simp [Expr.subst, Expr.shift, v0, v1, unit']
  refine wp_lolli _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  -- `wp-val`; unfold 𝒱⟦⊸⟧ again, let `vf` be arbitrary, apply `wp-⊸`
  refine wp_val _ _ _ ?_
  intro vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (.loc ℓ)) (.app (.app v0 unit') (.val (.loc ℓ))))
      = Expr.pair (.val (.loc ℓ))
          (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) := by
    simp [Expr.subst, v0, unit']
  refine wp_lolli _ vf _ _ ?_
  rw [hβ₂]
  -- `ImmFrame` at `ℓ ↦ vℓ ⋆ 𝒱⟦T₁⟧δ(vℓ)`, with the callback's resource `ρ₂` under
  -- the `⋔α`; the immutable borrow hands the same `vℓ` back, so no `∀v′`
  obtain ⟨σ, hcσ, hcτ⟩ := compS_reassoc hcℓ hc₂
  refine wp_I_frame ℓ (vDen T₁ δ) vℓ _ _ τ
    ⟨ρℓ, σ, hcτ, hown, ρP, ρ₂, hcσ, hP, ?_⟩
  -- `⋔r` at `@ρ₂` and `⋔-mono` down to `⊓Δδ`: the bound is `@ρ₂ ⊓ ⊓Δδ`
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  -- `─⋆R`: take the borrow `ℓ ↦ I α 𝒱⟦T₁⟧δ`
  intro ρm σ' hm' hcm
  -- `wp-bind` at `vf () ℓ` under `(ℓ, −)`
  refine wp_bind (.pairR (.loc ℓ) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) _ σ' ?_
  -- unfold 𝒱⟦∀⟧ at `α ⊏ ⊓Δδ`: the thunk runs at `δ['x↦α]`
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wp_bind_frame (.appL .hole (.loc ℓ)) (.app (.val vf) (.val .unit))
    (vDen (.lolli (.imm (.var x) T₁) (.box (.var x) T₂)) (δ.extend x α))
    (ptoImm ℓ α (vDen T₁ δ)) _ ?_ _ ⟨ρ₂, ρm, hcm, hwpf, hm'⟩
  rintro vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, himm⟩
  simp only [Kont.plug]
  -- fold: `'x` is not free in `T₁`, so `ℓ ↦ I α 𝒱⟦T₁⟧δ` is `𝒱⟦Imm 'x T₁⟧_{δ['x↦α]}(ℓ)`
  have hT₁ : vDen T₁ (δ.extend x α) = vDen T₁ δ := vDen_extend_of_not_free hfree₁ δ α
  have hT₂ : vDen T₂ (δ.extend x α) = vDen T₂ δ := vDen_extend_of_not_free hfree₂ δ α
  have himm' : vDen (.imm (.var x) T₁) (δ.extend x α) (.loc ℓ) σ₂ :=
    ⟨α, find?_extend_self δ x α, ℓ, pure_sep_mk rfl (by rw [hT₁]; exact himm)⟩
  -- the callback's own 𝒱⟦⊸⟧ at that borrow, then `wp-mono` at its result `v″`
  refine wp_mono (fun v'' ρ'' hb => ?_) _ σ'' (hvg (.loc ℓ) σ₂ σ'' himm' hcσ'')
  -- unfold 𝒱⟦['x] T₂⟧_{δ['x↦α]}, which is `[α] 𝒱⟦T₂⟧δ(v″)` since `'x` is not free in `T₂`
  obtain ⟨α', hα', hT₂δ', hout⟩ := hb
  rw [Lifetime.Life.interp_var, find?_extend_self] at hα'
  cases Option.some.inj hα'
  have hT₂' : vDen T₂ δ v'' ρ'' := by rw [← hT₂]; exact hT₂δ'
  -- `wp-ret`, and the cell ImmFrame gets back, at the same `vℓ`: `v₁ ≔ ℓ`, `v₂ ≔ v″`
  refine wp_pair (.loc ℓ) v'' _ _ (wp_val (.pair (.loc ℓ) v'') _ _ ?_)
  refine ⟨fun c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
  exact ⟨.loc ℓ, v'', pure_sep_mk rfl
    ⟨s, ρ'', ResU.CompS.comm hρs, ⟨ℓ, vℓ, pure_sep_mk rfl ⟨c₁, p₁, hs, hc₁, hp⟩⟩, hT₂'⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_172 := BoCa.Fig16.LogRel.withbor1_compat
alias TR.«withbor-compat1» := BoCa.Fig16.LogRel.withbor1_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- `Withbor1Side` at `T₁ = T₂ = 1`: `'x` is free in `1` on neither side.
`[about ours: an inhabitant of `Withbor1Side`]` -/
theorem withbor1Side_unit (x : LifeVar) : Withbor1Side x .unit .unit :=
  ⟨fun h => h, fun h => h⟩

/-!
## Lemma 6.173 (withbor-compat2) · `[TR]` p. 46 · `variant`

> If Δ ⊢ T₁ ⊐ @b then Δ ⊨ withbor : Ref T₁ ⊸ (∀'a ⊏ ⨅Δ. Mut 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂

**Printed proof, transcribed.** Let `T_f = ∀'a ⊏ ⨅Δ. Mut 'a T₁ ⊸ ['a]T₂`.  Follow the proof of Lemma 6.172 up to the point where ImmFrame is applied: `ℓ ↦ v_ℓ ⋆ 𝒱⟦T₁⟧δ(v_ℓ) ⋆ 𝒱⟦T_f⟧δ(v_f) ⊨ wp(ℓ, v_f () ℓ){𝒱⟦Ref T₁ ⊗ T₂⟧δ}`.  Since `Δ ⊢ T₁ ⊐ @b`, Lemma 6.60 gives `𝒱⟦T₁⟧δ ⊨ [@bδ]𝒱⟦T₁⟧δ`, so MutFrame (6.65) applies: `𝒱⟦T_f⟧δ(v_f) ⊨ Иα. ℓ ↦M_α 𝒱⟦T₁⟧δ –⋆ wp(ℓ, v_f () ℓ){[α] ∀v′. ℓ ↦ v′ –⋆ 𝒱⟦T₁⟧δ(v′) –⋆ 𝒱⟦Ref T₁ ⊗ T₂⟧δ}`.  Apply `wp-bind`, `wp-ret`; unfold `𝒱⟦Ref T₁ ⊗ T₂⟧δ` and simplify; choose `v₁ ≔ ℓ`, `v₂ ≔ v″`, `v_ℓ ≔ v′`; cancel `ℓ ↦ v′`, `𝒱⟦T₁⟧δ(v′)`: `𝒱⟦T_f⟧δ(v_f) ⊨ Иα. ℓ ↦M_α 𝒱⟦T₁⟧δ –⋆ wp(v_f () ℓ){v″. [α]𝒱⟦T₂⟧δ(v″)}`.  The remainder follows the proof of Lemma 6.172 from the step "Unfold `T_f`" onwards.

**Lean.** `BoCa.Fig16.LogRel.withbor2_compat`, aliases `TR.lemma_6_173`, `TR.«withbor-compat2»`, tag `[variant: the printed hypothesis is kept and two are added, `hfree₁`/`hfree₂`,
the binder convention its last step folds by]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.withbor2_compatX`.

**Note.** `hside` is the printed `Δ ⊢ T₁ ⊐ @b`, read existentially (§12.9, §C.25), and spent where p. 46 spends it: 6.60 at `@bδ` (`vDen_outlives`) is `MutFrame`'s premise.  `hfree₁`/`hfree₂` and `Δ.find? x = none` are as at 6.172; `withbor2Side_unit` inhabits the added hypotheses.
-/
/-- `[TR]` Lemma 6.173 (`withbor-compat2`, p. 46).
`[variant: the printed hypothesis is kept and two are added, `hfree₁`/`hfree₂`,
the binder convention its last step folds by]` -/
theorem withbor2_compat {Δ : LifeCtx} {Γ : Ctx Ty} {T₁ T₂ : Ty} (x : LifeVar)
    (hΓ : Ctx.Dead Γ) (_hx : Δ.find? x = none)
    (hside : ∃ b, Δ.Defines b ∧ BoCa.Outlives Δ T₁ b)
    /- p. 46: "Fold and simplify, using that 'b does not occur free in T₁ or T₂"
       — the bound variable of `∀'a ⊏ ⊓Δ. …`, which is `x` here. -/
    (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
    Sem Δ Γ withbor (axWithbor2Ty x Δ.meetOfDom T₁ T₂) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  show wp withbor _ _
  refine wp_val _ _ _ ?_
  -- unfold 𝒱⟦⊸⟧, let `v` be arbitrary, apply `wp-⊸`
  intro v₁ ρ₁ τ₀ hv₁ hcomp
  have hτ₀ : τ₀ = ρ₁ := eq_of_compS_empty_left hcomp
  subst hτ₀
  -- unfold 𝒱⟦Ref T₁⟧: `v = ℓ`, and the resource is `ℓ ↦ vℓ ⋆ 𝒱⟦T₁⟧δ(vℓ)`
  obtain ⟨ℓ, vℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, ρℓ, ρP, hcℓ, hown, hP⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.pair v1 (.app (.app v0 unit') v1))))
      = Expr.val (Val.lam (.pair (.val (.loc ℓ))
          (.app (.app v0 unit') (.val (.loc ℓ))))) := by
    simp [Expr.subst, Expr.shift, v0, v1, unit']
  refine wp_lolli _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  -- `wp-val`; unfold 𝒱⟦⊸⟧ again, let `vf` be arbitrary, apply `wp-⊸`
  refine wp_val _ _ _ ?_
  intro vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (.loc ℓ)) (.app (.app v0 unit') (.val (.loc ℓ))))
      = Expr.pair (.val (.loc ℓ))
          (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) := by
    simp [Expr.subst, v0, unit']
  refine wp_lolli _ vf _ _ ?_
  rw [hβ₂]
  -- "Since `Δ ⊢ T₁ ⊐ @b`, theorem 6.60 gives `𝒱⟦T₁⟧δ ⊧ [@bδ] 𝒱⟦T₁⟧δ`, so
  -- MutFrame applies" — at `ℓ ↦ vℓ ⋆ 𝒱⟦T₁⟧δ(vℓ)`, with the callback's resource
  -- `ρ₂` under the `⋔α`
  obtain ⟨b, hdef, hO⟩ := hside
  obtain ⟨β, hb⟩ := hdef δ hδ
  have hβ := vDen_outlives hδ hb hO
  obtain ⟨σ, hcσ, hcτ⟩ := compS_reassoc hcℓ hc₂
  refine wp_M_frame ℓ β (vDen T₁ δ) (fun v ρ' h => ⟨h, hβ v ρ' h⟩) vℓ _ _ τ
    ⟨ρℓ, σ, hcτ, hown, ρP, ρ₂, hcσ, hP, ?_⟩
  -- `⋔r` at `@ρ₂` and `⋔-mono` down to `⊓Δδ`: the bound is `@ρ₂ ⊓ ⊓Δδ`
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  -- `─⋆R`: take the borrow `ℓ ↦ M α 𝒱⟦T₁⟧δ`
  intro ρm σ' hm' hcm
  -- `wp-bind` at `vf () ℓ` under `(ℓ, −)`
  refine wp_bind (.pairR (.loc ℓ) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) _ σ' ?_
  -- unfold 𝒱⟦∀⟧ at `α ⊏ ⊓Δδ`: the thunk runs at `δ['x↦α]`
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wp_bind_frame (.appL .hole (.loc ℓ)) (.app (.val vf) (.val .unit))
    (vDen (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)) (δ.extend x α))
    (ptoMut ℓ α (vDen T₁ δ)) _ ?_ _ ⟨ρ₂, ρm, hcm, hwpf, hm'⟩
  rintro vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, hmut⟩
  simp only [Kont.plug]
  -- fold: `'x` is not free in `T₁`, so `ℓ ↦ M α 𝒱⟦T₁⟧δ` is `𝒱⟦Mut 'x T₁⟧_{δ['x↦α]}(ℓ)`
  have hT₁ : vDen T₁ (δ.extend x α) = vDen T₁ δ := vDen_extend_of_not_free hfree₁ δ α
  have hT₂ : vDen T₂ (δ.extend x α) = vDen T₂ δ := vDen_extend_of_not_free hfree₂ δ α
  have hmut' : vDen (.mut (.var x) T₁) (δ.extend x α) (.loc ℓ) σ₂ :=
    ⟨α, find?_extend_self δ x α, ℓ, pure_sep_mk rfl (by rw [hT₁]; exact hmut)⟩
  -- the callback's own 𝒱⟦⊸⟧ at that borrow, then `wp-mono` at its result `v″`
  refine wp_mono (fun v'' ρ'' hb => ?_) _ σ'' (hvg (.loc ℓ) σ₂ σ'' hmut' hcσ'')
  -- unfold 𝒱⟦['x] T₂⟧_{δ['x↦α]}, which is `[α] 𝒱⟦T₂⟧δ(v″)` since `'x` is not free in `T₂`
  obtain ⟨α', hα', hT₂δ', hout⟩ := hb
  rw [Lifetime.Life.interp_var, find?_extend_self] at hα'
  cases Option.some.inj hα'
  have hT₂' : vDen T₂ δ v'' ρ'' := by rw [← hT₂]; exact hT₂δ'
  -- `wp-ret`, and the `∀v′` that pays `MutFrame` back: `v₁ ≔ ℓ`, `v₂ ≔ v″`, `vℓ ≔ v′`
  refine wp_pair (.loc ℓ) v'' _ _ (wp_val (.pair (.loc ℓ) v'') _ _ ?_)
  refine ⟨fun w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
  exact ⟨.loc ℓ, v'', pure_sep_mk rfl
    ⟨s, ρ'', ResU.CompS.comm hρs, ⟨ℓ, w, pure_sep_mk rfl ⟨c₁, p₁, hs, hc₁, hp⟩⟩, hT₂'⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_173 := BoCa.Fig16.LogRel.withbor2_compat
alias TR.«withbor-compat2» := BoCa.Fig16.LogRel.withbor2_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- `Withbor2Side` at `T₁ = T₂ = 1`: `'x` is free in `1` on neither side.
`[about ours: an inhabitant of `Withbor2Side`]` -/
theorem withbor2Side_unit (x : LifeVar) : Withbor2Side x .unit .unit :=
  ⟨fun h => h, fun h => h⟩

/-!
## Lemma 6.174 (withbor-compat3) · `[TR]` p. 47 · `variant`

> Δ ⊨ withbor : Mut @a T₁ ⊸ (∀'b ⊏ ⨅Δ. Mut 'b T₁ ⊸ ['b]T₂) ⊸ Mut @a T₁ ⊗ T₂

**Printed proof, transcribed.** Let `T_f = ∀'b ⊏ ⨅Δ. Mut 'b T₁ ⊸ ['b]T₂` and fix `δ ∈ ⟦Δ⟧`.  Apply `wp-val`, `wp⊸` and fix `v, v_f`.  Unfold, let `α ≔ @aδ` and substitute `v = ℓ`: `ℓ ↦M_α 𝒱⟦T₁⟧δ ⋆ 𝒱⟦T_f⟧(v_f) ⊨ wp(ℓ, v_f () ℓ){𝒱⟦Mut @a T₁ ⊗ T₂⟧δ}`.  Apply AntiFrame (6.66); apply `∀R`, `–⋆R`: `𝒱⟦T_f⟧(v_f) ⋆ ℓ ↦ v ⋆ 𝒱⟦T₁⟧δ(v) ⊨ wp(ℓ, v_f () ℓ){v′. ∃v. ℓ ↦ v ⋆ 𝒱⟦T₁⟧δ(v) ⋆ (ℓ ↦M_α 𝒱⟦T₁⟧δ(v) –⋆ 𝒱⟦Mut @a T₁ ⊗ T₂⟧δ(v′))}`.  Apply `wp-bind`, `wp-val`; simplify `𝒱⟦Mut @a T₁ ⊗ T₂⟧δ(ℓ, v″)`; cancel `ℓ ↦M_α 𝒱⟦T₁⟧δ(v)`: `… ⊨ wp(v_f () ℓ){v″. ∃v. ℓ ↦ v ⋆ 𝒱⟦T₁⟧δ(v) ⋆ 𝒱⟦T₂⟧δ(v″)}`.  *"Have `Δ ⊢ T₁ ⊐ @a` by well-formedness of the type `Mut @a T₁`, hence `𝒱⟦T₁⟧δ ⊨ [α]𝒱⟦T₁⟧δ` by theorem 6.60, so MutFrame applies"*: `𝒱⟦T_f⟧(v_f) ⊨ Иα. ℓ ↦M_α 𝒱⟦T₁⟧δ –⋆ wp(v_f () ℓ){v″. [α] ∀v′. ℓ ↦ v′ –⋆ 𝒱⟦T₁⟧δ(v′) –⋆ ∃v. ℓ ↦ v ⋆ 𝒱⟦T₁⟧δ(v) ⋆ 𝒱⟦T₂⟧δ(v″)}`.  In the postcondition choose `v ≔ v′` and cancel.  The remainder follows the proof of Lemma 6.172 from the step "Unfold `T_f`" onwards.

**Lean.** `BoCa.Fig16.LogRel.withbor3_compat`, aliases `TR.lemma_6_174`, `TR.«withbor-compat3»`, tag `[variant: the printed statement carries no side condition; two hypotheses are
added, `hfree₁`/`hfree₂`, 6.172's binder convention, which 6.174 inherits]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.withbor3_compatX`.

**Note.** `MutFrame`'s premise `𝒱⟦T₁⟧δ ⊨ [β]𝒱⟦T₁⟧δ` is read off the borrow in hand, `ℓ ↦ mut(β, v, ρ′, P̂)` with `P̂ : Val → SProp_β` (`vDen_mut_supported`), where p. 47 cites `Δ ⊢ T₁ ⊐ @a` *"by well-formedness of the type `Mut @a T₁`"* (definition row 2.28, §12.32).  `hfree₁`/`hfree₂` and `Δ.find? x = none` are as at 6.172; `withbor3Side_unit` inhabits the added hypotheses.
-/
/-- `[TR]` Lemma 6.174 (`withbor-compat3`, p. 47).
`[variant: the printed statement carries no side condition; two hypotheses are
added, `hfree₁`/`hfree₂`, 6.172's binder convention, which 6.174 inherits]` -/
theorem withbor3_compat {Δ : LifeCtx} {Γ : Ctx Ty} {a : Lifetime.Life}
    {T₁ T₂ : Ty} (x : LifeVar) (hΓ : Ctx.Dead Γ) (_hx : Δ.find? x = none)
    /- 6.174 inherits 6.172's "'b not free in T₁ or T₂" — the bound variable of
       `∀'b ⊏ ⊓Δ. …`, which is `x` here; the folding step reads
       `ℓ ↦ M α 𝒱⟦T₁⟧δ` as `𝒱⟦Mut 'x T₁⟧_{δ['x↦α]}(ℓ)` and `[α] 𝒱⟦T₂⟧_{δ['x↦α]}`
       as `[α] 𝒱⟦T₂⟧δ` by it. -/
    (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
    Sem Δ Γ withbor (axWithbor3Ty a x Δ.meetOfDom T₁ T₂) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  show wp withbor _ _
  refine wp_val _ _ _ ?_
  -- unfold 𝒱⟦⊸⟧, let `v₁` be arbitrary, apply `wp-⊸`
  intro v₁ ρ₁ τ₀ hv₁ hcomp
  have hτ₀ : τ₀ = ρ₁ := eq_of_compS_empty_left hcomp
  subst hτ₀
  -- unfold 𝒱⟦Mut @a T₁⟧: `v₁ = ℓ`, `α₀ = @aδ`, resource is `ℓ ↦ M α₀ 𝒱⟦T₁⟧δ`
  obtain ⟨α₀, ha, ℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, hmut⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.pair v1 (.app (.app v0 unit') v1))))
      = Expr.val (Val.lam (.pair (.val (.loc ℓ))
          (.app (.app v0 unit') (.val (.loc ℓ))))) := by
    simp [Expr.subst, Expr.shift, v0, v1, unit']
  refine wp_lolli _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  -- `wp-val`; unfold 𝒱⟦⊸⟧ again, let `vf` be arbitrary, apply `wp-⊸`
  refine wp_val _ _ _ ?_
  intro vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (.loc ℓ)) (.app (.app v0 unit') (.val (.loc ℓ))))
      = Expr.pair (.val (.loc ℓ))
          (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) := by
    simp [Expr.subst, v0, unit']
  refine wp_lolli _ vf _ _ ?_
  rw [hβ₂]
  -- `AntiFrame` at `ℓ ↦ M α₀ 𝒱⟦T₁⟧δ`, with the callback's resource `ρ₂` as the
  -- second conjunct; `v₂` is the payload it hands over, `c₁`/`p₁` the owned cell
  -- and payload it lends back for the length of the run
  refine wp_M_antiFrame ℓ α₀ (vDen T₁ δ) _ _ τ ⟨τ₀, ρ₂, hc₂, hmut, ?_⟩
  intro v₂ c₁ c₂ hc hcc p₁ p₂ hp hcp
  -- from here the resources are 6.173's after its `𝒱⟦Ref T₁⟧` unfold: `MutFrame`
  -- at the recovered `ℓ ↦ v₂ ⋆ 𝒱⟦T₁⟧δ(v₂)`, its premise `𝒱⟦T₁⟧δ ⊨ [β]𝒱⟦T₁⟧δ`
  -- read off the borrow in hand — the `mut` cell's own invariant is a
  -- `Val → SProp_β` — and the callback's resource `ρ₂` under the `⋔α`
  obtain ⟨β, hβ⟩ : ∃ β, ∀ v ρ, vDen T₁ δ v ρ → Fig16.BoLo.Outlives ρ β := by
    obtain ⟨b, w, σ, hσ, Q, hw, -, -, hofS⟩ := hmut
    exact ⟨b, fun u τ hu => by rw [← hofS] at hu; exact hu.1⟩
  -- `(ρ₂ ● ℓ↦v₂) ● ρ_{𝒱⟦T₁⟧δ(v₂)}` regrouped as `ℓ↦v₂ ● (ρ_{𝒱⟦T₁⟧δ(v₂)} ● ρ₂)`
  obtain ⟨σ, hcσ, hmid⟩ := compS_reassoc' hcc (ResU.CompS.comm hcp)
  refine wp_M_frame ℓ β (vDen T₁ δ) (fun v ρ' h => ⟨h, hβ v ρ' h⟩) v₂ _ _ p₂
    ⟨c₁, σ, ResU.CompS.comm hmid, hc, p₁, ρ₂, hcσ, hp, ?_⟩
  -- `⋔r` at `@ρ₂` and `⋔-mono` down to `⊓Δδ`: the bound is `@ρ₂ ⊓ ⊓Δδ`
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  -- `─⋆R`: take the borrow `ℓ ↦ M α 𝒱⟦T₁⟧δ`
  intro ρm σ' hm' hcm
  -- `wp-bind` at `vf () ℓ` under `(ℓ, −)`
  refine wp_bind (.pairR (.loc ℓ) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) _ σ' ?_
  -- unfold 𝒱⟦∀⟧ at `α ⊏ ⊓Δδ`: the thunk runs at `δ['x↦α]`
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wp_bind_frame (.appL .hole (.loc ℓ)) (.app (.val vf) (.val .unit))
    (vDen (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)) (δ.extend x α))
    (ptoMut ℓ α (vDen T₁ δ)) _ ?_ _ ⟨ρ₂, ρm, hcm, hwpf, hm'⟩
  rintro vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, hmut⟩
  simp only [Kont.plug]
  -- fold: `'x` is not free in `T₁`, so `ℓ ↦ M α 𝒱⟦T₁⟧δ` is `𝒱⟦Mut 'x T₁⟧_{δ['x↦α]}(ℓ)`
  have hT₁ : vDen T₁ (δ.extend x α) = vDen T₁ δ := vDen_extend_of_not_free hfree₁ δ α
  have hT₂ : vDen T₂ (δ.extend x α) = vDen T₂ δ := vDen_extend_of_not_free hfree₂ δ α
  have hmut' : vDen (.mut (.var x) T₁) (δ.extend x α) (.loc ℓ) σ₂ :=
    ⟨α, find?_extend_self δ x α, ℓ, pure_sep_mk rfl (by rw [hT₁]; exact hmut)⟩
  -- the callback's own 𝒱⟦⊸⟧ at that borrow, then `wp-mono` at its result `v″`
  refine wp_mono (fun v'' ρ'' hb => ?_) _ σ'' (hvg (.loc ℓ) σ₂ σ'' hmut' hcσ'')
  -- unfold 𝒱⟦['x] T₂⟧_{δ['x↦α]}, which is `[α] 𝒱⟦T₂⟧δ(v″)` since `'x` not free in `T₂`
  obtain ⟨α', hα', hT₂δ', hout⟩ := hb
  rw [Lifetime.Life.interp_var, find?_extend_self] at hα'
  cases Option.some.inj hα'
  have hT₂' : vDen T₂ δ v'' ρ'' := by rw [← hT₂]; exact hT₂δ'
  -- `wp-ret`; the `∀v′` that pays `MutFrame` back, `v ≔ v′`, and the borrow
  -- `AntiFrame` handed back, together folding `𝒱⟦Mut @a T₁ ⊗ T₂⟧δ((ℓ, v″))`
  refine wp_pair (.loc ℓ) v'' _ _ (wp_val (.pair (.loc ℓ) v'') _ _ ?_)
  refine ⟨fun w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
  obtain ⟨W, hcWi, hcW⟩ := compS_reassoc hs (ResU.CompS.comm hρs)
  -- give the borrow back: `ℓ ↦ M α₀ 𝒱⟦T₁⟧δ ⋆ 𝒱⟦T₂⟧δ(v″)` folds to
  -- 𝒱⟦Mut @a T₁ ⊗ T₂⟧δ((ℓ, v″)), as at `withswap_compat`
  exact ⟨w, c₁, W, hcW, hc₁, p₁, ρ'', hcWi, hp,
    fun m₁ m₂ hm hcm => ⟨.loc ℓ, v'', pure_sep_mk rfl
      ⟨m₁, ρ'', ResU.CompS.comm hcm, ⟨α₀, ha, ℓ, pure_sep_mk rfl hm⟩, hT₂'⟩⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_174 := BoCa.Fig16.LogRel.withbor3_compat
alias TR.«withbor-compat3» := BoCa.Fig16.LogRel.withbor3_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- `Withbor3Side` at `T₁ = T₂ = 1`, the same instance as `withbor2Side_unit`.
`[about ours: an inhabitant of `Withbor3Side`]` -/
theorem withbor3Side_unit (x : LifeVar) : Withbor3Side x .unit .unit :=
  ⟨fun h => h, fun h => h⟩

/-!
## Lemma 6.175 (withload-compat) · `[TR]` p. 47 · `proved*`

> Δ ⊨ withload : Imm @a T₁ ⊸ (∀'b ⊏ ⨅Δ. Imm̲ 'b T₁ ⊸ ['b]T₂) ⊸ T₂

**Printed proof, transcribed.** Let `δ ∈ ⟦Δ⟧`.  Unfold `𝒱⟦⊸⟧` at `v`; apply `wp⊸` and `wp-val`; unfold `𝒱⟦⊸⟧` at `v_f`; apply `wp⊸`.  Unfold `𝒱⟦Imm⟧`, `v = ℓ`: `ℓ ↦I_{@aδ} 𝒱⟦T₁⟧δ ⋆ 𝒱⟦∀'b ⊏ ⨅Δ. …⟧δ(v_f) ⊨ wp(v_f () (load ℓ)){𝒱⟦T₂⟧δ}`.  Apply `wp-bind`; apply `wp-load-I` and let `v_ℓ` be arbitrary: `ℓ ↦I_{@aδ} (v′. (v′ = v_ℓ) ⋆ 𝒱⟦T₁⟧δ(v′)) ⋆ … ⊨ wp(v_f () v_ℓ){𝒱⟦T₂⟧δ}`.  Apply `↺V₂`: the payload becomes `(v′ = v_ℓ) ⋆ Иβ. ↺_β 𝒱⟦Imm̲ 'b T₁⟧δ['b↦β](v′)`.  Apply Lemma 6.134: `Иβ. ↺_β((v′ = v_ℓ) ⋆ 𝒱⟦Imm̲ 'b T₁⟧δ['b↦β](v′))`.  Apply Theorem 6.150: `𝒱⟦∀'b ⊏ ⨅Δ. …⟧δ(v_f) ⊨ Иβ. ∀v′. v′ = v_ℓ ⋆ 𝒱⟦Imm̲ 'b T₁⟧δ['b↦β](v′) –⋆ wp(v_f () v′){[β]𝒱⟦T₂⟧δ}`.  Substitute `v_ℓ` for `v′`.  Apply `ИR` on the left; by `И-mono` let `β ⊏ ⨅δ` be arbitrary; apply `–⋆R`.  Have `𝒱⟦T₂⟧δ = 𝒱⟦T₂⟧δ['b↦β]` because `'b` does not occur free in `T₂`.  Fold `ℰ⟦−⟧`: `… ⊨ ℰ⟦['b]T₂⟧δ['b↦β](v_f () v_ℓ)`.  Follows from `∀E-compat` and `⊸E-compat`.

**Lean.** `BoCa.Fig16.LogRel.withload_compat`, aliases `TR.lemma_6_175`, `TR.«withload-compat»`, tag `[restricted: to `hfree₁` (6.132's), `hesc` (6.150's) and `hfree₂`]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.withload_compatX`.

**Note.** `hfree₁` is 6.132's *"if `'a` not free in `T`"*; `hesc` is `RebEscrow`, 6.150's inheritance from 6.55, at this proof's `P̂`; `hfree₂` is p. 48's *"because `'b` does not occur free in `T₂`"*.  `withload_hesc_unit` and `withloadSide_unit` inhabit them, and `withloadSide_of_wfB` derives the two freshnesses from p. 2's `Δ ⊢ T`.  6.150's `P̂` is `Life → Val → SProp`, its `β` bound by the `Иβ` (§12.61).  `Δ.find? x = none` is as at 6.172 (§12.32).

**At the repaired judgment.**  `Typed.withload_compatX` has no `hesc`: its 6.150 step `Typed.wpTS_reborrow` reads the reborrow off the `CohE` the argument's `𝒱X⟦Imm @a T₁⟧` carries at the loaded cell (§12.71).  `[restricted: to `hfree₁` and `hfree₂`]`, which `Typed.fundamental` derives from p. 2's `Δ ⊢ T` (`BoCa.scopedB_axWithloadTy`).
-/
/-- `[TR]` Lemma 6.175 (`withload-compat`, pp. 47–48).
`[restricted: the conclusion is the printed entailment and three hypotheses are
added — `hfree₁`, which is `↺V₂`'s (6.132); `hesc`, which is the `↺` rule's
(6.150); and `hfree₂`, the sentence the last fold is.  No printed statement is
touched]`

`Imm̲ 'b T₁` is `Ty.immReborrow (.var 'b) T₁` (§12.11).  `wp-load-I` (6.144) leaves
`(v′. ⌜v_ℓ = v′⌝ ⋆ 𝒱⟦T₁⟧δ(v_ℓ))`, where p. 48's display writes the second factor at
`v′`; the pin makes the two one proposition. -/
theorem withload_compat {Δ : LifeCtx} {Γ : Ctx Ty} {a : Lifetime.Life}
    {T₁ T₂ : Ty} (x : LifeVar) (hΓ : Ctx.Dead Γ) (_hx : Δ.find? x = none)
    /- `[TR]` 6.150's inherited pair, at the reborrows this proof's own `↺_β P̂`
       names. -/
    (hesc : ∀ (δ : LSub) (vℓ : Val), RebEscrow
      (fun β v' => ⌜vℓ = v'⌝ ⋆ vDen (T₁.immReborrow (.var x)) (δ.extend x β) vℓ))
    /- p. 35: `↺V₂`'s *"if `'a` not free in `T`"*; p. 48: *"because `'b` does
       not occur free in `T₂`"*. -/
    (hfree₁ : ¬ LFree x T₁) (hfree₂ : ¬ LFree x T₂) :
    Sem Δ Γ withload (axWithloadTy a x Δ.meetOfDom T₁ T₂) := by
  refine sem_iff.mpr fun δ γ ρ hδ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  show wp withload _ _
  refine wp_val _ _ _ ?_
  -- "Unfold 𝒱⟦⊸⟧.  Let `v` be arbitrary.  Apply `wp⊸` and `wp-val`."
  intro v₁ ρ₁ τ₀ hv₁ hcomp
  have hτ₀ : τ₀ = ρ₁ := eq_of_compS_empty_left hcomp
  subst hτ₀
  -- "Unfold 𝒱⟦Imm⟧.  There exists some `ℓ` such that `v = ℓ`."
  obtain ⟨α₀, ha, ℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, himm⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.app (.app v0 unit') (.app load' v1))))
      = Expr.val (Val.lam (.app (.app v0 unit') (eLoad ℓ))) := by
    simp [eLoad, Expr.subst, Expr.shift, v0, v1, unit', load']
  refine wp_lolli _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  -- "Unfold 𝒱⟦⊸⟧.  Let `v_f` be arbitrary.  Apply `wp⊸`."
  refine wp_val _ _ _ ?_
  intro vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf (Expr.app (.app v0 unit') (eLoad ℓ))
      = Expr.app (.app (.val vf) (.val .unit)) (eLoad ℓ) := by
    simp [eLoad, Expr.subst, v0, unit']
  refine wp_lolli _ vf _ _ ?_
  rw [hβ₂]
  -- "Apply `wp-bind`", with continuation `v_ℓ. v_f () v_ℓ`
  refine wp_bind (.appR (.app (.val vf) (.val .unit)) .hole) (eLoad ℓ) _ _ ?_
  -- "Apply `wp-load-I`.  Let `v_ℓ` be arbitrary."
  refine wp_load_I ℓ α₀ (vDen T₁ δ) _ τ ⟨_, ρ₂, hc₂, himm, ?_⟩
  intro vℓ ρc ρcomp hcell hccomp
  simp only [Kont.plug]
  -- "Apply `↺V₂`" — under `I-mono` (6.113) at the cell and `⋆mono` (6.92) at
  -- the pin, on the payload `𝒱⟦T₁⟧δ(v_ℓ)` the pin leaves
  have hcell₂ := ptoImm_mono
    (P := fun v' => ⌜vℓ = v'⌝ ⋆ vDen T₁ δ vℓ)
    (Q := fun v' => ⌜vℓ = v'⌝ ⋆
      fresh fun β => reborrow β (vDen (T₁.immReborrow (.var x)) (δ.extend x β) vℓ))
    (fun _ => sep_mono (fun _ h => h) (reborrow_vDen_fresh T₁ hfree₁ vℓ))
    ρc hcell
  -- "Apply theorem 6.134."
  have hcell₃ := ptoImm_mono
    (Q := fun v' => fresh fun β => reborrow β
      (⌜vℓ = v'⌝ ⋆ vDen (T₁.immReborrow (.var x)) (δ.extend x β) vℓ))
    (fun _ => pure_sep_reborrow_vDen_fresh T₁ vℓ) ρc hcell₂
  -- "Apply theorem 6.150": lend the reborrow to `v_f () v_ℓ` at a fresh `β`
  refine wp_reborrow ℓ α₀
    (fun β v' => ⌜vℓ = v'⌝ ⋆ vDen (T₁.immReborrow (.var x)) (δ.extend x β) vℓ)
    _ (vDen T₂ δ) (hesc δ vℓ) ρcomp
    ⟨ρc, ρ₂, ResU.CompS.comm hccomp, hcell₃, ?_⟩
  -- "Apply `ИR` on the left-hand side.  By `И-mono`, let `β ⊏ ⨅δ` be arbitrary."
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine fresh_mono (β' := m) ?_ ρ₂ (fresh_R _ ρ₂ hvf)
  rintro β hβ σ₀ ⟨hvfσ, houtσ⟩
  -- "Apply `─⋆R`" (6.93), at the `⋆` the print's next display writes
  refine ⟨fun v => wand_R ?_ σ₀ hvfσ, houtσ⟩
  -- "Substitute `v_ℓ` for `v′`", which the pin does
  rintro ρpc ⟨σ, ρp, hpc, hvfσ', hP⟩
  obtain ⟨hvv, hreb⟩ := pure_sep_iff.mp hP
  subst hvv
  -- the callback's `𝒱⟦∀⟧` at `β ⊏ ⊓Δδ`: the thunk `v_f ()` runs at `δ['x↦β]`
  have hlt : LtLife δ Δ.meetOfDom β := ⟨m, hm, hβ⟩
  have hwpf := hvfσ' β PMap.empty σ ⟨rfl, hlt⟩ (ResU.comp_empty_right σ)
  -- "Fold ℰ⟦−⟧": `wp-bind` on the thunk, framing the reborrow through
  refine wp_bind_frame (.appL .hole vℓ) (.app (.val vf) (.val .unit))
    (vDen (.lolli (Ty.immReborrow (.var x) T₁) (.box (.var x) T₂)) (δ.extend x β))
    (vDen (Ty.immReborrow (.var x) T₁) (δ.extend x β) vℓ) _ ?_ ρpc
    ⟨σ, ρp, hpc, hwpf, hreb⟩
  rintro vg σ ⟨σ₁, σ₂, hcσ, hvg, hR⟩
  simp only [Kont.plug]
  -- "Follows from `∀E-compat` and `⊸E-compat`": the callback's `⊸` at the
  -- reborrow, then `wp-mono` on its postcondition
  refine wp_mono (fun v' ρ' hb => ?_) _ σ (hvg vℓ σ₂ σ hR hcσ)
  obtain ⟨α', hα', hbox⟩ := hb
  rw [Lifetime.Life.interp_var, find?_extend_self] at hα'
  cases Option.some.inj hα'
  -- "Have `𝒱⟦T₂⟧δ = 𝒱⟦T₂⟧δ['b↦β]` because `'b` does not occur free in `T₂`."
  rw [vDen_extend_of_not_free hfree₂ δ β] at hbox
  exact hbox

end BoCa.Fig16.LogRel

alias TR.lemma_6_175 := BoCa.Fig16.LogRel.withload_compat
alias TR.«withload-compat» := BoCa.Fig16.LogRel.withload_compat

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- `withload_compat`'s `hesc` at `T₁ = 1`: `Imm̲ 'x 1 = 1` (§12.11), so every
reborrow the `P̂` names has image `∅` (`Fig16.BoLo.rebEscrow_emp`).
`[about ours: an inhabitant of the hypothesis `withload_compat` inherits from
`[TR]` 6.150]` -/
theorem withload_hesc_unit (x : LifeVar) (δ : LSub) (vℓ : Val) :
    RebEscrow (fun β v' => ⌜vℓ = v'⌝ ⋆
      vDen (Ty.immReborrow (.var x) .unit) (δ.extend x β) vℓ) := by
  intro b w σ χ hreb hP
  exact rebEscrow_emp b w σ χ hreb (pure_sep_iff.mp hP).2.1

/-- `WithloadSide` at `T₁ = T₂ = 1`: `withload_hesc_unit` is the escrow half,
and `'x` is free in `1` on neither side.
`[about ours: an inhabitant of `WithloadSide`]` -/
theorem withloadSide_unit (x : LifeVar) : WithloadSide x .unit .unit :=
  ⟨withload_hesc_unit x, fun h => h, fun h => h⟩

@[inherit_doc withloadSide_of_scopedB]
theorem withloadSide_of_wfB {Δ : LifeCtx} {x : LifeVar} {T₁ T₂ : Ty}
    (hesc : ∀ (δ : LSub) (vℓ : Val), RebEscrow
      (fun β v' => ⌜vℓ = v'⌝ ⋆ vDen (T₁.immReborrow (.var x)) (δ.extend x β) vℓ))
    (hx : Δ.find? x = none) (h₁ : T₁.wfB Δ = true) (h₂ : T₂.wfB Δ = true) :
    WithloadSide x T₁ T₂ :=
  withloadSide_of_scopedB hesc hx (Ty.scopedB_of_wfB h₁) (Ty.scopedB_of_wfB h₂)

/-!
## Lemma 6.176 (withswap-compat) · `[TR]` p. 48 · `proved`

> ─────────────────────────────────────────────────────────── withswap
> Δ; ∅ ⊨ withswap : Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ Mut @a T₁ ⊗ T₂

**Printed proof, transcribed.** Let `δ ∈ ⟦Δ⟧`.  Unfold `𝒱⟦⊸⟧` at `v₁`; apply `wp-⊸` and `wp-val`; unfold `𝒱⟦⊸⟧` at `v_f`; apply `wp-⊸`: `𝒱⟦Mut @a T₁⟧δ(v₁) ⋆ 𝒱⟦T₁ ⊸ T₁ ⊗ T₂⟧δ(v_f) ⊨ wp(let (y, z) = v_f (load v₁); store v₁ y; (v₁, z)){𝒱⟦Mut @a T₁ ⊗ T₂⟧δ}`.  Unfold `𝒱⟦Mut⟧`, `v₁ = ℓ`.  Apply `wp-m-anti-frame` (6.66) at an arbitrary `v₂`: the antecedent becomes `ℓ ↦ v₂ ⋆ 𝒱⟦T₁⟧δ(v₂) ⋆ 𝒱⟦T₁ ⊸ T₁ ⊗ T₂⟧δ(v_f)` and the postcondition `∃v. ℓ ↦ v ⋆ 𝒱⟦T₁⟧δ(v) ⋆ (ℓ ↦M_{@aδ} 𝒱⟦T₁⟧δ –⋆ 𝒱⟦Mut @a T₁ ⊗ T₂⟧δ)`.  Apply `wp-bind` at `load ℓ` and `wp-load`; instantiate `𝒱⟦T₁ ⊸ T₁ ⊗ T₂⟧δ(v_f)` with `𝒱⟦T₁⟧δ(v₂)`; apply `wp-bind` at `f v₂` and `wp-mono`; unfold `𝒱⟦⊗⟧` at `v₃, v₄`; apply `wp-⊗`; apply `wp-bind` at `store ℓ v₃`, `wp-store`, `wp-1` and `wp-val`: `ℓ ↦ v₃ ⋆ 𝒱⟦T₁⟧δ(v₃) ⋆ 𝒱⟦T₂⟧δ(v₄) ⊨ ∃v. …`.  Choose `v ≔ v₃`: `𝒱⟦T₂⟧δ(v₄) ⋆ ℓ ↦M_{@aδ} 𝒱⟦T₁⟧δ ⊨ 𝒱⟦Mut @a T₁ ⊗ T₂⟧δ((ℓ, v₄))`, which follows from the `𝒱` definitions.

**Lean.** `BoCa.Fig16.LogRel.withswap_compat`, aliases `TR.lemma_6_176`, `TR.«withswap-compat»`, tag `[as printed]`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.withswap_compatX`.
-/
/-- `[TR]` Lemma 6.176 (`withswap-compat`, pp. 48–49).  `[as printed]` -/
theorem withswap_compat {Δ : LifeCtx} {Γ : Ctx Ty} {a : Lifetime.Life}
    {T₁ T₂ : Ty} (hΓ : Ctx.Dead Γ) :
    Sem Δ Γ withswap (axWithswapTy a T₁ T₂) := by
  refine sem_iff.mpr fun δ γ ρ _ hg => ?_
  have hρ : ρ = PMap.empty := gSep_dead hΓ (gDen_iff.mp hg).2
  subst hρ
  show wp withswap _ _
  refine wp_val _ _ _ ?_
  -- unfold 𝒱⟦⊸⟧, let `v₁` be arbitrary, apply `wp-⊸`
  intro v₁ ρ₁ τ₀ hv₁ hcomp
  have hτ₀ : τ₀ = ρ₁ := eq_of_compS_empty_left hcomp
  subst hτ₀
  -- unfold 𝒱⟦Mut⟧: `v₁ = ℓ`, and the resource is `ℓ ↦ M @aδ 𝒱⟦T₁⟧δ`
  obtain ⟨α, ha, ℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, hmut⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.letpair (.app v0 (.app load' v1))
          (.seq (.app (.app store' v3) v1) (.pair v3 v0)))))
      = Expr.val (Val.lam (.letpair (.app v0 (eLoad ℓ))
          (.seq (.app (.app store' (.val (.loc ℓ))) v1)
                (.pair (.val (.loc ℓ)) v0)))) := by
    simp [eLoad, Expr.subst, Expr.shift, v0, v1, v3, load', store']
  refine wp_lolli _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  -- `wp-val`; unfold 𝒱⟦⊸⟧ again, let `vf` be arbitrary, apply `wp-⊸`
  refine wp_val _ _ _ ?_
  intro vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.letpair (.app v0 (eLoad ℓ))
          (.seq (.app (.app store' (.val (.loc ℓ))) v1)
                (.pair (.val (.loc ℓ)) v0)))
      = Expr.letpair (.app (.val vf) (eLoad ℓ))
          (.seq (.app (.app store' (.val (.loc ℓ))) v1)
                (.pair (.val (.loc ℓ)) v0)) := by
    simp [eLoad, Expr.subst, v0, v1, store']
  refine wp_lolli _ vf _ _ ?_
  rw [hβ₂]
  -- `wp-m-anti-frame` at `ℓ ↦ M @aδ 𝒱⟦T₁⟧δ`, with the callback's resource `ρ₂`
  -- as the second conjunct; let `v₂` be the payload it hands over
  refine wp_M_antiFrame ℓ α (vDen T₁ δ) _ _ τ ⟨τ₀, ρ₂, hc₂, hmut, ?_⟩
  intro v₂ c₁ c₂ hc hcc p₁ p₂ hp hcp
  -- `(ρ₂ ● ℓ↦v₂) ● ρ_{𝒱⟦T₁⟧δ(v₂)}` regrouped so the cell is the outer factor
  obtain ⟨s, hs, hsp⟩ := compS_exch hcc hcp
  -- `wp-bind` at the argument `load ℓ`, then `wp-load`
  refine wp_bind (.letpair (.appR (.val vf) .hole) _) (eLoad ℓ) _ _ ?_
  refine wp_load ℓ v₂ _ _ ⟨c₁, s, ResU.CompS.comm hsp, hc, ?_⟩
  intro r₁ r₂ hr hcr
  simp only [Kont.plug]
  -- instantiate the callback's 𝒱⟦⊸⟧ with 𝒱⟦T₁⟧δ(v₂); `wp-bind` at `vf v₂`,
  -- framing the cell through the run, and `wp-mono` at its result
  refine wp_bind_frame (.letpair .hole _) (.app (.val vf) (.val v₂))
    (vDen (.tensor T₁ T₂) δ) (ptoOwn ℓ v₂) _ ?_ _
    ⟨s, r₁, hcr, hvf v₂ p₁ s hp hs, hr⟩
  -- unfold 𝒱⟦⊗⟧ at that result, for some `v₃`, `v₄`
  rintro w σ ⟨σ₁, σ₂, hcσ, hw, hown⟩
  obtain ⟨v₃, v₄, hs₂⟩ := hw
  obtain ⟨rfl, ρ₃, ρ₄, hc34, h₃, h₄⟩ := pure_sep_iff.mp hs₂
  simp only [Kont.plug]
  -- `wp-⊗`
  have hβ₃ : Expr.subst 0 v₃ (Expr.subst 0 (v₄.shift 1 0)
        (Expr.seq (.app (.app store' (.val (.loc ℓ))) v1) (.pair (.val (.loc ℓ)) v0)))
      = Expr.seq (eStore ℓ v₃) (.pair (.val (.loc ℓ)) (.val v₄)) := by
    simp [eStore, Expr.subst, v0, v1, store',
      Expr.subst_shift 0 0 0 v₃ v₄.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  refine wp_tensor v₃ v₄ _ _ _ ?_
  rw [hβ₃]
  -- `wp-bind` at `store ℓ v₃`, then `wp-store`, `wp1`, the pair and `wp-val`
  refine wp_bind (.seq .hole (.pair (.val (.loc ℓ)) (.val v₄))) (eStore ℓ v₃) _ _ ?_
  refine wp_store ℓ v₂ v₃ _ _ ⟨σ₂, σ₁, ResU.CompS.comm hcσ, hown, ?_⟩
  intro t₁ t₂ ht hct
  simp only [Kont.plug]
  refine wp_1 _ _ _ ?_
  refine wp_pair (.loc ℓ) v₄ _ _ (wp_val (.pair (.loc ℓ) v₄) _ _ ?_)
  -- choose `∃v` to be `v₃`, and give the borrow back: `𝒱⟦T₂⟧δ(v₄)` is what the
  -- wand is applied to, so `ℓ ↦ M @aδ 𝒱⟦T₁⟧δ ⋆ 𝒱⟦T₂⟧δ(v₄)` folds to
  -- 𝒱⟦Mut @a T₁ ⊗ T₂⟧δ((ℓ, v₄))
  refine ⟨v₃, t₁, σ₁, ResU.CompS.comm hct, ht, ρ₃, ρ₄, hc34, h₃, ?_⟩
  intro m₁ m₂ hm hcm
  exact ⟨.loc ℓ, v₄, pure_sep_mk rfl
    ⟨m₁, ρ₄, ResU.CompS.comm hcm, ⟨α, ha, ℓ, pure_sep_mk rfl hm⟩, h₄⟩⟩

end BoCa.Fig16.LogRel

alias TR.lemma_6_176 := BoCa.Fig16.LogRel.withswap_compat
alias TR.«withswap-compat» := BoCa.Fig16.LogRel.withswap_compat


end
