import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S4_LogicalRelation.Remarks
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_8_FundamentalProperty.Lemmas
import Support.Dynamics.Machine
import Support.Dynamics.PrintedWp
import Support.LogicalRelation.Adequacy
import Support.LogicalRelation.ClosedJudgment
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Compatibility
import Support.Model.Cells
import Support.Model.Empty
import Support.Model.FlatteningCells
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.Surgery
import Support.Model.Update
import Support.Statics.Contexts
import Support.Statics.Presupposed
import Support.Syntax.Terms
import Support.TypedWorld.Compatibility
import Support.TypedWorld.Records
import Support.TypedWorld.Relation
import Support.TypedWorld.World

/-!
# [CONF] §3 — the conference paper's numbered results  (pp. 415:17–18)

Lemma 3.1 is `[TR]` 6.151; its record here aliases the declaration in
`Paper/S6_8_FundamentalProperty/Lemmas.lean`.  Theorem 3.2 (adequacy: termination
and memory reclamation) and Corollary 3.3 (adequacy at `1`) are stated in `[CONF]`
and proved in neither document; the proofs here are ours (`docs/adjudications.md`
§A.1).  Each is stated over the library's machine (`BoLo.Steps`), over `[TR]` §3's
machine as printed (`TR3.Steps`), and at the repaired judgment
(`Fig16.LogRel.Typed.theorem32`, `Fig16.LogRel.Typed.corollary33`).
`Fig16.LogRel.Typed.adequacy` composes Corollary 3.3 at `SemX` with 6.151.  Records
as in §6.1's file.
-/

noncomputable section

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-- `[CONF]` Theorem 3.2 (Adequacy, p. 415:18) over the completed machine: `→*` is
`BoLo.Steps`, the `↦*` of the same row's `wp` (§12.42).
`[as printed]` (`[CONF]` Theorem 3.2, p. 415:18; the `→*` is `[TR]` §3 completed
as §12.42 adjudicates) -/
def Theorem32 : Prop :=
  ∀ (e : Expr) (P : Val → Prop),
    wp e (fun v => Fig16.BoLo.pure (P v)) (PMap.empty : WRes) →
    ∃ v : Val, BoCa.BoLo.Steps emptyMem e emptyMem (.val v) ∧ P v

end BoCa.Adequacy

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `TR3.wp` entails `Fig16.BoLo.wp`, since `TR3.Steps` is contained in
`BoLo.Steps` (`TR3.Steps.toWp`); `wp_lt_fig16` makes the entailment strict (D6).
`[about ours: the two `wp`s, over the two machines]` -/
theorem wp_le_fig16 (e : Expr) (Q : Val → WProp) :
    Entails (wp e Q) (Fig16.BoLo.wp e Q) := by
  intro ρ hw ρf hf
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC⟩ := hw ρf hf
  exact ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇,
    Steps.toWp h₈, h₉, hA, hB, hC⟩

end BoCa.TR3

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-- `[CONF]` Theorem 3.2 over `[TR]` §3's machine as printed: `TR3.wp` in the
antecedent and `TR3.Steps` in the conclusion.  Not comparable with `Theorem32` (D6).
`[as printed]` (`[CONF]` Theorem 3.2, p. 415:18, over `[TR]` §3's machine as
`TR3.Steps` transcribes it) -/
def Theorem32Printed : Prop :=
  ∀ (e : Expr) (P : Val → Prop),
    BoCa.TR3.wp e (fun v => Fig16.BoLo.pure (P v)) (PMap.empty : WRes) →
    ∃ v : Val, BoCa.TR3.Steps emptyMem e emptyMem (.val v) ∧ P v

/-- The memory-reclamation residue: `∅ ↭ ρ⁺` and `ρ⁺|own = ∅` force `ρ⁺ = ∅`.  This is
the conjunct `[CONF]` p. 415:23 calls *"essential for the memory reclamation
component of adequacy (Theorem 3.2), which insists that owned cells are freed
rather than forgotten"*.
`[about ours: what `[CONF]` Theorem 3.2 reduces to at `ρ = ρ_f = ∅`]` -/
def Reclaim : Prop :=
  ∀ ρ : WRes, ResU.UpdV PMap.empty ρ → NoOwn ρ → ρ = PMap.empty

/-- `ResU.Flat.get` (`[TR]` 6.16's step) carries a cell of `ρ` into `⦇ρ⦈` with its
kind; `NoOwn` refuses `own`, and `↭`'s two clauses against `⦇∅⦈ = ∅`
(`Fig16.BoLo.flat_empty`) refuse `imm` and `mut`.
`[about ours: `[CONF]` Theorem 3.2's reclamation conjunct at `ρ = ρ_f = ∅`;
no proof of it is printed in either document]` -/
theorem reclaim : Adequacy.Reclaim := by
  intro ρ hupd hno
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  cases hg : ρ.get l with
  | none => rfl
  | some ψ =>
      exfalso
      obtain ⟨σ, hσ⟩ := hupd.2.2
      obtain ⟨χ, hχ, hk, -, -⟩ := ResU.Flat.get hσ hg
      have hfa : ρ.FlatAt l χ := (ResU.flatAt_iff hσ l χ).mpr hχ
      rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
      · have hko : ψ.kind = Kind.own := by rw [← hk]; exact CellU.kind_ownOf w
        have hr : (ρ.restrict Kind.own).get l = some ψ :=
          ResU.restrict_eq_some.mpr ⟨hg, hko⟩
        rw [hno, PMap.empty_get] at hr
        simp at hr
      · have hemp := (hupd.1.1 l s w ξ hξ).mpr hfa
        rw [ResU.flatAt_iff Fig16.BoLo.flat_empty, PMap.empty_get] at hemp
        simp at hemp
      · obtain ⟨w', ξ', h', hP', hfa'⟩ := (hupd.1.2 l b P).mpr ⟨w, ξ, hξ, hP, hfa⟩
        rw [ResU.flatAt_iff Fig16.BoLo.flat_empty, PMap.empty_get] at hfa'
        simp at hfa'

end BoCa.Adequacy

/-!
## Lemma 3.1 (Fundamental Property) · `[CONF]` p. 415:17 · `variant`

> If Δ; Γ ⊢ e : T then Δ; Γ ⊨ e : T.

**Printed proof, transcribed.** *"The proof of the Fundamental Property is by induction on the syntactic typing judgment, and it is divided into a collection of compatibility lemmas, one per syntactic typing rule, which establishes that its semantic analogue is admissible."*

**Lean.** `BoCa.Fig16.LogRel.Typed.fundamentalProperty`, alias `CONF.lemma_3_1` — `[TR]` Lemma 6.151, the same statement printed twice; its record gives the tag.
-/
alias CONF.lemma_3_1 := BoCa.Fig16.LogRel.Typed.fundamentalProperty

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-!
## Theorem 3.2 (Adequacy) · `[CONF]` p. 415:18 · `proved`

> If ⊨ wp(e){⌜P̂⌝} then (∅, e) →* (∅, v) and P̂(v) for some v.

**Printed proof, transcribed.** Neither document prints one (`docs/adjudications.md` §A.1).

**Lean.** `BoCa.Adequacy.theorem32` (statement `Adequacy.Theorem32`), alias `CONF.theorem_3_2`, tag `[as printed]`; over `[TR]` §3's machine as printed, `Adequacy.theorem32Printed`; at `wpTS`, `Fig16.LogRel.Typed.theorem32`.

**Note.** `⊨ H` is `H ∅` (§A.2a), `⌜P̂⌝` the pointwise lift of a meta `P̂ : Val → Prop`, and `∅` on the memory side `Adequacy.emptyMem`.  The rows over the two machines are not comparable (D6).
-/
/-- `[CONF]` Theorem 3.2 over the completed machine.  `⊨ H` is `H ∅`, so `wp` is read
at `ρ = ∅` and its own `∀ρ_f` at `ρ_f = ∅`; `⌜−⌝` pins `ρ′ = ∅`, the four
composites collapse (`ResU.eq_of_comp_empty_left`), and what is left is `reclaim`.
No occurrence of `→*` survives the unfolding: `[TR]` p. 6's `wp` is a
total-correctness row that asserts the run.
`[about ours: `[CONF]` Theorem 3.2's proof, which neither document prints]` -/
theorem theorem32 : Adequacy.Theorem32 := by
  intro e P hwp
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ',
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    hwp PMap.empty Fig16.LogRel.hash_empty
  obtain ⟨hρ'e, hPv⟩ := h12
  subst hρ'e
  obtain rfl : (PMap.empty : WRes) = fρ := ResU.eq_of_comp_empty_left h4
  obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
  obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl : ρp = PMap.empty := reclaim ρp h10 h11
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h5 Fig16.BoLo.lower_empty
  obtain rfl : μ' = (fun _ => none) := ResU.Lower.functional h7 Fig16.BoLo.lower_empty
  exact ⟨v, h8, hPv⟩

end BoCa.Adequacy

alias CONF.theorem_3_2 := BoCa.Adequacy.theorem32

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-- `[CONF]` Theorem 3.2 over `[TR]` §3's machine as printed, by the same argument;
the residue `reclaim` mentions no machine.
`[about ours: `[CONF]` Theorem 3.2's proof over `[TR]` §3's machine, which
neither document prints]` -/
theorem theorem32Printed : Adequacy.Theorem32Printed := by
  intro e P hwp
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ',
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    hwp PMap.empty Fig16.LogRel.hash_empty
  obtain ⟨hρ'e, hPv⟩ := h12
  subst hρ'e
  obtain rfl : (PMap.empty : WRes) = fρ := ResU.eq_of_comp_empty_left h4
  obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
  obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl : ρp = PMap.empty := reclaim ρp h10 h11
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h5 Fig16.BoLo.lower_empty
  obtain rfl : μ' = (fun _ => none) := ResU.Lower.functional h7 Fig16.BoLo.lower_empty
  exact ⟨v, h8, hPv⟩

end BoCa.Adequacy

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `[CONF]` Theorem 3.2 at the tagged `wpTS`, at the empty list.
`[about ours: [CONF] 3.2 at `wpTS`; the proof is `Adequacy.theorem32`'s]` -/
theorem theorem32 (e : Expr) (P : Val → Prop)
    (hwp : wpTS [] e (fun _ v => Fig16.BoLo.pure (P v)) (PMap.empty : WRes)) :
    ∃ v : Val, BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val v) ∧ P v := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', -, -,
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, -, -, -, -, h12⟩ :=
    hwp PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _)
      TW.empty htg
  obtain ⟨hρ'e, hPv⟩ := h12
  subst hρ'e
  obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
  obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl : ρp = PMap.empty := Adequacy.reclaim ρp h10 h11
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h5 Fig16.BoLo.lower_empty
  obtain rfl : μ' = (fun _ => none) := ResU.Lower.functional h7 Fig16.BoLo.lower_empty
  exact ⟨v, h8, hPv⟩

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-- `[CONF]` Corollary 3.3 (p. 415:18).  `⊨ e : 1` is `Fig16.LogRel.Sem` at
`Δ = Γ = ∅`, whose `ℰ` is `Fig16.BoLo.wp` over `BoLo.Steps`.
`[as printed]` (`[CONF]` Corollary 3.3, p. 415:18) -/
def Corollary33 : Prop :=
  ∀ e : Expr,
    Fig16.LogRel.Sem LifeCtx.empty ([] : Ctx Ty) e Ty.unit →
    BoCa.BoLo.Steps emptyMem e emptyMem (.val .unit)

/-!
## Corollary 3.3 (Adequacy at 1) · `[CONF]` p. 415:18 · `proved`

> If ⊨ e : 1 then (∅, e) →* (∅, ()).

**Printed proof, transcribed.** Neither document prints one (`docs/adjudications.md` §A.1).

**Lean.** `BoCa.Adequacy.corollary33` (statement `Adequacy.Corollary33`), alias `CONF.corollary_3_3`, tag `[as printed]`; over `[TR]` §3's machine as printed, `Adequacy.corollary33Printed`; at `SemX`, `Fig16.LogRel.Typed.corollary33`.

**Literal reading.** `BoCa.TR3.corThree_unreachable`, in `Paper/LiteralReadings/CONF.lean`.

**Note.** The hypothesis is the semantic judgment, so the corollary appeals to Lemma 3.1 nowhere; `Fig16.LogRel.Typed.adequacy` composes the two.  `TR3.corThree_unreachable` measures that composite over the printed machine: `TR3.wp_seq_false` refuses the semantic hypothesis at the same term (§12.42, D6).
-/
/-- `[CONF]` Corollary 3.3: Theorem 3.2 at `P̂ ≜ (· = ())`, since
`Fig16.LogRel.vDen_unit` makes `𝒱⟦1⟧δ` the pure `⌜v = ()⌝`; `Fig16.LogRel.sem_iff`
at `δ = ∅`, `γ = []`, `ρ = ∅` supplies the antecedent.
`[about ours: `[CONF]` Corollary 3.3's proof, which neither document prints]` -/
theorem corollary33 : Adequacy.Corollary33 := by
  intro e hsem
  have hwp := Fig16.LogRel.sem_iff.mp hsem Lifetime.LSub.empty [] PMap.empty
    models_empty (gDen_empty _)
  rw [Fig16.LogRel.substAll, psub_nil, vDen_unit_eq] at hwp
  obtain ⟨v, hsteps, hv⟩ := theorem32 e (· = Val.unit) hwp
  subst hv
  exact hsteps

end BoCa.Adequacy

alias CONF.corollary_3_3 := BoCa.Adequacy.corollary33

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-- `⊨ e : 1` over `[TR]` §3's machine as printed.  `wp` occurs in `𝒱⟦T⟧δ` only at
`⊸` and `∀`, so at `T = 1`, `Δ = Γ = ∅` the interpretation names no machine and
this is `[TR]` p. 4's `Δ; Γ ⊨ e : T` there.
`[about ours: `[TR]` p. 4's `Δ; Γ ⊨ e : T` at `Δ = Γ = ∅`, `T = 1`, over
`TR3.Steps`]` -/
def SemUnitPrinted (e : Expr) : Prop :=
  ∀ δ : LSub, LifeCtx.Models LifeCtx.empty δ →
    BoCa.TR3.wp e (Fig16.LogRel.vDen .unit δ) (PMap.empty : WRes)

/-- `[CONF]` Corollary 3.3 over `[TR]` §3's machine as printed.
`[as printed]` (`[CONF]` Corollary 3.3, p. 415:18, over `[TR]` §3's machine as
`TR3.Steps` transcribes it) -/
def Corollary33Printed : Prop :=
  ∀ e : Expr, SemUnitPrinted e → BoCa.TR3.Steps emptyMem e emptyMem (.val .unit)

/-- `[CONF]` Corollary 3.3 over `[TR]` §3's machine as printed, from
`SemUnitPrinted` by `theorem32Printed`.
`[about ours: `[CONF]` Corollary 3.3's proof over `[TR]` §3's machine, which
neither document prints]` -/
theorem corollary33Printed : Adequacy.Corollary33Printed := by
  intro e hsem
  have hwp := hsem Lifetime.LSub.empty models_empty
  rw [vDen_unit_eq] at hwp
  obtain ⟨v, hsteps, hv⟩ := theorem32Printed e (· = Val.unit) hwp
  subst hv
  exact hsteps

end BoCa.Adequacy

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `[CONF]` Corollary 3.3 at `SemX`.
`[about ours: [CONF] 3.3 at `SemX`; the proof is `Adequacy.corollary33`'s]` -/
theorem corollary33 (e : Expr) (hsem : SemX LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) := by
  have hwp := hsem LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenX_nil _ _)
  rw [substAll, Adequacy.psub_nil] at hwp
  obtain ⟨v, hsteps, hv⟩ := theorem32 e (· = Val.unit) hwp
  subst hv
  exact hsteps

/-- Adequacy from a typing derivation: a closed program `[TR]` p. 2 types at `1`
(`DerivesWf`) runs from the empty memory to `()` and the empty memory.  It is
`fundamental` (6.151 at `SemX`) composed with `corollary33`; at `Δ = Γ = ∅` the
hypotheses `⊧ Δ` and `Δ ⊢ Γ` hold outright.
`[about ours: [CONF] Lemma 3.1 composed with Corollary 3.3, at `SemX`]` -/
theorem adequacy (e : Expr) (hD : DerivesWf LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) :=
  corollary33 e (fundamental _ _ _ _ hD ok_empty (fun s hs => absurd hs (by simp)))

end BoCa.Fig16.LogRel.Typed

end
