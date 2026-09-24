import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Dynamics.Machine
import Support.Dynamics.PrintedWp
import Support.Model.CellFacts
import Support.Model.Composition
import Support.Model.Empty
import Support.Model.Entailments
import Support.Model.Flattening
import Support.Model.Notation
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.ReborrowFrame
import Support.Model.ReborrowRule
import Support.Model.Singletons
import Support.Model.Subtraction
import Support.Model.SubtractionKeep
import Support.Model.UpdateFrame
import Support.Model.UpdateSymmetry
import Support.Syntax.Terms

/-!
# [TR] §6.7 Weakest Precondition Rules  (physical pp. 35–40), Lemmas 6.135–6.150

The rules of `wp` (`[TR]` p. 6, row 5.33): `wp-bind` (6.135), `wp-val` (6.136), the
head steps `wp1`, `wp⊗`, `wp⊕`, `wp⊸` (6.137–6.140), the memory rules `wp-alloc`,
`wp-free`, `wp-load`, `wp-load-I`, `wp-store` (6.141–6.145), `wp-ramify` (6.146),
`wp[]` (6.147), the two forget rules (6.148, 6.149) and the reborrowing rule
`↺ rule` (6.150).

Each rule is proved over the library's machine (rows 3.30, 3.31) and, as `TR3.wp_…`,
over `[TR]` §3's printed machine (6.150 excepted; `docs/adjudications.md` D6).  A
record's *Typed-world version* names the same statement at `wpTS` in
`Support/TypedWorld/`.  Records as in §6.1's file.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.135 (wp-bind) · `[TR]` p. 35 · `proved`

> wp(e){v. wp(K[v]){Q̂}} ⊨ wp(K[e]){Q̂}

**Printed proof, transcribed.** Let `wp(e){v. wp(K[v]){Q̂}}(ρ)` (H1); the goal is `wp(K[e]){Q̂}(ρ)` (G1).  Unfold `wp` in G1 and let `ρ_f # ρ`.  H1 at `ρ_f` gives `(⟦ρ_f ● ρ⟧, e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧, v)` (H2), `ρ ↭ ρ′ ● ρ⁺` (H3), `ρ⁺|own = ∅` (H4) and `wp(K[v]){Q̂}(ρ′)` (H5), for some `ρ′ # ρ_f` (H6), `ρ⁺ # ρ_f ● ρ′` (H7), `v`.  Instantiate H5 at `ρ_f ● ρ⁺`, which is `# ρ′` by H7 and Lemma 6.46: `(⟦ρ_f ● ρ⁺ ● ρ′⟧, K[v]) →* (⟦ρ_f ● ρ⁺ ● ρ⁺⁺ ● ρ″⟧, v′)` (H8), `ρ′ ↭ ρ″ ● ρ⁺⁺` (H9), `ρ⁺⁺|own = ∅` (H10), `Q̂(v′)(ρ″)` (H11), for some `ρ″ # ρ_f ● ρ⁺` (H12), `ρ⁺⁺ # ρ_f ● ρ⁺ ● ρ″` (H13), `v′`.  In G1 choose `ρ″, ρ⁺ ● ρ⁺⁺, v′`.  `ρ″ # ρ_f` by H12 and Lemma 6.11; `ρ⁺ ● ρ⁺⁺ # ρ_f ● ρ″` by H13 and Lemma 6.46; the run by transitivity with H2 and H8; `ρ ↭ ρ″ ● ρ⁺ ● ρ⁺⁺` by H3, H9, H13 and Lemmas 6.48 and 6.49; `(ρ⁺ ● ρ⁺⁺)|own = ∅` by H4 and H10; `Q̂(v′)(ρ″)` by H11.

**Lean.** `BoCa.Fig16.BoLo.wp_bind`, aliases `TR.lemma_6_135`, `TR.«wp-bind»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_bind`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_bind`, in `Support/TypedWorld/Wp.lean`.

**Literal reading.** `BoCa.TR3.stuck_wInj`, `BoCa.TR3.stuck_wSeq`, `BoCa.TR3.wp_inj₁_false`, `BoCa.TR3.wp_seq_false`, `BoCa.TR3.wp_stuck_false_nonvacuous`, `BoCa.TR3.wp_lt_fig16`, in `Paper/LiteralReadings/S6_7_WeakestPreconditionRules.lean`.
-/
/-- `[TR]` Lemma 6.135 (`wp-bind`, p. 35).  `[as printed]` -/
theorem wp_bind (K : Kont) (e : Expr) (Q : Val → WProp) :
    Entails (wp e fun v => wp (K.plug (.val v)) Q) (wp (K.plug e) Q) := by
  intro ρ hw ρf hf
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC⟩ := hw ρf hf
  -- the continuation's frame is `ρ_f ● ρ⁺`, by H7 and `[TR]` 6.46
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρ').mp ⟨fρ', h₂, h₃⟩
  have hfz : ResU.CompS ρf ρp z := ResU.CompS.comm hzp
  obtain ⟨ρ'', ρpp, Y₁, Y'', Y''p, π'', v', ν, ν', k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈,
    k₉, kA, kB, kC⟩ := hC z hz
  -- `[TR]` 6.11 at `ρ_f ● ρ⁺ # ρ″`
  obtain ⟨hfρ'', -⟩ := ResU.Hash.split hfz (ResU.hash_symm k₁)
  -- `(ρ_f ● ρ⁺) ● ρ″ = (ρ_f ● ρ″) ● ρ⁺`
  obtain ⟨F, hF, hFp⟩ := compS_exch hfz k₂
  -- `ρ⁺ ● ρ⁺⁺ # ρ_f ● ρ″`, by 6.46
  obtain ⟨ZZ, hZZ, hZF⟩ := (hash_shift ρpp ρp F).mp ⟨Y'', ResU.CompS.comm hFp, k₃⟩
  have hZZ' : ResU.CompS ρp ρpp ZZ := ResU.CompS.comm hZZ
  obtain ⟨ZZ₀, hZZ₀, hFZ₀⟩ := compS_reassoc hFp k₆
  have hFZ : ResU.CompS F ZZ Y''p := by
    rwa [ResU.CompS.functional hZZ₀ hZZ'] at hFZ₀
  -- the two runs meet at `⟦(ρ_f ● ρ⁺) ● ρ′⟧ = ⟦(ρ_f ● ρ′) ● ρ⁺⟧`
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρ' fρ'p := by rwa [ResU.CompS.functional hz₀ hfz] at hY
  have hν : ν = μ' :=
    ResU.Lower.functional (ResU.CompS.functional k₄ hzY ▸ k₅) h₇
  -- `ρ⁺ # ρ′` and `ρ⁺ # ρ″ ● ρ⁺⁺`, by 6.11 and 6.46
  obtain ⟨-, hpρ'⟩ := ResU.Hash.split h₂ (ResU.hash_symm h₃)
  obtain ⟨d, hd, hfd⟩ := compS_reassoc hfz k₂
  obtain ⟨-, hdp⟩ := ResU.Hash.split hfd (ResU.hash_symm k₃)
  obtain ⟨π₀, hπ₀, hpπ₀⟩ := (hash_shift ρp ρ'' ρpp).mpr ⟨d, hd, hdp⟩
  have hpπ : ResU.Hash ρp π'' := by rwa [ResU.CompS.functional hπ₀ k₉] at hpπ₀
  obtain ⟨Yn, hYn, -⟩ := hpπ.2
  obtain ⟨ZZ₁, hZZ₁, hρ''Z₀⟩ := compS_lcomm k₉ hYn
  have hρ''Z : ResU.CompS ρ'' ZZ Yn := by
    rwa [ResU.CompS.functional hZZ₁ hZZ'] at hρ''Z₀
  refine ⟨ρ'', ZZ, fρ, F, Y''p, Yn, v', μ, ν', ResU.hash_symm hfρ'', hF, hZF,
    h₄, h₅, hFZ, k₇, (h₈.plug K).trans (hν ▸ k₈), hρ''Z, ?_,
    noOwn_compS hZZ' hB kB, kC⟩
  exact ResU.UpdV.trans hA
    (updV_frame (ResU.CompS.comm h₉) hYn (ResU.hash_symm hpρ') hpπ kA)

end BoCa.Fig16.BoLo

alias TR.lemma_6_135 := BoCa.Fig16.BoLo.wp_bind
alias TR.«wp-bind» := BoCa.Fig16.BoLo.wp_bind

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.135 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_bind (K : Kont) (e : Expr) (Q : Val → WProp) :
    Entails (wp e fun v => wp (K.plug (.val v)) Q) (wp (K.plug e) Q) := by
  intro ρ hw ρf hf
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC⟩ := hw ρf hf
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρ').mp ⟨fρ', h₂, h₃⟩
  have hfz : ResU.CompS ρf ρp z := ResU.CompS.comm hzp
  obtain ⟨ρ'', ρpp, Y₁, Y'', Y''p, π'', v', ν, ν', k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈,
    k₉, kA, kB, kC⟩ := hC z hz
  obtain ⟨hfρ'', -⟩ := ResU.Hash.split hfz (ResU.hash_symm k₁)
  obtain ⟨F, hF, hFp⟩ := compS_exch hfz k₂
  obtain ⟨ZZ, hZZ, hZF⟩ :=
    (hash_shift ρpp ρp F).mp ⟨Y'', ResU.CompS.comm hFp, k₃⟩
  have hZZ' : ResU.CompS ρp ρpp ZZ := ResU.CompS.comm hZZ
  obtain ⟨ZZ₀, hZZ₀, hFZ₀⟩ := compS_reassoc hFp k₆
  have hFZ : ResU.CompS F ZZ Y''p := by
    rwa [ResU.CompS.functional hZZ₀ hZZ'] at hFZ₀
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρ' fρ'p := by rwa [ResU.CompS.functional hz₀ hfz] at hY
  have hν : ν = μ' :=
    ResU.Lower.functional (ResU.CompS.functional k₄ hzY ▸ k₅) h₇
  obtain ⟨-, hpρ'⟩ := ResU.Hash.split h₂ (ResU.hash_symm h₃)
  obtain ⟨d, hd, hfd⟩ := compS_reassoc hfz k₂
  obtain ⟨-, hdp⟩ := ResU.Hash.split hfd (ResU.hash_symm k₃)
  obtain ⟨π₀, hπ₀, hpπ₀⟩ := (hash_shift ρp ρ'' ρpp).mpr ⟨d, hd, hdp⟩
  have hpπ : ResU.Hash ρp π'' := by rwa [ResU.CompS.functional hπ₀ k₉] at hpπ₀
  obtain ⟨Yn, hYn, -⟩ := hpπ.2
  obtain ⟨ZZ₁, hZZ₁, hρ''Z₀⟩ := compS_lcomm k₉ hYn
  have hρ''Z : ResU.CompS ρ'' ZZ Yn := by
    rwa [ResU.CompS.functional hZZ₁ hZZ'] at hρ''Z₀
  refine ⟨ρ'', ZZ, fρ, F, Y''p, Yn, v', μ, ν', ResU.hash_symm hfρ'', hF, hZF,
    h₄, h₅, hFZ, k₇, (h₈.plug K).trans (hν ▸ k₈), hρ''Z, ?_,
    noOwn_compS hZZ' hB kB, kC⟩
  exact ResU.UpdV.trans hA
    (updV_frame (ResU.CompS.comm h₉) hYn (ResU.hash_symm hpρ') hpπ kA)

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.136 (wp-val) · `[TR]` p. 36 · `proved`

> Q̂(v) ⫤⊨ wp(v){Q̂}

**Printed proof, transcribed.** Let `Q̂(v)(ρ)` (H1) and `ρ_f # ρ` (H2).  Choose `ρ′, ρ⁺, v` to be `ρ, ∅, v`.  It suffices that `ρ # ρ_f` (H2); `∅ # ρ_f ● ρ′` (by definition); `(⟦ρ_f ● ρ⟧, v) →* (⟦ρ_f ● ρ ● ∅⟧, v)` (Lemma 6.4 and reflexivity); `ρ ↭ ρ ● ∅` (Lemmas 6.4 and 6.47); `∅|own = ∅` (by definition); `Q̂(v)(ρ)` (H1).

**Lean.** `BoCa.Fig16.BoLo.wp_val`, aliases `TR.lemma_6_136`, `TR.«wp-val»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_val`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_val`, in `Support/TypedWorld/Wp.lean`.

**Note.** The printed `⫤⊨` is read as `⊨`; the printed proof runs that direction only (`docs/adjudications.md` §12.65).
-/
/-- `[TR]` Lemma 6.136 (`wp-val`, p. 36), its `⊨` direction (§12.65).  `[as printed]` -/
theorem wp_val (v : Val) (Q : Val → WProp) : Entails (Q v) (wp (.val v) Q) := by
  intro ρ hQ ρf hf
  obtain ⟨σ, μ, hσ, hv, hμ⟩ := hash_lower hf
  exact ⟨ρ, PMap.empty, σ, σ, σ, ρ, v, μ, μ, ResU.hash_symm hf, hσ,
    ResU.hash_symm (ResU.hash_empty_right hv), hσ, hμ,
    ResU.comp_empty_right σ, hμ, Steps.refl _ _, ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, noOwn_empty, hQ⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_136 := BoCa.Fig16.BoLo.wp_val
alias TR.«wp-val» := BoCa.Fig16.BoLo.wp_val

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.136 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_val (v : Val) (Q : Val → WProp) : Entails (Q v) (wp (.val v) Q) := by
  intro ρ hQ ρf hf
  obtain ⟨σ, μ, hσ, hv, hμ⟩ := hash_lower hf
  exact ⟨ρ, PMap.empty, σ, σ, σ, ρ, v, μ, μ, ResU.hash_symm hf, hσ,
    ResU.hash_symm (ResU.hash_empty_right hv), hσ, hμ,
    ResU.comp_empty_right σ, hμ, Steps.refl _ _, ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2,
    noOwn_empty, hQ⟩

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- One deterministic head step in front of a `wp`; `[TR]` 6.137–6.140 are instances.
`[about ours: the step `[TR]` 6.137–6.140 share]` -/
theorem wp_head {e e' : Expr} (h : ∀ μ : Heap, Head μ e μ e') (Q : Val → WProp) :
    Entails (wp e' Q) (wp e Q) := by
  intro ρ hw ρf hf
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC⟩ := hw ρf hf
  exact ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇,
    .more (Step1.head (h μ)) h₈, h₉, hA, hB, hC⟩

/-!
## Lemma 6.137 (wp1) · `[TR]` p. 36 · `proved`

> wp(e){Q̂} ⊨ wp((); e){Q̂}

**Printed proof, transcribed.** Let `wp(e){Q̂}(ρ)` (H1) and `ρ_f # ρ` (H2).  H1 at `ρ_f` gives the run (H3), `ρ ↭ ρ′ ● ρ⁺` (H4), `ρ⁺|own = ∅` (H5), `Q̂(v)(ρ′)` (H6), `ρ′ # ρ_f` (H7), `ρ⁺ # ρ_f ● ρ′` (H8).  Choose `ρ′, ρ⁺, v`.  Most obligations are immediate; the run is `(⟦ρ_f ● ρ⟧, (); e) → (⟦ρ_f ● ρ⟧, e)` by the operational semantics, then H3.

**Lean.** `BoCa.Fig16.BoLo.wp_1`, aliases `TR.lemma_6_137`, `TR.wp1`, tag `[as printed]`.

**Also here.** `BoCa.Fig16.BoLo.wp_head`; `BoCa.TR3.wp_head`; `BoCa.TR3.wp_1`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_head`, in `Support/TypedWorld/Wp.lean`; `BoCa.Fig16.LogRel.Typed.wpTS_1`, in `Support/TypedWorld/Wp.lean`.
-/
/-- `[TR]` Lemma 6.137 (`wp1`, p. 36).  `[as printed]` -/
theorem wp_1 (e : Expr) (Q : Val → WProp) :
    Entails (wp e Q) (wp (.seq (.val .unit) e) Q) :=
  wp_head (fun μ => .seq μ e) Q

end BoCa.Fig16.BoLo

alias TR.lemma_6_137 := BoCa.Fig16.BoLo.wp_1
alias TR.wp1 := BoCa.Fig16.BoLo.wp_1

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- One printed head step in front of a `wp`.
`[about ours: the step `[TR]` 6.137–6.140 share]` -/
theorem wp_head {e e' : Expr} (h : ∀ μ : Heap, Head μ e μ e') (Q : Val → WProp) :
    Entails (wp e' Q) (wp e Q) := by
  intro ρ hw ρf hf
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC⟩ := hw ρf hf
  exact ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇,
    .more (Step1.head (h μ)) h₈, h₉, hA, hB, hC⟩

/-- `[TR]` Lemma 6.137 over `[TR]` §3's printed machine, whose `1↦` fires at `()` alone.  `[as printed]` -/
theorem wp_1 (e : Expr) (Q : Val → WProp) :
    Entails (wp e Q) (wp (.seq (.val .unit) e) Q) :=
  wp_head (fun μ => .one μ e) Q

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.138 (wp⊗) · `[TR]` p. 36 · `proved`

> wp(e[v₁/x₁, v₂/x₂]){Q̂} ⊨ wp(let (x₁, x₂) = (v₁, v₂); e){Q̂}

**Printed proof, transcribed.** As for Lemma 6.137: H1 at `ρ_f` gives H3–H8; choose `ρ′, ρ⁺, v`; the run is `(⟦ρ_f ● ρ⟧, let (x₁, x₂) = (v₁, v₂); e) → (⟦ρ_f ● ρ⟧, e[v₁/x₁, v₂/x₂])` by the operational semantics, then H3.

**Lean.** `BoCa.Fig16.BoLo.wp_tensor`, aliases `TR.lemma_6_138`, `TR.«wp⊗»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_tensor`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_tensor`, in `Support/TypedWorld/Wp.lean`.
-/
/-- `[TR]` Lemma 6.138 (`wp⊗`, p. 36).  `[as printed]` -/
theorem wp_tensor (v₁ v₂ : Val) (e : Expr) (Q : Val → WProp) :
    Entails (wp ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁) Q)
      (wp (.letpair (.val (.pair v₁ v₂)) e) Q) :=
  wp_head (fun μ => .letpair μ v₁ v₂ e) Q

end BoCa.Fig16.BoLo

alias TR.lemma_6_138 := BoCa.Fig16.BoLo.wp_tensor
alias TR.«wp⊗» := BoCa.Fig16.BoLo.wp_tensor

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.138 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_tensor (v₁ v₂ : Val) (e : Expr) (Q : Val → WProp) :
    Entails (wp ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁) Q)
      (wp (.letpair (.val (.pair v₁ v₂)) e) Q) :=
  wp_head (fun μ => .tensor μ v₁ v₂ e) Q

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.139 (wp⊕) · `[TR]` p. 36 · `proved`

> wp(eᵢ[v/xᵢ]){Q̂} ⊨ wp(match i v {1 x₁ ⇒ e₁ ∣ 2 x₂ ⇒ e₂}){Q̂}

**Printed proof, transcribed.** As for Lemma 6.137: H1 at `ρ_f` gives H3–H8; choose `ρ′, ρ⁺, v`; the run is `(⟦ρ_f ● ρ⟧, match i v {…}) → (⟦ρ_f ● ρ⟧, eᵢ[v/xᵢ])` by the operational semantics, then H3.

Schematic in `i`, as Lemma 6.72: one declaration per `i`.

**Lean.** `BoCa.Fig16.BoLo.wp_sum₁`, aliases `TR.lemma_6_139_1`, `TR.«wp⊕₁»`, tag `[as printed]`; `BoCa.Fig16.BoLo.wp_sum₂`, aliases `TR.lemma_6_139_2`, `TR.«wp⊕₂»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_sum₁`; `BoCa.TR3.wp_sum₂`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_sum₁`, in `Support/TypedWorld/Wp.lean`; `BoCa.Fig16.LogRel.Typed.wpTS_sum₂`, in `Support/TypedWorld/Wp.lean`.
-/
/-- `[TR]` Lemma 6.139 (`wp⊕`, p. 36) at `i = 1`.  `[as printed]` -/
theorem wp_sum₁ (v : Val) (e₁ e₂ : Expr) (Q : Val → WProp) :
    Entails (wp (e₁.subst 0 v) Q) (wp (.case (.val (.inj₁ v)) e₁ e₂) Q) :=
  wp_head (fun μ => .case₁ μ v e₁ e₂) Q

end BoCa.Fig16.BoLo

alias TR.lemma_6_139_1 := BoCa.Fig16.BoLo.wp_sum₁
alias TR.«wp⊕₁» := BoCa.Fig16.BoLo.wp_sum₁

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `[TR]` Lemma 6.139 at `i = 2`.  `[as printed]` -/
theorem wp_sum₂ (v : Val) (e₁ e₂ : Expr) (Q : Val → WProp) :
    Entails (wp (e₂.subst 0 v) Q) (wp (.case (.val (.inj₂ v)) e₁ e₂) Q) :=
  wp_head (fun μ => .case₂ μ v e₁ e₂) Q

end BoCa.Fig16.BoLo

alias TR.lemma_6_139_2 := BoCa.Fig16.BoLo.wp_sum₂
alias TR.«wp⊕₂» := BoCa.Fig16.BoLo.wp_sum₂

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.139 at `i = 1`, over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_sum₁ (v : Val) (e₁ e₂ : Expr) (Q : Val → WProp) :
    Entails (wp (e₁.subst 0 v) Q) (wp (.case (.val (.inj₁ v)) e₁ e₂) Q) :=
  wp_head (fun μ => .sum₁ μ v e₁ e₂) Q

/-- `[TR]` Lemma 6.139 at `i = 2`, over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_sum₂ (v : Val) (e₁ e₂ : Expr) (Q : Val → WProp) :
    Entails (wp (e₂.subst 0 v) Q) (wp (.case (.val (.inj₂ v)) e₁ e₂) Q) :=
  wp_head (fun μ => .sum₂ μ v e₁ e₂) Q

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.140 (wp⊸) · `[TR]` p. 36 · `proved`

> wp(e[v/x]){Q̂} ⊨ wp((λx.e) v){Q̂}

**Printed proof, transcribed.** As for Lemma 6.137: H1 at `ρ_f` gives H3–H8; choose `ρ′, ρ⁺, v`; the run is `(⟦ρ_f ● ρ⟧, (λx.e) v) → (⟦ρ_f ● ρ⟧, e[v/x])` by the operational semantics, then H3.

**Lean.** `BoCa.Fig16.BoLo.wp_lolli`, aliases `TR.lemma_6_140`, `TR.«wp⊸»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_lolli`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_lolli`, in `Support/TypedWorld/Wp.lean`.
-/
/-- `[TR]` Lemma 6.140 (`wp⊸`, p. 36).  `[as printed]` -/
theorem wp_lolli (b : Expr) (v : Val) (Q : Val → WProp) :
    Entails (wp (b.subst 0 v) Q) (wp (.app (.val (.lam b)) (.val v)) Q) :=
  wp_head (fun μ => .beta μ b v) Q

end BoCa.Fig16.BoLo

alias TR.lemma_6_140 := BoCa.Fig16.BoLo.wp_lolli
alias TR.«wp⊸» := BoCa.Fig16.BoLo.wp_lolli

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.140 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_lolli (b : Expr) (v : Val) (Q : Val → WProp) :
    Entails (wp (b.subst 0 v) Q) (wp (.app (.val (.lam b)) (.val v)) Q) :=
  wp_head (fun μ => .lolli μ b v) Q

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.141 (wp-alloc) · `[TR]` p. 37 · `proved`

> (∀ℓ. ℓ ↦ v –⋆ Q̂(ℓ)) ⊨ wp(alloc v){Q̂}

**Printed proof, transcribed.** Let `(∀ℓ. ℓ ↦ v –⋆ Q̂(ℓ))(ρ)` (H1) and `ρ_f # ρ` (H2).  Choose `ℓ ∉ ρ_f ● ρ` (H3).  H1 at `ℓ`, `ℓ ↦ own(v)`, `ρ ● ℓ ↦ own(v)` gives `Q̂(ℓ)(ρ ● ℓ ↦ own(v))` (H4).  Choose `ρ′, ρ⁺, v` to be `ρ ● ℓ ↦ own(v), ∅, ℓ`.  `ρ ● ℓ ↦ own(v) # ρ_f` by H2 and H3; `∅ # ρ_f ● ρ′` by definition; the run is `(⟦ρ_f ● ρ⟧, alloc v) → (⟦ρ_f ● ρ⟧ ⊎ ℓ ↦ v, ℓ)`, and `⟦ρ_f ● ρ⟧ ⊎ ℓ ↦ v = ⟦ρ_f ● ρ⟧ ⊎ ⟦ℓ ↦ own(v)⟧ = ⟦ρ_f ● ρ ● ℓ ↦ own(v)⟧`; `ρ ↭ ρ ● ℓ ↦ own(v)` by definition, since `↭` ignores `own` cells; `∅|own = ∅`; `Q̂(ℓ)(ρ ● ℓ ↦ own(v))` by H4.

**Lean.** `BoCa.Fig16.BoLo.wp_alloc`, aliases `TR.lemma_6_141`, `TR.«wp-alloc»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_alloc`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_alloc`, in `Support/TypedWorld/Wp.lean`.

**Note.** The print chooses `ℓ ∉ ρ_f ● ρ`; the `alloc↦` step needs `ℓ ∉ ⟦ρ_f ● ρ⟧`, so `ℓ` is chosen fresh for the flattening and `Fig16.BoLo.get_eq_none_of_flat` recovers the print's choice.
-/
/-- `[TR]` Lemma 6.141 (`wp-alloc`, p. 37).  `[as printed]` -/
theorem wp_alloc (v : Val) (Q : Val → WProp) :
    Entails (all fun l : BoCa.Loc => wand (ptoOwn l v) (Q (.loc l)))
      (wp (.app (.val (.prim .alloc)) (.val v)) Q) := by
  intro ρ h ρf hf
  obtain ⟨σ, μ, hσ, hvσ, hμ⟩ := hash_lower hf
  obtain ⟨τ, hτ, hval⟩ := id hμ
  obtain ⟨l, hl⟩ := PMap.exists_fresh loc_infinite τ
  have hμl : μ l = none := (lower_eq_none_iff hval).mpr hl
  have hρl : ρ.get l = none :=
    ((ResU.Comp.eq_none_iff hσ l).mp (get_eq_none_of_flat hτ hl)).2
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hρl)
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ hμ hμl hx
  exact ⟨x, PMap.empty, σ, σ', σ', x, .loc l, μ, BoCa.BoLo.Heap.upd μ l v,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    hσ, hμ, ResU.comp_empty_right σ', hlow',
    Steps.one (Step1.head (Head.alloc μ v l hμl)), ResU.comp_empty_right x,
    updV_compS_own hx (hash_valid hf).2 (hash_valid hfx).2,
    noOwn_empty, h l _ x rfl hx⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_141 := BoCa.Fig16.BoLo.wp_alloc
alias TR.«wp-alloc» := BoCa.Fig16.BoLo.wp_alloc

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.141 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_alloc (v : Val) (Q : Val → WProp) :
    Entails (all fun l : BoCa.Loc => wand (ptoOwn l v) (Q (.loc l)))
      (wp (.app (.val (.prim .alloc)) (.val v)) Q) := by
  intro ρ h ρf hf
  obtain ⟨σ, μ, hσ, hvσ, hμ⟩ := hash_lower hf
  obtain ⟨τ, hτ, hval⟩ := id hμ
  obtain ⟨l, hl⟩ := PMap.exists_fresh loc_infinite τ
  have hμl : μ l = none := (lower_eq_none_iff hval).mpr hl
  have hρl : ρ.get l = none :=
    ((ResU.Comp.eq_none_iff hσ l).mp (get_eq_none_of_flat hτ hl)).2
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hρl)
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ hμ hμl hx
  exact ⟨x, PMap.empty, σ, σ', σ', x, .loc l, μ, BoCa.BoLo.Heap.upd μ l v,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    hσ, hμ, ResU.comp_empty_right σ', hlow',
    Steps.one (steps_alloc μ v l hμl), ResU.comp_empty_right x,
    updV_compS_own hx (hash_valid hf).2
      (hash_valid hfx).2,
    noOwn_empty, h l _ x rfl hx⟩

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.142 (wp-free) · `[TR]` p. 37 · `proved`

> ℓ ↦ v ⋆ Q̂(v) ⊨ wp(free ℓ){Q̂}

**Printed proof, transcribed.** Let `ρ = ρ₁ ● ρ₂` with `ρ₁ = ℓ ↦ own(v)` and `Q̂(v)(ρ₂)` (H1), and `ρ_f # ρ` (H2).  Choose `ρ′, ρ⁺, v` to be `ρ₂, ∅, v`.  What is not immediate is the run: by definition `⟦ρ_f ● ℓ ↦ own(v) ● ρ₂⟧ = ⟦ρ_f ● ρ₂⟧ ⊎ ℓ ↦ v`, and by the operational semantics `(⟦ρ_f ● ρ₂⟧ ⊎ ℓ ↦ v, free ℓ) → (⟦ρ_f ● ρ₂⟧, v)`.

**Lean.** `BoCa.Fig16.BoLo.wp_free`, aliases `TR.lemma_6_142`, `TR.«wp-free»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_free`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_free`, in `Support/TypedWorld/Wp.lean`.
-/
/-- `[TR]` Lemma 6.142 (`wp-free`, p. 37).  `[as printed]` -/
theorem wp_free (l : BoCa.Loc) (v : Val) (Q : Val → WProp) :
    Entails (sep (ptoOwn l v) (Q v))
      (wp (.app (.val (.prim .free)) (.val (.loc l))) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, rfl, hQ⟩ ρf hf
  obtain ⟨σ, μ, hσ, hvσ, hμ⟩ := hash_lower hf
  have h₂ : ResU.Hash ρf ρ₂ :=
    ResU.hash_symm (ResU.Hash.split hcρ (ResU.hash_symm hf)).2
  obtain ⟨σ₂, hσ₂, hσ₂σ⟩ :=
    (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v)) σ).mp
      ⟨ρ, ResU.CompS.comm hcρ, hσ⟩
  obtain ⟨hlv, μ₂, hlow₂, hupd, hnone⟩ := lower_compS_own_inv hσ₂σ hμ
  have hdel : BoCa.BoLo.Heap.del μ l = μ₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.del_same, hnone]
    · rw [BoCa.BoLo.Heap.del_other e, hupd, BoCa.BoLo.Heap.upd_other e]
  refine ⟨ρ₂, PMap.empty, σ, σ₂, σ₂, ρ₂, v, μ, μ₂,
    ResU.hash_symm h₂, hσ₂,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp h₂ hσ₂)),
    hσ, hμ, ResU.comp_empty_right σ₂, hlow₂, ?_, ResU.comp_empty_right ρ₂,
    (updV_compS_own (ResU.CompS.comm hcρ) (hash_valid h₂).2 (hash_valid hf).2).symm,
    noOwn_empty, hQ⟩
  rw [← hdel]
  exact Steps.one (Step1.head (Head.free μ l v hlv))

end BoCa.Fig16.BoLo

alias TR.lemma_6_142 := BoCa.Fig16.BoLo.wp_free
alias TR.«wp-free» := BoCa.Fig16.BoLo.wp_free

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.142 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_free (l : BoCa.Loc) (v : Val) (Q : Val → WProp) :
    Entails (sep (ptoOwn l v) (Q v))
      (wp (.app (.val (.prim .free)) (.val (.loc l))) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, rfl, hQ⟩ ρf hf
  obtain ⟨σ, μ, hσ, hvσ, hμ⟩ := hash_lower hf
  have h₂ : ResU.Hash ρf ρ₂ :=
    ResU.hash_symm (ResU.Hash.split hcρ (ResU.hash_symm hf)).2
  obtain ⟨σ₂, hσ₂, hσ₂σ⟩ :=
    (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v)) σ).mp
      ⟨ρ, ResU.CompS.comm hcρ, hσ⟩
  obtain ⟨hlv, μ₂, hlow₂, hupd, hnone⟩ := lower_compS_own_inv hσ₂σ hμ
  have hdel : BoCa.BoLo.Heap.del μ l = μ₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.del_same, hnone]
    · rw [BoCa.BoLo.Heap.del_other e, hupd, BoCa.BoLo.Heap.upd_other e]
  refine ⟨ρ₂, PMap.empty, σ, σ₂, σ₂, ρ₂, v, μ, μ₂,
    ResU.hash_symm h₂, hσ₂,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp h₂ hσ₂)),
    hσ, hμ, ResU.comp_empty_right σ₂, hlow₂, ?_, ResU.comp_empty_right ρ₂,
    (updV_compS_own (ResU.CompS.comm hcρ) (hash_valid h₂).2
      (hash_valid hf).2).symm,
    noOwn_empty, hQ⟩
  rw [← hdel]
  exact Steps.one (Step1.head (Head.free μ l v hlv))

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.143 (wp-load) · `[TR]` p. 37 · `proved`

> ℓ ↦ v ⋆ (ℓ ↦ v –⋆ Q̂(v)) ⊨ wp(load ℓ){Q̂}

**Printed proof, transcribed.** Let `ρ = ρ₁ ● ρ₂` with `ρ₁ = ℓ ↦ own(v)` and `(ℓ ↦ v –⋆ Q̂(v))(ρ₂)` (H1).  H1 at `ρ₁, ρ` gives `Q̂(v)(ρ)` (H2).  Let `ρ_f # ρ` and choose `ρ′, ρ⁺, v` to be `ρ, ∅, v`.  What is not immediate is the run: `⟦ρ_f ● ρ⟧ = ⟦ρ_f ● ρ₁ ● ℓ ↦ own(v)⟧ = ⟦ρ_f ● ρ₁⟧ ⊎ ℓ ↦ v`, and `(⟦ρ_f ● ρ₁⟧ ⊎ ℓ ↦ v, load ℓ) → (⟦ρ_f ● ρ₁⟧ ⊎ ℓ ↦ v, v)`.

**Lean.** `BoCa.Fig16.BoLo.wp_load`, aliases `TR.lemma_6_143`, `TR.«wp-load»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_load`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_load`, in `Support/TypedWorld/Wp.lean`.
-/
/-- `[TR]` Lemma 6.143 (`wp-load`, p. 37).  `[as printed]` -/
theorem wp_load (l : BoCa.Loc) (v : Val) (Q : Val → WProp) :
    Entails (sep (ptoOwn l v) (wand (ptoOwn l v) (Q v)))
      (wp (.app (.val (.prim .load)) (.val (.loc l))) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, rfl, hwand⟩ ρf hf
  obtain ⟨σ, μ, hσ, hvσ, hμ⟩ := hash_lower hf
  have hρ : ρ.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_right_none hcρ (ResU.compatS_single_own hcρ.1),
      ResU.single_get_self]
  have hlv : μ l = some v :=
    lower_get_own hμ (by
      rw [ResU.Comp.get_of_left_none hσ (get_eq_none_of_compatS_own
        (ResU.CompatS.symm hf.1) hρ)]
      exact hρ)
  exact ⟨ρ, PMap.empty, σ, σ, σ, ρ, v, μ, μ,
    ResU.hash_symm hf, hσ,
    ResU.hash_symm (ResU.hash_empty_right hvσ),
    hσ, hμ, ResU.comp_empty_right σ, hμ,
    Steps.one (Step1.head (Head.load μ l v hlv)), ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, noOwn_empty,
    hwand _ ρ rfl (ResU.CompS.comm hcρ)⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_143 := BoCa.Fig16.BoLo.wp_load
alias TR.«wp-load» := BoCa.Fig16.BoLo.wp_load

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.143 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_load (l : BoCa.Loc) (v : Val) (Q : Val → WProp) :
    Entails (sep (ptoOwn l v) (wand (ptoOwn l v) (Q v)))
      (wp (.app (.val (.prim .load)) (.val (.loc l))) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, rfl, hwand⟩ ρf hf
  obtain ⟨σ, μ, hσ, hvσ, hμ⟩ := hash_lower hf
  have hρ : ρ.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_right_none hcρ (ResU.compatS_single_own hcρ.1),
      ResU.single_get_self]
  have hlv : μ l = some v :=
    lower_get_own hμ (by
      rw [ResU.Comp.get_of_left_none hσ (get_eq_none_of_compatS_own
        (ResU.CompatS.symm hf.1) hρ)]
      exact hρ)
  exact ⟨ρ, PMap.empty, σ, σ, σ, ρ, v, μ, μ,
    ResU.hash_symm hf, hσ,
    ResU.hash_symm (ResU.hash_empty_right hvσ),
    hσ, hμ, ResU.comp_empty_right σ, hμ,
    Steps.one (Step1.head (Head.load μ l v hlv)), ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2,
    noOwn_empty, hwand _ ρ rfl (ResU.CompS.comm hcρ)⟩

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.144 (wp-load-I) · `[TR]` p. 37 · `proved`

> ℓ ↦I_α P̂ ⋆ (∀v. ℓ ↦I_α (v′. ⌜v = v′⌝ ⋆ P̂(v)) –⋆ Q̂(v)) ⊨ wp(load ℓ){Q̂}

**Printed proof, transcribed.** Let `R = ∀v. ℓ ↦I_α (v′. ⌜v = v′⌝ ⋆ P̂(v)) –⋆ Q̂(v)` and `ρ ∈ ℓ ↦I_α P̂ ⋆ R`, so `ρ = ℓ ↦ imm(β, v, ρ_v) ● ρ_R` with `ρ_v ∈ P̂(v)`, `α ⊑ ⊔β` and `ρ_R ∈ R`.  Since `⌜v = v′⌝ ⋆ P̂(v)` is equivalent to `P̂(v)`, and `α ⊑ ⊔β`, `ℓ ↦ imm(β, v, ρ_v) ∈ ℓ ↦I_α (v′. ⌜v = v′⌝ ⋆ P̂(v))`; since `ρ_R ∈ R` and `ρ_R` is composable with the cell, `ℓ ↦ imm(β, v, ρ_v) ● ρ_R = ρ ∈ Q̂(v)`.  For any `ρ_f # ρ`, choosing `ρ′ ≔ ρ`, `ρ⁺ ≔ ∅`, `v ≔ v` gives `(⟦ρ_f ● ρ⟧, load ℓ) →* (⟦ρ_f ● ρ′⟧, v)`, `⟦ρ_f ● ρ⟧ = ⟦ρ_f ● ρ′⟧`, `ρ ↭ ρ′ ● ρ⁺`, `ρ⁺|own = ∅` and `ρ′ ∈ Q̂(v)`.

**Lean.** `BoCa.Fig16.BoLo.wp_load_I`, aliases `TR.lemma_6_144`, `TR.«wp-load-I»`, tag `[as printed]`.

**Also here.** `BoCa.Fig16.BoLo.wp_load_I_conf`; `BoCa.Fig16.BoLo.wp_load_I_nonvacuous`; `BoCa.TR3.wp_load_I`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_load_I`, in `Support/TypedWorld/Wp.lean`.

**Note.** `[CONF]` Fig. 13b prints a rule of the same name at the constant family and at `wp(v){Q̂}`; it is `Fig16.BoLo.wp_load_I_conf`, `[variant]` (`docs/adjudications.md` §12.65).
-/
/-- `[TR]` Lemma 6.144 (`wp-load-I`, p. 37).  `[as printed]` -/
theorem wp_load_I (l : BoCa.Loc) (α : Life) (P Q : Val → WProp) :
    Entails
      (sep (ptoImm l α P)
        (all fun v =>
          wand (ptoImm l α (fun v' => sep (pure (v = v')) (P v))) (Q v)))
      (wp (.app (.val (.prim .load)) (.val (.loc l))) Q) := by
  rintro ρ ⟨ρ₁, ρR, hcρ, ⟨s, v, σ, hs, rfl, hP, hα⟩, hR⟩ ρf hf
  have hcell : ptoImm l α (fun v' => sep (pure (v = v')) (P v))
      (ResU.single l (CellU.immOf s v σ hs)) :=
    ⟨s, v, σ, hs, rfl, (pure_sep_biEntails rfl (P v)).2 σ hP, hα⟩
  have hQ : Q v ρ := hR v _ ρ hcell (ResU.CompS.comm hcρ)
  obtain ⟨τ, μ, hτ, hvτ, hμ⟩ := hash_lower hf
  obtain ⟨χ, hχ, heχ⟩ := compS_get_erase hcρ (ResU.single_get_self l _)
  obtain ⟨χ', hχ', heχ'⟩ := compS_get_erase (ResU.CompS.comm hτ) hχ
  have hlv : μ l = some v := by
    rw [lower_get hμ hχ', heχ', heχ]
    rfl
  exact ⟨ρ, PMap.empty, τ, τ, τ, ρ, v, μ, μ,
    ResU.hash_symm hf, hτ,
    ResU.hash_symm (ResU.hash_empty_right hvτ),
    hτ, hμ, ResU.comp_empty_right τ, hμ,
    Steps.one (Step1.head (Head.load μ l v hlv)), ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, noOwn_empty, hQ⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_144 := BoCa.Fig16.BoLo.wp_load_I
alias TR.«wp-load-I» := BoCa.Fig16.BoLo.wp_load_I

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.144 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_load_I (l : BoCa.Loc) (α : Life) (P Q : Val → WProp) :
    Entails
      (sep (ptoImm l α P)
        (all fun v =>
          wand (ptoImm l α (fun v' => sep (Fig16.BoLo.pure (v = v')) (P v)))
            (Q v)))
      (wp (.app (.val (.prim .load)) (.val (.loc l))) Q) := by
  rintro ρ ⟨ρ₁, ρR, hcρ, ⟨s, v, σ, hs, rfl, hP, hα⟩, hR⟩ ρf hf
  have hcell : ptoImm l α (fun v' => sep (Fig16.BoLo.pure (v = v')) (P v))
      (ResU.single l (CellU.immOf s v σ hs)) :=
    ⟨s, v, σ, hs, rfl, (Fig16.BoLo.pure_sep_biEntails rfl (P v)).2 σ hP, hα⟩
  have hQ : Q v ρ := hR v _ ρ hcell (ResU.CompS.comm hcρ)
  obtain ⟨τ, μ, hτ, hvτ, hμ⟩ := hash_lower hf
  obtain ⟨χ, hχ, heχ⟩ :=
    Fig16.BoLo.compS_get_erase hcρ (ResU.single_get_self l _)
  obtain ⟨χ', hχ', heχ'⟩ :=
    Fig16.BoLo.compS_get_erase (ResU.CompS.comm hτ) hχ
  have hlv : μ l = some v := by
    rw [Fig16.BoLo.lower_get hμ hχ', heχ', heχ]
    rfl
  exact ⟨ρ, PMap.empty, τ, τ, τ, ρ, v, μ, μ,
    ResU.hash_symm hf, hτ,
    ResU.hash_symm (ResU.hash_empty_right hvτ),
    hτ, hμ, ResU.comp_empty_right τ, hμ,
    Steps.one (Step1.head (Head.load μ l v hlv)), ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, noOwn_empty, hQ⟩

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `[CONF]` Fig. 13b's `wp Load I` (p. 415:15):
`ℓ ↦ I_α P̂ ⋆ (∀v. ℓ ↦ I_α (_. P̂(v)) ─⋆ wp(v){Q̂}) ⊨ wp(load ℓ){Q̂}` (§12.65).
`[variant: `[CONF]` Fig. 13b's printing of `[TR]` 6.144, at the constant family
and at `wp(v){Q̂}` in place of `Q̂(v)`]` -/
theorem wp_load_I_conf (l : BoCa.Loc) (α : Life) (P Q : Val → WProp) :
    Entails
      (sep (ptoImm l α P)
        (all fun v => wand (ptoImm l α (fun _ => P v)) (wp (.val v) Q)))
      (wp (.app (.val (.prim .load)) (.val (.loc l))) Q) := by
  rintro ρ ⟨ρ₁, ρR, hcρ, ⟨s, v, σ, hs, rfl, hP, hα⟩, hR⟩ ρf hf
  have hcell : ptoImm l α (fun _ => P v) (ResU.single l (CellU.immOf s v σ hs)) :=
    ⟨s, v, σ, hs, rfl, hP, hα⟩
  have hwp : wp (.val v) Q ρ := hR v _ ρ hcell (ResU.CompS.comm hcρ)
  obtain ⟨τ, μ, hτ, -, hμ⟩ := hash_lower hf
  obtain ⟨χ, hχ, heχ⟩ := compS_get_erase hcρ (ResU.single_get_self l _)
  obtain ⟨χ', hχ', heχ'⟩ := compS_get_erase (ResU.CompS.comm hτ) hχ
  have hlv : μ l = some v := by
    rw [lower_get hμ hχ', heχ', heχ]
    rfl
  obtain ⟨ρ', ρp, fρ', fρ'p, π, w, μ', h₁, h₂, h₃, h₆, h₇, h₈, h₉, hA, hB, hC⟩ :=
    wp_lower hwp hf hτ hμ
  exact ⟨ρ', ρp, τ, fρ', fρ'p, π, w, μ, μ', h₁, h₂, h₃, hτ, hμ, h₆, h₇,
    .more (Step1.head (Head.load μ l v hlv)) h₈, h₉, hA, hB, hC⟩

/-- 6.144's premise inhabited, at one `imm` cell, with its wand reached.
`[about ours: an inhabitant of the printed premise]` -/
theorem wp_load_I_nonvacuous (b : Life) (w : Val) :
    sep (ptoImm 0 b (fun _ _ => True))
      (all fun v =>
        wand (ptoImm 0 b (fun v' => sep (pure (v = v')) (fun _ => True)))
          (ptoAny 0))
      (ResU.single 0 (CellU.immOf (LSet.singleton b) w PMap.empty
        (stratum_empty _))) := by
  refine ⟨_, PMap.empty, ResU.comp_empty_right _,
    ⟨LSet.singleton b, w, PMap.empty, stratum_empty _, rfl, trivial,
      Nat.le_refl _⟩, ?_⟩
  rintro v ρ₁ ρ₂ ⟨s, v₀, σ, hσ, rfl, -, -⟩ hc
  exact ⟨_, eq_of_compS_empty_left hc⟩

/-!
## Lemma 6.145 (wp-store) · `[TR]` p. 37 · `proved`

> ℓ ↦ v₁ ⋆ (ℓ ↦ v₂ –⋆ Q̂(())) ⊨ wp(store ℓ v₂){Q̂}

**Printed proof, transcribed.** Let `ρ = ρ₁ ● ρ₂` with `ρ₁ = ℓ ↦ own(−)` and `(ℓ ↦ v –⋆ Q̂(()))(ρ₂)` (H1).  H1 at `ℓ ↦ own(v)`, `ρ₂ ● ℓ ↦ own(v)` gives `Q̂(())(ρ₂ ● ℓ ↦ own(v))` (H2).  Let `ρ_f # ρ` (H3) and choose `ρ′, ρ⁺, v` to be `ρ₂ ● ℓ ↦ own(v), ∅, ()`.  `ρ₂ ● ℓ ↦ own(v) # ρ_f` by H3 and Lemma 6.40; `∅ # ρ₂ ● ρ₂ ● ℓ ↦ own(v)` by definition; the run: `ℓ ∈ ⟦ρ_f ● ℓ ↦ own(−) ● ρ₂⟧`, so `(⟦ρ_f ● ℓ ↦ own(−) ● ρ₂⟧, store ℓ v) → (⟦ρ_f ● ℓ ↦ own(−) ● ρ₂⟧[ℓ ↦ v], ())`, and `⟦ρ_f ● ℓ ↦ own(−) ● ρ₂⟧[ℓ ↦ v] = ⟦ρ_f ● ℓ ↦ own(v) ● ρ₂⟧`; `ℓ ↦ own(−) ● ρ₂ ↭ ρ₂ ● ℓ ↦ own(v)` by definition and Lemma 6.47, since `↭` ignores `own`; `∅|own = ∅`; `Q̂(())(ρ₂ ● ℓ ↦ own(v))` by H2.

The printed proof cites Lemma 6.40 for `ρ₂ ● ℓ ↦ own(v) # ρ_f`.  6.40 has no declaration (see its record in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`); the Lean obtains that `#` from `Fig16.BoLo.hash_compS_own`.

**Lean.** `BoCa.Fig16.BoLo.wp_store`, aliases `TR.lemma_6_145`, `TR.«wp-store»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_store`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_store`, in `Support/TypedWorld/Wp.lean`.
-/
/-- `[TR]` Lemma 6.145 (`wp-store`, p. 37).  `[as printed]` -/
theorem wp_store (l : BoCa.Loc) (v₁ v₂ : Val) (Q : Val → WProp) :
    Entails (sep (ptoOwn l v₁) (wand (ptoOwn l v₂) (Q .unit)))
      (wp (.app (.val (.storeV (.loc l))) (.val v₂)) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, rfl, hwand⟩ ρf hf
  obtain ⟨σ, μ, hσ, hvσ, hμ⟩ := hash_lower hf
  have h₂ : ResU.Hash ρf ρ₂ :=
    ResU.hash_symm (ResU.Hash.split hcρ (ResU.hash_symm hf)).2
  obtain ⟨σ₂, hσ₂, hσ₂σ⟩ :=
    (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v₁)) σ).mp
      ⟨ρ, ResU.CompS.comm hcρ, hσ⟩
  obtain ⟨hlv, μ₂, hlow₂, hupd, hnone⟩ := lower_compS_own_inv hσ₂σ hμ
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ₂ (ResU.single l (CellU.ownOf v₂))).mpr
    (compatS_single_of_get_none (ResU.compatS_single_own hcρ.1))
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ₂ hlow₂ hnone hx
  have hstep : BoCa.BoLo.Heap.upd μ l v₂ = BoCa.BoLo.Heap.upd μ₂ l v₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.upd_same, BoCa.BoLo.Heap.upd_same]
    · rw [BoCa.BoLo.Heap.upd_other e, BoCa.BoLo.Heap.upd_other e, hupd,
        BoCa.BoLo.Heap.upd_other e]
  refine ⟨x, PMap.empty, σ, σ', σ', x, .unit, μ, BoCa.BoLo.Heap.upd μ₂ l v₂,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    hσ, hμ, ResU.comp_empty_right σ', hlow', ?_, ResU.comp_empty_right x, ?_,
    noOwn_empty, hwand _ x rfl hx⟩
  · rw [← hstep]
    exact Steps.one (Step1.head (Head.store μ l v₂ v₁ hlv))
  · exact ResU.UpdV.trans
      (updV_compS_own (ResU.CompS.comm hcρ) (hash_valid h₂).2 (hash_valid hf).2).symm
      (updV_compS_own hx (hash_valid h₂).2 (hash_valid hfx).2)

end BoCa.Fig16.BoLo

alias TR.lemma_6_145 := BoCa.Fig16.BoLo.wp_store
alias TR.«wp-store» := BoCa.Fig16.BoLo.wp_store

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.145 over `[TR]` §3's printed machine, at `store ℓ v₂` spelled `(store ℓ) v₂`, the same term.
`[as printed]` -/
theorem wp_store (l : BoCa.Loc) (v₁ v₂ : Val) (Q : Val → WProp) :
    Entails (sep (ptoOwn l v₁) (wand (ptoOwn l v₂) (Q .unit)))
      (wp (.app (.app (.val (.prim .store)) (.val (.loc l))) (.val v₂)) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, rfl, hwand⟩ ρf hf
  obtain ⟨σ, μ, hσ, hvσ, hμ⟩ := hash_lower hf
  have h₂ : ResU.Hash ρf ρ₂ :=
    ResU.hash_symm (ResU.Hash.split hcρ (ResU.hash_symm hf)).2
  obtain ⟨σ₂, hσ₂, hσ₂σ⟩ :=
    (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v₁)) σ).mp
      ⟨ρ, ResU.CompS.comm hcρ, hσ⟩
  obtain ⟨hlv, μ₂, hlow₂, hupd, hnone⟩ := lower_compS_own_inv hσ₂σ hμ
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ₂ (ResU.single l (CellU.ownOf v₂))).mpr
    (compatS_single_of_get_none (ResU.compatS_single_own hcρ.1))
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ₂ hlow₂ hnone hx
  have hstep : BoCa.BoLo.Heap.upd μ l v₂ = BoCa.BoLo.Heap.upd μ₂ l v₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.upd_same, BoCa.BoLo.Heap.upd_same]
    · rw [BoCa.BoLo.Heap.upd_other e, BoCa.BoLo.Heap.upd_other e, hupd,
        BoCa.BoLo.Heap.upd_other e]
  refine ⟨x, PMap.empty, σ, σ', σ', x, .unit, μ, BoCa.BoLo.Heap.upd μ₂ l v₂,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    hσ, hμ, ResU.comp_empty_right σ', hlow', ?_, ResU.comp_empty_right x, ?_,
    noOwn_empty, hwand _ x rfl hx⟩
  · rw [← hstep]
    exact Steps.one (steps_store μ l v₂ v₁ hlv)
  · exact ResU.UpdV.trans
      (updV_compS_own (ResU.CompS.comm hcρ) (hash_valid h₂).2
        (hash_valid hf).2).symm
      (updV_compS_own hx (hash_valid h₂).2
        (hash_valid hfx).2)

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.146 (wp-ramify) · `[TR]` p. 38 · `proved`

> wp(e){P̂} ⋆ (P̂ –⋆ Q̂) ⊨ wp(e){Q̂}

**Printed proof, transcribed.** Let `ρ = ρ₁ ● ρ₂` with `wp(e){P̂}(ρ₁)` (H1) and `(∀(P̂ –⋆ Q̂))(ρ₂)` (H2), and `ρ_f # ρ` (H3).  Instantiate H1 at `ρ_f ● ρ₂`, which is `# ρ₁` by H3 and Lemma 6.46: `(⟦ρ_f ● ρ₂ ● ρ₁⟧, e) →* (⟦ρ_f ● ρ₂ ● ρ′ ● ρ⁺⟧, v)` (H4), `ρ₁ ↭ ρ′ ● ρ⁺` (H5), `ρ⁺|own = ∅` (H6), `P̂(v)(ρ′)` (H7), for `ρ′ # ρ_f ● ρ₂` (H8), `ρ⁺ # ρ_f ● ρ₂ ● ρ′` (H9), `v`.  H2 at `v, ρ′, ρ₂ ● ρ′` gives `Q̂(v)(ρ₂ ● ρ′)` (H10).  Choose `ρ₂ ● ρ′, ρ⁺, v`; most obligations are immediate and the others follow from Lemma 6.46 or Lemma 6.48.

**Lean.** `BoCa.Fig16.BoLo.wp_ramify`, aliases `TR.lemma_6_146`, `TR.«wp-ramify»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_ramify`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_ramify`, in `Support/TypedWorld/Wp.lean`.

**Note.** The printed `(P̂ –⋆ Q̂)` is `Fig16.BoLo.wandAll`, `∀v. P̂(v) ─⋆ Q̂(v)`, as H2 of the printed proof reads it.
-/
/-- `[TR]` Lemma 6.146 (`wp-ramify`, p. 38).  `[as printed]` (the printed `(P̂ –⋆ Q̂)`
read as `wandAll`) -/
theorem wp_ramify (e : Expr) (P Q : Val → WProp) :
    Entails (sep (wp e P) (wandAll P Q)) (wp e Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, hwp, hwand⟩ ρf hf
  -- `ρ_f ● ρ₂ # ρ₁`, by `[TR]` 6.46
  obtain ⟨y, hy, hy₁⟩ := (hash_shift ρf ρ₂ ρ₁).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
  obtain ⟨ρ', ρp, Y₁, Y', Y'p, π', v, μ, μ', g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉,
    gA, gB, gC⟩ := hwp y hy₁
  -- `W` is the printed `ρ₂ ● ρ′`: `(ρ_f ● ρ₂) ● ρ′ = ρ_f ● (ρ₂ ● ρ′)`
  obtain ⟨W, hW, hfW⟩ := compS_reassoc hy g₂
  -- …and `(ρ_f ● ρ₂) ● ρ₁ = ρ_f ● ρ`, so the run starts from `⟦ρ_f ● ρ⟧`
  obtain ⟨r, hr, hfr⟩ := compS_reassoc hy g₄
  have hfρ : ResU.CompS ρf ρ Y₁ := by
    rwa [ResU.CompS.functional hcρ (ResU.CompS.comm hr)]
  -- `ρ₂ ● ρ′ # ρ_f`, again by 6.46
  obtain ⟨W₀, hW₀, hWf₀⟩ := (hash_shift ρ' ρ₂ ρf).mp ⟨y, ResU.CompS.comm hy, g₁⟩
  have hWf : ResU.Hash W ρf := by
    rwa [ResU.CompS.functional (ResU.CompS.comm hW₀) hW] at hWf₀
  -- `ρ₂ # ρ′ ● ρ⁺`, by 6.11 and 6.46
  obtain ⟨-, hWp⟩ := ResU.Hash.split hfW (ResU.hash_symm g₃)
  obtain ⟨πW, hπW, h₂π₀⟩ := (hash_shift ρ₂ ρ' ρp).mpr ⟨W, hW, hWp⟩
  have h₂π : ResU.Hash ρ₂ π' := by rwa [ResU.CompS.functional hπW g₉] at h₂π₀
  obtain ⟨πn, hπn, -⟩ := h₂π.2
  obtain ⟨Wn, hWn, hWπ₀⟩ := compS_reassoc' g₉ hπn
  have hWπ : ResU.CompS W ρp πn := by
    rwa [ResU.CompS.functional hWn hW] at hWπ₀
  refine ⟨W, ρp, Y₁, Y', Y'p, πn, v, μ, μ', hWf, hfW, g₃, hfρ, g₅, g₆, g₇, g₈,
    hWπ, ?_, gB, hwand v ρ' W gC hW⟩
  exact updV_frame (ResU.CompS.comm hcρ) hπn
    ⟨(ResU.CompS.comm hcρ).1, ρ, ResU.CompS.comm hcρ, (hash_valid hf).2⟩ h₂π gA

end BoCa.Fig16.BoLo

alias TR.lemma_6_146 := BoCa.Fig16.BoLo.wp_ramify
alias TR.«wp-ramify» := BoCa.Fig16.BoLo.wp_ramify

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.146 over `[TR]` §3's printed machine.  `[as printed]` (the printed `(P̂ –⋆ Q̂)`
read as `wandAll`) -/
theorem wp_ramify (e : Expr) (P Q : Val → WProp) :
    Entails (sep (wp e P) (wandAll P Q)) (wp e Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, hwp, hwand⟩ ρf hf
  obtain ⟨y, hy, hy₁⟩ :=
    (hash_shift ρf ρ₂ ρ₁).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
  obtain ⟨ρ', ρp, Y₁, Y', Y'p, π', v, μ, μ', g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉,
    gA, gB, gC⟩ := hwp y hy₁
  obtain ⟨W, hW, hfW⟩ := compS_reassoc hy g₂
  obtain ⟨r, hr, hfr⟩ := compS_reassoc hy g₄
  have hfρ : ResU.CompS ρf ρ Y₁ := by
    rwa [ResU.CompS.functional hcρ (ResU.CompS.comm hr)]
  obtain ⟨W₀, hW₀, hWf₀⟩ :=
    (hash_shift ρ' ρ₂ ρf).mp ⟨y, ResU.CompS.comm hy, g₁⟩
  have hWf : ResU.Hash W ρf := by
    rwa [ResU.CompS.functional (ResU.CompS.comm hW₀) hW] at hWf₀
  obtain ⟨-, hWp⟩ := ResU.Hash.split hfW (ResU.hash_symm g₃)
  obtain ⟨πW, hπW, h₂π₀⟩ := (hash_shift ρ₂ ρ' ρp).mpr ⟨W, hW, hWp⟩
  have h₂π : ResU.Hash ρ₂ π' := by rwa [ResU.CompS.functional hπW g₉] at h₂π₀
  obtain ⟨πn, hπn, -⟩ := h₂π.2
  obtain ⟨Wn, hWn, hWπ₀⟩ := compS_reassoc' g₉ hπn
  have hWπ : ResU.CompS W ρp πn := by
    rwa [ResU.CompS.functional hWn hW] at hWπ₀
  refine ⟨W, ρp, Y₁, Y', Y'p, πn, v, μ, μ', hWf, hfW, g₃, hfρ, g₅, g₆, g₇, g₈,
    hWπ, ?_, gB, hwand v ρ' W gC hW⟩
  exact updV_frame (ResU.CompS.comm hcρ) hπn
    ⟨(ResU.CompS.comm hcρ).1, ρ, ResU.CompS.comm hcρ,
      (hash_valid hf).2⟩ h₂π gA

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.147 (wp[]) · `[TR]` p. 38 · `proved`

> [α]wp(e){Q̂} ⊨ wp(e){[α]Q̂}

**Printed proof, transcribed.** Let `wp(e){Q̂}(ρ)` (H1), `@ρ ⊐ α` (H2) and `ρ_f # ρ` (H3).  H1 at `ρ_f` gives the run (H4), `ρ ↭ ρ′ ● ρ⁺` (H5), `ρ⁺|own = ∅` (H6), `Q̂(v)(ρ′)` (H7), `ρ′ # ρ_f` (H8), `ρ⁺ # ρ_f ● ρ′` (H9).  Choose `ρ′, ρ⁺, v`; all obligations are immediate except `@ρ′ ⊐ α`.  Lemma 6.50 with H2 and H5 gives `@(ρ′ ● ρ⁺) ⊐ α`, and Lemma 6.45 gives `@ρ′ ⊐ α`.

**Lean.** `BoCa.Fig16.BoLo.wp_box`, aliases `TR.lemma_6_147`, `TR.«wp[]»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_box`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_box`, in `Support/TypedWorld/Wp.lean`.
-/
/-- `[TR]` Lemma 6.147 (`wp[]`, p. 38).  `[as printed]` -/
theorem wp_box (α : Life) (e : Expr) (Q : Val → WProp) :
    Entails (box α (wp e Q)) (wp e fun v => box α (Q v)) := by
  rintro ρ ⟨hw, hout⟩ ρf hf
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC⟩ := hw ρf hf
  exact ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC, ((outlives_comp h₉ α).mp (updV_outlives hout hA)).1⟩

end BoCa.Fig16.BoLo

alias TR.lemma_6_147 := BoCa.Fig16.BoLo.wp_box
alias TR.«wp[]» := BoCa.Fig16.BoLo.wp_box

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.147 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_box (α : Life) (e : Expr) (Q : Val → WProp) :
    Entails (box α (wp e Q)) (wp e fun v => box α (Q v)) := by
  rintro ρ ⟨hw, hout⟩ ρf hf
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC⟩ := hw ρf hf
  exact ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC, ((outlives_comp h₉ α).mp (updV_outlives hout hA)).1⟩

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- A frame with no owned cell passes through a run.
`[about ours: the argument `[TR]` 6.148 and 6.149 share]` -/
theorem wp_frame_noOwn {R : WProp} (hR : ∀ ρ, R ρ → NoOwn ρ) (e : Expr)
    (Q : Val → WProp) : Entails (sep R (wp e Q)) (wp e Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, hR₁, hwp⟩ ρf hf
  -- `ρ_f ● ρ₁ # ρ₂`, by `[TR]` 6.46
  obtain ⟨y, hy, hy₂⟩ := (hash_shift ρf ρ₁ ρ₂).mp ⟨ρ, hcρ, hf⟩
  obtain ⟨ρ'', ρp, Y₂, Y'', Y''p, π', v', μ, μ', g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉,
    gA, gB, gC⟩ := hwp y hy₂
  -- `[TR]` 6.11 at `ρ_f ● ρ₁ # ρ″`
  obtain ⟨hfρ'', -⟩ := ResU.Hash.split hy (ResU.hash_symm g₁)
  obtain ⟨F, hF, hFv⟩ := hfρ''.2
  -- `⟦ρ_f ● ρ⟧` is the memory the inner run starts from
  obtain ⟨bc, hbc, hfρ⟩ := compS_reassoc hy g₄
  cases ResU.CompS.functional hbc hcρ
  -- `ρ_f ● ρ₁ ● ρ″ = (ρ_f ● ρ″) ● ρ₁`
  obtain ⟨F', hF', hFρ₁⟩ := compS_exch hy g₂
  cases ResU.CompS.functional hF' hF
  -- `ρ⁺ ● ρ₁ # ρ_f ● ρ″`, by `[TR]` 6.46
  obtain ⟨Z, hZ, hZF⟩ :=
    (hash_shift ρp ρ₁ F).mp ⟨Y'', ResU.CompS.comm hFρ₁, g₃⟩
  -- …and the final memory is `⟦(ρ_f ● ρ″) ● (ρ⁺ ● ρ₁)⟧`
  obtain ⟨Z', hZ', hFZ⟩ := compS_reassoc hFρ₁ g₆
  cases ResU.CompS.functional (ResU.CompS.comm hZ') hZ
  -- `ρ₁ # ρ″ ● ρ⁺`, again by 6.11 and 6.46
  obtain ⟨d, hd, hfd⟩ := compS_reassoc hy g₂
  obtain ⟨-, hdp⟩ := ResU.Hash.split hfd (ResU.hash_symm g₃)
  obtain ⟨π'', hπ'', h₁π⟩ := (hash_shift ρ₁ ρ'' ρp).mpr ⟨d, hd, hdp⟩
  cases ResU.CompS.functional hπ'' g₉
  obtain ⟨πn, hπn, -⟩ := h₁π.2
  -- `ρ₁ ● (ρ″ ● ρ⁺) = ρ″ ● (ρ⁺ ● ρ₁)`
  obtain ⟨ac, hac, hπZ⟩ := compS_lcomm g₉ hπn
  cases ResU.CompS.functional (ResU.CompS.comm hac) hZ
  refine ⟨ρ'', Z, Y₂, F, Y''p, πn, v', μ, μ', ResU.hash_symm hfρ'', hF, hZF,
    hfρ, g₅, hFZ, g₇, g₈, hπZ, ?_, noOwn_compS hZ gB (hR ρ₁ hR₁), gC⟩
  exact updV_frame hcρ hπn ⟨hcρ.1, ρ, hcρ, (hash_valid hf).2⟩ h₁π gA

/-!
## Lemma 6.148 (wp-M-forget) · `[TR]` p. 38 · `proved`

> ℓ ↦M_α P̂ ⋆ wp(e){Q̂} ⊨ wp(e){Q̂}

**Printed proof, transcribed.** Let `ρ = ρ₁ ● ρ₂` with `ρ₁ = ℓ ↦ mut(β, v, ρ′, P̂)` and `wp(e){Q̂}(ρ₂)` (H1), and `ρ_f # ρ` (H2).  Instantiate H1 at `ρ_f ● ρ₁`, which is `# ρ₂` by H2 and Lemma 6.46: the run (H3), `ρ₂ ↭ ρ′ ● ρ⁺` (H4), `ρ⁺|own = ∅` (H5), `Q̂(v)(ρ′)` (H6), `ρ′ # ρ_f ● ρ₁` (H7), `ρ⁺ # ρ_f ● ρ₁ ● ρ′` (H8).  Choose `ρ′, ρ⁺ ● ρ₁, v`.  `ρ′ # ρ_f` by H7 and Lemma 6.11; `ρ⁺ ● ρ₁ # ρ_f ● ρ′` (H9) by H8 and Lemma 6.46; `(ρ⁺ ● ρ₁)|own = ∅` by H5 and since `ρ₁` contains only a borrow; `ρ₁ ● ρ₂ ↭ ρ′ ● ρ⁺ ● ρ₁` by H4, H9 and Lemma 6.48.

**Lean.** `BoCa.Fig16.BoLo.wp_M_forget`, aliases `TR.lemma_6_148`, `TR.«wp-M-forget»`, tag `[as printed]`.

**Also here.** `BoCa.Fig16.BoLo.wp_frame_noOwn`; `BoCa.TR3.wp_frame_noOwn`; `BoCa.TR3.wp_M_forget`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_frame_noOwn`, in `Support/TypedWorld/Wp.lean`; `BoCa.Fig16.LogRel.Typed.wpTS_M_forget`, in `Support/TypedWorld/Wp.lean`.
-/
/-- `[TR]` Lemma 6.148 (`wp-M-forget`, p. 38).  `[as printed]` -/
theorem wp_M_forget (l : BoCa.Loc) (α : Life) (P : Val → WProp) (e : Expr)
    (Q : Val → WProp) : Entails (sep (ptoMut l α P) (wp e Q)) (wp e Q) := by
  refine wp_frame_noOwn (fun ρ h => ?_) e Q
  obtain ⟨b, v, σ, hs, R, hw, hα, rfl, -⟩ := h
  exact ResU.restrict_single_other (by simp)

end BoCa.Fig16.BoLo

alias TR.lemma_6_148 := BoCa.Fig16.BoLo.wp_M_forget
alias TR.«wp-M-forget» := BoCa.Fig16.BoLo.wp_M_forget

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- A frame with no owned cell passes through a printed run.
`[about ours: the argument `[TR]` 6.148 and 6.149 share]` -/
theorem wp_frame_noOwn {R : WProp} (hR : ∀ ρ, R ρ → NoOwn ρ)
    (e : Expr) (Q : Val → WProp) : Entails (sep R (wp e Q)) (wp e Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, hR₁, hwp⟩ ρf hf
  obtain ⟨y, hy, hy₂⟩ := (hash_shift ρf ρ₁ ρ₂).mp ⟨ρ, hcρ, hf⟩
  obtain ⟨ρ'', ρp, Y₂, Y'', Y''p, π', v', μ, μ', g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉,
    gA, gB, gC⟩ := hwp y hy₂
  obtain ⟨hfρ'', -⟩ := ResU.Hash.split hy (ResU.hash_symm g₁)
  obtain ⟨F, hF, hFv⟩ := hfρ''.2
  obtain ⟨bc, hbc, hfρ⟩ := compS_reassoc hy g₄
  cases ResU.CompS.functional hbc hcρ
  obtain ⟨F', hF', hFρ₁⟩ := compS_exch hy g₂
  cases ResU.CompS.functional hF' hF
  obtain ⟨Z, hZ, hZF⟩ :=
    (hash_shift ρp ρ₁ F).mp ⟨Y'', ResU.CompS.comm hFρ₁, g₃⟩
  obtain ⟨Z', hZ', hFZ⟩ := compS_reassoc hFρ₁ g₆
  cases ResU.CompS.functional (ResU.CompS.comm hZ') hZ
  obtain ⟨d, hd, hfd⟩ := compS_reassoc hy g₂
  obtain ⟨-, hdp⟩ := ResU.Hash.split hfd (ResU.hash_symm g₃)
  obtain ⟨π'', hπ'', h₁π⟩ := (hash_shift ρ₁ ρ'' ρp).mpr ⟨d, hd, hdp⟩
  cases ResU.CompS.functional hπ'' g₉
  obtain ⟨πn, hπn, -⟩ := h₁π.2
  obtain ⟨ac, hac, hπZ⟩ := compS_lcomm g₉ hπn
  cases ResU.CompS.functional (ResU.CompS.comm hac) hZ
  refine ⟨ρ'', Z, Y₂, F, Y''p, πn, v', μ, μ', ResU.hash_symm hfρ'', hF, hZF,
    hfρ, g₅, hFZ, g₇, g₈, hπZ, ?_,
    noOwn_compS hZ gB (hR ρ₁ hR₁), gC⟩
  exact updV_frame hcρ hπn
    ⟨hcρ.1, ρ, hcρ, (hash_valid hf).2⟩ h₁π gA

/-- `[TR]` Lemma 6.148 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_M_forget (l : BoCa.Loc) (α : Life) (P : Val → WProp) (e : Expr)
    (Q : Val → WProp) : Entails (sep (ptoMut l α P) (wp e Q)) (wp e Q) := by
  refine wp_frame_noOwn (fun ρ h => ?_) e Q
  obtain ⟨b, v, σ, hs, R, hw, hα, rfl, -⟩ := h
  exact ResU.restrict_single_other (by simp)

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
## Lemma 6.149 (wp-I-forget) · `[TR]` p. 38 · `proved`

> ℓ ↦I_α P̂ ⋆ wp(e){Q̂} ⊨ wp(e){Q̂}

**Printed proof, transcribed.** Proceeds almost identically to the proof of Lemma 6.148.  The reasoning depends only on the resource being a borrow, not on it being a mutable borrow.

**Lean.** `BoCa.Fig16.BoLo.wp_I_forget`, aliases `TR.lemma_6_149`, `TR.«wp-I-forget»`, tag `[as printed]`.

**Also here.** `BoCa.TR3.wp_I_forget`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_I_forget`, in `Support/TypedWorld/Wp.lean`.
-/
/-- `[TR]` Lemma 6.149 (`wp-I-forget`, p. 38).  `[as printed]` -/
theorem wp_I_forget (l : BoCa.Loc) (α : Life) (P : Val → WProp) (e : Expr)
    (Q : Val → WProp) : Entails (sep (ptoImm l α P) (wp e Q)) (wp e Q) := by
  refine wp_frame_noOwn (fun ρ h => ?_) e Q
  obtain ⟨s, v, σ, hs, rfl, -, -⟩ := h
  exact ResU.restrict_single_other (by simp)

end BoCa.Fig16.BoLo

alias TR.lemma_6_149 := BoCa.Fig16.BoLo.wp_I_forget
alias TR.«wp-I-forget» := BoCa.Fig16.BoLo.wp_I_forget

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-- `[TR]` Lemma 6.149 over `[TR]` §3's printed machine.  `[as printed]` -/
theorem wp_I_forget (l : BoCa.Loc) (α : Life) (P : Val → WProp) (e : Expr)
    (Q : Val → WProp) : Entails (sep (ptoImm l α P) (wp e Q)) (wp e Q) := by
  refine wp_frame_noOwn (fun ρ h => ?_) e Q
  obtain ⟨s, v, σ, hs, rfl, -, -⟩ := h
  exact ResU.restrict_single_other (by simp)

end BoCa.TR3

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps)

/-!
## Theorem 6.150 (↺ rule) · `[TR]` p. 39 · `proved*`

> ℓ ↦ Imm α (Иβ. ↺_β P̂) ⋆ (Иβ. ∀v. P̂(v) –⋆ wp(e){[β]Q̂}) ⊨ wp(e){Q̂}

**Printed proof, transcribed.** Let `ρ` satisfy the left side (H1); unfold `wp` at `ρ_f # ρ` (H2); the goals are `ρ′ # ρ_f` (G2), `ρ⁺ # ρ′ ● ρ_f` (G3), the run (G4), `ρ ↭ ρ′ ● ρ⁺` (G5), `ρ⁺|own = ∅` (G6), `ρ′ ∈ Q̂(v)` (G7).  Unfolding `⋆`, `ρ = ρᵢ ● ρ_b` (H3) with `ρᵢ ∈ ℓ ↦ Imm α (Иβ. ↺_β P̂)` (H4) and `ρ_b ∈ Иβ. ∀v. P̂(v) –⋆ wp(e){[β]Q̂}` (H5).  Unfolding `Imm`, `ρᵢ = ℓ ↦ imm(ᾱ, v′, ρ′)` (H6), `ρ′ ∈ (Иβ. ↺_β P̂)(v′)` (H7), `α ⊑ ᾱ` (H8).  Unfolding `И` in H7 gives `γᵢ` with `ρ′ ∈ ∀β ⊏ γᵢ. [β](↺_β P̂)(v′)` (H9); in H5, `γ_b` with `ρ_b ∈ ∀β ⊏ γ_b. [β](∀v. …)` (H10).  Let `β ⊏ γᵢ ⊓ γ_b` (H11) — *"such a `β` always exists"*.  Specialising and unfolding `[β]`: `ρ′ ∈ ↺_β P̂(v′)` (H12), `@ρ′ ⊐ β` (H13), `ρ_b ∈ P̂(v′) –⋆ wp(e){[β]Q̂}` (H14), `@ρ_b ⊐ β` (H15).  Unfolding `↺_β` in H12, `ρ_P̂(v′) ∈ reb_β(ρ′)` (H16) and `ρ_P̂(v′) ∈ P̂(v′)` (H17).  By Lemma 6.10 with H2, `✓ρ`, so `ρᵢ # ρ_b` (H18); by Lemma 6.55 with H16, `ρ_P̂(v′) # ρ_b` (H19), and similarly `ρ_P̂(v′) # ρ_b ● ρ_f`; by 6.55, `ρᵢ # ρ_P̂(v′)`; by Lemma 6.15 with H2, `ρ_P̂(v′) # ρᵢ ● ρ_b ● ρ_f` (H20).  By `–⋆`, `ρ_P̂(v′) ● ρ_b ∈ wp(e){[β]Q̂}` (H21); unfolding at the frame `ρᵢ ● ρ_f` with H20 gives `ρ_Q # ρᵢ ● ρ_f` (H22), `ρ⁺ # ρ_Q ● ρᵢ ● ρ_f` (H23), `v`, the run from `⟦ρᵢ ● ρ_f ● ρ_P̂(v′) ● ρ_b⟧` to `⟦ρᵢ ● ρ_f ● ρ_Q ● ρ⁺⟧` (H24), `ρ_P̂(v′) ● ρ_b ↭ ρ_Q ● ρ⁺` (H25), `ρ⁺|own = ∅` (H26), `ρ_Q ∈ [β]Q̂(v)` (H27), i.e. `ρ_Q ∈ Q̂(v)` (H28) and `@ρ_Q ⊐ β` (H29).  Let `ρ⁺′ = ρ⁺ ⊟ ρ_P̂(v′)|dom(ρ′|mut,own)`.  Rewriting H24 with Lemma 6.58 applied to H16, H25, H15, H29, H18 and H23 with Lemma 6.11 gives `(⟦ρ_f ● ρᵢ ● ρ_b⟧, e) ⇓ (⟦ρ_f ● ρ_Q ● ρᵢ ● ρ⁺′⟧, v)` (H30).  By Lemma 6.11 with H23, `ρ_Q # ρ_f` (H31) and `ρᵢ ● ρ⁺′ # ρ_Q ● ρ_f` (H32).  By Lemma 6.59 applied to H16, H25, H15, H29, H18 and H23, `ρᵢ ● ρ_b ↭ ρ_Q ● ρᵢ ● ρ⁺′` (H33).  At `ρ′ ≔ ρ_Q`, `ρ⁺ ≔ ρᵢ ● ρ⁺′`: G2 by H31, G3 by H32, G4 by H30, G5 by H33, G6 by H26, G7 by H28.

**Lean.** `BoCa.Fig16.BoLo.wp_reborrow`, aliases `TR.lemma_6_150`, `TR.«↺ rule»`, tag `[restricted: to `RebEscrow P̂`]`.

**Also here.** `BoCa.Fig16.BoLo.rebEscrow_emp`; `BoCa.Fig16.BoLo.wp_reborrow_nonvacuous`; `BoCa.Fig16.BoLo.wp_reborrow_emp_applies`; `BoCa.Fig16.BoLo.rebEscrow_of_no_own`.

**Typed-world version.** `BoCa.Fig16.LogRel.Typed.wpTS_reborrow`, in `Support/TypedWorld/Reborrow.lean`.

**Literal reading.** `BoCa.DeepReborrow.wp_reborrow_unreconciled_at_split_view`, in `Paper/LiteralReadings/S6_7_WeakestPreconditionRules.lean`; `BoCa.Fig16.BoLo.deepReborrow_not_rebEscrow`, in `Paper/LiteralReadings/S6_7_WeakestPreconditionRules.lean`.

**Note.** `P̂` is indexed by the `β` of the `Иβ` it stands under, as [TR] 6.175 instantiates the rule (p. 48). `[restricted: to `Fig16.BoLo.RebEscrow P̂` — the two inputs 6.55 adds (`Fig16.EscrowAgree ρ′ ρ (ag ρ_f)` and `ag(ρ)` defined), at the reborrows `↺_β P̂` names]` (`docs/adjudications.md` §12.61). `rebEscrow_of_no_own` gives the hypothesis's scope; `rebEscrow_emp` and `wp_reborrow_nonvacuous` its non-vacuity.
-/
/-- `[TR]` Theorem 6.150 (`↺` rule, p. 39).  `P̂` is indexed by the `β` of its `Иβ` (§12.61).
`[restricted: to `RebEscrow P̂` — the two inputs `[TR]` 6.55 adds
(`Fig16.EscrowAgree ρ′ ρ (ag ρ_f)` and `ag(ρ)` defined), at the reborrows `↺_β P̂` names]` -/
theorem wp_reborrow (l : BoCa.Loc) (α : Life) (P : Life → BoCa.Val → WProp)
    (e : Expr) (Q : BoCa.Val → WProp) (hesc : RebEscrow P) :
    Entails
      (ptoImm l α (fun v => fresh fun b => reborrow b (P b v)) ⋆
        (fresh fun b => all fun v => P b v ─⋆ wp e (fun v' => box b (Q v'))))
      (wp e Q) := by
  rintro ρ ⟨ρi, ρb, hc, hpi, hpb⟩ ρf hf
  -- H4 unfolded: `ρᵢ = ℓ ↦ imm(ᾱ, v′, ρ′)`, H7 and H8.
  obtain ⟨s, v', σ, hs, hρi, hP7, hα⟩ := hpi
  subst hρi
  -- H9 and H10 — the two `И` bounds.
  obtain ⟨gi, hP9⟩ := hP7
  obtain ⟨gb, hP10⟩ := hpb
  -- H11.
  obtain ⟨β, hβi, hβb⟩ := exists_shorter gi gb
  obtain ⟨⟨χ, hreb, hPχ⟩, h13⟩ := hP9 β hβi
  obtain ⟨hwand0, h15⟩ := hP10 β hβb
  have hwand := hwand0 v'
  -- H18: by 6.10 with H2, `✓ρ`, and therefore `ρᵢ # ρ_b`.
  have hvρ : ResU.Valid ρ := (hash_valid hf).2
  have h18 : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) ρb := ⟨hc.1, ρ, hc, hvρ⟩
  have hbi : ResU.Hash ρb (ResU.single l (CellU.immOf s v' σ hs)) := ResU.hash_symm h18
  -- the two inputs 6.55 adds, at this reborrow
  obtain ⟨⟨A, hagχ⟩, hEA⟩ := hesc β v' σ χ hreb hPχ
  -- H19: by 6.55 with H16.
  have h19 : ResU.Hash ρb χ := ResU.six55 hreb (fun a ha => hEA ρb a ha) hagχ hbi
  obtain ⟨ρbχ, hbχ⟩ := (ResU.compS_defined_iff ρb χ).mpr h19.1
  -- *"By similar reasoning, we have `ρ_P̂(v′) # ρ_b ● ρ_f`."*
  obtain ⟨ρbf, hbf, hbfi⟩ :=
    (hash_shift ρf ρb (ResU.single l (CellU.immOf s v' σ hs))).mp ⟨ρ, ResU.CompS.comm hc, hf⟩
  have h19' : ResU.Hash ρbf χ := ResU.six55 hreb (fun a ha => hEA ρbf a ha) hagχ hbfi
  -- *"By lemma 6.55, `ρᵢ # ρ_P̂(v)`."*
  have hvi : ResU.Valid (ResU.single l (CellU.immOf s v' σ hs)) := (hash_valid hbi).2
  have h55self : ResU.Hash χ (ResU.single l (CellU.immOf s v' σ hs)) :=
    ResU.six55_self hreb (fun a ha => hEA _ a ha) hagχ (ResU.hash_self_single_imm hvi)
  -- H20: *"therefore by lemma 6.15 with H2, `ρ_P̂(v′) # ρᵢ ● ρ_b ● ρ_f`."*
  have hiρbf : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) ρbf := ResU.hash_symm hbfi
  obtain ⟨W, hW⟩ :=
    (ResU.compS_defined_iff (ResU.single l (CellU.immOf s v' σ hs)) ρbf).mpr hiρbf.1
  have h20 : ResU.Hash χ W := ResU.hash_of_pairwise h55self hiρbf (ResU.hash_symm h19') hW
  -- *"setting `ρ_f = ρᵢ ● ρ_f`, with the compatibility constraint from H20"*
  obtain ⟨ρF, hF, hFb⟩ := compS_reassoc' hbf hW
  have hFbχ : ResU.Hash ρF ρbχ := by
    obtain ⟨x, hx, hxh⟩ := (hash_shift ρF ρb χ).mpr ⟨W, hFb, ResU.hash_symm h20⟩
    rwa [ResU.CompS.functional hx hbχ] at hxh
  -- H21: by the definition of `─⋆`.
  have h21 : wp e (fun v'' => box β (Q v'')) ρbχ := hwand χ ρbχ hPχ hbχ
  obtain ⟨ρQ, ρp, fρ, fρ', fρ'p, π, v, μ, μ', g1, g2, g3, g4, g5, g6, g7, g8, g9, gA, gB, gC⟩ :=
    h21 ρF hFbχ
  -- H28 and H29, by unfolding `[β]` in H27.
  obtain ⟨h28, h29⟩ := gC
  -- *"Let `ρ⁺′ = ρ⁺ ⊟ ρ_P̂(v′)|dom(ρ′|mut,own)`"* — `[TR]` 6.52 at that `⊟`.
  obtain ⟨ψ, hsubK, hsplit, hψβ⟩ :=
    ResU.six52_keep hreb (ResU.CompS.comm hbχ) g9 gA h15 h29
  -- 6.11 at the `#`s the inner `wp` produced.
  obtain ⟨hiQ, hfQ⟩ := ResU.Hash.split hF (ResU.hash_symm g1)
  obtain ⟨hFp, hQp⟩ := ResU.Hash.split g2 (ResU.hash_symm g3)
  obtain ⟨hip, hfp⟩ := ResU.Hash.split hF hFp
  obtain ⟨hψQ, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm hQp)
  obtain ⟨hψi, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm hip)
  have hvfp : ResU.Valid fρ'p := by obtain ⟨τ, hτ, -⟩ := g7; exact ⟨τ, hτ⟩
  -- The source memory: `⟦ρᵢ ● ρ_f ● ρ_P̂(v′) ● ρ_b⟧` regrouped as 6.58's `ρ ● ρ_b ● ρᵢ`.
  obtain ⟨t1, ht1, ht1'⟩ := compS_reassoc hF g4
  obtain ⟨u1, hu1, hu1'⟩ := compS_reassoc' hbχ ht1
  rw [ResU.CompS.functional hu1 hbf] at hu1'
  obtain ⟨Y58, hY58⟩ :=
    (ResU.compS_defined_iff ρbf (ResU.single l (CellU.immOf s v' σ hs))).mpr hbfi.1
  -- *"By rewriting in H24 with lemma 6.58"* — the first conclusion.
  have h58L := ResU.six58_left hreb (fun a ha => hEA _ a ha) hagχ (ResU.hash_symm h19')
    hbfi (ResU.CompS.comm hu1') (ResU.CompS.comm ht1') hY58
  have hLY : ResU.Lower Y58 μ := (h58L μ).mp g5
  -- `ρ_b ● ρ_f ● ρᵢ = ρ_f ● ρ`, which is the source H30 names.
  obtain ⟨ac, hac, hac'⟩ := compS_exch hbf hY58
  obtain ⟨t2, ht2, ht2'⟩ := compS_reassoc hac hac'
  rw [ResU.CompS.functional ht2 hc] at ht2'
  -- The target memory: `⟦ρᵢ ● ρ_f ● ρ_Q ● ρ⁺⟧` regrouped as 6.58's `ρ′ ● ρ⁺ ● ρᵢ`.
  obtain ⟨t3, ht3, ht3'⟩ := compS_reassoc hF g2
  obtain ⟨u3, hu3, hu3'⟩ := compS_reassoc ht3' g6
  have hiu3 : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) u3 :=
    ⟨hu3'.1, fρ'p, hu3', hvfp⟩
  have hvu3 : ResU.Valid u3 := (ResU.Valid.split hu3' hvfp).2
  have ht3p : ResU.Hash t3 ρp := ⟨hu3.1, u3, hu3, hvu3⟩
  obtain ⟨hψt3, -⟩ := ResU.Hash.split hsplit (ResU.hash_symm ht3p)
  obtain ⟨ρ'χ, hρ'χ⟩ := (ResU.compS_defined_iff t3 ψ).mpr (ResU.hash_symm hψt3).1
  obtain ⟨ht3i, -⟩ := ResU.Hash.split hu3 (ResU.hash_symm hiu3)
  have hiρ'χ : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) ρ'χ :=
    ResU.hash_of_pairwise (ResU.hash_symm ht3i) (ResU.hash_symm hψt3)
      (ResU.hash_symm hψi) hρ'χ
  obtain ⟨Q58, hQ58⟩ :=
    (ResU.compS_defined_iff ρ'χ (ResU.single l (CellU.immOf s v' σ hs))).mpr
      (ResU.hash_symm hiρ'χ).1
  -- *"…with lemma 6.58"* — the second conclusion.
  have h58R := ResU.six58_right hreb (fun a ha => hEA _ a ha) hagχ (ResU.hash_symm hiu3)
    hu3 hsubK.toSub hsplit hρ'χ (ResU.CompS.comm hu3') hQ58
  have hLQ : ResU.Lower Q58 μ' := (h58R μ').mp g7
  -- `ρ′ ● ρ⁺′ ● ρᵢ = (ρ_f ● ρ_Q) ● (ρᵢ ● ρ⁺′)`, the shape the goal's row takes.
  obtain ⟨bc, hbc, hbc'⟩ := compS_exch hρ'χ hQ58
  obtain ⟨ρpG, hρpG, hρpG'⟩ := compS_reassoc hbc hbc'
  -- H33, by lemma 6.59.
  have hiπ : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) π :=
    ResU.hash_of_pairwise hiQ hQp hip g9
  obtain ⟨w59, hw59⟩ := (ResU.compS_defined_iff ρQ ψ).mpr (ResU.hash_symm hψQ).1
  have hiw59 : ResU.Hash (ResU.single l (CellU.immOf s v' σ hs)) w59 :=
    ResU.hash_of_pairwise hiQ (ResU.hash_symm hψQ) (ResU.hash_symm hψi) hw59
  obtain ⟨Y59, hY59⟩ :=
    (ResU.compS_defined_iff w59 (ResU.single l (CellU.immOf s v' σ hs))).mpr
      (ResU.hash_symm hiw59).1
  have hvY59 : ResU.Valid Y59 := hash_valid_comp (ResU.hash_symm hiw59) hY59
  obtain ⟨σX, hσX⟩ := id hvρ
  obtain ⟨σY, hσY⟩ := id hvY59
  have h59 : ResU.Upd ρ Y59 :=
    ResU.six59 hreb (ResU.CompS.comm hbχ) g9 gA h15 h29 (ResU.hash_symm h18)
      (ResU.hash_symm hiπ) hsubK hc ⟨w59, hw59, hY59⟩ hσX hσY
  -- `ρ_Q ● ρᵢ ● ρ⁺′` is `ρ_Q ● (ρᵢ ● ρ⁺′)` — 6.59's `Y` at the goal's bracketing.
  obtain ⟨bc59, hbc59, hbc59'⟩ := compS_reassoc hw59 hY59
  rw [ResU.CompS.functional (ResU.CompS.comm hbc59) hρpG] at hbc59'
  -- G2–G7.
  refine ⟨ρQ, ρpG, Y58, t3, Q58, Y59, v, μ, μ', ResU.hash_symm hfQ, ht3, ?_, ht2', hLY,
    hρpG', hLQ, g8, hbc59', ⟨h59, hvρ, hvY59⟩,
    ?_, h28⟩
  · exact ResU.hash_symm
      (ResU.hash_of_pairwise ht3i (ResU.hash_symm hψi) (ResU.hash_symm hψt3) hρpG)
  · exact noOwn_compS hρpG (noOwn_single_imm l s v' σ hs) (noOwn_subKeep hsubK gB)

end BoCa.Fig16.BoLo

alias TR.lemma_6_150 := BoCa.Fig16.BoLo.wp_reborrow
alias TR.«↺ rule» := BoCa.Fig16.BoLo.wp_reborrow

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps)

/-- `RebEscrow`'s second half is empty at a reborrow whose source carries no `own` cell.
`[about ours: where the added hypothesis is empty]` -/
theorem rebEscrow_of_no_own {P : Life → BoCa.Val → WProp}
    (hno : ∀ (b : Life) (w : BoCa.Val) (σ χ : WRes), ResU.Reb b σ χ → P b w χ →
      ∀ m ψ, σ.get m = some ψ → ψ.kind ≠ Kind.own)
    (hag : ∀ (b : Life) (w : BoCa.Val) (σ χ : WRes), ResU.Reb b σ χ → P b w χ →
      ∃ A, AgW χ A) :
    RebEscrow P :=
  fun b w σ χ hreb hP =>
    ⟨hag b w σ χ hreb hP,
      fun _ a _ => escrowAgree_of_no_own (hno b w σ χ hreb hP) χ a⟩

/-- `RebEscrow` holds at `P̂ = (· = ∅)`.
`[about ours: non-vacuity of the added hypothesis]` -/
theorem rebEscrow_emp : RebEscrow (fun _ _ ρ => ρ = PMap.empty) := by
  rintro b w σ χ - rfl
  exact ⟨⟨PMap.empty, agW_empty⟩,
    fun _ _ _ l v ψ ψf _ he => absurd he (by simp)⟩

/-- 6.150's premise holds at `ℓ ↦ imm({⊤}, v, ∅)` and `P̂ = (· = ∅)`.
`[about ours: non-vacuity of the rule's premise at a satisfying hypothesis]` -/
theorem wp_reborrow_nonvacuous (l : BoCa.Loc) (v₀ : BoCa.Val) :
    (ptoImm l ⊤ (fun v => fresh fun b => reborrow b ((fun _ _ ρ => ρ = PMap.empty) b v)) ⋆
      (fresh fun b => all fun _v : BoCa.Val =>
        (fun _ _ ρ => ρ = PMap.empty) b _v ─⋆
          wp (Expr.val v₀) (fun v' => box b ((fun _ => emp) v'))))
      (ResU.single l (CellU.immOf (LSet.singleton ⊤) v₀ PMap.empty
        (fun _ _ e => absurd e (by simp)))) := by
  refine ⟨_, PMap.empty, ResU.comp_empty_right _,
    ⟨LSet.singleton ⊤, v₀, PMap.empty, (fun _ _ e => absurd e (by simp)), rfl,
      ⟨⊤, fun b _ => ⟨⟨PMap.empty, reb_empty b, rfl⟩, fun _ _ e => absurd e (by simp)⟩⟩,
      le_rfl⟩,
    ⟨⊤, fun b _ => ⟨fun _ ρ₁ ρ₂ hρ₁ hcs => ?_, fun _ _ e => absurd e (by simp)⟩⟩⟩
  subst hρ₁
  rw [eq_of_compS_empty_left hcs]
  exact wp_val v₀ _ _ ⟨⟨rfl, trivial⟩, fun _ _ e => absurd e (by simp)⟩

/-- 6.150 applied at `rebEscrow_emp` and `wp_reborrow_nonvacuous`.
`[about ours: the rule applied at the inhabitant above]` -/
theorem wp_reborrow_emp_applies (l : BoCa.Loc) (v₀ : BoCa.Val) :
    wp (Expr.val v₀) (fun _ => emp)
      (ResU.single l (CellU.immOf (LSet.singleton ⊤) v₀ PMap.empty
        (fun _ _ e => absurd e (by simp)))) :=
  wp_reborrow l ⊤ (fun _ _ ρ => ρ = PMap.empty) (Expr.val v₀) (fun _ => emp)
    rebEscrow_emp _ (wp_reborrow_nonvacuous l v₀)

end BoCa.Fig16.BoLo

end
