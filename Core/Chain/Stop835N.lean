import Core.Chain.Lend791N
import Core.EffBoxed

/-!
# BOXED-κ's stop lemma at `erwp`  `[spec §28]`

Core's `stop_sem` (`Core/EffBoxed.lean`), step by step, at the chain relation:

* `↭` keeps `Res_α` (Core's `ResU.updV_inStratum`): at the index, `↭`'s `imm` clause is Core's and
  its `mut` clause keeps each cell's lifetime (`MutStep`'s `ψ.at = ψ'.at`), so the proof is
  Core's (`UpdVN.inStratum`);
* a run started in `Res_α` ends in `Res_α` (Core's `wpG_inStratum`): `rwpG`'s end carries `↭` from
  the run's start to `π`, and the end resource is a `●`-factor of `π` (`rwpG_inStratum`);
* `opTableNS α T` is `opTableN T` with each non-abortive stop's share in `Res_α` (Core's
  `opTableS`), below `opTableN T` (`erwpS_erwp`);
* `erwp_stratify` (Core's `ewp_stratify`): at a table whose answers lie in `Res_α`, a run from
  `Res_α` stops only with its share in `Res_α`, and a resumption starts at the share and the
  answer, in `Res_α`. Core inducts on `ewpTS`'s least fixed point; `erwp` is recursive on the
  index, so the induction is on the index;
* `stop_semN` (`StopKW835N`, Core's `stop_sem`): the context's resource is in `Res_{δ(d)}`
  (`gN_outlives`, Core's `gSepC_outlives`) and the row's answers are (`tabN_ansIn`, Core's
  `Row.ansIn_of_ansOutlives`).

Core's `stop_sem` takes `Row.divB S = false` to pass from `cwp` to `ewpTS`. A row holding `Div` is
a row of the chain's table and `erwp` is step-indexed (interface entry E13), so `stop_semN` has no
such premise.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont performE opPayload)

/-! ### `Res_α` through a run -/

/-- **`↭` at the index keeps the stratum** (Core's `ResU.updV_inStratum`, `[TR]` 6.50 read as a
statement about `Res_α`): an `imm` cell of the far side is one of the near side's flattening
(Core's clause); a `mut` cell is stepped from one at the same lifetime (`MutStep`). -/
theorem UpdVN.inStratum {Φ : LocFam} {n : Nat} {ρ ρ' : WRes} {α : Life}
    (hd : ρ.InStratum α) (hu : UpdVN Φ n ρ ρ') : ρ'.InStratum α := by
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hσα : σ.InStratum α := BoLo.flat_inStratum hσ hd
  refine BoLo.flat_inStratum_inv hσ' ?_
  intro m χ hχ
  rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
  · exact trivial
  · obtain ⟨τ, hτ, hgg⟩ := (hu.1.1 m s w ξ hξ).mpr ⟨σ', hσ', hχ⟩
    cases ResU.Flat.functional hτ hσ
    exact hσα m _ hgg
  · obtain ⟨ψ, ⟨τ, hτ, hgg⟩, hk, -, hat, -⟩ :=
      hu.1.2.2 m _ ⟨σ', hσ', hχ⟩ (CellU.kind_mutOf _ _ _ _ _ _)
    cases ResU.Flat.functional hτ hσ
    have h := BoLo.cell_at_of_inStratum (by rw [hk]; simp) (hσα m ψ hgg)
    rw [hat] at h
    exact BoLo.cell_inStratum_of_at h

/-- **A run started in `Res_α` ends in `Res_α`** (Core's `wpG_inStratum`): `rwpG`'s `↭` from its
start to its end keeps `Res_α`, and the end resource is a `●`-factor of `↭`'s right side. -/
theorem rwpG_inStratum {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr}
    {ρ : WRes} {α : Life} (hρ : ρ.InStratum α) (h : rwpG (ℍ := ℍ) Φ Q n ls e ρ) :
    rwpG (ℍ := ℍ) Φ (fun k ls' t σ => Q k ls' t σ ∧ σ.InStratum α) n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃, ResU.CompS.inStratum_left h₆ (UpdVN.inStratum hρ h₇)⟩

/-! ### The stratified table -/

/-- `performStopN` with the continuation's share in `Res_α` (Core's `performStopS`). -/
def performStopNS (α : Life) (T : OpTabN) : TableN := fun k ls t Ψ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntN) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆
        (en.PA k ls v ⋆ fun ρ => contShareN en k ls K Ψ ρ ∧ ρ.InStratum α)

/-- `opTableN T` with every non-abortive stop's share in `Res_α`; the abortive stops as
`opTableN`'s (Core's `opTableS`). -/
def opTableNS (α : Life) (T : OpTabN) : TableN := fun k ls t Ψ =>
  BoLo.or (performStopNS α T k ls t Ψ) (raiseStopN T k ls t Ψ)

theorem opTableNS_local (α : Life) (T : OpTabN) : (opTableNS α T).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, ρa, ρk, hc, hA, ⟨hu, hcont⟩, hs⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, ⟨hu, fun ls' he =>
      ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ k' hk _ _ _ ((hcont ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
        (hcont ls' he).2⟩⟩, hs⟩⟩
  · exact Or.inr h

theorem opTableNS_down (α : Life) {T : OpTabN} (hT : T.Down) : (opTableNS α T).Down := by
  intro k ls t Ψ ρ h
  rcases h with ⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, ⟨hu, hcont⟩, hs⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩ ⟨ρa, ρk, hc,
      hT.pa _ _ _ h₃ _ _ _ _ hA, ⟨hu, fun ls' he =>
      ⟨fun k' hk => (hcont ls' he).1 k' (by omega), fun hq P hP =>
        hT.fin _ _ _ _ h₃ hP _ _ _ _ ((hcont ls' he).2 hq P hP)⟩⟩, hs⟩⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρn, hc, ⟨hA, hnA⟩, hnn⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩
      ⟨ρa, ρn, hc, ⟨hT.pa _ _ _ h₃ _ _ _ _ hA, hnA⟩, hnn⟩⟩

/-- The stratified table is below the table (Core's `opTableS_le`). -/
theorem opTableNS_le {α : Life} {T : OpTabN} {k : Nat} {ls : List SRec} {t : Expr} {Ψ : ContN}
    {ρ : WRes} (h : opTableNS α T k ls t Ψ ρ) : opTableN T k ls t Ψ ρ := by
  rcases h with ⟨K, n, i, v, en, hp⟩ | h
  · obtain ⟨hpure, ρa, ρk, hc, hA, hcs, -⟩ := pure_sep_iff.mp hp
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hc, hA, hcs⟩⟩
  · exact Or.inr h

/-- `erwp` at the stratified table gives `erwp` at the table (Core's `ewpS_ewp`). -/
theorem erwpS_erwp {Φ : LocFam} {α : Life} {T : OpTabN} {Q : PostN} :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableNS α T) Q n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ :=
  erwp_mono (fun _ _ _ _ h => h) (fun k ls t Ψ Ψ' ρ hΨ h =>
    opTableN_local T k ls t Ψ Ψ' ρ hΨ (opTableNS_le h))

/-- The answers of a table's non-abortive operations lie in `Res_α`, at every index (Core's
`OpTab.AnsIn`). -/
def OpTabN.AnsIn (α : Life) (T : OpTabN) : Prop :=
  ∀ n i en, T n i = some en → en.abort = false → ∀ k ls w τ, en.PB k ls w τ → τ.InStratum α

/-- **The stop lemma, semantically** (Core's `ewp_stratify`). A computation in `erwp` at
`opTableN T`, started in `Res_α`, at a table whose answers lie in `Res_α`, is in `erwp` at
`opTableNS α T`: at every stop of every run, the continuation's share is in `Res_α`. -/
theorem erwp_stratify {Φ : LocFam} {α : Life} {T : OpTabN} (hT : T.AnsIn α) {Q : PostN} :
    ∀ n ls e ρ, ρ.InStratum α → erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableNS α T) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ hρ h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨ht, hσ⟩ => ?_) (rwpG_inStratum hρ h)
  rcases ht with hv | ⟨K, m, i, v, en, hp⟩ | hr
  · exact Or.inl hv
  · obtain ⟨hpure, ρa, ρk, hc, hA, hu, hk'⟩ := pure_sep_iff.mp hp
    have hρk : ρk.InStratum α := ResU.CompS.inStratum_right hc hσ
    refine Or.inr (Or.inl ⟨K, m, i, v, en, pure_sep_mk hpure
      ⟨ρa, ρk, hc, hA, ⟨hu, fun ls'' he => ⟨fun k' hk'' w τ₁ τ₂ hB hcτ => ?_, (hk' ls'' he).2⟩⟩,
        hρk⟩⟩)
    have h₁ := (hk' ls'' he).1 k' hk'' w τ₁ τ₂ hB hcτ
    simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
    exact ih k' (by omega) _ _ _
      (inStratum_compS hcτ hρk (hT m i en hpure.2.2.1 hpure.2.2.2 k' ls'' w τ₁ hB)) h₁
  · exact Or.inr (Or.inr hr)

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
