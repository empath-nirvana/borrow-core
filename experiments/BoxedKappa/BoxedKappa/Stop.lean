import Core.Fundamental
import Support.Model.Surgery
import Support.Model.Outlives
import Support.Model.Singletons

/-!
# BoxedKappa — the stop lemma

A stratified protocol table, `opTableS α T`: `opTable T` with the continuation's share at every
non-abortive stop also in `Res_α`. It is below `opTable T` (`opTableS_le`), so `ewpTS` at it gives
`ewpTS` at `opTable T` (`ewpS_ewp`).

The stop lemma needs no new invariant. `wpG` carries `↭` from a run's start to its end
(`ResU.UpdV ρ π`, the ninth conjunct of `wpG`), and `↭` keeps `Res_α` (`ResU.updV_inStratum`, `[TR]`
6.50 read at `Res_α`). So a run started in `Res_α` ends in `Res_α` (`wpG_inStratum`), and its
stop's share, a `●`-factor of the stop's resource, is in `Res_α`. Across a resumption the next run
starts at the share and the answer: in `Res_α` when the answer is (`ewp_stratify`).

Typed (`stop_lemma`): the context's resource is in `Res_{δ(d)}` by `[]I`'s fold of 6.60
(`gSepC_outlives`), and an answer of a type outliving `d` is (`vC_outlives`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore Step1N performE raiseE opPayload
  cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The stratified table -/

/-- `performStop` with the continuation's share in `Res_α`. -/
def performStopS (α : Life) (T : OpTab) : Table := fun ls t Φ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEnt) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆
        (en.PA ls v ⋆ fun ρ => contShare en ls K Φ ρ ∧ ρ.InStratum α)

/-- `opTable T` with every non-abortive stop's share in `Res_α`; the abortive stops as
`opTable`'s. -/
def opTableS (α : Life) (T : OpTab) : Table := fun ls t Φ =>
  BoLo.or (performStopS α T ls t Φ)
    (ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
      ex fun (en : OpEnt) =>
        ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
          T n i = some en ∧ en.abort = true⌝ ⋆
          ((fun ρ => en.PA ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ))

theorem opTableS_mono (α : Life) (T : OpTab) : (opTableS α T).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  rcases h with ⟨K, n, i, v, en, hp⟩ | h
  · obtain ⟨hpure, ρa, ρk, hc, hA, ⟨hu, hk⟩, hs⟩ := pure_sep_iff.mp hp
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure
      ⟨ρa, ρk, hc, hA, ⟨hu, fun ls' he => ⟨fun w τ₁ τ₂ hB hc' => ?_, (hk ls' he).2⟩⟩, hs⟩⟩
    exact hΦ _ _ _ ((hk ls' he).1 w τ₁ τ₂ hB hc')
  · exact Or.inr h

/-- The stratified table is below the table. -/
theorem opTableS_le {α : Life} {T : OpTab} {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : opTableS α T ls t Φ ρ) :
    opTable T ls t Φ ρ := by
  rcases h with ⟨K, n, i, v, en, hp⟩ | h
  · obtain ⟨hpure, ρa, ρk, hc, hA, hcs, -⟩ := pure_sep_iff.mp hp
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hc, hA, hcs⟩⟩
  · exact Or.inr h

/-- `ewpTS` at the stratified table gives `ewpTS` at the table. -/
theorem ewpS_ewp {α : Life} {T : OpTab} {ls : List SRec} {e : Expr}
    {Q : List SRec → Val → WProp} {ρ : WRes} (h : ewpTS ls e (opTableS α T) Q ρ) :
    ewpTS ls e (opTable T) Q ρ :=
  ewp_mono (opTable_mono T) (fun _ _ _ _ h => opTableS_le h) (fun _ _ _ h => h) h

/-! ### `Res_α` through a run -/

/-- `Res_α` is closed under `●`. -/
theorem inStratum_compS {α : Life} {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : ρ₁.InStratum α) (h₂ : ρ₂.InStratum α) : ρ.InStratum α :=
  BoLo.inStratum_comp (BoLo.compS_hC α) h h₁ h₂

/-- **A run started in `Res_α` ends in `Res_α`**: `wpG`'s `↭` from its start to its end, which
keeps `Res_α` (`ResU.updV_inStratum`), and the end resource a `●`-factor of `↭`'s right side. -/
theorem wpG_inStratum {α : Life} {ls : List SRec} {e : Expr} {Q : List SRec → Expr → WProp}
    {ρ : WRes} (hρ : ρ.InStratum α) (h : wpG ls e Q ρ) :
    wpG ls e (fun ls' t σ => Q ls' t σ ∧ σ.InStratum α) ρ := by
  intro ρf fρ ps h1 h2 h3 h4 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h ρf fρ ps h1 h2 h3 h4 A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, ResU.CompS.inStratum_left a8 (ResU.updV_inStratum hρ a9)⟩

/-- The answers of a table's non-abortive operations lie in `Res_α`. -/
def OpTab.AnsIn (α : Life) (T : OpTab) : Prop :=
  ∀ n i en, T n i = some en → en.abort = false → ∀ ls w τ, en.PB ls w τ → τ.InStratum α

/-- **The stop lemma, semantically.** A computation in `ewpTS` at `opTable T`, started in `Res_α`,
at a table whose answers lie in `Res_α`, is in `ewpTS` at `opTableS α T`: at every stop of every
run, the continuation's share is in `Res_α`. -/
theorem ewp_stratify {α : Life} {T : OpTab} (hT : T.AnsIn α) {Q : List SRec → Val → WProp}
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : ewpTS ls e (opTable T) Q ρ)
    (hρ : ρ.InStratum α) : ewpTS ls e (opTableS α T) Q ρ := by
  refine (ewp_ind (fun ls e ρ => ρ.InStratum α → ewpTS ls e (opTableS α T) Q ρ) ?_ h) hρ
  intro ls e ρ hs hρ
  refine ewp_fold (opTableS_mono α T) (wpG_mono ?_ (wpG_inStratum hρ hs))
  rintro ls' t σ ⟨hq, hσ⟩
  rcases hq with hv | hq
  · exact Or.inl hv
  rcases hq with ⟨K, n, i, v, en, hp⟩ | habt
  · obtain ⟨hpure, ρa, ρk, hc, hA, hu, hk⟩ := pure_sep_iff.mp hp
    have hρk : ρk.InStratum α := ResU.CompS.inStratum_right hc hσ
    refine Or.inr (Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure
      ⟨ρa, ρk, hc, hA, ⟨hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc' => ?_, (hk ls'' he).2⟩⟩, hρk⟩⟩)
    exact (hk ls'' he).1 w τ₁ τ₂ hB hc'
      (inStratum_compS hc' hρk (hT n i en hpure.2.2.1 hpure.2.2.2 ls'' w τ₁ hB))
  · exact Or.inr (Or.inr habt)

/-! ### The stop lemma at Core's typing -/

/-- `Δ ⊢ Σ ⊐ @d` at the answers: every non-abortive operation's answer type outlives `@d`. -/
def Row.AnsOutlives (Δ : LifeCtx) (d : Lifetime.Life) (S : Row) : Prop :=
  ∀ o ∈ S, o.abort = false → VOutlives Δ d o.B

/-- A row whose answer types outlive `@d` has its answers in `Res_{δ(d)}` (6.60, `vC_outlives`). -/
theorem Row.ansIn_of_ansOutlives {Δ : LifeCtx} {δ : LSub} {d : Lifetime.Life} {α : Life}
    {S : Row} (hδ : Δ.Models δ) (hd : d.interp δ = some α) (hS : Row.AnsOutlives Δ d S) :
    (Row.tab S δ).AnsIn α := by
  intro n i en hT ha ls w τ hB
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  exact vC_outlives hδ hd (hS o (Row.find_mem hf).1 ha) true ls w τ hB

/-- The stratified semantic judgment at `F_Σ A`: at every substitution and every interpretation of
`@d`, the computation is in `ewpTS` at the stratified table of `Σ` at `δ(d)`. -/
def SemCS (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (S : Row) (A : VTy) (d : Lifetime.Life) :
    Prop :=
  ∀ δ γ (ls : List SRec) ρ α, Δ.Models δ → d.interp δ = some α → gDenC ls δ Γ γ ρ →
    ewpTS ls (substAll γ M) (opTableS α (Row.tab S δ)) (fun ls v => vC true A ls δ v) ρ

/-- The stratified judgment gives the judgment, where `@d` is defined. -/
theorem SemCS.semC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {S : Row} {A : VTy}
    {d : Lifetime.Life} (h : SemCS Δ Γ M S A d) (hd : Δ.Defines d) :
    SemC Δ Γ M (CTy.effOf S A) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, ha⟩ := hd δ hδ
  exact (cC_effOf S A ls δ _ ρ).mpr (ewpS_ewp (h δ γ ls ρ α hδ ha hg))

/-- **The stop lemma at `SemC`.** -/
theorem stop_sem {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {S : Row} {A : VTy}
    {d : Lifetime.Life} (hM : SemC Δ Γ M (CTy.effOf S A)) (hΓ : CtxOutlives Δ Γ d)
    (hS : Row.AnsOutlives Δ d S) : SemCS Δ Γ M S A d := by
  intro δ γ ls ρ α hδ hd hg
  exact ewp_stratify (Row.ansIn_of_ansOutlives hδ hd hS)
    ((cC_effOf S A ls δ _ ρ).mp (hM δ γ ls ρ hδ hg))
    (gSepC_outlives hδ hd hΓ.2 (gDenC_iff.mp hg).2)

/-- **The stop lemma.** A computation typed at `F_Σ A` under `Γ_M`, with `Δ ⊨ Γ_M ⊐ @d` and every
non-abortive answer type of `Σ` outliving `@d`: at every stop, at every `δ`, the continuation's
share is in `Res_{δ(d)}`. No premise for T1: `CDerives` types a lend's callback at the pure row or
at a row of abortive operations, and `wpG`'s `↭` already excludes a lend open at a stop. -/
theorem stop_lemma {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {S : Row} {A : VTy}
    {d : Lifetime.Life} (hder : CDerives Δ Γ M (.comp (CTy.effOf S A)))
    (hΓ : CtxOutlives Δ Γ d) (hS : Row.AnsOutlives Δ d S) : SemCS Δ Γ M S A d :=
  stop_sem (fundamentalC hder) hΓ hS

end BoCa.Fig16.LogRel.Core

end
