import Core.Chain.ConstKW835N
import Core.Chain.HandleTKW835N

/-!
# BOXED-κ's stop lemma at `SemJN`  `[spec §28]`

Core's `stop_sem` (`Core/EffBoxed.lean`) at the relation at `KW`, step by step:

* `tabN_ansIn` (Core's `Row.ansIn_of_ansOutlives`): a row whose answer types outlive `@d` has, at
  every world, its non-abortive answers in `Res_{δ(d)}` (`vN_outlives`);
* `SemCSN` (Core's `SemCS`): the computation in `erwpK` at the stratified table `opTableKS` at
  `δ(d)`, at every floor;
* `SemCSN.semJN` (Core's `SemCS.semC`): the stratified table is below the row's table;
* `stop_semN` (Core's `stop_sem`): the context's resource is in `Res_{δ(d)}` (`gN_outlives`,
  Core's `gSepC_outlives`), and `erwpK_stratify` (Core's `ewp_stratify`).

`erwpK` is step-indexed, so `stop_semN` has no `Row.divB` premise (interface entry E13).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **A row whose answer types outlive `@d` has its answers in `Res_{δ(d)}`** (Core's
`Row.ansIn_of_ansOutlives`, 6.60 through `vN_outlives`), at every world. -/
theorem tabN_ansIn {Δ : LifeCtx} {δ : LSub} {d : Lifetime.Life} {α : Life} {S : Row}
    (hδ : Δ.Models δ) (hd : d.interp δ = some α) (hS : Row.AnsOutlives Δ d S) (R : VTy) :
    ∀ (x : KW) n i (en : OpEntK KW), tabN (ℍ := ℍ) (CTy.effOf S R) δ x n i = some en →
      en.abort = false → ∀ y k ls w τ, en.PB y k ls w τ → τ.InStratum α := by
  intro x n i en hT ha y k ls w τ hB
  obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find (tabF_of_tabN hT)
  exact vN_outlives hδ hd (hS o (Row.find_mem hf).1 (by simpa [RowRd.ent, OpSig.abort] using ha))
    y.Θ k w τ hB.1

/-- The stratified semantic judgment at `F_Σ A` (Core's `SemCS`): at every substitution, world,
view, floor, index and interpretation of `@d`, the computation is in `erwpK` at the stratified
table of `Σ` at `δ(d)`. -/
def SemCSN (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (S : Row) (A : VTy) (d : Lifetime.Life) :
    Prop :=
  ∀ (δ : LSub) (γ : List Val) (Θ : LocTy) (c : Loc → Option Life) (lo : Life) (n : Nat)
    (ls : List SRec) (ρ : WRes) (α : Life), Δ.Models δ → d.interp δ = some α → Θ.OK →
      ConsistentX c ρ → Ctx.LiveWithin Γ γ → gN (ℍ := ℍ) δ Θ Γ γ n ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableKS z.lo α (tabN (ℍ := ℍ) (CTy.effOf S A) δ z))
        (fun z k _ v ρ => vN (ℍ := ℍ) A δ z.Θ k v ρ) ⟨Θ, c, lo⟩ n ls (substAll γ M) ρ

/-- The stratified table is below the row's table. -/
theorem opTableKS_le {ι : Type} (lo α : Life) (T : OpTabK ι) (k : Nat) (ls : List SRec) (t : Expr)
    (Ψ : ContK ι) (ρ : WRes) (h : opTableKS lo α T k ls t Ψ ρ) : opTableK lo T k ls t Ψ ρ := by
  rcases h with ⟨K, n, i, v, en, hp⟩ | hr
  · obtain ⟨hpure, ρa, ρk, hc, hA, hcs, -⟩ := pure_sep_iff.mp hp
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hc, hA, hcs⟩⟩
  · exact Or.inr hr

/-- The stratified judgment gives the judgment, where `@d` is defined (Core's `SemCS.semC`). -/
theorem SemCSN.semJN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {S : Row} {A : VTy}
    {d : Lifetime.Life} (h : SemCSN (ℍ := ℍ) Δ Γ M S A d) (hd : Δ.Defines d) :
    SemJN (ℍ := ℍ) Δ Γ M (.comp (CTy.effOf S A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, ha⟩ := hd δ hδ
  refine (cN_effOf S A δ Θ c n ls _ ρ).mpr fun lo => ?_
  exact erwpK_mono (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
    (Tb := fun z => opTableKS z.lo α (tabN (ℍ := ℍ) (CTy.effOf S A) δ z))
    (Q := fun z k _ v ρ => vN (ℍ := ℍ) A δ z.Θ k v ρ) (fun _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun x k ls t Ψ Ψ' ρ hΨ h' =>
      opTableK_local _ _ k ls t Ψ Ψ' ρ hΨ (opTableKS_le _ _ _ _ _ _ _ _ h'))
    n (⟨Θ, c, lo⟩ : KW) ls _ ρ (h δ γ Θ c lo n ls ρ α hδ ha hΘ hc hlw hg)

/-- **The stop lemma at `SemJN`** (Core's `stop_sem`, BOXED-κ's premise): a computation typed at
`F_Σ A` under `Γ`, with `Δ ⊨ Γ ⊐ @d` and every non-abortive answer type of `Σ` outliving `@d`, has
the continuation's share in `Res_{δ(d)}` at every stop, at every `δ`, world and floor. -/
theorem stop_semN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {S : Row} {A : VTy}
    {d : Lifetime.Life} (hM : SemJN (ℍ := ℍ) Δ Γ M (.comp (CTy.effOf S A)))
    (hΓ : CtxOutlives Δ Γ d) (hS : Row.AnsOutlives Δ d S) : SemCSN (ℍ := ℍ) Δ Γ M S A d := by
  intro δ γ Θ c lo n ls ρ α hδ hd hΘ hc hlw hg
  exact erwpK_stratify (tabN_ansIn hδ hd hS A) n (⟨Θ, c, lo⟩ : KW) ls _ ρ
    (gN_outlives hδ hd hΓ.2 hg)
    ((cN_effOf S A δ Θ c n ls _ ρ).mp (hM δ γ Θ c n ls ρ hδ hΘ hc hlw hg) lo)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
