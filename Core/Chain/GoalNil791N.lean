import Core.Chain.Adequacy791N
import Core.Stdio

/-!
# `Goal791N` with no suspending-lend constant, from Core's adequacy  `[spec §62]`

`Goal791N`'s suspending lends are only the `Const791` constants: `CDerives` has none of its own
(its plain lends' callbacks are value `⊸`, its `*U` lends ask for an unwinding row). At `cs = []`
the program is a closed `CDerives` derivation, and Core's `fundamentalC`, which takes no
hypothesis, covers it.

* `orDiverges_of_runs`: a program every run of which from the empty memory continues to a value
  at the empty memory is `OrDiverges`. The first two conjuncts are read off the continuing run; a
  `free` that is not yet a value steps, and its only step finds its cell (`step1_free_iff`).
* `goal791N_nil`: `Goal791N`'s instance at `cs = []`, `Γx = []`, without `HandlerLawN`, from
  `adequacyD_obs`.
* `goal791N_nil_externs`: the same over host externs closed by values meeting Core's contract
  `ExternsMeet`, from `fundamentalC` and `gDenC_of_meets`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx)
open BoCa.BoLo (Heap Steps Step1 Kont freeE)

/-- **A program whose every run continues to a value at the empty memory is `OrDiverges`.** A
reached configuration is a value or steps (the continuing run is empty or not); a reached value
is the continuing run's end, at the empty memory (`steps_from_val`); a reached `free` is no
value, so it steps, and a `free`'s step finds its cell (`step1_free_iff`).  `[spec §62]` -/
theorem orDiverges_of_runs {P : Expr}
    (h : ∀ {μ₁ : Heap} {e₁ : Expr}, Steps (ℍ := ℍ) Adequacy.emptyMem P μ₁ e₁ →
      ∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) :
    OrDiverges (ℍ := ℍ) P := by
  intro μ e hs
  obtain ⟨v, hv⟩ := h hs
  have hp : IsVal e ∨ ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e' := by
    cases hv with
    | refl => exact .inl v.2
    | more h _ => exact .inr ⟨_, _, h⟩
  refine ⟨hp, fun he => ?_, fun K ℓ he => ?_⟩
  · obtain ⟨hμ, -⟩ := steps_from_val (v := ⟨e, he⟩) hv
    exact hμ.symm
  · subst he
    rcases hp with hval | ⟨μ', e', hst⟩
    · have := K.isVal_of_plug hval
      simp [freeE, Expr.val, Val.prim] at this
    · obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).1 hst
      exact ⟨u, hu⟩

/-- **`Goal791N`'s instance at `cs = []`, `Γx = []` without `HandlerLawN`**: every closed program
with no suspending-lend constant, from Core's `fundamentalC` and adequacy (`adequacyD_obs`).
`[spec §62]` -/
theorem goal791N_nil {e : Expr} {R : VTy} (h : CDerives LifeCtx.empty [] e (.comp (.ret R)))
    (hR : R.Persistent) : OrDiverges (ℍ := ℍ) e :=
  orDiverges_of_runs fun hs => by
    obtain ⟨v, hv, -⟩ := EffPrograms.adequacyD_obs hR h hs
    exact ⟨v, hv⟩

/-- **`goal791N_nil` over host externs**: a program typed at `F R`, `R` persistent, in a context
of externs closed by values meeting Core's contract `ExternsMeet`, with no suspending-lend
constant and no `HandlerLawN`, from Core's `fundamentalC` (`gDenC_of_meets`, `theorem32D`).
`[spec §62]` -/
theorem goal791N_nil_externs {Γx : Ctx VTy} {γx : List Val} {e : Expr} {R : VTy}
    (h : CDerives LifeCtx.empty Γx e (.comp (.ret R))) (hR : R.Persistent)
    (hx : ExternsMeet Γx γx) : OrDiverges (ℍ := ℍ) (substAll γx e) :=
  orDiverges_of_runs fun hs => by
    have hwp := fundamentalC h LSub.empty γx [] PMap.empty Adequacy.models_empty
      (gDenC_of_meets hx [] LSub.empty)
    have hwp' : wpTS [] (substAll γx e) (fun _ v => Fig16.BoLo.pure True) PMap.empty :=
      wpTS_mono (fun _ _ _ hv => by
        obtain rfl := vP_empty_of_persistent hR hv
        exact ⟨rfl, trivial⟩) PMap.empty hwp
    obtain ⟨v, hv, -⟩ := theorem32D _ _ hwp' hs
    exact ⟨v, hv⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
