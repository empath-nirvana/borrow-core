import Targets.Restricted.CoreLaws
import Targets.Restricted.Composition
import Core.Totality

/-!
# Targets — T1 at Core σ=[], at the platform with no operation (DESIGN §9 items 5, 6, 20)

* `adequateRetAt_core_none : AdequateRetAt coreW Platform.none`: a closed computation of `F_S A`,
  `A` data, in Core's relation at the empty resource, is safe and terminating under the platform
  with no operation (`S` must be `[]`: main's row holds only platform operations).  From
  `theorem32D` (every run continues to a value at the empty memory, through `wpTS_demonic`),
  `vC_data`, and the semantic form of `total_no_infinite_run`.
* `soundRetAt_tier1_none : SoundRetAt tier1 Platform.none`: T1's return conjunct for Core's typing
  at that platform, from `FL coreW tier1` (`fundamentalC`) and adequacy.  **PROVED AT A
  RESTRICTION** (`P = Platform.none`, the ret conjunct).
* The existing acceptance programs of `Core/EffPrograms.lean` and `Core/EffExamples.lean` against
  it (`acceptedT1_*`).

`every_alloc_of_wpTS` and `no_infinite_of_wpTS` are `total_every_alloc` and
`total_no_infinite_run`'s glue at a semantic hypothesis (`wpTS` at the empty world) rather than at a
`CDerives` derivation; the lemmas that carry their argument (`ARun.no_infinite`, `Alloc.ofRun`,
`InfRun.astep`) are Core's, reused.  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `total_every_alloc` at `wpTS` at the empty world: under every allocator, from every allocation
count, the run from the empty memory reaches a value. -/
theorem every_alloc_of_wpTS {e : Expr} {Q : List SRec → Val → WProp}
    (hwp : wpTS (ℍ := ℍ) [] e Q (PMap.empty : WRes)) (Al : Alloc) (k : Nat) :
    ∃ (k' : Nat) (μ' : Heap) (v : Val), ARun (ℍ := ℍ) Al k Adequacy.emptyMem e k' μ' (.val v) := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨-, -, -, -, -, v, μ, μ', -, -, -, -, -, h4, -, -, ⟨k', hrun⟩, -⟩ :=
    hwp PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg
      Al k
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h4 Fig16.BoLo.lower_empty
  exact ⟨k', μ', v, hrun⟩

/-- `total_no_infinite_run` at `wpTS` at the empty world. -/
theorem no_infinite_of_wpTS {e : Expr} {Q : List SRec → Val → WProp}
    (hwp : wpTS (ℍ := ℍ) [] e Q (PMap.empty : WRes)) :
    ¬ ∃ f : ℕ → Heap × Expr, f 0 = (Adequacy.emptyMem, e) ∧
      ∀ n, Step1 (ℍ := ℍ) (f n).1 (f n).2 (f (n + 1)).1 (f (n + 1)).2 := by
  rintro ⟨f, h0, hf⟩
  obtain ⟨_, _, _, hv⟩ :=
    every_alloc_of_wpTS hwp (BoCa.Fig16.LogRel.Core.Alloc.ofRun (ℍ := ℍ) hf) 0
  refine BoCa.Fig16.LogRel.Core.ARun.no_infinite hv
    (fun n => ((InfRun.cnt hf n), (f n).1, (f n).2)) ?_ ?_
  · simp [InfRun.cnt, countTrue, h0]
  · intro n
    exact InfRun.astep hf n

/-! ### Runs under the platform with no operation -/

/-- A row the empty platform answers is empty. -/
theorem row_nil_of_le {S : Row} (h : RowLe S Platform.none.ops) : S = [] := by
  cases S with
  | nil => rfl
  | cons o S =>
      exfalso
      have hf : Row.find (o :: S) o.n o.i = some o := by simp [Row.find]
      have := h o.n o.i o hf
      simp [Platform.none, Row.find] at this

/-- A step under the empty platform is a machine step. -/
theorem pstep_none {c c' : Conf Platform.none} (h : PStep (ℍ := ℍ) Platform.none c c') :
    Step1 (ℍ := ℍ) c.μ c.e c'.μ c'.e := by
  cases h with
  | mach h => exact h
  | plat _ ho _ => simp [Platform.none, Row.find] at ho

theorem psteps_none {c c' : Conf Platform.none} (h : PSteps (ℍ := ℍ) Platform.none c c') :
    Steps (ℍ := ℍ) c.μ c.e c'.μ c'.e := by
  induction h with
  | refl => exact .refl _ _
  | tail _ hs ih => exact ih.trans (.one (pstep_none hs))

/-- A machine run is a run under the empty platform. -/
theorem psteps_of_steps {μ μ' : Heap} {e e' : Expr} (s : Unit) (h : Steps (ℍ := ℍ) μ e μ' e') :
    PSteps (ℍ := ℍ) Platform.none (⟨μ, e, s⟩ : Conf Platform.none) ⟨μ', e', s⟩ := by
  induction h with
  | refl => exact .refl
  | more h _ ih => exact Relation.ReflTransGen.head (.mach h) ih

/-- **`AdequateRetAt coreW Platform.none`.** -/
theorem adequateRetAt_core_none : AdequateRetAt (ℍ := ℍ) (coreW (ℍ := ℍ)) Platform.none := by
  intro S A e hd hle h
  obtain rfl := row_nil_of_le hle
  have hwp : wpTS (ℍ := ℍ) [] e (fun _ v => Fig16.BoLo.pure (DataVal A v)) (PMap.empty : WRes) :=
    wpTS_mono (fun _ _ _ hv => by
      obtain ⟨rfl, hD⟩ := (vC_data hd).mp hv
      exact ⟨rfl, hD⟩) _ h
  have hrun : ∀ c, PSteps (ℍ := ℍ) Platform.none (init Platform.none e) c →
      ∃ v, Steps (ℍ := ℍ) c.μ c.e Adequacy.emptyMem (.val v) ∧ DataVal A v :=
    fun c hc => theorem32D e _ hwp (psteps_none hc)
  refine ⟨fun c hc => ?_, fun c hc => ?_, ?_⟩
  · obtain ⟨v, hs, hD⟩ := hrun c hc
    rcases c with ⟨μc, ec, sc⟩
    cases hs with
    | refl => exact Or.inl ⟨v, rfl, hD, rfl⟩
    | more h _ => exact Or.inr ⟨⟨_, _, sc⟩, .mach h⟩
  · obtain ⟨v, hs, hD⟩ := hrun c hc
    exact ⟨⟨Adequacy.emptyMem, .val v, c.s⟩, psteps_of_steps c.s hs, v, rfl, hD, rfl⟩
  · rintro ⟨f, h0, hf⟩
    refine no_infinite_of_wpTS hwp ⟨fun n => ((f n).μ, (f n).e),
      by show ((f 0).μ, (f 0).e) = _; rw [h0]; rfl, fun n => pstep_none (hf n)⟩

/-- **`SoundRetAt tier1 Platform.none`**: T1's return conjunct for Core's typing, at the platform
with no operation.  PROVED AT A RESTRICTION. -/
theorem soundRetAt_tier1_none : SoundRetAt (ℍ := ℍ) tier1 Platform.none :=
  soundRetAt_of_FL fl_core_tier1 adequateRetAt_core_none

/-! ### The existing acceptance programs against T1's restricted instance -/

/-- A closed Core program at a data answer: typed by tier 1, and every run under the empty
platform safe and terminating with the memory empty. -/
def AcceptedT1 (e : Expr) (A : VTy) : Prop :=
  tier1.closed e (.ret A) ∧ SafeRuns (ℍ := ℍ) Platform.none A e ∧
    Terminates (ℍ := ℍ) Platform.none A e

/-- A closed `CDerives` derivation at a data answer is accepted. -/
theorem acceptedT1_of_derives {e : Expr} {A : VTy} (hA : A.Data)
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A))) : AcceptedT1 (ℍ := ℍ) e A :=
  ⟨fun _ _ => h, soundRetAt_tier1_none [] A e hA (fun _ _ _ h => h) (fun _ _ => h)⟩

end Targets

end
