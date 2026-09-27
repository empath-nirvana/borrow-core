import FrameTheorems.Footprint
import Core.Steps

/-!
# FrameTheorems — from the exhibited run to every run that does not allocate

`wpTS` exhibits one run.  The machine is deterministic except at `alloc↦`, which may pick any
location the heap misses, and at the array step `tab`, which may place its cells at any run of
such locations.  So a run that takes no `alloc↦` step and no array step (`ArrRedex`; `idx` and
`drop` are excluded too, for `TwoRun`'s renaming) is the only run to a value from its start
(`stepsNA_det`): every other run to a value takes the same steps.  The footprint of the
exhibited run is therefore the footprint of every such run (`wpTS_footprint_every`).

A run that allocates is related to the exhibited one only through a renaming of the locations
it allocates.  Runs to values need not agree even on the initial heap's domain
(`not_runsAgreeOnDom`): `store 0 (alloc ())` writes the fresh location's name into cell `0`,
and two runs pick different names.  The footprint on every run, allocating or not, is stated as
`EveryRunFootprint` and not derived.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.FrameTheorems
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-! ### The head step is a function away from `alloc` -/

/-- The redex `alloc v`. -/
def allocRedex (v : Val) : Expr := .app (.val (.prim .alloc)) (.val v)

/-- The redex of an array step, `tab v`, `idx v` or `drop v`.  `tab` picks a run of fresh
consecutive locations, so it is not a function of the configuration, like `alloc`; `idx` and
`drop` compute locations from a base, so a renaming of `Loc` does not carry them (`TwoRun`). -/
def ArrRedex (a : Expr) : Prop :=
  ∃ (p : Prim) (v : Val), (p = .tab ∨ p = .idx ∨ p = .drop) ∧ a = .app (.val (.prim p)) (.val v)

theorem arrRedex_tab (v : Val) : ArrRedex (.app (.val (.prim .tab)) (.val v)) :=
  ⟨.tab, v, .inl rfl, rfl⟩

theorem arrRedex_idx (v : Val) : ArrRedex (.app (.val (.prim .idx)) (.val v)) :=
  ⟨.idx, v, .inr (.inl rfl), rfl⟩

theorem arrRedex_drop (v : Val) : ArrRedex (.app (.val (.prim .drop)) (.val v)) :=
  ⟨.drop, v, .inr (.inr rfl), rfl⟩

/-- Two head steps from one configuration agree, unless the redex is an allocation or an
array step. -/
theorem head_det_gen {μ μ' μ₁ μ₂ : Heap} {a b a₁ a₂ : Expr} (h₁ : Head μ a μ₁ a₁)
    (h₂ : Head μ' b μ₂ a₂) (hab : a = b) (hμ : μ = μ')
    (hna : ∀ v : Val, a ≠ allocRedex v) (hnr : ¬ ArrRedex a) : μ₂ = μ₁ ∧ a₂ = a₁ := by
  subst hμ
  cases h₁ with
  | alloc v _ _ => exact absurd rfl (hna v)
  | tab => exact absurd (arrRedex_tab _) hnr
  | idx => exact absurd (arrRedex_idx _) hnr
  | drop => exact absurd (arrRedex_drop _) hnr
  | _ => cases h₂ <;> simp_all [allocRedex, Expr.val, Subtype.val_inj]

theorem head_det {μ μ₁ μ₂ : Heap} {a a₁ a₂ : Expr} (h₁ : Head μ a μ₁ a₁)
    (h₂ : Head μ a μ₂ a₂) (hna : ∀ v : Val, a ≠ allocRedex v) (hnr : ¬ ArrRedex a) :
    μ₂ = μ₁ ∧ a₂ = a₁ :=
  head_det_gen h₁ h₂ rfl rfl hna hnr

/-- A step whose redex is neither an allocation nor an array step. -/
def Step1NA (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ Head μ a μ' a' ∧
    (∀ v : Val, a ≠ allocRedex v) ∧ ¬ ArrRedex a

/-- A run that takes no `alloc↦` step and no array step. -/
inductive StepsNA : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : StepsNA μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1NA μ e μ₁ e₁) (t : StepsNA μ₁ e₁ μ' e') : StepsNA μ e μ' e'

theorem Step1NA.toStep1 {μ μ' : Heap} {e e' : Expr} (h : Step1NA μ e μ' e') :
    Step1 μ e μ' e' := by
  obtain ⟨K, a, a', h₁, h₂, h₃, -⟩ := h
  exact ⟨K, a, a', h₁, h₂, h₃⟩

theorem StepsNA.toSteps {μ μ' : Heap} {e e' : Expr} (h : StepsNA μ e μ' e') :
    Steps μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more h.toStep1 ih

/-- A step that is not an allocation is the only step. -/
theorem step1_det {μ μ₁ μ₂ : Heap} {e e₁ e₂ : Expr} (h₁ : Step1NA μ e μ₁ e₁)
    (h₂ : Step1 μ e μ₂ e₂) : μ₂ = μ₁ ∧ e₂ = e₁ := by
  obtain ⟨K, a, a', rfl, rfl, hh₁, hna, hnr⟩ := h₁
  obtain ⟨K', b, b', hE, rfl, hh₂⟩ := h₂
  obtain ⟨K'', rfl, rfl⟩ := plug_decomp hh₂ K K' hh₁.not_isVal hE
  obtain rfl : K'' = .hole := head_plug hh₁ K'' hh₂.not_isVal rfl
  obtain ⟨rfl, rfl⟩ := head_det hh₁ hh₂ hna hnr
  exact ⟨rfl, by rw [Kont.plug_comp]; rfl⟩

/-- **A run that does not allocate is the only run to a value.**  Every run to a value from
the same configuration ends at the same heap and value. -/
theorem stepsNA_det {μ μ₁ : Heap} {e e₁ : Expr} (h₁ : StepsNA μ e μ₁ e₁) :
    ∀ {v₁ : Val} {μ₂ : Heap} {v₂ : Val}, e₁ = v₁.1 → Steps μ e μ₂ v₂.1 → μ₂ = μ₁ ∧ v₂ = v₁ := by
  induction h₁ with
  | refl μ e =>
      intro v₁ μ₂ v₂ he h₂
      subst he
      exact steps_from_val h₂
  | more hs _ ih =>
      intro v₁ μ₂ v₂ he h₂
      cases h₂ with
      | refl =>
          exact absurd hs.toStep1 (BoCa.BoLo.no_step_val (w := v₂))
      | more h t =>
          obtain ⟨rfl, rfl⟩ := step1_det hs h
          exact ih he t

/-! ### The footprint on every run that does not allocate -/

/-- **The footprint on every allocation-free run.**  From the tagged typed world `ρf ● ρ`,
every run of `e` to a value that takes no `alloc↦` step satisfies `Footprint ρf ρ`, and its
result satisfies the post-condition. -/
theorem wpTS_footprint_every {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp}
    {ρ : WRes} (hw : wpTS ls e Q ρ) {ρf fρ : WRes} {ps : List FrameRec}
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) {μ μR : Heap} {w : Val} (hμ : ResU.Lower fρ μ)
    (hR : StepsNA μ e μR (.val w)) :
    (∃ ls' ρ', Q ls' w ρ') ∧ Footprint ρf ρ μ μR := by
  obtain ⟨μ', v, hrun, hQ, hfp⟩ := wpTS_footprint hw hf hc hT htg hμ
  obtain ⟨rfl, rfl⟩ := stepsNA_det hR rfl hrun
  exact ⟨hQ, hfp⟩

/-! ### Runs that allocate -/

/-- Any two runs to values from one configuration agree on the initial heap's domain. -/
def RunsAgreeOnDom : Prop :=
  ∀ (μ μ₁ μ₂ : Heap) (e : Expr) (v₁ v₂ : Val), Steps μ e μ₁ v₁.1 → Steps μ e μ₂ v₂.1 →
    ∀ l, μ l ≠ none → μ₁ l = μ₂ l

/-- `store 0`, a value. -/
def store0 : Val := ⟨.app (.prim .store) (.loc 0), .storeV .loc⟩

/-- The heap with one cell, `0 ↦ ()`. -/
def heap0 : Heap := BoLo.Heap.upd (fun _ => none) 0 .unit

/-- `store 0 (alloc ())` runs to `()` with cell `0` naming whichever location `alloc` picked. -/
theorem store0_alloc_runs (ℓ : Loc) (hℓ : ℓ ≠ 0) :
    Steps heap0 (.app store0.1 (allocRedex .unit))
      (BoLo.Heap.upd (BoLo.Heap.upd heap0 ℓ .unit) 0 (.loc ℓ)) (Val.unit).1 := by
  refine .more (μ₁ := BoLo.Heap.upd heap0 ℓ .unit)
    (e₁ := .app store0.1 (.val (.loc ℓ))) ?_ (.one ?_)
  · exact ⟨.appR store0.1 .hole, allocRedex .unit, .val (.loc ℓ), rfl, rfl,
      Head.alloc _ .unit ℓ (by simp [heap0, BoLo.Heap.upd, hℓ])⟩
  · exact Step1.head (Head.store _ 0 (.loc ℓ) .unit (by simp [heap0, BoLo.Heap.upd, hℓ.symm]))

/-- The machine's runs to values do not agree on the initial heap: they differ by the names
of the locations they allocate. -/
theorem not_runsAgreeOnDom : ¬ RunsAgreeOnDom := by
  intro h
  have := h _ _ _ _ _ _ (store0_alloc_runs 1 (by decide)) (store0_alloc_runs 2 (by decide)) 0
    (by simp [heap0, BoLo.Heap.upd])
  simp [BoLo.Heap.upd] at this


/-- The footprint on every run, allocating or not: the statement `wpTS_footprint_every` proves
for the runs that do not allocate.  Not derived here. -/
def EveryRunFootprint : Prop :=
  ∀ (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) (ρ ρf fρ : WRes)
    (ps : List FrameRec) (μ μR : Heap) (w : Val),
    wpTS ls e Q ρ → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) →
    Tagged fρ ps ls → ResU.Lower fρ μ → Steps μ e μR (.val w) → Footprint ρf ρ μ μR

end BoCa.Fig16.LogRel.Core.FrameTheorems

end
