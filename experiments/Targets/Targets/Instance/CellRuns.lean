import Targets.Instance.Runs
import Targets.B.BumpSim

/-!
# The Instance — runs around a capture cell: joins across the cell's location

At a linear or affine operation the catch hands `κ` a fresh cell (SPEC §25): the `[op]` step, the
allocation of `()` at a location the memory does not hold, and later the release of that location
by `κ`'s resume or affine cancel.  Such a run is not quiet (`Quiet`): two of its steps change the
memory, and the allocation may pick any free location.  Between them the run is quiet at every
location, and after the release the memory is the one before the allocation.

* **Finite memories** (`finDom_reach`): every configuration a run reaches from the empty memory
  holds finitely many cells, so some location is free (`exists_fresh_of_finDom`).
* **The allocation, at every location** (`obsFrom_alloc_iff`): when the complete runs after the
  allocation show the same answers and traces as a configuration `c` at every free location, so do
  the complete runs from the allocation.
* **A step that changes the memory and is its configuration's only step** (`obsFrom_mstep_iff`).
* **Steps with events**: the complete runs of an allocation are, at some free location, the
  allocation there and the complete runs after it (`obsFrom_alloc_ex_iff`); along a chain of head
  steps, the chain's observable events and then the complete runs of its end
  (`obsFrom_chain_obs_iff`); from a value, the empty run alone (`obsFrom_val_iff`).
* **Calm runs** (`CellQuiet`, `Calm`): quiet runs, and runs around one cell — quietly to an
  allocation of `()`, at every location quietly from its answer to the release of that location,
  and quietly on from the release's answer.  Calm runs compose and go under every evaluation
  context (`Calm.plug`); from a memory with finitely many cells the complete runs of the two ends
  of a calm run show the same answers and traces (`obsFrom_calm_iff`), so two terms with a common
  calm reduct run alike in every evaluation context (`runsAlike_of_calm`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE hndVal kappa
  clauseAt capTag kappaAt kappaC kappaCBody kappaCell freeE ccatchE cancelVal)
open BoCa.Lifetime (LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg HeadChain)

/-! ### Finite memories -/

theorem finDom_empty : FinDom (Adequacy.emptyMem : Heap) :=
  ⟨[], fun _ h => absurd rfl h⟩

theorem finDom_upd {μ : Heap} (h : FinDom μ) (ℓ : Loc) (v : Val) : FinDom (μ.upd ℓ v) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨ℓ :: d, fun k hk => ?_⟩
  by_cases hkℓ : k = ℓ
  · rw [hkℓ]; exact List.mem_cons_self
  · rw [Heap.upd_other hkℓ] at hk; exact List.mem_cons_of_mem _ (hd k hk)

theorem finDom_del {μ : Heap} (h : FinDom μ) (ℓ : Loc) : FinDom (μ.del ℓ) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun k hk => hd k ?_⟩
  by_cases hkℓ : k = ℓ
  · rw [hkℓ, Heap.del_same] at hk; exact absurd rfl hk
  · rwa [Heap.del_other hkℓ] at hk

theorem finDom_fill {μ : Heap} (h : FinDom μ) (ℓ : Loc) (n : ℕ) (v : Val) :
    FinDom (μ.fill ℓ n v) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨List.range' ℓ n ++ d, fun k hk => ?_⟩
  unfold Heap.fill at hk
  split at hk
  · rename_i hr
    exact List.mem_append_left _ (List.mem_range'_1.2 ⟨hr.1, hr.2⟩)
  · exact List.mem_append_right _ (hd k hk)

/-- A memory with finitely many cells leaves some location free. -/
theorem exists_fresh_of_finDom {μ : Heap} (h : FinDom μ) : ∃ ℓ, μ ℓ = none := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset d.toFinset
  refine ⟨x, ?_⟩
  by_contra hne
  exact hx (List.mem_toFinset.2 (hd x hne))

/-- A head step keeps a memory's cells finitely many. -/
theorem finDom_head {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a') (hf : FinDom μ) :
    FinDom μ' := by
  cases h <;>
    first
    | exact hf
    | exact finDom_upd hf _ _
    | exact finDom_del hf _
    | exact finDom_fill hf _ _ _

section Fin
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

theorem finDom_ostep {c c' : Heap × Expr} {ev : (𝕊).Event} (h : OStep (ℍ := ℍ) RF Ξ c ev c')
    (hf : FinDom c.1) : FinDom c'.1 := by
  cases h with
  | mach hh => exact finDom_head hh hf
  | again => exact hf
  | fin => exact hf

theorem finDom_rstep {R : (𝕊).Runner} {c c' : (𝕊).RConf R} {ev : (𝕊).Event}
    (h : (𝕊).RStep R c ev c') (hf : FinDom c.1.1) : FinDom c'.1.1 := by
  cases h with
  | mach h' => exact finDom_ostep h' hf
  | io => exact hf

/-- **Every configuration a run reaches from the empty memory holds finitely many cells.** -/
theorem finDom_reach {R : (𝕊).Runner} {P : Expr} {c : (𝕊).RConf R}
    (h : (𝕊).RReach R ((𝕊).rinit R P) c) : FinDom c.1.1 := by
  induction h with
  | refl => exact finDom_empty
  | tail _ hst ih =>
      obtain ⟨ev, hst⟩ := hst
      exact finDom_rstep hst ih

end Fin

/-! ### The allocation and the release, under every runner -/

section Obs
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- `alloc v`. -/
abbrev allocE (v : Val) : Expr := .app (.val (.prim .alloc)) (.val v)

/-- **The steps of an allocation**: every step of a configuration at `alloc v` allocates `v` at a
location the memory does not hold, and shows no event. -/
theorem rstep_alloc_inv (R : (𝕊).Runner) {μ : Heap} {s : R.St} (K : Kont) (v : Val)
    {ev : (𝕊).Event} {c' : (𝕊).RConf R} (h : (𝕊).RStep R ((μ, K.plug (allocE v)), s) ev c') :
    ∃ ℓ, μ ℓ = none ∧ ev = .tau ∧ c' = ((μ.upd ℓ v, K.plug (.val (Val.loc ℓ))), s) := by
  have hal : Head (ℍ := ℍ) Adequacy.emptyMem (allocE v) (Adequacy.emptyMem.upd 0 v)
      (.val (Val.loc 0)) := Head.alloc _ v 0 rfl
  have hs1 : Step1 (ℍ := ℍ) Adequacy.emptyMem (K.plug (allocE v)) (Adequacy.emptyMem.upd 0 v)
      (K.plug (.val (Val.loc 0))) := ⟨K, _, _, rfl, rfl, hal⟩
  have hnv : ¬ IsVal (allocE v) := fun h => by cases h
  generalize hc : ((μ, K.plug (allocE v)), s) = c at h
  cases h with
  | mach h' =>
      generalize hc2 : (μ, K.plug (allocE v)) = c₀ at h'
      cases h' with
      | mach hh =>
          have h1 := (Prod.mk.inj hc2).1
          have h2 := (Prod.mk.inj hc2).2
          subst h1
          obtain ⟨rfl, rfl⟩ := plug_decomp hh K _ hal h2
          obtain ⟨ℓ, hℓ, rfl, rfl⟩ := Targets.head_alloc_inv hh
          exact ⟨ℓ, hℓ, labelOf_tau_of rfl, rfl⟩
      | again =>
          rw [(Prod.mk.inj hc2).2] at hs1
          exact (no_step1_drive _ hs1).elim
      | fin =>
          rw [(Prod.mk.inj hc2).2] at hs1
          exact (no_step1_drive _ hs1).elim
  | io hterm hK =>
      exact (no_io_of_step1 hs1 _ _ _ _ hterm hK).elim

/-- **An allocation, at every free location**: when, at every location the memory does not hold,
the complete runs after allocating `v` there show what `Q` says, so do the complete runs from the
allocation.  (Some location must be free: otherwise the allocation has no step.) -/
theorem obsFrom_alloc_iff (R : (𝕊).Runner) {μ : Heap} {s : R.St} (K : Kont) (v : Val)
    (hfr : ∃ ℓ, μ ℓ = none) {Q : OVal → List (𝕊).Event → Prop}
    (h : ∀ ℓ, μ ℓ = none → ∀ w tr,
      (𝕊).ObsFrom R ((μ.upd ℓ v, K.plug (.val (Val.loc ℓ))), s) w tr ↔ Q w tr)
    (w : OVal) (tr : List (𝕊).Event) :
    (𝕊).ObsFrom R ((μ, K.plug (allocE v)), s) w tr ↔ Q w tr := by
  have hτ : ((.tau : (𝕊).Event)).Obs = false := rfl
  constructor
  · rintro ⟨q, ⟨hp, hlast⟩, hv, htr⟩
    cases hp with
    | nil =>
        obtain ⟨ℓ, hℓ⟩ := hfr
        exact absurd (hlast.2 _ _ (OStep.mach (Head.alloc μ v ℓ hℓ))) (fun h => h)
    | @cons _ ev c₁ q' hst hp' =>
        obtain ⟨ℓ, hℓ, rfl, rfl⟩ := rstep_alloc_inv R K v hst
        refine (h ℓ hℓ w tr).1 ⟨q', ⟨hp', ?_⟩, ?_, ?_⟩
        · rw [← A.EffectSystem.lastC_cons (S := 𝕊) _ _ .tau]
          exact hlast
        · rw [← A.EffectSystem.lastC_cons (S := 𝕊) _ _ .tau]
          exact hv
        · rw [← htr]
          exact (List.filter_cons_of_neg (Bool.eq_false_iff.mp hτ)).symm
  · intro hQ
    obtain ⟨ℓ, hℓ⟩ := hfr
    obtain ⟨q, ⟨hp, hlast⟩, hv, htr⟩ := (h ℓ hℓ w tr).2 hQ
    have hst : (𝕊).RStep R ((μ, K.plug (allocE v)), s) .tau
        ((μ.upd ℓ v, K.plug (.val (Val.loc ℓ))), s) := by
      have := A.EffectSystem.RStep.mach (R := R) (s := s)
        (OStep.mach (RF := RF) (Ξ := Ξ) (K := K) (Head.alloc (ℍ := ℍ) μ v ℓ hℓ))
      rwa [labelOf_tau_of rfl] at this
    have hc := A.EffectSystem.lastC_cons (S := 𝕊) ((μ, K.plug (allocE v)), s)
      ((μ.upd ℓ v, K.plug (.val (Val.loc ℓ))), s) .tau q
    refine ⟨(.tau, ((μ.upd ℓ v, K.plug (.val (Val.loc ℓ))), s)) :: q, ⟨.cons hst hp, ?_⟩, ?_, ?_⟩
    · exact (congrArg (fun x => (𝕊).IsVal x.1) hc).mpr hlast
    · exact (congrArg (fun x => (𝕊).term x.1 = (𝕊).ret w) hc).mpr hv
    · rw [← htr]
      exact List.filter_cons_of_neg (Bool.eq_false_iff.mp hτ)

/-- At a configuration whose redex allocates nothing and whose step shows no event, the complete
runs are that step, which may change the memory, followed by the complete runs of the next
configuration. -/
theorem obsFrom_mstep_iff (R : (𝕊).Runner) {μ μ' : Heap} {s : R.St} {K : Kont} {a a' : Expr}
    (hh : Head (ℍ := ℍ) μ a μ' a') (hn : a.allocs = false) (hτ : (labelOf RF Ξ a).Obs = false)
    (v : OVal) (tr : List (𝕊).Event) :
    (𝕊).ObsFrom R ((μ, K.plug a), s) v tr ↔ (𝕊).ObsFrom R ((μ', K.plug a'), s) v tr := by
  have hτ' : (labelOf RF Ξ a : (𝕊).Event).Obs = false := hτ
  constructor
  · rintro ⟨q, ⟨hp, hlast⟩, hv, htr⟩
    cases hp with
    | nil => exact absurd (hlast.2 _ _ (OStep.mach hh)) (fun h => h)
    | @cons _ ev c₁ q' hst hp' =>
        obtain ⟨rfl, rfl⟩ := rstep_det hh hn hst
        refine ⟨q', ⟨hp', ?_⟩, ?_, ?_⟩
        · rw [← A.EffectSystem.lastC_cons (S := 𝕊) _ _ (labelOf RF Ξ a)]
          exact hlast
        · rw [← A.EffectSystem.lastC_cons (S := 𝕊) _ _ (labelOf RF Ξ a)]
          exact hv
        · rw [← htr]
          exact (List.filter_cons_of_neg (Bool.eq_false_iff.mp hτ')).symm
  · rintro ⟨q, ⟨hp, hlast⟩, hv, htr⟩
    have hc := A.EffectSystem.lastC_cons (S := 𝕊) ((μ, K.plug a), s)
      ((μ', K.plug a'), s) (labelOf RF Ξ a) q
    refine ⟨(labelOf RF Ξ a, ((μ', K.plug a'), s)) :: q,
      ⟨.cons (.mach (OStep.mach hh)) hp, ?_⟩, ?_, ?_⟩
    · exact (congrArg (fun x => (𝕊).IsVal x.1) hc).mpr hlast
    · exact (congrArg (fun x => (𝕊).term x.1 = (𝕊).ret v) hc).mpr hv
    · rw [← htr]
      exact List.filter_cons_of_neg (Bool.eq_false_iff.mp hτ')

/-- **An allocation, at some free location**: the complete runs from it are the allocation at a
location the memory does not hold, then the complete runs of the next configuration.  (Some location
must be free: otherwise the allocation has no step.) -/
theorem obsFrom_alloc_ex_iff (R : (𝕊).Runner) {μ : Heap} {s : R.St} (K : Kont) (v : Val)
    (hfr : ∃ ℓ, μ ℓ = none) (w : OVal) (tr : List (𝕊).Event) :
    (𝕊).ObsFrom R ((μ, K.plug (allocE v)), s) w tr ↔
      ∃ ℓ, μ ℓ = none ∧ (𝕊).ObsFrom R ((μ.upd ℓ v, K.plug (.val (Val.loc ℓ))), s) w tr := by
  have hτ : ((.tau : (𝕊).Event)).Obs = false := rfl
  constructor
  · rintro ⟨q, ⟨hp, hlast⟩, hv, htr⟩
    cases hp with
    | nil =>
        obtain ⟨ℓ, hℓ⟩ := hfr
        exact absurd (hlast.2 _ _ (OStep.mach (Head.alloc μ v ℓ hℓ))) (fun h => h)
    | @cons _ ev c₁ q' hst hp' =>
        obtain ⟨ℓ, hℓ, rfl, rfl⟩ := rstep_alloc_inv R K v hst
        refine ⟨ℓ, hℓ, q', ⟨hp', ?_⟩, ?_, ?_⟩
        · rw [← A.EffectSystem.lastC_cons (S := 𝕊) _ _ .tau]
          exact hlast
        · rw [← A.EffectSystem.lastC_cons (S := 𝕊) _ _ .tau]
          exact hv
        · rw [← htr]
          exact (List.filter_cons_of_neg (Bool.eq_false_iff.mp hτ)).symm
  · rintro ⟨ℓ, hℓ, q, ⟨hp, hlast⟩, hv, htr⟩
    have hst : (𝕊).RStep R ((μ, K.plug (allocE v)), s) .tau
        ((μ.upd ℓ v, K.plug (.val (Val.loc ℓ))), s) := by
      have := A.EffectSystem.RStep.mach (R := R) (s := s)
        (OStep.mach (RF := RF) (Ξ := Ξ) (K := K) (Head.alloc (ℍ := ℍ) μ v ℓ hℓ))
      rwa [labelOf_tau_of rfl] at this
    have hc := A.EffectSystem.lastC_cons (S := 𝕊) ((μ, K.plug (allocE v)), s)
      ((μ.upd ℓ v, K.plug (.val (Val.loc ℓ))), s) .tau q
    refine ⟨(.tau, ((μ.upd ℓ v, K.plug (.val (Val.loc ℓ))), s)) :: q, ⟨.cons hst hp, ?_⟩, ?_, ?_⟩
    · exact (congrArg (fun x => (𝕊).IsVal x.1) hc).mpr hlast
    · exact (congrArg (fun x => (𝕊).term x.1 = (𝕊).ret w) hc).mpr hv
    · rw [← htr]
      exact List.filter_cons_of_neg (Bool.eq_false_iff.mp hτ)

theorem obs_cons {R : (𝕊).Runner} (ev : (𝕊).Event) (c : (𝕊).RConf R)
    (q : List ((𝕊).Event × (𝕊).RConf R)) :
    (𝕊).obs ((ev, c) :: q) = [ev].filter Targets.A.Ev.Obs ++ (𝕊).obs q := by
  unfold A.EffectSystem.obs
  simp only [List.map_cons, List.filter_cons, List.filter_nil]
  split <;> rfl

/-- **A head step that keeps every memory and allocates nothing, showing its event**: the
complete runs of its configuration are the step, showing its event if observable, then the complete
runs of the next configuration. -/
theorem obsFrom_head_iff (R : (𝕊).Runner) {μ : Heap} {s : R.St} {K : Kont} {a a' : Expr}
    (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a') (hn : a.allocs = false) (v : OVal)
    (tr : List (𝕊).Event) :
    (𝕊).ObsFrom R ((μ, K.plug a), s) v tr ↔
      ∃ tr', tr = ([labelOf RF Ξ a] : List (𝕊).Event).filter Targets.A.Ev.Obs ++ tr' ∧
        (𝕊).ObsFrom R ((μ, K.plug a'), s) v tr' := by
  constructor
  · rintro ⟨q, ⟨hp, hlast⟩, hv, htr⟩
    cases hp with
    | nil => exact absurd (hlast.2 _ _ (OStep.mach (hh μ))) (fun h => h)
    | @cons _ ev c₁ q' hst hp' =>
        obtain ⟨rfl, rfl⟩ := rstep_det (hh μ) hn hst
        refine ⟨(𝕊).obs q', ?_, q', ⟨hp', ?_⟩, ?_, rfl⟩
        · rw [← htr]; exact obs_cons (R := R) _ _ _
        · rw [← A.EffectSystem.lastC_cons (S := 𝕊) _ _ (labelOf RF Ξ a)]
          exact hlast
        · rw [← A.EffectSystem.lastC_cons (S := 𝕊) _ _ (labelOf RF Ξ a)]
          exact hv
  · rintro ⟨tr', rfl, q, ⟨hp, hlast⟩, hv, htr⟩
    have hc := A.EffectSystem.lastC_cons (S := 𝕊) ((μ, K.plug a), s)
      ((μ, K.plug a'), s) (labelOf RF Ξ a) q
    refine ⟨(labelOf RF Ξ a, ((μ, K.plug a'), s)) :: q,
      ⟨.cons (.mach (OStep.mach (hh μ))) hp, ?_⟩, ?_, ?_⟩
    · exact (congrArg (fun x => (𝕊).IsVal x.1) hc).mpr hlast
    · exact (congrArg (fun x => (𝕊).term x.1 = (𝕊).ret v) hc).mpr hv
    · rw [← htr]; exact obs_cons (R := R) _ _ _

/-- **Along a chain of head steps that keep every memory and allocate nothing**, the complete runs
of its start are the chain's path, showing the chain's observable events, then the complete runs
of its end. -/
theorem obsFrom_chain_obs_iff (R : (𝕊).Runner) {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q e' → ∀ v tr,
      ((𝕊).ObsFrom R ((μ, e), s) v tr ↔
        ∃ tr', tr = (𝕊).obs (chainPath R μ s q) ++ tr' ∧ (𝕊).ObsFrom R ((μ, e'), s) v tr')
  | _, _, _, .nil, v, tr =>
      ⟨fun h => ⟨tr, rfl, h⟩, fun ⟨tr', h₁, h₂⟩ => by
        have : tr = tr' := h₁
        subst this; exact h₂⟩
  | _, _, _, @HeadChain.cons _ _ K a a' e' q hh hn hq, v, tr => by
      refine (obsFrom_head_iff R hh hn v tr).trans ?_
      have hcp : chainPath R μ s ((K, a, a') :: q) =
          (labelOf RF Ξ a, ((μ, K.plug a'), s)) :: chainPath R μ s q := rfl
      constructor
      · rintro ⟨tr₁, rfl, h₁⟩
        obtain ⟨tr₂, rfl, h₂⟩ := (obsFrom_chain_obs_iff R hq v tr₁).1 h₁
        exact ⟨tr₂, by rw [hcp]; erw [obs_cons]; rw [List.append_assoc], h₂⟩
      · rintro ⟨tr₂, rfl, h₂⟩
        exact ⟨_, by rw [hcp]; erw [obs_cons]; rw [List.append_assoc],
          (obsFrom_chain_obs_iff R hq v _).2 ⟨tr₂, rfl, h₂⟩⟩

/-- The release of a cell the allocation added gives back the memory before it. -/
theorem del_upd_fresh {μ : Heap} {ℓ : Loc} (h : μ ℓ = none) (v : Val) : (μ.upd ℓ v).del ℓ = μ := by
  funext k
  by_cases hk : k = ℓ
  · rw [hk, Heap.del_same, h]
  · rw [Heap.del_other hk, Heap.upd_other hk]

/-- Along a quiet run, at every memory, the complete runs of the two ends show the same answers
and traces. -/
theorem obsFrom_quiet_iff (R : (𝕊).Runner) {μ : Heap} {s : R.St} {e e' : Expr}
    (h : Quiet (ℍ := ℍ) e e') (v : OVal) (tr : List (𝕊).Event) :
    (𝕊).ObsFrom R ((μ, e), s) v tr ↔ (𝕊).ObsFrom R ((μ, e'), s) v tr := by
  obtain ⟨q, hc, hf⟩ := h
  refine obsFrom_chain_iff R hc (fun x hx => ?_) v tr
  rw [labelOf_tau_of (hf x hx)]; rfl

/-- The complete runs from a value: the empty run, answering the value, showing nothing. -/
theorem obsFrom_val_iff (R : (𝕊).Runner) {μ : Heap} {s : R.St} (v : Val) (w : OVal)
    (tr : List (𝕊).Event) :
    (𝕊).ObsFrom R ((μ, v.1), s) w tr ↔ w.1 = v.1 ∧ tr = [] := by
  constructor
  · rintro ⟨q, ⟨hp, -⟩, hv, htr⟩
    cases hp with
    | nil => exact ⟨hv.symm, htr.symm⟩
    | cons hst _ => exact (no_rstep_val R v hst).elim
  · rintro ⟨hw, rfl⟩
    exact ⟨[], ⟨.nil, isVal_val μ v⟩, hw.symm, rfl⟩

end Obs

/-! ### Calm runs -/

/-- **`e` reaches `e'` around one fresh cell**: quietly to an allocation of `()`; at every location
`ℓ`, quietly from the allocation's answer `ℓ` to the release of `ℓ`; and quietly from the
release's answer `()` to `e'`. -/
def CellQuiet (e e' : Expr) : Prop :=
  ∃ K₁ : Kont, Quiet (ℍ := ℍ) e (K₁.plug (allocE Val.unit)) ∧
    ∀ ℓ : Loc, ∃ K₂ : Kont,
      Quiet (ℍ := ℍ) (K₁.plug (.val (Val.loc ℓ))) (K₂.plug (freeE (.val (Val.loc ℓ)))) ∧
      Quiet (ℍ := ℍ) (K₂.plug (.val Val.unit)) e'

/-- **`e` reaches `e'` calmly**: by quiet runs and runs around one fresh cell. -/
def Calm : Expr → Expr → Prop :=
  Relation.ReflTransGen fun a b => Quiet (ℍ := ℍ) a b ∨ CellQuiet (ℍ := ℍ) a b

theorem Calm.refl (e : Expr) : Calm (ℍ := ℍ) e e := Relation.ReflTransGen.refl

theorem Calm.trans {e e' e'' : Expr} (h₁ : Calm (ℍ := ℍ) e e') (h₂ : Calm (ℍ := ℍ) e' e'') :
    Calm (ℍ := ℍ) e e'' := Relation.ReflTransGen.trans h₁ h₂

theorem Quiet.calm {e e' : Expr} (h : Quiet (ℍ := ℍ) e e') : Calm (ℍ := ℍ) e e' :=
  Relation.ReflTransGen.single (.inl h)

theorem CellQuiet.calm {e e' : Expr} (h : CellQuiet (ℍ := ℍ) e e') : Calm (ℍ := ℍ) e e' :=
  Relation.ReflTransGen.single (.inr h)

/-- A run around one cell goes under every evaluation context. -/
theorem CellQuiet.plug (K₀ : Kont) {e e' : Expr} (h : CellQuiet (ℍ := ℍ) e e') :
    CellQuiet (ℍ := ℍ) (K₀.plug e) (K₀.plug e') := by
  obtain ⟨K₁, h₁, h₂⟩ := h
  refine ⟨K₀.comp K₁, ?_, fun ℓ => ?_⟩
  · rw [Kont.plug_comp]; exact h₁.plug K₀
  · obtain ⟨K₂, h₃, h₄⟩ := h₂ ℓ
    refine ⟨K₀.comp K₂, ?_, ?_⟩
    · rw [Kont.plug_comp, Kont.plug_comp]; exact h₃.plug K₀
    · rw [Kont.plug_comp]; exact h₄.plug K₀

/-- A calm run goes under every evaluation context. -/
theorem Calm.plug (K₀ : Kont) {e e' : Expr} (h : Calm (ℍ := ℍ) e e') :
    Calm (ℍ := ℍ) (K₀.plug e) (K₀.plug e') := by
  induction h with
  | refl => exact Calm.refl _
  | tail _ hs ih =>
      rcases hs with hs | hs
      · exact ih.trans (hs.plug K₀).calm
      · exact ih.trans (hs.plug K₀).calm

section CalmObs
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- **Around one cell, from a memory with finitely many cells**, the complete runs of the two ends
show the same answers and traces: at every location the allocation may pick, the run releases it
and gives back the memory. -/
theorem obsFrom_cellQuiet_iff (R : (𝕊).Runner) {μ : Heap} {s : R.St} (hf : FinDom μ)
    {e e' : Expr} (h : CellQuiet (ℍ := ℍ) e e') (v : OVal) (tr : List (𝕊).Event) :
    (𝕊).ObsFrom R ((μ, e), s) v tr ↔ (𝕊).ObsFrom R ((μ, e'), s) v tr := by
  obtain ⟨K₁, h₁, h₂⟩ := h
  refine (obsFrom_quiet_iff R h₁ v tr).trans ?_
  refine obsFrom_alloc_iff R K₁ Val.unit (exists_fresh_of_finDom hf)
    (Q := fun v tr => (𝕊).ObsFrom R ((μ, e'), s) v tr) (fun ℓ hℓ v tr => ?_) v tr
  obtain ⟨K₂, h₃, h₄⟩ := h₂ ℓ
  refine (obsFrom_quiet_iff R h₃ v tr).trans ?_
  have hfree : Head (ℍ := ℍ) (μ.upd ℓ Val.unit) (freeE (.val (Val.loc ℓ)))
      ((μ.upd ℓ Val.unit).del ℓ) (.val Val.unit) := Head.free _ ℓ Val.unit (Heap.upd_same _ _ _)
  refine (obsFrom_mstep_iff R hfree rfl (by rw [labelOf_tau_of rfl]; rfl) v tr).trans ?_
  rw [del_upd_fresh hℓ]
  exact obsFrom_quiet_iff R h₄ v tr

/-- **Along a calm run, from a memory with finitely many cells**, the complete runs of the two ends
show the same answers and traces. -/
theorem obsFrom_calm_iff (R : (𝕊).Runner) {μ : Heap} {s : R.St} (hf : FinDom μ) {e e' : Expr}
    (h : Calm (ℍ := ℍ) e e') (v : OVal) (tr : List (𝕊).Event) :
    (𝕊).ObsFrom R ((μ, e), s) v tr ↔ (𝕊).ObsFrom R ((μ, e'), s) v tr := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hs ih =>
      rcases hs with hs | hs
      · exact ih.trans (obsFrom_quiet_iff R hs v tr)
      · exact ih.trans (obsFrom_cellQuiet_iff R hf hs v tr)

/-- **Two terms with a common calm reduct run alike in every evaluation context.**  The
configurations `RunsAlike` reads are reached from the empty memory, so their memories hold finitely
many cells. -/
theorem runsAlike_of_calm {t₁ t₂ t : Expr} (h₁ : Calm (ℍ := ℍ) t₁ t) (h₂ : Calm (ℍ := ℍ) t₂ t) :
    (𝕊).RunsAlike t₁ t₂ := by
  rintro R - P ε A ⟨⟨μ, e⟩, s⟩ (K₀ : Kont) - - hreach hterm v tr
  have hf : FinDom μ := finDom_reach hreach
  change e = K₀.plug t₁ at hterm
  subst hterm
  exact (obsFrom_calm_iff R hf (h₁.plug K₀) v tr).trans
    (obsFrom_calm_iff R hf (h₂.plug K₀) v tr).symm

/-- At a typing system whose reached configurations are closed, two terms run alike when, closed,
they have a common calm reduct. -/
theorem runsAlike_of_live_calm (hL : LiveOK (ℍ := ℍ) RF Ξ J) {t₁ t₂ : Expr}
    (h : closedAt 0 t₁ = true → ∃ t, Calm (ℍ := ℍ) t₁ t ∧ Calm (ℍ := ℍ) t₂ t) :
    (𝕊).RunsAlike t₁ t₂ := by
  intro R hR P ε A c K₀ hA hP hreach hterm
  have hlive : (𝕊).Live c.1 := ⟨P, _, R, c.2, hR, hP, hreach⟩
  have hcl := (hL c.1 hlive).1
  have hterm' : c.1.2 = K₀.plug t₁ := hterm
  rw [hterm'] at hcl
  obtain ⟨t, h₁, h₂⟩ := h (closedAt_plug_inv K₀ hcl)
  exact runsAlike_of_calm h₁ h₂ R hR P ε A c K₀ hA hP hreach hterm

end CalmObs

/-! ### Resuming and cancelling `κ` around its cell -/

/-- The value `κ`'s resume branch leaves after its cell's release: `λy. hnd H K[y]`, before its
substitutions are carried out. -/
def kResV (H : Val) (K : Kont) : Expr :=
  Expr.subst 0 Val.unit (Expr.subst 1 (Val.inj₁ Val.unit)
    (.val (.lam (hndE (H.shift 3 0) ((K.shift 3 0).plug (.var 0))))))

/-- **Resuming `κ` at its cell `ℓ`** reaches the release of `ℓ` quietly, and from the release's
answer reaches `hnd H K[w]` quietly. -/
theorem kappaC_resume_parts (aff : Bool) (ℓ : Loc) (H : Val) (K : Kont) (w : Val) :
    Quiet (ℍ := ℍ) (.app (.app (kappaC aff ℓ H K) (.val (Val.inj₁ .unit))) (.val w))
      ((Kont.appL (Kont.seq .hole (kResV H K)) w).plug (freeE (.val (Val.loc ℓ)))) ∧
    Quiet (ℍ := ℍ) ((Kont.appL (Kont.seq .hole (kResV H K)) w).plug (.val Val.unit))
      (hndE H (K.plug (.val w))) := by
  refine ⟨?_, ?_⟩
  · refine (Quiet.head (.appL .hole w) (fun μ => Head.beta μ _ _) rfl rfl).trans ?_
    refine (Quiet.head (.appL .hole w) (fun μ => Head.case₁ μ Val.unit _ _) rfl rfl).trans ?_
    exact Quiet.head (.appL .hole w) (fun μ => Head.seq μ _) rfl rfl
  · refine (Quiet.head (.appL .hole w) (fun μ => Head.seq μ _) rfl rfl).trans ?_
    have hb := Quiet.head (ℍ := ℍ) .hole (fun μ => Head.beta μ
      (Expr.subst 1 Val.unit (Expr.subst 2 (Val.inj₁ Val.unit)
        (hndE (H.shift 3 0) ((K.shift 3 0).plug (.var 0))))) w) rfl rfl
    rw [kappa_resume_subst] at hb
    exact hb

/-- The term an affine `κ`'s cancel branch leaves after its cell's release:
`ccatch (K†[raise (0, (0, none))])`, before its substitutions are carried out. -/
def kCanE (K : Kont) : Expr :=
  Expr.subst 0 Val.unit (Expr.subst 1 (Val.inj₂ Val.unit)
    (ccatchE ((K.dead.shift 2 0).plug (raiseE (.val (cancelVal none))))))

/-- **Cancelling an affine `κ` at its cell `ℓ`** reaches the release of `ℓ` quietly, and from the
release's answer reaches `κ`'s cancel run quietly. -/
theorem kappaC_cancel_parts (ℓ : Loc) (H : Val) (K : Kont) :
    Quiet (ℍ := ℍ) (.app (kappaC true ℓ H K) (.val (Val.inj₂ .unit)))
      ((Kont.seq .hole (kCanE K)).plug (freeE (.val (Val.loc ℓ)))) ∧
    Quiet (ℍ := ℍ) ((Kont.seq .hole (kCanE K)).plug (.val Val.unit))
      (Targets.cancelOf K) := by
  refine ⟨?_, ?_⟩
  · refine (Quiet.head .hole (fun μ => Head.beta μ _ _) rfl rfl).trans ?_
    refine (Quiet.head .hole (fun μ => Head.case₂ μ Val.unit _ _) rfl rfl).trans ?_
    exact Quiet.head .hole (fun μ => Head.seq μ _) rfl rfl
  · refine (Quiet.head (ℍ := ℍ) .hole (fun μ => Head.seq μ (kCanE K)) rfl rfl).trans ?_
    have e : kCanE K = Targets.cancelOf K := kappa_cancel_subst K _ _
    rw [e]
    exact Quiet.refl _

/-- A run `look` computes, none of whose steps is a finaliser's, is quiet. -/
theorem quiet_of_look (k : ℕ) (e : Expr) (hf : (Targets.lookRun k e).all (fun x => !finHead x.2.1) = true) :
    Quiet (ℍ := ℍ) e (Targets.lookEnd k e) :=
  ⟨Targets.lookRun k e, Targets.lookRun_sound k e, fun x hx => by
    simpa using List.all_eq_true.1 hf x hx⟩

/-- The tag of a linear or affine qualifier makes the catch's `κ` a cell's. -/
theorem kappaAt_tag_cell {q : Qual} (hq : q ≠ .unr) (H : Val) (K : Kont) :
    kappaAt q.tag H K = kappaCell (cellAff q) H K := kappaAt_cell hq H K

end Targets.Inst

end
