import HandleSpike.ParamProgs
import Core.TreeCactus

/-!
# Spike (#792): cancel-as-resume at the canceller-parametric share

The scheduler `HC` (name `nS`) has one cancellable operation `park`, whose payload is the
scheduler itself. Its clause cancels the stopped task under the scheduler again:

  `λ(h, κ). hnd h (κ (inj₂ ()))`

The task is `ubind (λ_. (), D) (park HC)` with the finaliser `D = λ_. ubind (λ_. (), λ_. ()) (park HC)`.
Under `HC`: the task parks; the clause cancels it under `HC`; the unwinding runs `D`, which parks
again at `HC`'s operation; the park comes back to `HC`'s clause as an ordinary stored continuation
(`KapP` at its stop); the clause cancels it again; the inner finaliser answers, the cancels are
caught, and the program answers `()` (`cancel_as_resume`), safe or diverging
(`cancel_as_resume_safe`, through `cerwpT_adequacy`).

The task proves its cancel at every canceller whose table has `park` (`task_ok`), not at `HC`'s
particular table; `cerwpP_handle` chooses the canceller (the inner table) when `HC`'s clause
cancels.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.HandleSpike.Param.PCancel
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.HandleSpike
open BoCa.Fig16.Tree.Wp.HandleSpike.Param
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.Tree.Wp.SchedProgs (compS_empty_left_eq)
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE hndVal capTag
  clauseAt ccatchE)

abbrev nS : UInt32 := 3

/-! ### The scheduler -/

/-- The clause `λ(h, κ). hnd h (κ (inj₂ ()))`. -/
def clC : Val := Val.lam (.letpair (.var 0)
  (.app (.app (.prim .hnd) (.var 1)) (.app (.var 0) (.inj₂ .unit))))

def qsC : Val := Val.pair (Val.i32 1) Val.unit
def hsC : Val := Val.pair clC Val.unit
def HC : Val := hndVal nS qsC Inst.idV hsC

/-- `park`: cancellable, its cancel owed; the payload the scheduler; the finaliser may park. -/
def enPkE : OpEntT where
  q := .cancel
  abort := false
  PA := fun _ _ _ v ρ => v = HC ∧ ρ = PMap.empty
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ σ = PMap.empty
  fin := true
  fd := fdJoinT
  oc := fun _ O => O = []

def enPk : OpEntP := ⟨enPkE, fun m i => m = nS ∧ i = 0⟩

def TC : OpTabP := fun m i => if m = nS ∧ i = 0 then some enPk else none

theorem TC_some {m i : UInt32} {en : OpEntP} (h : TC m i = some en) :
    m = nS ∧ i = 0 ∧ en = enPk := by
  unfold TC at h
  split at h
  · rename_i hm; cases h; exact ⟨hm.1, hm.2, rfl⟩
  · cases h

theorem TC_PA : PADown TC := fun _ _ _ h _ _ _ _ _ hA => by
  obtain ⟨-, -, rfl⟩ := TC_some h; exact hA

/-! ### The task -/

/-- `λ_. ()`. -/
def Nu : Val := Val.lam (Val.unit).1
def ubK (N D : Val) : Kont := .appR (.app (.prim .ubind) (Val.pair N D).1) .hole
def ccK : Kont := .appR (.prim .ccatch) .hole
def cfK2 : Kont := .appR (.prim .ccatch) (.appR (.app (.prim .cfin) (cancelVal none).1) .hole)
def K4 : Kont := .appR (.prim .ccatch) (.appR (.app (.prim .cfin) (cancelVal none).1)
  (.appR (.app (.prim .cfin) (cancelVal none).1) .hole))
/-- The finaliser's park in its frames: `ccatch (cfin c (ubind (N, N) [·]))`. -/
def K3 : Kont :=
  .appR (.prim .ccatch) (.appR (.app (.prim .cfin) (cancelVal none).1) (ubK Nu Nu))

def parkC : Expr := performE (.val (opPayload nS 0 HC))
def D : Val := Val.lam ((ubK Nu Nu).plug parkC)
def eTask : Expr := (ubK Nu D).plug parkC

theorem D_beta : ((ubK Nu Nu).plug parkC).subst 0 Val.unit = (ubK Nu Nu).plug parkC := by
  simp [ubK, Nu, parkC, HC, hsC, clC, qsC, hndVal, Inst.idV, Expr.subst, Kont.plug, performE,
    opPayload]
  repeat (first | rfl | constructor)

theorem nu_beta : ((Val.unit).1).subst 0 Val.unit = (Val.unit).1 := rfl

/-- **The inner finaliser's cancel**, at every downward-closed canceller: `ubind (N, N)`'s cancel
runs `N ()`, and the cancels are caught. -/
theorem fin2_ok {T'' : OpTabP} (hPA : PADown T'') {Fb F : TFrame} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} :
    cerwpP (ℍ := ℍ) T'' Qunit Fb F n w ls [] (cancelE K3) PMap.empty := by
  have hD := fun e e' (h : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') =>
    @cerwpP_det ℍ _ T'' Qunit Qunit_down hPA Fb F n w ls [] e e' PMap.empty h
  refine hD _ _ (fun μ => step1Only_plug (Head.ufinC μ Nu Nu none .hole rfl) rfl cfK2) ?_
  refine hD _ _ (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl K4) ?_
  refine hD _ _ (fun μ => step1Only_plug (Head.cfret μ none Val.unit) rfl cfK2) ?_
  refine hD _ _ (fun μ => step1Only_plug (Head.cfcancel μ none none .hole rfl) rfl ccK) ?_
  refine hD _ _ (fun μ => step1Only_plug (Head.cancel μ .hole rfl) rfl .hole) ?_
  exact cerwpP_unit

/-- **The finaliser `D`'s run under any canceller with `park`**: it parks again; resumed, `N`
answers and the cancel is caught; cancelled again, `fin2_ok`. -/
theorem fin1_ok {T' : OpTabP} (hT : T' nS 0 = some enPk) (hPA : PADown T') {Fb F : TFrame}
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} :
    cerwpP (ℍ := ℍ) T' Qunit Fb F n w ls [] (cancelE (ubK Nu D)) PMap.empty := by
  have hD := fun e e' (h : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') =>
    @cerwpP_det ℍ _ T' Qunit Qunit_down hPA Fb F n w ls [] e e' PMap.empty h
  refine hD _ _ (fun μ => step1Only_plug (Head.ufinC μ Nu D none .hole rfl) rfl ccK) ?_
  refine hD _ _ (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl cfK2) ?_
  rw [D_beta]
  show cerwpP (ℍ := ℍ) T' Qunit Fb F n w ls [] (K3.plug parkC) PMap.empty
  refine cerwpP_perform K3 rfl hT rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  obtain rfl := RR.of_empty hr
  refine ⟨rfl, PMap.empty, PMap.empty, ResUT.compS_empty_right _, ⟨rfl, rfl⟩,
    fun h => absurd h (by simp [enPk, enPkE]), ?_⟩
  intro w' ρ' ls' O' _ hr' _ hO'
  obtain rfl := RR.of_empty hr'
  cases hO'
  refine ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun _ _ k' hk' T'' Fb'' hT'' _ => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := compS_empty_left_eq hcσ
    simp only [cerwpPC, hk', if_true]
    have hD' := fun e e' (h : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') =>
      @cerwpP_det ℍ _ T' Qunit Qunit_down hPA Fb (fdAt enPk.e Val.unit Fb ([] : List (FrameRecT w'.K)))
        k' w' ls' [] e e' PMap.empty h
    refine hD' _ _ (fun μ => step1Only_plug (Head.uthen μ Nu Nu Val.unit) rfl cfK2) ?_
    refine hD' _ _ (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl cfK2) ?_
    refine hD' _ _ (fun μ => step1Only_plug (Head.cfret μ none Val.unit) rfl ccK) ?_
    refine hD' _ _ (fun μ => step1Only_plug (Head.cancel μ .hole rfl) rfl .hole) ?_
    exact cerwpP_unit
  · simp only [cerwpPK, hk', if_true]
    exact fin2_ok hT''.2

/-- **The task at `TC`**, its cancel proved at every canceller whose table has `park`. -/
theorem task_ok (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpP (ℍ := ℍ) TC Qunit Fb F n w ls [] eTask PMap.empty := by
  refine cerwpP_perform (ubK Nu D) rfl (show TC nS 0 = some enPk by simp [TC]) rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  obtain rfl := RR.of_empty hr
  refine ⟨rfl, PMap.empty, PMap.empty, ResUT.compS_empty_right _, ⟨rfl, rfl⟩,
    fun h => absurd h (by simp [enPk, enPkE]), ?_⟩
  intro w' ρ' ls' O' _ hr' _ hO'
  obtain rfl := RR.of_empty hr'
  cases hO'
  refine ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun _ _ k' hk' T' Fb' hT' _ => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := compS_empty_left_eq hcσ
    simp only [cerwpPC, hk', if_true]
    refine cerwpP_det Qunit_down TC_PA
      (fun μ => step1Only_plug (Head.uthen μ Nu D Val.unit) rfl .hole) ?_
    exact cerwpP_det Qunit_down TC_PA (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole)
      cerwpP_unit
  · simp only [cerwpPK, hk', if_true]
    have hT : T' nS 0 = some enPk := hT'.1 nS 0 enPk ⟨rfl, rfl⟩ (by simp [TC])
    exact fin1_ok hT hT'.2

/-! ### The scheduler meets `HandleOKP` -/

theorem ret_ok (Fbo : TFrame) : RetP (ℍ := ℍ) OpTabP.empty Qunit Qunit Fbo Inst.idV := by
  intro F k w ls O v ρ _ _ _ _ _ ⟨hv, hO, hρ⟩
  subst hv; subst hO; subst hρ
  exact cerwpP_det Qunit_down PADown.empty
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) cerwpP_unit

/-- **The clause cancels the stored task under the scheduler**: `KapP`'s cancel clause, one step
below. -/
theorem clC_ok (Fbo : TFrame) :
    ClauseP (ℍ := ℍ) OpTabP.empty HC Qunit Fbo enPk clC := by
  rintro F k w ls O v κ ρ hFm hoc hFM hcov hls _ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  change O = [] at hoc
  subst hoc
  obtain rfl := compS_empty_left_eq hc
  cases k with
  | zero => rw [cerwpP_eq]; exact twp_zero
  | succ k₀ =>
  have h := hκ.2.2 w ρ ls [] (TWd.Ext.refl _ _) (RR.refl hcov)
    (KeepRel.of_srecsRR (SRecsRR.refl hls) _) .nil (by decide) rfl k₀ (by omega) F hFm hFM
  rw [cerwpP_eq]
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (Val.pair HC κ)) rfl .hole) ?_
  simp only [Kont.plug, Expr.subst]
  refine twp_det (postP_down Qunit_down PADown.empty)
    (fun μ => step1Only_plug (Head.letpair μ HC κ _) rfl .hole) ?_
  have e₂ : Expr.subst 0 HC (Expr.shift 1 0 κ.1) = κ.1 := by
    rw [Expr.subst_shift 0 0 0 HC κ.1 (le_refl 0) (le_refl 0), Expr.shift_zero]
  have h' := cerwpP_unfold_at (Nat.le_succ k₀) h
  convert h' using 2
  simp [Kont.plug, Expr.subst, hndE, Val.shift, e₂]

theorem handle_ok (Fbo : TFrame) :
    HandleOKP (ℍ := ℍ) TC OpTabP.empty nS qsC Inst.idV hsC Qunit Qunit Fbo := by
  refine ⟨fun m i en hm h => absurd (TC_some h).1 hm, fun i en h _ => ?_,
    fun m i en h v w O ρf => ?_, Qunit_down, PADown.empty, TC_PA, ret_ok Fbo, ret_ok Fbo,
    fun i en h => ?_⟩
  · obtain ⟨-, rfl, rfl⟩ := TC_some h; rfl
  · obtain ⟨-, -, rfl⟩ := TC_some h; exact Iff.rfl
  · obtain ⟨-, rfl, rfl⟩ := TC_some h
    exact ⟨clC, by simp [clauseAt, hsC, Val.pair, clC, Val.lam, IsVal.lam], clC_ok Fbo⟩

/-! ### The program -/

theorem empty_mono : TFrame.Mono (fun w ρf => ρf = (PMap.empty : TRes w.K)) :=
  fun _ _ _ _ _ hr h => by subst h; exact RR.of_empty hr

/-- **Cancel-as-resume at the parametric share**: `hnd HC eTask` at the empty table, answering
`()` owning nothing, at every index. -/
theorem cancel_as_resume (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpP (ℍ := ℍ) OpTabP.empty Qunit (fun w ρf => ρf = (PMap.empty : TRes w.K))
      (fun w ρf => ρf = (PMap.empty : TRes w.K)) n w ls [] (hndE HC eTask) PMap.empty :=
  cerwpP_handle (handle_ok _) empty_mono n Qunit (ret_ok _) (fun _ => False) _
    (fun _ ρf => ResUT.Valid ρf) (fdMask fun _ => False) w ls [] eTask PMap.empty empty_mono
    (fun w _ h => by subst h; exact fdMask_empty _ w) (fun x hx => by simp [recMask] at hx)
    (fun _ _ hv => hv) (fun _ _ h => h) (task_ok n _ _ w ls)

/-- At the empty table the two relations agree: no stop is allowed at either. -/
theorem cerwpP_empty_cerwpT {Q : TPostV} {Fb F : TFrame} : ∀ (n : Nat) {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K},
    cerwpP (ℍ := ℍ) OpTabP.empty Q Fb F n w ls O e ρ →
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Q Fb F n w ls O e ρ := by
  intro n w ls O e ρ h
  rw [cerwpP_eq] at h
  rw [cerwpT_eq]
  refine twp_mono (fun k w' ls' O' t ρ' ht => ?_) h
  rcases ht with ht | ⟨_, _, _, _, _, _, _, hT, _⟩
  · exact Or.inl ht
  · simp [OpTabP.empty] at hT

/-- **The program is safe and leak-free, or diverges.** -/
theorem cancel_as_resume_safe (P : ParentFn) : OrDiverges (ℍ := ℍ) (hndE HC eTask) :=
  cerwpT_adequacy P (fun _ _ _ _ _ _ h => h.2.2) fun n =>
    cerwpP_empty_cerwpT n (cancel_as_resume n _ [])

end BoCa.Fig16.Tree.Wp.HandleSpike.Param.PCancel

end
