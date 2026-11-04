import Core.TreeHandleFwd
import Core.TreePoolSpawnProgs

/-!
# A forwarded stop inside a lend, cancelled, its finaliser performing  `[spec §62]`

Closed programs through `PoolSchedAdequacyT`, each premise discharged, whose root runs the loan task
with a parking finaliser (`LC`) under forwarding handlers (`hFw`), and spawns `C = park (); cancel
()`. Under `HS` (`Core/TreePoolSpawn.lean`):

* `LC` allocates, opens a lend and parks holding the lend cell; `park` passes outward through the
  forwarding handlers to `HS`, the stored continuation holding the handlers' frames;
* `C` cancels the root (`HS`'s `cancel` clause): the unwinding `K†` has the forwarding handlers'
  frames removed, and runs `LC`'s finaliser, which parks again with the lend still open and comes
  back to `HS` as a stored continuation;
* resumed, the finaliser ends the lend and frees the cell; the cancel answers `()` owning nothing.

`rootFwd_cerwpT` is `cerwpT_handle` at one forwarding handler, `rootFwd3_cerwpT` `cerwpT_handleStack`
at three. The forwarding handlers handle a name the task does not perform, so their clauses are
never run; what is exercised is forwarding, the forwarded cancel and its cancel row.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.SchedProgs.FwdProgs
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack
open BoCa.Fig16.Tree.Wp.SchedProgs.Spawn
open BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs
open BoCa.Fig16.Tree.Wp.SchedProgs (compS_empty_left_eq)
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload hndE hndVal capTag clauseAt)

/-- The base frame condition: every valid frame. -/
abbrev Fv : TFrame := fun _ ρf => ResUT.Valid ρf

theorem Fv_mono : TFrame.Mono Fv := fun _ _ _ _ _ hr hv =>
  WitRel.ResUT.Valid.sim (W := rrRel _ _ _) hv hr.rsim

/-- `λx. x`. -/
def idV : Val := Val.lam (.var 0)

/-- **A forwarding handler of the name `nm`**, returning its argument; it has no clauses. -/
def hFw (nm : UInt32) : HFrameT :=
  ⟨nm, Val.pair Val.unit Val.unit, idV, Val.pair Val.unit Val.unit, TS (ℍ := ℍ), QS, Fv⟩

/-- The identity return clause at the root's table and answer. -/
theorem idRet_ok : RetT (ℍ := ℍ) (TS (ℍ := ℍ)) QS QS Fv idV := by
  intro F k w ls O v ρ _ _ _ _ _ ⟨hv, hO, hρ⟩
  subst hv; subst hO; subst hρ
  exact cerwpT_det (post_down TS_down) (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole)
    cerwpT_unit

/-- **A forwarding handler of a name other than `park`'s meets `HandleOKT`** at the root's table:
every operation is forwarded, with its cancel row. -/
theorem hFw_ok (nm : UInt32) (hnm : nm ≠ nP) :
    HandleOKT (ℍ := ℍ) (TS (ℍ := ℍ)) (TS (ℍ := ℍ)) nm (hFw nm).qs (hFw nm).hr (hFw nm).hs QS QS
      Fv := by
  refine ⟨fun m i en _ h => ⟨h, fun _ _ _ _ h' => h'⟩, fun i en h => ?_,
    fun m i en h v w O ρf => ?_, QB_down, TS_down, idRet_ok, fun ⟨i, en, h, _⟩ => ?_,
    fun i en h => ?_⟩
  · exact absurd (TS_some h).1 hnm
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := TS_some h <;> exact Iff.rfl
  · exact absurd (TS_some h).1 hnm
  · exact absurd (TS_some h).1 hnm

theorem stack_ok : ∀ (ns : List UInt32), (∀ nm ∈ ns, nm ≠ nP) →
    StackOKT (ℍ := ℍ) (TS (ℍ := ℍ)) QS (ns.map hFw)
  | [], _ => trivial
  | nm :: ns, h => ⟨hFw_ok nm (h nm (by simp)), Fv_mono, fun _ _ hv => hv,
      stack_ok ns fun x hx => h x (by simp [hx])⟩

theorem top_eq : ∀ (ns : List UInt32),
    HFrameT.topT (TS (ℍ := ℍ)) (ns.map hFw) = TS (ℍ := ℍ) ∧ HFrameT.topQ QS (ns.map hFw) = QS ∧
      HFrameT.topFb Fv (ns.map (hFw (ℍ := ℍ))) = Fv
  | [] => ⟨rfl, rfl, rfl⟩
  | _ :: ns => top_eq ns

/-- **`LC` under a stack of forwarding handlers**, at the root's table, at every index, from the
present frame condition the spawner's resume gives (`fdAt enSpawn () Fv []`). -/
theorem fwdLC_cerwpT (ns : List UInt32) (hns : ∀ nm ∈ ns, nm ≠ nP) (n : Nat) (w : TWd)
    (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT (TS (ℍ := ℍ))) QS Fv
      (fdAt (enSpawn (ℍ := ℍ)) Val.unit Fv ([] : List (FrameRecT w.K))) n w ls []
      (HFrameT.wrap (ns.map (hFw (ℍ := ℍ))) LC) PMap.empty := by
  have h := cerwpT_handleStack _ _ _ _ (stack_ok ns hns) (fun _ _ hv => hv) n (fun _ => False) w
    ls [] LC PMap.empty (fun x hx => by simp [recMask] at hx)
    (LC_cerwpT TS_park TS_down α₀ n _ _ w ls)
  obtain ⟨e₁, e₂, e₃⟩ := top_eq (ℍ := ℍ) ns
  rw [e₁, e₂, e₃] at h
  refine cerwpT_frameCond_rel (fun w₀ O₀ ρf hO₀ hf => ?_) h
  cases hO₀
  exact fdMask_le (fun _ h => h.elim) (hf.2 [] .nil)

theorem wrap_closed : ∀ (ns : List UInt32) (e : Expr) (v : Val), e.subst 0 v = e →
    (HFrameT.wrap (ns.map (hFw (ℍ := ℍ))) e).subst 0 v = HFrameT.wrap (ns.map (hFw (ℍ := ℍ))) e
  | [], _, _, h => h
  | nm :: ns, e, v, h => wrap_closed ns _ v (by
      simp only [hndE, Expr.subst, h]
      repeat (first | rfl | constructor))

/-- **The root**: `let _ = spawn (λ_. park (); cancel ()) in hnd_{ns} LC`, the forwarding
handlers `ns` around `LC`. -/
def rootFwd (ns : List UInt32) : Expr :=
  .app (.lam (HFrameT.wrap (ns.map (hFw (ℍ := ℍ))) LC)) (spawnE thC)

theorem rootFwd_cerwpT (ns : List UInt32) (hns : ∀ nm ∈ ns, nm ≠ nP) (n : Nat) (w : TWd)
    (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT (TS (ℍ := ℍ))) QS Fv (fdMask fun _ => False) n w ls []
      (rootFwd (ℍ := ℍ) ns) PMap.empty :=
  cerwpT_spawnThen (fun j w' ls' Fb' Fe' _ _ => thC_ok j w' ls' Fb' Fe') fun k' _ w' ls' => by
    rw [wrap_closed ns LC Val.unit (LC_closed _)]
    exact fwdLC_cerwpT ns hns k' w' ls'

/-- `(hnd HS root) (HS, [])`. -/
def progFwd (ns : List UInt32) : Expr := progOf (rootFwd (ℍ := ℍ) ns)

theorem progFwd_safe (ns : List UInt32) (hns : ∀ nm ∈ ns, nm ≠ nP) :
    OrDiverges (ℍ := ℍ) (progFwd (ℍ := ℍ) ns) :=
  poolSchedAdequacyT beforeP TS nP qsS stackRet hsS QS QS InvS Fv _ (rootFwd ns)
    (fun _ _ _ _ _ _ h => h.2.2) (fun _ h => by cases h) hs_schedOK (fun _ _ h => h)
    (fun _ _ h => h) fun n => rootFwd_cerwpT ns hns n _ _

/-- **The hardest case, at one forwarding handler, is safe and leak-free, or diverges.** The root
runs `LC` under a handler forwarding `park` and `cancel` to `HS`; `LC` parks holding its lend; `C`
cancels it; the unwinding, the forwarding handler's frame removed, runs `LC`'s finaliser, which
parks again with the lend open, is resumed, ends the lend and frees the cell. -/
theorem progFwdCancel_safe : OrDiverges (ℍ := ℍ) (progFwd (ℍ := ℍ) [7]) :=
  progFwd_safe [7] (by intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide)

/-- **The hardest case through three forwarding handlers.** -/
theorem progFwdCancel3_safe : OrDiverges (ℍ := ℍ) (progFwd (ℍ := ℍ) [7, 8, 9]) :=
  progFwd_safe [7, 8, 9] (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> decide)

/-! ### A clause that cancels -/

/-- The name of the cancelling handler's operation. -/
abbrev nC : UInt32 := 11

/-- The clause `λ(h, κ). hnd h (κ (inj₂ ()))`: cancel the stored continuation under the handler
`h` the payload names. -/
def clC : Val := Val.lam (.letpair (.var 0)
  (.app (.app (.prim .hnd) (.var 1)) (.app (.var 0) (.inj₂ .unit))))

def qsC : Val := Val.pair (Val.i32 1) Val.unit
def hsC : Val := Val.pair clC Val.unit
/-- **The cancelling handler**: every stop at `nC` is cancelled, its unwinding run under the
handler again. -/
def HC : Val := hndVal nC qsC idV hsC

/-- `nC`: cancellable, its cancel owed; the payload the handler; its unwinding may perform `nC`. -/
def enC : OpEntT where
  q := .cancel
  abort := false
  PA := fun _ _ _ v ρ => v = HC ∧ ρ = PMap.empty
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ σ = PMap.empty
  fin := true
  fd := fdJoinT
  oc := fun _ O => O = []
  cn := fun m i => m = nC ∧ i = 0

def TCk : OpTabT := fun m i => if m = nC ∧ i = 0 then some enC else none

theorem TCk_some {m i : UInt32} {en : OpEntT} (h : TCk m i = some en) :
    m = nC ∧ i = 0 ∧ en = enC := by
  unfold TCk at h
  split at h
  · rename_i hm; cases h; exact ⟨hm.1, hm.2, rfl⟩
  · cases h

theorem PADown_empty : PADown OpTabT.empty := fun _ _ _ h => by cases h

theorem retC_ok (Fbo : TFrame) : RetT (ℍ := ℍ) OpTabT.empty Qunit Qunit Fbo idV := by
  intro F k w ls O v ρ _ _ _ _ _ ⟨hv, hO, hρ⟩
  subst hv; subst hO; subst hρ
  exact cerwpT_det (cerwpPostT_down (fun _ _ _ _ _ _ h => h) PADown_empty)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) cerwpT_unit

/-- **The clause cancels the stored continuation under the handler**: `KapT`'s cancel, one step
below. -/
theorem clC_ok (Fbo : TFrame) : ClauseT (ℍ := ℍ) OpTabT.empty HC Qunit Fbo enC clC := by
  rintro F k w ls O v κ ρ hFm hoc hFM hcov hls _ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  change O = [] at hoc
  subst hoc
  obtain rfl := compS_empty_left_eq hc
  cases k with
  | zero => exact cerwpT_zero
  | succ k₀ =>
  have h := hκ.2.2 w ρ ls [] (TWd.Ext.refl _ _) (RR.refl hcov)
    (KeepRel.of_srecsRR (SRecsRR.refl hls) _) .nil (by decide) rfl k₀ (by omega) F hFm hFM
  rw [cerwpT_eq]
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (Val.pair HC κ)) rfl .hole) ?_
  simp only [Kont.plug, Expr.subst]
  refine twp_det (cerwpPostT_down (fun _ _ _ _ _ _ h => h) PADown_empty)
    (fun μ => step1Only_plug (Head.letpair μ HC κ _) rfl .hole) ?_
  have e₂ : Expr.subst 0 HC (Expr.shift 1 0 κ.1) = κ.1 := by
    rw [Expr.subst_shift 0 0 0 HC κ.1 (le_refl 0) (le_refl 0), Expr.shift_zero]
  have h' := cerwpT_unfold_at (opTableT_local _) (Nat.le_succ k₀) h
  convert h' using 2
  simp [Kont.plug, Expr.subst, hndE, Val.shift, e₂]

/-- **The cancelling handler meets `HandleOKT`** at the empty outer table, its operation
cancellable, so its return clause is asked at `Qunit` too. -/
theorem handleC_ok (Fbo : TFrame) :
    HandleOKT (ℍ := ℍ) TCk OpTabT.empty nC qsC idV hsC Qunit Qunit Fbo := by
  refine ⟨fun m i en hm h => absurd (TCk_some h).1 hm, fun i en h _ => ?_,
    fun m i en h v w O ρf => ?_, fun _ _ _ _ _ _ h => h, PADown_empty, retC_ok Fbo,
    fun _ => retC_ok Fbo, fun i en h => ?_⟩
  · obtain ⟨-, rfl, rfl⟩ := TCk_some h; rfl
  · obtain ⟨-, -, rfl⟩ := TCk_some h; exact Iff.rfl
  · obtain ⟨-, rfl, rfl⟩ := TCk_some h
    exact ⟨clC, by simp [clauseAt, hsC, Val.pair, clC, Val.lam, IsVal.lam], clC_ok Fbo⟩

theorem TCk_cancels : TCk.Cancels nC := ⟨0, enC, by simp [TCk], by decide, rfl⟩

end BoCa.Fig16.Tree.Wp.SchedProgs.FwdProgs

end
