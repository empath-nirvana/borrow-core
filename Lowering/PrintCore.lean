import Lowering.PrintFwd
import Lowering.Print
import Lowering.OwnLow

/-!
# Lowering — the print's simulation on the core fragment  `[spec §56]`

`lirOf` (`Lowering/LIRPrint.lean`) prints a closed term of the core fragment (`coreB`: no
location, no primitive other than literals and host operations) whose only constants are `copy`
and `forget` (`explicitB isCF`). Its simulation (`printSimAt_lirOf`) is the forward simulation
(`fwd`) of the source's run, which a term in the relation at `F 1` has (`every_run_of_sem`): the
interpreter answers `()` from some fuel on, and at every fuel answers it or runs out of fuel, so it
never faults. The run leaves no object: the print allocates none.

`own_printSimOn` is `PrintSim` for `own` and `printOwn` on the checked programs with no pin, in
the pure fragment, whose lowered term is core with only `copy` and `forget` as constants;
`own_lir_every_run` composes it with `own_lowerSem` and `own_lowersInto`. `bindChecked`
(`return () to x. return x`) is in the class.
-/

namespace Lowering
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Check Frontend.Check
open BoCa.Lifetime (LifeCtx)
open Backend2 (Prog LV St)

local instance : HostIs Backend2.lirHost := ⟨⟩

/-- **The print's simulation on a class `P` of checked programs.** -/
def PrintSimOn (Site : Checked → Expr → Prop) (P : Checked → Prop) (lower : TExpr → Expr)
    (print : Checked → Prog) : Prop :=
  ∀ c : Checked, P c → c.ctx = [] → c.C = .ret .unit → LowExpr (Site c) 0 (lower c.t) →
    PrintSimAt (ℍ := Backend2.lirHost) (lower c.t) (print c)

/-- **The print of a closed core term in the relation at `F 1` is simulated.** -/
theorem printSimAt_lirOf (e : Expr) (hc : coreB e = true) (hx : explicitB isCF e = true)
    (hcl : ∀ k, mentions e k = false)
    (hsem : SemC (ℍ := Backend2.lirHost) LifeCtx.empty [] e (.ret .unit)) :
    PrintSimAt (ℍ := Backend2.lirHost) e (lirOf e) := by
  obtain ⟨N, n', hpr, hn', hN2, hty⟩ := lirOf_pr e hc
  have hs := every_run_of_sem hsem (.refl _ _)
  obtain ⟨k, hbig⟩ := big_of_steps hs (w := Val.unit) rfl hc
  have hbig' : BigN (ℍ := Backend2.lirHost) k Adequacy.emptyMem (Expr.psub 0 [] e)
      Adequacy.emptyMem Val.unit := by
    rw [Adequacy.psub_nil 0 e]; exact hbig
  have hbud : BudOK e (fun _ => 0) := fun k => by
    obtain ⟨u, hu, hb⟩ := occ_unmentioned e k (hcl k)
    exact ⟨u, hu, hb.1, hb.2⟩
  have hfr : FrameOK (lirOf e) N [] (fun _ => 0) 0 (fun _ => 0) (lirInit (lirOf e)).frame :=
    ⟨fun x v hx => by simp [lirInit] at hx, fun _ => Nat.zero_le _,
      fun _ h => absurd h (by decide), fun _ _ h => absurd h (by decide)⟩
  obtain ⟨v, F', hv, -, -, -, hsim⟩ := fwd hty hN2 k _ _ _ _ _ hpr hn' [] (fun _ => 0)
    (lirInit (lirOf e)) _ _ _ k le_rfl hbig' hx hc hbud hfr (lirOf e).mainTy
  have hvu := vrel_unit_inv hv
  subst hvu
  refine ⟨⟨fun w v => w = Val.unit ∧ v = .unit, fun μ s => μ = Adequacy.emptyMem ∧
      s.objs.isEmpty = true, fun _ h => h.2, fun _ h => h.2⟩, ?_, ?_, ?_⟩
  · intro fuel msg hrun hmsg
    rcases hsim.1 fuel with h | h
    · exact absurd (hrun.symm.trans h) (by simp)
    · exact absurd (by rw [lirRun] at hrun; rw [hrun] at h; cases h; rfl) hmsg
  · intro fuel v s hrun
    rcases hsim.1 fuel with h | h
    · have h' : lirRun (lirOf e) fuel = _ := h
      rw [hrun] at h'
      cases h'
      exact ⟨_, Val.unit, hs, ⟨rfl, rfl⟩, rfl, by simp [lirInit]⟩
    · have h' : lirRun (lirOf e) fuel = _ := h
      rw [hrun] at h'; cases h'
  · intro _ _ _
    obtain ⟨F₀, hF⟩ := hsim.2
    exact ⟨F₀, _, _, hF F₀ le_rfl⟩

/-- **`PrintSim` for `own` and `printOwn`** on the checked programs with no pin, in the pure
fragment, whose lowered term is core with only `copy` and `forget` as constants. -/
theorem own_printSimOn :
    PrintSimOn (fun _ => noSite) (fun c => c.pins = [] ∧ coreB (own c.t) = true ∧
      explicitB isCF (own c.t) = true) own printOwn := by
  rintro c ⟨hp, hc, hx⟩ hΓ hC hlow
  have hsem := own_lowerSem (ℍ := Backend2.lirHost) c hp
  rw [hΓ, hC] at hsem
  exact printSimAt_lirOf _ hc hx (fun k => hlow.closed k (Nat.zero_le _)) hsem

/-- **End to end on the core fragment**: a checked closed `main : F 1` with no pin, in the pure
fragment, whose lowered term is core with only `copy` and `forget` as constants, runs every time
at the LIR when printed: no fault, an answer, and every answer `()` with no live object. -/
theorem own_lir_every_run (c : Checked) (hp : c.pins = []) (hΓ : c.ctx = [])
    (hC : c.C = .ret .unit) (hpure : pureT c.t = true) (hc : coreB (own c.t) = true)
    (hx : explicitB isCF (own c.t) = true) : LIREveryRun (printOwn c) := by
  have hsem := own_lowerSem (ℍ := Backend2.lirHost) c hp
  have hlow := own_lowersInto c ⟨hΓ, hpure⟩
  rw [hΓ] at hlow
  have hsim := own_printSimOn c ⟨hp, hc, hx⟩ hΓ hC hlow
  rw [hΓ, hC] at hsem
  exact lir_every_run_of_sem hsem hsim

/-! ### Non-vacuity -/

/-- `return () to x. return x`, a computation of `F 1`. -/
def bindMain : TExpr :=
  .bind default (.comp (.ret .unit)) .unit (.ret .unit) ⟨[]⟩
    (.ret default (.comp (.ret .unit)) .unit (.unitI default (.val .unit)))
    (.ret default (.comp (.ret .unit)) .unit (.var default (.val .unit) 0 .unit))

theorem bindCovers : Covers (Masks.mk []).u₁ 0 (TExpr.ret default (.comp (.ret .unit)) .unit
      (.unitI default (.val .unit))).erase ∧
    Covers (Masks.mk []).u₂ 1 (TExpr.ret default (.comp (.ret .unit)) .unit
      (.var default (.val .unit) 0 .unit)).erase :=
  ⟨fun k hk => by simp [TExpr.erase, ClauseKinds.mentions, Expr.val, Val.unit] at hk,
    fun k hk => by simp [TExpr.erase, ClauseKinds.mentions] at hk⟩

theorem bindMain_typedAt (Ξ : EffCtx) :
    TDerivesAt Ξ LifeCtx.empty [] bindMain (.comp (.ret .unit)) :=
  .bind .nil .nil bindCovers (.ret (.unitI .nil)) (.ret (.var (.here .nil)))

theorem bindMain_typedP : TDerivesP LifeCtx.empty [] bindMain (.comp (.ret .unit)) :=
  .bind .nil .nil bindCovers (.ret (.unitI .nil)) (.ret (.var (.here .nil)))

/-- The checked `main` `return () to x. return x`. -/
def bindChecked : Checked where
  ctx := []
  t := bindMain
  C := .ret .unit
  sigs := []
  ok := rfl
  pins := []
  tied := ⟨fun _ Ξ _ => bindMain_typedAt Ξ, bindMain_typedP⟩
  cells := []
  cellsOk := rfl

/-- **Non-vacuity**: `bindChecked` meets `own_lir_every_run`'s hypotheses. -/
theorem bindChecked_lir_every_run : LIREveryRun (printOwn bindChecked) :=
  own_lir_every_run bindChecked rfl rfl rfl (by decide) (by decide) (by decide)

end Lowering
