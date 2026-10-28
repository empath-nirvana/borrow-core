import Lowering.PrintCall
import Lowering.PrintTotal
import Lowering.OwnLow
import Lowering.OwnSem
import Core.Examples

/-!
# Lowering — the print's simulation  `[spec §56]`

`lirOf` (`Lowering/LIRPrint.lean`) prints a closed term with no effect primitive. Its simulation
(`printSimAt_lirOf`) follows the source's run under the LIR's allocator (`bumpAlloc`), which a
closed `F 1` term in the relation has (`arun_of_sem`): the interpreter answers `()` from some fuel
on, and at every fuel answers it or runs out of fuel, so it never faults. The memories correspond
(`HRel`) from the empty memory to the end, so the run leaves no live object.

`own_printSimOn` is `PrintSim` for `own` and `printOwn` on the checked programs with no pin
(`PrintSimOn`), and `own_printSim_pin` is `PrintSim` itself under `PinLaw`. `own_lir_every_run`:
every checked closed `main : F 1` with no pin whose term is in the pure fragment (`pureT`) runs
every time at the LIR; `own_lir_every_run_pin`, every one in the pure fragment, under `PinLaw`.
-/

noncomputable section

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

theorem objs_empty {s : St} (h : ∀ a : Nat, s.objs[a]? = none) : s.objs.isEmpty = true := by
  rw [Std.HashMap.isEmpty_iff_forall_not_mem]
  intro x hx
  rw [Std.HashMap.mem_iff_isSome_getElem?, h x] at hx
  simp at hx

/-- The LIR's initial state and the empty memory correspond at the allocation count `0`. -/
theorem hrel_init (p : Prog) (N : Nat) : HRel p N 0 Adequacy.emptyMem (lirInit p) := by
  refine ⟨?_, fun a => ?_, fun a v h => ?_, fun a => ?_, fun a h => ?_⟩
  · simp [lirInit, regionBase]
  · simp [lirInit, Adequacy.emptyMem]
  · simp [Adequacy.emptyMem] at h
  · simp [lirInit, Adequacy.emptyMem]
  · simp [Adequacy.emptyMem] at h

theorem heapEF_empty : HeapEF Adequacy.emptyMem := fun _ _ h => by
  simp [Adequacy.emptyMem] at h

/-- **The print of a closed effect-free term in the relation at `F 1` is simulated.** -/
theorem printSimAt_lirOf (e : Expr) (hef : effFreeB e = true) (hcl : ∀ k, mentions e k = false)
    (hsem : SemC (ℍ := Backend2.lirHost) LifeCtx.empty [] e (.ret .unit)) :
    PrintSimAt (ℍ := Backend2.lirHost) e (lirOf e) := by
  obtain ⟨N, n', hpr, hn', hN, hrt, hty⟩ := lirOf_pr e hef
  obtain ⟨c', hrun⟩ := arun_of_sem hsem bumpAlloc
  obtain ⟨k, hbig⟩ := big_of_arun hrun (w := Val.unit) rfl hef heapEF_empty
  have hbig' : BigN (ℍ := Backend2.lirHost) bumpAlloc k 0 Adequacy.emptyMem (Expr.psub 0 [] e) c'
      Adequacy.emptyMem Val.unit := by
    rw [Adequacy.psub_nil 0 e]; exact hbig
  have hfr : FrameOK (lirOf e) N [] (fun _ => 0) 0 (need e noOut) (lirInit (lirOf e)).frame :=
    ⟨fun x v hx => by simp [lirInit] at hx, fun k hk => by simp [need, noOut, hcl k] at hk,
      fun k _ hk => by simp [need, noOut, hcl k] at hk⟩
  obtain ⟨v, s', hv, hh', -, hsim⟩ := (fwd_all hty hN hrt k).1 _ _ _ _ _ _ hpr hn' []
    (lirInit (lirOf e)) 0 Adequacy.emptyMem c' Adequacy.emptyMem Val.unit k (le_refl k) hbig' hfr
    (hrel_init _ N)
  have hvu := vrel_unit_inv hv
  subst hvu
  have hobjs : s'.objs.isEmpty = true := objs_empty fun a => by
    rw [hh'.objs a]; simp [Adequacy.emptyMem]
  have hs := (hsim (lirOf e).mainTy)
  refine ⟨⟨fun w v => w = Val.unit ∧ v = .unit, fun μ s => μ = Adequacy.emptyMem ∧
      s.objs.isEmpty = true, fun _ h => h.2, fun _ h => h.2⟩, ?_, ?_, ?_⟩
  · intro fuel msg hrun' hmsg
    rcases hs.1 fuel with h | h
    · exact absurd (hrun'.symm.trans h) (by simp)
    · exact absurd (by rw [lirRun] at hrun'; rw [hrun'] at h; cases h; rfl) hmsg
  · intro fuel v s hrun'
    rcases hs.1 fuel with h | h
    · have h' : lirRun (lirOf e) fuel = _ := h
      rw [hrun'] at h'
      cases h'
      exact ⟨_, Val.unit, hrun.toSteps, ⟨rfl, rfl⟩, rfl, hobjs⟩
    · have h' : lirRun (lirOf e) fuel = _ := h
      rw [hrun'] at h'; cases h'
  · intro _ _ _
    obtain ⟨F₀, hF⟩ := hs.2
    exact ⟨F₀, _, _, hF F₀ le_rfl⟩

/-- A term with effect primitives only at no site has none. -/
theorem effFreeB_of_noSite : ∀ {e : Expr}, EffOnlyAt noSite e → effFreeB e = true := by
  intro e h
  induction h with
  | site h => exact h.elim
  | var _ | unit | loc _ => rfl
  | prim h => simp [effFreeB, h]
  | pair _ _ iha ihb | seq _ _ iha ihb | app _ _ iha ihb | letpair _ _ iha ihb =>
      simp [effFreeB, iha, ihb]
  | inj₁ _ ih | inj₂ _ ih | lam _ ih => simpa [effFreeB] using ih
  | case _ _ _ ihs iha ihb => simp [effFreeB, ihs, iha, ihb]

/-- **`PrintSim` for `own` and `printOwn`** on the checked programs with no pin: every one whose
lowered term is low (at no site) has its print simulated. -/
theorem own_printSimOn :
    PrintSimOn (fun _ => noSite) (fun c => c.pins = []) own printOwn := by
  intro c hp hΓ hC hlow
  have hsem := own_lowerSem (ℍ := Backend2.lirHost) c hp
  rw [hΓ, hC] at hsem
  exact printSimAt_lirOf _ (effFreeB_of_noSite hlow.effects) (fun k => hlow.closed k (Nat.zero_le _))
    hsem

/-- **`PrintSim` for `own` and `printOwn`, under `PinLaw`**: every checked closed `main : F 1`
whose lowered term is low (at no site). -/
theorem own_printSim_pin (hPin : PinLaw (ℍ := Backend2.lirHost)) :
    PrintSim (ℍ := Backend2.lirHost) (fun _ => noSite) own printOwn := by
  intro c hΓ hC hlow
  have hsem := own_lowerSemRel (ℍ := Backend2.lirHost) c (checked_sem_pin hPin c)
  rw [hΓ, hC] at hsem
  exact printSimAt_lirOf _ (effFreeB_of_noSite hlow.effects) (fun k => hlow.closed k (Nat.zero_le _))
    hsem

/-- **End to end on the pure fragment**: every checked closed `main : F 1` with no pin whose term
is in the pure fragment runs every time at the LIR when printed: no fault, an answer, and every
answer `()` with no live object. -/
theorem own_lir_every_run (c : Checked) (hp : c.pins = []) (hΓ : c.ctx = [])
    (hC : c.C = .ret .unit) (hpure : pureT c.t = true) : LIREveryRun (printOwn c) := by
  have hsem := own_lowerSem (ℍ := Backend2.lirHost) c hp
  have hlow := own_lowersInto c ⟨hΓ, hpure⟩
  rw [hΓ] at hlow
  have hsim := own_printSimOn c hp hΓ hC hlow
  rw [hΓ, hC] at hsem
  exact lir_every_run_of_sem hsem hsim

/-- **End to end on the pure fragment, under `PinLaw`**: every checked closed `main : F 1` in the
pure fragment. -/
theorem own_lir_every_run_pin (hPin : PinLaw (ℍ := Backend2.lirHost)) (c : Checked)
    (hΓ : c.ctx = []) (hC : c.C = .ret .unit) (hpure : pureT c.t = true) :
    LIREveryRun (printOwn c) := by
  have hsem := own_lowerSemRel (ℍ := Backend2.lirHost) c (checked_sem_pin hPin c)
  have hlow := own_lowersInto c ⟨hΓ, hpure⟩
  rw [hΓ] at hlow
  have hsim := own_printSim_pin hPin c hΓ hC hlow
  rw [hΓ, hC] at hsem
  exact lir_every_run_of_sem hsem hsim

/-- **No `unreachable` in the pure fragment**: the print of every checked closed `main` whose term
is in the pure fragment writes none. -/
theorem printOwn_noUnr (c : Checked) (hΓ : c.ctx = []) (hpure : pureT c.t = true) :
    Tm.noUnr (printOwn c).main = true ∧ ∀ f ∈ (printOwn c).fns, Tm.noUnr f.body = true := by
  have hlow := own_lowersInto c ⟨hΓ, hpure⟩
  exact lirOf_noUnr _ (effFreeB_of_noSite hlow.effects)

/-! ### Non-vacuity -/

/-- A term whose free variables are all below `0` mentions none. -/
theorem closed_of_fvBound {e : Expr} (h : fvBound e = 0) (k : Nat) : mentions e k = false := by
  cases hm : mentions e k
  · rfl
  · have := mentions_lt hm; omega

/-- **A program that allocates, borrows and frees** (`cImmBorrow`, `Core/Examples.lean`): a
cell allocated, lent immutably to a callback that loads through the borrow, then freed. Its
print runs every time at the LIR. -/
theorem cImmBorrow_lir_every_run : LIREveryRun (lirOf cImmBorrow) :=
  lir_every_run_of_sem (fundamentalC cImmBorrow_derives)
    (printSimAt_lirOf cImmBorrow (by decide) (closed_of_fvBound (by decide))
      (fundamentalC cImmBorrow_derives))

end Lowering
