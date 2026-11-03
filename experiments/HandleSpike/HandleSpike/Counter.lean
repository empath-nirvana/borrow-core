import HandleSpike.Handle
import Core.TreeCactus

/-!
# Spike (#792): a forwarded cancellable operation, where `[handle]` at `cerwpT` fails

A handler `H` of name `nH`, answering `1` from its return clause, around `perform (nB, 0, ())`,
where `nB` is cancellable with a cancel branch owed (`q = cancel`, `fin = true`). The handled
computation is `cerwpT` at its table, answering `()` (`inner_ok`). The handler meets every clause of
`HandleOKT` but the no-cancel restriction on forwarded entries (`handler_ok_but_cancel`). And
`hnd H (perform (nB, 0, ()))` is not `cerwpT` at the outer table at index 3 (`forward_cancel_fails`).

Why: `nB` passes `H` and stops at the outer table. `contShareT` owes the stop's cancel branch at the
outer continuation relation, `cerwpT (opTableT To) Qout`, of `ccatch (K.dead[raise cancel])` with
`K = hndK H`. `K.dead` removes the handler's frame (`dead_hndK`), so the cancel runs without `H` and
answers `()` at once (`Head.cancel`); `()` is not in `Qout`. The inner share owes the same cancel at
`Qin`, where `()` is: the obligation moves from `Qin` to `Qout` because the handler's return clause is
not on the dead run.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.HandleSpike.Counter
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.HandleSpike
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.Tree.Wp.SchedProgs (cerwpPostT_down compS_empty_left_eq cerwpT_det)
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE hndVal capTag
  clauseAt ccatchE)

abbrev nB : UInt32 := 5
abbrev nH : UInt32 := 7

/-- The forwarded operation: cancellable, its cancel branch owed, no payload or answer resource. -/
def enF : OpEntT where
  q := .cancel
  abort := false
  PA := fun _ _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ σ = PMap.empty
  fin := true
  fd := fdJoinT
  oc := fun _ O => O = []

def T : OpTabT := fun m i => if m = nB ∧ i = 0 then some enF else none

theorem T_some {m i : UInt32} {en : OpEntT} (h : T m i = some en) : m = nB ∧ i = 0 ∧ en = enF := by
  unfold T at h
  split at h
  · rename_i hm; cases h; exact ⟨hm.1, hm.2, rfl⟩
  · cases h

def Qin : TPostV := fun _ _ _ O r ρ => r = Val.unit ∧ O = [] ∧ ρ = PMap.empty
def Qout : TPostV := fun _ _ _ O r ρ => r = Val.i32 1 ∧ O = [] ∧ ρ = PMap.empty

theorem Qin_down : Qin.Down := fun _ _ _ _ _ _ h => h
theorem Qout_down : Qout.Down := fun _ _ _ _ _ _ h => h

theorem T_PA_down : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ →
    en.PA k w ls v ρ := fun m i en h _ _ _ _ _ hA => by obtain ⟨-, -, rfl⟩ := T_some h; exact hA

/-- `λ_. 1`. -/
def retOne : Val := Val.lam (.val (Val.i32 1))
def qsH : Val := Val.pair Val.unit Val.unit
def hsH : Val := Val.pair Val.unit Val.unit
def H : Val := hndVal nH qsH retOne hsH

def e : Expr := performE (.val (opPayload nB 0 Val.unit))

/-! ### The handled computation is `cerwpT` at `T` -/

theorem inner_ok (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT T) Qin Fb F n w ls [] e PMap.empty := by
  show cerwpT (ℍ := ℍ) (opTableT T) Qin Fb F n w ls [] (Kont.hole.plug e) PMap.empty
  refine cerwpT_perform .hole rfl (show T nB 0 = some enF by simp [T]) rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  obtain rfl := RR.of_empty hr
  refine ⟨rfl, PMap.empty, PMap.empty, ResUT.compS_empty_right _, ⟨rfl, rfl⟩, ?_⟩
  unfold contShareT
  refine ⟨fun h => absurd h (by simp [enF]), ?_⟩
  intro w' ρ' ls' O' _ hr' _ hO'
  refine ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun _ _ k' hk' => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := RR.of_empty hr'
    obtain rfl := compS_empty_left_eq hcσ
    cases hO'
    simp only [cerwpTC, hk', if_true]
    exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
      cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩
  · obtain rfl := RR.of_empty hr'
    cases hO'
    simp only [cerwpTC, hk', if_true]
    refine cerwpT_det (cerwpPostT_down Qin_down T_PA_down)
      (fun μ => step1Only_plug (Head.cancel μ .hole rfl) rfl .hole) ?_
    exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
      cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩

/-! ### The handler meets `HandleOKT` but for the no-cancel restriction -/

theorem ret_ok (Fbo : TFrame) : RetT (ℍ := ℍ) T Qin Qout Fbo retOne := by
  intro F k w ls O v ρ _ _ _ _ _ ⟨_, hO, hρ⟩
  subst hO; subst hρ
  refine cerwpT_det (cerwpPostT_down Qout_down T_PA_down)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact cerwpT_val (v := Val.i32 1) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
    cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩

/-- **Every clause of `HandleOKT` but the restriction holds**, and the restriction fails at `nB`. -/
theorem handler_ok_but_cancel (Fbo : TFrame) :
    (∀ m i en, m ≠ nH → T m i = some en → T m i = some en) ∧
    (∀ i en, T nH i = some en → en.abort = false → capTag qsH.1 i.toNat = en.q.tag) ∧
    (∀ m i en, T m i = some en → ∀ v w O ρf, en.fd v w O ρf ↔ fdJoinT v w O ρf) ∧
    Qout.Down ∧
    (∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ) ∧
    RetT (ℍ := ℍ) T Qin Qout Fbo retOne ∧
    (∀ i en, T nH i = some en →
      ∃ c, clauseAt hsH.1 i.toNat = some c ∧ ClauseT (ℍ := ℍ) T H Qout Fbo en c) ∧
    T nB 0 = some enF ∧ ¬ (enF.q = .lin ∨ enF.fin = false) := by
  refine ⟨fun _ _ _ _ h => h, fun i en h => ?_, fun m i en h v w O ρf => ?_, Qout_down,
    T_PA_down, ret_ok Fbo, fun i en h => ?_, by simp [T], by simp [enF]⟩
  · obtain ⟨h, -⟩ := T_some h; cases h
  · obtain ⟨-, -, rfl⟩ := T_some h; exact Iff.rfl
  · obtain ⟨h, -⟩ := T_some h; cases h

/-! ### The conclusion fails -/

/-- **`hnd H (perform (nB, 0, ()))` is not `cerwpT` at `T` answering `Qout`**, from the empty world,
at index 3, base and present frame condition "the frame is empty". -/
theorem forward_cancel_fails (P : ParentFn) :
    ¬ cerwpT (ℍ := ℍ) (opTableT T) Qout (fun _ ρf => ρf = PMap.empty)
      (fun _ ρf => ρf = PMap.empty) 3 ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩ [] []
      (hndE H e) (PMap.empty : TRes (WCactus.ofParent P)) := by
  intro h
  rw [cerwpT_eq] at h
  have hK : (hndK H).HasHnd nB = false := by rw [H, hndK_hasHnd]; decide
  have hfin : ∀ μ, Final (ℍ := ℍ) μ (hndE H e) :=
    final_opPlug (K := hndK H) (r := false) (payloadName_opPayload nB 0 Val.unit) hK
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, -, -, -⟩ :=
    h _ PMap.empty PMap.empty PMap.empty [] [] [] [] (fun _ => none) (TWd.Ext.refl _ _) RR.empty
      .nil .nil rfl (ResUT.hash_empty_right ⟨_, flat_empty⟩) (ResUT.compS_empty_right _)
      ⟨fun p => by simp, fun p hp => by simp at hp⟩ (recInv_empty P) (winv_empty P)
      finDom_empty 0 _ _ (by omega) (.refl _ _) (hfin _)
  obtain rfl : ρf' = PMap.empty := RR.of_empty g₁
  rcases g₈ with ⟨v, hv, -⟩ | ⟨K, m, i, v, en, ht, -, hT, -, hoc, ρa, ρk, hc, hA, hsh⟩
  · have hv' := v.2
    rw [← hv] at hv'
    cases hv'
  obtain ⟨hKe, hp⟩ := plug_perform_inj (K := hndK H) ht
  obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hp.symm
  subst hKe
  rw [show T nB 0 = some enF by simp [T]] at hT
  cases hT
  change O' = [] at hoc
  subst hoc
  obtain ⟨-, rfl⟩ := hA
  obtain rfl := compS_empty_left_eq hc
  have hcov : CovR (sem w'.Θ) w'.K ρ' := cov_of_comp g₄ g₇
  have h₁ := (hsh.2 w' ρ' ls' [] (TWd.Ext.refl _ _) (RR.refl hcov)
    (KeepRel.of_srecsRR (SRecsRR.refl g₆.cov_ls) _) .nil).2 (by decide) rfl 2 (by omega)
  simp only [cerwpTC, show (2 : Nat) < 3 - 0 by omega, if_true] at h₁
  rw [H, dead_hndK, cerwpT_eq] at h₁
  have hstep : StepsN (ℍ := ℍ) 1 (fun _ => none)
      (ccatchE (Kont.hole.plug (raiseE (.val (cancelVal none))))) (fun _ => none)
      (Val.unit).1 :=
    .more (step1Only_plug (Head.cancel (fun _ => none) .hole rfl) rfl .hole).1 (.refl _ _)
  obtain ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, -, -, -, -, -, -, -, -, g₈', -, -, -⟩ :=
    h₁ w' ρ' PMap.empty fρ' ls' [] ps' psF' (fun _ => none) (TWd.Ext.refl _ _) (RR.refl hcov)
      (SRecsRR.refl g₆.cov_ls) .nil
      ⟨rfl, fun O'' _ => fdMask_empty _ _⟩ (ResUT.hash_symm g₃) g₄ g₅ g₆ g₇ finDom_empty 1 _ _
      (by omega) hstep (final_val _ _)
  rcases g₈' with ⟨v, hv, hq, -, -⟩ | ⟨K, m, i, v, en, ht, -⟩
  · have : v = Val.unit := Subtype.ext hv.symm
    subst this
    have := congrArg Subtype.val hq
    simp [Val.unit, Val.i32] at this
  · exact plug_perform_ne_val K _ Val.unit ht.symm

end BoCa.Fig16.Tree.Wp.HandleSpike.Counter

end
