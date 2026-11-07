import Core.Chain.PoolN
import Core.Chain.SI.LendCancelProg
import Core.TreePoolSpawn

/-!
# The scheduler `HS` over the chain relation: park, spawn and cancel  `[spec §62]`

`HS` (`Core/TreePoolSpawn.lean`) keeps its stopped tasks in a list and has, under the name `nP`,

* `park ()` (`enParkN`, index 0): the stopped task is parked; if the list's top is a ready task
  it is resumed and the stopped task stays beneath it (`poolAnsN_park`, then
  `poolAnsN_resumeSnd`); otherwise (the list empty) the stopped task is resumed;
* `spawn th` (`enSpawnN`, index 1): the spawner is parked and the child `th ()`, holding nothing,
  is run under the scheduler beside the pool (`poolAnsN_park`, then `poolAnsN_run_le`);
* `cancel ()` (`enParkN`, index 2): the stopped task is parked; if the top is a ready task it is
  cancelled, its cancel branch run under the scheduler (`poolAnsN_park`, then
  `poolAnsN_cancelSnd`); otherwise the stopped task is resumed.

A task's end resumes the list's top (`stackRet`, `poolAnsN_resume`), or, the list empty, is the
program's answer. `HS`'s fourth clause (`par`) has no entry in the table `TJN`, so no task performs
it and `erwp_handle_le` never asks for it.

The clauses are proved for every list of any length (`hs_schedOKN`), by strong induction on the
stop index (`SchedOKNLe`): the spawn clause runs its child, and the cancel clause a stored task's
cancel branch, below its own index, at the scheduler's clauses there.

**Children at any depth.** A child's thunk is verified at a table that itself has `spawn`: the
tables are indexed (`tabAtN k`), the spawn entry of `tabAtN k` reading the children of a stop at
`j < k` at `tabAtN j`. A run at `tabAtN j` at an index up to `j` is a run at `TJN`
(`erwp_tabAtN`), since the two tables agree at the stops up to `j`.

**Cancel runs.** Each entry's cancel obligation is a cancel run at the empty table: the unwinding
of a cancelled task performs no operation. The location family of the cancel obligations (`Φc`)
is a parameter of the table apart from the one the children are verified at, so that a task can
be verified with its lends' location families changing the first only.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.PoolSpawn
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg (unitP)
open BoCa.Fig16.Tree.Wp.SchedProgs.Park (nP)
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack (stackRet retBody retL subst_shift0')
open BoCa.Fig16.Tree.Wp.SchedProgs.Spawn (HS qsS hsS parkCl spawnCl cancelCl clauseOf readyE
  parkB cancelB spawnB subst_shift0)
open BoCa.BoLo (Heap Head Kont hndE hndVal clauseAt capTag)

/-! ### The tables -/

/-- A task's answer, and the program's: a value owning nothing. -/
def QVN : PostN := fun _ _ _ ρ => ρ = PMap.empty

theorem QVN_down : QVN.Down := fun _ _ _ _ h => h

/-- `park` and `cancel`: cancellable, no payload and no answer resource, the cancel run at the
empty table, resumed at `extF`. -/
def enParkN (Φc : LocFam) : OpEntN :=
  ⟨.cancel, false, unitP, unitP, some (cancelOblN (ℍ := ℍ) Φc OpTabN.empty), extF⟩

/-- `spawn` at a payload condition `PS`. -/
def enSpawnN (Φc : LocFam) (PS : Nat → List SRec → Val → WProp) : OpEntN :=
  ⟨.cancel, false, PS, unitP, some (cancelOblN (ℍ := ℍ) Φc OpTabN.empty), extF⟩

/-- **A child, run as a new task**: at every index `j` below `k`, at every list, `th ()`
holding nothing is verified at the table `Tf j`. -/
def ChildOKN (Φ : LocFam) (Tf : Nat → OpTabN) (k : Nat) (th : Val) : Prop :=
  ∀ j, j < k → ∀ ls, erwp (ℍ := ℍ) Φ (opTableN (Tf j)) QVN j ls (.app th.1 (.val Val.unit))
    PMap.empty

/-- `spawn`'s payload: a child holding nothing. -/
def spawnPAN (Φ : LocFam) (Tf : Nat → OpTabN) : Nat → List SRec → Val → WProp :=
  fun k _ v ρ => ρ = PMap.empty ∧ ChildOKN (ℍ := ℍ) Φ Tf k v

/-- The table, its cancel obligations' location family and its spawn payload given. -/
def tabOfN (Φc : LocFam) (PS : Nat → List SRec → Val → WProp) : OpTabN := fun m i =>
  if m = nP then
    (if i = 0 then some (enParkN (ℍ := ℍ) Φc) else if i = 1 then some (enSpawnN (ℍ := ℍ) Φc PS)
      else if i = 2 then some (enParkN (ℍ := ℍ) Φc) else none)
  else none

/-- **The table at index `k`**: its children's tables are those below `k`. -/
def tabAtN (Φ : LocFam) : Nat → OpTabN
  | k => tabOfN (ℍ := ℍ) Φ (spawnPAN (ℍ := ℍ) Φ fun j => if _h : j < k then tabAtN Φ j
      else OpTabN.empty)
termination_by k => k

/-- **The scheduler's table**: its children's tables are the indexed ones. -/
def TJN (Φ : LocFam) : OpTabN := tabOfN (ℍ := ℍ) Φ (spawnPAN (ℍ := ℍ) Φ (tabAtN (ℍ := ℍ) Φ))

theorem tabAtN_eq (Φ : LocFam) (k : Nat) :
    tabAtN (ℍ := ℍ) Φ k = tabOfN (ℍ := ℍ) Φ (spawnPAN (ℍ := ℍ) Φ fun j =>
      if j < k then tabAtN (ℍ := ℍ) Φ j else OpTabN.empty) := by
  rw [tabAtN]; rfl

theorem tabOfN_some {Φc : LocFam} {PS : Nat → List SRec → Val → WProp} {m i : UInt32}
    {en : OpEntN} (h : tabOfN (ℍ := ℍ) Φc PS m i = some en) :
    m = nP ∧ ((i = 0 ∧ en = enParkN (ℍ := ℍ) Φc) ∨ (i = 1 ∧ en = enSpawnN (ℍ := ℍ) Φc PS) ∨
      (i = 2 ∧ en = enParkN (ℍ := ℍ) Φc)) := by
  unfold tabOfN at h
  split at h
  · rename_i hm
    refine ⟨hm, ?_⟩
    split at h
    · cases h; exact Or.inl ⟨by assumption, rfl⟩
    split at h
    · cases h; exact Or.inr (Or.inl ⟨by assumption, rfl⟩)
    split at h
    · cases h; exact Or.inr (Or.inr ⟨by assumption, rfl⟩)
    · cases h
  · cases h

theorem tabOfN_park (Φc : LocFam) (PS : Nat → List SRec → Val → WProp) :
    tabOfN (ℍ := ℍ) Φc PS nP 0 = some (enParkN (ℍ := ℍ) Φc) := by simp [tabOfN]
theorem tabOfN_spawn (Φc : LocFam) (PS : Nat → List SRec → Val → WProp) :
    tabOfN (ℍ := ℍ) Φc PS nP 1 = some (enSpawnN (ℍ := ℍ) Φc PS) := by simp [tabOfN]
theorem tabOfN_cancel (Φc : LocFam) (PS : Nat → List SRec → Val → WProp) :
    tabOfN (ℍ := ℍ) Φc PS nP 2 = some (enParkN (ℍ := ℍ) Φc) := by simp [tabOfN]

/-- Every entry: not abortive, cancellable, its cancel run at the empty table, resumed at
`extF`, answering `()` owning nothing. -/
theorem tabOfN_ent {Φc : LocFam} {PS : Nat → List SRec → Val → WProp} {m i : UInt32}
    {en : OpEntN} (h : tabOfN (ℍ := ℍ) Φc PS m i = some en) :
    en.abort = false ∧ en.q = .cancel ∧ en.fin = some (cancelOblN (ℍ := ℍ) Φc OpTabN.empty) ∧
      en.wc = extF ∧ en.PB = unitP := by
  obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := tabOfN_some h <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A table whose spawn payload is downward closed is. -/
theorem tabOfN_down {Φc : LocFam} (hΦ : Φc.Down) {PS : Nat → List SRec → Val → WProp}
    (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ) : (tabOfN (ℍ := ℍ) Φc PS).Down where
  pa := fun _ _ en h k ls v ρ hA => by
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := tabOfN_some h
    · exact hA
    · exact hPS k ls v ρ hA
    · exact hA
  fin := fun _ _ en P h hP => by
    rw [(tabOfN_ent h).2.2.1] at hP
    cases hP
    exact LendProg.cancelOblN_down hΦ OpTabN.empty_down
  wcl := fun _ _ en h => by rw [(tabOfN_ent h).2.2.2.1]; exact extF_left

theorem spawnPAN_down (Φ : LocFam) (Tf : Nat → OpTabN) :
    ∀ k ls v ρ, spawnPAN (ℍ := ℍ) Φ Tf (k + 1) ls v ρ → spawnPAN (ℍ := ℍ) Φ Tf k ls v ρ :=
  fun _ _ _ _ ⟨h₁, h₂⟩ => ⟨h₁, fun j hj => h₂ j (by omega)⟩

theorem TJN_down {Φ : LocFam} (hΦ : Φ.Down) : (TJN (ℍ := ℍ) Φ).Down :=
  tabOfN_down hΦ (spawnPAN_down Φ _)

/-! ### A child verified at its indexed table -/

/-- **`tabAtN j`'s stops up to `j` are `TJN`'s**: the entries are the same but for the spawn
payload, and those agree up to `j`. -/
theorem tabAtN_incl (Φ : LocFam) (j : Nat) : ∀ k, k ≤ j → ∀ ls t (Ψ Ψ' : ContN) ρ,
    (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
    opTableN (tabAtN (ℍ := ℍ) Φ j) k ls t Ψ ρ → opTableN (TJN (ℍ := ℍ) Φ) k ls t Ψ' ρ := by
  intro k hk ls t Ψ Ψ' ρ hΨ h
  rcases opTableN_local _ k ls t Ψ Ψ' ρ hΨ h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    rw [tabAtN_eq] at h₃
    obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfN_some h₃
    · exact Or.inl ⟨K, nP, 0, v, _, pure_sep_mk ⟨h₁, h₂, tabOfN_park _ _, h₄⟩
        ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩
    · refine Or.inl ⟨K, nP, 1, v, _, pure_sep_mk ⟨h₁, h₂, tabOfN_spawn _ _, h₄⟩
        ⟨ρa, ρk, hc, ⟨hA.1, fun j' hj' ls' => ?_⟩, hu, hcont⟩⟩
      have := hA.2 j' hj' ls'
      simp only [show j' < j by omega, if_true] at this
      exact this
    · exact Or.inl ⟨K, nP, 2, v, _, pure_sep_mk ⟨h₁, h₂, tabOfN_cancel _ _, h₄⟩
        ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩
  · obtain ⟨⟨-, -, h₃, h₄⟩, -⟩ := pure_sep_iff.mp hp
    rw [tabAtN_eq] at h₃
    exact absurd h₄ (by rw [(tabOfN_ent h₃).1]; simp)

/-- **A child verified at `tabAtN j` at index `j` is verified at `TJN`.** -/
theorem erwp_tabAtN {Φ : LocFam} {Q : PostN} {j : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ (opTableN (tabAtN (ℍ := ℍ) Φ j)) Q j ls e ρ) :
    erwp (ℍ := ℍ) Φ (opTableN (TJN (ℍ := ℍ) Φ)) Q j ls e ρ :=
  erwp_mono_le j (fun _ _ _ _ _ h => h) (tabAtN_incl Φ j) j le_rfl ls e ρ h

/-! ### The invariant and the answers -/

/-- **The pool invariant**: every entry a ready task, tagged `inj₁ ()`, cancellable, its cancel
run at the scheduler's table, resumed at `()` holding nothing. -/
def InvSN (Φ : LocFam) (ts : List StoredN) : Prop :=
  ∀ t ∈ ts, t.tag = Val.inj₁ Val.unit ∧ t.en.q = .cancel ∧ t.Tc = some (TJN (ℍ := ℍ) Φ) ∧
    ∀ k ls, t.en.PB k ls Val.unit PMap.empty

/-- The scheduler's answers. -/
abbrev PA_SN (Φ : LocFam) : PostN := PoolAnsN (ℍ := ℍ) Φ QVN HS (InvSN (ℍ := ℍ) Φ)

/-- A stopped task at an entry of `TJN`, parked as a ready entry. -/
def readyN (Φ : LocFam) (en : OpEntN) (k : Nat) (ls : List SRec) (κ : Val) : StoredN :=
  ⟨PA_SN (ℍ := ℍ) Φ, en, some (TJN (ℍ := ℍ) Φ), k, ls, κ, Val.inj₁ Val.unit⟩

theorem invSN_ready {Φ : LocFam} {en : OpEntN} {k : Nat} {ls : List SRec} {κ : Val}
    {ts : List StoredN} (hq : en.q = .cancel) (hB : en.PB = unitP) (hi : InvSN (ℍ := ℍ) Φ ts) :
    InvSN (ℍ := ℍ) Φ (readyN (ℍ := ℍ) Φ en k ls κ :: ts) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨rfl, hq, rfl, fun _ _ => by simp only [readyN]; rw [hB]; exact ⟨rfl, rfl⟩⟩
  · exact hi x hx

set_option linter.unusedSimpArgs false

/-- Substitution into a clause body after a step. -/
syntax "ssimpN" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ssimpN) => `(tactic| simp [Kont.plug, Expr.subst, Expr.shift_shift,
      BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.subst_shift0, Expr.shift_zero, clauseOf, readyE, parkB,
      cancelB, spawnB, stateValN, poolValN])
  | `(tactic| ssimpN [$ls,*]) => `(tactic| simp [Kont.plug, Expr.subst, Expr.shift_shift,
      BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.subst_shift0, Expr.shift_zero, clauseOf, readyE, parkB,
      cancelB, spawnB, stateValN, poolValN, $ls,*])

/-! ### The clauses -/

/-- What every clause is asked, at an entry of `TJN`. -/
def ClauseN (Φ : LocFam) (N : Nat) (en : OpEntN) (c : Val) : Prop :=
  ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
    (en.PA k ls v ⋆ KapRelN (ℍ := ℍ) Φ (opTableN OpTabN.empty) (PA_SN (ℍ := ℍ) Φ) en
      (some (TJN (ℍ := ℍ) Φ)) k ls κ) ρ →
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (PA_SN (ℍ := ℍ) Φ) k ls
      (.app (.val c) (.pair (.val v) κ.1)) ρ

/-- **`park`'s clause**: the stopped task parked; the top ready, it is resumed and the stopped
task kept beneath it (`poolAnsN_resumeSnd`); otherwise the stopped task resumed
(`poolAnsN_resume`). -/
theorem parkClN_ok {Φ : LocFam} (hΦ : Φ.Down) (N : Nat) :
    ClauseN (ℍ := ℍ) Φ N (enParkN (ℍ := ℍ) Φ) parkCl := by
  rintro k _ ls v κ ρ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := eq_of_compS_empty_left hc
  have hTD := opTableN_down OpTabN.empty_down
  have hD := poolAnsN_down (ℍ := ℍ) Φ QVN HS (InvSN (ℍ := ℍ) Φ)
  refine erwp_det hΦ hTD hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl
    .hole) ?_
  refine erwp_det hΦ hTD hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine erwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtN_iff.mpr ?_)
  intro ts σ ρ' hi hg hP hc'
  obtain ⟨hP', hg'⟩ := poolAnsN_park (Val.inj₁ Val.unit) hκ (fun _ hm => extF_of_same hm ρ)
    hj hg hP hc'
  cases j with
  | zero => exact erwp_zero
  | succ j₀ =>
  refine erwp_step (opTableN_local _) (fun μ => step1Only_plug (Head.beta μ _ (stateValN HS ts))
    rfl .hole) ?_
  ssimpN
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.letpair μ HS (poolValN ts) _)
    rfl .hole) ?_
  ssimpN
  cases ts with
  | nil =>
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
      .hole) ?_
    ssimpN
    exact poolAnsN_resume hΦ hg' hP' ⟨rfl, rfl⟩ (ResU.comp_empty_right ρ') hi
  | cons u ts =>
    obtain ⟨htag, hq, -, hB⟩ := hi u List.mem_cons_self
    have hi' : InvSN (ℍ := ℍ) Φ ts := fun x hx => hi x (List.mem_cons_of_mem _ hx)
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair u.tag u.κ) (poolValN ts)) _ _) rfl .hole) ?_
    ssimpN
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair u.tag u.κ) (poolValN ts) _) rfl .hole) ?_
    ssimpN
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.letpair μ u.tag u.κ _) rfl
      .hole) ?_
    ssimpN
    rw [htag]
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl
      .hole) ?_
    ssimpN
    exact poolAnsN_resumeSnd hΦ hg' hP' (hB _ _) (ResU.comp_empty_right ρ')
      (invSN_ready (k := k) (ls := ls) (κ := κ) rfl rfl hi')

/-- The scheduler meeting its clauses at every stop below `N`. -/
abbrev SchedBelow (Φ : LocFam) (N : Nat) : Prop :=
  ∀ N', N' < N → SchedOKNLe (ℍ := ℍ) Φ N' (TJN (ℍ := ℍ) Φ) nP qsS stackRet hsS QVN
    (PA_SN (ℍ := ℍ) Φ)

/-- A cancel run's answer is a task's. -/
theorem unitPost_QVN : ∀ k ls v (ρ : WRes), unitPost k ls v ρ → QVN k ls v ρ :=
  fun _ _ _ _ ⟨h₁, _⟩ => h₁

/-- **`cancel`'s clause**: the stopped task parked; the top ready, it is cancelled, its cancel
branch run under the scheduler below the stop's index, the stopped task kept beneath it
(`poolAnsN_cancelSnd`); otherwise the stopped task resumed (`poolAnsN_resume`). -/
theorem cancelClN_ok {Φ : LocFam} (hΦ : Φ.Down) (N : Nat) (ih : SchedBelow (ℍ := ℍ) Φ N) :
    ClauseN (ℍ := ℍ) Φ N (enParkN (ℍ := ℍ) Φ) cancelCl := by
  rintro k hkN ls v κ ρ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := eq_of_compS_empty_left hc
  have hTD := opTableN_down OpTabN.empty_down
  have hD := poolAnsN_down (ℍ := ℍ) Φ QVN HS (InvSN (ℍ := ℍ) Φ)
  refine erwp_det hΦ hTD hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl
    .hole) ?_
  refine erwp_det hΦ hTD hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine erwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtN_iff.mpr ?_)
  intro ts σ ρ' hi hg hP hc'
  obtain ⟨hP', hg'⟩ := poolAnsN_park (Val.inj₁ Val.unit) hκ (fun _ hm => extF_of_same hm ρ)
    hj hg hP hc'
  cases j with
  | zero => exact erwp_zero
  | succ j₀ =>
  refine erwp_step (opTableN_local _) (fun μ => step1Only_plug (Head.beta μ _ (stateValN HS ts))
    rfl .hole) ?_
  ssimpN
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.letpair μ HS (poolValN ts) _)
    rfl .hole) ?_
  ssimpN
  cases ts with
  | nil =>
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
      .hole) ?_
    ssimpN
    exact poolAnsN_resume hΦ hg' hP' ⟨rfl, rfl⟩ (ResU.comp_empty_right ρ') hi
  | cons u ts =>
    obtain ⟨htag, hq, hTc, -⟩ := hi u List.mem_cons_self
    have hi' : InvSN (ℍ := ℍ) Φ ts := fun x hx => hi x (List.mem_cons_of_mem _ hx)
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair u.tag u.κ) (poolValN ts)) _ _) rfl .hole) ?_
    ssimpN
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair u.tag u.κ) (poolValN ts) _) rfl .hole) ?_
    ssimpN
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.letpair μ u.tag u.κ _) rfl
      .hole) ?_
    ssimpN
    rw [htag]
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl
      .hole) ?_
    ssimpN
    exact poolAnsN_cancelSnd hΦ (ih j₀ (by omega)) unitPost_QVN le_rfl hg' hP'
      (by rw [hq]; decide) hTc (invSN_ready (k := k) (ls := ls) (κ := κ) rfl rfl hi')

/-- **`spawn`'s clause**: the spawner parked as a ready task (`poolAnsN_park`), the child run
under the scheduler beside the pool below the stop's index (`poolAnsN_run_le`), lifted from its
indexed table (`erwp_tabAtN`). -/
theorem spawnClN_ok {Φ : LocFam} (hΦ : Φ.Down) (N : Nat) (ih : SchedBelow (ℍ := ℍ) Φ N) :
    ClauseN (ℍ := ℍ) Φ N (enSpawnN (ℍ := ℍ) Φ (spawnPAN (ℍ := ℍ) Φ (tabAtN (ℍ := ℍ) Φ)))
      spawnCl := by
  rintro k hkN ls v κ ρ ⟨ρa, ρk, hc, ⟨rfl, hth⟩, hκ⟩
  obtain rfl := eq_of_compS_empty_left hc
  have hTD := opTableN_down OpTabN.empty_down
  have hD := poolAnsN_down (ℍ := ℍ) Φ QVN HS (InvSN (ℍ := ℍ) Φ)
  refine erwp_det hΦ hTD hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v κ)) rfl
    .hole) ?_
  refine erwp_det hΦ hTD hD (fun μ => step1Only_plug (Head.letpair μ v κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine erwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtN_iff.mpr ?_)
  intro ts σ ρ' hi hg hP hc'
  obtain ⟨hP', hg'⟩ := poolAnsN_park (Val.inj₁ Val.unit) hκ (fun _ hm => extF_of_same hm ρ)
    hj hg hP hc'
  cases j with
  | zero => exact erwp_zero
  | succ j₀ =>
  refine erwp_step (opTableN_local _) (fun μ => step1Only_plug (Head.beta μ _ (stateValN HS ts))
    rfl .hole) ?_
  ssimpN
  refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.letpair μ HS (poolValN ts) _)
    rfl .hole) ?_
  ssimpN
  exact poolAnsN_run_le hΦ (ih j₀ (by omega)) le_rfl (fun u hu => (hg' u hu).le (by omega))
    (invSN_ready (k := k) (ls := ls) (κ := κ) rfl rfl hi) hP' (compS_empty_left ρ')
    (erwp_tabAtN (hth j₀ (by omega) ls))

/-- **The return clause**: the list's top resumed with the rest (`poolAnsN_resume`); or, the list
empty, the task's answer the program's. -/
theorem stackRetN_ok {Φ : LocFam} (hΦ : Φ.Down) : ∀ k ls v (ρ : WRes), QVN k ls v ρ →
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (PA_SN (ℍ := ℍ) Φ) k ls
      (.app (.val stackRet) (.val v)) ρ := by
  rintro k ls v ρ rfl
  have hTD := opTableN_down OpTabN.empty_down
  have hD := poolAnsN_down (ℍ := ℍ) Φ QVN HS (InvSN (ℍ := ℍ) Φ)
  refine erwp_det hΦ hTD hD (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  simp only [Kont.plug]
  refine erwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtN_iff.mpr ?_)
  intro ts σ ρ' hi hg hP hc'
  obtain rfl := eq_of_compS_empty_left hc'
  cases ts with
  | nil =>
    obtain rfl : ρ' = PMap.empty := hP
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.beta μ _ (stateValN HS []))
      rfl .hole) ?_
    simp [Kont.plug, Expr.subst, retBody, retL, stateValN, poolValN, Expr.shift_shift,
      subst_shift0', Expr.shift_zero]
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug
      (Head.letpair μ HS (Val.inj₂ Val.unit) _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
      .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    exact erwp_val (v := v) rfl
  | cons t ts =>
    cases j with
    | zero => exact erwp_zero
    | succ j₀ =>
    obtain ⟨-, -, -, hB⟩ := hi t List.mem_cons_self
    have hi' : InvSN (ℍ := ℍ) Φ ts := fun x hx => hi x (List.mem_cons_of_mem _ hx)
    refine erwp_step (opTableN_local _) (fun μ => step1Only_plug
      (Head.beta μ _ (stateValN HS (t :: ts))) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, retBody, retL, stateValN, poolValN, Expr.shift_shift,
      subst_shift0', Expr.shift_zero]
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug
      (Head.letpair μ HS (poolValN (t :: ts)) _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, poolValN, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair t.tag t.κ) (poolValN ts)) _ _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair t.tag t.κ) (poolValN ts) _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine erwp_det hΦ hTD QVN_down (fun μ => step1Only_plug (Head.letpair μ t.tag t.κ _) rfl
      .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    exact poolAnsN_resume hΦ hg hP (hB _ _) (ResU.comp_empty_right ρ') hi'

/-- **The scheduler meets its clauses at stops up to every `N`**, by strong induction on `N`. -/
theorem hs_schedOKNLe {Φ : LocFam} (hΦ : Φ.Down) : ∀ N, SchedOKNLe (ℍ := ℍ) Φ N (TJN (ℍ := ℍ) Φ)
    nP qsS stackRet hsS QVN (PA_SN (ℍ := ℍ) Φ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  refine ⟨TJN_down hΦ, fun m i hm => by simp [TJN, tabOfN, hm], fun i en h _ => ?_,
    fun i en h _ _ => ⟨OpTabN.empty, (tabOfN_ent h).2.2.1,
      fun _ _ _ h => by simp [OpTabN.empty] at h⟩,
    fun i en h ls ls' ρ hm => by rw [(tabOfN_ent h).2.2.2.1]; exact extF_of_same hm ρ,
    poolAnsN_down _ _ _ _, fun k _ => stackRetN_ok hΦ k, fun i en h => ?_⟩
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfN_some h <;> rfl
  · have hna : ∀ c, en.abort = true → ∀ k, k ≤ N → ∀ ls v (ρ : WRes), en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (PA_SN (ℍ := ℍ) Φ) k ls
          (.app (.val c) (.val v)) ρ := fun _ ha => by rw [(tabOfN_ent h).1] at ha; cases ha
    obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfN_some h
    · exact ⟨parkCl, by simp [clauseAt, hsS, Val.pair, parkCl]; exact (BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf _).2,
        fun _ => parkClN_ok hΦ N, hna _⟩
    · exact ⟨spawnCl, by simp [clauseAt, hsS, Val.pair, spawnCl]; exact (BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf _).2,
        fun _ => spawnClN_ok hΦ N ih, hna _⟩
    · exact ⟨cancelCl, by simp [clauseAt, hsS, Val.pair, cancelCl]; exact (BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf _).2,
        fun _ => cancelClN_ok hΦ N ih, hna _⟩

/-- **The scheduler `HS` meets `SchedOKN`** at the table `TJN`, its answers functions of its
list, for every list. -/
theorem hs_schedOKN {Φ : LocFam} (hΦ : Φ.Down) : SchedOKN (ℍ := ℍ) Φ (TJN (ℍ := ℍ) Φ) nP qsS
    stackRet hsS QVN (PA_SN (ℍ := ℍ) Φ) := hs_schedOKNLe hΦ

/-- **A root verified at the scheduler's table, closed under `HS`**: through
`poolSchedAdequacyN`, every premise discharged. -/
theorem progOfN_orDiverges {Φ : LocFam} (hΦ : Φ.Down) (hΦI : Φ.imm = []) {root : Expr}
    (h : ∀ n, erwp (ℍ := ℍ) Φ (opTableN (TJN (ℍ := ℍ) Φ)) QVN n [] root (PMap.empty : WRes)) :
    OrDiverges (ℍ := ℍ) (.app (hndE HS root) (stateValN HS []).1) :=
  poolSchedAdequacyN Φ (TJN Φ) nP qsS stackRet hsS QVN QVN (InvSN Φ) root hΦ hΦI
    (fun _ _ _ _ h => h) (fun _ h => by cases h) (hs_schedOKN hΦ) h

end BoCa.Fig16.LogRel.Core.Chain.SI.PoolSpawn

end
