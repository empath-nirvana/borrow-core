import Core.Chain.PoolSpawnN

/-!
# `HS` at a table whose `spawn` passes resources; a scheduler scope inside a task  `[spec §62]`

`TJN` (`Core/Chain/PoolSpawnN.lean`) spawns children holding nothing: its entries meet
`LendOK`/`LendOKC`, so a task's lend may stay open across them. `TJV` is the same table with
the spawn's payload any resource the child is verified from (`spawnPAV`, `ChildOKV`): a child
can hold a borrow of its spawner's lend. Such a payload is not in `Res_A`, and a stop carrying
it out of the lending segment is refused by `↭` (`Core/Chain/CrossStopN.lean`), so `TJV` is the
table of a scheduler handled inside the lend, not of the top-level one.

`hs_schedOKV`: the same scheduler code `HS` meets `SchedOKN` at `TJV`, by the proofs of
`PoolSpawnN` with the spawn clause running its child from the payload's resource beside the
pool. `erwp_scopeV`: `(hnd HS e) (HS, [])` inside a task, from the empty pool, is a run that
never stops outside and answers a value owning nothing; the scope ends only when its list is
empty, every task it started ended or cancelled.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.PoolScope
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.PoolSpawn
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg (unitP)
open BoCa.Fig16.Tree.Wp.SchedProgs.Park (nP)
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack (stackRet retBody retL subst_shift0')
open BoCa.Fig16.Tree.Wp.SchedProgs.Spawn (HS qsS hsS parkCl spawnCl cancelCl clauseOf readyE
  parkB cancelB spawnB subst_shift0)
open BoCa.BoLo (Heap Head Kont hndE hndVal clauseAt capTag)

set_option linter.unusedSimpArgs false

/-- **A child, run as a new task**: at every index `j` below `k`, at every list, `th ()`
holding nothing is verified at the table `Tf j`. -/
def ChildOKV (Φ : LocFam) (Tf : Nat → OpTabN) (k : Nat) (th : Val) (ρ : WRes) : Prop :=
  ∀ j, j < k → ∀ ls, erwp (ℍ := ℍ) Φ (opTableN (Tf j)) QVN j ls (.app th.1 (.val Val.unit)) ρ

/-- `spawn`'s payload: a child holding nothing. -/
def spawnPAV (Φ : LocFam) (Tf : Nat → OpTabN) : Nat → List SRec → Val → WProp :=
  fun k _ v ρ => ChildOKV (ℍ := ℍ) Φ Tf k v ρ

/-- **The table at index `k`**: its children's tables are those below `k`. -/
def tabAtV (Φ : LocFam) : Nat → OpTabN
  | k => tabOfN (ℍ := ℍ) Φ (spawnPAV (ℍ := ℍ) Φ fun j => if _h : j < k then tabAtV Φ j
      else OpTabN.empty)
termination_by k => k

/-- **The scheduler's table**: its children's tables are the indexed ones. -/
def TJV (Φ : LocFam) : OpTabN := tabOfN (ℍ := ℍ) Φ (spawnPAV (ℍ := ℍ) Φ (tabAtV (ℍ := ℍ) Φ))

theorem tabAtV_eq (Φ : LocFam) (k : Nat) :
    tabAtV (ℍ := ℍ) Φ k = tabOfN (ℍ := ℍ) Φ (spawnPAV (ℍ := ℍ) Φ fun j =>
      if j < k then tabAtV (ℍ := ℍ) Φ j else OpTabN.empty) := by
  rw [tabAtV]; rfl

theorem spawnPAV_down (Φ : LocFam) (Tf : Nat → OpTabN) :
    ∀ k ls v ρ, spawnPAV (ℍ := ℍ) Φ Tf (k + 1) ls v ρ → spawnPAV (ℍ := ℍ) Φ Tf k ls v ρ :=
  fun _ _ _ _ h j hj => h j (by omega)

theorem TJV_down {Φ : LocFam} (hΦ : Φ.Down) : (TJV (ℍ := ℍ) Φ).Down :=
  tabOfN_down hΦ (spawnPAV_down Φ _)

/-! ### A child verified at its indexed table -/

/-- **`tabAtV j`'s stops up to `j` are `TJV`'s**: the entries are the same but for the spawn
payload, and those agree up to `j`. -/
theorem tabAtV_incl (Φ : LocFam) (j : Nat) : ∀ k, k ≤ j → ∀ ls t (Ψ Ψ' : ContN) ρ,
    (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
    opTableN (tabAtV (ℍ := ℍ) Φ j) k ls t Ψ ρ → opTableN (TJV (ℍ := ℍ) Φ) k ls t Ψ' ρ := by
  intro k hk ls t Ψ Ψ' ρ hΨ h
  rcases opTableN_local _ k ls t Ψ Ψ' ρ hΨ h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    rw [tabAtV_eq] at h₃
    obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfN_some h₃
    · exact Or.inl ⟨K, nP, 0, v, _, pure_sep_mk ⟨h₁, h₂, tabOfN_park _ _, h₄⟩
        ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩
    · refine Or.inl ⟨K, nP, 1, v, _, pure_sep_mk ⟨h₁, h₂, tabOfN_spawn _ _, h₄⟩
        ⟨ρa, ρk, hc, fun j' hj' ls' => ?_, hu, hcont⟩⟩
      have := hA j' hj' ls'
      simp only [show j' < j by omega, if_true] at this
      exact this
    · exact Or.inl ⟨K, nP, 2, v, _, pure_sep_mk ⟨h₁, h₂, tabOfN_cancel _ _, h₄⟩
        ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩
  · obtain ⟨⟨-, -, h₃, h₄⟩, -⟩ := pure_sep_iff.mp hp
    rw [tabAtV_eq] at h₃
    exact absurd h₄ (by rw [(tabOfN_ent h₃).1]; simp)

/-- **A child verified at `tabAtV j` at index `j` is verified at `TJV`.** -/
theorem erwp_tabAtV {Φ : LocFam} {Q : PostN} {j : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ (opTableN (tabAtV (ℍ := ℍ) Φ j)) Q j ls e ρ) :
    erwp (ℍ := ℍ) Φ (opTableN (TJV (ℍ := ℍ) Φ)) Q j ls e ρ :=
  erwp_mono_le j (fun _ _ _ _ _ h => h) (tabAtV_incl Φ j) j le_rfl ls e ρ h

/-! ### The invariant and the answers -/

/-- **The pool invariant**: every entry a ready task, tagged `inj₁ ()`, cancellable, its cancel
run at the scheduler's table, resumed at `()` holding nothing. -/
def InvSV (Φ : LocFam) (ts : List StoredN) : Prop :=
  ∀ t ∈ ts, t.tag = Val.inj₁ Val.unit ∧ t.en.q = .cancel ∧ t.Tc = some (TJV (ℍ := ℍ) Φ) ∧
    ∀ k ls, t.en.PB k ls Val.unit PMap.empty

/-- The scheduler's answers. -/
abbrev PA_SV (Φ : LocFam) : PostN := PoolAnsN (ℍ := ℍ) Φ QVN HS (InvSV (ℍ := ℍ) Φ)

/-- A stopped task at an entry of `TJV`, parked as a ready entry. -/
def readyV (Φ : LocFam) (en : OpEntN) (k : Nat) (ls : List SRec) (κ : Val) : StoredN :=
  ⟨PA_SV (ℍ := ℍ) Φ, en, some (TJV (ℍ := ℍ) Φ), k, ls, κ, Val.inj₁ Val.unit⟩

theorem invSV_ready {Φ : LocFam} {en : OpEntN} {k : Nat} {ls : List SRec} {κ : Val}
    {ts : List StoredN} (hq : en.q = .cancel) (hB : en.PB = unitP) (hi : InvSV (ℍ := ℍ) Φ ts) :
    InvSV (ℍ := ℍ) Φ (readyV (ℍ := ℍ) Φ en k ls κ :: ts) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨rfl, hq, rfl, fun _ _ => by simp only [readyV]; rw [hB]; exact ⟨rfl, rfl⟩⟩
  · exact hi x hx

set_option linter.unusedSimpArgs false

/-! ### The clauses -/

/-- What every clause is asked, at an entry of `TJV`. -/
def ClauseV (Φ : LocFam) (N : Nat) (en : OpEntN) (c : Val) : Prop :=
  ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
    (en.PA k ls v ⋆ KapRelN (ℍ := ℍ) Φ (opTableN OpTabN.empty) (PA_SV (ℍ := ℍ) Φ) en
      (some (TJV (ℍ := ℍ) Φ)) k ls κ) ρ →
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (PA_SV (ℍ := ℍ) Φ) k ls
      (.app (.val c) (.pair (.val v) κ.1)) ρ

/-- **`park`'s clause**: the stopped task parked; the top ready, it is resumed and the stopped
task kept beneath it (`poolAnsN_resumeSnd`); otherwise the stopped task resumed
(`poolAnsN_resume`). -/
theorem parkClV_ok {Φ : LocFam} (hΦ : Φ.Down) (N : Nat) :
    ClauseV (ℍ := ℍ) Φ N (enParkN (ℍ := ℍ) Φ) parkCl := by
  rintro k _ ls v κ ρ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := eq_of_compS_empty_left hc
  have hTD := opTableN_down OpTabN.empty_down
  have hD := poolAnsN_down (ℍ := ℍ) Φ QVN HS (InvSV (ℍ := ℍ) Φ)
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
    have hi' : InvSV (ℍ := ℍ) Φ ts := fun x hx => hi x (List.mem_cons_of_mem _ hx)
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
      (invSV_ready (k := k) (ls := ls) (κ := κ) rfl rfl hi')

/-- The scheduler meeting its clauses at every stop below `N`. -/
abbrev SchedBelowV (Φ : LocFam) (N : Nat) : Prop :=
  ∀ N', N' < N → SchedOKNLe (ℍ := ℍ) Φ N' (TJV (ℍ := ℍ) Φ) nP qsS stackRet hsS QVN
    (PA_SV (ℍ := ℍ) Φ)

/-- **`cancel`'s clause**: the stopped task parked; the top ready, it is cancelled, its cancel
branch run under the scheduler below the stop's index, the stopped task kept beneath it
(`poolAnsN_cancelSnd`); otherwise the stopped task resumed (`poolAnsN_resume`). -/
theorem cancelClV_ok {Φ : LocFam} (hΦ : Φ.Down) (N : Nat) (ih : SchedBelowV (ℍ := ℍ) Φ N) :
    ClauseV (ℍ := ℍ) Φ N (enParkN (ℍ := ℍ) Φ) cancelCl := by
  rintro k hkN ls v κ ρ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := eq_of_compS_empty_left hc
  have hTD := opTableN_down OpTabN.empty_down
  have hD := poolAnsN_down (ℍ := ℍ) Φ QVN HS (InvSV (ℍ := ℍ) Φ)
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
    have hi' : InvSV (ℍ := ℍ) Φ ts := fun x hx => hi x (List.mem_cons_of_mem _ hx)
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
      (by rw [hq]; decide) hTc (invSV_ready (k := k) (ls := ls) (κ := κ) rfl rfl hi')

/-- **`spawn`'s clause**: the spawner parked as a ready task (`poolAnsN_park`), the child run
under the scheduler beside the pool below the stop's index (`poolAnsN_run_le`), lifted from its
indexed table (`erwp_tabAtV`). -/
theorem spawnClV_ok {Φ : LocFam} (hΦ : Φ.Down) (N : Nat) (ih : SchedBelowV (ℍ := ℍ) Φ N) :
    ClauseV (ℍ := ℍ) Φ N (enSpawnN (ℍ := ℍ) Φ (spawnPAV (ℍ := ℍ) Φ (tabAtV (ℍ := ℍ) Φ)))
      spawnCl := by
  rintro k hkN ls v κ ρ ⟨ρa, ρk, hc, hth, hκ⟩
  have hTD := opTableN_down OpTabN.empty_down
  have hD := poolAnsN_down (ℍ := ℍ) Φ QVN HS (InvSV (ℍ := ℍ) Φ)
  refine erwp_det hΦ hTD hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v κ)) rfl
    .hole) ?_
  refine erwp_det hΦ hTD hD (fun μ => step1Only_plug (Head.letpair μ v κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine erwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtN_iff.mpr ?_)
  intro ts σ ρ' hi hg hP hc'
  obtain ⟨x, hkx, hax⟩ := (ResU.CompS.assoc ρa ρk σ ρ').mpr ⟨ρ, hc, hc'⟩
  obtain ⟨hP', hg'⟩ := poolAnsN_park (Val.inj₁ Val.unit) hκ (fun _ hm => extF_of_same hm ρk)
    hj hg hP hkx
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
    (invSV_ready (k := k) (ls := ls) (κ := κ) rfl rfl hi) hP' hax
    (erwp_tabAtV (hth j₀ (by omega) ls))

/-- **The return clause**: the list's top resumed with the rest (`poolAnsN_resume`); or, the list
empty, the task's answer the program's. -/
theorem stackRetV_ok {Φ : LocFam} (hΦ : Φ.Down) : ∀ k ls v (ρ : WRes), QVN k ls v ρ →
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (PA_SV (ℍ := ℍ) Φ) k ls
      (.app (.val stackRet) (.val v)) ρ := by
  rintro k ls v ρ rfl
  have hTD := opTableN_down OpTabN.empty_down
  have hD := poolAnsN_down (ℍ := ℍ) Φ QVN HS (InvSV (ℍ := ℍ) Φ)
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
    have hi' : InvSV (ℍ := ℍ) Φ ts := fun x hx => hi x (List.mem_cons_of_mem _ hx)
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
theorem hs_schedOKVLe {Φ : LocFam} (hΦ : Φ.Down) : ∀ N, SchedOKNLe (ℍ := ℍ) Φ N (TJV (ℍ := ℍ) Φ)
    nP qsS stackRet hsS QVN (PA_SV (ℍ := ℍ) Φ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  refine ⟨TJV_down hΦ, fun m i hm => by simp [TJV, tabOfN, hm], fun i en h _ => ?_,
    fun i en h _ _ => ⟨OpTabN.empty, (tabOfN_ent h).2.2.1,
      fun _ _ _ h => by simp [OpTabN.empty] at h⟩,
    fun i en h ls ls' ρ hm => by rw [(tabOfN_ent h).2.2.2.1]; exact extF_of_same hm ρ,
    poolAnsN_down _ _ _ _, fun k _ => stackRetV_ok hΦ k, fun i en h => ?_⟩
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfN_some h <;> rfl
  · have hna : ∀ c, en.abort = true → ∀ k, k ≤ N → ∀ ls v (ρ : WRes), en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (PA_SV (ℍ := ℍ) Φ) k ls
          (.app (.val c) (.val v)) ρ := fun _ ha => by rw [(tabOfN_ent h).1] at ha; cases ha
    obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfN_some h
    · exact ⟨parkCl, by simp [clauseAt, hsS, Val.pair, parkCl]; exact (BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf _).2,
        fun _ => parkClV_ok hΦ N, hna _⟩
    · exact ⟨spawnCl, by simp [clauseAt, hsS, Val.pair, spawnCl]; exact (BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf _).2,
        fun _ => spawnClV_ok hΦ N ih, hna _⟩
    · exact ⟨cancelCl, by simp [clauseAt, hsS, Val.pair, cancelCl]; exact (BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf _).2,
        fun _ => cancelClV_ok hΦ N ih, hna _⟩

/-- **The scheduler `HS` meets `SchedOKN`** at the table `TJV`, its answers functions of its
list, for every list. -/
theorem hs_schedOKV {Φ : LocFam} (hΦ : Φ.Down) : SchedOKN (ℍ := ℍ) Φ (TJV (ℍ := ℍ) Φ) nP qsS
    stackRet hsS QVN (PA_SV (ℍ := ℍ) Φ) := hs_schedOKVLe hΦ

/-- **A scheduler scope inside a task**: `(hnd HS e) (HS, [])`, `e` a task at `TJV` from `ρ`, run
from `ρ` at any table: it answers a value owning nothing, its tasks all ended. The run never stops
outside the scope (`HS` handles every operation of `TJV`), so it is `poolAnsN_run_le` from the
empty pool at the empty table, lifted. -/
theorem erwp_scopeV {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (he : erwp (ℍ := ℍ) Φ (opTableN (TJV (ℍ := ℍ) Φ)) QVN n ls e ρ) :
    erwp (ℍ := ℍ) Φ Tb QVN n ls (.app (hndE HS e) (stateValN HS []).1) ρ := by
  have h := poolAnsN_run_le hΦ (hs_schedOKV hΦ n) le_rfl (fun _ h => by cases h)
    (fun _ h => by cases h) (poolN_nil (Φ := Φ)) (ResU.comp_empty_right ρ) he
  refine erwp_mono (fun _ _ _ _ h => h) (fun k ls t Ψ Ψ' ρ _ h => ?_) n ls _ ρ h
  rcases h with ⟨_, _, _, _, _, h'⟩ | ⟨_, _, _, _, _, h'⟩
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])

end BoCa.Fig16.LogRel.Core.Chain.SI.PoolScope

end
