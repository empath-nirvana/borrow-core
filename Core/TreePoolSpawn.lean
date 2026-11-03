import Core.TreePoolSchedProgs

/-!
# An interleaving scheduler with park, spawn and cancel, through `PoolSchedAdequacyT`  `[spec §62]`

The scheduler `HS` keeps its stopped tasks in its pool (`PoolAns`) and has three operations, all
cancellable, under the name `nP`:

* `park ()` (`enPark`, index 0): the stopped task is parked, and the task that was the pool's
  head is resumed in its place (`poolAns_park`, then `poolAns_resumeSnd`); the pool empty, the
  stopped task is resumed;
* `spawn th` (`enSpawn`, index 1): the spawner is parked at the pool's head and the child `th ()`
  is run under the scheduler beside the pool (`poolAns_park`, then `poolAns_run_le`);
* `cancel ()` (`enPark`, index 2): the stopped task is parked and the task that was the pool's
  head is cancelled, its cancel branch run under the scheduler (`poolAns_park`, then
  `poolAns_cancelSnd`); the pool empty, the stopped task is resumed.

A task's end resumes the pool's head with the rest (`stackRet`). The clauses are proved for every
pool of any length (`hs_schedOK`), by strong induction on the stop index (`SchedOKTLe`): the spawn
clause runs its child below its own index, at the scheduler's clauses there.

**Limits of this example scheduler, not of the theorem.** A child runs at the table `TC` (park and
cancel), so children are spawned from the root only, and a child starts owning nothing (`enSpawn`'s
payload holds no resource). The resume policy exchanges the parked task with the pool's head; it is
not a FIFO queue. Join and cross-task borrow sharing are #795.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.SchedProgs.Spawn
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload hndE hndVal capTag clauseAt ccatchE raiseE
  cancelVal)

/-! ### The tables -/

/-- A child's table: `park` (0) and `cancel` (2). -/
def TC : OpTabT := fun m i =>
  if m = nP then (if i = 0 then some enPark else if i = 2 then some enPark else none) else none

/-- **`spawn`**: the payload a thunk, verified at the child's table from every world and list at
every index below the stop's, at every base frame condition every valid frame meets and present
one every frame meets; it holds no resource. The spawner is answered `()`. -/
def enSpawn : OpEntT where
  q := .cancel
  abort := false
  PA := fun k _ _ v ρ => ρ = PMap.empty ∧ ∀ j, j < k → ∀ (w' : TWd) (ls' : List (SRecT w'.K))
    (Fb Fe : TFrame), (∀ w ρf, ResUT.Valid ρf → Fb w ρf) →
    (∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf) →
    cerwpT (ℍ := ℍ) (opTableT TC) QS Fb Fe j w' ls' [] (.app v.1 (.val Val.unit)) PMap.empty
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ σ = PMap.empty
  fin := true
  fd := fdJoinT
  oc := fun _ _ => True

/-- The root's table: the child's, and `spawn` (1). -/
def TS : OpTabT := fun m i =>
  if m = nP then (if i = 0 then some enPark else if i = 1 then some (enSpawn (ℍ := ℍ))
    else if i = 2 then some enPark else none) else none

theorem TS_some {m i : UInt32} {en : OpEntT} (h : TS (ℍ := ℍ) m i = some en) :
    m = nP ∧ ((i = 0 ∧ en = enPark) ∨ (i = 1 ∧ en = enSpawn (ℍ := ℍ)) ∨ (i = 2 ∧ en = enPark)) := by
  unfold TS at h
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

theorem TC_TS (m i : UInt32) (en : OpEntT) (h : TC m i = some en) : TS (ℍ := ℍ) m i = some en := by
  unfold TC at h; unfold TS
  split at h
  · rename_i hm
    rw [if_pos hm]
    split at h
    · rename_i hi; rw [if_pos hi]; exact h
    · rename_i hi
      split at h
      · rename_i hi2; subst hi2; simpa using h
      · cases h
  · cases h

/-! ### The clauses -/

/-- `park`'s clause: `λ(_, κ). λs. let (h, p) = s in case p {inj₁ q. let (κ', p') = q in
κ' (inj₁ ()) () (h, inj₁ (κ, p')) | inj₂ _. κ (inj₁ ()) () (h, inj₂ ())}`. -/
def swL : Expr := .letpair (.var 0) (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit)
  (.pair (.var 4) (.inj₁ (.pair (.var 6) (.var 0)))))
def swR : Expr := .app (.app (.app (.var 4) (.inj₁ .unit)) .unit) (.pair (.var 2) (.inj₂ .unit))
def swBody : Expr := .letpair (.var 0) (.case (.var 0) swL swR)
def parkCl : Val := Val.lam (.letpair (.var 0) (.lam swBody))

/-- `spawn`'s clause: `λ(th, κ). λs. let (h, p) = s in (hnd h (th ())) (h, inj₁ (κ, p))`. -/
def spBody : Expr := .letpair (.var 0) (.app (.app (.app (.prim .hnd) (.var 1))
  (.app (.var 4) .unit)) (.pair (.var 1) (.inj₁ (.pair (.var 3) (.var 0)))))
def spawnCl : Val := Val.lam (.letpair (.var 0) (.lam spBody))

/-- `cancel`'s clause: `λ(_, κ). λs. let (h, p) = s in case p {inj₁ q. let (κ', p') = q in
(hnd h (κ' (inj₂ ()))) (h, inj₁ (κ, p')) | inj₂ _. κ (inj₁ ()) () (h, inj₂ ())}`. -/
def cnL : Expr := .letpair (.var 0) (.app (.app (.app (.prim .hnd) (.var 4))
  (.app (.var 1) (.inj₂ .unit))) (.pair (.var 4) (.inj₁ (.pair (.var 6) (.var 0)))))
def cnBody : Expr := .letpair (.var 0) (.case (.var 0) cnL swR)
def cancelCl : Val := Val.lam (.letpair (.var 0) (.lam cnBody))

def qsS : Val := Val.pair (Val.i32 1) (Val.pair (Val.i32 1) (Val.pair (Val.i32 1) Val.unit))
def hsS : Val := Val.pair parkCl (Val.pair spawnCl (Val.pair cancelCl Val.unit))
def HS : Val := hndVal nP qsS stackRet hsS

/-- The pool invariant: every stored task is at a cancellable entry whose answer is `()` owning
nothing. -/
def InvS (ts : List StoredT) : Prop :=
  ∀ t ∈ ts, t.en.q = .cancel ∧ t.en.fin = true ∧
    ∀ k w ls, t.en.PBv t.v k w ls Val.unit PMap.empty

theorem invS_cons {t : StoredT} {ts : List StoredT} (h : InvS (t :: ts)) :
    (∀ k w ls, t.en.PBv t.v k w ls Val.unit PMap.empty) ∧ InvS ts :=
  ⟨(h t List.mem_cons_self).2.2, fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

abbrev PA_S : TPostV := PoolAns (ℍ := ℍ) QS HS InvS

set_option linter.unusedSimpArgs false

/-- A substitution below a shift by more than its index undoes one step of the shift. -/
theorem subst_shift0 (d j : Nat) (s : Val) (e : Expr) (h : j ≤ d) :
    Expr.subst j s (Expr.shift (d + 1) 0 e) = Expr.shift d 0 e :=
  Expr.subst_shift d 0 j s e (Nat.zero_le _) (by omega)

/-- Substitution into a clause body after a step. -/
macro "ssimp" : tactic => `(tactic| simp [Kont.plug, Expr.subst, Expr.shift_shift, BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.subst_shift0,
  Expr.shift_zero, swBody, swL, swR, spBody, cnBody, cnL])

/-- **`park`'s clause**: the stopped task parked, the pool's former head resumed in its place
(`poolAns_park`, `poolAns_resumeSnd`); the pool empty, the stopped task resumed. -/
theorem parkCl_ok (N : Nat) :
    SchedClauseTLe (ℍ := ℍ) N HS (PA_S (ℍ := ℍ)) enPark parkCl := by
  rintro F k w ls O v κ ρ _ _ _ _ _ _ _ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := compS_empty_left_eq hc
  rw [cerwpTE_iff]
  have hD := valPost_down (poolAns_down (ℍ := ℍ) QS HS InvS)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl .hole) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine twp_here (fun μ => final_val μ ⟨_, .lam⟩) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  refine ⟨⟨_, .lam⟩, rfl, fun j hj => poolAnsAt_iff.mpr ?_⟩
  intro ts Os σ ρ' hi hg hP hc' hσ hρ hap hcov hv hls hO' F' hF'm hF'M
  have hκ' := KapSchedT.mask_mono (fun x hx => (recMask_rr hO x).mp hx)
    (KapSchedT.kripke hκ hE hr (KeepRel.of_srecsRR hl _) hO)
  obtain ⟨hP', hg'⟩ := poolAns_park (Inv := InvS) hκ' hj hg hP hc' hσ hρ hap
    (CovR.of_compS_left hc' hcov) hls hO'
  have hQD := valPost_down QB_down
  cases j with
  | zero => exact twp_zero
  | succ j₀ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal HS ts)) rfl .hole) ?_
  ssimp
  refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ HS (poolVal ts) _) rfl .hole) ?_
  ssimp
  cases ts with
  | nil =>
    refine twp_det hQD (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    ssimp
    exact poolAns_resume hg' hP' (a := Val.unit) (σ := PMap.empty) ⟨rfl, rfl⟩
      (ResUT.compS_empty_right ρ') (noneAt_empty _) hcov hv hF'm hF'M (fun _ h => by cases h)
  | cons u ts =>
    refine twp_det hQD (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair u.κ (poolVal ts)) _ _) rfl .hole) ?_
    ssimp
    refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ u.κ (poolVal ts) _) rfl .hole) ?_
    ssimp
    have hi' := invS_cons hi
    exact poolAns_resumeSnd hg' hP' hv (hi'.1 _ _ _) (ResUT.compS_empty_right ρ') (noneAt_empty _)
      hcov hv hF'm hF'M (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
        · exact hi'.2 x hx)

/-- **`cancel`'s clause**: the stopped task parked, the pool's former head cancelled, its cancel
branch run under the scheduler with the rest (`poolAns_park`, `poolAns_cancelSnd`); the pool
empty, the stopped task resumed. -/
theorem cancelCl_ok (N : Nat) :
    SchedClauseTLe (ℍ := ℍ) N HS (PA_S (ℍ := ℍ)) enPark cancelCl := by
  rintro F k w ls O v κ ρ _ _ _ _ _ _ _ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := compS_empty_left_eq hc
  rw [cerwpTE_iff]
  have hD := valPost_down (poolAns_down (ℍ := ℍ) QS HS InvS)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl .hole) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine twp_here (fun μ => final_val μ ⟨_, .lam⟩) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  refine ⟨⟨_, .lam⟩, rfl, fun j hj => poolAnsAt_iff.mpr ?_⟩
  intro ts Os σ ρ' hi hg hP hc' hσ hρ hap hcov hv hls hO' F' hF'm hF'M
  have hκ' := KapSchedT.mask_mono (fun x hx => (recMask_rr hO x).mp hx)
    (KapSchedT.kripke hκ hE hr (KeepRel.of_srecsRR hl _) hO)
  obtain ⟨hP', hg'⟩ := poolAns_park (Inv := InvS) hκ' hj hg hP hc' hσ hρ hap
    (CovR.of_compS_left hc' hcov) hls hO'
  have hQD := valPost_down QB_down
  cases j with
  | zero => exact twp_zero
  | succ j₀ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal HS ts)) rfl .hole) ?_
  ssimp
  refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ HS (poolVal ts) _) rfl .hole) ?_
  ssimp
  cases ts with
  | nil =>
    refine twp_det hQD (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    ssimp
    exact poolAns_resume hg' hP' (a := Val.unit) (σ := PMap.empty) ⟨rfl, rfl⟩
      (ResUT.compS_empty_right ρ') (noneAt_empty _) hcov hv hF'm hF'M (fun _ h => by cases h)
  | cons u ts =>
    refine twp_det hQD (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair u.κ (poolVal ts)) _ _) rfl .hole) ?_
    ssimp
    refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ u.κ (poolVal ts) _) rfl .hole) ?_
    ssimp
    have hi' := invS_cons hi
    have hu := (hg' u (by simp)).1
    have h := poolAns_cancelSnd hg' hP' (by rw [(hi u List.mem_cons_self).1]; decide)
      (hi u List.mem_cons_self).2.1 hcov hv hF'm hF'M (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
        · exact hi'.2 x hx)
    rw [hu] at h
    exact h

/-- **`spawn`'s clause at stops up to `N`**, from the scheduler's clauses below `N`: the spawner
parked at the pool's head (`poolAns_park`), the child run under the scheduler beside the pool at
an index below the stop's (`poolAns_run_le`), its table `TC` included in `TS`
(`cerwpT_table_mono`). -/
theorem spawnCl_ok (N : Nat)
    (ih : ∀ N', N' < N → SchedOKTLe (ℍ := ℍ) N' TS nP qsS stackRet hsS QS (PA_S (ℍ := ℍ))) :
    SchedClauseTLe (ℍ := ℍ) N HS (PA_S (ℍ := ℍ)) enSpawn spawnCl := by
  rintro F k w ls O v κ ρ hkN _ _ _ _ _ _ ⟨ρa, ρk, hc, ⟨rfl, hth⟩, hκ⟩
  obtain rfl := compS_empty_left_eq hc
  rw [cerwpTE_iff]
  have hD := valPost_down (poolAns_down (ℍ := ℍ) QS HS InvS)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v κ)) rfl .hole) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ v κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine twp_here (fun μ => final_val μ ⟨_, .lam⟩) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  refine ⟨⟨_, .lam⟩, rfl, fun j hj => poolAnsAt_iff.mpr ?_⟩
  intro ts Os σ ρ' hi hg hP hc' hσ hρ hap hcov hv hls hO' F' hF'm hF'M
  have hκ' := KapSchedT.mask_mono (fun x hx => (recMask_rr hO x).mp hx)
    (KapSchedT.kripke hκ hE hr (KeepRel.of_srecsRR hl _) hO)
  obtain ⟨hP', hg'⟩ := poolAns_park (Inv := InvS) hκ' hj hg hP hc' hσ hρ hap
    (CovR.of_compS_left hc' hcov) hls hO'
  have hQD := valPost_down QB_down
  cases j with
  | zero => exact twp_zero
  | succ j₀ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal HS ts)) rfl .hole) ?_
  ssimp
  refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ HS (poolVal ts) _) rfl .hole) ?_
  ssimp
  have he := cerwpT_table_mono (opTableT_incl (TC_TS (ℍ := ℍ))) j₀ _ w₀ ls₀ [] _ _
    (hth j₀ (by omega) w₀ ls₀ (fun _ _ => True) (fdMask (recMask ([] : List (FrameRecT w₀.K))))
      (fun _ _ _ => trivial) (fun _ _ h => fdMask_le (fun x hx => by simp [recMask] at hx) h))
  have h := poolAns_run_le (ih j₀ (by omega)) le_rfl (fun u hu => (hg' u hu).le (by omega))
    (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
      · exact hi x hx)
    hP' (ResUT.CompS.comm (ResUT.compS_empty_right ρ')) hcov hv (fun _ h => by cases h)
    (NoneAt.of_false (fun x hx => by simp [recMask] at hx) _) (noneAt_empty _)
    (fun _ _ _ => trivial) (fun _ _ h => h) he hF'm (by simpa using hF'M)
  simp only [List.nil_append] at h
  exact h

/-- **The scheduler meets its clauses at stops up to every `N`**, by strong induction on `N`. -/
theorem hs_schedOKLe : ∀ N, SchedOKTLe (ℍ := ℍ) N TS nP qsS stackRet hsS QS (PA_S (ℍ := ℍ)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  refine ⟨fun m i hm => by simp [TS, hm], fun i en h _ => ?_, fun i en h v w O ρf hj => ?_,
    poolAns_down _ _ _, fun F k w ls O v ρ _ => stackRet_okAt (fun t ts hi => invS_cons hi) F k w ls O v ρ,
    fun i en h => ?_⟩
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := TS_some h <;> rfl
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := TS_some h <;> exact hj
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := TS_some h
    · exact ⟨parkCl, by simp [clauseAt, hsS, Val.pair, parkCl, Val.lam, IsVal.lam], parkCl_ok N⟩
    · exact ⟨spawnCl, by simp [clauseAt, hsS, Val.pair, spawnCl, Val.lam, IsVal.lam],
        spawnCl_ok N ih⟩
    · exact ⟨cancelCl, by simp [clauseAt, hsS, Val.pair, cancelCl, Val.lam, IsVal.lam],
        cancelCl_ok N⟩

/-- **The scheduler meets `SchedOKT`** with its answers functions of its pool, for every pool. -/
theorem hs_schedOK : SchedOKT (ℍ := ℍ) TS nP qsS stackRet hsS QS (PA_S (ℍ := ℍ)) :=
  schedOKT_of_le hs_schedOKLe

end BoCa.Fig16.Tree.Wp.SchedProgs.Spawn

end
