import Core.Chain.PoolJoinC
import Core.Fix

/-!
# Where `cerwp` stops an `imm` join from being resumed beside other tasks  `[spec §62]`

Configurations, every hypothesis discharged, about the Capture relation (`cerwp`) and the
scheduler interface over it (`KapRelC`, `SchedOKCLe`, `Core/Chain/PoolC.lean`). They are facts about
the relation, not about joining by task handle: no statement here mentions handles, and each fact
holds of every scheduler meeting `SchedOKCLe`.

**The join's frame condition.** A lend scope (`cerwp_scope`) ends at the resume of `join ℓ`
(`joinEnt`), whose `fd` is `joinFd ℓ`: the resumer's frame flattens to nothing at `ℓ`. A scheduler
resumes a stored continuation only through `KapRelC`, at its frame condition `FdAnd F en v`, beside
everything else it holds.

**Every scheduler's clauses accept a share holding a copy of another task's lend**
(`kapRelC_end`): a continuation that releases a cell it owns and ends through the return clause
meets `KapRelC` at a share holding, beside that cell, anything the scheduler's tasks may end with;
at `HJ`, copies of lends (`hj_joinerEntry`). The relation allows such shares: `crwpG`'s
post-configuration (`EndC`, `SI/Capture.lean`) holds any resource the world admits beside the
frame, without `↭`, and a copy of an `imm` cell the frame holds leaves the world unchanged.

**So an `imm` joiner is not resumable beside such a share** (`not_joinFd_of_holds`), and **two
joiners, each stored beside a copy of the other's lend, are resumable in neither order**
(`hj_joinersDeadlock`, `hj_joinersDeadlock₀`): both are must-resume, and each share owns a cell, so
neither is the other's join answer (`joinPBv_allImm`).

**A task resumed from `join ℓ` is owed `joinFd ℓ` at every later resume** (`fdAnd_joinFd`):
`contShareC` (`SI/CaptureE.lean`) resumes a stop at the run's frame condition and the entry's, so
the condition accumulates. Tasks may end holding a copy at `ℓ` (`hj_qin_copy`), and a frame holding
one falsifies it (`hj_joined_blocked`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Cross821Obs
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.PoolJoin
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack (stackRet)
open BoCa.BoLo (Heap Head Kont freeE hndVal)

/-! ### A continuation every scheduler's clauses accept -/

/-- **`λ_. λa. free c; h_ret a`**: resumed at `a`, it releases `c ↦ own(())` and ends through the return
clause `h_ret` at `a`. -/
def kapEnd (hr : Val) (c : Loc) : Val :=
  Val.lam (.lam (.seq (freeE (.val (Val.loc c))) (.app (.val hr) (.var 0))))

/-- **`kapEnd` meets `KapRelC` for every scheduler meeting `SchedOKCLe`**, at a must-resume entry,
at a share `c ↦ own(()) ● ρr` whenever the scheduler's tasks may end with `ρr` beside any answer
resource the entry hands back. -/
theorem kapRelC_end {N : Nat} {T : OpTabC} {n₀ : UInt32} {qs hr hs : Val} {Qin : PostCV}
    {Qo : (WRes → Prop) → PostCV} {Qc : PostCV}
    (hS : SchedOKCLe (ℍ := ℍ) N T n₀ qs hr hs Qin Qo Qc) (hcl : closedAt 0 hr.1 = true)
    {en : OpEntC} (hq : en.q = .lin) {F : WRes → Prop} {k : Nat} (hk : k ≤ N + 1) {v : Val}
    (c : Loc) {ρ ρr : WRes} (hc : ResU.CompS (ResU.single c (CellU.ownOf Val.unit)) ρr ρ)
    (hQ : ∀ k' ls (w : Val) σ ρ', k' < k → en.PBv v k' ls w σ → ResU.CompS ρr σ ρ' →
      Qin (k' - 1) ls [] w ρ') :
    KapRelC (ℍ := ℍ) Qo Qc en F k [] v (kapEnd hr c) ρ := by
  intro ls' k' hk'
  refine ⟨fun w σ₁ σ₂ hB hcσ => ?_, fun hq' => absurd hq hq'⟩
  obtain ⟨y, hy, hyσ⟩ := compS_reassoc hc hcσ
  have hDE := opTableC_down opTabC_emptyC_down
  have hD := hS.qdown (FdAnd F en v)
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.beta μ _ (Val.inj₁ Val.unit)) rfl
    (.appL .hole w)) ?_
  simp only [Kont.plug, Expr.subst, val_subst_closed hcl]
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  simp only [Kont.plug, Expr.subst, val_subst_closed hcl]
  show cerwp (ℍ := ℍ) _ _ _ _ _ _
    ((Kont.seq .hole (.app (.val hr) (.val w))).plug (freeE (.val (Val.loc c)))) _
  refine cerwp_freeX (opTableC_local _) _ c Val.unit hyσ ?_
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  exact hS.ret _ (k' - 1) (by omega) ls' [] w y (hQ k' ls' w σ₁ y hk' hB hy)

/-! ### Where `joinFd` fails -/

/-- **A valid frame holding a cell at `a` does not flatten to nothing there.** Every frame a run is
asked its frame condition at is valid: `crwpG` asks `F ρf` beside `ρf # ρ`. -/
theorem not_joinFd_of_holds {ρ X y : WRes} {a : Loc} {ψ : CellU Loc Val}
    (hρ : ρ.get a = some ψ) (hc : ResU.CompS ρ X y) (hv : ResU.Valid y) :
    ¬ joinFd (Val.loc a) y := by
  rintro ⟨m, hm, hfree⟩
  obtain rfl : a = m := by
    have := congrArg Subtype.val hm
    simpa [Val.loc, Expr.val, Val.prim] using this
  obtain ⟨τ, hτ⟩ := hv
  have hy := get_eq_none_of_flat hτ (hfree τ hτ)
  rw [((ResU.Comp.eq_none_iff hc a).mp hy).1] at hρ
  cases hρ

/-- **A join's answer holds only `imm` cells**, so a share that owns a cell is no join's answer. -/
theorem joinPBv_allImm {v : Val} {k : Nat} {ls : List SRec} {w : Val} {σ : WRes}
    (h : joinPBv v k ls w σ) : AllImm σ := by
  obtain ⟨m, -, -, hσ⟩ := h
  rcases hσ with rfl | ⟨s, u, hs, rfl⟩
  · exact ViewsC.empty.allImm
  · exact (ViewsC.single m s u hs).allImm

theorem not_allImm_own {c : Loc} {u : Val} {ρr ρ : WRes}
    (hc : ResU.CompS (ResU.single c (CellU.ownOf u)) ρr ρ) (hρr : ρr.get c = none) :
    ¬ AllImm ρ := by
  intro h
  have := h c _ (ResU.compS_single_get_self hc hρr)
  simp [CellU.ownOf, CellU.kind] at this

/-! ### At `HJ`: the stored joiners -/

theorem stackRet_closed : closedAt 0 stackRet.1 = true := by decide

/-- **A joiner of `a` stored at `HJ`**, its share `c ↦ own(())` beside copies `D`: `kapEnd` at
`joinEnt`, resumed at the join's answer, releases `c` and ends holding the copies and the answer. -/
theorem hj_joinerEntry (F : WRes → Prop) (k : Nat) (a c : Loc) {D ρ : WRes}
    (hD : ViewsC D) (hc : ResU.CompS (ResU.single c (CellU.ownOf Val.unit)) D ρ) :
    EntryC (ℍ := ℍ) QinJ
      ⟨PA_J (ℍ := ℍ), joinEnt, F, k, [], Val.loc a, kapEnd stackRet c, fun _ => True, tagL⟩ ρ :=
  ⟨kapRelC_end (hj_schedOKCLe (ℍ := ℍ) k) stackRet_closed rfl (Nat.le_succ k) c hc
    (fun _ _ _ σ _ _ hB hσ => ⟨rfl, hD.comp (by
      obtain ⟨m, -, -, hσ'⟩ := hB
      rcases hσ' with rfl | ⟨s, u', hs, rfl⟩
      · exact .empty
      · exact ViewsC.single m s u' hs) hσ⟩), trivial⟩

/-- `c ↦ own(u) ● ℓ ↦ imm({α}, (), ∅)` at two locations. -/
theorem exists_ownView {c l : Loc} (hcl : c ≠ l) (A : Life) :
    ∃ ρ, ResU.CompS (ResU.single c (CellU.ownOf Val.unit)) (viewA l Val.unit A) ρ :=
  (ResU.compS_defined_iff _ _).mpr (ResU.CompatS.symm (compatS_single_of_get_none
    (by rw [viewA, ResU.single_get_ne _ hcl])))

theorem get_none_of_compS {ρ₁ ρ₂ ρ : WRes} {x : Loc} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : ρ₁.get x = none) (h₂ : ρ₂.get x = none) : ρ.get x = none :=
  (ResU.Comp.eq_none_iff h x).mpr ⟨h₁, h₂⟩

theorem get_some_of_compS_left {ρ₁ ρ₂ ρ : WRes} {x : Loc} {ψ : CellU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ) (h₁ : ρ₁.get x = some ψ) : ρ.get x ≠ none := fun e => by
  rw [((ResU.Comp.eq_none_iff h x).mp e).1] at h₁
  cases h₁

theorem get_some_of_compS_right {ρ₁ ρ₂ ρ : WRes} {x : Loc} {ψ : CellU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ) (h₂ : ρ₂.get x = some ψ) : ρ.get x ≠ none := fun e => by
  rw [((ResU.Comp.eq_none_iff h x).mp e).2] at h₂
  cases h₂

/-- **Two `imm` joiners stored at `HJ`, each beside a copy of the other's lend**, deadlock. Both are
stored entries (`EntryC`) and form a pool; each is owed only at frames flattening to nothing at its
location (`FdAnd · joinEnt (loc ·)`), and every valid frame holding the other's share holds a cell
there; both entries are must-resume, so neither can be cancelled; each share owns a cell, so
neither is the other's join answer (`joinPBv_allImm`). A scheduler holding these two can resume
neither. -/
theorem hj_joinersDeadlock (F : WRes → Prop) (k : Nat) (a b ca cb : Loc) (A : Life)
    (hab : a ≠ b) (hca : ca ≠ a) (hcb : cb ≠ b) (hcab : ca ≠ b) (hcba : cb ≠ a) (hcc : ca ≠ cb) :
    ∃ (ρA ρB ρAB : WRes),
      let tA : StoredC :=
        ⟨PA_J (ℍ := ℍ), joinEnt, F, k, [], Val.loc a, kapEnd stackRet ca, fun _ => True, tagL⟩
      let tB : StoredC :=
        ⟨PA_J (ℍ := ℍ), joinEnt, F, k, [], Val.loc b, kapEnd stackRet cb, fun _ => True, tagL⟩
      PoolC (ℍ := ℍ) QinJ [tA, tB] ρAB ∧ tA.en.q = .lin ∧ tB.en.q = .lin ∧
      (∀ X y, ResU.CompS ρB X y → ResU.Valid y → ¬ FdAnd tA.F tA.en tA.v y) ∧
      (∀ X y, ResU.CompS ρA X y → ResU.Valid y → ¬ FdAnd tB.F tB.en tB.v y) ∧
      ¬ AllImm ρA ∧ ¬ AllImm ρB := by
  obtain ⟨ρA, hA⟩ := exists_ownView hcab A
  obtain ⟨ρB, hB⟩ := exists_ownView hcba A
  have hAB : ∃ ρAB, ResU.CompS ρA ρB ρAB := by
    refine (ResU.compS_defined_iff _ _).mpr (ResU.Compat.of_disjoint fun x => ?_)
    by_cases hxa : x = a
    · subst hxa
      exact Or.inl (get_none_of_compS hA (ResU.single_get_ne _ (Ne.symm hca))
        (by rw [viewA, ResU.single_get_ne _ hab]))
    by_cases hxb : x = b
    · subst hxb
      exact Or.inr (get_none_of_compS hB (ResU.single_get_ne _ (Ne.symm hcb))
        (by rw [viewA, ResU.single_get_ne _ (Ne.symm hab)]))
    by_cases hxc : x = ca
    · subst hxc
      exact Or.inr (get_none_of_compS hB (ResU.single_get_ne _ hcc)
        (by rw [viewA, ResU.single_get_ne _ hca]))
    · exact Or.inl (get_none_of_compS hA (ResU.single_get_ne _ hxc)
        (by rw [viewA, ResU.single_get_ne _ hxb]))
  obtain ⟨ρAB, hAB⟩ := hAB
  refine ⟨ρA, ρB, ρAB, ⟨ρA, ρB, hAB, hj_joinerEntry F k a ca (ViewsC.single _ _ _ _) hA,
    ρB, PMap.empty, ResU.comp_empty_right _, hj_joinerEntry F k b cb (ViewsC.single _ _ _ _) hB,
    rfl⟩, rfl, rfl, fun X y hX hv hF => ?_, fun X y hX hv hF => ?_,
    not_allImm_own hA (ResU.single_get_ne _ hcab),
    not_allImm_own hB (ResU.single_get_ne _ hcba)⟩
  · exact not_joinFd_of_holds (ResU.compS_single_get_self (ResU.CompS.comm hB)
      (ResU.single_get_ne _ hcba.symm)) hX hv hF.2
  · exact not_joinFd_of_holds (ResU.compS_single_get_self (ResU.CompS.comm hA)
      (ResU.single_get_ne _ hcab.symm)) hX hv hF.2

/-- `hj_joinersDeadlock` at four distinct locations. -/
theorem hj_joinersDeadlock₀ : ∃ (ρA ρB ρAB : WRes),
      let tA : StoredC :=
        ⟨PA_J (ℍ := ℍ), joinEnt, fun _ => True, 1, [], Val.loc 0, kapEnd stackRet 2, fun _ => True,
          tagL⟩
      let tB : StoredC :=
        ⟨PA_J (ℍ := ℍ), joinEnt, fun _ => True, 1, [], Val.loc 1, kapEnd stackRet 3, fun _ => True,
          tagL⟩
      PoolC (ℍ := ℍ) QinJ [tA, tB] ρAB ∧ tA.en.q = .lin ∧ tB.en.q = .lin ∧
      (∀ X y, ResU.CompS ρB X y → ResU.Valid y → ¬ FdAnd tA.F tA.en tA.v y) ∧
      (∀ X y, ResU.CompS ρA X y → ResU.Valid y → ¬ FdAnd tB.F tB.en tB.v y) ∧
      ¬ AllImm ρA ∧ ¬ AllImm ρB :=
  hj_joinersDeadlock (fun _ => True) 1 0 1 2 3 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-! ### A joined task, at every later resume -/

/-- **A run resumed from `join ℓ` is owed at `joinFd ℓ` at every later resume**: its frame
condition is `FdAnd F joinEnt (loc ℓ)`, and a stop of it is resumed at that and the stop's entry's
(`contShareC`, `KapRelC`). -/
theorem fdAnd_joinFd {F : WRes → Prop} {v w : Val} {en : OpEntC} {y : WRes}
    (h : FdAnd (FdAnd F joinEnt v) en w y) : joinFd v y := h.1.2

/-- **`HJ`'s tasks may end holding a copy of any lend** (`QinJ`). -/
theorem hj_qin_copy (k : Nat) (ls : List SRec) (v : Val) (a : Loc) (u : Val) (A : Life) :
    QinJ k ls [] v (viewA a u A) := ⟨rfl, ViewsC.single _ _ _ _⟩

/-- **A joined task's later resumes, beside a task's end holding a copy at the joined location**:
every valid frame holding that copy falsifies the frame condition the joined task is owed at. -/
theorem hj_joined_blocked {F : WRes → Prop} {w : Val} {en : OpEntC} (a : Loc) (u : Val)
    (A : Life) {X y : WRes} (hc : ResU.CompS (viewA a u A) X y) (hv : ResU.Valid y) :
    ¬ FdAnd (FdAnd F joinEnt (Val.loc a)) en w y :=
  fun h => not_joinFd_of_holds (ResU.single_get_self _ _) hc hv (fdAnd_joinFd h)

end BoCa.Fig16.LogRel.Core.Chain.SI.Cross821Obs

end
