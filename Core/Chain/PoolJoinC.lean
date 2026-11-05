import Core.Chain.PoolC
import Core.Chain.SI.CaptureScope
import Core.Chain.SI.CaptureScopeM
import Core.TreePoolSpawn

/-!
# A scheduler with `join` over the Capture relation, through `PoolSchedAdequacyC`  `[spec §62]`

The scheduler `HJ` keeps its stopped tasks in a list and has, under the name `nP`,

* `parkC ()` (index 0, cancellable): the stopped task is parked as a cancellable ready task; if
  the list's top is a ready task it is resumed and the stopped task stays beneath it
  (`poolAnsC_park`, then `poolAnsC_resumeSnd`); otherwise the stopped task is resumed;
* `spawn th` (index 1, must-resume): the payload's resource is the child's; the spawner is parked
  as a must-resume ready task and the child `th ()` is run under the scheduler beside the pool
  (`poolAnsC_park`, then `poolAnsC_run_le`);
* `cancel ()` (index 2, must-resume): the stopped task is parked; if the top is a cancellable
  ready task it is cancelled, its cancel branch run under the scheduler
  (`poolAnsC_cancelSnd`); otherwise the stopped task is resumed;
* `join ℓ` (index 3, `joinEnt`): if no other task is stored, the joiner is resumed with the
  borrows of `ℓ` the scheduler's bag holds, the bag keeping the rest; otherwise the scheduler
  diverges;
* `parkL ()` (index 4, must-resume): `parkC` for a task that may not be cancelled.

A task's end (`stackRet`) hands what it holds to the bag and resumes the list's top, or, the list
empty, is the program's answer.

**What a task holds when it ends is a copy of a lend** (`QinJ`): a composite of `imm` cells with
empty witnesses (`ViewsC`). The bag is such a composite, so it splits at any location into the
borrows held there (one `imm` cell, or nothing: `joinPBv`) and the rest, whose flattening holds
nothing there (`ViewsC.flat_none`). That is `joinFd` for the joiner's frame when the pool is empty.

**A join is a barrier, and a joined task runs alone.** `joinEnt`'s `fd` is asked at the joiner's
resume and kept in its frame condition at every later resume (`contShareC`). A stored task's share
is opaque to the scheduler, so `joinFd` can be met only when no other task is stored, and kept only
if no other task is created later. The join clause therefore resumes the joiner only when the list
is empty, and pushes a **marker** beneath it; `spawn` with the marker on top diverges. The marker
resumed acts as a task's end holding nothing (`markerKap`), so the program ends when the joined task
does. The invariant (`InvJ`) says: before any join, every stored task is ready at a trivial frame
condition; after one, the list is the marker alone, the running task's frame condition is implied by
"nothing at the joined locations", and the bag holds nothing there.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.PoolJoin
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.Tree.Wp.SchedProgs.Park (nP)
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack (stackRet retBody retL subst_shift0')
open BoCa.BoLo (Heap Head Kont hndE hndVal clauseAt capTag ccatchE)

/-! ### Copies of lends -/

/-- **A composite of copies**: `imm` cells with empty witnesses. -/
inductive ViewsC : WRes → Prop where
  | empty : ViewsC PMap.empty
  | cons {D D' : WRes} {m : Loc} {s : LSet} {u : Val}
      {h : ResU.InStratum s.join (PMap.empty : WRes)} :
      ViewsC D → ResU.CompS D (ResU.single m (CellU.immOf s u PMap.empty h)) D' → ViewsC D'

/-- One copy. -/
theorem ViewsC.single (m : Loc) (s : LSet) (u : Val)
    (h : ResU.InStratum s.join (PMap.empty : WRes)) :
    ViewsC (ResU.single m (CellU.immOf s u PMap.empty h)) :=
  .cons .empty (compS_empty_left _)

/-- Copies compose to copies. -/
theorem ViewsC.comp {D : WRes} (hD : ViewsC D) : ∀ {L X : WRes}, ViewsC L → ResU.CompS D L X →
    ViewsC X := by
  intro L X hL
  induction hL generalizing X with
  | empty => intro h; rw [ResU.CompS.functional h (ResU.comp_empty_right D)]; exact hD
  | cons hL₀ hc ih =>
      intro h
      obtain ⟨y, hy, hyX⟩ := compS_reassoc' hc h
      exact .cons (ih hy) hyX

/-- Every cell of a composite of copies is `imm`. -/
theorem ViewsC.allImm {D : WRes} (hD : ViewsC D) : AllImm D := by
  induction hD with
  | empty => intro _ _ h; simp at h
  | @cons D D' m s u h hD hc ih =>
      intro x ψ hx
      rcases ResU.Comp.get hc x with ⟨-, -, e⟩ | ⟨ψ₁, e₁, -, e⟩ | ⟨ψ₂, -, e₂, e⟩ |
        ⟨ψ₁, ψ₂, ψ₃, e₁, -, e, hC⟩
      · rw [e] at hx; cases hx
      · rw [e] at hx; cases Option.some.inj hx; exact ih x _ e₁
      · rw [e] at hx; cases Option.some.inj hx
        obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e₂
        exact CellU.kind_immOf _ _ _ _
      · rw [e] at hx; cases Option.some.inj hx
        obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, -, -, rfl⟩ := hC
        exact CellU.kind_immOf _ _ _ _

/-- **A composite of copies flattens to nothing where it holds nothing.** -/
theorem ViewsC.flat_none {D : WRes} (hD : ViewsC D) :
    ∀ τ, ResU.Flat D τ → ∀ x, D.get x = none → τ.get x = none := by
  induction hD with
  | empty => intro τ hτ x _; rw [flat_empty_eq hτ]; rfl
  | @cons D D' m s u h hD hc ih =>
      intro τ hτ x hx
      obtain ⟨σ₁, σ₂, h₁, h₂, h₁₂⟩ := flat_compR hc hτ
      obtain ⟨hDx, hcx⟩ := (ResU.Comp.eq_none_iff hc x).mp hx
      have hxm : x ≠ m := fun e => by subst e; rw [ResU.single_get_self] at hcx; cases hcx
      exact (ResU.Comp.eq_none_iff h₁₂ x).mpr ⟨ih σ₁ h₁ x hDx, flat_single_imm_empty h₂ x hxm⟩

/-- Two cells at one location compose to one cell there. -/
theorem compS_singles {m : Loc} {ψ₁ ψ₂ : CellU Loc Val} {X : WRes}
    (h : ResU.CompS (ResU.single m ψ₁) (ResU.single m ψ₂) X) :
    ∃ ψ, CellU.CompS ψ₁ ψ₂ ψ ∧ X = ResU.single m ψ := by
  rcases ResU.Comp.get h m with ⟨e, -, -⟩ | ⟨ψ, -, e, -⟩ | ⟨ψ, e, -, -⟩ | ⟨χ₁, χ₂, ψ, e₁, e₂, e, hC⟩
  · rw [ResU.single_get_self] at e; cases e
  · rw [ResU.single_get_self] at e; cases e
  · rw [ResU.single_get_self] at e; cases e
  · rw [ResU.single_get_self] at e₁ e₂
    cases Option.some.inj e₁; cases Option.some.inj e₂
    refine ⟨ψ, hC, PMap.ext fun x => ?_⟩
    by_cases hx : x = m
    · subst hx; rw [e, ResU.single_get_self]
    · rw [ResU.single_get_ne _ hx]
      exact (ResU.Comp.eq_none_iff h x).mpr ⟨ResU.single_get_ne _ hx, ResU.single_get_ne _ hx⟩

/-- **A composite of copies splits at a location** into the copies there (one cell, or none) and
the rest, which holds nothing there. -/
theorem ViewsC.split {D : WRes} (hD : ViewsC D) (l : Loc) :
    ∃ Dl Dr, ResU.CompS Dl Dr D ∧
      (Dl = PMap.empty ∨ ∃ (s : LSet) (u : Val) (h : ResU.InStratum s.join (PMap.empty : WRes)),
        Dl = ResU.single l (CellU.immOf s u PMap.empty h)) ∧ ViewsC Dr ∧ Dr.get l = none := by
  induction hD with
  | empty => exact ⟨_, _, compS_empty_left _, .inl rfl, .empty, by simp⟩
  | @cons D D' m s u h hD hc ih =>
      obtain ⟨Dl, Dr, hlr, hDl, hVr, hrl⟩ := ih
      by_cases hm : m = l
      · subst hm
        obtain ⟨a, ha, haD⟩ := compS_exch hlr hc
        refine ⟨a, Dr, haD, .inr ?_, hVr, hrl⟩
        rcases hDl with rfl | ⟨s', u', h', rfl⟩
        · obtain rfl := eq_of_compS_empty_left ha
          exact ⟨s, u, h, rfl⟩
        · obtain ⟨ψ, hC, rfl⟩ := compS_singles ha
          obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, -, rfl⟩ := hC
          obtain ⟨-, -, rfl⟩ := CellU.immOf_inj e₁
          exact ⟨_, v, h₃, rfl⟩
      · obtain ⟨b, hb, hbD⟩ := compS_reassoc hlr hc
        refine ⟨Dl, b, hbD, hDl, .cons hVr hb, ?_⟩
        exact (ResU.Comp.eq_none_iff hb l).mpr ⟨hrl, ResU.single_get_ne _ (Ne.symm hm)⟩

/-- A part of a resource holds nothing where the resource holds nothing. -/
theorem get_none_left {a b c : WRes} (h : ResU.CompS a b c) {x : Loc} (hx : c.get x = none) :
    a.get x = none := ((ResU.Comp.eq_none_iff h x).mp hx).1

theorem get_none_right {a b c : WRes} (h : ResU.CompS a b c) {x : Loc} (hx : c.get x = none) :
    b.get x = none := ((ResU.Comp.eq_none_iff h x).mp hx).2

/-- The flattening of a resource holds nothing at the locations `J`. -/
def NoAt (J : List Loc) (y : WRes) : Prop := ∀ x ∈ J, ∀ τ, ResU.Flat y τ → τ.get x = none

theorem ViewsC.noAt {D : WRes} (hD : ViewsC D) {J : List Loc} (hJ : ∀ x ∈ J, D.get x = none) :
    NoAt J D := fun x hx τ hτ => hD.flat_none τ hτ x (hJ x hx)

/-! ### The entries and the tables -/

/-- A task's answer at the scheduler, and a cancel run's: owning no record, holding copies. -/
def QinJ : PostCV := fun _ _ O _ ρ => O = [] ∧ ViewsC ρ

theorem QinJ_down : QinJ.Down := fun _ _ _ _ _ h => h

/-- The program's answer: owning no record, holding only `imm` cells. -/
def QJ : PostCV := fun _ _ O _ ρ => O = [] ∧ AllImm ρ

theorem QJ_down : QJ.Down := fun _ _ _ _ _ h => h

/-- `()`, owning nothing. -/
def unitPJ : Nat → List SRec → Val → WProp := fun _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty

/-- `parkC`: cancellable, no payload and no answer resource, its cancel run `PcanC QinJ`, its
stop owning no record. -/
def enParkC : OpEntC :=
  { q := .cancel, abort := false, PA := unitPJ, PB := unitPJ, fin := some (PcanC (ℍ := ℍ) QinJ),
    wc := fun _ _ _ => True, fd := fun _ _ => True, PBv := fun _ => unitPJ,
    oc := fun O => O = [] }

/-- A must-resume entry at a payload condition, answered `()` owning nothing. -/
def enLinN (PA : Nat → List SRec → Val → WProp) : OpEntN :=
  ⟨.lin, false, PA, unitPJ, none, fun _ _ _ => True⟩

/-- **A child, run as a new task**: at every index `j` below `k`, at every list, `th ()` from the
payload's resource at the table `Tf j`, under the trivial frame condition, owning no record. -/
def spawnPAC (Tf : Nat → OpTabC) : Nat → List SRec → Val → WProp := fun k _ th ρ =>
  ∀ j, j < k → ∀ ls, cerwp (ℍ := ℍ) (opTableC (Tf j)) QinJ (fun _ => True) j ls []
    (.app th.1 (.val Val.unit)) ρ

theorem spawnPAC_down (Tf : Nat → OpTabC) :
    ∀ k ls v ρ, spawnPAC (ℍ := ℍ) Tf (k + 1) ls v ρ → spawnPAC (ℍ := ℍ) Tf k ls v ρ :=
  fun _ _ _ _ h j hj => h j (by omega)

/-- The table, its spawn payload given. -/
def tabOfC (PS : Nat → List SRec → Val → WProp) : OpTabC := fun m i =>
  if m = nP then
    (if i = 0 then some (enParkC (ℍ := ℍ)) else if i = 1 then some (liftEnt (enLinN PS))
      else if i = 2 then some (liftEnt (enLinN unitPJ)) else if i = 3 then some joinEnt
      else if i = 4 then some (liftEnt (enLinN unitPJ)) else none)
  else none

/-- Its must-resume part: what a lend scope's body and join stop at. -/
def tabLinC (PS : Nat → List SRec → Val → WProp) : OpTabC := fun m i =>
  if m = nP then
    (if i = 1 then some (liftEnt (enLinN PS))
      else if i = 2 then some (liftEnt (enLinN unitPJ)) else if i = 3 then some joinEnt
      else if i = 4 then some (liftEnt (enLinN unitPJ)) else none)
  else none

/-- A lend scope's body's table, at `erwp`. -/
def tabInN (PS : Nat → List SRec → Val → WProp) : OpTabN := fun m i =>
  if m = nP then
    (if i = 1 then some (enLinN PS) else if i = 2 then some (enLinN unitPJ)
      else if i = 4 then some (enLinN unitPJ) else none)
  else none

/-- **The table at index `k`**: its children's tables are those below `k`. -/
def tabAtC : Nat → OpTabC
  | k => tabOfC (ℍ := ℍ) (spawnPAC (ℍ := ℍ) fun j => if _h : j < k then tabAtC j
      else OpTabC.emptyC)
termination_by k => k

/-- **The scheduler's table**: its children's tables are the indexed ones. -/
def TJC : OpTabC := tabOfC (ℍ := ℍ) (spawnPAC (ℍ := ℍ) (tabAtC (ℍ := ℍ)))

theorem tabAtC_eq (k : Nat) :
    tabAtC (ℍ := ℍ) k = tabOfC (ℍ := ℍ) (spawnPAC (ℍ := ℍ) fun j =>
      if j < k then tabAtC (ℍ := ℍ) j else OpTabC.emptyC) := by
  rw [tabAtC]; rfl

theorem tabOfC_some {PS : Nat → List SRec → Val → WProp} {m i : UInt32} {en : OpEntC}
    (h : tabOfC (ℍ := ℍ) PS m i = some en) :
    m = nP ∧ ((i = 0 ∧ en = enParkC (ℍ := ℍ)) ∨ (i = 1 ∧ en = liftEnt (enLinN PS)) ∨
      (i = 2 ∧ en = liftEnt (enLinN unitPJ)) ∨ (i = 3 ∧ en = joinEnt) ∨
      (i = 4 ∧ en = liftEnt (enLinN unitPJ))) := by
  unfold tabOfC at h
  split at h
  · rename_i hm
    refine ⟨hm, ?_⟩
    split at h
    · cases h; exact Or.inl ⟨by assumption, rfl⟩
    split at h
    · cases h; exact Or.inr (Or.inl ⟨by assumption, rfl⟩)
    split at h
    · cases h; exact Or.inr (Or.inr (Or.inl ⟨by assumption, rfl⟩))
    split at h
    · cases h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by assumption, rfl⟩)))
    split at h
    · cases h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by assumption, rfl⟩)))
    · cases h
  · cases h

theorem tabLinC_sub (PS : Nat → List SRec → Val → WProp) :
    (tabLinC PS).Sub (tabOfC (ℍ := ℍ) PS) := by
  intro m i en h
  unfold tabLinC at h
  unfold tabOfC
  split at h
  · rename_i hm
    rw [if_pos hm]
    have h0 : i ≠ 0 := by
      rintro rfl
      simp at h
    rw [if_neg h0]
    exact h
  · cases h

theorem tabLinC_lin {PS : Nat → List SRec → Val → WProp} {m i : UInt32} {en : OpEntC}
    (h : tabLinC PS m i = some en) : en.q = .lin := by
  unfold tabLinC at h
  split at h
  · split at h
    · cases h; rfl
    split at h
    · cases h; rfl
    split at h
    · cases h; rfl
    split at h
    · cases h; rfl
    · cases h
  · cases h

theorem tabOfC_down {PS : Nat → List SRec → Val → WProp}
    (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ) : (tabOfC (ℍ := ℍ) PS).Down where
  pa := fun _ _ en h k ls v ρ hA => by
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := tabOfC_some h
    · exact hA
    · exact hPS k ls v ρ hA
    · exact hA
    · exact hA
    · exact hA
  fin := fun _ _ en P h hP => by
    obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := tabOfC_some h <;>
      cases hP
    exact fun k ls e ρ hk F => cerwp_le (opTableC_local _) (opTableC_down opTabC_emptyC_down)
      QinJ_down (Nat.le_succ k) (hk F)

theorem tabLinC_down {PS : Nat → List SRec → Val → WProp}
    (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ) : (tabLinC PS).Down where
  pa := fun _ _ en h k ls v ρ hA => by
    simp only [tabLinC] at h
    split_ifs at h <;> cases h <;> first | exact hA | exact hPS _ _ _ _ hA
  fin := fun _ _ en P h hP => by
    simp only [tabLinC] at h
    split_ifs at h <;> cases h <;> cases hP

/-- A lend scope's tables: the body's entries lifted, and the join at `(nP, 3)`. -/
theorem scopeTabs (PS : Nat → List SRec → Val → WProp) :
    ScopeTabs (tabInN PS) (tabLinC PS) nP 3 where
  inner := fun m i en h => by
    unfold tabInN at h
    split at h
    · rename_i hm
      subst hm
      split at h
      · rename_i hi; subst hi; cases h
        exact ⟨rfl, rfl, fun _ _ _ _ _ _ _ => trivial, fun _ _ _ _ hB => hB.2, by simp [tabLinC]⟩
      split at h
      · rename_i hi; subst hi; cases h
        exact ⟨rfl, rfl, fun _ _ _ _ _ _ _ => trivial, fun _ _ _ _ hB => hB.2, by simp [tabLinC]⟩
      split at h
      · rename_i hi; subst hi; cases h
        exact ⟨rfl, rfl, fun _ _ _ _ _ _ _ => trivial, fun _ _ _ _ hB => hB.2, by simp [tabLinC]⟩
      · cases h
    · cases h
  join := by simp [tabLinC]

theorem TJC_down : (TJC (ℍ := ℍ)).Down := tabOfC_down (spawnPAC_down _)

/-! ### A child verified at its indexed table -/

/-- **`tabAtC j`'s stops up to `j` are `TJC`'s**: the entries are the same but for the spawn
payload, and those agree up to `j`. -/
theorem tabAtC_incl (j : Nat) : InclLeC j (tabAtC (ℍ := ℍ) j) (TJC (ℍ := ℍ)) := by
  intro F k hk ls O t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, hp⟩ := opTableC_local _ F k ls O t Ψ Ψ' ρ hΨ h
  obtain ⟨⟨h₁, h₂, h₃, h₄, h₅⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp hp
  rw [tabAtC_eq] at h₃
  obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfC_some h₃
  · exact ⟨K, nP, 0, v, _, pure_sep_mk ⟨h₁, h₂, by simp [TJC, tabOfC], h₄, h₅⟩
      ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩
  · refine ⟨K, nP, 1, v, liftEnt (enLinN (spawnPAC (ℍ := ℍ) (tabAtC (ℍ := ℍ)))),
      pure_sep_mk ⟨h₁, h₂, by simp [TJC, tabOfC], h₄, h₅⟩
      ⟨ρa, ρk, hc, fun j' hj' ls' => ?_, hu, hcont⟩⟩
    have := hA j' hj' ls'
    simp only [show j' < j by omega, if_true] at this
    exact this
  · exact ⟨K, nP, 2, v, _, pure_sep_mk ⟨h₁, h₂, by simp [TJC, tabOfC], h₄, h₅⟩
      ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩
  · exact ⟨K, nP, 3, v, _, pure_sep_mk ⟨h₁, h₂, by simp [TJC, tabOfC], h₄, h₅⟩
      ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩
  · exact ⟨K, nP, 4, v, _, pure_sep_mk ⟨h₁, h₂, by simp [TJC, tabOfC], h₄, h₅⟩
      ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩

/-- **A child verified at `tabAtC j` at index `j` is verified at `TJC`.** -/
theorem cerwp_tabAtC {Q : PostCV} {F : WRes → Prop} {j : Nat} {ls : List SRec}
    {O : List FrameRec} {e : Expr} {ρ : WRes}
    (h : cerwp (ℍ := ℍ) (opTableC (tabAtC (ℍ := ℍ) j)) Q F j ls O e ρ) :
    cerwp (ℍ := ℍ) (opTableC (TJC (ℍ := ℍ))) Q F j ls O e ρ :=
  cerwp_tab_mono_le (tabAtC_incl j) j le_rfl F ls O e ρ h

/-! ### The scheduler's code -/

/-- The tags: a cancellable ready task, a must-resume ready task, the marker. -/
def tagCE : Expr := .inj₁ (.inj₁ .unit)
def tagLE : Expr := .inj₁ (.inj₂ .unit)
def tagC : Val := Val.inj₁ (Val.inj₁ Val.unit)
def tagL : Val := Val.inj₁ (Val.inj₂ Val.unit)
def tagM : Val := Val.inj₂ Val.unit

/-- `park`'s body, the stopped task tagged `tg`, under `h, p, s, κ, v`: the top ready,
`κ′ (inj₁ ()) () (h, inj₁ ((tg, κ), p′))`; the top the marker or the list empty,
`κ (inj₁ ()) () (h, p)`. -/
def parkBT (tg : Expr) : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.letpair (.var 1) (.case (.var 1)
      (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit)
        (.pair (.var 7) (.inj₁ (.pair (.pair tg (.var 9)) (.var 3)))))
      (.app (.app (.app (.var 9) (.inj₁ .unit)) .unit) (.pair (.var 7) (.var 6))))))
    (.app (.app (.app (.var 4) (.inj₁ .unit)) .unit) (.pair (.var 2) (.var 1)))

/-- `cancel`'s body: the top a cancellable ready task,
`(hnd h (κ′ (inj₂ ()))) (h, inj₁ ((tagL, κ), p′))`; otherwise `κ (inj₁ ()) () (h, p)`. -/
def cancelBJ : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.letpair (.var 1) (.case (.var 1)
      (.case (.var 0)
        (.app (.app (.app (.prim .hnd) (.var 8)) (.app (.var 2) (.inj₂ .unit)))
          (.pair (.var 8) (.inj₁ (.pair (.pair tagLE (.var 10)) (.var 4)))))
        (.app (.app (.app (.var 10) (.inj₁ .unit)) .unit) (.pair (.var 8) (.var 7))))
      (.app (.app (.app (.var 9) (.inj₁ .unit)) .unit) (.pair (.var 7) (.var 6))))))
    (.app (.app (.app (.var 4) (.inj₁ .unit)) .unit) (.pair (.var 2) (.var 1)))

/-- `spawn`'s body: the top the marker, divergence; otherwise
`(hnd h (th ())) (h, inj₁ ((tagL, κ), p))`. -/
def spawnBJ : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.letpair (.var 1) (.case (.var 1)
      (.app (.app (.app (.prim .hnd) (.var 7)) (.app (.var 10) .unit))
        (.pair (.var 7) (.inj₁ (.pair (.pair tagLE (.var 9)) (.var 6)))))
      omegaE)))
    (.app (.app (.app (.prim .hnd) (.var 2)) (.app (.var 5) .unit))
      (.pair (.var 2) (.inj₁ (.pair (.pair tagLE (.var 4)) (.var 1)))))

/-- The marker's continuation: resumed, a task's end holding nothing. -/
def κM : Val := Val.lam (.lam (.app (.val stackRet) (.val Val.unit)))

/-- `join`'s body: the list empty, `κ (inj₁ ()) () (h, inj₁ ((tagM, κM), p))`; the top the marker,
`κ (inj₁ ()) () (h, p)`; the top a ready task, divergence. -/
def joinBJ : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.letpair (.var 1) (.case (.var 1)
      omegaE
      (.app (.app (.app (.var 9) (.inj₁ .unit)) .unit) (.pair (.var 7) (.var 6))))))
    (.app (.app (.app (.var 4) (.inj₁ .unit)) .unit)
      (.pair (.var 2) (.inj₁ (.pair (.pair (.inj₂ .unit) (.val κM)) (.var 1)))))

def parkClC : Val := BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf (parkBT tagCE)
def parkClL : Val := BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf (parkBT tagLE)
def spawnClJ : Val := BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf spawnBJ
def cancelClJ : Val := BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf cancelBJ
def joinClJ : Val := BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf joinBJ

def qsJ : Val := qualsVal [.cancel, .lin, .lin, .lin, .lin]
def hsJ : Val :=
  Val.pair parkClC (Val.pair spawnClJ (Val.pair cancelClJ (Val.pair joinClJ
    (Val.pair parkClL Val.unit))))
/-- **The scheduler.** -/
def HJ : Val := hndVal nP qsJ stackRet hsJ

/-! ### The invariant and the answers -/

/-- **A ready stored task**: resumed at a trivial frame condition, at `()` holding nothing;
tagged cancellable (its entry cancellable, its stop owning no record) or must-resume. -/
def ReadyOK (t : StoredC) : Prop :=
  (∀ y, t.F y) ∧ (∀ y, t.en.fd t.v y) ∧ (∀ k ls, t.en.PBv t.v k ls Val.unit PMap.empty) ∧
    ((t.tag = tagC ∧ t.en.q ≠ .lin ∧ t.O = []) ∨ t.tag = tagL)

/-- **The marker**: tagged `tagM`, holding nothing, resumed at a trivial frame condition at `()`
holding nothing. -/
def MarkerOK (t : StoredC) : Prop :=
  t.tag = tagM ∧ (∀ ρ, t.R ρ → ρ = PMap.empty) ∧ (∀ y, t.F y) ∧ (∀ y, t.en.fd t.v y) ∧
    (∀ k ls, t.en.PBv t.v k ls Val.unit PMap.empty) ∧ t.O = []

/-- **The pool invariant at the running task's frame condition `F`**: the bag a composite of
copies; and either no join has happened (`F` trivial, every stored task ready), or one has (the
list the marker alone, `F` implied by "nothing at the joined locations `J`", the bag holding
nothing there). -/
def InvJ (F : WRes → Prop) (ts : List StoredC) (D : WRes) : Prop :=
  ViewsC D ∧ (((∀ y, F y) ∧ ∀ t ∈ ts, ReadyOK t) ∨
    (∃ t, ts = [t] ∧ MarkerOK t ∧ ∃ J : List Loc, (∀ y, NoAt J y → F y) ∧
      ∀ x ∈ J, D.get x = none))

/-- The scheduler's answers. -/
abbrev PA_J : (WRes → Prop) → PostCV := PoolAnsC (ℍ := ℍ) QinJ QJ HJ InvJ

set_option linter.unusedSimpArgs false

/-- Substitution into a clause body after a step. -/
syntax "jsimp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| jsimp) => `(tactic| simp [Kont.plug, Expr.subst, Expr.shift_shift,
      BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.subst_shift0, Expr.shift_zero, BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf, parkBT,
      cancelBJ, spawnBJ, joinBJ, tagCE, tagLE, stateValC, poolValC])
  | `(tactic| jsimp [$ls,*]) => `(tactic| simp [Kont.plug, Expr.subst, Expr.shift_shift,
      BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.subst_shift0, Expr.shift_zero, BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf, parkBT,
      cancelBJ, spawnBJ, joinBJ, tagCE, tagLE, stateValC, poolValC, $ls,*])

/-! ### The return clause -/

/-- **The return clause**: what the task holds joins the bag; the list's top is resumed
(`poolAnsC_resume`), or, the list empty, the task's answer is the program's. -/
theorem stackRetJ_ok (F : WRes → Prop) : ∀ k ls O (v : Val) (ρ : WRes), QinJ k ls O v ρ →
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (PA_J (ℍ := ℍ) F) F k ls O
      (.app (.val stackRet) (.val v)) ρ := by
  rintro k ls O v ρ ⟨rfl, hV⟩
  have hDE := opTableC_down opTabC_emptyC_down
  refine cerwp_det hDE (poolAnsC_down _ _ _ _ _) (fun μ => step1Only_plug (Head.beta μ _ v) rfl
    .hole) ?_
  simp only [Kont.plug]
  refine cerwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtC_iff.mpr ?_)
  intro ts D σ ρ' hi hg hP hc hd
  obtain ⟨hVD, hi⟩ := hi
  cases ts with
  | nil =>
    obtain ⟨a, b, hab, rfl, rfl⟩ := hP
    obtain rfl := eq_of_compS_empty_left hab
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.beta μ _ (stateValC HJ []))
      rfl .hole) ?_
    simp [Kont.plug, Expr.subst, retBody, retL, stateValC, poolValC, Expr.shift_shift,
      subst_shift0', Expr.shift_zero]
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.letpair μ HJ (Val.inj₂ Val.unit) _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
      .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    exact cerwp_val (v := v) ⟨rfl, (hV.comp hVD hc).allImm⟩
  | cons t ts =>
    cases j with
    | zero => exact cerwp_zero
    | succ j₀ =>
    -- the task's holdings join the bag
    obtain ⟨p, d, hpd, hPp, rfl⟩ := hP
    obtain ⟨D', hD', hρD⟩ := compS_lcomm hpd hc
    have hP' : (PoolC (ℍ := ℍ) QinJ (t :: ts) ⋆ fun x => x = D') ρ' :=
      ⟨p, D', hρD, hPp, rfl⟩
    have hVD' : ViewsC D' := hV.comp hVD hD'
    -- what the top is resumed at
    have htop : (∀ y, t.F y) ∧ (∀ y, t.en.fd t.v y) ∧
        (∀ k ls, t.en.PBv t.v k ls Val.unit PMap.empty) ∧
        (∀ u ∈ ts, ReadyOK u) := by
      rcases hi with ⟨-, hr⟩ | ⟨u, hu, hm, -⟩
      · obtain ⟨h₁, h₂, h₃, -⟩ := hr t List.mem_cons_self
        exact ⟨h₁, h₂, h₃, fun u hu => hr u (List.mem_cons_of_mem _ hu)⟩
      · obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hu
        obtain ⟨-, -, h₁, h₂, h₃, -⟩ := hm
        exact ⟨h₁, h₂, h₃, fun _ h => by cases h⟩
    obtain ⟨hF₁, hF₂, hB, hr⟩ := htop
    refine cerwp_step (opTableC_local _) (fun μ => step1Only_plug
      (Head.beta μ _ (stateValC HJ (t :: ts))) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, retBody, retL, stateValC, poolValC, Expr.shift_shift,
      subst_shift0', Expr.shift_zero]
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.letpair μ HJ (poolValC (t :: ts)) _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, poolValC, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair t.tag t.κ) (poolValC ts)) _ _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair t.tag t.κ) (poolValC ts) _) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ t.tag t.κ _) rfl
      .hole) ?_
    simp [Kont.plug, Expr.subst, Expr.shift_shift, subst_shift0', Expr.shift_zero]
    exact poolAnsC_resume hg hP' (compS_empty_left D') (hB _ _)
      (fun _ _ y _ => ⟨hF₁ y, hF₂ y⟩) ⟨hVD', .inl ⟨fun y => ⟨hF₁ y, hF₂ y⟩, hr⟩⟩ hd.tail

/-! ### The clauses -/

/-- What every clause is asked, at an entry of `TJC`. -/
def ClauseJ (N : Nat) (en : OpEntC) (c : Val) : Prop :=
  ∀ (F : WRes → Prop) k, k ≤ N → ∀ ls O (v κ : Val) ρ, en.oc O →
    (en.PA k ls v ⋆ KapRelC (ℍ := ℍ) (PA_J (ℍ := ℍ)) QinJ en F k O v κ) ρ →
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (PA_J (ℍ := ℍ) F) F k ls O
      (.app (.val c) (.pair (.val v) κ.1)) ρ

/-- A stored task's resources, the marker alone: nothing. -/
theorem poolC_marker {u : StoredC} (hm : MarkerOK u) {σ : WRes}
    (h : PoolC (ℍ := ℍ) QinJ [u] σ) : σ = PMap.empty := by
  obtain ⟨a, b, hab, ⟨-, hR⟩, rfl⟩ := h
  obtain rfl := hm.2.1 a hR
  exact (eq_of_compS_empty_left hab)

/-- **`parkC`'s clause**: the stopped task parked as a cancellable ready task; the top ready, it
is resumed and the stopped task kept beneath it (`poolAnsC_resumeSnd`); otherwise the stopped task
resumed (`poolAnsC_resume`). -/
theorem parkClC_ok (N : Nat) : ClauseJ (ℍ := ℍ) N (enParkC (ℍ := ℍ)) parkClC := by
  rintro F k _ ls O v κ ρ hoc ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  have hO : O = [] := hoc
  subst hO
  obtain rfl := eq_of_compS_empty_left hc
  have hDE := opTableC_down opTabC_emptyC_down
  have hD := poolAnsC_down (ℍ := ℍ) QinJ QJ HJ InvJ F
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl
    .hole) ?_
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine cerwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtC_iff.mpr ?_)
  intro ts D σ ρ' hi hg hP hc' hd
  obtain ⟨hP', hg'⟩ := poolAnsC_park (fun _ => True) tagC hκ trivial hj hg hP hc'
  obtain ⟨hVD, hi⟩ := hi
  cases j with
  | zero => exact cerwp_zero
  | succ j₀ =>
  refine cerwp_step (opTableC_local _) (fun μ => step1Only_plug (Head.beta μ _ (stateValC HJ ts))
    rfl .hole) ?_
  jsimp
  refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ HJ (poolValC ts) _)
    rfl .hole) ?_
  jsimp
  cases ts with
  | nil =>
    have hF : ∀ y, F y := by
      rcases hi with ⟨hF, -⟩ | ⟨u, hu, -⟩
      · exact hF
      · cases hu
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
      .hole) ?_
    jsimp
    exact poolAnsC_resume hg' hP' (compS_empty_left D) ⟨rfl, rfl⟩
      (fun _ _ y _ => ⟨hF y, trivial⟩) ⟨hVD, .inl ⟨fun y => ⟨hF y, trivial⟩, fun _ h => by cases h⟩⟩
      (by simpa using hd)
  | cons u ts =>
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair u.tag u.κ) (poolValC ts)) _ _) rfl .hole) ?_
    jsimp
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair u.tag u.κ) (poolValC ts) _) rfl .hole) ?_
    jsimp
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ u.tag u.κ _) rfl
      .hole) ?_
    jsimp
    rcases hi with ⟨hF, hr⟩ | ⟨u', hu, hm, J, hJF, hJD⟩
    · -- the top ready: resumed, the stopped task beneath it
      obtain ⟨hu₁, hu₂, hu₃, htag⟩ := hr u List.mem_cons_self
      obtain ⟨x, hx⟩ : ∃ x, u.tag = Val.inj₁ x := by
        rcases htag with ⟨h, -⟩ | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      rw [hx]
      refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₁ μ x _ _) rfl .hole) ?_
      jsimp
      refine poolAnsC_resumeSnd hg' hP' (compS_empty_left D) (hu₃ _ _)
        (fun _ _ y _ => ⟨hu₁ y, hu₂ y⟩) ⟨hVD, .inl ⟨fun y => ⟨hu₁ y, hu₂ y⟩, fun t ht => ?_⟩⟩
        (by simpa using hd)
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hF, fun _ => trivial, fun _ _ => ⟨rfl, rfl⟩, .inl ⟨rfl, (fun h => by cases h), rfl⟩⟩
      · exact hr t (List.mem_cons_of_mem _ ht)
    · -- the top the marker: the stopped task resumed, alone with it
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hu
      have hm' := hm
      obtain ⟨htag, -, -, -, -, -⟩ := hm
      rw [htag]
      refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
        .hole) ?_
      jsimp
      rw [show (tagM : Val) = u.tag from htag.symm]
      refine cerwp_perm (fun p => by simp [recsC]) (poolAnsC_resume hg' hP' (compS_empty_left D)
        ⟨rfl, rfl⟩ (fun σr hσr y hy => ?_)
        ⟨hVD, .inr ⟨u, rfl, hm', J, fun y hy => ⟨hJF y hy, trivial⟩, hJD⟩⟩ (by simpa using hd))
      obtain rfl := poolC_marker hm' hσr
      obtain rfl := eq_of_compS_empty_left hy
      exact ⟨hJF _ (hVD.noAt hJD), trivial⟩

/-- **`parkL`'s clause**: `parkC`'s, the stopped task parked as a must-resume ready task; the top ready, it
is resumed and the stopped task kept beneath it (`poolAnsC_resumeSnd`); otherwise the stopped task
resumed (`poolAnsC_resume`). -/
theorem parkClL_ok (N : Nat) : ClauseJ (ℍ := ℍ) N (liftEnt (enLinN unitPJ)) parkClL := by
  rintro F k _ ls O v κ ρ - ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := eq_of_compS_empty_left hc
  have hDE := opTableC_down opTabC_emptyC_down
  have hD := poolAnsC_down (ℍ := ℍ) QinJ QJ HJ InvJ F
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl
    .hole) ?_
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine cerwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtC_iff.mpr ?_)
  intro ts D σ ρ' hi hg hP hc' hd
  obtain ⟨hP', hg'⟩ := poolAnsC_park (fun _ => True) tagL hκ trivial hj hg hP hc'
  obtain ⟨hVD, hi⟩ := hi
  cases j with
  | zero => exact cerwp_zero
  | succ j₀ =>
  refine cerwp_step (opTableC_local _) (fun μ => step1Only_plug (Head.beta μ _ (stateValC HJ ts))
    rfl .hole) ?_
  jsimp
  refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ HJ (poolValC ts) _)
    rfl .hole) ?_
  jsimp
  cases ts with
  | nil =>
    have hF : ∀ y, F y := by
      rcases hi with ⟨hF, -⟩ | ⟨u, hu, -⟩
      · exact hF
      · cases hu
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
      .hole) ?_
    jsimp
    exact poolAnsC_resume hg' hP' (compS_empty_left D) ⟨rfl, rfl⟩
      (fun _ _ y _ => ⟨hF y, trivial⟩) ⟨hVD, .inl ⟨fun y => ⟨hF y, trivial⟩, fun _ h => by cases h⟩⟩
      (by simpa using hd)
  | cons u ts =>
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair u.tag u.κ) (poolValC ts)) _ _) rfl .hole) ?_
    jsimp
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair u.tag u.κ) (poolValC ts) _) rfl .hole) ?_
    jsimp
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ u.tag u.κ _) rfl
      .hole) ?_
    jsimp
    rcases hi with ⟨hF, hr⟩ | ⟨u', hu, hm, J, hJF, hJD⟩
    · -- the top ready: resumed, the stopped task beneath it
      obtain ⟨hu₁, hu₂, hu₃, htag⟩ := hr u List.mem_cons_self
      obtain ⟨x, hx⟩ : ∃ x, u.tag = Val.inj₁ x := by
        rcases htag with ⟨h, -⟩ | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      rw [hx]
      refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₁ μ x _ _) rfl .hole) ?_
      jsimp
      refine poolAnsC_resumeSnd hg' hP' (compS_empty_left D) (hu₃ _ _)
        (fun _ _ y _ => ⟨hu₁ y, hu₂ y⟩) ⟨hVD, .inl ⟨fun y => ⟨hu₁ y, hu₂ y⟩, fun t ht => ?_⟩⟩
        (by simpa using hd)
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hF, fun _ => trivial, fun _ _ => ⟨rfl, rfl⟩, .inr rfl⟩
      · exact hr t (List.mem_cons_of_mem _ ht)
    · -- the top the marker: the stopped task resumed, alone with it
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hu
      have hm' := hm
      obtain ⟨htag, -, -, -, -, -⟩ := hm
      rw [htag]
      refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
        .hole) ?_
      jsimp
      rw [show (tagM : Val) = u.tag from htag.symm]
      refine cerwp_perm (fun p => by simp [recsC]) (poolAnsC_resume hg' hP' (compS_empty_left D)
        ⟨rfl, rfl⟩ (fun σr hσr y hy => ?_)
        ⟨hVD, .inr ⟨u, rfl, hm', J, fun y hy => ⟨hJF y hy, trivial⟩, hJD⟩⟩ (by simpa using hd))
      obtain rfl := poolC_marker hm' hσr
      obtain rfl := eq_of_compS_empty_left hy
      exact ⟨hJF _ (hVD.noAt hJD), trivial⟩

/-- The scheduler meeting its clauses at every stop below `N`. -/
abbrev SchedBelowJ (N : Nat) : Prop :=
  ∀ N', N' < N → SchedOKCLe (ℍ := ℍ) N' (TJC (ℍ := ℍ)) nP qsJ stackRet hsJ QinJ (PA_J (ℍ := ℍ))
    QinJ

/-- **`spawn`'s clause**: the top the marker, divergence; otherwise the spawner parked as a
must-resume ready task (`poolAnsC_park`), the child run under the scheduler beside the pool and
the bag below the stop's index (`poolAnsC_run_le`), from the payload's resource, lifted from its
indexed table (`cerwp_tabAtC`). -/
theorem spawnClJ_ok (N : Nat) (ih : SchedBelowJ (ℍ := ℍ) N) :
    ClauseJ (ℍ := ℍ) N (liftEnt (enLinN (spawnPAC (ℍ := ℍ) (tabAtC (ℍ := ℍ))))) spawnClJ := by
  rintro F k hkN ls O v κ ρ - ⟨ρa, ρk, hc, hth, hκ⟩
  have hDE := opTableC_down opTabC_emptyC_down
  have hD := poolAnsC_down (ℍ := ℍ) QinJ QJ HJ InvJ F
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v κ)) rfl
    .hole) ?_
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.letpair μ v κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine cerwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtC_iff.mpr ?_)
  intro ts D σ ρ' hi hg hP hc' hd
  obtain ⟨X, hX, hρ'⟩ := compS_reassoc hc hc'
  obtain ⟨hP', hg'⟩ := poolAnsC_park (fun _ => True) tagL hκ trivial hj hg hP hX
  obtain ⟨hVD, hi⟩ := hi
  cases j with
  | zero => exact cerwp_zero
  | succ j₀ =>
  have hchild := cerwp_tabAtC (hth j₀ (by omega) ls)
  refine cerwp_step (opTableC_local _) (fun μ => step1Only_plug (Head.beta μ _ (stateValC HJ ts))
    rfl .hole) ?_
  jsimp
  refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ HJ (poolValC ts) _)
    rfl .hole) ?_
  jsimp
  cases ts with
  | nil =>
    have hF : ∀ y, F y := by
      rcases hi with ⟨hF, -⟩ | ⟨u, hu, -⟩
      · exact hF
      · cases hu
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
      .hole) ?_
    jsimp
    refine cerwp_perm (fun p => by simp [recsC]) (poolAnsC_run_le (ih j₀ (by omega)) le_rfl
      (fun u hu => (hg' u hu).le (by omega)) ⟨hVD, .inl ⟨fun _ => trivial, fun t ht => ?_⟩⟩ hP'
      hρ' (by simp [RDisj]) trivial hchild)
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨hF, fun _ => trivial, fun _ _ => ⟨rfl, rfl⟩, .inr rfl⟩
    · cases ht
  | cons u ts =>
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair u.tag u.κ) (poolValC ts)) _ _) rfl .hole) ?_
    jsimp
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair u.tag u.κ) (poolValC ts) _) rfl .hole) ?_
    jsimp
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ u.tag u.κ _) rfl
      .hole) ?_
    jsimp
    rcases hi with ⟨hF, hr⟩ | ⟨u', hu, hm, -⟩
    · obtain ⟨-, -, -, htag⟩ := hr u List.mem_cons_self
      obtain ⟨x, hx⟩ : ∃ x, u.tag = Val.inj₁ x := by
        rcases htag with ⟨h, -⟩ | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      rcases u with ⟨Qu, enu, Fu, ku, Ou, vu, κu, Ru, tagu⟩
      simp only at hx
      subst hx
      refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₁ μ x _ _) rfl .hole) ?_
      jsimp
      refine cerwp_perm (fun p => by simp [recsC]) (poolAnsC_run_le (ih j₀ (by omega)) le_rfl
        (fun u hu => (hg' u hu).le (by omega)) ⟨hVD, .inl ⟨fun _ => trivial, fun t ht => ?_⟩⟩
        hP' hρ' (RDisj.cons (fun _ h => by cases h) (by simpa using hd)) trivial hchild)
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hF, fun _ => trivial, fun _ _ => ⟨rfl, rfl⟩, .inr rfl⟩
      · exact hr t ht
    · obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hu
      obtain ⟨htag, -⟩ := hm
      rw [htag]
      refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
        .hole) ?_
      jsimp
      exact cerwp_omega (opTableC_local _) _ _ _ _

/-- **`cancel`'s clause**: the stopped task parked as a must-resume ready task; the top a
cancellable ready task, it is cancelled, its cancel branch run under the scheduler below the stop's
index, the stopped task kept beneath it (`poolAnsC_cancelSnd`); otherwise the stopped task
resumed (`poolAnsC_resume`). -/
theorem cancelClJ_ok (N : Nat) (ih : SchedBelowJ (ℍ := ℍ) N) :
    ClauseJ (ℍ := ℍ) N (liftEnt (enLinN unitPJ)) cancelClJ := by
  rintro F k hkN ls O v κ ρ - ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := eq_of_compS_empty_left hc
  have hDE := opTableC_down opTabC_emptyC_down
  have hD := poolAnsC_down (ℍ := ℍ) QinJ QJ HJ InvJ F
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl
    .hole) ?_
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine cerwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtC_iff.mpr ?_)
  intro ts D σ ρ' hi hg hP hc' hd
  obtain ⟨hP', hg'⟩ := poolAnsC_park (fun _ => True) tagL hκ trivial hj hg hP hc'
  obtain ⟨hVD, hi⟩ := hi
  cases j with
  | zero => exact cerwp_zero
  | succ j₀ =>
  refine cerwp_step (opTableC_local _) (fun μ => step1Only_plug (Head.beta μ _ (stateValC HJ ts))
    rfl .hole) ?_
  jsimp
  refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ HJ (poolValC ts) _)
    rfl .hole) ?_
  jsimp
  cases ts with
  | nil =>
    have hF : ∀ y, F y := by
      rcases hi with ⟨hF, -⟩ | ⟨u, hu, -⟩
      · exact hF
      · cases hu
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
      .hole) ?_
    jsimp
    exact poolAnsC_resume hg' hP' (compS_empty_left D) ⟨rfl, rfl⟩
      (fun _ _ y _ => ⟨hF y, trivial⟩) ⟨hVD, .inl ⟨fun y => ⟨hF y, trivial⟩, fun _ h => by cases h⟩⟩
      (by simpa using hd)
  | cons u ts =>
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair u.tag u.κ) (poolValC ts)) _ _) rfl .hole) ?_
    jsimp
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair u.tag u.κ) (poolValC ts) _) rfl .hole) ?_
    jsimp
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ u.tag u.κ _) rfl
      .hole) ?_
    jsimp
    rcases hi with ⟨hF, hr⟩ | ⟨u', hu, hm, J, hJF, hJD⟩
    · have hr' : ∀ x ∈ ts, ReadyOK x := fun x hx => hr x (List.mem_cons_of_mem _ hx)
      obtain ⟨hu₁, hu₂, hu₃, htag⟩ := hr u List.mem_cons_self
      rcases htag with ⟨htag, hq, hO⟩ | htag
      · -- the top cancellable: cancelled, the stopped task beneath it
        rcases u with ⟨Qu, enu, Fu, ku, Ou, vu, κu, Ru, tagu⟩
        simp only at htag hq hO
        subst htag
        refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl
          .hole) ?_
        jsimp
        refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl
          .hole) ?_
        jsimp
        refine cerwp_perm (fun p => by simp [recsC]) (poolAnsC_cancelSnd (ih j₀ (by omega))
          (fun _ _ _ _ _ h => h) le_rfl hg' hP' hq hO ⟨hVD, .inl ⟨fun _ => trivial, fun t ht => ?_⟩⟩
          (fun _ _ => trivial) (by simpa using (show RDisj (O :: Ou :: ts.map StoredC.O) by
            simpa using hd).drop2))
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨hF, fun _ => trivial, fun _ _ => ⟨rfl, rfl⟩, .inr rfl⟩
        · exact hr' t ht
      · -- the top must-resume: the stopped task resumed
        rcases u with ⟨Qu, enu, Fu, ku, Ou, vu, κu, Ru, tagu⟩
        simp only at htag
        subst htag
        refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl
          .hole) ?_
        jsimp
        refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
          .hole) ?_
        jsimp
        exact poolAnsC_resume hg' hP' (compS_empty_left D) ⟨rfl, rfl⟩
          (fun _ _ y _ => ⟨hF y, trivial⟩)
          ⟨hVD, .inl ⟨fun y => ⟨hF y, trivial⟩, hr⟩⟩ (by simpa using hd)
    · -- the top the marker: the stopped task resumed, alone with it
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hu
      have hm' := hm
      obtain ⟨htag, -, -, -, -, -⟩ := hm
      rw [htag]
      refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
        .hole) ?_
      jsimp
      rw [show (tagM : Val) = u.tag from htag.symm]
      refine cerwp_perm (fun p => by simp [recsC]) (poolAnsC_resume hg' hP' (compS_empty_left D)
        ⟨rfl, rfl⟩ (fun σr hσr y hy => ?_)
        ⟨hVD, .inr ⟨u, rfl, hm', J, fun y hy => ⟨hJF y hy, trivial⟩, hJD⟩⟩ (by simpa using hd))
      obtain rfl := poolC_marker hm' hσr
      obtain rfl := eq_of_compS_empty_left hy
      exact ⟨hJF _ (hVD.noAt hJD), trivial⟩

/-! ### The marker -/

/-- The marker's entry: must-resume, resumed at `()` holding nothing, asking nothing of its
frame. -/
def markerEnt : OpEntC :=
  { q := .lin, abort := false, PA := unitPJ, PB := unitPJ, fin := none, wc := fun _ _ _ => True,
    fd := fun _ _ => True, PBv := fun _ => unitPJ, oc := fun _ => True }

/-- **The marker**, pushed at index `k₀`: `κM`, holding nothing, owning no record. -/
def markerS (k₀ : Nat) : StoredC :=
  ⟨PA_J (ℍ := ℍ), markerEnt, fun _ => True, k₀, [], Val.unit, κM, fun ρ => ρ = PMap.empty, tagM⟩

theorem markerS_ok (k₀ : Nat) : MarkerOK (markerS (ℍ := ℍ) k₀) :=
  ⟨rfl, fun _ h => h, fun _ => trivial, fun _ => trivial, fun _ _ => ⟨rfl, rfl⟩, rfl⟩

/-- **The marker resumed is a task's end holding nothing** (`stackRetJ_ok`). -/
theorem markerKap (k₀ : Nat) :
    KapRelC (ℍ := ℍ) (PA_J (ℍ := ℍ)) QinJ markerEnt (fun _ => True) k₀ [] Val.unit κM
      PMap.empty := by
  intro ls' k' _
  refine ⟨fun w τ₁ τ₂ ⟨hw, hτ⟩ hcτ => ?_, fun hq => absurd rfl hq⟩
  subst hw hτ
  obtain rfl := eq_of_compS_empty_left hcτ
  have hDE := opTableC_down opTabC_emptyC_down
  have hD := poolAnsC_down (ℍ := ℍ) QinJ QJ HJ InvJ (FdAnd (fun _ => True) markerEnt Val.unit)
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.beta μ _ (Val.inj₁ Val.unit)) rfl
    (.appL .hole Val.unit)) ?_
  simp only [Kont.plug, Expr.subst]
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  simp only [Kont.plug, Expr.subst]
  exact stackRetJ_ok _ k' ls' [] Val.unit PMap.empty ⟨rfl, .empty⟩

/-- The marker beside an empty pool. -/
theorem poolC_pushMarker (k₀ : Nat) {D σ : WRes}
    (hP : (PoolC (ℍ := ℍ) QinJ [] ⋆ fun x => x = D) σ) :
    (PoolC (ℍ := ℍ) QinJ [markerS (ℍ := ℍ) k₀] ⋆ fun x => x = D) σ := by
  obtain ⟨a, b, hab, rfl, rfl⟩ := hP
  exact ⟨PMap.empty, b, hab, ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _,
    ⟨markerKap k₀, rfl⟩, rfl⟩, rfl⟩

/-- **`join`'s clause**: no other task stored, the joiner resumed above the marker
(`poolC_pushMarker`, `poolAnsC_park`, `poolAnsC_resume`), with the bag's copies of the joined
location (`ViewsC.split`), its frame (the rest of the bag) holding nothing there (`joinFd`); the
marker on top, the same; a ready task on top, divergence. -/
theorem joinClJ_ok (N : Nat) : ClauseJ (ℍ := ℍ) N joinEnt joinClJ := by
  rintro F k _ ls O v κ ρ - ⟨ρa, ρk, hc, ⟨⟨l, rfl⟩, rfl⟩, hκ⟩
  obtain rfl := eq_of_compS_empty_left hc
  have hDE := opTableC_down opTabC_emptyC_down
  have hD := poolAnsC_down (ℍ := ℍ) QinJ QJ HJ InvJ F
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair (Val.loc l) κ)) rfl
    .hole) ?_
  refine cerwp_det hDE hD (fun μ => step1Only_plug (Head.letpair μ (Val.loc l) κ _) rfl
    .hole) ?_
  simp only [Kont.plug]
  refine cerwp_val (v := ⟨_, .lam⟩) (fun j hj => poolAnsAtC_iff.mpr ?_)
  intro ts D σ ρ' hi hg hP hc' hd
  obtain ⟨hVD, hi⟩ := hi
  obtain ⟨Dl, Dr, hlr, hDl, hVr, hrl⟩ := hVD.split l
  have hB : ∀ k ls, joinEnt.PBv (Val.loc l) k ls Val.unit Dl := fun _ _ => ⟨l, rfl, rfl, hDl⟩
  have hjfd : ∀ y, ViewsC y → y.get l = none → joinFd (Val.loc l) y :=
    fun y hy hyl => ⟨l, rfl, fun τ hτ => hy.flat_none τ hτ l hyl⟩
  cases j with
  | zero => exact cerwp_zero
  | succ j₀ =>
  refine cerwp_step (opTableC_local _) (fun μ => step1Only_plug (Head.beta μ _ (stateValC HJ ts))
    rfl .hole) ?_
  jsimp
  refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ HJ (poolValC ts) _)
    rfl .hole) ?_
  jsimp
  cases ts with
  | nil =>
    have hF : ∀ y, F y := by
      rcases hi with ⟨hF, -⟩ | ⟨u, hu, -⟩
      · exact hF
      · cases hu
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
      .hole) ?_
    jsimp
    have hPm := poolC_pushMarker (ℍ := ℍ) (k₀ := k) hP
    obtain ⟨hP', hg'⟩ := poolAnsC_park (fun _ => True) tagL hκ trivial hj
      (fun t ht => by
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨hj, fun _ _ _ _ _ _ _ h => h⟩
        · cases ht) hPm hc'
    refine cerwp_perm (fun p => by simp [recsC, markerS]) (poolAnsC_resume hg' hP' hlr (hB _ _)
      (fun σr hσr y hy => ?_)
      ⟨hVr, .inr ⟨markerS k, rfl, markerS_ok k, [l], fun y hy => ⟨hF y, ?_⟩, ?_⟩⟩
      (by simp [RDisj, markerS]))
    · obtain rfl := poolC_marker (markerS_ok k) hσr
      obtain rfl := eq_of_compS_empty_left hy
      exact ⟨hF _, hjfd _ hVr hrl⟩
    · exact ⟨l, rfl, hy l List.mem_cons_self⟩
    · intro x hx
      rw [List.mem_singleton.mp hx]
      exact hrl
  | cons u ts =>
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair u.tag u.κ) (poolValC ts)) _ _) rfl .hole) ?_
    jsimp
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair u.tag u.κ) (poolValC ts) _) rfl .hole) ?_
    jsimp
    refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.letpair μ u.tag u.κ _) rfl
      .hole) ?_
    jsimp
    rcases hi with ⟨-, hr⟩ | ⟨u', hu, hm, J, hJF, hJD⟩
    · -- a ready task stored: divergence
      obtain ⟨-, -, -, htag⟩ := hr u List.mem_cons_self
      obtain ⟨x, hx⟩ : ∃ x, u.tag = Val.inj₁ x := by
        rcases htag with ⟨h, -⟩ | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      rw [hx]
      refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₁ μ x _ _) rfl .hole) ?_
      jsimp
      exact cerwp_omega (opTableC_local _) _ _ _ _
    · -- the marker on top: the joiner resumed above it
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hu
      have hm' := hm
      obtain ⟨htag, -, -, -, -, -⟩ := hm
      rw [htag]
      refine cerwp_det hDE QJ_down (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl
        .hole) ?_
      jsimp
      rw [show (tagM : Val) = u.tag from htag.symm]
      obtain ⟨hP', hg'⟩ := poolAnsC_park (fun _ => True) tagL hκ trivial hj hg hP hc'
      have hJr : ∀ x ∈ J, Dr.get x = none := fun x hx => get_none_right hlr (hJD x hx)
      refine cerwp_perm (fun p => by simp [recsC]) (poolAnsC_resume hg' hP' hlr (hB _ _)
        (fun σr hσr y hy => ?_)
        ⟨hVr, .inr ⟨u, rfl, hm', l :: J, fun y hy => ⟨hJF y fun x hx => hy x
          (List.mem_cons_of_mem _ hx), l, rfl, hy l List.mem_cons_self⟩, ?_⟩⟩
        (by simpa using hd))
      · obtain rfl := poolC_marker hm' hσr
        obtain rfl := eq_of_compS_empty_left hy
        exact ⟨hJF _ (hVr.noAt hJr), hjfd _ hVr hrl⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hrl
        · exact hJr x hx

/-! ### The scheduler meets `SchedOKC` -/

theorem clauseAt_hsJ (i : Nat) :
    clauseAt hsJ.1 i = [parkClC, spawnClJ, cancelClJ, joinClJ, parkClL][i]? := by
  rcases i with _ | _ | _ | _ | _ | i <;>
    simp [clauseAt, hsJ, Val.pair, parkClC, spawnClJ, cancelClJ, joinClJ, parkClL,
      (BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.clauseOf _).2]

/-- **The scheduler meets its clauses at stops up to every `N`**, by strong induction on `N`. -/
theorem hj_schedOKCLe : ∀ N, SchedOKCLe (ℍ := ℍ) N (TJC (ℍ := ℍ)) nP qsJ stackRet hsJ QinJ
    (PA_J (ℍ := ℍ)) QinJ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  refine ⟨TJC_down, fun m i en h => (tabOfC_some h).1, fun i en h => ?_, fun i en h hq => ?_,
    fun F => poolAnsC_down _ _ _ _ F, QinJ_down, fun F k _ => stackRetJ_ok F k,
    fun i en h => ?_⟩
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfC_some h <;>
      refine ⟨rfl, (fun h => by cases h), ?_, fun _ _ _ => trivial⟩ <;>
      simp [qsJ, capTag_qualsVal] <;> rfl
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfC_some h
    · exact ⟨rfl, fun O h => h⟩
    all_goals exact absurd rfl hq
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOfC_some h
    · exact ⟨parkClC, by rw [clauseAt_hsJ]; rfl, parkClC_ok N⟩
    · exact ⟨spawnClJ, by rw [clauseAt_hsJ]; rfl, spawnClJ_ok N ih⟩
    · exact ⟨cancelClJ, by rw [clauseAt_hsJ]; rfl, cancelClJ_ok N ih⟩
    · exact ⟨joinClJ, by rw [clauseAt_hsJ]; rfl, joinClJ_ok N⟩
    · exact ⟨parkClL, by rw [clauseAt_hsJ]; rfl, parkClL_ok N⟩

/-- **The scheduler `HJ` meets `SchedOKC`** at the table `TJC`, its answers functions of its
list and bag, for every list. -/
theorem hj_schedOKC : SchedOKC (ℍ := ℍ) (TJC (ℍ := ℍ)) nP qsJ stackRet hsJ QinJ (PA_J (ℍ := ℍ))
    QinJ := hj_schedOKCLe

/-- The empty pool and bag meet the invariant at the trivial frame condition. -/
theorem invJ_nil : InvJ (fun _ => True) [] PMap.empty := ⟨.empty, .inl ⟨fun _ => trivial,
  fun _ h => by cases h⟩⟩

/-- **A root verified at the scheduler's table, closed under `HJ`**: through
`poolSchedAdequacyC`, every premise discharged. -/
theorem progOfC_orDiverges {root : Expr}
    (h : ∀ n, cerwp (ℍ := ℍ) (opTableC (TJC (ℍ := ℍ))) QinJ (fun _ => True) n [] [] root
      (PMap.empty : WRes)) :
    OrDiverges (ℍ := ℍ) (.app (hndE HJ root) (stateValC HJ []).1) :=
  poolSchedAdequacyC (TJC (ℍ := ℍ)) nP qsJ stackRet hsJ QinJ QinJ QJ InvJ root
    (fun _ _ _ _ _ h => h) invJ_nil hj_schedOKC h

end BoCa.Fig16.LogRel.Core.Chain.SI.PoolJoin

end
