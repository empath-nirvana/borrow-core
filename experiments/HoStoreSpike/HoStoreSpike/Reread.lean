import HoStoreSpike.Tower

/-!
# Re-reading a higher-order store (spike, #790)

`Cov`, `RC` and `RR` of `Tree/Reread.lean` are read at `semH Ψ n`, unchanged. What is proved here,
for **every** lawful store typing, uniformly in the types it gives:

* **A covered world is re-read at every tree extension and every index `m ≤ n`**
  (`RR.exists_H`): at a store typing keeping the types where the world holds a `mut` cell, the
  re-reading exists and is covered. The index may drop, so a cell's invariant is re-read one step
  later too.
* **A re-read cell's invariant is its location's type at the new tree and index**
  (`RC.mut_invH`, the analogue of `RC.mut_inv`), and **a lender reads back a value of the type one
  step later** (`RC.mut_readbackH`).
* **The content of a re-read cell is of its type there** (`RC.mut_contentH`). The content's
  resource is re-read with the rest; its type's monotonicity is what carries it
  (`cellInv_extend`), so a cell holding a thunk that holds a borrow is carried by the thunk type's
  own law (`HoStoreSpike/Formers.lean`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.HoStore
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp

/-- **A cell's content carried to a later tree, a store typing keeping its type, and an index
`m ≤ n`**: the type's laws. -/
theorem cellInv_extend {Ψ Ψ' : HStore} {τ : HTy} (hτ : τ.Lawful) {K K' : WCactus}
    (hE : K.Ext K') {n m : Nat} (hmn : m ≤ n) {v : BoCa.Val} {r : TRes K} {r' : TRes K'}
    (hag : AgreeH Ψ Ψ' r) (hr : RR (semH Ψ' m) r r') :
    (cellInv Ψ τ n).P K v r → (cellInv Ψ' τ m).P K' v r' := by
  cases m with
  | zero => intro _; trivial
  | succ m =>
      cases n with
      | zero => exact absurd hmn (by omega)
      | succ n =>
          intro h
          exact hτ.mono m K K' Ψ Ψ' (m + 1) v r r' hE hag hr
            (HTy.down_le hτ.down (by omega) h)

/-- One cell's re-reading at a later tree and index (`RC.exists_retype`'s proof). -/
theorem RC.exists_H {Ψ Ψ' : HStore} (hL : Ψ.Lawful) {K K' : WCactus} (hE : K.Ext K')
    {n m : Nat} (hmn : m ≤ n) {l : BoCa.Loc} {ψ : TCell K} (hc : Cov (semH Ψ n) K l ψ)
    (hagl : ψ.kind = .mut → Ψ' l = Ψ l) (hagw : AgreeH Ψ Ψ' ψ.wit)
    (hw : ∃ χ' : TRes K', RR (semH Ψ' m) ψ.wit χ') :
    ∃ ψ' : TCell K', RC (semH Ψ' m) l ψ ψ' := by
  cases hc with
  | own l v => exact ⟨_, .own l v⟩
  | imm l i _ =>
      obtain ⟨χ', hχ⟩ := hw
      have hs : χ'.InStratum i.ls := RR.inStratum hE hχ CellUT.wit_inStratum_imm
      let i' : TImm K' := ⟨i.ls, i.v, ResST.toRes ⟨χ', hs⟩⟩
      have hres : i'.res = χ' := ResST.toU_toRes ⟨χ', hs⟩
      refine ⟨.imm i', .imm l i i' rfl rfl ?_ ?_⟩
      · intro k; rw [hres]; exact hχ.1 k
      · intro k ψ ψ' e e'; rw [hres] at e'; exact hχ.2 k ψ ψ' e e'
  | «mut» l c κ hΘ hP hcw =>
      obtain ⟨χ', hχ⟩ := hw
      obtain ⟨τ, hτ, rfl⟩ := semH_some hΘ
      have hτ' : Ψ' l = some τ := (hagl rfl).trans hτ
      have hs : χ'.InStratum (K'.minS c.ls) :=
        (RR.inStratum hE hχ CellUT.wit_inStratum_mut).minS
      have hcont : (cellInv Ψ' τ m).P K' c.v χ' :=
        cellInv_extend (hL l τ hτ) hE hmn hagw hχ ((hP c.v c.ρ).mp c.hw)
      let c' : TMut K' := ⟨K'.minS c.ls, K'.minS_anti _, c.v, ResST.toRes ⟨χ', hs⟩,
        fun w r => (cellInv Ψ' τ m).P K' w r.toU, by
          show (cellInv Ψ' τ m).P K' c.v (ResST.toRes ⟨χ', hs⟩).toU
          rw [ResST.toU_toRes]; exact hcont⟩
      have hres : c'.res = χ' := ResST.toU_toRes ⟨χ', hs⟩
      refine ⟨.mut c', .mut l c c' _ (semH_of hτ') rfl rfl ?_ ?_ fun _ _ => Iff.rfl⟩
      · intro k; rw [hres]; exact hχ.1 k
      · intro k ψ ψ' e e'; rw [hres] at e'; exact hχ.2 k ψ ψ' e e'

theorem kind_mut_agree {K : WCactus} {Ψ Ψ' : HStore} {ρ : TRes K} (hag : AgreeH Ψ Ψ' ρ)
    {l : BoCa.Loc} {ψ : TCell K} (e : ρ.get l = some ψ) : ψ.kind = .mut → Ψ' l = Ψ l := by
  intro hk
  cases ψ with
  | «mut» c => exact hag l (.top e)
  | own => cases hk
  | imm => cases hk

/-- Re-readings exist in every stratum (`RR.exists_retype_stratum`'s proof). -/
theorem RR.exists_H_stratum {Ψ Ψ' : HStore} (hL : Ψ.Lawful) {K K' : WCactus} (hE : K.Ext K')
    {n m : Nat} (hmn : m ≤ n) (T : TSet) :
    ∀ ρ : TRes K, ρ.InStratum T → CovR (semH Ψ n) K ρ → AgreeH Ψ Ψ' ρ →
      ∃ ρ' : TRes K', RR (semH Ψ' m) ρ ρ' := by
  induction T using K.above_wf.induction with
  | _ T ih =>
  intro ρ hT hc hag
  refine RR.exists_of fun l ψ e =>
    RC.exists_H hL hE hmn (hc l ψ e) (kind_mut_agree hag e) (hag.wit e) ?_
  have hcl := hc l ψ e
  cases hcl with
  | own => exact ⟨_, RR.empty⟩
  | imm _ i hw => exact ih i.ls (hT l _ e) i.res CellUT.wit_inStratum_imm hw (hag.wit e)
  | «mut» _ c _ _ _ hw => exact ih c.ls (hT l _ e) c.res CellUT.wit_inStratum_mut hw (hag.wit e)

/-- **A covered world is re-read at every later tree and every index `m ≤ n`**, at a store typing
keeping the types where it holds a `mut` cell: the re-reading exists, and is covered there. -/
theorem RR.exists_H {Ψ Ψ' : HStore} (hL : Ψ.Lawful) {K K' : WCactus} (hE : K.Ext K')
    {n m : Nat} (hmn : m ≤ n) {ρ : TRes K} (hc : CovR (semH Ψ n) K ρ) (hag : AgreeH Ψ Ψ' ρ) :
    ∃ ρ' : TRes K', RR (semH Ψ' m) ρ ρ' ∧ CovR (semH Ψ' m) K' ρ' := by
  have : ∃ ρ' : TRes K', RR (semH Ψ' m) ρ ρ' := by
    refine RR.exists_of fun l ψ e =>
      RC.exists_H hL hE hmn (hc l ψ e) (kind_mut_agree hag e) (hag.wit e) ?_
    have hcl := hc l ψ e
    cases hcl with
    | own => exact ⟨_, RR.empty⟩
    | imm _ i hw =>
        exact RR.exists_H_stratum hL hE hmn i.ls i.res CellUT.wit_inStratum_imm hw (hag.wit e)
    | «mut» _ c _ _ _ hw =>
        exact RR.exists_H_stratum hL hE hmn c.ls c.res CellUT.wit_inStratum_mut hw (hag.wit e)
  obtain ⟨ρ', hr⟩ := this
  exact ⟨ρ', hr, hr.cov⟩

/-- **The invariant of a re-read `mut` cell is its location's type at the new tree, at the new
index, one step later** (`RC.mut_inv`'s analogue). -/
theorem RC.mut_invH {Ψ' : HStore} {K K' : WCactus} {m : Nat} {l : BoCa.Loc} {c : TMut K}
    {c' : TMut K'} {τ : HTy} (hτ : Ψ' l = some τ) (h : RC (semH Ψ' m) l (.mut c) (.mut c')) :
    ∀ w r, c'.P w r ↔ (cellInv Ψ' τ m).P K' w r.toU := by
  cases h with
  | «mut» _ _ _ κ hΘ _ _ _ _ hP =>
      rw [semH_of hτ] at hΘ; cases Option.some.inj hΘ; exact hP

/-- **A lender reads back a value of the location's type, one step later.** -/
theorem RC.mut_readbackH {Ψ' : HStore} {K K' : WCactus} {m : Nat} {l : BoCa.Loc} {c : TMut K}
    {c' : TMut K'} {τ : HTy} (hτ : Ψ' l = some τ) (h : RC (semH Ψ' (m + 1)) l (.mut c) (.mut c'))
    {u : BoCa.Val} {r : ResT BoCa.Loc BoCa.Val K' c'.ls} (hu : c'.P u r) :
    τ.P m K' Ψ' u r.toU :=
  (RC.mut_invH hτ h u r).mp hu

/-- **The content of a re-read cell is of its location's type there**, one step later. -/
theorem RC.mut_contentH {Ψ' : HStore} {K K' : WCactus} {m : Nat} {l : BoCa.Loc} {c : TMut K}
    {c' : TMut K'} {τ : HTy} (hτ : Ψ' l = some τ) (h : RC (semH Ψ' (m + 1)) l (.mut c) (.mut c')) :
    τ.P m K' Ψ' c'.v c'.res :=
  RC.mut_readbackH hτ h c'.hw

/-- **The world re-read at every later tree and index, and each of its top `mut` cells holding a
value of its location's type there.** -/
theorem reread_world_typed {Ψ Ψ' : HStore} (hL : Ψ.Lawful) {K K' : WCactus} (hE : K.Ext K')
    {n m : Nat} (hmn : m + 1 ≤ n) {ρ : TRes K} (hc : CovR (semH Ψ n) K ρ) (hag : AgreeH Ψ Ψ' ρ) :
    ∃ ρ' : TRes K', RR (semH Ψ' (m + 1)) ρ ρ' ∧ CovR (semH Ψ' (m + 1)) K' ρ' ∧
      ∀ l (c : TMut K) τ, ρ.get l = some (.mut c) → Ψ l = some τ →
        ∃ c' : TMut K', ρ'.get l = some (.mut c') ∧ τ.P m K' Ψ' c'.v c'.res := by
  obtain ⟨ρ', hr, hc'⟩ := RR.exists_H hL hE hmn hc hag
  refine ⟨ρ', hr, hc', fun l c τ e hτ => ?_⟩
  obtain ⟨ψ', e', hrc⟩ := hr.get_some e
  have hτ' : Ψ' l = some τ := (hag l (.top e)).trans hτ
  cases ψ' with
  | «mut» c' => exact ⟨c', e', RC.mut_contentH hτ' hrc⟩
  | own => cases hrc
  | imm => cases hrc

end BoCa.Fig16.Tree.HoStore

end
