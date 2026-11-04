import HoStoreSpike.D2
import Support.Model.Tree.CarrierGraftEx

/-!
# The hard case, inhabited (spike, #790)

At `K₁` (`Tree/CarrierGraftEx.lean`: the tree after a task is grafted under the handler's lend
`β`), a `mut` cell at `{α}` at `l₁` holds a thunk whose resource is the handler's borrow at `β`
(`borrowAt K₁ l₂`). Its location's type is `thunk (Imm @β 1)`. The world `l₁ ↦ mut(…)` is covered
at `semH Ψ (n+1)` (`hard_cov`), so it meets every hypothesis of `reread_world_typed`: at every later
tree, and every store typing keeping `l₁`'s type, its re-reading is covered and the re-read cell
holds a value of `thunk (Imm @β 1)` there, one step later, and still holds the borrow at `l₂`
(`hard_case`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.HoStore
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp

/-- The thunk's type: forced at any later world, a view at `β` of `1`. -/
def thunkTy : HTy := HTy.thunk (HTy.imm βL HTy.unit)

theorem leafImm_res {K : WCactus} {t : TSet} {u : BoCa.Val} :
    ∃ i : TImm K, (leafImm (Loc := BoCa.Loc) t u : TCell K) = .imm i ∧ i.ls = t ∧ i.v = u ∧
      i.res = PMap.empty :=
  ⟨_, rfl, rfl, rfl, ImmT.res_toRes _⟩

/-- **The thunk holding the borrow is of its type**, at every index and store typing. -/
theorem thunk_holds (n : Nat) (Ψ : HStore) (l₂ : BoCa.Loc) :
    thunkTy.P n K₁ Ψ (BoCa.Val.loc l₂) (borrowAt K₁ l₂ BoCa.Val.unit) := by
  intro k _ K' Ψ' j ρ' hE _ hr
  obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
  obtain ⟨i, ei, hls, hv, hres⟩ := leafImm_res (K := K₁) (t := TSet.single βL) (u := BoCa.Val.unit)
  rw [ei] at hrc
  cases hrc with
  | imm _ _ i' hs hv' hdom _ =>
      refine ⟨l₂, i', rfl, rfl, fun x hx => ?_, ?_, ?_⟩
      · rw [hs, hls] at hx
        simp only [TSet.single_set, Finset.mem_singleton] at hx
        subst hx; exact K'.refl _
      · rw [hv', hv]
      · exact PMap.ext fun m => by
          have := (hdom m).mp (by rw [hres]; rfl)
          simpa using this

/-- The borrow is in `α`'s stratum at `K₁`. -/
theorem borrow_inStratum (l₂ : BoCa.Loc) :
    (borrowAt K₁ l₂ BoCa.Val.unit : TRes K₁).InStratum (TSet.single αL) :=
  (borrowAt_inStratum_iff K₁ l₂ BoCa.Val.unit).mpr K₁_lt

open Classical in
/-- The store typing: `l₁ : thunkTy`. -/
def hardΨ (l₁ : BoCa.Loc) : HStore := fun l => if l = l₁ then some thunkTy else none

theorem hardΨ_l₁ (l₁ : BoCa.Loc) : hardΨ l₁ l₁ = some thunkTy := by simp [hardΨ]

theorem hardΨ_lawful (l₁ : BoCa.Loc) : (hardΨ l₁).Lawful := by
  intro l τ h
  unfold hardΨ at h
  split at h
  · cases h; exact HTy.thunk_lawful _
  · cases h

/-- The cell at `l₁`: `mut({α}, loc l₂, borrowAt l₂, thunkTy one step later)`. -/
def hardCell (n : Nat) (l₁ l₂ : BoCa.Loc) : TMut K₁ :=
  ⟨TSet.single αL, anti_single K₁ αL, BoCa.Val.loc l₂,
    ResST.toRes ⟨borrowAt K₁ l₂ BoCa.Val.unit, borrow_inStratum l₂⟩,
    fun w r => (cellInv (hardΨ l₁) thunkTy (n + 1)).P K₁ w r.toU, by
      show thunkTy.P n K₁ (hardΨ l₁) _ (ResST.toRes ⟨_, borrow_inStratum l₂⟩).toU
      rw [ResST.toU_toRes]; exact thunk_holds n _ l₂⟩

theorem hardCell_res (n : Nat) (l₁ l₂ : BoCa.Loc) :
    (hardCell n l₁ l₂).res = borrowAt K₁ l₂ BoCa.Val.unit :=
  ResST.toU_toRes _

/-- The world: the cell alone. -/
def hardWorld (n : Nat) (l₁ l₂ : BoCa.Loc) : TRes K₁ := PMap.sng l₁ (.mut (hardCell n l₁ l₂))

/-- **The world is covered** at `semH Ψ (n+1)`. -/
theorem hard_cov (n : Nat) (l₁ l₂ : BoCa.Loc) :
    CovR (semH (hardΨ l₁) (n + 1)) K₁ (hardWorld n l₁ l₂) := by
  classical
  intro l ψ e
  simp only [hardWorld, PMap.sng_get] at e
  split at e
  · rename_i hl; subst hl; cases e
    refine .mut l (hardCell n l l₂) _ (semH_of (hardΨ_l₁ l)) (fun _ _ => Iff.rfl) ?_
    intro k ψ' e'
    rw [hardCell_res] at e'
    simp only [borrowAt, PMap.sng_get] at e'
    split at e'
    · cases e'
      obtain ⟨i, ei, -, -, hres⟩ := leafImm_res (K := K₁) (t := TSet.single βL)
        (u := BoCa.Val.unit)
      rw [ei]
      exact .imm k i fun m ψ'' e'' => by rw [hres] at e''; simp at e''
    · cases e'
  · cases e

/-- **The hard case.** At every later tree and every store typing keeping `l₁`'s type, the world
holding the cell is re-read, covered, and the re-read cell holds a value of `thunkTy` at the new
tree, one step later, whose resource still holds the borrow at `l₂`. -/
theorem hard_case (n : Nat) {l₁ l₂ : BoCa.Loc} {K' : WCactus} (hE : K₁.Ext K') {Ψ' : HStore}
    (hag : AgreeH (hardΨ l₁) Ψ' (hardWorld n l₁ l₂)) :
    ∃ ρ' : TRes K', RR (semH Ψ' (n + 1)) (hardWorld n l₁ l₂) ρ' ∧
      CovR (semH Ψ' (n + 1)) K' ρ' ∧
      ∃ c' : TMut K', ρ'.get l₁ = some (.mut c') ∧ thunkTy.P n K' Ψ' c'.v c'.res ∧
        ∃ i' : TImm K', c'.res.get l₂ = some (.imm i') := by
  obtain ⟨ρ', hr, hc', hall⟩ :=
    reread_world_typed (hardΨ_lawful l₁) hE (Nat.le_refl _) (hard_cov n l₁ l₂) hag
  have e : (hardWorld n l₁ l₂).get l₁ = some (.mut (hardCell n l₁ l₂)) := by
    simp [hardWorld, PMap.sng_get]
  obtain ⟨c', e', hty⟩ := hall l₁ _ thunkTy e (hardΨ_l₁ l₁)
  refine ⟨ρ', hr, hc', c', e', hty, ?_⟩
  obtain ⟨ψ', e'', hrc⟩ := hr.get_some e
  rw [e'] at e''; cases e''
  cases hrc with
  | «mut» _ _ _ _ _ _ _ hdom hw _ =>
      obtain ⟨i, ei, -, -, -⟩ := leafImm_res (K := K₁) (t := TSet.single βL) (u := BoCa.Val.unit)
      have e₂ : (hardCell n l₁ l₂).res.get l₂ = some (.imm i) := by
        rw [hardCell_res, ← ei]; simp [borrowAt, PMap.sng_get]
      cases e₃ : c'.res.get l₂ with
      | none => exact absurd ((hdom l₂).mpr e₃) (by rw [e₂]; simp)
      | some ψ₂ =>
          have := hw l₂ _ ψ₂ e₂ e₃
          cases this with
          | imm _ _ i' => exact ⟨i', rfl⟩

/-- The hard case's hypotheses are met: at `K₁` itself and the same store typing. -/
theorem hard_case_inhabited (n : Nat) (l₁ l₂ : BoCa.Loc) :
    ∃ ρ' : TRes K₁, RR (semH (hardΨ l₁) (n + 1)) (hardWorld n l₁ l₂) ρ' ∧
      CovR (semH (hardΨ l₁) (n + 1)) K₁ ρ' ∧
      ∃ c' : TMut K₁, ρ'.get l₁ = some (.mut c') ∧ thunkTy.P n K₁ (hardΨ l₁) c'.v c'.res ∧
        ∃ i' : TImm K₁, c'.res.get l₂ = some (.imm i') :=
  hard_case n (WCactus.Ext.refl _) (AgreeH.refl _ _)

/-- Depth 1 and depth 3 cell types at the hard case's thunk, and the recursive cell-of-tasks
type, are lawful, so a store typing may give them to any location. -/
theorem depths_lawful :
    (depth1 αL (HTy.imm βL HTy.unit)).Lawful ∧
    (depth3 αL βL αL (HTy.imm βL HTy.unit)).Lawful ∧ (cellTask αL).Lawful :=
  ⟨depth1_lawful _ _, depth3_lawful _ _ _ _, cellTask_lawful _⟩

end BoCa.Fig16.Tree.HoStore

end
