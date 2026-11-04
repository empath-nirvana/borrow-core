import Support.Model.Tree.World.Codes

/-!
# Semantic types at the tree: monotonicity along re-reading  `[spec §62]`

`Tree/Reread.lean` reads a semantic type `KSem` at every lifetime tree and re-reads a world at a
grown tree (`RR`): every location, tag, value and lifetime name kept, each `mut` cell storing its
location's type read at the new tree. Here:

* **Monotonicity** (`KMono`): a value in `τ` at `K` is in `τ` at `K'`, on the re-reading of its
  resource. Proved for `1`, `+`, `Imm @a τ`, `ref τ` and `[a] τ` from the components'
  (`kmono_unit`, `kmono_sum`, `kmono_imm`, `kmono_ref`, `kmono_box`). `kmono_mut` and
  `kmono_thunk` hold by the definitions of `vMut` and `vThunk`, for every `τ` and every
  computation predicate: they say nothing about a cell's or a thunk's contents.
* **Existence and `✓`** (`reread`): when every type the location typing assigns is monotone
  (`MonoΘ`), a covered world at `K` has a re-reading at every extension `K'`, covered at `K'`,
  keeping every stratum, valid when the world is.
* **What carries `Mut`** (`reread_extends`): the re-read invariant holds wherever the old one
  held, on re-read resources. It is the type read at `K'`, not row 5.57's extension of the old
  predicate by falsity, which `Tree/KSemGraft.lean`'s `trU_not_kmono` refutes.

At codes (`World/Codes.lean`), `interp_retype` and `RR.exists_retype` give the same without
`MonoΘ`: a code's meaning is carried along re-reading by induction on the code. The relation's
step-indexed types (`Core/TreeSem.lean`) are read over codes.

**Not modelled:** the records list (`ls`), `Coh`, and `Ext` of Core's `vCT`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Θ : LocTy}

/-! ### Monotonicity -/

/-- **`τ` is monotone along tree extension**, carried by the re-reading. -/
def KMono (Θ : LocTy) (τ : KSem) : Prop :=
  ∀ (K K' : WCactus), K.Ext K' → ∀ (v : BoCa.Val) (ρ : TRes K) (ρ' : TRes K'),
    CovR Θ K ρ → RR Θ ρ ρ' → τ.P K v ρ → τ.P K' v ρ'

/-- Every type the location typing assigns is monotone. -/
def MonoΘ (Θ : LocTy) : Prop := ∀ l τ, Θ l = some τ → KMono Θ τ


/-! ### Existence of the re-reading -/

/-- One cell's re-reading, from its witness's. -/
theorem RC.exists_cell {K K' : WCactus} (hE : K.Ext K') (hM : MonoΘ Θ) {l : BoCa.Loc}
    {ψ : TCell K} (hc : Cov Θ K l ψ) (hw : ∃ χ' : TRes K', RR Θ ψ.wit χ') :
    ∃ ψ' : TCell K', RC Θ l ψ ψ' := by
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
  | «mut» l m τ hΘ hP hcw =>
      obtain ⟨χ', hχ⟩ := hw
      have hs : χ'.InStratum (K'.minS m.ls) :=
        (RR.inStratum hE hχ CellUT.wit_inStratum_mut).minS
      have hτ : τ.P K' m.v χ' :=
        hM l τ hΘ K K' hE m.v m.res χ' hcw hχ ((hP m.v m.ρ).mp m.hw)
      let m' : TMut K' := ⟨K'.minS m.ls, K'.minS_anti _, m.v, ResST.toRes ⟨χ', hs⟩,
        fun w r => τ.P K' w r.toU, by
          show τ.P K' m.v (ResST.toRes ⟨χ', hs⟩).toU
          rw [ResST.toU_toRes]; exact hτ⟩
      have hres : m'.res = χ' := ResST.toU_toRes ⟨χ', hs⟩
      refine ⟨.mut m', .mut l m m' τ hΘ rfl rfl ?_ ?_ fun _ _ => Iff.rfl⟩
      · intro k; rw [hres]; exact hχ.1 k
      · intro k ψ ψ' e e'; rw [hres] at e'; exact hχ.2 k ψ ψ' e e'

/-- Re-readings exist in every stratum, by row 5.58's recursion read in `K`. -/
theorem RR.exists_stratum {K K' : WCactus} (hE : K.Ext K') (hM : MonoΘ Θ) (T : TSet) :
    ∀ ρ : TRes K, ρ.InStratum T → CovR Θ K ρ → ∃ ρ' : TRes K', RR Θ ρ ρ' := by
  induction T using K.above_wf.induction with
  | _ T ih =>
  intro ρ hT hc
  refine RR.exists_of fun l ψ e => RC.exists_cell hE hM (hc l ψ e) ?_
  have hcl := hc l ψ e
  cases hcl with
  | own => exact ⟨_, RR.empty⟩
  | imm _ i hw => exact ih i.ls (hT l _ e) i.res CellUT.wit_inStratum_imm hw
  | «mut» _ m _ _ _ hw => exact ih m.ls (hT l _ e) m.res CellUT.wit_inStratum_mut hw

/-- **Every covered world has a re-reading** at an extension, when the location typing's types
are monotone. -/
theorem RR.exists {K K' : WCactus} (hE : K.Ext K') (hM : MonoΘ Θ) {ρ : TRes K}
    (hc : CovR Θ K ρ) : ∃ ρ' : TRes K', RR Θ ρ ρ' := by
  refine RR.exists_of fun l ψ e => RC.exists_cell hE hM (hc l ψ e) ?_
  have hcl := hc l ψ e
  cases hcl with
  | own => exact ⟨_, RR.empty⟩
  | imm _ i hw => exact RR.exists_stratum hE hM i.ls i.res CellUT.wit_inStratum_imm hw
  | «mut» _ m _ _ _ hw => exact RR.exists_stratum hE hM m.ls m.res CellUT.wit_inStratum_mut hw

/-- **Cell invariants re-read at the grown tree.** A covered valid world at `K`, with every type
of the location typing monotone, has at any extension `K'` a re-reading that is covered at `K'`
(each `mut` cell stores its type read at `K'`), lies in every stratum the world did, and is
valid. -/
theorem reread {K K' : WCactus} (hE : K.Ext K') (hM : MonoΘ Θ) {ρ : TRes K}
    (hc : CovR Θ K ρ) (hv : ResUT.Valid ρ) :
    ∃ ρ' : TRes K', RR Θ ρ ρ' ∧ CovR Θ K' ρ' ∧ ResUT.Valid ρ' ∧
      ∀ S, ρ.InStratum S → ρ'.InStratum S := by
  obtain ⟨ρ', h⟩ := RR.exists hE hM hc
  exact ⟨ρ', h, h.cov, WitRel.ResUT.Valid.sim hv h.rsim, fun _ => h.inStratum hE⟩

/-- **Against row 5.57**: the re-read invariant holds wherever the old one held, carried; it is
not false outside the old stratum's image. -/
theorem reread_extends {K K' : WCactus} (hE : K.Ext K') (hM : MonoΘ Θ) {l : BoCa.Loc}
    {m : TMut K} {m' : TMut K'} (hc : Cov Θ K l (.mut m)) (h : RC Θ l (.mut m) (.mut m'))
    {w : BoCa.Val} {r₀ : ResT BoCa.Loc BoCa.Val K m.ls} {r : ResT BoCa.Loc BoCa.Val K' m'.ls}
    (hr₀ : CovR Θ K r₀.toU) (hrr : RR Θ r₀.toU r.toU) (hP : m.P w r₀) : m'.P w r := by
  cases hc with
  | «mut» _ _ τ hΘ hPm _ =>
      cases h with
      | «mut» _ _ _ τ' hΘ' _ _ _ _ hP' =>
          rw [hΘ] at hΘ'; cases Option.some.inj hΘ'
          exact (hP' w r).mpr (hM l τ hΘ K K' hE w _ _ hr₀ hrr ((hPm w r₀).mp hP))

/-! ### Small resources -/

theorem RR.sng {K K' : WCactus} {l : BoCa.Loc} {ψ : TCell K} {ψ' : TCell K'}
    (h : RC Θ l ψ ψ') : RR Θ (PMap.sng l ψ) (PMap.sng l ψ') := by
  classical
  refine ⟨fun m => ?_, fun m χ χ' e e' => ?_⟩
  · simp only [PMap.sng_get]; split <;> simp
  · simp only [PMap.sng_get] at e e'
    split at e
    · subst m; rw [if_pos rfl] at e'
      cases Option.some.inj e; cases Option.some.inj e'; exact h
    · cases e

/-! ### `Mut` and thunks -/

/-- `𝒱⟦Mut @a τ⟧` at `δ(a) = a`: a cell `ℓ ↦ mut(β̄, w, χ, P̂)` with `a ⊑ x` at every member of
`β̄` read in `K`, whose location the location typing gives `τ`, and whose invariant is `τ` **read
at `K`** (`ptoMutT`'s shape, without the records list). -/
def vMut (Θ : LocTy) (a : Life) (τ : KSem) : KSem where
  P K v ρ := ∃ (l : BoCa.Loc) (m : TMut K), v = BoCa.Val.loc l ∧ ρ = PMap.sng l (.mut m) ∧
    Θ l = some τ ∧ (∀ x ∈ m.ls.set, K.le a x) ∧ ∀ w r, m.P w r ↔ τ.P K w r.toU

/-- `𝒱⟦U C⟧` for a computation predicate `C` read at each tree: `C` at every extension of the
tree, on the re-reading of the thunk's resource. -/
def vThunk (Θ : LocTy) (C : (K : WCactus) → BoCa.Val → TRes K → Prop) : KSem where
  P K v ρ := ∀ (K' : WCactus), K.Ext K' → ∀ ρ' : TRes K', RR Θ ρ ρ' → C K' v ρ'

/-- Forcing a thunk at the tree it is held at. -/
theorem vThunk_force {C : (K : WCactus) → BoCa.Val → TRes K → Prop} {K : WCactus}
    {v : BoCa.Val} {ρ : TRes K} (hc : CovR Θ K ρ) (h : (vThunk Θ C).P K v ρ) : C K v ρ :=
  h K (WCactus.Ext.refl K) ρ (RR.refl hc)

theorem kmono_unit : KMono Θ vUnit := by
  rintro K K' - v ρ ρ' - hr ⟨hv, rfl⟩
  exact ⟨hv, RR.of_empty hr⟩

theorem kmono_sum {τ₁ τ₂ : KSem} (h₁ : KMono Θ τ₁) (h₂ : KMono Θ τ₂) :
    KMono Θ (vSum τ₁ τ₂) := by
  rintro K K' hE v ρ ρ' hc hr (⟨v₁, rfl, h⟩ | ⟨v₂, rfl, h⟩)
  · exact Or.inl ⟨v₁, rfl, h₁ K K' hE v₁ ρ ρ' hc hr h⟩
  · exact Or.inr ⟨v₂, rfl, h₂ K K' hE v₂ ρ ρ' hc hr h⟩

theorem kmono_imm {a : Life} {τ : KSem} (hτ : KMono Θ τ) : KMono Θ (vImm a τ) := by
  rintro K K' hE v ρ ρ' hc hr ⟨l, i, rfl, rfl, hle, hP⟩
  obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
  have hci := hc.sng
  cases hrc with
  | imm _ _ i' hs hv hdom hw =>
      cases hci with
      | imm _ _ hcw =>
          refine ⟨l, i', rfl, rfl, fun x hx => hE.le (hle x (hs ▸ hx)), ?_⟩
          rw [hv]
          exact hτ K K' hE _ _ _ hcw ⟨hdom, hw⟩ hP

/-- `Mut @a τ` is monotone whatever `τ` is. **This holds by the definition of `vMut`** (the
invariant is `Θ ℓ` read at the tree) and of `RC` (the re-reading stores `Θ ℓ` read at `K'`); it
is not a result about the cell's contents. What carries the contents is `RC.exists_cell`, which
needs `τ` monotone (`MonoΘ`) to re-read the stored value into the new invariant, and
`reread_extends`. -/
theorem kmono_mut {a : Life} {τ : KSem} : KMono Θ (vMut Θ a τ) := by
  rintro K K' hE v ρ ρ' hc hr ⟨l, m, rfl, rfl, hΘ, hle, -⟩
  obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
  cases hrc with
  | «mut» _ _ m' τ' hΘ' hs _ _ _ hP =>
      rw [hΘ] at hΘ'; cases Option.some.inj hΘ'
      refine ⟨l, m', rfl, rfl, hΘ, fun x hx => ?_, hP⟩
      rw [hs] at hx
      exact hE.le (hle x (K'.minS_sub hx))

theorem kmono_ref {τ : KSem} (hτ : KMono Θ τ) : KMono Θ (vRef τ) := by
  classical
  rintro K K' hE v ρ ρ' hc hr ⟨l, w, ρ₁, rfl, hl, rfl, hP⟩
  obtain ⟨ψ', e', hrc⟩ := hr.get_some (m := l) (ψ := .own w) (by simp [PMap.ins_get])
  cases hrc
  have hr₁ : RR Θ ρ₁ (PMap.del ρ' l) := by
    refine ⟨fun m => ?_, fun m χ χ' e e'' => ?_⟩
    · rw [PMap.del_get]
      by_cases e : m = l
      · subst e; simp [hl]
      · rw [if_neg e]
        have := hr.1 m
        simp only [PMap.ins_get, if_neg e] at this
        exact this
    · rw [PMap.del_get] at e''
      by_cases em : m = l
      · rw [if_pos em] at e''; cases e''
      · rw [if_neg em] at e''
        exact hr.2 m χ χ' (by simp [PMap.ins_get, em, e]) e''
  have hc₁ : CovR Θ K ρ₁ := fun m χ e => by
    have em : m ≠ l := fun h => by subst h; rw [hl] at e; cases e
    exact hc m χ (by simp [PMap.ins_get, em, e])
  refine ⟨l, w, PMap.del ρ' l, rfl, by simp [PMap.del_get], PMap.ext fun m => ?_,
    hτ K K' hE w ρ₁ _ hc₁ hr₁ hP⟩
  rw [PMap.ins_get, PMap.del_get]
  by_cases e : m = l
  · subst e; simp [e']
  · simp [e]

theorem kmono_box {a : Life} {τ : KSem} (hτ : KMono Θ τ) : KMono Θ (vBox a τ) := by
  rintro K K' hE v ρ ρ' hc hr ⟨hP, hS⟩
  exact ⟨hτ K K' hE v ρ ρ' hc hr hP, hr.inStratum hE hS⟩

/-- A thunk is monotone for every computation predicate. **This holds by the definition of
`vThunk`**, which quantifies over every extension and re-reading: extensions and re-readings
compose. It is not a result about the thunk's computation; at the relation, a thunk is introduced
from its computation at every later tree, its environment carried there by the environment type's
monotonicity (`Core/TreeSemC.lean`'s `STy.thunk_intro`). -/
theorem kmono_thunk {C : (K : WCactus) → BoCa.Val → TRes K → Prop} : KMono Θ (vThunk Θ C) := by
  intro K K' hE v ρ ρ' _ hr h K'' hE' ρ'' hr'
  exact h K'' (hE.trans hE') ρ'' (Wp.RR.trans_retype hE' hr hr')

end BoCa.Fig16.Tree

end
