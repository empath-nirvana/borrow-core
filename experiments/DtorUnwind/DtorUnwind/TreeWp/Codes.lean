import DtorUnwind.TreeWp.Clause3

/-!
# Store types as syntactic codes read at the tree

`Tree/KSem.lean`'s store typing `Θ : Loc → Option KSem` gives each location a semantic type, and
`𝒱⟦Mut @a τ⟧` (`vMut`) compares `Θ ℓ` with `τ` as semantic values. A location's type is then
fixed for the run (`LocTy.Le` is growth only). Here, as Core's `FrameRec.T` is a syntactic type
read at a substitution, a store type is a code (`KTy`) and its meaning is read at the tree and at
the code typing (`KTy.interp`). The `Mut` clause reads `Θ ℓ = A` syntactically and stores `A`'s
meaning, so `interp` is structural in the code: there is no circularity to resolve.

* **The semantic typing is `sem Θ`** (`ℓ ↦ ⟦Θ ℓ⟧_Θ`); `Cov`, `RC`, `RR`, `WInv` are read at it
  unchanged, so every result of `Tree/KSem.lean` and `TreeWp/World.lean` applies.
* **Every code is monotone** (`interp_retype` at `Θ' = Θ`, `monoΘ_sem`): the hypothesis
  `MonoΘ` holds of every code typing.
* **A location may be re-typed** when no `mut` cell at it is held (`RR.exists_retype`): a world
  covered at `sem Θ` has a re-reading covered at `sem Θ'` at any tree extension, for any `Θ'`
  agreeing with `Θ` on the locations the world holds a `mut` cell at (`HoldsMut`, at any depth).
  A freed location holds no cell, so it is re-typed by a re-reading. At `Θ' = Θ` and `K' = K` the
  re-reading is the identity (`RR.refl`).

The codes are the formers whose meaning `Tree/KSem.lean` builds at the tree (`1`, `+`, `Imm`,
`Mut`, `[a]`); `ref` and thunks are not coded here.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

/-- **A store type, as a code.** -/
inductive KTy : Type where
  | unit
  | sum (A B : KTy)
  | imm (a : Life) (A : KTy)
  | mut (a : Life) (A : KTy)
  | box (a : Life) (A : KTy)

/-- A code typing of locations. -/
abbrev CodeTy : Type := BoCa.Loc → Option KTy

/-- **A code's meaning at the code typing `Θ`**, read at every tree. -/
def KTy.interp (Θ : CodeTy) : KTy → KSem
  | .unit => vUnit
  | .sum A B => vSum (A.interp Θ) (B.interp Θ)
  | .imm a A => vImm a (A.interp Θ)
  | .mut a A => ⟨fun K v ρ => ∃ (l : BoCa.Loc) (m : TMut K), v = BoCa.Val.loc l ∧
      ρ = PMap.sng l (.mut m) ∧ Θ l = some A ∧ (∀ x ∈ m.ls.set, K.le a x) ∧
      ∀ w r, m.P w r ↔ (A.interp Θ).P K w r.toU⟩
  | .box a A => vBox a (A.interp Θ)

/-- **The semantic store typing of a code typing.** -/
def sem (Θ : CodeTy) : LocTy := fun l => (Θ l).map (KTy.interp Θ)

theorem sem_of {Θ : CodeTy} {l : BoCa.Loc} {A : KTy} (h : Θ l = some A) :
    sem Θ l = some (A.interp Θ) := by simp [sem, h]

/-- `Mut`'s code reads into `vMut` at the semantic typing. -/
theorem interp_mut_le {Θ : CodeTy} {a : Life} {A : KTy} {K : WCactus} {v : BoCa.Val}
    {ρ : TRes K} (h : ((KTy.mut a A).interp Θ).P K v ρ) :
    (vMut (sem Θ) a (A.interp Θ)).P K v ρ := by
  obtain ⟨l, m, hv, hρ, hΘ, hle, hP⟩ := h
  exact ⟨l, m, hv, hρ, sem_of hΘ, hle, hP⟩

/-! ### Locations a world holds a `mut` cell at -/

/-- `ρ` holds a `mut` cell at `ℓ`, at any depth. -/
inductive HoldsMut {K : WCactus} : TRes K → BoCa.Loc → Prop where
  | top {ρ : TRes K} {l : BoCa.Loc} {m : TMut K} (e : ρ.get l = some (.mut m)) : HoldsMut ρ l
  | deep {ρ : TRes K} {k l : BoCa.Loc} {ψ : TCell K} (e : ρ.get k = some ψ)
      (h : HoldsMut ψ.wit l) : HoldsMut ρ l

/-- `Θ'` agrees with `Θ` wherever `ρ` holds a `mut` cell. -/
def AgreeOn {K : WCactus} (Θ Θ' : CodeTy) (ρ : TRes K) : Prop :=
  ∀ l, HoldsMut ρ l → Θ' l = Θ l

theorem AgreeOn.wit {K : WCactus} {Θ Θ' : CodeTy} {ρ : TRes K} (h : AgreeOn Θ Θ' ρ) {k : BoCa.Loc}
    {ψ : TCell K} (e : ρ.get k = some ψ) : AgreeOn Θ Θ' ψ.wit :=
  fun l hl => h l (.deep e hl)

theorem AgreeOn.refl {K : WCactus} (Θ : CodeTy) (ρ : TRes K) : AgreeOn Θ Θ ρ := fun _ _ => rfl

/-! ### Re-reading across a re-typing -/

/-- **A code's meaning is carried along a re-reading at a new tree and a new code typing**, when
the typings agree where the resource holds a `mut` cell. -/
theorem interp_retype {Θ Θ' : CodeTy} (A : KTy) :
    ∀ {K K' : WCactus}, K.Ext K' → ∀ (v : BoCa.Val) (ρ : TRes K) (ρ' : TRes K'),
      CovR (sem Θ) K ρ → RR (sem Θ') ρ ρ' → AgreeOn Θ Θ' ρ →
      (A.interp Θ).P K v ρ → (A.interp Θ').P K' v ρ' := by
  induction A with
  | unit =>
      rintro K K' - v ρ ρ' - hr - ⟨hv, rfl⟩
      exact ⟨hv, RR.of_empty hr⟩
  | sum A B ihA ihB =>
      rintro K K' hE v ρ ρ' hc hr hag (⟨v₁, rfl, h⟩ | ⟨v₂, rfl, h⟩)
      · exact Or.inl ⟨v₁, rfl, ihA hE v₁ ρ ρ' hc hr hag h⟩
      · exact Or.inr ⟨v₂, rfl, ihB hE v₂ ρ ρ' hc hr hag h⟩
  | imm a A ih =>
      rintro K K' hE v ρ ρ' hc hr hag ⟨l, i, rfl, rfl, hle, hP⟩
      obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
      have hci := hc.sng
      have e : (PMap.sng l (CellUT.imm i) : TRes K).get l = some (.imm i) := by
        simp [PMap.sng_get]
      cases hrc with
      | imm _ _ i' hs hv hdom hw =>
          cases hci with
          | imm _ _ hcw =>
              refine ⟨l, i', rfl, rfl, fun x hx => hE.le (hle x (hs ▸ hx)), ?_⟩
              rw [hv]
              exact ih hE _ _ _ hcw ⟨hdom, hw⟩ (hag.wit e) hP
  | «mut» a A _ =>
      rintro K K' hE v ρ ρ' - hr hag ⟨l, m, rfl, rfl, hΘ, hle, -⟩
      obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
      have hl : Θ' l = some A := by
        rw [hag l (.top (m := m) (by simp [PMap.sng_get]))]; exact hΘ
      cases hrc with
      | «mut» _ _ m' τ' hΘ' hs _ _ _ hP =>
          rw [sem_of hl] at hΘ'; cases Option.some.inj hΘ'
          refine ⟨l, m', rfl, rfl, hl, fun x hx => ?_, hP⟩
          rw [hs] at hx
          exact hE.le (hle x (K'.minS_sub hx))
  | box a A ih =>
      rintro K K' hE v ρ ρ' hc hr hag ⟨hP, hS⟩
      exact ⟨ih hE v ρ ρ' hc hr hag hP, hr.inStratum hE hS⟩

/-- **Every code typing's types are monotone.** -/
theorem monoΘ_sem (Θ : CodeTy) : MonoΘ (sem Θ) := by
  intro l τ e K K' hE v ρ ρ' hc hr h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.mp e
  exact interp_retype A hE v ρ ρ' hc hr (AgreeOn.refl Θ ρ) h

/-- One cell's re-reading across a re-typing, from its witness's (`RC.exists_cell`'s proof). -/
theorem RC.exists_retype {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K') {l : BoCa.Loc}
    {ψ : TCell K} (hc : Cov (sem Θ) K l ψ) (hagl : ψ.kind = .mut → Θ' l = Θ l)
    (hagw : AgreeOn Θ Θ' ψ.wit) (hw : ∃ χ' : TRes K', RR (sem Θ') ψ.wit χ') :
    ∃ ψ' : TCell K', RC (sem Θ') l ψ ψ' := by
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
      obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp hΘ
      have hA' : Θ' l = some A := (hagl rfl).trans hA
      have hs : χ'.InStratum (K'.minS m.ls) :=
        (RR.inStratum hE hχ CellUT.wit_inStratum_mut).minS
      have hτ : (A.interp Θ').P K' m.v χ' :=
        interp_retype A hE m.v m.res χ' hcw hχ hagw ((hP m.v m.ρ).mp m.hw)
      let m' : TMut K' := ⟨K'.minS m.ls, K'.minS_anti _, m.v, ResST.toRes ⟨χ', hs⟩,
        fun w r => (A.interp Θ').P K' w r.toU, by
          show (A.interp Θ').P K' m.v (ResST.toRes ⟨χ', hs⟩).toU
          rw [ResST.toU_toRes]; exact hτ⟩
      have hres : m'.res = χ' := ResST.toU_toRes ⟨χ', hs⟩
      refine ⟨.mut m', .mut l m m' _ (sem_of hA') rfl rfl ?_ ?_ fun _ _ => Iff.rfl⟩
      · intro k; rw [hres]; exact hχ.1 k
      · intro k ψ ψ' e e'; rw [hres] at e'; exact hχ.2 k ψ ψ' e e'

/-- Re-readings across a re-typing exist in every stratum (`RR.exists_stratum`'s proof). -/
theorem RR.exists_retype_stratum {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K') (T : TSet) :
    ∀ ρ : TRes K, ρ.InStratum T → CovR (sem Θ) K ρ → AgreeOn Θ Θ' ρ →
      ∃ ρ' : TRes K', RR (sem Θ') ρ ρ' := by
  induction T using K.above_wf.induction with
  | _ T ih =>
  intro ρ hT hc hag
  refine RR.exists_of fun l ψ e => RC.exists_retype hE (hc l ψ e) ?_ (hag.wit e) ?_
  · intro hk
    cases ψ with
    | «mut» m => exact hag l (.top e)
    | own => cases hk
    | imm => cases hk
  · have hcl := hc l ψ e
    cases hcl with
    | own => exact ⟨_, RR.empty⟩
    | imm _ i hw => exact ih i.ls (hT l _ e) i.res CellUT.wit_inStratum_imm hw (hag.wit e)
    | «mut» _ m _ _ _ hw => exact ih m.ls (hT l _ e) m.res CellUT.wit_inStratum_mut hw (hag.wit e)

/-- **A world re-read across a re-typing**: covered at `sem Θ`, with `Θ'` agreeing with `Θ`
wherever the world holds a `mut` cell, it has a re-reading at any tree extension, covered at
`sem Θ'`. -/
theorem RR.exists_retype {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K') {ρ : TRes K}
    (hc : CovR (sem Θ) K ρ) (hag : AgreeOn Θ Θ' ρ) :
    ∃ ρ' : TRes K', RR (sem Θ') ρ ρ' ∧ CovR (sem Θ') K' ρ' := by
  have : ∃ ρ' : TRes K', RR (sem Θ') ρ ρ' := by
    refine RR.exists_of fun l ψ e => RC.exists_retype hE (hc l ψ e) ?_ (hag.wit e) ?_
    · intro hk
      cases ψ with
      | «mut» m => exact hag l (.top e)
      | own => cases hk
      | imm => cases hk
    · have hcl := hc l ψ e
      cases hcl with
      | own => exact ⟨_, RR.empty⟩
      | imm _ i hw =>
          exact RR.exists_retype_stratum hE i.ls i.res CellUT.wit_inStratum_imm hw (hag.wit e)
      | «mut» _ m _ _ _ hw =>
          exact RR.exists_retype_stratum hE m.ls m.res CellUT.wit_inStratum_mut hw (hag.wit e)
  obtain ⟨ρ', hr⟩ := this
  exact ⟨ρ', hr, hr.cov⟩

/-- **Nothing changes where nothing grows**: at `Θ' = Θ` and `K' = K` the re-reading is the
world itself. -/
theorem RR.exists_retype_refl {Θ : CodeTy} {K : WCactus} {ρ : TRes K} (hc : CovR (sem Θ) K ρ) :
    RR (sem Θ) (K' := K) ρ ρ := RR.refl hc

/-- **A location holding no `mut` cell is re-typed**: `Θ[ℓ ↦ B]` agrees with `Θ` on every world
that holds no `mut` cell at `ℓ`. -/
theorem agreeOn_set {K : WCactus} (Θ : CodeTy) {l₀ : BoCa.Loc} (B : Option KTy) {ρ : TRes K}
    (h : ¬ HoldsMut ρ l₀) :
    AgreeOn Θ (fun l => if l = l₀ then B else Θ l) ρ := by
  intro l hl
  have : l ≠ l₀ := fun e => h (e ▸ hl)
  simp [this]

end BoCa.Fig16.Tree.Wp

end
