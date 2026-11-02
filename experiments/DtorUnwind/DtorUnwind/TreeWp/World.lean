import DtorUnwind.Tree.KSem
import DtorUnwind.Tree.Port.Base

/-!
# The world over the tree-stratified carrier

The step-indexed relation of `SI/Capture.lean` reads, at every frame and every end of a run, a
world `fρ` with records proper `ps`, a list `ls`, `TWNC fρ ps (rsOf ls)`, `Tagged fρ ps ls`, and
`ResU.Lower fρ μ`. Over the tree-stratified carrier (`Tree/Carrier.lean`) the world is:

* **`K`**, the lifetime tree, as a parent function `P` (`Tree/Parent.lean`): a fresh lend and a
  graft are both `ParentFn.Graft`s, so both extend `K` (`WCactus.Ext`) by `graft_mono`.
* **`Θ`**, the store typing: the semantic type, read at the current tree, every `mut` cell at a
  location stores (`Tree/KSem.lean`'s `Cov`). It grows (`LocTy.Le`).
* **the resource**, a `TRes K`, covered by `Θ` at `K`, lowering to the memory (`WInv`).

`TWd.Ext` is the extension of worlds: `K` keeps every nesting, `Θ` keeps every location's type.
Along it a resource is carried by `RR`, read at the new `Θ`. What this file proves of it:

* **`Θ` grows**: `Cov`, `RC` and `RR` read at `Θ` hold at every `Θ′ ⊒ Θ` (`Cov.mono`,
  `RC.mono`, `RR.mono`). `KSem` held `Θ` fixed; a type is carried along a growing `Θ` when it is
  monotone at every larger store typing (`MonoUp`).
* **`●` commutes with re-reading** (`RR.compS`, `RR.split`): the re-reading of a composite is the
  composite of the re-readings. `●` composes only `imm` cells, and two `imm` cells that compose
  agree on their witness, whose re-reading is unique (`RR.func`).
* **`⟦·⟧` is kept** (`ResUT.Lower.rr`): the walks are carried along `RR` with tags and values
  kept (`Tree/CarrierSim.lean`), so the flattening lowers to the same memory.
* **The world is re-read** at every extension (`WInv.reread`): covered, lowering to the same
  memory.

`RR.refl` is the identity when the world does not grow, so at `TWd.Ext w w` every statement here
is the one without re-reading.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-! ### The store typing grows -/

/-- `Θ′` keeps every location's type. -/
def LocTy.Le (Θ Θ' : LocTy) : Prop := ∀ l τ, Θ l = some τ → Θ' l = some τ

theorem LocTy.Le.refl (Θ : LocTy) : Θ.Le Θ := fun _ _ h => h

theorem LocTy.Le.trans {Θ₁ Θ₂ Θ₃ : LocTy} (h₁ : Θ₁.Le Θ₂) (h₂ : Θ₂.Le Θ₃) : Θ₁.Le Θ₃ :=
  fun l τ h => h₂ l τ (h₁ l τ h)

theorem Cov.mono {Θ Θ' : LocTy} (hΘ : Θ.Le Θ') {K : WCactus} {l : BoCa.Loc} {ψ : TCell K}
    (h : Cov Θ K l ψ) : Cov Θ' K l ψ := by
  induction h with
  | own l v => exact .own l v
  | imm l i _ ih => exact .imm l i ih
  | «mut» l m τ hτ hP _ ih => exact .mut l m τ (hΘ l τ hτ) hP ih

theorem CovR.mono {Θ Θ' : LocTy} (hΘ : Θ.Le Θ') {K : WCactus} {ρ : TRes K}
    (h : CovR Θ K ρ) : CovR Θ' K ρ :=
  fun l ψ e => (h l ψ e).mono hΘ

theorem RC.mono {Θ Θ' : LocTy} (hΘ : Θ.Le Θ') {K K' : WCactus} {l : BoCa.Loc} {ψ : TCell K}
    {ψ' : TCell K'} (h : RC Θ l ψ ψ') : RC Θ' l ψ ψ' := by
  induction h with
  | own l v => exact .own l v
  | imm l i i' hs hv hdom _ ih => exact .imm l i i' hs hv hdom ih
  | «mut» l m m' τ hτ hs hv hdom _ hP ih => exact .mut l m m' τ (hΘ l τ hτ) hs hv hdom ih hP

theorem RR.mono {Θ Θ' : LocTy} (hΘ : Θ.Le Θ') {K K' : WCactus} {ρ : TRes K} {ρ' : TRes K'}
    (h : RR Θ ρ ρ') : RR Θ' ρ ρ' :=
  ⟨h.1, fun m ψ ψ' e e' => (h.2 m ψ ψ' e e').mono hΘ⟩

/-- **A type carried along every growth of the store typing**: monotone along tree extension at
every store typing keeping `Θ`'s types. -/
def KMonoUp (Θ : LocTy) (τ : KSem) : Prop := ∀ Θ', Θ.Le Θ' → KMono Θ' τ

/-- Every type `Θ` assigns is carried along every growth. -/
def MonoUp (Θ : LocTy) : Prop := ∀ l τ, Θ l = some τ → KMonoUp Θ τ

theorem MonoUp.monoΘ {Θ : LocTy} (h : MonoUp Θ) : MonoΘ Θ :=
  fun l τ e => h l τ e Θ (LocTy.Le.refl Θ)

theorem MonoUp.mono {Θ Θ' : LocTy} (h : MonoUp Θ') (hΘ : Θ.Le Θ') : ∀ l τ, Θ l = some τ →
    KMono Θ' τ :=
  fun l τ e => h l τ (hΘ l τ e) Θ' (LocTy.Le.refl Θ')

/-- The types of `1`, `+` and `Imm` carried along every growth. -/
theorem kmonoUp_unit (Θ : LocTy) : KMonoUp Θ vUnit := fun _ _ => kmono_unit

theorem kmonoUp_sum {Θ : LocTy} {τ₁ τ₂ : KSem} (h₁ : KMonoUp Θ τ₁) (h₂ : KMonoUp Θ τ₂) :
    KMonoUp Θ (vSum τ₁ τ₂) := fun Θ' hΘ => kmono_sum (h₁ Θ' hΘ) (h₂ Θ' hΘ)

theorem kmonoUp_imm {Θ : LocTy} {a : Life} {τ : KSem} (h : KMonoUp Θ τ) :
    KMonoUp Θ (vImm a τ) := fun Θ' hΘ => kmono_imm (h Θ' hΘ)

/-! ### The world -/

/-- **A world over the tree-stratified carrier**: the lifetime tree and the store typing. -/
structure TWd where
  /-- The lifetime tree, as a parent function. -/
  P : ParentFn
  /-- The store typing. -/
  Θ : LocTy

/-- The lifetime tree. -/
abbrev TWd.K (w : TWd) : WCactus := WCactus.ofParent w.P

/-- **The extension of worlds**: every nesting of the tree kept, every location's type kept. -/
def TWd.Ext (w w' : TWd) : Prop := w.K.Ext w'.K ∧ w.Θ.Le w'.Θ

theorem TWd.Ext.refl (w : TWd) : w.Ext w := ⟨WCactus.Ext.refl _, LocTy.Le.refl _⟩

theorem TWd.Ext.trans {w₁ w₂ w₃ : TWd} (h₁ : w₁.Ext w₂) (h₂ : w₂.Ext w₃) : w₁.Ext w₃ :=
  ⟨WCactus.Ext.trans h₁.1 h₂.1, LocTy.Le.trans h₁.2 h₂.2⟩

/-- **Re-reading along a world extension**: `RR` at the new store typing. -/
abbrev RRw {w w' : TWd} (ρ : TRes w.K) (ρ' : TRes w'.K) : Prop := RR w'.Θ ρ ρ'

/-- Re-readings compose along world extensions. -/
theorem RRw.trans {w₁ w₂ w₃ : TWd} (h₂₃ : w₂.Ext w₃) {ρ₁ : TRes w₁.K} {ρ₂ : TRes w₂.K}
    {ρ₃ : TRes w₃.K} (h : RRw (w' := w₂) ρ₁ ρ₂) (h' : RRw (w' := w₃) ρ₂ ρ₃) :
    RRw (w' := w₃) ρ₁ ρ₃ :=
  RR.trans h₂₃.1 (h.mono h₂₃.2) h'

/-- **The world invariant**: the world covered at the tree by the store typing, its types carried
along every growth, its lowering the memory. -/
def WInv (w : TWd) (fρ : TRes w.K) (μ : BoCa.Loc → Option BoCa.Val) : Prop :=
  CovR w.Θ w.K fρ ∧ MonoUp w.Θ ∧ ResUT.Lower fρ μ

theorem WInv.valid {w : TWd} {fρ : TRes w.K} {μ : BoCa.Loc → Option BoCa.Val}
    (h : WInv w fρ μ) : ResUT.Valid fρ := by
  obtain ⟨σ, hσ, -⟩ := h.2.2
  exact ⟨σ, hσ⟩

/-! ### `imm` cells under re-reading -/

theorem ImmT.res_toRes {K : WCactus} {s : TSet} {v : BoCa.Val} {χ : TRes K}
    (h : χ.InStratum s) : (⟨s, v, ResST.toRes ⟨χ, h⟩⟩ : TImm K).res = χ :=
  ResST.toU_toRes ⟨χ, h⟩

/-- The re-reading of `imm(s, v, χ)`: `imm(s, v, χ′)` with `χ′` the re-reading of `χ`. -/
theorem RC.immOf_inv {Θ : LocTy} {K K' : WCactus} {l : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {χ : TRes K} {h : χ.InStratum s} {ψ' : TCell K'}
    (hr : RC Θ l (CellUT.immOf s v χ h) ψ') :
    ∃ (χ' : TRes K') (h' : χ'.InStratum s), ψ' = CellUT.immOf s v χ' h' ∧ RR Θ χ χ' := by
  unfold CellUT.immOf at hr
  cases hr with
  | imm _ _ i' hs hv hdom hw =>
      obtain ⟨s', v', ρ'⟩ := i'
      simp only at hs hv
      subst hs; subst hv
      rw [ImmT.res_toRes] at hdom hw
      refine ⟨ρ'.toU, ρ'.toU_inStratum, (ImmT.immOf_eta _).symm, hdom, hw⟩

theorem RC.immOf_of {Θ : LocTy} {K K' : WCactus} {l : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {χ : TRes K} {χ' : TRes K'} (h : χ.InStratum s) (h' : χ'.InStratum s) (hr : RR Θ χ χ') :
    RC Θ l (CellUT.immOf s v χ h) (CellUT.immOf s v χ' h') := by
  refine .imm l _ _ rfl rfl (fun m => ?_) (fun m ψ ψ' a b => ?_)
  · rw [ImmT.res_toRes, ImmT.res_toRes]; exact hr.1 m
  · rw [ImmT.res_toRes] at a b; exact hr.2 m ψ ψ' a b

/-- **`●` of two cells commutes with re-reading.** -/
theorem RC.compS {Θ : LocTy} {K K' : WCactus} {l : BoCa.Loc} {ψ₁ ψ₂ ψ : TCell K}
    {ψ₁' ψ₂' : TCell K'} (h₁ : RC Θ l ψ₁ ψ₁') (h₂ : RC Θ l ψ₂ ψ₂')
    (hc : CellUT.CompS ψ₁ ψ₂ ψ) : ∃ ψ', CellUT.CompS ψ₁' ψ₂' ψ' ∧ RC Θ l ψ ψ' := by
  obtain ⟨s₁, s₂, v, χ, a₁, a₂, a₃, rfl, rfl, rfl⟩ := hc
  obtain ⟨χ₁, b₁, rfl, r₁⟩ := RC.immOf_inv h₁
  obtain ⟨χ₂, b₂, rfl, r₂⟩ := RC.immOf_inv h₂
  obtain rfl := RR.func r₁ r₂
  have b₃ : χ₁.InStratum (s₁ ∪ s₂) := ResUT.inStratum_union_iff.mpr ⟨b₁, b₂⟩
  exact ⟨_, ⟨s₁, s₂, v, χ₁, b₁, b₂, b₃, rfl, rfl, rfl⟩, RC.immOf_of a₃ b₃ r₁⟩

/-- Two optional cells related by re-reading at `l`. -/
def ORel (Θ : LocTy) {K K' : WCactus} (l : BoCa.Loc) (o : Option (TCell K)) (o' : Option (TCell K')) :
    Prop :=
  (o = none ↔ o' = none) ∧ ∀ ψ ψ', o = some ψ → o' = some ψ' → RC Θ l ψ ψ'

theorem ORel.optComp {Θ : LocTy} {K K' : WCactus} {l : BoCa.Loc} {o₁ o₂ o : Option (TCell K)}
    {o₁' o₂' o' : Option (TCell K')} (h₁ : ORel Θ l o₁ o₁') (h₂ : ORel Θ l o₂ o₂')
    (hc : G.OptComp CellUT.CompS o₁ o₂ o) (hc' : G.OptComp CellUT.CompS o₁' o₂' o') :
    ORel Θ l o o' := by
  rcases o₁ with _ | ψ₁ <;> rcases o₂ with _ | ψ₂
  · have e₁ : o₁' = none := h₁.1.mp rfl
    have e₂ : o₂' = none := h₂.1.mp rfl
    subst e₁ e₂
    simp only [G.OptComp] at hc hc'
    subst hc hc'
    exact ⟨by simp, fun _ _ a => by cases a⟩
  · have e₁ : o₁' = none := h₁.1.mp rfl
    obtain ⟨ψ₂', e₂⟩ : ∃ ψ, o₂' = some ψ := Option.ne_none_iff_exists'.mp
      (fun e => absurd (h₂.1.mpr e) (by simp))
    subst e₁ e₂
    simp only [G.OptComp] at hc hc'
    subst hc hc'
    exact ⟨by simp, fun ψ ψ' a b => by cases a; cases b; exact h₂.2 _ _ rfl rfl⟩
  · obtain ⟨ψ₁', e₁⟩ : ∃ ψ, o₁' = some ψ := Option.ne_none_iff_exists'.mp
      (fun e => absurd (h₁.1.mpr e) (by simp))
    have e₂ : o₂' = none := h₂.1.mp rfl
    subst e₁ e₂
    simp only [G.OptComp] at hc hc'
    subst hc hc'
    exact ⟨by simp, fun ψ ψ' a b => by cases a; cases b; exact h₁.2 _ _ rfl rfl⟩
  · obtain ⟨ψ₁', e₁⟩ : ∃ ψ, o₁' = some ψ := Option.ne_none_iff_exists'.mp
      (fun e => absurd (h₁.1.mpr e) (by simp))
    obtain ⟨ψ₂', e₂⟩ : ∃ ψ, o₂' = some ψ := Option.ne_none_iff_exists'.mp
      (fun e => absurd (h₂.1.mpr e) (by simp))
    subst e₁ e₂
    obtain ⟨ψ, rfl, hψ⟩ := hc
    obtain ⟨ψ'', rfl, hψ''⟩ := hc'
    obtain ⟨ψ', hψ', r⟩ := RC.compS (h₁.2 _ _ rfl rfl) (h₂.2 _ _ rfl rfl) hψ
    obtain rfl := CellUT.CompS.functional hψ'' hψ'
    exact ⟨by simp, fun _ _ a b => by cases a; cases b; exact r⟩

theorem RR.orel {Θ : LocTy} {K K' : WCactus} {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ')
    (l : BoCa.Loc) : ORel Θ l (ρ.get l) (ρ'.get l) :=
  ⟨h.1 l, h.2 l⟩

/-- **`●` of two resources commutes with re-reading.** -/
theorem RR.compS {Θ : LocTy} {K K' : WCactus} {ρ₁ ρ₂ ρ : TRes K} {ρ₁' ρ₂' : TRes K'}
    (h₁ : RR Θ ρ₁ ρ₁') (h₂ : RR Θ ρ₂ ρ₂') (hc : ResUT.CompS ρ₁ ρ₂ ρ) :
    ∃ ρ', ResUT.CompS ρ₁' ρ₂' ρ' ∧ RR Θ ρ ρ' := by
  have hcat : ResUT.CompatS ρ₁' ρ₂' := by
    intro l ψ₁' ψ₂' e₁ e₂
    obtain ⟨ψ₁, f₁, r₁⟩ := h₁.get_some' e₁
    obtain ⟨ψ₂, f₂, r₂⟩ := h₂.get_some' e₂
    have hl := hc.2 l
    rw [f₁, f₂] at hl
    obtain ⟨ψ, -, hψ⟩ := hl
    obtain ⟨ψ', hψ', -⟩ := RC.compS r₁ r₂ hψ
    exact hψ'.compat
  obtain ⟨ρ', hρ'⟩ := (ResUT.compS_defined_iff ρ₁' ρ₂').mpr hcat
  have key : ∀ m, ORel Θ m (ρ.get m) (ρ'.get m) := fun m =>
    ORel.optComp (h₁.orel m) (h₂.orel m) (hc.2 m) (hρ'.2 m)
  exact ⟨ρ', hρ', fun m => (key m).1, fun m => (key m).2⟩

/-! ### Coverage of parts, and the re-reading of a split -/

theorem Cov.immOf_iff {Θ : LocTy} {K : WCactus} {l : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {χ : TRes K} {h : χ.InStratum s} :
    Cov Θ K l (CellUT.immOf s v χ h) ↔ ∀ m ψ, χ.get m = some ψ → Cov Θ K m ψ := by
  constructor
  · intro hc
    unfold CellUT.immOf at hc
    cases hc with
    | imm _ _ hw => intro m ψ e; exact hw m ψ (by rw [ImmT.res_toRes]; exact e)
  · intro hw
    exact .imm l _ fun m ψ e => hw m ψ (by rw [ImmT.res_toRes] at e; exact e)

/-- **A part of a covered resource is covered.** -/
theorem CovR.of_compS_left {Θ : LocTy} {K : WCactus} {a b y : TRes K}
    (hc : ResUT.CompS a b y) (h : CovR Θ K y) : CovR Θ K a := by
  intro l ψ e
  have hl := hc.2 l
  rw [e] at hl
  cases eb : b.get l with
  | none => rw [eb] at hl; simp only [G.OptComp] at hl; exact h l ψ hl
  | some ψb =>
      rw [eb] at hl
      obtain ⟨ψ', e', s₁, s₂, v, χ, a₁, a₂, a₃, rfl, rfl, rfl⟩ := hl
      exact Cov.immOf_iff.mpr (Cov.immOf_iff.mp (h l _ e'))

theorem CovR.of_compS_right {Θ : LocTy} {K : WCactus} {a b y : TRes K}
    (hc : ResUT.CompS a b y) (h : CovR Θ K y) : CovR Θ K b :=
  CovR.of_compS_left (ResUT.CompS.comm hc) h

/-- **The re-reading of a composite splits** into the re-readings of its parts. -/
theorem RR.split {Θ : LocTy} {K K' : WCactus} (hE : K.Ext K') (hM : MonoΘ Θ) {a b y : TRes K}
    {y' : TRes K'} (hc : ResUT.CompS a b y) (hy : CovR Θ K y) (hr : RR Θ y y') :
    ∃ a' b', RR Θ a a' ∧ RR Θ b b' ∧ ResUT.CompS a' b' y' := by
  obtain ⟨a', ha⟩ := RR.exists hE hM (hy.of_compS_left hc)
  obtain ⟨b', hb⟩ := RR.exists hE hM (hy.of_compS_right hc)
  obtain ⟨y'', hy'', hr'⟩ := RR.compS ha hb hc
  obtain rfl := RR.func hr hr'
  exact ⟨a', b', ha, hb, hy''⟩

/-! ### `⟦·⟧` along re-reading -/

/-- **The flattening carried along `RR`**, related cell by cell. -/
theorem ResUT.Flat.rr {Θ : LocTy} {K K' : WCactus} {ρ σ : TRes K} {ρ' : TRes K'}
    (h : ResUT.Flat ρ σ) (hr : RR Θ ρ ρ') :
    ∃ σ', ResUT.Flat ρ' σ' ∧ (rrRel Θ K K').RSim σ' σ := by
  obtain ⟨e, a, he, ha, hσ⟩ := h
  have hs := hr.rsim
  have hRS : ∀ ψ₁ ψ₂ ψ, CellUT.CompS (K := K') (Loc := BoCa.Loc) (Val := BoCa.Val) ψ₁ ψ₂ ψ →
      CellUT.CompatS ψ₁ ψ₂ := fun _ _ _ hc => hc.compat
  have hCS : ∀ {ψ₁ ψ₂ ψ : TCell K} {ψ₁' ψ₂' : TCell K'},
      (rrRel Θ K K').TSim ψ₁' ψ₁ → (rrRel Θ K K').TSim ψ₂' ψ₂ → CellUT.CompS ψ₁ ψ₂ ψ →
      ∃ ψ', CellUT.CompS ψ₁' ψ₂' ψ' ∧ (rrRel Θ K K').TSim ψ' ψ :=
    fun a b c => WitRel.wtsim_compS (W := rrRel Θ K K') a b c
  obtain ⟨e', he', se⟩ := WitRel.ExW.sim (W := rrRel Θ K K') hRS hCS he _ hs
  obtain ⟨a', ha', sa⟩ := WitRel.AgW.sim (W := rrRel Θ K K') ha _ hs
  obtain ⟨σ', hσ', sσ⟩ := WitRel.wrsim_comp (W := rrRel Θ K K') hRS hCS se sa hσ
  exact ⟨σ', ⟨e', a', he', ha', hσ'⟩, sσ⟩

/-- **`⟦·⟧` is kept by re-reading.** -/
theorem ResUT.Lower.rr {Θ : LocTy} {K K' : WCactus} {ρ : TRes K} {ρ' : TRes K'}
    {μ : BoCa.Loc → Option BoCa.Val} (h : ResUT.Lower ρ μ) (hr : RR Θ ρ ρ') :
    ResUT.Lower ρ' μ := by
  obtain ⟨σ, hσ, hμ⟩ := h
  obtain ⟨σ', hσ', hs⟩ := hσ.rr hr
  refine ⟨σ', hσ', fun l => ?_⟩
  rw [hμ l]
  have := hs l
  revert this
  cases σ'.get l <;> cases σ.get l <;> intro h <;> cases h
  · rfl
  · rename_i a b h; simp [h.2.1]

/-- **The world re-read at an extension**: covered, its types carried, lowering to the same
memory. -/
theorem WInv.reread {w w' : TWd} (hE : w.Ext w') {fρ : TRes w.K} {μ : BoCa.Loc → Option BoCa.Val}
    (h : WInv w fρ μ) (hM : MonoUp w'.Θ) :
    ∃ fρ' : TRes w'.K, RRw (w := w) (w' := w') fρ fρ' ∧ WInv w' fρ' μ := by
  have hM' : MonoΘ w'.Θ := hM.monoΘ
  obtain ⟨fρ', hr⟩ := RR.exists hE.1 hM' (h.1.mono hE.2)
  exact ⟨fρ', hr, hr.cov, hM, h.2.2.rr hr⟩

/-- `#` along re-reading: the composite re-read is valid. -/
theorem ResUT.Hash.of_compS {K : WCactus} {a b y : TRes K} (hc : ResUT.CompS a b y)
    (hv : ResUT.Valid y) : ResUT.Hash a b :=
  ⟨hc.1, y, hc, hv⟩

end BoCa.Fig16.Tree

end
