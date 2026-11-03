import Support.Model.Tree.World.Codes
import Support.Model.Tree.Port.Base

/-!
# The world over the tree-stratified carrier

`[spec §62]`. Core's typed world (`Core/World.lean`) reads, at every frame and every end of a run,
a world `fρ` with records proper `ps` and a tagged list `ls`, and `ResU.Lower fρ μ`. Over the
tree-stratified carrier (`Tree/Carrier.lean`) the world is:

* **`K`**, the lifetime tree, as a parent function `P` (`Tree/Parent.lean`): a fresh lend and a
  graft are both `ParentFn.Graft`s, so both extend `K` (`WCactus.Ext`) by `graft_mono`.
* **`Θ`**, the store typing, a code per location (`World/Codes.lean`); its cells are read at
  the semantic typing `sem Θ` (`Tree/Reread.lean`'s `Cov`).
* **`tc`**, the template choice the records' canonical images are read at
  (`World/Records.lean`'s `TChoice`); a run at a world keeps it, and a grown world carries it
  (`TWNT.reread`'s `TcCarried`).
* **the resource**, a `TRes K`, covered by `sem Θ` at `K`, lowering to the memory (`WInv`).

`TWd.Ext w w′ ρ` is the extension of worlds carrying `ρ`: `K` keeps every nesting, and `Θ′`
agrees with `Θ` wherever `ρ` holds a `mut` cell (`AgreeOn`). A location no `mut` cell of `ρ` is
at may be re-typed (a freed location re-allocated). Along it `ρ` is carried by `RR`, read at
`sem Θ′` (`RRw`). What this file proves of it:

* **`Ext` composes** along the re-reading (`TWd.Ext.trans`) and passes to the parts of a
  composite (`TWd.Ext.of_compS_left`).
* **`●` commutes with re-reading** (`RR.compS`, `RR.split_retype`): the re-reading of a composite
  is the composite of the re-readings. `●` composes only `imm` cells, and two `imm` cells that
  compose agree on their witness, whose re-reading is unique (`RR.func`).
* **`⟦·⟧` is kept** (`ResUT.Lower.rr`): the walks are carried along `RR` with tags and values
  kept (`Tree/CarrierSim.lean`), so the flattening lowers to the same memory.
* **The world is re-read** at every extension carrying it (`WInv.reread`, from
  `RR.exists_retype`): covered, lowering to the same memory. Codes are carried along
  re-reading (`interp_retype`), so no monotonicity is asked of the world.

At `w′ = w` the re-reading is the identity (`RR.refl`), and `TWd.Ext w w ρ` holds
(`TWd.Ext.refl`), so every statement here is the one without re-reading.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
open BoCa.Fig16.Tree.Wp

/-! ### The world -/

/-- **A world over the tree-stratified carrier**: the lifetime tree, the store typing and the
template choice. -/
structure TWd where
  /-- The lifetime tree, as a parent function. -/
  P : ParentFn
  /-- The store typing, a code per location. -/
  Θ : CodeTy
  /-- The template choice the canonical images of the world's records are read at
  (`TChoice`, `World/Records.lean`): kept by every step, carried when the tree grows. -/
  tc : TRes (WCactus.ofParent P) → KTy → BoCa.Val → TRes (WCactus.ofParent P)

/-- The lifetime tree. -/
abbrev TWd.K (w : TWd) : WCactus := WCactus.ofParent w.P

/-- **The extension of worlds carrying `ρ`**: every nesting of the tree kept, the store typing
kept wherever `ρ` holds a `mut` cell. -/
def TWd.Ext (w w' : TWd) (ρ : TRes w.K) : Prop := w.K.Ext w'.K ∧ AgreeOn w.Θ w'.Θ ρ

theorem TWd.Ext.refl (w : TWd) (ρ : TRes w.K) : w.Ext w ρ :=
  ⟨WCactus.Ext.refl _, AgreeOn.refl _ _⟩

/-- **Re-reading along a world extension**: `RR` at the new semantic typing. -/
abbrev RRw {w w' : TWd} (ρ : TRes w.K) (ρ' : TRes w'.K) : Prop := RR (sem w'.Θ) ρ ρ'

/-- Extensions compose along the re-reading of what they carry. -/
theorem TWd.Ext.trans {w₁ w₂ w₃ : TWd} {ρ₁ : TRes w₁.K} {ρ₂ : TRes w₂.K}
    (h₁ : w₁.Ext w₂ ρ₁) (hr : RRw (w := w₁) (w' := w₂) ρ₁ ρ₂) (h₂ : w₂.Ext w₃ ρ₂) :
    w₁.Ext w₃ ρ₁ :=
  ⟨WCactus.Ext.trans h₁.1 h₂.1, AgreeOn.trans h₁.2 hr h₂.2⟩

theorem TWd.Ext.of_compS_left {w w' : TWd} {a b y : TRes w.K} (hc : ResUT.CompS a b y)
    (h : w.Ext w' y) : w.Ext w' a :=
  ⟨h.1, h.2.of_compS_left hc⟩

theorem TWd.Ext.of_compS_right {w w' : TWd} {a b y : TRes w.K} (hc : ResUT.CompS a b y)
    (h : w.Ext w' y) : w.Ext w' b :=
  ⟨h.1, h.2.of_compS_right hc⟩

/-- Re-readings compose along world extensions. -/
theorem RRw.trans {w₁ w₂ w₃ : TWd} (h₂₃ : w₂.K.Ext w₃.K) {ρ₁ : TRes w₁.K} {ρ₂ : TRes w₂.K}
    {ρ₃ : TRes w₃.K} (h : RRw (w' := w₂) ρ₁ ρ₂) (h' : RRw (w' := w₃) ρ₂ ρ₃) :
    RRw (w' := w₃) ρ₁ ρ₃ :=
  RR.trans_retype h₂₃ h h'

/-- **The world invariant**: the world covered at the tree by the store typing, its lowering
the memory. -/
def WInv (w : TWd) (fρ : TRes w.K) (μ : BoCa.Loc → Option BoCa.Val) : Prop :=
  CovR (sem w.Θ) w.K fρ ∧ ResUT.Lower fρ μ

theorem WInv.valid {w : TWd} {fρ : TRes w.K} {μ : BoCa.Loc → Option BoCa.Val}
    (h : WInv w fρ μ) : ResUT.Valid fρ := by
  obtain ⟨σ, hσ, -⟩ := h.2
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

/-- **The re-reading of a composite across a re-typing splits** into its parts' re-readings. -/
theorem RR.split_retype {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K') {a b y : TRes K}
    {y' : TRes K'} (hc : ResUT.CompS a b y) (hy : CovR (sem Θ) K y) (hag : AgreeOn Θ Θ' y)
    (hr : RR (sem Θ') y y') :
    ∃ a' b', RR (sem Θ') a a' ∧ RR (sem Θ') b b' ∧ ResUT.CompS a' b' y' := by
  obtain ⟨a', ha, -⟩ := RR.exists_retype hE (hy.of_compS_left hc) (hag.of_compS_left hc)
  obtain ⟨b', hb, -⟩ := RR.exists_retype hE (hy.of_compS_right hc) (hag.of_compS_right hc)
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

/-- **The world re-read at an extension carrying it**: covered, lowering to the same memory. -/
theorem WInv.reread {w w' : TWd} {fρ : TRes w.K} (hE : w.Ext w' fρ)
    {μ : BoCa.Loc → Option BoCa.Val} (h : WInv w fρ μ) :
    ∃ fρ' : TRes w'.K, RRw (w := w) (w' := w') fρ fρ' ∧ WInv w' fρ' μ := by
  obtain ⟨fρ', hr, hc⟩ := RR.exists_retype hE.1 h.1 hE.2
  exact ⟨fρ', hr, hc, h.2.rr hr⟩

/-- `#` along re-reading: the composite re-read is valid. -/
theorem ResUT.Hash.of_compS {K : WCactus} {a b y : TRes K} (hc : ResUT.CompS a b y)
    (hv : ResUT.Valid y) : ResUT.Hash a b :=
  ⟨hc.1, y, hc, hv⟩

end BoCa.Fig16.Tree

end
