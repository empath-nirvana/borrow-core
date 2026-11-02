import Support.Model.Tree.CarrierSim
import Support.Model.Tree.CarrierGraftEx

/-!
# Semantic types read at the lifetime tree, and `mut` cells re-read as the tree grows

The tree-stratified carrier (`Tree/Carrier.lean`) is indexed by the cactus `K` its strata are
read in. Grafting a stored task under a newer lend extends `K` to `K'` (`WCactus.Ext`), and
`trU` carries a world across (`ResUT.Valid.graft`). `trU` keeps each `mut` cell's stored
predicate as an image, extended by falsity outside it as row 5.57 extends `SProp_α ⊆ SProp_α'`,
so a borrow newly admissible at `K'` never satisfies it (`graft_carried_refuses`).

Here the lifetime tree is part of the world semantic types are read at, and a `mut` cell's
invariant is its type's interpretation at the current tree.

* **Kripke semantic types.** `KSem`: a predicate on values and resources at every cactus.
* **Location typing.** `Θ : LocTy` gives each `mut` cell's location the semantic type of its
  contents, as a step-indexed store typing does (Ahmed's). A
  world is covered at `K` (`CovR`) when every `mut` cell in it, at any depth, stores `Θ ℓ` read
  at `K` on its stratum.
* **Re-reading.** `RC`/`RR`: the world at `K'` that keeps every location, tag, value and lifetime
  name (a `mut` cell's antichain `β̄` becomes `min_{K'} β̄`, as under `trU`) and stores at each
  `mut` cell `Θ ℓ` read at `K'`. It is single-valued (`RR.func`), the identity when the tree does
  not grow (`RR.refl`; at the printed chain nothing grows), and composes along extensions
  (`RR.trans`).
* **Monotonicity** (`KMono`): a value in `τ` at `K` is in `τ` at `K'`, carried by the re-reading.
  Proved for `1`, `+`, `Imm @a τ` (`vImm`), `Mut @a τ` (`vMut`), `ref τ` (`vRef`), `[a] τ`
  (`vBox`), and a thunk (`vThunk`), each from its components'.
* **Existence and `✓`** (`reread`): when every type `Θ` assigns is monotone, a covered world at
  `K` has a re-reading at `K'`; it is covered at `K'`, it keeps every stratum, and it is valid
  when the world is (`ResUT.Valid.sim`, the walks carried along `RR`).

**Against row 5.57.** The re-read invariant is not an extension by falsity: it is the type read
at `K'`, which holds wherever the old invariant held (on re-read resources, `reread_extends`) and
also at resources only `K'` admits. Cells whose location `Θ` does not type are not re-read; they
are not covered, and `reread` asks for coverage.

**Against the stratum condition `ρ_P ∈ Res_A`.** A re-read cell's payload lies in the stratum
`Res_{min β̄}` read at `K'` (`RC.inStratum`): every stratum of `K` sits inside the same-named
stratum of `K'`, so `ρ_P ∈ Res_A` at `K` gives it at `K'`.

**Not modelled:** the records list (`ls`), `Coh`, and `Ext` of Core's `vCT`, which the tree carrier
does not carry; and growth of `Θ` (allocation), which this file holds fixed.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-- A resource of the tree-stratified carrier at the program's locations and values. -/
abbrev TRes (K : WCactus) : Type := ResUT BoCa.Loc BoCa.Val K
/-- A cell. -/
abbrev TCell (K : WCactus) : Type := CellUT BoCa.Loc BoCa.Val K
/-- An `imm` payload. -/
abbrev TImm (K : WCactus) : Type := ImmT BoCa.Loc BoCa.Val K
/-- A `mut` payload. -/
abbrev TMut (K : WCactus) : Type := MutT BoCa.Loc BoCa.Val K

/-- **A semantic type read at every lifetime tree.** -/
structure KSem where
  /-- `𝒱⟦τ⟧` read at `K`. -/
  P : (K : WCactus) → BoCa.Val → TRes K → Prop

/-- A location typing: the semantic type of each `mut` cell's contents. -/
abbrev LocTy : Type := BoCa.Loc → Option KSem

/-! ### Order facts -/

theorem WCactus.Ext.refl (K : WCactus) : K.Ext K := fun h => h

theorem WCactus.Ext.trans {K K' K'' : WCactus} (h₁ : K.Ext K') (h₂ : K'.Ext K'') : K.Ext K'' :=
  fun h => h₂ (h₁ h)

theorem WCactus.Ext.le {K K' : WCactus} (hE : K.Ext K') {a b : Life} (h : K.le a b) :
    K'.le a b := by
  by_cases e : a = b
  · subst e; exact K'.refl a
  · exact (hE ⟨h, e⟩).1

/-- `min_{K''}(min_{K'} β̄) = min_{K''} β̄` when `K''` keeps `K'`'s nestings. -/
theorem WCactus.minS_minS {K' K'' : WCactus} (hE : K'.Ext K'') (s : TSet) :
    K''.minS (K'.minS s) = K''.minS s := by
  refine TSet.ext (Finset.ext fun x => ?_)
  rw [K''.mem_minS, K''.mem_minS]
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨K'.minS_sub hx, fun y hy hyx => ?_⟩
    obtain ⟨z, hz, hzy⟩ := K'.exists_minS_le hy
    exact hmin z hz (Cactus.lt_of_le_of_lt (hE.le hzy) hyx)
  · rintro ⟨hx, hmin⟩
    exact ⟨(K'.mem_minS).mpr ⟨hx, fun y hy hyx => hmin y hy (hE hyx)⟩,
      fun y hy => hmin y (K'.minS_sub hy)⟩

/-! ### Payload equalities -/

theorem ImmT.eq_of {K : WCactus} {i j : TImm K} (hs : i.ls = j.ls) (hv : i.v = j.v)
    (hr : i.res = j.res) : i = j := by
  obtain ⟨s, v, ρ⟩ := i
  obtain ⟨s', v', ρ'⟩ := j
  simp only at hs hv
  subst hs; subst hv
  have : ρ = ρ' := ResT.toU_injective hr
  subst this; rfl

theorem MutT.eq_of {K : WCactus} {m n : TMut K} (F : BoCa.Val → TRes K → Prop)
    (hs : m.ls = n.ls) (hv : m.v = n.v) (hr : m.res = n.res)
    (hm : ∀ w r, m.P w r ↔ F w r.toU) (hn : ∀ w r, n.P w r ↔ F w r.toU) : m = n := by
  obtain ⟨s, a, v, ρ, P, w⟩ := m
  obtain ⟨s', a', v', ρ', P', w'⟩ := n
  simp only at hs hv
  subst hs; subst hv
  have : ρ = ρ' := ResT.toU_injective hr
  subst this
  have : P = P' := funext fun w => funext fun r => propext ((hm w r).trans (hn w r).symm)
  subst this; rfl

/-! ### Coverage and re-reading -/

variable (Θ : LocTy)

/-- **A covered cell at `K`**: every `mut` cell in it, at any depth, stores `Θ ℓ` read at `K`. -/
inductive Cov (K : WCactus) : BoCa.Loc → TCell K → Prop where
  | own (l : BoCa.Loc) (v : BoCa.Val) : Cov K l (.own v)
  | imm (l : BoCa.Loc) (i : TImm K) (hw : ∀ m ψ, i.res.get m = some ψ → Cov K m ψ) :
      Cov K l (.imm i)
  | mut (l : BoCa.Loc) (m : TMut K) (τ : KSem) (hΘ : Θ l = some τ)
      (hP : ∀ w r, m.P w r ↔ τ.P K w r.toU)
      (hw : ∀ k ψ, m.res.get k = some ψ → Cov K k ψ) : Cov K l (.mut m)

/-- A covered world. -/
def CovR (K : WCactus) (ρ : TRes K) : Prop := ∀ l ψ, ρ.get l = some ψ → Cov Θ K l ψ

/-- **The re-reading of a cell** at `K'`: location, tag, value and lifetime names kept, a `mut`
cell's antichain read as `min_{K'}`, its invariant `Θ ℓ` read at `K'`. -/
inductive RC {K K' : WCactus} : BoCa.Loc → TCell K → TCell K' → Prop where
  | own (l : BoCa.Loc) (v : BoCa.Val) : RC l (.own v) (.own v)
  | imm (l : BoCa.Loc) (i : TImm K) (i' : TImm K') (hs : i'.ls = i.ls) (hv : i'.v = i.v)
      (hdom : ∀ m, i.res.get m = none ↔ i'.res.get m = none)
      (hw : ∀ m ψ ψ', i.res.get m = some ψ → i'.res.get m = some ψ' → RC m ψ ψ') :
      RC l (.imm i) (.imm i')
  | mut (l : BoCa.Loc) (m : TMut K) (m' : TMut K') (τ : KSem) (hΘ : Θ l = some τ)
      (hs : m'.ls = K'.minS m.ls) (hv : m'.v = m.v)
      (hdom : ∀ k, m.res.get k = none ↔ m'.res.get k = none)
      (hw : ∀ k ψ ψ', m.res.get k = some ψ → m'.res.get k = some ψ' → RC k ψ ψ')
      (hP : ∀ w r, m'.P w r ↔ τ.P K' w r.toU) :
      RC l (.mut m) (.mut m')

/-- **The re-reading of a world.** -/
def RR {K K' : WCactus} (ρ : TRes K) (ρ' : TRes K') : Prop :=
  (∀ m, ρ.get m = none ↔ ρ'.get m = none) ∧
    ∀ m ψ ψ', ρ.get m = some ψ → ρ'.get m = some ψ' → RC Θ m ψ ψ'

variable {Θ}

theorem RR.get_some {K K' : WCactus} {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ') {m : BoCa.Loc}
    {ψ : TCell K} (e : ρ.get m = some ψ) : ∃ ψ', ρ'.get m = some ψ' ∧ RC Θ m ψ ψ' := by
  cases e' : ρ'.get m with
  | none => rw [← (h.1 m)] at e'; rw [e] at e'; cases e'
  | some ψ' => exact ⟨ψ', rfl, h.2 m ψ ψ' e e'⟩

theorem RR.get_some' {K K' : WCactus} {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ') {m : BoCa.Loc}
    {ψ' : TCell K'} (e : ρ'.get m = some ψ') : ∃ ψ, ρ.get m = some ψ ∧ RC Θ m ψ ψ' := by
  cases e' : ρ.get m with
  | none => rw [h.1 m] at e'; rw [e] at e'; cases e'
  | some ψ => exact ⟨ψ, rfl, h.2 m ψ ψ' e' e⟩

theorem RR.empty {K K' : WCactus} :
    RR Θ (PMap.empty : TRes K) (PMap.empty : TRes K') :=
  ⟨fun _ => by simp, fun _ _ _ e => by simp at e⟩

theorem RR.of_empty {K K' : WCactus} {ρ' : TRes K'} (h : RR Θ (PMap.empty : TRes K) ρ') :
    ρ' = PMap.empty :=
  PMap.ext fun m => by simpa using ((h.1 m).mp rfl)

/-- The witnesses of a re-read cell are re-read. -/
theorem RC.wit {K K' : WCactus} {l : BoCa.Loc} {ψ : TCell K} {ψ' : TCell K'}
    (h : RC Θ l ψ ψ') : RR Θ ψ.wit ψ'.wit := by
  cases h with
  | own => exact RR.empty
  | imm _ _ _ _ _ hdom hw => exact ⟨hdom, hw⟩
  | «mut» _ _ _ _ _ _ _ hdom hw _ => exact ⟨hdom, hw⟩

theorem RC.kind {K K' : WCactus} {l : BoCa.Loc} {ψ : TCell K} {ψ' : TCell K'}
    (h : RC Θ l ψ ψ') : ψ'.kind = ψ.kind := by
  cases h <;> rfl

theorem RC.erase {K K' : WCactus} {l : BoCa.Loc} {ψ : TCell K} {ψ' : TCell K'}
    (h : RC Θ l ψ ψ') : ψ'.erase = ψ.erase := by
  cases h with
  | own => rfl
  | imm _ _ _ _ hv => exact hv
  | «mut» _ _ _ _ _ _ hv => exact hv

/-- **Re-reading is single-valued.** -/
theorem RC.func {K K' : WCactus} {l : BoCa.Loc} {ψ : TCell K} {a : TCell K'}
    (h : RC Θ l ψ a) : ∀ {b : TCell K'}, RC Θ l ψ b → a = b := by
  induction h with
  | own l v => intro b hb; cases hb; rfl
  | imm l i i' hs hv hdom hw ih =>
      intro b hb
      cases hb with
      | imm _ _ j hs' hv' hdom' hw' =>
          refine congrArg CellUT.imm (ImmT.eq_of (hs.trans hs'.symm) (hv.trans hv'.symm) ?_)
          refine PMap.ext fun k => ?_
          cases e : i.res.get k with
          | none => rw [(hdom k).mp e, (hdom' k).mp e]
          | some ψ =>
              cases e₁ : i'.res.get k with
              | none => rw [← hdom k, e] at e₁; cases e₁
              | some a =>
                  cases e₂ : j.res.get k with
                  | none => rw [← hdom' k, e] at e₂; cases e₂
                  | some b' => rw [ih k ψ a e e₁ (hw' k ψ b' e e₂)]
  | «mut» l m m' τ hΘ hs hv hdom hw hP ih =>
      intro b hb
      cases hb with
      | «mut» _ _ n τ' hΘ' hs' hv' hdom' hw' hP' =>
          rw [hΘ] at hΘ'
          cases Option.some.inj hΘ'
          refine congrArg CellUT.mut (MutT.eq_of (τ.P K') (hs.trans hs'.symm)
            (hv.trans hv'.symm) ?_ hP hP')
          refine PMap.ext fun k => ?_
          cases e : m.res.get k with
          | none => rw [(hdom k).mp e, (hdom' k).mp e]
          | some ψ =>
              cases e₁ : m'.res.get k with
              | none => rw [← hdom k, e] at e₁; cases e₁
              | some a =>
                  cases e₂ : n.res.get k with
                  | none => rw [← hdom' k, e] at e₂; cases e₂
                  | some b' => rw [ih k ψ a e e₁ (hw' k ψ b' e e₂)]

theorem RR.func {K K' : WCactus} {ρ : TRes K} {a b : TRes K'} (ha : RR Θ ρ a)
    (hb : RR Θ ρ b) : a = b := by
  refine PMap.ext fun k => ?_
  cases e : ρ.get k with
  | none => rw [(ha.1 k).mp e, (hb.1 k).mp e]
  | some ψ =>
      obtain ⟨x, ex, hx⟩ := ha.get_some e
      obtain ⟨y, ey, hy⟩ := hb.get_some e
      rw [ex, ey, hx.func hy]

/-- **Re-reading at the same tree is the identity** on covered cells. -/
theorem Cov.rc_refl {K : WCactus} {l : BoCa.Loc} {ψ : TCell K} (h : Cov Θ K l ψ) :
    RC Θ (K' := K) l ψ ψ := by
  induction h with
  | own l v => exact .own l v
  | imm l i _ ih =>
      exact .imm l i i rfl rfl (fun _ => Iff.rfl) fun k ψ ψ' e e' => by
        rw [e] at e'; cases Option.some.inj e'; exact ih k ψ e
  | «mut» l m τ hΘ hP _ ih =>
      exact .mut l m m τ hΘ (K.minS_of_anti m.anti).symm rfl (fun _ => Iff.rfl)
        (fun k ψ ψ' e e' => by rw [e] at e'; cases Option.some.inj e'; exact ih k ψ e) hP

theorem RR.refl {K : WCactus} {ρ : TRes K} (h : CovR Θ K ρ) : RR Θ (K' := K) ρ ρ :=
  ⟨fun _ => Iff.rfl, fun m ψ ψ' e e' => by
    rw [e] at e'; cases Option.some.inj e'; exact (h m ψ e).rc_refl⟩

/-- **A re-read cell is covered at the new tree.** -/
theorem RC.cov {K K' : WCactus} {l : BoCa.Loc} {ψ : TCell K} {ψ' : TCell K'}
    (h : RC Θ l ψ ψ') : Cov Θ K' l ψ' := by
  induction h with
  | own l v => exact .own l v
  | imm l i i' _ _ hdom hw ih =>
      refine .imm l i' fun k ψ' e' => ?_
      obtain ⟨ψ, e, hr⟩ := RR.get_some' (Θ := Θ) ⟨hdom, hw⟩ e'
      exact ih k ψ ψ' e e'
  | «mut» l m m' τ hΘ _ _ hdom hw hP ih =>
      refine .mut l m' τ hΘ hP fun k ψ' e' => ?_
      obtain ⟨ψ, e, hr⟩ := RR.get_some' (Θ := Θ) ⟨hdom, hw⟩ e'
      exact ih k ψ ψ' e e'

theorem RR.cov {K K' : WCactus} {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ') : CovR Θ K' ρ' :=
  fun _ _ e' => by obtain ⟨ψ, e, hr⟩ := h.get_some' e'; exact hr.cov

/-- **Re-readings compose** along extensions. -/
theorem RC.trans {K K' K'' : WCactus} (hE' : K'.Ext K'') {l : BoCa.Loc} {ψ : TCell K}
    {ψ' : TCell K'} (h : RC Θ l ψ ψ') : ∀ {ψ'' : TCell K''}, RC Θ l ψ' ψ'' → RC Θ l ψ ψ'' := by
  induction h with
  | own l v => intro ψ'' h'; cases h'; exact .own l v
  | imm l i i' hs hv hdom hw ih =>
      intro ψ'' h'
      cases h' with
      | imm _ _ i'' hs' hv' hdom' hw' =>
          refine .imm l i i'' (hs'.trans hs) (hv'.trans hv) (fun k => (hdom k).trans (hdom' k))
            fun k ψ ψ'' e e'' => ?_
          obtain ⟨ψ', e', hr⟩ := RR.get_some (Θ := Θ) ⟨hdom, hw⟩ e
          exact ih k ψ ψ' e e' (hw' k ψ' ψ'' e' e'')
  | «mut» l m m' τ hΘ hs hv hdom hw hP ih =>
      intro ψ'' h'
      cases h' with
      | «mut» _ _ m'' τ' hΘ' hs' hv' hdom' hw' hP' =>
          rw [hΘ] at hΘ'
          cases Option.some.inj hΘ'
          refine .mut l m m'' τ hΘ (by rw [hs', hs, WCactus.minS_minS hE']) (hv'.trans hv)
            (fun k => (hdom k).trans (hdom' k)) (fun k ψ ψ'' e e'' => ?_) hP'
          obtain ⟨ψ', e', hr⟩ := RR.get_some (Θ := Θ) ⟨hdom, hw⟩ e
          exact ih k ψ ψ' e e' (hw' k ψ' ψ'' e' e'')

theorem RR.trans {K K' K'' : WCactus} (hE' : K'.Ext K'') {ρ : TRes K} {ρ' : TRes K'}
    {ρ'' : TRes K''} (h : RR Θ ρ ρ') (h' : RR Θ ρ' ρ'') : RR Θ ρ ρ'' := by
  refine ⟨fun k => (h.1 k).trans (h'.1 k), fun k ψ ψ'' e e'' => ?_⟩
  obtain ⟨ψ', e', hr⟩ := h.get_some e
  exact hr.trans hE' (h'.2 k ψ' ψ'' e' e'')

/-- **Strata are kept**: a re-read cell lies in every stratum of `K'` the cell lay in at `K`. -/
theorem RC.inStratum {K K' : WCactus} (hE : K.Ext K') {l : BoCa.Loc} {ψ : TCell K}
    {ψ' : TCell K'} (h : RC Θ l ψ ψ') {S : TSet} (hS : ψ.InStratum S) : ψ'.InStratum S := by
  cases h with
  | own => exact trivial
  | imm _ i i' hs =>
      show K'.Above S i'.ls
      rw [hs]; exact hE.above hS
  | «mut» _ m m' _ _ hs =>
      show K'.Above S m'.ls
      rw [hs]; exact (K'.above_minS_iff).mpr (hE.above hS)

theorem RR.inStratum {K K' : WCactus} (hE : K.Ext K') {ρ : TRes K} {ρ' : TRes K'}
    (h : RR Θ ρ ρ') {S : TSet} (hS : ρ.InStratum S) : ρ'.InStratum S :=
  fun _ _ e' => by
    obtain ⟨ψ, e, hr⟩ := h.get_some' e'
    exact hr.inStratum hE (hS _ ψ e)

/-- `RR` as a relation `✓` is carried along. -/
def rrRel (Θ : LocTy) (K K' : WCactus) : WitRel BoCa.Loc BoCa.Val K K' where
  W := RR Θ
  func := RR.func
  pt := fun {a b} h l => by
    cases e : a.get l with
    | none => rw [(h.1 l).mp e]; exact Option.Rel.none
    | some ψ =>
        obtain ⟨ψ', e', hr⟩ := h.get_some e
        rw [e']
        exact Option.Rel.some ⟨hr.kind, hr.erase, hr.wit⟩

theorem RR.rsim {K K' : WCactus} {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ') :
    (rrRel Θ K K').RSim ρ' ρ :=
  (rrRel Θ K K').rsim_of_W h

/-! ### Monotonicity -/

/-- **`τ` is monotone along tree extension**, carried by the re-reading. -/
def KMono (Θ : LocTy) (τ : KSem) : Prop :=
  ∀ (K K' : WCactus), K.Ext K' → ∀ (v : BoCa.Val) (ρ : TRes K) (ρ' : TRes K'),
    CovR Θ K ρ → RR Θ ρ ρ' → τ.P K v ρ → τ.P K' v ρ'

/-- Every type the location typing assigns is monotone. -/
def MonoΘ (Θ : LocTy) : Prop := ∀ l τ, Θ l = some τ → KMono Θ τ

/-! ### Existence of the re-reading -/

/-- A world whose cells each have a re-reading has one. -/
theorem RR.exists_of {K K' : WCactus} {ρ : TRes K}
    (hc : ∀ l ψ, ρ.get l = some ψ → ∃ ψ' : TCell K', RC Θ l ψ ψ') :
    ∃ ρ' : TRes K', RR Θ ρ ρ' := by
  classical
  let f : BoCa.Loc → Option (TCell K') := fun l =>
    if h : ∃ ψ, ρ.get l = some ψ then some (Classical.choose (hc l _ (Classical.choose_spec h)))
    else none
  have hf : ∀ l, ρ.get l = none ↔ f l = none := by
    intro l
    by_cases h : ∃ ψ, ρ.get l = some ψ
    · obtain ⟨ψ, e⟩ := h
      have hf' : f l ≠ none := by
        simp only [f, dif_pos (⟨ψ, e⟩ : ∃ ψ, ρ.get l = some ψ)]; exact Option.some_ne_none _
      rw [e]; exact ⟨fun h => absurd h (Option.some_ne_none _), fun h => absurd h hf'⟩
    · have hf' : f l = none := by simp only [f, dif_neg h]
      refine ⟨fun _ => hf', fun _ => ?_⟩
      cases e : ρ.get l with
      | none => rfl
      | some ψ => exact absurd ⟨ψ, e⟩ h
  have fin : FinDom f := by
    obtain ⟨d, hd⟩ := ρ.finite
    exact ⟨d, fun l hl => hd l fun e => hl ((hf l).mp e)⟩
  refine ⟨⟨f, fin⟩, hf, fun l ψ ψ' e e' => ?_⟩
  have h : ∃ ψ, ρ.get l = some ψ := ⟨ψ, e⟩
  change f l = some ψ' at e'
  simp only [f, dif_pos h] at e'
  cases Option.some.inj e'
  have hs := Classical.choose_spec (hc l _ (Classical.choose_spec h))
  have : Classical.choose h = ψ := Option.some.inj ((Classical.choose_spec h).symm.trans e)
  subst this
  exact hs

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

open Classical in
/-- `ρ[ℓ ↦ x]`. -/
def PMap.ins {X : Type} (ρ : PMap BoCa.Loc X) (l : BoCa.Loc) (x : X) : PMap BoCa.Loc X where
  get m := if m = l then some x else ρ.get m
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨l :: d, fun m hm => ?_⟩
    by_cases e : m = l
    · exact e ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hd m (by simpa [e] using hm))

open Classical in
/-- `ρ` without `ℓ`. -/
def PMap.del {X : Type} (ρ : PMap BoCa.Loc X) (l : BoCa.Loc) : PMap BoCa.Loc X where
  get m := if m = l then none else ρ.get m
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun m hm => hd m ?_⟩
    by_cases e : m = l
    · simp [e] at hm
    · simpa [e] using hm

open Classical in
theorem PMap.ins_get {X : Type} (ρ : PMap BoCa.Loc X) (l : BoCa.Loc) (x : X) (m : BoCa.Loc) :
    (PMap.ins ρ l x).get m = if m = l then some x else ρ.get m := rfl

open Classical in
theorem PMap.del_get {X : Type} (ρ : PMap BoCa.Loc X) (l : BoCa.Loc) (m : BoCa.Loc) :
    (PMap.del ρ l).get m = if m = l then none else ρ.get m := rfl

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

/-- The re-reading of `ℓ ↦ ψ` is `ℓ ↦ ψ'` for the cell's re-reading `ψ'`. -/
theorem RR.of_sng {K K' : WCactus} {l : BoCa.Loc} {ψ : TCell K} {ρ' : TRes K'}
    (h : RR Θ (PMap.sng l ψ) ρ') : ∃ ψ', ρ' = PMap.sng l ψ' ∧ RC Θ l ψ ψ' := by
  classical
  obtain ⟨ψ', e', hr⟩ := h.get_some (m := l) (ψ := ψ) (by simp [PMap.sng_get])
  refine ⟨ψ', PMap.ext fun m => ?_, hr⟩
  rw [PMap.sng_get]
  by_cases e : m = l
  · subst e; rw [if_pos rfl, e']
  · rw [if_neg e]; exact (h.1 m).mp (by simp [PMap.sng_get, e])

theorem CovR.sng {K : WCactus} {l : BoCa.Loc} {ψ : TCell K} (h : CovR Θ K (PMap.sng l ψ)) :
    Cov Θ K l ψ :=
  h l ψ (by simp [PMap.sng_get])

/-! ### The interpretations -/

/-- `𝒱⟦1⟧`. -/
def vUnit : KSem where
  P _ v ρ := v = BoCa.Val.unit ∧ ρ = PMap.empty

/-- `𝒱⟦A + B⟧`. -/
def vSum (τ₁ τ₂ : KSem) : KSem where
  P K v ρ := (∃ v₁, v = BoCa.Val.inj₁ v₁ ∧ τ₁.P K v₁ ρ) ∨ (∃ v₂, v = BoCa.Val.inj₂ v₂ ∧ τ₂.P K v₂ ρ)

/-- `𝒱⟦Imm @a τ⟧` at `δ(a) = a`: a view `ℓ ↦ imm(β̄, w, χ)` with `a ⊑ x` at every member `x` of
`β̄` read in `K`, and the payload in `τ` (`ptoImmT`'s shape, without the records list). -/
def vImm (a : Life) (τ : KSem) : KSem where
  P K v ρ := ∃ (l : BoCa.Loc) (i : TImm K), v = BoCa.Val.loc l ∧ ρ = PMap.sng l (.imm i) ∧
    (∀ x ∈ i.ls.set, K.le a x) ∧ τ.P K i.v i.res

/-- `𝒱⟦Mut @a τ⟧` at `δ(a) = a`: a cell `ℓ ↦ mut(β̄, w, χ, P̂)` with `a ⊑ x` at every member of
`β̄` read in `K`, whose location the location typing gives `τ`, and whose invariant is `τ` **read
at `K`** (`ptoMutT`'s shape, without the records list). -/
def vMut (Θ : LocTy) (a : Life) (τ : KSem) : KSem where
  P K v ρ := ∃ (l : BoCa.Loc) (m : TMut K), v = BoCa.Val.loc l ∧ ρ = PMap.sng l (.mut m) ∧
    Θ l = some τ ∧ (∀ x ∈ m.ls.set, K.le a x) ∧ ∀ w r, m.P w r ↔ τ.P K w r.toU

/-- `𝒱⟦ref τ⟧`: `ℓ ↦ own(w)` beside a resource of the payload. -/
def vRef (τ : KSem) : KSem where
  P K v ρ := ∃ (l : BoCa.Loc) (w : BoCa.Val) (ρ₁ : TRes K), v = BoCa.Val.loc l ∧
    ρ₁.get l = none ∧ ρ = PMap.ins ρ₁ l (.own w) ∧ τ.P K w ρ₁

/-- `𝒱⟦[a] τ⟧` (row 5.32's box): `τ` with every borrow cell strictly longer-lived than `a`. -/
def vBox (a : Life) (τ : KSem) : KSem where
  P K v ρ := τ.P K v ρ ∧ ρ.InStratum (TSet.single a)

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

/-- `Mut @a τ` is monotone whatever `τ` is: the re-reading stores `Θ ℓ = τ` read at `K'`. -/
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

/-- A thunk is monotone for every computation predicate: re-readings compose. -/
theorem kmono_thunk {C : (K : WCactus) → BoCa.Val → TRes K → Prop} : KMono Θ (vThunk Θ C) := by
  intro K K' hE v ρ ρ' _ hr h K'' hE' ρ'' hr'
  exact h K'' (hE.trans hE') ρ'' (hr.trans hE' hr')

end BoCa.Fig16.Tree

end
