import Restrat.Injection

/-!
# Restrat — the action of a re-stratification on the carrier

`e : Emb c` acts on every layer of Fig. 16's carrier:

* `ᾱ ↦ e(ᾱ)` on `℘⁺(Life)` (`LSet.map`);
* `relC e α : Cell_α → Cell_{e α}`, by the same well-founded recursion on the stratum index that
  builds `Cell` ([TR] p. 4 row 3): every lifetime is moved, every witness is moved, and a `mut`
  cell's stored invariant `P̂ : Val → SProp_β` is moved to its **image**
  `e·P̂ (v)(ρ′) ≜ ∃ρ. ρ′ = e·ρ ∧ P̂(v)(ρ)`;
* `relU e` on the union `Cell`, and `relRU e` on `Res`.

The precedent is `relRes` (`Support/TypedWorld/Images.lean`), which re-takes one cell's image at
one lifetime; here every lifetime of every cell, at every depth, moves at once.

Proved here: the action is injective, commutes with the stratum embeddings (`relC_toU`), and
carries `@ψ` to `e(@ψ)`, `ψ ∈ Cell_α` to `e·ψ ∈ Cell_{eα}` both ways, and `immOf`/`mutOf` to
`immOf`/`mutOf` at the moved data.
-/

noncomputable section

namespace Restrat
open BoCa.Fig16

namespace Emb
variable {c : Life} (e : Emb c)

/-! ### `℘⁺(Life)` -/

/-- `e(ᾱ)`. -/
def mapL (s : LSet) : LSet where
  mem y := ∃ x, s.mem x ∧ e x = y
  join := e s.join
  meet := e s.meet
  join_mem := ⟨_, s.join_mem, rfl⟩
  meet_mem := ⟨_, s.meet_mem, rfl⟩
  join_greatest := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.monotone (s.join_greatest x hx)
  meet_least := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.monotone (s.meet_least x hx)

theorem lset_ext {s t : LSet} (hm : ∀ x, s.mem x ↔ t.mem x) (hj : s.join = t.join)
    (hm' : s.meet = t.meet) : s = t := by
  obtain ⟨m, j, mt, _, _, _, _⟩ := s
  obtain ⟨m', j', mt', _, _, _, _⟩ := t
  simp only at hj hm' hm
  subst hj; subst hm'
  have : m = m' := funext fun x => propext (hm x)
  subst this; rfl

@[simp] theorem mapL_join (s : LSet) : (e.mapL s).join = e s.join := rfl
@[simp] theorem mapL_meet (s : LSet) : (e.mapL s).meet = e s.meet := rfl

theorem mapL_injective : Function.Injective e.mapL := by
  intro s t h
  refine lset_ext (fun x => ?_) (e.injective (congrArg LSet.join h))
    (e.injective (congrArg LSet.meet h))
  have hx : (e.mapL s).mem (e x) ↔ (e.mapL t).mem (e x) := by rw [h]
  constructor
  · intro hs
    obtain ⟨y, hy, hxy⟩ := hx.mp ⟨x, hs, rfl⟩
    rwa [← e.injective hxy]
  · intro ht
    obtain ⟨y, hy, hxy⟩ := hx.mpr ⟨x, ht, rfl⟩
    rwa [← e.injective hxy]

theorem mapL_union (s t : LSet) : e.mapL (s ∪ t) = e.mapL s ∪ e.mapL t := by
  refine lset_ext (fun y => ?_) (e.map_sup _ _) (e.map_inf _ _)
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩

theorem mapL_singleton (a : Life) : e.mapL (LSet.singleton a) = LSet.singleton (e a) := by
  refine lset_ext (fun y => ?_) rfl rfl
  constructor
  · rintro ⟨x, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨a, rfl, rfl⟩

/-! ### Cells, by well-founded recursion on the stratum -/

variable {Loc Val : Type}

omit e in
theorem pmap_map_injective {A B : Type} {f : A → B} (hf : Function.Injective f) :
    Function.Injective (PMap.map (Loc := Loc) f) := by
  intro p q h
  refine PMap.ext fun l => ?_
  have := congrArg (fun r => PMap.get r l) h
  simp only [PMap.map_get] at this
  exact Option.map_injective hf this

/-- One layer of the action, given the action on the strata above. -/
def layer (α : Life) (rec : ∀ β, α < β → Cell Loc Val β → Cell Loc Val (e β)) :
    CellF Loc Val α (fun β _ => Cell Loc Val β) →
      CellF Loc Val (e α) (fun β _ => Cell Loc Val β)
  | .own v => .own v
  | .imm i =>
      .imm ⟨e.mapL i.ls, e.lt_iff.mpr i.hls, i.v,
        i.ρ.map (rec i.ls.join (lt_of_lt_of_le i.hls i.ls.meet_le_join))⟩
  | .mut m =>
      .mut ⟨e m.β, e.lt_iff.mpr m.hβ, m.v, m.ρ.map (rec m.β m.hβ),
        fun v r => ∃ r₀, r₀.map (rec m.β m.hβ) = r ∧ m.P v r₀, ⟨m.ρ, rfl, m.hw⟩⟩

/-- `e·ψ` on `Cell_α`. -/
def relC : ∀ α : Life, Cell Loc Val α → Cell Loc Val (e α) :=
  WellFounded.fix (invImage OrderDual.ofDual Nat.lt_wfRel).wf
    (C := fun α => Cell Loc Val α → Cell Loc Val (e α))
    (fun α rec x => Cell.ofF (e.layer α (fun β h => rec β h) x.toF))

theorem relC_eq (α : Life) (x : Cell Loc Val α) :
    e.relC α x = Cell.ofF (e.layer α (fun β _ => e.relC β) x.toF) := by
  unfold relC
  rw [WellFounded.fix_eq]

/-- `e·ρ` on `Res_α`. -/
def relR (α : Life) (ρ : Res Loc Val α) : Res Loc Val (e α) := ρ.map (e.relC α)

/-- The stored invariant of a moved `mut` cell: the image. -/
def relP (β : Life) (P : Val → SProp Loc Val β) : Val → SProp Loc Val (e β) :=
  fun v r => ∃ r₀, e.relR β r₀ = r ∧ P v r₀

/-- `e·ψ` on the union `Cell`. -/
def relU : CellU Loc Val → CellU Loc Val
  | .own v => .own v
  | .imm i => .imm ⟨e.mapL i.ls, i.v, e.relR i.ls.join i.ρ⟩
  | .mut m => .mut ⟨e m.β, m.v, e.relR m.β m.ρ, e.relP m.β m.P, ⟨m.ρ, rfl, m.hw⟩⟩

/-- `e·ρ` on `Res`. -/
def relRU (ρ : ResU Loc Val) : ResU Loc Val := ρ.map e.relU

@[simp] theorem relRU_get (ρ : ResU Loc Val) (l : Loc) :
    (e.relRU ρ).get l = (ρ.get l).map e.relU := rfl

/-- The action commutes with `Cell_α ↪ Cell`. -/
theorem relC_toU (α : Life) (x : Cell Loc Val α) : (e.relC α x).toU = e.relU x.toU := by
  rw [e.relC_eq]
  unfold Cell.toU
  rw [Cell.toF_ofF]
  generalize x.toF = y
  cases y <;> rfl

theorem relR_toU (α : Life) (ρ : Res Loc Val α) : (e.relR α ρ).toU = e.relRU ρ.toU := by
  refine PMap.ext fun l => ?_
  show ((ρ.get l).map (e.relC α)).map Cell.toU = ((ρ.get l).map Cell.toU).map e.relU
  cases ρ.get l with
  | none => rfl
  | some x => exact congrArg some (e.relC_toU α x)

/-! ### Simple invariants -/

@[simp] theorem kind_relU (ψ : CellU Loc Val) : (e.relU ψ).kind = ψ.kind := by
  cases ψ <;> rfl

@[simp] theorem erase_relU (ψ : CellU Loc Val) : (e.relU ψ).erase = ψ.erase := by
  cases ψ <;> rfl

@[simp] theorem at_relU (ψ : CellU Loc Val) : (e.relU ψ).at = e ψ.at := by
  cases ψ with
  | own v => exact e.map_top.symm
  | imm i => rfl
  | «mut» m => rfl

theorem wit_relU (ψ : CellU Loc Val) : (e.relU ψ).wit = e.relRU ψ.wit := by
  cases ψ with
  | own v => exact PMap.ext fun l => rfl
  | imm i => exact e.relR_toU _ i.ρ
  | «mut» m => exact e.relR_toU _ m.ρ

@[simp] theorem relU_ownOf (v : Val) : e.relU (CellU.ownOf (Loc := Loc) v) = CellU.ownOf v := rfl

/-- `ψ ∈ Cell_α ↔ e·ψ ∈ Cell_{eα}`. -/
theorem inStratum_relU (α : Life) (ψ : CellU Loc Val) :
    (e.relU ψ).InStratum (e α) ↔ ψ.InStratum α := by
  cases ψ with
  | own v => exact Iff.rfl
  | imm i => exact e.lt_iff
  | «mut» m => exact e.lt_iff

theorem inStratum_relRU (α : Life) (ρ : ResU Loc Val) :
    (e.relRU ρ).InStratum (e α) ↔ ρ.InStratum α := by
  constructor
  · intro h l ψ hψ
    exact (e.inStratum_relU α ψ).mp (h l _ (by rw [relRU_get, hψ]; rfl))
  · intro h l ψ' hψ'
    rw [relRU_get] at hψ'
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp hψ'
    exact (e.inStratum_relU α ψ).mpr (h l ψ hψ)

/-! ### Injectivity -/

theorem relC_injective : ∀ (α : Life), Function.Injective (e.relC (Loc := Loc) (Val := Val) α) := by
  intro α
  induction α using (invImage OrderDual.ofDual Nat.lt_wfRel).wf.induction with
  | _ α ih =>
    intro x y hxy
    rw [e.relC_eq, e.relC_eq] at hxy
    have h := congrArg Cell.toF hxy
    rw [Cell.toF_ofF, Cell.toF_ofF] at h
    rw [← Cell.ofF_toF x, ← Cell.ofF_toF y]
    congr 1
    generalize x.toF = x' at h
    generalize y.toF = y' at h
    have hmap : ∀ β (hβ : α < β), Function.Injective
        (PMap.map (Loc := Loc) (e.relC (Loc := Loc) (Val := Val) β)) :=
      fun β hβ => pmap_map_injective (ih β hβ)
    cases x' with
    | own v =>
        cases y' with
        | own w => cases h; rfl
        | imm j => cases h
        | «mut» n => cases h
    | imm i =>
        cases y' with
        | own w => cases h
        | «mut» n => cases h
        | imm j =>
            obtain ⟨ls, hls, v, ρ⟩ := i
            obtain ⟨ls', hls', v', ρ'⟩ := j
            simp only [layer, CellF.imm.injEq] at h
            obtain ⟨hl, hv, hρ⟩ := ImmF.mk.inj h
            have hl' := e.mapL_injective hl
            subst hl'; subst hv
            have := hmap _ (lt_of_lt_of_le hls ls.meet_le_join) (eq_of_heq hρ)
            subst this; rfl
    | «mut» m =>
        cases y' with
        | own w => cases h
        | imm j => cases h
        | «mut» n =>
            obtain ⟨β, hβ, v, ρ, P, hw⟩ := m
            obtain ⟨β', hβ', v', ρ', P', hw'⟩ := n
            simp only [layer, CellF.mut.injEq] at h
            obtain ⟨hb, hv, hρ, hP⟩ := MutF.mk.inj h
            have hb' := e.injective hb
            subst hb'; subst hv
            have hρ' := hmap _ hβ (eq_of_heq hρ)
            subst hρ'
            have hP' := eq_of_heq hP
            have : P = P' := by
              funext u r
              apply propext
              have k : (∃ r₀, PMap.map (e.relC β) r₀ = PMap.map (e.relC β) r ∧ P u r₀) ↔
                  (∃ r₀, PMap.map (e.relC β) r₀ = PMap.map (e.relC β) r ∧ P' u r₀) :=
                Iff.of_eq (congrFun (congrFun hP' u) _)
              constructor
              · intro hr
                obtain ⟨r₀, h₀, hr₀⟩ := k.mp ⟨r, rfl, hr⟩
                rwa [← hmap _ hβ h₀]
              · intro hr
                obtain ⟨r₀, h₀, hr₀⟩ := k.mpr ⟨r, rfl, hr⟩
                rwa [← hmap _ hβ h₀]
            subst this; rfl

theorem relR_injective (α : Life) : Function.Injective (e.relR (Loc := Loc) (Val := Val) α) :=
  pmap_map_injective (e.relC_injective α)

theorem relU_injective : Function.Injective (e.relU (Loc := Loc) (Val := Val)) := by
  intro x y h
  cases x with
  | own v => cases y with
    | own w => cases h; rfl
    | imm j => cases h
    | «mut» n => cases h
  | imm i => cases y with
    | own w => cases h
    | «mut» n => cases h
    | imm j =>
        obtain ⟨ls, v, ρ⟩ := i
        obtain ⟨ls', v', ρ'⟩ := j
        simp only [relU, CellU.imm.injEq] at h
        obtain ⟨hl, hv, hρ⟩ := ImmU.mk.inj h
        have hl' := e.mapL_injective hl
        subst hl'; subst hv
        have := e.relR_injective _ (eq_of_heq hρ)
        subst this; rfl
  | «mut» m => cases y with
    | own w => cases h
    | imm j => cases h
    | «mut» n =>
        obtain ⟨β, v, ρ, P, hw⟩ := m
        obtain ⟨β', v', ρ', P', hw'⟩ := n
        simp only [relU, CellU.mut.injEq] at h
        obtain ⟨hb, hv, hρ, hP⟩ := MutU.mk.inj h
        have hb' := e.injective hb
        subst hb'; subst hv
        have hρ' := e.relR_injective _ (eq_of_heq hρ)
        subst hρ'
        have hP' := eq_of_heq hP
        have : P = P' := by
          funext u r
          apply propext
          have k : e.relP β P u (e.relR β r) ↔ e.relP β P' u (e.relR β r) :=
            Iff.of_eq (congrFun (congrFun hP' u) (e.relR β r))
          constructor
          · intro hr
            obtain ⟨r₀, h₀, hr₀⟩ := k.mp ⟨r, rfl, hr⟩
            rwa [← e.relR_injective β h₀]
          · intro hr
            obtain ⟨r₀, h₀, hr₀⟩ := k.mpr ⟨r, rfl, hr⟩
            rwa [← e.relR_injective β h₀]
        subst this; rfl

theorem relRU_injective : Function.Injective (e.relRU (Loc := Loc) (Val := Val)) :=
  pmap_map_injective e.relU_injective

end Emb

end Restrat
