import Paper.S5_Model.Definitions

/-!
# Nominal — the cell model over a partial order of lifetimes

`Paper/S5_Model` builds `Cell_α ≜ own(Val) + imm(Imm_α) + mut(Mut_α)` by well-founded recursion
on `Life = ℕᵒᵈ`, a chain. Here the lifetimes are any partial order `L` with a top `⊤` (static)
and no infinite strictly ascending chain (`WellFoundedGT L`); `α < β` reads "`β` strictly
outlives `α`". The free order of atoms with parents (`Atoms.lean`) is one such `L`.

**Strata are indexed by finite sets of lifetimes.** `Res_T` is the resources whose cells strictly
outlive every member of `T`. Core's `Res_α` is `Res_{α}`; Core's `imm` witness lies in
`Res_{⊔ᾱ}`, the stratum of the longest member of `ᾱ`, which in a chain is "strictly outlives
every member of `ᾱ`" — in a partial order the longest member need not exist, and `Res_ᾱ` is that
condition read as a set.

    Cell_S ≜ own(Val) + imm(Imm_S) + mut(Mut_S)
    Imm_S  ≜ {(ᾱ, v, ρ : Res_ᾱ) ∣ ᾱ ≠ ∅, every member of ᾱ strictly outlives every member of S}
    Mut_S  ≜ {(β, v, ρ : Res_{β}, P̂ : Val → SProp_{β}) ∣ β strictly outlives every member of S,
              P̂(v)(ρ)}

`Above T S` is "`T` nonempty and every member of `T` strictly outlives every member of `S`"; it
is well-founded because `L` has no infinite ascending chain (`above_wf`), so the recursion is
`WellFounded.fix` on it, as `Paper/S5_Model`'s is on `ℕᵒᵈ`. `Cell_eq` is the cell equation,
`isCarrier` its solution. Conversely an infinite ascending chain leaves no solution: the strata
along it would have strictly descending cardinals (`no_carrier_of_strictMono`, `DenseCarrier`'s
Cantor argument with set-indexed strata), so `carrier_iff`: a partial order carries the cells
exactly when it has no infinite ascending chain. Unlike a chain carrying them, it need not be
rigid (`Atoms.lean`'s swaps).

The union `CellU ≜ ⋃_S Cell_S` (`ImmU`, `MutU`), stratum membership `CellU.InStratum`, and the
passage between `Res_S` and `{ρ ∈ Res ∣ ρ ∈ Res_S}` are `Paper/S5_Model`'s, with set-indexed
strata. A cell is determined by its data: tag, value, lifetimes, witness and stored predicate
read on the union (`CellU.ext_data`); `immOf`/`mutOf` build a cell from that data.

**`[α]P` splits in two** in a partial order (`CellU.InStratum`, `CellU.Survives`):

* (a) *every cell strictly outlives `α`*: `ρ ∈ Res_{α}`, the stratum. A `mut` cell's witness and
  the `M Frame` side condition (`[TR]` 6.65's payload in `Res_β`) are this.
* (b) *no cell is at or beneath `α`*: `ρ` survives the end of `α`. Ending a borrow (`[TR]` 6.64's
  postcondition, the relation's `[@a] T`) is this.

On cells whose lifetimes are comparable with `α` they agree (`survives_iff_inStratum`); a cell
at a lifetime incomparable with `α` survives `α` and is not in `Res_{α}` (`Witnesses.lean`'s
`split_is_real`).
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap)

section Strata
variable {L : Type} [PartialOrder L]

/-- `T` above `S`: `T` is nonempty and every member of `T` strictly outlives every member of
`S`. -/
def Above (T S : Finset L) : Prop := T.Nonempty ∧ ∀ t ∈ T, ∀ s ∈ S, s < t

/-- **The strata are well-founded**: no infinite ascending chain of lifetimes, no infinite
descending sequence of strata. -/
theorem above_wf [WellFoundedGT L] : WellFounded (Above (L := L)) := by
  have key : ∀ x : L, ∀ S : Finset L, x ∈ S → Acc Above S := by
    intro x
    induction x using WellFoundedGT.induction with
    | _ x ih =>
      intro S hx
      refine Acc.intro S (fun T hT => ?_)
      obtain ⟨t, ht⟩ := hT.1
      exact ih t (hT.2 t ht x hx) T ht
  refine ⟨fun S => Acc.intro S (fun T hT => ?_)⟩
  obtain ⟨t, ht⟩ := hT.1
  exact key t T ht

theorem above_singleton_iff {b : L} {S : Finset L} : Above {b} S ↔ ∀ s ∈ S, s < b := by
  constructor
  · intro h s hs
    exact h.2 b (Finset.mem_singleton_self b) s hs
  · intro h
    refine ⟨Finset.singleton_nonempty b, fun t ht s hs => ?_⟩
    rw [Finset.mem_singleton.mp ht]
    exact h s hs

theorem above_singleton_singleton {a b : L} : Above {b} {a} ↔ a < b := by
  rw [above_singleton_iff]
  exact ⟨fun h => h a (Finset.mem_singleton_self a),
    fun h s hs => (Finset.mem_singleton.mp hs) ▸ h⟩

/-- A stratum above `S` is above every smaller index. -/
theorem Above.mono_right {T S S' : Finset L} (h : Above T S) (hS : S' ⊆ S) : Above T S' :=
  ⟨h.1, fun t ht s hs => h.2 t ht s (hS hs)⟩

end Strata

/-! ### One layer of the cell equation -/

section Layer
variable {L : Type} [PartialOrder L]

/-- `Imm_S`, one layer: a nonempty lifetime set `ls` above `S`, a value, a witness in
`Res_ls`. -/
structure ImmF (S : Finset L) (below : ∀ T, Above T S → Type) : Type where
  ls : Finset L
  hls : Above ls S
  v : Val
  ρ : PMap Loc (below ls hls)

/-- `Mut_S`, one layer: a lifetime `β` above `S`, a value, a witness in `Res_{β}`, a stored
predicate on `Res_{β}` that holds at the witness. -/
structure MutF (S : Finset L) (below : ∀ T, Above T S → Type) : Type where
  β : L
  hβ : Above {β} S
  v : Val
  ρ : PMap Loc (below {β} hβ)
  P : Val → PMap Loc (below {β} hβ) → Prop
  hw : P v ρ

/-- `Cell_S`, one layer. -/
inductive CellF (S : Finset L) (below : ∀ T, Above T S → Type) : Type where
  | own (v : Val)
  | imm (i : ImmF S below)
  | mut (m : MutF S below)

/-- A solution of the cell equation: a family of types, each the layer over the others. -/
def IsCarrier (Cell : Finset L → Type) : Prop :=
  Nonempty (∀ S, Cell S ≃ CellF S (fun T _ => Cell T))

end Layer

/-! ### The construction -/

section Construction
variable {L : Type} [PartialOrder L] [WellFoundedGT L]

/-- `Cell_S`, by well-founded recursion on the strata. -/
def Cell : Finset L → Type := WellFounded.fix above_wf (fun S below => CellF S below)

/-- **The cell equation.** -/
theorem Cell_eq (S : Finset L) : Cell S = CellF S (fun T _ => Cell T) :=
  WellFounded.fix_eq above_wf (fun S below => CellF S below) S

/-- **The cell equation has a solution** over every partial order with no infinite ascending
chain. -/
theorem isCarrier : IsCarrier (Cell (L := L)) := ⟨fun S => Equiv.cast (Cell_eq S)⟩

/-- `Res_S`. -/
abbrev Res (S : Finset L) : Type := PMap Loc (Cell S)

def Cell.toF {S : Finset L} (x : Cell S) : CellF S (fun T _ => Cell T) := cast (Cell_eq S) x

def Cell.ofF {S : Finset L} (y : CellF S (fun T _ => Cell T)) : Cell S := cast (Cell_eq S).symm y

@[simp] theorem Cell.toF_ofF {S : Finset L} (y : CellF S (fun T _ => Cell T)) :
    (Cell.ofF y).toF = y := cast_cast _ _ y

@[simp] theorem Cell.ofF_toF {S : Finset L} (x : Cell S) : Cell.ofF x.toF = x := cast_cast _ _ x

end Construction

/-! ### Only an order with no infinite ascending chain carries the cells -/

section NoCarrier
variable {L : Type} [PartialOrder L]

/-- The one-location map `ℓ ↦ a`. -/
def pmapSingle {A : Type} (l : Loc) (a : A) : PMap Loc A where
  get := fun l' => if l' = l then some a else none
  finite := ⟨[l], fun l' h => by
    by_cases e : l' = l
    · exact e ▸ List.mem_singleton.mpr rfl
    · exact absurd (if_neg e) h⟩

theorem pmapSingle_ne_empty {A : Type} (l : Loc) (a : A) : pmapSingle l a ≠ PMap.empty := by
  intro h
  have := congrArg (fun p => PMap.get p l) h
  simp [pmapSingle, PMap.empty] at this

theorem pmapSingle_injective {A : Type} (l : Loc) : Function.Injective (pmapSingle (A := A) l) := by
  intro a b h
  have := congrArg (fun p => PMap.get p l) h
  simpa [pmapSingle] using this

/-- The stored predicate that encodes `T`: `∅`, or a single cell of `T` at `ℓ₀`. -/
def encodeP {A : Type} (l₀ : Loc) (T : A → Prop) : Val → PMap Loc A → Prop :=
  fun _ ρ => ρ = PMap.empty ∨ ∃ c, T c ∧ ρ = pmapSingle l₀ c

/-- **A `mut` cell of stratum `S` stores any predicate on the cells of a stratum `{β}` above
`S`**, injectively. -/
theorem predInj (Cell : Finset L → Type) {S : Finset L} {β : L} (h : Above {β} S) (l₀ : Loc)
    (v₀ : Val) :
    Function.Injective (fun T : Set (Cell {β}) =>
      (CellF.mut ⟨β, h, v₀, PMap.empty, encodeP l₀ T, Or.inl rfl⟩ :
        CellF S (fun T _ => Cell T))) := by
  intro T U hTU
  have hm := CellF.mut.inj hTU
  obtain ⟨-, -, -, hP⟩ := MutF.mk.inj hm
  have hP' : encodeP (A := Cell {β}) l₀ T = encodeP l₀ U := eq_of_heq hP
  ext c
  have hc := congrFun (congrFun hP' v₀) (pmapSingle l₀ c)
  simp only [encodeP, eq_iff_iff] at hc
  constructor
  · intro hT
    rcases hc.mp (Or.inr ⟨c, hT, rfl⟩) with he | ⟨c', hU, he⟩
    · exact absurd he (pmapSingle_ne_empty _ _)
    · rwa [pmapSingle_injective _ he]
  · intro hU
    rcases hc.mpr (Or.inr ⟨c, hU, rfl⟩) with he | ⟨c', hT, he⟩
    · exact absurd he (pmapSingle_ne_empty _ _)
    · rwa [pmapSingle_injective _ he]

/-- **No solution over a partial order with an infinite strictly ascending chain**: the strata
along it would have strictly descending cardinals (Cantor). -/
theorem no_carrier_of_strictMono (Cell : Finset L → Type) (hC : IsCarrier Cell) (a : ℕ → L)
    (ha : StrictMono a) : False := by
  obtain ⟨e⟩ := hC
  have key : ∀ n, Cardinal.mk (Cell {a (n + 1)}) < Cardinal.mk (Cell {a n}) := by
    intro n
    have hlt : Above {a (n + 1)} {a n} := above_singleton_singleton.mpr (ha (Nat.lt_succ_self n))
    have hinj : Function.Injective (fun T : Set (Cell {a (n + 1)}) =>
        (e {a n}).symm (CellF.mut ⟨a (n + 1), hlt, Val.unit, PMap.empty, encodeP 0 T,
          Or.inl rfl⟩)) :=
      (e {a n}).symm.injective.comp (predInj Cell hlt 0 Val.unit)
    calc Cardinal.mk (Cell {a (n + 1)}) < 2 ^ Cardinal.mk (Cell {a (n + 1)}) :=
          Cardinal.cantor _
      _ = Cardinal.mk (Set (Cell {a (n + 1)})) := Cardinal.mk_set.symm
      _ ≤ Cardinal.mk (Cell {a n}) := Cardinal.mk_le_of_injective hinj
  exact not_strictAnti_of_wellFoundedLT (fun n => Cardinal.mk (Cell {a n}))
    (strictAnti_nat_of_succ_lt key)

theorem wellFoundedGT_of_no_chain (h : ∀ a : ℕ → L, ¬ StrictMono a) : WellFoundedGT L := by
  refine ⟨?_⟩
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => h f fun m n hmn => ?_⟩
  exact f.map_rel_iff.mpr hmn

end NoCarrier

/-! ### The union `CellU ≜ ⋃_S Cell_S` -/

section Union
variable {L : Type} [PartialOrder L] [WellFoundedGT L]

/-- The `imm` payload of the union. -/
structure ImmU (L : Type) [PartialOrder L] [WellFoundedGT L] : Type where
  ls : Finset L
  hne : ls.Nonempty
  v : Val
  ρ : Res ls

/-- The `mut` payload of the union. -/
structure MutU (L : Type) [PartialOrder L] [WellFoundedGT L] : Type where
  β : L
  v : Val
  ρ : Res ({β} : Finset L)
  P : Val → Res ({β} : Finset L) → Prop
  hw : P v ρ

/-- `ψ ∈ Cell ≜ ⋃_S Cell_S`. -/
inductive CellU (L : Type) [PartialOrder L] [WellFoundedGT L] : Type where
  | own (v : Val)
  | imm (i : ImmU L)
  | mut (m : MutU L)

/-- `Res ≜ Loc ⇀ᶠⁱⁿ Cell`. -/
abbrev ResU (L : Type) [PartialOrder L] [WellFoundedGT L] : Type := PMap Loc (CellU L)

/-- `SProp ≜ Res → ℙ`. -/
abbrev WPropN (L : Type) [PartialOrder L] [WellFoundedGT L] : Type := ResU L → Prop

/-- `ψ ∈ Cell_S`: every lifetime of the cell strictly outlives every member of `S`; `own`
cells are in every stratum. -/
def CellU.InStratum (S : Finset L) : CellU L → Prop
  | .own _ => True
  | .imm i => Above i.ls S
  | .mut m => Above {m.β} S

/-- `ρ ∈ Res_S`: (a) of the module docstring at `S = {α}`. -/
def ResU.InStratum (S : Finset L) (ρ : ResU L) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → ψ.InStratum S

/-- One layer of `Cell_S` as a member of the union. -/
def CellF.toU {S : Finset L} : CellF S (fun T _ => Cell T) → CellU L
  | .own v => .own v
  | .imm i => .imm ⟨i.ls, i.hls.1, i.v, i.ρ⟩
  | .mut m => .mut ⟨m.β, m.v, m.ρ, m.P, m.hw⟩

def CellU.toLayer (S : Finset L) :
    (ψ : CellU L) → ψ.InStratum S → CellF S (fun T _ => Cell T)
  | .own v, _ => .own v
  | .imm i, h => .imm ⟨i.ls, h, i.v, i.ρ⟩
  | .mut m, h => .mut ⟨m.β, h, m.v, m.ρ, m.P, m.hw⟩

theorem CellF.toU_inStratum {S : Finset L} (x : CellF S (fun T _ => Cell T)) :
    (CellF.toU x).InStratum S := by
  cases x with
  | own v => trivial
  | imm i => exact i.hls
  | «mut» m => exact m.hβ

theorem CellU.toU_toLayer {S : Finset L} (ψ : CellU L) (h : ψ.InStratum S) :
    CellF.toU (ψ.toLayer S h) = ψ := by
  cases ψ <;> rfl

theorem CellF.toLayer_toU {S : Finset L} (x : CellF S (fun T _ => Cell T))
    (h : (CellF.toU x).InStratum S) : (CellF.toU x).toLayer S h = x := by
  cases x <;> rfl

/-- The injection `Cell_S ↪ Cell`. -/
def Cell.toU {S : Finset L} (x : Cell S) : CellU L := CellF.toU x.toF

theorem Cell.toU_inStratum {S : Finset L} (x : Cell S) : x.toU.InStratum S :=
  CellF.toU_inStratum x.toF

/-- Its inverse on the cells of the stratum. -/
def CellU.toStratum (S : Finset L) (ψ : CellU L) (h : ψ.InStratum S) : Cell S :=
  Cell.ofF (ψ.toLayer S h)

theorem CellU.toU_toStratum {S : Finset L} (ψ : CellU L) (h : ψ.InStratum S) :
    (ψ.toStratum S h).toU = ψ := by
  unfold Cell.toU CellU.toStratum
  rw [Cell.toF_ofF, CellU.toU_toLayer]

theorem Cell.toStratum_toU {S : Finset L} (x : Cell S) (h : x.toU.InStratum S) :
    x.toU.toStratum S h = x := by
  unfold CellU.toStratum
  rw [show x.toU.toLayer S h = x.toF from CellF.toLayer_toU x.toF h, Cell.ofF_toF]

theorem Cell.toU_injective {S : Finset L} : Function.Injective (Cell.toU (S := S)) := by
  intro x y h
  rw [← Cell.toStratum_toU x x.toU_inStratum, ← Cell.toStratum_toU y y.toU_inStratum]
  congr 1

/-- `Res_S ↪ Res`. -/
def Res.toU {S : Finset L} (ρ : Res S) : ResU L := ρ.map Cell.toU

@[simp] theorem Res.toU_get {S : Finset L} (ρ : Res S) (l : Loc) :
    ρ.toU.get l = (ρ.get l).map Cell.toU := rfl

theorem Res.toU_inStratum {S : Finset L} (ρ : Res S) : ρ.toU.InStratum S := by
  intro l ψ e
  rw [Res.toU_get] at e
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp e
  exact x.toU_inStratum

def optToStratum (S : Finset L) : (o : Option (CellU L)) →
    (∀ ψ, o = some ψ → ψ.InStratum S) → Option (Cell S)
  | none, _ => none
  | some ψ, h => some (ψ.toStratum S (h ψ rfl))

theorem optToStratum_eq_none {S : Finset L} {o : Option (CellU L)}
    (k : ∀ ψ, o = some ψ → ψ.InStratum S) (e : o = none) : optToStratum S o k = none := by
  subst e; rfl

/-- `{ρ ∈ Res ∣ ρ ∈ Res_S} → Res_S`. -/
def ResU.toStratum {S : Finset L} (ρ : ResU L) (h : ρ.InStratum S) : Res S where
  get := fun l => optToStratum S (ρ.get l) (fun ψ e => h l ψ e)
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    exact ⟨d, fun l hl => hd l (fun e => hl (optToStratum_eq_none _ e))⟩

theorem optToStratum_toU {S : Finset L} (o : Option (CellU L))
    (k : ∀ ψ, o = some ψ → ψ.InStratum S) :
    Option.map Cell.toU (optToStratum S o k) = o := by
  cases o with
  | none => rfl
  | some ψ => exact congrArg some (CellU.toU_toStratum ψ _)

theorem optToStratum_map {S : Finset L} (o : Option (Cell S))
    (k : ∀ ψ, Option.map Cell.toU o = some ψ → ψ.InStratum S) :
    optToStratum S (Option.map Cell.toU o) k = o := by
  cases o with
  | none => rfl
  | some x => exact congrArg some (Cell.toStratum_toU x _)

theorem ResU.toU_toStratum {S : Finset L} (ρ : ResU L) (h : ρ.InStratum S) :
    (ρ.toStratum h).toU = ρ :=
  PMap.ext fun l => optToStratum_toU (ρ.get l) _

theorem Res.toStratum_toU {S : Finset L} (ρ : Res S) (h : ρ.toU.InStratum S) :
    ρ.toU.toStratum h = ρ :=
  PMap.ext fun l => optToStratum_map (ρ.get l) _

theorem Res.toU_injective {S : Finset L} : Function.Injective (Res.toU (S := S)) := by
  intro ρ σ h
  rw [← Res.toStratum_toU ρ ρ.toU_inStratum, ← Res.toStratum_toU σ σ.toU_inStratum]
  congr 1

theorem ResU.toStratum_congr {S : Finset L} {ρ σ : ResU L} (e : ρ = σ) (h : ρ.InStratum S)
    (h' : σ.InStratum S) : ρ.toStratum h = σ.toStratum h' := by
  subst e; rfl

/-! ### A cell's data -/

/-- The tag. -/
def CellU.kind : CellU L → BoCa.Fig16.Kind
  | .own _ => .own
  | .imm _ => .imm
  | .mut _ => .mut

/-- `⟦ψ⟧`, the value. -/
def CellU.erase : CellU L → Val
  | .own v => v
  | .imm i => i.v
  | .mut m => m.v

/-- The witness, in the union. -/
def CellU.wit : CellU L → ResU L
  | .own _ => PMap.empty
  | .imm i => i.ρ.toU
  | .mut m => m.ρ.toU

/-- The lifetimes: `ᾱ` of an `imm` cell, `{β}` of a `mut` cell, none for `own`. -/
def CellU.lts : CellU L → Finset L
  | .own _ => ∅
  | .imm i => i.ls
  | .mut m => {m.β}

/-- The stored predicate read on the union, `False` outside the stratum (`Paper`'s `ofS`);
`False` for `own` and `imm`. -/
def CellU.pu : CellU L → Val → ResU L → Prop
  | .mut m => fun u σ => ∃ h : σ.InStratum {m.β}, m.P u (σ.toStratum h)
  | _ => fun _ _ => False

theorem CellU.wit_inStratum_imm (i : ImmU L) : (CellU.imm i).wit.InStratum i.ls :=
  Res.toU_inStratum i.ρ

theorem CellU.wit_inStratum_mut (m : MutU L) : (CellU.mut m).wit.InStratum {m.β} :=
  Res.toU_inStratum m.ρ

theorem CellU.pu_inStratum (m : MutU L) {u : Val} {σ : ResU L} (h : (CellU.mut m).pu u σ) :
    σ.InStratum {m.β} := h.1

/-- `imm(ᾱ, v, ρ)`, from its data. -/
def CellU.immOf (s : Finset L) (hs : s.Nonempty) (v : Val) (ρ : ResU L)
    (h : ρ.InStratum s) : CellU L :=
  .imm ⟨s, hs, v, ρ.toStratum h⟩

/-- `mut(β, v, ρ, P̂)`, from its data: `P` holds only in `Res_{β}` and at the witness. -/
def CellU.mutOf (b : L) (v : Val) (ρ : ResU L) (h : ρ.InStratum {b})
    (P : Val → ResU L → Prop) (hw : P v ρ) : CellU L :=
  .mut ⟨b, v, ρ.toStratum h, fun u r => P u r.toU, by rw [ResU.toU_toStratum]; exact hw⟩

@[simp] theorem CellU.kind_immOf (s : Finset L) (hs : s.Nonempty) (v : Val) (ρ : ResU L)
    (h : ρ.InStratum s) : (CellU.immOf s hs v ρ h).kind = .imm := rfl
@[simp] theorem CellU.erase_immOf (s : Finset L) (hs : s.Nonempty) (v : Val) (ρ : ResU L)
    (h : ρ.InStratum s) : (CellU.immOf s hs v ρ h).erase = v := rfl
@[simp] theorem CellU.wit_immOf (s : Finset L) (hs : s.Nonempty) (v : Val) (ρ : ResU L)
    (h : ρ.InStratum s) : (CellU.immOf s hs v ρ h).wit = ρ := ResU.toU_toStratum ρ h
@[simp] theorem CellU.lts_immOf (s : Finset L) (hs : s.Nonempty) (v : Val) (ρ : ResU L)
    (h : ρ.InStratum s) : (CellU.immOf s hs v ρ h).lts = s := rfl
@[simp] theorem CellU.pu_immOf (s : Finset L) (hs : s.Nonempty) (v : Val) (ρ : ResU L)
    (h : ρ.InStratum s) : (CellU.immOf s hs v ρ h).pu = fun _ _ => False := rfl

@[simp] theorem CellU.kind_mutOf (b : L) (v : Val) (ρ : ResU L) (h : ρ.InStratum {b})
    (P : Val → ResU L → Prop) (hw : P v ρ) : (CellU.mutOf b v ρ h P hw).kind = .mut := rfl
@[simp] theorem CellU.erase_mutOf (b : L) (v : Val) (ρ : ResU L) (h : ρ.InStratum {b})
    (P : Val → ResU L → Prop) (hw : P v ρ) : (CellU.mutOf b v ρ h P hw).erase = v := rfl
@[simp] theorem CellU.wit_mutOf (b : L) (v : Val) (ρ : ResU L) (h : ρ.InStratum {b})
    (P : Val → ResU L → Prop) (hw : P v ρ) : (CellU.mutOf b v ρ h P hw).wit = ρ :=
  ResU.toU_toStratum ρ h
@[simp] theorem CellU.lts_mutOf (b : L) (v : Val) (ρ : ResU L) (h : ρ.InStratum {b})
    (P : Val → ResU L → Prop) (hw : P v ρ) : (CellU.mutOf b v ρ h P hw).lts = {b} := rfl

/-- The stored predicate of `mutOf` is `P` cut down to `Res_{β}`. -/
theorem CellU.pu_mutOf (b : L) (v : Val) (ρ : ResU L) (h : ρ.InStratum {b})
    (P : Val → ResU L → Prop) (hw : P v ρ) :
    (CellU.mutOf b v ρ h P hw).pu = fun u σ => P u σ ∧ σ.InStratum {b} := by
  funext u σ
  apply propext
  constructor
  · rintro ⟨hσ, hP⟩
    change P u (σ.toStratum hσ).toU at hP
    exact ⟨by rw [ResU.toU_toStratum] at hP; exact hP, hσ⟩
  · rintro ⟨hP, hσ⟩
    exact ⟨hσ, by show P u (σ.toStratum hσ).toU; rw [ResU.toU_toStratum]; exact hP⟩

/-- When `P` holds only in `Res_{β}`, the stored predicate of `mutOf` is `P`. -/
theorem CellU.pu_mutOf_of {b : L} {v : Val} {ρ : ResU L} {h : ρ.InStratum {b}}
    {P : Val → ResU L → Prop} {hw : P v ρ} (hP : ∀ u σ, P u σ → σ.InStratum {b}) :
    (CellU.mutOf b v ρ h P hw).pu = P := by
  rw [CellU.pu_mutOf]
  funext u σ
  exact propext ⟨fun k => k.1, fun k => ⟨k, hP u σ k⟩⟩

theorem CellU.inStratum_immOf (S : Finset L) (s : Finset L) (hs : s.Nonempty) (v : Val)
    (ρ : ResU L) (h : ρ.InStratum s) : (CellU.immOf s hs v ρ h).InStratum S ↔ Above s S :=
  Iff.rfl

theorem CellU.inStratum_mutOf (S : Finset L) (b : L) (v : Val) (ρ : ResU L)
    (h : ρ.InStratum {b}) (P : Val → ResU L → Prop) (hw : P v ρ) :
    (CellU.mutOf b v ρ h P hw).InStratum S ↔ Above {b} S := Iff.rfl

/-- **A cell is determined by its data.** -/
theorem CellU.ext_data {ψ ψ' : CellU L} (hk : ψ.kind = ψ'.kind) (he : ψ.erase = ψ'.erase)
    (hw : ψ.wit = ψ'.wit) (hl : ψ.lts = ψ'.lts) (hp : ψ.pu = ψ'.pu) : ψ = ψ' := by
  cases ψ with
  | own v =>
      cases ψ' with
      | own v' => cases he; rfl
      | imm _ => cases hk
      | «mut» _ => cases hk
  | imm i =>
      cases ψ' with
      | own _ => cases hk
      | «mut» _ => cases hk
      | imm i' =>
          obtain ⟨s, hs, v, ρ⟩ := i
          obtain ⟨s', hs', v', ρ'⟩ := i'
          change s = s' at hl
          subst hl
          change v = v' at he
          subst he
          have : ρ = ρ' := Res.toU_injective hw
          subst this
          rfl
  | «mut» m =>
      cases ψ' with
      | own _ => cases hk
      | imm _ => cases hk
      | «mut» m' =>
          obtain ⟨b, v, ρ, P, hwit⟩ := m
          obtain ⟨b', v', ρ', P', hwit'⟩ := m'
          change ({b} : Finset L) = {b'} at hl
          obtain rfl := Finset.singleton_inj.mp hl
          change v = v' at he
          subst he
          have : ρ = ρ' := Res.toU_injective hw
          subst this
          have hP : P = P' := by
            funext u r
            have := congrFun (congrFun hp u) r.toU
            apply propext
            change (∃ h : r.toU.InStratum {b}, P u (r.toU.toStratum h)) =
              (∃ h : r.toU.InStratum {b}, P' u (r.toU.toStratum h)) at this
            constructor
            · intro k
              have k' : ∃ h : r.toU.InStratum {b}, P u (r.toU.toStratum h) :=
                ⟨r.toU_inStratum, by rw [Res.toStratum_toU]; exact k⟩
              rw [this] at k'
              obtain ⟨h, k''⟩ := k'
              rwa [Res.toStratum_toU] at k''
            · intro k
              have k' : ∃ h : r.toU.InStratum {b}, P' u (r.toU.toStratum h) :=
                ⟨r.toU_inStratum, by rw [Res.toStratum_toU]; exact k⟩
              rw [← this] at k'
              obtain ⟨h, k''⟩ := k'
              rwa [Res.toStratum_toU] at k''
          subst hP
          rfl

/-- Every `imm` cell is an `immOf`. -/
theorem CellU.imm_eta (i : ImmU L) :
    CellU.imm i = CellU.immOf i.ls i.hne i.v i.ρ.toU i.ρ.toU_inStratum :=
  CellU.ext_data rfl rfl (CellU.wit_immOf _ _ _ _ _).symm rfl rfl

theorem CellU.mut_pu_inStratum (m : MutU L) :
    ∀ u σ, (CellU.mut m).pu u σ → σ.InStratum {m.β} := fun _ _ h => h.1

theorem CellU.mut_pu_wit (m : MutU L) : (CellU.mut m).pu m.v m.ρ.toU := by
  show ∃ h : m.ρ.toU.InStratum {m.β}, m.P m.v (m.ρ.toU.toStratum h)
  exact ⟨m.ρ.toU_inStratum, by rw [Res.toStratum_toU]; exact m.hw⟩

/-- Every `mut` cell is a `mutOf` of its stored predicate. -/
theorem CellU.mut_eta (m : MutU L) :
    CellU.mut m = CellU.mutOf m.β m.v m.ρ.toU m.ρ.toU_inStratum (CellU.mut m).pu
      (CellU.mut_pu_wit m) :=
  CellU.ext_data rfl rfl (CellU.wit_mutOf _ _ _ _ _ _).symm rfl
    (CellU.pu_mutOf_of (CellU.mut_pu_inStratum m)).symm

/-! ### `[α]P`, two readings -/

/-- (b) `ψ` survives the end of `α`: none of its lifetimes is at or beneath `α`. -/
def CellU.Survives (α : L) : CellU L → Prop
  | .own _ => True
  | .imm i => ∀ m ∈ i.ls, ¬ m ≤ α
  | .mut m => ¬ m.β ≤ α

/-- (b) for a resource. -/
def ResU.Survives (α : L) (ρ : ResU L) : Prop := ∀ l ψ, ρ.get l = some ψ → ψ.Survives α

/-- (a) `[α]P`: `P` and every cell strictly outlives `α` (`ρ ∈ Res_{α}`). -/
def boxS (α : L) (P : WPropN L) : WPropN L := fun ρ => P ρ ∧ ρ.InStratum {α}

/-- (b) `[α]P`: `P` and `ρ` survives the end of `α`. -/
def boxE (α : L) (P : WPropN L) : WPropN L := fun ρ => P ρ ∧ ρ.Survives α

/-- (a) implies (b): a cell strictly above `α` is not at or beneath it. -/
theorem CellU.survives_of_inStratum {α : L} {ψ : CellU L} (h : ψ.InStratum {α}) :
    ψ.Survives α := by
  cases ψ with
  | own v => trivial
  | imm i =>
      exact fun m hm hle => absurd (h.2 m hm α (Finset.mem_singleton_self α)) (not_lt_of_ge hle)
  | «mut» m => exact fun hle => absurd (h.2 m.β (Finset.mem_singleton_self _) α
      (Finset.mem_singleton_self α)) (not_lt_of_ge hle)

/-- **On lifetimes comparable with `α` the two readings agree.** -/
theorem CellU.survives_iff_inStratum {α : L} {ψ : CellU L}
    (hc : ∀ m ∈ ψ.lts, m ≤ α ∨ α ≤ m) : ψ.Survives α ↔ ψ.InStratum {α} := by
  refine ⟨fun h => ?_, CellU.survives_of_inStratum⟩
  cases ψ with
  | own v => trivial
  | imm i =>
      refine ⟨i.hne, fun m hm s hs => ?_⟩
      rw [Finset.mem_singleton.mp hs]
      rcases hc m hm with hle | hle
      · exact absurd hle (h m hm)
      · exact lt_of_le_of_ne hle (fun e => h m hm (e ▸ le_rfl))
  | «mut» m =>
      refine above_singleton_singleton.mpr ?_
      rcases hc m.β (Finset.mem_singleton_self _) with hle | hle
      · exact absurd hle h
      · exact lt_of_le_of_ne hle (fun e => h (e ▸ le_rfl))

end Union

/-- **The cell equation over a partial order has a solution exactly when the order has no
infinite ascending chain.** -/
theorem carrier_iff {L : Type} [PartialOrder L] :
    (∃ Cell : Finset L → Type, IsCarrier Cell) ↔ WellFoundedGT L := by
  constructor
  · rintro ⟨Cell, hC⟩
    exact wellFoundedGT_of_no_chain fun a ha => no_carrier_of_strictMono Cell hC a ha
  · intro _
    exact ⟨Cell, isCarrier⟩

end Nominal

end
