import Nominal.Equivariance
import Nominal.Facts
import Nominal.Atoms

/-!
# Nominal — closing a self-borrow and re-opening it at a fresh lifetime

A **package** `∃'x. (own c, contents typed in 'x)` holds, while stored, no live borrow: an owned
cell `c` with value `u` and payload resource `σu`, and contents `w` with resource `ρw`
(`Pkg`, `Pkg.Closed`). **Opening it at `y`** lends `c` at `y` — the lent cell `mut(y, u, σu, P̂)`
storing the payload's relation — beside the contents (`Pkg.Opens`); the contents are read at
`δ['x ↦ y]`. **Closing** ends that borrow: `c ↦ own(u)` and `σu` come back (`Pkg.Closed`), and the
contents must survive the end of `y` (`Pkg.CloseOK`, reading (b) of `[y]`).

**The corollary** (`reopen`, `reopen_iff`): for every order automorphism `π` that fixes the
package and the reading of the other variables, opening at `π y` relates, at `δ['x ↦ π y]`, exactly
what opening at `y` related at `δ['x ↦ y]`; the opened resource at `π y` is the moved one. It is
`vN_map` (equivariance) at `π`, nothing else: no history, no derivation, no hypothesis about how
the package was built.

**Re-opening at a fresh atom with the same parents** (`reopen_swap`): `π` is the hereditary swap
`x ↔ x′` (`Atoms.lean`), an automorphism exactly because `x′` has `x`'s parents. Its hypotheses are
freshness — `x` and `x′` occur in no lifetime `δ` reads (`LSubN.Avoids`, met by `fresh`), and the
swap fixes the package — and are discharged for packages whose cells are owned
(`fixedBy_of_ownOnly`) and for captured borrows at lifetimes the swap fixes storing relation
instances (`relU_mutOf_fix`, `img_vN_fix`). `reopen_fresh` states it at `x′ = fresh x.ps avoid`.

`exists_iff_forall_fresh`: "some fresh atom with parents `S` opens the package to a related
configuration" iff "every one does" — the И quantifier.
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)
open BoCa.Fig16.LogRel.Core (VTy CTy forceE)
open BoCa.Lifetime (LifeVar LifeCtx)

set_option linter.unusedSectionVars false

variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- A closed package: the owned place `c` holding `u` (payload resource `σu`), and the contents
`w` (resource `ρw`). -/
structure Pkg (L : Type) [PartialOrder L] [WellFoundedGT L] where
  c : Loc
  u : Val
  σu : ResU L
  w : Val
  ρw : ResU L

namespace Pkg

/-- The closed package's resource: the self-borrow ended, `c` owned again. -/
def Closed (p : Pkg L) (ρ : ResU L) : Prop :=
  ∃ ρ₁, ResU.CompS (ResU.single p.c (.own p.u)) p.σu ρ₁ ∧ ResU.CompS ρ₁ p.ρw ρ

/-- Opening at `y`: `c` lent at `y`, the lent cell storing `P`, beside the contents. -/
def Opens (P : Val → WPropN L) (p : Pkg L) (y : L) (ρ : ResU L) : Prop :=
  ∃ (h : p.σu.InStratum {y}) (hw : P p.u p.σu),
    ResU.CompS (ResU.single p.c (CellU.mutOf y p.u p.σu h P hw)) p.ρw ρ

/-- Ending the borrow at `y` leaves the contents intact: none of their cells is at or beneath
`y` (reading (b) of `[y]`). -/
def CloseOK (p : Pkg L) (y : L) : Prop := p.ρw.Survives y

/-- `π` fixes the package and the stored predicate. -/
def FixedBy (π : L ≃o L) (P : Val → WPropN L) (p : Pkg L) : Prop :=
  relRU π p.σu = p.σu ∧ relRU π p.ρw = p.ρw ∧ img π P = P

theorem FixedBy.symm {π : L ≃o L} {P : Val → WPropN L} {p : Pkg L} (h : p.FixedBy π P) :
    p.FixedBy π.symm P := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [← h₁]
    exact relRU_symm_relRU π p.σu
  · conv_lhs => rw [← h₂]
    exact relRU_symm_relRU π p.ρw
  · have := img_img_symm π.symm P
    rw [OrderIso.symm_symm] at this
    conv_lhs => rw [← h₃]
    exact this

end Pkg

/-- The image of a predicate holding only in `Res_{y}`, stratum moved. -/
theorem img_inStratum (π : L ≃o L) (y : L) :
    img π (fun (_ : Val) (σ : ResU L) => σ.InStratum {y}) =
      fun _ σ => σ.InStratum {π y} := by
  funext u τ
  apply propext
  obtain ⟨σ, rfl⟩ := relRU_surjective π τ
  rw [img_apply, inStratum_relRU_singleton]

/-- A lent cell whose witness and stored predicate `π` fixes moves to the lent cell at `π y`. -/
theorem relU_mutOf_of_fix (π : L ≃o L) {y : L} {u : Val} {σ : ResU L} {h : σ.InStratum {y}}
    {P : Val → WPropN L} {hw : P u σ} (hσ : relRU π σ = σ) (hP : img π P = P) :
    relU π (CellU.mutOf y u σ h P hw) =
      CellU.mutOf (π y) u σ (by rw [← hσ]; exact (inStratum_relRU_singleton π y σ).mpr h) P hw := by
  refine CellU.ext_data (by rfl) (by rfl) ?_ ?_ ?_
  · rw [wit_relU, CellU.wit_mutOf, CellU.wit_mutOf, hσ]
  · rw [lts_relU, CellU.lts_mutOf, CellU.lts_mutOf]; rfl
  · rw [pu_relU, CellU.pu_mutOf, CellU.pu_mutOf, img_and, hP, img_inStratum]

namespace Pkg

/-- **The opened resource moves with `π`.** -/
theorem opens_relRU {π : L ≃o L} {P : Val → WPropN L} {p : Pkg L} (hfix : p.FixedBy π P)
    {y : L} {ρ : ResU L} (h : p.Opens P y ρ) : p.Opens P (π y) (relRU π ρ) := by
  obtain ⟨h₁, hw, hc⟩ := h
  obtain ⟨hσ, hρw, hP⟩ := hfix
  have hc' := compS_relRU (π := π) hc
  rw [relRU_single, relU_mutOf_of_fix π hσ hP, hρw] at hc'
  exact ⟨_, hw, hc'⟩

theorem opens_relRU_iff {π : L ≃o L} {P : Val → WPropN L} {p : Pkg L} (hfix : p.FixedBy π P)
    {y : L} {ρ : ResU L} : p.Opens P (π y) (relRU π ρ) ↔ p.Opens P y ρ := by
  refine ⟨fun h => ?_, opens_relRU hfix⟩
  have := opens_relRU hfix.symm h
  rwa [OrderIso.symm_apply_apply, relRU_symm_relRU] at this

theorem closeOK_iff {π : L ≃o L} {P : Val → WPropN L} {p : Pkg L} (hfix : p.FixedBy π P)
    (y : L) : p.CloseOK (π y) ↔ p.CloseOK y := by
  unfold CloseOK
  conv_lhs => rw [← hfix.2.1]
  exact survives_relRU π y p.ρw

end Pkg

/-- **Opening at `π y` relates exactly what opening at `y` related**, at every type, for every
automorphism fixing the package and the other variables' reading. A corollary of `vN_map`. -/
theorem reopen (π : L ≃o L) {P : Val → WPropN L} {p : Pkg L} (hfix : p.FixedBy π P)
    {δ : LSubN L} (hδ : δ.map π = δ) (xv : LifeVar) (y : L) (b : Bool) (T : VTy) {ρ : ResU L}
    (h : p.Opens P y ρ) :
    p.Opens P (π y) (relRU π ρ) ∧
      (vN (ℍ := ℍ) b T (δ.extend xv (π y)) p.w (relRU π ρ) ↔
        vN (ℍ := ℍ) b T (δ.extend xv y) p.w ρ) := by
  refine ⟨Pkg.opens_relRU hfix h, ?_⟩
  have := vN_map (ℍ := ℍ) π b T (δ.extend xv y) p.w ρ
  rwa [LSubN.map_extend, hδ] at this

/-- The same at a computation type: the contents read as a computation. -/
theorem reopenC (π : L ≃o L) {P : Val → WPropN L} {p : Pkg L} (hfix : p.FixedBy π P)
    {δ : LSubN L} (hδ : δ.map π = δ) (xv : LifeVar) (y : L) (C : CTy) (e : Expr) {ρ : ResU L}
    (h : p.Opens P y ρ) :
    p.Opens P (π y) (relRU π ρ) ∧
      (cN (ℍ := ℍ) C (δ.extend xv (π y)) e (relRU π ρ) ↔ cN (ℍ := ℍ) C (δ.extend xv y) e ρ) := by
  refine ⟨Pkg.opens_relRU hfix h, ?_⟩
  have := cN_map (ℍ := ℍ) π C (δ.extend xv y) e ρ
  rwa [LSubN.map_extend, hδ] at this

/-- **Re-opening relates exactly what opening related**: some opening at `π y` is related iff
some opening at `y` is. -/
theorem reopen_iff (π : L ≃o L) {P : Val → WPropN L} {p : Pkg L} (hfix : p.FixedBy π P)
    {δ : LSubN L} (hδ : δ.map π = δ) (xv : LifeVar) (y : L) (b : Bool) (T : VTy) :
    (∃ ρ, p.Opens P (π y) ρ ∧ vN (ℍ := ℍ) b T (δ.extend xv (π y)) p.w ρ) ↔
      (∃ ρ, p.Opens P y ρ ∧ vN (ℍ := ℍ) b T (δ.extend xv y) p.w ρ) := by
  constructor
  · rintro ⟨ρ', ho, hv⟩
    obtain ⟨ρ, rfl⟩ := relRU_surjective π ρ'
    refine ⟨ρ, (Pkg.opens_relRU_iff hfix).mp ho, ?_⟩
    exact (reopen π hfix hδ xv y b T ((Pkg.opens_relRU_iff hfix).mp ho)).2.mp hv
  · rintro ⟨ρ, ho, hv⟩
    exact ⟨relRU π ρ, Pkg.opens_relRU hfix ho, (reopen π hfix hδ xv y b T ho).2.mpr hv⟩

/-! ### Discharging the hypotheses -/

/-- The relation at a reading `π` fixes is fixed. -/
theorem img_vN_fix (π : L ≃o L) {δ : LSubN L} (hδ : δ.map π = δ) (b : Bool) (A : VTy) :
    img π (vN (ℍ := ℍ) b A δ) = vN (ℍ := ℍ) b A δ := by
  refine img_eq_of π fun u σ => ?_
  have := vN_map (ℍ := ℍ) π b A δ u σ
  rwa [hδ] at this

/-- **A package whose resources are owned is fixed by every automorphism** fixing the payload's
reading. -/
theorem fixedBy_of_ownOnly (π : L ≃o L) {p : Pkg L} (h₁ : OwnOnly p.σu) (h₂ : OwnOnly p.ρw)
    {δA : LSubN L} (hδ : δA.map π = δA) (A : VTy) :
    p.FixedBy π (vN (ℍ := ℍ) true A δA) :=
  ⟨h₁.relRU_eq π, h₂.relRU_eq π, img_vN_fix π hδ true A⟩

/-- `x` occurs in no lifetime `δ` reads. -/
def LSubN.Avoids (δ : LSubN Lft) (x : Atom) : Prop :=
  ∀ p ∈ δ.entries, ∀ a : Atom, p.2 = (a : Lft) → ¬ a ≤ x

/-- The swap fixes a reading that avoids both atoms. -/
theorem map_swapLft_of_avoids {x x' : Atom} (hs : Atom.SameParents x x') {δ : LSubN Lft}
    (h : δ.Avoids x) (h' : δ.Avoids x') : δ.map (swapLft hs) = δ := by
  conv_rhs => rw [← LSubN.map_id δ]
  exact LSubN.map_congr fun p hp =>
    swapLft_fix hs fun a ha => ⟨h p hp a ha, h' p hp a ha⟩

/-- The atoms a reading reads. -/
def LSubN.atoms (δ : LSubN Lft) : List Atom :=
  δ.entries.filterMap fun p => (p.2 : Option Atom)

theorem LSubN.mem_atoms {δ : LSubN Lft} {p : LifeVar × Lft} (hp : p ∈ δ.entries) {a : Atom}
    (ha : p.2 = (a : Lft)) : a ∈ δ.atoms := by
  refine List.mem_filterMap.mpr ⟨p, hp, ?_⟩
  rw [ha]
  rfl

/-- A fresh atom with the given parents avoids every reading it is chosen against. -/
theorem fresh_avoids (S : List Atom) (δ : LSubN Lft) (avoid : List Atom) :
    δ.Avoids (Atom.fresh S (δ.atoms ++ avoid)) := by
  intro p hp a ha
  exact Atom.fresh_not_le (List.mem_append.mpr (Or.inl (LSubN.mem_atoms hp ha)))

/-- **Re-opening at a fresh atom with the same parents relates exactly what opening at `x` did.**
`x′` is any atom with `x`'s parents; `x` and `x′` occur in no lifetime the other variables read,
and the swap fixes the package. -/
theorem reopen_swap {x x' : Atom} (hs : Atom.SameParents x x') {P : Val → WPropN Lft}
    {p : Pkg Lft} (hfix : p.FixedBy (swapLft hs) P) {δ : LSubN Lft} (hx : δ.Avoids x)
    (hx' : δ.Avoids x') (xv : LifeVar) (b : Bool) (T : VTy) :
    (∃ ρ, p.Opens P (x' : Lft) ρ ∧ vN (ℍ := ℍ) b T (δ.extend xv (x' : Lft)) p.w ρ) ↔
      (∃ ρ, p.Opens P (x : Lft) ρ ∧ vN (ℍ := ℍ) b T (δ.extend xv (x : Lft)) p.w ρ) := by
  have := reopen_iff (ℍ := ℍ) (swapLft hs) hfix (map_swapLft_of_avoids hs hx hx') xv (x : Lft) b T
  rwa [swapLft_x] at this

/-- The same at the fresh atom `fresh x.ps avoid`, for a package of owned cells: every hypothesis
discharged but the reading avoiding `x`. -/
theorem reopen_fresh (x : Atom) (avoid : List Atom) {p : Pkg Lft} (h₁ : OwnOnly p.σu)
    (h₂ : OwnOnly p.ρw) (A : VTy) {δ : LSubN Lft} (hx : δ.Avoids x) (xv : LifeVar) (b : Bool)
    (T : VTy) :
    let x' := Atom.fresh x.ps (δ.atoms ++ avoid)
    (∃ ρ, p.Opens (vN (ℍ := ℍ) true A δ) (x' : Lft) ρ ∧
        vN (ℍ := ℍ) b T (δ.extend xv (x' : Lft)) p.w ρ) ↔
      (∃ ρ, p.Opens (vN (ℍ := ℍ) true A δ) (x : Lft) ρ ∧
        vN (ℍ := ℍ) b T (δ.extend xv (x : Lft)) p.w ρ) := by
  intro x'
  have hs : Atom.SameParents x x' := fun q => by simp [x', Atom.ps_fresh]
  have hx' : δ.Avoids x' := fresh_avoids x.ps δ avoid
  have hδ : δ.map (swapLft hs) = δ := map_swapLft_of_avoids hs hx hx'
  exact reopen_swap hs (fixedBy_of_ownOnly _ h₁ h₂ hδ A) hx hx' xv b T

/-- **The И quantifier**: some fresh atom with parents `S` opens the package to a related
configuration iff every one does, when every swap of two such atoms fixes the package. -/
theorem exists_iff_forall_fresh {P : Val → WPropN Lft} {p : Pkg Lft} {δ : LSubN Lft}
    (S : List Atom) (Fresh : Atom → Prop) (hF : ∀ y, Fresh y → δ.Avoids y)
    (hfix : ∀ y y' (hs : Atom.SameParents y y'), Fresh y → Fresh y' →
      p.FixedBy (swapLft hs) P)
    (xv : LifeVar) (b : Bool) (T : VTy) :
    (∃ y : Atom, y.ps = S ∧ Fresh y ∧
        ∃ ρ, p.Opens P (y : Lft) ρ ∧ vN (ℍ := ℍ) b T (δ.extend xv (y : Lft)) p.w ρ) →
      ∀ y' : Atom, y'.ps = S → Fresh y' →
        ∃ ρ, p.Opens P (y' : Lft) ρ ∧ vN (ℍ := ℍ) b T (δ.extend xv (y' : Lft)) p.w ρ := by
  rintro ⟨y, hy, hFy, hrel⟩ y' hy' hFy'
  have hs : Atom.SameParents y y' := fun q => by rw [hy, hy']
  exact (reopen_swap hs (hfix y y' hs hFy hFy') (hF y hFy) (hF y' hFy') xv b T).mpr hrel

end Nominal

end
