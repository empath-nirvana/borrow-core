import Core.Chain.ExtRLit791
import Core.Chain.SI.HandleN
import Core.Chain.Cancel791N

/-!
# `κ` read at `vN`: Core's `vC_kTy_of_kapRel` at the chain  `[spec §19, §27]`

`docs/new-core/scope-831-interface.md` §10.1, E10. Core's handler (`ewp_handle_vals`,
`Core/EffFin.lean`) hands each clause `κ` with `KapRel` at the stop's list and reads it at `κ`'s type
`kTy Σ R q B F` by `vC_kTy_of_kapRel`: `KapRel` is Kripke along `Ext` from the stop's list, which is
`vC`'s `U` at that list, since one world, the record list, indexes both. At the chain the clause gets
`KapRelN` (`SI/HandleN.lean`): the handled continuation owed at the run's view `Θ.view c`, at the
tables read at `Θ` and `c`, and along `extF` from the stop's list. `vN`'s `U` clause at `kTy` asks it
at every `Θ′` with `Θ.ExtR Θ′ ρ`, every view consistent with `κ`'s share, and every list.

`KapRelKTyN` is Core's step at the chain. Two configurations refute it, each with every hypothesis
discharged, each at the stop's own list:

* **The world** (`kapRelN_world`, `not_kTy_world`). The stop at the empty world, answer type
  `Mut 'x 1`: no `Mut` value exists at the empty world, so `KapRelN` holds of the stuck `κ = ()`.
  The world `∅ + (ℓ′, α) ↦ 𝒱⟦1⟧` is an `ExtA` extension, so `U` reaches it; at the stop's own view
  and list it holds the answer `ℓ′ ↦ mut(α, (), ∅, 𝒱⟦1⟧)`, and `κ` applied to it is stuck from the
  typed world of two cells (`ExtRLit791.world_two`).
* **The view** (`kapRelN_view`, `not_kTy_view`). The stop at the world with the key `(ℓ′, α)`, at a
  view with no lifetime at `ℓ′`: the answer at the key is not consistent with the run's view, which
  a row's table reads (`tabN`'s `ConsistentX c`), so `KapRelN` holds of `κ = ()` again. At the same
  world and list, `U` reads `κ` at a view consistent with its share that puts `ℓ′` at `α`, and the
  same run is stuck.

`ExtRFoldTransfer` is what a stop's share made Kripke along `ExtR` (route 2) asks of the Mut
Frame's fold: the borrowed continuation's share holds the lent cell `mut` at `A`, the lender's holds
it folded to `own`. `not_extRFoldTransfer`: `ExtR` at the lender's share admits a key added above
`A`, which `ExtR` at the borrowed share refuses. It is `SI/ExtF.lean`'s `not_extFoldTransfer` (D8)
at the world.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Kappa835N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791
open BoCa.Lifetime (LSub LifeVar)

/-! ### Core's step at the chain -/

/-- **Core's `vC_kTy_of_kapRel` at the chain**: a continuation owed as `erwp_handle` hands it to a
clause (`KapRelN` at the outer row's table and answer at the world `Θ` and the view `c`, the entry
the row's table holds for the operation), at the index above, is a value of `kTy Σ R q B F` at `Θ`. -/
def KapRelKTyN : Prop :=
  ∀ (S : Row) (R A B : VTy) (q : Qual) (F : CTy) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life)
    (Tc : Option OpTabN) (k : Nat) (ls : List SRec) (κ : Val) (ρ : WRes),
    Θ.OK → ConsistentX c ρ →
    KapRelN (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c))
      (fun k _ v ρ => retN (ℍ := ℍ) (CTy.effOf S R) δ Θ k v ρ)
      (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) B δ Θ k v ρ ∧ ConsistentX c ρ) (finN (ℍ := ℍ) F δ Θ c))
      Tc (k + 1) ls κ ρ →
    vN (ℍ := ℍ) (kTy S R q B F) δ Θ k κ ρ

/-- The answer type of the configurations: `Mut 'x 1`. -/
abbrev bMut (x : LifeVar) : VTy := .mut (.var x) .unit

/-- `κ`'s type at a must-resume operation answering `Mut 'x 1`, at the empty row answering `1`:
`U((Mut 'x 1 ⊸ F 1) & ⊤)`. -/
abbrev kTyC (x : LifeVar) : CTy := .amp (.arr (bMut x) (CTy.effOf [] .unit)) .top

theorem kTy_eq (x : LifeVar) : kTy [] .unit .lin (bMut x) (.ret .unit) = .thunk (kTyC x) := rfl

/-- The world with one key `(ℓ′, α) ↦ 𝒱⟦1⟧`. -/
abbrev Θ₁ (_x : LifeVar) (δ : LSub) (α : Life) (l' : Loc) : LocTy :=
  LocTy.empty.add l' α (famL α (fun Θ j u r => vN (ℍ := ℍ) .unit δ Θ j u r) LocTy.empty)

theorem Θ₁_ok (x : LifeVar) (δ : LSub) {N α : Life} (hNα : N < α) (l' : Loc) :
    (Θ₁ (ℍ := ℍ) x δ α l').OK :=
  ⟨LocTy.down_add LocTy.empty_down l' (vN_fam_down .unit _ α _),
    ⟨N, LocTy.fresh_add (N := N) (fun _ _ h => absurd rfl h) le_rfl hNα l' _⟩⟩

/-- **`U((Mut 'x 1 ⊸ F 1) & ⊤)` fails at the stuck thunk `()` wherever `U` reaches the world with
the key `(ℓ′, α)` at a view putting `ℓ′` at `α`**: that world holds the argument
`ℓ′ ↦ mut(α, (), ∅, 𝒱⟦1⟧)`, and `() (inj₁ ()) ℓ′` is stuck from the typed world of the two cells. -/
theorem not_kTy_at (x : LifeVar) (δ : LSub) {α b : Life} {m l' : Loc}
    (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b) (hcl : c l' = some α) :
    ¬ cN (ℍ := ℍ) (kTyC x) (δ.extend x α) (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') c 1 []
      Val.unit.1 (ρb m b) := by
  intro h
  let P : CPredL := fun Θ j u r => vN (ℍ := ℍ) .unit (δ.extend x α) Θ j u r
  have hw : famL α P LocTy.empty 1 Val.unit ⟨PMap.empty, ResU.inStratum_empty α⟩ := ⟨rfl, rfl⟩
  let cell : WRes := ResU.single l' (CellU.mutOf α Val.unit PMap.empty
    (ResU.inStratum_empty α) (famL α P LocTy.empty 1) hw)
  have hv : vN (ℍ := ℍ) (bMut x) (δ.extend x α) (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') 1
      (Val.loc l') cell :=
    ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL LocTy.empty l' α P le_rfl _ hw,
      fun _ _ _ r h => by obtain ⟨-, rfl⟩ := h; exact ResU.inStratum_empty α⟩
  obtain ⟨ρ', hρ'⟩ := (ResU.compS_defined_iff (ρb m b) cell).mpr
    (compatS_single_of_get_none (ResU.single_get_ne _ hml))
  have hcb : ConsistentX c (ρb m b) := consistentX_single_mut (consistentX_empty c) hcm
  have hcc : ConsistentX c cell := consistentX_single_mut (consistentX_empty c) hcl
  have hc' : ConsistentX c ρ' := consistentX_compS hρ' hcb hcc
  have h' := h.1 c 1 le_rfl (Val.loc l') cell ρ' hρ' hv hc'
  obtain ⟨μ, hH, hT, htg, hl, hfd⟩ := world_two hml _ trivial _ hw hρ'
  let K : BoCa.BoLo.Kont := .appL .hole (Val.loc l')
  change erwp (ℍ := ℍ) _ _ _ 1 [] (K.plug (.app .unit (Val.inj₁ Val.unit).1)) ρ' at h'
  rw [erwp_eq] at h'
  have hfin : Final (ℍ := ℍ) μ (K.plug (.app .unit (Val.inj₁ Val.unit).1)) :=
    fun _ _ hs => stuck_no_step (stuckAt_unit_app (Val.inj₁ Val.unit)) K hs
  have hE := h' PMap.empty ρ' [] μ hH (compS_empty_left ρ') hT htg
    (ImmTieL.of_nil rfl _) hl hfd 0 _ _ (by decide) (.refl _ _) hfin
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, hq⟩ := hE
  rcases hq with ⟨v, hv, -⟩ | ⟨_, _, _, _, _, h''⟩ | ⟨_, _, _, _, _, h''⟩
  · have : IsVal (K.plug (.app .unit (Val.inj₁ Val.unit).1)) := hv ▸ v.2
    simp only [K, BoCa.BoLo.Kont.plug] at this
    cases this.app_fun
  · exact absurd (pure_sep_iff.mp h'').1.2.2.1 (by simp [OpTabN.empty])
  · exact absurd (pure_sep_iff.mp h'').1.2.2.1 (by simp [OpTabN.empty])

/-- `kTy`'s value at the stuck thunk fails at every world `U` reaches the world with the key from. -/
theorem not_kTy_of_extR (x : LifeVar) (δ : LSub) {N α b : Life} (hNα : N < α) {m l' : Loc}
    (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b) (hcl : c l' = some α)
    {Θ : LocTy} (hE : Θ.ExtR (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') (ρb m b)) :
    ¬ vN (ℍ := ℍ) (kTy [] .unit .lin (bMut x) (.ret .unit)) (δ.extend x α) Θ 1 Val.unit
      (ρb m b) := by
  intro h
  exact not_kTy_at x δ hml c hcm hcl (h _ hE (Θ₁_ok x _ hNα l') c
    (consistentX_single_mut (consistentX_empty c) hcm) [])

/-! ### The world -/

/-- **The stop at the empty world owes the stuck `κ` nothing**: no `Mut` value exists there. -/
theorem kapRelN_world (x : LifeVar) (δ : LSub) (c : Loc → Option Life) (ls : List SRec) {m : Loc}
    {b : Life} :
    KapRelN (ℍ := ℍ) (LocTy.empty.view c)
      (opTableN (tabN (ℍ := ℍ) (CTy.effOf [] .unit) δ LocTy.empty c))
      (fun k _ v ρ => retN (ℍ := ℍ) (CTy.effOf [] .unit) δ LocTy.empty k v ρ)
      (entN .lin (bMut x) (fun k v ρ => vN (ℍ := ℍ) .unit δ LocTy.empty k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) (bMut x) δ LocTy.empty k v ρ ∧ ConsistentX c ρ)
        (finN (ℍ := ℍ) (.ret .unit) δ LocTy.empty c))
      none 2 ls Val.unit (ρb m b) := by
  unfold KapRelN
  refine ⟨(fun h => by cases h), fun ls' _ k' _ => ⟨fun w σ₁ σ₂ hB _ => ?_, fun hq => absurd rfl hq⟩⟩
  have hB' : vN (ℍ := ℍ) (bMut x) δ LocTy.empty k' w σ₁ := hB.1
  obtain ⟨β, _, b', _, ⟨l, _, _, _, _, _, _, _, hl, _⟩, -⟩ := hB'
  simp at hl

/-- **The world refutes Core's step**: at the empty world, the stop's view `c` and its list `ls`,
`KapRelN` holds of the stuck `κ` (`kapRelN_world`); `U` at `kTy` reaches the world with a key, at the
same view and list, where `κ` fails (`not_kTy_at`). -/
theorem not_kTy_world (x : LifeVar) (δ : LSub) {N α b : Life} (hNα : N < α) {m l' : Loc}
    (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b) (hcl : c l' = some α) :
    LocTy.empty.OK ∧ ConsistentX c (ρb m b) ∧
      KapRelN (ℍ := ℍ) (LocTy.empty.view c)
        (opTableN (tabN (ℍ := ℍ) (CTy.effOf [] .unit) (δ.extend x α) LocTy.empty c))
        (fun k _ v ρ => retN (ℍ := ℍ) (CTy.effOf [] .unit) (δ.extend x α) LocTy.empty k v ρ)
        (entN .lin (bMut x) (fun k v ρ => vN (ℍ := ℍ) .unit (δ.extend x α) LocTy.empty k v ρ)
          (fun k v ρ => vN (ℍ := ℍ) (bMut x) (δ.extend x α) LocTy.empty k v ρ ∧ ConsistentX c ρ)
          (finN (ℍ := ℍ) (.ret .unit) (δ.extend x α) LocTy.empty c))
        none 2 [] Val.unit (ρb m b) ∧
      LocTy.empty.ExtR (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') (ρb m b) ∧
      ¬ cN (ℍ := ℍ) (kTyC x) (δ.extend x α) (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') c 1 []
        Val.unit.1 (ρb m b) ∧
      ¬ vN (ℍ := ℍ) (kTy [] .unit .lin (bMut x) (.ret .unit)) (δ.extend x α) LocTy.empty 1
        Val.unit (ρb m b) :=
  have hE : LocTy.empty.ExtR (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') (ρb m b) :=
    (LocTy.extA_add (fun _ _ h => absurd rfl h) l' _).extR _
  ⟨LocTy.empty_ok, consistentX_single_mut (consistentX_empty c) hcm, kapRelN_world x _ c [], hE,
    not_kTy_at x δ hml c hcm hcl, not_kTy_of_extR x δ hNα hml c hcm hcl hE⟩

/-! ### The view -/

/-- **The stop at the world with the key `(ℓ′, α)`, at a view with no lifetime at `ℓ′`, owes the
stuck `κ` nothing**: a `Mut` answer at that world is at `ℓ′`, and the answer a row's table reads is
consistent with the run's view. -/
theorem kapRelN_view (x : LifeVar) (δ : LSub) (α : Life) {l' : Loc} (c : Loc → Option Life)
    (hcl : c l' = none) (ls : List SRec) {m : Loc} {b : Life} :
    KapRelN (ℍ := ℍ) ((Θ₁ (ℍ := ℍ) x δ α l').view c)
      (opTableN (tabN (ℍ := ℍ) (CTy.effOf [] .unit) δ (Θ₁ (ℍ := ℍ) x δ α l') c))
      (fun k _ v ρ => retN (ℍ := ℍ) (CTy.effOf [] .unit) δ (Θ₁ (ℍ := ℍ) x δ α l') k v ρ)
      (entN .lin (bMut x) (fun k v ρ => vN (ℍ := ℍ) .unit δ (Θ₁ (ℍ := ℍ) x δ α l') k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) (bMut x) δ (Θ₁ (ℍ := ℍ) x δ α l') k v ρ ∧ ConsistentX c ρ)
        (finN (ℍ := ℍ) (.ret .unit) δ (Θ₁ (ℍ := ℍ) x δ α l') c))
      none 2 ls Val.unit (ρb m b) := by
  unfold KapRelN
  refine ⟨(fun h => by cases h), fun ls' _ k' _ => ⟨fun w σ₁ σ₂ hB hc => ?_, fun hq => absurd rfl hq⟩⟩
  refine erwp_of_valid fun hv => ?_
  exfalso
  have hB' : vN (ℍ := ℍ) (bMut x) δ (Θ₁ (ℍ := ℍ) x δ α l') k' w σ₁ := hB.1
  have hBc : ConsistentX c σ₁ := hB.2
  obtain ⟨-, -, b', -, ⟨l, u, χ, hχ, j, hw, -, -, hl, rfl⟩, -⟩ := hB'
  have hll : l = l' := by
    by_contra hne
    rw [LocTy.add_other _ hne] at hl
    simp at hl
  subst hll
  have hv₁ := (ResU.Valid.split hc hv).2
  have := consistentX_get hBc hv₁ (ResU.single_get_self _ _) (CellU.kind_mutOf _ _ _ _ _ _)
  rw [hcl] at this
  cases this

/-- **The view refutes Core's step**: at the world with the key `(ℓ′, α)`, the stop's view `c₀`
with no lifetime at `ℓ′`, and its list `ls`, `KapRelN` holds of the stuck `κ` (`kapRelN_view`); `U`
at `kTy` reads `κ` at the same world and list at a view consistent with its share that puts `ℓ′` at
`α`, where `κ` fails (`not_kTy_at`). -/
theorem not_kTy_view (x : LifeVar) (δ : LSub) {N α b : Life} (hNα : N < α) {m l' : Loc}
    (hml : l' ≠ m) (c₀ c : Loc → Option Life) (hc₀m : c₀ m = some b) (hc₀l : c₀ l' = none)
    (hcm : c m = some b) (hcl : c l' = some α) :
    (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l').OK ∧ ConsistentX c₀ (ρb m b) ∧
      KapRelN (ℍ := ℍ) ((Θ₁ (ℍ := ℍ) x (δ.extend x α) α l').view c₀)
        (opTableN (tabN (ℍ := ℍ) (CTy.effOf [] .unit) (δ.extend x α)
          (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') c₀))
        (fun k _ v ρ => retN (ℍ := ℍ) (CTy.effOf [] .unit) (δ.extend x α)
          (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') k v ρ)
        (entN .lin (bMut x)
          (fun k v ρ => vN (ℍ := ℍ) .unit (δ.extend x α) (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') k v ρ)
          (fun k v ρ => vN (ℍ := ℍ) (bMut x) (δ.extend x α)
            (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') k v ρ ∧ ConsistentX c₀ ρ)
          (finN (ℍ := ℍ) (.ret .unit) (δ.extend x α) (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') c₀))
        none 2 [] Val.unit (ρb m b) ∧
      ConsistentX c (ρb m b) ∧
      ¬ cN (ℍ := ℍ) (kTyC x) (δ.extend x α) (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') c 1 []
        Val.unit.1 (ρb m b) ∧
      ¬ vN (ℍ := ℍ) (kTy [] .unit .lin (bMut x) (.ret .unit)) (δ.extend x α)
        (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') 1 Val.unit (ρb m b) :=
  ⟨Θ₁_ok x _ hNα l', consistentX_single_mut (consistentX_empty c₀) hc₀m,
    kapRelN_view x _ α c₀ hc₀l [], consistentX_single_mut (consistentX_empty c) hcm,
    not_kTy_at x δ hml c hcm hcl,
    not_kTy_of_extR x δ hNα hml c hcm hcl (LocTy.extR_refl _ _)⟩

/-- **Core's step does not hold at the chain.** The world configuration at `'x ↦ 1`, the share's
cell at `0` at the lifetime `2`, the key at `1` at the lifetime `1`, the stop's list `[]`. -/
theorem not_kapRelKTyN : ¬ KapRelKTyN (ℍ := ℍ) := by
  intro h
  let α : Life := OrderDual.toDual 1
  let b : Life := OrderDual.toDual 2
  have hbα : b < α := OrderDual.toDual_lt_toDual.mpr (by decide)
  let c : Loc → Option Life := fun y => if y = 0 then some b else if y = 1 then some α else none
  obtain ⟨-, -, hK, -, -, hn⟩ := not_kTy_world (ℍ := ℍ) 0 LSub.empty hbα (m := 0) (l' := 1)
    (by decide) c rfl rfl
  exact hn (h [] .unit .unit (bMut 0) .lin (.ret .unit) _ LocTy.empty c none 1 [] Val.unit
    (ρb 0 b) LocTy.empty_ok (consistentX_single_mut (consistentX_empty c) rfl) hK)

/-! ### Route 2 at the Mut Frame's fold -/

/-- The configuration of a Mut Frame's fold at the world: `ExtR` at the lender's share (the lent
cell folded to `own`) from `Θ` to `Θ′` gives `ExtR` at the borrowed continuation's share (the cell
`mut` at `A`) from the lend's world `Θ + (ℓ, A)` to `Θ′ + (ℓ, A)`. -/
def ExtRFoldTransfer : Prop :=
  ∀ (Θ Θ' : LocTy) (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) (v : Val),
    Θ.OK → Θ'.OK → Θ.Fresh A → Θ'.Fresh A → Θ.ExtR Θ' (ResU.single l (CellU.ownOf v)) →
    (Θ.add l A F).ExtR (Θ'.add l A F)
      (ResU.single l (CellU.mutOf A v PMap.empty (ResU.inStratum_empty A) (fun _ _ => True) trivial))

/-- **`ExtR` is not carried across a fold**: a key added above the lend's lifetime is admitted at the
lender's share, which holds no borrow cell, and refused at the borrowed continuation's share, whose
cell at `A` asks that nothing be added above `A`. -/
theorem not_extRFoldTransfer : ¬ ExtRFoldTransfer := by
  intro h
  let A : Life := OrderDual.toDual 1
  let β : Life := OrderDual.toDual 0
  have hAβ : A < β := OrderDual.toDual_lt_toDual.mpr (by decide)
  let G : Nat → Val → SPropS Loc Val β := fun _ _ _ => True
  have hG : DownFam β G := fun _ _ _ _ => trivial
  let Θ' : LocTy := LocTy.empty.add 1 β G
  have hfr : Θ'.Fresh A := LocTy.fresh_add (N := A) (fun _ _ h => absurd rfl h) le_rfl hAβ 1 G
  have hOK : Θ'.OK := ⟨LocTy.down_add LocTy.empty_down 1 hG, ⟨A, hfr⟩⟩
  let F : Nat → Val → SPropS Loc Val A := fun _ _ _ => True
  have hE : LocTy.empty.ExtR Θ' (ResU.single 0 (CellU.ownOf Val.unit)) :=
    ⟨fun _ _ _ hF _ => by simp at hF, fun _ hx _ => by simp at hx⟩
  have h' := (h LocTy.empty Θ' 0 A F Val.unit LocTy.empty_ok hOK (fun _ _ h => absurd rfl h) hfr
    hE).1 0 A F (LocTy.add_self _ _ _ _)
    ⟨0, _, ResU.single_get_self _ _, by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c,
      by rw [CellU.at_mutOf]⟩
  have h₁ := congrArg (fun Θ : LocTy => Θ 1 β) h'.2
  have hβA : β ≠ A := ne_of_gt hAβ
  simp only [LocTy.above_apply, if_pos hAβ, LocTy.add_keep _ _ _ _ hβA, Θ'] at h₁
  rw [LocTy.add_self] at h₁
  simp at h₁

end BoCa.Fig16.LogRel.Core.Chain.SI.Kappa835N

end
