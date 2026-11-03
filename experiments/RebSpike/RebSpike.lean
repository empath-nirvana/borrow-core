import Core.TreeLend

/-!
# Spike (#791): a reborrow at `twp`, and the world's template choice

Throwaway. Question: can a run at `twp` take a reborrow of an escrow's contents (`TWNT.reb`) with
the relation as it stands?

`TWNT.reb` asks the image to be the canonical one at the world's template choice,
`c = canonTc w₀.tc r β`, and to be typed at `Imm̲ 'β T`. What is shown here:

* **`twp` does not read its own world's choice** (`twp_tc_irrel`): `twp … w …` and
  `twp … ⟨w.P, w.Θ, tc⟩ …` are the same proposition, for every `tc`. `TWd.Ext` reads `K` and `Θ`
  only, so a run's start world `w₀` carries an arbitrary choice.
* **A start world at the empty choice** (`tc0`): an `imm` lend of `ℓ ↦ own(loc m)` with the
  non-empty escrow `m ↦ own(())`, open, meets `RecInv` and `WInv` at `⟨P, Θ, tc0⟩`
  (`config_tc0`). There the canonical image of the record is `∅` at every `β` (`canonTc_tc0`), and
  `∅` is not typed at `Imm̲ 'β (ref 1) = Imm @β 1` (`reb_untyped_tc0`): `TWNT.reb` does not apply
  to the record, at any `β`, any lent location, any world holding it.
* **No re-reading changes it** (`tcCarried_pins`): a choice carried from `tc0` along any
  re-reading (`TWNT.reread`'s `TcCarried`) is `∅` at the record's re-read argument, so
  `twp_extend` cannot move the run to a world where the reborrow applies.
* At the `Classical` choice the same configuration takes the reborrow (`twnt_config`,
  `World/FdEsc.lean`).

**Not shown**: that no `TWNT` derivation at all reaches `ℓ ↦ imm({α}, loc m, R) ● m ↦ imm({β},(),∅)`
at `tc0`. That needs `TemplAtT` (`World/Templ.lean`) to be an invariant of `TWNT`; only its
re-reading (`templAt_reread`) is proved.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp.RebSpike
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### `twp` does not read its world's choice -/

/-- The world `w` at the choice `tc`. -/
def withTc (w : TWd) (tc : TChoice w.K) : TWd := ⟨w.P, w.Θ, tc⟩

/-- **`twp` at `w` is `twp` at `w` with any other template choice.** -/
theorem twp_tc_irrel {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} (tc : TChoice w.K)
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : BoCa.Expr} {ρ : TRes w.K} :
    twp (ℍ := ℍ) F Q n w ls O e ρ ↔ twp (ℍ := ℍ) F Q n (withTc w tc) ls O e ρ := Iff.rfl

/-- Every world extends to itself at any other choice, carrying anything. -/
theorem ext_withTc (w : TWd) (tc : TChoice w.K) (ρ : TRes w.K) : w.Ext (withTc w tc) ρ :=
  TWd.Ext.refl w ρ

/-! ### The empty choice -/

variable {K : WCactus}

/-- The empty template choice. -/
def tc0 : TChoice K := fun _ _ _ => PMap.empty

theorem relResT_empty (R : TRes K) (β : Life) : relResT R β PMap.empty = PMap.empty :=
  PMap.ext fun m => by rw [relResT_get]; simp

/-- At `tc0` every canonical image is `∅`. -/
theorem canonTc_tc0 (r : FrameRecT K) (β : Life) : canonTc tc0 r β = PMap.empty :=
  relResT_empty _ _

/-- `∅` is not typed at `Imm @β 1`. -/
theorem reb_untyped_tc0 (Θ : CodeTy) (β : Life) (l m : BoCa.Loc) :
    ¬ (((recE (K := K) l m).T.immReborrow β).interp Θ).P K (recE (K := K) l m).v
      (canonTc tc0 (recE l m) β) := by
  rw [canonTc_tc0]
  rintro ⟨x, i, -, h, -⟩
  have := congrArg (fun ρ : TRes K => ρ.get x) h
  simp [PMap.sng_get] at this

/-- **`TWNT.reb` never fires at the record at `tc0`**: its premises at `recE l m` are
contradictory, at every world, lent location and lifetime. -/
theorem no_reb_tc0 {Θ : CodeTy} {W W' c : TRes K} {ps rs : List (FrameRecT K)} {l m le : BoCa.Loc}
    {s : TSet} {β : Life} {hs : (recE (K := K) l m).R.InStratum s}
    (_hT : TWNT K Θ tc0 W ps rs) (_hr : recE l m ∈ rs)
    (_hle : W.get le = some (CellUT.immOf s (recE (K := K) l m).v (recE (K := K) l m).R hs))
    (_hreb : ResUT.Reb β (recE (K := K) l m).R c)
    (hty : (((recE (K := K) l m).T.immReborrow β).interp Θ).P K (recE (K := K) l m).v c)
    (hc : c = canonTc tc0 (recE (K := K) l m) β) (_hW : ResUT.CompS W c W') : False := by
  subst hc; exact reb_untyped_tc0 Θ β l m hty

/-- **A choice carried from `tc0` is `∅` at the record's argument**, along every re-reading. -/
theorem tcCarried_pins {K' : WCactus} {Θ' : CodeTy} {W : TRes K} {rs : List (FrameRecT K)}
    {tc' : TChoice K'} (h : TcCarried Θ' W rs tc0 tc') {r : FrameRecT K} (hr : r ∈ rs)
    {R' : TRes K'} (hR : RR (sem Θ') r.R R') : tc' R' r.T r.v = PMap.empty :=
  RR.of_empty (h r.R r.T r.v (Or.inl ⟨r, hr, rfl, rfl, rfl⟩) R' hR)

/-! ### The configuration: an open lend with a non-empty escrow -/

/-- The lent location's cell `ℓ ↦ imm({α}, loc m, m ↦ own(()))`. -/
abbrev lendW (α : Life) (l m : BoCa.Loc) : TRes K := ResUT.single l (lendCell α m)

/-- **The lend is a `TWNT` world at every choice**: `m ↦ own(())`, `ℓ ↦ own(loc m)` allocated,
`ℓ` lent `imm` at `α`. No step reads the choice. -/
theorem twnt_lend (Θ : CodeTy) (tc : TChoice K) (α : Life) {l m : BoCa.Loc} (hlm : l ≠ m) :
    TWNT K Θ tc (lendW α l m) [recE l m] [recE l m] ∧ ResUT.Valid (lendW (K := K) α l m) := by
  have h1 : TWNT K Θ tc (escR m) [] [] :=
    .alloc (μ := fun _ => none) .empty ⟨_, flat_empty, fun x => by simp⟩ rfl
      (ResUT.comp_empty_left _) (ResUT.valid_single_own m _)
  obtain ⟨W2, hW2⟩ := single_compS (K := K) hlm.symm (CellUT.ownOf BoCa.Val.unit)
    (CellUT.ownOf (BoCa.Val.loc m))
  have hv2 := valid_two_own (K := K) BoCa.Val.unit (BoCa.Val.loc m) hW2
  have h2 : TWNT K Θ tc W2 [] [] :=
    .alloc (μ := fun x => if x = m then some BoCa.Val.unit else none) h1
      ⟨_, ResUT.flat_single_own m _, fun x => by
        rw [PMap.sng_get]; by_cases hx : x = m <;> simp [hx]⟩ (if_neg hlm) hW2 hv2.1
  have hv3 : ResUT.Valid (lendW (K := K) α l m) := valid_single_imm _ hW2 hv2.1
  refine ⟨?_, hv3⟩
  exact TWNT.immFrame (W := W2) (X := W2) (Z := PMap.empty) (R := escR m) (ds := [])
    (KTy.ref KTy.unit) (own_inStratum (TSet.single α) m BoCa.Val.unit) h2 (ResUT.CompS.comm hW2)
    (ResUT.compS_empty_right _) (escR_typed Θ m) (ResUT.compS_empty_right _) hv3
    (fun d => ⟨fun h => by simp at h, fun h => (recE_no_desc l m d h).elim⟩)

theorem descRT_recE {l m : BoCa.Loc} {d : FrameRecT K} (h : DescRT (recE l m) d) :
    d = recE l m := by
  obtain ⟨p, hp⟩ := h
  cases p with
  | nil => cases hp; rfl
  | cons x p => exact (recE_no_desc l m d ⟨_, List.cons_ne_nil _ _, hp⟩).elim

/-- The record's frame is at `α`: the lend cell's lifetime; its lineage location `m` is `own` in the
aliasable walk. -/
theorem frameLife_lend (α : Life) {l m : BoCa.Loc} (hlm : l ≠ m) :
    FrameLifeT K (lendW α l m) (recE l m) α := by
  refine ⟨fun a ha ζ t eζ ht y hy => ?_, fun a ha m' hm' ψ s eψ hs x hx => ?_⟩
  · rw [show (recE (K := K) l m).le = l from rfl, (ag_lend hlm ha).1] at eζ
    cases eζ
    erw [CellUT.lsOfI_immOf, Option.some.injEq] at ht
    subst ht
    simpa using hy
  · obtain ⟨d, hd, ζ, eζ, -⟩ := hm'
    obtain rfl := descRT_recE hd
    obtain ⟨rfl, -⟩ := ResUT.single_get_eq_some eζ
    rw [(ag_lend hlm ha).2] at eψ
    cases eψ
    simp at hs

theorem cov_lend (Θ : CodeTy) (α : Life) (l m : BoCa.Loc) :
    CovR (sem Θ) K (lendW α l m) := by
  intro x ψ e
  obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
  refine Cov.immOf_iff.mpr fun k χ ek => ?_
  obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some ek
  exact .own _ _

/-- **The configuration at the empty choice**: at `⟨P, Θ, tc0⟩` the open lend meets `RecInv` and
`WInv` (a start world `twp` quantifies over); its record's canonical image is untyped at every
`β`, so `TWNT.reb` does not apply to it; and every choice carried from `tc0` keeps the record's
template `∅`. -/
theorem config_tc0 (P : ParentFn) (Θ : CodeTy) (α : Life) {l m : BoCa.Loc} (hlm : l ≠ m) :
    let w : TWd := ⟨P, Θ, tc0⟩
    ∃ μ : BoCa.BoLo.Heap, RecInv w (lendW α l m) [recE l m] [(recE l m, α)] ∧
      WInv w (lendW α l m) μ ∧ FinDom μ ∧
      (∀ β, ¬ (((recE (K := w.K) l m).T.immReborrow β).interp w.Θ).P w.K (recE (K := w.K) l m).v
        (canonTc w.tc (recE l m) β)) ∧
      (∀ (K' : WCactus) (Θ' : CodeTy) (tc' : TChoice K'),
        TcCarried Θ' (lendW (K := w.K) α l m) [recE l m] w.tc tc' →
        ∀ R' : TRes K', RR (sem Θ') (recE (K := w.K) l m).R R' →
          tc' R' (recE (K := w.K) l m).T (recE (K := w.K) l m).v = PMap.empty) := by
  intro w
  obtain ⟨hT, hv⟩ := twnt_lend (K := w.K) Θ tc0 α hlm
  obtain ⟨σ, hσ⟩ := hv
  refine ⟨fun x => (σ.get x).map CellUT.erase, ⟨hT, fun x hx => ?_⟩,
    ⟨cov_lend Θ α l m, σ, hσ, fun _ => rfl⟩, ?_, fun β => reb_untyped_tc0 Θ β l m,
    fun K' Θ' tc' h R' hR => tcCarried_pins h List.mem_cons_self hR⟩
  · simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨recE l m, List.mem_cons_self, ⟨[], .nil _⟩, frameLife_lend α hlm⟩
  · obtain ⟨d, hd⟩ := σ.finite
    exact ⟨d, fun x hx => hd x fun e => hx (by simp [e])⟩

/-- **The contrast**: at the `Classical` choice the same lend takes the reborrow at `β ⊏ α`
(`twnt_config`): the world `ℓ ↦ imm({α}, loc m, R) ● m ↦ imm({β}, (), ∅)` is a `TWNT` world. -/
theorem config_tmpl (Θ : CodeTy) {α β : Life} (hβα : K.lt β α) {l m : BoCa.Loc} (hlm : l ≠ m) :
    ∃ W, ResUT.CompS (lendW (K := K) α l m) (viewRes β m) W ∧
      TWNT K Θ (tmplT K Θ) W [recE l m] [recE l m] :=
  twnt_config Θ hβα hlm

end BoCa.Fig16.Tree.Wp.RebSpike

end
