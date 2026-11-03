import Support.Model.Tree.World.InvUses
import Support.Model.Tree.World.ExtF
import Support.Model.Tree.World.Branches

/-!
# The end of an `imm` lend whose escrow holds an `own` cell

`TWNT.immEnd` turns `ℓ ↦ imm({α}, v, R)` back into `ℓ ↦ own(v) ● R` beside the rest `Y` of the
world, and asks `✓(ℓ ↦ own(v) ● R ● Y)`.

**The configuration** (`immEnd_esc_config`). `R = m ↦ own(())`, `v = loc m`, the record at
`ref 1`, and a reborrow of the record at `β ⊏ α` (`TWNT.reb`, its image the canonical one,
`m ↦ imm({β}, (), ∅)`). The world `W = ℓ ↦ imm({α}, loc m, R) ● m ↦ imm({β}, (), ∅)` is a `TWNT`
world, so every invariant of `TWNT` holds of it. Split at the record, the rest is the image
`Y = m ↦ imm({β}, (), ∅)`. Its flattening holds nothing at `ℓ`: the join's frame condition at
`ℓ` (`joinFd`, `SI/CaptureScope.lean`) holds of `Y`. Yet `ℓ ↦ own(loc m) ● R ● Y` is undefined:
`own(())` and `imm({β}, (), ∅)` meet at `m`.

So the frame condition at the lent location does not give `immEnd`'s `✓`, and no invariant of the
world does either: the configuration is a `TWNT` world. It is on the printed chain as well
(`immEnd_esc_chain`). What excludes it in the printed run is who
holds `Y`. In 6.64 the run's own resource outlives `α` (H24, `@ρ′ ⊐ α`; the image is at `β ⊏ α`)
and the frame is fixed for the run (6.38's H6, read at the lend). Over the tree the frame is the
other branches, which change while the lending segment is stopped.

**What supplies it** (`immEnd_valid_of_fdEsc`): the frame condition read at the lent location
and at every location of `ex(R)`, the escrow's exclusive part at any depth. With it,
`✓(ℓ ↦ own(v) ● R ● Y)` follows from `✓(ℓ ↦ imm(s, v, R) ● Y)`, along 6.38's proof: the
flattening splits into the exclusive parts and the aliasable parts; every disjointness but the
one between `ex(R) ● ℓ ↦ own(v)` and `Y`'s flattening is read off `✓W`, and that one is the
condition. The lender's piece is valid at every record proper (`TWNT.lenderValid`). Where the
escrow has no exclusive part the condition is the one at `ℓ` (`fdEsc_iff_of_ex_empty`).
`JoinReadyEscT` is `JoinReady` at those locations; `joinReadyEsc_fdEsc` gives the condition from
it, as `joinReady_fd` gives `joinFd`.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-! ### The cells -/

theorem own_inStratum (S : TSet) (l : BoCa.Loc) (v : BoCa.Val) :
    (ResUT.single l (CellUT.ownOf v) : TRes K).InStratum S :=
  ResUT.inStratum_single_own S l v

theorem emptyT_inStratum (S : TSet) : ResUT.InStratum S (PMap.empty : TRes K) :=
  ResUT.inStratum_empty S

/-- The escrow `R = m ↦ own(())`. -/
def escR (m : BoCa.Loc) : TRes K := ResUT.single m (CellUT.ownOf BoCa.Val.unit)

/-- The lender's cell `ℓ ↦ imm({α}, loc m, R)`. -/
def lendCell (α : Life) (m : BoCa.Loc) : TCell K :=
  CellUT.immOf (TSet.single α) (BoCa.Val.loc m) (escR m) (own_inStratum _ _ _)

/-- The image's cell `m ↦ imm({β}, (), ∅)`. -/
def viewCell (β : Life) : TCell K :=
  CellUT.immOf (TSet.single β) BoCa.Val.unit PMap.empty (emptyT_inStratum _)

/-- The image `m ↦ imm({β}, (), ∅)`. -/
def viewRes (β : Life) (m : BoCa.Loc) : TRes K := ResUT.single m (viewCell β)


theorem single_disjoint {l m : BoCa.Loc} (h : l ≠ m) (ψ χ : TCell K) :
    ∀ x, (ResUT.single l ψ).get x = none ∨ (ResUT.single m χ).get x = none := by
  intro x
  by_cases hx : x = l
  · subst hx; exact Or.inr (ResUT.single_get_ne _ h)
  · exact Or.inl (ResUT.single_get_ne _ hx)

/-- Two singletons at distinct locations compose. -/
theorem single_compS {l m : BoCa.Loc} (h : l ≠ m) (ψ χ : TCell K) :
    ∃ W, ResUT.CompS (ResUT.single l ψ) (ResUT.single m χ) W :=
  (ResUT.compS_defined_iff _ _).mpr (ResUT.Compat.of_disjoint (single_disjoint h ψ χ))

/-- A world of `imm` cells has `ex = ∅`. -/
theorem exST_all_imm {ρ : TRes K} (h : ∀ l ψ, ρ.get l = some ψ → ψ.kind = Kind.imm) :
    ExST ρ PMap.empty := ExWT.empty_of_all_imm h

/-- `✓` of two `own` singletons at distinct locations. -/
theorem valid_two_own {l m : BoCa.Loc} (v w : BoCa.Val) {W : TRes K}
    (hW : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) (ResUT.single m (CellUT.ownOf w)) W) :
    ResUT.Valid W ∧ ResUT.Flat W W := by
  have he : ExST W W := (ExST.split hW).mpr ⟨_, _, ExWT.single_own l v, ExWT.single_own m w, hW⟩
  have ha : AgWT W PMap.empty :=
    (AgWT.split hW).mpr ⟨_, _, AgWT.single_own l v, AgWT.single_own m w,
      ResUT.compR_empty_right _⟩
  have hf : ResUT.Flat W W := ⟨W, PMap.empty, he, ha, ResUT.compS_empty_right W⟩
  exact ⟨⟨W, hf⟩, hf⟩

/-- `✓(ℓ ↦ imm(s, v, ρ_v))` from `✓(ρ_v ● ℓ ↦ own(v))`, by 6.34 against `∅`. -/
theorem valid_single_imm {l : BoCa.Loc} {s : TSet} {v : BoCa.Val} {ρv X : TRes K}
    (hs : ρv.InStratum s) (hX : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) X)
    (hv : ResUT.Valid X) : ResUT.Valid (ResUT.single l (CellUT.immOf s v ρv hs)) := by
  obtain ⟨-, y, hy, hvy⟩ := ResUT.six34 (ρ := PMap.empty) (hs := hs) hX
    (ResUT.hash_symm (ResUT.hash_empty_right hv))
  rwa [← ResUT.CompS.functional hy (ResUT.comp_empty_left _)]


/-! ### The aliasable walks of the two cells -/

/-- `ag(ℓ ↦ imm({α}, loc m, R))` holds the lender's cell at `ℓ` and `own(())` at `m`. -/
theorem ag_lend {α : Life} {l m : BoCa.Loc} (hlm : l ≠ m) {a : TRes K}
    (h : AgWT (ResUT.single l (lendCell α m)) a) :
    a.get l = some (lendCell α m) ∧ a.get m = some (CellUT.ownOf BoCa.Val.unit) := by
  obtain ⟨e, a', p, he, ha', hp, hc⟩ := AgWT.single_imm_inv h
  obtain rfl : e = escR m := ExRT.functional he (ExWT.single_own m _)
  obtain rfl : a' = PMap.empty := AgWT.functional ha' (AgWT.single_own m _)
  obtain rfl : escR m = p := ResUT.eq_of_comp_empty_right hp
  refine ⟨(ResUT.Comp.get_of_right_none hc (ResUT.single_get_ne _ hlm)).trans
      (ResUT.single_get_self _ _), ?_⟩
  exact (ResUT.Comp.get_of_left_none hc (ResUT.single_get_ne _ hlm.symm)).trans
    (ResUT.single_get_self _ _)

/-- `ag(m ↦ imm({β}, (), ∅)) = m ↦ imm({β}, (), ∅)`. -/
theorem ag_view {β : Life} {m : BoCa.Loc} {a : TRes K} (h : AgWT (viewRes β m) a) :
    a = viewRes β m := by
  obtain ⟨e, a', p, he, ha', hp, hc⟩ := AgWT.single_imm_inv (χ := PMap.empty) h
  obtain rfl : e = PMap.empty := ExRT.functional he (ExWT.empty_of_all_imm (fun _ _ e => by simp at e))
  obtain rfl : a' = PMap.empty := AgWT.functional ha' BoCa.Fig16.Tree.agW_empty
  obtain rfl : PMap.empty = p := ResUT.eq_of_comp_empty_right hp
  exact (ResUT.eq_of_comp_empty_right hc).symm

theorem valid_view (β : Life) (m : BoCa.Loc) : ResUT.Valid (viewRes (K := K) β m) :=
  valid_single_imm (emptyT_inStratum _) (ResUT.comp_empty_left _) (ResUT.valid_single_own m _)

/-- The flattening of the image is the image: nothing at `ℓ ≠ m`. -/
theorem flat_view {β : Life} {m : BoCa.Loc} {τ : TRes K} (h : ResUT.Flat (viewRes β m) τ) :
    τ = viewRes β m := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  obtain rfl : e = PMap.empty := ExST.functional he (exST_all_imm fun x ψ e => by
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e; exact CellUT.kind_immOf _ _ _ _)
  obtain rfl := ag_view ha
  exact ResUT.CompS.functional hc (ResUT.comp_empty_left _)

/-! ### The image at `β` -/

theorem escR_del (m : BoCa.Loc) : (escR (K := K) m).del m = PMap.empty :=
  PMap.ext fun x => by
    by_cases hx : x = m
    · subst hx; simp
    · rw [ResUT.del_get_ne _ hx]; exact ResUT.single_get_ne _ hx

/-- `m ↦ imm({β}, (), ∅) ∈ reb_β(m ↦ own(()))`. -/
theorem view_reb (β : Life) (m : BoCa.Loc) : ResUT.Reb β (escR (K := K) m) (viewRes β m) := by
  refine ⟨own_inStratum _ _ _, [(m, escR m)], escR m, ⟨List.nodup_singleton m, fun x => ?_⟩,
    (BigCompT.singleton_iff ResUT.compLawsS).mpr rfl, ⟨PMap.empty, ResUT.compS_empty_right _⟩,
    ?_⟩
  · simp only [List.map, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨_, ResUT.single_get_self _ _⟩
    · rintro ⟨ψ, e⟩; exact (ResUT.single_get_eq_some e).1
  · intro x p hx
    simp only [List.mem_singleton, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨⟨_, ResUT.single_get_self _ _⟩, fun v e => ?_, fun b _ v χ hb P hw e => ?_,
      fun s v χ h e => ?_⟩
    · rw [escR, ResUT.single_get_self] at e
      cases e
      refine ⟨by rw [escR_del]; exact emptyT_inStratum _, ?_⟩
      rw [viewRes, ResUT.single_get_self]
      exact congrArg some (CellUT.immOf_congr rfl rfl (escR_del x).symm _ _)
    · rw [escR, ResUT.single_get_self] at e
      exact absurd (Option.some.inj e) (CellUT.ownOf_ne_mutOf)
    · rw [escR, ResUT.single_get_self] at e
      exact absurd (Option.some.inj e) (CellUT.ownOf_ne_immOf)

/-- The image is typed at `Imm̲ 'β (ref 1) = Imm @β 1`. -/
theorem view_typed (Θ : CodeTy) (β : Life) (m : BoCa.Loc) :
    (((KTy.ref KTy.unit).immReborrow β).interp Θ).P K (BoCa.Val.loc m) (viewRes β m) :=
  ⟨m, ⟨TSet.single β, BoCa.Val.unit, ResST.toRes ⟨PMap.empty, emptyT_inStratum _⟩⟩, rfl, rfl,
    fun x hx => by
      simp only [TSet.single_set, Finset.mem_singleton] at hx
      subst hx; exact K.refl _,
    rfl, ResST.toU_toRes _⟩

theorem view_cov (Θ : CodeTy) (β : Life) (m : BoCa.Loc) : CovR (sem Θ) K (viewRes β m) := by
  intro x ψ e
  obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
  refine .imm _ _ fun k χ ek => ?_
  change (viewCell (K := K) β).wit.get k = some χ at ek
  rw [viewCell, CellUT.wit_immOf] at ek
  simp at ek

/-- **The canonical image at `β` is `m ↦ imm({β}, (), ∅)`**: every template of the record is one
`imm` cell at `m` holding `()` over `∅`, and `relRes` re-takes it at `{β}`. -/
theorem canonT_view (Θ : CodeTy) (β : Life) (l m : BoCa.Loc) :
    canonT K Θ ⟨l, BoCa.Val.loc m, escR m, KTy.ref KTy.unit⟩ β = viewRes β m := by
  have hex : ∃ c, TmplSpecT K Θ (escR m) (KTy.ref KTy.unit) (BoCa.Val.loc m) c :=
    ⟨viewRes β m, β, view_reb β m, view_typed Θ β m, ⟨_, (agW_of_valid (valid_view β m)).choose_spec⟩,
      view_cov Θ β m⟩
  obtain ⟨β₀, -, ⟨m', i, hv, htm, -, hiv, hir⟩, -, -⟩ := tmplT_spec hex
  cases hv
  refine PMap.ext fun x => ?_
  rw [canonT, relResT_get, tmplR]
  change ((tmplT K Θ (escR m) (KTy.ref KTy.unit) (BoCa.Val.loc m)).get x).map _ = _
  rw [htm, PMap.sng_get, viewRes, PMap.sng_get]
  by_cases hx : x = m
  · subst hx
    simp only [if_true, Option.map_some]
    congr 1
    unfold relCellT
    have hw : (CellUT.imm i : TCell K).wit = PMap.empty := hir
    rw [dif_pos ⟨rfl, ⟨_, ResUT.single_get_self _ _, by simp⟩, by
      rw [hw]; exact emptyT_inStratum _⟩]
    exact CellUT.immOf_congr rfl hiv hw _ _
  · simp [hx]


/-! ### The world -/

/-- The record: `ℓ`, `loc m`, `R`, `ref 1`. -/
def recE (l m : BoCa.Loc) : FrameRecT K := ⟨l, BoCa.Val.loc m, escR m, KTy.ref KTy.unit⟩

/-- `R ∈ ⟦ref 1⟧` at `loc m`. -/
theorem escR_typed (Θ : CodeTy) (m : BoCa.Loc) :
    ((KTy.ref KTy.unit).interp Θ).P K (BoCa.Val.loc m) (escR m) :=
  ⟨m, BoCa.Val.unit, PMap.empty, rfl, rfl,
    PMap.ext fun x => by
      rw [escR, PMap.ins_get, PMap.sng_get]; by_cases hx : x = m <;> simp [hx]; rfl, rfl, rfl⟩

/-- The record has no sub-records: `ref 1` has no `Mut` position. -/
theorem recE_no_desc (l m : BoCa.Loc) (d : FrameRecT K) : ¬ DescT (recE l m) d := by
  rintro ⟨p, hp, h⟩
  cases h with
  | nil => exact hp rfl
  | cons hs _ =>
      obtain ⟨hg, -⟩ := hs
      change GPosT (escR m) (KTy.ref KTy.unit) (BoCa.Val.loc m) _ _ at hg
      cases hg with
      | here hm => cases hm
      | step hr _ hg' =>
          cases hr
          cases hg' with
          | here hm => cases hm
          | step hr' _ _ => cases hr'

/-- `✓(ℓ ↦ imm({α}, loc m, R) ● m ↦ imm({β}, (), ∅))`: `ex = ∅`; `ag` is `ℓ ↦ imm({α}, …)`
beside `own(()) ○ imm({β}, (), ∅) = imm({β}, (), ∅)` at `m`. -/
theorem valid_W4 {α β : Life} {l m : BoCa.Loc} (hlm : l ≠ m) {W : TRes K}
    (hv3 : ResUT.Valid (ResUT.single l (lendCell (K := K) α m)))
    (hW : ResUT.CompS (ResUT.single l (lendCell α m)) (viewRes β m) W) : ResUT.Valid W := by
  obtain ⟨a₃, ha₃⟩ := agW_of_valid hv3
  obtain ⟨ac, hac⟩ := agW_of_valid (valid_view (K := K) β m)
  obtain rfl := ag_view hac
  have hm₃ := (ag_lend hlm ha₃).2
  have hcR : ResUT.CompatR a₃ (viewRes β m) := by
    intro x ψ₁ ψ₂ e₁ e₂
    obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e₂
    rw [hm₃] at e₁; cases e₁
    exact ⟨_, CellUT.CompR.ownImm _ _ _ _⟩
  obtain ⟨a, ha⟩ := (ResUT.compR_defined_iff _ _).mpr hcR
  have hag : AgWT W a := (AgWT.split hW).mpr ⟨_, _, ha₃, hac, ha⟩
  have hex : ExST W PMap.empty := exST_all_imm fun x ψ e => by
    rcases compS_back hW e with ⟨χ, eχ, kχ, -⟩ | ⟨χ, eχ, kχ, -⟩ <;>
    · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some eχ
      rw [← kχ]; exact CellUT.kind_immOf _ _ _ _
  exact ⟨a, PMap.empty, a, hex, hag, ResUT.comp_empty_left _⟩

/-- **The configuration is a `TWNT` world**: `m ↦ own(())` and `ℓ ↦ own(loc m)` allocated, `ℓ`
lent `imm` at `α` (the record at `ref 1`), the record reborrowed at `β ⊏ α` with its canonical
image. -/
theorem twnt_config (Θ : CodeTy) {α β : Life} (hβα : K.lt β α) {l m : BoCa.Loc} (hlm : l ≠ m) :
    ∃ W, ResUT.CompS (ResUT.single l (lendCell α m)) (viewRes β m) W ∧
      TWNT K Θ (tmplT K Θ) W [recE l m] [recE l m] := by
  -- `m ↦ own(())`
  have h1 : TWNT K Θ (tmplT K Θ) (escR m) [] [] :=
    .alloc (μ := fun _ => none) .empty ⟨_, flat_empty, fun x => by simp⟩ rfl
      (ResUT.comp_empty_left _) (ResUT.valid_single_own m _)
  -- `ℓ ↦ own(loc m)`
  obtain ⟨W2, hW2⟩ := single_compS (K := K) hlm.symm (CellUT.ownOf BoCa.Val.unit)
    (CellUT.ownOf (BoCa.Val.loc m))
  have hv2 := valid_two_own (K := K) BoCa.Val.unit (BoCa.Val.loc m) hW2
  have h2 : TWNT K Θ (tmplT K Θ) W2 [] [] :=
    .alloc (μ := fun x => if x = m then some BoCa.Val.unit else none) h1
      ⟨_, ResUT.flat_single_own m _, fun x => by
        rw [PMap.sng_get]; by_cases hx : x = m <;> simp [hx]⟩ (if_neg hlm) hW2 hv2.1
  -- the `imm` lend at `α`
  have hv3 : ResUT.Valid (ResUT.single l (lendCell (K := K) α m)) :=
    valid_single_imm _ hW2 hv2.1
  have h3 : TWNT K Θ (tmplT K Θ) (ResUT.single l (lendCell α m)) [recE l m] [recE l m] := by
    have hX : ResUT.CompS (ResUT.single l (CellUT.ownOf (BoCa.Val.loc m))) (escR m) W2 :=
      ResUT.CompS.comm hW2
    have := TWNT.immFrame (W := W2) (X := W2) (Z := PMap.empty) (R := escR m) (ds := [])
      (KTy.ref KTy.unit) (own_inStratum (TSet.single α) m BoCa.Val.unit) h2 hX
      (ResUT.compS_empty_right _) (escR_typed Θ m) (ResUT.compS_empty_right _) hv3
      (fun d => ⟨fun h => by simp at h, fun h => (recE_no_desc l m d h).elim⟩)
    exact this
  -- the reborrow at `β`
  obtain ⟨W4, hW4⟩ := single_compS (K := K) hlm (lendCell α m) (viewCell β)
  refine ⟨W4, hW4, ?_⟩
  refine TWNT.reb (recE l m) (le := l) (s := TSet.single α) (hs := own_inStratum _ _ _) h3
    List.mem_cons_self (ResUT.single_get_self _ _) (view_reb β m) (view_typed Θ β m) ?_
    (canonT_view Θ β l m).symm hW4 (valid_W4 hlm hv3 hW4)
  -- `RebRecLe`: the frame's lifetime is `α`, read off `ag` at `ℓ`
  intro p hp α' hfl _
  simp only [List.mem_singleton] at hp
  subst hp
  obtain ⟨a₃, ha₃⟩ := agW_of_valid hv3
  have hα := hfl.1 a₃ ha₃ _ _ (ag_lend hlm ha₃).1 (CellUT.lsOfI_immOf _ _ _ _) α (by simp)
  subst hα
  exact hβα.le

/-! ### The end of the lend -/

/-- **The end of the lend at the configuration.** The world is a `TWNT` world holding the record
proper `p = (ℓ, loc m, R, ref 1)`; split at `p`'s cell, the rest `Y` is the image; `Y`'s
flattening holds nothing at `ℓ` (`joinFd` at `ℓ`); and `ℓ ↦ own(loc m) ● R` does not compose
with `Y`, so `TWNT.immEnd` has no end world. -/
theorem immEnd_esc_config (Θ : CodeTy) {α β : Life} (hβα : K.lt β α) {l m : BoCa.Loc}
    (hlm : l ≠ m) :
    ∃ W, TWNT K Θ (tmplT K Θ) W [recE l m] [recE l m] ∧
      ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) (recE (K := K) l m).v (recE l m).R
        (own_inStratum _ _ _))) (viewRes β m) W ∧
      (∀ τ, ResUT.Flat (viewRes (K := K) β m) τ → τ.get l = none) ∧
      ∀ X' : TRes K, ResUT.CompS (ResUT.single l (CellUT.ownOf (recE (K := K) l m).v)) (recE l m).R X' →
        ¬ ∃ W', ResUT.CompS X' (viewRes β m) W' := by
  obtain ⟨W, hW, hT⟩ := twnt_config Θ hβα hlm
  refine ⟨W, hT, hW, fun τ hτ => by rw [flat_view hτ]; exact ResUT.single_get_ne _ hlm, ?_⟩
  rintro X' hX' ⟨W', hW'⟩
  have eX : X'.get m = some (CellUT.ownOf BoCa.Val.unit) :=
    (ResUT.Comp.get_of_left_none hX' (ResUT.single_get_ne _ hlm.symm)).trans
      (ResUT.single_get_self _ _)
  have hc := hW'.1 m _ _ eX (ResUT.single_get_self _ _)
  exact absurd (CellUT.compatS_iff.mp hc).1 (by simp)


/-- **The same configuration on the printed chain** (`β = 2 ⊏ α = 1`): the record, the reborrow
and the end are the printed ones; what is not printed is a frame holding the image. -/
theorem immEnd_esc_chain (Θ : CodeTy) :
    ∃ W, TWNT WCactus.chain Θ (tmplT WCactus.chain Θ) W [recE 1 2] [recE 1 2] ∧
      ResUT.CompS (ResUT.single 1 (CellUT.immOf (TSet.single (OrderDual.toDual 1))
        (recE (K := WCactus.chain) 1 2).v (recE 1 2).R (own_inStratum _ _ _)))
        (viewRes (OrderDual.toDual 2) 2) W ∧
      (∀ τ, ResUT.Flat (viewRes (K := WCactus.chain) (OrderDual.toDual 2) 2) τ → τ.get 1 = none) ∧
      ∀ X' : TRes WCactus.chain, ResUT.CompS (ResUT.single 1
          (CellUT.ownOf (recE (K := WCactus.chain) 1 2).v)) (recE 1 2).R X' →
        ¬ ∃ W', ResUT.CompS X' (viewRes (OrderDual.toDual 2) 2) W' :=
  immEnd_esc_config Θ ((WCactus.chain_lt _ _).mpr (by decide)) (by decide)

/-! ### What supplies `immEnd`'s `✓` -/

theorem none_of_comp_none_left {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    {a b c : TRes K} (h : ResUT.Comp R C a b c) {x : BoCa.Loc} (hx : c.get x = none) :
    a.get x = none := ((ResUT.Comp.eq_none_iff h x).mp hx).1

theorem none_of_comp_none_right {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    {a b c : TRes K} (h : ResUT.Comp R C a b c) {x : BoCa.Loc} (hx : c.get x = none) :
    b.get x = none := ((ResUT.Comp.eq_none_iff h x).mp hx).2

/-- **`#` from the walks** (the converse of `ResUT.Hash.walks`, as 6.38's proof reads it): two
resources compose to a valid one when their exclusive parts are disjoint, their aliasable parts
`○`-compose, and each exclusive part is disjoint from each aliasable part. The top-level `▸◂` is
read off the walks: an `own`/`mut` cell sits in `ex`, an `imm` cell in `ag`. -/
theorem hash_of_walks {ρ₁ ρ₂ e₁ e₂ a₁ a₂ : TRes K}
    (he₁ : ExST ρ₁ e₁) (he₂ : ExST ρ₂ e₂) (ha₁ : AgWT ρ₁ a₁) (ha₂ : AgWT ρ₂ a₂)
    (hee : ∀ x, e₁.get x = none ∨ e₂.get x = none) (haa : ResUT.CompatR a₁ a₂)
    (h11 : ∀ x, e₁.get x = none ∨ a₁.get x = none) (h12 : ∀ x, e₁.get x = none ∨ a₂.get x = none)
    (h21 : ∀ x, e₂.get x = none ∨ a₁.get x = none) (h22 : ∀ x, e₂.get x = none ∨ a₂.get x = none) :
    ResUT.Hash ρ₁ ρ₂ := by
  have hcs : ResUT.CompatS ρ₁ ρ₂ := by
    intro x ψ₁ ψ₂ e₁x e₂x
    by_cases k₁ : ψ₁.kind = Kind.imm
    · by_cases k₂ : ψ₂.kind = Kind.imm
      · obtain ⟨χ₁, f₁, kχ₁, eχ₁, wχ₁⟩ := AgWT.get_imm ha₁ e₁x k₁
        obtain ⟨χ₂, f₂, kχ₂, eχ₂, wχ₂⟩ := AgWT.get_imm ha₂ e₂x k₂
        obtain ⟨χ, hχ⟩ := haa x χ₁ χ₂ f₁ f₂
        have nk₁ : χ₁.kind ≠ Kind.own := by rw [kχ₁]; simp
        have nk₂ : χ₂.kind ≠ Kind.own := by rw [kχ₂]; simp
        refine CellUT.compatS_iff.mpr ⟨k₁, k₂, ?_, ?_⟩
        · rw [← eχ₁, ← eχ₂, ← hχ.erase_left, hχ.erase_right]
        · rw [← wχ₁, ← wχ₂, ← (hχ.nonown_left nk₁).2, (hχ.nonown_right nk₂).2]
      · have f₂ := ExST.get_of_ne_imm he₂ e₂x k₂
        obtain ⟨χ₁, f₁, -⟩ := AgWT.get_imm ha₁ e₁x k₁
        rcases h21 x with h | h
        · rw [h] at f₂; cases f₂
        · rw [h] at f₁; cases f₁
    · have f₁ := ExST.get_of_ne_imm he₁ e₁x k₁
      by_cases k₂ : ψ₂.kind = Kind.imm
      · obtain ⟨χ₂, f₂, -⟩ := AgWT.get_imm ha₂ e₂x k₂
        rcases h12 x with h | h
        · rw [h] at f₁; cases f₁
        · rw [h] at f₂; cases f₂
      · have f₂ := ExST.get_of_ne_imm he₂ e₂x k₂
        rcases hee x with h | h
        · rw [h] at f₁; cases f₁
        · rw [h] at f₂; cases f₂
  obtain ⟨ρ, hρ⟩ := (ResUT.compS_defined_iff _ _).mpr hcs
  obtain ⟨e, he⟩ := (ResUT.compS_defined_iff e₁ e₂).mpr (ResUT.Compat.of_disjoint hee)
  obtain ⟨a, ha⟩ := (ResUT.compR_defined_iff a₁ a₂).mpr haa
  have hea : ∀ x, e.get x = none ∨ a.get x = none := by
    intro x
    cases ex : e.get x with
    | none => exact Or.inl rfl
    | some ψ =>
        right
        refine (ResUT.Comp.eq_none_iff ha x).mpr ⟨?_, ?_⟩
        · rcases ResUT.Comp.get he x with ⟨-, -, f⟩ | ⟨χ, f₁, -, -⟩ | ⟨χ, -, f₂, -⟩ |
              ⟨χ₁, χ₂, χ, f₁, f₂, -, -⟩
          · rw [ex] at f; cases f
          · exact (h11 x).resolve_left (by rw [f₁]; simp)
          · exact (h21 x).resolve_left (by rw [f₂]; simp)
          · exact (h11 x).resolve_left (by rw [f₁]; simp)
        · rcases ResUT.Comp.get he x with ⟨-, -, f⟩ | ⟨χ, f₁, -, -⟩ | ⟨χ, -, f₂, -⟩ |
              ⟨χ₁, χ₂, χ, f₁, f₂, -, -⟩
          · rw [ex] at f; cases f
          · exact (h12 x).resolve_left (by rw [f₁]; simp)
          · exact (h22 x).resolve_left (by rw [f₂]; simp)
          · exact (h12 x).resolve_left (by rw [f₁]; simp)
  obtain ⟨σ, hσ⟩ := (ResUT.compS_defined_iff e a).mpr (ResUT.Compat.of_disjoint hea)
  exact ⟨hcs, ρ, hρ, σ, (ResUT.Flat.split hρ).mpr ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, he, ha₁, ha₂,
    ha, hσ⟩⟩


/-- **The frame condition at an escrow's exclusive locations.** `Y`'s flattening holds nothing at
the lent location `ℓ` (`joinFd`) and nothing at any location of `ex(R)`, the escrow's
exclusive part at any depth. -/
def FdEsc (l : BoCa.Loc) (R Y : TRes K) : Prop :=
  ∀ τ, ResUT.Flat Y τ → τ.get l = none ∧ ∀ eR, ExST R eR → ∀ x, (eR.get x).isSome → τ.get x = none

/-- **`immEnd`'s `✓` from the frame condition at the escrow's exclusive locations.** With
`W = ℓ ↦ imm(s, v, R) ● Y` valid and the lender's piece `ℓ ↦ own(v) ● R` valid (as it was at the
lend), `ℓ ↦ own(v) ● R # Y`. Along 6.38's proof: `ag(ℓ ↦ imm(s, v, R)) = ℓ ↦ imm(…) ○ ⦇R⦈`
(6.33), so `ag(R) ⋈ ag(Y)` and `ex(Y) ⊥ ag(R)` are read off `✓W`; `ex(R) ● ℓ ↦ own(v)` against
`ex(Y)` and `ag(Y)` is the condition. -/
theorem immEnd_hash_of_fdEsc {l : BoCa.Loc} {s : TSet} {v : BoCa.Val} {R Y W X' : TRes K}
    {hs : R.InStratum s} (hv : ResUT.Valid W)
    (hW : ResUT.CompS (ResUT.single l (CellUT.immOf s v R hs)) Y W)
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X') (hvX : ResUT.Valid X')
    (hfd : FdEsc l R Y) : ResUT.Hash X' Y := by
  -- `⦇ℓ ↦ own(v) ● R⦈ = ℓ ↦ own(v) ● ex(R) ● ag(R)`
  obtain ⟨σX, hσX⟩ := hvX
  obtain ⟨o₁, eR, eX, z, aR, aX, ho₁, heR, heX, hz, haR, haX, hσXc⟩ :=
    (ResUT.Flat.split hX).mp hσX
  obtain rfl : o₁ = ResUT.single l (CellUT.ownOf v) := ExST.functional ho₁ (ExWT.single_own l v)
  obtain rfl : z = PMap.empty := AgWT.functional hz (AgWT.single_own l v)
  have haXR : aR = aX := ResUT.eq_of_comp_empty_left haX
  subst aX
  -- `⦇R⦈ = ex(R) ● ag(R)`, `✓R`
  have hvR : ResUT.Valid R := (ResUT.Valid.split hX ⟨σX, hσX⟩).2
  obtain ⟨σR, hσR⟩ := hvR
  obtain ⟨eR', aR', heR', haR', hσRc⟩ := id hσR
  have e1 : eR = eR' := ExST.functional heR heR'
  subst e1
  have e2 : aR = aR' := AgWT.functional haR haR'
  subst e2
  -- `⦇W⦈`: `ex(W) = ex(Y)`, `ag(W) = ag(ℓ ↦ imm(…)) ○ ag(Y)`
  obtain ⟨σW, hσW⟩ := hv
  obtain ⟨n₁, eY, eW, aI, aY, aW, hn₁, heY, heW, haI, haY, haW, hσWc⟩ :=
    (ResUT.Flat.split hW).mp hσW
  obtain rfl : n₁ = PMap.empty := ExST.functional hn₁ (exST_all_imm fun x ψ e => by
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e; exact CellUT.kind_immOf _ _ _ _)
  have e7 : eY = eW := ResUT.eq_of_comp_empty_left heW
  subst e7
  -- `ag(ℓ ↦ imm(s, v, R)) = ℓ ↦ imm(…) ○ ⦇R⦈`, by 6.33
  obtain ⟨e', a', p, he', ha', hp, hI⟩ := AgWT.single_imm_inv haI
  have e3 : aR = a' := AgWT.functional haR ha'
  subst e3
  have e4 : σR = p :=
    ResUT.FlatR.functional (ResUT.six33 hσR) ⟨aR, e', haR, he', ResUT.CompR.comm hp⟩
  subst e4
  -- every cell of `ag(R)` is a cell of `ag(ℓ ↦ imm(…))` away from `ℓ`, and a cell there at `ℓ`
  have hRI : ∀ x ψ, aR.get x = some ψ → x ≠ l → aI.get x = some ψ := by
    intro x ψ e hx
    have hσ : σR.get x = some ψ := by
      have heRx : eR.get x = none :=
        (ResUT.CompatS.disjoint_of_immFree (ExST.immFree heR) hσRc.1 x).resolve_right
          (by rw [e]; simp)
      exact (ResUT.Comp.get_of_left_none hσRc heRx).trans e
    exact (ResUT.Comp.get_of_left_none hI (ResUT.single_get_ne _ hx)).trans hσ
  have hRIl : ∀ ψ, aR.get l = some ψ → ∃ χ, aI.get l = some χ := by
    intro ψ _
    rcases ResUT.Comp.get hI l with ⟨f, -, -⟩ | ⟨χ, -, -, f⟩ | ⟨χ, f, -, -⟩ |
        ⟨χ₁, χ₂, χ, -, -, f, -⟩
    · simp at f
    · exact ⟨χ, f⟩
    · simp at f
    · exact ⟨χ, f⟩
  -- `Y`'s flattening holds nothing at `ℓ` nor at `ex(R)`
  obtain ⟨σY, hσY⟩ : ResUT.Valid Y := (ResUT.Valid.split hW ⟨σW, hσW⟩).2
  obtain ⟨eY', aY', heY', haY', hσYc⟩ := id hσY
  have e5 : eY = eY' := ExST.functional heY heY'
  subst e5
  have e6 : aY = aY' := AgWT.functional haY haY'
  subst e6
  obtain ⟨hYl, hYR⟩ := hfd σY hσY
  have hX'ex : ∀ x, (eX.get x).isSome → σY.get x = none := by
    intro x hx
    rcases ResUT.Comp.get heX x with ⟨-, -, f⟩ | ⟨χ, f₁, -, -⟩ | ⟨χ, -, f₂, -⟩ |
        ⟨χ₁, χ₂, χ, f₁, f₂, -, -⟩
    · rw [f] at hx; cases hx
    · rw [(ResUT.single_get_eq_some f₁).1]; exact hYl
    · exact hYR eR heR x (by rw [f₂]; rfl)
    · rw [(ResUT.single_get_eq_some f₁).1]; exact hYl
  have hXe : ExST X' eX := (ExST.split hX).mpr ⟨_, _, ho₁, heR, heX⟩
  have hXa : AgWT X' aR := (AgWT.split hX).mpr ⟨_, _, hz, haR, haX⟩
  refine hash_of_walks hXe heY hXa haY (fun x => ?_) (fun x ψ₁ ψ₂ e₁ e₂ => ?_) (fun x => ?_)
    (fun x => ?_) (fun x => ?_) (fun x => ?_)
  · -- `ex(ℓ ↦ own(v) ● R)` against `ex(Y)`: the condition
    cases h : eX.get x with
    | none => exact Or.inl rfl
    | some _ =>
        exact Or.inr (none_of_comp_none_left hσYc (hX'ex x (by rw [h]; rfl)))
  · -- `ag(R) ⋈ ag(Y)`, from `✓W`
    by_cases hx : x = l
    · subst hx
      exact absurd (none_of_comp_none_right hσYc hYl) (by rw [e₂]; simp)
    · exact haW.1 x ψ₁ ψ₂ (hRI x ψ₁ e₁ hx) e₂
  · -- `ex(ℓ ↦ own(v) ● R)` against `ag(R)`: `✓(ℓ ↦ own(v) ● R)`
    exact ResUT.CompatS.disjoint_of_immFree (ExST.immFree hXe) hσXc.1 x
  · -- `ex(ℓ ↦ own(v) ● R)` against `ag(Y)`: the condition
    cases h : eX.get x with
    | none => exact Or.inl rfl
    | some _ =>
        exact Or.inr (none_of_comp_none_right hσYc (hX'ex x (by rw [h]; rfl)))
  · -- `ex(Y)` against `ag(R)`, from `✓W`
    cases h : aR.get x with
    | none => exact Or.inr rfl
    | some ψ =>
        left
        have haIx : ∃ χ, aI.get x = some χ := by
          by_cases hx : x = l
          · subst hx; exact hRIl ψ h
          · exact ⟨ψ, hRI x ψ h hx⟩
        obtain ⟨χ, hχ⟩ := haIx
        have haWx : aW.get x ≠ none := fun hn => by
          rw [none_of_comp_none_left haW hn] at hχ; cases hχ
        exact (ResUT.CompatS.disjoint_of_immFree (ExST.immFree heY) hσWc.1 x).resolve_right
          haWx
  · -- `ex(Y)` against `ag(Y)`: `✓Y`
    exact ResUT.CompatS.disjoint_of_immFree (ExST.immFree heY) hσYc.1 x

/-- The end world exists and is valid. -/
theorem immEnd_valid_of_fdEsc {l : BoCa.Loc} {s : TSet} {v : BoCa.Val} {R Y W X' : TRes K}
    {hs : R.InStratum s} (hv : ResUT.Valid W)
    (hW : ResUT.CompS (ResUT.single l (CellUT.immOf s v R hs)) Y W)
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X') (hvX : ResUT.Valid X')
    (hfd : FdEsc l R Y) : ∃ W', ResUT.CompS X' Y W' ∧ ResUT.Valid W' := by
  obtain ⟨-, W', hW', hv'⟩ := immEnd_hash_of_fdEsc hv hW hX hvX hfd
  exact ⟨W', hW', hv'⟩

/-- At the configuration, the condition fails at `m`, the escrow's `own` cell: `Y`'s flattening
holds the image there. -/
theorem config_not_fdEsc {β : Life} {l m : BoCa.Loc} :
    ¬ FdEsc l (escR (K := K) m) (viewRes β m) := by
  intro h
  have hf : ResUT.Flat (viewRes (K := K) β m) (viewRes β m) := by
    obtain ⟨τ, hτ⟩ := valid_view (K := K) β m
    obtain rfl := flat_view hτ
    exact hτ
  have := (h _ hf).2 (escR m) (ExWT.single_own m _) m (by rw [escR, ResUT.single_get_self]; rfl)
  rw [viewRes, ResUT.single_get_self] at this
  cases this


/-! ### The lender's piece is valid -/

/-! ### The join's condition at the escrow -/

/-! ### The statement with branch points -/

/-- **The escrow's frame condition from branch points**: at a `TWNT` world, for a record proper
`p` whose frame is at `α`, a part `ρ_rest` of the world whose top cells are on a branch `n` not
inside `α` holds nothing at `p`'s location nor at its escrow's exclusive locations. -/
def FdEscOfBranchT : Prop :=
  ∀ (K : WCactus) (Θ : CodeTy) (tc : TChoice K) (W ρo ρrest : TRes K)
    (ps rs : List (FrameRecT K)) (p : FrameRecT K) (α n : Life),
    TWNT K Θ tc W ps rs → p ∈ ps → ResUT.CompS ρo ρrest W → FrameLifeT K W p α →
    OnBranchResT K n ρrest → ¬ K.le n α → FdEsc p.le p.R ρrest

end BoCa.Fig16.Tree.Wp

end
