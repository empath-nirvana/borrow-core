import Spike743.NaturalK2

/-!
# Spike743 — round P2: `mut_not_natural`'s configuration is arising

`Restrat.MutCounterexample` reads `𝒱⟦Mut 'a (Imm 'b 1)⟧` at `['a ↦ 3, 'b ↦ 1]` at the share
`ρ₀ = ℓ ↦ mut(2, ℓ′, ℓ′ ↦ imm({1}, (), ∅), 𝒱⟦Imm 'b 1⟧)`. Here the same share is built at Core's
relation (the stored invariant is Core's `𝒱⟦Imm 'b 1⟧` at the list's records above `2`) and shown
arising (`mut_world_arising`): `return x` at `x : Mut 'a (Imm 'b 1)`, closed by `x := ℓ`, at the
list `[(r, 1)]`, `r` the frame record of `ℓ′`, in the world built by `alloc ℓ`, `alloc ℓ′`,
`immFrame` at `1` and `mutFold` at `2` (`mut_world`).

At the shift `['a ↦ 4, 'b ↦ 2]` (`Emb.shift ⊤ 1`'s), `LifeNatural`'s conclusion holds whenever
the view is the configuration's own variable read at its type (`mut_world_rebuilt`): the view is
rebuilt at the new assignment, so the image action that `mut_not_natural` refutes is never
taken. `NaturalK2` is a different instance of the statement's premises.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Spike743.NaturalWorld
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Spike743.Natural
open Spike743.NaturalK2 (L models_empty)

def ℓ : Loc := 0
def ℓ' : Loc := 1

/-- `['a ↦ 3, 'b ↦ 1]`, `'a = 0`, `'b = 1`. -/
def δm : LSub := ⟨[(0, 3), (1, 1)]⟩
/-- The image of `δm` under `n ↦ n + 1`: `['a ↦ 4, 'b ↦ 2]`. -/
def δm' : LSub := ⟨[(0, 4), (1, 2)]⟩

/-- `Imm 'b 1`. -/
abbrev S : VTy := .imm (.var 1) .unit
/-- `Mut 'a (Imm 'b 1)`. -/
abbrev T : VTy := .mut (.var 0) S

/-- The frame record of `ℓ′`, borrowed `imm` at `1`. -/
def r : FrameRec := ⟨ℓ', .unit, PMap.empty, VTy.unit, δm⟩
/-- The list: the record tagged `1`. -/
def lsm : List SRec := [(r, L 1)]

theorem hstr1 : ResU.InStratum (LSet.singleton (L 1)).join (PMap.empty : WRes) :=
  ResU.inStratum_empty _

/-- `ℓ′ ↦ imm({1}, (), ∅)`. -/
def σ0 : WRes := ResU.single ℓ' (CellU.immOf (LSet.singleton (L 1)) .unit PMap.empty hstr1)

theorem σ_in : σ0.InStratum (L 2) :=
  ResU.inStratum_single _ (show L 2 < L 1 from OrderDual.toDual_lt_toDual.mpr (by decide))

/-- `𝒱⟦Imm 'b 1⟧(ls)δm` lies in `Res_2`. -/
theorem vS_supported (ls : List SRec) (u : Val) (σ : WRes) (h : vC true S ls δm u σ) :
    σ.InStratum (L 2) := by
  obtain ⟨α, hα, m, hk⟩ := h
  have hα' : α = L 1 := (Option.some.inj hα).symm
  obtain ⟨-, s, u', ξ, hξ, ls₀, rfl, -, hle, -⟩ := pure_sep_iff.mp hk
  refine ResU.inStratum_single _ ?_
  show L 2 < s.meet
  rw [hα'] at hle
  exact lt_of_lt_of_le (OrderDual.toDual_lt_toDual.mpr (by decide)) hle

/-- `𝒱⟦Imm 'b 1⟧(lsm)δm(ℓ′)` at the frame's cell: coherent with the record `r`. -/
theorem vS_at : vC true S lsm δm (.loc ℓ') σ0 := by
  refine ⟨L 1, rfl, ℓ', pure_sep_mk ⟨rfl, ⟨VTy.unit, δm, TyEq.refl _ _,
    Or.inl ⟨r, (show r ∈ [r] from List.mem_singleton_self r), rfl, rfl, fun _ h => by simp [r, VFree] at h⟩⟩⟩ ?_⟩
  refine ⟨LSet.singleton (L 1), .unit, PMap.empty, hstr1, [], rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
  · exact le_rfl
  · intro x
    simp only [List.not_mem_nil, false_iff, not_and, lsm, List.mem_singleton]
    rintro rfl
    exact lt_irrefl _

/-- The stored invariant: Core's `𝒱⟦Imm 'b 1⟧` at the records above `2`. -/
def Qm : Val → SPropS Loc Val (L 2) := fun v => SPropU.toS (L 2) (vC true S lsm δm v)

theorem hw : Qm (.loc ℓ') ⟨σ0, σ_in⟩ := vS_at

theorem ofS_Qm : ofS Qm = vC true S lsm δm := by
  funext v ρ
  apply propext
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨vS_supported _ _ _ h, h⟩

/-- `ρ₀ = ℓ ↦ mut(2, ℓ′, ℓ′ ↦ imm({1}, (), ∅), 𝒱⟦Imm 'b 1⟧)`, at Core's relation. -/
def ρ₀ : WRes := ResU.single ℓ (CellU.mutOf (L 2) (.loc ℓ') σ0 σ_in Qm hw)

/-- `𝒱⟦Mut 'a (Imm 'b 1)⟧(lsm)δm(ℓ)(ρ₀)`. -/
theorem vT_holds : vC true T lsm δm (.loc ℓ) ρ₀ := by
  refine ⟨L 3, rfl, ℓ, pure_sep_mk rfl ?_⟩
  refine ⟨L 2, .loc ℓ', σ0, σ_in, Qm, hw, lsm,
    show (2 : ℕ) ≤ 3 by decide, rfl, ofS_Qm, ?_, fun _ u' σ' h => vS_supported _ u' σ' h⟩
  intro x
  simp only [lsm, List.mem_singleton]
  constructor
  · rintro rfl; exact ⟨rfl, OrderDual.toDual_lt_toDual.mpr (by decide)⟩
  · exact fun h => h.1

/-- **The world**: `alloc ℓ`, `alloc ℓ′`, `immFrame` at `1` (as `LoopBorrow.consumer_frame_world`),
then `mutFold` at `2`, the frame's cell the folded payload. -/
theorem mut_world :
    ResU.Hash (PMap.empty : WRes) ρ₀ ∧ TW ρ₀ [r] (rsOf lsm) ∧ Tagged ρ₀ [r] lsm := by
  classical
  obtain ⟨x₁, σ₁, hx₁, -, hσ₁, hT₁, hlow₁, -, -⟩ :=
    alloc_world (ρf := PMap.empty) (ρ := PMap.empty) (ps := []) (rs := []) (l := ℓ)
      (Val.loc ℓ') Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty
      Fig16.BoLo.lower_empty rfl
  obtain rfl := ResU.eq_of_comp_empty_left hx₁
  obtain rfl := ResU.eq_of_comp_empty_left hσ₁
  have hfree : (Heap.upd (fun _ => none) ℓ (Val.loc ℓ')) ℓ' = none := by
    simp [Heap.upd, ℓ, ℓ']
  obtain ⟨x₂, σ₂, hx₂, hfx₂, hσ₂, hT₂, -, -, -⟩ :=
    alloc_world (ρf := PMap.empty) (l := ℓ') (.unit : Val)
      ⟨hx₁.1, _, hx₁, ResU.valid_single_own ℓ (Val.loc ℓ')⟩
      hx₁ hT₁ hlow₁ hfree
  obtain rfl := ResU.eq_of_comp_empty_left hσ₂
  have hvx₂ : ResU.Valid x₂ := (hash_valid hfx₂).2
  have hown : ResU.Hash (ResU.single ℓ (CellU.ownOf (Val.loc ℓ')))
      (ResU.single ℓ' (CellU.ownOf (.unit : Val))) := ⟨hx₂.1, x₂, hx₂, hvx₂⟩
  obtain ⟨-, W', hW', hvW'⟩ :=
    ResU.six34 (hs := hstr1) (ResU.comp_empty_left (ResU.single ℓ' (CellU.ownOf (.unit : Val))))
      hown
  have hX : ResU.CompS (ResU.single ℓ' (CellU.ownOf (.unit : Val))) PMap.empty
      (ResU.single ℓ' (CellU.ownOf (.unit : Val))) := ResU.comp_empty_right _
  have hnodesc : ∀ d, d ∈ ([] : List FrameRec) ↔ Desc r d := by
    intro d
    refine ⟨fun h => absurd h (by simp), ?_⟩
    rintro ⟨p, hp, hlp⟩
    cases hlp with
    | nil => exact absurd rfl hp
    | cons hs _ =>
      obtain ⟨-, -, ζ, e, -⟩ := hs
      simp [r] at e
  have hT' : TW W' (r :: []) (r :: ([] ++ [])) :=
    TW.immFrame .unit δm hstr1 hT₂ (fun x hx => absurd hx (by simp [VFree])) hX
      (ResU.CompS.comm hx₂) ⟨rfl, rfl⟩ (ResU.CompS.comm hW') hvW' hnodesc
  obtain ⟨hFL, -⟩ := frameLife_frame .unit δm hvx₂ hX (ResU.CompS.comm hx₂)
    (ResU.CompS.comm hW') hT₂.inv
  have htg' : Tagged W' [r] lsm := by
    intro x hx
    simp only [lsm, List.mem_singleton] at hx
    subst hx
    exact ⟨r, List.mem_singleton_self r, DescR.refl r, hFL⟩
  -- `mutFold` at `2`: the own cell `ℓ ↦ own(ℓ′)` and its payload `σ0` folded into `ρ₀`
  have hXm : ResU.CompS (ResU.single ℓ (CellU.ownOf (Val.loc ℓ'))) σ0 W' := hW'
  have hH : ResU.Hash (PMap.empty : WRes) ρ₀ :=
    ResU.six23 (hstr := σ_in) (P := Qm) (hw := hw) (ResU.CompS.comm hXm)
      ⟨ResU.Compat.of_disjoint (fun _ => Or.inl rfl), W', ResU.comp_empty_left _, hvW'⟩
  have hTm : TW ρ₀ [r] (rsOf lsm) := by
    exact (TW.mutFold (hstr := σ_in) (P := Qm) (hw := hw) hT' hXm (ResU.comp_empty_right _)
        (ResU.comp_empty_right _) (hash_valid hH).2)
  refine ⟨hH, hTm, tagged_of_ag (fun a ha =>
    (mut_fold_ag hXm (ResU.comp_empty_right _) (ResU.comp_empty_right _) a).mpr ha) htg'⟩

theorem subst_var0 : substAll [Val.loc ℓ] (.var 0) = .val (Val.loc ℓ) := by
  show Expr.psub 0 [Val.loc ℓ] (.var 0) = _
  rw [Expr.psub_cons 0 (Val.loc ℓ) [] _, Val.shift_zero, BoCa.Adequacy.psub_nil]
  rfl

/-- **`mut_not_natural`'s configuration is arising**: `return x` at `x : Mut 'a (Imm 'b 1)`,
closed by first-order data, at `δm`, the share `ρ₀` in the context's relation and a tagged typed
world at `[(r, 1)]`. -/
theorem mut_world_arising :
    Arising ⟨[]⟩ [⟨T, true⟩] (.var 0) (.ret T) [Val.loc ℓ] δm lsm ρ₀ := by
  obtain ⟨hH, hT, htg⟩ := mut_world
  exact ⟨.ret (.var (.here .nil)), .cons (.data .loc) .nil, models_empty δm,
    gDenC_mk (by simp [Ctx.LiveWithin])
      ⟨ρ₀, PMap.empty, ResU.comp_empty_right _, vT_holds, rfl, trivial⟩,
    PMap.empty, ρ₀, [r], hH, ResU.comp_empty_left _, hT, htg⟩

/-- The computation is in the relation at `δm`. -/
theorem mut_world_holds : cC (ℍ := ℍ) (.ret T) lsm δm (substAll [Val.loc ℓ] (.var 0)) ρ₀ := by
  rw [subst_var0]; exact wpTS_val _ _ _ _ vT_holds

/-- The image shift `['a ↦ 4, 'b ↦ 2]` is a `RegionShift` of `δm` at the list, with an empty rest:
each moved lifetime is no longer than the record's `1`. -/
theorem mut_world_shift : RegionShift δm δm' lsm lsm PMap.empty := by
  intro y hy
  have hle : ∀ n : ℕ, 1 ≤ n → ∀ x ∈ lsm, L n ≤ x.2 := by
    intro n hn x hx
    simp only [lsm, List.mem_singleton] at hx
    subst hx
    exact OrderDual.toDual_le_toDual.mpr hn
  by_cases h0 : y = 0
  · subst h0
    exact ⟨L 3, L 4, rfl, rfl, hle 3 (by decide), hle 4 (by decide), ResU.inStratum_empty _,
      ResU.inStratum_empty _⟩
  by_cases h1 : y = 1
  · subst h1
    exact ⟨L 1, L 2, rfl, rfl, hle 1 le_rfl, hle 2 (by decide), ResU.inStratum_empty _,
      ResU.inStratum_empty _⟩
  · exfalso; apply hy
    simp [δm, δm', LSub.find?, Lifetime.assocFind, Ne.symm h0, Ne.symm h1]

/-- **At the image shift, with the view rebuilt, the conclusion holds**: whatever resource is in
`𝒱⟦Mut 'a (Imm 'b 1)⟧` at the new assignment, `return ℓ` is in the relation there. -/
theorem mut_world_rebuilt {ls' : List SRec} {ρv' : WRes} (hv' : vC true T ls' δm' (.loc ℓ) ρv') :
    cC (ℍ := ℍ) (.ret T) ls' δm' (substAll [Val.loc ℓ] (.var 0)) ρv' := by
  rw [subst_var0]; exact wpTS_val _ _ _ _ hv'

end Spike743.NaturalWorld

end
