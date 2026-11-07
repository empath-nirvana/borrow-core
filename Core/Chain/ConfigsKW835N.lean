import Core.Chain.ConstKW835N
import Core.Chain.Depart831N
import Core.Chain.Shape791N
import Core.Chain.LendExit835N
import Core.Chain.Public835N
import Core.Chain.Kappa835N
import Core.Chain.ExtRLit791
import Core.Chain.ImmRec791N

/-!
# Configurations at the relation at `KW`  `[spec §62]`

The configurations that read `𝒱⟦·⟧` or `𝒞⟦·⟧`, at `vN`/`cN`, one section per file whose design
they check: `ImmRec791N`, `Depart831N`, `Shape791N`, `ExtRLit791`, `Kappa835N`, `Public835N`,
`LendExit835N` and `Lend791N`. The `Map831N` section checks an `imm` lend's step at the per-lend
world (`docs/new-core/scope-831-map.md` §3): at an `OK` world with a `mut` key at `α`, the world
with one more record lent below `α` is an extension (`extR_addImm_inst`), and an extension of it
holds an `Imm` value (`imm_at_extension`).
-/

noncomputable section

open Classical

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ## `ImmRec791N` -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.ImmRec791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub LifeVar)

/-- `vN`'s `Imm` clause admits the cell at `Imm @a (Ref 1)`, at the world holding its record. -/
theorem vN_cellI (x : LifeVar) (α : Life) (l l' : Loc) (n : Nat) :
    vN (ℍ := ℍ) (.imm (.var x) (.ref .unit)) (LSub.empty.extend x α)
      (ΘRef (LSub.empty.extend x α) l l' α) n (Val.loc l) (cellI α l l') := by
  refine ⟨α, interp_ext_self _ x α, ⟨l, LSet.singleton α, Val.loc l', escU l',
    escU_inStratum l' _, rfl, rfl, le_refl _, l', Val.unit, PMap.empty, rfl,
    ResU.comp_empty_right _, rfl, rfl⟩, fun l₀ s₀ u₀ σ₀ h₀ e => ?_⟩
  obtain ⟨rfl, e'⟩ := single_immOf_inj e
  obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
  exact ⟨_, List.mem_singleton_self _, le_refl _, _, DescR.refl _, .ref .unit,
    LSub.empty.extend x α, TyEq.refl _ _,
    Or.inl ⟨_, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩

/-- `vN` has no value of an `Imm` type at `∅`. -/
theorem not_vN_imm_empty (a : BoCa.Lifetime.Life) (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat)
    (v : Val) : ¬ vN (ℍ := ℍ) (.imm a A) δ Θ n v PMap.empty := by
  rintro ⟨-, -, ⟨m, s, u, σ, hs, -, hρ, -⟩, -⟩
  have := congrArg (fun ρ : WRes => ρ.get m) hρ
  simp at this

/-- **`vN`'s `Imm` clause alone does not meet step 8**, at `ℓ = 0`, `ℓ′ = 1`, `α = 1`: `WlImage`
has no entry tie, and the run it reads may be entered at `world_thunk`'s list. -/
theorem not_wlImage_vN : ¬ WlImage (fun A δ Θ n v ρ => vN (ℍ := ℍ) A δ Θ n v ρ) :=
  not_wlImage _ (l := 0) (l' := 1) (by decide) 1 (.var 0) (LSub.empty.extend 0 1)
    (ΘRef (LSub.empty.extend 0 1) 0 1 1) 0 1
    (vN_cellI 0 1 0 1 0) (not_vN_imm_empty _ _ _ _ _ _)

/-- `not_wlImageA` at the clause that reads, besides `vN`'s `Imm`, any condition `G` on the world
at the cell's location and type which the world holding the cell's record at `Ref 1` meets: every
such clause with every agreement from `erwp`, at `ℓ = 0`, `ℓ′ = 1`, `α = 1`. -/
theorem not_wlImageA_vN (G : LocTy → Loc → VTy → LSub → Prop)
    {Agree : LocTy → Loc → VTy → LSub → Prop} (hA : ImmAgreeErwp (ℍ := ℍ) Agree)
    (hG : G (ΘRef (LSub.empty.extend 0 1) 0 1 1) 0 (.ref .unit) (LSub.empty.extend 0 1)) :
    ¬ WlImageA (fun A δ Θ' n v ρ => vN (ℍ := ℍ) A δ Θ' n v ρ ∧
      ∀ a B l, A = .imm a B → v = Val.loc l → G Θ' l B δ) Agree :=
  not_wlImageA _ hA (l := 0) (l' := 1) (by decide) 1 (.var 0) (LSub.empty.extend 0 1)
    (ΘRef (LSub.empty.extend 0 1) 0 1 1) 0 0
    ⟨vN_cellI 0 1 0 1 0, fun a B l hA hv => by
      cases hA
      obtain rfl : l = 0 := by
        have := congrArg Subtype.val hv
        simpa [Val.loc] using this.symm
      exact hG⟩
    (fun h => not_vN_imm_empty _ _ _ _ _ _ h.1)

end BoCa.Fig16.LogRel.Core.Chain.SI.ImmRec791N

/-! ## `Map831N` -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Map831N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.ImmRec791N (recT cellI escU escU_inStratum)
open BoCa.Lifetime (LSub LifeVar)

/-- **An `Imm` value is witnessed by a record of the world**, so the world has one. -/
theorem imm_world_ne_nil {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat}
    {v : Val} {ρ : WRes} (h : vN (ℍ := ℍ) (.imm a A) δ Θ n v ρ) : Θ.imm ≠ [] := by
  obtain ⟨-, -, ⟨l, s, u, σ, hs, -, rfl, -, -⟩, hw⟩ := h
  obtain ⟨x, hx, -⟩ := hw l s u σ hs rfl
  intro e
  rw [e] at hx
  exact List.not_mem_nil hx

/-- The configuration's world: `∅ + (0, α) ↦ 𝒱⟦1⟧`, `α = 1`. -/
def Θc : LocTy :=
  LocTy.empty.add 0 (OrderDual.toDual 1)
    (famL (OrderDual.toDual 1) (fun Θ j u r => vN (ℍ := ℍ) .unit LSub.empty Θ j u r) LocTy.empty)

theorem Θc_ok : (Θc (ℍ := ℍ)).OK := by
  let α : Life := OrderDual.toDual 1
  let b : Life := OrderDual.toDual 2
  have hbα : b < α := OrderDual.toDual_lt_toDual.mpr (by decide)
  have hfam := vN_fam_down (ℍ := ℍ) .unit LSub.empty α LocTy.empty
  exact ⟨LocTy.down_add LocTy.empty_down 0 hfam,
    ⟨b, LocTy.fresh_add (N := b) (fun _ _ h => absurd rfl h) le_rfl hbα 0 _⟩⟩

/-- **Core's `ext_add` at the configuration, every hypothesis discharged**: at the callback
resource `0 ↦ mut(α, (), ∅, ⊤)`, which holds a borrow cell at the key's lifetime `α`, the world
with one more record lent at `β = 2 ⊏ α` is an extension. -/
theorem extR_addImm_inst (r : FrameRec) :
    (Θc (ℍ := ℍ)).ExtR ((Θc (ℍ := ℍ)).addImm (r, OrderDual.toDual 2))
      (ExtRLit791.ρb 0 (OrderDual.toDual 1)) := by
  refine LocTy.extR_addImm _ r (ResU.inStratum_single 0 ?_)
  rw [CellU.inStratum_mutOf]
  exact OrderDual.toDual_lt_toDual.mpr (by decide)

/-- **An extension of the configuration holds an `Imm` value**: the world with the record of
`ℓ ↦ own(loc ℓ′)` lent at `β = 2` holds `𝒱⟦Imm 'x (Ref 1)⟧` at `δ['x ↦ β]`, so the argument that
no extension at the callback's resource holds an `Imm` value fails. -/
theorem imm_at_extension (x : LifeVar) (l l' : Loc) (n : Nat) :
    ∃ Θ', (Θc (ℍ := ℍ)).ExtR Θ' (ExtRLit791.ρb 0 (OrderDual.toDual 1)) ∧
      vN (ℍ := ℍ) (.imm (.var x) (.ref .unit)) (LSub.empty.extend x (OrderDual.toDual 2)) Θ' n
        (Val.loc l) (cellI (OrderDual.toDual 2) l l') := by
  let β : Life := OrderDual.toDual 2
  refine ⟨(Θc (ℍ := ℍ)).addImm (recT (.ref .unit) (LSub.empty.extend x β) l l', β),
    extR_addImm_inst _, ?_⟩
  refine ⟨β, interp_ext_self _ x β, ⟨l, LSet.singleton β, Val.loc l', escU l',
    escU_inStratum l' _, rfl, rfl, le_refl _, l', Val.unit, PMap.empty, rfl,
    ResU.comp_empty_right _, rfl, rfl⟩, fun l₀ s₀ u₀ σ₀ h₀ e => ?_⟩
  obtain ⟨rfl, e'⟩ := single_immOf_inj e
  obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
  exact ⟨_, List.mem_cons_self .., le_refl _, _, DescR.refl _, .ref .unit,
    LSub.empty.extend x β, TyEq.refl _ _,
    Or.inl ⟨_, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Map831N

/-! ## `Depart831N` -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Depart831N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.ImmRec791N (recT cellI escU escU_inStratum)
open BoCa.Lifetime (LSub LifeVar)

/-- **The step `tabUN_eq_addImm` takes, under the location reading**: a value of an `Imm` type at
the world with a record lent at `α`, at a resource in `Res_α`, is at an extension of the world
without the record. -/
def UnwindArgStepLoc : Prop :=
  ∀ (Θ : LocTy) (p : FrameRec) (α : Life) (a : Lifetime.Life) (A : VTy) (δ : LSub) (n : Nat)
    (v : Val) (ρ : WRes), Θ.OK → vN (ℍ := ℍ) (.imm a A) δ (Θ.addImm (p, α)) n v ρ →
    ρ.InStratum α → (Θ.addImm (p, α)).ExtRLoc Θ ρ

/-- **The configuration, every hypothesis discharged.** At `Θq + (p, α)`, `α = 2`, the resource
`ℓ ↦ imm({γ}, loc ℓ′, ℓ′ ↦ own(()))` is a value of `Imm 'y (Ref 1)` at `δ['y ↦ γ]`, witnessed by
`q`. It lies in `Res_α` and the lifetime reading moves it to `Θq` (`LocTy.extR_of_addImm`).
The location reading does not: `Rel p ρ` holds at `ℓ`, and `p` is not a record of `Θq`. -/
theorem unwindArg_inst (y : LifeVar) (l l' : Loc) (n : Nat) :
    let Θ := Θq y l l'
    let α : Life := OrderDual.toDual 2
    Θ.OK ∧
    vN (ℍ := ℍ) (.imm (.var y) (.ref .unit)) (LSub.empty.extend y (OrderDual.toDual 1))
      (Θ.addImm (pRec l l', α)) n (Val.loc l) (cellI (OrderDual.toDual 1) l l') ∧
    (cellI (OrderDual.toDual 1) l l').InStratum α ∧
    (Θ.addImm (pRec l l', α)).ExtR Θ (cellI (OrderDual.toDual 1) l l') ∧
    ¬ (Θ.addImm (pRec l l', α)).ExtRLoc Θ (cellI (OrderDual.toDual 1) l l') := by
  intro Θ α
  let γ : Life := OrderDual.toDual 1
  let δ := LSub.empty.extend y γ
  have hst : (cellI γ l l').InStratum α := by
    refine ResU.inStratum_single l ?_
    rw [CellU.inStratum_immOf]
    exact OrderDual.toDual_lt_toDual.mpr (by decide)
  refine ⟨Θq_ok y l l', ?_, hst, LocTy.extR_of_addImm Θ _ hst, ?_⟩
  · refine ⟨γ, interp_ext_self _ y γ, ⟨l, LSet.singleton γ, Val.loc l', escU l',
      escU_inStratum l' _, rfl, rfl, le_refl _, l', Val.unit, PMap.empty, rfl,
      ResU.comp_empty_right _, rfl, rfl⟩, fun l₀ s₀ u₀ σ₀ h₀ e => ?_⟩
    obtain ⟨rfl, e'⟩ := single_immOf_inj e
    obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
    exact ⟨(recT (.ref .unit) δ l l', γ), List.mem_cons_of_mem _ (List.mem_singleton_self _),
      le_refl _, _, DescR.refl _, .ref .unit, δ, TyEq.refl _ _,
      Or.inl ⟨_, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩
  · rintro ⟨-, hk⟩
    have hrel : Rel (pRec l l') (cellI γ l l') :=
      ⟨l, _, ResU.single_get_self _ _, CellU.kind_immOf _ _ _ _, Or.inl rfl⟩
    have hp : pRec l l' ∈ rsOf (Θ.addImm (pRec l l', α)).imm :=
      mem_rsOf.mpr ⟨α, List.mem_cons_self ..⟩
    obtain ⟨t, ht⟩ := mem_rsOf.mp (hk _ hp hrel)
    have e := congrArg Prod.fst (List.mem_singleton.mp ht)
    exact pRec_ne y l l' e

/-- **The step fails under the location reading.** -/
theorem not_unwindArgStepLoc : ¬ UnwindArgStepLoc (ℍ := ℍ) := by
  intro h
  obtain ⟨hok, hv, hst, -, hn⟩ := unwindArg_inst (ℍ := ℍ) (0 : LifeVar) 0 1 0
  exact hn (h _ _ _ _ _ _ _ _ _ hok hv hst)

/-- **`F_Σ R` is `erwpK` at the row's table, at every floor, on both sides of Core's split on
`Row.divB`.** -/
theorem cN_effOf_divB (S : Row) (b : Bool) (_hb : Row.divB S = b) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes) :
    cN (ℍ := ℍ) (CTy.effOf S R) δ Θ c n ls e ρ ↔ ∀ lo : Life,
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S R) δ z))
        (fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) ⟨Θ, c, lo⟩ n ls e ρ :=
  cN_effOf S R δ Θ c n ls e ρ

end BoCa.Fig16.LogRel.Core.Chain.SI.Depart831N

/-! ## `Shape791N` -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Shape791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.BoLo (Heap Step1 Head Kont)
open BoCa.Lifetime (LSub)

/-- `𝒱⟦U(F 1)⟧`'s member at an index, at the empty world. -/
abbrev thunkUnit (δ : LSub) (k : Nat) : Val → WRes → Prop :=
  vN (ℍ := ℍ) (.thunk (.ret .unit)) δ LocTy.empty k

theorem stuckV_one (δ : LSub) : thunkUnit (ℍ := ℍ) δ 1 stuckV PMap.empty := by
  intro Θ' _ _ c _ ls
  refine (cN_ret_iff _ _ _ _ _ _ _ _).mpr ?_
  show erwp (ℍ := ℍ) (Θ'.view c) _ _ 1 ls (.app stuckV.1 (.val .unit)) PMap.empty
  rw [erwp_eq]
  intro ρf fρ ps μ _ _ _ _ _ _ _ j μ' e' hj hrun hfin
  obtain rfl : j = 0 := by omega
  cases hrun
  exact absurd (step1Only_plug (ℍ := ℍ) (Head.beta μ (.app .unit Val.unit.1) Val.unit) rfl
    .hole).1 (hfin _ _)

theorem stuckV_not_two (δ : LSub) : ¬ thunkUnit (ℍ := ℍ) δ 2 stuckV PMap.empty := by
  intro h
  have h2 := (cN_ret_iff _ _ _ _ _ _ _ _).mp (h LocTy.empty (LocTy.extR_refl _ _)
    LocTy.empty_ok (fun _ => none) (consistentX_empty _) [])
  change erwp (ℍ := ℍ) _ _ _ 2 [] (.app stuckV.1 (.val .unit)) PMap.empty at h2
  rw [erwp_eq] at h2
  have hstep := (step1Only_plug (ℍ := ℍ) (Head.beta (fun _ => none) (.app .unit Val.unit.1)
    Val.unit) rfl .hole).1
  have hbody : Kont.hole.plug (Expr.subst 0 Val.unit (.app .unit Val.unit.1)) =
      Kont.hole.plug (.app .unit Val.unit.1) := by
    simp [Kont.plug, Expr.subst, Val.unit]
  rw [hbody] at hstep
  have hfin : Final (ℍ := ℍ) (fun _ => none) (Kont.hole.plug (.app .unit Val.unit.1)) :=
    fun _ _ hs => stuck_no_step (stuckAt_unit_app Val.unit) .hole hs
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  have hE := h2 PMap.empty PMap.empty [] (fun _ => none) Fig16.LogRel.hash_empty
    (ResU.comp_empty_right _) TWNC.empty htg (ImmTieL.nil _) Fig16.BoLo.lower_empty fd_empty 1 _ _
    (by omega) (.more hstep (.refl _ _)) hfin
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, hq⟩ := hE
  rcases hq with ⟨v, hv, -⟩ | ⟨_, _, _, _, _, h'⟩ | ⟨_, _, _, _, _, h'⟩
  · have : IsVal (Kont.hole.plug (.app .unit Val.unit.1)) := hv ▸ v.2
    exact (stuckAt_unit_app (ℍ := ℍ) Val.unit).not_val this
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])

theorem unitV_all (δ : LSub) (k : Nat) : thunkUnit (ℍ := ℍ) δ k unitV PMap.empty := by
  intro Θ' _ hOK c _ ls
  have hΦ := LocTy.view_down hOK.1 c
  refine (cN_ret_iff _ _ _ _ _ _ _ _).mpr ?_
  show erwp (ℍ := ℍ) (Θ'.view c) _ _ k ls (.app unitV.1 (.val .unit)) PMap.empty
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down)
    (fun k _ v ρ h => vN_down _ δ _ k v ρ h)
    (fun μ => step1Only_plug (ℍ := ℍ) (Head.beta μ Val.unit.1 Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit Val.unit.1) = Val.unit.1 := by
    simp [Kont.plug, Expr.subst, Val.unit]
  rw [e]
  exact erwp_val ⟨rfl, rfl⟩

/-- The family of `U(F 1)` at a cell at `β`. -/
def famTU (δ : LSub) (β : Life) : Nat → Val → SPropS Loc Val β :=
  fun j u r => thunkUnit (ℍ := ℍ) δ j u r.1

/-- The cell `ℓ ↦ mut(β, λ_. (), ∅, 𝒱₂⟦U(F 1)⟧)`. -/
def cellTU (δ : LSub) (l : Loc) (β : Life) : WRes :=
  ResU.single l (CellU.mutOf β unitV PMap.empty (ResU.inStratum_empty β) (famTU (ℍ := ℍ) δ β 2)
    (unitV_all δ 2))

/-- **The reseal at a location `Φ` does not type.** The cell is a value of the per-location
`Mut @β (U(F 1))` clause at the index `2`. At every `Φ` with `Φ ℓ = none` and every index `n`, no
`↭` step (`MutStep`, `UpdMutN`'s clause) from the cell reaches a cell whose predicate admits the
content `λ_. () ()`, which is in `𝒱⟦U(F 1)⟧` at the index `1`. -/
theorem reseal_untyped (δ : LSub) (l : Loc) (β : Life) :
    mutCellPL β (fun j u r => thunkUnit (ℍ := ℍ) δ j u r) 2 (Val.loc l)
      (cellTU (ℍ := ℍ) δ l β) ∧
    thunkUnit (ℍ := ℍ) δ 1 stuckV PMap.empty ∧
    ∀ (Φ : LocFam), Φ l = none → ∀ (n : Nat) (ψ' : CellU Loc Val),
      MutStep Φ n l (CellU.mutOf β unitV PMap.empty (ResU.inStratum_empty β)
        (famTU (ℍ := ℍ) δ β 2) (unitV_all δ 2)) ψ' →
      ¬ cellPred ψ' stuckV PMap.empty := by
  refine ⟨⟨l, unitV, PMap.empty, ResU.inStratum_empty β, 2, unitV_all δ 2, le_rfl, rfl,
    rfl⟩, stuckV_one δ, fun Φ hl n ψ' hs hp => ?_⟩
  have heq := hs.2.2.2.1 hl
  rw [← heq] at hp
  obtain ⟨_, hp⟩ := (mpred_mutOf _ _).mp hp
  exact stuckV_not_two (ℍ := ℍ) δ hp

end BoCa.Fig16.LogRel.Core.Chain.SI.Shape791N

/-! ## `ExtRLit791` -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub LifeVar)

/-- **`𝒱⟦U(Mut 'x 1 ⊸ F 1)⟧` with the Kripke order `E`**: `vN`'s `U` clause, reading `E` where
`vN` reads `LocTy.ExtR`, then `cN`'s `⊸` clause at the world reached. -/
def vUgen (E : LocTy → LocTy → WRes → Prop) (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat)
    (v : Val) (ρ : WRes) : Prop :=
  ∀ Θ' : LocTy, E Θ Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ → ∀ ls : List SRec,
    ∀ c', ∀ k, k ≤ n → ∀ (w : Val) (ρv ρ' : WRes),
      ResU.CompS ρ ρv ρ' → vN (ℍ := ℍ) (.mut (.var x) .unit) δ Θ' k w ρv → ConsistentX c' ρ' →
        cN (ℍ := ℍ) (.ret .unit) δ Θ' c' k ls (.app (forceE (tyC x) v.1) (.val w)) ρ'

/-- At the interpretation's own order, `vUgen` is `vN`. -/
theorem vN_eq_vUgen (x : LifeVar) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes) :
    vN (ℍ := ℍ) (.thunk (tyC x)) δ Θ n v ρ ↔ vUgen (ℍ := ℍ) LocTy.ExtR x δ Θ n v ρ := by
  simp only [vNE, cN, tyC, vUgen]

/-- **Under the literal order the thunk is valid at the empty world**: every literal extension
keeps nothing above `b`, so none has a key at `α > b`, and no `Mut @α 1` argument exists. -/
theorem valid_at_empty (x : LifeVar) (δ : LSub) {α b : Life} (hbα : b < α) (m : Loc) (n : Nat)
    (v : Val) : vUgen (ℍ := ℍ) ExtRL x (δ.extend x α) LocTy.empty n v (ρb m b) := by
  intro Θ' hE _ c _ ls c' k _ w ρv ρ' _ hv _
  exfalso
  obtain ⟨β, hβ, b', hβb', ⟨l', _, _, _, _, _, _, _, hl, _⟩, -⟩ := hv
  rw [interp_ext_self] at hβ
  cases Option.some.inj hβ
  have habove := hE.2 b (cellIn_ρb m b)
  have h := congrArg (fun Θ : LocTy => Θ l' b') habove
  simp only [LocTy.above_apply, if_pos (lt_of_lt_of_le hbα hβb'), LocTy.empty_apply] at h
  rw [h] at hl
  cases hl

/-- **Under the literal order the thunk is not valid at the world with a lend at `α`**: that world
holds the argument `ℓ′ ↦ mut(α, (), ∅, 𝒱⟦1⟧)`, and `() ℓ′` is stuck. -/
theorem not_valid_at_lend (x : LifeVar) (δ : LSub) {N α b : Life} (hNα : N < α) {m l' : Loc}
    (hml : l' ≠ m) {n : Nat} (hn : 0 < n) :
    ¬ vUgen (ℍ := ℍ) ExtRL x (δ.extend x α)
      (LocTy.empty.add l' α (famL α (fun Θ j u r => vN (ℍ := ℍ) .unit (δ.extend x α) Θ j u r)
        LocTy.empty)) n Val.unit (ρb m b) := by
  intro h
  let P : CPredL := fun Θ j u r => vN (ℍ := ℍ) .unit (δ.extend x α) Θ j u r
  let Θ₁ := LocTy.empty.add l' α (famL α P LocTy.empty)
  have hfam : DownFam α (famL α P LocTy.empty) := vN_fam_down .unit _ α _
  have hOK : Θ₁.OK := ⟨LocTy.down_add LocTy.empty_down l' hfam,
    ⟨N, LocTy.fresh_add (N := N) (fun _ _ h => absurd rfl h) le_rfl hNα l' _⟩⟩
  have hw : famL α P LocTy.empty n Val.unit ⟨PMap.empty, ResU.inStratum_empty α⟩ := ⟨rfl, rfl⟩
  let cell : WRes := ResU.single l' (CellU.mutOf α Val.unit PMap.empty
    (ResU.inStratum_empty α) (famL α P LocTy.empty n) hw)
  have hv : vN (ℍ := ℍ) (.mut (.var x) .unit) (δ.extend x α) Θ₁ n (Val.loc l') cell :=
    ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL LocTy.empty l' α P le_rfl _ hw,
      fun _ _ _ r h => by obtain ⟨-, rfl⟩ := h; exact ResU.inStratum_empty α⟩
  obtain ⟨ρ', hρ'⟩ := (ResU.compS_defined_iff (ρb m b) cell).mpr
    (compatS_single_of_get_none (ResU.single_get_ne _ hml))
  let c : Loc → Option Life := fun y => if y = m then some b else none
  let c' : Loc → Option Life := fun y => if y = m then some b else if y = l' then some α else none
  have hcb : ConsistentX c (ρb m b) :=
    consistentX_single_mut (consistentX_empty c) (by simp [c])
  have hcb' : ConsistentX c' (ρb m b) :=
    consistentX_single_mut (consistentX_empty c') (by simp [c'])
  have hcc : ConsistentX c' cell :=
    consistentX_single_mut (consistentX_empty c') (by simp [c', hml])
  have hc' : ConsistentX c' ρ' := consistentX_compS hρ' hcb' hcc
  have h' := (cN_ret_iff _ _ _ _ _ _ _ _).mp
    (h Θ₁ (extRL_refl _ _) hOK c hcb [] c' n le_rfl (Val.loc l') cell ρ' hρ' hv hc')
  obtain ⟨μ, hH, hT, htg, hl, hfd⟩ := world_two hml _ trivial _ hw hρ'
  change erwp (ℍ := ℍ) _ _ _ n [] (BoCa.BoLo.Kont.hole.plug (.app .unit (Val.loc l').1)) ρ' at h'
  rw [erwp_eq] at h'
  have hfin : Final (ℍ := ℍ) μ (BoCa.BoLo.Kont.hole.plug (.app .unit (Val.loc l').1)) :=
    fun _ _ hs => stuck_no_step (stuckAt_unit_app (Val.loc l')) .hole hs
  have hE := h' PMap.empty ρ' [] μ hH (compS_empty_left ρ') hT htg
    (ImmTieL.of_nil rfl _) hl hfd 0 _ _ hn (.refl _ _) hfin
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, hq⟩ := hE
  rcases hq with ⟨v, hv, -⟩ | ⟨_, _, _, _, _, h''⟩ | ⟨_, _, _, _, _, h''⟩
  · have : IsVal (BoCa.BoLo.Kont.hole.plug (.app .unit (Val.loc l').1)) := hv ▸ v.2
    exact (stuckAt_unit_app (ℍ := ℍ) (Val.loc l')).not_val this
  · exact absurd (pure_sep_iff.mp h'').1.2.2.1 (by simp [OpTabN.empty])
  · exact absurd (pure_sep_iff.mp h'').1.2.2.1 (by simp [OpTabN.empty])

/-- **The literal reading of Core's `Ext` breaks `vN_extA` at `U`.** Both worlds are `OK`, the
second is an `ExtA` extension of the first (a fresh lend), and a value of
`U(Mut 'x 1 ⊸ F 1)` under the literal order at the first is not one at the second. At the
interpretation's order `LocTy.ExtR`, `vN_extA` holds at every type. -/
theorem extRL_breaks_extA :
    ∃ (x : LifeVar) (δ : LSub) (Θ Θ' : LocTy) (n : Nat) (v : Val) (ρ : WRes),
      Θ.OK ∧ Θ'.OK ∧ Θ.ExtA Θ' ∧ vUgen (ℍ := ℍ) ExtRL x δ Θ n v ρ ∧
        ¬ vUgen (ℍ := ℍ) ExtRL x δ Θ' n v ρ := by
  let α : Life := OrderDual.toDual 1
  let b : Life := OrderDual.toDual 2
  have hbα : b < α := OrderDual.toDual_lt_toDual.mpr (by decide)
  let P : CPredL := fun Θ j u r => vN (ℍ := ℍ) .unit ((LSub.empty : LSub).extend 0 α) Θ j u r
  have hfam : DownFam α (famL α P LocTy.empty) := vN_fam_down .unit _ α _
  refine ⟨0, LSub.empty.extend 0 α, LocTy.empty, LocTy.empty.add 1 α (famL α P LocTy.empty), 1, Val.unit,
    ρb 0 b, LocTy.empty_ok, ⟨LocTy.down_add LocTy.empty_down 1 hfam,
      ⟨b, LocTy.fresh_add (N := b) (fun _ _ h => absurd rfl h) le_rfl hbα 1 _⟩⟩,
    LocTy.extA_add (fun _ _ h => absurd rfl h) 1 _, valid_at_empty 0 _ hbα 0 1 _,
    not_valid_at_lend 0 _ hbα (by decide) (by decide)⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791

/-! ## `Kappa835N` -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Kappa835N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791
open BoCa.Lifetime (LSub LifeVar)

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
  have h' := (cN_ret_iff _ _ _ _ _ _ _ _).mp (h.1 c 1 le_rfl (Val.loc l') cell ρ' hρ' hv hc')
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

end BoCa.Fig16.LogRel.Core.Chain.SI.Kappa835N

/-! ## `Public835N` -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Public835N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.Kappa835N
open BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791
open BoCa.Lifetime (LSub LifeVar)

/-- **The handled continuation owed along the public order** (DNB's `K⟦τ⟧`, read at `U`): at
every public extension of the stop's world at the floor `lo`, every view consistent with the
share and every record list, `κ` is in `𝒞⟦C⟧`. -/
def KapRelP (lo : Life) (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (κ : Val) (ρ : WRes) : Prop :=
  ∀ Θ' : LocTy, Θ.ExtP lo Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ → ∀ ls,
    cN (ℍ := ℍ) C δ Θ' c n ls (forceE C κ.1) ρ

/-- **The world with the key `(ℓ′, α)` is a public extension of the empty world** at every floor
the key is below. -/
theorem extP_world (x : LifeVar) (δ : LSub) {α lo : Life} (hα : α ≤ lo) (l' : Loc) (ρ : WRes) :
    LocTy.empty.ExtP lo (Θ₁ (ℍ := ℍ) x δ α l') ρ :=
  LocTy.extP_add (fun _ _ h => absurd rfl h) hα l' _ ρ

/-- Above the key, the same world is a private move. -/
theorem not_extP_world (x : LifeVar) (δ : LSub) {α lo : Life} (hlo : lo < α) (l' : Loc)
    (ρ : WRes) : ¬ LocTy.empty.ExtP lo (Θ₁ (ℍ := ℍ) x δ α l') ρ := by
  intro h
  have := h.2.1 l' α hlo
  rw [LocTy.add_self] at this
  simp [LocTy.empty] at this

/-- **The world configuration is excluded by the public reading**: the stuck `κ = ()` is not owed
along `ExtP` at the empty world, at any floor above the key. -/
theorem not_kapRelP_world (x : LifeVar) (δ : LSub) {N α b lo : Life} (hNα : N < α) (hα : α ≤ lo)
    {m l' : Loc} (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b)
    (hcl : c l' = some α) :
    ¬ KapRelP (ℍ := ℍ) lo (kTyC x) (δ.extend x α) LocTy.empty 1 Val.unit (ρb m b) := fun h =>
  not_kTy_at x δ hml c hcm hcl (h _ (extP_world x _ hα l' _) (Θ₁_ok x _ hNα l') c
    (consistentX_single_mut (consistentX_empty c) hcm) [])

/-- **The view configuration is excluded by the public reading**: at the world with the key, the
obligation reaches the view that puts `ℓ′` at `α`. -/
theorem not_kapRelP_view (x : LifeVar) (δ : LSub) {N α b : Life} (hNα : N < α) (lo : Life)
    {m l' : Loc} (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b)
    (hcl : c l' = some α) :
    ¬ KapRelP (ℍ := ℍ) lo (kTyC x) (δ.extend x α) (Θ₁ (ℍ := ℍ) x (δ.extend x α) α l') 1 Val.unit
      (ρb m b) := fun h =>
  not_kTy_at x δ hml c hcm hcl (h _ (LocTy.extP_refl _ _ _) (Θ₁_ok x _ hNα l') c
    (consistentX_single_mut (consistentX_empty c) hcm) [])

end BoCa.Fig16.LogRel.Core.Chain.SI.Public835N

/-! ## `LendExit835N` -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.LendExit835N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.BoLo (Kont performE raiseE opPayload)
open BoCa.Fig16.LogRel.Core.Chain.SI.Kappa835N
open BoCa.Fig16.LogRel.Core.Chain.SI.ExtRLit791
open BoCa.Fig16.LogRel.Core.Chain.SI.Public835N
open BoCa.Lifetime (LSub LifeVar)

/-- **`κ` owed along `ExtR`**: at every extension of the stop's world along `ExtR` at the share,
every view consistent with the share and every record list, `κ` is in `𝒞⟦C⟧`. -/
def KapRelR (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (κ : Val) (ρ : WRes) : Prop :=
  ∀ Θ' : LocTy, Θ.ExtR Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ → ∀ ls,
    cN (ℍ := ℍ) C δ Θ' c n ls (forceE C κ.1) ρ

/-- **`U` at `vN` is `KapRelR`.** -/
theorem vN_thunk_iff_kapRelR (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (κ : Val) (ρ : WRes) :
    vN (ℍ := ℍ) (.thunk C) δ Θ n κ ρ ↔ KapRelR (ℍ := ℍ) C δ Θ n κ ρ :=
  Iff.rfl

/-- **A public extension of the empty world at `α` holds no `Mut` value at a lifetime above `α`**:
such a value is at a key at or above its lifetime, and `ExtP α` adds no key above `α`. -/
theorem not_bMut_extP (x : LifeVar) (δ : LSub) {α β : Life} (hαβ : α < β) {Θ' : LocTy}
    {ρ : WRes} (hE : LocTy.empty.ExtP α Θ' ρ) {k : Nat} {w : Val} {σ : WRes} :
    ¬ vN (ℍ := ℍ) (bMut x) (δ.extend x β) Θ' k w σ := by
  rintro ⟨a, ha, b, hab, ⟨l, _, _, _, _, _, _, _, hl, _⟩, -⟩
  rw [interp_ext_self] at ha
  cases Option.some.inj ha
  rw [hE.2.1 l b (lt_of_lt_of_le hαβ hab)] at hl
  simp at hl

/-- **The obligation at the lowered floor `α` holds of the stuck `κ`** at the empty world, when the
answer type's lifetime `β` is above `α`. -/
theorem kapRelP_floor_world (x : LifeVar) (δ : LSub) {α β : Life} (hαβ : α < β) (κ : Val)
    (ρ : WRes) : KapRelP (ℍ := ℍ) α (kTyC x) (δ.extend x β) LocTy.empty 1 κ ρ := by
  intro Θ' hE _ c _ ls
  exact ⟨fun _ _ _ _ _ _ _ hv _ => absurd hv (not_bMut_extP x δ hαβ hE), trivial⟩

/-- **The floored reading after a lend's exit.** The stop at the empty world, at the lowered floor
`α`, owes the stuck `κ = ()` nothing along `ExtP α`; `U` read along `ExtP lo`, at the floor
`lo ≥ β > α` of a handler around the lender, reaches the world with a key at `β`, where `κ` fails. -/
theorem flooredExit (x : LifeVar) (δ : LSub) {N α β b lo : Life} (hNβ : N < β) (hαβ : α < β)
    (hβ : β ≤ lo) {m l' : Loc} (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b)
    (hcl : c l' = some β) :
    α < lo ∧ KapRelP (ℍ := ℍ) α (kTyC x) (δ.extend x β) LocTy.empty 1 Val.unit (ρb m b) ∧
      ¬ KapRelP (ℍ := ℍ) lo (kTyC x) (δ.extend x β) LocTy.empty 1 Val.unit (ρb m b) :=
  ⟨lt_of_lt_of_le hαβ hβ, kapRelP_floor_world x δ hαβ _ _,
    not_kapRelP_world x δ hNβ hβ hml c hcm hcl⟩

/-- **The order outside `Sched` excludes the same `κ`**: `ExtR` reaches the world with the key at
`β` from the empty world at every floor, where `κ = ()` fails. -/
theorem not_kapRelR_world (x : LifeVar) (δ : LSub) {N β b : Life} (hNβ : N < β) {m l' : Loc}
    (hml : l' ≠ m) (c : Loc → Option Life) (hcm : c m = some b) (hcl : c l' = some β) :
    ¬ KapRelR (ℍ := ℍ) (kTyC x) (δ.extend x β) LocTy.empty 1 Val.unit (ρb m b) := fun h =>
  not_kTy_at x δ hml c hcm hcl (h _ ((LocTy.extA_add (fun _ _ h => absurd rfl h) l' _).extR _)
    (Θ₁_ok x _ hNβ l') c (consistentX_single_mut (consistentX_empty c) hcm) [])

/-- **The configuration at concrete lifetimes**: the share's cell at `0` lent at the top lifetime,
the handler's floor and the key's lifetime `1`, the floor after the exit `2`, the key at `1`. -/
theorem flooredExit_inst :
    let α : Life := OrderDual.toDual 2
    let β : Life := OrderDual.toDual 1
    let b : Life := OrderDual.toDual 0
    let c : Loc → Option Life := fun y => if y = 0 then some b else if y = 1 then some β else none
    α < β ∧ KapRelP (ℍ := ℍ) α (kTyC 0) (LSub.empty.extend 0 β) LocTy.empty 1 Val.unit (ρb 0 b) ∧
      ¬ KapRelP (ℍ := ℍ) β (kTyC 0) (LSub.empty.extend 0 β) LocTy.empty 1 Val.unit (ρb 0 b) ∧
      ¬ KapRelR (ℍ := ℍ) (kTyC 0) (LSub.empty.extend 0 β) LocTy.empty 1 Val.unit (ρb 0 b) ∧
      ConsistentX c (ρb 0 b) := by
  intro α β b c
  have hαβ : α < β := OrderDual.toDual_lt_toDual.mpr (by decide)
  obtain ⟨-, h₁, h₂⟩ := flooredExit (ℍ := ℍ) 0 LSub.empty hαβ hαβ le_rfl (m := 0) (l' := 1)
    (by decide) c rfl rfl
  exact ⟨hαβ, h₁, h₂, not_kapRelR_world 0 LSub.empty hαβ (m := 0) (l' := 1) (by decide) c rfl rfl,
    consistentX_single_mut (consistentX_empty c) rfl⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.LendExit835N


/-! ## `Lend791N` -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg (noOwn_single_mut)
open BoCa.BoLo (Head Kont)
open BoCa.Lifetime (LSub LifeVar)

/-- **`λ_. λu. ()` is a callback of the lend at the empty row and the answer `1`**: it performs
nothing, and the borrow is left as garbage at the return (admissible: Core has `releaseMut`).
A callback that performs at a suspending row while holding the borrow is `cbPerform_sem`
(`Core/Chain/ConstKW835N.lean`). -/
theorem cbRelease_sem {x : LifeVar} {bnd : Lifetime.Life} {A : VTy} {δ : LSub}
    (Θ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (cbUTy x bnd (.mut (.var x) A) .unit []) δ Θ n cbRelease PMap.empty := by
  intro Θ' _ hOK c _ ls
  refine fun α _ c' k _ v ρv ρ' hc hv _ => ?_
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨β, hβ, b, -, ⟨l, w, χ, hχ, j, hw, -, rfl, -, rfl⟩, -⟩ := hv
  have hΦ := LocTy.view_down hOK.1 c'
  have hQ : PostN.Down
      (fun k _ v ρ => vN (ℍ := ℍ) (.box (.var x) .unit) (δ.extend x α) Θ' k v ρ) :=
    fun k _ v ρ h => vN_down _ _ _ k v ρ h
  refine (cN_ret_iff _ _ _ _ _ _ _ _).mpr ?_
  show erwp (ℍ := ℍ) (Θ'.view c') (opTableN OpTabN.empty) _ k ls
    (.app (.app cbRelease.1 (.val .unit)) (.val (Val.loc l))) _
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl (.appL .hole (Val.loc l))) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  simp only [Kont.plug, Expr.subst, Val.unit, Expr.val]
  exact erwp_garbage (compS_empty_left _) (noOwn_single_mut l)
    (erwp_val (v := Val.unit) ⟨α, interp_ext_self δ x α, ⟨rfl, rfl⟩, ResU.inStratum_empty α⟩)

/-- **`U(F 1)` has values outside every stratum `↓α`**: `λ_. ()` holding a short `mut` cell as
garbage. -/
theorem answer_not_inStratum (δ : LSub) (α : Life) (l : Loc) :
    ∃ ρ : WRes, (∀ Θ n, vN (ℍ := ℍ) (.thunk (.ret .unit)) δ Θ n unitThunk ρ) ∧
      ¬ ρ.InStratum (↓α) := by
  refine ⟨ResU.single l (CellU.mutOf (↓(↓α)) Val.unit PMap.empty
    (ResU.inStratum_empty _) (fun _ _ => True) trivial), fun Θ n Θ' _ hOK c _ ls => ?_,
    fun h => ?_⟩
  · have hΦ := LocTy.view_down hOK.1 c
    refine (cN_ret_iff _ _ _ _ _ _ _ _).mpr ?_
    show erwp (ℍ := ℍ) (Θ'.view c) (opTableN OpTabN.empty) _ n ls
      (.app unitThunk.1 (.val .unit)) _
    refine erwp_det hΦ (opTableN_down OpTabN.empty_down)
      (fun k _ v ρ h => vN_down _ _ _ k v ρ h)
      (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
    simp only [Kont.plug, Expr.subst, Val.unit, Expr.val]
    exact erwp_garbage (compS_empty_left _) (noOwn_single_mut l)
      (erwp_val (v := Val.unit) ⟨rfl, rfl⟩)
  · have := h l _ (ResU.single_get_self _ _)
    rw [CellU.inStratum_mutOf] at this
    exact lt_asymm this (Life.down_sqsubset _)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
