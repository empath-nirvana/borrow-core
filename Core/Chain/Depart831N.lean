import Core.Chain.ImmLend833N

/-!
# Two departures of the lemma interface, checked  `[spec §62]`

`docs/new-core/scope-831-interface.md` §6.3.

## K4/V10: `Keeps` by lifetime

Core's `Keeps rs rs′ ρ := ∀ r ∈ rs, Rel r ρ → r ∈ rs′` (`Core/FrameRecords.lean`) reads relevance
off the record's location. Core reaches it only through `ext_drop`'s premise, which it discharges
inside a run, at the Imm Frame's exit, by `not_rel_lineage` from the run's `FrameLife`, `AgW` and
`ICpAt`. The chain does the same at the run's record list: `erwp_I_frameR`'s `hQ` is Core's `Ext`
on lists, and its exit is Core's.

The world's records (`LocTy.imm`) are a second carrier, which `vN`'s `Imm` clause reads.
`tabN_unwind_eq` (`Core/Chain/ImmLend833N.lean`) moves the world-level step outside any run. It
identifies the callback's table at `Θ + (p, α)` with the lender's at `Θ`, and it does that by
moving every value of every operation's argument type, at a resource in `Res_α`, from the world
with the record to the world without it (`LocTy.extR_of_addImm`). A table is a function of the
world and the view. It has no run, so there is no `FrameLife`, `AgW` or `ICpAt` for
`not_rel_lineage` to read.

`LocTy.KeepsLoc`/`LocTy.ExtRLoc` are Core's reading at the world: `Keeps` on `rsOf Θ.imm`, and
`ExtR`'s key conjunct unchanged. `UnwindArgStepLoc` is the step `tabN_unwind_eq` takes, read that
way, at every value of an `Imm` type. **It fails** (`not_unwindArgStepLoc`). The configuration
`unwindArg_inst` is an `OK` world holding one record `q`, lent at `γ = 1` at `ℓ`, and a record
`p ≠ q` at the same location, lent at `α = 2 ⊏ γ`. The resource is `ℓ ↦ imm({γ}, …)`. It is a
value of `Imm 'y (Ref 1)` at `δ['y ↦ γ]` in the world with `p`, witnessed by `q`, and it lies in
`Res_α`. `Rel p ρ` holds there, and `p` is not a record of the world without it. Under the
lifetime reading the same step holds (`unwindArg_inst`'s fourth conjunct, by
`LocTy.extR_of_addImm`).

This configures the step, not `tabN_unwind_eq` itself. The step is the one Core never takes,
because Core's table does not read the record list (`Row.tab_local`, `hS.tab_extend`). Core moves a
stop's argument along `Ext` inside the frame instead (`opTable_ext` at `hQ`).

## E13: a `Div` row is a table row

Core's `ewpTS` is a least fixed point, so a run that ticks forever is not in it, and at a row that
holds `Div` Core takes the greatest fixed point over segments (`cwp`, `Core/DivDefs.lean`).
`erwp` at `n` constrains only the runs of fewer than `n` steps that reach a final configuration.
So a computation with no final configuration is in `erwp` at every index, whatever the table
and the postcondition (`erwp_of_noFinal`), and no fixed point needs to be added to admit it. The
chain's `F_Σ R` is `erwp` at the row's table at every row (`cN_effOf`), whether or not the row
holds `Div` (`cN_effOf_divB`). Core's split on `Row.divB` is a split between `CDerives`
constructors (`effThen`, `effThenDiv`) and between `effWp`'s branches. The first is kept as
printed. Under the second, both branches go to `erwp`.
-/

noncomputable section

open Classical

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Depart831N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel.Core.Chain.SI.ImmRec791N (recT cellI escU escU_inStratum)
open BoCa.Lifetime (LSub LifeVar)

/-! ### K4/V10 -/

/-- **Core's `Keeps` at the world**: the records of `Θ` relevant to `ρ` by location (`Rel`) are
records of `Θ′`. -/
def _root_.BoCa.Fig16.LogRel.Core.Chain.SI.LocTy.KeepsLoc (Θ Θ' : LocTy) (ρ : WRes) : Prop :=
  Keeps (rsOf Θ.imm) (rsOf Θ'.imm) ρ

/-- `LocTy.ExtR` with its record conjunct read by location. -/
def _root_.BoCa.Fig16.LogRel.Core.Chain.SI.LocTy.ExtRLoc (Θ Θ' : LocTy) (ρ : WRes) : Prop :=
  (∀ l a F, Θ l a = some F → CellIn ρ a → Θ' l a = some F ∧ Θ'.above a = Θ.above a) ∧
    Θ.KeepsLoc Θ' ρ

/-- **The step `tabN_unwind_eq` takes, under the location reading**: a value of an `Imm` type at
the world with a record lent at `α`, at a resource in `Res_α`, is at an extension of the world
without the record. -/
def UnwindArgStepLoc : Prop :=
  ∀ (Θ : LocTy) (p : FrameRec) (α : Life) (a : Lifetime.Life) (A : VTy) (δ : LSub) (n : Nat)
    (v : Val) (ρ : WRes), Θ.OK → vN (ℍ := ℍ) (.imm a A) δ (Θ.addImm (p, α)) n v ρ →
    ρ.InStratum α → (Θ.addImm (p, α)).ExtRLoc Θ ρ

/-- The configuration's world: the one record `q`, lent at `γ = 1`. -/
def Θq (y : LifeVar) (l l' : Loc) : LocTy :=
  LocTy.empty.addImm (recT (.ref .unit) (LSub.empty.extend y (OrderDual.toDual 1)) l l',
    OrderDual.toDual 1)

/-- A record at `ℓ` other than `q`. -/
def pRec (l l' : Loc) : FrameRec := ⟨l, Val.loc l', escU l', .unit, LSub.empty⟩

theorem pRec_ne (y : LifeVar) (l l' : Loc) :
    pRec l l' ≠ recT (.ref .unit) (LSub.empty.extend y (OrderDual.toDual 1)) l l' := by
  intro e
  have := congrArg FrameRec.T e
  simp [pRec, recT] at this

theorem Θq_ok (y : LifeVar) (l l' : Loc) : (Θq y l l').OK :=
  ⟨fun l₀ b F h => LocTy.empty_down l₀ b F h,
    let ⟨N, hN⟩ := LocTy.empty_bounded; ⟨N, fun l₀ b h => hN l₀ b h⟩⟩

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

/-- **The same step under the lifetime reading holds at every value** (`LocTy.extR_of_addImm`). -/
theorem unwindArgStep (Θ : LocTy) (p : FrameRec) {α : Life} {ρ : WRes}
    (hρ : ρ.InStratum α) : (Θ.addImm (p, α)).ExtR Θ ρ :=
  LocTy.extR_of_addImm Θ p hρ

/-! ### E13 -/

/-- **A computation with no final configuration is in `erwp` at every index**, at every table
and postcondition: `erwp` reads only the runs that end. -/
theorem erwp_of_noFinal {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (h : ∀ (μ : BoCa.BoLo.Heap) j μ' e', StepsN (ℍ := ℍ) j μ e μ' e' → ¬ Final (ℍ := ℍ) μ' e') :
    erwp (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  rw [erwp_eq]
  intro _ _ _ μ _ _ _ _ _ _ _ j μ' e' _ hrun hfin
  exact absurd hfin (h μ j μ' e' hrun)

/-- **`F_Σ R` is `erwp` at the row's table on both sides of Core's split on `Row.divB`.** -/
theorem cN_effOf_divB (S : Row) (b : Bool) (_hb : Row.divB S = b) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes) :
    cN (ℍ := ℍ) (CTy.effOf S R) δ Θ c n ls e ρ ↔
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c))
        (fun k _ v ρ => vN (ℍ := ℍ) R δ Θ k v ρ) n ls e ρ :=
  cN_effOf S R δ Θ c n ls e ρ

end BoCa.Fig16.LogRel.Core.Chain.SI.Depart831N

end
