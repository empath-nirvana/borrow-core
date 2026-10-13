import DenseCarrier.Shift
import Core.Invariant
import ProbeD1.SegShift
import ProbeD1.BridgeProbe

/-!
# DenseCarrier — re-slotting a region: cells, records and reading moved together

ProbeD1's segment shift (`SegShift.SegShiftInv`, `Bridge.CoreThawTop`) moves a configuration by a
re-stratification `θ : Restrat.Emb c` of the slots: every cell is re-slotted by `θ.relRU` (its
lifetime moved by `θ`, its witness moved, its stored predicate moved to its image), every record
by `Targets.srecRestrat θ`, and the reading by `θ`. Over the lifetime order `L` the slots stay
where `ι` puts them, so a re-slotted cell sits at the position `ι (θ s)`, and the reading moves by
any `ψ : L → L` that agrees with `ι ∘ θ ∘ ι⁻¹` on the slots' positions (`hψ`). At `WithTop ℚ` with
Core's slots at `-n`, `Shift.lean`'s position shift `shiftQ` is such a `ψ` (`shiftQ_ratSlots`).

**The move does not preserve the relation**, inside the fragment, at every lifetime order:

* `not_vD_mm_relRU`: at `Mut 'a (Mut 'b 1)` no re-slotted resource is related, once some slot `g`
  with no preimage under `θ` sits at or above `@'b` in `L`. The inner `Mut 'b 1` holds at a
  `mut` cell at `g`; the re-slotted outer cell stores an image, which holds only at re-slotted
  resources (`ofS_relS_ne_vD_mb`). It is `Restrat.MutCounterexample.mut_not_natural`'s mechanism
  with `Mut` in place of `Imm`: no `Imm` is needed.
* `not_wpTS_mm_relRU`: no re-slotted typed world runs to a value of `Mut 'a (Mut 'b 1)` there
  either: `↭` keeps each `mut` cell's stored predicate, and every `mut` cell of a re-slotted
  flattening stores an image (`Restrat.Emb.flatAt_mut_moved`).
* `not_reslotInvV`, `not_reslotInvC`: for every `L`, every `ι`, every re-slotting `θ` other than
  the identity and every `ψ` agreeing with `ι ∘ θ ∘ ι⁻¹` on the slots, a configuration is related
  before the move and not after, at `Mut 'a (Mut 'b 1)` and at `F (Mut 'a (Mut 'b 1))`: a borrow
  of a borrow (`rhoMM`), a typed world (`tw_nested`).
* `reslotFailsAtEveryCut`: in particular every segment shift `Restrat.Emb.shift c k`, `k > 0`, at
  every cut `c`.
* `not_bridgeV`: re-slotting the resource and the records is not moving the slots' positions
  (`ι` to `ι ∘ θ`). It fails without `Imm`, so no extension of the fragment restores it.
* `not_denseThawTop`: the dense analogue of `Bridge.not_coreThawTop`, at every `L` and `ι`.
* In Core (`L = Life`, the identity placement, through `cD_id`): `core_reslot_fails`,
  `not_segShiftInv_noAll`, `not_coreThawTop_noAll`, at a type with no `∀`.
* No slot in the gap: a placement of the slots keeps their order and never creates room between
  two of them (`slots_between_iff`, `no_slot_between_adjacent`, `placement_keeps_order`), and the
  gap probe 1's position shift opens in `L` holds no slot (`shiftSlots_gap_empty`).

What re-slotting cannot do is the gap: `θ` leaves slots with no preimage, and the relation at the
moved reading reads cells there.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)
open GhostEnd (innerView unitQ unitQ_holds)

variable {L : Type} [LinearOrder L] [OrderTop L]

/-! ### The type -/

/-- `Mut 'b 1`, with `'b = 1`. -/
abbrev mb : VTy := .mut (.var 1) .unit

/-- `Mut 'a (Mut 'b 1)`, with `'a = 0`. -/
abbrev mm : VTy := .mut (.var 0) mb

theorem fragV_mm : FragV mm := trivial

theorem fragC_retMM : FragC (.ret mm) := trivial

/-- A value of `Mut 'x A` over `L`: a location, and a single `mut` cell at a slot whose position is
at or above `@'x`, storing `𝒱⟦A⟧`. -/
theorem vD_mut_inv (ι : Slots L) {x : LifeVar} {A : VTy} {ls : List SRec} {δ : LSubD L}
    {v : Val} {ρ : WRes} (h : vD (ℍ := ℍ) ι (.mut (.var x) A) ls δ v ρ) :
    ∃ α ℓ, δ.find? x = some α ∧ v = .loc ℓ ∧
      ptoMutD ι ℓ α ls (fun ls₀ => vD (ℍ := ℍ) ι A ls₀ δ) ρ := by
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨hv, hp⟩ := pure_sep_iff.mp hsep
  exact ⟨α, ℓ, hα, hv, hp⟩

/-! ### The gap -/

/-- **An image predicate is not `𝒱⟦Mut 'b 1⟧`** once a slot `g` with no preimage under `θ` sits at
or above `@'b` in `L`: the type holds at a `mut` cell at `g`, the image only at re-slotted
resources. -/
theorem ofS_relS_ne_vD_mb (ι : Slots L) {c : Life} (θ : Restrat.Emb c) {g : Life}
    (hg : ∀ x, θ x ≠ g) {δ : LSubD L} {β : L} (hβ : δ.find? 1 = some β) (hβg : β ≤ ι g)
    {b₀ : Life} (Q₀ : Val → SPropS Loc Val b₀) (ls₀ : List SRec) :
    ofS (θ.relS b₀ Q₀) ≠ vD (ℍ := ℍ) ι mb ls₀ δ := by
  intro h
  have hgap : vD (ℍ := ℍ) ι mb ls₀ δ (.loc 0) (innerView 0 g) :=
    ⟨β, hβ, 0, pure_sep_mk rfl (ptoMutD_innerView_le ι hβg ls₀ δ)⟩
  rw [← h, θ.ofS_relS] at hgap
  obtain ⟨r₀, hr₀, -⟩ := hgap
  have hc := congrArg (fun r => PMap.get r 0) hr₀
  simp only [Restrat.Emb.relRU_get, innerView, ResU.single_get_self] at hc
  obtain ⟨ψ, -, hψ⟩ := Option.map_eq_some_iff.mp hc
  have hat := congrArg CellU.at hψ
  rw [Restrat.Emb.at_relU, CellU.at_mutOf] at hat
  exact hg _ hat

/-- **No re-slotted resource is related at `Mut 'a (Mut 'b 1)`** once a slot with no preimage
under `θ` sits at or above `@'b` in `L`. -/
theorem not_vD_mm_relRU (ι : Slots L) {c : Life} (θ : Restrat.Emb c) {g : Life}
    (hg : ∀ x, θ x ≠ g) {δ : LSubD L} {β : L} (hβ : δ.find? 1 = some β) (hβg : β ≤ ι g)
    (ls : List SRec) (v : Val) (ρ : WRes) : ¬ vD (ℍ := ℍ) ι mm ls δ v (θ.relRU ρ) := by
  intro h
  obtain ⟨α, ℓ, -, -, b, u, σ, hσ, Q, hw, ls₀, -, hρ, hQ, -, -⟩ := vD_mut_inv ι h
  obtain ⟨ψ, hψ, -⟩ := θ.relRU_eq_single hρ
  rcases CellU.rep ψ with ⟨w, rfl⟩ | ⟨s, w, τ, m, rfl⟩ | ⟨b₀, w, τ, m, Q₀, w₀, rfl⟩
  · rw [Restrat.Emb.relU_ownOf] at hψ
    exact CellU.ownOf_ne_mutOf hψ.symm
  · rw [θ.relU_immOf] at hψ
    exact CellU.immOf_ne_mutOf hψ.symm
  · rw [θ.relU_mutOf] at hψ
    obtain rfl : b = θ b₀ := CellU.mutOf_at hψ
    obtain ⟨-, -, rfl⟩ := CellU.mutOf_inj hψ
    exact ofS_relS_ne_vD_mb ι θ hg hβ hβg Q₀ ls₀ hQ

/-- **No re-slotted typed world runs to a value of `Mut 'a (Mut 'b 1)`**, at any expression, once a
slot with no preimage under `θ` sits at or above `@'b` in `L`: the answer's cell stores a predicate
some `mut` cell of the start's flattening stores (`↭`), and those are images. -/
theorem not_wpTS_mm_relRU (ι : Slots L) {c : Life} (θ : Restrat.Emb c) {g : Life}
    (hg : ∀ x, θ x ≠ g) {δ : LSubD L} {β : L} (hβ : δ.find? 1 = some β) (hβg : β ≤ ι g)
    (e : Expr) (ρ : WRes) (hT : TW (θ.relRU ρ) [] []) :
    ¬ wpTS [] e (fun ls'' => vD (ℍ := ℍ) ι mm ls'' δ) (θ.relRU ρ) := by
  intro hwp
  have hval : ResU.Valid (θ.relRU ρ) := hT.valid
  obtain ⟨ρ', ρp, -, -, π, v, -, -, -, ls', -, -, -, -, -, -, -, hπ, hU, -, -, -, -, -, hQ⟩ :=
    hwp PMap.empty _ [] ⟨(compS_empty_left _).1, _, compS_empty_left _, hval⟩
      (compS_empty_left _) hT (fun _ hx => absurd hx List.not_mem_nil)
      BoCa.BoLo.Alloc.leastFree 0
  obtain ⟨α, ℓ, -, -, b, u, χ, hχ, Q, hw, ls₀, -, hρ', hQ', -, -⟩ := vD_mut_inv ι hQ
  have hg' : ρ'.get ℓ = some (CellU.mutOf b u χ hχ Q hw) := by rw [hρ']; simp
  have hf : π.FlatAt ℓ (CellU.mutOf b u χ hχ Q hw) :=
    ProbeD1.pvLocal π ρp ρ' hU.2.2 (ResU.CompS.comm hπ) ℓ _ hg' (CellU.kind_mutOf _ _ _ _ _ _)
  obtain ⟨v₀, χ₀, h₀, hw₀, k₀⟩ := (hU.1.2 ℓ b Q).mpr ⟨u, χ, hχ, hw, hf⟩
  obtain ⟨b₀, rfl⟩ := θ.flatAt_mut_lifetime k₀
  obtain ⟨Q₀, -, -, -, rfl, -, -⟩ := θ.flatAt_mut_moved k₀
  exact ofS_relS_ne_vD_mb ι θ hg hβ hβg Q₀ ls₀ hQ'

/-- **A re-slotting other than the identity leaves a gap below a slot it moves**: the least moved
slot `n` is not an image, and its image lies below it. -/
theorem exists_gap {c : Life} (θ : Restrat.Emb c) (hθ : ∃ x, θ x ≠ x) :
    ∃ n : ℕ, (∀ x, θ x ≠ OrderDual.toDual n) ∧ θ (OrderDual.toDual n) < OrderDual.toDual n := by
  classical
  have hex : ∃ n : ℕ, θ.toNat n ≠ n := by
    obtain ⟨x, hx⟩ := hθ
    exact ⟨OrderDual.ofDual x, fun h => hx (congrArg OrderDual.toDual h)⟩
  have hmin : ∀ m < Nat.find hex, θ.toNat m = m := fun m hm => not_not.mp (Nat.find_min hex hm)
  have hn : θ.toNat (Nat.find hex) ≠ Nat.find hex := Nat.find_spec hex
  have hgt : Nat.find hex < θ.toNat (Nat.find hex) :=
    lt_of_le_of_ne (θ.toNat_strictMono.id_le _) (Ne.symm hn)
  refine ⟨Nat.find hex, fun x hx => ?_, hgt⟩
  have hx' : θ.toNat (OrderDual.ofDual x) = Nat.find hex := congrArg OrderDual.ofDual hx
  rcases lt_trichotomy (OrderDual.ofDual x) (Nat.find hex) with h | h | h
  · rw [hmin _ h] at hx'; omega
  · rw [h] at hx'; exact hn hx'
  · have := θ.toNat_strictMono h; omega

/-! ### The configuration -/

section Config
variable (ι : Slots L) (δ : LSubD L) {si bo : Life}

/-- Every resource of `𝒱⟦Mut 'b 1⟧` lies in the stratum of `bo`, when `@'b` is the position of a
slot `si` above `bo`. -/
theorem vD_mb_inStratum (h1 : δ.find? 1 = some (ι si)) (hbs : bo < si) {ls : List SRec}
    {u : Val} {σ : WRes} (h : vD (ℍ := ℍ) ι mb ls δ u σ) : σ.InStratum bo := by
  obtain ⟨α, ℓ, hα, -, b, w, χ, hχ, Q, hw, ls₀, hαb, hρ, -⟩ := vD_mut_inv ι h
  rw [h1] at hα
  obtain rfl := Option.some.inj hα
  subst hρ
  exact ResU.inStratum_single _ (show bo < b from lt_of_lt_of_le hbs (ι.le_iff.mp hαb))

/-- The outer cell's stored predicate: `𝒱⟦Mut 'b 1⟧δ`, at the stratum `bo`. -/
def qOut (bo : Life) : Val → SPropS Loc Val bo :=
  fun v => SPropU.toS bo (vD (ℍ := ℍ) ι mb [] δ v)

theorem ofS_qOut (h1 : δ.find? 1 = some (ι si)) (hbs : bo < si) :
    ofS (qOut (ℍ := ℍ) ι δ bo) = vD (ℍ := ℍ) ι mb [] δ := by
  funext v r
  apply propext
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨vD_mb_inStratum ι δ h1 hbs h, h⟩⟩

theorem innerView_inStratum (ℓ' : Loc) (hbs : bo < si) : (innerView ℓ' si).InStratum bo :=
  ResU.inStratum_single _ hbs

theorem qOut_holds (ℓ' : Loc) (h1 : δ.find? 1 = some (ι si)) (hbs : bo < si) :
    qOut (ℍ := ℍ) ι δ bo (.loc ℓ') ⟨innerView ℓ' si, innerView_inStratum ℓ' hbs⟩ :=
  ⟨ι si, h1, ℓ', pure_sep_mk rfl (ptoMutD_innerView_le ι le_rfl [] δ)⟩

/-- `ℓ ↦ mut(bo, ℓ′, ℓ′ ↦ mut(si, (), ∅, 𝒱⟦1⟧), 𝒱⟦Mut 'b 1⟧δ)`: a borrow of a borrow. -/
def rhoMM (ℓ ℓ' : Loc) (h1 : δ.find? 1 = some (ι si)) (hbs : bo < si) : WRes :=
  ResU.single ℓ (CellU.mutOf bo (.loc ℓ') (innerView ℓ' si) (innerView_inStratum ℓ' hbs)
    (qOut (ℍ := ℍ) ι δ bo) (qOut_holds ι δ ℓ' h1 hbs))

/-- **The borrow of a borrow is related at `Mut 'a (Mut 'b 1)`** when `'a` reads the position of
the outer cell's slot and `'b` that of the inner one. -/
theorem vD_rhoMM (ℓ ℓ' : Loc) (h0 : δ.find? 0 = some (ι bo)) (h1 : δ.find? 1 = some (ι si))
    (hbs : bo < si) : vD (ℍ := ℍ) ι mm [] δ (.loc ℓ) (rhoMM (ℍ := ℍ) ι δ ℓ ℓ' h1 hbs) :=
  ⟨ι bo, h0, ℓ, pure_sep_mk rfl ⟨bo, .loc ℓ', innerView ℓ' si, innerView_inStratum ℓ' hbs,
    qOut ι δ bo, qOut_holds ι δ ℓ' h1 hbs, [], le_rfl, rfl, ofS_qOut ι δ h1 hbs,
    fun x => by simp, fun _ _ _ h => vD_mb_inStratum ι δ h1 hbs h⟩⟩

end Config

/-! ### The typed world of a borrow of a borrow -/

/-- A `mut` cell whose witness is a single `mut` cell with an empty witness is flattened to the
two cells side by side. -/
theorem flat_nested {ℓ ℓ' : Loc} {b b' : Life} {u u' : Val} {χ' : WRes}
    {h' : χ'.InStratum b'} {Q' : Val → SPropS Loc Val b'} {hw' : Q' u' ⟨χ', h'⟩}
    (hχ' : χ' = PMap.empty)
    {h : (ResU.single ℓ' (CellU.mutOf b' u' χ' h' Q' hw')).InStratum b}
    {Q : Val → SPropS Loc Val b} {hw : Q u ⟨_, h⟩} {σ : WRes}
    (hσ : ResU.CompS (ResU.single ℓ (CellU.mutOf b u _ h Q hw))
      (ResU.single ℓ' (CellU.mutOf b' u' χ' h' Q' hw')) σ) :
    ResU.Flat (ResU.single ℓ (CellU.mutOf b u _ h Q hw)) σ := by
  subst hχ'
  exact ⟨σ, PMap.empty,
    ExW.single_mut (ExW.single_mut BoLo.exW_empty (ResU.comp_empty_right _)) hσ,
    AgW.single_mut (AgW.single_mut BoLo.agW_empty), ResU.comp_empty_right σ⟩

/-- **A borrow of a borrow is a typed world**: allocate and fold the inner place, then the outer. -/
theorem tw_nested {ℓ ℓ' : Loc} (hne : ℓ' ≠ ℓ) {b b' : Life} {u u' : Val} {χ χ' : WRes}
    {h' : χ'.InStratum b'} {Q' : Val → SPropS Loc Val b'} {hw' : Q' u' ⟨χ', h'⟩}
    (hχ' : χ' = PMap.empty) {h : χ.InStratum b} {Q : Val → SPropS Loc Val b}
    {hw : Q u ⟨χ, h⟩} (hχ : χ = ResU.single ℓ' (CellU.mutOf b' u' χ' h' Q' hw')) :
    TW (ResU.single ℓ (CellU.mutOf b u χ h Q hw)) [] [] := by
  subst hχ
  subst hχ'
  have hflat' := ProbeD1.flat_single_mut_empty (k := ℓ') (u := u') (hw := hw')
  have h₁ : TW (ResU.single ℓ' (CellU.ownOf u')) [] [] :=
    TW.alloc TW.empty lower_empty rfl (ResU.comp_empty_left _) (ResU.valid_single_own _ _)
  have h₂ : TW (ResU.single ℓ' (CellU.mutOf b' u' PMap.empty h' Q' hw')) [] [] :=
    TW.mutFold (ρ := PMap.empty) (Z := PMap.empty) (hw := hw') h₁ (ResU.comp_empty_right _)
      (ResU.comp_empty_right _) (ResU.comp_empty_right _) ⟨_, hflat'⟩
  obtain ⟨W, hW⟩ := (ResU.compS_defined_iff
    (ResU.single ℓ' (CellU.mutOf b' u' PMap.empty h' Q' hw'))
    (ResU.single ℓ (CellU.ownOf u))).mpr
    (compatS_single_of_get_none (ResU.single_get_ne _ hne.symm))
  have hvW : ResU.Valid W := ⟨W, (flat_compS_own hW).mpr ⟨_, hflat', hW⟩⟩
  have h₃ : TW W [] [] :=
    TW.alloc h₂ ⟨_, hflat', fun _ => rfl⟩
      (by show Option.map _ ((ResU.single ℓ' _).get ℓ) = none
          rw [ResU.single_get_ne _ hne.symm]; rfl) hW hvW
  obtain ⟨σ, hσ⟩ := (ResU.compS_defined_iff
    (ResU.single ℓ (CellU.mutOf b u _ h Q hw))
    (ResU.single ℓ' (CellU.mutOf b' u' PMap.empty h' Q' hw'))).mpr
    (compatS_single_of_get_none (ResU.single_get_ne _ hne))
  exact TW.mutFold (W := W) (X := W) (Z := PMap.empty) h₃ (ResU.CompS.comm hW)
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) ⟨σ, flat_nested rfl hσ⟩

/-! ### The faithful re-slotting -/

/-- **The re-slotting preserves and reflects the value relation**, at every fragment type: the
resource re-slotted by `θ`, the records by `srecRestrat θ`, the reading by `ψ`. -/
def ReslotInvV (ι : Slots L) {c : Life} (θ : Restrat.Emb c) (ψ : L → L) : Prop :=
  ∀ (A : VTy), FragV A → ∀ (ls : List SRec) (δ : LSubD L) (v : Val) (ρ : WRes),
    vD (ℍ := ℍ) ι A (ls.map (Targets.srecRestrat θ)) (δ.map ψ) v (θ.relRU ρ) ↔
      vD (ℍ := ℍ) ι A ls δ v ρ

/-- **The re-slotting preserves and reflects the computation relation**, at every fragment type. -/
def ReslotInvC (ι : Slots L) {c : Life} (θ : Restrat.Emb c) (ψ : L → L) : Prop :=
  ∀ (C : CTy), FragC C → ∀ (ls : List SRec) (δ : LSubD L) (e : Expr) (ρ : WRes),
    cD (ℍ := ℍ) ι C (ls.map (Targets.srecRestrat θ)) (δ.map ψ) e (θ.relRU ρ) ↔
      cD (ℍ := ℍ) ι C ls δ e ρ

/-- The reading of the witness: `'a` at the outer cell's slot, `'b` at the inner one's. -/
def δmm (ι : Slots L) (bo si : Life) : LSubD L := ⟨[(0, ι bo), (1, ι si)]⟩

theorem δmm_find0 (ι : Slots L) (bo si : Life) : (δmm ι bo si).find? 0 = some (ι bo) := rfl

theorem δmm_find1 (ι : Slots L) (bo si : Life) : (δmm ι bo si).find? 1 = some (ι si) := rfl

theorem δmm_map_find1 (ι : Slots L) (bo si : Life) (ψ : L → L) :
    ((δmm ι bo si).map ψ).find? 1 = some (ψ (ι si)) := rfl

/-- `n + 1` is below `n` in `Life`. -/
theorem succ_lt_life (n : ℕ) : OrderDual.toDual (n + 1) < (OrderDual.toDual n : Life) := by
  show n < n + 1
  omega

/-- **The re-slotting breaks the value relation**: for every lifetime order, every placement of the
slots, every re-slotting other than the identity and every reading move agreeing with it on the
slots, the borrow of a borrow is related before the move and not after. -/
theorem reslot_fails_vD (ι : Slots L) {c : Life} (θ : Restrat.Emb c) (hθ : ∃ x, θ x ≠ x)
    (ψ : L → L) (hψ : ∀ s, ψ (ι s) = ι (θ s)) :
    ∃ (A : VTy) (ls : List SRec) (δ : LSubD L) (v : Val) (ρ : WRes), FragV A ∧
      vD (ℍ := ℍ) ι A ls δ v ρ ∧
      ¬ vD (ℍ := ℍ) ι A (ls.map (Targets.srecRestrat θ)) (δ.map ψ) v (θ.relRU ρ) := by
  obtain ⟨n, hgap, hθn⟩ := exists_gap θ hθ
  have hbs := succ_lt_life n
  refine ⟨mm, [], δmm ι (OrderDual.toDual (n + 1)) (OrderDual.toDual n), .loc 0,
    rhoMM ι _ 0 1 (δmm_find1 ι _ _) hbs, fragV_mm,
    vD_rhoMM ι _ 0 1 (δmm_find0 ι _ _) (δmm_find1 ι _ _) hbs, ?_⟩
  rw [List.map_nil]
  refine not_vD_mm_relRU ι θ hgap (δmm_map_find1 ι _ _ ψ) ?_ [] _ _
  rw [hψ]
  exact ι.le_iff.mpr hθn.le

theorem not_reslotInvV (ι : Slots L) {c : Life} (θ : Restrat.Emb c) (hθ : ∃ x, θ x ≠ x)
    (ψ : L → L) (hψ : ∀ s, ψ (ι s) = ι (θ s)) : ¬ ReslotInvV (ℍ := ℍ) ι θ ψ := by
  intro h
  obtain ⟨A, ls, δ, v, ρ, hA, h₁, h₂⟩ := reslot_fails_vD (ℍ := ℍ) ι θ hθ ψ hψ
  exact h₂ ((h A hA ls δ v ρ).mpr h₁)

/-- The borrow of a borrow, re-slotted, is a typed world. -/
theorem tw_relRU_rhoMM (ι : Slots L) {c : Life} (θ : Restrat.Emb c) (δ : LSubD L)
    {si bo : Life} (h1 : δ.find? 1 = some (ι si)) (hbs : bo < si) :
    TW (θ.relRU (rhoMM (ℍ := ℍ) ι δ 0 1 h1 hbs)) [] [] := by
  rw [rhoMM, θ.relRU_single, θ.relU_mutOf]
  refine tw_nested (ℓ' := 1) (b' := θ si) (u' := Val.unit)
    (h' := (θ.inStratum_relRU si PMap.empty).mpr (ResU.inStratum_empty si))
    (Q' := θ.relS si (unitQ si)) (hw' := θ.relS_holds (ResU.inStratum_empty si) (unitQ_holds si))
    (by decide) (Restrat.Emb.relRU_empty (e := θ)) ?_
  rw [innerView, θ.relRU_single, θ.relU_mutOf]

/-- **The re-slotting breaks the computation relation**: the same configuration at
`F (Mut 'a (Mut 'b 1))` and `return ℓ`. -/
theorem reslot_fails_cD (ι : Slots L) {c : Life} (θ : Restrat.Emb c) (hθ : ∃ x, θ x ≠ x)
    (ψ : L → L) (hψ : ∀ s, ψ (ι s) = ι (θ s)) :
    ∃ (ls : List SRec) (δ : LSubD L) (e : Expr) (ρ : WRes),
      cD (ℍ := ℍ) ι (.ret mm) ls δ e ρ ∧
      ¬ cD (ℍ := ℍ) ι (.ret mm) (ls.map (Targets.srecRestrat θ)) (δ.map ψ) e (θ.relRU ρ) := by
  obtain ⟨n, hgap, hθn⟩ := exists_gap θ hθ
  have hbs := succ_lt_life n
  refine ⟨[], δmm ι (OrderDual.toDual (n + 1)) (OrderDual.toDual n), .val (.loc 0),
    rhoMM ι _ 0 1 (δmm_find1 ι _ _) hbs,
    wpTS_val [] (.loc 0) _ _ (vD_rhoMM ι _ 0 1 (δmm_find0 ι _ _) (δmm_find1 ι _ _) hbs), ?_⟩
  rw [List.map_nil]
  refine not_wpTS_mm_relRU ι θ hgap (δmm_map_find1 ι _ _ ψ) ?_ _ _
    (tw_relRU_rhoMM ι θ _ (δmm_find1 ι _ _) hbs)
  rw [hψ]
  exact ι.le_iff.mpr hθn.le

theorem not_reslotInvC (ι : Slots L) {c : Life} (θ : Restrat.Emb c) (hθ : ∃ x, θ x ≠ x)
    (ψ : L → L) (hψ : ∀ s, ψ (ι s) = ι (θ s)) : ¬ ReslotInvC (ℍ := ℍ) ι θ ψ := by
  intro h
  obtain ⟨ls, δ, e, ρ, h₁, h₂⟩ := reslot_fails_cD (ℍ := ℍ) ι θ hθ ψ hψ
  exact h₂ ((h _ fragC_retMM ls δ e ρ).mpr h₁)

/-! ### At every cut -/

/-- A segment shift by `k > 0` moves the slot just below its cut. -/
theorem shift_ne_id (c : Life) {k : ℕ} (hk : 0 < k) : ∃ x, Restrat.Emb.shift c k x ≠ x := by
  refine ⟨OrderDual.toDual (OrderDual.ofDual c + 1), fun h => ?_⟩
  have h' := congrArg OrderDual.ofDual h
  rw [Restrat.Emb.shift_apply_lt (show OrderDual.toDual (OrderDual.ofDual c + 1) < c from by
    show OrderDual.ofDual c < OrderDual.ofDual c + 1; omega)] at h'
  change OrderDual.ofDual c + 1 + k = OrderDual.ofDual c + 1 at h'
  omega

/-- **Every segment shift by `k > 0`, at every cut, breaks the relation once it re-slots the
cells**, at every lifetime order, every placement of the slots and every reading move agreeing
with it on the slots. -/
def ReslotFailsAtEveryCut (ι : Slots L) : Prop :=
  ∀ (c : Life) (k : ℕ), 0 < k → ∀ ψ : L → L, (∀ s, ψ (ι s) = ι (Restrat.Emb.shift c k s)) →
    ∃ (C : CTy) (ls : List SRec) (δ : LSubD L) (e : Expr) (ρ : WRes), FragC C ∧
      cD (ℍ := ℍ) ι C ls δ e ρ ∧
      ¬ cD (ℍ := ℍ) ι C (ls.map (Targets.srecRestrat (Restrat.Emb.shift c k))) (δ.map ψ) e
        ((Restrat.Emb.shift c k).relRU ρ)

theorem reslotFailsAtEveryCut (ι : Slots L) : ReslotFailsAtEveryCut (ℍ := ℍ) ι := by
  intro c _ hk ψ hψ
  obtain ⟨ls, δ, e, ρ, h₁, h₂⟩ := reslot_fails_cD (ℍ := ℍ) ι _ (shift_ne_id c hk) ψ hψ
  exact ⟨_, ls, δ, e, ρ, fragC_retMM, h₁, h₂⟩

/-- At `WithTop ℚ`, `Shift.lean`'s position shift agrees with the re-slotting on Core's slots: the
faithful shift is probe 1's shift of the reading together with the re-slotting of the cells. -/
theorem shiftQ_ratSlots (c : Life) (k : ℕ) (s : Life) :
    shiftQ (ratSlots c) (k : ℚ) (ratSlots s) = ratSlots (Restrat.Emb.shift c k s) := by
  by_cases hs : s < c
  · rw [shiftQ_of_lt (ratSlots.strictMono hs)]
    have hn : OrderDual.ofDual (Restrat.Emb.shift c k s) = OrderDual.ofDual s + k :=
      Restrat.Emb.shift_apply_lt hs
    have hs0 : OrderDual.ofDual s ≠ 0 := by
      have : OrderDual.ofDual c < OrderDual.ofDual s := hs
      omega
    show WithTop.map (fun q => q - (k : ℚ)) (ratPos (OrderDual.ofDual s)) =
      ratPos (OrderDual.ofDual (Restrat.Emb.shift c k s))
    rw [hn]
    unfold ratPos
    rw [if_neg hs0, if_neg (by omega)]
    simp only [WithTop.map_coe]
    congr 1
    push_cast
    ring
  · have hcs : c ≤ s := not_lt.mp hs
    rw [shiftQ_of_le (ratSlots.strictMono.monotone hcs), (Restrat.Emb.shift c k).fix s hcs]

theorem not_reslotInvC_rat (c : Life) {k : ℕ} (hk : 0 < k) :
    ¬ ReslotInvC (ℍ := ℍ) ratSlots (Restrat.Emb.shift c k) (shiftQ (ratSlots c) (k : ℚ)) :=
  not_reslotInvC ratSlots _ (shift_ne_id c hk) _ (shiftQ_ratSlots c k)

/-! ### The bridge -/

/-- The slots read through a re-slotting: the slot `s` at the position of `θ s`. -/
def Slots.reslot (ι : Slots L) {c : Life} (θ : Restrat.Emb c) : Slots L :=
  ⟨fun x => ι (θ x), ι.strictMono.comp θ.strictMono, by
    show ι (θ ⊤) = ⊤
    rw [θ.map_top, ι.map_top]⟩

/-- **The bridge**: re-slotting the resource and the records by `θ` is moving the slots'
positions to `ι ∘ θ`, at every fragment value type. -/
def BridgeV (ι : Slots L) {c : Life} (θ : Restrat.Emb c) : Prop :=
  ∀ (A : VTy), FragV A → ∀ (ls : List SRec) (δ : LSubD L) (v : Val) (ρ : WRes),
    vD (ℍ := ℍ) ι A (ls.map (Targets.srecRestrat θ)) δ v (θ.relRU ρ) ↔
      vD (ℍ := ℍ) (ι.reslot θ) A ls δ v ρ

/-- **The bridge is false** for every re-slotting other than the identity, at the borrow of a
borrow: through `ι ∘ θ` the original configuration is related, and its re-slotting is not. It
fails without `Imm`, so no extension of the fragment restores it. -/
theorem not_bridgeV (ι : Slots L) {c : Life} (θ : Restrat.Emb c) (hθ : ∃ x, θ x ≠ x) :
    ¬ BridgeV (ℍ := ℍ) ι θ := by
  intro h
  obtain ⟨n, hgap, hθn⟩ := exists_gap θ hθ
  have hbs := succ_lt_life n
  have hv := vD_rhoMM (ℍ := ℍ) (ι.reslot θ)
    (δmm (ι.reslot θ) (OrderDual.toDual (n + 1)) (OrderDual.toDual n)) 0 1
    (δmm_find0 _ _ _) (δmm_find1 _ _ _) hbs
  have hm := (h mm fragV_mm [] _ _ _).mpr hv
  rw [List.map_nil] at hm
  refine not_vD_mm_relRU ι θ hgap (δmm_find1 _ _ _) ?_ [] _ _ hm
  exact ι.le_iff.mpr hθn.le

/-! ### No slot in the gap

In the two-order design a cell sits at a slot, so a lifetime of `L` carries a cell only if it is a
slot's position. The moves the relation is invariant under move positions (`cD_map`,
`segShift_iff`), and those keep the order of the slots and the number of slots between any two:
they never put a slot between two slots that had none between them, nor the region's slots below
the resumer's when the resumer's lends were taken below them. Probe 1's shift opens a gap of `L`
that holds no slot. The move that does free slots there is re-slotting, which breaks the relation
(`not_reslotInvC`). -/

/-- **A placement of the slots never creates room between two slots**: under every placement, the
slots whose positions lie strictly between those of `r` and `t` are the slots strictly between
them. -/
theorem slots_between_iff (ι : Slots L) (r s t : Life) :
    (ι r < ι s ∧ ι s < ι t) ↔ (r < s ∧ s < t) :=
  and_congr ι.lt_iff ι.lt_iff

/-- Adjacent slots stay adjacent: under every placement no slot sits strictly between the
positions of the slot `n + 1` and the slot `n` above it. -/
theorem no_slot_between_adjacent (ι : Slots L) (n : ℕ) (s : Life) :
    ¬ (ι (OrderDual.toDual (n + 1)) < ι s ∧ ι s < ι (OrderDual.toDual n)) := by
  rw [slots_between_iff]
  rintro ⟨h₁, h₂⟩
  have e₁ : OrderDual.ofDual s < n + 1 := h₁
  have e₂ : n < OrderDual.ofDual s := h₂
  omega

/-- The resumer's lends, taken below the region's, stay below them under every placement. -/
theorem placement_keeps_order (ι : Slots L) {f r : Life} (h : f < r) : ι f < ι r :=
  ι.strictMono h

/-- **Probe 1's shift opens a gap of `L` that holds no slot**: after the shift at the cut `q` by
`k > 0`, no slot's position lies in `[q - k, q)`. -/
theorem shiftSlots_gap_empty (ι : Slots (WithTop ℚ)) (q : ℚ) {k : ℚ} (hk : 0 < k) (s : Life) :
    ¬ (((q - k : ℚ) : WithTop ℚ) ≤ shiftSlots ι q hk s ∧ shiftSlots ι q hk s < (q : WithTop ℚ)) := by
  rintro ⟨h₁, h₂⟩
  change ((q - k : ℚ) : WithTop ℚ) ≤ shiftQ q k (ι s) at h₁
  change shiftQ q k (ι s) < (q : WithTop ℚ) at h₂
  by_cases h : ι s < (q : WithTop ℚ)
  · obtain ⟨r, hr⟩ : ∃ r : ℚ, ι s = r :=
      WithTop.ne_top_iff_exists.mp (ne_top_of_lt h) |>.imp fun _ e => e.symm
    rw [hr] at h h₁
    rw [shiftQ_coe_lt h] at h₁
    have h' : r < q := WithTop.coe_lt_coe.mp h
    have h₁' : q - k ≤ r - k := WithTop.coe_le_coe.mp h₁
    linarith
  · rw [shiftQ_of_le (not_lt.mp h)] at h₂
    exact h h₂

/-- The gap is not empty. -/
theorem shiftQ_gap_nonempty (q : ℚ) {k : ℚ} (hk : 0 < k) :
    ((q - k : ℚ) : WithTop ℚ) < (q : WithTop ℚ) :=
  WithTop.coe_lt_coe.mpr (by linarith)

/-! ### The dense thaw at the top cut -/

/-- **The dense thaw at `⊤`** (`Bridge.CoreThawTop` over `L`): every lifetime below `⊤`
re-instantiated by `shift ⊤ 1` on the slots — cells, records and reading moved together, the
reading by `ψ` — preserves the relation at every configuration. -/
def DenseThawTop (ι : Slots L) (ψ : L → L) : Prop :=
  ∀ (C : CTy) (ls : List SRec) (δ : LSubD L) (e : Expr) (ρ : WRes),
    cD (ℍ := ℍ) ι C ls δ e ρ →
      cD (ℍ := ℍ) ι C (ls.map (Targets.srecRestrat ProbeD1.adjθ)) (δ.map ψ) e
        (ProbeD1.adjθ.relRU ρ)

/-- **The dense thaw is false**, at every lifetime order, every placement of the slots and every
reading move agreeing with `shift ⊤ 1` on the slots. -/
theorem not_denseThawTop (ι : Slots L) (ψ : L → L) (hψ : ∀ s, ψ (ι s) = ι (ProbeD1.adjθ s)) :
    ¬ DenseThawTop (ℍ := ℍ) ι ψ := by
  intro h
  obtain ⟨ls, δ, e, ρ, h₁, h₂⟩ :=
    reslot_fails_cD (ℍ := ℍ) ι ProbeD1.adjθ (shift_ne_id ⊤ one_pos) ψ hψ
  exact h₂ (h _ ls δ e ρ h₁)

/-! ### In Core

At `L = Life` and the identity placement the fragment relation is Core's (`cD_id`), so the same
configuration refutes `SegShift.SegShiftInv` and `Bridge.CoreThawTop` at `F (Mut 'a (Mut 'b 1))`,
a type with no `∀`. ProbeD1's witnesses read the room below a `∀`'s bound; this one reads none, and
fails at every lifetime order the same way. -/

theorem toLSub_map_emb {c : Life} (θ : Restrat.Emb c) (δ : LSubD Life) :
    toLSub (δ.map θ.f) = Restrat.LSub.mapN θ.toNat (toLSub δ) := by
  simp only [toLSub, LSubD.map, Restrat.LSub.mapN, List.map_map]
  rfl

/-- **Core's relation is not invariant under re-slotting at a type with no `∀`**: at every
re-slotting other than the identity, at every cut. -/
theorem core_reslot_fails {c : Life} (θ : Restrat.Emb c) (hθ : ∃ x, θ x ≠ x) :
    ∃ (ls : List SRec) (δ : BoCa.Lifetime.LSub) (e : Expr) (ρ : WRes),
      cC (ℍ := ℍ) (.ret mm) ls δ e ρ ∧
      ¬ cC (ℍ := ℍ) (.ret mm) (ls.map (Targets.srecRestrat θ)) (Restrat.LSub.mapN θ.toNat δ) e
        (θ.relRU ρ) := by
  obtain ⟨ls, δ, e, ρ, h₁, h₂⟩ := reslot_fails_cD (ℍ := ℍ) Slots.id θ hθ θ.f (fun _ => rfl)
  refine ⟨ls, toLSub δ, e, ρ, ?_, ?_⟩
  · rw [← cD_id _ fragC_retMM]
    exact h₁
  · rw [← toLSub_map_emb, ← cD_id _ fragC_retMM]
    exact h₂

/-- `SegShift.SegShiftInv` is false at a type with no `∀`. -/
theorem not_segShiftInv_noAll : ¬ ProbeD1.SegShift.SegShiftInv (ℍ := ℍ) := by
  intro h
  obtain ⟨ls, δ, e, ρ, h₁, h₂⟩ :=
    core_reslot_fails (ℍ := ℍ) (ProbeD1.SegShift.segθ ⊤ 1) (shift_ne_id ⊤ one_pos)
  exact h₂ (h ⊤ 1 _ ls δ e ρ h₁)

/-- `Bridge.CoreThawTop` is false at a type with no `∀`. -/
theorem not_coreThawTop_noAll : ¬ ProbeD1.Bridge.CoreThawTop (ℍ := ℍ) := by
  intro h
  obtain ⟨ls, δ, e, ρ, h₁, h₂⟩ :=
    core_reslot_fails (ℍ := ℍ) ProbeD1.adjθ (shift_ne_id ⊤ one_pos)
  exact h₂ (h _ ls δ e ρ h₁)

/-- At `WithTop ℚ`, Core's slots at `-n`, and the reading translated by `-1`. -/
theorem not_denseThawTop_rat : ¬ DenseThawTop (ℍ := ℍ) ratSlots (shiftQ ⊤ 1) := by
  have h := shiftQ_ratSlots ⊤ 1
  refine not_denseThawTop ratSlots _ fun s => ?_
  rw [← h s]
  rfl

end DenseCarrier

end
