import DenseCarrier.Gap
import DenseCarrier.Rat

/-!
# DenseCarrier — the shift test

The move a resume makes on a suspended region (`SegShift.lean`): every lifetime strictly below a
cut `c` moves `k` lower, everything at or above the cut stays, and a gap opens between the cut and
the moved segment. On a configuration it moves what the relation reads in `L`: the slots'
positions and the reading `δ`. The resource, records and term are the model's and stay.

* **`L = WithTop ℚ`: every segment shift preserves the relation, at every cut, at every
  configuration and every type of the fragment** (`segShiftInvD`), and reflects it
  (`segShift_iff`). The shift is not onto, but on the configuration's lifetimes it agrees with an
  order automorphism (`exists_aut_agree`), and the relation is invariant under automorphisms
  (`cD_map`).
* **`L = Life` (Core): every segment shift by `k > 0`, at every cut, breaks the relation somewhere**
  (`segShiftFailsAtEveryCutD`): the cell adjacent to the cut has no room below the cut before the
  shift and `k` lifetimes of room after it (`holdsD`, `failsD`). This is
  `ProbeD1.segShiftFailsAtEveryCut` with the move made on the slots' positions.

So the two carriers differ exactly where `SegShift.lean` located the failure: the `∀` reading the
room between a cell and the cut.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)
open GhostEnd (innerView unitQ unitQ_holds)
open ProbeD1 (adjE)

/-! ### `L = WithTop ℚ` -/

/-- The slots moved by the segment shift at `c` by `k`. -/
def shiftSlots (ι : Slots (WithTop ℚ)) (c : WithTop ℚ) {k : ℚ} (hk : 0 < k) :
    Slots (WithTop ℚ) :=
  ι.comp (shiftQ c k) (shiftQ_strictMono hk) (shiftQ_top c k)

/-- **The segment shift, at every cut, leaves the relation unchanged**: the moved configuration is
related exactly when the configuration is. -/
theorem segShift_iff (ι : Slots (WithTop ℚ)) (c : WithTop ℚ) {k : ℚ} (hk : 0 < k) (C : CTy)
    (ls : List SRec) (δ : LSubD (WithTop ℚ)) (e : Expr) :
    cD (ℍ := ℍ) (shiftSlots ι c hk) C ls (δ.map (shiftQ c k)) e = cD (ℍ := ℍ) ι C ls δ e := by
  obtain ⟨π, hπ⟩ := exists_aut_agree hk (configLifes ι δ) (config_bound ι δ c)
  have hι : shiftSlots ι c hk = ι.map π :=
    Slots.ext fun s => (hπ (ι s) (Or.inl ⟨s, rfl⟩)).symm
  have hδ : δ.map (shiftQ c k) = δ.map π :=
    LSubD.map_congr fun p hp => (hπ p.2 (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩))).symm
  rw [hι, hδ, cD_map]

/-- **The segment shift preserves the relation at every cut** (the dense analogue of
`SegShift.SegShiftInv`, which is false on `ℕᵒᵈ`). -/
def SegShiftInvD : Prop :=
  ∀ (c : WithTop ℚ) (k : ℚ) (hk : 0 < k) (ι : Slots (WithTop ℚ)) (C : CTy) (ls : List SRec)
    (δ : LSubD (WithTop ℚ)) (e : Expr) (ρ : WRes),
    cD (ℍ := ℍ) ι C ls δ e ρ → cD (ℍ := ℍ) (shiftSlots ι c hk) C ls (δ.map (shiftQ c k)) e ρ

theorem segShiftInvD : SegShiftInvD (ℍ := ℍ) := by
  intro c k hk ι C ls δ e ρ h
  rw [segShift_iff]
  exact h

/-- The dense analogue of `CoreAllNotNatural`: a configuration related before the shift at `⊤`
by `1` and not after it. -/
def DenseCoreAllNotNatural (ι : Slots (WithTop ℚ)) : Prop :=
  ∃ (C : CTy) (ls : List SRec) (δ : LSubD (WithTop ℚ)) (e : Expr) (ρ : WRes),
    cD (ℍ := ℍ) ι C ls δ e ρ ∧
      ¬ cD (ℍ := ℍ) (shiftSlots ι ⊤ one_pos) C ls (δ.map (shiftQ ⊤ 1)) e ρ

theorem not_denseCoreAllNotNatural (ι : Slots (WithTop ℚ)) :
    ¬ DenseCoreAllNotNatural (ℍ := ℍ) ι := by
  rintro ⟨C, ls, δ, e, ρ, h₁, h₂⟩
  exact h₂ (segShiftInvD ⊤ 1 one_pos ι C ls δ e ρ h₁)

/-- The position-`∀` over `L` (reading (A) of `ProbeD1/Gap.lean`, `CutAllC`): the relation at every
renaming of the configuration by an order automorphism of `L`. -/
def CutAllD {L : Type} [LinearOrder L] [OrderTop L] (ι : Slots L) (C : CTy) (ls : List SRec)
    (δ : LSubD L) (e : Expr) : WProp :=
  fun ρ => ∀ π : L ≃o L, cD (ℍ := ℍ) (ι.map π) C ls (δ.map π) e ρ

/-- **The relation implies the position-`∀`**, at every lifetime order: the dense analogue of
`ProbeD1.NotCoreAllImpCutAll` is the positive statement. -/
theorem cD_imp_cutAllD {L : Type} [LinearOrder L] [OrderTop L] (ι : Slots L) (C : CTy)
    (ls : List SRec) (δ : LSubD L) (e : Expr) (ρ : WRes) (h : cD (ℍ := ℍ) ι C ls δ e ρ) :
    CutAllD (ℍ := ℍ) ι C ls δ e ρ := fun π => by rw [cD_map]; exact h

/-! ### `L = Life`: Core -/

/-- The cut `m`, read at `'1`. -/
abbrev cutδ (m : ℕ) : LSubD Life := ⟨[(1, OrderDual.toDual m)]⟩

/-- Core's slots moved by `Restrat.Emb.shift` at the cut `m` by `k`. -/
def coreShiftSlots (m k : ℕ) : Slots Life :=
  Slots.id.comp (Restrat.Emb.shift (OrderDual.toDual m) k).f
    (Restrat.Emb.shift _ k).strictMono (Restrat.Emb.map_top _)

theorem coreShift_fix (m k : ℕ) :
    (Restrat.Emb.shift (OrderDual.toDual m) k).f (OrderDual.toDual m) = OrderDual.toDual m :=
  (Restrat.Emb.shift (OrderDual.toDual m) k).fix _ le_rfl

theorem coreShift_succ (m k : ℕ) :
    (Restrat.Emb.shift (OrderDual.toDual m) k).f (OrderDual.toDual (m + 1)) =
      OrderDual.toDual (m + 1 + k) := by
  apply OrderDual.ofDual.injective
  rw [Restrat.Emb.shift_apply_lt (show OrderDual.toDual (m + 1) < OrderDual.toDual m from by
    show m < m + 1; omega)]
  rfl

/-- Every lifetime strictly below `m` is at or below `m + 1`. -/
theorem room_succ (m : ℕ) (α : Life) (h : α < OrderDual.toDual m) :
    α ≤ Slots.id (OrderDual.toDual (m + 1)) := by
  have h' : m < OrderDual.ofDual α := h
  show m + 1 ≤ OrderDual.ofDual α
  omega

/-- **Every segment shift by `k > 0`, at every cut, breaks Core's relation somewhere**: the
configuration with the bound at the cut and a `mut` cell adjacent to it. -/
def SegShiftFailsAtEveryCutD : Prop :=
  ∀ (m k : ℕ), 0 < k →
    ∃ (C : CTy) (ls : List SRec) (δ : LSubD Life) (e : Expr) (ρ : WRes),
      cD (ℍ := ℍ) Slots.id C ls δ e ρ ∧
        ¬ cD (ℍ := ℍ) (coreShiftSlots m k) C ls
          (δ.map (Restrat.Emb.shift (OrderDual.toDual m) k).f) e ρ

theorem segShiftFailsAtEveryCutD : SegShiftFailsAtEveryCutD (ℍ := ℍ) := by
  intro m k hk
  have hm : interpD (cutδ m) (.var 1) = some (OrderDual.toDual m) := rfl
  refine ⟨gapC (.var 1), [], cutδ m, adjE, innerView 0 (OrderDual.toDual (m + 1)),
    holdsD Slots.id (.var 1) (cutδ m) hm _ (room_succ m), ?_⟩
  have hm' : interpD ((cutδ m).map (Restrat.Emb.shift (OrderDual.toDual m) k).f) (.var 1) =
      some (OrderDual.toDual m) := by
    show (((cutδ m).map _).find? 1) = _
    rw [LSubD.find?_map]
    show Option.map _ (some (OrderDual.toDual m)) = _
    rw [Option.map_some, coreShift_fix]
  refine failsD (coreShiftSlots m k) (.var 1) _ hm' (α := OrderDual.toDual (m + 1)) ?_ ?_
    (unitQ_holds _)
  · show (Restrat.Emb.shift (OrderDual.toDual m) k).f (OrderDual.toDual (m + 1)) < _
    rw [coreShift_succ]
    show m + 1 < m + 1 + k
    omega
  · show m < m + 1
    omega

end DenseCarrier

end
