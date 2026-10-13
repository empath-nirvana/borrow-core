import DenseCarrier.Gap
import DenseCarrier.Rat

/-!
# DenseCarrier — moving the slots' positions

A segment shift of the lifetime order: every lifetime of `L` strictly below a cut `c` moves `k`
lower, everything at or above the cut stays, and a gap opens in `L` between the cut and the moved
segment. Here it moves what the relation reads in `L` and nothing else: the slots' positions and
the reading `δ`. The resource, the records and the term stay, so no cell changes slot. This is
**not** `SegShift.lean`'s move, which re-slots the cells and the records (`θ.relRU`,
`srecRestrat θ`); that move is `Reslot.lean`'s, and it breaks the relation (`not_reslotInvC`).

* **`L = WithTop ℚ`: invariance under moving slot positions**, at every cut, every configuration
  and every type of the fragment (`segShift_iff`, `segShiftInvD`). It is a corollary of `cD_map`
  and the homogeneity of `ℚ`: the shift is not onto, but on the configuration's lifetimes it agrees
  with an order automorphism (`exists_aut_agree`).
* **`L = Life`: a position shift by `k > 0`, at every cut, breaks the relation somewhere**
  (`segShiftFailsAtEveryCutD`): the cell adjacent to the cut has no room below the cut before the
  shift and `k` lifetimes of room after it (`holdsD`, `failsD`).

So at `L = Life` the `∀` reads the room between a cell and the cut, and at `WithTop ℚ` it does
not. The gap the shift opens in `L` holds no slot (`Reslot.shiftSlots_gap_empty`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)
open GhostEnd (innerView unitQ unitQ_holds)
open ProbeD1 (adjE)

/-! ### `L = WithTop ℚ` -/

/-- **A move of the configuration's lifetimes that agrees with an order automorphism on them
leaves the relation unchanged**, at every lifetime order: the slots moved by `θ`, the reading
moved by `θ`, and `θ` equal to an automorphism `π` on every slot position and every value of the
reading. -/
theorem cD_comp_of_agree {L : Type} [LinearOrder L] [OrderTop L] (ι : Slots L) {θ : L → L}
    (hθ : StrictMono θ) (hθt : θ ⊤ = ⊤) (π : L ≃o L) (hι : ∀ s, π (ι s) = θ (ι s))
    (δ : LSubD L) (hδ : ∀ p ∈ δ.entries, π p.2 = θ p.2) (C : CTy) (ls : List SRec) (e : Expr) :
    cD (ℍ := ℍ) (ι.comp θ hθ hθt) C ls (δ.map θ) e = cD (ℍ := ℍ) ι C ls δ e := by
  have h₁ : ι.comp θ hθ hθt = ι.map π := Slots.ext fun s => (hι s).symm
  have h₂ : δ.map θ = δ.map π := LSubD.map_congr fun p hp => (hδ p hp).symm
  rw [h₁, h₂, cD_map]

/-- The slots moved by the segment shift at `c` by `k`. -/
def shiftSlots (ι : Slots (WithTop ℚ)) (c : WithTop ℚ) {k : ℚ} (hk : 0 < k) :
    Slots (WithTop ℚ) :=
  ι.comp (shiftQ c k) (shiftQ_strictMono hk) (shiftQ_top c k)

/-- **Moving the slots' positions by the segment shift, at every cut, leaves the relation
unchanged**: the configuration with its positions and reading moved is related exactly when the
configuration is (a corollary of `cD_map`, through `exists_aut_agree`). -/
theorem segShift_iff (ι : Slots (WithTop ℚ)) (c : WithTop ℚ) {k : ℚ} (hk : 0 < k) (C : CTy)
    (ls : List SRec) (δ : LSubD (WithTop ℚ)) (e : Expr) :
    cD (ℍ := ℍ) (shiftSlots ι c hk) C ls (δ.map (shiftQ c k)) e = cD (ℍ := ℍ) ι C ls δ e := by
  obtain ⟨π, hπ⟩ := exists_aut_agree hk (configLifes ι δ) (config_bound ι δ c)
  have hι : shiftSlots ι c hk = ι.map π :=
    Slots.ext fun s => (hπ (ι s) (Or.inl ⟨s, rfl⟩)).symm
  have hδ : δ.map (shiftQ c k) = δ.map π :=
    LSubD.map_congr fun p hp => (hπ p.2 (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩))).symm
  rw [hι, hδ, cD_map]

/-- **Moving the slots' positions by a segment shift preserves the relation at every cut.**
`SegShift.SegShiftInv` re-slots the cells instead; its analogue here is `Reslot.ReslotInvC`,
which is false at every lifetime order. -/
def SegShiftInvD : Prop :=
  ∀ (c : WithTop ℚ) (k : ℚ) (hk : 0 < k) (ι : Slots (WithTop ℚ)) (C : CTy) (ls : List SRec)
    (δ : LSubD (WithTop ℚ)) (e : Expr) (ρ : WRes),
    cD (ℍ := ℍ) ι C ls δ e ρ → cD (ℍ := ℍ) (shiftSlots ι c hk) C ls (δ.map (shiftQ c k)) e ρ

theorem segShiftInvD : SegShiftInvD (ℍ := ℍ) := by
  intro c k hk ι C ls δ e ρ h
  rw [segShift_iff]
  exact h

/-- A configuration related before the position shift at `⊤` by `1` and not after it:
`CoreAllNotNatural` with the move made on the slots' positions instead of re-slotting the cells.
With the cells re-slotted such a configuration exists at every lifetime order
(`Reslot.reslot_fails_cD`, `Reslot.not_denseThawTop`). -/
def DenseCoreAllNotNatural (ι : Slots (WithTop ℚ)) : Prop :=
  ∃ (C : CTy) (ls : List SRec) (δ : LSubD (WithTop ℚ)) (e : Expr) (ρ : WRes),
    cD (ℍ := ℍ) ι C ls δ e ρ ∧
      ¬ cD (ℍ := ℍ) (shiftSlots ι ⊤ one_pos) C ls (δ.map (shiftQ ⊤ 1)) e ρ

theorem not_denseCoreAllNotNatural (ι : Slots (WithTop ℚ)) :
    ¬ DenseCoreAllNotNatural (ℍ := ℍ) ι := by
  rintro ⟨C, ls, δ, e, ρ, h₁, h₂⟩
  exact h₂ (segShiftInvD ⊤ 1 one_pos ι C ls δ e ρ h₁)

/-- The position-`∀` over `L`: the relation at every renaming of the slots' positions and the
reading by an order automorphism of `L`. Reading (A) of `ProbeD1/Gap.lean` (`CutAllC`) renames
the cells too; that renaming is `Reslot.lean`'s re-slotting. -/
def CutAllD {L : Type} [LinearOrder L] [OrderTop L] (ι : Slots L) (C : CTy) (ls : List SRec)
    (δ : LSubD L) (e : Expr) : WProp :=
  fun ρ => ∀ π : L ≃o L, cD (ℍ := ℍ) (ι.map π) C ls (δ.map π) e ρ

/-- **The relation implies the position-`∀`**, at every lifetime order (`cD_map`). -/
theorem cD_imp_cutAllD {L : Type} [LinearOrder L] [OrderTop L] (ι : Slots L) (C : CTy)
    (ls : List SRec) (δ : LSubD L) (e : Expr) (ρ : WRes) (h : cD (ℍ := ℍ) ι C ls δ e ρ) :
    CutAllD (ℍ := ℍ) ι C ls δ e ρ := fun π => by rw [cD_map]; exact h

/-! ### `L = Life`, the cells kept and the slots' positions moved -/

/-- The cut `m`, read at `'1`. -/
abbrev cutδ (m : ℕ) : LSubD Life := ⟨[(1, OrderDual.toDual m)]⟩

/-- The slots' positions in `L = Life` moved by `Restrat.Emb.shift` at the cut `m` by `k`. -/
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

/-- **At `L = Life`, every position shift by `k > 0`, at every cut, breaks the relation
somewhere**: the slots' positions moved by `Restrat.Emb.shift` with the cells kept, at the
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
