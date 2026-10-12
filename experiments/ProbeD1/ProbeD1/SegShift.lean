import ProbeD1.GapWitness

/-!
# ProbeD1 — Core's relation under a whole-segment shift (`BRIDGE.md` § Segment-shift check)

`Life = ℕᵒᵈ`: `⊤ = 0` is the longest lifetime, and a younger lifetime is a larger natural, lower
in the order. The youngest lends — the top of the lend stack — are the lowest lifetimes.

A **whole-segment shift at the cut `c` by `k`** is `Restrat.Emb.shift c k`: it fixes every
lifetime at or above `c` (`c` and everything older) and sends every lifetime strictly below `c`
(younger than `c`) to the lifetime `k` younger. On the moved lifetimes it is a translation, so it
opens no gap among them; the `k` lifetimes it leaves without a preimage lie between `c` and the
moved segment. This is the move a resume would apply to a packed segment pushed back on top of a
stack that has `k` more lends above the cut than at the stop.

* `SegShiftInv`: Core's `cC` is invariant under every such shift, at every configuration.
* `not_segShiftInv`: false, by `coreAllNotNatural`, whose `adjθ` is the shift at the cut `⊤` by `1`.
* `segShiftFailsAtEveryCut`: the failure is not special to `⊤`. At every cut `c = m` and every
  `k > 0`, at `∀'0 ⊏ 'c. F (Mut '0 1)` read with `'c ↦ m` and the value `Λ. return ℓ₀`, the clause
  holds at a `mut` cell at `m + 1` (adjacent to the cut) and fails at its image, a cell at
  `m + 1 + k`. Reading, records and resource are moved together; the reading is fixed (`m` is at
  the cut).
* `segShiftFailsWithRoom`: a segment already separated from the cut is not safe either. At
  `∀'0 ⊏ 'c. ∀'2 ⊏ '0. F (Mut '2 1)` and `Λ. Λ. return ℓ₀`, the clause holds at a cell at `m + 2`
  (one lifetime of room below the cut) and fails at its image at `m + 2 + k`: two nested `∀`s
  read distance two from the cut, as one reads adjacency.

The witnesses are GAP.md §3c's at a general cut and depth. They are not claimed to arise from a
typed program.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1.SegShift
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (innerView unitQ unitQ_holds innerView_ptoMutS)

/-- The whole-segment shift at the cut `c` by `k`. -/
abbrev segθ (c : Life) (k : ℕ) : Restrat.Emb c := Restrat.Emb.shift c k

/-- **Core's relation is invariant under every whole-segment shift**: the reading, the records and
the resource moved together. -/
def SegShiftInv : Prop :=
  ∀ (c : Life) (k : ℕ) (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes),
    cC (ℍ := ℍ) C ls δ e ρ →
      cC (ℍ := ℍ) C (ls.map (Targets.srecRestrat (segθ c k)))
        (Restrat.LSub.mapN (segθ c k).toNat δ) e ((segθ c k).relRU ρ)

/-- GAP.md §3c's `adjθ` is the whole-segment shift at the cut `⊤` by `1`. -/
theorem adjθ_eq_segθ : adjθ = segθ ⊤ 1 := rfl

/-- **The invariance is false**, by GAP.md §3c's witness: `shift ⊤ 1` is a whole-segment shift. -/
theorem not_segShiftInv : ¬ SegShiftInv (ℍ := ℍ) := by
  intro h
  obtain ⟨C, ls, δ, e, ρ, h₁, h₂⟩ := coreAllNotNatural (ℍ := ℍ)
  exact h₂ (h ⊤ 1 C ls δ e ρ h₁)

/-! ### The witness at every cut -/

/-- `∀'0 ⊏ '1. F (Mut '0 1)`. -/
abbrev cutC : CTy := .all 0 (.var 1) (.ret (.mut (.var 0) .unit))

/-- `'1 ↦ m`: the bound read at the cut. -/
abbrev cutδ (m : ℕ) : LSub := ⟨[(1, m)]⟩

/-- Every lifetime strictly below `m` is at or below `m + 1`. -/
theorem le_succ_of_lt {m : ℕ} {α : Life} (h : α < OrderDual.toDual m) : α ≤ lifeN (m + 1) := by
  have h' : m < OrderDual.ofDual α := h
  show m + 1 ≤ OrderDual.ofDual α
  omega

/-- **At `ℓ₀ ↦ mut(m+1, (), ∅, 𝒱⟦1⟧)` the clause holds**: `m + 1` is adjacent to the cut `m`. -/
theorem cut_holds (m : ℕ) :
    cC (ℍ := ℍ) cutC [] (cutδ m) adjE (innerView 0 (lifeN (m + 1))) := by
  intro α ρ₁ ρ₂ hp hc
  obtain ⟨rfl, β, hβ, hlt⟩ := hp
  rw [show β = m from (Option.some.inj hβ).symm] at hlt
  have hρ₂ : ρ₂ = innerView 0 (lifeN (m + 1)) :=
    ResU.CompS.functional hc (ResU.comp_empty_right _)
  subst hρ₂
  refine wpTS_lolli [] (.val (Val.loc 0)) Val.unit _ _ ?_
  rw [adj_subst]
  refine wpTS_val [] (Val.loc 0) _ _ ?_
  exact ⟨α, rfl, 0, pure_sep_mk rfl (ptoMutS_innerView_le (le_succ_of_lt hlt) [] _)⟩

/-- **At a single `mut` cell at `n ≥ m + 2` with an empty witness, the clause fails**: at
`α = m + 1`, below the cut, the answer's cell must be at a lifetime `⊒ m + 1`, and a run's `↭`
keeps the lifetime `n` of the only `mut` cell of the flattening. -/
theorem cut_fails {m n : ℕ} (hn : m + 2 ≤ n) {h : ResU.InStratum (lifeN n) (PMap.empty : WRes)}
    {Q : Val → SPropS BoCa.Loc Val (lifeN n)} (hw : Q Val.unit ⟨PMap.empty, h⟩) :
    ¬ cC (ℍ := ℍ) cutC [] (cutδ m) adjE
      (ResU.single 0 (CellU.mutOf (lifeN n) Val.unit PMap.empty h Q hw)) := by
  intro hC
  have hflat := flat_single_mut_empty (k := 0) (u := Val.unit) (hw := hw)
  have hval : ResU.Valid (ResU.single 0 (CellU.mutOf (lifeN n) Val.unit PMap.empty h Q hw)) :=
    ⟨_, hflat⟩
  have hlt : LtLife (cutδ m) (.var 1) (lifeN (m + 1)) :=
    ⟨m, rfl, show OrderDual.toDual (m + 1 : ℕ) < OrderDual.toDual m from by
      show m < m + 1; omega⟩
  have hwp := hC (lifeN (m + 1)) PMap.empty _ ⟨rfl, hlt⟩ (ResU.comp_empty_right _)
  obtain ⟨ρ', ρp, -, -, π, v, -, -, -, ls', -, -, -, -, -, -, -, hπ, hU, -, -, -, -, -, hQ⟩ :=
    hwp PMap.empty _ [] ⟨(compS_empty_left _).1, _, compS_empty_left _, hval⟩
      (compS_empty_left _) (tw_single_mut_empty hw) (fun _ hx => absurd hx List.not_mem_nil)
      BoCa.BoLo.Alloc.leastFree 0
  obtain ⟨α, hα, ℓ, hsep⟩ := hQ
  obtain rfl : α = lifeN (m + 1) := (Option.some.inj hα).symm
  obtain ⟨-, b, u, χ, hχ, Q', hw', -, hαb, hρ', -, -, -⟩ := pure_sep_iff.mp hsep
  have hg : ρ'.get ℓ = some (CellU.mutOf b u χ hχ Q' hw') := by rw [hρ']; simp
  have hf : π.FlatAt ℓ (CellU.mutOf b u χ hχ Q' hw') :=
    pvLocal π ρp ρ' hU.2.2 (ResU.CompS.comm hπ) ℓ _ hg (CellU.kind_mutOf _ _ _ _ _ _)
  obtain ⟨v₀, χ₀, h₀, hw₀, σ₀, hσ₀, hg₀⟩ := (hU.1.2 ℓ b Q').mpr ⟨u, χ, hχ, hw', hf⟩
  rw [ResU.Flat.functional hσ₀ hflat] at hg₀
  obtain ⟨-, he⟩ := ResU.single_get_eq_some hg₀
  have hb : b = lifeN n := CellU.mutOf_at he
  rw [hb] at hαb
  have : n ≤ m + 1 := hαb
  omega

/-- `cut_fails` at a witness equal to `∅` and a lifetime equal to `n`. -/
theorem cut_fails' {m n : ℕ} (hn : m + 2 ≤ n) {b : Life} (hb : b = lifeN n) {χ : WRes}
    (hχe : χ = PMap.empty) {h : χ.InStratum b} {Q : Val → SPropS BoCa.Loc Val b}
    (hw : Q Val.unit ⟨χ, h⟩) :
    ¬ cC (ℍ := ℍ) cutC [] (cutδ m) adjE (ResU.single 0 (CellU.mutOf b Val.unit χ h Q hw)) := by
  subst hb hχe
  exact cut_fails hn hw

/-- The shift moves the cell at `m + 1` to `m + 1 + k`. -/
theorem segθ_succ (m k : ℕ) : segθ (lifeN m) k (lifeN (m + 1)) = lifeN (m + 1 + k) := by
  apply OrderDual.ofDual.injective
  rw [Restrat.Emb.shift_apply_lt (show lifeN (m + 1) < lifeN m from by
    show m < m + 1; omega)]
  rfl

/-- The shift fixes the reading: `m` is at the cut. -/
theorem mapN_cutδ (m k : ℕ) : Restrat.LSub.mapN (segθ (lifeN m) k).toNat (cutδ m) = cutδ m := by
  have : (segθ (lifeN m) k).toNat m = m :=
    congrArg OrderDual.ofDual ((segθ (lifeN m) k).fix (lifeN m) le_rfl)
  simp [Restrat.LSub.mapN, this]

/-- The image of the cell at `m + 1`. -/
theorem cut_relRU (m k : ℕ) :
    (segθ (lifeN m) k).relRU (innerView 0 (lifeN (m + 1))) =
      ResU.single 0 (CellU.mutOf (segθ (lifeN m) k (lifeN (m + 1))) Val.unit
        ((segθ (lifeN m) k).relRU PMap.empty)
        (((segθ (lifeN m) k).inStratum_relRU (lifeN (m + 1)) PMap.empty).mpr
          (ResU.inStratum_empty _))
        ((segθ (lifeN m) k).relS (lifeN (m + 1)) (unitQ (lifeN (m + 1))))
        ((segθ (lifeN m) k).relS_holds (ResU.inStratum_empty _) (unitQ_holds (lifeN (m + 1))))) := by
  rw [innerView, Restrat.Emb.relRU_single, Restrat.Emb.relU_mutOf]

/-- **Every whole-segment shift by `k > 0`, at every cut, breaks Core's relation somewhere**: the
configuration with the bound at the cut and a `mut` cell adjacent to it. -/
def SegShiftFailsAtEveryCut : Prop :=
  ∀ (m k : ℕ), 0 < k →
    ∃ (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes),
      cC (ℍ := ℍ) C ls δ e ρ ∧
        ¬ cC (ℍ := ℍ) C (ls.map (Targets.srecRestrat (segθ (lifeN m) k)))
          (Restrat.LSub.mapN (segθ (lifeN m) k).toNat δ) e ((segθ (lifeN m) k).relRU ρ)

theorem segShiftFailsAtEveryCut : SegShiftFailsAtEveryCut (ℍ := ℍ) := by
  intro m k hk
  refine ⟨cutC, [], cutδ m, adjE, innerView 0 (lifeN (m + 1)), cut_holds m, ?_⟩
  rw [List.map_nil, mapN_cutδ, cut_relRU]
  exact cut_fails' (n := m + 1 + k) (by omega) (segθ_succ m k) (Restrat.Emb.relRU_empty (e := segθ (lifeN m) k)) _

/-! ### Room already present does not help: two nested `∀`s read distance two -/

/-- `∀'0 ⊏ '1. ∀'2 ⊏ '0. F (Mut '2 1)`. -/
abbrev cut2C : CTy := .all 0 (.var 1) (.all 2 (.var 0) (.ret (.mut (.var 2) .unit)))

/-- `Λ. Λ. return ℓ₀`. -/
abbrev cut2E : Expr := .val (.lam (.val (.lam (.val (Val.loc 0)))))

theorem cut2_subst :
    Expr.subst 0 Val.unit (.val (.lam (.val (Val.loc 0))) : Expr) = .val (.lam (.val (Val.loc 0))) := by
  simp [Expr.subst]

/-- **At `ℓ₀ ↦ mut(m+2, (), ∅, 𝒱⟦1⟧)`, one lifetime of room below the cut, the clause holds.** -/
theorem cut2_holds (m : ℕ) :
    cC (ℍ := ℍ) cut2C [] (cutδ m) cut2E (innerView 0 (lifeN (m + 2))) := by
  intro α ρ₁ ρ₂ hp hc
  obtain ⟨rfl, β, hβ, hlt⟩ := hp
  rw [show β = m from (Option.some.inj hβ).symm] at hlt
  have hρ₂ : ρ₂ = innerView 0 (lifeN (m + 2)) :=
    ResU.CompS.functional hc (ResU.comp_empty_right _)
  subst hρ₂
  refine cC_head _ (fun μ => .beta μ _ Val.unit) rfl _ _ _ ?_
  rw [cut2_subst]
  intro α' ρ₁ ρ₂ hp hc
  obtain ⟨rfl, β', hβ', hlt'⟩ := hp
  rw [show β' = OrderDual.ofDual α from (Option.some.inj hβ').symm] at hlt'
  have hρ₂ : ρ₂ = innerView 0 (lifeN (m + 2)) :=
    ResU.CompS.functional hc (ResU.comp_empty_right _)
  subst hρ₂
  refine wpTS_lolli [] (.val (Val.loc 0)) Val.unit _ _ ?_
  rw [adj_subst]
  refine wpTS_val [] (Val.loc 0) _ _ ?_
  have hle : α' ≤ lifeN (m + 2) := by
    have h1 : m < OrderDual.ofDual α := hlt
    have h2 : OrderDual.ofDual α < OrderDual.ofDual α' := hlt'
    show m + 2 ≤ OrderDual.ofDual α'
    omega
  exact ⟨α', rfl, 0, pure_sep_mk rfl (ptoMutS_innerView_le hle [] _)⟩

/-- **At a single `mut` cell at `n ≥ m + 3` with an empty witness, the clause fails**, at
`α = m + 1`, `α' = m + 2`. -/
theorem cut2_fails {m n : ℕ} (hn : m + 3 ≤ n) {h : ResU.InStratum (lifeN n) (PMap.empty : WRes)}
    {Q : Val → SPropS BoCa.Loc Val (lifeN n)} (hw : Q Val.unit ⟨PMap.empty, h⟩) :
    ¬ cC (ℍ := ℍ) cut2C [] (cutδ m) cut2E
      (ResU.single 0 (CellU.mutOf (lifeN n) Val.unit PMap.empty h Q hw)) := by
  intro hC
  have hflat := flat_single_mut_empty (k := 0) (u := Val.unit) (hw := hw)
  have hval : ResU.Valid (ResU.single 0 (CellU.mutOf (lifeN n) Val.unit PMap.empty h Q hw)) :=
    ⟨_, hflat⟩
  have hlt : LtLife (cutδ m) (.var 1) (lifeN (m + 1)) :=
    ⟨m, rfl, show OrderDual.toDual (m + 1 : ℕ) < OrderDual.toDual m from by
      show m < m + 1; omega⟩
  have hC1 := hC (lifeN (m + 1)) PMap.empty _ ⟨rfl, hlt⟩ (ResU.comp_empty_right _)
  have hlt' : LtLife ((cutδ m).extend 0 (m + 1)) (.var 0) (lifeN (m + 2)) :=
    ⟨m + 1, rfl, show OrderDual.toDual (m + 2 : ℕ) < OrderDual.toDual (m + 1) from by
      show m + 1 < m + 2; omega⟩
  have hwp := hC1 (lifeN (m + 2)) PMap.empty _ ⟨rfl, hlt'⟩ (ResU.comp_empty_right _)
  obtain ⟨ρ', ρp, -, -, π, v, -, -, -, ls', -, -, -, -, -, -, -, hπ, hU, -, -, -, -, -, hQ⟩ :=
    hwp PMap.empty _ [] ⟨(compS_empty_left _).1, _, compS_empty_left _, hval⟩
      (compS_empty_left _) (tw_single_mut_empty hw) (fun _ hx => absurd hx List.not_mem_nil)
      BoCa.BoLo.Alloc.leastFree 0
  obtain ⟨α, hα, ℓ, hsep⟩ := hQ
  obtain rfl : α = lifeN (m + 2) := (Option.some.inj hα).symm
  obtain ⟨-, b, u, χ, hχ, Q', hw', -, hαb, hρ', -, -, -⟩ := pure_sep_iff.mp hsep
  have hg : ρ'.get ℓ = some (CellU.mutOf b u χ hχ Q' hw') := by rw [hρ']; simp
  have hf : π.FlatAt ℓ (CellU.mutOf b u χ hχ Q' hw') :=
    pvLocal π ρp ρ' hU.2.2 (ResU.CompS.comm hπ) ℓ _ hg (CellU.kind_mutOf _ _ _ _ _ _)
  obtain ⟨v₀, χ₀, h₀, hw₀, σ₀, hσ₀, hg₀⟩ := (hU.1.2 ℓ b Q').mpr ⟨u, χ, hχ, hw', hf⟩
  rw [ResU.Flat.functional hσ₀ hflat] at hg₀
  obtain ⟨-, he⟩ := ResU.single_get_eq_some hg₀
  have hb : b = lifeN n := CellU.mutOf_at he
  rw [hb] at hαb
  have : n ≤ m + 2 := hαb
  omega

theorem cut2_fails' {m n : ℕ} (hn : m + 3 ≤ n) {b : Life} (hb : b = lifeN n) {χ : WRes}
    (hχe : χ = PMap.empty) {h : χ.InStratum b} {Q : Val → SPropS BoCa.Loc Val b}
    (hw : Q Val.unit ⟨χ, h⟩) :
    ¬ cC (ℍ := ℍ) cut2C [] (cutδ m) cut2E (ResU.single 0 (CellU.mutOf b Val.unit χ h Q hw)) := by
  subst hb hχe
  exact cut2_fails hn hw

theorem segθ_add2 (m k : ℕ) : segθ (lifeN m) k (lifeN (m + 2)) = lifeN (m + 2 + k) := by
  apply OrderDual.ofDual.injective
  rw [Restrat.Emb.shift_apply_lt (show lifeN (m + 2) < lifeN m from by
    show m < m + 2; omega)]
  rfl

/-- **A segment already separated from the cut by a gap is not safe either**: at every cut and
every `k > 0`, a configuration whose only cell lies one lifetime of room below the cut is related
and its whole-segment shift is not. -/
def SegShiftFailsWithRoom : Prop :=
  ∀ (m k : ℕ), 0 < k →
    ∃ (C : CTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes),
      (∃ (b : Life) (u : Val) (χ : WRes) (h : χ.InStratum b) (Q : Val → SPropS BoCa.Loc Val b)
          (hw : Q u ⟨χ, h⟩), ρ = ResU.single 0 (CellU.mutOf b u χ h Q hw) ∧
          b = lifeN (m + 2)) ∧
      cC (ℍ := ℍ) C ls δ e ρ ∧
        ¬ cC (ℍ := ℍ) C (ls.map (Targets.srecRestrat (segθ (lifeN m) k)))
          (Restrat.LSub.mapN (segθ (lifeN m) k).toNat δ) e ((segθ (lifeN m) k).relRU ρ)

theorem segShiftFailsWithRoom : SegShiftFailsWithRoom (ℍ := ℍ) := by
  intro m k hk
  refine ⟨cut2C, [], cutδ m, cut2E, innerView 0 (lifeN (m + 2)),
    ⟨_, _, _, _, _, _, rfl, rfl⟩, cut2_holds m, ?_⟩
  rw [List.map_nil, mapN_cutδ, innerView, Restrat.Emb.relRU_single, Restrat.Emb.relU_mutOf]
  exact cut2_fails' (n := m + 2 + k) (by omega) (segθ_add2 m k)
    (Restrat.Emb.relRU_empty (e := segθ (lifeN m) k)) _

end ProbeD1.SegShift

end
