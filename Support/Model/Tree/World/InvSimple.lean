import Support.Model.Tree.World.TInvReread

/-!
# `TIT` at the steps that keep the aliasable walk

`Core/Invariant.lean`'s `own_cell_ag`, `mut_fold_ag`, the `MutAt` lemmas, `chainInv_of_ag_sub` and
`ti_of_ag`, `ti_mutFold`, over the tree. `TIT` reads `ag(W)` only through hypotheses `AgW W a`
and `mut` cells only through `¬ MutAt W x` (`TIT.of_ag`). Allocation, `free`, `store` and
`mutUnfold` keep both (`tit_free`, `tit_store`, `tit_mutUnfold`); `mutFold` keeps the walk and
adds a `mut` cell only at a location no view sits at (`tit_mutFold`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-- `ag(ℓ ↦ own(v) ● Z) = ag(Z)`. -/
theorem own_cell_ag {Z W : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (h : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) Z W) (a : TRes K) : AgWT W a ↔ AgWT Z a := by
  constructor
  · intro ha
    obtain ⟨o, z, ho, hz, hc⟩ := (AgWT.split h).mp ha
    rw [AgWT.functional ho (AgWT.single_own l v)] at hc
    rw [ResUT.CompR.functional hc (ResUT.comp_empty_left z)]
    exact hz
  · intro ha
    exact (AgWT.split h).mpr ⟨_, _, AgWT.single_own l v, ha, ResUT.comp_empty_left a⟩

/-- `ag(ℓ ↦ own(v) ● ρ ● Z) = ag(ℓ ↦ mut(β, v, ρ, P̂) ● Z)`. -/
theorem mut_fold_ag {W X Z ρ W' : TRes K} {l : BoCa.Loc} {v : BoCa.Val} {b : TSet} [Fact (K.Anti b)]
    {hstr : ρ.InStratum b} {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K b} {hw : P v ⟨ρ, hstr⟩}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ X) (hW : ResUT.CompS X Z W)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.mutOf b v ρ hstr P hw)) Z W') (a : TRes K) :
    AgWT W a ↔ AgWT W' a := by
  constructor
  · intro ha
    obtain ⟨x, z, hx, hz, hxz⟩ := (AgWT.split hW).mp ha
    have hx' : AgWT ρ x := (own_cell_ag hX x).mp hx
    exact (AgWT.split hW').mpr ⟨x, z, AgWT.single_mut hx', hz, hxz⟩
  · intro ha
    obtain ⟨m, z, hm, hz, hmz⟩ := (AgWT.split hW').mp ha
    exact (AgWT.split hW).mpr ⟨m, z, (own_cell_ag hX m).mpr (AgWT.single_mut_inv hm), hz, hmz⟩

/-- `MutAt` moves along any map of non-`own` cells that keeps kind and witness. -/
theorem MutAtT.mono {ρ σ : TRes K}
    (t : ∀ m (ψ : TCell K), ρ.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ζ : TCell K, σ.get m = some ζ ∧ ζ.kind = ψ.kind ∧ ζ.wit = ψ.wit)
    {l : BoCa.Loc} (h : MutAtT ρ l) : MutAtT σ l := by
  cases h with
  | top e hk =>
      obtain ⟨ζ, eζ, kζ, -⟩ := t _ _ e (by rw [hk]; simp)
      exact MutAtT.top eζ (kζ.trans hk)
  | nest e hk hw =>
      obtain ⟨ζ, eζ, kζ, wζ⟩ := t _ _ e hk
      exact MutAtT.nest eζ (kζ ▸ hk) (wζ ▸ hw)

theorem MutAtT.of_compS_left {a b c : TRes K} (h : ResUT.CompS a b c) {l : BoCa.Loc}
    (hm : MutAtT a l) : MutAtT c l :=
  MutAtT.mono (fun m ψ e _ => by
    obtain ⟨ζ, eζ, kζ, wζ, -⟩ := compS_get_left' h e
    exact ⟨ζ, eζ, kζ, wζ⟩) hm

theorem MutAtT.of_compS_right {a b c : TRes K} (h : ResUT.CompS a b c) {l : BoCa.Loc}
    (hm : MutAtT b l) : MutAtT c l := MutAtT.of_compS_left (ResUT.CompS.comm h) hm

theorem MutAtT.of_le {q w : TRes K} (h : ResUT.Le q w) {l : BoCa.Loc} (hm : MutAtT q l) : MutAtT w l := by
  obtain ⟨τ, hτ⟩ := h
  exact MutAtT.of_compS_left hτ hm

theorem MutAtT.of_del {q : TRes K} {m l : BoCa.Loc} (hm : MutAtT (q.del m) l) : MutAtT q l :=
  MutAtT.mono (fun x ψ e _ => by
    by_cases hx : x = m
    · subst hx; rw [ResUT.del_get_self] at e; cases e
    · rw [ResUT.del_get_ne _ hx] at e; exact ⟨ψ, e, rfl, rfl⟩) hm

/-- A cell of a `●` comes from an operand with its kind and witness. -/

theorem MutAtT.split {a b c : TRes K} (h : ResUT.CompS a b c) {l : BoCa.Loc} (hm : MutAtT c l) :
    MutAtT a l ∨ MutAtT b l := by
  cases hm with
  | top e hk =>
      rcases compS_back h e with ⟨ψ, eψ, kψ, -⟩ | ⟨ψ, eψ, kψ, -⟩
      · exact Or.inl (MutAtT.top eψ (kψ.trans hk))
      · exact Or.inr (MutAtT.top eψ (kψ.trans hk))
  | nest e hk hw =>
      rcases compS_back h e with ⟨ψ, eψ, kψ, wψ⟩ | ⟨ψ, eψ, kψ, wψ⟩
      · exact Or.inl (MutAtT.nest eψ (kψ ▸ hk) (wψ ▸ hw))
      · exact Or.inr (MutAtT.nest eψ (kψ ▸ hk) (wψ ▸ hw))

/-- An `own` cell carries no `mut` cell. -/
theorem not_mutAt_single_own (m : BoCa.Loc) (v : BoCa.Val) (l : BoCa.Loc) :
    ¬ MutAtT (ResUT.single m (CellUT.ownOf (K := K) v)) l := by
  intro h
  cases h with
  | top e hk => obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e; exact absurd hk (by simp)
  | nest e hk _ => obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e; exact hk rfl

/-- **`chainInv_of_ag_sub`.** -/
theorem chainInvT_of_ag_sub {Θ : CodeTy} {W W' : TRes K} {rs : List (FrameRecT K)}
    (t : ∀ a, AgWT W' a → AgWT W a) (h : ChainInvT K Θ W rs) : ChainInvT K Θ W' rs := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun r hr p m S u hc a ha ψ e hk => h1 r hr p m S u hc a (t a ha) ψ e hk,
    fun r hr m u hm a ha => h2 r hr m u hm a (t a ha), h3, h4, fun r hr hv => ?_,
    fun r hr p₀ l₀ S₀ u₀ hc hv => ?_⟩
  · obtain ⟨S, m, u, hR, a, ha, ψ, e, hk⟩ := hv
    obtain ⟨β₀, c₀, q1, q2, q3, q5⟩ := h5 r hr ⟨S, m, u, hR, a, t a ha, ψ, e, hk⟩
    exact ⟨β₀, c₀, q1, q2, q3, fun S m u hR a ha => q5 S m u hR a (t a ha)⟩
  · obtain ⟨m, S, u, hc', a, ha, ψ, e, hk⟩ := hv
    obtain ⟨w₀, hw₀, β₀, c₀, q1, q2, q3, q5⟩ :=
      h6 r hr p₀ l₀ S₀ u₀ hc ⟨m, S, u, hc', a, t a ha, ψ, e, hk⟩
    exact ⟨w₀, fun a ha => hw₀ a (t a ha), β₀, c₀, q1, q2, q3,
      fun m S u hc a ha => q5 m S u hc a (t a ha)⟩

theorem nestLifeT_of_ag {W W' : TRes K} {r : FrameRecT K} (t : ∀ a, AgWT W' a → AgWT W a)
    (h : NestLifeT K W r) : NestLifeT K W' r :=
  fun l₀ l S u hc a ha => h l₀ l S u hc a (t a ha)

/-- **`ti_of_ag`.** -/
theorem TIT.of_ag {Θ : CodeTy} {W W' : TRes K} {ps rs : List (FrameRecT K)}
    (t : ∀ a, AgWT W' a → AgWT W a) (tm : ∀ x, MutAtT W' x → MutAtT W x)
    (h : TIT K Θ W ps rs) : TIT K Θ W' ps rs := by
  obtain ⟨h3, hl, hid, hio, hN, hM, hmem, hC⟩ := h
  exact ⟨chainInvT_of_ag_sub t h3, fun r hr a ha => hl r hr a (t a ha), hid, hio,
    fun r hr => nestLifeT_of_ag t (hN r hr), ⟨fun r hr hm => hM.1 r hr (tm _ hm),
    fun r hr l u hl' hm => hM.2 r hr l u hl' (tm _ hm)⟩, hmem, fun a ha => hC a (t a ha)⟩

/-- **`TWNT.free` keeps `TIT`.** -/
theorem tit_free {Θ : CodeTy} {W W' : TRes K} {ps rs : List (FrameRecT K)} {l : BoCa.Loc}
    {v : BoCa.Val} (hW : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) W' W)
    (h : TIT K Θ W ps rs) : TIT K Θ W' ps rs :=
  TIT.of_ag (fun a ha => (own_cell_ag hW a).mpr ha) (fun _ hm => MutAtT.of_compS_right hW hm) h

/-- **`TWNT.store` keeps `TIT`.** -/
theorem tit_store {Θ : CodeTy} {W Z W' : TRes K} {ps rs : List (FrameRecT K)} {l : BoCa.Loc}
    {v₁ v₂ : BoCa.Val} (hW : ResUT.CompS (ResUT.single l (CellUT.ownOf v₁)) Z W)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.ownOf v₂)) Z W') (h : TIT K Θ W ps rs) :
    TIT K Θ W' ps rs := by
  refine TIT.of_ag (fun a ha => (own_cell_ag hW a).mpr ((own_cell_ag hW' a).mp ha))
    (fun x hm => ?_) h
  rcases MutAtT.split hW' hm with h | h
  · exact (not_mutAt_single_own _ _ _ h).elim
  · exact MutAtT.of_compS_right hW h

/-- **`TWNT.mutUnfold` keeps `TIT`.** -/
theorem tit_mutUnfold {Θ : CodeTy} {W X Z ρ W' : TRes K} {ps rs : List (FrameRecT K)}
    {l : BoCa.Loc} {v : BoCa.Val} {b : TSet} [Fact (K.Anti b)] {hstr : ρ.InStratum b}
    {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K b} {hw : P v ⟨ρ, hstr⟩}
    (hW : ResUT.CompS (ResUT.single l (CellUT.mutOf b v ρ hstr P hw)) Z W)
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ X) (hW' : ResUT.CompS X Z W')
    (h : TIT K Θ W ps rs) : TIT K Θ W' ps rs := by
  refine TIT.of_ag (fun a ha => (mut_fold_ag hX hW' hW a).mp ha) (fun x hm => ?_) h
  rcases MutAtT.split hW' hm with h | h
  · rcases MutAtT.split hX h with h' | h'
    · exact (not_mutAt_single_own _ _ _ h').elim
    · refine MutAtT.nest (ResUT.CompS.get_left_of_ne_imm hW (ResUT.single_get_self _ _)
        (by simp)).2 (by simp) ?_
      rw [CellUT.wit_mutOf]; exact h'
  · exact MutAtT.of_compS_right hW h

/-- **`TWNT.mutFold` keeps `TIT`** (`ti_mutFold`). -/
theorem tit_mutFold {Θ : CodeTy} {W X Z ρ W' : TRes K} {ps rs : List (FrameRecT K)} {l : BoCa.Loc} {v : BoCa.Val} {b : TSet} [Fact (K.Anti b)]
    {hstr : ρ.InStratum b} {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K b} {hw : P v ⟨ρ, hstr⟩}
    (hvW : ResUT.Valid W) (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ X)
    (hW : ResUT.CompS X Z W)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.mutOf b v ρ hstr P hw)) Z W') (h : TIT K Θ W ps rs) :
    TIT K Θ W' ps rs := by
  have t := fun a ha => (mut_fold_ag hX hW hW' a).mpr ha
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have Wl : W.get l = some (CellUT.ownOf v) :=
    (ResUT.CompS.get_left_of_ne_imm hW
      (ResUT.CompS.get_left_of_ne_imm hX (ResUT.single_get_self _ _) (by simp)).2 (by simp)).2
  have lNone : aW.get l = none := by
    obtain ⟨σ, eW, aW', heW, haW', hc⟩ := hvW
    rw [AgWT.functional haW' haW] at hc
    cases e : aW.get l with
    | none => rfl
    | some ζ =>
        exact (ex_ag_disjoint ⟨σ, eW, aW, heW, haW, hc⟩ heW haW
          (ExST.get_of_ne_imm heW Wl (by simp)) e).elim
  have tm : ∀ x, MutAtT W' x → MutAtT W x ∨ x = l := by
    intro x hm
    rcases MutAtT.split hW' hm with h₁ | h₂
    · cases h₁ with
      | top e hk => exact Or.inr (ResUT.single_get_eq_some e).1
      | nest e hk hw' =>
          obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
          rw [CellUT.wit_mutOf] at hw'
          exact Or.inl (MutAtT.of_compS_left hW (MutAtT.of_compS_right hX hw'))
    · exact Or.inl (MutAtT.of_compS_right hW h₂)
  obtain ⟨h3, hl, hid, hio, hN, hM, hmem, hC⟩ := h
  refine ⟨chainInvT_of_ag_sub t h3, fun r hr a ha => hl r hr a (t a ha), hid, hio,
    fun r hr => nestLifeT_of_ag t (hN r hr), ⟨fun r hr hm => ?_, fun r hr m u hm hmm => ?_⟩,
    hmem, fun a ha => hC a (t a ha)⟩
  · rcases tm _ hm with h' | h'
    · exact hM.1 r hr h'
    · obtain ⟨ψ, e, -⟩ := hl r hr aW haW
      rw [h', lNone] at e; cases e
  · rcases tm _ hmm with h' | h'
    · exact hM.2 r hr m u hm h'
    · obtain ⟨ζ, e⟩ := h3.2.1 r hr m u hm aW haW
      rw [h', lNone] at e; cases e


end BoCa.Fig16.Tree.Wp

end
