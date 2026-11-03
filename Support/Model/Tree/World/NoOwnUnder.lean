import Support.Model.Tree.World.TInv

/-!
# No `own` cell of a lent location beneath a borrow, over the tree world

`Tree/NoOwnUnder.lean` (branch `tree-life`) over `TWNT`: the vocabulary (`OwnAt`, `OwnUnder`)
and its lemmas, ported by `port-tools/port.py` from that file and `Tree/JoinFd.lean`, with
`Core/Invariant.lean`'s `compS_back` and `hSS`. `TWNT.noOwnUnder`, which reads `TIT`, is in
`TreeWp/InvUses.lean`, after `TWNT.inv`.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

variable {K : WCactus}
/-- A cell of a `●` comes from an operand with its kind and witness. -/
theorem compS_back {a b c : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompS a b c) {m : Loc} {ζ : CellUT Loc Val K}
    (e : c.get m = some ζ) :
    (∃ ψ : CellUT Loc Val K, a.get m = some ψ ∧ ψ.kind = ζ.kind ∧ ψ.wit = ζ.wit) ∨
    (∃ ψ : CellUT Loc Val K, b.get m = some ψ ∧ ψ.kind = ζ.kind ∧ ψ.wit = ζ.wit) := by
  rcases ResUT.Comp.get h m with ⟨-, -, e'⟩ | ⟨χ, e₁, -, e'⟩ | ⟨χ, -, e₂, e'⟩ |
      ⟨χ₁, χ₂, χ, e₁, e₂, e', hC⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, rfl, rfl⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, rfl, rfl⟩
  · rw [e'] at e; cases e
    refine Or.inl ⟨_, e₁, ?_, (CellUT.CompS.wit hC).1.symm⟩
    rw [CellUT.CompS.kind hC]
    obtain ⟨_, _, _, _, _, _, _, h₁, _, _⟩ := hC
    rw [h₁]; rfl

theorem hSS : ∀ ψ₁ ψ₂ ψ : CellUT Loc Val K, CellUT.CompS ψ₁ ψ₂ ψ → CellUT.CompatS ψ₁ ψ₂ := by
  intro ψ₁ ψ₂ ψ h
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, -, e₁, e₂, -⟩ := h
  exact ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩


/-- `OwnAt ρ ℓ`: an `own` cell at `ℓ` sits in `ρ`, at the top or inside the witness of a
non-`own` cell (`MutAt` at `own`). -/
inductive OwnAt : (ResUT BoCa.Loc BoCa.Val K) → Loc → Prop
  | top {ρ : (ResUT BoCa.Loc BoCa.Val K)} {l : Loc} {ψ : CellUT Loc Val K} :
      ρ.get l = some ψ → ψ.kind = Kind.own → OwnAt ρ l
  | nest {ρ : (ResUT BoCa.Loc BoCa.Val K)} {l m : Loc} {ψ : CellUT Loc Val K} :
      ρ.get m = some ψ → ψ.kind ≠ Kind.own → OwnAt ψ.wit l → OwnAt ρ l

/-- An `own` cell at `ℓ` beneath a borrow of `ρ`. -/
def OwnUnder (ρ : (ResUT BoCa.Loc BoCa.Val K)) (l : Loc) : Prop :=
  ∃ m, ∃ ψ : CellUT Loc Val K, ρ.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ OwnAt ψ.wit l

theorem OwnUnder.of_compS_left {a b c : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompS a b c) {l : Loc}
    (ho : OwnUnder a l) : OwnUnder c l := by
  obtain ⟨m, ψ, e, hk, hw⟩ := ho
  obtain ⟨ζ, eζ, kζ, wζ, -⟩ := compS_get_left' h e
  exact ⟨m, ζ, eζ, kζ ▸ hk, wζ ▸ hw⟩

theorem OwnUnder.of_compS_right {a b c : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompS a b c) {l : Loc}
    (ho : OwnUnder b l) : OwnUnder c l := OwnUnder.of_compS_left (ResUT.CompS.comm h) ho



/-- `OwnAt` moves along any map of cells that keeps kind and witness. -/
theorem OwnAt.mono {ρ σ : (ResUT BoCa.Loc BoCa.Val K)}
    (t : ∀ m (ψ : CellUT Loc Val K), ρ.get m = some ψ →
      ∃ ζ : CellUT Loc Val K, σ.get m = some ζ ∧ ζ.kind = ψ.kind ∧ ζ.wit = ψ.wit)
    {l : Loc} (h : OwnAt ρ l) : OwnAt σ l := by
  cases h with
  | top e hk =>
      obtain ⟨ζ, eζ, kζ, -⟩ := t _ _ e
      exact OwnAt.top eζ (kζ.trans hk)
  | nest e hk hw =>
      obtain ⟨ζ, eζ, kζ, wζ⟩ := t _ _ e
      exact OwnAt.nest eζ (kζ ▸ hk) (wζ ▸ hw)

theorem OwnAt.of_compS_left {a b c : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompS a b c) {l : Loc}
    (ho : OwnAt a l) : OwnAt c l :=
  OwnAt.mono (fun _ _ e => by
    obtain ⟨ζ, eζ, kζ, wζ, -⟩ := compS_get_left' h e
    exact ⟨ζ, eζ, kζ, wζ⟩) ho

theorem OwnAt.of_le {q w : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.Le q w) {l : Loc} (ho : OwnAt q l) : OwnAt w l := by
  obtain ⟨τ, hτ⟩ := h
  exact OwnAt.of_compS_left hτ ho

theorem OwnAt.of_del {q : (ResUT BoCa.Loc BoCa.Val K)} {m l : Loc} (ho : OwnAt (q.del m) l) : OwnAt q l :=
  OwnAt.mono (fun x ψ e => by
    by_cases hx : x = m
    · subst hx; rw [ResUT.del_get_self] at e; cases e
    · rw [ResUT.del_get_ne _ hx] at e; exact ⟨ψ, e, rfl, rfl⟩) ho

/-- A borrow cell of `W` puts every `own` cell of its witness beneath a borrow of `W`. -/
theorem OwnUnder.of_cell {W : (ResUT BoCa.Loc BoCa.Val K)} {m : Loc} {ψ : CellUT Loc Val K} (e : W.get m = some ψ)
    (hk : ψ.kind ≠ Kind.own) {x : Loc} (h : OwnAt ψ.wit x) : OwnUnder W x :=
  ⟨m, ψ, e, hk, h⟩

/-- A borrow of a `●` is a borrow of an operand. -/
theorem OwnUnder.split {a b c : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompS a b c) {x : Loc}
    (ho : OwnUnder c x) : OwnUnder a x ∨ OwnUnder b x := by
  obtain ⟨m, ζ, e, hk, hw⟩ := ho
  rcases compS_back h e with ⟨ψ, eψ, kψ, wψ⟩ | ⟨ψ, eψ, kψ, wψ⟩
  · exact Or.inl ⟨m, ψ, eψ, kψ ▸ hk, wψ ▸ hw⟩
  · exact Or.inr ⟨m, ψ, eψ, kψ ▸ hk, wψ ▸ hw⟩

theorem not_ownUnder_single_own (m : Loc) (v : Val) (x : Loc) :
    ¬ OwnUnder (ResUT.single m (CellUT.ownOf (K := K) v)) x := by
  rintro ⟨y, ψ, e, hk, -⟩
  obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
  exact hk rfl

/-- The witness of a cell of a reborrow image is a piece of the source or the witness of a
source cell: an `own` cell beneath a borrow of the image sits in the source. -/
theorem ownAt_image {β : Life} {w₀ c : (ResUT BoCa.Loc BoCa.Val K)} (hr : ResUT.Reb β w₀ c) {x : Loc}
    (ho : OwnUnder c x) : OwnAt w₀ x := by
  obtain ⟨m, ψ, e, -, hw⟩ := ho
  obtain ⟨-, hcase⟩ := reb_cell hr e
  rcases hcase with ⟨u, q, h, hown, rfl, hqσ, ζq, hζq⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
  · rw [CellUT.wit_immOf] at hw
    exact OwnAt.of_le hqσ (OwnAt.of_del hw)
  · exact OwnAt.nest eζ (by rw [kζ]; simp) (wζ ▸ hw)
  · exact OwnAt.nest eζ (by rw [kζ]; simp) (wζ ▸ hw)

/-! ### What `✓` refuses -/

/-- An `own` cell at `ℓ` at any depth of `ρ` shows at `ℓ` in `ex(ρ)` or in `ag(ρ)`
(`mutAt_walk_dom` at `own`). -/
theorem ownAt_walk_dom {ρ : (ResUT BoCa.Loc BoCa.Val K)} {x : Loc} (h : OwnAt ρ x) :
    ∀ {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
      {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop},
      (∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) → ResUT.CompLaws C →
      ∀ {e a : (ResUT BoCa.Loc BoCa.Val K)}, ExWT R C ρ e → AgWT ρ a →
      (∃ ζ, e.get x = some ζ) ∨ (∃ ζ, a.get x = some ζ) := by
  induction h with
  | @top ρ l ψ e hk =>
      intro R C hR hC ex a hex ha
      cases hex with
      | mk hs hw hb hnm hσ =>
          obtain ⟨ζ₁, e₁⟩ := comp_some hnm (ResUT.restrict_get_some e hk)
          exact Or.inl (comp_some hσ e₁)
  | @nest ρ l m ψ e hk hmw ih =>
      intro R C hR hC ex a hex ha
      cases hkk : ψ.kind with
      | own => exact absurd hkk hk
      | imm =>
          obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgWT.imm_wit_le ha e hkk
          rcases ih hRR ResUT.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · obtain ⟨_, h1⟩ := comp_some hp hζ; exact Or.inr (comp_some hz h1)
          · obtain ⟨_, h1⟩ := comp_some_r hp hζ; exact Or.inr (comp_some hz h1)
      | «mut» =>
          obtain ⟨ev, z, hev, hz⟩ := ExWT.wit_le hR hC hex e hkk
          obtain ⟨av, z', hav, hz'⟩ := AgWT.mut_wit_le ha e hkk
          rcases ih hR hC hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · exact Or.inl (comp_some hz hζ)
          · exact Or.inr (comp_some hz' hζ)

/-- **A top-level `ℓ ↦ own(u)` of a valid resource sits beneath none of its borrows**
(`not_mutAt_top_own` at `own`). -/
theorem not_ownUnder_top_own {W : (ResUT BoCa.Loc BoCa.Val K)} (hv : ResUT.Valid W) {x : Loc} {u : Val}
    (hx : W.get x = some (CellUT.ownOf u)) : ¬ OwnUnder W x := by
  rintro ⟨m, ψ, e, hk, hmw⟩
  obtain ⟨σ, eW, aW, heW, haW, hc⟩ := hv
  have eo : eW.get x = some (CellUT.ownOf u) := ExST.get_of_ne_imm heW hx (by simp)
  have noAg : ∀ ζ, aW.get x = some ζ → False := fun ζ hζ =>
    ex_ag_disjoint ⟨σ, eW, aW, heW, haW, hc⟩ heW haW eo hζ
  cases hkk : ψ.kind with
  | own => exact hk hkk
  | imm =>
      obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgWT.imm_wit_le haW e hkk
      rcases ownAt_walk_dom hmw hRR ResUT.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
      · obtain ⟨_, h1⟩ := comp_some hp hζ
        obtain ⟨_, h2⟩ := comp_some hz h1
        exact noAg _ h2
      · obtain ⟨_, h1⟩ := comp_some_r hp hζ
        obtain ⟨_, h2⟩ := comp_some hz h1
        exact noAg _ h2
  | «mut» =>
      obtain ⟨av, z, hav, hz⟩ := AgWT.mut_wit_le haW e hkk
      cases heW with
      | mk hs hw hb hnm hσ =>
          rename_i nm b w
          obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, e, hkk⟩)
          obtain ⟨ψ', hψ', hex'⟩ := ExWitsT.mem hw q hq
          rw [hq₁, e] at hψ'
          cases Option.some.inj hψ'
          rcases ownAt_walk_dom hmw hSS ResUT.compLawsS hex' hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · obtain ⟨z', hz'⟩ :=
              BigCompT.mem_factor hSS ResUT.compLawsS hb q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩)
            obtain ⟨ζb, hζb⟩ := comp_some hz' hζ
            have hnm' : nm.get x = some (CellUT.ownOf u) := by
              have hown : (G.restrict CellUT.kind W Kind.own).get x = some (CellUT.ownOf u) :=
                ResUT.restrict_get_some hx (by simp)
              exact (ResUT.CompS.get_left_of_ne_imm hnm hown (by simp)).2
            have := ResUT.CompatS.right_eq_none hσ.1 hnm' (by simp)
            rw [hζb] at this; cases this
          · obtain ⟨_, h1⟩ := comp_some hz hζ
            exact noAg _ h1

/-- **No `own` cell at the top where every `ag(W)` holds a cell**: `ex(W)_●` and `ag(W)` are
disjoint (`ex_ag_disjoint`). -/
theorem own_not_at_view {W : (ResUT BoCa.Loc BoCa.Val K)} (hv : ResUT.Valid W) {y : Loc}
    (hag : ∀ a, AgWT W a → ∃ ψ : CellUT Loc Val K, a.get y = some ψ) {χ : CellUT Loc Val K} (e : W.get y = some χ) (hk : χ.kind = Kind.own) :
    False := by
  obtain ⟨σ, eW, aW, heW, haW, hc⟩ := hv
  have eo : eW.get y = some χ := ExST.get_of_ne_imm heW e (by rw [hk]; simp)
  obtain ⟨ψ, hψ⟩ := hag aW haW
  exact ex_ag_disjoint ⟨σ, eW, aW, heW, haW, hc⟩ heW haW eo hψ


/-- A frame step: the borrows of `W′ = new ● Z` are `Z`'s, which sit in `W = (old ● ρ) ● Z`,
or the new cell's, whose witness `ρ` sits at the top of `W` or beneath one of its borrows. -/
theorem step_frame {W X Z ρ W' : (ResUT BoCa.Loc BoCa.Val K)} {l : Loc} {v : Val} {ψ : CellUT Loc Val K}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ X) (hW : ResUT.CompS X Z W)
    (hψw : ψ.wit = ρ) (hW' : ResUT.CompS (ResUT.single l ψ) Z W') {x : Loc}
    (ho : OwnUnder W' x) :
    OwnUnder W x ∨ (∃ χ : CellUT Loc Val K, ρ.get x = some χ ∧ χ.kind = Kind.own) := by
  rcases OwnUnder.split hW' ho with ⟨m, ζ, e, hk, hw⟩ | hz
  · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
    rw [hψw] at hw
    cases hw with
    | top e' hk' => exact Or.inr ⟨_, e', hk'⟩
    | nest e' hk' hw' =>
        exact Or.inl (OwnUnder.of_compS_left hW
          (OwnUnder.of_compS_right hX ⟨_, _, e', hk', hw'⟩))
  · exact Or.inl (OwnUnder.of_compS_right hW hz)

/-- The top of `ρ` in `W = (ℓ ↦ own(v) ● ρ) ● Z` is the top of `W`. -/
theorem top_of_frame {W X Z ρ : (ResUT BoCa.Loc BoCa.Val K)} {l : Loc} {v : Val}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ X) (hW : ResUT.CompS X Z W) {x : Loc}
    {χ : CellUT Loc Val K} (e : ρ.get x = some χ) :
    ∃ ζ : CellUT Loc Val K, W.get x = some ζ ∧ ζ.kind = χ.kind := by
  obtain ⟨ζ₁, e₁, k₁, -, -⟩ := compS_get_left' (ResUT.CompS.comm hX) e
  obtain ⟨ζ, e₂, k₂, -, -⟩ := compS_get_left' hW e₁
  exact ⟨ζ, e₂, k₂.trans k₁⟩

/-! ### Re-reading -/

/-- An `own` cell at depth of a re-read resource sits at depth of the original. -/
theorem OwnAt.rr_back {Θ : LocTy} {K' : WCactus} {ρ' : TRes K'} {x : BoCa.Loc}
    (h : OwnAt ρ' x) : ∀ {ρ : TRes K}, RR Θ ρ ρ' → OwnAt ρ x := by
  induction h with
  | top e hk =>
      intro ρ hr
      obtain ⟨ψ, e', hc⟩ := hr.get_some' e
      exact OwnAt.top e' (hc.kind ▸ hk)
  | nest e hk _ ih =>
      intro ρ hr
      obtain ⟨ψ, e', hc⟩ := hr.get_some' e
      exact OwnAt.nest e' (hc.kind ▸ hk) (ih hc.wit)

theorem OwnUnder.rr_back {Θ : LocTy} {K' : WCactus} {ρ : TRes K} {ρ' : TRes K'}
    (hr : RR Θ ρ ρ') {x : BoCa.Loc} (h : OwnUnder ρ' x) : OwnUnder ρ x := by
  obtain ⟨m, ψ', e', hk, hw⟩ := h
  obtain ⟨ψ, e, hc⟩ := hr.get_some' e'
  exact ⟨m, ψ, e, hc.kind ▸ hk, hw.rr_back hc.wit⟩

/-! ### The invariant -/


end BoCa.Fig16.Tree.Wp

end
