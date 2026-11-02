import DtorUnwind.Tree.JoinFd

/-!
# No `own` cell of a lent location beneath a borrow: an invariant of `TWNC`

`NoOwnUnder W ps`: for every record proper `p`, no `own` cell at `p.le` sits beneath a borrow of
`W` (`OwnUnder`). `TWNC.noOwnUnder` proves it of every `TWNC` world by induction on the
constructors, the way `NoMut` is carried in `Core/Invariant.lean`:

* the borrows of the new world are borrows of the old one (`alloc`, `free`, `store`, `rebEnd`,
  `rebEndDeep`, and the untouched part of every other step);
* a new borrow's witness is a resource that already sat in the old world: at the top
  (`immFrame`'s escrow, `mutFold`'s payload) or beneath a borrow (`reb`/`rebDeep`'s image, whose
  witnesses are pieces of an escrow, `ownAt_image`; `mutUnfold`'s and `immEnd`'s released
  payloads).

An `own` cell at the top of the old world, at a record's location, is refused by `✓` and
`LeInv` (`own_not_at_view`); at the new record's location, beneath a borrow, by `✓` and the
`own` cell the lend takes (`not_ownUnder_top_own`, `MutAt`'s `not_mutAt_top_own` at `own`).

`joinFd_of_branch`: the join's frame condition at every type, from `fdFromBranch_views`'s
hypotheses and `p ∈ ps` alone.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Tree
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI

/-! ### Moving `own` cells -/

/-- `OwnAt` moves along any map of cells that keeps kind and witness. -/
theorem OwnAt.mono {ρ σ : WRes}
    (t : ∀ m (ψ : CellU Loc Val), ρ.get m = some ψ →
      ∃ ζ : CellU Loc Val, σ.get m = some ζ ∧ ζ.kind = ψ.kind ∧ ζ.wit = ψ.wit)
    {l : Loc} (h : OwnAt ρ l) : OwnAt σ l := by
  cases h with
  | top e hk =>
      obtain ⟨ζ, eζ, kζ, -⟩ := t _ _ e
      exact OwnAt.top eζ (kζ.trans hk)
  | nest e hk hw =>
      obtain ⟨ζ, eζ, kζ, wζ⟩ := t _ _ e
      exact OwnAt.nest eζ (kζ ▸ hk) (wζ ▸ hw)

theorem OwnAt.of_compS_left {a b c : WRes} (h : ResU.CompS a b c) {l : Loc}
    (ho : OwnAt a l) : OwnAt c l :=
  OwnAt.mono (fun _ _ e => by
    obtain ⟨ζ, eζ, kζ, wζ, -⟩ := compS_get_left' h e
    exact ⟨ζ, eζ, kζ, wζ⟩) ho

theorem OwnAt.of_le {q w : WRes} (h : ResU.Le q w) {l : Loc} (ho : OwnAt q l) : OwnAt w l := by
  obtain ⟨τ, hτ⟩ := h
  exact OwnAt.of_compS_left hτ ho

theorem OwnAt.of_del {q : WRes} {m l : Loc} (ho : OwnAt (q.del m) l) : OwnAt q l :=
  OwnAt.mono (fun x ψ e => by
    by_cases hx : x = m
    · subst hx; rw [ResU.del_get_self] at e; cases e
    · rw [ResU.del_get_ne _ hx] at e; exact ⟨ψ, e, rfl, rfl⟩) ho

/-- A borrow cell of `W` puts every `own` cell of its witness beneath a borrow of `W`. -/
theorem OwnUnder.of_cell {W : WRes} {m : Loc} {ψ : CellU Loc Val} (e : W.get m = some ψ)
    (hk : ψ.kind ≠ Kind.own) {x : Loc} (h : OwnAt ψ.wit x) : OwnUnder W x :=
  ⟨m, ψ, e, hk, h⟩

/-- A borrow of a `●` is a borrow of an operand. -/
theorem OwnUnder.split {a b c : WRes} (h : ResU.CompS a b c) {x : Loc}
    (ho : OwnUnder c x) : OwnUnder a x ∨ OwnUnder b x := by
  obtain ⟨m, ζ, e, hk, hw⟩ := ho
  rcases compS_back h e with ⟨ψ, eψ, kψ, wψ⟩ | ⟨ψ, eψ, kψ, wψ⟩
  · exact Or.inl ⟨m, ψ, eψ, kψ ▸ hk, wψ ▸ hw⟩
  · exact Or.inr ⟨m, ψ, eψ, kψ ▸ hk, wψ ▸ hw⟩

theorem not_ownUnder_single_own (m : Loc) (v : Val) (x : Loc) :
    ¬ OwnUnder (ResU.single m (CellU.ownOf v)) x := by
  rintro ⟨y, ψ, e, hk, -⟩
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  exact hk rfl

/-- The witness of a cell of a reborrow image is a piece of the source or the witness of a
source cell: an `own` cell beneath a borrow of the image sits in the source. -/
theorem ownAt_image {β : Life} {w₀ c : WRes} (hr : ResU.Reb β w₀ c) {x : Loc}
    (ho : OwnUnder c x) : OwnAt w₀ x := by
  obtain ⟨m, ψ, e, -, hw⟩ := ho
  obtain ⟨-, hcase⟩ := reb_cell hr e
  rcases hcase with ⟨u, q, h, hown, rfl, hqσ, ζq, hζq⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
  · rw [CellU.wit_immOf] at hw
    exact OwnAt.of_le hqσ (OwnAt.of_del hw)
  · exact OwnAt.nest eζ (by rw [kζ]; simp) (wζ ▸ hw)
  · exact OwnAt.nest eζ (by rw [kζ]; simp) (wζ ▸ hw)

/-! ### What `✓` refuses -/

/-- An `own` cell at `ℓ` at any depth of `ρ` shows at `ℓ` in `ex(ρ)` or in `ag(ρ)`
(`mutAt_walk_dom` at `own`). -/
theorem ownAt_walk_dom {ρ : WRes} {x : Loc} (h : OwnAt ρ x) :
    ∀ {R : CellU Loc Val → CellU Loc Val → Prop}
      {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop},
      (∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) → ResU.CompLaws C →
      ∀ {e a : WRes}, ExW R C ρ e → AgW ρ a →
      (∃ ζ, e.get x = some ζ) ∨ (∃ ζ, a.get x = some ζ) := by
  induction h with
  | @top ρ l ψ e hk =>
      intro R C hR hC ex a hex ha
      cases hex with
      | mk hs hw hb hnm hσ =>
          obtain ⟨ζ₁, e₁⟩ := comp_some hnm (ResU.restrict_get_some e hk)
          exact Or.inl (comp_some hσ e₁)
  | @nest ρ l m ψ e hk hmw ih =>
      intro R C hR hC ex a hex ha
      cases hkk : ψ.kind with
      | own => exact absurd hkk hk
      | imm =>
          obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgW.imm_wit_le ha e hkk
          rcases ih hRR ResU.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · obtain ⟨_, h1⟩ := comp_some hp hζ; exact Or.inr (comp_some hz h1)
          · obtain ⟨_, h1⟩ := comp_some_r hp hζ; exact Or.inr (comp_some hz h1)
      | «mut» =>
          obtain ⟨ev, z, hev, hz⟩ := ExW.wit_le hR hC hex e hkk
          obtain ⟨av, z', hav, hz'⟩ := AgW.mut_wit_le ha e hkk
          rcases ih hR hC hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · exact Or.inl (comp_some hz hζ)
          · exact Or.inr (comp_some hz' hζ)

/-- **A top-level `ℓ ↦ own(u)` of a valid resource sits beneath none of its borrows**
(`not_mutAt_top_own` at `own`). -/
theorem not_ownUnder_top_own {W : WRes} (hv : ResU.Valid W) {x : Loc} {u : Val}
    (hx : W.get x = some (CellU.ownOf u)) : ¬ OwnUnder W x := by
  rintro ⟨m, ψ, e, hk, hmw⟩
  obtain ⟨σ, eW, aW, heW, haW, hc⟩ := hv
  have eo : eW.get x = some (CellU.ownOf u) := ExS.get_of_ne_imm heW hx (by simp)
  have noAg : ∀ ζ, aW.get x = some ζ → False := fun ζ hζ =>
    ex_ag_disjoint ⟨σ, eW, aW, heW, haW, hc⟩ heW haW eo hζ
  cases hkk : ψ.kind with
  | own => exact hk hkk
  | imm =>
      obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgW.imm_wit_le haW e hkk
      rcases ownAt_walk_dom hmw hRR ResU.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
      · obtain ⟨_, h1⟩ := comp_some hp hζ
        obtain ⟨_, h2⟩ := comp_some hz h1
        exact noAg _ h2
      · obtain ⟨_, h1⟩ := comp_some_r hp hζ
        obtain ⟨_, h2⟩ := comp_some hz h1
        exact noAg _ h2
  | «mut» =>
      obtain ⟨av, z, hav, hz⟩ := AgW.mut_wit_le haW e hkk
      cases heW with
      | mk hs hw hb hnm hσ =>
          rename_i nm b w
          obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, e, hkk⟩)
          obtain ⟨ψ', hψ', hex'⟩ := ExWits.mem hw q hq
          rw [hq₁, e] at hψ'
          cases Option.some.inj hψ'
          rcases ownAt_walk_dom hmw hSS ResU.compLawsS hex' hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · obtain ⟨z', hz'⟩ :=
              BigComp.mem_factor hSS ResU.compLawsS hb q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩)
            obtain ⟨ζb, hζb⟩ := comp_some hz' hζ
            have hnm' : nm.get x = some (CellU.ownOf u) := by
              have hown : (W.restrict Kind.own).get x = some (CellU.ownOf u) :=
                ResU.restrict_get_some hx (by simp)
              exact (ResU.CompS.get_left_of_ne_imm hnm hown (by simp)).2
            have := ResU.CompatS.right_eq_none hσ.1 hnm' (by simp)
            rw [hζb] at this; cases this
          · obtain ⟨_, h1⟩ := comp_some hz hζ
            exact noAg _ h1

/-- **No `own` cell at the top where every `ag(W)` holds a cell**: `ex(W)_●` and `ag(W)` are
disjoint (`ex_ag_disjoint`). -/
theorem own_not_at_view {W : WRes} (hv : ResU.Valid W) {y : Loc}
    (hag : ∀ a, AgW W a → ∃ ψ : CellU Loc Val, a.get y = some ψ) {χ : CellU Loc Val} (e : W.get y = some χ) (hk : χ.kind = Kind.own) :
    False := by
  obtain ⟨σ, eW, aW, heW, haW, hc⟩ := hv
  have eo : eW.get y = some χ := ExS.get_of_ne_imm heW e (by rw [hk]; simp)
  obtain ⟨ψ, hψ⟩ := hag aW haW
  exact ex_ag_disjoint ⟨σ, eW, aW, heW, haW, hc⟩ heW haW eo hψ

/-- `LeInv` gives `own_not_at_view`'s hypothesis at every record proper. -/
theorem leInv_view {W : WRes} {ps rs : List FrameRec} (hT : TWNC W ps rs) {q : FrameRec}
    (hq : q ∈ ps) :
    ∀ a, AgW W a → ∃ ψ : CellU Loc Val, a.get q.le = some ψ := fun a ha => by
  obtain ⟨ψ, hψ, -, -, -⟩ := hT.inv.2.1 q hq a ha
  exact ⟨ψ, hψ⟩

/-! ### The invariant -/

/-- **No `own` cell of a record's location beneath a borrow of the world.** -/
def NoOwnUnder (W : WRes) (ps : List FrameRec) : Prop := ∀ p ∈ ps, ¬ OwnUnder W p.le

/-- A frame step: the borrows of `W′ = new ● Z` are `Z`'s, which sit in `W = (old ● ρ) ● Z`,
or the new cell's, whose witness `ρ` sits at the top of `W` or beneath one of its borrows. -/
theorem step_frame {W X Z ρ W' : WRes} {l : Loc} {v : Val} {ψ : CellU Loc Val}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X) (hW : ResU.CompS X Z W)
    (hψw : ψ.wit = ρ) (hW' : ResU.CompS (ResU.single l ψ) Z W') {x : Loc}
    (ho : OwnUnder W' x) :
    OwnUnder W x ∨ (∃ χ : CellU Loc Val, ρ.get x = some χ ∧ χ.kind = Kind.own) := by
  rcases OwnUnder.split hW' ho with ⟨m, ζ, e, hk, hw⟩ | hz
  · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
    rw [hψw] at hw
    cases hw with
    | top e' hk' => exact Or.inr ⟨_, e', hk'⟩
    | nest e' hk' hw' =>
        exact Or.inl (OwnUnder.of_compS_left hW
          (OwnUnder.of_compS_right hX ⟨_, _, e', hk', hw'⟩))
  · exact Or.inl (OwnUnder.of_compS_right hW hz)

/-- The top of `ρ` in `W = (ℓ ↦ own(v) ● ρ) ● Z` is the top of `W`. -/
theorem top_of_frame {W X Z ρ : WRes} {l : Loc} {v : Val}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X) (hW : ResU.CompS X Z W) {x : Loc}
    {χ : CellU Loc Val} (e : ρ.get x = some χ) :
    ∃ ζ : CellU Loc Val, W.get x = some ζ ∧ ζ.kind = χ.kind := by
  obtain ⟨ζ₁, e₁, k₁, -, -⟩ := compS_get_left' (ResU.CompS.comm hX) e
  obtain ⟨ζ, e₂, k₂, -, -⟩ := compS_get_left' hW e₁
  exact ⟨ζ, e₂, k₂.trans k₁⟩

/-- **`NoOwnUnder` is an invariant of `TWNC`.** -/
theorem TWNC.noOwnUnder {W : WRes} {ps rs : List FrameRec} (h : TWNC W ps rs) :
    NoOwnUnder W ps := by
  induction h with
  | empty => intro p hp; simp at hp
  | alloc _ _ _ hW _ ih =>
      intro p hp ho
      rcases OwnUnder.split hW ho with h | h
      · exact ih p hp h
      · exact not_ownUnder_single_own _ _ _ h
  | @immFrame W X Z R W' ps rs ds l v α T δ hα hT hadm hX hW hden hW' hv hds ih =>
      intro p hp ho
      rcases step_frame hX hW (CellU.wit_immOf _ _ _ _) hW' ho with h | ⟨χ, e, hk⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · -- the new record: `W(ℓ) = own(v)`
          have hl : W.get l = some (CellU.ownOf v) :=
            (ResU.CompS.get_left_of_ne_imm hW
              (ResU.CompS.get_left_of_ne_imm hX (ResU.single_get_self _ _) (by simp)).2
              (by simp)).2
          exact not_ownUnder_top_own hT.valid hl h
        · exact ih p hp h
      · rcases List.mem_cons.mp hp with rfl | hp
        · -- `ρ` misses `ℓ`: `ℓ ↦ own(v) ● ρ` is defined
          have := hX.1 l _ χ (ResU.single_get_self _ _) e
          exact absurd (CellU.CompatS.kind_left this) (by simp)
        · obtain ⟨ζ, eζ, kζ⟩ := top_of_frame hX hW e
          exact own_not_at_view hT.valid (leInv_view hT hp) eζ (kζ.trans hk)
  | reb r x hT hr hle hx hreb hden hβ hc hW hv ih =>
      intro p hp ho
      rcases OwnUnder.split hW ho with h | h
      · exact ih p hp h
      · exact ih p hp (OwnUnder.of_cell hle (by simp)
          (by rw [CellU.wit_immOf]; exact ownAt_image hreb h))
  | rebDeep r x hT hr hch hcell hx hreb hden hβc hrec hc hW hv ih =>
      intro p hp ho
      rcases OwnUnder.split hW ho with h | h
      · exact ih p hp h
      · exact ih p hp (OwnUnder.of_cell hcell (by simp)
          (by rw [CellU.wit_immOf]; exact ownAt_image hreb h))
  | mutFold hT hX hW hW' hv ih =>
      intro p hp ho
      rcases step_frame hX hW (CellU.wit_mutOf _ _ _ _ _ _) hW' ho with h | ⟨χ, e, hk⟩
      · exact ih p hp h
      · obtain ⟨ζ, eζ, kζ⟩ := top_of_frame hX hW e
        exact own_not_at_view hT.valid (leInv_view hT hp) eζ (kζ.trans hk)
  | mutUnfold hT hW hX hW' hv ih =>
      intro p hp ho
      rcases OwnUnder.split hW' ho with h | h
      · rcases OwnUnder.split hX h with h | ⟨m, ζ, e, hk, hw⟩
        · exact not_ownUnder_single_own _ _ _ h
        · obtain ⟨ψ, eψ, kψ, wψ, -⟩ :=
            compS_get_left' hW (ResU.single_get_self _ _)
          refine ih p hp (OwnUnder.of_cell eψ (by rw [kψ]; simp) ?_)
          rw [wψ, CellU.wit_mutOf]
          exact OwnAt.nest e hk hw
      · exact ih p hp (OwnUnder.of_compS_right hW h)
  | free hT hW hv ih =>
      intro p hp ho
      exact ih p hp (OwnUnder.of_compS_right hW ho)
  | store hT hW hW' hv ih =>
      intro p hp ho
      rcases OwnUnder.split hW' ho with h | h
      · exact not_ownUnder_single_own _ _ _ h
      · exact ih p hp (OwnUnder.of_compS_right hW h)
  | immEnd r hT hr hc hX' hW' hv hps hrs ih =>
      intro p hp ho
      have hp' : p ∈ _ := ((hps p).mp hp).1
      rcases OwnUnder.split hW' ho with h | h
      · rcases OwnUnder.split hX' h with h | ⟨m, ζ, e, hk, hw⟩
        · exact not_ownUnder_single_own _ _ _ h
        · obtain ⟨ψ, eψ, kψ, wψ, -⟩ :=
            compS_get_left' hc (ResU.single_get_self _ _)
          refine ih p hp' (OwnUnder.of_cell eψ (by rw [kψ]; simp) ?_)
          rw [wψ, CellU.wit_immOf]
          exact OwnAt.nest e hk hw
      · exact ih p hp' (OwnUnder.of_compS_right hc h)
  | rebEnd r hT hr hle hreb hW hβ ih =>
      intro p hp ho
      exact ih p hp (OwnUnder.of_compS_left hW ho)
  | rebEndDeep r hT hr hch hle hreb hW hβ ih =>
      intro p hp ho
      exact ih p hp (OwnUnder.of_compS_left hW ho)

/-- **The join's frame condition at every type.** With `fdFromBranch_views`'s hypotheses and
the record `p` proper, the resumer's other resources hold nothing at `p`'s location at any
depth; `joinFd_of_branch_of_noOwn`'s `hown` is `TWNC.noOwnUnder`. -/
theorem joinFd_of_branch (K : Cactus) {W ρf ρS ρk ρrest : WRes} {ps rs : List FrameRec}
    {p : FrameRec} {α n : Life} (hT : TWNC W ps rs) (hp : p ∈ ps)
    (hW : ResU.CompS ρf ρS W) (hS : ResU.CompS ρk ρrest ρS) (hFLp : FrameLife W p α)
    (hbr : ∀ τ, ResU.Flat ρrest τ → OnBranchRes K n τ) (hnα : ¬ K.le n α) :
    joinFd (Val.loc p.le) ρrest :=
  joinFd_of_branch_of_noOwn K hT hp hW hS hFLp hbr hnα (TWNC.noOwnUnder hT p hp)

end BoCa.Fig16.LogRel.Core.Tree

end
