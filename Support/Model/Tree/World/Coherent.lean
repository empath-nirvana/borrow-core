import Support.Model.Tree.World.Templ
import Support.Model.Tree.World.NoOwnUnder

/-!
# Template coherence across a re-reading

`[spec §62]`. `TcCoherent` (`World/Templ.lean`) asks that two used arguments at one code and value whose
escrows re-read to one escrow have templates that re-read to one template. A re-reading keeps
every cell's location, kind, value and an `imm` cell's lifetime set; it reads a `mut` cell's
antichain as `min_{K′}`, so two `mut` cells at one location differing only in their antichains can
re-read to one cell. That is the only way two resources re-read to one (`RR.inj_of`).

**Two `mut` cells at one location, at any depth of a `TWNT` world, are one cell**
(`TWNT.mutOne`). A `mut` cell is made only by `mutFold` from an `own` cell at the top of a valid
world, where no other cell of that location sits at any depth (`cellAt_top_own`); the other
operations move cells, copy witnesses into reborrow images, or remove cells; a re-reading is a
function. So every used argument, its cells at depth in the world, re-reads injectively, and
`TcCoherent` holds (`TWNT.tcCoherent`).

* `CellAt ρ y ψ`: `ψ` sits at `y` at some depth of `ρ` (`OwnAt` at every kind).
* `cellAt_walk_dom`, `cellAt_top_own`: `ownAt_walk_dom` and `not_ownUnder_top_own` at every kind.
* `MutOne`, `TWNT.mutOne`: the invariant, by `TWNT`'s induction.
* `RC.inj_of`, `RR.inj_of`: re-reading is injective on cells at depth of a `MutOne` world.
* `agW_cellAt`: a non-`own` cell of `ag(ρ)` carries the witness of a cell at depth of `ρ`.
* `TWNT.used_cellAt`, `TWNT.tcCoherent`, `TWNT.tcCarried_exists` read `TIT`; they are in
  `World/InvUses.lean`, after `TWNT.inv`.

The choice itself is recorded in the world (`TWd.tc`, `World/World.lean`): `RecInv` reads
`TWNT` at `w.tc`, so a run that does not grow the tree reads every canonical image at its start's
choice, and a grown world's choice is a carried one.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-! ### Cells at depth -/

/-- `ψ` sits at `y` in `ρ`, at the top or at some depth of a top cell's witness. -/
inductive CellAt : TRes K → BoCa.Loc → TCell K → Prop
  | top {ρ : TRes K} {y : BoCa.Loc} {ψ : TCell K} : ρ.get y = some ψ → CellAt ρ y ψ
  | nest {ρ : TRes K} {m y : BoCa.Loc} {χ ψ : TCell K} :
      ρ.get m = some χ → CellAt χ.wit y ψ → CellAt ρ y ψ

theorem CellAt.not_empty {y : BoCa.Loc} {ψ : TCell K} : ¬ CellAt (PMap.empty : TRes K) y ψ := by
  intro h
  cases h with
  | top e => simp at e
  | nest e _ => simp at e

/-- The cells of a cell's witness at depth are at depth. -/
theorem CellAt.wit_trans {ρ : TRes K} {y : BoCa.Loc} {ψ : TCell K} (h : CellAt ρ y ψ)
    {m : BoCa.Loc} {χ : TCell K} (e : ψ.wit.get m = some χ) : CellAt ρ m χ := by
  induction h with
  | top e' => exact .nest e' (.top e)
  | nest e' _ ih => exact .nest e' (ih e)

/-- A non-`imm` cell at depth of a `●`-operand is one of the composite. -/
theorem CellAt.of_compS_left {a b c : TRes K} (hc : ResUT.CompS a b c) {y : BoCa.Loc}
    {ψ : TCell K} (h : CellAt a y ψ) (hk : ψ.kind ≠ Kind.imm) : CellAt c y ψ := by
  cases h with
  | top e => exact .top (ResUT.CompS.get_left_of_ne_imm hc e hk).2
  | nest e h' =>
      obtain ⟨ζ, eζ, -, wζ, -⟩ := compS_get_left' hc e
      exact .nest eζ (wζ ▸ h')

theorem CellAt.of_compS_right {a b c : TRes K} (hc : ResUT.CompS a b c) {y : BoCa.Loc}
    {ψ : TCell K} (h : CellAt b y ψ) (hk : ψ.kind ≠ Kind.imm) : CellAt c y ψ :=
  CellAt.of_compS_left (ResUT.CompS.comm hc) h hk

theorem CellAt.of_le {q w : TRes K} (hq : ResUT.Le q w) {y : BoCa.Loc} {ψ : TCell K}
    (h : CellAt q y ψ) (hk : ψ.kind ≠ Kind.imm) : CellAt w y ψ := by
  obtain ⟨τ, hτ⟩ := hq
  exact h.of_compS_left hτ hk

theorem CellAt.of_del {q : TRes K} {m y : BoCa.Loc} {ψ : TCell K} (h : CellAt (q.del m) y ψ) :
    CellAt q y ψ := by
  cases h with
  | top e =>
      by_cases hy : y = m
      · subst hy; rw [ResUT.del_get_self] at e; cases e
      · rw [ResUT.del_get_ne _ hy] at e; exact .top e
  | @nest _ m' _ χ _ e h' =>
      by_cases hm : m' = m
      · subst hm; rw [ResUT.del_get_self] at e; cases e
      · rw [ResUT.del_get_ne _ hm] at e; exact .nest e h'

/-- A `●` composes `imm` cells only. -/
theorem CellUT.CompS.kind_imm {ψ₁ ψ₂ ψ : TCell K} (hC : CellUT.CompS ψ₁ ψ₂ ψ) :
    ψ.kind = Kind.imm := by
  rw [CellUT.CompS.kind hC]

/-- A non-`imm` cell at depth of a composite sits at depth of an operand. -/
theorem CellAt.split {a b c : TRes K} (hc : ResUT.CompS a b c) {y : BoCa.Loc} {ψ : TCell K}
    (h : CellAt c y ψ) (hk : ψ.kind ≠ Kind.imm) : CellAt a y ψ ∨ CellAt b y ψ := by
  cases h with
  | top e =>
      rcases ResUT.Comp.get hc y with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, -, -, f, hC⟩
      · rw [e] at f; cases f
      · rw [e] at f; cases Option.some.inj f; exact Or.inl (.top f₁)
      · rw [e] at f; cases Option.some.inj f; exact Or.inr (.top f₂)
      · rw [e] at f; cases Option.some.inj f; exact absurd (CellUT.CompS.kind_imm hC) hk
  | nest e h' =>
      rcases compS_back hc e with ⟨ψ₀, e₀, -, w₀⟩ | ⟨ψ₀, e₀, -, w₀⟩
      · exact Or.inl (.nest e₀ (w₀ ▸ h'))
      · exact Or.inr (.nest e₀ (w₀ ▸ h'))

theorem CellAt.single_inv {l y : BoCa.Loc} {φ ψ : TCell K} (h : CellAt (ResUT.single l φ) y ψ) :
    (y = l ∧ ψ = φ) ∨ CellAt φ.wit y ψ := by
  cases h with
  | top e => obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e; exact Or.inl ⟨rfl, rfl⟩
  | nest e h' => obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e; exact Or.inr h'

theorem CellAt.single_own {l y : BoCa.Loc} {v : BoCa.Val} {ψ : TCell K}
    (h : CellAt (ResUT.single l (CellUT.ownOf v)) y ψ) : ψ = CellUT.ownOf v := by
  rcases h.single_inv with ⟨-, rfl⟩ | h'
  · rfl
  · rw [CellUT.wit_ownOf] at h'; exact absurd h' CellAt.not_empty

/-! ### What `✓` refuses -/

/-- A cell at `ℓ` at any depth of `ρ` shows at `ℓ` in `ex(ρ)` or in `ag(ρ)` (`ownAt_walk_dom` at
every kind). -/
theorem cellAt_walk_dom {ρ : TRes K} {x : BoCa.Loc} {ψ : TCell K} (h : CellAt ρ x ψ) :
    ∀ {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop},
      (∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) → ResUT.CompLaws C →
      ∀ {e a : TRes K}, ExWT R C ρ e → AgWT ρ a →
      (∃ ζ, e.get x = some ζ) ∨ (∃ ζ, a.get x = some ζ) := by
  induction h with
  | @top ρ l ψ e =>
      intro R C hR hC ex a hex ha
      cases hkk : ψ.kind with
      | imm =>
          obtain ⟨χ, hχ, -⟩ := AgWT.get_imm ha e hkk
          exact Or.inr ⟨χ, hχ⟩
      | own =>
          cases hex with
          | mk hs hw hb hnm hσ =>
              obtain ⟨ζ₁, e₁⟩ := comp_some hnm (ResUT.restrict_get_some e hkk)
              exact Or.inl (comp_some hσ e₁)
      | «mut» =>
          cases hex with
          | mk hs hw hb hnm hσ =>
              obtain ⟨ζ₁, e₁⟩ := comp_some_r hnm (ResUT.restrict_get_some e hkk)
              exact Or.inl (comp_some hσ e₁)
  | @nest ρ m l χ ψ e hmw ih =>
      intro R C hR hC ex a hex ha
      cases hkk : χ.kind with
      | own =>
          rcases CellUT.rep' χ with ⟨u, rfl⟩ | ⟨s, v, χ', hs, rfl⟩ | ⟨b, _, v, χ', hb, P, hw, rfl⟩
          · rw [CellUT.wit_ownOf] at hmw; exact absurd hmw CellAt.not_empty
          · simp [CellUT.kind, CellUT.immOf] at hkk
          · simp [CellUT.kind, CellUT.mutOf] at hkk
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

/-- **A top-level `ℓ ↦ own(u)` of a valid resource is the only cell at `ℓ` at any depth**
(`not_ownUnder_top_own` at every kind). -/
theorem cellAt_top_own {W : TRes K} (hv : ResUT.Valid W) {x : BoCa.Loc} {u : BoCa.Val}
    (hx : W.get x = some (CellUT.ownOf u)) {ψ : TCell K} (h : CellAt W x ψ) :
    ψ = CellUT.ownOf u := by
  cases h with
  | top e => rw [hx] at e; exact (Option.some.inj e).symm
  | @nest _ m _ χ _ e hmw =>
  exfalso
  obtain ⟨σ, eW, aW, heW, haW, hc⟩ := hv
  have eo : eW.get x = some (CellUT.ownOf u) := ExST.get_of_ne_imm heW hx (by simp)
  have noAg : ∀ ζ, aW.get x = some ζ → False := fun ζ hζ =>
    ex_ag_disjoint ⟨σ, eW, aW, heW, haW, hc⟩ heW haW eo hζ
  cases hkk : χ.kind with
  | own =>
      rcases CellUT.rep' χ with ⟨u', rfl⟩ | ⟨s, v, χ', hs, rfl⟩ | ⟨b, _, v, χ', hb, P, hw, rfl⟩
      · rw [CellUT.wit_ownOf] at hmw; exact CellAt.not_empty hmw
      · simp [CellUT.kind, CellUT.immOf] at hkk
      · simp [CellUT.kind, CellUT.mutOf] at hkk
  | imm =>
      obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgWT.imm_wit_le haW e hkk
      rcases cellAt_walk_dom hmw hRR ResUT.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
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
          obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨χ, e, hkk⟩)
          obtain ⟨ψ', hψ', hex'⟩ := ExWitsT.mem hw q hq
          rw [hq₁, e] at hψ'
          cases Option.some.inj hψ'
          rcases cellAt_walk_dom hmw hSS ResUT.compLawsS hex' hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
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

/-! ### One `mut` cell per location -/

/-- **Two `mut` cells at one location, at any depth of `W`, are one cell.**

**Departure (D3, `docs/new-core/scope-781.md` §8).** The printed carrier has no such condition.
It makes a flattened `mut` cell a stored one (`flat_mut_cellAt`); without it, clause 3 of `○` on
two covered cells is not covered (`clause3_not_cov`, which is on the printed chain as well,
`clause3_chain`). It is an invariant of `TWNT` (`TWNT.mutOne`), not a premise. The printed
technique not built: reasoning about clause 3's `P̂ ∧ Q̂` composite. -/
def MutOne (W : TRes K) : Prop :=
  ∀ y (ψ₁ ψ₂ : TCell K), CellAt W y ψ₁ → CellAt W y ψ₂ → ψ₁.kind = Kind.mut →
    ψ₂.kind = Kind.mut → ψ₁ = ψ₂

theorem MutOne.of_back {W W' : TRes K} (h : MutOne W)
    (hb : ∀ y ψ, CellAt W' y ψ → ψ.kind = Kind.mut → CellAt W y ψ) : MutOne W' :=
  fun y ψ₁ ψ₂ h₁ h₂ k₁ k₂ => h y ψ₁ ψ₂ (hb y ψ₁ h₁ k₁) (hb y ψ₂ h₂ k₂) k₁ k₂

theorem kind_mut_ne_imm {ψ : TCell K} (hk : ψ.kind = Kind.mut) : ψ.kind ≠ Kind.imm := by
  rw [hk]; simp

/-- A non-`imm` cell at depth of a reborrow image sits at depth of the source: the image's
cells are `imm`, over a piece of the source or a source cell's witness (`reb_cell`). -/
theorem cellAt_image {β : Life} {σ c : TRes K} (hr : ResUT.Reb β σ c) {y : BoCa.Loc}
    {ψ : TCell K} (h : CellAt c y ψ) (hk : ψ.kind ≠ Kind.imm) : CellAt σ y ψ := by
  cases h with
  | top e => exact absurd (reb_cell hr e).1 hk
  | nest e h' =>
      obtain ⟨-, hcase⟩ := reb_cell hr e
      rcases hcase with ⟨u, q, hq, -, rfl, hqσ, -⟩ | ⟨ζ, eζ, -, wζ⟩ | ⟨ζ, eζ, -, wζ⟩
      · rw [CellUT.wit_immOf] at h'
        exact h'.of_del.of_le hqσ hk
      · exact .nest eζ (wζ ▸ h')
      · exact .nest eζ (wζ ▸ h')

/-- The cells at depth of a re-read resource are the re-readings of cells at depth. -/
theorem CellAt.rr_back {Θ : LocTy} {K' : WCactus} {ρ' : TRes K'} {y : BoCa.Loc}
    {ψ' : TCell K'} (h : CellAt ρ' y ψ') :
    ∀ {ρ : TRes K}, RR Θ ρ ρ' → ∃ ψ, CellAt ρ y ψ ∧ RC Θ y ψ ψ' := by
  induction h with
  | top e =>
      intro ρ hr
      obtain ⟨ψ, e', hc⟩ := hr.get_some' e
      exact ⟨ψ, .top e', hc⟩
  | nest e _ ih =>
      intro ρ hr
      obtain ⟨χ, e', hc⟩ := hr.get_some' e
      obtain ⟨ψ, hψ, hcψ⟩ := ih hc.wit
      exact ⟨ψ, .nest e' hψ, hcψ⟩

/-- **`MutOne` is an invariant of `TWNT`.** Departure D3 (see `MutOne`). -/
theorem TWNT.mutOne {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {ps rs : List (FrameRecT K)}
    (h : TWNT K Θ tc W ps rs) : MutOne W := by
  induction h with
  | empty => intro y ψ₁ _ h₁; exact absurd h₁ CellAt.not_empty
  | alloc _ _ _ hW _ ih =>
      refine ih.of_back fun y ψ hψ hk => ?_
      rcases hψ.split hW (kind_mut_ne_imm hk) with h | h
      · exact h
      · rw [h.single_own] at hk; simp at hk
  | immFrame T hα _ hX hW _ hW' _ _ ih =>
      refine ih.of_back fun y ψ hψ hk => ?_
      rcases hψ.split hW' (kind_mut_ne_imm hk) with h | h
      · rcases h.single_inv with ⟨-, rfl⟩ | h
        · simp [CellUT.kind, CellUT.immOf] at hk
        · rw [CellUT.wit_immOf] at h
          exact (h.of_compS_right hX (kind_mut_ne_imm hk)).of_compS_left hW (kind_mut_ne_imm hk)
      · exact h.of_compS_right hW (kind_mut_ne_imm hk)
  | reb r _ _ hle hreb _ _ _ hW _ ih =>
      refine ih.of_back fun y ψ hψ hk => ?_
      rcases hψ.split hW (kind_mut_ne_imm hk) with h | h
      · exact h
      · exact .nest hle (by rw [CellUT.wit_immOf]; exact cellAt_image hreb h (kind_mut_ne_imm hk))
  | rebDeep r _ _ _ hcell hreb _ _ _ _ hW _ ih =>
      refine ih.of_back fun y ψ hψ hk => ?_
      rcases hψ.split hW (kind_mut_ne_imm hk) with h | h
      · exact h
      · exact .nest hcell
          (by rw [CellUT.wit_immOf]; exact cellAt_image hreb h (kind_mut_ne_imm hk))
  | @mutFold K Θ tc W X Z ρ W' ps rs l v b _ hstr P hw _ hX hW hW' hv ih =>
      have hl : W.get l = some (CellUT.ownOf v) :=
        (ResUT.CompS.get_left_of_ne_imm hW
          (ResUT.CompS.get_left_of_ne_imm hX (ResUT.single_get_self _ _) (by simp)).2
          (by simp)).2
      have hvW : ResUT.Valid W := by
        rename_i hT
        exact hT.valid
      -- each `mut` cell at depth of `W′` is the new cell at `ℓ` or one at depth of `W`
      have back : ∀ y ψ, CellAt W' y ψ → ψ.kind = Kind.mut →
          (y = l ∧ ψ = CellUT.mutOf b v ρ hstr P hw) ∨ CellAt W y ψ := by
        intro y ψ hψ hk
        rcases hψ.split hW' (kind_mut_ne_imm hk) with h | h
        · rcases h.single_inv with h | h
          · exact Or.inl h
          · rw [CellUT.wit_mutOf] at h
            exact Or.inr ((h.of_compS_right hX (kind_mut_ne_imm hk)).of_compS_left hW
              (kind_mut_ne_imm hk))
        · exact Or.inr (h.of_compS_right hW (kind_mut_ne_imm hk))
      intro y ψ₁ ψ₂ h₁ h₂ k₁ k₂
      rcases back y ψ₁ h₁ k₁ with ⟨hy₁, rfl⟩ | b₁ <;> rcases back y ψ₂ h₂ k₂ with ⟨hy₂, rfl⟩ | b₂
      · rfl
      · subst hy₁; rw [cellAt_top_own hvW hl b₂] at k₂; simp at k₂
      · subst hy₂; rw [cellAt_top_own hvW hl b₁] at k₁; simp at k₁
      · exact ih y ψ₁ ψ₂ b₁ b₂ k₁ k₂
  | mutUnfold _ hW hX hW' _ ih =>
      refine ih.of_back fun y ψ hψ hk => ?_
      rcases hψ.split hW' (kind_mut_ne_imm hk) with h | h
      · rcases h.split hX (kind_mut_ne_imm hk) with h | h
        · rw [h.single_own] at hk; simp at hk
        · refine CellAt.of_compS_left hW (.nest (ResUT.single_get_self _ _) ?_)
            (kind_mut_ne_imm hk)
          rw [CellUT.wit_mutOf]; exact h
      · exact h.of_compS_right hW (kind_mut_ne_imm hk)
  | free _ hW _ ih =>
      exact ih.of_back fun y ψ hψ hk => hψ.of_compS_right hW (kind_mut_ne_imm hk)
  | store _ hW hW' _ ih =>
      refine ih.of_back fun y ψ hψ hk => ?_
      rcases hψ.split hW' (kind_mut_ne_imm hk) with h | h
      · rw [h.single_own] at hk; simp at hk
      · exact h.of_compS_right hW (kind_mut_ne_imm hk)
  | immEnd r _ _ hc hX' hW' _ _ _ ih =>
      refine ih.of_back fun y ψ hψ hk => ?_
      rcases hψ.split hW' (kind_mut_ne_imm hk) with h | h
      · rcases h.split hX' (kind_mut_ne_imm hk) with h | h
        · rw [h.single_own] at hk; simp at hk
        · refine CellAt.of_compS_left hc (.nest (ResUT.single_get_self _ _) ?_)
            (kind_mut_ne_imm hk)
          rw [CellUT.wit_immOf]; exact h
      · exact h.of_compS_right hc (kind_mut_ne_imm hk)
  | rebEnd _ _ _ _ _ hW _ ih =>
      exact ih.of_back fun y ψ hψ hk => hψ.of_compS_left hW (kind_mut_ne_imm hk)
  | rebEndDeep _ _ _ _ _ _ hW _ ih =>
      exact ih.of_back fun y ψ hψ hk => hψ.of_compS_left hW (kind_mut_ne_imm hk)
  | reread _ _ _ hr _ _ _ ih =>
      intro y ψ₁' ψ₂' h₁ h₂ k₁ k₂
      obtain ⟨ψ₁, c₁, r₁⟩ := h₁.rr_back hr
      obtain ⟨ψ₂, c₂, r₂⟩ := h₂.rr_back hr
      obtain rfl := ih y ψ₁ ψ₂ c₁ c₂ (r₁.kind ▸ k₁) (r₂.kind ▸ k₂)
      exact RC.func r₁ r₂

/-! ### Re-reading is injective on cells at depth -/

/-- **Re-reading is injective on cells at depth of a `MutOne` world**: `own` cells re-read to
themselves, an `imm` cell keeps its lifetime set and value and its witness is re-read cell by
cell, and two `mut` cells at one location at depth are one cell. -/
theorem RC.inj_of {Θ : LocTy} {K' : WCactus} {W : TRes K} (hM : MutOne W) {l : BoCa.Loc}
    {ψ₁ : TCell K} {ψ' : TCell K'} (h₁ : RC Θ l ψ₁ ψ') :
    ∀ {ψ₂ : TCell K}, RC Θ l ψ₂ ψ' → CellAt W l ψ₁ → CellAt W l ψ₂ → ψ₁ = ψ₂ := by
  induction h₁ with
  | own l v => intro ψ₂ h₂ _ _; cases h₂; rfl
  | imm l i i' hs hv hdom hw ih =>
      intro ψ₂ h₂ c₁ c₂
      cases h₂ with
      | imm _ j _ hs' hv' hdom' hw' =>
          refine congrArg CellUT.imm (ImmT.eq_of (hs.symm.trans hs') (hv.symm.trans hv') ?_)
          refine PMap.ext fun k => ?_
          cases e₁ : i.res.get k with
          | none =>
              have := (hdom k).mp e₁
              rw [← hdom' k] at this
              rw [this]
          | some φ₁ =>
              cases e₂ : j.res.get k with
              | none =>
                  have := (hdom' k).mp e₂
                  rw [← hdom k, e₁] at this; cases this
              | some φ₂ =>
                  cases e' : i'.res.get k with
                  | none => rw [← hdom k, e₁] at e'; cases e'
                  | some a =>
                      rw [ih k φ₁ a e₁ e' (hw' k φ₂ a e₂ e') (c₁.wit_trans e₁)
                        (c₂.wit_trans e₂)]
  | «mut» l m m' τ hΘ hs hv hdom hw hP ih =>
      intro ψ₂ h₂ c₁ c₂
      cases h₂ with
      | «mut» _ n _ τ' hΘ' hs' hv' hdom' hw' hP' => exact hM l _ _ c₁ c₂ rfl rfl

/-- Two resources whose cells sit at depth of a `MutOne` world and re-read to one resource are
one resource. -/
theorem RR.inj_of {Θ : LocTy} {K' : WCactus} {W : TRes K} (hM : MutOne W) {ρ₁ ρ₂ : TRes K}
    {ρ' : TRes K'} (h₁ : RR Θ ρ₁ ρ') (h₂ : RR Θ ρ₂ ρ')
    (c₁ : ∀ y ψ, ρ₁.get y = some ψ → CellAt W y ψ)
    (c₂ : ∀ y ψ, ρ₂.get y = some ψ → CellAt W y ψ) : ρ₁ = ρ₂ := by
  refine PMap.ext fun k => ?_
  cases e₁ : ρ₁.get k with
  | none =>
      have := (h₁.1 k).mp e₁
      rw [← h₂.1 k] at this
      rw [this]
  | some φ₁ =>
      obtain ⟨a, ea, ra⟩ := h₁.get_some e₁
      obtain ⟨φ₂, e₂, r₂⟩ := h₂.get_some' ea
      rw [e₂, RC.inj_of hM ra r₂ (c₁ k φ₁ e₁) (c₂ k φ₂ e₂)]

/-! ### The aliasable walk reads witnesses at depth -/

/-- A non-`own` cell of `ex(ρ)_○` carries the witness of a cell at depth of `ρ`. -/
theorem exRT_cellAt {ρ σ : TRes K} (h : ExRT ρ σ) :
    ∀ x (ψ : TCell K), σ.get x = some ψ → ψ.kind ≠ Kind.own →
      ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.wit = ψ.wit := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : TCell K), σ.get x = some ψ →
      ψ.kind ≠ Kind.own → ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.wit = ψ.wit)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ x (ψ : TCell K), q.2.get x = some ψ →
      ψ.kind ≠ Kind.own → ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.wit = ψ.wit) ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs hw hb hnm hσ ih x ψ e hk
    rcases back_view hσ e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
    · rcases back_view hnm e₁ k₁ with ⟨ψ₂, e₂, k₂, w₂⟩ | ⟨ψ₂, e₂, -, w₂⟩
      · exact absurd (ResUT.restrict_eq_some.mp e₂).2 k₂
      · exact ⟨ψ₂, .top (ResUT.restrict_eq_some.mp e₂).1, (w₁.trans w₂).symm⟩
    · obtain ⟨τ, hτ, ψ', e', k', w'⟩ := bigComp_back hb e₁ k₁
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
      obtain ⟨ψ₀, c₀, w₀⟩ := ih q hq x ψ' e' k'
      exact ⟨ψ₀, c₀, w₀.trans (w₁.trans w').symm⟩
  case nil => intro ρ' q hq; exact absurd hq (by simp)
  case cons =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro x φ ex kx
      obtain ⟨ψ₀, c₀, w₀⟩ := ihe x φ ex kx
      exact ⟨ψ₀, .nest hψ c₀, w₀⟩
    · exact ihw q hq'

/-- **A non-`own` cell of `ag(ρ)` carries the witness of a cell at depth of `ρ`.** -/
theorem agW_cellAt {ρ σ : TRes K} (h : AgWT ρ σ) :
    ∀ x (ψ : TCell K), σ.get x = some ψ → ψ.kind ≠ Kind.own →
      ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.wit = ψ.wit := by
  refine G.AgW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : TCell K), σ.get x = some ψ →
      ψ.kind ≠ Kind.own → ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.wit = ψ.wit)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ x (ψ : TCell K), q.2.get x = some ψ →
      ψ.kind ≠ Kind.own → ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.wit = ψ.wit)
    (motive_3 := fun ρ w _ => ∀ q ∈ w, ∀ x (ψ : TCell K), q.2.get x = some ψ →
      ψ.kind ≠ Kind.own → ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.wit = ψ.wit)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi x ψ e hk
    rcases back_view hσ e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
    · rcases back_view ha e₁ k₁ with ⟨ψ₂, e₂, -, w₂⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
      · exact ⟨ψ₂, .top (ResUT.restrict_eq_some.mp e₂).1, (w₁.trans w₂).symm⟩
      · obtain ⟨τ, hτ, ψ', e', k', w'⟩ := bigComp_back hbm e₂ k₂
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
        obtain ⟨ψ₀, c₀, w₀⟩ := ihm q hq x ψ' e' k'
        exact ⟨ψ₀, c₀, w₀.trans (w₁.trans (w₂.trans w')).symm⟩
    · obtain ⟨τ, hτ, ψ', e', k', w'⟩ := bigComp_back hbi e₁ k₁
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
      obtain ⟨ψ₀, c₀, w₀⟩ := ihi q hq x ψ' e' k'
      exact ⟨ψ₀, c₀, w₀.trans (w₁.trans w').symm⟩
  case nilM => intro ρ' q hq; exact absurd hq (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro x φ ex kx
      obtain ⟨ψ₀, c₀, w₀⟩ := ihe x φ ex kx
      exact ⟨ψ₀, .nest hψ c₀, w₀⟩
    · exact ihw q hq'
  case nilI => intro ρ' q hq; exact absurd hq (by simp)
  case consI =>
    intro ρ' pe l w ψ hψ hk e a hex hag hc hw iha ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro x φ ex kx
      rcases back_view hc ex kx with ⟨φ₁, e₁, k₁, w₁⟩ | ⟨φ₁, e₁, k₁, w₁⟩
      · obtain ⟨ψ₀, c₀, w₀⟩ := exRT_cellAt hex x φ₁ e₁ k₁
        exact ⟨ψ₀, .nest hψ c₀, w₀.trans w₁.symm⟩
      · obtain ⟨ψ₀, c₀, w₀⟩ := iha x φ₁ e₁ k₁
        exact ⟨ψ₀, .nest hψ c₀, w₀.trans w₁.symm⟩
    · exact ihw q hq'

/-! ### The used arguments sit at depth -/

/-- The cells of a lineage member's escrow sit at depth of `W` when the root's do. -/
theorem LinPathT.cellAt {W : TRes K} {r d : FrameRecT K} {p : List BoCa.Loc}
    (h : LinPathT r p d) (hr : ∀ y ψ, r.R.get y = some ψ → CellAt W y ψ) :
    ∀ y ψ, d.R.get y = some ψ → CellAt W y ψ := by
  induction h with
  | nil => exact hr
  | cons hs _ ih =>
      obtain ⟨-, ζ, eζ, -, -, wζ⟩ := hs
      exact ih fun y ψ e => (hr _ ζ eζ).wit_trans (by rw [wζ]; exact e)

end BoCa.Fig16.Tree.Wp

end
