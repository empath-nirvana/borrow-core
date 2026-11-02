import DtorUnwind.Tree.FdTree

/-!
# The join's frame condition at every type

`joinFd (loc ℓ) ρ_rest` (`SI/CaptureScope.lean`): the flattening of the resumer's other
resources holds nothing at the location `ℓ = p.le` of a record `p` the resumed task owns.
`fdFromBranch_views` (`Tree/FdTree.lean`) supplies its `imm` half from the cactus invariant.
This file supplies the rest, cell kind by cell kind of the flattening `⦇ρ_rest⦈ = ex ● ag`.

* **`own`/`mut` in `ex(ρ_rest)_●`** (`fd_ex_none`): `ex(W)_●` would carry it at `ℓ`, while
  every `ag(W)` carries an `imm` cell there (`LeInv`, `p` a record proper), and `⦇W⦈` is defined
  (`✓W`): `●` joins `imm` cells only.
* **`mut` in `ag(ρ_rest)`** (`fd_ag_not_mut`): `ag` raises a `mut` cell only from one at some
  depth of `ρ_rest` (`agW_mut`), so `MutAt W ℓ`, which `NoMut` refuses at a record's location.
* **`own` in `ag(ρ_rest)`**: `ag` raises an `own` cell only from one beneath a borrow of
  `ρ_rest` (`agW_own`, `OwnUnder`), hence of `W`. That no `own` cell of a lent location sits
  beneath a borrow of the world is the hypothesis `hown` here; it is an invariant of `TWNC`
  (`TWNC.noOwnUnder`, `Tree/NoOwnUnder.lean`).

`joinFd_of_branch_of_noOwn`: `joinFd` at every type of the resumer's other resources, from
`fdFromBranch_views`'s hypotheses, `p ∈ ps`, and `hown`. No type of `ρ_rest` is read.
`Tree/NoOwnUnder.lean`'s `joinFd_of_branch` discharges `hown`.
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

/-! ### `own` cells at depth -/

/-- `OwnAt ρ ℓ`: an `own` cell at `ℓ` sits in `ρ`, at the top or inside the witness of a
non-`own` cell (`MutAt` at `own`). -/
inductive OwnAt : WRes → Loc → Prop
  | top {ρ : WRes} {l : Loc} {ψ : CellU Loc Val} :
      ρ.get l = some ψ → ψ.kind = Kind.own → OwnAt ρ l
  | nest {ρ : WRes} {l m : Loc} {ψ : CellU Loc Val} :
      ρ.get m = some ψ → ψ.kind ≠ Kind.own → OwnAt ψ.wit l → OwnAt ρ l

/-- An `own` cell at `ℓ` beneath a borrow of `ρ`. -/
def OwnUnder (ρ : WRes) (l : Loc) : Prop :=
  ∃ m, ∃ ψ : CellU Loc Val, ρ.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ OwnAt ψ.wit l

theorem OwnUnder.of_compS_left {a b c : WRes} (h : ResU.CompS a b c) {l : Loc}
    (ho : OwnUnder a l) : OwnUnder c l := by
  obtain ⟨m, ψ, e, hk, hw⟩ := ho
  obtain ⟨ζ, eζ, kζ, wζ, -⟩ := compS_get_left' h e
  exact ⟨m, ζ, eζ, kζ ▸ hk, wζ ▸ hw⟩

theorem OwnUnder.of_compS_right {a b c : WRes} (h : ResU.CompS a b c) {l : Loc}
    (ho : OwnUnder b l) : OwnUnder c l := OwnUnder.of_compS_left (ResU.CompS.comm h) ho

theorem compR_own_src : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ →
    ψ.kind = Kind.own → ψ₁.kind = Kind.own ∨ ψ₂.kind = Kind.own := by
  intro ψ₁ ψ₂ ψ h hk
  cases h with
  | same => exact Or.inl hk
  | strict k =>
      rw [CellU.CompS.kind (CellU.compS_spec _ _ k)] at hk; cases hk
  | mutMut => simp at hk
  | mutOwn => simp at hk
  | ownMut => simp at hk
  | immOwn => simp at hk
  | ownImm => simp at hk
  | immMut => simp at hk
  | mutImm => simp at hk

theorem compS_own_src : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompS ψ₁ ψ₂ ψ →
    ψ.kind = Kind.own → ψ₁.kind = Kind.own ∨ ψ₂.kind = Kind.own := by
  intro ψ₁ ψ₂ ψ h hk
  rw [CellU.CompS.kind h] at hk; cases hk

theorem comp_own_src {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind = Kind.own → ψ₁.kind = Kind.own ∨ ψ₂.kind = Kind.own)
    {a b c : WRes} (h : ResU.Comp R C a b c) {x : Loc} {ψ : CellU Loc Val}
    (e : c.get x = some ψ) (hk : ψ.kind = Kind.own) :
    (∃ ψ₁ : CellU Loc Val, a.get x = some ψ₁ ∧ ψ₁.kind = Kind.own) ∨
    (∃ ψ₂ : CellU Loc Val, b.get x = some ψ₂ ∧ ψ₂.kind = Kind.own) := by
  rcases ResU.Comp.get h x with ⟨-, -, e'⟩ | ⟨χ, e₁, -, e'⟩ | ⟨χ, -, e₂, e'⟩ |
      ⟨χ₁, χ₂, χ, e₁, e₂, e', hCc⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, hk⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, hk⟩
  · rw [e'] at e; cases e
    rcases hC _ _ _ hCc hk with k | k
    · exact Or.inl ⟨_, e₁, k⟩
    · exact Or.inr ⟨_, e₂, k⟩

theorem bigComp_own_src {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind = Kind.own → ψ₁.kind = Kind.own ∨ ψ₂.kind = Kind.own) :
    ∀ {L : List WRes} {b : WRes}, BigComp R C L b → ∀ {x : Loc} {ψ : CellU Loc Val},
      b.get x = some ψ → ψ.kind = Kind.own →
      ∃ σ ∈ L, ∃ ψ' : CellU Loc Val, σ.get x = some ψ' ∧ ψ'.kind = Kind.own
  | [], b, h, x, ψ, e, _ => by cases h; rw [PMap.empty_get] at e; cases e
  | σ :: L, b, h, x, ψ, e, hk => by
      cases h with
      | cons hrest hc =>
          rcases comp_own_src hC hc e hk with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₂, e₂, k₂⟩
          · exact ⟨σ, List.mem_cons_self, ψ₁, e₁, k₁⟩
          · obtain ⟨τ, hτ, ψ', e', k'⟩ := bigComp_own_src hC hrest e₂ k₂
            exact ⟨τ, List.mem_cons_of_mem _ hτ, ψ', e', k'⟩

/-- `ex(ρ)` raises an `own` cell only from one in `ρ`. -/
theorem exW_own {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind = Kind.own → ψ₁.kind = Kind.own ∨ ψ₂.kind = Kind.own)
    {ρ σ : WRes} (h : ExW R C ρ σ) :
    ∀ x (ψ : CellU Loc Val), σ.get x = some ψ → ψ.kind = Kind.own → OwnAt ρ x := by
  refine ExW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : CellU Loc Val), σ.get x = some ψ →
      ψ.kind = Kind.own → OwnAt ρ x)
    (motive_2 := fun ρ w _ => ∀ p ∈ w, ∀ x (ψ : CellU Loc Val), p.2.get x = some ψ →
      ψ.kind = Kind.own → OwnAt ρ x) ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs hw hb hnm hσ ih x ψ e hk
    rcases comp_own_src hC hσ e hk with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₂, e₂, k₂⟩
    · rcases comp_own_src hC hnm e₁ k₁ with ⟨ψ₃, e₃, k₃⟩ | ⟨ψ₃, e₃, k₃⟩
      · exact OwnAt.top (ResU.restrict_eq_some.mp e₃).1 k₃
      · have := (ResU.restrict_eq_some.mp e₃).2; rw [k₃] at this; cases this
    · obtain ⟨τ, hτ, ψ', e', k'⟩ := bigComp_own_src hC hb e₂ k₂
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hτ
      exact ih p hp x ψ' e' k'
  case nil => intro ρ' p hp; exact absurd hp (by simp)
  case cons =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw p hp x ψ' e' k'
    rcases List.mem_cons.mp hp with rfl | hp
    · exact OwnAt.nest hψ (by rw [hk]; simp) (ihe x ψ' e' k')
    · exact ihw p hp x ψ' e' k'

/-- `ag(ρ)` raises an `own` cell only from one beneath a borrow of `ρ`. -/
theorem agW_own {ρ σ : WRes} (h : AgW ρ σ) :
    ∀ x (ψ : CellU Loc Val), σ.get x = some ψ → ψ.kind = Kind.own → OwnUnder ρ x := by
  refine AgW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : CellU Loc Val), σ.get x = some ψ →
      ψ.kind = Kind.own → OwnUnder ρ x)
    (motive_2 := fun ρ w _ => ∀ p ∈ w, ∀ x (ψ : CellU Loc Val), p.2.get x = some ψ →
      ψ.kind = Kind.own → OwnUnder ρ x)
    (motive_3 := fun ρ w _ => ∀ p ∈ w, ∀ x (ψ : CellU Loc Val), p.2.get x = some ψ →
      ψ.kind = Kind.own → OwnUnder ρ x)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi x ψ e hk
    rcases comp_own_src compR_own_src hσ e hk with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₂, e₂, k₂⟩
    · rcases comp_own_src compR_own_src ha e₁ k₁ with ⟨ψ₃, e₃, k₃⟩ | ⟨ψ₃, e₃, k₃⟩
      · have := (ResU.restrict_eq_some.mp e₃).2; rw [k₃] at this; cases this
      · obtain ⟨τ, hτ, ψ', e', k'⟩ := bigComp_own_src compR_own_src hbm e₃ k₃
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hτ
        exact ihm p hp x ψ' e' k'
    · obtain ⟨τ, hτ, ψ', e', k'⟩ := bigComp_own_src compR_own_src hbi e₂ k₂
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hτ
      exact ihi p hp x ψ' e' k'
  case nilM => intro ρ' p hp; exact absurd hp (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw p hp x ψ' e' k'
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨m, ζ, eζ, kζ, hζ⟩ := ihe x ψ' e' k'
      exact ⟨l, ψ, hψ, by simp [hk], OwnAt.nest eζ kζ hζ⟩
    · exact ihw p hp x ψ' e' k'
  case nilI => intro ρ' p hp; exact absurd hp (by simp)
  case consI =>
    intro ρ' q l w ψ hψ hk e a hex hag hc hw iha ihw p hp x ψ' e' k'
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨l, ψ, hψ, by simp [hk], ?_⟩
      rcases comp_own_src compR_own_src hc e' k' with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₁, e₁, k₁⟩
      · exact exW_own compR_own_src hex x ψ₁ e₁ k₁
      · obtain ⟨m, ζ, eζ, kζ, hζ⟩ := iha x ψ₁ e₁ k₁
        exact OwnAt.nest eζ kζ hζ
    · exact ihw p hp x ψ' e' k'

/-! ### The three halves -/

/-- A non-`imm` cell of a flattening is a cell of `ex` or of `ag`. -/
theorem flat_nonimm_src {e a τ : WRes} (hc : ResU.CompS e a τ) {l : Loc}
    {χ : CellU Loc Val} (hχ : τ.get l = some χ) (hk : χ.kind ≠ Kind.imm) :
    e.get l = some χ ∨ a.get l = some χ := by
  rcases ResU.Comp.get hc l with ⟨-, -, f⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, -, -, f, hC⟩
  · rw [hχ] at f; cases f
  · rw [hχ] at f; cases Option.some.inj f; exact Or.inl f₁
  · rw [hχ] at f; cases Option.some.inj f; exact Or.inr f₂
  · rw [hχ] at f; cases Option.some.inj f
    exact absurd (CellU.CompS.kind hC) hk

/-- **`ex(ρ_rest)_●` holds nothing at a record's location**: every `ag(W)` holds an `imm` cell
there (`LeInv`), and `⦇W⦈ = ex(W)_● ● ag(W)` is defined. -/
theorem fd_ex_none {W ρf ρS ρk ρrest er : WRes} {ps rs : List FrameRec} {p : FrameRec}
    (hT : TWNC W ps rs) (hp : p ∈ ps) (hW : ResU.CompS ρf ρS W)
    (hS : ResU.CompS ρk ρrest ρS) (her : ExS ρrest er) : er.get p.le = none := by
  cases e : er.get p.le with
  | none => rfl
  | some χ =>
      exfalso
      have hk : χ.kind ≠ Kind.imm := ExS.immFree her _ _ e
      obtain ⟨σW, eW, aW, heW, haW, hcW⟩ := hT.valid
      obtain ⟨e₁, eS, -, heS, hc1⟩ := (ExS.split hW).mp heW
      obtain ⟨ek, er', -, her', hc2⟩ := (ExS.split hS).mp heS
      obtain rfl := ExS.functional her' her
      have hS' : eS.get p.le = some χ :=
        (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc2) e hk).2
      have hW' : eW.get p.le = some χ :=
        (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc1) hS' hk).2
      obtain ⟨ψ, hψ, hψk, -, -⟩ := hT.inv.2.1 p hp aW haW
      exact hk (CellU.CompatS.kind_left (hcW.1 p.le χ ψ hW' hψ))

/-- **`ag(ρ_rest)` holds no `mut` cell at a record's location**: `NoMut`. -/
theorem fd_ag_not_mut {W ρf ρS ρk ρrest ar : WRes} {ps rs : List FrameRec} {p : FrameRec}
    (hT : TWNC W ps rs) (hp : p ∈ ps) (hW : ResU.CompS ρf ρS W)
    (hS : ResU.CompS ρk ρrest ρS) (har : AgW ρrest ar) {χ : CellU Loc Val}
    (hχ : ar.get p.le = some χ) : χ.kind ≠ Kind.mut := fun hk =>
  hT.inv.2.2.2.2.2.1.1 p hp
    (MutAt.of_compS_right hW (MutAt.of_compS_right hS (agW_mut har _ χ hχ hk)))

/-- **`ag(ρ_rest)` holds an `own` cell at `ℓ` only beneath a borrow of the world.** -/
theorem fd_ag_own {W ρf ρS ρk ρrest ar : WRes} {l : Loc} (hW : ResU.CompS ρf ρS W)
    (hS : ResU.CompS ρk ρrest ρS) (har : AgW ρrest ar) {χ : CellU Loc Val}
    (hχ : ar.get l = some χ) (hk : χ.kind = Kind.own) : OwnUnder W l :=
  OwnUnder.of_compS_right hW (OwnUnder.of_compS_right hS (agW_own har _ χ hχ hk))

/-- **The join's frame condition at every type.** With `fdFromBranch_views`'s hypotheses, the
record `p` proper, and no `own` cell of `p`'s location beneath a borrow of the world (`hown`),
the resumer's other resources hold nothing at `p`'s location at any depth. -/
theorem joinFd_of_branch_of_noOwn (K : Cactus) {W ρf ρS ρk ρrest : WRes} {ps rs : List FrameRec}
    {p : FrameRec} {α n : Life} (hT : TWNC W ps rs) (hp : p ∈ ps)
    (hW : ResU.CompS ρf ρS W) (hS : ResU.CompS ρk ρrest ρS) (hFLp : FrameLife W p α)
    (hbr : ∀ τ, ResU.Flat ρrest τ → OnBranchRes K n τ) (hnα : ¬ K.le n α)
    (hown : ¬ OwnUnder W p.le) :
    joinFd (Val.loc p.le) ρrest := by
  refine ⟨p.le, rfl, fun τ hτ => ?_⟩
  cases hg : τ.get p.le with
  | none => rfl
  | some χ =>
      exfalso
      have himm := fdFromBranch_views K hT hW hS hFLp hbr hnα τ hτ χ hg
      obtain ⟨er, ar, her, har, hcr⟩ := hτ
      rcases flat_nonimm_src hcr hg himm with he | ha
      · rw [fd_ex_none hT hp hW hS her] at he; cases he
      · cases hk : χ.kind with
        | imm => exact himm hk
        | «mut» => exact fd_ag_not_mut hT hp hW hS har ha hk
        | own => exact hown (fd_ag_own hW hS har ha hk)

end BoCa.Fig16.LogRel.Core.Tree

end
