import Core.Chain.RelBase791N

/-!
# The observable view and the image of a reborrow at `vN₀`  `[spec §62]`

`withload_compatX`'s steps 5, 7 and 8 (`chain-interpretation.md` §6.3) at `vN₀`'s `Imm` clause, which
reads its payload in the observable view `vO₀` (Core's `vCE false`) and its location's witness in
the world's `imm` records (`ImmWitW`, Core's `CohE`):

* `vN_vO₀`: a value is observable (Core's `vC` at `true` read at `false`);
* `vN_vShape₀`, `vO_vShape₀`: the shape of a value (Core's `vC_vShape`);
* `vO_transfer₀`: the observable view transfers between two pieces of one escrow (Core's
  `obs_transfer`);
* `relabel_vN₀`: an image of an escrow re-taken at `β` is a value of `Imm̲ 'x A` at `δ['x ↦ β]`
  (Core's `relabel_obs`), the witnesses of the image's new cells supplied at the escrow's `Ref`
  and `Mut` positions;
* `RefPos.tyEq`, `MutPos.tyEq`: positions read across `TyEq`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### A value is observable -/

/-! ### The shape of a value -/

/-! ### The observable view transfers between pieces of one escrow -/

/-- `Val.loc` is injective. -/
theorem loc_inj {l l' : Loc} (h : Val.loc l = Val.loc l') : l = l' := by
  have := congrArg Subtype.val h; simpa [Val.loc] using this

/-- **Every `imm` cell of `B` is no longer-lived than every world record coherent at its
location**: Core's `FrameLife` (a record's lineage views have lifetimes ⊑ its tag) read at the
cells of `B` and the world's records. A run's typed world supplies it at its entry
(`Withload791N.lifeBoundW_of_entry`). -/
def LifeBoundOn (I : List SRec) (P : Loc → Prop) (B : WRes) : Prop :=
  ∀ m t u σ h, B.get m = some (CellU.immOf t u σ h) → P m → ∀ x ∈ I, ∀ d, DescR x.1 d →
    ∀ S δ₀, CohE [d] m S δ₀ → ∀ y, t.mem y → y ≤ x.2

/-- `LifeBoundOn` at every location. -/
abbrev LifeBoundW (I : List SRec) (B : WRes) : Prop := LifeBoundOn I (fun _ => True) B

/-- A piece of an `imm` cell has fewer lifetimes. -/
theorem imm_piece_left {B₁ B₂ B : WRes} (hc : ResU.CompS B₁ B₂ B) {m : Loc} {t : LSet}
    {u : Val} {σ : WRes} {hσ : σ.InStratum t.join} (e : B₁.get m = some (CellU.immOf t u σ hσ)) :
    ∃ (t' : LSet) (h' : σ.InStratum t'.join), B.get m = some (CellU.immOf t' u σ h') ∧
      ∀ y, t.mem y → t'.mem y := by
  rcases ResU.Comp.get hc m with ⟨f₁, -, -⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, f₁, -, -⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, -, f, hC⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁; cases Option.some.inj f₁
    exact ⟨t, hσ, f, fun _ h => h⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁; cases Option.some.inj f₁
    obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, rfl, rfl⟩ := hC
    obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₁
    exact ⟨_, h₃, f, fun _ h => Or.inl h⟩

theorem LifeBoundOn.left {I : List SRec} {P : Loc → Prop} {B₁ B₂ B : WRes}
    (hc : ResU.CompS B₁ B₂ B) (h : LifeBoundOn I P B) : LifeBoundOn I P B₁ := by
  intro m t u σ hσ e hP x hx d hd S δ₀ hco y hy
  obtain ⟨t', h', e', ht⟩ := imm_piece_left hc e
  exact h m t' u σ h' e' hP x hx d hd S δ₀ hco y (ht y hy)

theorem LifeBoundOn.right {I : List SRec} {P : Loc → Prop} {B₁ B₂ B : WRes}
    (hc : ResU.CompS B₁ B₂ B) (h : LifeBoundOn I P B) : LifeBoundOn I P B₂ := h.left hc.comm

/-- **Every cell of `c` at an `own` location of `R` has its witness bounded** (`LifeBoundW`). -/
def LifeBoundWit (I : List SRec) (R c : WRes) : Prop :=
  ∀ m ψ, c.get m = some ψ → (∃ u, R.get m = some (CellU.ownOf u)) → LifeBoundW I ψ.wit

theorem LifeBoundWit.left {I : List SRec} {R c₁ c₂ c : WRes} (hc : ResU.CompS c₁ c₂ c)
    (h : LifeBoundWit I R c) : LifeBoundWit I R c₁ := by
  intro m ψ e hR
  obtain ⟨ψ', e', -, w', -⟩ := compS_get_left' hc e
  rw [← w']
  exact h m ψ' e' hR

/-! ### The image of a reborrow, re-taken at `β`, at `vN₀` -/

/-! ### Positions across `TyEq` -/

/-- **A `Ref` position is read across `TyEq`**, at a pointee type `TyEq` to the first. -/
theorem _root_.BoCa.Fig16.LogRel.Core.RefPos.tyEq {T : VTy} {v : Val} {l : Loc} {S : VTy} (h : RefPos T v l S) :
    ∀ {T' : VTy} {δ δ' : LSub}, TyEq T δ T' δ' → ∃ S', RefPos T' v l S' ∧ TyEq S δ S' δ' := by
  induction h with
  | ref S l =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      exact ⟨_, RefPos.ref _ l, hT⟩
  | tensorL _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.1
      exact ⟨S', RefPos.tensorL h', e⟩
  | tensorR _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', RefPos.tensorR h', e⟩
  | sumL _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.1
      exact ⟨S', RefPos.sumL h', e⟩
  | sumR _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', RefPos.sumR h', e⟩
  | box _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', RefPos.box h', e⟩
  | @mu A _ _ _ hcl _ ih =>
      intro T' δ δ' hT
      cases T' with
      | mu A' =>
          simp only [TyEq] at hT
          have hcl' : (VTy.mu A').Cl 0 := (TyEq.Cl_iff (.mu A) (A' := .mu A') 0 hT).mp hcl
          obtain ⟨S', h', e⟩ := ih (TyEq.inst (S := .mu A) (S' := .mu A') hT hT)
          exact ⟨S', RefPos.mu hcl' h', e⟩
      | _ => simp only [TyEq] at hT
  | fam hi _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT
      exact ⟨S', RefPos.fam hi h', e⟩

/-- **A `Mut` position is read across `TyEq`**, at a pointee type `TyEq` to the first. -/
theorem _root_.BoCa.Fig16.LogRel.Core.MutPos.tyEq {T : VTy} {v : Val} {l : Loc} {S : VTy} (h : MutPos T v l S) :
    ∀ {T' : VTy} {δ δ' : LSub}, TyEq T δ T' δ' → ∃ S', MutPos T' v l S' ∧ TyEq S δ S' δ' := by
  induction h with
  | «mut» a S l =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      exact ⟨_, MutPos.mut _ _ l, hT.2⟩
  | tensorL _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.1
      exact ⟨S', MutPos.tensorL h', e⟩
  | tensorR _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', MutPos.tensorR h', e⟩
  | sumL _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.1
      exact ⟨S', MutPos.sumL h', e⟩
  | sumR _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', MutPos.sumR h', e⟩
  | box _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', MutPos.box h', e⟩
  | @mu A _ _ _ hcl _ ih =>
      intro T' δ δ' hT
      cases T' with
      | mu A' =>
          simp only [TyEq] at hT
          have hcl' : (VTy.mu A').Cl 0 := (TyEq.Cl_iff (.mu A) (A' := .mu A') 0 hT).mp hcl
          obtain ⟨S', h', e⟩ := ih (TyEq.inst (S := .mu A) (S' := .mu A') hT hT)
          exact ⟨S', MutPos.mu hcl' h', e⟩
      | _ => simp only [TyEq] at hT
  | fam hi _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT
      exact ⟨S', MutPos.fam hi h', e⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
