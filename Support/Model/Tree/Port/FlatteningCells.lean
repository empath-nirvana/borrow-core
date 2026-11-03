import Support.Model.Tree.Port.AlgebraInstances

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Support/Model/FlatteningCells.lean`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

/-!
# Support — Model — FlatteningCells

`[about ours]`.  The cells of a flattening: a cell of `ρ` reappears in `⦇ρ⦈`, the walks' witnesses lie beneath their cells, and the order `≤` on resources.
-/



namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- Where the left operand of a `●` is `imm`-free, every cell of the right
operand passes into the composite unchanged. -/
theorem ResUT.CompS.get_right_of_immFree {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompS ρ₁ ρ₂ ρ)
    (himm : ρ₁.ImmFree) {l : Loc} {ψ : CellUT Loc Val K} (e : ρ₂.get l = some ψ) :
    ρ.get l = some ψ := by
  rcases h.get l with ⟨-, f₂, -⟩ | ⟨χ, -, f₂, -⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, -, hC⟩
  · rw [f₂] at e; exact absurd e (by simp)
  · rw [f₂] at e; exact absurd e (by simp)
  · rw [f₂] at e; cases Option.some.inj e; exact f
  · exact absurd (CellUT.CompatS.kinds (CellUT.CompS.compat hC)).1 (himm l χ₁ f₁)

/-- An `imm` cell of the left operand of a `○` reappears in the composite as an
`imm` cell over the same value and witness. -/
theorem ResUT.CompR.get_imm_left {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompR ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellUT Loc Val K} (e : ρ₁.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, ρ.get l = some χ ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit := by
  rcases h.get l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [f₁] at e; exact absurd e (by simp)
  · rw [f₁] at e; cases Option.some.inj e; exact ⟨_, f, hk, rfl, rfl⟩
  · rw [f₁] at e; exact absurd e (by simp)
  · rw [f₁] at e
    cases Option.some.inj e
    obtain ⟨m₁, m₂, m₃⟩ := CellUT.CompR.imm_left hC hk
    exact ⟨χ, f, m₁, m₂, m₃⟩

/-- The mirror of `ResUT.CompR.get_imm_left`. -/
theorem ResUT.CompR.get_imm_right {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompR ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellUT Loc Val K} (e : ρ₂.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, ρ.get l = some χ ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit :=
  ResUT.CompR.get_imm_left h.comm e hk

/-- `ex(ρ)_●` keeps every own-or-mut cell of `ρ` where it is.
`[about ours: the own-or-mut half of "the cells of `ρ′` are a subset of those of
`⦇ρ′⦈`" (`[TR]` Lemma 6.16's proof, p. 8), at the exclusive walk]` -/
theorem ExST.get_of_ne_imm {ρ σ : ResUT Loc Val K} (h : ExST ρ σ) {l : Loc}
    {ψ : CellUT Loc Val K} (e : ρ.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    σ.get l = some ψ := by
  cases h with
  | mk hs hw hb hnm hσ =>
      refine (ResUT.CompS.get_left_of_ne_imm hσ ?_ hk).2
      cases hkk : ψ.kind with
      | own => exact (ResUT.CompS.get_left_of_ne_imm hnm (ResUT.restrict_get_some e hkk) hk).2
      | imm => exact absurd hkk hk
      | «mut» =>
          exact (ResUT.CompS.get_right_of_ne_imm hnm (ResUT.restrict_get_some e hkk) hk).2

/-- `ag(ρ)` keeps every `imm` cell of `ρ` at its own location, as an `imm` cell
over the same value and witness.
`[about ours: the `imm` half of "the cells of `ρ′` are a subset of those of
`⦇ρ′⦈`" (`[TR]` Lemma 6.16's proof, p. 8), at the aliasable walk]` -/
theorem AgWT.get_imm {ρ σ : ResUT Loc Val K} (h : AgWT ρ σ) {l : Loc}
    {ψ : CellUT Loc Val K} (e : ρ.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, σ.get l = some χ ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      obtain ⟨χ₀, f₀, k₀, e₀, w₀⟩ :=
        ResUT.CompR.get_imm_left ha (ResUT.restrict_get_some e hk) hk
      obtain ⟨χ, f, k', e', w'⟩ := ResUT.CompR.get_imm_left hσ f₀ k₀
      exact ⟨χ, f, k', e'.trans e₀, w'.trans w₀⟩

/-- "The cells of `ρ` are a subset of those of `⦇ρ⦈`" (`[TR]` Lemma 6.16's
proof, p. 8): an `own` or `mut` cell reappears unchanged, an `imm` cell over the
same value and witness with its lifetime set possibly enlarged.
`[about ours: the step of `[TR]` Lemma 6.16's proof that unravels `⦇−⦈`, at the
walks]` -/
theorem ResUT.Flat.get {ρ σ : ResUT Loc Val K} (h : ResUT.Flat ρ σ) {l : Loc}
    {ψ : CellUT Loc Val K} (e : ρ.get l = some ψ) :
    ∃ χ, σ.get l = some χ ∧ χ.kind = ψ.kind ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit := by
  obtain ⟨ex, ag, hex, hag, hc⟩ := h
  by_cases hk : ψ.kind = Kind.imm
  · obtain ⟨χ, f, k', e', w'⟩ := AgWT.get_imm hag e hk
    exact ⟨χ, ResUT.CompS.get_right_of_immFree hc (ExST.immFree hex) f,
      k'.trans hk.symm, e', w'⟩
  · exact ⟨ψ, (ResUT.CompS.get_left_of_ne_imm hc (ExST.get_of_ne_imm hex e hk) hk).2,
      rfl, rfl, rfl⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
variable {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
variable {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}

/-- A factor of a factor is a factor.
`[about ours: `[TR]` Lemma 6.3 with both intermediate values existentially
quantified away]` -/
theorem ResUT.Comp.factor_trans (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ResUT.CompLaws C) {x y u v w : ResUT Loc Val K}
    (h₁ : ResUT.Comp R C x y u) (h₂ : ResUT.Comp R C u v w) :
    ∃ z, ResUT.Comp R C x z w := by
  obtain ⟨z, -, hz⟩ := (ResUT.Comp.assoc hR hC.assoc x y v w).mpr ⟨u, h₁, h₂⟩
  exact ⟨z, hz⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- Either factor of a `○` is `≼` the composite. -/
theorem ResUT.LeR.left {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompR ρ₁ ρ₂ ρ) :
    ResUT.LeR ρ₁ ρ := ⟨ρ₂, h⟩

theorem ResUT.LeR.right {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompR ρ₁ ρ₂ ρ) :
    ResUT.LeR ρ₂ ρ := ⟨ρ₁, ResUT.CompR.comm h⟩

/-- `≼` is transitive. -/
theorem ResUT.LeR.trans {ρ σ τ : ResUT Loc Val K}
    (h₁ : ResUT.LeR ρ σ) (h₂ : ResUT.LeR σ τ) : ResUT.LeR ρ τ := by
  obtain ⟨z₁, hz₁⟩ := h₁
  obtain ⟨z₂, hz₂⟩ := h₂
  exact ResUT.Comp.factor_trans (fun _ _ ψ hc => ⟨ψ, hc⟩) ResUT.compLawsR hz₁ hz₂

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
variable {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
variable {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}

/-- Every member of an iterated composition is a factor of it.
`[about ours: `[TR]` Lemmas 6.2 and 6.3 carried along the fold]` -/
theorem BigCompT.mem_factor (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResUT.CompLaws C) :
    ∀ {xs : List (ResUT Loc Val K)} {b : ResUT Loc Val K}, BigCompT R C xs b →
      ∀ x ∈ xs, ∃ z, ResUT.Comp R C x z b := by
  intro xs
  induction xs with
  | nil => intro b _ x hx; exact absurd hx (by simp)
  | cons y ys ih =>
      intro b hbc x hx
      cases hbc with
      | cons hb hc =>
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨_, hc⟩
          · obtain ⟨υ, hυ⟩ := ih hb x hx'
            exact ResUT.Comp.factor_trans hR hC hυ (ResUT.Comp.comm_of_laws hR hC hc)

/-- A sub-family folds to a factor of the whole family's fold: `[TR]` 6.127's
second bullet (p. 33), *"Since `π′ ⊆ π`, `ρ ≥ ⨀_{ℓ∈dom(π)} π(ℓ) ≥
⨀_{ℓ∈dom(π′)} π′(ℓ)`."*
`[about ours: `BigCompT` is the fold shape; the step is `[TR]` 6.127's own]` -/
theorem BigCompT.sublist (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResUT.CompLaws C)
    {l l' : List (ResUT Loc Val K)} (hs : List.Sublist l' l) :
    ∀ {b : ResUT Loc Val K}, BigCompT R C l b →
      ∃ b' f, BigCompT R C l' b' ∧ ResUT.Comp R C b' f b := by
  induction hs with
  | slnil =>
      intro b h
      cases h
      exact ⟨PMap.empty, PMap.empty, G.BigComp.nil, ResUT.comp_empty_right _⟩
  | cons a _ ih =>
      intro b h
      cases h with
      | cons hτ hcσ =>
          obtain ⟨b', f, hb', hcf⟩ := ih hτ
          obtain ⟨x, hx⟩ :=
            ResUT.Comp.factor_trans hR hC hcf (ResUT.Comp.comm_of_laws hR hC hcσ)
          exact ⟨b', x, hb', hx⟩
  | cons_cons a _ ih =>
      intro b h
      cases h with
      | cons hτ hcσ =>
          obtain ⟨b', f, hb', hcf⟩ := ih hτ
          obtain ⟨y, hy₁, hy₂⟩ :=
            (ResUT.Comp.assoc hR hC.assoc a b' f b).mp ⟨_, hcf, hcσ⟩
          exact ⟨y, f, G.BigComp.cons hb' hy₁, hy₂⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `BigCompT.sublist` at `●`, read in the order `[CONF]` p. 415:24 footnote 1
defines: the sub-family's fold is `≤` the whole family's.
`[about ours: `BigCompT.sublist` at `●`]` -/
theorem BigCompT.leS_of_sublist {l l' : List (ResUT Loc Val K)} (hs : List.Sublist l' l)
    {b : ResUT Loc Val K} (h : BigCompT CellUT.CompatS CellUT.CompS l b) :
    ∃ b', BigCompT CellUT.CompatS CellUT.CompS l' b' ∧ ResUT.Le b' b := by
  obtain ⟨b', f, hb', hcf⟩ :=
    BigCompT.sublist (fun _ _ _ hc => CellUT.CompS.compat hc) ResUT.compLawsS hs h
  exact ⟨b', hb', f, hcf⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
variable {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
variable {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}

/-- `ex(ρᵥ)_◐` is a factor of `ex(ρ)_◐` wherever `ρ(ℓ) = mut(_,_,ρᵥ,_)`.
`[about ours: the factor `ρₘ ● ex(ρᵥ)_●` of `[TR]` Lemma 6.17's display (p. 8),
at the walk schema]` -/
theorem ExWT.wit_le (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResUT.CompLaws C)
    {ρ σ : ResUT Loc Val K} (h : ExWT R C ρ σ) {l : Loc} {ψ : CellUT Loc Val K}
    (e : ρ.get l = some ψ) (hk : ψ.kind = Kind.mut) :
    ∃ ev z, ExWT R C ψ.wit ev ∧ ResUT.Comp R C ev z σ := by
  cases h with
  | mk hs hw hb hnm hσ =>
      obtain ⟨p, hp, hp₁⟩ := List.mem_map.mp ((hs.2 l).mpr ⟨ψ, e, hk⟩)
      obtain ⟨χ, hχ, hev⟩ := ExWitsT.mem hw p hp
      rw [hp₁, e] at hχ
      cases Option.some.inj hχ
      obtain ⟨z, hz⟩ := BigCompT.mem_factor hR hC hb p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      obtain ⟨z', hz'⟩ :=
        ResUT.Comp.factor_trans hR hC hz (ResUT.Comp.comm_of_laws hR hC hσ)
      exact ⟨p.2, z', hev, hz'⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `ag(ρᵥ)` is a factor of `ag(ρ)` wherever `ρ(ℓ) = mut(_,_,ρᵥ,_)`.
`[about ours: the factor `ag(ρᵥ)` of `[TR]` Lemma 6.17's display (p. 8)]` -/
theorem AgWT.mut_wit_le {ρ σ : ResUT Loc Val K} (h : AgWT ρ σ) {l : Loc}
    {ψ : CellUT Loc Val K} (e : ρ.get l = some ψ) (hk : ψ.kind = Kind.mut) :
    ∃ av z, AgWT ψ.wit av ∧ ResUT.CompR av z σ := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellUT Loc Val K, CellUT.CompR ψ₁ ψ₂ ψ → CellUT.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      obtain ⟨p, hp, hp₁⟩ := List.mem_map.mp ((hsm.2 l).mpr ⟨ψ, e, hk⟩)
      obtain ⟨χ, hχ, hav⟩ := AgWitsMT.mem hwm p hp
      rw [hp₁, e] at hχ
      cases Option.some.inj hχ
      obtain ⟨z, hz⟩ :=
        BigCompT.mem_factor hR ResUT.compLawsR hbm p.2 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      obtain ⟨z₁, hz₁⟩ :=
        ResUT.Comp.factor_trans hR ResUT.compLawsR hz
          (ResUT.Comp.comm_of_laws hR ResUT.compLawsR ha)
      obtain ⟨z₂, hz₂⟩ := ResUT.Comp.factor_trans hR ResUT.compLawsR hz₁ hσ
      exact ⟨p.2, z₂, hav, hz₂⟩

/-- If `ρₘ` carries `mut(_, _, ρᵥ, _)` at some location and `ρ ● ρₘ` is valid,
then `ρ ▸◂ ρᵥ`: `[TR]` Lemma 6.17's two closing sentences, "`ρ` and `ρᵥ` agree on
imm cells up to lifetimes" and "`ρ` and `ρₘ ● ρᵥ` have disjoint own-or-mut
cells", which on this carrier are the single statement `ρ ▸◂ ρᵥ`.
`[about ours: `[TR]` Lemma 6.17's proof (p. 8) from its display onward, for a
`mut` cell in any `ρₘ`]` -/
theorem ResUT.CompatS.of_valid_mut {ρ ρm ρv ρ' : ResUT Loc Val K} {l : Loc}
    {ψ : CellUT Loc Val K} (hm : ρm.get l = some ψ) (hk : ψ.kind = Kind.mut)
    (hwit : ψ.wit = ρv) (h : ResUT.CompS ρ ρm ρ') (hval : ResUT.Valid ρ') :
    ResUT.CompatS ρ ρv := by
  obtain ⟨σ, hσ⟩ := hval
  obtain ⟨e₁, e₂, e, a₁, a₂, a, -, -, he₁, he₂, hec, ha₁, ha₂, hac, hc, -, -⟩ :=
    ResUT.Flat.split_factors h hσ
  obtain ⟨ev, zv, hev, hzv⟩ :=
    ExWT.wit_le (fun _ _ _ hcc => CellUT.CompS.compat hcc) ResUT.compLawsS he₂ hm hk
  obtain ⟨av, za, hav, hza⟩ := AgWT.mut_wit_le ha₂ hm hk
  rw [hwit] at hev hav
  intro l' χ χv f fv
  by_cases k₁ : χ.kind = Kind.imm <;> by_cases k₂ : χv.kind = Kind.imm
  · -- Both `imm`.  Their images meet inside `ag(ρ) ○ ag(ρₘ)`, whose cell-level
    -- `○` forces one value and one witness on them.
    obtain ⟨d₁, g₁, m₁, n₁, w₁⟩ := AgWT.get_imm ha₁ f k₁
    obtain ⟨d₂, g₂, m₂, n₂, w₂⟩ := AgWT.get_imm hav fv k₂
    obtain ⟨d₃, g₃, m₃, n₃, w₃⟩ := ResUT.CompR.get_imm_left hza g₂ m₂
    obtain ⟨hve, hwt⟩ := CellUT.compatR_iff.mp (hac.1 l' d₁ d₃ g₁ g₃)
    refine CellUT.compatS_iff.mpr ⟨k₁, k₂, ?_, ?_⟩
    · exact n₁.symm.trans (hve.trans (n₃.trans n₂))
    · refine w₁.symm.trans ?_
      exact (hwt (by rw [m₁]; simp) (by rw [m₃]; simp)).trans (w₃.trans w₂)
  · -- `χ` is `imm` and `χᵥ` is not: the first reaches `ag`, the second `ex`, and
    -- the final `●` of `⦇ρ ● ρₘ⦈` would have to compose them.
    obtain ⟨d₁, g₁, m₁, -, -⟩ := AgWT.get_imm ha₁ f k₁
    obtain ⟨d, g, -, -, -⟩ := ResUT.CompR.get_imm_left hac g₁ m₁
    have hev' : e.get l' = some χv :=
      (ResUT.CompS.get_right_of_ne_imm hec
        (ResUT.CompS.get_left_of_ne_imm hzv (ExST.get_of_ne_imm hev fv k₂) k₂).2 k₂).2
    exact absurd (CellUT.CompatS.kinds (hc.1 l' χv d hev' g)).1 k₂
  · -- The mirror: `χ` is not `imm` and `χᵥ` is.
    obtain ⟨d₂, g₂, m₂, -, -⟩ := AgWT.get_imm hav fv k₂
    obtain ⟨d₃, g₃, m₃, -, -⟩ := ResUT.CompR.get_imm_left hza g₂ m₂
    obtain ⟨d, g, -, -, -⟩ := ResUT.CompR.get_imm_right hac g₃ m₃
    have he' : e.get l' = some χ :=
      (ResUT.CompS.get_left_of_ne_imm hec (ExST.get_of_ne_imm he₁ f k₁) k₁).2
    exact absurd (CellUT.CompatS.kinds (hc.1 l' χ d he' g)).1 k₁
  · -- Neither is `imm`: both reach `ex(ρ)_●` and `ex(ρₘ)_●` at `ℓ′` unchanged,
    -- and `●` keeps the own-or-mut cells of its two operands disjoint.
    have h₂ : e₂.get l' = some χv :=
      (ResUT.CompS.get_left_of_ne_imm hzv (ExST.get_of_ne_imm hev fv k₂) k₂).2
    have h₁ := (ResUT.CompS.get_left_of_ne_imm hec (ExST.get_of_ne_imm he₁ f k₁) k₁).1
    rw [h₁] at h₂
    exact absurd h₂ (by simp)

end BoCa.Fig16.Tree

end
