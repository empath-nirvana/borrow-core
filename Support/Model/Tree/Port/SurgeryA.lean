import Support.Model.Tree.Port.Six48

/-!
# Singleton and empty-resource facts for the surgery lemmas, over the tree-stratified carrier

Translated from `Support/Model/Reborrow.lean` and `Support/Model/Surgery.lean` and edited by
hand, not generated. The facts about `ℓ ↦ mut(…)` singletons, empty composites and agreement off
a location that Lemmas 6.16–6.24 and the surgery lemmas use, over `CellUT K`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
theorem ResUT.sites_nil_of_none {ρ : ResUT Loc Val K} {k : Kind} {d : List Loc}
    (h : ResUT.Sites ρ k d) (hno : ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ k) : d = [] := by
  cases d with
  | nil => rfl
  | cons a t =>
      obtain ⟨ψ, hg, hk⟩ := (h.2 a).mp List.mem_cons_self
      exact absurd hk (hno a ψ hg)

theorem ResUT.sites_singleton_of {ρ : ResUT Loc Val K} {k : Kind} {d : List Loc} {l : Loc}
    (hs : ResUT.Sites ρ k d)
    (hchar : ∀ x, (∃ ψ, ρ.get x = some ψ ∧ ψ.kind = k) ↔ x = l) : d = [l] := by
  have hm : ∀ x, x ∈ d ↔ x = l := fun x => (hs.2 x).trans (hchar x)
  cases d with
  | nil => exact absurd ((hm l).mpr rfl) (by simp)
  | cons a t =>
      obtain rfl : a = l := (hm a).mp List.mem_cons_self
      cases t with
      | nil => rfl
      | cons b t' =>
          obtain rfl : b = a := (hm b).mp (List.mem_cons_of_mem _ List.mem_cons_self)
          exact absurd List.mem_cons_self (List.nodup_cons.mp hs.1).1

theorem BigCompT.nil_inv {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop} {b : ResUT Loc Val K}
    (h : BigCompT R C [] b) : b = PMap.empty := by cases h; rfl

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
variable {Loc Val : Type} {K : WCactus}
/-- `ρ ◐ ∅ = σ` determines `σ`, at any cell-level operation.
`[about ours: the schema-level converse of `[TR]` 6.4, for the walks,
whose operator is a parameter]` -/
theorem ResUT.eq_of_comp_empty_right {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop} {ρ σ : ResUT Loc Val K}
    (h : ResUT.Comp R C ρ PMap.empty σ) : ρ = σ := by
  refine PMap.ext fun l => ?_
  have hl := h.2 l
  have he : (PMap.empty : ResUT Loc Val K).get l = none := rfl
  rw [he] at hl
  cases e : ρ.get l with
  | none => rw [e] at hl; exact (show σ.get l = none from hl).symm
  | some ψ => rw [e] at hl; exact (show σ.get l = some ψ from hl).symm

/-- `∅ ◐ ρ = σ` determines `σ`.
`[about ours: the schema-level converse of `[TR]` 6.4, for the walks]` -/
theorem ResUT.eq_of_comp_empty_left {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop} {ρ σ : ResUT Loc Val K}
    (h : ResUT.Comp R C PMap.empty ρ σ) : ρ = σ := by
  refine PMap.ext fun l => ?_
  have hl := h.2 l
  have he : (PMap.empty : ResUT Loc Val K).get l = none := rfl
  rw [he] at hl
  cases e : ρ.get l with
  | none => rw [e] at hl; exact (show σ.get l = none from hl).symm
  | some ψ => rw [e] at hl; exact (show σ.get l = some ψ from hl).symm

/-- `ex` at a singleton `mut` cell, read backwards: the cell composed with the
witness's walk.
`[about ours: `ex`'s printed row evaluated at one `mut` cell]` -/
theorem ExWT.single_mut_inv {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {l : Loc} {b : TSet} [Fact (K.Anti b)] {v : Val} {χ : ResUT Loc Val K} {hstr : ResUT.InStratum b χ}
    {P : Val → SPropST Loc Val K b} {hw : P v ⟨χ, hstr⟩} {σ : ResUT Loc Val K}
    (h : ExWT R C (ResUT.single l (CellUT.mutOf b v χ hstr P hw)) σ) :
    ∃ e, ExWT R C χ e ∧
      ResUT.Comp R C (ResUT.single l (CellUT.mutOf b v χ hstr P hw)) e σ := by
  have hk : (CellUT.mutOf b v χ hstr P hw).kind = Kind.mut :=
    CellUT.kind_mutOf _ _ _ _ _ _
  cases h with
  | mk hs hwts hb hnm hσ =>
      rename_i nm bb w
      have hfst : w.map Prod.fst = [l] := by
        refine ResUT.sites_singleton_of hs (fun x => ⟨?_, ?_⟩)
        · rintro ⟨ψ, hg, -⟩
          exact (ResUT.single_get_eq_some hg).1
        · rintro rfl
          exact ⟨_, ResUT.single_get_self _ _, hk⟩
      cases w with
      | nil => simp at hfst
      | cons q t =>
          obtain ⟨x, e⟩ := q
          simp only [List.map_cons, List.cons.injEq] at hfst
          obtain ⟨-, ht⟩ := hfst
          obtain rfl : t = [] := by
            cases t with
            | nil => rfl
            | cons c t' => simp at ht
          cases hwts with
          | cons ψ hψ hkψ he hwts' =>
              obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some hψ
              rw [CellUT.wit_mutOf] at he
              have hbe : e = bb := by
                cases hb with
                | cons hnil hcomp =>
                    rename_i τ
                    obtain rfl : τ = (PMap.empty : ResUT Loc Val K) := BigCompT.nil_inv hnil
                    exact ResUT.eq_of_comp_empty_right hcomp
              rw [ResUT.restrict_single_other (k := Kind.own)
                    (by rw [hk]; exact fun c => Kind.noConfusion c),
                  ResUT.restrict_single_self hk] at hnm
              have hnmeq := ResUT.eq_of_comp_empty_left hnm
              refine ⟨e, he, ?_⟩
              rw [hnmeq, hbe]
              exact hσ

/-- `ag` at a singleton `mut` cell, read backwards: the witness's own `ag`.
`[about ours: `ag`'s printed row evaluated at one `mut` cell]` -/
theorem AgWT.single_mut_inv {l : Loc} {b : TSet} [Fact (K.Anti b)] {v : Val} {χ : ResUT Loc Val K}
    {hstr : ResUT.InStratum b χ} {P : Val → SPropST Loc Val K b} {hw : P v ⟨χ, hstr⟩}
    {σ : ResUT Loc Val K}
    (h : AgWT (ResUT.single l (CellUT.mutOf b v χ hstr P hw)) σ) : AgWT χ σ := by
  have hk : (CellUT.mutOf b v χ hstr P hw).kind = Kind.mut :=
    CellUT.kind_mutOf _ _ _ _ _ _
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i a bm bi wm wi
      obtain rfl : wi = [] := by
        have hnil : wi.map Prod.fst = [] :=
          ResUT.sites_nil_of_none hsi (by
            intro m ψ hg
            obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some hg
            rw [hk]; exact fun c => Kind.noConfusion c)
        cases wi with
        | nil => rfl
        | cons q t => simp at hnil
      obtain rfl : bi = (PMap.empty : ResUT Loc Val K) := BigCompT.nil_inv hbi
      have hfst : wm.map Prod.fst = [l] := by
        refine ResUT.sites_singleton_of hsm (fun x => ⟨?_, ?_⟩)
        · rintro ⟨ψ, hg, -⟩
          exact (ResUT.single_get_eq_some hg).1
        · rintro rfl
          exact ⟨_, ResUT.single_get_self _ _, hk⟩
      cases wm with
      | nil => simp at hfst
      | cons q t =>
          obtain ⟨x, am⟩ := q
          simp only [List.map_cons, List.cons.injEq] at hfst
          obtain ⟨-, ht⟩ := hfst
          obtain rfl : t = [] := by
            cases t with
            | nil => rfl
            | cons c t' => simp at ht
          cases hwm with
          | cons ψ hψ hkψ hag hwm' =>
              obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some hψ
              rw [CellUT.wit_mutOf] at hag
              have hbe : am = bm := by
                cases hbm with
                | cons hnil hcomp =>
                    rename_i τ
                    obtain rfl : τ = (PMap.empty : ResUT Loc Val K) := BigCompT.nil_inv hnil
                    exact ResUT.eq_of_comp_empty_right hcomp
              rw [ResUT.restrict_single_other (k := Kind.imm)
                    (by rw [hk]; exact fun c => Kind.noConfusion c)] at ha
              have haeq := ResUT.eq_of_comp_empty_left ha
              have hσeq := ResUT.eq_of_comp_empty_right hσ
              rw [← hσeq, ← haeq, ← hbe]
              exact hag

/-- Two resources that agree off `ℓ` and carry an exclusive cell at `ℓ` have
the same `▸◂` partners: `[TR]` 6.22's *"Since `ρ_o` contains a single `own`
cell, this composite is well-defined if and only if the same composite is defined
when `ρ_o` is replaced by `ρ_m`"*, which 6.23's proof reuses.
`[about ours: the sentence `[TR]` 6.22 and 6.23 close on, as a lemma]` -/
theorem ResUT.compatS_congr_of_excl {l : Loc} {s s' A : ResUT Loc Val K}
    (hoff : ∀ x, x ≠ l → s'.get x = s.get x)
    {ψ : CellUT Loc Val K} (hg : s.get l = some ψ) (hk : ψ.kind ≠ Kind.imm)
    (hc : ResUT.CompatS s A) : ResUT.CompatS s' A := by
  intro x χ₁ χ₂ e₁ e₂
  by_cases hx : x = l
  · subst hx
    rw [ResUT.CompatS.right_eq_none hc hg hk] at e₂
    exact absurd e₂ (by simp)
  · exact hc x χ₁ χ₂ (by rw [← hoff x hx]; exact e₁) e₂

/-- Two composites over the same left operand agree wherever their right
operands do. -/
theorem ResUT.compS_agree_off_right {l : Loc} {ρ₁ ρ₂ ρ₂' ρ ρ' : ResUT Loc Val K}
    (h : ResUT.CompS ρ₁ ρ₂ ρ) (h' : ResUT.CompS ρ₁ ρ₂' ρ')
    (hoff : ∀ x, x ≠ l → ρ₂'.get x = ρ₂.get x) :
    ∀ x, x ≠ l → ρ'.get x = ρ.get x := by
  intro x hx
  have h1 := h.2 x
  have h2 := h'.2 x
  rw [hoff x hx] at h2
  cases e₁ : ρ₁.get x <;> cases e₂ : ρ₂.get x <;> rw [e₁, e₂] at h1 h2
  · rw [h1, h2]
  · rw [h1, h2]
  · rw [h1, h2]
  · obtain ⟨ψa, ha, hCa⟩ := h1
    obtain ⟨ψb, hb, hCb⟩ := h2
    rw [ha, hb, CellUT.CompS.functional hCa hCb]

/-- `ex` at a singleton `mut` cell, forwards.
`[about ours: `ex`'s printed row evaluated at one `mut` cell]` -/
theorem ExWT.single_mut {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {l : Loc} {b : TSet} [Fact (K.Anti b)] {v : Val} {χ : ResUT Loc Val K} {hstr : ResUT.InStratum b χ}
    {P : Val → SPropST Loc Val K b} {hw : P v ⟨χ, hstr⟩} {e σ : ResUT Loc Val K}
    (he : ExWT R C χ e)
    (hσ : ResUT.Comp R C (ResUT.single l (CellUT.mutOf b v χ hstr P hw)) e σ) :
    ExWT R C (ResUT.single l (CellUT.mutOf b v χ hstr P hw)) σ := by
  have hk : (CellUT.mutOf b v χ hstr P hw).kind = Kind.mut :=
    CellUT.kind_mutOf _ _ _ _ _ _
  refine G.ExW.mk (w := [(l, e)]) (b := e)
    (nm := ResUT.single l (CellUT.mutOf b v χ hstr P hw))
    (ResUT.sites_single_self hk) ?_ (BigCompT.single e) ?_ hσ
  · exact G.ExWits.cons (CellUT.mutOf b v χ hstr P hw) (ResUT.single_get_self _ _) hk
      (by rwa [CellUT.wit_mutOf]) G.ExWits.nil
  · rw [ResUT.restrict_single_other (k := Kind.own)
        (by rw [hk]; exact fun c => Kind.noConfusion c),
      ResUT.restrict_single_self hk]
    exact ResUT.comp_empty_left _

/-- `ag` at a singleton `mut` cell, forwards.
`[about ours: `ag`'s printed row evaluated at one `mut` cell]` -/
theorem AgWT.single_mut {l : Loc} {b : TSet} [Fact (K.Anti b)] {v : Val} {χ : ResUT Loc Val K}
    {hstr : ResUT.InStratum b χ} {P : Val → SPropST Loc Val K b} {hw : P v ⟨χ, hstr⟩}
    {a : ResUT Loc Val K} (ha : AgWT χ a) :
    AgWT (ResUT.single l (CellUT.mutOf b v χ hstr P hw)) a := by
  have hk : (CellUT.mutOf b v χ hstr P hw).kind = Kind.mut :=
    CellUT.kind_mutOf _ _ _ _ _ _
  refine G.AgW.mk (wm := [(l, a)]) (wi := []) (a := a) (bm := a) (bi := PMap.empty)
    (ResUT.sites_single_self hk)
    (ResUT.sites_single_other (by rw [hk]; exact fun c => Kind.noConfusion c))
    ?_ G.AgWitsI.nil (BigCompT.single a) G.BigComp.nil ?_ (ResUT.comp_empty_right _)
  · exact G.AgWitsM.cons (CellUT.mutOf b v χ hstr P hw) (ResUT.single_get_self _ _) hk
      (by rwa [CellUT.wit_mutOf]) G.AgWitsM.nil
  · rw [ResUT.restrict_single_other (k := Kind.imm)
        (by rw [hk]; exact fun c => Kind.noConfusion c)]
    exact ResUT.comp_empty_left _

end BoCa.Fig16.Tree

end
