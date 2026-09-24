import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Dynamics.PrintedWp
import Support.Model.CellFacts
import Support.Model.Entailments
import Support.Model.ReborrowFrame
import Support.Model.Update
/-!
# Resources holding only `imm` cells  `[spec §2]`

`Free k ρ`: `ρ` has no cell of kind `k`.  A resource free of `own` and `mut` cells is idempotent
under `●` (`compS_self_of_imm`) and is its own reborrow at any `α` it outlives
(`reb_self_of_imm`), so `[α] P ⊨ ↺α P` for any `P` whose resources hold only `imm` cells
(`reborrow_self_of_imm`).  `SPEC.md` §2 uses it for `[TR]` 6.131 at `fn T₁ T₂`, whose resource
is `∅`.
-/

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
noncomputable section

/-- `ρ` has no cell of kind `k`. -/
def Free (k : Kind) (ρ : WRes) : Prop := ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ k

theorem free_empty (k : Kind) : Free k (PMap.empty : WRes) := by
  intro l ψ h
  rw [PMap.empty_get] at h
  exact absurd h (by simp)

theorem free_single {k : Kind} {l : BoCa.Loc} {ψ : CellU BoCa.Loc BoCa.Val}
    (hk : ψ.kind ≠ k) : Free k (ResU.single l ψ) := by
  intro m χ hm
  by_cases hml : m = l
  · subst hml
    rw [ResU.single_get_self] at hm
    cases Option.some.inj hm
    exact hk
  · rw [ResU.single_get_ne _ hml] at hm
    exact absurd hm (by simp)

/-- Freedom from a kind other than `imm` is closed under `●`: `●` composes `imm` cells only. -/
theorem free_compS {k : Kind} (hk : k ≠ Kind.imm) {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : Free k ρ₁) (h₂ : Free k ρ₂) : Free k ρ := by
  intro l ψ hl
  have hc := h.2 l
  cases e₁ : ρ₁.get l <;> cases e₂ : ρ₂.get l <;> rw [e₁, e₂] at hc
  · rw [hc] at hl; exact absurd hl (by simp)
  · rw [hc] at hl; cases Option.some.inj hl; exact h₂ l _ e₂
  · rw [hc] at hl; cases Option.some.inj hl; exact h₁ l _ e₁
  · obtain ⟨χ, hχ, hC⟩ := hc
    rw [hχ] at hl
    cases Option.some.inj hl
    obtain ⟨s₁, s₂, w, χw, k₁, k₂, k₃, -, -, e⟩ := hC
    rw [e, CellU.kind_immOf]
    exact fun h => hk h.symm

/-- A resource of `imm` cells only is idempotent under `●`. -/
theorem compS_self_of_imm {ρ : WRes} (ho : Free Kind.own ρ) (hm : Free Kind.mut ρ) :
    ResU.CompS ρ ρ ρ := by
  have key : ∀ l ψ, ρ.get l = some ψ → CellU.CompatS ψ ψ ∧ CellU.CompS ψ ψ ψ := by
    intro l ψ hψ
    cases ψ with
    | own v => exact absurd rfl (ho l _ hψ)
    | «mut» m => exact absurd rfl (hm l _ hψ)
    | imm i =>
        have h3 : i.res.InStratum (i.ls ∪ i.ls).join :=
          ResU.InStratum.sup i.ρ.toU_inStratum i.ρ.toU_inStratum
        rw [← ImmU.immOf_eta i]
        exact ⟨⟨i.ls, i.ls, i.v, i.res, _, _, rfl, rfl⟩,
          ⟨i.ls, i.ls, i.v, i.res, _, _, h3, rfl, rfl,
            CellU.immOf_congr (LSet.union_self _).symm rfl rfl _ _⟩⟩
  refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => ?_, fun l => ?_⟩
  · rw [e₁] at e₂
    cases Option.some.inj e₂
    exact (key l ψ₁ e₁).1
  · cases e : ρ.get l with
    | none => rfl
    | some ψ => exact ⟨ψ, rfl, (key l ψ e).2⟩

/-- `ρ` holds only `imm` cells. -/
def UnrRes (ρ : WRes) : Prop := Free Kind.own ρ ∧ Free Kind.mut ρ

private theorem memSingle' {A B : Type} {a a' : A} {b b' : B} (hm : (a, b) ∈ [(a', b')]) :
    a = a' ∧ b = b' := by
  have he := List.mem_singleton.mp hm
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- An `imm` cell is its own reborrow: `[TR]` 6.123's construction, keeping the cell. -/
theorem reb_single_imm {α : Life} (l : BoCa.Loc) (s : LSet) (v : BoCa.Val) (σ : WRes)
    (hs : σ.InStratum s.join) (ho : (ResU.single l (CellU.immOf s v σ hs)).InStratum α) :
    ResU.Reb α (ResU.single l (CellU.immOf s v σ hs)) (ResU.single l (CellU.immOf s v σ hs)) := by
  have hρl : (ResU.single l (CellU.immOf s v σ hs)).get l
      = some (CellU.immOf s v σ hs) := ResU.single_get_self _ _
  refine ⟨ho, [(l, ResU.single l (CellU.immOf s v σ hs))], _,
    ResU.dom_single _ _, BigComp.single _, ResU.Le.refl _, ?_⟩
  intro k p hm
  obtain ⟨rfl, rfl⟩ := memSingle' hm
  refine ⟨⟨_, hρl⟩, ?_, ?_,
    fun s' _ _ h' e' => ⟨⟨s', h', fun _ y => y, e'⟩, ResU.dom_single _ _⟩⟩
  · intro x e
    have hx : CellU.immOf s v σ hs = CellU.ownOf x := Option.some.inj (hρl.symm.trans e)
    exact absurd hx.symm CellU.ownOf_ne_immOf
  · intro b' x χ hb' Q' hw' e
    have hx : CellU.immOf s v σ hs = CellU.mutOf b' x χ hb' Q' hw' :=
      Option.some.inj (hρl.symm.trans e)
    exact absurd hx CellU.immOf_ne_mutOf

/-- An all-`imm` resource in `Res_α` is its own reborrow at `α`. -/
theorem reb_self_of_imm {α : Life} :
    ∀ (d : List BoCa.Loc) (ρ : WRes), (∀ l, ρ.get l ≠ none → l ∈ d) →
      Free Kind.own ρ → Free Kind.mut ρ → ρ.InStratum α → ResU.Reb α ρ ρ
  | [], ρ, hd, _, _, _ => by
      have e : ρ = PMap.empty := PMap.ext fun l => by
        rw [PMap.empty_get]
        by_contra h
        exact absurd (hd l h) (by simp)
      subst e
      exact BoLo.reb_empty α
  | l :: d, ρ, hd, ho, hm, hα => by
      cases hg : ρ.get l with
      | none =>
          refine reb_self_of_imm d ρ (fun m hm' => ?_) ho hm hα
          rcases List.mem_cons.mp (hd m hm') with rfl | h
          · exact absurd hg hm'
          · exact h
      | some ψ =>
          have hc := ResU.del_compS hg
          have hdel : ∀ m, (ρ.del l).get m ≠ none → m ∈ d := by
            intro m hm'
            by_cases hml : m = l
            · subst hml; rw [ResU.del_get_self] at hm'; exact absurd rfl hm'
            · rw [ResU.del_get_ne _ hml] at hm'
              rcases List.mem_cons.mp (hd m hm') with h | h
              · exact absurd h hml
              · exact h
          have sub : ∀ (k : Kind), Free k ρ → Free k (ρ.del l) := by
            intro k h m χ e
            by_cases hml : m = l
            · subst hml; rw [ResU.del_get_self] at e; cases e
            · rw [ResU.del_get_ne _ hml] at e; exact h m χ e
          have hαd : (ρ.del l).InStratum α := by
            intro m χ e
            by_cases hml : m = l
            · subst hml; rw [ResU.del_get_self] at e; cases e
            · rw [ResU.del_get_ne _ hml] at e; exact hα m χ e
          have h₁ := reb_self_of_imm d (ρ.del l) hdel (sub _ ho) (sub _ hm) hαd
          have h₂ : ResU.Reb α (ResU.single l ψ) (ResU.single l ψ) := by
            cases ψ with
            | own v => exact absurd rfl (ho l _ hg)
            | «mut» x => exact absurd rfl (hm l _ hg)
            | imm i =>
                rw [← ImmU.immOf_eta i]
                refine reb_single_imm l i.ls i.v i.res _ (fun m χ e => ?_)
                by_cases hml : m = l
                · subst hml
                  rw [ResU.single_get_self] at e
                  cases Option.some.inj e
                  rw [ImmU.immOf_eta i]; exact hα m _ hg
                · rw [ResU.single_get_ne _ hml] at e; cases e
          obtain ⟨ρ', hc', hreb⟩ := ResU.six61 h₁ h₂ hc
          rw [ResU.CompS.functional hc' hc] at hreb
          exact hreb

/-- **`[α] P ⊨ ↺α P` for every `P` whose resources are all-`imm`.** -/
theorem reborrow_self_of_imm (α : Life) (P : SPropU BoCa.Loc BoCa.Val)
    (hP : ∀ ρ, P ρ → Free Kind.own ρ ∧ Free Kind.mut ρ) :
    box α P ⊨ reborrow α P := by
  rintro ρ ⟨h, ho⟩
  obtain ⟨d, hd⟩ := ρ.finite
  exact ⟨ρ, reb_self_of_imm d ρ hd (hP ρ h).1 (hP ρ h).2 ho, h⟩


end

end BoCa.Fig16.BoLo
