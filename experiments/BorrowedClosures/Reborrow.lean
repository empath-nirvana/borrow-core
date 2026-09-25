import ModesLabels.Modes
/-!
# Experiment: borrowing computations — the model-level licence

`[TR]` 6.131's `⊸` bullet reborrows a closure to nothing: *"Unfold `[α] 𝒱⟦T₁ ⊸ T₂⟧δ(v) ⊧
↺α emp`"*, which is why `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk`.  A closure whose resource holds only
`imm` cells (`unr` mode: Rust's `Fn`) needs no such loss: an all-`imm` resource is its own
reborrow (`reb_self_of_imm`), so `[α] P ⊨ ↺α P` for any `P` whose resources are all-`imm`
(`reborrow_self_of_imm`).  That is 6.131 at `Imm̲ 'b T ≜ T` for such a `T`.
-/

namespace Experiments.BorrowedClosures
open BoCa BoCa.Fig16 Experiments.ModesLabels
open BoCa.Fig16.BoLo hiding Free
noncomputable section

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

end Experiments.BorrowedClosures
