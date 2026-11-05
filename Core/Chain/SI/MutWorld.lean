import Core.Chain.SI.Sem

/-!
# `mut` cells at a step index — where the index meets BoLo's world

`𝒱⟦Mut @a A⟧` (`Core/Relation.lean`, `ptoMutS`) stores `ofS P̂ = 𝒱⟦A⟧` in the cell
`mut(β, v, ρ, P̂, | P̂(v)(ρ))` (`[TR]` p. 4, row 5.8: the cell carries the witness `hw`), and the
printed update `ρ₁ ↭ ρ₂` (`[TR]` p. 5, row 5.27, `ResU.UpdMut`) keeps every `mut` cell's `β` and
`P̂` fixed across a `wp`, the value and witness free.

Read at a step index, `𝒱⟦A⟧` is a family `𝒱ₖ⟦A⟧`, downward closed. A cell stores one member,
`𝒱ₖ⟦A⟧`. A write through the borrow at a later index `m < k` knows the new value only in
`𝒱ₘ⟦A⟧`; the printed `↭` asks for it in the stored `𝒱ₖ⟦A⟧` (`printedUpd_keeps`), and a
downward-closed family has members of `𝒱ₘ` outside `𝒱ₖ` (`StepGap`, inhabited at a stratified
family: `stepGap_holds`). So the definition the index forces to change is row 5.27's `mut ⇔ mut`
clause (`ResU.UpdMut`), not the stratification: every member of a family over `Res_β` is over
`Res_β` (`SPropS`'s type), and `β` stays fixed.

`UpdMutSI` is the index-relative clause: a map `Φ` from locations to a stratum and a family
(Ahmed's location typing), and a cell following `Φ ℓ` may step down its member, `𝒱ₖ` to `𝒱ₖ′`,
`k′ ≤ k`. A lender reads the member back at a later index, so it gets `𝒱ₖ′ ⊆ 𝒱ₙ` for its own
`n ≤ k′`. It is reflexive and transitive, and a write at a lower index meets it
(`updMutSI_write`). It is a new definition beside the printed one; nothing printed is edited.

`UpdMutSI` does not carry `[TR]` 6.48's `mut ○ mut` step, and bounds the new member only from
above (`SI/UpdN.lean`, `not_mutMutMemberStep`). The clause the relation uses is `UpdMutN` there.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-- **The printed `↭` keeps a `mut` cell's `P̂`**: after the update the cell holds `P̂` again, at a
value that meets it. -/
theorem printedUpd_keeps {ρ₁ ρ₂ : WRes} (h : ResU.UpdMut ρ₁ ρ₂) {l : Loc} {b : Life}
    {P : Val → SPropS Loc Val b} {v : Val} {χ : WRes} {hχ : χ.InStratum b}
    {hw : P v ⟨χ, hχ⟩} (h₁ : ρ₁.FlatAt l (CellU.mutOf b v χ hχ P hw)) :
    ∃ (v' : Val) (χ' : WRes) (h' : χ'.InStratum b) (hw' : P v' ⟨χ', h'⟩),
      ρ₂.FlatAt l (CellU.mutOf b v' χ' h' P hw') :=
  (h l b P).1 ⟨v, χ, hχ, hw, h₁⟩

/-- A step-indexed family of payload predicates over `Res_β`, downward closed. -/
def DownFam (b : Life) (F : Nat → Val → SPropS Loc Val b) : Prop :=
  ∀ k u r, F (k + 1) u r → F k u r

/-- **The gap**: a downward-closed family over `Res_β` with a value in a lower member and not in a
higher one. A cell storing the higher member cannot take that value under the printed `↭`. -/
def StepGap : Prop :=
  ∃ (b : Life) (F : Nat → Val → SPropS Loc Val b), DownFam b F ∧
    ∃ (m k : Nat) (u : Val) (r : ResS Loc Val b), m < k ∧ F m u r ∧ ¬ F k u r

/-- The gap is inhabited, at every stratum: `F k u _ ≜ k = 0 ∨ u ≠ ()`, safe for no step at `()`
beyond the first, as a thunk safe for `m` steps and not for `k`. -/
theorem stepGap_holds : StepGap := by
  refine ⟨0, fun k u _ => k = 0 ∨ u ≠ Val.unit, ?_, 0, 1, Val.unit,
    ⟨PMap.empty, fun _ _ h => by simp [PMap.empty] at h⟩, by omega, .inl rfl, ?_⟩
  · intro k u r h
    rcases h with h | h
    · omega
    · exact .inr h
  · rintro (h | h)
    · omega
    · exact h rfl

/-- **The index-relative `mut ⇔ mut` clause.** `Φ ℓ = (β, F)`: the cell at `ℓ` follows the family
`F` over `Res_β`; across the update its member may step down. Cells `Φ` does not cover keep the
printed clause. -/
def UpdMutSI (Φ : Loc → Option (Σ b : Life, Nat → Val → SPropS Loc Val b)) (ρ₁ ρ₂ : WRes) :
    Prop :=
  (∀ (l : Loc) (b : Life) (F : Nat → Val → SPropS Loc Val b), Φ l = some ⟨b, F⟩ → ∀ k,
    (∃ (v : Val) (χ : WRes) (h : χ.InStratum b) (hw : F k v ⟨χ, h⟩),
        ρ₁.FlatAt l (CellU.mutOf b v χ h (F k) hw)) →
    ∃ k', k' ≤ k ∧ ∃ (v : Val) (χ : WRes) (h : χ.InStratum b) (hw : F k' v ⟨χ, h⟩),
        ρ₂.FlatAt l (CellU.mutOf b v χ h (F k') hw)) ∧
  (∀ (l : Loc), Φ l = none → ∀ (b : Life) (P : Val → SPropS Loc Val b),
    (∃ (v : Val) (χ : WRes) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ρ₁.FlatAt l (CellU.mutOf b v χ h P hw)) ↔
    (∃ (v : Val) (χ : WRes) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ρ₂.FlatAt l (CellU.mutOf b v χ h P hw)))

theorem updMutSI_refl (Φ : Loc → Option (Σ b : Life, Nat → Val → SPropS Loc Val b)) (ρ : WRes) :
    UpdMutSI Φ ρ ρ :=
  ⟨fun _ _ _ _ k h => ⟨k, le_rfl, h⟩, fun _ _ _ _ => Iff.rfl⟩

theorem updMutSI_trans {Φ : Loc → Option (Σ b : Life, Nat → Val → SPropS Loc Val b)}
    {ρ₁ ρ₂ ρ₃ : WRes} (h₁₂ : UpdMutSI Φ ρ₁ ρ₂) (h₂₃ : UpdMutSI Φ ρ₂ ρ₃) : UpdMutSI Φ ρ₁ ρ₃ := by
  refine ⟨fun l b F hΦ k h => ?_, fun l hΦ b P => (h₁₂.2 l hΦ b P).trans (h₂₃.2 l hΦ b P)⟩
  obtain ⟨k', hk', h'⟩ := h₁₂.1 l b F hΦ k h
  obtain ⟨k'', hk'', h''⟩ := h₂₃.1 l b F hΦ k' h'
  exact ⟨k'', le_trans hk'' hk', h''⟩

/-- **A write at a lower index meets `UpdMutSI`**: where the cell at `ℓ` held member `k` and holds
member `m ≤ k` with the written value's witness, and everything else is as the printed clause
asks. -/
theorem updMutSI_write {Φ : Loc → Option (Σ b : Life, Nat → Val → SPropS Loc Val b)}
    {ρ₁ ρ₂ : WRes} {l₀ : Loc} {b₀ : Life} {F₀ : Nat → Val → SPropS Loc Val b₀}
    (hΦ₀ : Φ l₀ = some ⟨b₀, F₀⟩) {m : Nat} {u : Val} {σ : WRes} {hσ : σ.InStratum b₀}
    {hu : F₀ m u ⟨σ, hσ⟩} (hnew : ρ₂.FlatAt l₀ (CellU.mutOf b₀ u σ hσ (F₀ m) hu))
    (hold : ∀ k, (∃ (v : Val) (χ : WRes) (h : χ.InStratum b₀) (hw : F₀ k v ⟨χ, h⟩),
        ρ₁.FlatAt l₀ (CellU.mutOf b₀ v χ h (F₀ k) hw)) → m ≤ k)
    (hrest : ∀ l, l ≠ l₀ → ∀ (b : Life) (P : Val → SPropS Loc Val b),
      (∃ (v : Val) (χ : WRes) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
          ρ₁.FlatAt l (CellU.mutOf b v χ h P hw)) ↔
      (∃ (v : Val) (χ : WRes) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
          ρ₂.FlatAt l (CellU.mutOf b v χ h P hw))) :
    UpdMutSI Φ ρ₁ ρ₂ := by
  refine ⟨fun l b F hΦ k h => ?_, fun l hΦ b P => ?_⟩
  · by_cases hl : l = l₀
    · subst hl
      rw [hΦ₀] at hΦ
      cases hΦ
      exact ⟨m, hold k h, u, σ, hσ, hu, hnew⟩
    · exact ⟨k, le_rfl, (hrest l hl b (F k)).1 h⟩
  · have hl : l ≠ l₀ := by rintro rfl; rw [hΦ₀] at hΦ; cases hΦ
    exact hrest l hl b P

end BoCa.Fig16.LogRel.Core.Chain.SI

end
