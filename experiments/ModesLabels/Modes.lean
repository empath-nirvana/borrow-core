import Paper.S6_8_FundamentalProperty.Lemmas
/-!
# Experiment: ownership kinds as adjoint modes, lifetimes as labels

Three modes, `lin < aff < unr`, with the structural rules adjoint logic assigns them
(Pruiksma–Chargin–Pfenning–Reed: a monotone `σ` from modes to subsets of `{W, C}`):
`σ(lin) = ∅`, `σ(aff) = {W}`, `σ(unr) = {W, C}`.  `mode : Ty → Mode` reads a type's
mode off its constructors: `Ref`, `⊸`, `∀` linear; `Mut @a` affine; `Imm @a`, `!T`, `1`,
`Unk` unrestricted; `⊗`/`⊕` the meet of their components; `[a]` its body's.

Soundness of `σ` over the typed world, at every type and both modes of `vX`:
* `weaken_sound`: a value at a mode with `W` holds no `own` cell, so dropping it leaks
  nothing;
* `contract_sound`, `dup_sound`: a value at a mode with `C` holds only `imm` cells, and
  `𝒱⟦T⟧ ⊨ 𝒱⟦T⟧ ⋆ 𝒱⟦T⟧`;
* `mode_immReborrow`: `Imm̲ 'b T` is unrestricted at every `T` — the metafunction is the
  projection to the top mode.
-/

namespace Experiments.ModesLabels
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LSub LifeCtx LifeVar)
noncomputable section

/-! ## Modes and `σ` -/

inductive Mode where
  | lin
  | aff
  | unr
  deriving DecidableEq

def Mode.rank : Mode → Nat
  | .lin => 0
  | .aff => 1
  | .unr => 2

def Mode.meet (m k : Mode) : Mode := if m.rank ≤ k.rank then m else k

/-- `W ∈ σ(m)`. -/
def Mode.W (m : Mode) : Prop := 1 ≤ m.rank

/-- `C ∈ σ(m)`. -/
def Mode.C (m : Mode) : Prop := m = .unr

/-- `σ` is monotone. -/
theorem Mode.σ_mono {m k : Mode} (h : m.rank ≤ k.rank) : (m.W → k.W) ∧ (m.C → k.C) := by
  cases m <;> cases k <;> simp_all [Mode.rank, Mode.W, Mode.C]

theorem Mode.meet_W {m k : Mode} : (m.meet k).W ↔ m.W ∧ k.W := by
  cases m <;> cases k <;> simp [Mode.meet, Mode.rank, Mode.W]

theorem Mode.meet_C {m k : Mode} : (m.meet k).C ↔ m.C ∧ k.C := by
  cases m <;> cases k <;> simp [Mode.meet, Mode.rank, Mode.C]

/-- A type's mode. -/
def mode : Ty → Mode
  | .unit => .unr
  | .unk => .unr
  | .sum T₁ T₂ => (mode T₁).meet (mode T₂)
  | .tensor T₁ T₂ => (mode T₁).meet (mode T₂)
  | .lolli _ _ => .lin
  | .all _ _ _ => .lin
  | .ref _ => .lin
  | .mut _ _ => .aff
  | .imm _ _ => .unr
  | .bang _ => .unr
  | .box _ T => mode T

/-- `Imm̲ 'b T` is unrestricted at every `T`. -/
theorem mode_immReborrow (b : Lifetime.Life) : ∀ T : Ty, mode (T.immReborrow b) = .unr
  | .unit => rfl
  | .unk => rfl
  | .sum T₁ T₂ => by
      simp only [Ty.immReborrow, mode, mode_immReborrow b T₁, mode_immReborrow b T₂]; rfl
  | .tensor T₁ T₂ => by
      simp only [Ty.immReborrow, mode, mode_immReborrow b T₁, mode_immReborrow b T₂]; rfl
  | .lolli _ _ => rfl
  | .all _ _ _ => rfl
  | .ref _ => rfl
  | .mut _ _ => rfl
  | .imm _ _ => rfl
  | .bang _ => rfl
  | .box _ T => by simp only [Ty.immReborrow]; exact mode_immReborrow b T

/-- The labelled constructors are the only ones whose mode exceeds their payload's:
`Mut @a (Ref T)` is affine over a linear payload. -/
example (a : Lifetime.Life) (T : Ty) : (mode (.mut a (.ref T))).W ∧ ¬ (mode (.ref T)).W := by
  simp [mode, Mode.W, Mode.rank]

/-! ## Resources free of a kind -/

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

/-! ## `σ` is sound -/

variable {wpX : WpOp}

/-- **Weakening.**  At a mode with `W`, `𝒱X⟦T⟧` holds no `own` cell. -/
theorem weaken_sound : ∀ (b : Bool) (T : Ty) {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    (mode T).W → vX wpX b T ls δ v ρ → Free Kind.own ρ
  | _, .unit, _, _, _, _, _, h => h.1 ▸ free_empty _
  | _, .unk, _, _, _, _, _, h => h.1 ▸ free_empty _
  | b, .tensor T₁ T₂, _, _, _, _, hm, h => by
      obtain ⟨hm₁, hm₂⟩ := Mode.meet_W.mp hm
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact free_compS (by decide) hc (hp.1 ▸ free_empty _)
        (free_compS (by decide) hc' (weaken_sound b T₁ hm₁ h₁) (weaken_sound b T₂ hm₂ h₂))
  | b, .sum T₁ T₂, _, _, _, _, hm, h => by
      obtain ⟨hm₁, hm₂⟩ := Mode.meet_W.mp hm
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact free_compS (by decide) hc (hp.1 ▸ free_empty _) (weaken_sound b T₁ hm₁ h₁)
      · exact free_compS (by decide) hc (hp.1 ▸ free_empty _) (weaken_sound b T₂ hm₂ h₂)
  | _, .lolli _ _, _, _, _, _, hm, _ => absurd hm (by simp [mode, Mode.W, Mode.rank])
  | _, .all _ _ _, _, _, _, _, hm, _ => absurd hm (by simp [mode, Mode.W, Mode.rank])
  | _, .ref _, _, _, _, _, hm, _ => absurd hm (by simp [mode, Mode.W, Mode.rank])
  | _, .bang _, _, _, _, _, _, h => h.1 ▸ free_empty _
  | b, .box a T, _, _, _, _, hm, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact weaken_sound b T hm hb
  | _, .imm a T, _, _, _, _, _, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, hcoh⟩, s, u, σ, hs, ls₀, hρ₁, hP, hαs, hls₀⟩ := h
      exact free_compS (by decide) hc (hρ₀ ▸ free_empty _) (hρ₁ ▸ free_single (by simp))
  | _, .mut a T, _, _, _, _, _, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, hls₀,
        hunif⟩ := h
      exact free_compS (by decide) hc (hρ₀ ▸ free_empty _) (hρ₁ ▸ free_single (by simp))

/-- **Contraction.**  At a mode with `C`, `𝒱X⟦T⟧` holds only `imm` cells. -/
theorem contract_sound : ∀ (b : Bool) (T : Ty) {ls : List SRec} {δ : LSub} {v : Val}
    {ρ : WRes}, (mode T).C → vX wpX b T ls δ v ρ → Free Kind.own ρ ∧ Free Kind.mut ρ
  | _, .unit, _, _, _, _, _, h => ⟨h.1 ▸ free_empty _, h.1 ▸ free_empty _⟩
  | _, .unk, _, _, _, _, _, h => ⟨h.1 ▸ free_empty _, h.1 ▸ free_empty _⟩
  | b, .tensor T₁ T₂, _, _, _, _, hm, h => by
      obtain ⟨hm₁, hm₂⟩ := Mode.meet_C.mp hm
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      obtain ⟨o₁, u₁⟩ := contract_sound b T₁ hm₁ h₁
      obtain ⟨o₂, u₂⟩ := contract_sound b T₂ hm₂ h₂
      exact ⟨free_compS (by decide) hc (hp.1 ▸ free_empty _) (free_compS (by decide) hc' o₁ o₂),
        free_compS (by decide) hc (hp.1 ▸ free_empty _) (free_compS (by decide) hc' u₁ u₂)⟩
  | b, .sum T₁ T₂, _, _, _, _, hm, h => by
      obtain ⟨hm₁, hm₂⟩ := Mode.meet_C.mp hm
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · obtain ⟨o, u⟩ := contract_sound b T₁ hm₁ h₁
        exact ⟨free_compS (by decide) hc (hp.1 ▸ free_empty _) o,
          free_compS (by decide) hc (hp.1 ▸ free_empty _) u⟩
      · obtain ⟨o, u⟩ := contract_sound b T₂ hm₂ h₂
        exact ⟨free_compS (by decide) hc (hp.1 ▸ free_empty _) o,
          free_compS (by decide) hc (hp.1 ▸ free_empty _) u⟩
  | _, .lolli _ _, _, _, _, _, hm, _ => absurd hm (by simp [mode, Mode.C])
  | _, .all _ _ _, _, _, _, _, hm, _ => absurd hm (by simp [mode, Mode.C])
  | _, .ref _, _, _, _, _, hm, _ => absurd hm (by simp [mode, Mode.C])
  | _, .mut _ _, _, _, _, _, hm, _ => absurd hm (by simp [mode, Mode.C])
  | _, .bang _, _, _, _, _, _, h => ⟨h.1 ▸ free_empty _, h.1 ▸ free_empty _⟩
  | b, .box a T, _, _, _, _, hm, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact contract_sound b T hm hb
  | _, .imm a T, _, _, _, _, _, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, hcoh⟩, s, u, σ, hs, ls₀, hρ₁, hP, hαs, hls₀⟩ := h
      exact ⟨free_compS (by decide) hc (hρ₀ ▸ free_empty _) (hρ₁ ▸ free_single (by simp)),
        free_compS (by decide) hc (hρ₀ ▸ free_empty _) (hρ₁ ▸ free_single (by simp))⟩

/-- **Duplication.**  At a mode with `C`, `𝒱X⟦T⟧ ⊨ 𝒱X⟦T⟧ ⋆ 𝒱X⟦T⟧`. -/
theorem dup_sound (b : Bool) (T : Ty) (ls : List SRec) (δ : LSub) (v : Val) (hm : (mode T).C)
    (ρ : WRes) (h : vX wpX b T ls δ v ρ) : (vX wpX b T ls δ v ⋆ vX wpX b T ls δ v) ρ := by
  obtain ⟨ho, hu⟩ := contract_sound b T hm h
  exact ⟨ρ, ρ, compS_self_of_imm ho hu, h, h⟩

end

end Experiments.ModesLabels
